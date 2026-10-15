-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4098
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:33:44.064316+00:00
-- url     : https://prove2.me/submissions/107ea964-cdc9-4a87-a846-8b1d0bb43bbe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 736870503 ≤ n < 737050359 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 736871753 1250 736870503 736870531
    0x7050405070f02010f0b09130305090d21050403020a050d110405100614090a0b131205060a0f05100e071412160908191529030a1104050406020c06 64
    0x7030b400c042c0c00c0d54103109602c60070390319140044100d950343c410044c0c1c1240009000c1400004d1a08089a07284074100125400024580140081203e20f07031415250207101c0d481549158214a0b04440c10b01c41c0d40310203503002ca280c074400e200a00d001c000c48984288503035000d110300314211010a080e28000c592160074640309000c10801d841c0c008240721626440d150700d041c501060b003800200142c4260107441c01009000c5400010480360050503c040c0c652103110541c466802c0c1391070741c0e484808a8041c0c00c1103040100c45180034440e4081d05000303100300c114486060303040810380b20341c20744014611010001c0c2280c48402d00400080285415440501da4000514050b008990003e40c0b07122900d00b08040480100301c00d000128602c075080c0c620b05136584403410707a030400d000d10801d0400c20011562401e8407400400342d86105200c1408051400e450104507402c08145d140c040c0d44001504004100101001916055022030f0f401441484010b05155180d01100e2a20b401280d083c4c03494600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 736873003 1250 736871753 736871777
    0x3020d0f1a0420030a0f110c030c070b0702030c010819110c1209060d0b06190e0a08030405030c150f0708041e03020d080307140f0a090b0304030c0807050705040507 72
    0x4680203400201e403160f410014a0710900c0400015440020556030b49159140c410822600494001c0010807040b0b20450343c07071704e00c0d4811003916030b408182000218818428001120344003202640c200d260014090b00d40e0820003001074800070f1005010a03c65100d2094005038804c0c54420141b26950300c0c00102c0e11050510822868010703074400c00340b01000144018031003540c60100300c40c48440c02c0400441c10710f1002d0041010741c016880c568480c0084102000c0030300d648880e005840d03120444240016990780c0302c4403034513840b4500032142c15400589910780e403420504403402192403080350007880e00c10030004d01915a00302e0041140c2d540308c0007508120390506116001c00d1448101c1e0a07410251a540c0010355508022000401065020000031401405501c0d012014913036016070903035802c0c0b03000d0100c2059119080356008a078402c400441e0703500c44030042d240708940c140c0315180c5188d41500d0342510341d04001d9040f5640d100c1d81c000481e0300c0d1218000e09010364050b40303400f451281 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 736874253 1250 736873003 736873009
    0xa1805130c110a0f0f05010b030d0807020606240c030702100302030f010e10170c030d09170106080d030b0d120930030f030609050f0709080f0c0103020d0f1a 69
    0x242d000702254a40c40300c41d0341e1010911604035400010f0748006030a0a00205117800d43c091301800c4401e645c140130302044144040e4001e021644240119401d440c015a07501d800c002450440300101400703041000070342c0c1c0e0154186001000381c0c0381107000312030400c0c4103a40003410385030f10480034000080d00401480301e043c81e14140d83e0b0141c040c0760304003e02e52a210307a0b44441419184030f0811100d20141200f000388600740512045041d000e0140c071440300715441c1c040c1842c94035210b1560519100304c0401603404041c4100c2c003e80303044601070300e402506031404801400c454002d09500458004054002038022102041d07181800e880b103407195894404000210040e040c4507440300c0c812085008001e648a580c2c0a038080c0d45810040c182c9000e415045008003c0d80e001024071515101c28001c20100c118009440741340150f8540b094a07869001345526041955400d03c0359a11001d28110300b58083d402510380603420940004040c0b00c182400b0054541801142c04007140c9100c209034282 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 736875503 1250 736874253 736874267
    0xc200a031704030c0602090a051804230c040504020f10082409040210030f06030c0314031204030e0303120115120c021e0c06120a140601050a1805130c 66
    0x416010040840c40c50b00e600d000c0c003208003004c40240714035400111300c0c000b07955160344007001d00405084c02121191050307645103c0d0f0820307503060322410118909100009100d030b0180d010b40005401a0956078010020701029102c00b5000301c1c0d001100b90915026034482e50340c2250700400503074851030745042c07405554400c0018803003800314988292030301044680b02e03170a9807604180d055407040804000300b24100c0003011b000c90a55045030034401c002023880f000c0c40226007901e00400c008000c080004080701d94a01c10910038400d94440c0c8000903020a0056121111841c1c01074180c9140c00e103204240700761900240c12403c19021a031881841555000c014001142d140e242c040000004d40d01020755959012009681072800341c01114007460f20a02070700e11952005895552600c26000703070145100001c07110420002d140c82590207034110040041801850182c564601c3c0a004030011240f6882d000e4102046550b07a02c07001940752038010812092420704100040d6a40350540002e00d44 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 736876753 1250 736875503 736875527
    0xa03020610053a05070609031106031003021203071b06180602071e09020f070b28090221030a03061e0b07140304030b01090624030c200a03 61
    0x80e403510403440416008211a44040304004200d43c1140407160507410f4021920303a8004200b8007450700001645a00000301d0b60070340744103d201e04141003404007481060b000071500200c4440503641c0c100090b0030049140d81d45051400c007a01d140841070380354040c080c480041007400e50b0b60191020421141d0220340d1907044d04d001c1da4031030003103850400d00a555000034000c0c1d044041800c2a41e100086d201d0000500504681d042551103e00302d00d51580300380c06c184029140307210b010b000039078015080385035141d54a40100ca0840f40c100392052040091070001000c036000b00d00c0580099030201c07491003011000d810040119a038450b9544001d0540d203955102242c4c925804108003603040c2c031032a10748240d074400c4a080c0d4482c621070920036154610030070720102d03a0000240c0401403000010341d03d4180c0791300800138016280e6480200d04680450111130184e0040c41407044240b505c0394002008003805483c02219000c50921280062450386250811940c4910840d00030550424020514 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 736878003 1250 736876753 736876759
    0x3150f0e071d030c01080903160b10060f08040f0609080d0506030f0a170a141201030201020c0904050604021504180e011505010906050f040e0c090301110f040519080a0302061005 78
    0x6040d5002021903070380c141c4d09420605101c050340020301400f00400568000224403c558034041d03441d0300b88801d10f040150794114059801d2280881c846000b0300008c5080300803580c40c0c00c1260744a0720b0703a10080038440c0e82103030b68035182c4004001103691302002c4c116025105500042a00b080420036107024012246002d454000d0300182e0045040e25040a0b421000510300a9035840032000072210786941d220b01c07002a480100f1040c102e648501c801a0689101ba002c03603820448400400841c65801c46006005600150001d401414940c038401c1d030b00c800f0910118200f03a12803d03008014400c1803d40901e8030f47d11000c01003010b200340101c035040d8080300ca02c4406c0781e0400c0002440d591160040c0818003800107031017120200800d003114001c10400c24441440c1c1011300d80980c0b81e40c0500ca03018465802d00e01c4544c8826800d900b15011401414045860107280030144000a0081400300b001c0d0800c502000510350018043c0c0c0145900ca6805070080d80341901c91050385e00850b030007480c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 736879253 1250 736878003 736878047
    0x30209271014011b02181f150e0333010b090321120403110d08010f09090f080406030617030a020618010b1207080f01020f04050103150f0e07 62
    0x1c24000511540b82d503090a1070310180038800610101055900444025049040c4604400c1c1500c4003580d0326008200d95400000302d0003244804404010300c0740119510744169800f02c00c8101e000b000c40181c4050301405681d0040001101d840c035103210f44981c05001042100080ba24a001064090140502c4403019040200b04804a41d0707034180621103007041c00308094602e42c40c00c410819221408150411030340c50345020301d00105000009410070f42c0600c0340c0040c04904034006c0382618161400040713945030356450001c18101510a448064a5560b014200000842c2d1400c000303101414580c1c0300495410716210141c4541120420807824980017804000d51451303000c0307a01900f0070b10141820080360f80d0300082500621141c8415176008416543c3c7c05640503001c0361184c220340018060703824019010130624281d1240419900800c0c03010841401150b020b64032051603007540d40d82c10340e1401e80761801108126204c1d004120311520140422070302d6544480302c0b00800d010030700c03181e0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 736880503 1250 736879253 736879259
    0x30b0615040308030c37080f0f1501090306060e100f12061109060a1101200412060608100b1c0f121b0609140703020a0e070302092710 59
    0x42c26900010384003da15030000521a40e21010711066141940940c4030304218a1004030710034140417546c03140b1400460b2110f8000341d840101c032036145115811504c02c1718942e035510400000030101e0f100010b414004c040e240880400e80c03034030401020b040c0300c4503070180c107003082d00c41481c3c0240c03541d20480d031820403820f05000204a03031030743d06000c65004001040300e038451030340d11425019146807690418008183d07440300f036500000d800200c061800003000340e003400305051410394a084070035800002c010001002880d141c0d404d152201800b440001501a89686119040071805d14080405503100e41022201d07180185141022250520810009800d1591280168081d015003d440811071072960541207000d0f2030807114412200302e03a900c8225042c074000005055080d0142e8400b400c00c0d080e800c000c0d0780000c150090381c0d0010f101c2400c42d8581002d1100840e0018001d101301602031114a00769110038040b503007141503413060180c603c81c00781e0402d008180c004220800780d04420600b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 736881753 1250 736880503 736880513
    0x504170711152110030204180b010905010f0b0f090a0810110306010804020d050a0204180c1a03040f06060515031f0605040603090201200c100807020d032301030b06150403 75
    0x110801500628101d203c0740d503940880348000c52240e002940043c01d240300e400107402030b01c0c40d190388940715032502d45040c0d0302e80b450081220024041c1c2800103095017402e001c10041c0b440903154201e8460b182c80e25000044010500c940d40d940c0c00440d403940200d012820300f90080c090703280200c118a4555086240120008101a1008d04041c1c0030780c4a40701c1036424014240700150010350050800c0c8440c0d103810306108900040d100050b6000c0b01410710220781079051b80b04c1c401100900b010b843d400c5031502c6d01c9103c0c48441310401101da4954032000024140c4480011000000f05c660105442e80b80105200014040d24a00b003401c5064203d01404819041419901541d22526000514940714030041e5182e40c80e11100b505030642c50b580004e03140300700007028847c811050790400b180e00c1d010f50b800e440c50722003980c118000d40c01c02013090720305601c254004901c081c0c82c1c038456820028108001310300c1e40408c0e04182c61464001c0204465400c08000c80801301c1900d0010901d8039146841e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 736883003 1250 736881753 736881787
    0xf1903050730030f080901140f01060f0c110f12060903070b0a090507172506030b03060c0d0c050f0a0801030605060d210207170304090b010e0d0303050417071115 71
    0x182c41800240c1011404221b425405024441100f646c40742060620001c0401c0e65070007440b03410300240124540d41c1c820f9204540344524981e0107d81c0c00104002075042001b50340c01c1802e0a90840c11906c0000b850b40c100b0015a4007590740d82c0042c6985074144d09007807035040802440d01c01c00608040303401c4002800054000101c9056480400400c14550382c0e803814118044076048440c0c001e240c0e006901045040c005007111801e40302007140442c11028541c5516040325801280e030414041042204043d030858085a0b4581c076200b46031900c10307a4901c0380782d00802c0303880000a03580001801006150301c24541c02c0b0208540c0f54254a02c2581c0c0c4916420070b0760404510801c4441107800942d00070000d0030701402c070024100030b2a85466081982c2c0390070504c14810700c9030401d01c00c01400d5000340d50303000c882d280190500d85c116441d83c41c00e801904c2c010304111214214806400d0b851118030015080c1d06200c0c012281e480540784040166007081c004404045840c1040803d80007114210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 736884253 1250 736883003 736883027
    0x51f051b07020f0d0510060e06040f0608060106030c180b03060f0a050f011119050a0c0506071119050a320a0e07021204030b0f09010b0f190305073003 66
    0x160440034040c4e80d14000b42000c02a01c04000020304160000ca01510341e014140e1080a05031010001001e01003c1441611440c3c82900306a400c00ea0040c000144a43c10080c2c420305603080c000b5880c1c41e091091050680164041c0481c0500482800f505282c40c0d0041c0b10110b008507a591006c504000003d00c02d2058010314a041c01101d030300c0c042c8481c1052000660404059258001041e05801c0c00c0d40c644003032a500315005803210b10007091a203446d0b400d603019a078004115414400001080c0090300540c90043c900c14141c800b800a07803641c41d8614038005e842010a11914a04d98025079407000e518100010b4001c94014800501501e900062104940d04420980e0740380d1640795060342455041e078451005c003840080c0210030310203a502124000d0b401c0c0e80c0c8141095072139000041c00c94025500d01d90703200320180030000c941d20703018052240b03030f01c038508c2a08051981c03a07071510316048007031f40216108a000031306c0b4841ca9180022141c0c0320340c6c07043c6100c17010b0509590001d040006080f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 736885503 1250 736884253 736884259
    0x50f0d120e0109150905100507050706020307030f1506030e030f2d0c03090a0501020c0d030f0e030307050105010915030f150e2a0402040b09060304051f051b07020f 72
    0x416400c000440940140380f1040e00b202d4103800c0030213205500f401610161100fa00c0d6449544150250142c052203207600c145499560241059071a50351b0708042d62000e00510209615081507044c43c04882c4540300700e00c2d20928034154020301d00700c400741c29a41d030f08065111a800500558699601c1d039000c0741c16008107200803066241d91010250700d5001030215030400142d02043c0c200b41951b0000051074891800c84080500c5640d601c0120380d1102802d000d140c03c04441192100040e01410945c01d0084140c00c1100013803081001092440d000414141d4040c0e45600040010461030300c00e81345039030401c22920600c42d003980c80c0c1c07003090929110010b0143c141d40ca46101c0c150b07076580c05000940c00840a6480d51003042c1071181c04078a801c10550058044d0072020300e0343c1d24081c400c49080780c1c85051400d0a281540041107640c0e08020805c0d070701c174010307484502e0305601e25100581c0c45803009000041c050070280641c140610303c070404194811000c104050140c1d0312250410607581c411 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 736886753 1250 736885503 736885511
    0x902040e0c0f041809110a061e0e27060d0519030e090103050a020a06111b0a0306140916030308040209061810030203190b06012d0903050f0d12 63
    0x30300b058041d204070f42c0301442c3d608414980c0200000c40c1c1d01300b0f0030524040d901c00c1d14450741100401240712414416040403a8084101d100507013020140880e8502503402c0c1085103200f407801040209100c2d2280c2c4200c0e61441e1a042c101d0701c07a40001940129080e40c84e08902c0c0083c1ea241c41d510b1110350302c5420030030b900c0600b2100301403044148400000005e0401c0c045540e4901e40642d4601040c2c508912071600801c001c29814440e40c94001c001440000a2403c19001a0354192240d000084d181d0814030307010b000703c00300701c0900910311010f803011042000b501d0816021030401101d41c80c1500c9a80404600f0000320358024140e030740054040780c21000e581c4491001030140f90f03681c81621110030210040000c06c1e40c1d18a68a42120300941c00d50740301038080064a0803100c1c1c41d0200030a00d441303c0000c00c040e07501c10304c0017151210101000c0200c80005510b110f008802030200740c0e0008031048010f1007004814080000d41c10000345c000c05598241d00f602030300100c7d240a5140001c2d5079 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 736888003 1250 736886753 736886767
    0x106060e0112270c091a0103050a0c0905060918100e0711060f0a0e0d09230d030e0607141606111005060301020405040501031b120f02010e0f1c020a0902040e0c 70
    0x1400301c074400170943c50b041040039000494001d0104556100c0c4580460f10b444001000c020b02801107109600e125a03581906c03500b81820400160080c00c2442d80064808400c1d072400ca5003500c20030b018000f46521a403c680c5007400c07800140d8801403601c03041084584029240640000e222904055984140c08041e6240340c1030038001c145c00c5000d07495038071400c006466050303040300300c03034080d50159034140f0b1146d0b194105d030034503006c50300f900e054101e2002c481d50700200e4403481c0c000d291583d0060070985000181e480e109a0a00c0e010620400360b008003c002c0c80c080d04400e01000209003d0500680802a1850390b648031280510b04803596500d0382d0000c0e20aa4017981103502900c40104108610350b16030500380da00d0001c43c4c0300740c0c0140040810104030042c1404030200c40c1a401000315800f0806980112141484070034115003202c0620400c3e4410355900ba82d502010000c10b0b090030703000d0300c94010000c4102403079000e5189944100001d00070040c14082240c0d110408640071552900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 736889253 1250 736888003 736888013
    0xa05030a090b04031d010504050a03110607140f071a0307030b1c1104060b04030c03111809030c010b010806010905060306030f15190c0e040e07080106060e011227 71
    0x9041ca1000b00080042410481003540003000110400c0100107081c5141124100540d05846107005580e032064444008000080f1603060f030410350b44002c1c01450400b10300d942c4d00000502c1441c3c0100260300220721540c124401041510020075850025400c2403006200c003171201c0c800903105d181007540721400180191129107a103170b007040381e06904004800a9081c80c2440350f505100d01740c8100c0c10034400282050960040c0e07001e594109280140440c5140d0303c1039507000741d10b081160451a0700c1562072921510210300c0d8411f000b624041d41d83d629028146d02e0850300110384650510548000b88016a60b20070440f400755a410f40d1901e0b502c0d220103002a00d400c2212201848510903550304956144840f9080c900071303461460040c00e02030009100c40140d0320301c8401000050028200512280b0381504901c142c0001d8206950000303860300e03a11420f6030603541044010400848403d03009580c03010030035644ca80541c40030054956903201080d10088902c02c0302c0d00d04c06c40c80c00801c003404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 736890503 1250 736889253 736889261
    0x8120a201f02070209130203060c0a0c0f0f02030d090311012d0c120c1707151b09080114060d02060c070f0f0602060601020715090e040b010510050f0a05030a 69
    0x85454400040c018450700c1a400070354800c4000300d000b20007035000b01d003d50458001c66103d4660060141c43c0640c0d500c030032a20241c01c0800040b04100c091510900810101d0403c8004039001d130329000ca0b000307203032b0040c145800d0708604071804002c1c0040c420004202001c0f68050f05941c2440d080300b007003080b2101c00c40e200c0340205880035010242400c2d61005500101110695071040c064506002c280c3c10302540c5801f000800602518201c4101030311002c02800207124070340c0315160052084421941a00032501c0940e4220700c20440c1c030b000e900c07110750004043c42c000c0c032100e8024007906081907204003403085e000c1c2c400380c02603590b0000b481c1196a16402d64620480340c03002c441e1200c3d0b8425100c0c12841d0304c1e10404a80700180c040108449201181c61841940306030002d00c01c00b8901503144104050a02400d010806041408140b06c1e900d0944a0301403401002d03010300d40d5052034100028006030140f9031013401010881c80720340d60180c200340e40618a060401c0390703e9a5840c1060000740c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 736891753 1250 736890503 736890523
    0x12010b04060803071e0b0a0c05070f0303060608090102040308040504090c031a01180e060712020c0706020c0f0307120314160303150509010812030405030d021308120a20 74
    0xd42007440101c0c010200001400d600707409240d140080030700b00203400c03010304441c49000e009100d10a00141484086400c5002c201800d4a000c91815009480f0034a4651409000702d0000f52214010018203521210303994110071590021860140385a540d40000e20440c406e50f40151388560144d400d001403040303404019a002020400c042c0003e154130f180c441c1d000d000c0d40794500d550340103e521350441c6100c0c65000d002154010200c1c0c8d00c7e150015903032840c01c1b04500200f0394007084464200c00d000d0080c0784c0181a0b0f9002001d445c0440c0c8100310b2480560b030038240c000e50004808100c402c0446220000311601410144801c040010b486401d1f8801c8106e84031184901c1c03100d0b1820168554440c0e6401441902d004443c1030301c42c0100210442c003031203842e10b103038451075400004c0c1011800664202c2c0c8608210380c0380801c07000c9281c00341e1f04201022101c90404520800010400b80007042e9500d082c0c02c0324600d0180356880140034108038400c2040c5144000382150341c41d0504000300845 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 736893003 1250 736891753 736891759
    0x30309060a181a0408070e130818120d0818060708040c0f1412060402031c180608010e090304050109120302190804080708031c0b1f03020307080f041112010b 69
    0x83c400c041a0491030780d401031042a00318843c01e4000101a200c80c80340794010441002052000c07403243e1115440d83c0c110744044600b49404442690142d6144080d51112428134030151170716800d5880d002d44583e4000f019145040c0441084000350003010400b1540300c0c1390342c2401160382e280c50a022000e44c4081e0461840152901c1d0045040c110508132080381d9002110b40c1000c009004178080e0b00c030681550002c0d0503612a06000c034190000c0b60300e0f400c000c1d441d840d00130b00e605200300040e0310034941ca92200000c20f1701c030740060100107104101154885030b01d0004504c5c161500300000c0050396075114541d076212029880004052003400b032f50340c901e0002038002ca04800380b801c0c03003030040e03000b403003009014400c00c0e1001a1110001c001d403010070841e1840e10b0001381e01e58580f04040c0a0b41c050700c03175004808074948440c00c1412500004c10a61a0340e0041c2c1740d140c00c101c040c1c0220f101800481211181c542000300044005412031030302c5c02e00b5038513038500f204424800f07809400486c01c0d0a038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 736894253 1250 736893003 736893029
    0x1e15090b070503040f09140c090114030115030b0117281e0f060e0f100b04080609070e091f0609020414040c030501120f031e050c0606030309060a18 65
    0x41030002c004040c100b0303140039041c105161a56125140c049070003840d281c0c800e5455031800111510321050180142c500103042c9054510007540010711168400d810400066150162030059181d05118052100d4000c0c208250100e1203103180c80c52030200180031340c01da00c1000c044010500000810480c0460720018140a140015960851000100c20f411018289071961032110a0494040d100c12109607030307003005068450b8506032821140040c540c00d62050701c0f05000402c400050001d000030000c0501600050030310440f0a030500d2019481944d02a0048051164246000c80c410802010310300406184562b8003100390b002c0e014035031084204a01c0410000390032030140d80c902c0b10b030242c04c550410450b1403204081d01110401e01881200d40402e1004100081c0400052100c44d0300905042d86402c00381c2410518207001020150001440828042032a19080180c0c41e00050210041d5080c01002d0005c81c24a008000042d801c20484180403070071411450b8a0034003410440c0f6842d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 736895503 1250 736894253 736894267
    0x50d0c0317071a0603120307170a060b0f07030e0402071101050304020117090c270103030c06061e150f02060c0d060f03050102040602070e22060b0405010801151e15090b 74
    0x5202d010003200c0d4207000307019031184221b00d481c0c04000c40c2d02c250704584550019100e180755608680000400b551681d55445002003050607055003d003915008003810655030398420325008050705403c0039614000d0340184094000680d600c199808400c10a280c03c2e40c40f56102d00049401454004442c00c0c403070b80090901100503800b0516648669082d1900e0b00b4810011300c106400c2c054492901c400c02584c8401400000d2040001c0801c4500500c0702140d13580e120340050340d803448840e0181d405542001820443c200078800340c0c5158511905140e01c1c1e01c45142030203916010300904004c541c0d00b00007844020b5400d194400c41c040c01c46284c10480031038036883d00c40d0003035009024250261198200000702001ca40300b002d80715142c0780c07144000b00c11050f0000345016003074081c111070168844240010a440f68852503000b045407070004510f80030500804420828150003041c400351901500000c0000c1001d03020381150850481c41880341c00c3d0320f40440e481c00380c80d00040c070503c200160704 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 736896753 1250 736895503 736895543
    0x190303180605100816051810170604060b0f0919021308010f0e071d0703020c0d0e0a05010216030b0603030c0d0c03031506020a030315150c0c050d0c031707 68
    0x140c404e0341e1850048500e03120400f560460344020501c507103940007682e1a02c0300c0b801c01e407180c41300740c0000c1080f15800ea031030f032030300138010780c010400c2c000703003016401a0204801e102090060b002d4110303040d643c10052450318030106501c03d03801080c4c80c003e40c40e1071610403400106581181c906103a0b95000603502910350080302c0c007820710300c01c00f02007190405952001c0880045032a0003100e0001701500412760603c2001c2c5503840d4014080c405143d807d1100c90122074041c8407500b20300c076440c0e0f2140c2600c0c02c084200944106141c01840c115030100352000301e000d4400c000d84d0103403504156440056a641c000080c0345100c4c800300c1036118040c603070400050342e40143c8803416581c800e403400e001d00072100c000b542c3d49401c548146401640411941d10100380294410746d4508a1444001c11190300c0d81c02444601c4040842c0d41d000132949444078042c403203600385120141030708440001c522165901d82480c6004507002c081d280c000622002e11560b4000c10031285503507401441045c60060310032036 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 736898003 1250 736896753 736896781
    0x110f1206040515060d050c0d050106020c120d0c0219030c1205010b042306041b111209060a0503071205040c2903130807051617190303180605 62
    0x31401142058040b40060064495605407080c02502c000d04210121144030b01811002e0182c1c0461101002118a5030106000702da000c0d01840e0000c0445000f10020320600c1c410040c0d0441c215000034541118150303200ca80c8459054048032010202e054002c11000d02c0103595000505400c2e00d208001303a01c0101d0041c07072001c54000e8008200681c5070000380415104001c03001c41c1016080b40c3c0e144a40003418144a03003104010b04001070150318481443c480180700300408004c2000502c000051410820211001c1c0708404a028108520302c008207102e8000d20007004140540400000c80262103000c2c11949010030200c01c1c03040d4200f50903c0c014201c014050074502090392505492a41c0000d10201c490a0140b50201d107180d5810f034503020702d0305101d4001c40f2003010402001e00410340404c194200c01054844000e90f00c3d00d400e80c1030000300c051891100580d003020078a002955001e50742140c240307030941404165000c421a150001800c0d4590040c4402c2c80c201c240440181d00d403c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 736899253 1250 736898003 736898011
    0x102180102070b12010501110a0605040b181c03050c0c01060605070b0a020a12110c1218010f0c111302180a0515190311040303030b09070908060a110f12 67
    0x307a440c983d88401003002c80c0c0c0300d04d00b0055140229600100304030751049001e04442002d110564180300103e664280590750251404d03219420103a060041e1821059072984050130180700030110703094941d0540c80507140070101d0740280b55030754001595808042c003c9840d0808144001c0100380d03121180548107070800c0c4010b440b2848004000344944c440c500c02c0f81d11042240d1a0891400340f2a0182070240001c0c0d40c501c1e083d480203101022801c070007000b0800d000c2c0030501205440d0300180c60b0b0010400d02c0c003420310741044416569501401d07084014441c284d500900d2a20705200d019000c208000301040000d48103030310002d11444084030060400d02e41c0c0b84200d078070022080e038810030003424003030343d00411a0000e0204074100c546412034840c4e200002c02410b000c00e404080c0d5021800581040c1d00c103402280d16038411903a1444c10b2201182d000c2e516091140d509818080241d948210041004002559070710402c401422040f007501c0464017400c0ea22641c50140781400e9124400a039 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 736900503 1250 736899253 736899257
    0x705160305030301151103071203060503011103011404090f0311210a030f0204180510030b1e010911040312090b04060e04050a0e03090d0c0305010f02091c02030d0c02011101021801 79
    0x1103000d0906c0c071a80358494108081c000170360400805845091550705882c100c1000e25640790340000749a14217000d0042441340600b84d850f242d40c50b00d0700381342020204030700340351240b0f15041e041c0c40015001218170000940501d428807242c0e05548801c4d2a111000061801d91170702802109007525404005268111045e034060015402e1450b04805074040c034028a000c070900d4087c1000f06018583c0b01540c0500110a180d900c15501e44035600500d100741c0c0d046031640c40030019078071074907866403100b401809500e0f020403803810141814030642c0142d0000505517501e00c108840518400c0348000050b00d04c2030340813555a50b0302c00340034148e030340c103070b80c02070700650801c000a90542d07064802c04d0322100c13044024514040702c150421900082c2414216011845c140300031010034801d03c40c480d81c0701003100d0010703a00c10f01c001c04c01610441400140500000542c081c2005071008542102c1800342da0a21841060585c1300581d0301000d00782ca4038900b0362000c5520402a401c801c41949040000e0f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 736901753 1250 736900503 736900529
    0x17070b0a020702030d03060303091205160603090b0f010f050402030705121005010311091e0102750603090105071103030c04050d06060b1201140d15020705160305030301 74
    0x801d05c00e4041c2c513080d00c00076000c591850020060f1f56000055190868450344c26a0100c12802e50500e0a840181d007080d000030382d40b1a584c10030001500c0c0f1550b00b0040041130041258074244c44180c0f0194103015544c00703241c000c000700c0d00442c00f51090750792802d07041010844038900300d0403100e840751a40c03003a40d0019040c03c113000d047d101c2400486100e0038001c0e00d849600c01c4a10341c1701c4062081c2c2030016045108000801188c0311001c075402d1144401181d08546c0c544980f0b50100202c1c02120110350a441036050b210000d400f010074080020724000303411000d0000101d03401342080c4a5080c61900120000100501d2030010340c4102d20490340d945501240005c0704400b640c0d2400101d4139864001b00c204402d1042d484d16040c0882413030310454002c2850780d250072a002050704090403001c034202c0a080180280100d24035140b640800c10382c0c0c110441222a103407090101d505003154100310f580007850318140030040c8081c9090607803482c03030102050750b43d260443d030720f40c800d2141010840b45 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 736903003 1250 736901753 736901773
    0x105070315061d09040203070e0702070e0f01080d2102040f0e0906060607030311131805071805151204080705010b1e0111070317072102060417070b0a02070203 70
    0x10350010440d0f000c42c0c110038682c140004240035210001034400d981c984903550000566041001d1030510030745075a40074000d81c502c1c1c1107140c041084041d025181d02c0c200100184415040069450040c680d11715021310344401c1c019160b00345102d42c3c0816171096000080c08503000407080c4820f0125071020034441d0b515500c5102881d224041590401d038440c0b420841440880c2c420f403c40319264401159842c609a041414881601c080d43c1c003442030306600e80724100d11000b0b140b141560007080b40c02e01883d111608184030702042d86500030684503600842c1c8148114001e1402d60b600703903400140d032481608140c140a442ca0f001114110341d55030030001c00c41d80c0c0d401d098804c580403004101d88814404100401911000b21010700c1844610907080c000001c03d03a403170045841d40d0380141806503240c040341020582c80c62081603981c00c4071907120800c1081a80040c1301a40290070040b144c0b484000030762844490301c21303203001030700c413411060034050200b00c0d41c0c0c000c2003244c1c4220111031551103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 736904253 1250 736903003 736903007
    0x606051207140301200a1103190f090b0f1803030a2102070503030402040f1e0b010e03030708250f0302070f0806090d1215081c020f0d030b040e010507031506 69
    0x1181d40c45641540d041006084a44102c4c0c40140201030300c1b50505070341d604192800300b455904114000070a07600313180040c5000c190000010f41282e400e030719062051905021410815118050b0b00b4600000c0000d810010b41c4d40070300c141903e00c18002c0569981d006004c000400003100845140e0181c2645103c040900310188200c8040d00e074840080d40c03c5036103030380801000b410403030342800f02c03c1c2d21103005a0034000e10030702001c070040040c0f40001c0c2d0241e4050005080390141b8a883d17000e03034401c001d403401250004007035640768000e01c540d607989a51a8980b1001d021581a0004c007881c0004031020200754000c1150340a803a40c600c803a0410941d03c2d000c550f070340c801c1030710b50580c0350f00203240c1142c40c0c038418803803500f0750f01c038003200032800180d0f2008000a080c41c0354030244c410b03041804035144100d80d100f144403100ba0b251000f0019101e081c10065243c000021025040c950780c1d1b00c0700401c6481e07607040181c0680010008100d6482d207480d02030701400b40000301d40801f84c200b41c2d001c50341380c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 736905503 1250 736904253 736904261
    0x1e0418111903050606070b09060403080703090317070e0d0c150e06091003022106030f0105160806040f0e01090224180406090e100b010e06030c070606051207140301 72
    0x24182500e5401d416a8150040d4010a40a801582c0000040044c00003003218142c0c1c0078003458181004040300e00d81030800510000d0040c040108050401101c0030100381d01c1079000040c1c0c90038031480038040c0c448500540341c00d011000f46c1c5800c4515407010006205007004100c0884569001a148112040748105c8010781d20300319095000d4802c4c402c042c80c030700f01903c070042c0c0720340c982c20700500d0000040030101d1004040c0c440e41c6040700507101080001d06060080c030f0180100c17500203209a090034144031100b001241a110b0400c4075150010b805a072715504240c4a001501000b0400c600456205501030300c001c0100ba0f006140595000340502c0149840c2446440c85500c980e0400015a07602100240441026a0300513141c040118008005100b40140100f080e002410080780304451a4152460100b900c0e042c4581d86032030031100d45488044a0748054010207143c0d075100b691500341e00034030a13900969000724003030f8910201c2240010b610401c1e40c0c00802890042000001090300380c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 736906753 1250 736905503 736905517
    0x1103030307080a0b240d18050d12140f150109380c0c1305011a03040201120e0709060e090a02060a2604060e0a0b07051e041811 56
    0xd5890000402403c0150304c03001070b16600410440840d10241303030321161212560b02c088600d10f00007a80c080810001c0c07280b03801e0124803030040303071031400b440d00ca02e40c580410440020a0080030701c012020a001540a038401090358500b0f038580d424100e401c550200b1084412408841c90040303507105540c0641d403050100c2d0603038400940d011020301184901d0b6030a082001400c0d40191120b1602c410707110028002405a0000516542ca0b2841c200100324007503003610b025a07031811005004040c1c00c9881a1281e08001c2801c0c0e5a075144d520040b60038036000101190790130700c4d0800f440101c0c07001142c06411503110803000c0c0706480e01c0340b410100036001a03403900710551111440d4001810810003401d4002e0747c50411072004013203c0d4031800d070b001c0200b86010404003944100001c110b01813144101c43c074662030080c14055416a903135208400c0c050071010138040c010450190218040842d180320aa24083d22a155070b036030a950880c2d0424021002c851508181014004020082c00d4a081c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 736908003 1250 736906753 736906757
    0x310080f100c020705040504080a09170c210a060b010f1107120201031517150c1206060f0d050f060409020a120501060f060518150d020c07211103030307 67
    0x4401400c1c14650002d20100c0815400d501403c14002225a070304d00c9036034440d0b80596809996401d0403000141401c01c20703088480303907880c81003d141070750b1780010b05600c20920070354003070740700c0c4241c929140c803241c41d1b0403c8411288603420300d00c002c0040e981c0080c10390076003c1c1c8a24041c1c800030030b001d8600c0800440922030580c8903180c1048004c54400c41b0b4410380340103050009551003541c0900f008511036403c54002c1080c07001c281580f03140100b180da40200086e469069946c2042500b038405480350540340c1c549520520b000c40c1c0300d41c2d9010101c0300c084480104480c1d54201c840000c2003d440110b400d482d015600c41e002840d141031601400701d1982c1c0c010091124141002508020051080d0741940c00d0340d6101e0011034000b02c0e405078003000c0d1045d03072189511000703611860403109801c030303405c14080d1034018141102061030000755408500e00b00405616074000360200c5203800d0b15a40420b44200200c01c844103881c54a01422014501803000c040c85000c031340060540e01e00c030541d55400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 736909253 1250 736908003 736908013
    0x912020103020715020a200a0b0f06040608012d06061b06090f150c0311030601111c0e090708074113050a03110d24020310080f 56
    0x401503200764024620144110340c03021400d0310b4080c03030400700d03001184070001080c240c0075441040c01080b10310301d00e1202601e00803c130b24000769542100c43e040140c558240d03031140b2008680c2640d100c0d089030700542501002040754680000841d0f80c003070038140607020a00c20ba0a00016941814080c100030b44800740c4810180030310448031124082c0e1091010b498141d9078222031000100f86074110450140645400039408880005031030031191200d6403d4103151609450000d000481000e8a500803001d013040100c1c039403584012400e000800035000d0f144403da441807004241c010706035040820301610740c00c4d0b444e9070f02201961400d50994682c0c0220702d00d070383d05564084074a48072020345000e03a8280094002c0f1110b000250304808005061218030110700030200c80076200b9000c001f00381c1201c18220251a603110040804840440d25000e80d500240040a00850540551030080201d0000d00c2140e40c00d115030009410580c0c01c24040b01c3e600724000f070440350008540b0040060100942 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 736910503 1250 736909253 736909289
    0x120123040f15020406140924070b270f07060f0504081509160812030a0e030a0c1e02011704060b0d0503090f0d03300212040203060105030a121d0a080d0f09 68
    0x718124546210301c01001004103c0000002c540c000c0040c0558aa110003401c004a4a0bc40102098113501000f0603070f808072051101130039000840c030301110b1503030404844140200c10115042d10941d0410f0348144242c00f440c8200322203042c0058420b09034401980c40120201c005c0310343c110391611900410340c1c03288896000d100003640085400043e1003100040c0400c9060300c0c5d9042d0b411014004e0045100252a8007d218400c0e80e841190060129101d07014040703a400a030504080801c0c50001107850000a41044890f600c40008048020203407003070841d0614055540794040b0f110180500c15a5200400703600b04407003200c407203d90688400d00705500c0c0c2401d008421881041c80c607500d0481404000503014903100070101564151240e130018601130042c0742c90248180c0c0005d0103075109110070030116007038540040e480c03c601c2c5025040050700340c110640158074414150f600000c0c500002410700d40004699404200540399007110444000b000d5a50f090648501c3c1520032040c0026 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 736911753 1250 736910503 736910539
    0x60206100803040b180f09070503190c051c021312120201020301050904020111070e011202040509030403020f06131805160c08090409020310020d050402120123040f150204061409 78
    0x182120080603041c1ba0791050400009952034078141c1c2c031440030070000024032003031100a00b048007824041d47d806114010720881d00a18902c94070041000280d24445406511100358046403980c42c0d03201c014940f61916424010803c0d00c03070074021a401c110240f03401c1c282c94018029a070480798020803447d8141d841e60015584015100c2841d8403a024424000c01c040f0b64588049000e40401d030710084050485205001c02c440000c1c2c40084030b0ba00c240410030069650320404507540900740c074050f1301c1c0e100b1200c1c90301000320741d0341007100c1c20410110260104103407684000c0c840e01c516004c51f210440c4002050f070704441c400d000503064a034200103c0e011800c0076048801414405012958001113030802d0703608076000803034002403040e2240144802d620f0070389014155803006000802502215507107050406031200c507a501d00e0100540050140000c90b0146642160481101203000c00c488030104001e40c454004d2001150088620040201240301130b03406c103100c060039040c9000d500c0710389 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 736913003 1250 736911753 736911787
    0x8040617040f0f140d0905100e03030a051312050d0f030e0706140409090804030b16080415060801020a021006060c051015030c0e090d030b030d27060206100803040b 72
    0x140c0301d061048490204c00e40003000b070307130700c11820070398602c9000e0b070400d000c00060703041800c000350411410180420607a900170048694215140c104959560756540580c48216199030146207400705080e200d800340f01c800304401400030a665203844e0360300c400617800d40840e060420109441d030300a07581840460b014203140446e9404c1c905166050690b29070000007601c036500300440f40550007182c00c00030491071002c42074024000300340e01250801403006c02000140024005844084031a001d03007030a82c401d501c02405010407400940d502c5003402c4002c0d5072118005040343c0485c0c03804030002482da01c100805034206070700074040c1c81841013010039000170f44884c207440d407034442483c1000000107207440100700003056418959a041d140110015040030701070740542d810705041c00038070200f9542c04140e4403440502401c26410601141501060303010b00224a4041c0310140c1c030000c40d05940014202e845030301011054008191110314240d224043ca21502c0c001013401d2050300000010100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 736914253 1250 736913003 736913033
    0x10807111212010902040b2d041235091503040c0e0108120703050703090e0a0902031b0d14101b0e03010606080114150708040617040f 59
    0x60001055205001403030309191039007a201c00e061400180d0022075040c0e40341100d004003180755007103061074906a01000703148507000b40004c20700341020b0301a502410700d2052001c403400c20104144c0392515104021804142680c040d55800813501040e20f9245500445141c3c0068103214004640d01e8030366620303016089481c540c0d900214042c0c003071a240303030300d0000f451041d80545e810f2011a803910040245051068004410540001d40703004800d0929604907207103240d0501e0441d9030398060307041c203e403040f00030f0704008059882e4a00744044000c0c140c01900c80f860084041e00c5030358282650400702c041d8014007190708218523100280c00b25614130501c0c084024407809a03404400e90740d24010840368080300072031445441c40814400c482d4017580703503000441c05078002c000c0c0604200f009000494140718001c04071001840301501500c83d0501100d9401c070030032080d42c40c5c20310b6151a040c07a811078000d060015514825201c60404800d0055000325000760541051070707116101c1c0d101c1c00802034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 736915503 1250 736914253 736914257
    0x606021c1b02040f0f02092407080d0209040504060b042306040c0c061b090e2e09020c0a020f010c08040306090f080c0a0507060216140f1003020306190e06010807 71
    0x4091145004135401a110300c07801518005940d40008410080424080540c07590740710200004440801c41000031540d0303042e04051905d4554424100d000060f200e1920b4840c0c005d81400180000c204460b00b00c1c2d8001d2034200c1d805d00c1400a00c000c04103009021030941e60038a108407006c15124185980304032490303c0145070031050302c2c0940c0c5580050780ca100d01c8003030b01500041c442541241d48501c1c5080508114100034049041460031401079a0841486240c40303d42c000081144100800f1150000c201761403007992626054840e20342c465003014406c0c0d0080d042410314001c00d61103103070981101c0c0da001c8006420581981c982ea001003a415104450104642440502003000700c0007600115880390010010240c0030300d005030800d1113070b030b000a095500690542016401d200301e9101903602840c0d040034040c001c0c02c00101d134050300d1000c0c00e4002c0c000f40c4200c00c40552640046204030402c1da03080701c3e04080c2c55045001c1c20078900c0b03040f014484490201d5400d42c42a4010341d0480c8841c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 736916753 1250 736915503 736915511
    0xa030b03031309110f070605071b0308040b060102010216060506060403060f0f0606020d0905120307301403270f0a050c0a0f0501050a03060e07030606021c1b0204 71
    0x16101003451680b08580907040080c0300b01e800c00c4040c4450040807200602c201030103007421015440d49110b400f07441c0e00286074130344400005010500c540581403452800758802d5a241029080c09420648243e44c00c1d50240300250000f00c01c0c0d40140203d40306003004803030a5a04811b10303118400240310250840358000420400040450b640b80500c0d10362a50700b10000500340c13039070403e5404450003a408601950002c01d41c04450940200304c51046890640300d007541444030f141d526003184a1000300500745051a561591a8005504d405034101d640b40c602c80c0b4020081c0105403100d030715030340840545030700410004825400e500c182d8118007034260003010600044c0302d8003905144004504000396071240000c1d401303108081104001148058611442d034909007030001e0580107040c003d46040c00800100c0054607482035001d00010101400c0071216410000c0c07004016041070722030000184280140106100806101190010f5007501d45101d401501e806282840307250000c103a03800707130f0b03a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 736918003 1250 736916753 736916771
    0x4050d1409060d02040503010e070e060411040314070f060801230f10030506150f0703081e0a06030209071d04050907080a0614090615010c0f0204090c0609140d0204020a03 75
    0x82c081c007070410610402c00250301c482c24071080c1821038582c1140210544d01041c0200701408008030b101e50040401e44001ca101c0c410202621103600c5140d000910200c04446498001d58011641200b80c411145420300081d030f40d004200e440410a02442103031100c18101040c034850101803444840d18081c2c0b00c0f908646615000801c40074102502c0c40129403a00208400c502c1e203940b0007070221807c0c0300998144444c0c203001d440c1034010100d0040500820b03401003224030120b0041c14050301102c542c2907110749441c1c03100c100903104510080b07000300954004070b294136002e0610a45c045611191030245800e80c4e1003048084c04018140f5030907401014000700b51482d060184845041c00b85601044d041c034055428001d1100082c08250030360004414881d814414007401d40091000b4a085000300750281000b4a00c02d2810500943c41440c4c15002000c2169490300d280071a055510764841040d9202604843c1e0550300c0821540100e071408410b00510349a4040c02100500d0b10700002e020344 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 736919253 1250 736918003 736918009
    0x6150906080c07062a03050901020c030f071b0b0712210527010608070501050c03030712020d0203070e030c060a170406020d051f05010314131403160309050904050d1409 74
    0x15501400e005020040174078444559054081d80c1e4004d440074000b1450301001d110200d4a0f40918400c07500702090000d042400c2c043e403403003842a0200d40c62285010703140d4401e003809065110103800c89201d004030403c500480d020703c00f90750a010003a10f40c0e020750002c0040b030400600d001845074894040d0b4001d00e071a00c8010900144600c45520300001d21a800c0805032031800c1d250f0f5029604000d41084030720802039010054a40103031041c101500402c0307072890f9082c06400341d0780200d0002c038408070811862560102e10880800d10903404d4580300e0390460b091068a10800036140007203540b0045c004114840b11104592181c0102d07c01400d1091400d01a416603a0680d118a0342040f400c0c030090400780403018031002070109003401c101c43c1907071010926980d00000c0c40034148180c4a154032080c0810000c4038005c01d550b20017500d81d42e11110101048031a51310710b054001800181021510741002e07004140120740213401080520005482180c0318481c481d19800514020301c0240c0302d43e1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 736920503 1250 736919253 736919291
    0x60801060e04020307120e0d020c0d170c120d0c0f110712050a1509030f05040303021e1c050a0905030312150a080f0a0b0a1503020103110403020a030606150906080c0706 74
    0x40c0407c0142268011039140285807290440c42e4510901d01c000603030f800500d640030307044071241e80300c400030707449aa0a154050800d02c0d211003c50303000b00c000482030656402640546140d594684801a400600301e01c21034000bd80b1042603029130b48070b01d60911102074159051343d00c181c441e034211119400655a28103e0507804034440320015102d292070010190000002c82d50b424042c58440c2c2403602e1510300a64034a82d07200303030030f0b0121102c000c10b55039030006000300d402a000c0c44495807000c1c1d41039040104144e1000780941c000a040d100041002e02d00482200c0c01c0b114002c1c584509510381024070085a10b10186c1035a01c0407a0050009043c01e00703010345014818100080c10a8801c9030600c85c040c18401800d0500c90381c9011603809825448100350340c140c3c0e80a00c0d000441c1e142c404103201e03041c403903600040e40c0060941e400008000c9190044020380702d0b1400c0c82e044650041304182c602891038040c10300440c1d40c41000800005001c4068804030380103040c0800c01034a403640c003581c58 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 736921753 1250 736920503 736920521
    0x9060706020c030c39060904140a0501080106030807060510080d020d030b0405010e16050c07080601140d0803040b09030405040908031e131401140c13060801060e0402030712 76
    0x5030008541e440084e0014404103a503030003624013034001c0440b59000010101c5110381000701d210703d2500c088040303840304025140c00e41c43c01340023004014041c0f1214100c1c1c1e641140c100380c0c154144000440c0c07101060107a50300703c2f030340484c40900340710240e99802d02408004200e54402015801d002170058810032001004114540281c40011a4060001c2c00e80e00c2c81c10255010703900700310042029001d452000c03540080c5042c0040740081d243c0c00119054451000204001e2003501f50208142c5e1002c6144c504071030034a55008407020404003801505200d030b4901400705001800010003240221070921340c070502d50800d49103010303194000101280c002d9402590200700200400444880b441c810001c07000700060070355514605032a82c000241c0c2d00c540c0040c002d10074200c150003048000d400c54a02d080004208241c189003151b582103040e0070040561800d038060b079800107440790050701d005060350b106580701c0c50f2442e002010b00000c0e600c09071240c01041803151070951441e245209103090 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 736923003 1250 736921753 736921777
    0xf0b0c03092d0901030b0402040f0b040234030207180e030d022d1e07060501080a03120203010b041203050c0d0e030f06011202040c021509060421020a06020906070602 73
    0x1035245600c8842c1100e40302d03014680038803003540040c0b000c1206414100c4d4403550407600400d502c10702003120000b80c04618030b895005800402c52940d610040c1d142c10510360740e008403008034409015464101d001d6201009405038006020600402ca8007405466a4003960280490300f9880c40480034a10740c00411010170b03007580460102c80d03080e92910466242e4044641e410782d205101c891190312840350000014203a0f264114a4040c118000252084140c025400f0021982d40b10b071010b0b21200038a004400183d101c0203500380e1950076100390ba0580d40c00c01c2006082505002950394075020203101502802801c0c07010382c2407240b040004148480c4c8903590160120040ca06051030030401c06090250754100303200501030b949007504038078022a012900070900d0345407603e040c5d081468801c13141000401001c2044243d42d400a443c0e03001d20311070480300221346240b10001a0040a003410800143c1090b002103020481c140c000d07085042d40201098030384280d940c0e4140c226801b00d05c071008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 736924253 1250 736923003 736923049
    0xb0c25050909160905160c030801090c0e0301050c070b0c03011211060403060f0b150a08040615080f0105041a04030e0d0c090603050f010510030b01090c02100905010905160f0b0c0309 80
    0x4071385801e403c06200c086e59061016040020740c0e0040d05044050040c4a80349588442038038042e44103211500d120b88001d0003c00050a201c401001181c2c4840300540721190f0b007201240c600282a01107074100c0341e40c21949842c81e0b000b651140c3e460103011107819840030b010720001c808a54107105a20500c080d5081c00030350444c1d48014084d8507491034000c480d40c1501845078229a5401c8a03070190311a81c00540021102000c3d1400d00c2040700b40c0c1c100c0322440c800c0010340c0d61b80050542c050f6000e00e0281a01120f0441c9485610290a408450003400101d20351200d91040c1003c900c3d1080c1c192007100554521a00d5024039003c0301c0d03032a4810740d00d65204030031401d0900300a102d125081801d05000c00c40160564480c3c040199040c8100502d06542e0680c400545100b03000415192900d40d0041c4001c80980c10110301030302d112101500c140c00f400c01c11240c03642444071007000b22051454001d03e024640043d90b1241d4210303207150070940c002040714074096600c0309030945020b0001e4050708 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 736925503 1250 736924253 736924261
    0xd112806240501020105070e010513030b07081906050a0332031b07080d0c1509030507060b100816030e1501080d03050912070501150b0c25050909160905 67
    0x1981001d0180d12607030541e4540f07421300c00201c0c0d1103401d00c0c103440b0f0282050f81e41e0740540304c00c4840b400240d40c009000404c44200780103c0c10740c040286800340b02804656102408090003031001c0320400e00c06c00f07a01c0b00c1a1031007000010310358a035048690401c4041d82c01100c1a100c4001c4601d07414a25100c11038000113240076058840308038000549a0200040c020305043c00c3e00d055403081042503008c10310000d075080d5410840168a1ba8014001003041401450700900d00030700150005002120340700c0c1407068500c030342d00b01640c99901d420f40c1607403021001c2c2c864104089000c0c110380580c004050300c03102d4400000c03604001c0b840030702945242c2c05585614000310982080201d104500c201802d1609000c12542c0c005030245c00c00c4006140d45540303102c04d203449801455010704007905100f80c41800182c0c004800040c14101504000360341d118001c0280c81004044c165a11503145c0b100007c040c0094140304c10304c558040e90203402c48001c0743e40995003002024440c3d11444e85a07031118104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 736926753 1250 736925503 736925561
    0xf0b0106020d08091b12010216060c0e030604111c0b0a05070f0203040e100e040f05070801090b010308030a090b09030d060509060303120705040b16050d112806 70
    0x51118629500d0303c40810b090042e03596846119101307150140d14004c034281d12041d03984592410a07040490300071035940382c40c2d41d10814185907809003980d0f0940f4014101124a006806280c101c20004015206070307940c6680d0704c18682405000d16070000a40032030485807030440501200041d0042880c020a4585a1300e00015140e0060080c820080d0300c10356000c51607000411f4500303464408401d01040e40c1c40c2c48000912100c07503400a80c40f00034181c140014003510042d48600c5501490684441a80b65501c0300c1c00d031843d1480082542000100400c0030403562805150000b1a41502044400454031a800741200a1382c07414510741001a02690842591040f40000d10081d58401c1c2c2c9840c00400180c1c480c003e4070722541303c0080000c001b40400f8451021039003e4080d1261081e1640b440e1145075643c825024800c0f551072040801140c100f0380913000c0015149200002031103400700d05040111005c00b801002000904c0c0800b0680003d00140140e2030368008445909007866940040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 736928003 1250 736926753 736926763
    0x2040504050604020901091401050d1406030105090d09170309060403030809010501090b1008041103190501060b03010308070318030c03150c030b0a060c0515010305010b1201060f090c03090f0b010602 87
    0x7503503c200c1c4100301140345640c000b2007100890701c19084080d5080d80c02d45c0107070385500c1a4040c0c401040e18061140800c0f201441851380500720940003080340b551040d034441c1d5140c400c0e00315130010401041082020000130105040c08003403e030700792030400720f0f504041100c540040e00308401040703c07401084078001003442018010040a103050005030104800301d01030884044802c1d041041001c001010f002c08100700310440600a4120381c1c0e8080005d440c0780b80c20703908003806c99281d420b001d0000740108841c015039041c5d075008440316150400680e015600f0000b004d1018641e00312412000012650511070300c0001c5004402825000e0102e00d002411601d0f818100030500d4504030281d50a900e0f0a41104c045c1c4002e4102400304403c10b052084ca80205034103007461200045001004002c81034100c404041000c1d03840e01c611720303400031030113003a245540200c00d8482c800c504c1c200003089080c0c200c12908070150400007a02c500544481c5a40c0b103114070300303031001103807500108170103541000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 736929253 1250 736928003 736928011
    0x40525081b01022a01030207050309030a0b0a0605030c0603010603021b06100303090626090a0f0609020315010b37020c01391b1401080703020a021c030219030204050405 74
    0x10b00c000404c1c101901401c9040d804890301e0b0401d070f80450007404022080085610694004080300c00c08481880d004200f000704440e1aa2420b0409500007281d090000c2c84400b9120000c04103802c580c20450224000d410100c8403150a808082101415507814000c0e1402003800c11484078000c0d0541c18003030001101e50340403d02300710712040c000303907181010501013541c41401007001c0d141380c0381c40000038500f509064000d0400207850415a0400156920a000051080c6e050303484450090550f100840001d20400c08048003c0108010207010b880e2004446248040e06a0101e034800f01440190400d0105071400341e40580e81083e003540c0c02c031242200c5a0143c2c884403a06116a42640d40307246680d031116000c04224450500400c42c40d0f0700c030074002ea800080013000c480d60f15583c040303402940411a5002c0381c0341c1800310748520f10034002c031102c0c0502500208180484090750707002c00490030106000705030b0300b84810041803c0b569000b1034a000265800342c0c5850503d410041100e002030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 736930503 1250 736929253 736929283
    0x4030c08101a010f030c1e170a0b01050d051b0a020f011d1218090c040e01090c0c030f140c0309121902090a140a02071a040525081b0102 60
    0x542e064402da82d10003410300144240d80f0f0007007100c1e1000002655a921411b100540e80102021951840c0e40c0c0b10281c2402003c0e4030f141c15989440d0120704400301c514584101c3d00151040254441449654000075080004200c0e110304203003010301c06c1000340d040030720b0340c20051700440403840d25503030240664241402440701400e000c0400d0b0703112035668600c007010034018100100d0710941c00703000b482601d00c0503c0c000d411351072145000400d1501e107a01501403405420b01c14000410002000d10548200000b15213134140c4d0301040341c40a54040e6211044d8808110580120700608056a00a04241c0034044021a15801e01c04200305801d02048690000c0d80e10000b06c51000105002007101960380580e00c3c0001d586034200c0320005003214041e2443c0b014021028001400c103a0750050424500940004000c0c3c025160a240202c80c10f6401400d0340d8401c02a04440f0780749500b0702c10074500c85295070101259110f04082c201140b608040c00521b0104a9200d003550701030260101c011145 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 736931753 1250 736930503 736930541
    0x3030d0f1b051606020d05041b060804030e06300a140402090f341b1a180a120912080301090b0a0504050a090215071109060604030c0810 60
    0x1c900003041c5000301e600007000c0381070b00c40700282448859812650405000c0b002407150b0f244c1400e1048000c0841e407410383d80c03003460340000594039100b000c1d0140585d505a6a0744422850b01e8100044c98115244030340100629214104d4002c0104120680300102c49800d04a0b80c94148090301c21580c019000060500004003080300582e25640c1d181d80c0312440d06403000340c0da2a40700401c00b115880015801d60a058070450704881660324019800704640ea940750b400c014840103400202d003104a00040508070385940701c1c000c10056002c46944a002042d40c1c03400b038901c100c0c00600c0c02e0094a41982e85407610b21070040c4040d17000310b00314040c16801880c1d500000165444245e84c3c44148181b0003101c0d42e80e00501d50569504044d0402080300420a000906150221000402000808912135450850030030144070740002034801054220050180700d0780031500340941d0100c020b0000d03038001c1c0704000100c0000c00d4041020094090a401040a04d080500040448150008402040440d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 736933003 1250 736931753 736931801
    0x305010623040c09051507150e152805040213020a1b0f14100510082109180121021c0204090b131a0603030a0c1103030d0f 54
    0x800ca00010010009031000158903e814108456801d51508501d51040724a00784503100c402c18070140821500071030713130114a00448442c40046485001e2640781c1d035004148481200103109185130b900c03070115841c0320344c210300f0122008040340e81d010785030164035a070b4004d00065007840e40300c4070760700501480c013149420083c0740041d001441c00d000031260040d40c0070b4010100600c9a0300c40c142ca5074880f407184c500560a040c03141c2c0b10003280c11049895450700c000030b940e814087c1c114400f280c0201000d4021580c5105106007091440a0030b0b00300b980782044034420030740710402c0c000043e1b0401c803400d2005504154030aa00f000c198036001c3c0c540c3c458122607101603903942c4518048180008141c08140c142440485c000e4111240007030007126000080003c0202803c403aa81311b20711030007008039460025031016110441c10b13107891790954006c0c072400b800380d0300440468100b68010347d61800081d00e9440081e10350391160a2201c00d4a480d207029420707903a003034000c200007a40309885038280128 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 736934253 1250 736933003 736933049
    0x100b09060f0621070f030c0e06311202031501030b0a020702220501081203010e060108090708032d18010e0103090c030b07020d02030f09060a171003050106 68
    0x10302640780c61081c10000b400c961039090260185482d1142d24250f042c451034444000b610110190040d41d0200b81400c0c0744180103803246196404404004040354145210b113595440f100d44200c400d0b134480601d0044240d0072080392042e9600901300580700c0001c0400b14030505042c50305410784007426010510050000800c03950015512600e901d1317006032140c40500000d52550024203440345504c2d0b41500034490070720540c02a5050b6021a001c5810305221400100c01d00c0c0310900c90b00c040b43d00c0c03840120703585600c500b000d1500040280c0407a54010707124038543c1c2c20f40d442091201032602e400e460064011042110118900401e100f00e03509004440c0010840b65114091a50406c07080c50b0054160703a000342d1241c10810b03080341e07491812503120b02d0070150889040d80d0840140c03241c000070300300c410305c00403c556201c12802322890070841240184801c541102c60050203008550050340b404d4001700d81a03922400b40302d40a000c085185052090841c1d085400440100c85004442c4207422 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 736935503 1250 736934253 736934269
    0x10e0f1b060f07050a03031a0306042604090e060105060f1207200303090f03130e0702030f0f07020a0801020301140d0602040807120c150f0807110f100b0906 69
    0x5116110390200344569140041c019104112003518040d0000c00c0072000d100000520b070b0b140500c2a1410820500a13210b031008070019950310940c154000300000c3c0014080c0d81c40840c24525041c100e41d0210440740340c3c01305d15002034108260107541c8001a03c3c441d4000c100c2140141020f8a1603481d0680512101000340b051145019181090740e001c52001032181c0410300c3c04112440c80031220080f20301c6c2042d200d60065401c4030380c1d4400d04a110928000108c00c40314400c0608202034009480d00e030300030301e2203c4001c0c12001580810b03c2420030751070845c0020803503071103c000f00c00d0366403c1c64410419010240d8004503101d0707106000500c101420450206900c80c01201e003402c21502d18580308010b03206681100c00ca0340149440014465042c01b039103500d15220f110000c08903900e0f10550a08a03240401a02c006401030030320300f015a005003003142d084040d500d05250131058540302c10349481d1748400500065404100d000c110003004d0320851040017400c5a24001ca82020300c0003408031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 736936753 1250 736935503 736935523
    0x3021606090320041104081b0a0509070507050a03081603060b030a110c0f0d0815010e01030207020609100f02070e1006030c110a0602040e0606090d15060e01090e010e0f 74
    0x1044009550141107041d865049410010007001030044171074185900d440d9812070b1080407428031958400501c0f500403414103a5840318050011401d40b8940070412042050190100701408030412070840440c0c001d2060114440c041d484420309420404981001100c090003260105403400c2c0c014482201c0c104200c0741c000c8846400481e8181d5407502c80c5a8611608603100d113103110303241d03030310020107408142c0032003200391620f5184060741d510018a4180e100c403103030513000400541c0c1c0d50301c156010b136020701041c7d40058801030410960802041140600118200215580301200c000441d8108012009020400c500c002030f0b00b496a0340d41c4e105a207500501d0185515140b042600d24464209040100c000000320380d010a5141001030003903005001d000c1d03001080000144079410524200c80100d1005812121000090380355601c1b81c0c200280c1c0501c6888d200e4400162040b07844850b980a03011030000005d201e92080ca086003140e40441c4078248503004840c440d00ca1a10108443c400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 736938003 1250 736936753 736936763
    0x106020f070501080601091e15091d0a2c16060c081e030f060a05090103030e040e010612061b0c020105160804170d03061a0f0c0c1804030216060903 65
    0x130507207a010069590388080d40182541511207000f009070f16102c0b000100440b01401d140e43c0201d00d00e00c000701c842840c580200f070904001c4140d078220304100d075440c00c0d42c0f218072030720b0020340460900940c0c038240c090107400c541c6001060015803005c1200b404142000002d06095050842c81c0220280c1003882c01c40000c4c02100000c100030444016081d90302c00d070217400311100c41d96841c02502101042500b940c20a000306004c000104060070807001050680350151030b0503191303420711000c20015080d0387e0b010180d107549560002134890140d88007240784510509021584a07203003400307074844510004915041040503000703040940d0b000703c200e803400ca1642042c0300302c0e0030003800c2140c15403080f41c1c40550702140e0800817401010000c02c0130482d00499a0741803203440c1c0d41c0c20040a0420300c4080c4080041e508002c039003002c1100000402e00844080241c50b4200d0800703001504208695505d0311107000c60300200020564103011b8080320b0300b2050100c0700c040e410888024100c400da4000106 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 736939253 1250 736938003 736938017
    0x21b060709140105030c1204050a14012003330f0405041205131d27030901030f0b040504030c050f0307030c0b04050a0c0308041701110d02071712040b0106020f070501 73
    0x56105046c0044171065a0000100400707401d29142c101d5440000a0307003658046120b00a00c2d501e01c00600070810488059060003200f805105503080d0039138005000309100c05220390f6020303058541c6101c03401207000c459240b0b28042c0030003018864404545000729109034605010000000c079801d0b01c140150341107107020394440c548140e48105598990f00010980340e0161000d810501702141964030030390145180c503c0c100620a0071a00041d03450750131041c02c1d0130074032000036154402da12001c03c00c16002404141c0700b0700303000820120303101138900b940014160801c800c28031008100c0350301c0350300007500110b2620348182c40c010009110080c0c000c1c400009000850144a8104041000203410280001d40e02d952494419503030381c05803007010071035a80310196420548040c42102109040038004602d0a1008002100290b000c200209c9200216107400410402c40c000546000158518105440d04040c1000455010141c0c048011503000b620030209800c000300b0761000300c5100303003040c5c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 736940503 1250 736939253 736939261
    0x21b030a032714011b03230d0f1d030a090e04110414040b18120a020304120606062a0f05011b08220209041704030204021b06070914010503 61
    0x680c1144544a50041c051040c2000301e82e40074040d041c111044805d80320038600c040340000e0140030304006480070b004100c504000e044841d900d038a0f40309441e40c0b09482d89141c800b404c1410400c44080d10b0b020403025507a284d0529041110100e640c22030082440158100001404010700c070740700034094810f03002c4481c40403408000703801c3c00e1541001d0004006100e0318100d5026501061002c03242075a10081010200b176101404000c40745241d0840343c082d140d42144c41c0b101440540c043c00340303a000c5200400c00002d4544101c8100c009662203110302084640c504800280074a81d42c5000c40b046d414801d00460240081e07a401c0400c840e440042c448441d00c2609025004000d00714000c1c0020002c418041c99070391f80103040e0b600c104403414600d0b4041d200b2441c82d14241e811400000e42048000d404038006c101162081d0402c0846104602c0c5495100d6002c6026600032a04070b41080f0701c10351304201d0020041c004550f10510910b072020301c89191940b411a01c0503403052041c18018000f000c6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 736941753 1250 736940503 736940537
    0x12110301091203020c010b060415081f031103031b06040501050a181e12030e120a0e131b051801020c0105041509050d0506010f0603140103032f0c01021b030a03 70
    0x11508244000b468247ca892b6280700101d1009115590031002484810010300115044802140d91100300b40141304007a04695410505a000c41080c03545840b0902035040b10350b003034450800c51564500c01078220750600e4980039003900c5020b000603240303a04284100c0ba01403503120b01154060380000020002c180c10725000b1301c04884406026007503108801180d001181c00d9003001030304d10240412500c050000e50b0f51131683e80180c0e0909030014030703c901056004d16014010404c00074040c0b07400180441003c3c1e458180d46500d060340004902d001c12408003101c4610101c0c0c01d49042030014182446206000034404e00c202d014000d4034842034042d14540a2003003072014003809000c1c0109460503e00e0a080303a40d41424442d15420034080c000c04182d41d4820b00840441c40380c50445010f86909603a41680d0491402103000e400c0381954240b0340296010440c40c10f0000032100140c405458100c000900340408080300301404034a030a4142e401d61400900005545e405203003041da101c1b148082 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 736943003 1250 736941753 736941761
    0x70b060f0d05010f0e0d180603020c0708010e2d0d030509031606061403160306111912060b0c21040b0408010203151206061203090a12110301091203020c01 68
    0x1c050515840d08030039030304070f0070303542d02118442d1132640031280314552401080b240c400608440b1410042602405c0005078000d802400f03039990060305031110503880d15100c1e42114056104480d1507400005032130402d044062100102110040384102440240a151036a4010300e00c03a0f14105139542000426510081c000c1d0340782603e080c8500010301c84ca908080d0040c080710700550000f202c0d62543c49829140000f21b40c1c100040b01003001d4541741c59600c409000700344126400c0d5051104101c2100f51040c0c0205148000c1308a4456100341c030440f00075a011542d0503048040c0e001000c0146007640c600c00a016501120340b95036190701000c60008410343d0f03000c1c2707910a40110002040100e0049019005144140e105000601400d1340c510100910300b01104649901c5401000104256050120850700342c00401401c903840c1403000d5001c190024401e82c840c0d60610301412092080000c8085c85101210044000348125012915240c1c0c9403010301c0d00000505900251501c80100d007904 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 736944253 1250 736943003 736943029
    0x109020301061b26090907050306211f051b0a0c0602090f0d080a030e010501180c03060b040b070b0c090f0915090a05060108070306180c03060b191103070b060f 70
    0x140100d11650081c11415040044c0643c401c201840007e0306140c80780007030300c1c031400000701501c048140300741100e00f0b00481c0f141100e820f0702414180005d002a400c00c1082c107407090706000980c901d0321107101174800340214080c02000804200315580c1c65400122107030300e96000440181c0d2244454001000143c03000c11594100140044001c284001c81c40a0501c0c01c981d602c0510100f034054804a00703c0d8024020030b44041750079456440501415032242c607001c456410009001074540c1d400700900d80155200c01c0b1041c0c0c00003032039401c02519080710303030300401040c6180c0c0c184104400050080c034141d4070104d000c0c0c0500000200009002d0b84914207840c4003600144c80390602400b460b02406e002c403680d1340031500703080114490610921601c4100c0d80d01482102c1e0045240040c0c4014001080d5910101a100c84002c44c1c080100c1d40240105805882e602100061800780a0415030704120f0180c082c0d002804810081000848080c0d0300c60340898141200d060017400241c080050340c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 736945503 1250 736944253 736944293
    0x5130207020307081f05010f0303111f0c0e031504060e03160501061d06030a06110403080d020702012a031b0b07020106031b0803040e0705040305061306050109020301061b 75
    0x7640010880e00100d90941c1c400000e207140302030b8602e41940c040540305c0138400d000900c04230580c1000884d118048402c0075003280b5082e100d0325840c2c05514801c3c11205000041569999503400d824550044104e00310458103a0207000d2980f1480c0c00078101c000700503c007a0810b500e841c0b003d40c070303001c043c0b0840715500c07141d01100010007500d051843c028074681c010b048039104008100302e0b41c40118002644120f500800a00d0f012205513248000340420b241c440e03102035402d100100c0000c10f038101400410f081c0c2000142c82e401c0b5400010b15070a007459168030440c419094020024034284060704640ea01401c0c54854041e0803040303036807000040000580000008014440a10707410f41120f421030f405145001003189118110608602d601e103d86440c66200b04020804640c1d0b0015040d8003000b0390501074105540e940718a400c01c00c2c1140d031043d6081403002a0b070200316040c41581c4c0074110313081045045606041020300b010449490308621030341210080420000514841480202a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 736946753 1250 736945503 736945513
    0x906080c0a110d03020c0c0105090904020d0519061401090902031902030309041118040209010210090c0b130f09020708180a0312050417210307020114150f19051302070203 75
    0x450303c000e000f90031041084c00c1500802c0070441c0d07598460001d4602e840001810803219403a65820400104d078a0942107446002d0108014034081c0c052194a00e2280111400700c1d802081328855064004160880c0013014a4440c0310b1026850020f000203070000700303c0e92440010594000079245008a200040d4414200b0044c072044010700b10142c1407180c2c041c425003440c03811140811081e800381d0710800e0300607403202200465800c01d68000ea02800c2c007941d00d550a441d20b81c1c12540c0c00d980311100903082e812907000d040103407a60901e1201e006000b40c030411030501d41e881d034501c1e00c248140404a685020036140d50200c0350343c0c1c8000ca400a40e071080c015214005420f4000e005074200744107182d0038014602420000b00300c0410100d003c2d441c1f10343c0000d84942485880f030318035000508004115035940d10700b203030180341040c00c0c03d002d60000941110443d000400300315102c200b034101a4019034000818411000c0031500400c16204100c410441002c840e2080384001c0c01100d60103940340c452 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 736948003 1250 736946753 736946773
    0xe09190c05190c030815060c010f0b09010f030f142b12020306030304090c050c01090b01050a0b0711010f11150a0e07030305030a050403050c1510060906080c0a11 71
    0x7034000e02440b0105007111096600c55182a00d030107200c40310250101d0341000004002121003038882c0311008004201d40d0609001690180c01c4a0002c150545c0641d0348510700304052610b0743d041c0d1300402101480c0346103241541d44030302c0c200000210003841d4509990600040c0d07041070201a404207405445c5800702208030312801d0519480382c1c607200110782c3c810108c180b80d01c12030088030f00c90403000e0001d40ca000d02d0080603100429401040b002003000a200003103c40000707006488110b401445401e40b03950418041101805039030b4840707540070f40c041200f180000c0301c0c440007001c0781c0000d00701072501049049080e140c03007500b02454600c0b0700400382c1d404a00780c40f603085a0300605041c501003042e0200d0b1549a40c0e03070819400b02501086041c03000860f20001a00502e6009100c5c0c130704503003815500000e480c5071490603c01200d40121201c20002a101c0701d03076201000300f080e0f181c0640d040c1d1038150301501902c0040d00f0000700c0d002c00070f100b0b000c0740e01401802c45040c5d1400226148440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 736949253 1250 736948003 736948007
    0x708180904171e130e0c07050c060d1401030c0e0f060108070309021903051006151407263105060d060b0a20070b18030f120c0c030604030e09190c 64
    0xc154002c17005103616250104d49041950003d40b02c059a01100501e44e0f80750a50070000f080e0010054124160f45410407010b940004a0000340294803461040ca2000d080050b59140b42000030f00402d01542c0c45010000c2aa900003040c40d00151103040010720748151b4004500048044400da1031006040741001081000000312100040600e10003081103680317440c011804800046103090004840302c0803070b40d6100c00100109901c83c403c904802c03400c0c0702c40929800948440d07060784220140420340e8011075181c40400035903071280c0034042040422400c800300e0f10070139900981e07008000c003041054048515900c0440980f642c060440e403034900c101401400f10301d201e0703070402041c00480b0f00c45403408d42c0060075005440c0556a22420080410104000381c0d242402031a0300d44550700c00301040100520100410381408660103039911400d00c0306c02d281131964500c00c0d00a503c03000400001c02d43c004401940749008035101d241f55190082c20032004c0021102181c00245032a4001318625 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 736950503 1250 736949253 736949287
    0x20910030209090d02062e060309061401050303160501090b090d1229010509040510051e06120702070f060804030f0f0f050c0109080708180904171e 65
    0x28401c4518400e550343e2a00404d03102c0c50809a02c2c0c016078801004940d01584544440d4889a00710040c00142041ca0180c2040304070385500050200b0307690080c0c002481294002d0054000710040584419403601010964920503103010101100c5441c0701242008020b42140b521a6000f201d50030381802c101c0030150b00c42c1071003582078010030303048254401081c100d40600e6500c0301c01c1800460360482c50f0a644a119284054203a04006041203010306907612441841d000d03502c07140e0111900ca0502d81400741c19000c11445404500c0d0745500404034ad510801200c508048aa2800c0380075201e9810030780c6820718a410010110410020105000b039024800c01d2003035010390b48a074811042203000351140c5864100040000b002c4500085641e8013420007010140c0c0200000100d660036074407441065045064115000743c0009000b1846c9110b0381b80007019840300301d40510940c06c00b6501c01800c00c0144c0c1c1950030140010820703010b46050140c8c1d0040e1500580d00e0b0503600c540c1598405115 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 736951753 1250 736950503 736950509
    0xb0307020316050d1b080910050d020a0215070e030a3003020a030c1b0b04050f1209150f0d0902060409110304021e0a0501120f020412030909021c02070f020910 70
    0x10007140005108800503e086004035401015041c47c02c1d13492420b012103080580c00c0c0e030060040c01c03c01280d103e645071004003800306865024001402211030b81d41003030207015018104000045203d2340950f43d01240c540b0540364001500e20b040d0040d5894030381107840165000c00c5009861424841558050b002041200529a010010f90010340e41c2600e210106000340300b6801414100800083c950341040fa070418000c00803a075403a507202d0780461405009400540980402007102c110301c1c2023641182000c04c0e1250b13044c904120607200d40e0080c0703010b5203281c1ca0300035859091103025910b4000448000d42602c1c0804c0c4108461801104500e920544040340924030200003c0301e0a151802c4904800400070a00818a072510004650703a8113580201c2440a0b40c1d84000c3c0d0403141d8901c000c100900c10b418035004400203506002c0c054482c241d10190690340108400c80d1400758846001200f6416880c0060b202c0c400e034100f03584a18034080000303400040200034000c402c2c1c1e0351000e100071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 736953003 1250 736951753 736951757
    0xa060c1a1605031b030106020109050705090f0621030a05040509130c05010c060f0c08060108070201050c03370e0c03030c06220b0a0c0e0d0c0b0307020316050d 70
    0x850351080c1240464440c044401d00c80c040003250311055064864401144c0110301600340c00b041c0c0c0400b004901942d8820707402130001d41c2d5240c0300d02c000c22100340000d8000b0b100403030300c04a0520740789402009100004100520420895521070b441d96010310b030980741c00000c502283d40710f104425000d0141d03802409654807480359440010240b041305107580d00166401006c810010b86440f0044d0b03482d00142000300e4400f03032501c0c62050200c0c2288110114440c043d0341d000c0650812200240002ca4050a00c10031039041c01d0801601c86d1903a000c0329085a210355a806500c401d180d40b8042049a4001d1507518608015541d003c04446400c0f000955002d0400d40310074403410340405959100307404281589401400c0000e8030359200072400020841c3e00161581c040b100e55aa10499003000c960807101d00341d903042c405020f80d40c00b9101d2542e40308183c6408400240c141c850a003050141d100321449075000000181c8003520a000303682d040706502d2094401d0f80c40d0f07450031a4407128103040b0200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 736954253 1250 736953003 736953023
    0x6080303060f03240c1c0c0e01021c3032181903020303040309060309050c0d0c120c080d080601051b07030212060708060f150d0b0a060c 60
    0x4003d00e03010074050881c4001524100210042c08040d5281500c0141401405081408400c0c0352005030712100d403080c56542c000140c25599a8005070070b203240ca4440a0440d032080c1c42c0200390308540c01e6a045030702c0160400282c54000031142c000d0300c0c12903404800d580405003140c424244866044681e05008640070001800c0042d82c80003004070000004d800010b80e0750317000c5088202c15201600f004d514034004e80e1181e10080440c5c0500c2f40c4510002c80c0180d00000800040c5584010150b0141141d403409000610040c0c440e20b070340749402900c051251014581480400036601e0750765004000e08e1801c09035216940c01d04040010081c41202d0141c000c0000000302c142c403681c03030306218000584440c0e0812440c0351004044606c142d10f07015062251103000700142c0e6480043d59143e14a0b071009008500d0194002043d045018008600900301c44980c0e1406644000940ea40072100204494540c640380b00280702a0018420043d01704000804c0402c00c1030740308161b0706685000d080100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 736955503 1250 736954253 736954279
    0x13051e0d020607032d090c06211503020609010201060305010e070e01090209031c09082e050103080f070f21090b0304020f130902120708071a1213060608030306 70
    0x50240d40c4009540038140380781c407108054a9807017203980440e030003841400040c00d00d015070720411100e425400c80300c041008910f50010111140c0000070040e13240c5441449010440382c0c0c000a40403150000a11941010035980480d91003544858020f54108009102028034ad20550751200514082c02e071880e2200c00c00460001030900840721a098090004c04020f02c0b07a070011001c03910480d8000041200307039a00002c5440c010040741060310005440c8400c00352640300b941041035039a144d0010720754201001040860003039010b580001c8124500b0b29500d201a181c06007218030031650040a41001c132140070000301441c14103954130291134440b400c12a07160842c581807800b08550095010038404c119000504041101e1666264590004108000c05500142800030a48078502c410350105030100081c42e010170143c030013849890700c00105001031f0078000c5540d00c038001c07003081070784066004030303206104441c100c60103660045410000d8035259240b058403a4020350b0402c3c070404001c01d070b00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 736956753 1250 736955503 736955507
    0x423150a0c0323040f120801090b0f011709030d05041103011508060415020f071101140918060a03050a08180a1206151a070219030b13051e0d020607 65
    0x21210340b80c00b00222050041481410f1541044011300c126900410300020200280001801c03518125140d2180b01c0c0790360400325400101c030500440300d8400c05c0b80380c040d9207142c1d80015011006405040c010121581e461500c5403442c82202c580d15110742ca04410001800200d40740f170f000c3d8840490082c000d02c06040c040c020080c0c068010510560014804200040c0d03101c0c0c4051030002c000762000d410000c8444110035181c000500035100d031400765180c5800783d0b034482600e002071070810440f01e091900302004038650703d400c0c560142000140b0000304000380e0314121743d80e000b140e0010440d02003545078500400e0a8001c0307030341c40c034074440b010350018014030301120001d054030903660041e05014503035264074002e4101c0d2041461108074581000c20700d8a1100c201e242103910a04520307564a24902c10f2003a081888041108200701c00e690500014103600504d54002c0b9085c0c0e010b413540249170a105007410100b852111b440011022403080d40b180c007040c21007000600307800b0780c0c1c0547e641d0710301 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 736958003 1250 736956753 736956761
    0x3060310020703020c0418030f020106060c060f0204090501120b0f070e010518060f0c1b2d0405100302090f06100f050706020424050a02060423150a0c03 67
    0x66154000d0446410680c94075406071481500910480b00c00419100200b4100c40031801c1011610707490040d010300313140d0803000700d01d2080a00e2000b042004d250207001001d020714400700404468440516021080045d016030b0041c01140d841004079503540ca00d83d0140d20303030a0030304a807802c210b500041c42608000c00442c0c030070201502c4d0540b081c040310004507000d40c05000e0314007100803035035441c0045403541d5014041c50506400120780d59032410000700e18004030780c00143e0410000110070704164441c403140c505040c1c850350141d482b07090501e0030450481010746080d90460320703003820402c000058801f00c0b01128021303a0040c016444910888180303000851310035030840100d81305011341c41e00c2281a51b400e82e0061412909004c00e55840e4030903139025502c0b07608885100c0613001c1280300110416456183d4505045217044189800651034007002080079003000d018a020324400280030310780c80e11801105058a2120002c4101d994400348190380c000354280c581024404454082d200d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 736959253 1250 736958003 736958011
    0x2031203040210030905011e0b0307050a0b0910111009120e01090b030910020c030408070b0c06071805130e060a02040308091e0a060201090b060a0605030f10180609060b03 75
    0x202c185000c0720403143c264054003030040205e40540d82c600505081141000981c540c1c50404840400c40c1c44444041610341240754000300d03c640d1280004000701d0038a0070482da1404c1c0d00750b840302101c1c01c0340c131002c0d1a0040309000482d100d00035440e058218000d140d000b4074a05100f5212415080c0712032108854542000070402c0c08149406001d201c0c0c51450009194840c20b400100c5403520040100760060360020f8080101c96800131805001086040c00b240b000b60100e1400309040505081c5802d47c0d8a03800341041d4244a68018650911003040ea15400500000707400f414030203411000c442d0041180c541903100342e0042402068211405000b15400c6903000303c4004d0404201c5000c010404a1348004d213800fa0303124507401c04141d181c1001420003443e003030b000000c00f40f04c107007000541c400000301040e11601d40e050301480300a401900b03403900510b006158244070f03516030140e03000b10301d56074022290060040f02e004070402030f0f6401200c150b903800320042c860240d807841d03411020b0005036 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 736960503 1250 736959253 736959259
    0x1306030e061b13060903020405150105030f061507120e040b180a0212010b04080f0c0d061a0303130f05030102040b0403021e040908070b1f270f0207020312030402 71
    0x452201041d802640015107442c05105103420300c0072081c0240b80c48554050b1010400144c420030a501e400d02c1040d90000704290b9258450300341ca00024410f1200800781c1005002040214940b03031502d0303212001e40701e109582c0b10f03130326055807e08100c0c00d104a0340c10000101d100444400d1402c003070081807600c03280682a41d042c0b2416061791803281e00700401c1700401d80d07401c2c40a020305e1604801007500800c03640e04960341c1c890822100c5414500b03405092981540036003002081611400c040654860b0803e10000c2c01480c0c81c03010040c5241c0c030160f80da60600c8007142c2600202400c1600d40116028540d00d10a41070f646d00a06003070b4026849101030010090000304058104400c1c0d00d80d003405109990f5441d1981040020101c4945441c291070202010402c0c10402540e4001c0b25041200a824442c00303110740f0001c04400c1c1c3c80c50045d031110b080e52811103481050350700c40918054040c00024028401d140c1032a8000b500043c1d01039100344034a0ba580d0003c0c2d5030400072680559005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 736961753 1250 736960503 736960513
    0x30a11130209040603030309170304031403090109060e060a0c020c130b0a080109150b0603130215072907050f090108040c03050307030f110309031c03090b0c1306030e 73
    0x401011055400d91101038903000c000151180c0c0e5148100d102840c4030ba00e00080240b1a030800e07440700e94920f025019004010424440425000006404d004042ea0b0070310b81c0d01d0b0743e841040c80c05441181402070515007030a010401c0060049001403159000388010080104840012a500c0390f0014445070009150070300c10020b4003032500082c89401000d80b4624180d9070341c080b260308407510102c080e10000c0c0c3c140c944801003001c502a80d240e1403811074015055003400c002c3c0107211425200000d10030010080c041c00000c01704410340fa44a030708448685445092401448183c0d1141100c901d81ca0040d1390020310b10328000e100b81d61409440d141c50301d080030703a08030042d20242400381c030607136904c0850040003001820400041915034865a07505c003072105101405801c01c4c50506140340c0d183c100780007650b0142c40000c1d4180002e070114042c0d001c01401202c0039002004446009005844a5001c1102d9040900001c004410340c2c0c5c12071101c1247c1c2e07000c080382250012600c9590360303041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 736963003 1250 736961753 736961783
    0x15040b0f0702120d02010c020105060409022107260c010c030801300305090f030106050f04050a0f0203010e010e070507110907020106180e160f0b0310030b07080411030a 74
    0x2480340682141d9201a0040014610681109141c001c50b03800e4400141c0d199040500b41136030a000d03494102030203503020b0007001195400655a003001520220b001d60803140102001e05040102c0c1c40200400d42e54142e6909082c00c0031780aa180c2c000d0110058807580d003491580d544199520b52206800d5564800d50380d013000c2c0340e90b842206403003004400c06012008038000204000c20346154510a481d4180d032465401c051000000b16120b0080c8a64501030702000561504080c4100806007102c002a49503202c80140c0c0c010b08102280005180c0301200200307031000c4250400c0d0694050b2000c0311040e9546540480d09c40c03107081401801c1d02a01091075100d0300344500c203190000c1203400046509a00c030b004115841c81c0c06501d01b0001a21120b508150310018002865018101c40030301c40c42c0c60520365a65102c8140748030b1490b410800000041e40d048019290201442e8003508456603420100300040141d001503c003542e10300d0801201d100c0e5441c001880c090340c680d1050104d021049 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 736964253 1250 736963003 736963027
    0x6230c0c090912120a020c0d1e1715060403081909140a060318150b01110604050715120c05030a06050f03101d0106080703030201061a03010902130810090215040b 71
    0x1002400400e05c26400b4822402e42d01c0701030180b41d10818096031080202c51840042c90381d41c100e00300d07011081c8140800b50306241101990070b03541c0308d140c2d40c00c850014601305000c2024ad00c120f0340090b110500201d00c1c2e10211000030041240c00a2507130b10060b8040d01c0d105035502650350b4248076030384403017048402c000050294012611501c0241d4444034a0081501e42d5411414140c03482220580d54801c07219003582c004103a0aa008002d5005103080e2900307075182559402103009500b8910505805041c80c40e12034542c81446080241c010700844802e08009006908240c4900402c1c90804101080d00e0030110f4000400b100b006008003000006c181d811f2000f0508507008005081d008204140102c03001d005400080032890024100380e46541402401c4900e113411242e1072142a108092022a107003040d40e056a1500e140140e85050602c60300c0c400d00c40070b51142555006e126502c0c40440a154000191a8025a004001c0c900b0391228912036104500038108036107c18030a00b00050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 736965503 1250 736964253 736964287
    0xb0301080d0c2d050613020a0317040b0d0605040b061801030911150d0c09081c02011515030f0509030d090c240e04050601080106230c0c090912 63
    0x180c000c80c4084511080c0f6460f4007282c40c035003039603080740300140b00a0b50300700b140400402e40d0000554411a203891305550001d0101d0840e440098229440d0b513070003100003811002102c0c000c0181510701551100d040070210060003c520480d48a1440c090010009081040460300307a40324030083c2404840200c2c0040d0014003803050287d41245080c1c12464039500c0f800400440c519410007040d440f03519040d00e00c010748900314201c01c00c1202d0200c08000f000c000103440313034582c000326403075802c2c0c1081d8482c100e005010340a00c0c15144184000d0006441c2d00496900201c0030440d5001e2040b000b0074940c0130700307640040d0380541242d4010001b980c00b400d850782c0441d203002d101e20b05120b0302a80c1d850720004000b100c0310454002050420142e82065001482c0e010410001d45041c4440c1c9025000030700100014031401c41403041215141400c0d220341c1c86006040c903080041310340c03035104c4e0844503540c1d01d8000410500410200c408034190381c0d00050a10007004045030420f182c0098a5101c6141d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 736966753 1250 736965503 736965527
    0x30807090312030b0f1509120c090103030f020d090308030a1e0507031401090c0e04020c0f0604110a0911030403051e0d0b0901060e090403030c0c021215010b0301080d 73
    0x201040300003000040c9002c154030301825655401203581103400040126060245403202d22920240c0110204040600c0548004100483c0c01c0c081140340b80350000d007080c1c140840b5aa0061406d00044201500080c0000511100b6402c48a164210b248291510307901408041c1c0b0010f424400a800d1126541080010840e0760f41c0900e811403261060034169401941c3c5000070036100c903005889005024881c0340180100702c1c050100c2d00d64280b028011042000380c02c0d005603000200c1403210442000754a40100c2c2e0003080750007900d4603080840b4150707041c03081148504075002000524074032a0203003540d000500c0e0320349881c40d1220340d001e603507581c42940c0d03074105001e11003520100c2c2d2081ca405051110a43d580220780d0b4844401005000b28058100d402801841c84416800b91a2001d000364010f51501300010500166071043e5a1004600b000a5004c2803106440101d0300c40810580c2240001c928240e00a0b40ca4030b41c20b2010380000d0080c10103941c4842c6404034054800c25204000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 736968003 1250 736966753 736966757
    0xf080d1106040c140109120606090b1c0303051023030c030309031b031501080703050705010503040f150b03010c031b1b060c12050c090a060e01090b07110301090b0a150f03030807 78
    0x1c0b441d0b846c40c3c1c1594401d1140c0c41502c2c1c0341e40e40d100400c4042c80c140500bc1d8098822078030540303c1c0704101c5c46141e0304044801c028080654400005000031070a4406401420319000402d0060005040f4240c0f10726003018120301038010200c96040c0c40c00c00205484800c0300050140007544102d00c0403504030b24544013015032511400200c0042c5461074445240a001c10030040d0090318114104185444155401103041207000c00402c00800d42255203804055817105010b600743c1010f054441c0a03201503420150f140d407815074010091505030b800780409010382800c060100552101c00c0d00c0c1307080c56404c002070072641e5030b60030390000310103500018440311981811505901d030a03c1000c1245c904840646080f41e0000d641d0f49a0303e0140701400052025141000c0c19140c0040000c11503841880303000d03000c020104042e410800b008500707100c5064060020070041c01c1904201d8502c5e8002d40d103144079240b4000d0491500c0c40c81c07c080343c0c180d071540c1c00417540003031071035030700f00d42040d40140380c181 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 736969253 1250 736968003 736968017
    0x51203070c081e07060906050d0e101406030705011707052101050111010501050609042018090106051603050d14040804180605030a060b03070f080d1106040c1401 71
    0x400301d1040c900503048080092003000b0785489240441505a05016510341c04040704001c4150f01042240c01d0351040d02c1d01c991951040c10503040901819010429240141e0310803000c8803009a10000648030710005814854903078405160305c45003e40690b90001d004106003c3c1000c10b1095804d81102492a15a113080c0c800d1484070449484442843c2c1c03101c019400400066038000010111032281100800c4203525040c001341ca58030986024500a94580b81c038055810b4511130751000c076600c114812541d402e41d080c0b041c0c81e400004861507205503030b131030b00209400d0302c158143c2c2c07a105030301380c0d25024112841d181920035402c0800025102519243d010741104004a8010b000b0b52183d002d254803a0300306190b100003404050a21403005140150401895800240c0001c00d180c110b40001903946009010a0604603d900142031006a0b9840080c00d09000142c42c40c00700c1060790b408188440011b8801d484d948241c07000362150100d8034050050000781081c50441c004141410741c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 736970503 1250 736969253 736969267
    0xa0315090f0503030c0d2318030706141f141c1406160e030c040f060b280906210204120303020304121e050f041d10090b030304051203 59
    0x2491603104a480704c10641e40450b5561800c999401001040d07242069003c40207c09000300d0101200005d113891115038010680036042d103020300403100c640d40c100c1d1044c0400c040000a0704410b440580d911450f212140510048401c8036907001803d030792401c1402c400c4810356008204601d0580c03110940b5500041c04030320001402c8421206201040901504040c58000c0b609214080302d81061000c2c0407441c442d52005940c041100204c80400301e4001482a0f01c00e2801c00050005d500120000c0350700051601014513403140c4040c403034041b08000503018001d6842100d80404512401001c0754074421070586401030302e9813407401422425001400c1681d5082c140300801050482070700426800400e00c41823200410703030b26601007094180700804040c80f20800f441c3c6032541010a041140c007103403140240c1d038490100e400402c0c1d05040359071070701035460f44484207602c140c400e526009485100040c0d00d4120780510511482d00070040d60405142c1000d100f00000324144115107400200501 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 736971753 1250 736970503 736970513
    0x20f0405060c0d030e01020a050702040f0b031203010f0b1e0702132c0102120f10082a040b1507030c021f090b030c071103031902030c0c0a0315090f 65
    0x141c691184841c000342815180b5800103030441d170940c10515039690040000c1d0300040c2c0c2180440b0141641901c0004000c00401c1c0d140b00201000d6207016458001e0300d880480800750480a107040c0d8080100c009052692491001054070035004a8211604c02ca13100450202c1d004010f42034103070010f408450201c600b210184100c072540d0f0300c1c000e1541580d5608200c82564801c074501008070a6008525000d00c4510181d025100200007036600f804000c001107602c030402811000800d500c0b01201c180040c0200f00303100056500c03851044e10b01c0340c0800d01c2035519103402041200c000280484122620100084803990300c03000040d828400395603040001a1130741560701c0c3d480c1c0d5805050001c0c01403003110051607036500342d05c0034a40c0300090061001c640748000849401a85c0a009103062006080c04a800c60180007041c00b504610508070603800c4d500070005004c048a110103481503070040c00e00301301c08000c0c1804003030000c01441e4468050040242e000c0701040740602c01004c420003131a0b8407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 736973003 1250 736971753 736971757
    0xf140301020c010c050c010c1b08091305071e03050f0601080a062601050f070e0d0312021303030e01051c0e0703140c04050a05220602090612010f050909070603020f040506 75
    0x80c13030005000050f0307407204500c0a210303080c0c101381580340c003840071400a5201c1d6200d05c02d64101600a81e400911034281d07990700b030f405101519803035005211610b001c0303c010b0090380f0b042d4441084401c4504100d400e1501c2441880c0c42070000c0c414000240d00c4034001140d0860b0024035401c516540c644000c070b0300e035602c240e5465105500700c45525040e41d2125146094450250040e03c46240720300510141c50b401c40ea00802d40321080d654007102c0d0302d1604084030030141c0c07480310310056480007881032140c0403003100300c20507a4000d4035150b105c0190000110761034031500c00c1d03688884950011080403000c458120406819050040b96001c0e5200d46650981103420030760000c041d07000c11940001c50a06e401680d501c04144001000306250540e500b4001da1071000300715184031040c180160400c0050303815101c000720701a24260b242c1c8030f03551045103240020b00903107080c5908444006680c0c9070030042c2d144503c42250142281600e00031050340a0340280c05201d003000c50a01c0042030540b62100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 736974253 1250 736973003 736973021
    0x60303030b30250314150703020708070b01060302132301050d23040c0f03030509010305072d03050604380409060212060a0303270314061e010f140301020c01 69
    0x100c0702c128203165280c01260480f42007546090b40d00544084c40100b6050b10640354070500a023800740c1d0303400c007030300d450b03001d901c00c003400248420115000858015415806803614894402d507145c0c0d11502c0308484244044011842ca4219050001816403540b040c0013510725035500c030740c000ca078040e01e45030b070743c5000e0301e501c0c014060815089003040288030144044100501030814889026410341d20000e0492041030b800d107042c1a108c2c00400e0495100d800541d00c075840c512065841d406020601c5c6544200101050000904040204481d4642403003840c0c0c4400020b41c50440c421300c0005d0521650303109003482c00c1d03680b1401c0440c0c1219100c40c003c640e042d902c0760000603900c44503084180b1183d0806480580510082903082c00025044074040b08040900c5c40c104076141d1110003805503080d85504014440d01c0300a90702c160446001444030f005a0a8845050b0b01e80714140f5411070998003441021400b00c6440f004004802c030000015a4044014001500d00740769140c0507420f44030104 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 736975503 1250 736974253 736974313
    0x5120f0d02030408090a1202060d0911030105090115091a0909121602040606050c100b0303092206051909020901030e1501030c080f03030105190e0a060303030b30 71
    0x50000424079100000c000900042c1c1f0300b80988034001c2d008101d0f40d0141b00030341e050443e5104d00301001d020440300101b1146d400100240024036100d1038003806002140d8101d60700c10031aa0020680000301c0c0035103d82c08115950034803103d201c080412482c14009855520180604000d010101d121140209100c100c080c0d09440721035003903c1400215000d076480030b000c0020038426422401e1b0003180c40010011207240110b0440d1824001034150702c900001107034801c61b80300d21001004020002d4112114540c401040b40603030314801d2012194890180352515007034104140045041c95000d0305030100d040c03600080001142c5521468201b614218006002c4034100400401410324000f0300544a118090a100e041c0c030184aa0780c1c0c00180035181c403420b0510a00e002a00c0408003a0340100620319564646050009044009100b81e02003907000a04000d156882805c0c601300040c085110020402d181041c481200c808200781c1032000e1401d4019240240444003400840c0c2079403450349 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 736976753 1250 736975503 736975507
    0x5030a240603091101030b0609010c1707060501140f0a06110304030f0809040f02160f020f1f1b02010905100c050106091e09030f080705040b0a121805120f0d02030408 73
    0xa04285225000304c0400328101400c000101030140c8440d400d41d0b003280300078244010044e419240907204540d104108001c9000f021800071b050180a4000ca812070381214007114050380d80506010319204486610b0360401c541000c01c0201e513200d103216076000150402560704254503555000b10740c414000301a222a28082080809868180708880780546140821850a1103d03000364400c100c40309400f81040007900880025034540344007544040c080140300c03031070503c103e40100862a41c91020440094011412000d4241c992140428150740513101c0c00441d03032400703081045009070000c60320100b1403070365024000500d090140401402e200c90011444101c5030754510b03564070308103120002207801e1005590220380c1100440100d0075061800501541c1c82c0d01d002d4a4600c16a440442518030014031100c5081d8402420032014107502c106104000b01906840d20601071100b0103480c1d03400400080e906000c4120007445c140a590342c220341884902c8070310608a8104071002d071450500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 736978003 1250 736976753 736976771
    0x30601090603050c040b0a1401020c13060602060907050102100b01031503030504051c1208060105071401050402090a1e050910061d1003080a1202070b090703060608030a05030a240603 80
    0x82401310080700c13002505e0030810b600110000481e02e50188c03082c7c50b0341c2600c10901f440603920900c0405a00317030014181c2103a222040d62031800078180c521543c2d00502484000c50249407001c14030000300d03030050703004015a0000c80d0b0800000c10b460201581415911a6071041e50301d0032008050083d80244c68240d01c3ea441c0c4000d00c01905109400280904640da400710b00240b05030b0030b10f40c40f4409900e85a506030780d4620040c0c5d200d10440a020709002108100003405403815082144103174402d842d010303a251212030016058403000c080b45040454101040440070491b944941d074449601c0c011180c0000000800380119486600b003a200b0540201d00f42c2200104940c0f000c5d0403c84810010114900e15225031004c4e0295901400420415409441d56098260155014190404600781c1d0a003090840c0c0c81d038418242c81704541c400e080c15000214200c0100540c6c0086c4815260072386155a480c504000400303681e00075102c094401d80b0b07041020601d241c0c104002c1d00c1d0b80e8800040042c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 736979253 1250 736978003 736978013
    0x1012050a05070603022701021509010603170903100e210c060601051c15230f01031503170f0f07050c19121a161704050607110c030601090603 62
    0x10094005405043c010041c5090280750080300241d030b1b00022100000c0c02c0c0c8503500403400c0c106480300e44425040c0784824803108020640c030060440344a104d07820a508060315090800f8000c0c1101143e25802c0803119440b400541e402c6880385040c0007058402d02d40070000060343e070442c00100400700000c0421841c0b240034007084080d80001d403d08040d400c10344034001b242d01400c127641c00204000c0c0c45811a05024031503c002ca002380280001050a07050141e200320074194a880040340724007002d44400c5044e5000c0d01c544900000003038200b0b01c001d070540d1a2240e000c0d28014140c0058481084100010b0380d039500070740b1a811005821030368602090a0003450306074a082003a01c0b54041d804400c0800c01414881000c41d000c003039a10b032020b0308604158200c0203003910340c204110300400802210004040d2400d940c5040e50302c0d544610100380c0181929240101c034001c04603800540400c03482c80c010b143d2034081880d076404468a00ca02d00c000b003030030310700300381d0003465102d0301c030361040c42001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 736980503 1250 736979253 736979263
    0xa02070302010506190315110708031e060a05060a2c0a06050a080708150307060302030a1a0901120203070329390d110403050705060a02060f1012050a05 67
    0x590700700c5c0d81c0c0e80001464800c00444e008248401000300c0851400c506164015800201a010010f400503032551680d080042c56030713200f11035190b42d0300c644054294007003014a4109000d64000740405501c0c40c2050300388a070a82c032070b039151030130302c010a007156242c0d841e4103aa05228190340c003494800c3e171703140d0b03c180201040280c121a080c07020500402c40582c1e40f041c1174991003045440d0404007522034004140ba04000c4800c0690580503610700420341541580055014044081d0100003c00740e00549c08181400383c181160f000c0d01e81d03c010466415804140d50400f40000c0694035202e035a40c0e5030100c040c0c50103076040d242035126400e0103c05550212b17455441100a883d0302c0188201c2c41a24040d841002206d00641005a0071103c544405105803440d84040090400020f09009210030250300541f00c12036091141481c04207541c1072883c05d030b0f018040507030018015500c0e207041200c200603005140f21f0b14203d10b02d00000f907803010312150b402603501490113070100004a0400c03034185 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 736981753 1250 736980503 736980511
    0x51e031b0c0d020c0d050303040f08120403170105040204080c0d0311060106030b030c0f0f01080702031c09260f0304051219080f01181d0109120201140f011e0e0a020703020105 77
    0x851718100704801285011040341d60083d4480c0d071102481409261240e0b00340129040c00c0c4800001d401080205500001400c3c0100c000001c0d035403141c2e81c1c0c0c0041005a1245001c3c6410940010049404505200c61000b6032076100341801c10120101c40c020310300d000800d81c04400040e40b9401d08000030f060500502d8404401601c1385d01201d1500e0000c2803280c0c90102103141000b07015400155074078420310540c0c40c181c0161012015400317200c045070018010000095810301140d11400010380004a5030391400d00c484080581062540c840510341c40c0c00050040e02d2a008400c06085591060802040c85400303401003c400c4c2010620002d01c8960010300c1003220382200001809103800d1588003e200c00070039607001c60944c803414003818500e11a00041840d0350300700410842008081c903d010005507032035000301b001410704030020103585800e40e5404603440030880144001980c001d141c0c81c503070315501c070f00f03040e010313600c0d204e400b04500c00301c1d465221542d000c5116420142e0a010381604 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 736983003 1250 736981753 736981759
    0x80d0b0604050901060f0c05060106111005011a0a0309020303121801090203071e0305010c110609010612030c060209030d0e1002010221070917100b01051e031b0c0d020c 74
    0x5090030200450000f80c1c041c06100180000300d440030540c50703c43c80c2d0400b005580401a0383c2c183d40d655101400120140644203401c0c000c140c0c0b4451940207900c210760480362020703500c002c42840304089a402b540641d085404150f101c20726030380980c908000910840c804030054100d946445020a151080340c03400342d042d903904054120016a90000d61304d4240c91210321914850000030003403600c03101150703000a0480d4201007003502d0350358101d000c030303034440681c04281c2e04e2507950100c8042c00c80d100d500400c0300f56000314a0900100e8450b18070080310500c50000180742203907240009141085890f503c80c000340c90354030300c2c26190400e04000c0f002c01109000035402d281d403121340590f030000b8500e00641100e04180000e0360440c42840c00400800c4251040c001c400040c000342600c503e049091858042d040042621855214504031516502a503103014000b10043c240c07244c40d03504c05003424035a03c0c0c241c4184580341c2c520000400940484100174607006101c83d40103414804154101e40c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 736984253 1250 736983003 736983007
    0x4050702010905150c09150901031803082205030d050105130606020a0b040c030b04050a1a0712090606081f062c0717090109060614060d0b0607020607080d0b06 70
    0x150001102441005484d0203a071103581d569a0510300d600031402401d600540a43c0c2061101542d2401091845000c1c0ea041c0b0043c00c1189840100c40c04403100180054411800200d4a40401c003141c10360f840008040c407040c02054480c980781d50000300307520150503500c0340104100d250211140840c820518410f100c403c1c5002c0d4040d4550039080c00241ca10840403000504002004443d00c003d550f000075801080d06050074496a60b81c94220105c4601071107220031242e00d50310015142c03048249039242e0860010606414016181c000d1088031450340310032010902c40010f00180e20b40c1c600d010300015a05008604503030507102c540d84000c011004d4080403040c82038118420f00c0b00050501d081c2c10054540d00400c485680040401305450f418402c24490072081c190860828030380505400e104540e159102401100305030b06000354050020014100401103d030031040e454880241280c3c1010f6482c4c000c2303021540310200071958400e000566407141d0103107100351400200d095072024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 736985503 1250 736984253 736984271
    0xe030c0a080718180b15090c070204150906171501080d050a02070803070f05010e060106021902011b0c06110102030115030506031e01060f09020f0322050a0506060405070201 76
    0xb03455003100c0c020000585240200c40d41d60f14034542024144103500c01c0300007400080f600340b21031610004d07203031032580c0322000142c9074561074090354442c029400b04820b0303407030000b42c0c1c0d0030400103003501c8000b00d4000442030b1002035a801c481c0300e204010142c541042c03a503005130100b5281000c01400c1c02d5a100c042c804010301c080800000c10320017080481c01d14660391101c0b55001c1c0d29140300303070740300390410f200002d48181040114a01031004d280b240c00248820110851001d4481e0400d0003540010b034081005200200e01c1c00b2000b441250041c1407401c5182c44000d542542403100060a0760100084034040041c40d87c0211140022044400218119410030280c0c400c85d2580c0d4180c01e003016190800310b01d0b90354051041d500c00038045612443c1310104000d0950203010755100d60981d80701d4800c2c001034400c056000307c442a03000443c035540355940311141e0b11302ca02403c200d02080c0ba0010800f080000740c0400c11004983d0042d0003d0100c2d00d002000c100070303540c00901c80411a41042003407 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 736986753 1250 736985503 736985519
    0x3031d070e0c0714010c09031211151b0f120603120a230d0902040e010c09090207080f03180106050a05060316050910051309180f0201030902040c0e030c0a 68
    0x45038200c00c4450855503124102e0400c4e2071101d2400c08101800d518040c140ea00b002d030080c000300110b0344296144401d1141c1c440090303420806940c1500303040e4004a40300800d030108400c0190b405410380300104c21004c5080c03950320300c540202d480794214200014040b2000203820807400d6108508900420b0000096040c14030140521426402441440300f41484e41d107004211101200c0c3c82d04030841d440300054000c400140141640503070241c3c1c80c14080324000782d010b00030100d80c4041c507260381c4000340c078148600000b54051042941c1400048c000f154200090310000c601603c03a402c0c1c4500c0c1892098501400c42da041c1c0d000500c100e04450042003e030b250541079036408291042c3e03541301100d440c6030a1f1100e200341c0c0403c1b54004003840a0040701a00030000d00303940c082840300034007120b13180c03102d41c421641040d07210301c44c10342101c50303550009400304101c08a0f6881898003007503621440d80420141c1d18007280c0200070070380d1003161001c00e0400300044d10003140304440469040346040c4c44 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 736988003 1250 736986753 736986779
    0xc031f0f06080a060e1027181b050303041710150e10240315080a050c12030906070c0902040306050a18020109050d0804050a1712040602030301210506010303031d07 72
    0xb0151f0705070350301103202e88040c0c104041010603252000140180b030740000c503560b592035141000322078094000f80c55000c1c002403040f0100541380d001d00110714003410030650110004107a010321744240300e0510701d0344010303085000d041c4c41041440120071442e42800340c280025000200385040102041d4820800542046603070310301c0c0c0c1d80914040ca00380d20041011405010400c3c500f0000f0313441e00b4000a00c0d00c10002e0300004450280301590201e4001c0800c00c811800c0c0060504207550ac02c5c0032864141ca003038401070005a00ca40d9a4010725076840d920b00050303070050340c0140da0303040c5e80300304000000000d0701030a01c143e1029641f0b40ca040c600e42d400a04103202034003c86000c0c0000b00318140412810f50102c034040c0c0b00007408513118643c0c0e211040c1040840d000d0b812100e00500c0740011031001450186e0b81034501c141c003d942160f0070000780d03207004030111490611072120388820001080007484664040c50084e0f5000c555011291004044010002030100066020b950b04100c0304c120307045 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 736989253 1250 736988003 736988009
    0x20d06180216111f0e190b040e18070f03031103120c0306010c05031201030203010e06070c030f12020d0509061e010e090f030c240c031f0f06080a060e10 67
    0x640408004100e602007498844010302044d813541d80103e200c60b110380c21110520703003050120f50030b40044440303120f8950031403910722805907409005e01c000c1c46640700f041c0c40d05501414451075150404032a034100c0d481c001c2e09a004000b14808a2003e206140e4001d520501c4034031004021448d2494071001c04c03070441c000500c10542c050011000c0f802c3e84e8802d0740d24101054124007200d8440c81c550400210b204402e1004038070035071808200c0488038038082040c2d8800c0a00d5192414440c100e0f487c10794100b010000b0450400c000440e07101c210003880e102034585855007840014040c80c00400903894000e0141a800f039411855081d0881e100d280b00815054890307400c1c8010041e100e0020252a0951441d60742030203000101d000f01c00c540000801038040410411242105541c4c031314405031814098a840f403030200300700005004d40e804a03191403c0c0300040c1c040080c0c4640c0e250440c0b58840c245820040c0020400402e00103c00302074021000500000c40c0410150b08200320010b0501800d44 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 736990503 1250 736989253 736989263
    0x10507020f03100f0e0f0604150c142709012d0506041d0a02070209060f240d20071e12120509010c020d120f020d06180216 54
    0x21240d00301d40d02e0500c90502860301000e400e2003e040c15900000240a00351801402031050700a07810b8116000192180100c0e081220114121041c442c0c9038040c0000d40030741000d1041402c00140407400c031400034400a0b000700d440301c001d080240510030003900302c40d040a109115080041c000408031448844030110540888201c214400791140004841c0c0d0b4001c5902c48000708001415840320011034010204c2d45074141e490781d9500902100b28003607544c010b0f400c001c0190028180c0d0030000503c139001540244490180080c4e810f4240900c0c160380d0849001781000300b00c0000c0d12060740140e11001c81c402001031811014011903101600500d5800b0706180c5a610030840d1503000d0740480f045c92500302030070b408030003082e21000e040010306403200c14010b494000026a0514184119020026590301801d80d004a000303003141c042d801e4070900909142d541c03140440d9040c01d84000c2c44600b1001c02c011541c6032a22001070401080c41803105425401045400c09100c401e8000113640c940c04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 736991753 1250 736990503 736990519
    0x40b010813031413060216030b010b070203030c010c0e15070203030d0b0a090903052a0a02040b150304050106150906050306012d0206040c05060a17070e150901021b01050702 76
    0x41c02c08581031200d00e400590841c0c00001c1a5100c031040b006000c003520724a400b01c40c901c801c10314410300d245410f44805000c1c01c40c01c2005000090502008006246c00101182c0c01c00c20b0710030031603084880ba003a030940840c0c0e20340c1d00c1502c1800d046002ca90480e075500c401e181082c2e10b0f5000700352030307110740c52004010559424243c10b00d41c0d00d04000e48040d0900c0300040000100718900a00b569100158115a07024121302400e084d107800400c1d4001c0b600d80c0000742c44c0340307140c65092101500e0342e00036440c0d2050411030a140c0071600b81020b14070490142e000031985900e410410801d04420b180c9460410036824021303c0010341140131030340c20090a10b072030548103030310b03d503020800e155490307503c1012840d0840c00d00045600203040d034004c0340590405002c0c280c6e00e008001c0244100c1111001144040e621020410b20001450b5407040d04c1d0305081c40740c140800001140201c1c201001c0000d80404100e04407556410400344401030050000c14110000c3c400001c2c3c52809001e038024070540784 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 736993003 1250 736991753 736991791
    0x10020f1803011d240c07060b0a0b0d1d0607020316030e060a03050601120e1b151306080a0204060c0f0c0b0a02100e031908090c0a0303080411040b0108 66
    0x750310401c120070004290800300d0f040c1c0f024481d101c0b6040f1407061800040100c002d140348011814041c051008200341c10b2400791190b843e1b00142c2011141194000c8041900140304441c1c000104960a82e03400000b95242c040380840407403511511509120794400020070174100d03000001c039980742032610460b080095291038115408640e0220301070b0402c04c0070500703014840d015000346011345800d803203210703010035580a41d6084400040400826130700104040340f002203209140445030b000540980f070706021803440d1004036404400f01c201100001f00d010400c03190310100032034000480d00780940c40c1a2415a0040201e0040040640220824a014000c01c50300042c3c903401040f02c084041c1c1c541c0440703400652691030420340c0700001401d044404106110120032111030404050007104030605064045400c0322008040c45840d20884d00c100825a940d203029000542c440c0d40c0b403840c0f61415181605044c85c0d0200e98500442c00c001d80409c0c0380c0e822540301c603440755014550b8a44001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 736994253 1250 736993003 736993009
    0x40f0218090c1c050106110a05033403180902030c0706020d0228230d0e28020a0b070b071b0606180c020f12160218010810020f18 57
    0x1140703000c0a800c3c04403030740000040301e030302e030f003080d812264a03071a0400300d00101d034662130b02c038600c0784c8008141c0e03041042000d000b5180840d81820801c0103103902c0034401c0e007d0b07000d01618905810254085481d000519441c5603d4200600140071701d02415030844c00d00401e064014015401c000b4001da0f004103500396802c100f9030595a0b6841c01c6080c0c003200031140100101d10b20300e00d11212000400f442c680d4004000e200300d10064008a649038503140401c1d8031b0403040240480f01000101c2e0191074a00940401c00c8816400748035408036991045095034810004001c0d000e510a08880d0801e00000001c2003206071980d27804040750402c00c29920089284461130090414024069490804040350003240c2c0070040007641c038805004c100c0924011016a9103c07441c155040d41540110420780c071001248010741055034410400041c0102158006031400880030120414050300c0c800411030608100b000754154603070040114540010385402c1c040621990f00c0d03070603a0042989051010351 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 736995503 1250 736994253 736994257
    0x5091609020d1e05070201050a11070b0402010509060d14180604020d15060306020c0d02030405031216060e0a3318051c0e010906090e15030d030b040f0218090c 70
    0x540c40404a0a140351440f00721801000190b030b94000540c03038403002403203002c514401c003030350140048002400c040b074555441c9a03908006008a0401809120b184a01c0d03c0b0310001d01445842e80b4004610000e00c80b84005114000030b00540b003080c0300b00758088000101107040e40d082601a15503000084540c1000d8803104820074008107042d1038084000203010303503903014150702c1102f881a2202040e28034003c0360303213010340d004050741500081603070714180c07500d5802000307480810f8800010040c010b4982d00119140e164107000c103a0000d03c0f044040001000504400035180040e0040c4402402080b40c440100001d0820300240e40b48801e90b001200f9107807440271158460200c402040150054522007250003505001213903110b00340758450340c000d001c08426103046503240c040030382c680014015203190141480ca8112294124003000c1c1d14284940104880c01e5100840e104801c0000c1c041112402c955105d0028410320031214241c541c0081a036080400b101c1424807a151b030a0300380701034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 736996753 1250 736995503 736995521
    0x30405060406031d25050402040b2d030f010302100810090e070e04082106060708030705190905030d0528090b0307031b0c0f080c070b0403080d05091609020d 69
    0xd106045d00007100800110107020350480d92624892802d81e61810302090380164001c0240700720703041c00109808a004000e010b500409501e40c40f945403486c0b0701c41b0800c2d0740195500140d01803440018000e508011801c048071003001e29005085252800f0800441e2174030340980c0e40340c25110303120154a00d004100307070000303401d00c2040c0c20454109031501c1d07007840d031100003203074603402c4200b40c8422110040c4c54503511891002d8450b41c074150003965921801c2d40010500c20900ca418800c00c00c00c3d55501500607507001103519000306040c20300040620b00141880d0b01c800700441008141301e044001c5120512240900003102007501001c0c0095442d8451a045041814404801c00c81441d51507044050705150a08583ca4058205082115044600507003e0001c00700c602d81400040d44000c02043d442982c0c41c01e070b40072030344c440300f54000641c003d074010346218001142e0203080900600c251900400d1b0f0800400c010390707190010211080d03403031241c102007e80c00b280098004801c1c1c0c00c101c080e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 736998003 1250 736996753 736996811
    0x30c050f0c01020d0c17190e15010e0a06030f0f23100c0c030503040f020f0607030203070c0e01180203070306050a062303070e270408030a0c0203040506040603 70
    0x4504106500d94000d400c8054110403040c100502c001e170840c014a0011240c0c0c060812008a41c3c3d81d100d00c0c0300104620480e040060f030750b6401c6135020000300380301c16214001c4c1000305d414694035109141d50780807005480e2048291070800104009000c600c00d060f21250f100d41040ca0f90000c40c01c1c82c20541400b420714544508451a6040d44180b0220712400706154044080048d5204050121841051380324001c0202d07034200041000f240003408000c00c502e1004050340507102d9402c0124900e0381110000b103016900101e42d101c20407007060b1000000c2c0c032690401541d10740c5451910221032075040c40c5940c81a0f40000456111031103078118001401c4080c010126003641e4040040c088450b404c0184100c0014510381c81c031001c5543c0031203000b05a05d030760b010700340e003514400c001d2150421031402c210b80c42030061020001d40650301c441d11a501598840703880b454006c0308a4140c1da07501141c44c0844d042000240042c3d039070003090742d05950303451900041154200c1c003902200b03041c2010440c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 736999253 1250 736998003 736998007
    0x50c09030a0c061701030b0f1306060f06120c080708180d0e01030e16051905040504030305180601060c03030509013c1802040b150403050303040b070f020d030c050f 72
    0x10030302640d010340e201203d110b076440118030000c1d0b04404208010070b000040003070304e4070b0010035514207149210540040d098490b4441103151641e42e01d04039041e80d8003500403000840c400308078003034104240354850482e400d4240643e05121100428140300240124188100035001c40c1500c1c00030711950310180505030032100441401440170746000110f014140c00281000901030703215a0100d035100c0d490304082560720465050404020070440c0300c0f40d140c4403050503001c00003203540d01ea002d080d01650080d10005081d04241140c28846c1002614800c005c0e84444010002c0941c02010310b20300a80510300081c440e01d0342859680075000b8010b12203002091044414042581440242d13003981d1110009402c5000c00c59260050362543d41d0004090049020150b016050a805c6180349110007070200034081a07034401303203103030f40c000c0d0b00140e440b0341c00402000108901d49003102d411400c28107200e8034068103402c000b5030301e4800c100d503502096122034141c00c1c07d90144048d18659580c8000d07031a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 737000503 1250 736999253 736999273
    0x6081518030c0303150402090d11012a0303060b070b040f020609210706020c030a122a020103050604050c1e04080f0c0a0b0a020a1218140102070504021c050c0903 71
    0x55940e400503201003c030014019445d1513645041d1003103810b5003c02621001c56203541e038940c0350070600d01f41601c07418010684912454480b0b03d083c842c400c4810507042d05d9208041d420000c080360240d41081120000803c00c2d01c010803042140c8503800340c2d202c9600b003444003035440410030b03a005e520324058010314040c0042c030011445200c20a2480d82030801c50b0320496035810105e99820101947d25003603001001742d840440e000c0790f50749104041354102007076128015500a88082055010344444d40792601144046682c54000e03030f034100000712820302c810b0802e01505070751031080c40d079101100f11019080202c1c41034544140c0e401801e018050b94000000801d4803030710354618002d0b0b1845841e000c800854100041c400b510b5110303a06600600c040e00095840b041501041c4422105210f00c1d04101100c1041e00c22040d406080b0344102800300845040c000380c940603035500550302c01e500500031100c880c900c8800a06a80004500100701034441261209035885804149905402044680 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 737001753 1250 737000503 737000527
    0x70305060a050a1121061c0618020a0b0409150b04052103032a03250903020a15031b0e040b0402040e090303040309080c030d080c120108100e010608151803 68
    0x65200308102805424640d581d900800903440f00c11f411640240d22241d02d91030106400d40e003c404421951440041000d20030303000100541030a034858280c288000405100c4002107001d94401e0307100d01c06d124409070303041c10102d5030940284c1c003500b40226541358485401802120442d51000c1c1c965058a41e2410044013100f1601d865452460540b03032054030746d000c03040800c4100d0b4071038860507424a60002008502c1c54410703951229000c00c00c010340c2c0703002c009641c402c20f07020b0080010b00403541d2010011000034081e500e00b0070350361070342c0390108844030900c541080c81c4c000e03521b5080b2000035072500c018002a00034010b030380050a140a00008000ca89a00080158000d074005e4885209460740d440e141551040014a405d0305070300120030784c1080c00d0150403440d8200aa800819003000c41e803148240f80303408241d021083e0795000521140d440312462007940c030040240002401031a040c01c1b01c2a6855122034015454403401e0781c00610003640c1d06040c440e282841c80d01781ea940d4281c800c18 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 737003003 1250 737001753 737001787
    0xd080d06240504050f010c0510050108011a030c012114010906030b0c07031d04110703020a0201031b1e05090307060801140a030f0b0901111204110102070305060a050a11 74
    0x808058440300038a001d154020b02c02c1e541154402048200d0565000004540d0b0160105045909100d05008030a9203500c5000b564080d00c1d0070400010044003070540c40001e41100e03c281402074121400404259074071403141c0750030110410101c01c14011b00c07c1900c00a14507540c07a02ca480306083c001103442c4030035402c0002124081d080300380c1e507070701ca40240c0f40c420b02ca12200200401c10f001d140c01c40143c8110300c6805400c01c010400a03200550201c07100d41c50344440b0b401c60050704000038800c02c40d070305072143d801540d0b01c0040d00c150302c00b03040c10060690b00c03003d05039806078001c6818101c07880d44180d0403100c02c4400075043e01c580c1c50352142d024100307110078082c20313130075000849600700365050400540b000c581d040351074242c1a2145480e507000c2410702400005495403101d9101c2843c0c0700c00340041c0307a0722441d0800a032052819007024200c8404018140d411900140401c00200314009030782500f04108040004640e110040240000c1444081d03820340400c0c0800d03103922045440b08 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 737004253 1250 737003003 737003039
    0x10225080d0e030715050313020a0504090602090406060518010c02030109051903020f01020322050c060c070801050a020313121106010f2603040b09120604050f0d0309050604020d080d06 81
    0x116004e0549940c8070320111984c1d1503c1000040003071000400b50700d001340c1202c0308180040c2100ea200741d01d6002040a40740d40003820b07030300340f42c0004980c0c80d20300303140c45010010049450000e00300f013441041e4100010b41c480d41c40d030401c42c02c10524001d40d07500390300034550554000d00725a018a03c00c5141d8003040c070140403c0d8007601070041000710114040c0202ca100700681aa12200030100c609104d20041861070140c030f940c81514001d60b502d455840c001d040509a0301c005000861612510509550b0002e2020f4120b44c011310600c20b818100700400240294040d5102005e4412004222a0348003c1c950780c0300c1d244120000011801ca19025940545101d060380f0700c060605d001510242c01c001484143d0698020001000400c2c1860b02600c15001c00038012902402c1c45c1021b41e161606c00e4070709031403503001017001c4c002e014000c1180d031180c000c0c0c5003400d0050b4800c50b2109922000003c00190058285101ca42c0c00c004084084072101034110f0f4080000d43c0d01c0e654400640c0201c01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 737005503 1250 737004253 737004259
    0x90612040302070f080c061c1d1b180714160204140f01030b0c0702040f0608161409040609080c0105040203100e030d0c0c02150702010e040209010225080d0e 69
    0x220001c50154000180b40e003e442e5600020310240040e074080c0203103a80300a6881105148181003894102d90318041c88080c000827a000c6d0440c0311481403018288030340300c03401e807548a03404007075001142c4035049030360003110114041d000c4a580e4120141d039200d02200e00f44104041c000303580504261030041c0035185030300a842c00c111440c41400a01141c49096500c0803026141000400000d603001e981191f0140f82114542c0c1411030303641c0401e00b920300710500c00c100a902c0316024048070714100040141d010b814400554101d14100c0500824900c00305420b004504070000a018002c9a800002e265a40007ea05994045200c0c0c820300031b0100b650304910034041c081d80a010814907029155221290380065458440e0315101c0400422540c41c414090000031301b4444096507422107241c00540078a50610f55900c0e1500c0010010030084481c9440380d841409030301c40990b4006003502507200e2003110740c0c280c1c10b0b814030f6100000c40107501407811445103500c0002074030350000d07030001850029 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 737006753 1250 737005503 737005513
    0x209030c22050f04021e01030b0d0b011409071d06120108010906060501020313060e030a120f0306080a080d09030309020619080a02040e0f040c0f1202010210092303090612040302 78
    0x84070b0710540d2000940c0c005c0e600101c0c184d15003004200c50005800303034110504000038401501400b041e40390b00d18610668130002e1000040150a4503000c96461200c0211941d441500e40031801074841d094500c1048e210800385d032000c0e0240e4480c00111a4640e00074117038402250f0f0b480b41051b0113402c1c0010100c50083c10101c0004195000105440c140d171041543d4009036810580100c2d800001510b0807a458031400030f0980108100400c0704806500954030050004d0040c080034080d54030341d900541950340000c50510100d502002034412814135030102290400ca1400c0480240c0351041c07000e5803141d4000381d6280005004038801c8888031b240c2d22545107580d40c050a0344101d01461088101c080b5000700002c086500d0032511941c05071103180a80350840c0c0f540c44541c52002150003021151107a00c0310542035680400c0f080e0581c1040c14401e110409280c4d542035581148600003d80d292000c2203020952007052055421410780548100d488080c48040c10700c00c244283c41c00c0d8058011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 737008003 1250 737006753 737006761
    0x60c0304060608120c0d0801052d0d1406100605070b06010507211b0510090201120203271b130f09050102030109110301080c0d020409050604050d09091e0209030c2205 73
    0xa1b102e908d0480d08000c256402042684104440318110b4075034440011807100801010750341c51130b07407410610f8001d07442c0102c0d0034402d00b80503140c0540a4100c2401e01803048041245e207a10200300d5201c00e5002c1401080e640b903140042e00d0a02075804010502e501100340d80c4080200d4500006000b00d1a99031520600301a06508041c0048807002504a81040500e43d0803404180c1202001c14411715241400c0e000d80180401240c1098074ad071204403079081d260551421001404064648480d405000b0701c803091142c3e1500c0c4480951403501600340c00c1c9203044030300300340c1d070146010300400c400903ca020200c0c54002d00070f50090140c0030420b072030106807130115058a42a24140c960500082c200b40c0031000c2040804100200201c1e03026803194100000580e042c0002401740344120020100c4290003900541403881c0c1d500b00007a01c41ca0014000740c60200810903030f8100340744050041c0c1d2001c00d40301082c14400c0f20022507800140d40003200f81c196280c00c030540a1004041410000343d29 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 737009253 1250 737008003 737008007
    0x30604200402162901030507030302120a0203030412182d03020a091109041802401d070924030201121b020a140a05060c0304060608120c0d 61
    0xb0055000c11800c00b10f441000000c1491400301c030381e6812404001103aa10b006214030081c60309801c21280d6030010741c0e04104068041210f2240d0354242c1c540c082c1042c4072000006c0d502d0000501c00b62008204010340c5000c140034080364074500c2c10500c2d18000303250b1107100101c1c1d410320340045500076035110002c43d100050b046041c0400d9960080081c10b0707052410f00c540028080310009110746c41d1003080091959a144e2051a0000c04080c04242a02003c2d0040002c40d40307d0400c10130701c000f8600c03805020440041d50804080d501c01104201c00101148039000410080f00d034885070080198490000c180001500300444200040601001065100e640c6440403600da003160110400c00d4140010b601406800a030040f90320310000b2141030031030000324003628458076000941c100f043c41e0400e100506420a14000302c1c04014805c00016540c3c09a44010051003209403c0c801b002060400000d50042c1005000540464051004450f5600040d60211048c00614816003c042603554 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 737010503 1250 737009253 737009257
    0x3060608010b040e0403050f0408030406030b040b041103060d05010f06060c0c06050a0f030903021908040f17060601080403021608060604050114010804030f05040902120a06050108040b150a0302030604200402 91
    0x4641c1139050b0301c40d85559030243e0341500550710400300450240300100c4c004104001420040030b031503601042e80e030350140c24802110305240e0054040d501704201100311541041c1180c3d00410151040d0381a50a5401c05900400d60003022160b1181030010020b20302c0e0f400f80490310201e0103100d80c041da150381e0304025106031007400804000300b42008607651281d40a076212120850090061310091030071910906034403078000b1022a21070b80b000c81c0c180165000048200d01074107a4032403620301d03000e03074984240e580c2c14000c00c2e450400040700d001404161080c080c115041814640381d4140c60745036458039845070000c59840d40030364540000000c4081c0907100b00401140180c440c1c1d01c0b240c880303807006c8400964820500f824030400b0800040d1a05151008105a45202c40304403580e0900443c02d006a0301c4651003a030405c5041414800451079021103590803c5101d8030b04084030103840045050a0580d42c4041d605000701c800704001d02000501e003062600c040d0f6074444600c580807003000b00302c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 737011753 1250 737010503 737010509
    0xa060b0f0c06060315041b120311010605040207150c1b0309180902010e09060a08030c03030a0c020309060a050d09140d12151806090c0f03050a050114060d0e0d03060608010b04 77
    0xb030707401180446c01080100e03481c80648115031000880c0c254441a040300c460046150440010f4401c00007501c00400a2203108080c0400300e80940c0303030003a16166030f0840d1701f1244911782c3c202d944500e03038403032240204169038044030011554070b16850030b800d000c2c02e00700031441921800c50300c0d14840c4808181078492030102a6058603103c04829044050094070701e40241944d412012010010400c140204064042e01700c05000440e80d030700d000d900a0b8140c8002c17140c8007003507500034041d40d20150f40702c00031b403802c0803800d02c7c00645582114400c0c0c400f9181c006800391520401c1180603514110108132000d0480407a10bc0712140241540d49408464015904101409403100140811104c0c40040324410101c80310204480307482d00895412a40b900f48003001046100c500040c0e42da03010b000303043e4003282d21b80b402c0103103600d05110a072003180314034091032040000044520103c020742c2e00003c035011444003101d8800182000207002400c03035010f1900820460400041e031250303480c0481d415 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 737013003 1250 737011753 737011783
    0xb0f100e0703020702120106080d020f15010621020f03012904140111160503160b0304170d06230a03020303072d03050406090b0a0e06030a060b0f0c060603 68
    0x31965121002c800035040044100d0344a02c12003c041e031003801c24010100548103c1c80540454400c608000e4900300c0d0351251619907421059101d4000c1e60f690900c281140d0b80c6040011803503141c00e04c00c0207a000d2070301b40010302d6031000c22483c4180b020480918141d034556040491080f0b4080d620b1005440d9210104002900030001404203154821034000358107410f041030003522003603442450400d05500d880707111460046a0400c90b44c90304010040801c0461700504821034140400b00c159407000804c060900001c0003408140080f65000b01c0f120805000030400030795031110b005003a9043c008541703a9281c1c000402c0108586846074a51003140c2d401802103141c80107a40d2101811310040c8024074900c0384154000d0207084031002d40380c0060303101350340d9075a95608110b0084c10782c02081d0092012440b060280ea03000c142c21044188510780121901c64896650446001c00b9100e06d4004c0380d016140428042110322400f00030702441020788081e214165120014503580340000501041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 737014253 1250 737013003 737013029
    0x23030711010e0f120a0605101a07031106070201050115030e031204020a0b0f0d0f0504030f140d020a1106010b160b040305071a100f050105042d030b0f10 67
    0x20941d80201207800b9010701c040d0045440942820025101c542c50a281d202d842d088580003000b08496403250551101180440035400d070f04200e18000e20307400390950f555032000001000300905000e003a000110074424011200c80e4540100001c0c0030301002c1c45411700841c07a11505411b8603000e8028440714205450003141411181c0f400a0f800d10f41c0540140c0e04141107100105004615400411411101c400920395500c41c06010f20112104052a041001c2c540380034032000030303440b05030210880304915241021340030080c40c0c21740130b00c903a410751001140f00080c640c48a5402c24a040c2d844400302090399003030707aa101000302080c8100f04a5402066001100000140102c104550498028038195060400a5a81c01200b4800c034841d00c00c602900806c0054a404020500300542000d0309220445444d042c00a81180924021800c0d08807039102807541c080c6680e4142081c140d411021003016039030700c0c00c01c451200401c1d0b5614814240d41800034143c10780d00041102100c236122201e00b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 737015503 1250 737014253 737014283
    0x10020f07090227040605030312100902030705090d0c081c2309150702090f190c0816030b1309031d0a060509130e0607090801050f01060809030403050a230307 69
    0x4400c0e0003460f0789040e07100d5507546000c22240ca04001506540e800c50281d1111800c2c4001d60201d1410349901c540e521a00401c100411795502c1015900c2c03d030001d0f101400651643c2c902010301c074102d074004481c18468098009054a41c4411641c0e0700041600e0341c40c0171060f4401d4091218014602c089607515082061051504050340d041790000c4040c419070741040044c3e40051400401640c0c0ca51412144e0414003101c0781d8038504100c20440b901e40c00300b200d0783d0300e9040580400c100070b28494605d020501078008490198228440418004204207085040d8042d0b81000380704d0000d0031b4001400b03210906060003180c084415031404001c4c110348500e4503000c400c54103a03005580d11a0480102c894010718052180070b0201441400d2001d01035621740060f00914a071110740c04a021030303040000b40b10441d03d0110069042d03031103034038000c401a501e542d0541d00d18460390b0310081c00c510801c1606010b0200ca0301c808c082c001c21141504c1511300f0603254182d5240500d19016040202001c036417 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 737016753 1250 737015503 737015557
    0x905030414091b0c0a1403090a05120d180905040f120c0b0a02071a040f020f03030a0801031509200117091005060f030304030c09050705040308040608040305070210020f070902 77
    0x182c001300c6404030440708544241d136500100010007000d117180a5102095008441c80e003582008003074201544d884401d058403a0300c0c299504600c0501c882444507003070380410648240032411016180f411018881401d152414140d000d00c1184107884c0ca5400c03032510007003588140d0a4403d10360304a2a4071445403070348501103000350301803a8221000707200d1012092010741d502203100c0c0304501030707c003544c3d02c1c01513030050110710000b009a151094004000105900740c009020505590b049402003e407082d1080d484001454100c1c009807100d41520144c4000c00320300c5200c0c140d402420790385d00c040040364501d404c40c0d451081e078100c103490704100003244000c800341d40003941c410801843c0c10504920311004c6421980b10740c206490040e4595001e0102c5400360084503003114042c54104d2070280755403242a43c80c002e07805108100010712001c0b800345032050094400c280d07001405006840342508000c0e64518080c042550385014808000031203a02030b2098406070038690c160882c040f591140b079 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 737018003 1250 737016753 737016757
    0x306010b030a0509010207020d0f02030d02030921070f181401050105070f03141b071e030f05010227030c1002250807080c19081908070203010905030414091b 69
    0x186070f135a660a204410140c0e84c0c4110110742e903400746002c3d9608058034014582800d9a110700641517500030098a91280c549448002c06000d20501d0540320b4582408481c0c02d00010354400100114440b50100c2c0e0b1140c40760306036120000f000c0c41000722407410032005c140e5500901c01d5a020980c248041408101e02c4211020f03080e11920701034421070380c91000560a81c0011002c840c80b02c44c034070345c80920408200308a40240c070336100781125403030901c80d00140130704941c00010502c25015840004114007501560302003241c0501d00b0510194088610600016041205209220700d400c40481400e00d2040325001c0303103040c0c1c0a80080780c2000c064011030074a40899030701c1c2c840125000181620140070720405052214080c00c02d481c0218200b0440c8050000d2410301082003440c1008402c1000402c2400d401c50410302000c0038410341890901d9020300c20029406501b046014010014084020025580684914400c1c03011b071100b4011803a50803582c800d01444080094108640c1206c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 737019253 1250 737018003 737018011
    0x190305042d05010c020102030a0f1b05070507080715030c0c2a030f060518070b030f070309050a0f020a0b0717250c030210210e1e0304030b01050306010b030a05 70
    0x40200581e80345a51680c0c2181ca00f52031380700050f5408020300101228502030000c081044407018400042d200d00000301000c0c1d0b100d0120148240083d0304000c201050107803400800c42c00040e60b80450ba2591804109000c58074072000007440d00004030301040c001c61000c03035165008454810248a8030758016000c2c10b000201154050411030004002203080d1a0b201400e84034900108090410f1a008049550006800d41d41600108000c0c840c0fa00c043c42565801641d1014500e0952030f08c2e48260000d0441c1500501f440c001c20005406000304c0340301d0000002c0c401d560404215076216102c007100e004d80703030b0000c0c049500358000d00071150311320003d0708203180f2030005038140c644040c020400d140e10500741105c2c07a19408408205625100068601d00d8000d070034240903c1881c110003403003510300d4080f43c0307010a80d110b80e0500c05034000c01c1103030b40e0f1036109440482c480b41580c00a84d9a904607100c00ca4180841c2000415541800310316681240c91280c6282d0842d00e91120050292134010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 737020503 1250 737019253 737019323
    0x8010602062a160605100b070813030807080c0c0114041403030409141b1c09050a06020307091a12010621090c05010e0306060a1502070e01060519030504 67
    0x401d400b09104500b001000c800c0c0044400950214981c07500c1015503400130700c2d0042494031821b04110018081040700c030001c0c2c0c01410780d9a071b09030700845c4400d0121203400140845001043c80030400800d03000614070080180200e950105031940116030300e136001c14009013408005e02080000f0381d40d2501c00e1300c111100409482c05c0984680c030708400c8402c507400c9084610b1990701482042400c0b100b02e02c5203896840f410516100929815002035107100360040c0d611075455809a0a021084c424546480d41c051070039552030918500041c0001418010411421008107180000ca1203020880e0341c5880080365140880c3e113400780a0301c014610540c5400743e02008042c0c01c0301a00140329801035144901045900e0718105400103025802c40d01240740241c0c0f145007400a541c0d2280e00490450340740c80d02101e0314020781d04041b4103107032503541700c80204404140007050594110029010400300c8160030395031200c1d58901203056460544010303020001242028a03c40040040c1e100840c02c45 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 737021753 1250 737020503 737020561
    0x80a0b220b03030c031b0a02220b091005040b0102060f07110f070303021c030b030a060b0609030f0106060807050304034803090b0711060310080f060a0c0801060206 72
    0x81d01c0843e0030341d800b80c40036200301e40000520045980490614002403140c2c40c0c000c21414441d54045600307064076125160040031480d482c80c04031001600801c960810203030807440142040c2002c5141c0d00c4181c05014031a500300150b07800c0303552001442500c190180841510103448048060b14030740b05140102041c1d010315500452164001c000d1a03005510990081480044030142c11490181c4450003004160a0801d41001c070f680019204450a42000c8001001e00101000030b41d0361003660307459601409601151140c0d400107520940848011b41c940100e107542e030f42d0088403540700450f0f00070081041d04c1c2500c080d003012a00c6210540e6000c4454829880001ea111700c0b40d0f4113150400341000c5030809c085820554095404001001022032903401c1148650f108094000e00c10b03042070180102100186012050440250051000781c013a0788c00400404843d940b074500407200700352618200300d00389082038464a480f5040325007540c050320043e1242040d0035140020301914010071016 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 737023003 1250 737021753 737021771
    0xc0f120f060f010306050a091212060f0902131d013b10060f051c0204050d030c030e0316051c080a05041e030f02060c030408150403080a0b22 62
    0x10400c41c0e540603484a1000410b10341c0341d49040c2d000d071040140a90304003030401402d80700155500ca00040c1313502450810081851b14003912000a11141c1d00804040d02c0b042c0d00018544460fa0092009070551810003c040351500d07428540001000b21402c1000703d400010401c52111f1241c400990000510b40d4040101844541c402c88000b84d141d000e041c5824400d1200d8810b071180610002c00c41400c2c00d41030000600c1700a03000b4000c480100c50994221512101c0c0d00303e01c0e904481c003070074000b40030090020710340c00c0040441192500c11400302d0302030070350b01c1990b103800640101522160f54408a0850400702404002c0b440301201c0d43d241d801c4c41c680c0b00000b640c1d03003000d0081c445066030380381c1e2580c0c601901e04101d20881e603108020603540e500c040c008903210f0190f404038590140c0d40b8690721842c1e0a040d61075481540e02c004010f014468100c50f0038803c104c805400340e8080e0303851000c552149a5854100c0c0c1180003540c1c0d0242142621640201051903a101100e88042d40011041d0f6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 737024253 1250 737023003 737023033
    0xf2b03121b0219172505030a2606040b010e03151b040b03010b03060303070605041113050906191d1608121c020f07230c0f12 55
    0x2400e4140204164030705841100c1140d0400c00c0ba25103c541038580515080da0380c882c841e60184180003000c807540001201071105140030740698203c4140040007261003428142261250010b04954000480d500c51843c1c030100b9040b002c8a40c100c002100c03400c2510f075a0100002440c450080c3d074188a800c0e41080d481359030501102e03160548100c852400b502d0044a052058510305160b05000b1101740810301050300b41e0310550341900c14030b00400340d5a0302c861001900d0740c000c1400042009060074104002c20042c03460034040c5800640f21038080c001c440104100341c480403581c00d1626440780000984010748680045803051340002c0c0081e4948112030b880010010900140f00682c0c84851a150140903100741c0c1c0004100d800c5c05040480744e030400300c076554421804203270f41c6c540641403a4480c2500c1f03541200d41015000342080e07510700c2145041d110b011010076000030712096514114070b09000100300030344106030007402c82c01100034100801980c60161110328166101e03241d00903440310 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 737025503 1250 737024253 737024261
    0x22020a12050c0a050312031605040521100b030307030f11010207031e02030403051b0301020f0d0e12041503020f040302060a0c060605100806091b180f2b0312 69
    0x80d000360060020303a0380785400c0c00f00c5280f20f42e0103180664040c5801e40c040c00d072544180d030740051f010920a8103000e91260111400c3c02580c0000e43e00628200171085500800394000c1c0240c5401410345565901008803102290702c407940468050708100b1072000000d01c1034424211040072810980340c0349444042d49422a00018000c50214245510780b01d66900c0944040d0000d222510040d490107003540d803440c1e150303601c40c20681140410400c8078003203583c007074040c4e4010b0781c84110440d84a0024440c1000644900b2002e84a1030003a44200d00700030a5401c01c440c1903c001c00d5002c9105d0018007402c400030f43c04145c040d02948020f10021006171758a1006103424003e60340d60004134207550502c5811500c02e98051032290300295101400380c1d41200c007081d0f1100046841c4031243c2e40741400d44070920b0700c01e40d40702c5040d45c000500b80c070b010b5420440360702c4405041e07030381c64019401d480500003079003c0b03580da1460001c594038868101e0424201b4030502c10788640b425010041044901009031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 737026753 1250 737025503 737025539
    0x1e030f0c02030c0c040506061605010e01090b0411010c05070b071b060509180403080f0405010914030316110604021c0b0a02030411010816051b0316060c0822020a 71
    0x16080021003810a000402101d940135038100c904020500308400092414454808603845d43c002c1200a603061000a41c024803002c3c01c4807000380034400b014038140e00d0152044408403585e14440318200c4e02c0c0c1d4418119075a0b00d030b501038001e2000c07a00b008480385030768104150458a00c00480341d403101c2500d0590181f4014000e176121540c03216540410801486c00c50550200980304100401000c41d6000d80059008840c5020f04211501c071420064050007524030060207a070b0300744200e6450000000300075442000f00c0d1068204201c0c200070110b441d8864420010031030fa101c40b010802610304030221040001810507240d886284507030386c034170f0701c80801c030b23490302c5510740c080308000030310031205a5001488424603240c202403400c0600700110710389800c04141081404030700484202c0c452070302d401c1003601120031241c64401c0c03180c9000d09030030820030845419061480110010303000c2c1c0c080307174050f5402c2c40304001201d182980380b900070202da030000d0360310250780c0f0740008002414562401384 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 737028003 1250 737026753 737026757
    0x6050a0c020a26130602010501151b08090301150e06010c02011d0105190801061b120c05010609110711010305070c2d081207051804051504020c0f060c0a1e030f0c 71
    0x4c00e46010000381c211041640320020b28142d00c591401861b90240c82090156414205070400d494203051103441401840c080f10341562a003400003880d520310b02c000e40200d0760110290300581c0e0b5404011648403010300b030001e0100c0e0b903000714140c2c0d15032000084c460502c410326086051030343e0303981c0c2c40315541c00c45103030100460003840052200b50f900c4110441200d45007801c01c4401c1c022070741c89801800ea12003500003007101012270202000002c1d04100010015030a00f400001c100444141440d40a501e08444260303101c41a0b42c0154000d0050501c114129214600c0709105500d5524891522035403000c680305002c40c2804216200c61250b00d50325000d0900d0548a01d18500241b020381d901030040c505220051082e00000054240c003241c14181c1680c01080765180e890b1841c010038a040744155110b0300208140800c6e000010380681c0f403035051400c6400303540711062004541d11940501e0000a56510b10314045e90210300c0001411310418600082d03076100c0c0182e02c4e0126000c060329940 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 737029253 1250 737028003 737028037
    0xd0807120c1511220305011e050604110717040e0709150806100c021314040c0b0405030c0913020d081314030304120206070804030f06050a0c020a26 65
    0x109200780d548180b0349454020408100f195120301c00180c3c0c13802003401d0031180c01c8009070003000c4070540055840c01194008001d02070380e02e8031240c800189141311010300d94549848000382180c80e01d802000d80340013840120310301c1e29046488100c815018415110308428080200140c440103c0e89603900c9141b280e516414420b081181c882c031803203c1141c02404105407002800300035030f05c507c10041c00c900e4504150701f1185407880401c54207407104010040d210318103840301c040d034407800165074466481112041038507515125040300a01540c0503154241e4030824910704642032829600380c0010784c20009540c150036aa00188100040e124100c0f803808001c10301d104034030010030000016042684d1380908080303130f44001c01d03a40d0140d4410f420b00c4003405c9400c0d10039515041c04544683c0d0b000180360b40e49079140d04103403403e402c01200489039130f031511000a80d00e43c804c0c41401d840890781d9014008010741615682c035003101c03007024064910169400140911501310042c00c8a0851011001e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 737030503 1250 737029253 737029277
    0x1a0f070f1101120e15091e0a05070e010e01060e060c0d02010b0a050103060503061603110307020309150304082b0c03090203070e0f22170d1d0c0d080712 67
    0x60000140b20f03480c018007801c00181d500a9080032803034020380a081c461200c4103039102e0401c2071034584c00c403811000200003086c5501c1d01e001c010a042c140d06000303800300d4192036a40c10805d84140001d200c1d00510841c500d00600c0740c18802c1544501d10300004000b42d040685180c800e606084c00d00c012540542e65178003d0107014206180a0001082d09007001c200d400d243c50082503d074400100310542e552140d1242c0501c6034044d51001a00a10100c00c03641c41e490300c0b4030069980e6002e4280280301d4503003007a020150700c0f00041107038170031a0f0080c9840c0c00c5c40318140c0b1810741642c2600f00d500e10000103060803442610507106800124039141e50104d0034071454014542000180d410002154101c48200710000728442c10b030030b400034011110107200c0d1404000c42c5c04040d01c6804001c111105d003280082c0c048904a0140ca0311100c40401005201c500c00024881000145803c40158021618204a80c40d004c1941c0000c0c0b400350200c0c40c80c001c0300b6a94100040418141c400101d0b01d465010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 737031753 1250 737030503 737030507
    0x180b220906051b04030b19110304060e0106120f140d03090227071b02030706090905150a090b030106120804170d08131a07030f0e071a0f070f1101 64
    0x1803508084411a8048001e50b2040c40e0f840e03034891800090144c050000c0410400c407282d40b500c046007020310070b04008040c8002d21944090744280c90956026041c004206070300c81062091078204d441e00c0f0580490000c0c580c2d114140601c00c070340c05960311005030401415a8400348985510b6800790f40e00012071a0707241c410094039403180500d00440301d450070481e00d10201c030084029001005810a1150f0f990040b40f445000405c129000303405009240001408507000b1a40c4001c0e1041030a09000c40d0b9603080c400c90030607000c0700c0d0050b4401c0d40da54003001f050155a101100a45000d40041810740c0c0b031300200c2802031407200b012580040d0000317080041c411001c810040100f0400701600ca00c503000348005002040c060840d00d100da0360b4206403020018011900070920b07040c446c0c0c00038545000c0b1005801820300900b560000d508000105070a070b0350229010058070400201140108408100350320150804064229040c60801c540d80c04110003080c0c030b1070002c1c85405104000c1c5068000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 737033003 1250 737031753 737031761
    0x265a0d020d02031206091b1c0b030c150c0f0a0c0f05180c3403020105070c02011d030a0515013b09010b060a020c031501180b220906 58
    0x1203011900103008540f100d1142c584513076080082140c0480580d140c940e56000c40280c2d106886072800c800040d80054982c8010b00080c4502000400b081001211024162a1840840b00952017550321030000c00103403900f80584a044120022070f51041d410444d29413800703106200170340b61940c41820403c00e10340c01e0005000074210a490002140b2104501080080d1002c0e00385114084041465007059401d818038890000c205030492000818849850092803c4000250015420100003801c01409408080400760707040e035070310941608450580f400c001d0383e500c109070715004041c44500401c1c410003559005280c21120300f401c9500d0302c200e0403021000440e40f54840c9000000f840b15603c0e10340480a0a00d01c0030003000801e40e1b82003001801840f0040c6cac00e5500c1b480201d03090031019400200c000708030605070704a800030314101c80c8102450400344580a03c4031003600c41030307000c00e0071900b000a0301e14001d044ac0d0702e031041c000040c1080c0840049074600e4030303980e00d00c110305101250007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 737034253 1250 737033003 737033023
    0x50d180909151a0306010612090602120a0b0406050607081308070b030108250506571905100204090c1803030206150a265a0d02 56
    0x52450a0f0308010042a100c80051040702c0901c004440f0a01200c0000d801c243c081c1036126804641c0da071107410b01a940050140e622a14807803401131030450038186889085c040c1c0328000c216505001542d61000035981c840305604c041150172420005140b04e007002400090403e08440c41d40ba50b041584091918420040c0082c208815402c0d07a000051141f19880076200c060314003035501c0c690950840ba820648001c10641c4500840d459003010009042c05040500300340c2216414000111084000c6002c4807400b00035900420544152200d8000c1c02c00c052030304c218184c903800c60000700480203d8229600c140e10041c0c403082a61912a4070464a2030b01c500b403201c0302003c00d0308540b4004c0d40d40f070005000700f03260b140c19818131101c1d542d031081c0c6500034030404103c0c1d413900e000304001c4514a20544a50b80c01032140440394030790302c003106082d22000c8008003280e08c206802c0264628610f041c4280c5055100903850728203486250b0171460b4807000901d1001400e441e108028020718203c0094 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 737035503 1250 737034253 737034281
    0x23007050703050a0308160818031b010b150711060a17040308070f080403020a030e06090d060902011b05100914061e06040c080a0509190f0b0112050d18090915 70
    0x9641f10182e0343c100d144950002c00c400140581d0009601d4114950710403a240c40300900c0820700d01e002c5005054000d24010182512550880003c901210701580103403140205038004440c06502541040b20140510080514040c810349080035000c1c0c1e8039400035501580000c0070300d030400c420b01e600720328180700c09115480c0403002e500d0035850080d120003099400a040001351400e08a1655507801070301c1e0840801001300316a004a890f0440003005c00c1c2004901040159090b41c0302a46200942000250410082d065000c1c0341007a4a0051241410480d1b220500c002547d5030450200032540c810400c4502a1034042240f203401c0b4803540000309940d104600703102c1c081035025030000026800401088010915440c0c507035130700342030610100540002d088098460000d10010314102c002060048640210b96602c80c12080385440140c4000b41080e8441c1c04d040031250300c201030003c07200070200c110241c4203407118010010344a484c24141c500141041d286d40c0c09d0081d92141c413510201c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 737036753 1250 737035503 737035531
    0x3120605011106061905100306090c050c0d120f090503030402010801050f2b050102190306060e0616170a021f050601081f0312050301080d023007050703050a0308 71
    0xc082c042e0707500c2000074011070040e030810580303071180f2541405003400790000a200d807859601d4440700a000b4139242c07061b841c080c0c0c245080b080390750340608101c3d151b20000c40007030403c2001c1170b031055580406601002104a5682c4140c81c03a0300524458010114400c5010b159203080a0000410400041c1c005610a4000d2207000c06640e80e107902004a501d42101d0100c807134114030680c0c080c0c0e841d1083e0058031715400003611482180d101481e000000003035407010003600b0349461045414400344811150000410055031009207c00410202d05a20813020300c100c5032a4040307180c4d030941008000c4005030303200c480d103140c0183c0030349100b003000880c0c18810042e034645100003c0007a00702a000000030104615500e08040c001c0820001030f542040703c8180d038841c1031348024070780e5109129000d4940904a510308d403091000c21050b08011003840c081e0b5120f400c440c60580f001c5280741c2c031200c0c1c4000402160000910a010b110000c602400180900444605003d407028034020510040c061031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 737038003 1250 737036753 737036777
    0xf05040e071415090d0602040302090709080d030e0102071203020307090512030d0b13020304030207170115060f0e0307090b0913051f090506040b0105040e03040b03040f0c0f030312060501 82
    0x2488003100e0b02c0355046420b5410030541c400090301a00c00c1d20b00680d001010403501d2400e120a540080003100c0c800e680c84000340da84e48104079650225409081000d03004070602d14030381803180d0807210034156890700040c40d0015036038035070041941c0802c0d41408260040208070a440e001030104008101c1030351514030f1a04802103840e00d901c00e5040c1c0354101035640d0030401c1c96484620000070341c4030303440e101103640c3c1c109030901030342d1a000c500c14420010398980250f0f5041e030303040c041c1c03450030012032101800075820450309451408103402c0040400c00301045c24184c559040003e54001c2c01540e1001036a11522414096603047c003c21900e41c1200140b0385c200001d5000514403c0c1141c1c141c20201d0300603c0f482c0c80805080184c00c040d103113114550511091020368040da0f4100d95040320200451045034940e246ca0707024900c500395501e141440040c0c00b00d07107007540000d2041e2040c49000011912004280c1d813a000303c2e04190b000442c0d98901480003106d40c4a640c010b040d09080102c02041 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 737039253 1250 737038003 737038019
    0x70207120f0204090807020a140307090e1b0616060b040e0102090907050f0405041a09060307050d03050702030f0d0903032d0507020d080a020a020a121a0c130f05040e07 74
    0x201c07240081c025a40c410501050101103000e4801e00c6a00601c0c03032100d0380c1d8075480780d0b0081d40300300d100301d109004404000450860700c2c49403950288c01312002e08440d407141203a25210203000d41c1070b640c0200c8100101249002d03c10f40070000b01d03104035400a2400c0c0d00800b84002c0b03c01c00100d41406a2040155103455a5030140707090344070040d440c1c4580e503000840c0440086004d140c0c000b98119003402000075807160156016408200e0645000009948010415683d50940d11485401840304502000841e100b4001000c2e80e50000c1e0443ea203a5503102c445524111101e0344020000340d1186080c0105540194a943c903101e000c01142c41c2c500e850034014034280f10b16060b26042c081c0c002014030464807805144d28046070081c0c442a100c000741e00d0081c0d254406800103d10842008401103032400f21001d1040707400350080801498901c0c0020070380d840c0540a04201c12809040c040d80702c0c00c6400560200180101e01c036008078440c5085d0902007518200d040365820754000d002e051184034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 737040503 1250 737039253 737039273
    0xd0606020f160b0a030b030102070f0209070e09130615030c1d07020705041a1002070609170a03080705040e1609142b0b0a05090c030609100c090510030507020712 71
    0x34522000f220782e039a650010980082c0101d0282c1c940650000c110070342448045070074490300a0003650000665560080d046903594440c42249034010b03134940106040008070300620803501c0c0300710800104500c1e2855004290b50588e403080b2541c0100c00310034816654141d4182c409581c15100d41c0c0b14174148014080c1d1250003602565010b540e03200314945124040180d1005a4000600780d4242e01304440740c029260b5070f40f409654080340b8a0350001405802106c01000c1c0b100d000c0014000b0f0300140da8044440000140c0607104115060ac0040b441104400c4040c1c0140642c82c81000d03075452516001d0702903d806d500807501c00121010007540c1e0784442d54200301700740a01e401907442820003901060340c001100d0300604009200c07010400c4001c940c0d4022402066854101c3c1d48241001e070800d0383e684421140c80e4403c2e0003020221502c0000741d007011802c0e8000d07061022100752607001081d841c42400c803090000a0b21030701484403581d01442984050040f940d000680f1243e1038984803d40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 737041753 1250 737040503 737040509
    0x14030117120f04092a090602061b0304110d020a080303091203130b1f060504171c080c1605060f0f150618030a0c150801030b0604020a030608030d0606020f16 69
    0x4c90710344036510710050204040b40890410700071060114402403c00800c0c80c0514040c00025224040c045484034600e4100301c0d5020403d0600c3e140f0315580d035510b01c11143c90740500640c1003499490305000607910100b984003d8503540c00210740f246440d240c418500400041c9019160030b04006002410107640c90301c03911150804418005a01c40b00200080440d096152003c000100800418030aa000e4020300c00c68015954140c0210303510200345866004503800d408494000150881250303000f400c015030300c542680e0070030b82082511340c0303118003088034448101c605400000405c00359000d007084042d00070044111900b000e04d0001c403403420540c5640740c854814000411681e40150000c14090303807102c1c2c081e0039683c800c1034034540300c44030307086038000ca800d003000041102101074451070f074007812a0703001401440603807102c10600c8000d40c0b014291008040c3c45020220304107074104002c061607000d000000039800d150501c02420202c4a4182d00c030300360010700c5104001d0081d0204c203815 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 737043003 1250 737041753 737041769
    0x2303010608040302100515091b04120318060527060307110f0a0308160e010903230a11030106050d020f01030b1c120801050603060102070e0714030117120f04 69
    0x4a82ca40742400ea180c502c00c1e01000200a05040030004085183d0440e11080d030415a2030981e207442c2d054260381c155a181c0c002c00720040c0240302c1003184929100007040914003d04243c499000c0b40462500a40310300d030000400301d0340010303e945510b0601d11101c800d889101031207600050228000802c2840003406550400c8100208850a00c0c01031210070031345100c00c001c03105180382600c0c01500c4103d003200c0c1c041140d850800d0142c113103400b555211460f204146c1d80ca20036507084d99102c1c103060120b1944041e000520409080110004004411070785000300051a1861503040c1010701f51241d070741005006560030602c1320010b0f2103001080c62603000c2403c021420308080c9010401202ca204030b403042c886204891001800480340c10013842c0c256650b07454005a07241d00c14801c845c401900c01900580c00000b080106800c0ca00e0314940240301d40c60034940300e11a12038130500b50303002070f0010703481003107195061845c0342c808012340200031201c48105400c102d4240c00307140c0d49018910a14070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 737044253 1250 737043003 737043017
    0x80103080d0f05010f1a03040309120f080c0f0f0106030309030b1e0a0b0f0409150914010c020f1501031e02040209120102130506030c0403110a05100203030723030106 73
    0x1403100ca038221441e0b00b1103400080101c1e680d1451900d29002c3c02d40310b01d1551200007002c80c6038032408481128800c0b6019252042454940206041c40c9031440c503003a200300c1c10b00c05115000a48042c0282140c443d00d00042102e902c4041289007000d85914400c042d80c1e252103c1080000d80000514040300d421025480c6903a03102c0c1c14000140e0708042d040700c800c6480c41e080089040c040e5002502001081e242108100c0c000800d0108071150798901919000c2e16a04103a003894498108801a41c410302c4001440c0e0000c0540c1401d4514012410025801840d0381e21104a010000814410050b50400c442545103842700e620841401034441c400b2080a01c00303a043d5162034045a60005020f099806204461401c1d68002e4000340350f000d5a10b41c3c2c4000001d058500b000035039000f091035015a078070302407855036003500c005031114410760011240200007825540e13508645210042c02c0d0041c41d5a45440e070401031003003001120350414410a01c20a024541c01c00c0e094030b0641c1c0d01f50a10318 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 737045503 1250 737044253 737044267
    0xf0c010305061306032301020708040b031503120c1002040623090316080c01080705091e0a0b0307080108070f0b0c01140a02130e0f070818030f041a0a08010308 70
    0x2002225043c02c55210103040420010410401e1064410f80141010422040a01300c00c1081d00382d20506801502140051205001c2c004204001f5904008422080510104d414021a050000c00040241c115802203562030320098107015080c0e6040000310114034060420901415a0018826140ca80341a011000b00841c0300d030012213035084070080c00c86402c040c4c1c1803103400d10344c01c840c000e09216000340e84580c031942d40640030f040e0041701c16440c0c1904181a9400344414100d000c4039040c40c80c1c00e0701b0580b8205481b581410070180600140309941d903e844a03014000c40010f920a0f02e460380840c1d03081004221a140d0b034010790b10200c48441d41c42100262684c0540803515001007210400701c00e021160b00c065004181c000864412940c50343d58902050b202042d0840304102e001c40c24400003a030341032081a03400e50008990910f00f20a80040110700c0c03454200c40001007003003000181c1440700540390700d00409522400c840541c500045180018850b80040c8002446403030040744507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 737046753 1250 737045503 737045509
    0xe01151e0f0c050613060b0910030314040b030c181f051b0303070903031806120e030f0304060f140408120a0204120c050405010e011d0408091e090601020f0c01030506 73
    0x7001d1880c0c2060441c0c4640c1880c410300981110175120449280f803400000542d141400c90005109446403810000501d107152000e0303842c00c030403202034682484104000318503c0f4100c0081c40c040c06888102070f84032164040000d028890a550b900e01c54120007459000840d044503c5034000b4809203000d540b9104040c2c00d91910700540207065080303010210030840c0065000d800b500440b4029690070f40300d0008000e402c02c20000d40d024540c00140c0105550740048034903008a001c3d03c04100c1160b00d0410034140c2914284c2050350106c0300c02c0e4803140a03400000650058080e07454031210314000e1820941c0c2c80d402c442c4143c05100d4540604400011036a4030380784e041d18020b0655101030341c1c030160700745080b0440f114a0b004507407007035107030000100d600d8805440300740c103880081b0b00894422426140030143c1c8040240304075a605410030550070a600c0d00030004111200ca00941c0714020340f600108040020002c207068115880002c4400b4082d1000942141d804800e007000511510b03a00c1c04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 737048003 1250 737046753 737046767
    0x50715050403020411120c0a02070302040b030f030a080f07080106080f060d050d02010c080a0c09122909010e011506030c0e060f092b061a03070e01151e0f 68
    0x301070740c0700e803401107040c0c0710620001c0200f004003c1b0038070b41c81d100d560b4114924194081c40c480040180e05c0300b2018001420580c2c81088124401001c64000c02010a0364900e142c0c4400410301c0007846200510107500f186620b04c541100c001c0c10060119070404100500f00e000c000c0030b800c2c0140b1503001142203611001c105601494002d806d4070400c3d013001e18041d002e000005a643c000501c6a800206014054071400d0044411650760350b00c00361074100208000b209041e410780b60290810500c171854003000415802c5584801e45034002440c20b0300007035007160b25144484c8410b034103140c41d118408681004a0b800d0701c40b10304000843e042814411181c808030040441c2d00404d000646603440d103080f1001d048049411a8401140040c407030b56540032000f9110542c65074500e05005000048060700240159051a00703520410544480060301d00030240d8421180c03102c0000041c4050400710800d4020f9000c00d041800044141031440001c104400031201c0420030f205240c110510300c606070b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 737049253 1250 737048003 737048009
    0x9090402041803112803051b010c02010c140703140a030f1d0607090b12130f030c02040b011106061215040b0708060a0303020c122104180501030507150504 68
    0x26000c2e040010758540900b58003040c842400c924071481100340d0b007900c2ea001d156141e07000c200c101e4450641c034a5400340c0c0c0c190000801c060401c00a000340300d054240174400c103070041340c040d03001050450808401408103071010482403243c980400c50200440d4004100301c03200b0202c0c4030081d696945d07510040307008050303940082207143c4c144085072241d0807600c00003034120880b580035201651240c0ba8161070606442c4500484030b031041c020b0b5a03880002c1c4001d940c0c04691003034801000794640d911141c6880704da2030110081400182d554084d82000e1003020309070130007820b102e0303544100c40c03011395528030f40140800c3c80303504c44618030700c4500403d1062a005004101d54069035040c20b06d4410074100b011909940066580400503142d40b82908101c41100c1d0150080d0007426884d03401d110a0001018000e5102d11502141c403003803030b80141c40c407c01929100d40c00da03180c500b0107001401c010724590841d50603034140340041c0040b44001c41c5110072943d0b0036440c0700c2034441210094038a4080c03a4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 737050359 1106 737049253 737049281
    0x20a08030c0d0e03010b130903030509070f091814150603012a1106010605040906091103070810050a0e0a142202060403150c1b080909040204 62
    0x3d0801145070401a002041c1c20446802040c200b040d1400c0017a0001e590303460071300a2503810311911f0b801000301d10107000403d00d4000c03a10303d0140c50b4003d0100c42070340c40000c002007000e0580c0342c6c50240d9000c02d0786c46404500f00d00d45900c4803c014041d002c80c1044200140d540d01c0c040c0b14031786920091041e0110040001c0d0f092032101d0038801c000d0020301c00d5582650380005e40400c8054024812640c41642d15410443c1200955130030758000d44a05080480c5500f860101c4001d4a0784840d0f90302c0d0443d65a541d060880603c0c0425034007003600600c2950000c90900b9818900703e00c9205d1080b414042460035618031800d0074402c0310052a00c00172031622542d00b80b0807a9940c08074500003840d1a082a8480d11a581014084c4980d5504a591101d002c204141c1195135103048010a9030305986000b0261240000c902c00e0000861240b00c0801c0003408556903588031107440c20601d = true := by decide +kernel

theorem cover : BRFrame.Cov 736870503 737050359 := by
  have h0 := BRFrame.cov_init 736870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 736870503 ≤ n) (h2 : n < 737050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
