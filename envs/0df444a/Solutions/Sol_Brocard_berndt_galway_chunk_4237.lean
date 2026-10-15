-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4237
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:58:14.232624+00:00
-- url     : https://prove2.me/submissions/69f734ba-0031-4e4b-ba87-c7f98064d578

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 761870503 ≤ n < 762050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 761871753 1250 761870503 761870519
    0x109020c0601030f0309030206070605010f060507021305091c031406100c1e0f050307110301020f160f080a02030301091506090e130605100302030f0105013c0e011e 72
    0x1c1c1100d0b0041e0130418001d10b181030850352520305030000394002c200092500c0c10400705a10890403580c85601a0941c43d032a034070121280e100c1c001c0e01940c0040c2e0401c0b070121160380c03035202d2904881c03804201d5400b00d1800c81c4000c0c0000001c401c0ba00402d556407903180c0c0104120407125885042103941000c000c0c40d001029003903141b5600c0c080c19004130b4518201c031041d41351001c448103a400c0100314503000b445d4941246d40b42d11209044518800d04040c0940034141402030b155081d89100c0003034105544403103800d841019a15055840b100c2c6000b2110104422400030001c070800c0ba400f6550725030408104a090300c2d40c1007910304441d105d80364104001079000403900242c43c1c02c1416400030303031550120780480114240740540118541030a0112078400e0740700c01000c4a20950a999000404030040e03401ca4109228821051400003244014444160b896100103030100000f10f4104192201c03000700340301c064210f8014412060300622031038842420405c501400c1d0840b000b09a81004d0070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 761873003 1250 761871753 761871763
    0x2031c0e0712110607080a0f020c1e0402271002030a05030a0c030f1d0c0621190905012705070b0f0405040504080702011701080a030c020402161101080109020c 70
    0x600c150320451192107001c01000300c1d030015210000a0109488a6171410b00c5010355100c0c081d04004510450f2482d110035002158046030800024124000c1001800b00054030b138560100050740641e080140c141c0600380c000c64070102250384846091090b120100380f00c0a52160a01441554810b0181185560340710741200d501845121010a0b404007174002540982642c90701c045819041c1514107403490070000940366484a032100703c0301c3d0100f9190900006108a4040684868a03051001100030565610b00c5d0800e90040c541552000c113030406008070345011200b102c0b03a075141d000741c1c2038886124036401d000084a07114564120603507071303410340c3c0e8540510032110446800300c2d5045840207400156401400e025200f488249064600111564029601240420f9041300b03010300010b00a0141c42c180c40c0e0b00790081408045988003510300680710842268819020014203162540d035041d440c0f181c1d4403419688141e0120140007602c03440051300980b41891050144404020340022 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 761874253 1250 761873003 761873009
    0x915030c06120c0d0b0d05010f05070c0c03060b0a0f030f030f030513020d021f03020d0f06050102060a023702150601020d1b05060f10090204060c02130f0c02031c0e07 73
    0x9151381d420603441a402070048000c00503031006075285002c2c1801810342080103200458a400c1080b50756100080c0c0c1e201c000130401a128490700c2c01e0a10009032158008415058010a070302015983c464030385403101c11a40003118540b810381c11000401d41c1202c1e2100c50300c00b540c00c05000501c0d204859104115041c20003a05c20b00d000000b04055450301700b00c9102000603014a05c0d42c8800050000c0d0281d4001103040300790a15102d82d40c1c109018501c1000190b5105a02a203921340303a1300c8103900690004c10045482c80c4040b011102c1402e0b03111254210740c01280100d2101c401e05010107814064940e0702c40c205140480f0401c041603901103404550185182051011109507005003850b00281500081c814807401c3d041c0b24a040702d964040e8400c810084640c0042078844440c50182e0046100310404039034022002001484c2a403c2c0782030007600d040001440e41d01d420021800e40d00e0050220b070250f0000144204590281c50440c000740e43c05041c02d00c000c003008110140e561032588 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 761875503 1250 761874253 761874271
    0x60605090603160c020907020703030207080c101805190303180b09010c06020c0109030c0c1205070e070315060801050f090103150b0303130305330105040b030c0915030c0612 76
    0xc0322264900444c61440340940280c4164201c5c5003810000c0d40d600d076140030036000351142d041d00140c043d00004001902150142095200000c001030a13600081a0610b003d241401d20001140c1a03c0d0071001d08c12000c000a1500034952035400c000d481c0d1103440c6003d491040c05801e06006101c4d4dc4411148104420702c0e10b0420310000381003031402806803258280c515401c0c40310b554103050740120344814141c06007980ea54519620300384d0205810800c40020f1854000352010008504111501030703003e0942c1c20003044203551030100042450440e0410300200b42c601c1d0050060341030135102c9000c4a017040e190600554115214542039000c4504268035498030b603807804020b0344061040d0361040c00314028201d12243c17685890350b20f840d002000c00c02e1114010501402900d40342007419000e43e14221000456428042444050300001540076051702c50303c0300a042c0760b1161050356107c2c080f400345803084240e50004141c240140ca0056038460001404505910aa040c1109800c05101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 761876753 1250 761875503 761875531
    0xc062119050a051b030a023105120d0813050a0b0a1803050d09020439090302220e1002040f0b0403030210091e0326090d0c0615030c0801060605090603 66
    0x2040114080d01c100307844c04042c101070310300e14401d14901e003820540c00e0000200388c1010070344400602600100240c10b00c41d1540c070000c1d0b091411802005165041042c41c50440107c3d07020b070700e500d49011605901101c502102800b0407036003814900c01e1180c50055100200f580543c6918001c0c60342c0207e0224081240c0d03100b901c0c00c11540c0b80d9000f8594402030001103501242c0b1201c803150054090051203040ca8500c04014800a11900b01c010030303640d00030844220710064241401000003000c12030304001f90756091007000301d5400c100ca000e41340e01454000d40d80340d041009005502d01c0340e80c0107021042041c00f040c800260040341ca1948071030016000030b5620040d0a08104c00100c5181125640482322031800600d58040c1030310b4452841e10341e503800c003413142414050a440040700c52400355049109842e0441e84258401c0d01d0040c050034020400001c0c2844007501590180e1048074841da2200003004140d80278000c0100900c41810968204102c4001007641403100904240c515000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 761878003 1250 761876753 761876761
    0x90c0105031b09120706120b01092111061305011b0b180a060504080406081605041a07020406060203091e010c080f27120109050c062119050a051b03 65
    0xf5854907000c02c1a84c081c100d420341c903981c010250800d4100014505010700b071007171001165000f94034110440303c0784d08085080203100b076030f0141c2c411030101c01100c141200380b500d5400c95071644041c0120380281e101c4800d65070325010002d000d40f040315608503850540301a00c000859401c01c02d107541f04400c0c0389051591a801c00d0468140762a005004140c1c034a800c050100b8400c1900c040d0003604c44d03d03100c107100d58466a40c203000350300f507244d00600040e80c100310a0118005402d00180c103840034035031281c00d00c00203600080c1038822540040b0300603803011031405580e02c0d224030040040680e0b100303215410301116000070075490b2011005060300d000001d01c00c01080e120f0084400403000c84801100c0745680000007508107904944c000d116080e82403500340100e50612a1f610000d600c1002040c00301380d2030b17050040907007021182c100c500c2e070041e0800f035082d442c10450501c00c8414015000c1c601600154070411a400501043c9001e45804200a40040a4080da000000c05502103e45917030f5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 761879253 1250 761878003 761878009
    0x60909151e0c050d060501021c1d03030417010c05030403090509130b18100b220b030a0b0702061510200d023003040f0201020a020d0506090c0105031b09 67
    0x8180780c40e0842035031905a20320000d0754040c0c0580701a02d214841408100c0d41c80004a80d07904580c41015400c540c0c800101107414084c0d10041c04482c0d015600c072080b0740c00f0381c001a0a41e0041d600c1000e09041484000d44020300c207100b80c0260400e1400c04909505280d2030041400b5001c0c060107001c3d410050200e50310a8015407540c045681c000d20201d42494004081c1c0940401070300030103000d22544211031000c05240c09003001d011005005521a0410600381d801240c1812810030f503019903580368035202e41c50501004580a006080184c4103080c80d03800285410f000901c1c007002c0001d1184c00b040550380340358580000313090a103031203140040311060900100000c5000c1241502c0b9010314100025008142105071010306c0c04140503c860460032480e5442d1611510400081e003080050000313000042d5100c83d160047c03044900d002101d138046a078000038504103440c0b50b4080d00410076040001c106401801500380713404d07819801c100e070410800440303140f50740da0030501c04105861035131 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 761880503 1250 761879253 761879291
    0x121908040201181401022a090604180f15050f0f04050c040606020d17090307120212070b01090506121f2a020f120405040b0301090b090102030a06090915 67
    0x100e80a52030911242d13039402d19100c2c0d42e0031080d1a6026024143d50065a40f006d100700c407002c51080d4182844540c030400410540c00c100420b0291f10990740c1d2141d00890741004449000541b00d1100d82040c21401c2c144443d02d07103009071403065000c1c188030400000602e006601c0343c01c075498100036526a1150b1800c0b0b4102001c0c5810250402c1c0303410700004c1c407180c0c000380000000d0410344403408a00903000881155480880700781c2040d910030459440000d17501142e2040759601441a680955507504098140380e022540554940320040014407982500c0c0c410036400c140300300c0c0ca441010030001d0540351030b078000140c0543e1040c2848181030b41038001d9045564441f5400f403120034252154424001400301c00c00c0400010300c05c180c00d0740445c00001412541400c1000c9205080926040810010b40356100340d81e5050754071400c0e2100010741101c0e00c140190403040000d03072249040741c107400032070b281c0e50301c070308107450030000740e40003140c000071500d40140140344010445c40104200c0324200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 761881753 1250 761880503 761880527
    0xc18020c2a01020f06040305090a0e0f01030201110a0213151d0a18050705060d0e061608130b0c030a0e10020702090106090506180a050d0c0503121908040201 69
    0x90194251121511920201c41620040c48240740010210114012a910000c081600389203500260120300400c0c0071390043c1061110040c880c405854581000740c6521a055031000300040268005008541e00800c3d82c403424002071000300b45820280e000140d1124944021160b510360794100c80f9148000d544802019110361303000f100c502c072032420a091424104681d8a40241d24000d8003240000003c070807681e02e0340d04a0000c1c4a0b032400c007010420b207580f000d14400c0c0d80555900700780c03488640501845101d400310380694944401c08100c081c09198008000030032040310700c0e07542c00004c1d407240340e0550440340c541c14207503d130766410b40480e005013030113249020340b4820051150b0950802e5001801307014070a4424442d181d0780d44030b050300e0608103401015440b15060110342007404500c1940c00f00300a008020085e03a5641d14007003107a030246054244c0d805490310f0ba091000c0e0608004220221700050490361502e85030f04e0320b42c180101c01c000348004001c4043c0101d000c6da0b1050341c2c0700041c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 761883003 1250 761881753 761881777
    0x3011104091a060c1509070b07080304020909010b0a0b09010504091a1302090a031506050d0f1e0809091513020d1a03120c07180903030513030f030e0f010501080c13090c1802 76
    0x40c0301c89c40c1c140018a030700103c50891041900f4400541c404006024017643c5800140c00100d0a50816414980507001410b0890420409000000e8041c80c6400754002c9800c4030001c0d1183d07080030381d0500c145540041c80a03021310740100004100c5864090407030b030449801c400030140301419138240c48007400450340001c0e401130b00c031810704003844084042c0c42d540c280b156180d074003007000e40c0e49a090300703510307030403010b805900c2c04d2081232070508141548551105500700f2508108140d4400101e501000394018940b003607021070040441c20451050050484040341c2e00320b140ca450300d0010b903980c2c005a4040791401c0340481e11400ca20310404c07868010341080004100925030541100d801058020742c242d0001e420200862010f200001c0d1880311250107580d0400c0364426404242e018144c1600380003168440c40e425004101c03000e00c156406868000c1c0a0030382003209004105d05011010034030340c0068640b142c03910001d044000150111600616a2400c0744882260036009000306403000c1030b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 761884253 1250 761883003 761883007
    0xe01180e0c0301081c09030209090a0f050d02100e07031217041209050d0b01091a0d15051b030a0b060c011a011805030309060903011104091a060c1509070b 68
    0x1000c1003190740030354141c5a5440480300000746111412081d40d8030f050580020605000c001d00142c284406041d5000704804220b030100e0013240d0b240c5c501c10303000c42401d51b21a0803001800803030644c10702c00052a03a080700000e10070101040e038003984501462000402c901040b51008034402d006160300b000140f100da420000d0f52400e0306052030140251052080024030008000c5003a15110143c4d190b460340140400300280e0074040c040005080c2d4103108049100e0400e03900c840307036580c02d584580140c825408415000030022150b01510b0015004120741031048214072803860352201501d9208005800208541e09007601060391403060b03281a051550030b0034840b15215850700c0d03e0040c0c5602c04c4e62983c40c0d1900404440b40380a0b402d0144c2c0d81d040c3c10800110301d0501d0842d0141c14520f00090000540c40c0042c3c0c0410b5042d031082c0c1c05015415154900d08240300c0090100c0c6003142e4003030302e1052601207440301c443e4403500307500d901d804075881d80301c0412280441005050044c00415030034903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 761885503 1250 761884253 761884261
    0x30506060423040e0a0b102103180803130302090c030c0747090607050901270810200a210204091a040b010f14070501110c010b0f010e01180e 62
    0x1b000c8050101da0788295100c5550001440c13074800300007064010843d120102e81c1c083c050354102c409902c940404241c41c0050440841c00101c01d0008000c040741c0315201d90705d420701c1c2d441889040d000040000c1e200242c14400c00400c10b000a08030303410640d10484000c030b40032581e1242d9543d40703281c00516154401030483e01783e030300042180c92521011810055883c507a102c1116030342e1030b070003101c01c20001141032010502c154000e2502d50340070070088940c000d585032100f00d80b24140c1d00c1d0f6405100300350300480107820041040d10401c00d01d4110030603081206010510020030034031a8003000e01c1000106001840b55407900c205500056039403507010342da940d035240200c50203800c001d1841c201c030050b2038420b00c02c1403034684607050f0f9051068403800c40e001c01d150001c0d200c0e80301405022a41d0b420070084100010002c0c810308918076010390116481d9082c80400900711111041702078003c5500104590036680c01c041c010601640900e0300b2104a80d60380d0100420b860306510050002910702d00348 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 761886753 1250 761885503 761885513
    0xf1e030a0504030e03010501060509130e01020a0201090b0c0405090f19050405031b070e01060525030306060905180115020a06022107020a03090b07170c060106030506060423040e0a 79
    0x14000c0f40241d9804202d104075070201800c0b201c0a12400000c00c00c00c0140380214200032001600940c0e58074400141c800d0350a0f10282a68003820b07240740141d541d05032402c104a82c0c0308119801c1035004402505050901020908041e0040d1075400d081440300300041c0c0059407040c1441c03101503a00820322481c01d01d8078002e5542d0300a1450002c00f000c0c5803608124000300043d4400480b100d9044034001a407a040c0c0540301503005034840707100815070420401162102100744600b8601c00d990014842d86842402810802e298005d40d01c200013102000440e800e002c00d0403410349c1c200911240c2003001d003070b4003a403070009107500081c109400807504807080d265040c00d08030b00c000c07051030821440d5105102261030f24412140100821135000b024802d5001a0014002803840344030080300001700f48000108540020307c021b031960784101b0041c001d450b8180169500b00b0000d862207400c20307060800c000b2803440007201640320744240809090069456400c503a941c00c000b081a299540068100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 761888003 1250 761886753 761886761
    0x602040b18030105070e0108060d0f0515010914072001060515190512041e0204021801020d03062117040b03090105070203032419090f0e060c0f1e030a 66
    0x1064843e51070a030019252030b01030040d018a07284140e40d46802681e48608002e030038441d00b4425501c101e0b2034070048000590401402009441c7c00142241c0c0d0340c5001c0795181139a03003002ca01d04042e100d22040c00036064200c01e00c003640c40c01c901c0c028502c2d070481d110344500505640e4030240d03001a20100c0c6420806c1003100800940d51005034055000c0400f00003030700c4505c1501e82103e01d580410700014041250b5190002d070000710799000c044d02140a400203000d9821994100d0311103c0c052680c2d460310368042041c42c10a681c1814144072441c43c1c203840ca4000024017030800c40035021500c0c5141041800c940110f0442d00000d60300761981d0315030705203a00c10b03042200d007444158640070109025500000c2070f039101d006152107044900c4000710280c1c00d118020300090380c01c10300d500303400790b80c3d2515040310034041c018000c000209042882242c60039510b07840000b11440c0c0050051045440300102180c07880f0040800341c070350f03c0ba401f0141c0e17103110000c03a030409100340020042c48030b106a9500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 761889253 1250 761888003 761888047
    0x12030c0c010501050a03031e020c030a080d051509150105040b0412020a0905100605210a0b0f0409050c09040203150106030b0901050f0a090c02031e03070f1701030f0602040b 76
    0x30010b5a8981c010303c00f00c0000d038040900415030980036060002d0f040e00c203960900301103106454124800a000c60320f0070420803000c50780c0c0180814005003200d06881400d50154816040843d00d540c0b1401003140317072401500038420380e95054000b20469020760704807001002410709003a034440d91540c600301903040d100412441600c0034900090017644c2c1b400b4079401051104000ca401c145400000d94683d031001c009012603144400c0c0801904401c0702d02c141c0700341c1300d110f0040340c0c000400003041100a00e440781e1620480c90400d0072000315034001030003440f001c03080d00c51100360340710390000030b240004410160f00a50141800071030710701d605422000008205540b080c0340c0340d80302c50400c0420003040500c4e540210303007221b04000708910f6400a1450440c20b0058902d00f00c1000c03041c04900080da40d00e540b00d1840042440140741d03200804001100161404942c03011071906441da4154040c40302412480880302da1000380302c426412500100030309007420740c1d9031710202103850342046242 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 761890503 1250 761889253 761889277
    0x10807030b010201230f01080f1f091a0a0606050a090e18030703090801060f0311090c041509180212040f06110c0c031e0c01050c01111204110a0302060d02070512030c 73
    0x50001812a00c0011b2801d0b8501c1c00354058a40e01c40c2101400c548ac0c0d0f05100c1c1c0454040e04c0e6002600406c0c20300c1620b0720b4640042d8482c0041d4500411210180c900507840b18003004410011100c81d9607001030804141d8a00c900d054a46443e0110070803030314400c2c0c164a8089000c002060404c16422044010458541b1002480000d43d5013420701403110040c031000c1c14040c07541c0010a854500700b0206a0700070160183c00b410292501129000c0304148004040403490802d402e025800700b01043e0750750f920812109520381000410315065140004e480141524034544104041002c5500002022000b580c5da0b0340d11030300c0145100c3c0d507600350200c28500030b00a200d4804081c0709004900d41c1c0d082420710040c03d80c2c005d010011500c541c41000b4034032244d56100019a2102032082c0104030340000f8604903823442c242801d10041d131b40b110407801441150b0020040006071118000d42c0e62100002a005840c2c3d105418000d007416401c910350b2401e0308000042105002601000d04012038800c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 761891753 1250 761890503 761890531
    0x7142a122b0f211134121d030303150108131113140a0c090902041208030402010507060c08091614061b060709030209090309010807030b01020123 64
    0x4105a0300701e000080b404000421143c1d00d10003080001d16414051104503000140145402052100d82e03000443c050003109041c99030b074250700120341610b41a100c1c0c1303182d200b030000300c2d00d03590804404449007003d010300c0741c5030b004141013920502012406a0010303040e04c1eaa894a40c1e02040c1070304d100e500312400b151340c80000c140c00e0741d407030813070051f83c0d6a001110b070f4004071440d0300700420340110810301a5400d848041d18004000c041001d1400f0b600c9104010490fa07090820146c40030f0a15003203035404520500c002c011030020903054509180c0c018601581d0707602c071400100d50a12507030707402071300060800f081b80311007542c0804811310440a800551f03d40805418104c09100c2c01c1e8441d055900400312401d0f081c0c0d18250300180202030b04a0b0a041ca2180441503081c2044012600c107404200d182c8020025414a0700c40181d121400c000074616020004002a04401010704a5020169140d090f482203900035805400344164a40c2540c9204030f0a040d00c66040381c048510000d01288 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 761893003 1250 761891753 761891833
    0x1805031219051c050f0c160b0606042303070b0a09030303051306020c0d0e040603020a0b0a0c170703030f0c051605030c0118140105060603182107142a12 67
    0x411b4094500200303150118604071f01094468044a61000d803207644c0c841000c1000180c0701c044114071044190840740441d820b48100c40406080081c5648407003400c11003000b18408040e80b003179620003900c3c1d06060002d503d8031420300306a400395400303900410591001503040080500000c0c4030700c0d04400740d500c2c0c0e50701c50110300034003040c0c07282c83c44000e403c0511110103101440406000c0e105074403a40c40d090818a6083d15441000750580041d486080c1002901005041d414010300c0449a00c8101c18031440c880000004c15a1050685000948841001c0e001c100002807048652541e2158000e00c24608100103402c01c4104603441228448000e148024010750107000e094400c4000510035030a507601c4910088188480007001d504134019600258141c441c0a0011070b00d070000000c076141c542d2041c2c50030804801d464110301c800ea03401159000c40716039049010240c0300486420024211080304046003001c030f0500f42c80c4003e4041d0900080c140c1c100040b6695101080701c5c0c0048c103103e5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 761894253 1250 761893003 761893021
    0x90603100e0c0d15060b2109010e0105041a0f040b190f02190305010504051314070302030a03080117070e070c050307050304060c0b0a0c0f03050402010c020901061805031219051c050f 80
    0x407c000420b4080c4104108810b94600c151212170f9101c54020000302d10344031040300031401c55004071401c0b52000c404080e00e03075002c03050800300caa01c0f51002141303210070f003010b0711101c02c4a02c0090804503a14001c0c2c03090400d00c0c1e03d9404c4250030070000c04095440303001105034407035003490100144002031720705400083c00f440c140c01128000d942004640058030f56546842030a80209900046103200340b07100003005840400682c00c46502030b55801000d5410003e0002d101c0c0c0c1d130107541d019140d0002d41300340968840100d4080e0004194284185006038625050342940039100001d230960001107000200386030402c4a821002c1d100c0c0c114104580e548280303000848a2034101200000c1c001501d0505450090b417095810500504110201c0202076000510858090704480002100071030f407031941c001004860f001503d411000341001c0441c202e4070a070940641c40488055082c545c0d10044520b0003400ec45030f0f0001803a0f8102c0703900c841c5841d00c5000d460140d91070b00b000b14040000403804c607 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 761895503 1250 761894253 761894257
    0xa090203061509130506120f03030103030809060417090d08180a150e0603040c0b1c05090c220e0a061415130f0e010f0f0b090603100e0c0d15060b 64
    0x7000c03030b400744801940260003820010480c0342c007d03900d02600c6c0b01c10b54040000070b07410800e00740150f55a6041d854010b008c0007004e0b14000c0145e10880a00c400103089000401c580c1c041c1d40482601c544000300001c529051401c40540b0003100040c0001c80d03410502250139042c1001e07030740721108994400c51130b0f00201ca14503142d070000320310044a00c50fa180640086400900039104e0341642ca40358000c0000f03d0740812071103140f640c1c4541000e45140b44c1401b60503408898440a0481d4a10460210320301d4000c608a2800000c407500240f45042d03040c1d40200c211600b0310040f50880c044503e0654000c109040300d0807400b035641d000040c00841c05603000d0b500180041e0440c1c0629481301c4503600078040c060301084403261242c82e41c0c1780c0c0d07000c24800d40b410103d14541c046402011580624202c55403504038074000c00c3c5200401110ba100001c0d01020b00100900000700d840d8102c20080c14051039021960b40240002d200c00180310394418007000034210002c013000410f41d01c40a201c594 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 761896753 1250 761895503 761895517
    0x240806130b0a0b0105041d0601030e0c0a05060c07080d180b090f01030c03240f120b06012a2001020a05070515130e07080711071a090a0902030615 64
    0x141105030002d60090503d03000300e0b440c01c00c1170600600b810748928460340ea485900000c84203500d90360381042034a684c9030081c0701c43d0485e5100940311900200c80131402440c203c3c00b40c180140300021b41203070080780803c030502c014055002650495075403100004c0c40120054001c680340d449451001c25503060300000c8401d00040100601210111400190f003c0c0c001055490f0505644203054250605004202590b071820203e81c0441a401d10101c82024513164001414240075aa007040010b45102a0b1682008090900405500c0d04a524002102c0074070143c3c0c41d10b100e03e00000b02001050050604d2241000d2010408440d81a00490356080300c00c0c0007402039030003440104514204100348030b05800780c8200da10314202030900c4499404040390b00000c00c02c090340f820490400d82c42901d1a4001043d40781c0030300100304c00e42c400740d940c0005000c0e4a0602400f03041c0303014510080d804590f10a0005810034120303e41c1c60702c042000350000c40343c5a001e140151603d4000700c0b0088111a05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 761898003 1250 761896753 761896763
    0x60f0702010f09151b0c062a0b04140f15160206070c260f070b011517060f190509130506180708070305010c0906030203250324080613 59
    0x1809002c00c13412a600d0308440c44081006040c003034840c1c081406030000a020b04015100d141080d102041041c40312610320010040492030640d0803000140e0b44142150800e070011a03985400714060040c42c10480c40030040540c5200781203003c0c4280210203100d40c803036000032080490340090341030140d0f00c42e0801c072020b500144440041ca00061500b0340380300c4035250880c0d008035011200b0399000c401e561040c0c2c04165084000304d81c103010031070201aa00d015122000c44d0403c003003601580031305041c952602d05003130340079004006040350306d980408441c0030f1300c01040080800c501c450b5009600a6600510f401600b101e00040c21880545c000300090f40d5012008065660b580d00d0080b0b8071201c9002c904145008001000030342c000e041102c0700155000b9400007906010a050243c20203c0c560b105000f494010f10070890820b103000c2143d442c201c03500e011001c1d007590b90b0500700d0040c9170696526849641152168000300d10300d001400580300b070320302218060740b10101e1840c145015140c0040c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 761899253 1250 761898003 761898029
    0x1009180f0209090c04060303090503060a0c020604081c0524090c0714010b060c061501080c0a03090c0504050c0a080906220c15050c010b0114160201090302060f0702010f09 75
    0xc01410004403040d808203030003050720209859240080d0a440c0c4650095002494145003401a0718040c00550703040380600204000030803e07001c0181d210b0000500103804e83c030b000b050b0a440800003440c20340130060b040b50f080040b85007840300f106201c000d04031880800991032036502c1d414240007106c9802540d078171491034200b03515555407101c1e00c001c4510044d681d540300c145a001d140c4a4001910408003100c01405561034003109646122800142c0c5a04000c0d012043c4218000ba0004030f6540054504c0d004c00e03440f07140d080580c0c400b6041d6005071703042440c0200304240c592440303020b40309800503a911096503031500d5103401e946180a4403010a00c5803203805046000104c03d5481060921403500040b40c107980b016868108610020504c010440c0061001e040c0743c001e20401c1058102400c00e1041d00d00440441c91140c000d50102c50010074888000350250380c01504454020740c6e0090980307035203500c4020102e800350000e20049011504a000e00e24503140501012020394180c010000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 761900503 1250 761899253 761899283
    0xa09060c0f081929100e060d020f0c100b030d0203040308120612060c12090d020d140d0e0322030b06100e030a0b040c1d0a020c0312100918 61
    0x30030f4522070848036144990301c801c4100040c03616441c254003594000d040d50002d599203c24890f100742c800c00c0020412000022184890340ca02c02a50520804000300585541108440040c184110074403d00d071441000c1c144c520750140703074001303882c100015020742d000380c07070705100c281c0e076a00a500004001c0c013410f2103896803404043d80040d1f40000c3c018602810140c00c0c0d8011350a003a41a90070384000c0e1400200c1040b034050200a5a8104420400071312444d42a610001d41383c4000080f09420829448101c0c00100900c400341c5036220700304c0c1002c00224600c80039076075683d404100b2a0b8840d0201149036640900d44100e46400c40342c0001100580351b50742810000107001c40741d40c040c140b01c0e4034a00c8020340c1c1c030100304100c030701486000000c1550825081a0390003412650080c00798068030141028094a500f030340940120329030740050b8546001d8000700b415806940311070100140c541c010041c0c0208010801021036400c29070402001006a00c03001c1d0740076540350041e1440309c2e181608 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 761901753 1250 761900503 761900521
    0x1b0f123103200c1504030807210c02010215040309080d090f1212050c0a0b1f050402180d05250603050702160e0601030e0d09180213030b0c0c01050a09060c0f08 70
    0x107080c103020b44104d0900d403a8032540d540c1d2407500143c1c41550000034042a61030940103204101d600d600003820102c181c88013541c0000c0d0345040644800f0058001030000c601018000c10009026000e02c80503038540640c00303900107003020135500c11540c010180c0303100007400180d122034000a9a41090501020b0040a5016107459004000441e01441860141c10204a90102e2103000c0e24941039240d1706880c1c04138800c00e940d0181e0300554451881008525480c2c031403d040011482401e0320a070f5165403040c00c0050400e0740e0f001c0e00c0291f8461050070003070201740204000042c0c45140d2003c1046807a040e0040f40d85400d1000d40503420b42442c0f00030700031450b001c5505c5a00a00c145004034048031030f011f031542481c2c1000714450224580d00c4040c4410304020f0101242c18007400021030404182c01c414110b85081c0d48801b506801403140468420082c20088626207007406009001e213040082413440284034401c001c0d503610745040b50501002d4810f1060000900003a90381541503101e078515 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 761903003 1250 761901753 761901769
    0xb220803190e1009050405060a050a170a0b070825121e09030224130303090302030d0204030b06150309070e1306050408031b0f123103200c 61
    0x140e1024814030031440c40840c0d44502c04000f0400305641c0e04d1103040e18040500084d104042d0080b032040d82d01e41418400c503103c56080d1000c8440c0e20310304140450303560659034201a00c0003406002202c05804000b00960014441d07401900700b0404010010305040f4049240408150b41c1c50003d2041c0c50180300035100b0b50884c440040c0019521101841001e2082c001c48004a41c00c5000d41c201402c1300c09400c9201e808031100a02c9200345010902d00007444800c0795401c240300070300749a0340da201a41814401c006a03003c603e26003808540d12616410a03a22003901100c05a11680034004040003c2c0d880606072800303801c00800034442d20b0306001540340c86900040104401c2d00242900c00081841ea000301801140104a8990b0702d00384440225040202c0c0000042d43c01410440324507184111000c5901045802c950011243c0715103110b200306904200c40e80d40d100382d1074202004403480110000ba00b940c802e84074007910340b01c042c00205025903c607011002d517800803150003c2c1c0e0b00305001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 761904253 1250 761903003 761903047
    0x61306080a08131217132c090106050307170703140f010b18070f0e0402040b03010e0a0e030d050a1e0c0315080d05070204021e0a0912021e0a030204060b220803 70
    0x341c941e12520341050030501004a030400d10764802d0b06031f007031802600d6440e2030fa030008548030081c803040741490007007907891006220f200341c1b85055020300b0790400403d01151015641c0500c002080c2444051400d5031120f001c101c0315429444d110b0740003031500c3d10111034443c00c1b001d01c81c86c100c995034025040d650b107259052540180310b407106e4184a01c0d55244001c01c003410407103181c2d9449504140415015940080c9184004c0d860700b480240c0802002007a0b444501841c100880d040d50b914041d0030207000a488240072001107202c00010303050060708070b80306e05103103903504201c840110aa104050000c0f4032038000030f90002c4008c440303600c2c070a00051002900107030025140440310304034400001d1008108424084012403068070541c0e0041d0708100401f100020190706030090340008071305015214002c0690701a01003010119200e140b02c0c01c0c011900140200000c5a50380c24070112644070440e5528150014503e1080d050b400c141c0c0d00050b602000c0046052123030007108501c010700c03080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 761905503 1250 761904253 761904277
    0xe0402060c0f1c02060c13031b080d0e01030f1407030207140703050604030f02030304111e03060a0203010612020310030f02030f0f0d0f02010b010206061306080a08131217 75
    0x380d08000d030240b007042105442d1140442003c001c50008030000e041040240c1182c100325820440c40c0c003401c1c421010103041e03c0d00100640d107504503409040c1c00c01210703640010000d0140b0305c241c142d840d420900c010030429080e02e080c05002c55591a903c100d54134145d003160704004540208042034465400351518512070181e000041e10f8548080e45080d200782d10403545a40704008003c20140d1085141200741220300041d4150300f459170341d6169801c0681201d0780103242c204011b03d03035602504120182c0380405820b03294241444005031380694802d0080a02290300385420a140c20f03406d10031603108050f807090100c5010b0540d90340003482000d42100b682d1511600340003000c4207400f40601041d201d00c0138000d03c841e402c0104003030010b003000001202075901d451075414140e42c010070207550001c2c04440418814041000c1c0400900031904104110302c55440c2e09000c0208440045c100c0f0300104030080103003175846003c81c844040180d00140160300f003800d003049200c000c0002c0c0c52040514 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 761906753 1250 761905503 761905513
    0x91707030927020412020321090103150509090d1d030307020402160b010905010302040f021801230c030315190b0702031905032110050904081b0706090f0e0402060c 72
    0x211911403d81c0c00503000b850400f80007010400440c50b04010302d8540d010f2110350800c400740c0c241b480013414050302e01040d0525447d40c0b00001c6460090022401a00c401000c0c446c543c00d011908a130340b9034010303081e1000324041c1800b1014448403581c5502030244010700951400c0c9055091001a40090341004030402850700781100040c06540114003030500103800041540c918010081600d400041740e0443c1481004030301180307109180150740781d14081c24200002c1d082e0149910402c1411002c41000c90300100e80f900300032002000a50040c1c14040030012010400c1d030801944c168003102614131044410300802591240c00090407049000400343d07400c1d2010016526101480303000e04039103035080050802140d2108103411000307611280e8603c011458900ca61543d000c0c6c60340900c61248280c10005402c10084100311504002c100701c5a04850b4003033300c049552210280101e0000c2610302802047c50034401c0003180894a0380000450181c072980c0900c0130b15400299141214051 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 761908003 1250 761906753 761906819
    0x141c11070503071e02091503100623031203431b0c050607050c1903050d1d06090418030e03010b01020f060412020a050d030917070309 59
    0x588000d01103041c0150051a900c220a00c0d040c0510b07904940100d1401c4141449000941c5900e914203a01000c1d044802e0000d41c1101e000030700e804280458040607034100718010610740a00c07112000071310742d6201809030001d5603000701900c41100c500752086041e01800050b00c1d180c12250001d250003042d942e58605601e082c24101c8840c980640c80d50001c10061611011441d4050040151040c1040410384100030300da45e140d00320130704c41c4982485103001081400501c01c0034003544031410401070541d9034810061020442d0303156148001e03038a47c041c0c031100d54200f40c040c2620060703100480b43d607042c503900003c1c00c12459400c03201249801943d1000d481c0c1c0034040359102030314054020b4452015030710b01101050b00303455084480604640000161060203040002d515411641c0104030b038040e466801022850200c480300080c04a22540d40881e0400e41c0685c8010242030180b520308060340b01e1001c80039070501c5070307500080c0002d070211000c10048405c0008a4500ea84a00080c0c2005503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 761909253 1250 761908003 761908031
    0x110c01090c170d09060e01030e030d0902011709150a060305010e070510051c0906090b0f060307090c0807030507050903071d09010501230f270106141c 66
    0x626400100e4901c0306904080c00b011006014958440b800d1078010b00b601c0361411001000030465204520621480d0102c031003950780681c000144030000c40049a0316014128540c0024200307005007680414808850b0640108101d00300c584508480d2004144100300401b100c20b560400902081807a0341d20b200100010f0401e0040040c4041c0c03d000424106081004021003c030300e45c0d1908091003020042a00c2d102c01c81c140c07a5411107803905c800110230400d410818050a40400020000030b8401704010718908030b03031001402340a05500301c41186e13803541060f41c2242e07824140580811040703000100703a0362203500160b60182203440e0032402c000608001c80d00e00b1081c0e801c0f0702c80400d1822920110144e0140c0c50540c0100c00304020f1089500d4260300042c480b0960700b1050050a2a600c0a182ca403034250901c0151040030346400e41c400d40d21030f00300420f0500940009082c080d80e100000e042440740c0e0b280d1040342c0e660518145070100c89800010807a0200040d09042900d85c0500e060b410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 761910503 1250 761909253 761909261
    0x160513060e041d0a050f0304060e01030504020d061107110a060509040c0c05011104030303110901050915160305070219031106090a0b120115020703030909050705090d0c0f0b120406110c01 82
    0xa0916801044c80703070365920388039051003e01ca110031081d07403052008000680e0b015200c0c0031060020b080000700e946450010801e00d039140c00001c0d12481c200844a00c0c43c3c042e0400500541d4040e42496004011580c00c20000443c50702c03945000580500103907c45182c1544024000078550806c41401412943c0d000d0a42e4004841a01c0180b0046003c20500d42c05010301175540c032104030021320740000710001030118042c01841b5401000082e01c1d07920807072401d0b42160700d84080084030342c140c00d099140040c81a0b12a40c0128099480200540d13504070840842c0420740e580500c00e21451503200c0c051000380d4100c6886268014441c01c4001526100078000740392038000e0306114442903040c4074080c820611b0300e041050440d4001102000802d5110001da4103550050601217019280e0700d10071240d50081d68101c50340b001c0c0310f5600a040041e1001c0a10031141d03c0344800c05600c2c1d607113211021501444004113106c15543d0009000943d50364403d000c5200402d65150801c650250b9840c211307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 761911753 1250 761910503 761910551
    0x41a09150121140622020d030804050f030c0102040311030a230a150c03140c0715020415020109021c0309050d0204060e0a0204080606220c1214160513060e04 69
    0x2130704060f0901000036074500c25607110311003072808062151259170110301011103040000c1c04000001011404200b400e10052034032055103411a43c5511364654401e0003075100e44000c490f050003410301e400c900e003004074000c92615007002e2245020404500103903156054165118014010011030000003011114038400c034244034180047c0301410000058116614000030350f01130704c254001c05c101c01c01031000310f4800e1030380010941d5000c6080d84011019019a8020184000302c41030343c5408103038150712050440307008a03550b0300007480d03103040c0e503000410201c805000a45001e6062007103040c20030352094500c3c4040e100084c0346036250140c4104845c02c0e034031410b6140c4c0000301002060010403a40340c000c682190f41c0c48803030b400c0440380c004280c8010042c20006496804002c54140030b040458440584043c0074416004030800318000054201c0300410900261440903030001d1203103040d6201b17989140602420903050140c151290258000380310f034070a807100c0d4801c4001406103648030b61 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 761913003 1250 761911753 761911793
    0x140d0503090301020d140f160c020a05090408090310050c090d020a08060f0f01060314061c050f0102071704060e01110c0406030b060f1e010c0f020405041a09150121 72
    0x4c41c4003c006d1200b180030018101003241c041c410180b00919410346401c909250390350515036980d4a02d1304c00f00700100c0159000d1540700e18900d0801c024804d0701c070010007080e8011015203d83e80b40e111684c4086907001e50319480b0342e0720305125403140d60401e652089441800140708520f50384d521042c00345460b40403903a02c18149116000e11614074008801540948002c5c24140200518160340c0300b440c441c0244101d00c076440183c080c03041c00400d2019551251340007010b49921140c03201d910b9010358000340c03088a035046e0034442a0305022a04080e01c0565609564080100c00310000448401c114000c201c42c5600400c031710b0400e00d6885e480b50300c00640c81211812118a420010821204611a69140100c40c4060001c107040e140c1c45045240f8102400d001851410a04040c6400c80f46e101d4000d4101e880c001c107000921042e04070b0034081800e00300c400d050715034512800c40c1d100c05100890180709030002005004000040c01d01041c1c0c0800014001c42d005c00079200e00b030540c0030013244824 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 761914253 1250 761913003 761913011
    0x120d180b0412030216270b040908031e0402061207120903020a03080108011406062b05150612010e0c2206020106060c0f0605061f03051e01140d0503090301020d 70
    0x1c00d50144911102c00c0d8404410f141c0d42c6280c000d00a045118450651010905424506c1280c0100780c0c09000404130107841000001220b00d09507125500c00e55034000c0f0080f000c595850f2003504011828455030340a0503043c1800700070384004980d40b001805c2d5800384103125244035044405407181c0e0b80e442d070203607004216500960501a000b0034060304601807603414008445607a004550f030007a0045000e441c5541c0d1400440307844480c051002c003902d02c0c0c248810b402d500282c1910382006000314032031065041000980400c02c0f0b818030408146014401d240b80040208081159000e944800c240c1072a03440c0140c4800c02f003c0ca1101d0b5940081c81030301f002000d2041d9642445000d01401050401940c0d44402d625440003038000a2801018180c07128001101342d11a01c90342451240b4049803880a90200900500a0002100d1040311004503619819103184081c2c01d1034102c8140c414060302e040401c0041c0943d1146108040d10760b840100081716007a04d01344010081295014000a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 761915503 1250 761914253 761914289
    0xd0c0e1c0615081b01050c010c050309070608090a0318030b090d0e040501080a0b06030c0a08030c06150a060e010e06031005040e030a090b0a031401090c030b120d180b04 74
    0x804070b41c2c9002c254006140c10742c00a001201c000640110070304601e0000708111492140120741902c500c01d0303c5c1c2119401d01c0c5100c0c1640703800c000514051003941d01980c682d1512408201c50540d8212800990799015242240100340152140d0320308282c1050043c0b03820ba01c907102d4211000c400c1d41c0328140c80d40402c15032039000340d0004104204004c2241e05000c594580495039907911015440507080c0c0014401241e855079041080340440e060191840d00026030300c458154894100201c0760240340501c200140031038200e052114404a002058100820704001007116941c1481c40540d05101c5031001300745040e504d00000e94454604a2200240b036800d00007440280ea04042c400c4042d6031060100440f07440c0c11601c541c0580ba41001803645614010703000701c010301200d42241c9103040c42e84001141c0c01d40d01d90040503510043da1030900502e0003a00074410030f03150051100106800c107042030200140b003151a001403110042541c45482e450728410041d0b0380c0a40d00013261b0b841025101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 761916753 1250 761915503 761915513
    0x6040b18010506240d06031b0b0406090b07050c1807110a0206070b13060c0206061c05070e0606071b030c0605040303050a0c060908190e030a02060d0c0e1c 68
    0x4194040640c000a00c5541080400f00b4050082c608240b50324000302542c2c0c034402440300e000c2e500e0104c0c2d101d00a03c0820f640381400315001041d07840d04d0a69445400303000c1411001101100d0442e0071507640c00c82c043c1d207454000c0380030343c00c80402141c4500803104a1591645e42d0403c858228544924240d13250801500180c1550750340c80d11070045400c07903140403016a9440c010303146080d4002c00b00903219501ca4054228140f9001001408170b40b03401a40001d4617400500d042c0320300001d984848403042d0034500014201104a0b00901c5076000000521060b44a20b01d1319402c00b80c003520050808a140c0d4603a00d240c82285520f0460845d440810404d0000b0071040c040109050b0400c1450075095440c02801031080990380028408000c00c50001c200d801d60190203829040200640c440c1c04200750401014035020b00940010030208600d42140703000700b0071080703950b4000d101c1481c00c86803129071400b030309818174064240b0409640700c20b620f0711480c1c64540501048103e5050400c81c41c42c00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 761918003 1250 761916753 761916781
    0x80a0c0509130f0602070c0e01030f051b030a11030c04090b1b0702091506070204020414030c10020d1b1406010801050a06060903030c17040605041a09010e061b06040b 73
    0x31505141000310701e40c0000c01d04040303100d603140f5008240503990b50014200282c400009500c034030700c2c070207188c00000107000c060689482010310071810341d5655004903000c15000303003502d2425076140d0011052a4000366415180300440800a42603d80d4524401c00090031120b50070029115101c0070700401613907a0510b10307015400c0d50302d030b01c04506100468003c1100c0d402e0060082c031780c0050080403103001d583e4000544050030750050080d99119150385d42035030104c14540c0e005000f841484550001303071074188040b4800070015802132a5403906200100c9010341c490004404034920f082100c030214041d1040c6100e41c10421004001952500c02140d08441d002007215207041e1901f9018059130740e0080b8000c048907011300c0c4c241c01600c400d00b0304c0c000c208202e4090030464030000400190b5650017402a10840b400013a22503048030740060002841c3c8148856580001d0141c040c2c0c011030301d424005007469400003c50a0384c4000c510000c00d20382281514103a54001001003081a06240042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 761919253 1250 761918003 761918011
    0x52a0702030f06070507020d050c190603200a120207050f0106031e0203030a030506040209090702011d0319050c120c012a02060c0a0203090d23030309030f090a080a0c0509 75
    0x180001c0c9082a13008005019030301009106941c1202e0250601200b000340415902006080030807118408030385c2c00b8121510300c03414000c03e007400f078581080c40c030b40585012600c100c02c00c07003450441d178094110ad0300f2583c0e0200f58541d40c4c2c03d00000c0c022490412003240d0140c02200002019411070406039840c612511046920b810241450001a00e010040e01d25031111030502141507211400010040d000701c502c2643c10030b0303040003000801d603070540103018240c10f40c22003420003540c03d01c0090745a110760813007070380f281c04000c1c1030242c12761080c07004045040201d416a83c004c0c0d19503060610a50002c1140da070f82d0781d11500ea105030b18618620340381c0200e5180200d0907484c049170344060b407a26402480342078403500c00310380b135101d0500a000302c682e002402454803c03107400741c1c60040307445a03a00b00c450f04200000941d210114600208a034000c0075103800540c146461400c2200c59a440320080d00e40100c455000000e416108000034a502846410361807051400c090a100c0200d000030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 761920503 1250 761919253 761919283
    0x30615160b13030e01080c16050c0909012a050705030c03030f01090209010e01180906182301150201110301090207170a05040e1e0403051309090b0a052a070203 70
    0x24030400002608503c01d018601302c00c3c288009640c1d03542c0000040740c046c007194003840f40044c0c0f5001c0c041040228108540800481e460541c988030318403841d00b20780ba4101c241d0749111a5070700540022442011204400038180760079031400782c859942e0343c00c40d000083d02c003031070364004024030418889800c81e150140800d0802141000b032241c00090090b0280000d06041c41080d503003002c04980c640b061500070b440348200501c10103030390b04c00440400780c90807045103c01d80f9000700900c1c3c1810000c403401c02c1e41c165107907501569003410340c003001c0943d41500c120150341d41d034442e1201042c1035501450007810301c2600141c4444860615a007014090403c102c0b1420017040010a419005415141980c848000000700d03580c2d10240c408000b0401c0c200c0d50f014140240401c000c15512800030075104074500d1a414840d81c1d9000c00f482901c5004100400120b84d990005409014030f07400b00740c0c0010b50b00003404540f44d140320000d010051070380e41510103080026062055013010032005003125000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 761921753 1250 761920503 761920531
    0x306051b0a1d0d23101109030705040204050f0111030c0a0f02032523181801090b131110051b0f0d0c03050403061401090c03140408030615160b 63
    0x3e40da500e0101c009400c940c5107008085070300880c0e00c400803c11502814240380f010010b054492164100541140b0340540c4248102180406d8a080c94001c1e501140d00150000000da400e82005540499458841d4410f501c014001c64a0348101000b417200b420f8000d000c070521048150040c10706024440215401030050415500b60f0081a20000c1c0100c0d003442c41c1c00c103820014500026048403422005561155000081c00d00303100081003007600680a50000f414006d00d50b0b407095007601c00036507004d030103031410740001482d25064080c2d01c0c0b1018803c81d01e00c8003003000c2c60000382c00140003850729800075030081113003541d02410010640303401401d00300a1413140c1400c1c00c0541c0c0c03415925848010400e5440008080500950513a405540e00c6801480759110450903100900303000d216417402c580c2421050700c20700740284032303081c001241ca4124416507621a203036181a944007908142d00110004151000d511000019021020706203201c10b201d0015410a642d42070000303070940341d9030000b07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 761923003 1250 761921753 761921779
    0x50406022104111c0209090303010f080f151503030c01200c0703020d080415050307030b01050f0307030b0a0b0c100c090e0f07021002161214040306051b0a1d 69
    0xf019580719440c2c111005410301050000c60510f000204000030341040d100414407000410110186050740c0d01c40710034103140703a80c800c1f115076100d0b00112685110f8000402c10007901c0707620009954880358180402c8800e1007180c0120746035a019332415540c90750354145440342c200c41c1e0009844143d080740852810301c0e00580940c1d488000d03620000388214405420982000400c106807002030110380c2c030740a604c04407141d0160a5038411a50200000d18003505105290700a006603a42d44d054020068103550310800207070000c0085c1070003507030f00c6000b03004c0c0011a03030001d4000340024a00c00001c4e124140310300c0c210f8416901c500c0e61800500805103424018182510030f0141e01810640da50030184c3c6614109034200008444045110380c0000b6100400144010110000b14801d015403503483c0010441100e0603c007103d00c4451409080100f000490b0070754000b10b4204481c091001005020280d803c0d03d81d900200c0c036040070601c2a01c1c02e00181c00c82100394104241d059a1807800d03442 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 761924253 1250 761923003 761923013
    0x4030e04050c0417120301030f0b06040204150810080106060f09050405040308040f0f0b07080115030e0601060f090b04030303140f060d02060304110312180a0b07061e050406022104 79
    0x40d0301071219048080c14407135180d0142040303000c062100c004251550384d6100d05142c90012030103441a201000c054002c6026400c191007101d0895400d4000c203a000c83e042107088829060103031080034041c01c03081c00490490307428800c15008004945500761040711156015102c44201d5004034070452404007080086a00403e0b07056000b6440780245003201c40a190451004a2240c40075100c0300a410400c030200743c02011190580e220304081d200d101410050440590700040200e2055800403401089002d01a00310070320b4116160500e00790f032948801908089400035401600042e4603503003102d544505c4003a04580154608030305008070318100c070100d0b001a4401130003c1c0500320000c001018070030101c0132421107490040c02da504140306e00184c007680e07401084007036044c01c03d00000324000d0310700512070307400300e400019a590400304d20f0b44a40c401003d014080140e00e11401903034885417a86031207110300c20b034403070103006840c1c4c5a4003001340f0004844032100b5011500f40e0043c080810 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 761925503 1250 761924253 761924257
    0x30709061206020f0408060a050403030e0d0f0f050d2c06010605070206090a0803070f03110c0102060c1b06090a0c0e04080306040b030f0f0601030605090a0c06031a0a060804030e04050c 81
    0x42d041140542c1d44c1e40724030004e58644c40341d42e00003c40d0b0b000d528240401944550801402580a0b40e4140300e854480d83d5026151404101500c020500584a0500035802084d0080045950b030a08c2410240340045080c00e49054012054040a000b40348655640d00301c03407840007040c1103400901042d81040c0014204c0d109401e07001c3c1c402c22011403840085e82d83c00d1542000340c0304000c107503601c0b00d0b0140b030308109241c6011011004902c0c60350440c40460030008007000107800503030043c605d40d1901d600c0038207140d200301c0d280400e5041804041c0481c0d43d0401045000327000700c10041525081500b015050401642c010400312135205040c40080381d894000d80382c111104550006042401d01d00092038296400364040150040d0001c890816501180311030490740501c40c144803c0e038545234503d0f00e941c4207040041c4540c10700c3c0c0091006511076401180142175940300f50b031844280d440010042d0507240d000b500060103039030070001095803192a4101e40710040e0b0b4140701c54189809541942c4c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 761926753 1250 761925503 761925539
    0x30305190504032703020d0302060414060601140f13080a0507080c090c13050301181406010b0a0c03020c150c1b0105190504030f2303070f0f0f12050903070906 70
    0x5a42d404041390350380101105200550303004012540c0f07140d161030081c1d15200102e0301a5440c115040c2d0a000b4860f010800c85d101e1003059442e40202d6550340e08003070301ea03009500c0c8421720f17000920464516555500300b42001c0d10143c0300502c034051075842d000e481e0220741d8010010716003040740e0307120f041d0319002e40b5140c0102c3c90581294440c0401c070a020074110450740100e5042d030a01c688040c0e08040841420720346401249500000e2180003051540c0b64030270310900403680800c02070590400d00c80c106c80310702540b007072043da03590140302c2001850b0801c00e4031400d600d580c400518800521020007581003940c1d009111403c090804070000382c264043c2007002c81103e40c00c1d00d50010300ca8490350407500610f6128001c4508202c0390306241000240f140c0c60248503410101c2060b14124001096445540d4801d00304200204655580000c20300c00c0c201c00c999112480c0910400114034400c084038580556640c0ba071903a00c00e4003014601102580113100f000d143c15002e0203960000091840c030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 761928003 1250 761926753 761926787
    0x4080a02090421030209030c0102061302010c0515091509010c0207031202160902040e070c0c05041505210610030203100522031832130903030519050403 67
    0x50b5110700f08a0380d40d18455242034448100d0040d560075442d09540603040c0d0140a40440d10700c070b42541d005907914142a100030105102821840005600ca20712600d0010310071003d54100e0030441e0340c002da106030f0507113601965070409880920792508941c90145c0c8151440004e1010141c0d0410281d26214240806071030101c0e050241c100d0b06000b00000800d0561a004420b01315588000a4000b0b401070b0007003550700c82d45030f000b0900c480e100301000007105401489020110b80760204000041291141c0068400e03000e102c0011a80d803100340e1302e580800d5007003809440010704401030b400e10000800c1810941c1100d142840561000510029242424100040d0a0321a0070203031040c49040c8810842d4100300140c803404241c4e203e03449540d0004a1001c62080c1c03915840c0ca08402c072104401c1300d0404141c102a1041d50b01c1100c21510004009042c5489840a1881920503964006421307000700344c035001402010000c030010105c1841c441402000035081075500100345003685d5800c024 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 761929253 1250 761928003 761928019
    0x319030813020607112103120a05010501050d020702010201151409010b0a050f0310050303210f041a0a110c0f0f28210809010b030703020907120603020a0e0f070504080a02 75
    0xc1980b12039002c1b0b54480d01da1010340b08030001071842290349030b100400409510300307040c004c2419550340307000d5141a00c8058650301c2c1850a40b8100b80020b4020b00802c1e411036407030b901c0140da60000164a5000f602075645104141c44400c010f0005400c410f0b44114091503041000c915065032010544100300d402039000343d03498688416440d4814015013046070b05001c002840c854660303440081142400306441d40c0354003540e4000c0c150358820030459002e040c2400032441180405180010750b6488031482000140700e203544102502c05800c0328000d0f0398030790302c81d00ca080c240500400010003041410340003403c141480d0040d0f80d0042a20240411015042440c00c504025400c0750280310b00031280340002a48401290060070a1402e589181c074551800046807064100800c0c0c64003541c3c0c01400c013640603100c100085902001040030140031990f02c60021006a40d140c0159000f06074a0900007203a040c0302c1c12031200200090500001c3c058100403c114100012071901c405a8044401003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 761930503 1250 761929253 761929283
    0x30114030c1512070e0d08220b09150306130e070b030c0405180f040308071b1217012306090301020a02010e19030e1302090319030813020607 62
    0x203807074000c81d03000719980000440c40020120b9000300261540100e0529001803640310301c141034843c400c1074900c46410000c00340030140070400c0380005040e005c42d0010203225003103600000e1b515040f0b05401005211000141800c550314190481901441c214800c00345141050b40008003a6541d420310a1710254407035208914104080c03000070002c0605081490b92440d00000d10f202c070341c0c8680a00c91044c001070b541c164501034404501f9200b000d2550111109499503202a281c040e0002c00c404e0801c0306d030311204440f10005070461419144a655118060207014901600039009540b000300d0403400e94004011500406840000740003510440030440588038001c134200b807007a0800181c15600014050042690540c080f0100704031000a0301c0002d000e01d046095460074180e800340000d03850344a075220340d1900503100c1318940391180c0014500200c0740d011905000c50301d51615540c100f40c070002c4003416000701d41c0980c019440d0301640e00380e10195000410320f01138007401802c1e11781c0a4281d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 761931753 1250 761930503 761930509
    0x3060c0a0503040f081324050309033106021b0910060e0a0306050c0703020c010e031519090507151b030503061504270501030521040306050f0723030114 67
    0x40d1000924141b1043e82c003a1900c00380020242d5901001c2c0340d0451300e940708000c803842a000d07240030725414800780d072511b402d111612112181400c5400f265451580c1c48881c42c2d03500c1d2041000805168000e00011000c03030302158421007074203c0a9005002e041c041010442c0c1c03e42512040d40c800341400070003100c4140114000300440d803c000c09007860542401030b01d01d22070001d005100d101340d00701c44036004003100448020000001841d0182d0048091808440d88121151f41c44030b080855200b800200c00d0300002502c0801d04c0c25074132500030813011b018030509100e2071078866105003403426281c003070200040019504444060304000000c0081a2150380341c401042050b400f01d281c494545407100000492815182c41044072548000c2c40c24000328001c1c041c29040765044400b40682040e940c0d07490303801c0014501171000d43d6804000101c0054501d01c00c2d140642000c4604403540e103003001001c0c01c486020f40c0401c1051030b80040303c1c0541204602141c0c151601030164030980da01003004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 761933003 1250 761931753 761931757
    0x40f0201140c0d0e0f19090209220c08070519050c031303110a1e09020705030c01061e050103021e1b07120c0b1309050408070b1503060c0a0503040f08 66
    0x1d540802c3c0165200b100169a102414040c2501c0480c0c00d0780c40780017000108212030742c41166074511550200c41c00c018102c411382c042d041002000d0186580c440d84150100b59000742a9070400350380d569950038544103039100c0c003200c2d072040c0d4a0406034900700c0700507610b40d22180d2010a0008000001504400801050059a00c1025900d41000c44103880f89880024803144203d114018a494940000e10744603c204001005511001f412445820301d95010040d602800e0141c43c10300c810004003d10a509108010040c13107003c0d800b001d5000031400e02c0710720700d1580e44a2410940144901035240070300c00361010b0000e10b54001300d551200d00301080c1d14400c602d01c02e944001d0141c000000748841d6074148204540b48501e8803907100c1c0b9145c001d5145c0314000e05140d0000ca143c1142d003401f074214641e0140ea0080d00504429040000c0b6903900c046541040300c071601c55000d2130300c0d800d901e4101000241e0b003244000c0c210a041910402c00102640402080034000359036008100090102a2003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 761934253 1250 761933003 761933017
    0x61215040902060a1215061413051f08010501050931020c030d06080a150207030903020409150c0503060f0108040f05060c07030e0d08030103061e051f0806040f020114 73
    0xb03c40c40e00d50820510203800c0030701e8040d1420442d400e0001e803a4080e01452241419100503440303990640074481c1c900c482a40041011120304880e200c0081040c0d1307203c10780c055221114040c260301c6c00c10486402061820103901944c1400f10506c4030680036600c4818480403160500c401c5601490614081d0441180d07c0d100d100310350b840050442d80c40c1d0740100c0100200c0184407003d01041c2da4545055564114600d800f0f0001d400702c94041240c0a069001001520301030724111074141d840c1d800090844181c458105d40340301c0c000e80303001c500c10b0b110f025440034920346080150440c0b4065002c0303907131007980880d40c1c0e040080c094001400c0010320680c900d8001d8000d0f0464801d07241c2034411038510741c4200c4003a03000c42d032852840c0000385810030080c1d4265501c015014116440c540c2e40038094690440700c03da130640c280724110907140182c40303914800d1390b100040388848102c01c0c062510001003034010b6040d6801030010000490000f40001cbe81c900d40c20301e420907041186100074416405040f03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 761935503 1250 761934253 761934259
    0xc06090609021507060b09041a0a0b040204090b100c1e0221010b120303010b04060c0203010b04050a0506120c060f032d040b150108040602090409080409020c0c061215040902 76
    0xf19001d10009001005080c2440c490b2808000d00d0a0078801c0001426080b140100008640e60b0f00e0001d0350940d00100360800d00541021a00034001c0f400602a0782164009110251340ca4020540c0351401e001c0c0c2c0c0940750f0036420300000c091060307210304d442180000c220b250b940210144840854440c80340855000d400c103c03d0880c2c0220900b0b807140131700310010f001c62003221084070000c43d405002c41200d04890840302e400749058544841942c00f2002e101042c0d0380340d540d0301c140000344c1c4c445001d81380c41b981152000149600c0c00303900f00003940a00810845481c0e001c420300c071a403615507208032000500c6e480c40c0d503601d0381d481150070321112101100080d4422443d100401028906001c031318040e0740b01d404882110364840e5072208495612650a83c00111903002244c041860f544c003c005284002d0b00c081480301803070300c5590305d84e801944407041159001a21400340300052101544491084480c41d00d40780448001000306c2c0e402178940290f45150304100005c550ba0755208a840b13583c09 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 761936753 1250 761935503 761935519
    0xd020604151e17041403180301060812180604030c150201110a1b0501110a0810050d080d18020d03030f1409070315020f0f13060804030c0609060902 65
    0xca600c0212050320480c0718022964810340c0c0070400704042401031006160f5958010b1030701075010f0742c5109000203031096914036098000030300707083c40a00c000d1035000744085006020403001c03c10f0508564840d848580c40c3d812620b400404880340e030084401c1e26942c0f48666201b10b41c02030014006108951004011a2319a940014411011520714286600e150000c03c40f000e4640350450142c8144030000000400c0350812501c684426086a82410702810000509480b40c1813200015400090f001002c45d0124007001210803009000002030407040e43c01e40c840b0796075076956002c1c0303000d01380612900ca0307101c02490091161810001c40580e8000f060340756581c1007414007034000c201c6920089040c50504031101e880c1c003107080c0c01c64010046103004001c1545542c07107085038690280d00700001c3d01e800304071a49081c200200a40318040d1016200d03035882d400c1c6501040300c000213500100074446170768100000b00c1d0f0895041c000c41508400007052800d00307841c10700020541d45900175400000d0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 761938003 1250 761936753 761936759
    0x504060e0307081906110306060301030f0f05030a090e1b040e041401020415031d1018051506031605031c181701180b0720030f12070f090b090d020604 66
    0x5051364080b0640c0150010081184442240b0f20640301c1242c60581040b070400041000940d00c2100d000418001c6400c0d18600d5440d80c0c0e680e0035544415104400141c1e2048103201d80c692281c040d5800c1848080750744003070182807640e1002c5000345c0c0300d80640742c0c1c0d103503000a05000b41e00301c58481141ca140000c65807991134401c60302522401c00311100009182442d0880030849511280703170301480d00342c02403808814200414000d0540300440580c907140c2c2c0c60700e1100141003000240c03125560b050031141249010010702d40707041d00020185a0503004210104030710344010031600c000f02c106050b4051640101113058920720441c1501080f0035052060002e07004840e803954508020340003009121154840c00009038001e0034a00182c4102042c80100721190b000718045102c94018441c2541c035035162803526411600021511001c03414002180031140d11900c0c9856442100c40c20505c24a000c89000106440311901030041d42020005011810b981c40c4601b200704140d000b00000d41c0d841d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 761939253 1250 761938003 761938033
    0x1806130507083c0c120c0c16060c0201050901031b030501050301060605070503180a0f0e09060f0f06011d130e1b15160807030315080d0504060e030708 66
    0x150450300c640d602400d50415001e51040d00f90144440c15415200b8480e981080b10700420302e55000e018080a120308100b0708801c650032500c9684281000e141d0b15880c2c0381078a2210781071081c00301801d100d13040110000d06c00c0350340040c85584200d80a10302a52103098081c016401028403d6540c24000e5182400510140e8541c0000d41680c0050f8020310103140e135203c05580314040c80c480148260801d010100400260640041e03000000a02540040d44c0e5007840d40303a1140385402021043c0000001c001405a0400c5a0754008001101c0d01810340f034110a500755018000c0d1050f4101f0581349004040340384803000d20102d00c600105058002c15004043c80c00400031007141d1032103401400f01000c40d0100d0360b0a0f4003840140600b03440a6030401d411040e1541d40a54060341c0d00030a41e405071404505014080c0c40814401d031000141c1402d2150717011040e1105c0d80c40303880194002101107001682c405c00303440c105d030000c0c00c7c02602d10b114100068100301039900110303628403c0074140042c0310 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 761940503 1250 761939253 761939267
    0x82506050439060309050a0b0903070b0c04270b100908070f050d020607062c06061005182215060c0804150e090c040f0e061806130507 59
    0x1800c181007181d5641058203205101e401001c9078154600c484100800c40d4a0203030300705440961048080d40e47e0515540d9840c50004070541c0c409485600115005c42000207000166421011100c8454201860420b1a000240785100721510800040d107141c034600102d9000510400ca008104401d04408014001d02408540c820402203110f990800603040080c1c01501041e41c1010b0072404007104c05400b4424540c0c00958200c51480e541c480c0345052a030b14426242c50030074140d40d00354201c3d80001d05146841c43c00b4051a00c5140440d00c0001d1040c0c00034100c0d285098590401414006c0000021380300300d191080c0e07082c5114214054401001c0305034050604244a0b4070b14171201904c07010203c0302003c103a24000c145280c100400d010308210b038480d1040007601d51a0543c0111018008142800c2082d500e0700758140002c20140550071044103c0c2c006804500e01060203480e245c1c00055042000d540743c00301408203900412899218002c501d8220040c84206210904003804024030311 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 761941753 1250 761940503 761940533
    0xd18030e0f0414040f0c031505190b030c040f0f02040e0610080c0a051b030c0c01090803070b0a020702040b0d03020c0a240f030e191e0825060504 64
    0xc5455003582040e074606403043c401e24111801c000032460340c0e15a2464560459000f00b5961034042180000002c0c514a0348040460300360400800d00c0c1c1401400100300f030003440140340700d950600c0083c2a01d5140080d1a10240e00704403400f2a603800d145500c000102030050840d02e0031800000c001c40d5210202034600c1c02130006958213002003803945e004803420711054850140c00c003420004c1104492040000e020000812000d295a00d18030188040c5141c0c8052400344284c2c1101b4540c40d259038100c0c01c1e80300100b00400107107140c9402540c0340c1d0b0380000010074035244c0b50381c04111003041d07484660009031030041c0903014140001305810007954810741403041a1103804647c0c4041a48003032001800500300b5500002c00c8061000e031819103803d102c41c4550410540d4441c3c1c001000102009060500b000c041d0805981c69030138140340800300101c0c900d0100b1140c00e0720707010000038500d80450760800da8803c41807564100031307a5006207007400014050540d41c10007050005000d04200a520380b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 761943003 1250 761941753 761941759
    0x90f030b0f06040c020d0521091014010501020c01032403031d03031c0b011404090e0f030313021002210c010f0b010206060d05070b0c031c0207050a03050d18030e 71
    0x4566603101000f081c1c5070740c0500840180c0089041421082c0035002421103505100700507191034a544198110602044a4100b83c550007018080030b2500329104c1c0c000c03030340340e042e10600841d03040000107940c0e00035601c0384a0400d6076540302e41403004c10039900e0391104070070040c000314810381e02e0600030940551484071040100c0c9010505119140c00401c80d201400038031400800f0312000c8503414020f00d11860707018180f01e021104221244e82580c000c0000d01050340340040c03a40d9050302d6aa2500a45010a0029078020030900000380c404407000d01d200c55044850540351452018100d0418405604110098200c140803008070200d0402078021074040c13000802c0600700707900010003a98120583d03a4096080038010038900c4c10031b07615802c091030142c421036540700e0781d03022880c2d0150701820f42503410b5000404c001480c2003daa02016400d03003192419420103115860b0b0355100c285104008080c001c0014642c106564190050600e04141c03401190700380e90581400781400086640b0350388 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 761944253 1250 761943003 761943031
    0x501050f09070801020a0c03030f18080310093c020d062102010905270906180715030203070e0d0c03030f1b061a0306250305091903090f030b 62
    0x2c0c004814403d81d0300d28851a511030307c1848940e1015002880404150340041d500e500c010003021000711390303407905584558071003981d0303117000329501b80450302941052020038140109a560300842c0c880152805d18822000818524800180c0c1f42c043c40c58490308100d94004102d0000c2041c080c1d1000007103071820000c4940c1c208803880c0701c01360b00085890003800300322a07401c14401414010703125060103040884102020714410080c800341001201d9800c030b941c0c488410000182c40c50f01c20f0241003065030f0001d091031810449c00b81100f003070544201c001c160f4080009007080d0b00c00d003c880102240a03024014003901420f101908050501003a00414808114104040d01caa54940c0000f0780d0044c050343c500d9881d5545034050002c2032410032142c22002101069582c3c01e100300340c025003440007603054140e440020003a00c0040c0c5091001810f00d400b04200c0d20050220365a5000c503481702c1c034038012034258032381540e02c50360301d4000905900140e43c020040000c10148540102509540d0107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 761945503 1250 761944253 761944259
    0x30903070f0e070f05041802040f051f030b031507030203040c05060301080304060c020a050603091621111908010e1b03030403081804022a15180102070501050f0907 72
    0x26186228450b0100d29004880007034103440c4070755100381e200f001d203141c4549859a160f061711a003000005640b082c49a00180801c0040300d0710442500070403060303d41705040300300d54460ad10b6541d403008521091584420503200700d5039041c8201c0c460380380e04c00c001a90701d050000008009410440d01124174001c1e40e44049002e1800d1400e6a0490301121300a5281505100c42210214101481240c001c240300d4008101a51100040c511130341c0031600400303140747c80c56144079034220700e6480402812440c13483c071405132035003452041c410ba400c001709503203050000c0c000c03c06405202c0c944401003a0440c0012a405406400c81c1c10320501c00800c40794100ca8607010201880c01244506516038400c04c4100001117801001e825007640070581c00c4447d00c50324000c5000c0e41c0c05101403007101380f000d0445035220f4407000144841e0b8011000104582c0080552404091601030301321840200045980a0081f000350101c0d0140c55100c0b000f40003504100011504621042e10000000d0091031004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 761946753 1250 761945503 761945519
    0xf091c110103090c1e05030303011d10050f040203070219060f0c0206010e012106061401030f15090203060f0301020d060503060606070305030c03040807120903030e0303090604031106190203090307 86
    0x901d43e6500580011074040c6080302c1090404460100c0c0ea807082c0c0f241c00001025030b420300c0514000c0c415100314141903c4148551104100000c3c0701608068000e582885162252030990007a020142d40047e661344400c102640f4142c0c40310041c035001e041d104d844004020881c1c110414110707030b00100b8001c1c00032608080e40c41e91001d0003205200c40c2400300410500728140c1a4080140401ca03180245d60305e2901c4002c01c6e50016046a0019a0f80581440c85542d0620409500c02e00c070700c404010039810000d0b4210841c4042c401c191205030040049942c0ea503c6072084090000010021941e94150312981c402a00d441d20803d44a070064200042903424914101d03100243d05a0302c0c0341c619030721250602c03000e41002d0004d4404120521039100000c9040b600b0710301842c200e0301e40010543c55440c1c014860224864020702903001800072124544549090b10103a95210880a9009914101081090107000c42000c88a42610a00110300703401100400c1d40710300550680741c00e00e80351100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 761948003 1250 761946753 761946761
    0x219170304060525050604080c0c0109120308040303180f060b010e0108240907020303151c020d0204140c0c0f0c09060d03032a030605091b0f091c110103 67
    0x1404080340040004d03010301500900800f01c0d1040c000c05401d6203a002e07445103840c102c41105c08445003640020740c503031140000c1280b509545000d22b072441042c0d00b000c7c10a00500d0300420000d09200410000c60100b500a0b08480c81800c480121003866000300e0510280d0740d05040003d80340c1e1343c84c00303814070303ea944202c054658000d010b85a60503079468546401040e20700400e2a000701c2c40510242001c82e0740d5108005008140c954000c503200c0c10a005907001085481c403003a44105040401005804101c4da98040e42c01c0c2c0441f80c1c0b0842c40024000301d03018010450043d00352141c4041040286201440078004403c508012146800e6160315941e545402a90442d0f81c03181c0803034002105031074043d4201d03420b82d02c40d01c1c1c00b140d059880d1880541103045200440a000c0703603540ca06070429894031032000181002c88180165041c0080d05410314680c0c0c4803410503140000601c002c1a1424008444e90b190024242c0c440741c100c95480300200000d101402c5425a000826461283d80f0a0007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 761949253 1250 761948003 761948009
    0x310080615090a0c2a0f0c031b151101020f040801060612090803150402120906090d031a0402090d140106090501090c020c0f0a0807080a03091a0702040c05070219170304 74
    0x16040d4000c400710200e0100c1c040c00351448444005450700e15800201c00c2046c2c542d40e6071103000e4000e80c050840c50403041c1c000040010514205185008200c000740c0e440c0200d401029038241140c01140b80102107019220301c0c600c14504c042c0005002848881c15803181045518a03a10342c503458103920405030a440c0c9040303002e0034a58043c404030b4000c860401521080100050005181c0000c0456072040c1c20821500c0781d0f40c5030000c5003005808031050000c04400c030708520b010010f81c00303050030340d0014143c0c551116000d96404a80d84140307032109458040503c1e000b0b50507880c3d01102251082c043c042d94003e4034211030030075000013103264450080f4421a042ca4010b4000c0d42c4d02501842103422004010302e40c080e0000c5800106510248024005051080b001d03081040f4a4203000c3c1c00903d1a034441090703c0800c000b4620402c01000c190785260341d04540100310003c2c02c10049466000d51240698402e5400340c0c0c3c1c0140c0001c40710924215002000075284012620400507203c1c09188 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 761950503 1250 761949253 761949257
    0xd0624030c0e1812030c21250801030b040812040c06121a0f010e040f090b180615060f040e0402030f190609050a05030703020f0c09100501050310080615090a0c 70
    0x400940344c02e000c50701460740718692401c103600341208100e051a240c0041510700038065442014000724604103201c10500c449109607000140b0152035000301181414440600454074100c041010800080110703102d0a0307042c0290b00c41c5080600701840c0348482c40c070a20300490840d81c01c20440b6141401804254161800000507a050300414428080600c01c0746031304214000c1807040315a40c50703101b002c11011207100700080b0004c0c1c61400642d8050082c0c0b40d4413070f1343c0000200c0100e2050000e40b2583c0114031441c600b0100d850080403503240c0c05009109440d13400c0c003040100c2d4140318140801c0c0324600880841c0d07401c110f0f89511584501e0401e00c00e07028200d03500100030209c0d27029004445001d1041044404030b502c907403100b90640c2c01250f8210f006030410345e40f80300514001c1010840c0d4140441d130202ca41d040c240b0003480444154415141840000710020f842c007012400000001d00500d41601c5045ca040c002c06404c500b40300c120343e44103284203000b00c1d416495a03c0380080342c0440d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 761951753 1250 761950503 761950513
    0x111305030601050d1101030f0c03020904060906050319061107030806010e0a140402130314010501061805100e0d020909070906060201050f01052407080d06050303090d0624030c0e18 79
    0x41d882d50700440c17890505150615460700e0b0484490343c01445410501d07519540c005032680d5035541080243c6896074007202c415414110280447d03070340810308011106140f41801120312461030003001800c5002400d190590010900c0014950010b80b0031b446000b003681c81441c507090620400ca1810014002e0b15001c481b80030303103c025800c103640140b00142c20110303c03064003a5a65204201c180b00b16030b4924190351564010404079400a01c0211568019080215014101004241c0040804a600080000204140c0c9031925500c4040651640203080c0304e6441c0740120103a40c0c2c0d0001c80c0705140c119890300c480092414410300c611030089504106042d403a134030302420801d581c100410070410006a40c90050035603004007000700201031090102c07a884150900b201002c840312984954040c2e081004400016620b03002c10401c1c041c2d00140000b03001795622494100102c1000ca030400d4217011070004014440828680f5040350300070015a80c00741c0d6402d00280e07510810b090340503090762003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 761953003 1250 761951753 761951779
    0x21302070b0a061707150207080a060b01030e0f061906090504050c01080903130b1e032503061809080d0606020303040501060f06050a030e030d0204090e2107080c1011130503060105 79
    0x1d121b4008100e84110f104545540b80c46007a0141040800c42044941c950360b010f0703040c071030358150140c2c0c90024000405001e07246680c89280391a154000c0c0b40180d10680f107818030000c002c042d4422405060304a03020012485c240c60000d0b998400e003401c00d0b010400200020b88000e6001044070780c100e000c2800340d41054070b8000c420105030000b44004004501d861148084559140d0244d4450b00c540030140c2410081c5c3e4803590540142901414201420480180140801080702d0480d081c41044001190095070030113803a540902191020942d00b404000540141e000001d5405980100300810901c0d584040448081481d485a200071503c180b00c0700001c1402517010b80c562501400c00d592400c80b0380c0d5009030407640b294000049495030303541c480b0001201000007007204e080401e20864030340c1d0402c400c0740789409140d40040481c2070000e00c2185101042c025812007004812040c0701e0b01035101d03500d14840e08244c02c42107400d80c1e01580050249400500c281c12642e02501808070040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 761954253 1250 761953003 761953019
    0x1b0b030603030405010503040609050a051b03060106050406050904142a0702010c021c050111070b090c0307090b01030e031b1225030c0b2a1903020304021302070b0a061707 75
    0xb00420660b8227076910110940420001c7c0052082d8510450151509110de100841c060340b401c0342ca901d01a600610050181d05d0700901224150341503801d20a484072502e000207400780c501d0002c5000c0c0b049078001402030350900b054a11040e495094040f00750401c803000e404603d4010130101038001000020300401505155404000307440d12840d20025020b03403500c45d50300307540c02c200c0c544586140000f0a4010f001c00c180640d80c0101c4240c01402d070349448140080e5485009006003919140d90b00c010308420b038040d038810308004180505994645200c1c10a40130000051a0301659500a09a400ca100f01c0c00d03030f0071a04011401c20341c86c407504096032103483e80050344000890031f102d480346240d004a201c14079054840c409808442501610680c0369100d00080c0d107200800481050016030710b100c0e80d441c030000079840c01c0c0c0790050700d81d42c541c0001403440c994081f0b0080481d200180610600c030702035455a1190800900500510303695501e200b442c4a100c01444880e50400041800307518 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 761955503 1250 761954253 761954257
    0x3330105031305072c040c0b13030b1303110708100f020403081215040608191109091b090402010c121101021605120307120b0307030f1b0b0306030304050105 69
    0xb03403504031035102e40500c41c1c0d1041d04d080c03820b810440d041c0c420011011004641c40075000c40b00342144250900c2400e042d550404c881c0c0442c051503508a00129407a07081c4004840781400540e0041076401050500f076118000d060680380d0190000396005811503201100000c41b41c04a407070000041c0001c4134607000540040800030040e50000742c00f0040000030554007005842d03c1c090001000180d42004440c08043e5a081c00b551401203040030420001600c0100f00804450b84114a00c2d02401e0f45203054500107003101141580312550b0000e100307107201c00241c840141081900e10340f608803030710010003183c0c001c2140c00a0001d440d43c440c0710300041c0b041d43d6881101c1e000c0e0900c0700c08080480c86040c00e90304240d40314526249102c42e4041405800c202c0c000c40c203550110a286076081415000307024403502078a03018865160714101c0c40544003080507000540d002050116060024503040070031011500080211401c068000300382042e9203812a4051b200003002140340524280044d6920307 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 761956753 1250 761955503 761955511
    0x3082208030705031f090203071107060504030b060f0d0f05060a110912010f050106030f0f0b0108040308090a121707020c240f0304240b0a0608040f050703080333010503 74
    0x1500405d001d40c500030b461201c2c0b00007500d508800540c80e4980044001d1189048440d4aa0203038008a0100325a58010301103806a940200c00c0006c03075a600800700d058015114451900903d4655003201807020001c1410309a074414820380710181c850600d42d0064404c500001d001120003040500a18649034803000780b6212404004a01c05d40350000301307421140240c0c050004030751505c040e45040e255a02c0b42501d49020608108150444480004c1054000900060a204200c40400c0741810304100d104180e903072142c2d03910016109a5001004040455403070107008907140041090b4500204681c64880e101500403135100e044c403002c0c480042603075005120303258010003520b00d01421400013982300e0b601075803180c20864010500000c004951099156a03186802d441800964968510342d04442c02441c0190a985960400340a9110841c0004219100d0350000104106945000d10f1281d1684614025406c0050b03662500340c04c0a40d20304558004520301101d1550b000d000a1900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 761958003 1250 761956753 761956771
    0x90306061c120201020d1401081002030c0f0403110109050f01140a0311070507051c150906060503100c020f030903071703190207050a050612060f030102160308220803070503 76
    0x5400442d0700d4030b09080c00c914652400507500007899480c020014087c1090b507078283e00c05c041c09989480c4056496400d40768013264142d40003c08540011138003815600b034400007403892941c507035507407400301102d105080600380800da58042c00180e900d4641c050240a08040e100d0419180d40d081001400d80d001402c29020f141e616086c105100e0360720005041c072944910000d1440d035042001300301c22040d20380034203036590001680590000d1a6130b00d000200305a900d20204000b5440e1038480c002d4125600100e42500c510300b600215848142c1041079174200940a5035030f00480c1c01c0c4101e80720311401c4c3d031035601750380003003003c11402e0100d0441e8030204c4c8c0c5000540b03062040141c0c10f440d80050b0500040010b034808041801146482d45803400104010bd8100e440d00384401000c0000c9400103007602c0c4504085442d080c0d07540c8081d0111850a1014a9120b00140f05403501904c83c01e026103205d80000170020000243c100c503041e0882d201608451040d045903103920044605030700007000300709 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 761959253 1250 761958003 761958049
    0x5130303090204022106180912070201211406060a1d040b03060103210518010f0909020408070306050f07020606120a0c23010c0210030f0905030307020109051209030606 74
    0x30b0b0b50103c0b5440c200c815a249011517006080c100c0411404103202c40b1250280c60302d807014002c05010001c2c803c5980c0c1003401000ba201d00b16400180c600300009286521050394540d00300c40381c1c40c200e500c1034002000c000c00e0f160031071702d483d070500c5007900954551070301040c1588141c0f0000b0034a22910078204000900108641c2002d0300800d003003200a80c01210b0305010214400f070707e01041440c05500c2c560501d0f10600307100b045d00b020740b05584651006414880c1c07212115540900c0781000b40c1c050041f0700020f5581d00d9481460179035070b41c0c0c00d00c000c2d00c00c41d00e848085460400003044203401516660300422468441004002051a120501416a114558043d400110003941c0c2100074840070b40000820b00b103641c0c1441d1210f19161030103040190400450005981e11006500c2101c11445e00140007849042032400502c003086011700684001b00802503455415000445100e12450544049074a032110107030940c01a41700b200c0c0e16400c6440002d00a0502c64050b0b400100d206007440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 761960503 1250 761959253 761959267
    0x50109020d0b0f0a090c0b0307021009031d0402040b0d020a1106040b01050907050913050c1b011a01110c010311070b150f0a0f0b0c07180203010302040501090513030309020402 77
    0xe0300380e907002081124504094001c2103a98000740c0074032640002d1964040c8081a400d0341c0d44480c56819006000c0e0800c3c0100120fa50300707100700850044402080300420851105050107061090301002d040701001c1078070503440386401c1c24002d07101100c2e440c0000d6410078070700f403e00304040e400c0700d12103c0c100440c09041030100e00d000c02030540118000c20741c0d501a5410304051003040140100000e0170301c041000122080d0300c070032600700c10950000d04d0004013a16580301c002c6851050182c9090320141c0310840e02101d41c01036102408594203104216600c6d0300d84d8005640301c00b000c80081d5920340020400d0010755010750080907010710644007841c6800c16030390b54400b21880513110143c0114110300840014140280a2451000121850060289002d02281603031005005a100900b4007041c0070405101c10000840a0168040c1c0c2d0741107440e019051600a4000f403001f41d2056042c440001440700c502c0c072559000e042c092031540d008941eaa10180c0141c41d44030350498101394204070039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 761961753 1250 761960503 761960509
    0x20a060209180c1215030c040510050d0b1602071503090c230406051504060c1b080d020c06120a020703090e190f0b0a060c03091a0301050319020a1205010902 69
    0x349105004100300d07113440d01040c0003160a003050081400160a914003034003011903800041203025a1800c440c041810b035260004858100d030b25600c4640c0046a41c80d8220400c041420207a00c60b40303941e94007055445420800700c1e0b8a05039440349102e60b003c81030044d05130a109800c034002e0720340196502626107035200c03010b03444800880d046200308244c08007081210319117070140d17200524007200c51103800c1d1949810030180e8400d80c46400c0500c80c000c01543c0400c54601009440da00c4180c207035007106991030341200d40701d400e4919444014004e4071507540c414a0f12405903030f020410244551041c0d507804919030b00a600030b003425010310504c881d0001d00c141010107414071a0300000b03038490038505190110025202d2a01c0e0580b18507042080900207511044c45d41c0e8122241440c0c5003050f0099400c2c251003600c2550015000311040000c01880084e200004504851095040300d02c034048400958000c40e0080300003d41c40032100b10104200c2c1403680c0d690300c03e076004c0d6000080001d143d07400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 761963003 1250 761961753 761961799
    0x6050d080307092102030105060d350c060f07110307140a44030f220b102304050c0f03010e010f05030d0507020d030309060504050709050106030c020a060209 69
    0x41c44804c0c43d5040c040000f1401d0038081c0ea42c10040556002e81d036503170b42e41d490001d4918041800016030040340d00106072160b0f04480d68090045915003169a128504046600c42d10211118800d44034108046003040d84074a10300440340b50071101039821322105588d0000300d00581c44a884c03c9100340b0100790301052151801620b440311081a4041d80f0107680100d031b512260029000c0e070101c5d00c0d00c2000740ba501c81c0c0400c8940c00164001c4805c2c2c40d035100c03116540c200f5000c07803c044a4200501c0c0c5041005141142240a10041c7c89081c08095848200400c0ba150703c9a00c038185017034100e1800c9903824160003042d00a0079064901d400c00c0f038032021150a070b40090b03210300050b00c84000100040c1c5801d942c403901400050b0082c00c14800301a0020f8030300e2285400090052102c90300d0141030510980c0400ea001d03510800c14051418207003440c80c1d4035078481c0135a41c4464640f00c000100315000744184400c10078030b50054201c09190b5114040250800803440307802000c108600c0d01d0f01e4080102e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 761964253 1250 761963003 761963039
    0x170f090603043810050109030807020429090f1302040b150d0f0501050d030207140105091509092203050c030f0a02060109180f02061c0501060f020f0106050d08030709 73
    0x645400b50350690410303243c003032034040c00b1500f00d03500001d000d01090341e00504500c1074a0304843c4035507481c0d81620100b802803420b81c9040400b903241540115030014407049040015030101c40030b50440e140e08001411246041c1c0b682800c0e110441c80401c010b0511b6000450890401007000d50103407003140c007040060f40002d201140306030307680d140d40b800c002107886107502418081d105010140300a540107550340c2010b00803245014000300300310b10207a100d00d0803640c09220181c1808200c842c0e80c006043d0a400080301544164011000680070200a54a074009954060a0142c121f503943e1410f440c00e5101c3d8050080c0c5010400290748400864030082134401f042d64014a45985006c090104407201040c800c0c424440e108568000b00e13030140d9a1a4582350119002603403404420108a00010f040c51072009050800f0700000b540e40d003000050302c40b003090f83c09984280750300980c054200c0c0d13002e0168079071102c021400c00340404c05a07009598080300e5401c1020b40d641d01d4490140000745060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 761965503 1250 761964253 761964323
    0xf01060e1f03390302030703080f0c0706030509060601030b0a061d0d0c030506010f080d0e0102100606022409061518040507090608031603050d06050411030103170f09060304 76
    0x181e0002c8440e2002c207241c40303802114420f4800c88504690009858003054803015242580103c1d81e1310503c0b82c1e0b80101c810510802c01201c2c0368681d1054040e000d0301044440c01c00714040c1900161a40d4000e004030a150903005103601c254505094040e1104d80101d0300c1c0d8030052442c80e900c446c00781c03905080e42d2002402100c3d141e07101891440e00302d1911030141c0203c0c1c034280407070100700844000020302e00070341c01d0703d4200142c0700444080101d203403410114003501c506007403c000242d81d40d0081000e05080da0401d0440001c5204d40007101c8140805681c5030200e40d00c01800507920190f003c02c1031f1541900105464980c0500341d42c00b140380d40081ea400d44494120070b00811662035030f80f0940009012540185081840c000c00f500005c030807444024003407100000d054501540d5940c03155015000040c000c00103210380210101f519013003400b00b00c481201408085e07403060703280b03403da80020440346500c034603202d240c03401d2112503040034004443c01e07401000307110f008200310002c2c40604900d80c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 761966753 1250 761965503 761965553
    0x212040803012d210f0b01051005120619030206070308092a1002010e01021c14010803160204091202060411011e0c1707030c050f01060e1f03 62
    0xb12030f842805072190021429208007480b006a940070164010200721102c0340385200309a2080c2007000c052a54090b8001c000c04011a4100200702c01c1c51400c070305a0700d040d90340e001c81c00030300c00d02500c1900c0742000104d14403070080b00003005454204001c000307846000704040080d0355264042041c64001d0742003207021030f01100c2042051384003088200c0c0440114523485400c4405d5405e01c0c80d8864060b03c01d80c0c09040700c0e001c1c0d006003d000b500048440d1980e00700856441d04e018402114840007070f140c0745603840c00d00701c81e51519141001c007a0706854070311000c0c0d49030140c50727807960780414041c0a080703811548840d840000300d00395410016002050b500606802c1c501031402500e01c02c4444112070521240300e500b000d001076507400004044045041c8440380303d216040c00e00850f15031240250000e0030000d00030040507840356000011500c40e400725024909081c40040c242d5040c1c0c00f032540c204003048006030000d000c4099001c5401e0b42e10f0428030010b0f450303446441000150703854a17013032980341c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 761968003 1250 761966753 761966759
    0x4060503160839040807050306090a05190618080409050f1006050a090807030309060f02010e0c0618130605100806060f22080d0311070302070302060d021204080301 72
    0x10003100035000d00c21072510b0600c80ca810500b4048522101000402140303040d01d0600085000340c5003e142c0c800d080e00c0782500c42e0341d940300382c564600d60390007424040c0c0030f00e402090401e00000356020015500401070228001002d5000d000742c4c450543c2951a90b07207034100c0b050594070f080d00c0601128081c402c440d81d59814903100c5c20548101a10408510383c0c0c0600b009944200d8800100c03d4a465203402d968a4541c00c00c125800c101a0b0403044035800b0303011002041507085600031003203401d40e450308200404041d4041e400c075881550b8201079134000c101d0030f0070301d8900200142880d00c0c8034410300c80e42180000c081244140602808203845d0346d0750320305202c1071030b090032088601d111900d0810303582c2c60f00e0340100360a03000d1440e95504030f2034082603800e800c01c140b0032886c14a0300a118510486980e6803401030f5285213445c01d11002c01e2920f03018500303c0f0300030000c4030b444d150544c005161044c659424800640e101c011340088459007800f0f003c29096429005600583c0901e02c0c041e02c03541 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 761969253 1250 761968003 761968021
    0xc0f01080c0423040e0a0b0c0a050d050109020306090916150302040e071808030708040e10050d1a010f1d04050c13020c070504021c0b0d020d0312050c0a201204060503 73
    0xc00c07000f105584d0784921b0550001440d40900395500c240704440d91510303004400b2040d1028001c11000305041c6007808004600109185d01641c89a181110b40034002c0c6c03070b01700015843d90800e503a101120745005900b4802c0d001c8181662f4540c0c4400c0c600180380c1a6603038000d82ca01c080644403040040c0200312036500e161400102072028000c00400b642c03905507565107003034891046114071020302131006c00003080bda0b490380c009802042c0141881034031210524200e030482c005040c03040c809607042000403400740035400d5480107440120074076034503189449400c8203101c04d00820460341481502c03002401611480ba8240c0c1041c0100d1016803910300a210190800e00c5681003a4026841400700d00300d5050015068401080055800a0708110001c0403550780040d00c403011b034011004202c090f0801d035000c41c000c2d55446007000100010f880d040f402c0d140520580c1900e600180c003a050307070000c0c03071901010042800b40d408212140100c8030001c2030f603281c009034031400c040303007022082001c030079 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 761970503 1250 761969253 761969261
    0x2060a03051503010e1f0e0a05150f060f01030213050a060507020301110c060c070611182106070e01031b02150901060308040306090201030b041104090b01020c0f01080c042304 77
    0x540d00703c000740907002c00503540343d07a641e135403070240f030032902d010b0744007490408180e4088800030480f0001d5500c0306410741082176541c038039443d0072080150310100007200611000c2c0c40b40e010f0003004216695100012004501a4003d010310101013115036000203401c1c1d81341203070b0500402554481c20b0b210401c074010035086400308a03042c660320004000c0168040c101040d0641d0004510460507122811400c1c610014184484003203110314002841c44044075a142080e209002c003120b801148203c05540c1e10080f0000c1441c00a0381d42c00040031a180320301490322541d04190614000802043c1c2111300900118214104070250f00441c0d9008910301c0791118295000c907010b0024000e4070b203143c0d1401d101d80b0440c84098005940c3d002c8540c11a8425006100d011500600a0000448140070b03045540d106108448840c1d107410505800c2d035001158002c01c940008100d001c010111030300540304600014400340341e1a404020109803080809811480e1811400601158507560000c0c03108803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 761971753 1250 761970503 761970541
    0x1509061404051006230313020a1235030f090c01091503020a110d0e0a0807050607081e0c0604020414240f040c0206150a0b040e1302060a0305 62
    0x110b007030034100100f8982030300181d0101c4100d07140400075200869155000e40102c1707a045255444000705102280c0b215142c2d0400341341c02242d40c2c070201581c2d11525401d4107010f450051104080610401018201e8120a0940d000c158840ca0944000410000d01c0d94000c54078202c14081507000e0004000040116200d14142803c244403500d051881031080c04091081e88002c042d0000761010b0340031700c10300c9803503203100000e4116141e03021400f03070103000e600031021124000c42300340c00300003494200001d2241c100e5501816a620b890703100e40ba0036000d580725030060390350902000e4964000c14802e40080107079065a0000d0711550806104100560710009103007181041c2440030321846180000b001d00700381c0c4a03070b11846810380c003981c003061211001c1c4003072552040c035004502003540d8021402900c14550702810740c1000203500d00b00048003a180c0604c200c0381c107040c031050210448100c100d80e0001c101509800300c80700d950f80060b0322540031480f00c41c0004d842c0e03014488907940380b01102d000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 761973003 1250 761971753 761971759
    0xe0102070209012d0303080714250218130615060f0e031e07030b100b1209011415101d0d030c020303030903040f06021c030b0415090614 60
    0xd042156000280801e006001d9040b862401c0b01c104c03d070301c5402d0340c11210070951301e12a00103002d81e01d0030040c001d01c00449180d004103070492041a120003400b411154909624601e0381901d000980b200106801340c214200e030032482c820700050310386a00d000c109119142200704150348a01e40d1070000240d940c280709440305203521007010700c10a9002800045400b146142000c1c0e840e03600800a80b6048841100c2c0b0080100d1000800e441c20020411106581c0142d040542076115030124403181c80880c411103001e50014081a041414003e01c8035400c43c2e924400072682002c550b030741900003d03042d41e11894861600d803102c1400d003801c048102102c80b4505000340503000700490f400514108901c4c4c2449100c8a5181004041c0601440c0001ca60060216620b81c500804000d07503d070b000c1d00800a070407070300240004070f40b440043c012800d104046000d10000d2200003068016040510080fa401911000c000502d621a01ca0110060900c1ca5012500c00d113000c4501c00c2c019002148240 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 761974253 1250 761973003 761973007
    0x18120206010302031024060503070e01110604060c12020f040608060d030e040f090b04080c060112080d1802060c0606010305070509033016150e060a110d1401090e0102 73
    0x2613a800b24043c0b9100340411070100ba400c0c401100d1500c01c4031756051901000f2940035002ca07045510101441c802c01c1c503521010340c1a4010b00055030355407596080150b050340941c00050018003d904030b0b0340c10914034142062200c4c0d40040312820ba03001000c0350f26140c1d002040405c080c3e139000d42c10366080541035502601c2012540c50042180050905260180341c0390040240d00907502d50189540940100c15561917040c54030302b5020581c8404400700341340c8101c8001203031071190703042144865a800341589242c001c080642c08068503050356540c24075864241d0940141e21560000c1078019180e00261406182c1540003404491001d0480020003006002d020340d00d440c0051600c02e9210300b803001c10084aa00d00300500480e18054440010781000701700e240b07114840a50340310b400c80c030503400c9400f41a042859042140d11800004002e58080d50114104010036400040d2040d80806004c1c906400814500292940c480540035100081801001500418404e1421700305070400258 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 761975503 1250 761974253 761974259
    0xa050a030c0c0902360d0b0603120c0a1b0b0d09150501120b040503280908061005100e150c120a091802071e0308070f08070f020a061812020601 63
    0x200500241403c21017420940801e10510151a202800d0f00343c03000400c50788088820389031140a00406590395030003071090789503031140450010142d43c5c10030702c0d001c000e01002005484440359111040c820180c0e8201310240450140007aa00401064140300c1010401072841e191001d2069080c4c00d100d9001803407c0014070500e294000b440c805560841d1400203030b6103450420038111f01c0394007883c4008455104407603040c05441c078030302c003c0e000c00d41e1900d032000c66840c2c00144c1c540d081100c5081450401c11003c0c402407400c840000c000c654546019803030060030074003007894011311140c0c4083c001000715401c074042c0300c10800711140c00404003c1e54100405400058461003041c0107101c100d0a0341c0c0031669484030780e07505840382a0f41100c98840e4101c10b101e0061101014018150000b46040001070201c42c0581c0a9100000c51952020995910104122540304a00740321004500800e02a0804a04035011781840c2c0159110640070001c140c1c42e010741a00140da900209540200d0010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 761976753 1250 761975503 761975527
    0xb03060a05070905041d0d0905100302040b0409050a1805030c0d050403080f031812090117100504021e0417070e070504140f040c031e0603050303060d050a050a030c0c0902 75
    0xc5004c55a0556002c61116401c02d4040f22810b80008507516910480c2e02c03e00c030309640003030150102e80060b50684140c80310b80c0e004400b644528051a5002e80302004104a25042944034075030100050b10000b801c0b0b14070320401d0081c1d010307582059446a20100720210f0004080c00f03407045441c1ba0307081140c41c0031319650754060a400341150703c400001e40400002c88040ba490003402d450303c091b10a4076107610030021220319070340028420701c1c005102210180910000403039040d009065840311105003070316201c1004080d5000614201c524a06000c0800c020461074011348050030310b0018003400800705da01528070380400c85e4031803500b0100318070a21007030070f401c98110341c240d81048110302c0041800b100072401070909901c5040c0c0041c50001c9040c00980d042e4465600340c0036000710744140202001101041d0340540c00098100d03002000412110b1030070f5240800030a2088040e920384030aa6295141450000310007600030881c065112000c0040c10559000075201242c01141000520f00007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 761978003 1250 761976753 761976767
    0x5192408060d020109030212062202010e12100e0309030d0f08010e07020319030c0801090614040f06031b240c080703020a050609010b01110d0f051810030b03060a0507 73
    0x1900e0142c50303420240019a446003441c14040d5030050900300700e50030001503003560f5020840c0c01840000040c1006848603000e01c0219000640507900d40c403441c0c2c03010007042070220109100308140e100d1000905210b2105004500d28100d1210103107440e07801c46002c1c035080100c04883c8800f0488031522840e8080c2e00400c00d5070665212107040504e039910000e091b499403050a2850340d0307119122000d0280258980c010200d0585207035030f28034650741d0715000305041d541c940c091044502c054810028030360800d603000c0061a401d088012071940e507a40c07180001d20b01640035142041d10140e000b4090341000071030329110500107002c100141e50300a0304c01400d05102a800402c0000000740303803404d161007045004112900001595243e050000c1e10302d000340103200a080c04151440c0c52040260b5011440580011031a16a600c140d40030301c400319516400f020614118003d043d0380d001d602e886505140c0031150940d00c000600d46510400c242c68090020044c985090405003000841a4000c078 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 761979253 1250 761978003 761978011
    0x210090c1205070306020d0b0f030d0818160807151d01080703090515150619181809060b120a0311240a05100b0304080702060405192408 60
    0x1848000d076007503141050600c0d00603400a443c50380003199109840941760f101111811084a4840301480135101781521401c42c0104000403901c800006a0b11007040e01060a90448850640e08522458035091500814039040b95420360700100c000c2c40032060022090b00c140b20903080914224400c14151035481c501451400e0400c035012011400c05c41c003d4222808042d031040644510160b41c1032004003811003202c980c0302981c48000702400c18207140044500d1107040b00c10099050000b40d0b41030314821584464038020b16036500c0c00050381c20316994543d95a1900c848085000c0c0c0daa4204034081c0c0b40c030703d0b581c1c030702c6201514080035030340500080300702e881035042c1083d28103807203040e02c42820404c5642aa805084a040c0500c0809440741c4816100d1041000108215150140c42051a104601400801c3d010410104011402c080302a0205030b02c010640c528164858002c54501c036294040c0d4201e40c8000c0600b4400701104102e0441e000d00003032480c000040c20414010b001075030140c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 761980503 1250 761979253 761979269
    0xc08010608120c0322090515010207051005163f030b01050d2a090302030d02070518061518041d03040911070803010803120601090302010e191707060210090c 69
    0x18105801ea02801d03181100038405403c0400c043d207400c0d088c40c0030480c4000788240c01405500f50115461429144031060700413207a5860307040c03004a02da80d030b12a81a10074290b89a07405130f031080c1114002c1c943d10700082e4890b407554654171900c14000a918840d4001c4250a00d8100078031900d1726640300c0240c90002c850480301051007090300358030840d4514070f140c880d52001012246040300c00d8022600804981c82070307044507040c03c500341049850740d49900502d0381c000c03217888031400b080361600102c1c2e4003c4001003400441c5401d21503804101d5201400c1c8a02c45583c0c0800180780b0302d0030b40325014042e42101c0314030003942c5203220803a0300e0744958040ea000403507881c1e00d91414101e49406640880350b01003101545c81d40c507491829600e40282c080014603d01050008141e5480384404000b1030390b06841d4400f40c042c80c48204200324440340c4007070900c541c00c800e0001e01000c0d00701c8040c1c030340e90800b4080d026081c00c1140003804c1080c0808510b81090801035090000303003220395103000300c0c2c1c494 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 761981753 1250 761980503 761980537
    0x904060f091704051302040f1a0c1c080907060f110703020409081c020f0f0f1303110a08060108030403031430072d0c0c08010608120c03 60
    0x1405264024841214058071001d490b051072400000c2038802001922801c482509403c0e0818041000b03038840e90003003030300074500780c3c0042000058035071030401016200110b8904000e1a80800d03460000400da010744080c1e030a4800780d94407a00948000d410080e001c0141140f182040005000321404000f101c00300148210700d06203004051054101941d8002c0c414400381d0558145903900740c001e00740c2c2c0c00a59201d00107070b00c00d458080c401c407400c45d0394a815540c2000f20715850800d4540002c95404040b08003040f8002e00c090240107254061485001395800b0404071100f80003400f040c5400c90090782d4407441c0140709103000003080c0d40403660300d49011004215038008001c1d0034022580354403280551002188a40c5280d0070840041914409440d50b16680303881085442940c01140e80c04000e0215001c0f95110180c1a01003030005030508103040102142d9507242d80860780da07405036099940d2004184078011083c017101e0842c03c1241e2660742801c1420074070544904c1000d0001c0c0c1c0c08210 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 761983003 1250 761981753 761981771
    0x60f0711100e03180a0e010521010e070e161e020307050f0d0e0409020616060204270501050906060a05210112020411031003240905070603110405090406 67
    0x300704150007403800c048140107200180403840e940f5045040840d0309a40e51841e100c85600307110462004442c440b200129031a403801c000e202c2040561040d192281c0c04041107035011079002d003e10000c00030750000038204545004041011000094400c080804148400c508050340c400c0150510040c40b401c00034180340d100900381c0c614481d490005006000301504440c140c0c40200b0700590001498941c4005403000c90300300000c8a190380c9009501c8042800440b410550306e80320031480b607200300390061911b902c0c2c2038203080008030004910031412003c415001a4080390250500401c0155802030030303030401200040751802804002c034200103002c60100e9080d02900440e007440d40003071654042d6540c42d4a880c419006010506078026030901109201c100c0384001200e20980144144010103410365590801886c0d10144801e000303180d0701402c41c20281a88204a4041d01c40c0005010081c81c14402400b9142c128a030f170085504140b104201c19194203031515480340d0f0140002881c5d0305 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 761984253 1250 761983003 761983037
    0x70512030d050a09060c0809062d06040b031218030102131802070c0b0c0f0c2110050708100b03010e07050a1b0b070e150901111f14060102060f07 64
    0x4064080c00d41402c1c404001d11094000f0b0030103008007540e000340c83c016500e003501c500c1251101e980c014002c0703070303152b4211840360304069040d60402130013400410b10810b00c3d000a460003d0b083c1c0b145400000025860307404c48248022046564000d8009504254003c141c0920b070110b544990816a29503a4503580808102e0b0304940b0080d0b0b03c202404029511002ca44046400c2424150010b200d10354051030b000d000040c00c001202002042d0003a0740048000050a407901c648003501ca610810a00308944a51070140500c10711481c2d503409120714201180b050101d58660041078549010070040c040b10a902610b99445201400e0181c0d98800c40d100c12985004008805e1142d0080704485900b08100110098002e19540d690041c0da001c4038010042280d9284140000d60f0340c0811807403d865020b10f01060b21b60982e1400e0b03650602006170400300e5440c6c0c62200b07042941d503401000d200c0c4400714a2640d0806030a1000301494502010005800c010240122050102c1c0303044d9041d80744 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 761985503 1250 761984253 761984261
    0xd0803060d12020318030c09070f09080715170702060a02070804051f020c120717120406050904060605090d02150408030d09050601120804060809010906020403080c070512030d050a 79
    0x2580c0000c11640d0b184090200a4907070f00422844c0b14030b0310004c0304802d040d1400041c0b0445059000384120a10307100d1050680d03840d0140c0340443d09100040da00040c90a5052110b0402420301c194901c11240031071500a01c0c125100107480546901e14060003200daa0000300654020142000143d4034489030501402c28000e543c0004d034890071500c0500c1220b014051a0302c00c2c0c1c00b0980031107009111060420407070034011075110720641d004107020020300c9042c10855121062190603a4440848a0841601c651040d00200301240000030032503140d050504c980c0e00141410303c2c21038105031340400024591207407110003030b01c13541e00e2030089651100b02c42c0c00c8800400406044a0780c561040070b100000e042c00c0d01041d101409075100001d10580510050000607034030026080ca042e0600310140ca106002401d2400c0c50740d6900d204400256441c4000c2c0003070f45c0100030081c0c4500c41e141c00c0a00d4051aa00701d1801042003104400c20708100001f5900c86010080300460b0030f40e01c41c8000d2000b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 761986753 1250 761985503 761985529
    0x201020a1b15110d0e010b01020c040b0604050d0b010314010b0d060f060b27060405010203030415060305060a0509010e1609020a030b04050c040807061b0b04210f030e07050d080306 79
    0xd03d01125000e0034421030b0001c002c0700150361018481340001142141c00c1320282c1301e5040c00741e000355080c600c080c6040d5000b01c650717900080c81541801d880d0004074a01c110301d2902103503240c400c0001132084c4001e801c1480d212800700030007030010303c034050003280d081c40d0561001041d490301c81c3e804141d0540c454200c00042c1100d40380075a101c45c0f0020341e01001340f90400c84400380e86041c4d200b0b025103003040340844003520010380041d8615121503803101c1210007c0c04641555580d50311020002400038881c5500514800401083c14141f0075040c5086400410054110798054283c00960150100d00300b011100c40c1eaa0042e22a0354249040d000742c00400034107075001e0b28090810541a0f280300150040d42c05144c01c0790902d540380c0a056408903c107030845201c45248000035400551440300407540140301700f03e00502400043d0510710ba080a00380083e02250364440071117511030f0300d80f10310404070a0341c50040c41d040346410003240440c40600b4015003011000000035040340c45440240841c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 761988003 1250 761986753 761986793
    0x7050105070203130501030207050d0e130515040608010b030a14010b0603250507080f03100b0316030b0d0803010e0c040f170d03050610080402010e0d05011a010201020a1b 75
    0x101d140034400203460340e004c142c40702c03451103c0502c042000d510034030075030b0343c1c1540c424020140003014002c22f41d440c000300d4807081e80c80442010408a145a6801028051020031003c50107003a040020070060b40c4164010080d141c1c0741c039032000842d903070006c2e40f1000c20b44c00c500c4601c001030b220a40c0c07901504000c0c4d1180c2c0c000c0b00c004107102302d4000d6a0000585600030003101500c2c040015411180d51180d4100644259400c0c08180341c0818004019500001d0005c40500d001e40e44400386070f0150400c0f1181c000003070200d5580480c0715010b002c1c4507042c103011616200580f100d6a03d902150206004a124940c80c880004013422003401c01c40e009407500da070824074083d41e03440e9260f600d0041c10740f005006c0e0050a81041c0b80c0d0380603009882c05185c004191030001c40c0200021170300e4100044c016810094031007002d13034032615812a10b080380b03805640041040010800407a118441c40c0c4503141c116031041020040c00e540c0448202807030744e030000c80105201920300303110a0690442c0e440b248 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 761989253 1250 761988003 761988011
    0x31b060609060b040e1609060f0509130902040b03030f0a0513260f03160204051e0c070506182112010e070e030c1311070c03050102070506090d1b0305070501 69
    0x43c821080805001120a0200320019030b581d0702403e28000000b03031004401084540f601403001e9800342200a140304810302d02282011021000510540c012141c00100c00d9520621242075041500072800c0c560f105600942c85d058115001c041d41c2e100b0840d008082081c0410b813802044c05c41c1c6042e000600b48000907800303c800800c00c0728813420030840303200c115120391724020380071040110555540382c0e040e000c3c07444c61440f19001c0c80080c0400420b07649040c0100381080d01c64031004070741c95011b0704c01448816200d624030314210389003007400717003145034456540031803004030b550000340407102d19241483d80c5220650106400391075004001c1c4001d034030f00d0410008110b00d80c208803824801c084903035401c915011080c01385501e80c8410440700750041506c1c20100a10b050940241035408440a43e00385400b4081e250f001c4041020f420031070315a500014140f0512900300142c42c2c1014104010b0120862030001c00341c6041e01c21000c522005001c481084141070044c401e4440c4030350410000d00c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 761990503 1250 761989253 761989259
    0x20c03090904050c011b030c080c0312091e07120609030c0f03020606180f04240f02040f06050316030f11070b01031401020c150603010b031b090112031b06060906 71
    0x2600c4a01150034640001c0c1c0080da1442a01b00c1c884880480d00e405450700000d9600c40d40314030296130b008c15140000ca100404c00c41c045021700f00c00f07e40c4640704401c0944001c4980c0d80142c006031064003c540c1c1d0582c0140c0d4280018074540c074902000c2c69200d00005200980ca150941c1c403011002000340107000000204014103070080380661140038120f5402c1940c1204014885413041d080e030b4680386044052002800040c912103c0c2030401000503d010440d003581e001250a48594030140e0219a0300800e040207000840407410001e03000302d080c01415480e26240c4226550310b6008840308054941001046d07010359940242c2d04500c03480049962400641450041910288000c039002080800c1c4402503c1c818401c7d1400030f040600540240c070900c1c84c0140d4022400703011141d165684015010182d60100300c3c0e561900803480b541a07134604594100819031205034000f540c0fa50918110070002540070314408a2100d440140500e200f00b40e0600c04010100c54110038030051400e107000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 761991753 1250 761990503 761990513
    0x61e09091d060c1c06061b0501150807030614011d040318080102090a090216030c0510051e06030712060504060f020301080c040b0d0b2d2706070e0103020c03090904 72
    0x2010482070441181d41508030340d096400488100f81b140740000f81030010800c034802d5001322050f228500810020038915001110716004042c80e0780510f025a1201e90100100035884c040c42d01111901c030b0307070500f20398501040b601603070600c500d800034031400d4800020308140c040e504e4201800303800050501c500703884001060003036200080712480749045040010741c1c82000c0c002c940e4541401b00440d0040c041c25a130a940b0441e040034202d601d40103640c0ba00c1c0584c150340c8100341c031440000d10400c4601c065940030f000082c01c0074140c40e0094000d100d081c461074152052044003594045400a10783e5280c0c141140101240507403108200d000100005215000040421b81c092044400b0001c4010481c1005110501140000c00d00444500003600203074007403100c1c100702e001401e800c811029490008500602c400c1320296610b010034000c81310500d810803901105244120010b0409041004020b0078100344905000d040640000b4504039800060069445110014001200c682014602 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 761993003 1250 761991753 761991757
    0x15080d080f22080a020c032109010e030a080301050a120b010303050f0c070e010812071a0402060705030d144005010501031104050606030c0a030213030209040b01061e09091d060c 78
    0x40100144501c6902d02e28510340810201c101584212303a4000f5107200c60743c52a401d800c006812814440745180030101c2e51070500059640c0391003054240da49605101c00c000121280e03401101c03d00c50b12900410004600d2914541940d41509100303845840c0c610285d540c510030b10b4424180ca004044000400c410309840003810703203060070144e4803003c8cc81c12040d980350040c13400140c0300c2c039510356040c0c4902c2c561811854015001406681c940044c5072107507440c660001009080c40da0f542c561003001c5403801d003034054008913035810504044281c941c1100540310307804042c036204030301c41c1942d48121850708150b00207994004002c0c0060b41c6c0d0f0703050401114200c103101e9170090f81403030300040680c54442c0440e0310400451205a04081ca0204224029044000c0c040601e06548a0120269844411f074910070b520030f44a10210b50706143c4000d000b903164048841030f484459100341c48040e040380042042d03400541002804001008010800410040c004000d5001d03040502501240d0040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 761994253 1250 761993003 761993017
    0x50a0309090501210803090111040b090f01050a050304060e0f100f0f1116020103090609050d02010c090f0e060406090c020d0f0e130203042415080d080f2208 69
    0x981008560703620b0300d40b94071052080c103c07131010200d04c080000000301d404c00a9074000c40c21600003d29440988005070283e80150001e0340b00ea00c000c60042030305d1078026090300c0c0c001e07401c0ca0305504041e010314002c2c040d0f0001030b0000b00542d4441c0d000c40c3d81400100441a0f0030081c0c034040f62460301a410740d140c0100400208628018104a14051744051500541d801441220750540c58548465040716285107898003c034109610382c0001d5012682070300640c2c071043e01900280c075041a00300320103402c4441c0450200240602440104580d14a00306403a04139500390340712051590305e040025005001c04c0d001151780710300d00b042e010351300360380001d4405620009031289405011100420b07503104c030002e605540e0050303000508507910b9100c3c1d00590f030814420101d1794079581580d610080c2c079034440e481800e000e0b5541c221600220081e002260002c06225010340040120076000410512000700050700500900000c0782131280b03600220200e0b0b81b41140a0070180082c3e1420007004e40c0a45 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 761995503 1250 761994253 761994269
    0x9021903020120031b121206011b1e03030e0303010905091615140d0501140a0b0c0601062106061205070305190b0105070c0e010510020307240603050a0309 68
    0x4410b1058a818142c2003e045102901c0154141080d4180440c51000b104850404034011014400e80e078041c1c040180c141e81080300b01020302407030230b40d00041507000c07200500c000703c504003040240419000b030314072040c0101040341001c100c0100e003401d0300500341107080703400c807880000000121303084c59a005070302400c96071040c1c8000c0d0701c8614007940c14039224000c001c08140c4148000700d910740956000c0c14480c9503406440d040080800341170342100d00c03d034840708080c1c480105002231860900240030190003031141c41c0d0b00305021040075640e40c5905000b80c0c0f0901001480501005000c900a0301e03000940d81c00138480240c0301c0304000c0c1003000c03424100105506140c007245406019005691003413100a05c0d00b501c0c00000103006011304140c200071418040d0420a80c07010403100d8002d000078100000900f1003e5160106010010706001c05000464005100308000192102004240c0480c15001c8030203007440000c0794001400c06038002401441404903010806410490080c2160480 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 761996753 1250 761995503 761995517
    0xc0f0e01030b0630040503030106030b3007090905030f09041e141302100c0321050421080711120c0a0201091a120c12090304090c0e010e0904020301090219030201 71
    0x280e5080521300819100208130360403d10040c0880391082d4400303100311100034680440040043c47d0203e088503801026068804401e0101206001c100b00500c020807400d4402c0150418540f40c05449001d00c00d01041c03086400100c1c80750f01c0e41d0ba9003008103500c283e01c000d41c3c5c054041da400b400c01403d0384000109000306d04e400007242400421003c0c240e444d00507001d10348402080030112907040391180102c090000e04403086903d040030840002d0700205040300060b5a08082c1051540c41d040c10741d80400300403c1d4150707415a5940061207a80107902030800789070102c01d9000043c1022110032810f1010301001c40c0d99652542c0c005007400e034140c000e0702d0b459440e0703032035944602e1802002e140c0080341540c00c0203000816144402d400b540510307280002804d2400e005800a881c0d081130300c107481117910205091048041034441c0740f1075408103080400c0c000400320006492480c01ca400c03148607210001c0080d0640d1820341002030041c3e4002c04890003640424001d031401103076808160300040003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 761998003 1250 761996753 761996827
    0x2407052b090b0a0813080a020d0e15161e08120f0103020102060c0a0504080d051b1b010e030f0a06060f06030216141c1d040c0f0e01030b06 61
    0x204040810b944802c40e04503c0c0000c1d0f404150390500003d08501c0103906801d00702d1001c607003104c01a140308034607a800341c4105840c1e1000280800740f92640c1c5c900c40e03d07807041c4058654003550210b443d45044c0e0702c2c603212400c0103400c1500b8142c203030042141d108400010100d04001082009180040d254250003080b038417450890f07032603410309002c000d0140c1d02000100e11540720101c00b500b8210000c0c038285240540b21b010181c201462000c840c80410004103480b03400100da040140c4d00c0d212040c00424195840c110108400c40f1f2201c030030760510000c8140304281d030f00e0610a0000d0110110704442c0e84a0701807500000611451150484450543c900401c11601c030b4001c69988140c3c0c50703070080001e80780b80c68401910015014500d090b12404484808070703032030524900d03444011500c690703c0c02c1c000d00d00e000e241001c40240440c42141340002c460003aa400c1039080c05500e100d89005910080304100580042803140580c6901c11008610402841e120000382020703418842c92201c00071380 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 761999253 1250 761998003 761998007
    0x5010c030504030507061e1d090a020702040e1c0c0308060609130c020d0e0d08070b0603070f0306140f070c171327061d060102070b0304060212060f2407052b 69
    0xf140c408a51050032300c040c5154145003140c0d1454100208580040c544070050703000800b1515400141821500088600c4000212040e1941c88031041800c003940a800380d40e8008203558801404d45208440110f031078100313038417a40041858004003540c01c100724683d800c00a5580c641c014420750000b80040c91601c540c1c204107400c440003550101c401c50504a0f5640c0c4c2c148500030082c01150584950500020407c00800c0740800850049200080314200700d070300360149030002001e03a0020101c090a0201c150703440804011000d811040401c3c035000340301001100c0e8030440107880030417029040045682401105042540410075270402d58200d030469540c829500c980c03107101540d5400c8032000000442e101c000641c420070500c10b590040341c882c03640355215081070700c0c107841150380030900001c800740f01c1c1c40c45070b0071a008880344420010040001201c201c49009072031440d00b03203a40440c0070f4100c1241940c00d11984203003902c1886511100c20f00d42c5050450b5414156071038075020400313282c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 762000503 1250 761999253 761999267
    0x18090c0c0209071e11030d0908090a0335030a020c0109023111070807050106051e030c0a0806070c050f0703122a020108090c0a030b01090b060c0705010c030504030507061e 75
    0x150942d001d541010a00c07d9480b006148011043c0d0320314404000202e00d503501d0360001d0380174521800403224000c130b1060b074809036085483c02e840f12040d0810104000c52a60201b84c99200c010303c0800342e55548542c100034090811081d009400c101040b042582c49520001c00701c1006a407280c00070304415040714000c0c29200300481e403681c8a103040056001260b40000200b00150050300003003191f560740c00c0400c3d41c44030f44111031110400b030b21b0004000307031800f8801001200011244400c40300c2c00c08105948135003024084070305001940038440b00b000800d01c20380f055031101c4001d07101000d40d40e041c811054441174680c940064040003030601100154120000c43c8128423040e242d0811840c3d0054030b50748d10240000c45c030f9205181c08100281e0b00c10910310055442852508030741e51400d00d000003601c658030260380c03050400f032003010002c41300040e465003103e10919021111507006c1c10281c0d480e100e19003000d000390084500108059400400c011390049c3e0000326101259040c02d402c81c1c400c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 762001753 1250 762000503 762000527
    0x60b1203031509040c050d0c030804060e0a08010c14031f03051b01110606010c0c09050411120a1e02150f03250f030b0127030c0618090c0c0209071e 65
    0x2103003645d041400300d13080c0a6071100744503100341244928140c41e51911980c03600305a00c44c00002d40140c60320301940c00c2a05100004028600080c0217032410b2603406003040c090503104140808002c4001428100b55017945031004005032510b4959584a0800c075407100b1304003505002d84884812a0741c855441545040b41006a0380003401c0e6a07228400110f585040040701a42c440c1d04200010414082a100c1da40c051740c42a800501e00485e281d041c4045040203420040083d040301d03c08030046001400d8100307111a00745030281e1608a80e10000c1c8808081d880c030701c40c00782004200d641a01403070078001e5001e4011000d01888520358112017809510820031312100049901e81c2803a58a4081c1d0410f4400c05d078141001e070070310301c0c62a90241801e0038601e2681e62040c0410410801c2c0101080c00e000503389600d4414a4007000c881c04001c609030600c51a41120fa5441203048071510416250103099801040c02055091540c4020421881c0b201d4100350a0507807029408400d000c0c0d200c100300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 762003003 1250 762001753 762001763
    0x606051009030623390a0305330a0e13050f0d0c0816080a0314060904020105070b1509040c080c0108070e19030602031f06020c0913060b120303150904 66
    0x507641748110311003140a00626400340482e03c0790110407418165101c429069408081c040d10790503901001404d807803000d00050550780184100340d800b03403414003203042100003044000c854802001d01280702c0410a44c4428000b484c200207100e4010a07205945400310300406c210f8014820340c001c69901c500416240c500807a081c1108100081d0b040b50117003001e0b08100c0000083ca900544070307003401e540f2414002000a582d210801840c01d901031300142c108506542074075032840c0a0f8000b134290b11a0400141c4101000c200140701082c04050f401102900036080c0c070140d040600d02000020114001c50b2481c0c0151074001c2c409501c1503404502ca0b00ba0703941c90105241620f07060001000d05031400410f105e00c00f00c070100201e400c2c0d0000310b01480d10140c04282c4c003179100c0d80b07090422445800100c00c5401c01c00406a550303890300082c41d0461000d0b00030708440702952a0500041c4046800681c0050148003045903281011001d14441c844c000c100348072454a000c10006030040441d03000300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 762004253 1250 762003003 762003071
    0xf03040212010626030702040f0b18132d03020106051203030f062103032403030f0a0305180a1109010b2506020f071412030f1306060510090306 63
    0x8140d80a12220500c0e04c40000d0913203150140c0c40c0c0100e03013070390700060720790f16517903100e050300b03501c03400d0544001e0798003110712800000320f0800c2c0700780d50380b4070503442070203841c0184402e030f11505c4a43d500b5250b9061000c032811500f030320000e0300d8041d018241c6441818801c0608481e180404040130003141c0c82690556070540311a950300007004040840004080f2441244002c802a00d45041000b14004c00514140d94600d214000c60030840c0c8014040043c02500140302d071072945a201000e0b600403066504003c592070750303480c500a010300b0b044110591301c2c0c800c0d20201001d110465000d280035101c00c0c1e85c2c2140507a01e0380120407103840303244994640070a03402c4840d122003041c0f0707500009241c8294405460b09105070018072044c4c0000302d00b81d03a4044c02b000c0c0c2210344941000400c0e0421450f417180340c150b140a00c2000d03d40000204881510403103c3d040c10104802e641c03020018050081654568031610300e001002c00718140400c65165281885191200f42c1003880d02d03030341b2084040076072 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 762005503 1250 762004253 762004289
    0x40210020114040318091116030311040306050a0b03030412080a03271101180909050a0b0c0301080106080105041e0c050307150e060c0304290a05070303050f060109060c03020709020f030402120106 86
    0x300c50b002c55032410380400d0b84d14058bc40764150340b200100011401403502042d2401d000322035408860701004d000c0e00c2030b4010081089518841c0040840440c3c001002c1912403603045001c1c0c0260148614420424007001003041c000d50900700100b000c140201d003c0f901c0c204442d0010744480d044109242d0b2404040c0d102045a05002c0e00b2820070944100e0a41304031182c240c0d5101105030041d16030700d0384594040014082c61304c092003000000e1020000900007418661604000f010f030a2400300000388540100100340449010508000e24001d400c9a0500d541d03041c0c44040c4035068150880005c0c01c84401c0042032a000c0c2c10f41c0c0c0c00c0542213000d90700d400e180c0004001c20342503460070f04e4000c26031403051107001258040500b85942160b01c902d03944031120b140040031a50010046030f0121001000d03c200c0f030f41d201005400340e56090800f03907260300b21401c099140118030ba00c0701d0002800004e090035035494220146004510a030748181c1d140303d4401030786003662841e018064060841c40a09 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 762006753 1250 762005503 762005527
    0x60608061002100c03020c0d020a11060315090f06120f03040b031b070b0106032415171510020f120304020d0f0605040b01050a0e0402100201140403180911 68
    0x1000ca88601d0b0049400841e41c034004901550110955500401d030b011176001a0300c081480340b0840c981c480d102600c416100c0d55030b100350b210440002c0c00d004200c0840002c0b0810107070707010309442c04002400c03a4100d1400c1c9010300d40d01103040b14000d010340f002d00c0040d69480d1001400c040b01d124188091030400e0308210140b1516080100750102080c0d1000311200000030040c01440e0443c0204460001903051020103015286204c100c0ba00104489500034183c00c2218080e00a44417030080101c0d0660400e10201d2f102e01c100d000325903031112200d0a120102c140ca0841c481c07440825204075481e031502240990b201da11441c120b0861342c001d4208004070303246000007160701070310090030011500e075a070b21884003848003c0c10072607a055a032014442440b01c00790b00603006010844003a80e41c47d060800b071203403a010150009003e1400c0e50724006800303000b034006070100b440c8094190075518007424014a01818040c0441c103404006001007414600c60145182030b130204070940d80f41058260750 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 762008003 1250 762006753 762006769
    0x60f090712020f0f0f15030f01050904050a0f080d0608030d1109030703030c021f020610210314041d04060c1d0607050f010606020304030c2102011116031208060406060806 75
    0x41e4040b845d0a125100c0790348240460184104036243c440d00ca06c0d20340c060000000c0c1c1078200c580304148100400000542c001014201240c1c081d0800d82c02184615050207075015007200c0403032003810300101080240300000038103a60360320900d052006d030350207002c0f0041c50b200300ca10940e01350300821828008130b4041c0004400c10391026214403414400c41490607448411a2544001a00300c402400001003d82d200c01015109040008a8140d6007280c00035090600d54002807e004400302199440207149042e1001801c03008544005200110a15480e02078201c0c0c0483c0c1046c0b91074100c08030740e4822210344280f41d6440c1c1c6a036801c0b20440d003c000c0550001f4504889034410003500f40980403003801100014447e50300215111421362600000c0c42c90039410003251321210802c8010100c81600c20360388403580a0a242000074200d400d110304150712101000c1881c00c40315000003c004e58000c0417000c2400310f07550031415407141d4003004117660480c0b00d2600001d1b0340c180032400d02d03c0c100d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 762009253 1250 762008003 762008029
    0x4050105040606140a0905060708030603011508071e050a030b0f0c090303030103080904020c0f0601051003050415020a110105010b070c0b09030a110a21032304091d060f090712020f 79
    0x24110001ba81da0700000d28260b00410045918102c040700340301103801d00340144910324054010300400c0070308041c00650385940511407a5442410440c0d80e00c004400145014080c000240a0030502d40d100c0c1807c0d86456410340b0120080b20040740092000418003003550306154000b8082e41c5076910795201c0000c0741d0000c440250780160300f000748003070740d400800254101d0078159024000942c03400381040840301da03d07007094041c18106010000001c004025558113941c80300b50040e15079800d444101c84050991310182800c0d885c00c4004114082004003900384640320301942c6000d203445600c100b00e0340c001d461049030181d01016055000032000324114200d2400a8002071400b60b66180c200041101c80400b00c5015540c902050280b55000c003410900e0031a12a0601c81d20701818611382c05032140e4401c43e40500c2d03944108505072450a404500003c01510468407941402340e10b00496140545203036425101d4854005042e030305407035446070620340051410b05e07a145a903040c4158880c00d42 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 762010503 1250 762009253 762009257
    0x5031b0907030b0904050a110607030c0b04140d120c1d04050619030303020d0b0a050307120606090e010b01020c01030b060406120e060702030307020d0e301b04050105040606140a 78
    0x1c5081d422544540e0700c1c1314411401100205440e40c507a05200d030401c3c200c09001409214104401e0010a030840d035940300c2942e22861124030f0f41d40320b00300b05c4209403a05000010500801400301300c42d03075001051010312401010100107841d4203402c00e9540e03e004a40f0400840c21107002c44480e4906030344410b5026601901c400d481005e40344004914080940040b404230781c1c080b07001412002c4511540030164419101074200301e0424000035074a108030300c180d0303410240292908040003030f01d0f08004010700c0706000600c11200c50101c524003070031001803864010710600b04c608c15950700c680100d000f01394025000754075050400c0800c56002c03107510100e0402d561100e01100310050200700032403040e042035010356142c2c1050301002741881400e20041040000c103841816241d524124000c402c200040000c2d280b40c0b0b03440150072100402c0d6a1680d1441c05160b022034000c8903040415074008208a42c2040960f0300c03842000122142800f5200000708801e20400140018500030041d25500c0c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 762011753 1250 762010503 762010511
    0x7230a0302061b1501080307240c030c080702011b03020a03020c0303010909020909010209090a05090a0b0108060910110304123609021e03061203030406051005031b090703 75
    0x80c0d0085030070342c0d200e1040d49070241101c800f00a01ca0b6410b01c00d950b0820521020614103516200c2207503564050004041c00840c803211112170180000700b0340840300000c044013400b6100c0f401802078002c1141086c1380000c07a600f6000503e0462041c03007416810401c00342c550400040014040300250081e1824506041e82085005c4414808101441c024064903030045040c0045206001142c0341c0a403443c1c51580c01401403802580d1841705040c0e100040480001e460782d500c1c42140d18045038110041e0111081c0d20000c6010003020400700d204001d007104032143e244415820100300da10340f40d11490030410500100d000541c1232040030b8003003001c0d881e102c150062041172110035003d20780a010700700703e04d41e41d0303001100c00290703203010040c40125811820300c0c0790f085d48400b0404402c1e4464503001000400142180e9038888030944030007540048035240d107020f02d0035400900007075030f100002480100c40000c441c5400220801052445104802c120652405005001001604060915480f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 762013003 1250 762011753 762011759
    0x415030b090a06050a0b030c180103031805180a0c0e010e0d02040e121c05010503061315060801020c0f010b1c060f180c0506091c05030c0f0601060f0207230a 69
    0x1030090f80e01a81d2681c10000300c0c6d403604000c0600c1d00200c00c0c1d078140241203928100064241c101100d074112505820450100c144103501000b96030155081603a000514a40860b61203805228a9205030108a01040192015a02502c000c0c5651f4072090020f4000c042c49203060500f9415002c403584054030100e00000010781590501806080c202488032022903c400907441d01d00c40700415401c1000100020b504100119840748401000111001d01e006000d004100c2e00e168401c404400006081007c85d4564400c9400f0398401100341f46240304144003014000c01c18440d5206109000304001401003411005100480044606941c0c096a400d92017900c04030078006c41d5840c1d000b01850030b2400d0300c1441d00002200380c54000a00803c0e043c800d40354a0349034141c196002e2008080070b001c1d2141c80d0b1034914510b20485008090f14068041d0200c44200000740942c180da51a46604407003801e041c00499496000b071003800c40d0460140346141110660b500c4401454602130584035121740c0f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 762014253 1250 762013003 762013013
    0x6041811130518060c04060906030911030d02010213080303060f0118270c0906020606040b0a03050d1e171801092f03032a071e140415030b090a 63
    0x50b0032039802c00d03420b004002d00e0404074021320200d540428011540d41c10142460401055052103025003418556620024814040c19203050940480028116132a00c4003400000f40030b9001992200e000080d005801716580b2008401d4030b11a0f9070250051951000f078900454540ca08045050070b16070325a88003003110340c000e101c203959160741c00c3e25400034880034444102c1182c5003c81010100f002601e01030140550104015030850b004450110300d492032200000c02e0614a540001e0903482840380c500041b0360450172b414040b010000105c075071810f184006540441e07848a140d0000d48a4400150103101102e4500444c8461200006244219952603a8002c600c282150341d4503000180c1e020112445c100c0f034400540e50aa01843c18010110000071800250680d541e66019031003503149448007003007140200408840b8240640e101222440c502a41158003880d0700c0d41c02020501407150600780640286d01d004e105c3c00080c010320f5621200d141c120050301c40d803c41d0041d00f1208001c50 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 762015503 1250 762014253 762014261
    0x61c180b0907050117060f150c0f0a0302010b09040b19020d0f0f0606030e030906030702010b09010f0503120a0c0f0309081609050106110d08190207030c02090604181113 74
    0x1140581c01402c0860410001510a01881c1034406041204204002e982c0d20350100d0307458039a070169220b403070307400c01c02e0700341c00ca24006c42c005212544030319010701c001e4140020300c0000031070098008106070413040c41801415102220058440358400300803d000302c6410b80140ca4018181200604080003210400292000c807070b190104e80f0b4460201d203020206912425005055030300342000705c0c445c01c1d800d440c4c4900408a04620500c004000107511070300039003003022104c5000300f4004003903850b0340200c40d12445500444c0d0007407151103000c0488162580445040301207035294000400c0c000d070b0700c103419107054400031400c20600500001d507002c010041c03010404c2e0800b62450a40f4100400780044840580c40380c1c04010b0400480003070410042282c0c1c40107034440c07401c5100342d03450520007043c554103100c41c418110301c00100368003450b0b4040008646544200c42c4600070341c9440c0d0410043d5244040c15034850401c030300d0300c0800a1042198200e40c1d09010708129644202100071608131 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 762016753 1250 762015503 762015511
    0x5130b030601091514030a02090904141203010f03020d02152a0a0209060d060e1911030111040b091c0b01030c0b0a0905090430020c061c180b 62
    0x820404418000c60b5a00608444081d0001041070300c00a641d02e0801045282c2083c003660019000202184070b040f003a8049411420000d40902a03504081c07600001e0003d0f01081c00d4954018451480c9501c410082224100e1f05901c41c0c3d2844c60303046400b00440304801120899101e0106c0240090b10b141100103080000040c07200420041064008600c0015004200c80c0c00c076041a02580f00583d101c0941d9900000180e82c0d0340f01406591802c000100610030100d220b80c810b12225881c240294130405c0c50240c80341c06500608a0740200341820f80c1c143ea4a6109844414041406110140c0d00030f0034010345c0c01014011004003417034091141c540c0c092029500000d19030010300c00d0000d41400000180382c814401c0d49403480505c002811074205002c1c0a1040d43d2880210701400b070100d05032500c403211000e18074200c2c400c2900c985102401c01e10b104001d40120000b404e0140ba0a8040d1070003440c009510240040b43e5901103c000c00e0b0408d10a9000c00e0941955401700d00b100302520b2003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 762018003 1250 762016753 762016769
    0x5060106030c0e0102011829040b071b02030d0305071815030605060f0d020a031b020c0108060a030308160903150519050c1602060d092301090803160513 67
    0xc1c82c415042d009120f9142004000e05581c10071002c4020355080340100312001c0e1b00800784282c12410b88901c480b400013052074444055110105010901c684c4100c824000e00d140d403111207502c41c0a020810a6003982d581c0694181c0000c81c0790b942c0d41c0d000f0341003181d0005e1b491a0403000c8200aa0f0001443d2045410400070703038018050050070280c040c4124000b50034211091b504164503810741d0b01840c40344824584920b80c0100d0902c40b1176009420107082000d0701d6013064141494400c0c020359403501140c0041c0095194030220b40c3c0d0307040482d4000180ca0705542d40c0748450791007030050229100c0c5030721400d08000341c08000001080603038046440c00a1030740c8010950b8208908968100e480e02412181c1040c81c060600c00381810b20710480b49541c800c4000044800114000511903004080030901100d0610480c542040040822490105c0146848511410102d0161401c8510b9850001c100c1c01007040441e04843c0542c4424440124a03e4451f103045146c80307221130344050f15440240 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 762019253 1250 762018003 762018011
    0x405090d031d19021905090a020706090b0a020d06170c04020c1c09090e01020414090a0b130e07090b03031b0c0d060606030e151504020c0d080405150402010903140a0506010603 77
    0x314505010840c1c8041501c041c817003401070600c070000d00c80500250011615a900007a41d80410410782c0091226940010f03501909150558220380654030030003038180707124507121021864161404984e1443e4040318010001d03225050b050100039404021000b195220710390101520450441440021007029035800c003205180400c00019074259031000361083c0d0040c8024081c0d040080300e8140d400318102c8a1003c5074a5090b004401003514012154100c041070f140194500d003c0e4000d80070042c1c00c2c000b100e8540e55541c02840840b0b04140c411a0305400403c00f0440c520341c2140c000d0a80340c1c034902510414100700700000e00300140390008903903042d10342c20100f0060b909440390005d000007460160400484a0f005808e044100401c403400680043d5540a0b2a48941c0d040e00c20403103802c01158809000d0300d5000c1c2c50213104071000c40e81446111500c0301030070100c00100f80541e40c1a116a20070700e0a603900c025004050300c80ba09480d224100100020070003c10029000382001d4900003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 762020503 1250 762019253 762019303
    0x180f050313060e06030c030c2710090b0d0209011b030e1c0201091703040801092a0b03041e05010218030c060c0606040506042d0b0405090d031d 63
    0x54100495480202807245030311601d902a2030700b10440e40d000c4001903089542c2d40c0c5000401140b801600d800c21341d8511100300c241d0311101250400c058840082b16442108040c0e01c50844400ca120300030002225420722100c2c4140074103802410300400141081850405900701d030010240301404203900280c45074028401e01c0c146200f0800c1300c507003402c21720071201140d500042e01c92003075803090440101c02600c40f4801c4803002d02c02e4401410014000340003190450901000b510382c02c00708690304c002100041158441505400402c4821103402241159215210600c21000d1001c0c02c41510164a518000081c820320003894030b0020005400e0303100380768109240c64013041c4001b041c003550302000b80109822000564552000c5c0458001c203466449101040141c01240303400105229a001c54010004003808c00503010848030380200241c213903101c00c00064400c1510385405a4000180e0446040c0c4203070014907817800100b8400b114400ca00303540320314021035082607007003c0e85001458 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 762021753 1250 762020503 762020527
    0xa0c060501050904050a151503030c0b06010e0102071707050a031401060b0c15090f03070c14040c091e0807080a021206010e0601180801050c09030f0f0709180f0503 72
    0x15400342c00291411481c03483c1580c2ca81d666010744031005040c1c4081e89961012001e060b8000740b900511040303a16228a43e01d160117440e1a95940c0b0032103001007100002400355100e503c8441c1503510580c001c01d9800d02d0310325481520011802010203d0144100200302ca44800895070001d61203220551051078200803518211600350b006070200b0722040055590308680040c1a19040007094010040c944540c12a14980203501800e21480d00011404409200344801044112001f40d01c03000d01a14410007000229100c091918000c66143d6400740a64404400c0342542c505440041000250b00d0714002d41c5013506a9120340d080303034070941c0401c003181451004d0b89240c0b1017100060030f855061030b4019040c01d0005120604007e03010383d40c0400908241c41c010020171194008001e03c1c200701a01b030f42e41c0d901000150b8080e00c9011400342841c0c00c0042d6000c00405001e010b0003805080c4a84800500034444590350301c00c01e002d04006c003091251180c218032500c208000c1d0b07a5080c22900c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 762023003 1250 762021753 762021761
    0x7180609060e040b01080c0d0221010f0602120a1b0f060519020306030304060f02100510030b070c0507090c02030417010917071101081801090c0501091e180603080a0c06 74
    0x2c0180214188044900d599030000c19031500020f41d4481c854036a00784101540081c081c0c11a46000300040b0760380c00482040c0320b061030741664940182c0e1081700c0c0d140d000c00d903600c40c1e941580115042d4100601c039a00ca21500e5202c03612120803a80e0000d0f100c02e81c640c4c0e00d05094125007030315919503c00a01664004206800f1001e0409050560841c9043d60010b6124000c0d4803c582c01e00000c83d0302503001a1003404001195044107604010707608020a43c2d91560b00300e0b01044454144c0c0c4004202c10f14041c0c1d001c8240385511000404a00f41805400c0000d444244816000c0d840144400706840607160941c454111785200006060b05080c10f0001c4c11129070201080303c2c200421a4030081a141190110403140a013029202074442c8405510f5030048a2045041da5103000148400c004119102100700d40d02680e03841e52907520340d20381c070803050740034584602601c0c42e810701003018140d40a2204030880690800081c03440d0303031703444880ca9903003c85804000116a140c1001c108100b81c41 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 762024253 1250 762023003 762023027
    0x2312100e041b08060a1e0603080d0203090114010806040b07171501120908090307061827090602091008010f030f02120102030106050318010911011805060f0903010605030c15030718060906 82
    0x80c240941f0b482c1d5180c3c0d01681c4030381c13601400380c96000000213000740000d4001c0702e0801e1809220701104e60b540c10015403a084203590807a040075001010884003807260b0300601c6522030701da403544625110764603904800c0440c400c4003414040c41504100340d1002d03602c10b42400d40d000740652039031540820101410003841e50016814080c030b40303010a8040c030456000ca0140c83c10580102c07030440800c2d1081c0100303e0307500d200d8415942052000420071040d90007804502c4003d4403130301140f014191050703501503801d020b030041c4004544001c1000c961503181c1180300600107410031480f803410442c4682a688240c1000c40072400003c1405a040401482181d5440300c150081208034078994901c10380135003036480305040001e084100c2d000d50190102610080c4001082240e80d002c41e40001201500600c1c1124480d501e00b400005150030301240384505408014680c20a50036a030700440c007590001b500b92810441c409003103003480180303c40f580e00034280d65158410520700c0c0480050050441396 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 762025503 1250 762024253 762024311
    0x606071722050a0f0b030901060807060f0219022209021309030206092404031707030c03060803070f0204020714151b09090c0a2312100e041b08060a 65
    0x140f0030030000b89100b20710380a40354884410f44e92626004060b60140c030381c50f001210103005101d00041c4260b000500000c40d01c2544d000e8aa070031003100d09036121003181040180d041856400f07016201c000f40d409194041c08625000507400c1c6164003c220060201701c0e01c0241c0da503441c4180c400303241c2c041259a40c04210000141940c80c645440045401d00c00114165040712210116007058002c035000802800c1e508520703040d03442e0100004011f40f103140390032408203191090102e40755a0210031a0030040d0800700c024100c0d4403650138403000398000c140599020112540c8050000c4061103000352120600c00300004a00f401c24001c581000b115041c0c00c40d00c141000500200d40310415015404051004102c0e140c0650050076280000541e0b4001d581e08086501e000c82442800050b04800400c01268600d659418180007103405041c0a520a80d8911100141c00a20741d1a800380031041d140107444a1030395180301035407400009440d0b10080a48600c9460300d400315030b02c004c6180300092 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 762026753 1250 762025503 762025519
    0x109030b010b070605162a02060a020106150201063804030b0f1501080609040204020c1005010306200f090301021e190e062a030708070501050705070209060607172205 73
    0x25850140001c8181758841f0341d141d48131000070601c0c3c2054118410b5194000d025070303075035414112009008007200d0141d110750003c01c1000c072a0307440c03051250b04203680d0303110701e52000c0390350020342d4401d45441c0a1070b10f0403599224030740c03001400d1017101410065214031040c48160500150410350f03490018100401d25014100c0501c00ea80e1215146810000c00e031410708413070b101e6001180c040d1007000c1a01403113105040c200b040a404541c03146048070f0103034a00300315200e4554040c50083c0541d42c8242400001403260500d5600300c18018801050001d000510301403602c04c02c010f8030307026141d000c1c4081e04042444500b62130b50040f03039034039012140b5010074a40c0c6110001001800740300910b040c00c01140550185020200030369003004450340d402ca98543d4564584842076174000c200442d181c2d42010301241c126400b0341d050b40e2a40e82e00408041d000da41d50400d00625400100c0152420482d80a089440c030b081e120041004500d0014400d402245586890007020496030121b4099400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 762028003 1250 762026753 762026791
    0x603040b0a0506030a0c12020111010c0e06160f0807110f030714040906090804150e03031e16060516050306060a0e030a0b01060816030902030d0503060109030b010b070605 75
    0x203601942a40030440a40000303103a180d800102c0c0c030389007440d1401455200e032544c003c10646180d41100341036600c01d13071700d0203460368950b40000d09851608110f00080703040501c1d00181c61a005020300301d10300b2801e1003480b20300c0b9162190041810718a05c16600483c000441d00f0500c40c0c4503007501e8550900355084a00c03d140b01c1c02103076031071034940300e5002c441c0c191401428080e607a540003100340075000a0207000b44035203400d250681354490711400162440442c084140da03400303403181d5a0403020090186003031001c3c091501e03e40c9070380101d018404450402400011480118100b03000c0b500511001416143c000602810301e082410340c40f050281c2441045039070342c0e400f4200c68040c070b800d10306a003009100c1c0000c246044d81d0401c00600e514000000445d0f12a40000c0391032046d48580314400494240703050070740441e51480c40103034040e000158403a2146020320000d40d00f01406141441801e907407510f49060401d420f800c004290240014001d05001407805910b411600c400c1d03802c40e040c48 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 762029253 1250 762028003 762028013
    0x3070e0402130e070e091008010b1002070b1b03030f0405071d150612041101031b020307020114040807060c0b010609051e03011e020a030e120a0e0303040f23060304 72
    0x8030751040680310080c0c2030010701000c2c450704c121403a4620140a00c00c40b0b00b00347c41000203040d041c1c010303594990719003000b1007418a0080804907404406801405001d42040380c0400c1c545c0c07080c52142c0100b41c401142d40121103040009521401c414110401141480c4c03910351b0610001c0e62102500d99a81040c03100f2094400b41680d801c4070420040003c9d140c0c6490114440e4011071000003031601c880c804110a02c103220543d5001c044007640c3c200300354120106074142c80440c18420303400682c0148104801540920f1000040c1300010041c0b40c00c0c541e89603245460a661500400700042d50b4182501c00c00c0110782ca2103000d0720762810304001060170f02e00420701005180d034291541d401030700f0000c8880c3c0c40a511640c081c00e116680e000d030103080a08148080e60060460600080c03030543c410b00c11b450042950b580c00c0b80c400928070b14240f40c4140858940071f07000180c0d9030500082000185000b42c016034800146101260942c0c100305005502405c56030290845005000030410800001c07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 762030503 1250 762029253 762029287
    0x403050642220b0306010f1d1504020c0d12020310030b2e06022a1309021e131b0302071403131508102114160512060105040903021c030203070e0402 65
    0xf0540a511004580c1d07202c9000c0500e203500740d0912b81161001580c2c0c9503503200410546018582600c407070940341410b42e1003a04170304c811140701040ca02e150b9000e00c002078802c44003681200e00039440341d100f0301c0c4035034980b03140f0b0992841102000c2c0c1241d10030000e6940502007206000e06188201e901801e860780d00100b10b0344201071980c4030740e80d002c40c51280020154400036071a1b4010f010990303020b6000c001d59251150307004140d407088401d00854644041e090048200116550a203400912004842a0069001b14a04883c1c245038083d050010f404104050304083d445800319050f002c0c5462000c100d60b00c0e0302480c000400140204110b09441e42d03034244030480702000c030b8505c1c054030307000c503100c044d004a031500420064006168041c3c120780081d2002000c3c400c8440710340c500e0f07602c408000340c2584903800c8920325044480100900c0ca8a60b20171102203011340141d49103400441556201c510502400740301003540401800b1400d03501086010000000f40c404620340351003109100150 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 762031753 1250 762030503 762030539
    0x41a09010b151908191806060504050403020d030506060702041e0b09040c030f060b100306050a1d010902030703020c0d02161208070b06060f0403050642220b0306010f 73
    0x1c00848404171314401300e580300803a5100803c40040081124203680c50322407044912090f10742c20300300040450545040c0c405c4600940e41034006086c158601a03056010f000020402c651043c0c05016050158a80740600c9410042e1300c8910007101c00c00f0318101d812140c0100350300740035903e01d000b0003001940802c1c3c04070541c1c0e082000001e1080c2c240c585000500242c501050300010014404c407103007509504414255181203c0c140d01e0311b519140611080e9003002100b68880300d58400400150302e0641c0210341101051138094507041110648503e482c09440c0c1540050740545829013100d02882201c00251007032100da4811030000d038499540d035009641c0301a00002d00000840c5c450740d42d040071900c290341c04000a48c0c03503a60386d00b082902d030081160800d042e1040c00c40046440c60a2076191001015140b5081c020441da218428a0070382591404680040300703240c0601500c0e01c80c54205903820178540c004145640c44400f80f505180d03060b48842044186003230b00b0302a1109040c115801 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 762033003 1250 762031753 762031757
    0x10b010c170403061a010909151a130f0e090105060d060203130506161205130f060f02180f0102010c02102c010b1507120305041a09010b1519 62
    0x307824050403050214412548000c0410789800001a01c503509090b0b0318500c00400d0700c0310002a507440c2200c0c3c1c280c501c440e002d0314880b020701d4828030401000c01c1c4844c081c17890f00710b80d09060104000f000204850f00c0d40005501d081d05d80410021100001505075024000030020301507400e20703002048490000810003440c50b80c0200c00200c80c82c0e04102c00c4008150010304030345041c10001d60640030611856500c400148400326101350a400c64020140102403100d01d41504008035102d50141503900ea5007105c0032a10b541107030b000480203001401183c0d680c001403943c41400070040001407018024031320306590401a1041ea074540104400901d42003040340820022140c42080c00c0256002e01110300f41140c407034070004101d40c150b10590f840141a5900d6801c95800c080051030381c0103481004088015800800000c68800e07002960001e11401101c03156142c594040c984a80c1c0c100d9016407da0340d80c000840c0703d480e01a40302075520040011092810446040056080e6054080c0d02d00f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 762034253 1250 762033003 762033023
    0x6070206160e130b180a1512050c400615121503060f02092e23180a091103160c0507030b011d09100b010905041509050108010b010c 58
    0x9500e1700c94002503c0d00703c040351039034201e6103450403e040c0208034005119091b80440c060124940107912420414240c02c4401420100000c4041004070003002c00a0641090641400001d000c41104c1008022514140f512541000303007075258100c50003580412130042c030381200000c01a400221000b07512064a0300806c05800c603403240f8040014590004007128500042510160541e41c0030f014160000c0315000a120410444640c0711201003601500e4581000d01c25000a405510a01d10307035607001009600c0710820446880854000b050101412064070381c6512142c90512940b2004d4508000100403038080c8815008088c00001d1408039200c01c1102240c0707a660003885601c032090b5201342211030281d01c030714160141074000e02c18510381007034a84001041c1060840700a01ca007001c40010840314880d603101101805a500b40d440c18030080001c042416140c0b4000d020450720401c0a4898561808a80004640307059000c0d1810b0307403600300080807907030380282e1407980b064001100e10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 762035503 1250 762034253 762034271
    0x51e040f0201082809031e030b12010b181b0d140901150b090d0c120b06090f1f030204020d0c02160605041a1c1409012a05040806070206160e13 63
    0x2a401c08010040c0c1f42d1004017124000507600d605400c0504210130540d40c84030198494056a426242c83c070b071481350b0048010041019604c12483c505601c104408040082d0584074000c950b0231381d120b610610340c0d05031030304800d6a1820098039140d0704601d6480c001c00844002207103a201e5400d4501503146d140da0009800c08650360707210400c2107c16045030307640303100c550344802e03105600400403030450700c2c010201e000030f001c0e03c5e01c240b10340c1c8079840300400c1e01341320364400d461b13558801005c21403100d00c50001c1d02c01101527102da01c09400b01040030180000c3d0440b000310081e1403ca032500d440703903407410120002d003c101c2c2d11009550071110030003030841030015410781040c0d003402102c910304c02030000300303c042e00e88000070381021001c2e00c4280a100c441da21103154031400e03500b40d0201c40075418403545904003042515110f01c0c01c1500a8034146043c00d8039911300a05000c425107001d00140e1003142440070ba1041d404d0710450300d42c4241000384507010032138080b98414003401101140181d03541449 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 762036753 1250 762035503 762035507
    0x150a050f09030610061116030215220501110a021003020309030f0c01090201120e0d0509190306050907050603040c051c020424080c030709051e040f020108280903 71
    0x785101e084000e060380c02030f2078955a1041650b455114490019902a400032080d64002c20b501d1b600b010703072016410303c107401c6800784200407500104580400350100b103d50703201e105203002c4c88503a140980080c01d0380e030b10b0603000505070081a1a9841d480d0403404080300142e6581c80c1000146c0c449090141c0c60b542ca0101060860007209500408003100250800d0f075036206502140c9075500c03d80311900b280002c800744500f1240240a010f00981c00144810802ca016201424000e00000d0034205a00d40e4020280c600010b568000c0303404039200c00500010110500c1232001400c0c00740ca0040c114075154444002140c1c0c24407a280c02170000803605199240e9081d0012100c68003d03109100c0120038a10700c0d1103810b040b60f81c4240c517203901e5001044a401c040303080d150708000203004000e040e0401450100422004d40005c2c1c031030281a042841521444841d54861070107a0450300c00d480c4103000140004400418014101c0c03810741daa522016590450021124000403001520510915003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 762038003 1250 762036753 762036757
    0xc0504060f181d09073f0c08031908060d060504050c04021c0c2604020a09140702010b030118080f0706110a02190c0b3a0b03010504021005070c0308030f15150a050f 72
    0x4050a02c81d0803480c0484d00701000030080c0402442b500d5110000110018120364032181910b0603640100c20303126100220300c10b6002250005c4c0075605846071492400001000c9034030180004c8c1114000c80072500e030b055407078400c1680c40009420401d4100d41485c61641d1440400d0f241c0200481c0b03d040410f06640712107000a01a000e810010845038807440700545040780102c81074001507080c10910401e90030103019030f0b0310040e5001d40b00a0249100e940709041500000c0e0509400078043c0171903c04a00503008541a0b900c4c1e0001003580d038146104001c2c14881000c4950761507503031841c2c0020005210380c0c2d9007001c03103a1200d6050345440d54a107040c01d070742100300c50807580b040c6003100c0c03950b09885d00380204001d80d40e048801c0002c880c1142c02e15090302d900b210065480301034400d004403014040c0d03000b0300d03020748186143d440b000e07141c0e500c03e0b00703680080d500d8400311480d03c8208104010800320004c69071004561548400b803200290340e6591140b01401d108011001c43c01021046034101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 762039253 1250 762038003 762038129
    0x30209031501140a0e1b0f0a050301061209081b0307062a020a1106071e0605240f132705010c0504060f181d0907 50
    0x3080c0d480c01c485560300c0450418003800381a65403000c00f207200c5900d00d4440c00340d80c11190340e503101c00880d65130064450b0065054030410703015a68100220400304010030005c09000000e920341c00c0e00c03541016001403480e031100c2d1500c1441490310349441d020030741034401c3e00c0072038240120b40c00c00110740410342804d5005008000f8001c5042030302004d051840205240e005100c002030841011500e04012a69000d2515000d050700695582504403801c100c4003c00410380070359030a40103201d05481110305401c01d4030b0705071805581c0e9001d0050002000382907280d12020154610b01030111500020064001030440078030511494643c2407000e00590002c00920303540000e05450700c130306038040111030381d04d44004a4103075103403c0701c40c041c003401030f41a101078500303d51751105d220b56004410384600400c120300502030130781d40d1000244114205000069180404000100c5042c1a6022031500640340c104145007402601d405019203005042241e0391000c410394001c070b80304c0320a03d0481d0216121 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 762040503 1250 762039253 762039259
    0x90f0e0a29040513081204030f0f0509040e0708030301081606050906120721020903010b03151b07170c1006081906060f081b010e010801030311100c0306091401120b07030209 76
    0xb10302c10740501d030b0f46c4545620403402134035441c03611a00c2d0201110b202c4120358070100805c800b80881801821709a101080741c0c0e1002044886141e200d26255155030401d0340601048d60024502110b2028100500001080e00342401030502c280d04d0005070740d070b008808646044d034440500040c1d20f60b00c01c025016180d0f4101101034850b8129652030300282d0301c01c005240c0070b58240b240e50b4200b8100002d44491b030101c0045540c1194841e4645480346500c0c100b20400c41c11340a22224001c0344070559021800c000d845000707981c0c0d44481c405039007051310b1498a018840d14060041110b4903010652403000c2c01940d801c4402404075140a50041c060703a00200c00e48483c104012500c101c1c0000e2010314440030b0021510900c40550044070340c00e09090021740002d07024401040064092100f07121031349807400030f80d02100c0a24855800b2600c4407200d010029031100c00402c43d40e91107118000e900c1520301e80031005503051a10000385844000002031810207410b000812141c4030342d0540d2a160303002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 762041753 1250 762040503 762040507
    0x30c031b05070302160803070201050d090804060801030b070f020714010210090b07140403170313050d0e040c230a050c010c03020306120a03020d050a090f0e0a2904051308 75
    0xd24001880c1d50081036003203000d84151002d0006008003481c4280c2214036103001185400c3d23485d401180c040d0050302c0100b00785a1542d240e0400903043c1c00141025020700da0b100805c940c0756080002501d00040e02540521051a120651041e17010420005a1f01d1440d082403850034000c004070710b0b00e402a20a04603041c900381e1504100010050242c0c003442d801d0b560307040d91018060a5030800d11030392000501e040034034403100040203104400741d64002682e8001d0090001c040c1c481d1b50070040b014020030300040044c001408240307814402d2100704c0c0168500903110510060301185143c02d481c6640d503204501241200c4150702c81d20881c4d200c40200d2000340700d0000d02078000f402035082030314a680f14590280342c0c01842640060f87d4688280c169001702405101d500c0156415803000104400b08440c004000c034400c413111158200501d43c5105d031103407601e40625898122080742c3c40948852514403440d85420009040300c820a007400c860000701611400c90741d0381020000c940003450301c280 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 762043003 1250 762041753 762041801
    0x1e0402030f0702010b031903031109040507080f0c0a0212090409080c0105010f05040c0f081b071a06030607080403050a020c0907020a170301051309060b04110408010e0319030c03 78
    0x7200400900400c8160000c1c000020601c0c00c1586031080c0880600f006020522080c011a100f50001c1601032000c8000c85d15242940001c5810b5440c1141c801c400300f0000c80511481803800300d0000d03408000002c0e101d08189000c00000c0d00c4601019190a04140101c1c0503405a60350f50301201449502002d0309558041c4c40100c00e020300800d03c200c4120321740c0c8a40004880c1040d0207080100307001c1742c1d2100402c403908070054600341009030007c10b17080740403011400d041100318001c114640c064000c140610018241c0b03200e030003900500c401e0090700f00074140001240c009040e00e4100703a041c2401e580f5a600c44008074540300c2c1e103000e040d03400500c14090111a0350003142400c00c9038051844400010501c0c0051a1140300a00c031709a04405150b40302c2c10780000c0d076030290208074031407040401c41222600000b0181e5142000c20740e503000300058108442c0c002441200c40742e050705030155041c44031420151090891449190007803544070024202e80c684a0350142100140d003007504400b02c41c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 762044253 1250 762043003 762043021
    0x307050d080d181707170a020a050f010b0418030806060a0c0515090d080c031801060306050a1d0a0f062304030504150302130b16240b04050609061e040203 68
    0x20a55a05441e9013407409242c440c0310903114212420705030401c4561120b4622402800300e507602c14129482180a00381402001070303003c0c016000c0d40034100d4000f06840300c0380401c101c215a01c0054040207000000080c80019400902c0d0340c1d44900110b5159840e07040305401950369000c0071070002c080d03002d0303400700c03c2205604110071801040d040381155446000c01c041500c5202080e00c074415110780510018500c0300c10907a49208500c41303a0f001003005e55481d03079003800303585090f943c0e00350403034849904500c03a0042040b08003600d007118009000e4003020303444010140403040d402610240d124403d070000d003110b0b1254000d00554180040704540340c02d0400420540050007100e04104948c110244154441e0003610003040499080564071361030021709140d16400210101c4800c443d10300c05d28049845064130031024a0380300808100e00c81d07011600012107065502d424412031400051014513124040919441041603482c08441e100c2c03401502441c80c41c03e04d0540d4004c0c000000c010201c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 762045503 1250 762044253 762044291
    0x10b030f0a0b010801030b270303150d0b1308040308120a050a09020307121112010b090112210306080a0813080309031506010e040f0507021002090307050d080d 70
    0x1032854440e1035600e9920300141512650102140054098401480402d0015000036013040e0020360b407581d4149a10a00210340c0c8500045951f6904040108800b140301d46200c0401641c00311880e80101d40070b80e580d201d03c40c1010f0300030320343d48161021240801994001b110080c40e0009252603d4150011140c1802c580450b40d80d100c1301e0504020070030300200342c0651441c55500402400b110303400d03e00090300132641c60380c05940700da0b8400070400c03d5071140145081c3c6a50780d0800400c50300307580070501c06d011106078005180d01c0300d08110803001c0345405601b0030091600b1005c80419441d008411070142181da0080540b6014201c031600030054200010b1210b0300c80c20031003071031060707035203c0103030320790007111103a640642201d2003025106110740c1301e00354800c405051141903456103402003000c40e0707120003d40c514296200c0a000c2c400da01041620f09008130000c05628000d107450210307803501080d10500d070243d002000c14a081010701030655411024151080044890159500c4244 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 762046753 1250 762045503 762045511
    0x2060c16050a0c180b030d0e06031f120b07080c0406031d0706030e01180203151f12060e0a0305160206040513051006051630052a070302010e06040905010b03 69
    0x260f07240c0805d0344c2180c1004143c00e40049070a0721007400a41011080c0815648002c20288481d45010320507681d4004041d501070240c490304e6070f00c0d40f9907500d03490f0030034036080040c2104c0c0c140708440c010018000c448008480a840440c03070003080d210701003502454402d106444440303080c0a500d80100d05a903040d4002c101200301d000c000d00041007541c8002e607050340f2903040030790181c1041010024034004010f0042d0040060803281b91003409600300010201002e40002c8020010310306038009100042c0608041030340c03800040d041c00700c41994098041c1c131500024265568003402024159034400060314000c21014106c0401895203211081c0207140c1111010882c0d20b20503400314640d4811415524185074440110b03403100071507254030301d00d9200b5040700c103a42c0030300c131038010000b08440f00301c0c00400506455450300c0307040211245925200d0801062070103c5540c0150b5505100000c094044039020f0800264044500740400c450740b1440d001a84401d05090000522103030300001075103d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 762048003 1250 762046753 762046799
    0x30306040f09080a0503041a0c0304020916020a02090901060b04120b0c120a090f2423190e0f0c030c0906030a02130f0c1e02060c16050a0c 61
    0x1c000c0301000c990300b02c2d04141e8014089203824081460501d0284004580181c0243c0c03a804003517121448488100344100e0704100d0000001c4240402c40c10304003800c0703422211050708440d00400a240c000c0d905e009448010b40300e000d5510224060340c00c290b10a20140c00309a490594954460000d9048411603200441d040c1d03100c03070006054200064103682c0c1101104048405984400540b10040e150007103040d6801410b1003041d0b00094090001c1412444901440e007008175410000d40c0100c841e81c4204140040810310051a811220f0107070f035a004070284001044003580c40206402401e442e0a451540d03ca200c2d030030b031922400080c1ca8252080101e00b1140c40400107802d0018090080d0b0f901034142d401020108010300c0c0064481103030000c1c00710002828404076840c0b4040c1d0b0b0361050808085480c135000074003469140c6c400c1d03c404900c1c900082040341414060040d10b407045221a06083c0308440500080103801e021500d0450b07046540d40c01200c2c1c0b40c0709510f00e001e000c0c0c0f0000c82 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 762049253 1250 762048003 762048011
    0xe0d030e090c0306090a11130303080603070510050a1b0803100807121e02031002030c040302030c040207050303041e0203010f060e0702010b0102030412022214180c0d06020c06070203030604 83
    0x1074400c2e02e00f1030703101d1040948000219141d02e2083c00c00780400812001c203200040c05a10058a80041440c0080d40030384d90344a02401c0170740516003003404a0704172078040d0364074800141d0565081002c0715400c0d00ea600e040c40d40036803010110300d140222a400180031060000910100da110759690805a40460007500c01d420f0396650303a0300c2452040e11000b40f003224008060005c0480002d4001c60190002c0c060340c11022010400304200e83c0100c880e801d4200d0082001d1040d42810415900b201c8002d4504524000403078842c01d5032400014001024034504c0502c01c0d12000503005407a40f010344c0900240b040010411140c0050100c1d40661800c009038840080c6000d44140642290854180c02840c90542051164982c1180c0b016090342c0029581d5686072a81070b8081a0240740a01d2103000101222500180c84119a028002a5140a181c0c2c0c09544000c408940c0f0354502c0c01c200e40d0300501100514011000e405405401c0c1d0080c0110010407072555004801984105401c036401c01c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 762050359 1106 762049253 762049261
    0x925030e0c1f030b0105070b04020d03020a1a0703050f19020307050906180a0b03150f010c1208043806040920041401061205070e0d030e09 61
    0x120620000c5000c00b8450f0705203e02e0640f8038007440d101c1c0c681803060b11a420302c0b8030043c01c041e1148100d07024031800c16008200c140001c0340d04c100401404000780345084d00b5100102c03108000720342490300007025a030b80521000d228503114070b150804200c6407040c0d1802508001c1203941480401c1001c1121a82c03148007a0040109026011100c054a80c0c14091080000c2e400010001400e00c28030040f072414001250300303010241c4644010189280040303d188500380000740041348401003180b42e080d44440018421401540c0940700409406401ca403682d031304500740c060b04802034140d4010040641959038011078000d00100e4103480e240c80344448800071080400f6889241104201141481c0c0640b42e003910000f1444915580350407009804012000c1c1e030400c40941d51000102c03014000c074607200882c01c0c06060385020340c00b00d280c06072025880c3c041c10741c070a5094100003 = true := by decide +kernel

theorem cover : BRFrame.Cov 761870503 762050359 := by
  have h0 := BRFrame.cov_init 761870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 761870503 ≤ n) (h2 : n < 762050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
