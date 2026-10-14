-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1457
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:05:03.323202+00:00
-- url     : https://prove2.me/submissions/d5ad115f-3c54-41ed-be85-8fb1ffd9e2a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 261870503 ≤ n < 262050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 261871753 1250 261870503 261870527
    0x1b11030d0b1503010b0a090510050717191e020c0d0b04060b040e07050f04150b0309010609020a0807020d0f1b02030a05010e0609100506090105040221040311010f15030b07 75
    0x2c0e07040040081074406180024000e2009607aa500602d1034455007405280e400f0007181d100804d80c244001c4c4001410050440180000720282c0e605049500703c900b4125122410302d00701103449041c040001c0541100c004502c00040c0c00100011200350300803464070b14134440060600500f80d0041010480b10342c00840c0e644100404c103010040a140ba00c80d00c0380d031315106040c49600788480310081c17414070340288a07103040712010010b145803a140c2c1c003155a0340001c1001d85195a1094041141e40c03680c0b019140064841c0e40b200c065180c0848040c2c82c003101c080d912000c0c040148041051203600c4103000e40c4d038070250660142d440d2002e1011a01c0c00d00384240c020310075400c064102c10300d42400512140702c1c40c240300440d4800c0036245007903c110380084d1855600000f201300188100c0c1041e030002d014401d040d030595440403101494804030b4200564049001451007003c0f40b00c40703c001d0140524850358840304000c459202c151400c0c8140051000500d0031030405d0000c0d898034001c5c2c6001c100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 261873003 1250 261871753 261871789
    0x31602101427030702091b04080d090b030f010b18060c030304111005160f230106081b0f040b10051c0e0318150d1b11030d0b 55
    0x34081e01107040111900102c0d246580b1940205205441d9000b220030100400c2c1c2210246152103842c1e028094080c40044c41102d00c039803407040c400343e04400100180001c02e044009000400401c1c00c0040c02040c2d5507001c801c1d2118140144003803070004c0800f15046070302c00304126076946078403041c00510a21010000c1e80c000d40205018060000110083d48610b101d44c488407405c00d128401c02c16002401a48030700010010b2007000074000e800007650705014050500b040e00a8003d50f1214640140001c600c181c91301d142260ba01c2c0340c0002d01480000d080c4560281003080b40d4119071110b020070a0320250320511001240036120740380c03036000703042c4410050030310040c04d06c91990107422a88115641c42401e00010b96102c8042c8840c8904042440d404003d18a4070100b9180e040070101c0480b09160300c440c1700301d10645550002402001c4084a402e004121000d41c0103c8000b035034003900030b500600032540c0c100c03480c07407101000b01d8000103040342e4001021851780c404180e541580c0b04071100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 261874253 1250 261873003 261873011
    0x1605070510030501150201090302070b09060d05040807050d0e01020a1e0b01080304031106040501050d1505100e040f0501060507030f090503010606110606040c080105150706110a02150c03160210 85
    0x10310a5410707040241030764a808002910175442c0501203007290a0a040603005802c169024010008004000d2410820003400c0c0d5007050f00e881c0340a01103a5081d00c1c21128600005503200400c40140650041075403641400c00c66842c44d4400170f91138181a4000401070740703020500240420700c100e180c0c2d54003500040c21030f51070340c1c46003405981da038810301054071080103030b0192046510f0420200c400355141a0f40c4e4a0400c0321015404001e8001000344218075030100343c021903141c4031900c543d15490820ba4452003515680c2c005d200c11a00812030740078000703003040018080a0b8001040701c03051913152800c1842200345800450b0020000d400259065007411400520306601024044a407182c02043e05c0b85a1200e108010031241d1101c81200443c1c0308800401c407915084a40520000c1ca4006280c6007441c19502c0703c04880a0301c40c0b034800d51402081d0ba5140581c100502a2075045465051400703052442508445000c0144030003128990307109081c0d43e403882400003034021040c1c00401c0c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 261875503 1250 261874253 261874279
    0xa0c0219050c15030912090103090f080a030b06070f0f03050d0e070e011e0311041808030a0608071a090a081606031104031a0408040f0f061b0816050705 67
    0x80e458a0542080c1d83c03040004038000ca407030010843c02c0b80e028410120003065121040404d00360b0641100c03404c541859a10131658010542921a0b22062407081d108942d07144180240601107540c0104114080c0703105001120026500103040d202071034021120030030000d1305190840c1c15201d5005142c002d0750605d00e004184500000f425001d4481d060307041001e603a2107107514544401030181c8000700101c10b08080000c1001148403850201c000340020401440304040b00070341c1004804102c44100d400010171404e0a00c1c0e02c1444060005000501180c03071a0120452007011354070080000c0010001c1d0300b0007990b5400d20240014403024041c0da0194801d400303900b05559942c425000420308110004010411401c115800d899101c980c4a0b139402c1810f020b004842c6008104a40e110341c100070220340e2454000ca0100245000503071010300604102c001040380d1070812400320700c1d482c2500003600140c41201501c80c215548503140c0e40000c4103080c00ea141107510b9000c5904036443c034202c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 261876753 1250 261875503 261875513
    0x807050f210d030615030e0d1413170d080103020d0b090a020d11010305010602010509030f0705010605031f0b0402041206050703060504020d06230a1a0705030d0e06060a0506030a0c0219 81
    0xc104035059000380580c4d80c84110019407c0e038009036000c15164015540b00c80710300c1d01484250700d44007005d102c4107090030820080040d035103580c0c2d04101c05026001500390612a820840c1100040c5945020301440d495a80800ea0107126440010240702811b000540390720001c001d01e42c1c4d401d8008040211074180c80c00c25821401d0801111760010f407d140c004101107005000b2a4011b010f45401035141400703e40428032544c00c904000c68455484003800200d503601000442c1c0001d60003810a00000c0e4142040300403264000d0703005004900501040118040790048840c0207501300e8400300e61540c035008210000c0c80550031803644075102040e220813003892b5070700200c02e0301c01181b00c492410201c18803410140b01078000542d0b2200e8503d0051000f110030140c1e402000d8002d580c95410f1800ba82d8815040d60800a909400746a480d10070082110b400c00c006504210290360202c049400c140100f50f06102c0103084400198540d155032407000c0c401c1000c42500180140c0d41e61041d0700fa0310744 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 261878003 1250 261876753 261876761
    0x10c030903030e0703020907030e010207021905100216090c020109051506030709050c0702040c1110050f01140102070911040906170601080d0c02010822030f090807050f210d03 77
    0x15000280f400011180e1442c000a155041d42d400514041d650750b20b0500c09c4015000000802e4015502801007a0050300e64140d80325007000c0a041d040e400a003080c5c24803d1000320001035030210340c041c3c0b22910a4000c030610080981d4803120011071052030084082e4050304800764024214818040052072006680074544d000310360440c280c82945a680c190b00040d16020307907980032030b41010441e01005192507809401d00718464104424043c0458440354180002c40c01f8108025403507504210b00140703401070460140c65514421200080d049000035504d8204e8001c000070303503a9500662020089440a460080982c00307024000b007a29081030003400101044408294480d80b400405d5503800800c00035042c0c0829a0b03070500182254004454445002d401d28410f40341ca402c051456028003240030078414042e4440c80c40303407540807500030301d0314130725501c00032407a000680240580d50702d0b402e10490300c15044803100040c0003444010000c901011400044034403411141503021031301500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 261879253 1250 261878003 261878021
    0x31501021b09180d03090c0902040f0e1308070f05060a052e050d0305120601020303010513020703050d09030e030705030601050d0303020c1c0807020c090c070f110406171c05120403050c010c03 84
    0x91586548d94a0010005a004500a42c240100c0381c4409000d1a806807160a600c241c81e8103851a507503546403075503407032544641c5043d14500810503141c4144070042102d02c1d0801484a010041450704e0a420092103402c20101c4258007509130707540030081001080003001d03110080070300050400500d009030450b4040340c00152034840307031000120158000301c00d0b40d04a5030088e0140001580c0217141000135400b50030100c00380b10060215042c41a0b46101c0d02d8850b5200c1d07100d54020114010400d1314103500b030750055109a204500610a503140ca00045900603854140541c49400a103981410321031004242840710001720300781040681e120058074050300e2a0340943e00320000f80340c00c0c000b0031201200e12172100001004107800003842d8100b0079241d580191444039001070554001001d0b5041d503030044201000b6880c00ea040c40e007003841051107104207903814460000d10080c010b41280220101131082b0489a00041c0526015030222040404864002c20040c0c4a84002500400da400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 261880503 1250 261879253 261879263
    0x9031c0c050105010e0f06060706060905070504080c1f110c0d050619050c0a1103070605010312120506090619080631020315060f03060c031501021b09180d0309 70
    0x110000803001700413600c40303001c0d80035624442050742c0c8a40502000764488001110b02d5030365200002640803ca10130540555040e0392501d47d2949031000b0149000f05c500b088a00c603001c0030000084440340b1050081e0304c8640f5042c80c0094030030300ca90103402c01908900d01500600106e502c07904100001c540385114504588605920082249500048440464203018400420012002c2e800d0241c80c4030351444108000b241d00d405c8007030342c03210180e440030703030048480d2090601012003c030b8000c444201110020001003200d80341400008010100c0940b03403d00581401043c071072100007405810740078003a1a000c8428600b01505c0000e40039070b0320202c8510b142d0038274680d040c0c00151140381580541e0000c000701b281c0744940407050b01e8030354080d1045911143c12050035029840600c0b03428804c0f1017204d845603d0340b13011025101003c04480c096811504010a4008480c000303030b021103031408042d01d80e503006030782e04081840c800801c541c40058a1040d40b40320041580e158008419262150b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 261881753 1250 261880503 261880511
    0xf030315060206370e010b04020f030103080c0c090903040e070507030210050a060f060504140a0302030d0c060213030b040c050a060906120b18011e0b0a0509031c0c0501 74
    0xa40301229519541c02000010f03001140032501e00314054054011801885400c0000382c0c445141d4420300c400801202400c079929807076000c06048007031241400842c010b442c2076203010060f2505041512050000a0616102080103080c004080104c080e8102c000340403220a400d0000000390ba07600148107940e00b01500e41c000803d0b691103a1709171890542d1540041110030501213690016050003003549041d03680d180740014103020601c1000f001015691203140d501e60034058195080c0d807001491078000c0711100700800040c0c80015081c0203001c880e1800003600c28803071402c00044c1c4202c8a0700303c16142d1299011042c8070840f04802e008a00c00e103100f144180d40e5009000800b050b5204500100b0700001040000501a1810b0030410b030b625a80001c801c11240001554100741c0300b0f1403c030b02c2d05820011b201c140c400030310080340d4401d0021805c4200303280082d0782c5071600c00c18280204200010980070042d8030100070324100151400750303451400440c440000c100e802c030140103850960034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 261883003 1250 261881753 261881771
    0x20706020f1e0403021302031503161701061d0a0603080301030b070305251d18071103070507090c050c0d03020a1d0a0e0c0715090213021812030708070f0303 69
    0xc07041124100c4e54064046620b51078000e08002c000d4100505d600c1280044a060b003d46980c10311201c08081c1c251001940081e04002800c20191010700c12588560300d0840d091258a050a1441c45810417621011005549809028005e000325504c020503110000c8004810400e4012216115100b9940c1c200a03595451034000388001c01701020041c16000207520008961045048043c0c084c0c024165003039000009010801c40341e0044c00c1300d0030010001e003d20001540c0140407200c8100030302d00540c100f8480761503107a21002544500440981d481811312000c40c0101c06a40e050b000e040c05a819005800c0c02c0030f0044d41c01881d80304001244841040303030b40b4140140743e007020100608040307500c5081070b40355a1100e038007414094600005108440c0050300d40c104d03d01c010703140340c800465021583d2060081e100751114102c0755040c014402c01c0e0391040b030b8403a182500d00080305c14506c04c1c03031880000c070f08501c82c0040c003030311001c0005511760a00410130b4400c5080d86c0310b55400c00817825 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 261884253 1250 261883003 261883057
    0x60a1e090804090c0203070309150903080f0304050c0102120409020a120e010906110c031c18031d06030103050c0f0a08030d15080d050f0a021e0607020d030b0f0112020706020f 77
    0x451f10a000b000f144061034107104c0c08140c65002512041641021000507072070351500d8000c0d4001103c00d0510010000c00c010800105000b4418200003c3c001061100c4208802c44d5a900880c050901c00540c0815140000d900c15941c403140050030741003c10045208603001806071131518020303102c05060109004480300260700b21556121210003a50904500003402e603a411614640407180c10744400e558452005614000a0740328800d4640400c119032589a280030701071603e070104d104410910042021410104084140d40403c45031104403031150000115211080c0d040040c00f131101090945004049512407400300b0503000620b000725680700c5009640303004035042400081c2c0280014030448003480090005018903005072040120b12813100c80044124100c0c4014540c001800d1292164061003552081d8801e464140072404103030b0041120080b090b40c0403810407002e884019022000e59054800d4264480015596051510300c0c04045401240072014420100b00d0701c4203e6203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 261885503 1250 261884253 261884257
    0xf1d06100e012313020c0601060807050a050d0b0d0501110d05090706020d2a0303060509060a0303021e0102040f08071e0e0106110109150e0d0e03060a1e090804090c0203 74
    0x20b4040301105072034142800d07403071078a00e0341c03c10301504825507a116281803c81c60020304484c005144c0180013543c5441d2009001c92000742035901884070402040c107041d80c0c000111581a501d0a101282100c0e01c400400c2020f00c1c40a80070301a03501e0007a41c41e101103440c00c01041c200c51902d0701404591030b041000d41d1180c015103d2007003d64001400d1003100c500031a201e088046a409180e413110a07202d08100703400d00220004c4001a6039050184968900b2040c20307a044902078a58002d603904542e0040d40d0740c0700301092140c10780c80b1901c080d591750109404079400f901560150285a0f030f40e502c10740d9a140554018252200300489007103801809031803030b41b0111550550404056440d09000752170011042882c66030b00d540f944854004a0703540e900710031810b529000c0010713001e0b040001c0242428040c001074400c01c04907031001c4419a070700040080d0003281e08074001681485013400c01c142014003006090500341003c04030420300818a0160045030030a6805000143c1c0c120000c0381c80b8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 261886753 1250 261885503 261885509
    0xa111c05150f091b2502010306060302130311120703110a082a040e0f0a060605040908191b1202060c09030d030b01021603080c1c020607030f1d06100e01 67
    0x44410540080c0c83c5002c82e04035440004520b40c1a94500500745610051001c100b41200184070064170260045583c18400c1d40000d1000d40380450808102c032200c510300900303500c4058010b104100400b00d01d5a01e02d80c542c0041c045010849824660300d1404150700108010218464120341c0d4001030103542c082280040201c01c0c09588100c04c1c4281494256901010705041d00316507240040e40e040c0b40f04000e214040c20400004100c4000700d4130f4403009441d1248c0203140543d040c1000c900016004000b501d0051b0b1409a512131131164007141115036410141e00d80344140104c003180e00520100c00d003480e244100f29425192150b60f40c3c600c0490610030300004c16090361049582011303c03446540840b10401c01441034581030301500c040a1650780503504251080c81c2c00290206100e074040000c2610b01842117081e01d001017542002035100c4000818250070700d6141d54a02010034919845014090400b26044800d000c003407152540da2542298000e0314507020400c0440e0002100ca00c21b412 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 261888003 1250 261886753 261886759
    0x604090206070b0c0403320705030705060304020409080a05030f0c0306090f13120522140603090c0d0b09010f0608100207050111041d011a030a111c05150f 68
    0x303401895682d810059078000c0413140014402c0c000400050804007a07016440d0011601000d0032401440c00c060110000500d240c7c03591100204020039200842c501084910481d03d041d200d940b240046005002e92040003090707960009980440036401c180034600522403100849640d40c1c0f48021100340d4407007900c5040c2e01c500c1000c00100650958031050ba8405282c2141c00314070341d5180c0c0c0310034010010100300004070b4400700301d942e807480000d207080204111114402005078a0484451030314903402517024080d00f03001000503140c02d0100000200d9000c05004040314443c2410071901c034907030075030b048441c55080c80034000c4200c0081c0142c00035116500041c0c406a0380030040f584c025404010102c0c1c0301d54840d00c0411807014440c0c003905c01440c041c81c5200c0f60000821102480e898140c0190008602d1003181c60700021040d0127032a4001c0c10b0400000d605c0e46c40001706901d90245040c0c0464041c43c084900c140500c0e035400103402802c101640c0c0c0007082840d002c011031403a0100d030550b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 261889253 1250 261888003 261888007
    0x102040e101a0705010209030604060b01110102070b1303110d030b0108160e060a020a0f050d081008030406120908160605071403040204201b0c120c0d0203011509050405060604090206 80
    0x441d0b06490802849844d10a0000501d04581880820304185045500b614001c5c1c0d81d86a80b841560030092900348401c20000071460889241c0ea80300a62001401c10344414032940c01c007000f01405241d801c841850820105c130706a03c01c1d980c008002e011a803914500150481001c02c01f01075030940f168010a0301510b90041c940164428002a81c001e10a407004611038a0ba5076804070f80c101c40c041c40440e01030405407443d800500030180c0400405411603480703a40d0b15404100311038001c81990140c031114a400c0712120001030820340175088040000c0d0940100046140c068064038859280c0240710f244140074903698413006461032071b82c0c0151176074440001c10000d0010314041d4460342c034189a410070582001110405d080c0c29801080b52203e8944450b608502e000908001800c4491002c45207600d1021101c2d03606038a911106003c240694246020350085503001e402c6003540e540155403c080c000d41e9028030a02601042d242075500d401881c020414a06040c082e00f05147c0d0058013981c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 261890503 1250 261889253 261889289
    0x6090f020310053117040f0f030b0610090315020d020f1b1902010e04110c031b24091e0c0909150c0a030e0a150e0604030909022a0102040e10 62
    0x60b401100030428581202e0704001c00305407d008080da040180030300340c17100904d01381141742c1516640006010b1030702c258000b4082a02c0c1d241e010312003a041d41e51002e5900416506071120324080c0c001c198204441c00e0020400041041ca442d02601c01c0032090350442da0300408041ea9141c43d01c8440c02c2c00c451100c0061408005940240101010140046c000242e0340f52100d04980460304040d000060300e400c00a00d0510016110310b07424440c45ca07000160030840840300c41c0c0901021010007442c01d0041610000300910824046800d00100c5a01102c44c1c0340445a00b183e01c0c0d41541325013501c20422440800c0c010240083e40462480820700c0b464ac5070380311480c0410144e0024040f500403d5151440070714498010f00c0028449407081a4400c05c000c04181c280068403082c4418034950740c040c80401c804260300c030f0020001c4920406006990701c030041c42d600c03040b0019186100040d40845000140c034001580100202d4002d030380040c119450f001c4503244611814480c030381c80740c06207071800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 261891753 1250 261890503 261890513
    0x30c0813020d0501050405150c04080a06050c0c0106060206090f03130302010e13090f12111506041d03030702010608061b0a05091e03010501050d0f06090f0203100531 73
    0x4040d1500040c0452a01c0d01c20f6900e035400d482045500b01c510340c1103410305008892030341c10303030b160004003914038241082d041803ca107039909030f8440c02070445601d40700031440f03800201e400c032403c0402d03480080c40032a0300d60300d01a6540a00f034548100621402d03c20300e800000200c155a03511601040302030345a40345800441d0030b9050607080d141d10031440706c1403e02c4800700c0d10580140ba84a405240307071103145403d11129a680700c0384404240480c2c809490150031010860300420241c5c00c08551903903c50b04046002804000b00680c07692415200204907004c001001d10b100e400d00750b00034090310741c82d84c4a06403210340c183d03000011411025031000311103030104d01412070b00c40c1038a029401c040c81d0700002098640c02041a150081482c00c403c0041d04003030240038054103060f28603600420711a6207001c2c0d500d52071b40000e410340d541e070380d01c100c10440406e00c0b179015290010b0807a51101d1b0390f1080c5000801c0c00b52065801d205115440448081244140c80300c9038218040c07140798501c094440e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 261893003 1250 261891753 261891781
    0x20a1b02060c0f06060406060c0b070c050c12101808030403050703210c080702071d0606040306051006020c0d0f080d060906060507050c0a080c060d0e010501090506030607030c08 78
    0x100d03809002480858554032040005103019a0824020441d50400301c0c02d10046404603003158040010300e05001c0c1c045003152441d25000f1906280014cc10101424428100f4900d082013513804482c05000c10b10311040014040c0d00720101001c100300802404000310a54204c0c19401071072480b040c4001408a40503202174034155000c1d0804800780444130003103034202546800d60705c2d0002da50b994084480c5031700c030060130341c03002035400106041824006a060f00826094841294a04450014041c1d0f00d0380d009a80c01183c1c004c0e030078444c605201e07410a9005220703000300401403080001841c02881c000c4600402e8903004104603010352055159501158030654480c0c0c00c0300c1c1c036020006022000c902c5680c0091009940e095103800d01407402c03038142200303d00700354440c0b000810f05000f0b0100214101084980407103626554250322000310018042824010065520746000094031004a8024500c2841c04905039601c80c4d0ba581e4040c0e04031031880c080000012a440002072000e02d60a107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 261894253 1250 261893003 261893057
    0x10b100c03090e040804030614061c0f08030f0f0f06010e1c1502180103060f0e060d0b01090b0f090712150308130e0702190b061503100513020a 63
    0x2405140b02038441c0c5040380c90b504280c40450310120002410002e00a951083c0f0300810340c1d040c1070300312904101c4001000601d0b4231040344501030b0221250810403013045182194150b00038602a100d207044440384140350002c440f1040c0884105002511030b903078000c2501d11440d0141c642c1050103203c0002c0c00030f02c841544981d460b0600c400c1840c00440c1007000c0c810301502d01d900d0050395408020744008040c001c100482814142040300c188603840035000d101040c0c4441c0e02400320b02e582d44034005413084004800280c40107405800102c1e5181d5103400000203800c0560300504448684402c0c00000c0c03100700ca15200142000b802e41c1c0c10007441d6044005800212656490b140352203881e222000c0d031000f091021030384c00d16201004040b850b100115408000d50000c0e040485513141880303c082120303103004021640385030000b142940c403420002c0802903007a1101e901d0b45050750003401c0d0b0761824020b03184140000600d055040e030b180e00031102401141c1e51002c2c214500d00c101c12400c031460780 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 261895503 1250 261894253 261894257
    0x30103060b0d0602190e01030c08061002010b060c0709110f03040b070210240602030307050415031107060b03010501090b1503150301090309060f090f170c04020406020a060b03010b100c03 82
    0xe00712901107141d50026058002c508105c5100041c000c4c50060841c610303000c0707202d043c1410582c021040326040024290f01010685d040a03981224800c200d0060140d450030a5000c0c0000c07840001070b190006820b802e490504504010300b152400e0341c80124091822000d20b1814100f0000b00041d07a90b1441d682c0106031401210315034102c15000c102580d02c03034440d4000307140c030700c400c0880401d4103013004400805060020350324600b0007030b100400314420383c0602180c40342c03010300021080c1d04c01c1d405078820086005005450f0340c02480c044000d014040c01051296003824004900c0022904c141080360000404d00007810001b8000c00640b6040101400102e01440e0826807803501c0a0040e00c03146840703031b915030354200c0c20f000c0e02804250601d0b226404008603003006000040e0403d0012007038441c0314000046101d8004500b40c540044001000e8201e4004180010029000520a6041441054140184580d40091508030349504020541c00208146121141401441e0101c0d18900034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 261896753 1250 261895503 261895519
    0x3021303020d0c0320040b0604031124040e150a06120c02031209030c060c16110d05010c020309030106120f02060f0c07080601060e0102031204080d1418160b030103060b 74
    0x17510b03030a03601e40443c044800c50b60700c00420801c4601c1c061040c01070182040ba5041d003000e0940d2a1030391805581c035900d03030044c18005904940ca004a01c6440302c0c203400104810360781d503202c4500244c0440d050f605a41c0880302e64511400b540f401248200030b8407e25a03540d0314052100a03a6405490f1942d60329043d0701080000c4102155803800043c41203503481c00450351800c1e004600c0d4034080c0c3c01021038214050034000101070030005100c0c00e01d01600300e6903401504241c08002182d0b40f510741e01c014800d40c40c02c0124009541c012003d400200811002044800d40e02d007070a00046141c0c48000f42009503a4a1100045c500a405440c1c200b64940d162800c1c104003120003460590781e6006003a2039880f41c0e00412403503a00200c0703107c60000030701c007450800c01420a290f6180340c2c0508002d20340030010910403650107990f4040b1012090700d980c6106a4141070380149555907082107007031158050b02650711403200641c0d015a049400c001e0f50140707140e10f90303214440100b1003115055806154 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 261898003 1250 261896753 261896759
    0xd080a0209041b09150e0415050603040501090b1e1f050a0b071e02090a050402060d09060902130509030417100f020a121503031407050a0b1603021303020d0c 69
    0x89108491440e480300040c00f01d1507901070000340c61444103030300a41040f0b80038507621302e8855010500007000c1000745e070301188064500d41d2408034401c1c55000b0541003000802000140141504140d0720580034010000070f0f600c81d04004055140c00c00b401114034280f03000407900c04641d1581211034142461204606544c403240042d1041d43c1940c00741e40c0300440403c218051001e01c407146002c40c04031080f020a0000164046081c0c1e20f001045244059034500000302551111003c4070510640007400700100540c41c9400c00040032446c81c2680a440086500c022100240c4030f92401400103400440c1401c0c981510074840300071800381c03003516004030500d8160b892070714001c076007500c018000302580301c60550350000c02554034003031881199424008201c0d040b1044131509403d0380c0c0c00d8601800c03031056030448041a403182110040841c804c0070b103410180402003440b180a5522485650b23501158400c0440a0303001d646a4120b100456036410001803403c0842607203c0b5208089080c0301d06d0b5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 261899253 1250 261898003 261898009
    0xd051203040b010f0b07030e0108100e011203080603060f18030c030708040509060f010912060603020901030c050907050a0f08090a060507020d02070902040810021c020a05130e04050d080a0209 84
    0xd85007150311010100051220150000700c13000a00350507001386081c9859620b00a02d214140d02c003407818040c030100418000c0601c102c044010780440205500035507034901000032540b280705ca0950000c1c2c0003501061072417a01041c5507004084000001c2c0d056146c0c146545920205c0100b1540148400c02c81c10303c2091040c03024201060084840d00c2d1668036001c14840b042500400c801c5c4610f854601c20403042e0703000401202607603090309155160b55502c2c582103005000540001c5d501000c2000004108200410319001303450054602c50703441c4c0c488000c2a50540140404070020802d103020022885100c0c404043e440200882125140c08940d1115022908207442060058000c041d1058060f501005568010010004118503083ca09a20b498880c144010741d4001181c0024a200b031100d88a103941e41c000d21200720440d90750f64003030000f034074070340c080b003402020301d80300e03620004190242d2a503ca00c5642c100024004581c580c24040b90781000040601e0b054035030a00c43d04145803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 261900503 1250 261899253 261899257
    0x80a020f15040605071b0305031f0f06090b040b0708030c251e20120607020106030627030806040609090f05011b0f030b010207090911040b0f0f0d0512 66
    0x106541d0300700481400c1a041c2101903680081c1218103014582030424400c01142a026104580625245449844407039543c260000f04003091100f00e16032050110380102c29040c3c42c01110807a8580c48440c65882134840100c1c00703148505c403101001030003808040f980c0c0100842d405101c006410385031150004802c0102d101d149000400c80c070450300c0c1d0604001150030700f41b03440301c2c889501411035112075031643d0011500041c0400d811707484c11880000e075220400f40380d41c0c040c503050584480e8a001e0000038000c02d074a201c1036800c1420482c00181d01a01c0e00c1e0001d40d04e81c5c4917049481d258015441c103862294000e416580c029075140000103603a078917407280001492003003080003103480c254100b450944441090080301c03441814401d18001c3d03007103001910100304604000c1580c50000005030308000c500d5120078415800c0000300310401001c0c8480c11090308044800700306480045050001004101b503c190f000100c501e0b120902d880c100144894681c0304104036404e20000c502440001c3d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 261901753 1250 261900503 261900523
    0x402010e120609011d030a0309080c010e0d020c0a0b030703020310080f010204050114040e0403110a0c060c0302010e070509060d061d060601110105060603010504020307031b050a17060a03080a020f 86
    0x41d81280040c0050000c0a008019040c085c3c8071114014400c00d40c003036522403044c5182e40c4d047c15680d030a40c000300030f291000d81e4072070b02e0400f00810034548408015501c403404261154014040c1010381501c6140001281c1c040d0303940075002d14156502c00000b50000d40c001741c820b0303030441c9900700f0008804504111a491013803841c0000350301c8506d4031300007415000346240f4542c001c8005110a1010002102c0c8035540903030186004403851020880d011305180c080480506420580ca2001c0349940d004510502071a11950082020714650003209855070308034010300d9400691407010400b286404c404a00400780958000541d010348001e60074040110380c50390f240c29400010410040750f07080b071080900400c400009115074644000010141d200c1400344c07a02c120f81c0440800c0341c081c800d521818403c08003004421b107881c030061000d880c0342c009446c0342000810040b0040340c1c00500840700c1c0c0c0204005005909610b00b181d498042c240c1000f81c00804600c00e524070300703102c140100441c0e012 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 261903003 1250 261901753 261901789
    0x1211010e250b0904090f0614060a05031519020c100b19210f0b13021f2309060a09090f0b01020604020f0f0a0602010509060a0915050402010e 62
    0x2038041d885040310750030a010751560548103007030081080300d250b054044940c1d0a00c02c4600107001340c0c55140040d000b0700606d102038030262070030301d002921a03415000503018000c102c03000110150741c0c10405968080c004c0000907170410100101c1c4000b02040821101680381c008090308101d0f406001514108594918010185c1c40f10032005090528440101752011042900c2e800c403401c0280b0340300894048003601096100c0c80c40d0180c207010160600c1c0c1e44641d80241c40d0074590a20150700e1405240020040c0d224242d00c81c83c401045130390f152400301c05402d5441d1803103101c424248403441c0b240e450701034a5850a0400c842c02c2c140d602d00c001490032840039220102c40754240082c2804848442d480c110304285007070350a5010344e80014070b00c1e9106904a0701070514a42d010042070049448102850304074050441c0454429010340180b84540241e40071070342d160ba284001082a1003030b0b00c030003410b142641908080d42ca4a59044180d00c2030040c10070407111054400800d4410a040601c0c40ba = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 261904253 1250 261903003 261903013
    0x5070b071a010f1d0c04120f05010509030c0a08090d1b060e1005070204200a031410060c03111f0f0e061b09010908122a03071211010e 59
    0x1800e40d0244040c1c003403e24014043e201500305422004200708139209000036012120010f42c0c5001090116030180c28070040c82c000300041458000c42c03400c6100b000f19040e508000000d4039190000060301c20403440100280b4010600303072100c00440c1e10210729141c0081e81c020642d00801c0204aa50601c17803c2e840700c2070301c0d05113080401810480818a04c07072061924a101c00c200d10791140645035450b4048034002110010407107220092000c1c0c0f80c150031b0500c030112342070201e190103501050184013500c3d810f0880383c0d24440c0150090600d4010a4081114042c403040440e119008512103101c1c621300700d800f03052008561310a0611807507607007241180c450700c55408070b03802030140c000d0070401c03003008051030700304228064032080c50700d0014814400c0114801100da8401c0080d0401081d02c07200341e64504d00c20088a841da40d0021b035203116400e01c4400603440d60500040c40c00001d03401e29019606005080e50b07129003440039403c81d00200103010f00401440142881012002014600140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 261905503 1250 261904253 261904283
    0x302010b120d080a0c08011503140403020102031801020715090804030f05070f0b090907120b060409060311060f07150e0d020109110409050a060c2705011b0f03030905070b07 76
    0x400c3d800c4024610454076042400340344509410000f49815600034405ca504d5050041c0030880c010140891341c2100c46040d2010303c0709040c1c040d80117600550f0001a6840c8007100008107034280d104820b0005c0144441540c410b0072901f041d844240e09a2040c00d10616003940ca03100c040c20b030008100c0954440e00400c00400150814046034801088140c96a50070030014000141440c48000c00c0d2105102c00702c0b440d01d8000e0001c0c0d00c00c0c120981c0003018251030700d44a07084200106031600048900d03124a1f42d1002951801105a07003a1104003201e1500e00011692960060300604283d41441074881860500e40e020500459207409881c0c6e000244c1c1d12150b003028810006040081401641b403c1d8140000c0303000072a0300055913400280218084c014060110f4048100c3e064041010384107000c02d500403980c0300241317000c43e1405d0340d488150f82c00342580140a680070903002401208000346103000607000e81c1008401038000e00540d21130f0382d99580001110340c8800811500d19000000750 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 261906753 1250 261905503 261905507
    0x102030603100c27180207020f0d0b15060f0307020a031d0a17100216200f041d01020307090503011b05040e0901020d1103090d030b030d05070302010b120d 68
    0x76011000c2d03400700501080d034559401401c41300d40341030100412103401c5034100c02080784c8008800206214040b005036503080a000000940002e51f00b02c0c0f003038245031141d421503e0000b552403140e42d0014040845a21040041048840b0980316540c1105d81402041070111a02c80034500c82c0c0d01603000742c030781e2007500d10b8000c2c03528105042e0250000c0300c100d1000210349812403524160348008403a8409030030b2101c45240340800f01c1010300d01c01400000c172400140000640c445a0f20f00c1821a201c0149800b0591000c840c8440b4016800450700c00c00c9009501e00390f01321040b5964100100300c141801c40c10581d0070b9910488035030000c556013040c1046141403d00c078407508a891074031115004180c501c00200f03203101d988140c1000602c4000171464101080d4100c4100c1c00089030100307c40300000600051980044070304941501507454081c0b80c1d41d0103401960050035004019000d11400c1a070305440680005009a00315942d1f180e20b0241ea41380c0c43c21a8220380310290051084203090100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 261908003 1250 261906753 261906763
    0x1b0815040b0f07110a110f04050108031c0e061501020f01021216030b0d03081605120601050304033f050603072903040516170604030e01170415200409020304030507020a03050102030603 81
    0x2052340180c0c50040100444080401aa11019141d50610303440c641d056100501800402208040304e000d9802400702ca296800a04001130500383c082d607403140c1c861030300c0303900301d026080c207400d00c50701c0d5400020b00c1c1e02c58481c4590300180141c00c00080041c0e52102192084d8900d5004601151051091005042000c0454a0041201c0c600390303141240705a0804503000e400340505060041c0480801c042500820b51702c11280b4104803203102c6003a081240220f8a80c0140c0305c446115582010034003448098080e09114140107401810303040d182074540c1c0385030b1140759004a080d1034488884a410800d8034004c6000318014401001c81d103e030f0131040d5039980070551100008001c3c0303ca15240d4141c012501640c05901410008c028441d401c00589000b8040e2142d20400c03145e400c10401003001e50f01004c04000111174081141e802041c07403c490303220304800541110360040c4130030050350106400640c2e026101f0300e440303424804240c0c040760f10000c0d650401c8800ba500442002441c1c141000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 261909253 1250 261908003 261908029
    0xd05091002090102070b0903010605030f010c080f0103020102150a0e01020c0a0c0501020601290702090718080304080a0b1003020a081f1a01110a1b0815040b0f07110a11 74
    0x4030461901c014107001070366901e003501c5084244d42010801070312030b580a501400050901030180c071203c2c21140c490381c1c001c100040702c3c1c2c07000c5010a0f010460f10a44128400d050301c0c1c2c10707002080030010107000d204000d60002c10703c86032191141403491145000380040c0588410320710090545203050304d0075100140c01e03500582e045600c1400100b15422900403041c0740344144410025211804075003403a1188240c001c040c1d0000784a800344015507502016075804010703910400c55a2680300d040458603480f0382d104030102a40401580c20109842c0200e080e00444404400003600b9030300e0b40810310040c90f80d03000b0041500181c140458082410b50111390b01000203908201815024543c0c10a10000c20046810000b80c3c0c0e99002c29240c04201540c90f40e0340000d00483e008808100b410300240b401e005281e140e008403c00c94601c43c182061160149922848070100b070342e1499000d01001000600a40c1000203200403098000d809015400005014284400c9906010f0042c4903d01807850 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 261910503 1250 261909253 261909283
    0xd0c0f061d1507080f0715181502250804060807021c21050907081009020a090b0604030c030b010608060d03090905060402090301140a050c040f0b09060f0d0509 70
    0x10114545690701e691905408448281402e43c5075085824026800d010b00e600c090b21505c0b0001d0500f042c0620403c100f150b0042c068401e00c0545603203a41e28112600e200c00003040501210003100c1c4803040c9070041c201f4445040d06203008003030904a0303441d6600003184e098884800c00242802400d5000c078025074000d0160005060043c80b451030900b9003000421604100b002c808401300c007a0300003014103c400000c051050100b406c0946c500d40e01c0307058522940e141c0344601e000c1041a441076000b4415102e4000b003d100000d450400881c014000028040d80d01c14020000880000c5002168001a40c043c020200c1c0940c18440050f015103009054507100c0c0181e04a0100003d501c016110b0a4503542c000209007512454017060190048a00d460750650800c0403274405c9034020340000d442540c44031020301076510355012040043c407507401000d040014241c001d012070644500280b100070300c054030a80c613010070600c2102d06034105012a100c0a502d6a0034812240020021580701000e04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 261911753 1250 261910503 261910547
    0xc01090605240901211707061a0f0901090b01090e1312051903200c0604020a09020c070905060102120a0e01230d1a04060b0a0305010b12060607020d0c0f06 68
    0x100c0740b20908011054200103c00b502844007040160106c0c640c04a01600850251156668900000074003500d01210f414880300c14100c3d6402c0c40c0c0409020070301c3d4000b608a110700e900f070911840207400c139000d80ca0b0501c81681c0c40010390f8402042018841c0d000f03448044603014081c03510440d1000e4008041e0204142407144400b004004699201000080e08001543c61982003440c40b58003c51003c00014207004907040840e1100844c415119620894022103041d480b07204820490050703c03010865a480080140039072400c80d440140c00100c140119a01c26000c6203400007254001d401d07010004800c1311407420b0658204281401d640d14034040143c142a00307540d180780c603008485901c81015182c04400c40600060b599000602d0405841030244070b844d0048403106510171041600024540400000d8511002c002d40b80301c040e41c500400f985403100c01c100070064200810030799100020b0225500081e8280e48144010950300101401452070300074060000200032400008003408 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 261913003 1250 261911753 261911759
    0x501030603080d091103030d141008070b0d06030f0f02090601141e040902040801050105010207080703030f050a1e120b0319230f06040c05040c0c020103020c01090605240901 76
    0x406400e80d00c000d51410f60000e008022400c01000301e9207111851505404000b80014000302c864000400c40c03601500100e000ea1030300328958030740c00d50500c50100c3c9034009280901c204bc040303400a022401051030301060301c641f01e4a0302030540100c2e10048480490500503c011401c0c8a04a85d40c0f004003400c0c801e1b240f004000803500c0500c110784940e141e400030b200000b4082d030342d01c3c416500540404201107403915226081130b402441c0a02a45001d440b41c2c40001231a4000040e9160a0f20303495611062121040700c420b90742c50f0010b003240e100380042d42150464894084060070001819603580180042144480302d0032545411100740c0281c0090700d440d50354214032018961510b07401440f80e01c128030000303a20301d82000e056070262000c0c05440c2d501244074000080741e50140c1c0c0648000311003259588200002c80e40d69480d0360000c140da420f108000741d0700950291504c00c0841c1c0010450b24959900e0300102d5404454004402400081030310300070300340d1000c1c0f40b00160207840803c100c0d41 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 261914253 1250 261913003 261913013
    0xc09120c0906060d0e0109050c040612080f0d0207050115090617060f130506280912031a100309060b0d030c2a03030e100806011b0501090f080706060501030603 70
    0x1000400b214010880011070002c0d40c08254021503903d55840b000308000c080b1391410640350341500c0c0007907101c0c40c1400c0001c10351a9000c40c404500c43c0d0311203819407400d102c429081c4401d8100b900d140c905140d00340049008200d00313019800004106004441075030342490b5a510840740c1a8000101d4466205423508050f03800281b45a0030054544c520020313562030f6a810501da54400100812500910091200c7c11090111a0104012120715506200461070602d0112045010007a1034460b01140c00f401150007540464038481c103658040c10f03243c9000b004581ba4403008003101002030340e501180800e2105a00c140708548404407031f04002d080058030010501041400042d110595508400c80d07045007101d500c91280c1c1d40790300d240a0099590502802002071443c6490003001d05003414013240e48900c6580d441081c1c161100318032001c411940102240b04414121419940c580041e00403030200140300802d0340c03080780382941c0c0d140306241c10b0003514000d42c086810305003000c0f800c1c00012 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 261915503 1250 261914253 261914269
    0x8070f0504020c010b0402040806070908160302010e0a0801020a09050f0f030c210706090312080108061302030a0507090e19030e090915010b0903010b09010810090302030c03030c09120c 81
    0x318111000341c3ca54109128941c01032a81421140d4401e05c0010300098800000c6040d500c660f5080c0c440200a544d22029140c0b904004080d20810405035a0305100560107102480007042e000b40183d130000d900e40595600f203900940469002c50f901c0303c0100400c3c07508907207400102105075074441d450800800401d81e100050b110103403280700050326408000940c2c00308100c09140c0b030342c12500d8140e6110800b034038800440c041030310710b0b004059482c0c40140c0200b00650482d00000c0084c00280c0d6013900310b481c10340002900b04d83c5070040689900c041f840030011000a0100000c0003d4156428012030780b402076550700d101000e0072038001803400309070030002545800c8030a42c0d5890703540d51901c400d10304003c6e406004150713043c0c4030800818210030100c05081c642d4002d0307008000e605102c108101410034240303c2c031001c55020b9981d00c103000d071044c0c00a11445201340101e9040024207c0200e0468004803040b08840d200807403a0b03080d510f0304085034a00040c8000c00b41c070700300610602041e160 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 261916753 1250 261915503 261915509
    0xa0b07030e030c03130311010806030607030f1d24010b09100c020603042307120f030306030b010b070203010c030608030a0f1101020a0e03060610050a0e041509020703080108070f 78
    0x4181d032030540c91141c0c002841102e161091000c01c1d030f0781c0c80285103600000449640030070340c0e04600c0751a5103802075010f01e01041c0074400c010010301a50303441d0f92b0100c0103000d400c07459940c1c240d203402c21188501e0082101c08681c0308d85101a242c540c6104c030f01120252074213000002c08031110401041608921310864140134400c0d24042a540200c1d81d003600c1c10744a540c00290001f170000104014030411007a00c0c08ca0112010640d04030780022300240c1c2c0d8a4980e40140c624000c51008032a00140c600c42c080e20485200b07082c0070038403d03940d407100804407400340d04c40c0c52507403000a44102180303000c2c8254021806036090801c10542400c1c14941d0b64003038000d15105001c0c480a01615017805445411964081c001c02176580f40a4002c009048000c4c3c0380482d1f0291041b0740c0031136254a04180074001061413035640c641001c041c0f6000705c40c00b002140c59035401c1030350b0314004141030480010406c06086203280150f60703000f40345401012080160311840203034001990610200201c85000011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 261918003 1250 261916753 261916757
    0xb090606010c120e0a06020c1009060e060d0902030105132a060503060307081b0a080303040f030522060c03020c01110705060d1401030c030201120c0507140f010507050910020a0b07 79
    0xf10700303007516041d1007083c8204640b40e07208540400001d0141d5000800e225000010b0b0780da000d1280c115101541d10208074040e500c0810f0407502c0a0440782408000741c401a000e07081c010a0741c602d603801003401c4803019140d10341d11098446407242408024510310452a0015581180b402e00d003240903485218036000d04001c00000001203a098ac0c1c4c204a8080a0602a82994004c0c03100384003840c201603505400078058032503024000348640010041d24030980d08242050b250300c00740d980c102c4040d0700c0102881403d41503488481000d240c07203070000000d4511501c8910904955040181c5401844081a81041001d0f41e140c80421000304186049036000c0d00c8050716290440c501c2c8000e4801e010542030750340010f0300000188542490010101d074000e0300d45c0c0c00c07400100121201039a40410140300850000c02401000440010009088039010415240d10007041d4913072508bd0352058072b2000001d070010038090f0541c6070481d500105600b1a0000b0310340c8008654450145940007496030742 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 261919253 1250 261918003 261918023
    0x50904030e03010b1305010f0909080306010f05040b03010e270a020906040e012c15041e02040507090f0501020c01020a1e0c03030807031b020c1002070914040b090606010c 75
    0xa294030b0940100303c0da07180040201010301100001100100ba00744a44401d04041c0000080c1c140b0892140400c4a60005181461075603524019070703001c0c1002c200c48003000010000010900f04030740c05035020b01040700b4100050305201c4107011040c98000c11200f01802c654420f0446020300103201d14082d40e05079460805565a400024000d02d00d80b411510154240b9646441019030310481c5051408007403801d450011500c08e03516641d0000c2210811040c0a02c0d012401242081d000585010044514007520b000c40341d01003130030b0312001c0e5009004110003c0302402480004050440508001c0c802010300c2c91001e00000e6072600d5118014168076039440141030f80c031118034072040055030040102d90000e9520b15000708058411603400002074503180c815208401080041c800300c1015500412100c45080100031b00040d800b0f1500c0c0035071103050000121143d0b0342c051aa41d40461450003400c2c2d280908040005004c02014010141c211604000c1e5980e04402d0500c405500084841c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 261920503 1250 261919253 261919277
    0xe06040c210204170a1707081b010e1002030c04030f020a08010203040305130f03030c0b0702010f06090b0f03060408030115051c0207051b0307151e0207031b05090403 73
    0x240d014020355101d51521841d94005107071600c1c80303070010000c803410501c0e400140140507a103140c0740d0380030701002410038001d0030780b0030303040c08901c0050603080d07000c1d0b001c192605a407041c1c0c1000108800e481c14000380d44510901140784410302c04007658101c2c2003000d40c13442c0b8100400c440a44981d010060240c0540d100c05010740d121491024007a11a40700210740c1c0b81000e09002c1c0444e00501110303080c0720380e441c00110305200020910707401c0780c1d410380340c4421749042581d94448900005020b038003150360f540d00c1281100514041c11004103903819000954511030414400c83c0c03000082e156010b58030080c2404002180f940880b4110b40780c10801c2c010407a0f039500d0840f0103108141c808084c0380200c000c44c000081080e4000c100c6070707104108881c0c0014a12003081c641040160300c50340c0c1500641020030000d108000084807074a550325000a80414002c107040034407000e5048000180e12000081c41040444000c1c01e9109103103584400704189000b00003228683c0040c402400c10019080c00703 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 261921753 1250 261920503 261920507
    0x103020a0c0f0605061903050c0d110d03050c12030f070c030c050d030b0a09050411090a15080307120c120e181302040b010f020c0904052506020c01090e06040c 70
    0x10700c8140d540503072180d910041c80d091440c050201a580315104008407200724800c1d11180d6900402c8036807040243c03407280f880e181005510701003000159180c1c2210301d20501c8990f1200042000715202c2e40b0b03003544904050705c08a19010076030041c590003540420038402210000d00d410f50344000b4a141c180b040360a02d260894510304c103d0030040951280d01584e1402d980c1681010000fa602699842411076880060806132242904d0250400c24001c48491807030401034506640a0400140404c2c00c80d640448605443c3e40c60784490142d41010581c00200b0122400f01f00100455140c120170024040c1c0303d84058080050f00710003070140c0c0c41503080c200d4941d0242d8002c3c24103940d1506200340360013110701d14600000b0804910031031600c004e1030420760003050440c4841c0c0e003550042403030059820502004200140003510903204110b1401d412611030a6251411181c00c40703000d074034624124000e481c0c55000401107050203a44030b002e00c80d46034406078150348514111400304d00c5081421003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 261923003 1250 261921753 261921767
    0x50c1002150c04090b0907080f06060405061c0b04090b1614030c0a02061b0417120309070906080304030b27030d0603051b1807050f03070e09070314060103020a 70
    0x1440c007101d58a00c100400115500d02400858600c42404c0c0134030b940c400d0070012900022507684003c0380c0c1d0038020814140400c0c1140380d00c100054016864591500c1c00100c1503088000c0001c442441e00d40e2042207000c042c0100040d00b04207650900519a0503900d681e42502e00400030380754420500300c0308090910401c41081d8071240031024a5580c00d000b259031a050b80715219860141c4120720103d100040c45c440e00340c9202d81c644004504081c24904150702e03120501203034181901c00c4074440070781142c01500440c0600d000000600000b80b0700901801901c0041c0e0000c3d1103900300707100c2000461f0045454a52081400604030003000100d11074485407503c01182c03044070b00c03020071002c2075808258005000e8900800c119444000444800300241c00c2528407560069840c2034000f1124000840903604a400d90400c0340c00e11948081340c0c07048e50401ca4043c000151018040101800c24039101a0400c0341c5203401c0c001e10811451004501102811f030604050b400100f50142600c2202 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 261924253 1250 261923003 261923023
    0xc030b09061c062d05070908070b0904060f0909052b0305060d0b0108010e0c0901080703030810030b0a060f06020a03021513050a05010e0d170a0b04060302041503030318050c1002 78
    0x6038122070502c00c0d100a284001304405401102850000885c4110340201035003011107200100a026041c00c1c8000300300c0c1904864001e43c1c0280d2100c4001c41e24801401001005c0c00300030b64000f4410441c1d0600d545440c0040001011542800050170382c0580009100c41465460b401d0100301034a83c100172403480030f03050760003501d0b0449200001c1070031041034100e540114010011a11302da0020010054100821720070b02e10b581d80726003c1000080e0003101280d40c0302c010f85141c02c3c00300d0b6881d22642481d850403604000d1156541109010913100024801c0240a441c40105076a20b00c82d034010799165036001c0b540c440303001000000385000e020041c03802038040d4032400303035422403c05242140c085e1114101090050003a211840e42c650b105542c1484d450000c000351006980360080303048001d08031440090380154540d540800580c50705e00501d141d0102000403801c08501c0c41c2001411100242c0520112408031a517032000f0510008070170310071302c4c0200c0e5803c2c3c00c003880e048242d18003201c000b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 261925503 1250 261924253 261924281
    0xd0615170606210603060610081b0f0409020703022a130f150510081608091606080a0f021e030c0910090611010225020d060f0c030b09061c06 62
    0x11149a921124071040f140164801e03411240c80d0b0f2245420842c03e4104807400c080000c4d004c200040b01910900b6403080100148a095441c0c0402c0501c5141264415040f00080d80c1d0002581020103504200344048203104540d10091002c9140100782035410000a1a11410004140c0800c1030455800040035943c1460100800486480c500755a0300051044a1080074844440300a403401029054421301c602c48a01d0440c8030034200071780c1c900340302074800040c41c41403845411303402c13100700c518a01400c66510341903203e181c05d0181c0001e66100c00004900e4500511060408040017484440415164078541340c44c2e5640758020492801015922540100080d1a0400c3c0b9504641076409854181e52159080040e1800541c05d03407184c00d103003d84210300490301e81d00c5e1400d003081142c892440200240a4407a107a150780f42500c90100e05017060030b60b01d0a01c011015018440c00411103010f842026003441c100002408038421010140713100c012000c1c4040c20400640c2c0b20410b200c22007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 261926753 1250 261925503 261925537
    0xb0f0703030b062208010b100503040501110403150b030a021005070f0219030201140c03090d03110106081b12100b01090905070206010518090706050a140c030d0615170606 75
    0x10054111000400340c1c0c41382c501c100011004180300e030040c0900c20540c0000303407915541d280d075035904032427681c4011b00a403000e541c1c030030a140c41d00380c40b4801040114002c00c42c282c60041011740581c02c0700c0309400560300c04c0d80040d007240010389038500f84180c0307403038642407d0b52290794605104000040001c0300070360002103c8003500c0c010b11000b8544095034005c1e41d40614000100d55108034034400d40c807008181394824800010036142c440700c541f80080c13083c507101c3c40d94442a405030b400e440340c9421222803504140e50030042c5000150107240c0c954030407119034200d40d0601d49010345a441c01101d460000341c03a28a810070690040c20500c0090a0002003000b0514003058000c3d12039a0a0051510810b0203015080258940d1a445030103002c1300005891440e00d442e00035a45680442c0c0c1a000b840301e110f141e17081501003000505900300e0582b020316900c0005404003011a541604100c3d06040446404040e8541c03100a94520105c050a102401d49602c0d0019543d03001c0c3c00081b001c60420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 261928003 1250 261926753 261926767
    0x818100603050703140a15020313080309010501050118030312020a090b0c0a05070501080903160201020c0a030b2706010b0a0c0f060f1a10121506020a050f03040b0f0703030b06 77
    0x2c0050700104480c010440c2d00742c11441812043c0c0c49100c0d040c4042c00ca506200f0308100446055070045802c0510300154825500301c035910703440b543c0c20841d0017400356503486d80104002d5800584000514080031031810041e4110765000d80511302a49001020f650301207925841140a815282d01a00100c030350640c807104015001c980d1065515804ca8881c01071050002e074650055881500440c4d04101440c2020002c101072001079a507000c00b41d0461181e000d022403641c4035018110f010f5802185248218905540c1140200444101c802c8010030320a00300c0f41440700200b1040d05440701c0d000a103983e4124a4021588038602e04000307051034104484420070041c850340855601c50f44458140542c0020030041c100328071426003e0b036002603003184c04204041c4290f05000c020900c41e000007518584009441400d42d105404c400c1c0540d1124800f1401d02c242082a00040b00440008602d09428800c15a48a001d0300c043c20f69001404a151020940a50010700c14038201409851710b60705 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 261929253 1250 261928003 261928013
    0x10615050d11130f05031c0c020301060b040816050d05070e092a1905012f060703020301061709120d022701090f12081615090303060e070818100603 65
    0x201510589044480380742001511b82000f1070561851b041c101500f21108000382000e03607403440d5081040740d040d56a48400701d0f00d0100c0002410103801844001d0400d01101d0b140481034100c50f4115510840300200900c0c00288001680415a510007111042548400d08902c0c84c2503250000f005503030324105034011845800540c628442c079404c40d00303074182464200b0480088001c80c040d250000300e091591560540540b8202e441c1e81c200041e41c043c1c2000040707442030038550300751802c00c000380c1c0001c01004100c5c2d002400384015001c50f01d0b03545c501d041480140d540c942044110461a09000c24445100000d80d03050301c851500c10080e000803000c0306928035140142140748240451038100300400c08002101c0340030140d4940c41c881d811071100a840b041c1c41c9400406c041c0b421000b41001c200001000340648210703c190080011900c0091454080c007501d005422156800038a01c082183c034940c00701103940c003d0030101d42c0c1c070410002918114108055180c0c4c11420500303044000003000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 261930503 1250 261929253 261929287
    0x220c1a0909070513031b03060e0601140a0807231f020d0309170906090d06020d06090e030a11010204080f03030a06060915110102160602120108010615050d11 69
    0x44125140600303036452082c00d07203013070040c05030314484168a00800c0c07000801c0010a1700c4070380c03104c4403843c4865981e56115020f4401d6908140307a0794100c000100051070700c0700b4410740341200458080800c1c41c2051012951103c0c5881761881d0606065141e10050545641030000e0780000781000c0014482c0c00350074003e03450301000e404010300c035402440d20032500c0b900c99a0700859210340c940305d041c400310844505540090102c83d41c021400c001900081ea2150300c0302192030b120b9007000d40c880007184a80300440783e09500030080c1e81e00f00404c03500030a0001c8115801d0452900300305116580780769034240240a1904009075601c641c44000380b1164001001e50f10071041600140011070b00c800e4101ea12103038600c260301034444101c2d20008424042c6800d60b81d2442c40c0d100040c10960200002e00040d0003d00084c5c440c4e0380c0c00604164a0098564494090302060000707000c91850b284d041c5400d84840c407900c03001c1210106495410113000d4012155510359011242d485200e1405804000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 261931753 1250 261930503 261930517
    0xd0b040201120e0a030e030f0601030c090e1504030c1a01080703021203040e0f0a0f050709060e121b0a0806072a0503030a020a050d090326220c1a 64
    0x1260744100c02c2c0609012074082c0c102d1101c998030161070102580e640c140e41071003840900139850300620030031080d12001040524002c50003007080000740c528144018049034411501610b4075003190030481544900d40d00043c0d002545458034641c0c011070384c00c21142144ca500410041d0b503185600028071180c001030799806480c02150001c9003100300c0c0c1d0410b9501d201d603108101d802c6900b140050015900340156560000c0d04000114040304034020140841d01c0071905c81e40440e000400512561381d0104048100200c05d0b0ac00e12088040840b0940c1c0e260106004a03142000b220021101a180c006100005001080c1155001d00308840090b005d000c1105260b0030701c114440e03071100e1a50301c4241d051521038001d03019529544904001c0c0010754005045207050007000c11044040c1c80d4544500c0c11800d010342e41d0414090381401402a24201801045500081c04003d0003540c210900000c1c1e403260003040c10003014a1245051070140d41240d02031580310300305a10341003510b000c5800030700346 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 261933003 1250 261931753 261931757
    0x30708190c1d1e2101060f0e010503010e07091802060409140c070f031407020306070806030601090608030d20040b0903120301061e020c0d1a0603010507050d0b0f0d0b040201 76
    0x70308501c0500340528001191011191981080f03186003c0e0b04000140d5880c950b055034050f800c034042c0042403800e45940d40c0c0400140e941600d0100900f01b0401051030150800310024403001c200b001600e41e94500f20701803901100d6561101c090000341e0f000322030361101d501410032521141d81c0c4101c400100000700064000150110003d10052044022a548203a1090724003030403010540781110b140100070010140d81204114400242c0e6041169a10a401c60743d42e03d8107524010041c1400c0172010b81c06424030074200f080612010101000340c45900d011004000340452600301e80068a020821040002c41c40008021400c4282a4014036003c401a8111440d0f509440c9041c1c41d60300c000d2003803000144014002da440340381c1189919190f455588110740000f1410b00004004c50182e00003101d614503000403400381030f00c07100741c4168401400c0b0300812403860481405002031181d9224151281c0d644c0c409034620f03039075540740c40c00c601c44050706001800103149000d240d018000ea800b680 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 261934253 1250 261933003 261933047
    0xc180905061c120c03030f0f0b010e0102340b0c280314030901060f080a05060a06030809060304030201020c07140f0301090c09020c010f02130303110303040503030708190c 75
    0x10315018040940c58985501c0a021080f0040d51502101c5404202408030101512000c2c40f00c1116680c1c000c010141c400100d000490314001c034005441e58180303104d403038155040030700012100444000e052140450b1030b1491000c5094000c000d01c504083c42d08800026803000c6004280d400001a82d001d418481c51481184c21480206550403034104540c003c00154a51884404000340c1d80081d40e0001c802030000300d1030740d84804640748441d0302c40d0081c0c4103981c0003a00c40814004100402604601c00d0801000614115120001c40c0d201d40e43c080c0e40030b031000002180800d4800d5048800740200041a42c5000707460f1904904034841c1000c1c824891000d0207950206450103124800c0307600e0307102140c81400c03441d0070003d00282d08100701900d802c4d540d56040b19640c00003400184045a040784a88039024254540902000030304004080158800d204000000b480003040344d4000076603050004c1186e0f80c900f5070510550700349101380c060f1030401403244103150f008403050b2542608800314030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 261935503 1250 261934253 261934279
    0x80307020106060912110103020702031c0e0112020f09010e240904140907050f06041a040e0c0c0309040b040608030a02010606080702011e02030903040b12060411030c0d0c18090506 79
    0x3000c00d61746100c041c10b95807112104021940c02540140b5860b480501601d820008600354494504070040c552000b003070a5622540203581d00c81350b006122400345000b18100203110b44845130b14003c03082c40e02c0c10710144024005070ad9550b2601554201d001c8040c151803001d4a42103803150ba0014000c072401942040c6410503010b0369103481a21480000780103000d003525150401c42018080c0200d15049032042101054154804044100ba480b182c0425590ba9180090180f0b44180c003c0030704100b42804c3c0596080050007000322102c0d001d0844000c0b542100103400140100040e5020b44c03a503100008060b03070841e406400c10b01c2100d1030f540f112074141d654000c040e800c1e2003024407071440086d4a640056211021980038640040603e4116820580c0316884d9500c13561120104451400e0f440c0d00300401c1f440c16002d01a1039005000416046d8101000c910500c1c0c011a00e4620030035440d8420501082c1c400c1c040400707540400030307000705125650892140284402d4800d14010441c0007003103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 261936753 1250 261935503 261935519
    0x616031205070f0f1e0806030c03070f0e0408040b0a020d23071502040e090a05010b19030206070203012702040b150a0807030e0a0b0105100804020306220803070201060609 75
    0x2440c410342d0b0540b14901c80d154071410440342a82c0107110740c4180f01102c241031300e000020200c1644000d1030350301d69100030b0078154101490a00b000803038074440c1d84001010b0180f07000f80d00c0190112803004060a880344c85038680220f45000303d820118204001151101c8807990003c4d42c02c0400d4060307120051040350600504981440240300020400c40c01c100700070008900e14036101c2da14440003001801c041e1280601c6000030010742c2c020704680d20002d042004d1003801c0c1b140d4080e001c0111076840c405100000702c400f10a48070321001c1d00c148000b00348541552403e41000c42c01110040034024040c003641611107a07481800c0d8180c2c002c62070700340e011500f0305005664442c01c070900d00a10b4180328100e4400c45071500024a600105602d51243d5000c40c074040007002d444621909011a0039810681448089400c0c1096003080004690034407003d80c4000c10040d81103528100d02280c91035588980c003600150030701008144000c0001004821603065001c1400d40b41a941ca510520381e84040e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 261938003 1250 261936753 261936761
    0x1504050c03060f01091203020601061701080616020c210c040902060f130e0403120b0f0a062303090601030b01060c051015230910030804091a06160312 66
    0x20036a2000c10114545240c11103002ca80740394149030413022251508840c601541704080101c0140c4d201400500c5542d400040c16201818500e0a60340b103585403082c55984e9280c00b40c80c502544d4003504071003217114400c1c082031100d0f00b0042d05041203414400380340c481409104c80e07010203a004100c40c40f56645090f0181d48400d03030f0014840c5003086103134085203420f5480101151008841071a002a074150790032001445a4004d8413280031542c46101080306031002c0754101c1748215407810404000e40d0300c000e1510f05407210382c90000c000709140e0582180391403c81d0691410031402000b0014142c1000640a05903480354171070f406180da81c0c0700c081d80c01400407080100281c00024419420200a900480340c0050150500301550f554960160354001606401034a20200f1a001013050410703003105d681042c8500c041312009451516440c1c40790280703000e02000703203442c6d4005100f24502140413005050004204039a200151001e0641d10500c4410842c0400d0701e400445c40388040c0d07885 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 261939253 1250 261938003 261938011
    0x80316300608062e05130203180a0308060a05040603120c08130b0c0c010314041106090409080a030e0c0a0915050411030709120b010b09010c0b07020f0c04050c0a2003070605150405 79
    0x1190760000500b100046c17001e90030080454105005240b108240c2c3c100c00c00c00e00408a010380c075880140e081801c140098002c0c1038025500a6080080c2000002c1801c409401e0441552078845030b00070440c40c00b0140352003003400c400c040340340c20040824810711203001040d040c07003d00121009004260015802d40b00b0101d4450240d0b15806d00140c0030440306018100c803401c0060160349401d01b55000a02200c034190300c16240105c0108407401d43c5034052086079a0b1460600040481103019000148003007828001c0b0055103480f000b1902c5446c82c1e880c101c0d0064100180b0900180c02d0203603400446400848074403001428900000a02c0200c05a400c0b1b0482c1c2c01ca1404500c6a0902062840e180c1c0051144bd040010003501600405e84803c1e8080c02040310398017415005007242c012500d080d0300d44403400d101c0c42c42c05061007402c1440c641122100b6806040001c21000541064500e000c55180c01081501000542c07078100304065022601c0b500320079000e80c4405184105100c1119001c035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 261940503 1250 261939253 261939259
    0x90108010f050d02010c060b0324060409150e010908030405010203161b021e0909030c011103060604170312010e070f03021903020f040b07080316300608062e05 70
    0x3a03561070141d44183e06c00aa92406140c2c00320307038005c1060100b4600289004070f0b03003000c1c15055480c410313542c3e201081c6400c508119014083c42d886915402116990610300d4100c81d40c0d1888181c1c80350200b90007403010a600954074584a00c0c1c28140f49010b50300c102c41d1102c207554a1100722001c1e81c080e0603081003203410322495003e031000c3c0754240441101c821717014680c50450600081c50079941c240c01280300f600100b0145884030200740c210f40c00e542c02600508159070303061040002a89950742a40d04580d0300101e940310a0442100550a40c8111400c04400100c140004a400d03080344280c1c502840055807030400031000d41500700d08901a00e60160210801c913034062006510039006000c166404111300c514103a551000002030b40c1c82807100700e1300240d001c002c20412601c0310405092194407414646d01c401d00120401c61440951000b0034211410340c0b1600320270a002e80e000d000903081c8a8100c0e030700d504006503184401e0826072004807151541a500d904a80c8002ea07030b0b00116000070b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 261941753 1250 261940503 261940519
    0x50604110a08150402210f0703051002070b0f0a0e060a0c140a1d040e0d0201150f0515030c07141b0a0602030d050c12010e01090e03040311060c15010b090108010f05 72
    0x50b07081004a80740180c0c902d00046c401e00040100800a003d4000007100090050006900e149052030615603003a061400320b9105111090200380d106e46001d41c002d0800c80942900e80d00c2500c141d005148400003110b6a201e098100420000c0303a501907120300005845010940420701c203190098032500026074002004180542920712480b8a042d000d6407004002041800850444a241c08900e215140c0181e450b40801500741440381414000742001e02c085011f5a0304007800306104d01d810a0b884003030901c0003c0060351013074039102901c1400e40d206005140d4203c02010301540c0340e0121290004007100c88600140900c2c060740b6202c100c40301e98001d141003c5a100e18107000348030040c030321014100b080004000c04c0742d9850515020b40f115408900595040c001000704a80326503842c1005076100700028000704420001100000c001281c0b200c1e42c900080d00083c0c02c10b84504582281d286150b0008900e056110703025201d088000c0ea00d01c519a0791b900d6040720b031318480d071046507004808 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 261943003 1250 261941753 261941761
    0x10f110c2a0409022107031406071403040f17040504050a09020a1a0408030f1c0c08040b04150510051201180311031207050703090501030c1d0d050604110a0815 70
    0x95002400601e00050503025103819007400c07945c40a000041000c100d4000440c24810400400c3c040160703d60507030f005000a180495000d0140039142801500c00c500110020341000407842440002540c000100c40d810308400f490344580b82c1050007410700c0340b402c100000301c26180398072581d2001c2d5001030803410300e6481c0c55401449005940d41e8414240c0d001c1001080e140002c0000306540d0bc0c242100540c1d41c1c4038480e085109244884443c102c047c24042c07241e10059000b03000076002900311024030300711703104d61070520803c0d80d81349216080d1505010410110075481e00b101300403148160b6500c40584032401801d4203e600c180040e05c109a0800190004a80310b0f04607000031021b5501100d00c1d206005003021400754080315104002280021050f042652005140000742000c0c242070205d0a040b090140807050001000044511086008451a030340e00410f80e07091504902696002d08280c101111100c4500100c1c80c060100c1c82000501c5040024024480568049240c649a12 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 261944253 1250 261943003 261943009
    0x3051e040b090309061201051005030c0414042d06090209030703060b031f050103031404031a0702120f0d0e060903030121021f0915021905010f110c2a 66
    0x5010341036101c20b20044c004120b0030780b102d0004080c940c000b10004001d9614110401c00c0884031213a0030380400c03500b4000e0086040c10b4509560a4a5541151040344082c6401040050034088112024401c00141003002c01a9036100244840b000543c2800442e482d0513019043c1e114182540d60158481c0c0801c00c0462a42c0d440043c07040c500500f1b407800c041c1a0105400c000c10036500c4640815510302c010004c064000c1408940710458106070380c20246952a030112900f0700101c00480c0c1e490300d00000b400c0600c28000302252017800c52a541d10f40c804e0119a03482038000580c800c0c035061038465a6140160009a00c074881e155120045140d6030901801c0c05544001e0396004c2c0544c25403a00c10b200503600c0b00050007141c070342401d40b041040c14425006041d040c01758001c44504035010ba04040ca00d90210f441c29643c041407061098000b0a850420300602069015800311460005081e02e0b1528800080c4680d949180460758030340d480407280c6a81004001d4801d048949400d00f90940d41 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 261945503 1250 261944253 261944273
    0x60906060605040b0d4113020915030c1314010504020f07230607051909231203031512031602090c070203100b01170f0604050c040b0c030403020103051e04 68
    0xc034481c035500c0e586c0a1105486480b00b01001d003403445a010f09107401214916405000b6809002041c24414a42a54010615440d0050300c812610486c0c0441501c80b84c0302000b5603507250b130000d040c514800ca81d000e03c202c000c00b90f40b241c441c401d40300407000107000d01d041c1c002c0e1444403441140300c601c0c00c1890f0f590403c3c58114035405d00951175007080b80850bc007600b4032019100344060740b00e02e6030318451040068441000100c22505004540c00244a014407140c00950b4a10224003800b0703411400900183da008a00b9100542900c000070800079084280103807401003540c181c4401c41440c0e481442c0b141c49020346281411101080690702c005803421041454000444880f154075001594010a092040c003043d42040c098441c2401009941c3c040d4078002914901c0d04450000c5c00c0001c0e4401c841e502c080e1000703201c0d1ba00c6001080003030440c241106c1c002e00414104565076aa20b1080e41d44903005440240d002c245000005149000d01540da0501000b0b1b10802020640c0c950361a07003001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 261946753 1250 261945503 261945521
    0x30723150423100c050a030c1e030203061206160206011203170c09030105040c0608060301110f09010203160c0905010b030f04020d1b0b0301032303070f1707060906060605040b0d 78
    0x140b00300340900c1842d0840384100c800150185c0c3e1100e035114030004010707081e500414048400c205000d90b00c060000c03140041c10110f00100d103405603403521303404001a0900424040d00f10980101ca0034001d01a42004942c500c11006400b920341e16a81d40280540410b0060b001502042da0100c52109000d8038540d66a4426403030301040c0d080005110200b400c462084404541115a02c5014400990032035009a8000c400324000c1c45103401104038603010b8003800d07250710710040c800305826000703038001d0040d1102003203403444501d0003519609161140001a01c1240c00c024684000440d0f403c0403041245e10425030b480070b1580a894030390074800e9018005000356a614214080b90030b00d0b004d1483ca100003020404005501d95042d408c01c9241d07060707907041981250745030103201c6211031004000e941145030880c0700044203c001c2d01b03014000c81c00d12601c03050b1420f0001401020429140c0c802c400c003500940702000016180c080940d0544102d0150901a29080c40303420610041038100e4440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 261948003 1250 261946753 261946823
    0x2031209030f03190501090b0f010e0612090d030f051005060a02120a0504170316030c0c080a06020307030c300605030303040f0b07031104030f03020307231504 70
    0x64003100b5468038403607801c292079a242c9040420454040f22400d070240a02500d07250204000d0b0074415000501400b401e14a800c0c1480b582080c409502d030b407040e080d01d22032203814540d031880d46401c0d0102a147d0f1190407000703001c41c2c6466262556500c0d07500c07626200e8003003072080c85d00d00c074200400c101c09a007000550130110301c1940710700e44483e03400382e0240180c6080341d2a00d0343c80c0c1e41006070340030b071144004021202c10382c0700f440b10400d4040d02c45d20080c0d1040c0c25003041d902034040313814200b0244400d5009080c080c0301709100c50042000781d03401184101015901041800c952000868600e00440ca03600070f200c0c2140041c9a00810700c45001e5807041645200060040e41c8030b0210f41160000c0314255407072040b1400704414080740060300c3d0b921480c1231508001b080000c1e80b1950450240c0c1c04003400c03425203080318908041c020022500781c150030901511a414045048103661103042105540600445134207000d0341c4103040b20603000315071020030b010301c0c3c15540c40c8884461004130880c040d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 261949253 1250 261948003 261948007
    0xf0c01021203153f0d0201090b010b0c100207030504230a0501030b1318170a09031b121104151d0a0b06030a02030a0c0809150615041707080d0203120903 67
    0x10f009240d18100031034103024213821022507a0b800103500303044072882c80b40c0540e4109041c0400081d41c0701d40c1d160544448260702600c64426070703141454010186a0211300174170004961040c9a0020050720889403000106011001150100d5529006849407150868841500cc1c0410741c080d4001c8900e4200240482180d000c15421039000c0e104100709440407428000f44103014840701080b25900c2c445103401031443c1c6a52024010104919440302400c1603241241803c0d0b0566224403c1005009484405140d06460300780383d40080005501c0911031840c1c040981404c0480f4144402201c0d1181c03100488600124020007a01d44001c104010f03040c0e5503880070f07000d40e840384051800340d1815400181c0ba80b60000b1500708980d2070b000182e0078001c0c3e00d01003010381040000c00d0121106003000d407c100e5180c94000c02c0c15040c608144070040c490208011031009548201c66000f02c01c000125420555a40c00300c0d600e54515500450043c3c00420501006002520243d40c10019000890f4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 261950503 1250 261949253 261949309
    0x150a060207140a08191b09050604050f0601202109010905030c03120c0f06091c080f010504020706110c0a0605160503010509090c060708030103020118240207080f0c0102120315 77
    0x846d0119541c0c00240000d5503070b5090103402c0c2028801e070340d80071400c070030f1750081b0b030602400180880558001805007101c000b0340c040c2d013400c020301c0710f64004281003030303184402d00545020060300d410070907031319000076828580040c2c0f514000030f0b20404040040c0117019610104125240307540e100701c1c2000083d102d02e43c07100c03031201000c010b900e00c40c0910340007410007500740d000300143c4070a8003c150070801c5101001d021602d00c42c48910350455404a50050341d405e424903244002c1e103c54850040d00890210741c040c003144012801002d0300d4403405d01080540d641d01441118806c8c100c04040c00a00148014055800c1c84d0030010380102e000400c071164028801d0000f0703901e81c4000f00c107c88013800400104110b581041018a403c603c01c840803035041d0070b1109a0a034945550002540e40040d800c81c03e000780c0c02400880c01800c0540e081d41c41e20030030b01d100c241d511401c140803580144200000d054130113605d0000c0c1c0b40a080311010301040f5a0080040105003d002d1501c45501c00e1039101c48 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 261951753 1250 261950503 261950543
    0xc1503060b0a0801031511030703020a1101140117190602070305070b10033f0905210606120304030b07050f0315030f03090a0509150a060207140a0819 66
    0x2d403a6854480d911a94250305610b020182a0003c0004440b060b0070034940303030445560502a43d40c052920710b00140c84000e4683e08446000c100c1d020700c142540703864a841115480740f035100303043e11400117803240b81590305c0c200301c1e0b80d07840d025101400c82400e00c000d07603000501580003450214041c0c41d20504000c0d041d12070000028007a5008a841d00c001c000400030025044040100303104000c020040038403015000442901c175500c03075900701010490607010301c14041c2c0340d8040a490050103219150011558241c0314014490729225140f140400050040c50081c9144450180210117581804c0c40c595903a8070418018042c5801e01c1000c0c02281c403105002c0c1c015600c201e2a2354214201000d9040c01d0604049195000b1242a003041181e08020303203807061100c044510030350b10b04032203030b9541d1010045900c004c68541d80c0441012400104198000b99481c2900c91035241c40c11500400c070700300421348000f8402c2c0c00c0590400074040600b514000e04011b0b91502924040c42c0d90300b140100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 261953003 1250 261951753 261951757
    0x2a150c0f0109060f02030f06300a060e0c1302030c040b0a030c0e2b0203030408010c02060103050d0f080a050601021f021c090b01171c030b1c0c1503060b 67
    0x100c0c8603580d03549410b681408410b0041c4051070007010b008614606013495980612040103000328043c80405c103084245043d40701d50840c1c41114007001c1c550200c2070b0b42540382c80c1c91603004140c4a56007014014031f0644070106448800c7d92008140c010100c4084070031340f001e504010201c50040006000014800110500522100d00b966800065024019802405000b45030740300f6406030500ba09204048140c500355000c5034a2509000e01d40032010b1300c0024038520454100c0b4145509220200c20143c1d000625a41030ba0301c00c0d02515243e5008107800c460074651003200c94005099200424440321035540200d811003418130541c2c4000026441502d1100c1c0c80c071004006541d030005d4807900500b82c030480b0402c20798548400303007d010007079201c409080f10706000e01d81e1600003030038010f0b911180130080021030f440420b4020585c8120404081c0080603007a0000d4010440103082460448410340c1ca00f2200754440e4150100d241041000d4858801c0051042c05245d03031440081510382c40040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 261954253 1250 261953003 261953023
    0x50903090d29010f05120606031009050c030a0b0417070f02010302090d0b07050c010c0207030c0618170106030303110a02100b010e220b100e0922142a150c 68
    0x40e0451a0a24000a1201b160010a0703c25450381102e028802d4542d0b022074501c4c015500c0001c040703011860741c101141004090b4012076410300c1216843d000700041201018415030040204144444101d84510328a01c40d52900404404a01517004010340c006d47c0688080b000241c0040c21a5a01d9036451013540015100700e8003046003c1100c9014039000d0145a0080f07600784007500c1284c0c51642d540b02240c03494010501800313840420b9507010070010b51034000030201c1c000d540c2c444101c0c812009009000602080e400a4101251424041424000c98044e0b03403071a4020010035a55000500041041035003643c10401008001100c50f905c9500445040c40b000a204964040666000089440741c0f100d690142d0b840c1d061004039250017608295000e80d007030f01e6503030081d0b4641440000e401c0050112408094001c12000c0501a04403a480480e4503036208440080600200500380c07502c801d002440880010751a01d0340b1802c100d030840c0a0302e40b000c8089410b2070852810070f41403581d00c02d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 261955503 1250 261954253 261954269
    0x7050d210c02010509012007020d1a0103030513060302090f13110f090306060a060c03050a122a0504050618060d060e1b1305100c02031204050103050903090d2901 71
    0x413080c41241c035020b214485807520100a40c81900480040c0e02405026008003e4417a034040740360310301440301c0c8008551202c5802461115150385a01e009017941d00302c00340d0319442002035600480c4c403d0007442101da110300020f140082c582c8261007007169000c040120b5000b02522031813410a4084010080d240c02000d1032034582d01e900802080c585060802000c8901c180340801080007581d40048515070455014075007981e507028042810b0b207441c0696a040201a441c1400407245071030303481d81481d10801e0b01c052840140e020640201c601d070142e8001d40358040002c00070120b02c04100a034900540d8800382809040121190441044800f075500c0001926010b10400c2410300075104501400348075103c450b414400305441409081e01280645406005c10b080481c1c01c1e41e005002030181a50f0003401c856079902c16541c0c8134402d4004d4400c03213010900380004503c009001006a40c41442c004d00380355030405987d1144080904e98900c0d07203003001043c50740c0d200000c0016480b140a44644 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 261956753 1250 261955503 261955511
    0x2150a06180c020c3a0b04031805030d03020d140103150b0d0213020903061608041e0b0a020a02160305190c0801050403030b09060111120918010f091107050d210c0201 73
    0x1c06840c1e0703180302d0b40700140e03c0d049100402e010009944141c1b850300541c02d442c2c5001c0180d4441e9094103540d8483e00107607410710640b1500c880c141d60540080150003000c4034188458640501120080807080c080104010300c003403403903000c0440d140d01c441e00d404001022004e0041064012411440007000e10b040001d400041c400203900742040083e41181030740e00200c005501d81940144800c5018200030004c2210b9511040e0304260381100310101c41d041070110358941030013030b0740e94003d40c80003130810050300482d2401d1000d10054800f010413a50000080e04400480c15142801c88100c59021681000c03203510110f03200d2000d108052240388203441c00103203001e424041100d140d100804c900d0401a92100c111034a10000c921458003141d00c000c00d580b02d488520014000c00c0c800103040748515461000010880c44040780201101c030507040c1046007150454000c5814850b504d009841e550285002202180c1720f03c104c408020b900103e801103047c408008070007900e40c124001c41c0141e440f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 261958003 1250 261956753 261956809
    0x5010f14031302031908040504050402010c120207030501060609120602031017011406150a0e01110a03200d17040c150305041a090703080c0a1202150a06180c020c 71
    0x100074521110005403034454005009a50303403061ba21071401101d014540792004a400c5900030780c10003850703039880a0f1241060039040d00080d80c5042a1109480c40d40c20b01c1c4000600c640500b012a003a101c080c11541c1c20209a910380300060b40c0041c0501422044840f00000d03180c01c41c5540c000b0400056001081c404e00050440d4003490004e400d03544501000c02c44103440300214401c464000485043c4401400fa1050061f292550403890502d941e0207141130030000c06500180d07841c50009030b846403404110710319600e02d640301011004580400c0481c00302c440c1e103010025015500510039007460150588801c96100300701501d451003000b00307446030140030030892580c035040100d0f5000e11001095203494580b081e516426840302400b074140000320ba01c100d001c00c1c0004651150080400584880300b008029a6054000c102d40700e842080008104005803901520088033300003692841e07200600900c0070020440f8150100541c441c2c11a4210691161855134480c05015240c088510038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 261959253 1250 261958003 261958009
    0x30f0a0b011a0f0415020a0204020f070b0c0c0304052101111b280f0c03050c0306072c060706060f150207030210030b13060816081605010f14031302 65
    0x140c10200c1c2820101400b20081d43c1c0d81035400d0f10b046503105001c0d1101604916070076801d040175040e010b504240001050307246035100074014400c1c80d10a140b451000d940f4988851036a010b40e0150040315003040004010900d07200c0790b201e4405a140600ea003c485148011508440d0100b00304600500c0100794103840726030000c2250024000744015100036010141d1950a034109484d1840514032014481c1e4107211204080d001169480844222041c0e140d040090341c3d03000000c42548281302c1c0c0d10000b1500c500c00c00a240c0c040b40c40229a01c400f41c1081d12480d10484542000c0342c0044041c000040440d845006001c000d00c00484a805400e00341080800c0710041070b151042598040e010400c016115021440008505440c2c00112180c06000140019601d505080c180700e06100c0082a80341c0e0100700070304540c0483c0c4805116566881d08030380c44034643e10405c9240c0b03a81030030400465020b54681c41d100e2049207403a08400104c0b00d20044581c0041e42c013240c04401c502c4a44003181 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 261960503 1250 261959253 261959279
    0xd0305070e0d0c0e0a09020a090e01051308090436142128030501050405280b0102010204080f07151403070f0201110a11070e070f050702030f0a0b01 65
    0x1407410b8036442d01100003030700c5422a10015200d24100c00098400050302940c0c0c5601a20300300d0347c014003000d0000d503100c6030a80035018850240405500e8580031079201008035802400c145c0d8880d0080e804d004155007040000d11144403140717450459600e14011415030b0410044c2c1e00d004044101841c0c8081e402c00d2091624003140440b1541d000025003544803903034460003070390aa01495480d545000c4c0d9036601050701d070351022240b21045103096180390150950401740c1a81d005a5080015030307034802d502200d528054140310000b05c09004d42e00d4078501d50703802c110542c0c1e10600015240c40d6458020500e48940003465080d160402d4034244000388400049051031509071928521001c14081484820301c40907046101f0710446001c02c102440c000e4008403000103440c405281c8400d00c401c0c0c00740603000c000b00180154021120b01058280485500724050040c81e5940c0c0c111800e0382d0310944071944401800d0360702d0300c1403c084402e454001c00102c40c40d01d107c3c0004820301c2d403420a042010f2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 261961753 1250 261960503 261960527
    0x4110c07080c06070b090c0607050706080606070809011209021f030b0402041508070201061d040212060708060f060405040204090b1002010b03031204080c1b0114030f01090c020f0d030507 82
    0x1607048504142107503030701c0f02e0680d2035040e00030740f124603652100d001891034140c8a49143da04030501140321418024042040c00844035544c039004a00d0b40e0324130410001f41314a40d00104094001e0140780d040c0d503c1948100b03010201c5010003e0f40381891340010f1540c01280000ca294070203880c10220907070354180507021054500b034074190306041c100703941c2e851824003403c802410040c40303c0008060394400d4102c00001d15001001c8841c040800e490540606011a41a4080c0c079029050100d50340700024090f1041d150795807141070584a070030401c640e2042d08541503501c01014800481d1940e0f6a2000340000e00308840005400d41e004070510444004081c900015645064482e0050f92000300890700d4020f0000b980611f19030701c4d4605001980034a40d00c220051048041014162480800d407400f541c100340c0710224a118649920340d564482242c0c0608524140b50042080d0503007074200d01025034950041c0d9400540000b03030907103051880d44c006000640c80310305100010380c0140f4141c8003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 261963003 1250 261961753 261961769
    0xd051b01110606010324080c15120c0901090315020d050c03040b04080304083c0a1b0804080d09092901120608030c070f06080702071206090204110c07 66
    0xc00500e00e038406032600c00c000c24050602d500c42c200c140c1d0443d60241454402c1c0c0541c81041011344d150001159200e030751a840c540120520158152114441005e440d80001e0428484102fa86c0d880306402d942d4001ea003c59060000c0690080b0002d03c00c84000a40e801c8180b070010713191000700b41c0749019688050700c06010740800f001804081020b22900383e600a4000c80d0050352903c59281c502c0040c8940800b0741040f008070f00c44c450101c0040c40d45c00c61141850010103000c0d4000c14580500b074840e407000400031849021201c1341c401e440c000750962a80c00761450600f8550b68035a850304112003000004001850341c1070601081a5900c100e070380313800b5003620408200424420100c480c0c00c10040260620403400c4001e000d601c915080b400180450300c01303072500c0c0e10b0003440865a0700c0341800b8000160019400c0400d0b1a072007101580d214408603401003100c00c0c500382c01d45c0680c1101c1102510001d4907180081e0141c2c48038090039050700200e049580c0d481140070710b02414040941c02c00e100c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 261964253 1250 261963003 261963017
    0xe100c09030203060c180d1a0604021603080603010f060f1802030106090303030213091a01021e0307150b100915090311040b030a0b100815060a09020a0e0d051b01 71
    0x10240e00c0004456a101c01c1c0c68089541e111061390013411b0504507000038643c0940c90b0301411080115030001c80c0d450035110420701609032640130810040e0300408280e4400c64146002e2440071038800c003410b41e040a4041c00001d4450040e41c901010382e445900140701c1c03044a400200b0400d803c40a008001c000c04010450440d418140018203403c09484040c08040d0007248018050480c02a00e50061030b20810411040c01c10f0240c0b0000a05845c19a03405805004680981c0a0301d540f80d01d030301c10790008042c618185880e515512150445070f014081075580d00034582158407a54211035410a0701e440c2c0c40e1016141c01d0308003001c00c4051102e10100b01010710304000294032003150b80c040e0241203501040d010042004a841e01c401d015000c1c100461030400e021012591081401c20b568140c410f65600720040150403d181409680458118501c1102000148501d50203010351b8615441c203c41c094101500040820081c1c034006d07280c5421482002581810040075180104400c1c01c01742 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 261965503 1250 261964253 261964259
    0xe07031b2702070201020f060106021f020301030210031107060c230903060c0906130b070606061106150f0907030c03061509150513090204140f0609120f010e100c09 72
    0x1502076001115060540760041258001c6a00900031070704501410400ca440230760303403030000030765907030342944404c01d54110710741c620350750300000d00031241aa9005042c190350980102c0d0b00310006c051211005450078001c1c484400080c60501840591628558451020000021142c048078007064900360310f1b51410445070009807800725080381c0c4035406000150300d070820f01c004280c4601c01c0100501c5c88c002a41404614120914040c1140c54040e4404100058480300e007601c1000d401c4081402540c4940005000044100058201c0084c0601401004000c0380045514940e00340d81d80300200340c85a4800c4c00061345403107034800030102308134011342250700180050041d0300c8900401c168541048400d03c4000d0042c4120b801450315214030160b42076480103004020740190003081804d000d0011900c1c401c1ca0310171540703805640000c1c40f4a19043c007200801ca00e24030010b44441090040e00850140e45800313105580246818070090304004185000701d5088039101c081c414140a0010001c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 261966753 1250 261965503 261965549
    0x2705010509040f0501061a19050304030c0b040501090b04030f0f020d14031b0705031c060302060409091103030c0708010e0d17070504030203010c050a0f03110910030e07031b 76
    0x801d411607080f101d51010210315040590250001d5000400098541001d1080f03894103000145008000b41c0407110384182c04900890b65448181d402034000340f1200d41c090b000c00c12402103660440d2040d0b0000440c0d1500f40d44110810781c0c215404e4020800c00030320395500681000520040130901e10143c078032071030b00a4003d442d40c0505c80c0000c5400c1808000158042c0a0201d400300030429095290340790811071401a41e282e02201490200760482c07054030f08034030307028040c10094980c01018182450f05001d220700c010a0880000e036481c1820b10b00078541c9840500040c00c0e000400d1020b01221030812204a013076a0500d4441200c0f640320526072202e075544450804660020f0140c00849501c0b5103070100d9503401a500003a46c907501c0c00c1503101515400078002c1c548881c1940303502c51076511038502a01180d0603003090345094034003040501e06904e4020060840c103206400c1c00070b409001c016035245030110700c0e0812103003104550380700d210212064004100a207801040800d450200c00c0c40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 261968003 1250 261966753 261966769
    0x6080604180503040b07020105120c1b161503020d0c03050618010b0304020f01090305030f030403080916030204021312060b010e09070516020f0d200a050307030215040b0427050105 79
    0x24040c1702c2e103010900f8000c580c45101280c900c219180d40c3d1481c0e0b410000c4016080b030348150400c0500350341c02204566021000b04031030501403040302009032900d1800c039801810301070f29041c0d9401c05a007002904000f00d44c0d031080120103212940c0c0080e00d445c0c080c080c001042168400b49a124641c00010405000b8444c1102e074840d6040d1130b00310020000c030340181c480c050309800040c800e0102140e18400340c43c14001461081d8029a120704c65500c540001030f4858012100040e582030b08003000740050b0416800500c444291101210a56956514500030300c40781300030101c400d02e0320341070602c01540c6d0103266940b071000c04840414060a1550300641240306d1003001a9420302d00415041c2903548245001c0c20441004d0002090303841c4a203401c60658441650821042307140c0104070780e290900300307150020b07030b0006002010307444d00319001c11030000d4203000d4414a140c400c020119885040300080e000810915000d0024641c0d503a1161902c0b4003010f048041051500c801008541d0b00e00340 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 261969253 1250 261968003 261968009
    0x2010606031a06070f0506010305030a0e090603060711101e050f07170601170408030402040509030c0a03081329010905190209010309051b010e121e010906060608060418050304 77
    0x2d2400e44e101114a050710a180311030001130424002d0380000009c0c482d004c80141407041440d5281c04c1402011010418000d1054405030382680c84600002e4095010304424464900d050303045074403540c00d074104042910628000703001040e5192403c20b03036282c52030045c650880e03a01248803401c0c0ca030003c2c3c02070204d10490900c501c601a45400328415900440c0d140c041c0948103480d00802e49410700b041758450b403003520128000c601c0d200c0090700001001c015500350701d02d0800546468602918121031116000e0040c1c1d59120410542c0030000c0c4140c07400020440c44007400c0c0d40710128480d460101c0a4059100c9204581030404020803002500c0d0300305007c0010745001621801c400b40124000d0000b10340040403440347d22084881d140e04051000301e904001d13070350350207900310305ca003070008000e00c0ca64045034660021503100b01e4050121695040908440c1c000100c0d000e094070340009903080390b40a000841c2e245001c1c80080e080a000f0381b01440d404004840d279039080c60383d0f500d0b942d1050b44 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 261970503 1250 261969253 261969259
    0x3090a090219050d0e070e0117070608070521010602150f060109051e0a080606030708010905071511060703050a0e161a0d020301030c050f01021b0d0f0506130302010606031a 76
    0x64114078100603036021010349010346080b1a54a031f01d030109114201000c0c0200703200d41034082010079078400001180c0c41904d80c030765a06021170311381c82425501790f000441d9003601c0b40e000e0044440c14004142e40706000384000c0d8000c204601d003ca80da031003d000c02030690100c0d84128020803005982201c03003802183c2d4199404d02c1107402c1241c984507814100d00c88140c3c0035904900c000b13000480054200d020703100803030946201c41d955091950032146401c0c0020711b241c105078020032038000c1c5040f06181c3d4010303d00701040284064801c80d400e02d00102c410030080784c2c1d07030f006004040682e40300d0720741101d203410018000c0d005075142d1504200841e00c04c00c0300202020b0709001441d926802520313105c4850750000d64072540c507032506104042c0a406102c1c05508400405002c5620002e500100c0c070f00154400f00c140d960103802e0180e0900d485206880e0320300170442c1c080c00100e00b0410940725503130002d11a00c4581e01842d00a096807655840070041605020b005484060000d065014640d021 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 261971753 1250 261970503 261970507
    0x1080a080a0f050d0c031b0309030e09040c08061602070e0108060f0c0d0c030618020f0703030c02120a0810050a061d0a0f08030703120207150504061d03090a09021905 73
    0x2488200c64034484c60441c202158146000e1400094058000c41040d41036403402e000c00d1502c1c42011800c44000c1a0081c001030809810095207003803001d244ca03081800b60842d4a00e1684a04036a07103050b20598203020b02c884145102c9407110381c180020b901400a000791260203500d0711400a40d2100050101d110446088012a1800d0010f504890104804103014803004c001c1e204090010f02841c881c181e0035810040c004401131070544202c5c0d2a1036882c1607424200b0b40c86440440007003904421100a41c0305175400003208082400291424007201c1e034803500d2074070b030080d103001c40410705900081c01415158028041103030403458503120391040322016001c0f5440d0348001001606580e11551400350341070404100f401e404402003140d42d0080e103030070070f0b10b0070000010381c224454850b01400002480d20218649003d070781059800034081c003404a5184075030203d9031550400011401c0e459030000a24000a007400a060401845190310071410401d950790b0300060900d80c4000c4001308500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 261973003 1250 261971753 261971777
    0x70c1409010b030f18120a032a0f020102070b01030609030f020f0c0d0503070803010603020301061b05070504050601030209131a0a03050c01081b0301090b1230040509090109020901080a080a 83
    0x117510410381240c07070400b04c8246000e1424180000d91000004c03c0009050501c442442420390601038542c80d17840c1c80605103d200401e0441d0820310b1501480110354003040408082110041700a02850140700001100c00f11460041d040c81030180d2141e0964109002e500c8405c031010034025440403081c1d0f600444401c0c0c07031528508510489200800201011002140c081c0c0d040e4095070589850b42c0341e00780b158440740312041c0c9000c090100100743d48d1001c038080c056801c150b007100c0d8004806040160900821900003880e0044140540342841d07036070301e580d2200310000c0d01d1a014644080d2480c0041509649072151a00c50b601001410700c00000d0210300803c0701038601c500742840f290040d90b00d83d6110f12800c070191600c0085584903162200448286140108038034801142c0c4101d202e44025620a02004a80400e02c549084e408144070029442e00c402c6081e070720600e921400011101c1e0b080c03041050305503060708075034125400304441500203150740d02240c103481050b05044100303083c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 261974253 1250 261973003 261973021
    0x1120b06090618030708030f1806041508040335070516031817030d0b0f0301020d050f090f2503061d0d0201020307050409021806070c1409010b030f 65
    0x31801040341c0e00542e000948616204040f48401c03c030540c02c07001c3d00d40c3d5966461059640b4000d241600092501c1000001c100f0404e04030680b00c01400607000d82d04160792652400301014040001c4030228100c8801c0000309a841b4200e180000d144080000c01a2002c02110081d15110385244002c03012060200b0309090003802501c82486803021517886866091030010080280d13a400050482425076021492200304014494a680300c840150304046c00d000c84c00010340b081c00030840e04801c504e158503032140c07000e000801e031810020340302068a081645004004100050074040b90342c01011210768401d101280698499054040c4045a0340c1d0b00070194000c0342569100a10362071809400c1d04c0d0f01d03007441c3c269502602c81081a20b0f807107031745004181e0a0f80310455a0f1030010b04200814040501268003400103080e2803203503030440083c1440459040c0d40310f40415074281604071000c2002204100010043d5001034602e1000343d458502600042d00000e840c10300214071160016840344 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 261975503 1250 261974253 261974257
    0x61306050702032b020609030304020108131103101509020406050708030a140708010311010f080126010e031c14180f01060b0d0f150b03190c030c0e010e01120b06 71
    0x406983c910130040482d41c56141e03805440c1c44054005800388a002035004240401583c3c49550103860300f00300c581c1e80c1292004e4051058008031014040541c0303d04641c1c40420820840b14000100002c241c49005220203441c0308070f501011543c0c0c010041800460b6012080d02c228035400b09a0715101d880d090320303d0010b40070f03144807180008000d9040051440e804043c490481e80030301c3c6136000200c140001180c88072161480c52001c1804800104144030309942c01d0607201c6105c01002400d00b4031602c6650959403600c0d410802a0f102042d40c030314000c40c2442200070010100c408000e031000f80c022146440c1d20003000c0104c076881810520f080d2000030f1002c44e8950740c90500801c10180c803601e45042c2d54000c80c0f41c106542c4d1910307100100311103661044411000c40802114440c1d413501c84844110b40c802004800b4640ca603503004588261503026464800006480108189039150320042003809480782a07030401a50f1440240384e660072480010080c40c1c80040442c104c019280460300394 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 261976753 1250 261975503 261975523
    0x306010f0306180f0c050f04091a1f030f1205030f1501050d0203190b041103040210020304051f020105160503040f02030f0a06090203010507080127090c080f010b06130605070203 78
    0x1e00d003066440f000f0001480c040f6021b48004950f0004550211001e120440350a2240200180c06060803480141c0544444030361003c00c0c0c04800a2591500c0b9109103402a80d6004a5003080003145080400c0714600c0c980400e490140340c003d065181c080310140500c040075002c074200101418190205920600440e0001d0402040a41da03a0420320492215400c4a40140c103295151015005482c9002d0040c1c44c1d0303203c54489801d05540341d60b020401d000081c081c0b10700643c8070820000905071100030322002180013007002a140701e4030380d031006420344a000b802414a4602c641581c806aa007100645e80c0160300610303604448003443c80441e190140e410040030503807048242c5542000440c0e000070b0a0a0f2094009100b607446000c000d8480312420302902407885512100c01910b10078000c00704204400c2d20f4808900c80b4a50307141c01e084602a9081f5211a4200010100182c0003d005203202954191070940c9072104a810502140425010700030030410b000070f0180965070100140c41d07403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 261978003 1250 261976753 261976763
    0x3803160e1501030b10260108061b07020d2402180a0f05090f04060923010c0e06090103020a020f07060504050a06020304051e040e0a080a020c0306010f030618 69
    0x50a0300c403003028850400c220303656050484058001c12065101e401910303000c2c80042c09460b28810b461000743d4000f207001242e030072a00d02e80c07036013804d800081040039030007004482c011346800d0a260300e0248000000305d100e02d4441c6004c020f441d00584601b5842d8510603046686185400103250012180c1c41c8001c1500500034004607401000b0701c181501000c80034000c5400d103064075501e04411102140c1c520071254000480720014001c0c4d241c484000764007910074400040c0c588170300e695195103240b8000410107440f905804040400400740300c1c6c55401078840c201112008041d000041c483c1c03045414007810160041100502c1500030441c03a020340c210380c0103543c07606403240401400354000744101842011355450002d074040c0040111000da4101404088010100c409055a408801c094064002d5641d0f846480180014403150304094425000241d0314400309a000745480b8291280a1294228000400034015a0401c0341c007204e502000119002103154401c4d521203074080381c0500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 261979253 1250 261978003 261978043
    0x61d010e1309060e0c01090b03010b0703020a0b090a02011d2101022b050714040902070c1e090b0f010e0405150a090507080a090210030506030c0402040b09043803 71
    0x803c41c242e04180c1100080c4002c861403844000011107142c502c0744980390080404000520a1041c81c05c0242a40c5001e8012940c2c50500ca555a042c1b4a400f03d030f0488070350b0491303e8034004545e40224024440e04403814415025803074440007a5164901d9a6401e00210008803103404c224400c0d0184c6c1c2000e200f803141c0013160500d028583e144109568030841449183c040010a404e014405001c0103c900403009400c180c240903141000754400e01c2d0030b40c2c0d075000b000000106052903110342e14203144512240254a031902911000b03885032502030b94070a9000020200c0c0e581d07400b00d00b20711000d400b101c001c2000c0e1203040000026406c0742040c290080c3c01c404001c0388420b481d0304924000d030010351341c4040310f07a25200070404a0304c0e50500254071195201c3d03070081c254401c0e080190080e078010141c0c0c1c1d45081d40d00000741240c0c06640001c880240108450003145880d10034100e480140c0b2031111030354942c03d401e25000c00c02c0b04009203440c00d80c8401d51641b645003006684196960100b10308 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 261980503 1250 261979253 261979271
    0x503030a0309060b04090b0103080307050f0a1110050702030f070615150806010c0b04020112112d03250203070b0a05040b0907050a060f0201020913060609061d010e13 73
    0xc1c007400110710b0643ea46400e02224400741d040c03501c100784185030004c0c0d04040f10390841d0717100102c660014001404018090100e901811100c800401c6815041c0c0c5900324114070070b400850906100d00e20100d003981c42e1200304072010b034000c012140710021154000340c1e621540c0c41c2100040000c060700c440070690009020034448403205991500781d0032501e4150507a9544c0c401110050f0070420002e10000c03411300403400550041c48045410700c0380031741c0820a40c08400e081d000b10340005003014504150300c55203e082100f101240c003001c406030503d0919614003020511031808803504d01d180c0c83c058903040b0584ea01e00c207006903240d07140d210040040c1410160000005031405039420703138008008030003050681c2c030001040c0c0101e40001c0d0151000c0b503e00340c03054900c40c42034401013055540030040a030003a40c82d46203000641e0204c150010346179040c50001400c40050741c0241c3d05018840144040e40d0f0007140040040394801d181040300d01c0014170228060070441844003289500302a042 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 261981753 1250 261980503 261980507
    0x80f0a030b18090c01110a0614240f01210501140f01030902011d0117090d2c090604020702061c0f090c030b06011b080d05070c02180406060503030a 65
    0x2501c291600311195016500d88090041e00898207070744003c0c0c0c03540042e140c4030803540a086900480050b403c00e0720a60042600d072103080d0f82d01e29a000e04040c01103002c003e0700041300d044002c441d41542e00c4008060010002080c445198201010305010302c2d032542c0300c0f11220a400400c1000e01001060003e9603480d081140c0a0b0000c41150340700b0070b0501384180301540b00f80304138080d89405a41c0e0024288550507203454815070380c24164100200501c19000c0080c0b021160380c040d10a080080003070300401e0070002d00f003000c030051100c1d5502c01071804455a8031a0710752081c014030102c680510580325100060000e100e4104025004407020940c0d08441c00c504486440d5140f490314144000c05464412a084481c03010300101625450002400807600c007400a40d44540d06042074a20400207008900d540c02c107111048882ea000001e900358141903a0045075088091420165520300712940060103070408001c403c3c00c2c6200300400a424049540c020300c0040c070014040e0303a600c000460340 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 261983003 1250 261981753 261981761
    0xe06181c0c20030c0d02040e0d0203070c0603110d2d14161b1103011407021612080a0e150a170103050d0c1113060305060619060309080f0a03 62
    0x41901c021044101003503040c00b8503181504003140040c0686041c00015081108181c44100306907009030f0384400d82d11a80b0410000c00d01000d003150011038075a021031609801f030f02d0090708008101400c02190000b5185110190350440c40c4441011801c841411014045155500156240790300400940c03500b019207035011488210403013180f405143d41d503520041c04032401120130710010340c00b958800c0007500c013005044002d61140f220407400d0030304c5800080c01d582c10462400c4500481c10103100e54590100700110f14803144107050502d042c0313001d0f442c82c11041440c00150007031000007001c1044034440c070003800088000030420201c1c4060608020040e070002d0701402d001c0349203401e00c103400d0b060b030140c07147c102c1b54048002c0400c0719200760b04503260207103020f040b0303106084c6e16200541c03a07454001000603c0800c580010301d441c07850030401d2801d1f80c090074081c06941030f010b2a000e41455002401c05680260802090001107484c00040520030029042165600030403409505581504 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 261984253 1250 261983003 261983027
    0xa20160e1e061c120503161106160c0c09020d06080c102307050a110402030f07031109090103050d0e06040608061e04020a020a1202010e06181c 63
    0x1200c90003959900014920401144a11094030348580c000240d19240190318808075070f0701d241034084220074581d40c440d050340d101500030001c241c4c04010088041c40201d14031803d0041850000f02c22880900350586500015001051668204911050b03190041c0042c3d124668894004d0120703c1d901d412a0740250000070801c00194100140020701c20400240040a0b007001000d500005507110426a0804d000342c5c2c0c0a0310004441e268400580c4021002c0c021301800348014180410300c41c07a11407840440c0340c1070780303100c2c620600611441240e503d21250340880b0a085c001604c41662103219118020090106e0b071189800700040b0410071701041992801038951220710080951408100660181d805400f0000e0704000000d6190725089406002c154401c0c08041c02c82404071001c5000d85c3d20484410000d40d0042e101107040103e0b41115110709030840c4002c021813a208500c494440c200606500c5007482598290400e00c2c000b4803001c9108201c001c03a488208826000141072030308520 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 261985503 1250 261984253 261984269
    0x70b18060907030803010b03040311070603091101080112021203041e0e09060c030a020306040b12011b030b030a0b180a030f091d061e030d0201060e0a06030203030a2016 74
    0x40c0400c1100e040080c03401d05882e0b0145445055030b0074403d48411a0304014001d804000e500140300003d500306111241c058015a5404540810542401c1d90070844c00c0000798104000800104052206070b8a80100c040d41140d4101941002080d2145940541e8211408500759101d410308481c4000c0010720441c0c060140100c19543c8d940c226a8032034101b00c40c49292440c00f0400140185a554011a0700c46002030000585420784004142d88c580354401c1c0360041d030f548040101080c00d14100d116040501c51a05002c4c81c40140c021a407240764054004003100c00d4140030596400c034020700003502125020807111103c542c7d040042c00d144e025403110f00800d541030b0b004104590020700c1540c6ca8070b0841c1d4100441c1d200c0c00c040c0100c132500c5001086c8040050001240c040d80c00384a00d001d0856258008a00d031414440000d0005101601200e0681d18200301000141c0780441034aa0340201c5050466801c5031020303d6902d800c4244402241d0380c001c181000e9074030380300c0c1c40c451005d031a003103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 261986753 1250 261985503 261985513
    0xe340503010504030c120201110d0c020c0406030c090207020105070206072105030603030a1d1206060f06130306020a050c03040306051501020303090a12050d05270316020114070b18 79
    0x144140340c00c80c0e00c00e6401500064103100a880454070145003680c0d440007620001030342e400100d560300500d402a00f4401090740e2543c500d03001c403d904009048803480211001c00469246a0324034041681c3d0384a000322403034001c100e1800350ba001e0405c2e282c0154000c0c04403607682055240110760000704d00303c0702d00d6513000015002c0f0218072a4042e80c0c81181d019000310b02d07021500038140c1d0103d8407104c040c45c4480054007001080c0d111095801060a07524000b0500c508041c010040451810709025020b040103121340300b0186404604441281e401800060782d510204104444c40c3c422840748903c2440700190000400285030b209610410b00b20b000800c1a00800c1c004903101e01c42552071584a6000e04455408504e82c0241000c40fa2418101146810308a2024a040e69421a00090041c41c802d00e1683c0c081d00301c0c0a2882c0402c07040001e0741ca40100100b8071b020b0900941c40c0a810001c5120b04004000210400c13540035540000d4554001c0c600504040340f02090056580210301a03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 261988003 1250 261986753 261986759
    0x6051e0c04150504270905010e06060a06020a0309290a020a060c0503010b121504180c0614030a020307180b0a03060806010503030708090d140a0c14090a0e34 69
    0x2190061340c054070003a82160501905070042c90400f01d40100002c0a1140e0f030302c1c3c10500007282441482030f640005800b078030030303031502c00200000078004ad81300d1005e5400c044606030000c1d81c000801030960b02e005a803000c000e15005804400c490100c502003500420000d40410010f40018040c00100d12420050015110044048030135000a2184500079182403003c81901c40100104644c000b40fa003007a0b03610f80c1c0b45d260000d4161205d001da08203248100b030b038540041c0084104002d001d852075041c44060307000d410a52841070300c001804108619400700c08210000d2140544014400c03803404000080c0ba142c001c0804207510007000d21001ca0b14000c40002c0031203001c40d6036812100014043c60610b805070700c400d2400d5121002e41e80d40280d9550b01000041c0d8031900c2084652204030045c42200c03414980400444c410b81c01c022a200e609151f10720941d56040140e0303602494918020404203d5806980d1800c40580071035500b094003410302d44017043e482c4601d110a0241c844490034100e903 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 261989253 1250 261988003 261988007
    0x906060a030f02010f0e090a02091503070801030f050307050a030f0807090e0601141c02040314060103020904080706200a1b02030a02150d0608030a0f020105060d06051e0c0415 77
    0x1240c1d00c401002410030600003000342d070003101403803003142c034900f001c9a2000880340058070301c03c000c0300c1d03600a8690104000c950303400c0c00d500d840305165800c1c2105240d030911201c058403e00c0c05200080404cac140c070f1006401c01406005580340e080d400012100d1403055460054400c1520410040c0051907640000e500903100300c40301402c440b00c160840e04140c81e020011203a1a95014000d007051508000c05041d070082001442e0f42d07000143c50041c0c58906516080e01c80d450f0403040101030b540312030b0060000d6969100342540166011034074958a144a2810b60080e20030801d0415001030020031078048040c0090050000c19059a142855940b03d030700e400300c801c140e801019405503c10800e080043c24010300034044204113401d81e9007040c0030b64440c01c05480c3c140e04811501d800204205403102e4100c0310308041001280000c0c8018900040401c07851030500502801720368584000c11120300380c443c032030424001110302e500b0242ca00146580c1d19940700e4401c1e550100b03007a1410180e42c40c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 261990503 1250 261989253 261989269
    0x507020c090103110a051519091d0415020c0d02122503031b0512010b030601020604060c030b0d0b010e070e0a030f0201090504021c0509070b090613081203090606 71
    0x24000410307002090f401c41e04c1c1e0b941d1300c43c00200030350b800400b84140806d4035074440c0c0008280080420a05135940e400f60032041018980507807240501003070307413414040081d002070407080404a805d40e6030384d980d540c0e00300128440c00222011000920000d44038002442c00701d07060410222075000c0341c8a04d608150110754501c40c80390f0084034100c520424032800484200107a04180c041c0c40c002c00d1043c0c4e00a118568410340002c0d0078082000007070540301002e00d1a43d8140100001601707581180307003000c0042d440c0c1d400204003c11855a030f403201f04050380640e110402d01d00010340b8071880c1324042e240c02c0601c40303428001d038000340703000e24006180544200203906e080d40015110050582c070b9941c440c1c4901c1c2e024036049050058951012403642c8462020f131940c0b001d80400808910b10300d00707520007103480c00350140c4915000a8000d01c0260084c404480304440d06a5071036580d029810601c01981c034517078120301c8450103104c0310500081c0f4164085e42c001c502100c103079082a00d45408102e504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 261991753 1250 261990503 261990523
    0x230d0207060213053a1a01150504050105030a0510030b01090c020f0d0c08070c0306022a0606010e0d06060810020a020d0e012001020c060106021e0106051c0c120510050702 75
    0x202d050f4105e000701c0442c2041041c1d240030501000e158850616510100740e071180030450880010010300400044129002c2c0003d03102d601d0410624050816000801d58400103005058403501da80110b0380303503c1048003281c0110740010000704956115044000900690031600c1d005200b035a0300305110b020042580da100a0041e29820003a07503055507201104d412401041c2c0d4441803940002002c07409074002440b00380d221a040e4001840c0303c4001e041c4403070180d410003d1940c0708600f0040f4a0b41c0101d40c011080b4412200403000d42800d00d09980a4400754102c80228021161048403202842d0041c03e0201d003283c080d1401616540c404a8042e900c1303107085800280c8138001036090a080711800180c04010070005031a02401c1050300385002d0342a0312100040c0d0285401007602c00d00042c0705800c0d080d854000344030980c90080011074020f0700c040c0b44e40c00300204807455420800d1101c500e9001304021031604240d81a035080c42d5484800704d00b01700081c6d6007420300007241e003840410744e4500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 261993003 1250 261991753 261991789
    0x9010e0609031e030c0d031b080906061309080c0109020a0503120702010f05070f03090314030c0606121f0207050606010905060d050405070f0308030a0c05040303230d020706021305 79
    0x304a041d011114843d08200a011410701040201d517072a54002d2105070710880315524049034800c29480c649a110b500c503d810403c08c0503100520501500105a040d0802001c561004c09005202d80b50b038020007900f48000c3c09003100094038403400d0410f4112509040c002c0340c0300740b011581c0300c00707064464041e03030090980203c007081084010740c0102e51680c4040310314a0114102155553b07a49000e48441000b5008500303106010001c101c084d1070001162011800071310306100711071001c50743e16070000d4401031007004952603c40c80c80f0020804121440460035008240e0000210250b009511181041d900384c01810000b03600741d40900c20080813901c01400003450441c5441c4c03003500238034028004903080d001d44400001d00c62904441100514080c007070f640c5d41c0b402d0034040613044074445100328007400411b12041000c01d4200501032100004070700c00c5004a001c1c03c2024400340308045511011358400701e9a030080c8281075003d412440c0c0d01d03244c1403040c0c9840301d08100440b1064603034168 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 261994253 1250 261993003 261993013
    0x14040807290705030d180803130b0c090109050114130e0a0f02030412081005060a120f060b04030209070212030a060303120b0603010b0a0201060e090c0102120702090a0c210209010e060903 82
    0x2404d8174981e0f0102408051001074800c0801c40380d41d401d2030950081c0c510311b0f104003902142c0c0041c80020362002c2c0e0060301071090503181480400000c0c01405151207030354103101c0442c0361090140203170b000701d403091010480c412515503181c0401c0e108050058485003841c0789000134000e07035105584200c9001c0c40d0040075070b100f80303101d4031011540b541c0002c00c0300980740e0304200001150f80b2042d015103000d081540f1480d202c040000c04c45011a4010440b00d502c0358200a401c01402c0042412241500d805a4001d0fa0302c1e0740f0302000341d02d4001010807008071000004204801c80005a0012080c0c0344243d40c0c0f51248084400e00c11305a45100c20354903400f01c81000100440b646403c01815809650300011400c1c81e40d409147c1e080b12400c48e038079980b640210b048060b03a503034144003e0200349580d1100d14180071958010070031580307005110641059a4125010007a8020340907072807044844060360075103544416150005e504180b12180c00f20b055010b49800e00c2c9400402c1c0c880d5008060b0040c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 261995503 1250 261994253 261994267
    0x309090209030f0a03030204061b02090c090612040b1009051017011103100e13080f030406090803040f12050901020318010306122001030506030d1404080729070503 72
    0x100081d40007450a65040c400c000b5003254028040c0064120280640c600607142c2d8a0007802030b08070600c000340b4264245070901e440005070b486080d502d4004031413841c0103403501c0c000b4001c2402403143ca176692000c40803080421040044904506118480c05500c444045a4034280d00041da50103550410080100003010302c20344c3c0611038415207400e8004004680010b1075268846030340d0003a01c46901d0003680003401c2c01002c504404568103c044501240711541a030b490f0340c0320b507020302111b000c04c1c0a80000400c0c240040d0390882c0c60301c90f40040e1002c0c3d990900749001a807072a407844080702c1c104090800d11104500680c241ca0b000081a000b6604d45140341503110448441072600354181039455a000c06c0e0f0880c6a00e504d0415481403000300d202c200750510452440c29242d591138105424203003040703210746020484640303440c0f2909100e6000300401540c041341d40920741000b11548120341000610001041030351001413003800c40c48502415a8141c903200c0e105d40300000e030a96004104030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 261996753 1250 261995503 261995519
    0x3021e0a030e01140a081008030a0909050411060301060c061d0706140f030907060905031b040e070b180a0b0301030b160e180610030902152505010507020d020a0309 72
    0xa502d4494140762001d070862440c0340b400e46642000030150700260b0b090040003144803d291598010f0499032004508005020f98000d24090090040019181d10b80020074200714441000705c1e8407120041c51580c0700d41e1a800002c1040440c240c081d181c045c01c0407401c041d401240008046c400e00994040d100701800c200e000d880300460b01c000189101d1040001d0512619031401450040310b4600c050001c441c0303040e0b0300400c40740c10313904085e100c0d81089142c8601200c42c0c464050f00350308217803804508410340c000f103a07040c960700754000c20a0000c0000d46451219201e52442e80c002d5041752483c803015160580350007203010034000200083d280d04040344481402840081880709540f80840c0460140d1000c10b048090b02e152031401c45400d40c052284a2501400340c0c000e4622070301d0b040240100d56000a0740030300304a048170303105020000d4408580b4008000c0c4210a00c0c00b040c2e07204020740e140c681603000700422a48103005003d6043c00301500c92010550801d1503030182c0c0c8200045040140e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 261998003 1250 261996753 261996767
    0x142401050d1104090908090a150c030c0f0204140a0e07050603040221070f030c05010309020120100e0a030f02120301060f091e0e0a150306050c12011203021e0a03 71
    0x1c1c9800c0c028060000140444d40c90207001c08070303803044803000c1c0c440b0681c42c18400e8580450b00004054800380c120307803c8455006a08000311501860b24508030003113410041e50700010041e001c3c0d0098105206e4400a6080e09241d90140007818000c01030110914016511000c540c00742a6100303a003007000c2005481c0c090135034520031110311b2101d500208401c042c40c2c0b03050b229510003a8041941c4d2420028001c640b4100002040c0a082c1403002c1d4102e035000900034071100c050b9200c80046c403c4c00d0182130504220007034650b43c41c8581007103000b48030b0040a44e50382d180d5600701c0005803400c10380c080300c41c070108107441a01024440035042d42d00308407050360341e005044542410062a40000100400340c280f409403800404c0e250a820a814108a180f00c11801454280f140381803ca18242d8050515940b030100c0350801d2000642d600c0f40e02c1d4a80640c0300c1c201440018030b0807030b000810414440c41600c0701e040d1294080310194441551401d0107900351070446903141d0072104900010a0060303403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 261999253 1250 261998003 261998021
    0x2d1e020c01170a0612110307090c08070f0311070305040e0106031806020f0d05040308040c0501050901090b0c16030b070801060c02090c03090132060a08061f09142401050d 75
    0x1401315a40c1c2d1100840003805240c510107865a140d400070342000750805204190213044501c0080c4800c2c40050000741c00d2400251100d01007041e0000f040400912a50184510482d42d0003070981d100d80d24180281076030458000c1d040714054003000014070324041d120300e5009443c000c0e0325005010550b20b0303002c020340000d48102145401007114a41b100c1301403141c00d204a02c640c0701d601580c10241042000100380c0d070401c5060140030484000f01d070307030070a01d09002c860398943e880c0e550380c050850050524200155203100c010b103650b03001c0100458031048501c1303081503603940f81041e80c0e80e901c05c8405c41d52141020750000d51740404602130711f11346001950b000c0a03010011440103480c00316914410f40c44400c000e01c00f0b2008200c501110403181006070803001c121041d00722305080c00c0a50703860b0340d0007030404101c03114a500c0c00c182d0648000c50f5003000f001024010041c1c4451078450080200003112005c0c40d41d80140181c4022448506001d078050348103075200d03030420111103001c4004021201c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 262000503 1250 261999253 261999271
    0xb27180c040911131505070206040603060305060601031a060c070302060d02071a040f0206090402210115170105010806030a0b01060201060905060d0c0e06040e01020c010603050d0c03020c012d1e020c0117 89
    0x80038056189d1707100800003403d8580d00043c04a14501f00107060140c080c201504040c10325500300c92000c515000c99841c070000702c56440d1b494043e00c80c1540340c0006a40000d40100001c1a6404910031030380c0500030050003411582c49505d27805042a2103a00c04072401042d105000031840003505003400501810f00001c4d20041c50499460321990b08561100743c041602c1003568010b001d60302580351402c6012042d401d0122400107101c2d0a1007840c041405200c0c100411360300021002e60301001030000035030b00f03c50004195610380b00f00a01a159034003c0d01e80c0c26007032001040584c20441c40000180340c10525540c526410828511909800030304031365446620381d00804813261084c402000552052030000a403103181d45405400c140c40b0094030f41c1445121010000480e07004149135034070071002d28000081d03a2003090f0003151580110540c41500c3e88201511640170342100100c410050300384a0703501004100c003400caa441c40c5205065000515004414251489080300150450024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 262001753 1250 262000503 262000507
    0x907031b0e13060609021e13030212030403170a1710080f030702090106080103120e031c03050906091c0804080702060304120305010b27180c040911131505 68
    0x9541400c4481c141a00d008a010386016524003c00500e4800c920043c584814294104014045181248040402242d008045c00600f18240c0d449030315102e4051640101803241814510801c56030b0307030700a80000c13900b00390b2180000d5024550301c000d640308400d80e0341d41c0000924a200582e141c48402030300c1420354801c20000403074101c009001d405562401800203503100c1446004000d580340040c2c4c8180180300c41074005201043c08100c000c48165000c3c10005180c0d112100400e18120800864000f4035802c007008081c150782c5034000728003801c8000c0855690740c9681028948803011490300410404030943c5452481e0702174a80198007500841c13003641032000c29004036010781e104440031140c165114002444003038040c89a140540006402d00e400d1110110b103d461401001c1c20034050713000c4001c2c0b40c0e1281d660309040040301002c40501c000207804c4c022900c4100390043d0044030011400e24904a5241078a10207031150080300c0211540c1c090700c2c11090707021910032181e40724200201 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 262003003 1250 262001753 262001759
    0x71410020412121e031e05070f050309330a0b01020705041503050307060510060e01020706030915090b090c0603101a04080f030405181014040e06040b070905090907031b 74
    0x1031301094000c1a0000c2e10081050710b00860300300d00b22140c40720384c42607103841c0034103100c005644104462411520340c140f0b2581c0e0344481c600d09142010f59802126024501c1c00ca1805c880303400701058640c1031031100707407403900c0c2c40307079088441900c0108019038016440741c0310400c068a06600204a1044012085e070f102e184c898540c01d0859004080a5420350f03114000d100444804000701c200030185464101c0c40d000220000030b40f14400c51080300c0402d9141e60310300b014400058910001507000080400031090a8908a03040c2c580886088265000340400c400d8a802c08100316880b401d50b05040441e95401d00d01c0304055106007942400c1800405d00c4080b4010400300711039003076185810010354440f8600008c00c11000c01c80c5100b502600740c0d040510075850040308200d41907500120001c1003075098400841c004140c0046107403140d114050901c814052070121080c0240c40c955180d4a940d41c6540a00551040c00d954140c0c565005150810200b520b4000c0f180010414051108a980e5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 262004253 1250 262003003 262003037
    0x2031603020a140102090f060d140a230c030a02032503051902070816081c05040c12031205090c042c070503060a050919080c1b0f130b040207141002041212 68
    0xb41119802c02c0709035133848642c191107440074030703501c06241408060407525040201c0345560202070080081c081d008804514103100c141c3e103500700864002840c0079103400703d01c0014060001070310422040b0741d40d034008100402c03040c003c944003550860b0300c06140800c0c003078000b04d4202025800380d07a2803405020741103401440441001510610b21000306040c2001e0600141912181d4410b80030b2400415183c00080d030000b030700488882e800f880000303840d40e64400d464140fa0341c00a820b60f0151420401200060760081003106a0704402441c001c1c0c0110181040c1da940d019016141c0d00d41d01c950001703005030920750400355001c0f41810540c0d16250440320b44c100d080c01401c00031544001c2c00310350800503c400300700000346022074909920800c042003011038040d040d203600090180c00c1900d0100804001608030440d0300b00040c00c111743d510a40d0408100308c0a01c0d89000d1454042e41121604041d007500030344094655203414083d182c0c005035240c1c01c490b0400c44080081c02111081c40c1c3c0604 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 262005503 1250 262004253 262004291
    0x406090c030803090f15010510090e0106050a1b0215030408070b010b0c0c03010c08130203120c0717060c0301120501090b0a27050307030f02031603020a140102090f060d 74
    0x500c0780d40c900f82c403410f1141c0810f082501c002086041c56108541c010705602c2842141030469609640005c00e98681000861301710200c7d80054850081410000070030700d0348580148049186a41c1e4105a02c4480c03640788000414480040d5220030f030b801c00c080285008200941c1c009224084035481c21b46c556895580b044c009130f0101c440c2480101d08401052414814242d0040b000c0300200f01c201c0070040c2c041d04010300034100810705039011040d50110346041095060300340c89200303415119400b05204543e14900d0b40249100d980031980300e00b102d2040092038a00614030100644e003075a003460200398103150f01c680140c07020364031103c595000c00e0612448a001d062651170208292140160030300403085003100401140000440e0400891408030650344242e600d40ba1424545070440001c9213103000c0c0301290400c0c01d1b80290280300300341c0c00255a080c880d00c911400e030310762148412958200e0061030501ea80107074000c00d140c0c055140ca00018900f03010400f000140c1801c0c244130302e206903 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 262006753 1250 262005503 262005509
    0xe0601022109040518101d0a061a030601030515131203050703060812040e07050415111513060906020418020c0c060306031c0c30030203010602150406090c 68
    0x40440002c4001d214103090140300d92050b28000a03850b0101c12066007980c4d9019260b11401c17580d9201d0182801400071071115485042c800f0880d07004801d1414640e00a004006c440c0d8050303007145e1003891260a011032503034122600440609040c6400e00d034040201d500003400404580c41031401c4100103894110000c2074010103580014081c030702254050102c03403540e0002c0000b584580903002100000408403400d58481c04900402c5032581d02040c0c40500441c0c00c11481102d02e01900c400080d07128080b18026404002208c0d18403200c08848841e0754003d844680111034041c800c40d01041e06908018443c5e440781c04014a42683d610000c407014411001c2e003000141c0000c2c200201000c10032601c04502c10032a070a91950600400107551102c210584611001c9910049a00c82d80034400082c2c0f40b0390020902031414000c46050090013040c0d00eaa4060162f00c1d00d5404a845d21a2003030307074181c5100350020300052450a51404106100600483c0c10701d8a89103420f001510000f83c03c002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 262008003 1250 262006753 262006813
    0x60a050c0405040c020f0c0616030c020f0616060f0b01200708030406030b1305090a1509020306010312170103030504060c050309030109060902150a09050d0f0b0906010f0e010b040e060102 82
    0x6c0401035215a040140301000c0703520039031081c0a000c812100794001c0c1d0a089626042105142100344041800c42c0c000454441c0d112201040e41e0110720320f03a4a43c10715540c0b15140c03c011034803404a01c6001c9800701c42103680024600d1401c0310715210380310751108a110202c4103e4440d0b942d1160124070355800398000d600040d4030345d0410941400c3c0010751011404006005009a1900a600d00d40c0c4000d8414082c0c103040a480003562031269640c0503044030340e0003170203684266171a4142441184050b6080d82c000400f052024250709001c0c60960b8140c0740c0c980c1e501031810b841c00c0300403945041c05403400c0d602030108115500071540d0906c6014483c0d8800d60022030500000e00401c000740312600d0138000c401c4810481040800e5001c08810240c401c1200d41043c5210242808940400c04e44002001041020107006d4508000120f5504907009000d824411b030b81c8803500e0140f403802c01c0c491400051024031041c40401c0b105e0b001140d01c01418411600003081070050101800c92043d59801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 262009253 1250 262008003 262008013
    0x503090a0306200711091807080312090607080406021b0604050c04110a0203041a0d14010e0702070308091e060d0218040207051906020d0e0709050f040203060a050c0405040c02 77
    0x340c035003c00c00c40f89a48500d0002550070000180c0728440c84008032030210380304400302d90005112441c0c00003808902d521190481d40010b0b00c0d0384401e940c96104061101a4030320803000104004000a4094840c41d541d5544218544860380c60034065044000201c8807104801c50281d0510b80804c15640310720700a100500e05003001800b44821140d4902c00810406000c020940b825500081124201e40128664840303210b601d02202c410ae008400000010318240300300460064945035103517060720f00220f85824541c44080d400da075140090f20000300307240c100b0b200080040c60032080c42c4041d650300240c008d00488290002a00d50360019410510595010810200b6001c040420b850350719400d413011446d07c16583c545a9890600c130152031040c2442d046818100080d80d0161003002142179000e1214888048610780c07500c800d40030703a00380946048001500c04494400e80740c082c0c0c6d0050003a100700d0301c0320100c0c540a40801001050880020080014561901c2c812882002404d80c0a0300d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 262010503 1250 262009253 262009271
    0x11150c061b030615160c090c03110307120b0a03020a0314010e0a0201080103060f110c0f010f020a080c0a1b0309030b1f090209010309080d02030609010b0f03070302070503090a0306 79
    0x40c0e010492040141e1881c0d0040c01007007003d440c1c0b6109525401044203480d0740b5012503c190102e0340802000041034200e0251001030040d0903a0400c607044d00880d04c05200100b134034143c180c00d60000712031643c0000e10028060134803155030b0b4480302400d075010300300c0d001803a281c0c0c000ca4481c03602540304660718601201401007040c030a03ca9180901c1e0860064426020a40c000900b201d806000140c840c0b55030385568071444401d03a210454192a501d80b980c0c450105050060311201a500c4240f915404d0890390740000e40140708a454111041d2115862a101d2444d08006a08160481c0050103240f9030308040c00354449040c80511440b9540e040c0d01242503282444600b0320140c02c2c007055840940c80303200c40f1950700c04020251000a0801a00c5144c0b407170040303010f4500c00030042c01e407901c00588101018050303002140300c1d0200b92030302200350340d032402c0542c0b081c410071082d401c8415080c804a100c4500c40c2d0010a0210700842c1101e04200304000042c02e00b42113030b40100d445550382c003984 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 262011753 1250 262010503 262010521
    0x3010626010e030703031805010504030f120209060f1308060c2113060c020c0607120e1507030806010306091404052a2b0b0a1b0c11150c06 61
    0x200304004500240502c030b034595005030340c80c080d40310000d06058441c0d91000f8041d45090a01d000350ba005802488641054100136201d80400708010000901031601001031a48074000c45a08240c098030b00c1d4582900401206655040082d2144041031003c0e00050900b008224143c05106405809540d5031680d030400e417406c0101519107807180f03500f8020054002e17100c4100c910520341190000c02e1100000e201203060045d80c820559204070b001c6904024840b24060990074100c040d00d810600c0305002d02005a4102c000c610164500020814400002c1c03298150a40004060402140300d40d00c80800e2016980342409000c0e580110004220034031200b0042c080c6004001051414100740400c0b030319800ca10300011290068203862f2040c140340204007c011614007490300740c54480c2c0303100d151000340700d9801d65010688078105064443c85100b040501c8204d0308107a00c408540b1200ca079207241c00019841e1030950310200d00c192120244000000808600c00c40ba00681810b283c45c00007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 262013003 1250 262011753 262011809
    0x2090a06090602030901030e0c04060311090703050103020913060f09150b0402040b090904171308070501090f090e0c06130302090a061a0705011e0903080708040b060f060702030106 79
    0x491810000c040000b000a00d8022044a811200a00c4c2c04030301f495880da40c0c40e103420200c204903900545005000010300100d90282c0c0c150180c200c1e004c402c103450b1180202c0584600303003c0a940200c7e10000b00b6107070302030000b186402e20320410b40841d00c401003040c103004581100400340d03541700f00c0301103d12401440b07100e101d1005104440c21402e041c100500c4825500814039414044c0c50460089004d01c60805003112002419642e002e0351524888800b03100a07a45100d225818450818041001e43c0264005003d5482010099224a02c0c04000da07014004e0540031215030300458090842540b5070800400040d0503140341215118994418000403403001055604014502103060001291800503085850301100e0040d441d6405070074103d00410010750011311401c0c5d03910345d040c600c072042d8001019003802512003418595800780c5c280c80d44642114000c0100f04014009003091405102500c0440c002404903030509895a002c0f03400c60380503400c540b48480d001c00d4032003000100c07001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 262014253 1250 262013003 262013009
    0x1050703090f0b091206010612090302030c0303010f030b0c030f04030c03111204140102011107020103110409060305100e0604020310050c090a0b030901060605040602030d0513050a03031b0c031704050a0c080102090a 94
    0xb01600d40c50840c005006441b600b89c000802c2c0d4407410b07803009061080098608800404050f41d6a03940e4804502200040034801111540885000140007061020aa9215044105c1d10035170b1035455580c115903140d5246000c07000d02c001403600d00c0c100c1d1002c00c03c0f020403104194135242d48038140301d1320250840e610440780341103a0500404e1424552001c0907135243c00c0d030a08000c2000c50bca6a500030700c5024135041400da01c0e1030080004203000000a050070a0003a0550410104c1080d80004e51580412200650140c0c045900c44141c032845600042d4000d5000c42100c2c240b25a40d400030ba102039043c0e00080c4440030110501c88004000c2c81004020f004905025181500e00580a5224090b5035500c0c130f0700316a602d00084501d10003c0e43d01c441c0541c02410380d0040e284500d0042e0081103d400003c01c10110709107501c50035030240d0201c0000721b03050303261102407003540c5004da0b24035140140101c9650085507525030014550b0000e4038050b0103e00c0c00940c0f95040e02c0203010b0740c201158 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 262015503 1250 262014253 262014289
    0x12060b01031d03220e10060315140d0201020f0a2a120311010b0616031808030714030712020a0b0603010c0e040203072313050301090c0501050703090f0b09 68
    0x8030700602c070400000304448111070b0000b03088000d8003401c0416450f14515601c4802c468000704108001b00015000e03010980e9080e46040001684040c000304440d03080303028080ca820220790410070103243c07030a0300e20b00c0d840c030520480d0101c844221901d400c15096500803500804814002101d19450003014040078204a210020a07031030b11070100325141c1208401740070700812020a060400080d00074000c1150094006c581d01c00424801c1035140d1504031050b0000781790713000001d58071184000c0344411510034500850410400e1344485403d00725181d00181c003480304004030b000241c00051003402e01d0569402401090620307090088200c100144164405d074544061584002d40050200c1000401078a005071a03581d000780544180b032118400c10b4040d1125216184812032560050002c442140380501d081a960810300d030a80300b0b4800e00501001400209210030b5200f01c028056040c024a40403e0b0b5940c0c0e402d0b50f1000e42010b4001400b6038100042034041800c05010b50788090b0407036 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 262016753 1250 262015503 262015541
    0x17100504110108070c0c0303050319060f1a1e091c05030313021212030603010605012102070c090203010305070501111c0807260103051203010303020a02061312060b0103 74
    0x20703500c030012210410509814010404041040903110307a0000c458103911400c81461a5140e04010f00203030001c9840c4600008003402010340c0921500800f0b04a40014139a0b003a041e0812500705c5408600c8140340700c103035900703010443c10083c885609100781207103001da096480c50014144090200462141a480b030701c1042d12500182001080707a60004404048034030104c1144001001c44900c003003124402c3c442c198108a482e02400700443c0500c5041303008004c469138030001940c144070b07040042040e456102c1017460018000703800074460b0302d1264052040321911035119100300d82083c2c00c240c1da564030400c0c0500071940c03c10214590888240e00500d1044802003010f04040d10b912540005c010301c040c081035013a805203135000c10164240c02001d0141c03034603c00051080200340300544451161103003604642d1180c20449060b640c056003d4510035100707400703100080e4411054400650030903200000c202a031541e41c011003910991004c80c10b2030071000010700f580d200d0b0426156003986 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 262018003 1250 262016753 262016761
    0x11803080c0a09090b040e010905010c020c011106011401051309240e0601030f02090409050a11040606140a0504030c03030201140f01150e06040e090303041401060501080103060e070b04171005 84
    0x20900003804c0356402c001c0440c50200543c08100034220a081116141d802c00d0000d030200f2506400c101049013250b400c403404041c00308011a0007050b410203000ea103801c2280180030800c00f00c4880d507d2000181896881c22805a03002500d4541340d6106032503280d80d13041e000040d031259400921003e441d244d82c000c1002c3c20a113800680e0100030700002e05040c0e0301e05103e001d403103064040d00c0280300020302c1045440320b44d0520944441c51083d046510059900e0800380030b161511460050759202e81c0c800b0014051081c012400380c2c4403050102c14013006000000c0001c041444030f1026511030b070b0000c903171280d80c071000000e80c0401903c070014800d1030400500400f0400c000f1030801030b1040c5030004400c201880403a9042c4119080408080340a00400854410004c002d5000f81c1c40f41020a001f040000e10f1942200d01314042c50340014812401000811700f250400d124001141060301c08071690780801e10140d5001d13038092004090540d2500710b4492040c8a0307880e203000104000d05c110300d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 262019253 1250 262018003 262018007
    0x30020607121e120b010c060e01020406111216051005180105070309080306040c0302071e0510021201171606020f010b010203090a06050f1201032d0c0b1b011803080c0a 73
    0xc0300c1407908100580c0d800a0b0611a0710582c0521b1010f40c2050080028482c08640c2c41e001c2d62150044801003990705040701c10240f400604481d0310000b171070b001c0c2c1c240700c066030640341c1000600d04261010f100381c0e0b290501292862041900540d01141176200020039000d13191700351080100b5100c149803034400c00e440031800c000201eaa02c1034080328002221104044190000d0041c00c0c1c015245a456003140842100c0704440500494007500440d0006101d0510500581c0b207103080c502618000d03003004101000400000204816000301640e0300314410807441090442e45a1003500103900c0400700c814401c100784502024001c00788051450100ac00300400c0d8101101c0c4101000c03c0740000741d0354500d000110507144a6030490083c07214550352400c0101c000100e034009103000364049100701151a26066420107001c0d0f205130b0245515103413060760b28060304064100ca100d0121040004114502841008264800c10048503003800c0c59080090108100a0021a164000300040c5003a030f9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 262020503 1250 262019253 262019267
    0x5040e0d08041b030c0f1d0103110405060d0b130b0615091c14162c060301060f1d0702072702040909200105030130020607121e 56
    0x1a00302a040184074450001c0c09600b0200c3e51010b0081c0060b800003190008036148441d0032506031f05000580c00c075001d902d06921110030b01c4014603600720090041614101608070a034403001c020015540c02410391210100020111005003400004040007000c0148200703c1e6600032109403001803a001104085c8211840740340511445150210074050010308202074414034144d00c501030f03d21384101d074584595034a0344c500600c4201302d402c800c041181d0280c1c0c83c100410500e2490318101c0c038200c245107029440c0d4060180d50f05952144004100b042c2082000002040d80313a0100608040203c2e4410710100007a00100841d00107800c00c00041c05410329128031203522803c240801004020850000e100c1d070b40c4001011030520744011b09000060b08401740041c104100452145e4141004407520300c402d0060301da0030240311b520642c80350003088002441d070f0411001442c0c039141c140c000402d560001d110441c0c9036140340c852080941e0340030341d064044407075203040b070b85e8201c0025201401e81 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 262021753 1250 262020503 262020511
    0x2070602030c0307020d080d0c0801080f0d0c032102040f0905060a0302150307020328020c090f07180503030d1509090b0601080903090904140c06040e0a2c010605040e0d08 75
    0xd038010150f242c0500c40e08100b1644001c0e904901002741640108028003071100900c40c00115005047c03c04031450800f10394800d205600382c0d2429980c07441c503a000e40300040e0310300190071503507405000c2810f0b02443d480180007a1001c00810005a443c0402031000c1d40e80082649004a440d11001c20050711109459214111801502a225640c2c080d040b803a5006640004c2e00d282c0321030200c449070300c54501641c1c000c41c880d9400e40d841c1100d048148902000c0580304400b12062050005444610a407400181e120b02c0290700d205250780c5e40002451134200c500c40101c0140d071817a00801001540c400d0a0081503c0b41d41480440c40039251424007440007081681400443c0300040c081b00c00620484100010040040c001401c0030300309100111007181d00268140300d00030340c02085107000e0050701d0031207015440c20001941c400c0b07001400f0300300800d452900c242d1019191601c0c001510302002d00101040000a103c9203481d0400c416a60004a056490340080031064403242d07102e5a01540 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 262023003 1250 262021753 262021759
    0x3040807051e0909190308040c060305070e060c03071b06090f0e0a020d06080d0908010e010e1b0604051302070b01050d0b040b1b040b0c011a01020307060903020c06180102070602030c030702 83
    0xd00d6442d40101800c1469004600c2ca0003c5ea03a440c1c8810517400c840d90300d0086015010b02c400d41a00c4110035400c40d4016504440421401c0300d14800915020b001410030500b903806603420310351560b40c0d0b4041180880340340203045000c16018000306500881c1d100060081490585803549428204d014007000502451312482e00041d014003c45400e0b001031008058400407502846074011004001d0342c6c850260401c035508100b54804d01c0304050180074103041150003e485d0226a00c0a072444200300100e8094000340280000201a075441e01d401d969034800600240e5200b88030b20b80304030807140580100f0700c01c000001b01e40f0045184ca003922644154003080030b10350364560200f89114840041c401000c0118001000300d85400c2e080054440f00b440407000388120210036104c5400c003808003030920b0059000744407601c08074070590040c034000e07030081c015908030039a80404507d1035440302c003603030481000b04000c042035940e0401a40004240d98800b82d414001650351030742d20391140c680e003e44 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 262024253 1250 262023003 262023019
    0x1317250e060607120c02010f021c11280309080d0f0e031c0e09010509090c01080c0405040203100e131e0303060b0c010507020f030901120513050f03040807051e 70
    0x3551940012502510b400c80c1034600702c0103a8203801030000400d184103d0001e07007022140c234043d5000103000000000c0c9002460707901d922490b82224601095a225082403140041500d03111030355010046400c580381125001d40015401d0280003084a43d0246009500004070400300541c4060807008900c2e0918140c0500014200000d10307000790050510320f4a19500050340440790402c0042c1c054803010340762036509a03a90303410802d20303500440380c044603500f0800c1e5034034040d03119040c0c6a6004c8000c0c804942007584950226089800c21100b00c2500f00303601d2824002c6141405040340d020790381e421100440301d026903a81c2000550940101100c0072441452010180290001c0c0060400f0840c0301d515a0021240c1c0c40c06003d06a07903150160007aa0f0841c0e00007540803049a0b64190182c451121110a40c9043c0d4024034005058010842c0c1c0c03880c0040008206101022000c8500001161254149850507042c030700281d010502c42d0180c48000c08503284080310b05d1045c5241111150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 262025503 1250 262024253 262024261
    0x109140d080f07020c09240d080a0807090801060e04030306080c0d03030c1106150a080304030506130204090f0c030506010803070c0504050615220e0f1602031317250e 73
    0x41d180c00201c0017510b030701164840030004030202c4005c404e80003500c160705402c05181e0030818020b848003004009010a90108041c04e2401e00a00c100c0c0c2c1c103c4402d20b0321451040e03503900d00c0c0e801c680f140c0d001010009100030501040c90742c5405a05c0c0070f00074013805002c0343e00040000a070044140c2e40000e040c144c94085103450300b4021420865200c10000a680b614542800c0120422198404d600d1040b141004040b07a0004004141c0f4180d85d8044000c109607120b2400240c0c000c2c40706541280d0103a00c0b811010009000f030b855035221039128080c100402803c5160040c14440140c012080540c0148044000328005c200401c0031204140c82c00101e40e02c0f50307004100b80c0500404280f4030184002400108444100d2035101d69021211440140d00d846505034000c0410640b00e1025424016000c904290901e016000c000030841c01128034040e80001c520484803959800404c0c0004c807900390906603c818481403108642222465030190509000900c07a40c845008030881040090000303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 262026753 1250 262025503 262025507
    0x4050c090a06050f2101020c0609011a01050d0e0c100e010e01030e0a02040509120f070b010605040e0c0a0c02040c170108030403020a031b1d01180506060a0525050109140d080f07 78
    0x242d40c015417004005d42d91038000c411002e90f1032030b050b10610565860a0f41c010303442c1d5601854044d410b07105a40f13051400c0805915000600f4805a003250b0a0003108040b0f0f010b03a5400c41780300b1543c20b064507079200c80000400090304000d40001c55030706050a040d00e402c4004004a41c0c900340ca40e048900007201c0e02d0b10007489140c03542c2c00e04150322580001811040000d410005405070324442c1c5882541030383c0301c00086855004d1403190b6080703801c410740424200c4601c4006070100380b126141420b482e401c260002400d48a0300728919000c81c3c89010300c030000741d481b80075460251450320000c520341703440c0d0350100e1021350381d611004d4044a1410064038001000d50106402401581d050000e80c43c403104614040032800c2c4280c0d107820f10380400c40701c20040e560280f00e110350b500400041c105200c640081c0d546500208003213101d10007000c02000010b840d107003503000701401a0b000044085d02842c1c09a100d642d0748a42d40311075440a4010408681d01c18101680720851341d42c0c1a01d103481d01d60b82 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 262028003 1250 262026753 262026799
    0x3030601110705041103010e0717011802071a06040c0e06090603060307030503030a060e06010e010f030e0c0d05010f0c17070e0a1d240114070c0b0304050c090a06050f 73
    0x40e134018100882e01c4071052002001e14140e03140c4013a01070305030311240400c0d5002c00d100d603143d034104c4068000410111098040b0800c240300345201c09440d11002e41e60b84000e942c80c0d80f88104034041303001e00707003c1c2c1410a8420b9402c3c03010350b42001440030340306500041c0b4070b000c0c0c000114401e580001c009102505c040c060a0000c6a1200c22682c076414401c0903040a40800d00810000c0280310001584c3ca41c032071000045c1104042c1c464a000c64482d000480c0502142c8a03013107c10302c55000340c0d03a0b054940310048607001c0d01803000014050f001d1500031050314130040100d03082019042d5408412283c2101c09608899941007015960401802103060814654070000d00900c449400d086055404900640b00c2c1c1814102c048100402140440c0d00100781003820703002a11100200c0c0c445009140100a070601502c4043c2c1c50f1684c620b00c0e112264030440f021070b49500001101551400e000a5203900654140d100f40601802c2c80c0201716404454172020748100700161046c4254141121 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 262029253 1250 262028003 262028009
    0x20c0106080f032101050607061505030304030606050a0b120f0a0902090c09010e01140403060e0c15040e060906100c170307020a02030c190b0c010b0301151409010602030306011107 79
    0x4151070703540c01e04410b0300c0c1e2260009200c0d0800512411100c000101300308100300c0c10fa07440106498140106034440310b009217440c1d2103454690071040f0780800c00d560200041c1c0011441242e0216401d41007109102c0c2425803940080314804081c0310b01030b15100d0581e0582d0307200d603200b00b1003a82965100c4985001d80540c05010390000716910a2210341068803004144101c007c0c0c0b100e0214000b104011200a0380e42c410042103810140800c1c00090f82c82c0e00074002f040f80a038101c0d600000700600281e45038000200c0340e151400b0004c0d0421620442d420b1080d4400c1003141c1e02c803480e14042e004203404004810715001040100d0007101d0800c807010180b5641c42d078032030341f42d41d460f032401c070780084d5480458503020fa01c1781c894a080c001d60303460711201c800f00141c06940c0c8881c85070304d8556203203855005503072442125500c4904818103030b142440740c0711042816a42c5d06034050f14200d540e40160a44110190203280c0c0d4000502c9810740020840360024421310340007a07030404513580103080c00c2d05030b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 262030503 1250 262029253 262029269
    0x1090e010f050d0c1221090e15192603190507030c0b090706030f1b1103120910060909020d02060a2001140f0f040308060d060f05150102070308030a020c0106 69
    0x85c80b4003c0c0014600140c02e00704540403401201541c0c11810303a8000900e2140c0f0300c0c0b1140c0e0303000007135206d01c030810700307048401c2d026107039045111310200c50075001103040c0c01242d600c2809100c00104440d1041e0402041012034018600e4100d55130301102c1141c0782125164240040000c59404240c071404600741c0c91600402d02e030314982021200d0b252211198880c01001034101040c40c42c102d04188940b40c40c4684400c40a0050b4188400c1a2403441c0050260300084c0802d01040000f09507182000f880b4681e000701614500390b587d0b04000403140c19400c919102840d00ac003501c01602c0b2060340031803c03901140d040d070f20b840e4038180807200c0750004450480c2070b84a00c40d030103202c1c05054000f021460445004181c00790f640b210500703003209088480c0d01d600e1072032030007080100f4001d0501c15000000a040502c0d0721080b51145800c0e919031000000c03d9550318130800505002c8020814031410092003e0329040717181d911442680d000c0500070701030681c5c0c001003400c01c40c1000d60009006150712 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 262031753 1250 262030503 262030529
    0xf040f02010f210b0a06180905070905100f0206220b0619080a061802030319140301060c0c050111070501030203090109061806050f010e0708040f0c0f0501090e010f050d0c 75
    0x1019040940540344c0d00c6401100d1001c00800c400e8000c510f000094005000b440c1581032604514101820016128809001c82c0c09800700c1c25884000a0351850a0540ca5039100310300c000c42e0003071030720800510201030386a040c141c0c40001080d0f80441481b40b500b001022001d0b03200c03030000501c0d070071013000703250304000c3d650400103807040c008500181c5443c0160000c2141d040342c0740651209500403d40207605130010880d0a04000650464140201322458002030007141c650105046610070303002030340420781146000041004400c0480064031083c60212402d040c0310700515503d000ea409010706040d008400601c06c00803d5115200743ea400c07100c103000c4404400b010014000000e03c1c1520542c0c01c20000070f2100440501c0c641c100c512502e080701041d500d8a004840c8070b4000b92046410854905440c000300c0c62208070b010180c1b2240b014400001e00e44800546580903960141c103000c410f850040040d881c508a41c00c08407842650b0704100680b0900d040140c00e1610b400c8040c4c81c85403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 262033003 1250 262031753 262031807
    0xc0b04050f031902060a110a080a0902060f07060c020d021c1407060501150201150b030a02070b0103110f090402030d08070216080604291b070f1101080f040f02010f 72
    0xf03100307a04403402d901c0e5002e845141d2140c065920980d9403070704c00944040c104100100b4054419407207254840107400340015070809945c002002580210002605003902264810501119201d100100541e500080906400c50f010203520750800101c2c0ea0345402c1248040c61929005400c401002000740908581d10704046c0340c610010102070281e4929020f020309201246401482076400d0200d0425480c1005843c3c84108a05039100802c90035242c0d4003802004005409442914040c0d88101203900042e0520000c1c40704010250000034800c007030810a000c05600e000c956024008824542503400e03607034140f000c2e03240010280444192008050001135224000f2a285000c1c0f80305850001c56443c40200b14200012000103203960448140c001c68003841440d403441c19000003640045040c04030980b64110007410783c503002d072040369000349074401c2580e000140c00d42c0668064a049154141511504450600d0f804001d060050102c819648030b805071030340545009203558002510340e2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 262034253 1250 262033003 262033027
    0x2102030c030d05010f1508160e030316050c0402070209130201140705010902010207090509100921050915030106020d030f0605040603080d0c020f0c190302101d030606010c0b04050f03 80
    0x1000b445501c4220007440c80c0032034902110700803c010006d80e5900c0034a1500d950041031f0009401d012101c061068a98101c7d1a40e01c00340040c110502ca02226042c4104141c14240d0912030490700b100e115601c10170460740142e4851581c181c2014002150240c00d480c0740c801038a4070900c00320f2212400000ac107120701080700540103100600e200303909803101d00795284807034400c3c2d4000383c1e04500c00b80c1091600d14244a0305038400c25201d40600074969000906001642d501403203c014403000600014000481c1d007090a2890120b03d0618840b6285d9890640c1c000e46400e0341500c02800c01da220b8058020190b42d80e000000036181c010300c100091544c91404041c554041402c00c40210308144201111900204502140f05c0c1600d0182c0022203480040100405080c45c0451070740551a0020015880b01411802c1c80311840d00d40d0b01c5404009001d0200c0c42c0c3d522050540309074081c004201490f48e00c14a84031000b9440f4903001000e45841c5450350814900032001c95036480007040d0b2138a100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 262035503 1250 262034253 262034261
    0x80306031504050d17151c02041b0e030312010608040f0204060e0610020d02190f1203090320030d0e1504080a17010803040e041403040303021005070c2102030c030d 72
    0xb20590300c41c50681ca202d05c1e0503282c01d0303204559401444100203108000b03410640d43c148489100012800140074042d40007504544100c03038075071101c890740c102c51343e00241c00017100001c84404900960401c42c05900d2007007034800c1402443c0070480440c1c045002c10060300560480a5802007040c461240c9030540030b02d600904a031458428115590b488000c2400807400b0f04480c2540c0e4043c00d101c889404000c5211403e4510031205141a040c5000200300d60a040480c40802c0d59800b08440c4140d09000342500441500e1501881d081020b80708040000000c807047c58007180c00101d245201c44c0c0d92282070000c64041050300310540000c000421208200403d0641c160f074451f00220801140000030302c490034001c0f090310358410807090181000c41c00211303a10600c50584d008465401510003411600b05600480c05a400618030000920007800f40c01ea01080303d140c804c024405903260381d5140c90411510700e041c02c035041500321207a4070070b2045403ea07000c910200d03a0747e000c4d81070440c8010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 262036753 1250 262035503 262035523
    0x8030c0d0801051e091e09011a0306010b1207050705100603020111010b090c28121a01050a0c110d03090302040e01020304050d12060e0415060b04050d08030603150405 73
    0x780328600108891401d0307413458072100b80c111501031a114070a4180000e4090182440141c1043c000c5100321800c10b035281d80740b140307041c440045032110302e9050101c203951007840030302c2c271a402000040c4051400300741034035031046107210380802e07903291101c003968244610707840540503001d00145200c0441d82074205c10112032003a44c030384881c03016080030700b8222801c004506901860f410301081e000c008480c003a0001a0419013460303030143c907141c1c1c019646031014000101280e1134001e1580c864546200d4099202c08612031694844c038200c0000f4038505c550624003062000c24010b0341700340000c1c804984e090003030140000e420441c0900380070b000c803d00762000300d100e1070030241c460764041c0040c001c0e82d010381d6104004020201680301d0a0300c0c0d500c120070b996501e2030b90b00c04c40014075041e0341d480940114040d01c0d030079041d07800c041c102e5015500184c20094448404002c208810303150000d046061507000000c03551245c4510000904144089050b40d000200000910041c8800030502d8580 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 262038003 1250 262036753 262036757
    0x3010e061b040e0702011509020412150209060301030c09110711010c060617161401080c03040f0512030a0f0e0705060f040e0421090302010509040c0c0f050d0905090105131508030c0d 80
    0x4000d03996004001a0b103d0350184895012f55000710000040c1c0f0a1401c20701450600005400c007556500801c81c40e4000f68001d90344200c100300108285d881502c20800c00704d524503c1149400300c41c2d05c854010021082d200d504021400840c0814080c580e0304c0080a003002450504035010018003940d6148003080c80540d10030400100014282504600f003140d610381a1190328985c3d0340c43c4080052070b00020401d5500301210441c010004200348110101604204249a16410308888000c203c80362280c0609000d1315084d4044209500000c1c4a01100c5044079000d42e91603401c150302c0340320300030341d4000b00071940030405101c1044441500102c6204210b0191130704810325900440d1101c40904c07000c0d020480420410182c0c5c2400d80241d000d09240d824001c0c0e0b80784156a802446696503c0d06448030781104007034804940d0f00c10803400c010074003190201087d5041000058400030045035203809250768003421500b041510740c07035800038080d110950361101886071407a921540641300401c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 262039253 1250 262038003 262038041
    0xe0f0a0816060c110402031e010801050124090b0319090c08120307050322051e1605090c070c050a08060106021618051b04030f1103010e061b040e070201 67
    0x51007440f84200c400c0440c1c110101c02c14242d0f01c0c41c00e02000798400b074000d1001111a113986071000142c5c9410394003c200720400021590724041480d4400f584280203481d244044144800e0709507401320441d01511060604c140c0d0700c1e141c1c10707503007000040c8040c00c1c0d071841c5040000c000c041c0107822103140111060181550350b45a9058260780080c403046800310f003c15001e101080301d440d001050000750f48030309480d203802e0302c3c695158689004044a5104000600700700c02d40e203089024810056450104541301150380d0510000820f0294000e01c802c011100c00b18031042840041c030313440d40040c44040d0403a503006489907199600e851090060340094401c07042c519400c0300d6054140300c00c592442021141c01c100c42201c0700b0142802919111003501c100c0c50300854440c01d02d0040c0011480b481031038501c1081440c05183d585034103c69288280d15000090300180c04c0400c0456028941541150031f600452020562a010340d4211f4a0444901c004100310160150310048003600180303c110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 262040503 1250 262039253 262039259
    0xa080a0b090115061103040b0d0203180105010b04090b0a0308031e010e06090604051906060f1206060503041514070e09060d080406030c020109080a170a11040302010e0f0a0816 77
    0x9030a9599240f8089009000700c8020410b4601c1001c0c0c0080012074502501d1400e40d4075188044a80c008021060710960b00100b40302c501c2640c0c8144041e65100310000b4404c66241640b070030340601851069101194071044400c01c2651500c808001440c2d2100b040c0d070316400c00c0d048502c084189015416642904038001080c44c00110045520070103006212800c16681d56003400081c0401412422201524092015130841c06016a01c00f828071560703000300360b80c00321070700402040755030380360340282c51030140b0502249500204582c0c1c001e8115100b20280b00c80040030100805080300c140e00c1181503001485104d6030711078180c0f00040c40031100d18043d0b48461007000906040024002e1080c03404010410100b402034000e1101d684640c0000140c0084503110120b5030b910501544000034501c3c0040c0c03404402c10000742e44c0002e04a4801c000b0759064200c040d20a00c100e02000e418080308204030941d039500d244043d07a207540b026001c4180c00d551012031560752407049041040c3e06c04141004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 262041753 1250 262040503 262040521
    0x1120908070f02040902090117010c05040b0403060c11100501050a060509030618010e1e0607180e04081c0b0a060e03071211030303090c03070b0c030702010806040b0a080a0b 76
    0x40501250804009031901c03400782e40b40303404a545480d0498100d5203030441200580e407582d000500800074203011488104000d5034040c21208483d801005101080c0010700c40d100c00481901c0a0341ea104000241c00c1c20444415208102003000f40d46892160422203072034803449030856812950f050302d80251098507000305072424080d12040d1a015400040001c001d05100e01040f5003050035240002020941d01400354204044c3d1218440c010036500b01040c0034036010400c85900400514040f4480c4580108003070901d00c02e03105800458440f08003080c02c1c04000d40848020101c0b058481c0c941c50b81a0160002804403003400d244695510840003454a00610b0b803002c40700740c000c02818841e4102180c1149400241206444403020300d002c0900d0341d00d0400042d40143e50f4a4000c092851040c0e08151402d0143e80100742982d505001d01c0c52030709400025030740180ea0900740021640e42d1040442e004003008002c141d4400300c4500f000803d96408525505c00e00d011b032403c5806075a50701c2032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 262043003 1250 262041753 262041761
    0x9050901050105071b12032604030f050a0519020a05010f2705010b0303221212030c020c040c1205060a15110a0c0f050112060e0601050a140d020403020112 68
    0x50940480c0c03041100c1c0c0b0005045c14034805401d049694004043d0f03440d151a04814070020004501040781f182d58a009244502040000d504809842809501e07141c1d4000786403400807d2107005000300803079410001c60045090390300c1c0000c03c001480f042d503039812000b941c0310140201980d40307501e0303d480f00306900902d001d92452648004084421080004026801c803c44050107442e95547c0c0d4040b070300c0341d80e400c4c0014000658520298401507101011007109083d03280c0c466240c1c482a50407040008a641c03285030556413042c200002c452080c008180c2c14900103a8909500c24644180c4000d100e030441404812404e54440400031f0f991110705102540416004202d401c003426401e25030301a21800b202c0d80c00600c01015940c260711140e4505801445a4000a1075050b07400c2050069580c400280070700d04040c3d0400344011450400082030f0198050147d44c1000000520281d030301d8040d00010002c0400340d58500d076603c0008185100135042400200e000030b407544882d28505142e409 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 262044253 1250 262043003 262043009
    0xa23070503030327030d0207021002010b031b041b021c020a08090f0112021818160806030c0d1101020d020706050a0e01030b09070807030e0f060c0702010203070516050109050901 78
    0x100461440d01ea8580e015101402100304111502c119045504d01e04024009040c442c60000005a16941d003441003010080c580b00380301c0210380c54810710910603580010080041800c20f1124005000d82602180251240b0840074022034098402d80e00d01503070000e002d00c1c20800c1c14811501c2020145412a1150701d0034a001e00210303001d020078000703403030320a2040c0e850b0503050600d400d03425501ca0700345007070382c000d00c000f2190400450f06c141da80b82001c0d590403062032080050300400e8035091980c0e87c54500d03540740710010000c3c0d50000501c5501c0400c00d0300c2c03110708000e1403da1044c01078035082411035074240c00a401400b40c0d00391041c00c54000903002c015190320340c40c0e81d07003000f8450320b0860750141e6000c00141055101c003001c05051301c1300000345004180941c0c0c0d50304240740610300035003660907000340c130348084d4440340288000c9803012513140d4200e01c0d01c8903465501d440c6030004038a140a810b1707000c3c1c04d82c00307800c900c1200c160070a11010304960003a2240c0c8090b80e03072081004082d40d0244 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 262045503 1250 262044253 262044259
    0x1d0a0f17070b0f01090e060c2a07050f0a0303121109031209150301051008070c02040c0e100e0d02121513031418240c0d09050405060a05060c0a050a230705 68
    0x11000c19030b0440524060003c51212710000c8008944010040c0c180d498038914062094000802c240f004d410400407809100c6001d49400c80400e00d503540c01400e01d5191000e02540c0ca640c0c490785034a6420135800c545a2201c02401c44901c090303c1c0040c4019984189482442841c0001402c42c0450218050b1381c12a00000e01c6415002c40c81c80381664503601c01005030701004844480d400061b03031540320310754440030240d503100c45003060b442c113100316101e43c0c0d070303004060011710050b05015a0314030455995096040c1d9030106548243c490961a002542041010100e01101005803500e202c0400d020994042d558000c0603010207041b0008911565a007025111011002154107041500f00120305401448120000c5100f60302100ca00390840d10300000039400c15410027281550100c07111001d014101c0e0704011a0500700c0c000f8040007114881d25015400204a209000b0380a000d145459a0084166002c81c80c80e441c1640c0c180640131000c0c00703217984490362220050703c0005d168060768005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 262046753 1250 262045503 262045513
    0x21060604180209070903080a080426041401090b07051614090f06120607030606020111161106070c03030c061b080601050c0304091505041d0a0f17070b0f01090e 70
    0x25000d10520343e60080c440ca080c0550542d00000086c0701d80000c0c42da0b107840c0e954020035030030300c1d00d420842c41c6941c0700e00c0925841c462803040c000e455120101d400300c500245141c1ca0801420300181c1d1003042980c03100c0302c6044c01007140c1042c06004640d04040c0004d038203071311404644412084440c100255000f6400203041c6c000130b156503058104c0740d82c002200070305c040030792032040c1d80c2d2610303090b012036820000a1303c030001046401d409024602201e45040001d5080052540303a01483c920000d0018041c44401000d03040c039511400b0403100d19603040000d000b2080e0700c900700035106110b00380003200c419160568144d881000f40c0142c0e84130031825640c05405844850046503039400c50500d1110a0204210020f41c00e1694410b40c05d0500b51000803890441c540341c1000222000c94a04142e0b40040e61104451801c010904e902c5066201d0200c4520142e941440740c10820f100060044980d0006000300c14003500100f01441548540c170960200d03a210421041070302d9000712032880541c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 262048003 1250 262046753 262046801
    0x6030515011a130b03040c030b01150804150204050d112b112701080d08090304180207020402120f0c09101101271203020906030106030207030201090221060604 70
    0x1524000c1c41c18003d0b0820503c0c85a0f101c0c4105074041d841901c040b40c81d81508501007080160450342c460040413010b407014000e01e25190081c140080050004149180c0282c40d51045106503050b1000b614014007030903200041d6180c000c1c00071100540046c8542050758250480c11905603039217509034200242c20224145076517911041003942c220941d4000c500d4160f24039203250350707840c000a00c40b0520101c0b00310751400510a0914003500c8005003000810402c11a40507400001c54088481c4210070511400e1860080c0d4000d020b000002944607000141d40b90a460168520a0084e01e581102200c0c5442d1000b07403240c5032103407019042c0c1003c048845d00711080c0c0602d0f0b990030300301c0041d00081003c0d54441c00c811464004c41e05820051000e0b041560188909131b6000121b03040242001c61402c004180081c0321804148141020180c00040b1101003501c00e400c1800d1490f80a4400380c1d80e40420503c0030f04108040155040034420200042c007240340502541c1c094405a195410169603 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 262049253 1250 262048003 262048049
    0xd080f0313140307260a081306020708180a03030e011202040801111207030213050d0323040929010c0f0c0803090f030c0906040203100504050a0603051501 68
    0x70540718590369030040c4140441e0389010032506520200c400355540c1c12071490400e2924500d60b41e007040180b02082e0038020311800404850390781e60300b4201080140ea900070380001c0c0034450300700100000d0000c51404200719614000d000980d00c0d020b4081c2c003000042c6c1c188200c0d0121031002400140c041c024144080d401a4004034800c0880e890152030180c6440040b800c1d180400f409140b0200d000500c501c28140a001146d0862000e180c290300e00000310031036100000850068520031850b00080e0003c050060841003408030a6005501040f00070302e0304100c01707410501c6030105090424034003c1811030141c450070b0717031010541d1390040b12440c1c41c801158641c04118040b0f455035003101411010403514080000100b24400086030390f000d0243c140400301240e018590702a611001c40403841e80d1302d10074000e501c600f0590300181c0380d546075007804c80341c20b51590000e60020700c1d21003805031412407600700d0000d03a0700590849a54006071042550401401d100d2020520719044c5481c1000e8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 262050359 1106 262049253 262049257
    0x10e030c071d090615010e0d030906080903071a070509030f010504020f091621091a1b030a0b010504050a0b0c01140712090515090604030e0d080f 64
    0x428241c51a135558800a81070098000c62201e10b04d0459209256005c00501e0003044043c03d807a003420040c021744814000c8600040d5540005414414000f0071200c0095000490305c424155000500c6075051003d46076100b0000e0800c00391506030740c204400700c42c0d04240c00c0009440c3c10103104114000034400b41d04c500900206081121110140881180c40d244030f08108140404819030301800350418000988800c2c94801c003041441100144016100700400c1d10381039580742c404001e154002c0c1a20b0405800d00104002500050f40381c118941140060500d141444d85034030020f00c802a50f600000484640400d40c4819181b09021300070714400c4100d0700d04c130300c0d05240c1001403004074640114040d4685401c19601040f00c20800c500e50410b01010001084c10316443e242e07196142960107400180441000310041e2a00c040b1200705113510281561034003070110038891090b = true := by decide +kernel

theorem cover : BRFrame.Cov 261870503 262050359 := by
  have h0 := BRFrame.cov_init 261870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 261870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 261870503 ≤ n) (h2 : n < 262050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
