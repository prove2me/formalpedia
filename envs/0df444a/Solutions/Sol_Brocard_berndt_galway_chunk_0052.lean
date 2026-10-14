-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0052
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:34:34.632908+00:00
-- url     : https://prove2.me/submissions/b3ad440c-583e-4239-a601-dbad13dc2c80

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 9172669 ≤ n < 9352525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 9173919 1250 9172669 9172679
    0x1060e150301110c030307180b0a030911120f0606060403030504050d05010b12010609180804060503070201020d020403030906030b12060c0d090b07030509060f0705041214060a0507030e030306060406030e07 90
    0x40003801c203082d407000c050346d2a841d02000280006443c002c0000080718001018006c0b5038000066500800552800040550452400d10000c1a11360141c07544081c09030282c915040001441c41900180801500d029444800c103100d854095030000402140c0b052000f8001c500740865201d40b001d024200105000c4d414102240741000c00ba034034030545946030141800360000078002d020002c66100c55020104a494844200c02c3c0114081c2604128000012601861003501500d2860b06403043c21540c880e52482d014002c5112441180d000c82d06103c2011800d2826281c1c0301d015885030320162005585885240c090380d80030400428103140d5611a4801051803030303104500c60b6000d9140000c56081c0701d0101468410010000ca21904908040000c620b80c00f10a81d030440d0200800645185010310b02442240080070342d00c071191050500304034406030a908110b0040c849a00d04104c014041005c203610b900c4222146138100303400304030410941e0b1182d808520f0704090304042d0340301c4035103032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 9175169 1250 9173919 9173951
    0xb010512180f070305030a0c0f0c06020312010608040c090c02030d05010e01060207150507020108060a030807061d0304080a0b0406110301060306090f0c0f1404170303011701060e150301 81
    0x589034402041d69503419054200d80c100072050708840e20707070010078020f840d558603207a0b02c1c411000c07480c00b04030800d045a410040c0b080030390a041c551003505200302e07545801e002952504002c1c41e0a485100301c80002403400e01459009000c0c80d00120160b08441c2403002250140200000340c2d4110700c420084042c080049100d01806800b262054507529403400000074586041c0d0381010201c80c0040240c100e03200c0c0c02500726100c0a80c2800c0030651592680000b03440c0c0400c56001800b00c03140003501c2010048243d01c080904010304080c40030160401120940d240658040c401c602c2e8402c074001c802155140c902d0300d40c828072521000c18038080310702985015410a034000c0b130100340c403018203000070000b0f800348510760140c0850400c54000d41800050503200040d03d050705200c2041d04d10021902000c01b1540176042c08810140c4490302000480e82c1e980c42442900d209007100301d0f4004040c04103018a00844401d151041e94a80380d214080f11082d00c94580298550f50352030000b10001c02c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 9176419 1250 9175169 9175171
    0x1808071202040501050301020421020a150807030501060504060914030c030304030803010303090905040b04060c020a0210110f060702120a09090507080a140c03070302090402071a07090f05030c040b010512 89
    0x46084445503098144140401c0e160306800c4240f00f6401400305000d030075080700e61112082c0c5114001041c0d8403260002c03421a604039000741d00381d4502c420031002010307008424507001ea850ba0b03500300600d0b81e07141e600311014020740c020700c00040c414040801c80c00c0003881904840500007019283c0c0d4001502c0041d295510907401243d00c01c8002c0010030900d80c0059500004001d08181072000d85000d0343c078540d070110300410090080342e980340703001483c5100b00840b0b60a0341e40a4500c1c05680741c0c20202800442501d8102d03001846901502540c4c8803010030740c1e0380910b600f50001c0c0342a00c1d05800d030302620b40000c6c05420403c4142d0b40000303581650703402241d00032401521110441d0418a085400317070b0360900c48000131036148505001980c901c4108699001807030303180040c1c2381c090500002d4040d201e800e402901d810385031580d8074204900b5004480c0249510346401c0003082d45c4840c01c042e902000c3c4a1640d054215030001021810f254010660072101450011b207800080e01c401460307208 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 9177669 1250 9176419 9176429
    0x903030a0e0c06280302040602120a020a0204060e06041d0307030e06070804060305010e0606090d0210050403080c01050901050f0108070b030c0c01020d0902030f010b1309020f060d09020306070804050a0201180807 93
    0x3503402849214031050850044c00b240d0b620713040d4501401c1280c06582c40c5001c0d100900c001d800000c190001501c2408941000c40c2e004006010b13061b500c070322444110000b134036140d228510380390300c1c644a40c062078460000c100001002d035080642c52344041d50b101030b012421540003841000600001844030700248058107030740e14005072035410489400d044141c024010b0380070341320030400c00e001940c5042c588403007654100c0d143ca482d03c41f1500202c4031802154001803030342001040e29140e03950190440c6104600280003040650380301e203802e42507203a081c450344010703800ca81070910442d5440002182d2100380700780320600e403160200c10a801c9070300000d18242015a102c00c00e9003145010700c0f012900d04601d80083c042c0025140000728081d24550307844107203540e40d2140004548604d154248802e01c0200303681c0d10742075120341000107405882c5040303100780585000111000e0003a04400d0003550080028a8641c8042d8010b480003003a03014842c1d000540c001e0002070383c000410403140070300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 9178919 1250 9177669 9177697
    0x504060204030f03180b121501020708010204030503040e060a030b0103030503061507050a050c0405010807050d060e0304031208010e0114010503070327020103050c0f09130204030b010906080d080903030a0e0c06 92
    0x2810035000000c03080e081c0c1c01c40503041404100b1425900b05e011fa195400c12400072441d150f0b0320380d4074010703464545694807040c075075400400d0000c01d1103000b0020b4000c403a05500c00104030360740d510401c10011f402c2c1c0001051000d5100040c80800c0c030078006194428030141c04046d030090382c0d01c40261150072031039040751590301c0046444100302081c45400f1030034805640600465050070580b548890240c05458000d1003030081d0758080c0170107074103c1d8100b000c48009495840c4e45a00b0300903041d100202c0d040d80400c4040c000000e100c0c02401e8918101c070202490b0022000b03160b00111176075803000c2d2070078bc2015102c032034600d014a420078080d1a0640c24645161906903144005401e0303400040404006039000d0018100486500e802c86001481c1107541c0c164030400064a40000e0180f5040a009103406a0002c20000259480302003511070050446d9040300f040c090407100350804650b681d000350424004603060b00c400c0d0f00000492030045003a5000d0110348404111560401c54a841c440d0b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 9180169 1250 9178919 9178937
    0x60a0b07030306180c030c03050609060409050705090a0c020d09060507030302070201050904050c18030a171b010501090209010e060304020109030b0606090d08070b010608070207060507080409090606080105160e040504060204030f03 101
    0x5d41c0c040c410100003220904052204d49489030000300486802001c090280d500e8407105810018140848005044010915162130414440d03182c000c00e0482000000f52049200c80f080700da01513444041212603036075485140488950b0104c01035000904100c3c14000184803201240d640c50044904c40c01341c80900d11345480115004424544090b0300c80790103600a020380f18045040103007170f40d44100300a90310300da640c4103d404100e014000e50094442c194600300001c0b5005813180c004018107002680c5400501c0c2001d001c01c00c1c14130080c1c400a0104040e450204005141000103c4d4400702c0140b50070700303252480c03010800d042e03940d0100b10303113604000500381d0407c0a04034109003d031019107001001481c005a010b540c8403601e00590301844400b140034001c119007035007114090302c04c1540078400150a46442005004640030704001035080c90b00003400b41074451035403000c401c26660b074503412400c60b0341800002c1002030800e542c20390b020080400403500e400c1c1c0c81c041d494032941d10700b408 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 9181419 1250 9180169 9180191
    0xa11040f0e01050406060902040b0f03090c09070e03060601031406010c020102030408030c0601030c0b041511010b2e02030307051c060306051806220201080618130308010e060a0b0703030618 83
    0x4403001900300e002910304c14081070040ad0403071010740d100d004c3c032404980c0d13030f039202c5400c2107150114550070705078404041070412149951204c44212415016400c40716181c6805005400f540c0c96100421a205101000203240750712881d0b50005181c01801624038082e1100142030450340300142c1c09202e0b5012100400400c982c54003071b00d0060508440701401d1038108511220020000c05148040000308a180d000860003940aa05c0d0804c0050100c1613410001c0607001400007041c803a4040d821100c060125511b001004403889610a40d071340d545809820348480706050f040d10030000b502d55a07514013100081c00e520039103000e03d4002054207034000da0038240c41e240ca50f00030900c181e8a03803490724100c034603181c4802442805a090800349401c0e41e808002c541010711558140c911f00c5203807000d000d00d800102883c525282d0203079072804c0c1c041c1c1e202c554000c001e1074290f804a420050310358080140c000054054406c00c5d2081c0b4000c25030b00d40d500010120380b0346c42c281c00b44070340c0e03660460040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 9182669 1250 9181419 9181421
    0x12050702010c11010606080105090406020f04061d011d0120070b03181f09080705060406020c07060309080301090c12050a0b100c0201080412020a061103090105010b0c0a11040f0e01050406 82
    0x80c001c3e25400013808410708100004181d481d0603c40c0b1070041e0b010b200460100182074060700c08403041880ca05031219035413207004005ca100c210212021060b1aa0000c000d9485003044645150700c800440c2000380000004413203800e0400c8440440c03d00390b10380762516880030b000c980d00406d510b046040c2c0b20f09040c1d0740c0002040e1480c1101401d644000c40a081d60300c00b20204030725210560a0006034000d55041c00003480c822200d00410320f0140208000400c00d0300d6014001c108001402c6419098684d502541260b500f94800350000c00f09000400c06030300c03d508905e4801c1c03c03900d0301d1599811212040803d80307406440a4294644501c2c0c0807020741002d01000000f80040d280808588031107400107042070324040e201401080100184040050082061100c0954041001c0081c220708007500d02e100d030000e84805005500f050300000701c1ca2100700689a00760900301c06054183c085640f1a01c1c0b14542000c0c40c0d801c1a00c58045180f00d000b94418075071a01070300b10004c1010300c0c01c0e28102d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 9183919 1250 9182669 9182687
    0x114090c0408060a0507050702030d030c0e0f090402040e0c09070806031002030c0904090309081005010306180b0c09031204030602030405010b030d0906030f02071e060e0a030f03090312050702010c 86
    0x89080d414030007008071020024101e80c001140c8a40002c01c0d843d980c3d01151207100340e110182d010b10a03800c480d04583c2d4140c3c00b010403000d09030b54180400d4500c4080000b41c00d81d2800881d031290b00800402c6c0549820341c800651403100c41c040703980e00c0c41c6204c0442c89070002250b1030004189501c0412026040c18425400070060b8080c046103140381c08101c5c8181402441030700c40c09581d40f2aa1042054051251036025110314030844060148854040025000074082111464105403282105102c055400f007000c5500c184130100a9850b4410b00c429034000314a1a07a00d80700705002c040ac0c0040d072400500240d4003442015a5900c0c050030410700f9151000721b940d010354021220b04240304c0d80154210107807185880c010034080807506d0510064054820301421034001c40b4803e0101d4511120f071004c0c2c06204e010180700c98901c0c00030480e191191044040c002c02c640111a05215209601c4a0343c218403034200881449001e00605080307030011103800c400342c0e540702800c1c148150411005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 9185169 1250 9183919 9183931
    0x17070201050103020d12030f06170c0901050913080702040207030809010b0f01050d0905011d01020717070b0406020901020a060e06070314060d1103120d050703060608090703030f050909011409 84
    0xa1086514550205c0c4031400c070402c1c0541095048054100741c0d0748a03800544680d40441020712209803554071482d07944881c220b001d0824482d01d400c40c40f060400300c4455040b40d030000c0031034a1a5658a00807507460260301011944004201300560042c2c0d664400782102074041d41c1c031000b841c03618000c260708484180a42030301c12402d07400410241da9000d01110300007420494003040381003403032070000e0141c022192030310718032801c00c0e0038000d48501c15400f4004050062411482c0721400208080346c620400b07201800e0300800344002400301c1c0d81a0010f0100c2034061044071002d0529072110405c83d01c3c01500945260892010b0240050380350003000980b104500c5002040e04040b4000340320300082050060134412a6010010070340d0f028010b00b144e02c014444c10795541d1f40717600c2c030711801004201c41c0300c00420314161011420703038412140144200c40328401410f00c142952800d40c2c1c2c42001c0c007051020004104540c8a0340d456040d4032500800742c0c0500352083c240c3d81d800b04560b581d8001c0038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 9186419 1250 9185169 9185171
    0xd0b030303040507051e04060b0702010311040e010603091e03030603050d0e03030306090a0e060702030c070e090a020409020406050a080f010f090803010e0403050d090302150106140405060306040f0c17070201 91
    0x1404045038000c00d07500d048400440700c6400001c0080381024a1002015400747d0151401c40700181109410b002044024800d0341e081050015500901c0c0d218005c0d80214000f4001c4000144107460096111400c03150003001041a00c80e07001c040c07030001ca050104102c0002e506d5950070404c110040080c0750007644036050120100d0f200c800840d030341c0c2c04002c02c103e02c100d4540000c101c00840a9100240342607000054139100c1c0b401450180d504c0c0d00c1071000314102d101c8c2660000d142502504d01600910812002c0c04500c0410b408020140144002c180c3e8440d64a240c001390720303660401c00c400140001c4020b04031800f034043c0c81d0340c01c403403001d01c45407005801c0000e80c0d000107001c042100e0542d09282c00c01449a01c0e1402c04480703d0140d41c88074841c02d8030340041d990902d60001a0102d00000c0e02c0c41e4040f85a03211101150713004400091003980040a21007440303d07191800180d6440030000c2c00003c0d18848415002065400c8518400b020480c844002c0c1201a0600704a81d405a42800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 9187669 1250 9186419 9186421
    0xa03020115140f1f0203070309090b010503070503070e090901090c0803030601050708030903070203060c0403050105060a05010f030f15170601060c0b04030806030c0a0e071b0c0501050903030d0c050d0b030303 91
    0x958414840c04071200d05100f103609400d5000c10740c0c3e55214100d51180100b0806024000002001e503403640014001c2d0042201f410000a0300110b034004d0103a02da8040e0b40b0141907841c0c14030165281d400140000042c0554550090a00c0d11441c4206118001c2c04d00003003840c03002401c181c880740d803264000d100700d40c00400c1004103698008003203a80f03555100c9507140c2d072991481070b09420360043c1d00000390705000f51000e000000900c0005041070701d00820003009540c5421041140b008031a104080c08220810490300699000b80e00c1800c0014200d68089245000001107200420403a0010303c00241d0541c0340c0450000200144c41c050708079400d12681d501040d031074120096100410003810811a0030028003030b510140300b241c080d180094240151161140914a007502c01105c5101c0001d0000841420422008101140a035008240d05c0592030500300110380070340c040d00003107800d480100107070036202c0200c0c40341c1400c8140950340c2030b881d03020640307081c000d50390f00045080c440d90080c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 9188919 1250 9187669 9187679
    0x303060604030305091c030305041202060708150a05030604051b120c06030a090803040b090105070c020108130c0f140f0105190c0606080d0507050d02011407210e0a03020115 76
    0x20803601500d8140c280341e900c0b045818005418a006c4070341031386180070740a503460100b580581010f03014510603e404680401c219004aa03904c00444410001800080111700e091600a0a009001d40041c004451468079000400e150030019541112554070051480e0040303032441c0765100d035064045802c6800f10554814107039403450b005d4003a030700c110300020105e03d03480c5c5581e021120141d0700090040d100e140c10b003801c04061034100c40516840d420480084c41d48d61148150801081e070507100e0301c6d0f403629203402007020384140810844134481c8640c80402d001c00b0101c017420040071188840a0f03102400c20501c1409020710051505001c82440310b0070481804829000c0c0030303041031415507001c0704030b400c00f0405044154400a800e001c1c00030f1142500d1341c8800285041806901290000781012104a0881381106041c3c611000b031080810985071140c40f54080880612286c8401c1120290080c402c4841c41e440849040d8401074030740003016028040c01c0800d60804401c129890b02c1c0c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 9190169 1250 9188919 9188929
    0x90a0513030f031503080a021002040f030602070f0b0f070f020d050a030e01060b0a020307020a0b070f02010f12021201030b06010c05071e03080406030506090c0901020304050105030601030209040504081b030306 92
    0x3094009080c08104074851040c28441e07801481c40a106405244c10341e9501c2c1492811580201d00b00b1005025402401d500722889000729000c6801d8500800311152441e16441e0003500301140854004030001c4c003a20205400c6140d2070b00512680d01c500410b130500103c0a8294201074241c01c0540d04091564051541c028040c0c2d2440042c070b00340420141d0104140c2030050049810280c030301c80021426101140d4008080c092491094589140c03494440f91400c9075402395100080c1040d08443ca10350041d4410f20450f0171008150914035102090104100300f0b9030004000c0c102d2203031108004206120a002c6e02c5a0486400c0c240302c01c1c1818292038080d00c0b180e15009400600900100c50890210105200c5000b1074105100540b13807510b5050040207800d098515a10402d00c01000ca050b0210300b40441d500e103e0144c0081d45041d103400300644081c2c00043c6403d05040e801e0100364650384560007070510071449091225a501c00030201500c0e03009280c4c02c012040e9206000708110742e110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 9191419 1250 9190169 9190201
    0x304030c0204180506010f0602070305030d0c0507061109090109020c0706110f0a0b090105160503010510030e010203040b06120a050c09090304080d0c1a1303080402040f1a090a05 78
    0x1464031039280304036030001c50060145050020445002c00d8500d000f84100030500034140c0e90240c030b1074005980d85110403a501c801d14000a000713900104901c47d5402016441010b07a081a41011401c054050b140c0d04201c034820354502c41020000542d04040746485072006001d0000c040d411402c2c0480b04040345d0303880f142da0180700180800280e0b03030a00d52000300100001503003200c04442d14082c1c1403a00c00e04400080e1042001c4d5803c10b0041058a44032070006030103180507070784e09820342c1c1c80c100c10400100b041d03d011806050b6076490328004404d081c0000c1d40300350b005072182c84080c01c00e0701c2841140740d0b4504000210b038014804400000c0d00c00304400c1500301c4121603482c169110070441c1ca045104640c007083d603500c905100110550b4012903c094168020303280000d0b040e410020510400394210754070724040d40c1200c03103040068010121b680c0c002c0e001400028801c10080840e90031118050f03860f805648641a41d61100e1820401c1107611541c043d10a0041d814001346144814038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 9192669 1250 9191419 9191423
    0xb0a05090904050c060a050904050f01030515060406030c15020705090c040b0928060e010203030f0703020a020a0203030301060c1103010c0212031305011e1406010504060e040b0301060605040e1b0304 87
    0x20311403000c10b0a20070b04001c00e00304400c00910003a03503415400c0f0003407ca42d0004210900030390134180051414040c1280040c1200d4000014041d9090069a804601e58004204650040d034600300800442c92904a0502130002c060300c401a840e03100c00040e140642980c441c611403003080042200740180b080684040741c2c41c0c009030707503220b80c4220700007040354540038003030089089140315075808487e803a907203202246d4035034807900a201d00305001280c0301d200031500002081c4601010034003d9110b64000e00e140400751060f2400315a040c1e00103030444e030089c0e20040004040402c82400e03c8103d1a00ca03c40d494120001c000d21049124041d494100d04160b02c5181900030001680304695200c4900e8020742c498000c0110703a0660420349181a5910101c003402850080d031003d9001c44616000d02901c2c1c1619201c1c10030f07141803c216040c54172141103a0300140c03620b0220700c090702d090040b0b1014010648460380c460341410740c0500700305002025141c404d4480030714400321804031011a03801507 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 9193919 1250 9192669 9192679
    0x50115050f04020706020f0c0303061314130206090d0302030a11010608060411010c0b0a0203010e0a0504021513030605011202040c1b060b120319020601050a0612020a030e060405070305070b0a0509 86
    0x4d9820036200a000d045404064800006030050800c000070000358030800013107c46252040d520170401048a00e0500420141d00481d40411044003603003c5030401e00d84010039842c500031048000c0380d507819421804401603400800c0d0f00348150f4200c4002451590a030000700862407501042c0c5075140070182010b400034810001c0700404ea4419403061072241e40068a103480e03410480f10703440096001344180344880c0290804204098140e01070540215002030904600d18400d0101c80601d86c014007013000d50600c840d00000028546001d014000c180021152410a499005000030b03284124906000c00c04000304140142e24004644c03841e06070000c9000440745484000308841075000500250544008200f00c0805190070f003031130304405079070750130b8403a180d0baa0024002d4903151409241d022030903000444450151650240c40e10140c1c42c0350100e241540c1030092030401a0655040d01d664014980a00501c98200b1015006043c1906d003140b070f0851200000f0528003481c06050b00c52 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 9195169 1250 9193919 9193927
    0xf03030a0c0302070512071104230a0b0d030806090601080c0409022d07020a05030d02030a080604021303050a05010c05030c090f0f0a060306090e0604020d080c0f06040f050115050f0402 81
    0x1080c402d40c10b88518517030120844010070003250101c80e040d00603a2040304c800311400704090f19030410740105020000c416000c002740b00d1000340c00103500311005058200e2030342d44405601d49942c440d000c2c0c00d503440c0661142e4032076051443c00d0010782013004000030306100c1c10105200c1c40d0302c560801c484c1154003c240041c3c03035200c0a80c60170007210700c0581c1241c010203038110340304a40c1c00b80c5000b094014400c49048103903d0341d84042c151101d941c2c16115015030010311640b2a41401101015803205004000501e004c0707031051400304c40c8101c1d40090741d042e800404403000f000400d200d02024051503050032815854030b00e0340c2e103509200c3d0391303080c03402040c42100d95010b0ba11982280244100d000749005625a190100100100f110b0710540ca01075040007480740b80c00700e000c6103250045d5006049094ac000041e11507000661000e10580c03018402c6251804442c0000d0044e140910722034270200d1031104107420840d0954480c0641410140c481c40020021130703a401151b200c01e041c040e500940c503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 9196419 1250 9195169 9195191
    0x30a0b01080a1107030810030f080306030c040603050309040903050c07030b010611030309071401030912030e010605040b0a0909080409020304060209040e01050f0105040c020c040501030804090c05030c0d0207060603150902010f020f03030a 104
    0x300720469000800382011050000d0800ac242c90240d0311a1106030304803511000b6002c10041501c8c414440546250020800a480d0b41069002903805a000303003840e038500222050042d240400560080e19030340094401481a80d5104c452401010407910045007182008041c1c1031302c4116901c5840c10201c138400e00e00c034459000b9009911340a400002030b10f81e40903d0300c8040c02620000c0600300855103005004601880c161140c0c504403103010f03000d194068101407980b00100f0b1a00e07030558a03103400f484002007803543d6000562113103114140268441076690306100603100c20807030074181a418107041264005e40b0a10050440d00220f4010520140e66036060b030401103114842c2e03030400d04020001c024010a0401001216000130003000b0880c0b40c183c04449600040d10455121402000b000c0d03140e10761707900039080080c0245030000708213580e40d0310424904480440d00001c2921050340314103540e0054040d019842c41b0780040c080e46400c0a0303655842e84401405e840845d44d40d00c00030a2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 9197669 1250 9196419 9196441
    0x12030f0b0402070507030203070f0303020c120a020a14040609020306061207030209030d2601180207020105040905010314010b030706050a0318080c03030405100b0109090b031002030a0b01080a11070308 88
    0x20039901400c115510343ca9420019161000e500040c2c2c02841900780c009112107607400318a00708c1750164080e01d14007a1441c204100000c423100d102055106107842e03100940c0d43c03050f254009200c03840e130151803041080103000607a501644107201980c810320070000c4645907003044600700c1c0880d4032070418039600c81d48190000d025004005815104071001d17940c4480d0050305070000c10b8400c3d40e46195111405020b0340c46070009000c0e03038043c1c124401200303c16007596000380007000c1c8141810340c106501c075400c040c100c0340c1c241e1040e40c01c050800040c0321900d60078072a0100c00003094001e404414240000508a4801c03113803080708059a51612241c004014606a48000da000280c166070b030209000b4a603581d001500c2c10b44150060014640703102c051031003040b40303156060710f0754a8074a00e4080200c0082c03e00002c0c2d160940030702c52801d0035810040c40110302c00da4100e0700c00180b200501d0001050103000401c021783d50361804806045020940d03003030b60f1105a1500e042069552114002c4c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 9198919 1250 9197669 9197681
    0x5070201170a0e01051302040e03090a060c080c03030705040611010b0105030105011803080c0102070201020d020a020a030303051906061d010e060313030c200f031f05070903020a0f0e07080412030f 86
    0x880551808061246c034000600010f030409000f04e905104040c1c00000c3c0135124810f940907960b100c00441401c00c2210301940c12200c0080c050400c640c00c2c0f2a1002001e030440c0c1c030454120002480004d82407150681142ca03c2c05809080c01c0200a4034003260700280c1144410300541c2e05000000b4900410030300705500e4240519072010149494030442d0120340d002c0c0d000180124007502548420852462002640031050307070700184621a01407031078405900034540940446044440c0070400c0c8540401402020010a802e5403818032200745501003c0240410940d2581000403160407084e040e50b86034240da41254400c0704410804d207440c50700340c908100380c400c000c00700d03400701c08454a1000c2d5900000340c825810341d0b0b44282107441004240c2c603640f5844204c10a030b0b650354110303182003080350b02c030a40c40046418040307011600c0c1e400080704484558407a00d01c03038a00d000d0611088248520186d00040c150504203a141040e81d00c0d204555006403800d810540d490008120040f4550010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 9200169 1250 9198919 9198941
    0xb1606020d02090f0907020a020103020a0302190903020901090605030604110f0901060819060803180307080a0b10140102030d1e1a0a06140a0804050f0102040803030106020c0105070201170a 83
    0x45540d0460401ca24000c0d4100b10b051500c158040c000001032070500e140154851251540a011406040c0e0300550081d0090b00c100c0080641c2444400c0c0b0b1000c4041d21003001c00c1482d110b44d40d00c0c41ca90f2040010303901c0c058004e1030900b0306060081115440c0014615001035014081d071114000c2803002c10135801410003440d80c408040400054215084420507019204c8035800c80303504002c01d0740c9001540c1091081e840643c1c010003030400b003948100940030749a0401415990b500c0c1d0389181c290b01e0141030100c1640c0310070001d018000103003402007448005016401515540c0d40004002079200e0003010400000541c03550200d401c03a48012402c4021a02c0c010350412222070500e00d4401c000d1354500d1074a019a80c850b001050903405640c2158041ea40d0382c44075403610600c804111040c14010340304a52500c61580c032020028420300250000d0800c1c000199200e626004000703141c0a91140c001d030600400f001144050b03640b2031402c02001401c3c00d14040b50307460b20500700000302816150 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 9201419 1250 9200169 9200171
    0x30b0a0e0303070819020a050a030b03100203150405090601030c0b07060e030d0204030501050603150115111005160908070306020c0a0203010c0201240e06090405030d02040e04020111030a090b1606 86
    0x2c203e01c1d15042601e150060445824059881c681030095504030710441c810b5101060050055500e25403103034004801111380070f0103403a40e07410864840c4099130000e4904082003580c0f03880d0010503040c644542035029501c10700400c1c9a526640302c1c0e4080b0310703140c000d68800138030001e8040207004054006070002c261503000c50356281c08816242d4025005400111459403c120100d1154640001c100c640d04031141040034459103001400002050007448100c18804103c0c21607110490600503804004110700d0003007424a4a4101145154024414007052214401003804402d40004075101606c1d4441c40044c1d1f600c0041c11024030301185031b0742c020342c035600340900c1e4590142e0640103e41740c40094850a503001900c4c000e810f9900b2580e0080f1254071103103c0000d1020700d45480c00340e130094011015645411640000c0001380d81c81508200441ca01c031205000455a00c1102c0d00310401c2c610002e541040c4030000014000416442074040d40c3d0000300c2c000c0760400c014030744501c0320b0f648094 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 9202669 1250 9201419 9201421
    0x4030507060906080a02030601080c090d020607060209040510030b060d1106030907030c08120d1104030803130b0a09020d02090903190315050102070803190c0b04060504150213030b0a0e0303 83
    0xc0020b148000c20b02614000442400202e080c500d0b80740252806240140c4402c0c10999030408080c886402620549620410340000c0d140940ca07400010b04070b0500402c009a82c1d08030003424041500e00151105011009000e810000300d0003541c0c4154220004440340071803008503043c0030020303010511990f580000000144080411b001580808803845424090b081c1592209120b40710407c241010214074010060340e0412140d50b0700072014a9200001c0c44c1c00d041d00c0ba00c503800c00b40c0040b00d000c108064000381c40300c14400c140720754035441010303024217020000c019404a120003c4c8000005d0213400c104020562481c014030580d02c03400d41d44103001c118129144801405452005010160603100080203e9554804a940c81c1515070300e000951030404981007100050f880714184408003c00116a01c0008012a80c0c4500443c003511000c40e0074181801e00303c2d281302e914101082c1c40c920410114034203940300359414003220780160000e160340e40c0385000303c0042d03c141e04003034241c1c0c00004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 9203919 1250 9202669 9202679
    0x4020f0901031a181806010b0a08090607051801031419060b0c0d0807050f0708121302090114040b0405010e0f011205060a0c1b05010507270b0f04030507 67
    0x540380040c0241c0e01403180c0e500445080c111100030a84598110040c50009188a880c40a81030741017050f035800c141c070007010001c00394240002070f04a5091000000303400201030394090300311904a0383e200007805181c103054001a01c1c5214602c0c0c10f0203011203d040d812141c1c2c2c00307684050035284c202c100c8500c00c1d29100000340b00100d0420788451040d4a89800070600d0b00342642542d0300e240c0c03500001e0883c40c03503900c020b0381c4c03100e0000d01200420404100d42c0600c10100009050500d120740300a03600e84054504c007031002c40c0001d00354031003283c051514602581d54860780703038110313a0040120f034403a00c082130102c1d001d08281d010283d0407a08040000601640344030f002da01c2113041d070019400796621213465502d0480c218a01034a9035000202146140801707a00c0b000b40b1402a040c500164000715030b408140c80000d03281512140d548504000b41c098200c3d0000d4040c54040216114000c1881d0040d2441000e42c0a508007151b004100c0559403006030044502840d041012518800d90392 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 9205169 1250 9203919 9203947
    0x3030712110f19020405040c030c030c03140607020c010e01031d0303040203010c020303070207210203010c1107050406060914010c0f0503030603010b0901061b2102030d0c0206090a03050c07050402 86
    0x600001c01c00c030b205400801c000b140020600500440c0c80e0001c1001ca000c1d50b808010203007001030070030303501d0b00010400080005c812000c403800a6104000702c6a806185040501101d842c11b5940d201c990030600c1080b425a501150b03400c0d51450034280843c200720480012070050034140325400d11540402d50285030b20000102a51003503208900a005080d80c807402240c5a0000340e80d80f0b00568047c11085c09280b0740501300c02d01c440741c00d800c02d019044054000a00b9900458440c40102c0e00760814184c18134420300c1008064082904d0a1011501d044001428000750f441214510b841010225000d0381c807a40c01058a20b070445015182c2e58840d04100e92254010b8521610941c078014050842d4142118030398103d0f00280c0314900c0b52105c143f0741a03074203404c419017100c00c110703009114051001241401c0304d084d40d49900854950f413013900c40c2d8089603007034205413082d984094100000008005000c0004541c585095a12401241000303803a0401c503810445e8040e00101c0c60303440032089 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 9206419 1250 9205169 9205187
    0xc090a06050c07050d02130f0f0c05030403080105060301080a031107080f060f060405040c0506072d050708070b0a1805040f09021c05030a0e030705030708070f0e0601020d030b03030712 81
    0x290030a030f40006036200100050a0b4240c4002500480310702e2061180c1171841d442004030591140f4040752500c0068205011a11030300313400c60203e1004404d210a05a006803240d000d03041c10340300c003842d55042400f1580d854454800003010030403501e0054a51500904c00a402007040504032400101580c0f0070a03151001260005041700c541d0002610b28a01409000d000d1508040d90000c054100024017101c1e60007001c050362243c02003e02c241240f800c4405280780c141d0310718480e803820042e51030300c241015141c1e0b1000c8429403201c2d02c01e01241e4080c0d0102c920a5142e03003403040c040d0303034005040b00915000368003803540310b0302d0544036408281c82d03608007418642c802c0703c0c07050000075510148001e60340c047c040903004c4d600a10542c205140608040101c11000504485465a03030b640084d1800c00700d42c120040b1a0081241044121242900c040c0606140c0c804815980f4042000035a202100452075042540701d031050303010703503c06208a98910707410410754180780034076031006460014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 9207669 1250 9206419 9206437
    0x2030f060a02040303120b010507080d18110109060e0604050f0d060207030509010f0f0c030807030b03010203010909120c03020c060f041502061801020901050304020603040501060b0703030902011b0201080604050c090a0605 97
    0x42441003125040000f8811041f003907405844075400c1c04038645031407601750010341c03e94400079900c441c07051414400e8a01e4000709031196001c0513000700b2540c0014107600c2640c0c0040140050301d0399400e0999180340958003070b02c800340e0320342d40a07909283c005820085d0719100508198400a600810706a01400404081d0803c0e00d410f40891180b0310100d0381031152507252400589280d16548c0000d00c0b90301e4282d0800300c0341c54042140b03440800001c0c00c903030080e441221841c2c1c1c0d5034801c01c01c1060000401c0803ca001e0304002c4221072a0381c07406034840302040d01061141c400000d8405008181405031409092255045810035101c800086e42e1141d0030345020803d81c001c0c0d00398030b51400c0c0500848000c11010713946d039411600e9690900c815034101502c1210195203030314000c07a011600f0b01c05407020703d020799000325000c4410f0001421000301c1b001001c4c0400407999240d005030340c100380000e4221900381d4000400e42d44035084041c10340078811a031071340900710860000c0c84590000c05000804 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 9208919 1250 9207669 9207677
    0x904060c031a030a0b0702010b030f0703060b0f0a060507050a0605040b15040e120f1917010b0301030201090509070e040e150c0405010e01051308010c080f0906040302120702030f060a02040303 84
    0x421408602c03214240b1110115070640c00404640c00003204148220b420018038000400c90810450000341000002c1c0803140103980020001c006008982c00307684040710056614105408600c0d0208000b855a07029132814450f0004143c0e0412004100100d1001d400c100e003000035040510f0682e2100c0740944502105101e48242c0c0303c11440d2600c0780c1150044644010f0102a0a000c0540302a030410213030703000298800e000e07200b0031b14980780218249920598682c003080041d900384610000301a08905040390081c0010300050340c10000340740a884080b034455003260b03205e541c00c6031038100414140e60071904120022503a410006950240f5111111080a040d9035949031301c40240264840c00d400601c14006402065000f840180f5002444a01c91016036840d0000d160954060000090000718118100608105040704207504000c0000103000282020746009583d44401e40d0400003290001984070115a01003080102e000c8004042e42c100d890820038940007900148412350100f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 9210169 1250 9208919 9208931
    0x4060911040e06011a040b0301060207080d140406080a02070501060602100c080f1b04090e030405040f0e06010b0f040e1e06030a05030403060c090806090d030c0203090a0506090105090904060c03 85
    0x181c949806501e0140c080344000f030078103030701c1c02c501c0d03030303440b044a11259850183c00c00003c61220312400086010301403a40080c5421454840260b10340051005e01e0410441c1c002681460710000303100b103030111203861400180c41e031544112040244100c0100401319840c010300006c02c4c50700421024410080684200654480c07140c043c1c8101e003013210200e500d0341508002415003038200c0b519041000d40f0810503420aa19001604200c4020116041460384082001c00603442e01c1e024440782d903503e1000512000448210042d510710b018010035042050116040c1e02e8121035a080e40d0080054205034050f5040120000c084213240d0001c001c1206a010700158450500040031913003c0d6200d4025880c091035600c60720014104440c020042007a28040003502002c1004841d000d04801405810942c00340303c00513040b03420780b180c690290b42040c8640c07540d40e43d4200241049920a4480c103070703184601e00c0100d44a1003041030082e4801c01945c1448240915984010541404c60300c0c03c00c07103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 9211419 1250 9210169 9210203
    0xa0804020405130804051011060108070302090c040b030f04080f121b070302060a05070314010602060f010801050606040b07020301020702030a140c01030504020d1e05030a180b04050d0b090a020405040609 89
    0x2a00201a001301d008000c1004281444180051501002c1c580405290030686401c1e081080a07407101803154840341c402e0003945846a1180c0d0001540002d03186450718041003915030f40401000d102d0420b8400300040e0901224404841c010b400800080c5d60f506480000c8101d02c1c00c4c10340d540c4441e02d42015003003810301c00707020495498640580080540359112002c1030050800208484e04258407a0a010040300180c0f00080c060581500a032500c0c4c80e05070b400003085001680205016030412051000c1510740004441c251100111125a00c01250010078060300c901c650080d010704c19074900c0020b00950b01400c10040030910255019009000011000e50300300788c40195001d0100000b9074000384200c0c08010200016082100c5580d903180c403600d0844e00301c0c1c40e262012070320400c800020888084c94072000b8044141165081c2810700740031500001400748020b145105079004501c542d00d08001c140c05032030740100180010324243c41c101d0003402e01701500302c80c10030304803081902d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 9212669 1250 9211419 9211441
    0x1060801060e012105010903030c0807080709140102030f0a020703050d02060403020705060d090c06050d060509040c0501050708040f030c0e06060304150b0607050303100303230706021308030a0804020405 89
    0x21646140c80c0d08820f6428050100d4840c036142004a82e800a210800703400108213000d82200d0a000351400607189a0152002c0c0510500600c1078007040b095104200f0351756004600c46040d141d0700121039a61995200c0183d10b948100c0401d120b10140c081202003000d640011006c06692043d003e44620040480c1c050742d40d6002540e0041c0136030040c40050029080003000380c18454011000811030380303c9521014588074050300180001030001030521820381c0d40c3d0107860020301042d62446070900d05519a008600e68034050306040060000311201400038900595020303100086004242d05c0da2840d04c0209246580f203403a0740180c40000046c0c41d45030403001d03244142e4001d408114010058000440185403240d00c04d580030509001000100b242000170307500c0f410780001c070203104a0a5060140c110b410f0f45c192400d074440c0c0f00c00840088242c010a40f41d455600410168440443c00000420700d03140e0b4100303c80511000c103012148591040c62180194000c0d14108841c2e150f0307a407890 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 9213919 1250 9212669 9212681
    0xb1005071a04030905040c030c030501081207120302120702060402100503071e02010609090f02040b03010204081c0306030209090109060f060503030a0c0204060302060c070303080c0909010e060d0501021b01060801 93
    0x340040440c00d104515400305026260342c054030900d414032030a500c480004049503c0c0107140d40c0020340d01c1406801d41505031007518090518070000344889212608030143c58071a480e0002c091a2203901c00c0742900f402601076030410030140c1e4000780e0900c0c1411700207541e200c08407016441000d142a181d034156000c0c2d4216801a1820303594400034550210007055100701c00c9809004640d41c0d204005032041e01c500c0b80d40c070741a01c58080d60b0520501d80c010401941c0e1856640ca100e0b0f413040004110800000948841c10800c01c0900d4401c07207051642174000700715692010750098100803c2210484c07040d4040c44000d0f00c075480030401006103018130b90440e203450054079050f900030440201c040d805501d20005c2d9a100401c0415080c0d12580814000d0304400a901c41980c010b810500030940c0114202d90b00a205540e500c0c1001c91200009110001c1880b034580c4601f1b0781c3d00859682e4860f00320200c90560450000d540e1201d20014a00315415480e50507642c55181c0500843e074110180110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 9215169 1250 9213919 9213923
    0x201240b1c0f02040602120f1608040306050106030504021002070506090d05030d060603090203070b0f030a02031e04050f0d020604020303040303031107150506040f0e071502010b03030d0b100507 85
    0x40006141008501840c541c020040030614607001101c00050782480e01415050070344209001d03843c3c03131501c0c4010380781440896a180c144002842905881c00d809015180e18002240c00c0700342031000f40c10103041a1213150405004130781000004110150140c100c01d015a1090b0740c0c60401c0c3e000c8500880e2264031601940364802405c0228002516041d880c2c81c0740f0074001c1d01a01d1500800e039805034200c0d86150702c40b002003922108000191b10b0b00303100c0d1000038400b407003040307281541d07500c004c440c01e01c8010510112540d011001c20522150001c0c012210800302d00a80a54102800c00356031320420206542c00c5803250031001c1d45441c1c07001c6040350066502800440c1014110340e402d401800018004055106050254034003180303050300d6601810704040c0000450381030090030302003a90104400344145904020a0110003900000c18800701c3d0042c10640515031002c00c022400740501e130400d43c0d1305200101d1801d42020456100103003203001254407600d00c0d903000c14280d503240910303200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 9216419 1250 9215169 9215231
    0x302070509090708150108010c0203030114040f0209030d031a06040518040501090b0109061503020306060a0c1b0f0801050112032c0607030201020306040b22020708090315070201 78
    0x400c0009003001c554075038001d406002a98000c503202c0c0c0c241c51800d504003081c40001c1042200410240000b0310030311b1b240805500c0614907641c18a001983c0040041700964007031071362507161030703000c80c46a0705403070200000a007980c0c1050164500100540640100380040354005044015a8601001198104c0724040c204400c000d440e018104200403000700180c0d01075403600c00040c00035901064076070113400424400100360342844010f052200d6040100c00901d48100203001013a516841510112001031414160900d02450321a80c1c02d40d000c00c0e41400c1d02c0040802113100315040d5200303816180008000c105e1070ba61042c00465000b05d42c0c50150104202c0b610710584c3c03004c00c1c5c10340d08800c006484060800c10b10100800c4c4036a0046100303a005135400b000340400c615082c0a240300c9094100c0d40c820030b0600d20742103000d030f40094401101c0c00300e900154010070429482d042d142c03014402402d0f642c001c1d015800c501001c40301103c00b94019440d00e404140048004040300b11304e903c040c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 9217669 1250 9216419 9216433
    0x70c0201050d15030305030a0507170f070201110313020906030d140d02070209040b06040c0903020901090e010b030d020f16080307110102031b010606090e0f0a09170a0201140f040302 80
    0x55400380d02c90300c00740d4041030b26070f11680101120240740d200254441e0fa03400e40d807840c0c4102d1000032100d002c0d280e00b042000c000200700c0d040d403108661030380103010002e091905855149081e030040c20907071181005040301204114002c50141002d9007054000e60f24147c03107940703180402d91142102d241d401c010071000304080c1042d000300d801501c540b0010f40001403400341e280d0001421048111421075190005030104150340c1018080c0c42401d000758100b110842e42598000380e00040c050040d8240c896a900713907018070000035003020300c0c1c60740d02805451211100c140002d4032000d100080c2a03044c410310700c14940440d000580d602c00c5490001c00380d82050701c196500c003000c0f000c001c5114110f10090110116001d14600305c1d00648030044000a82c0a2800801622320201c9a122122020070b880c100205036003c0346031701d5400f504014002a80030b85500d0040e6105c4001d13440b1450509000c600001c40640551041d18402d0b8442c0c000c001e25580c1084001d400a0f080b28000c00503007201d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 9218919 1250 9217669 9217673
    0x30c020708121c060306020318012903120705150c03040305040605070c0306180210050a0207030b0603031603050406080a09020105090112020c031201030b09010b0d031103040902030c07020a060305070c 88
    0xc014107040103880e21020140d15804003c003059030256001a02c03415400014801c0d030480781204032800140d0100280008051b101c151702101c89401c0409000f9220000085039642c0c1c2441101003070035924a200744c0307800784d604103165901e06403010441494440b4010804c520031520959100359855a961403409040c044c0464880e04100c3c01110646800c0c08040000f4091b402140180400350700c3c1084600818010482d030310f040c192034101808020451422225401700c0c19200b50b9801c002450844c3d2200c0c40424a18866042c1440d13410315452501e404060344500100115103d80d0b58510f07458550456800c110f541d0944001c1c0071078010001034820754090b40b03044a2180611100604244c2e12907003090543e03002c544500c0d65000c210340103108103e02d840c070103508490968000c02007044110041854441840000380900c0420b40d51010950b004100700c80161002e00c5c825034590400b02c0a0300620b8104c114220f04c07400c0501400b2130300320b110340f0429103d03008907612200c07003203426 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 9220169 1250 9218919 9218953
    0x30d090303020f040602010f0609061409040c0305030f070605090c06040e060d05010c0302040306050a0b210c10030501080c1002030a0302070c030206030408030105091302010e040c0e0d12030c020708 87
    0x11021001d068080c090054501c0b480340240c4001e000c03580003c100c8603544070b04c890403940c0913040303e40094034104040c4844440b08803c3d048461007510b4450098503141010301490b00c0b9584014050311000842003d460034000c007409450344680e5040c07000c0c1d294046100d840b440d04482040e0001c6052004001c02c0903a4020a80c01804c080c0020300340201d141ca4042c03c5d09e003188000004a0b4000804100700302d0a407090550040c1490400c00c40c403482c4000052000640f1400d64041c224070110315071911078180156000194010a0000420040f40d070180151009104121843c000e862030b00707050b42849050000005026400f552408080c2c0030250000e4120450640e24000001004001a1142001140264003a4403419100d43c5410104420750200503c2100401e030030041c0c440050740c11103101c1814000c00c48020400170a1820122482c008035501c141d4000340c243c032001c0900640050011018000e0340e420700c10806844000d9948640500c11900c1c258440030350340c4030410300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 9221419 1250 9220169 9220181
    0x18080111070f110907081614040603020a020709050f1602030a08010303081506031e0603030a0912030c02040f0501080c0a0503060c030405070b120702010b04050105010c020f13090506040209060102010b03030d 91
    0x1c03500010078200f074154046020030301c2c1121108042010101031010392000e0140311252401c8514283d030717856030600c031001c050340a20711891080c1a0040f8190407554020300c0301001500280d2010800c5241511540c00c2000064035146a81c0300c001d041c11021610100c12038180d002d558540ca8450b902e1503800300c40d6070100030034840584101010414507a41c40744021409414008927194102e001160b85030002600500001d102e51305c100301144000e504103003040100d030b041460144500d0b809050940e04d0f40c1081d040258404e00d000c0300b0030100b10496001a060350441821608041001000c0c003556003440d000f041e6041d4008400100c240f18608001c0d17034024401c0080c0c460321940c8002584043d004144820314810f001401c03c20b04c103a0900c5202240c5508071400d101c0d651418001801d001d00400b00030380200207103444080e145d212604804500b5a500904108880c558200152a0b5005441c1203229040f9603010600540c81400b65010000c0020080d601d0030800390488001810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 9222669 1250 9221419 9221423
    0x2090901060504020708090a08030a0210020d0906061215050c0904050a0209060a02070312021b0918060106020c0103050603010e0706050c0106050406060c03030c02010c020c01050f1918080111070f 86
    0x1d216840851a0b4545002420215118034041500c4142842c1000034103c0544c10110407584184103c0341a03644c00100c0c183c5995002c1001a0b4903582c080f82000588401d40340a0b00c0303d414540001048039140c1007001525002c0c2440c4110241e1710b400b0001990026102e603c0d40d00000c1c03004841c640317002d42c0025002350180e800103180030540b03000306205400450880d005a04062010400c2c0145116030020034081403000d4101c01e1014481c6060780702491704202e0085408a0029104810281034148000c1c070b2901150032540c2e444a00a6840401c0e81c2c03c3c500003824000820040c0c14140640807114840401501e0040d0a1441c102c0750b42d003140d071809800d5900d9000019240d1540c2c03040034090096036a0303500041c46a03040140a40d01e4241d801030440e8982240fa5822035404120401c400d902460440e56440380b0003031180c918042d584508501480b480400c2c01c00a4110040302840e903c80d01d80000500c1d50ba51042c1e01700d0b02c5800145007041070802045001400400d5402e07075080c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 9223919 1250 9222669 9222671
    0xf040204050a0b0403030f1103070303091b0906061101020705030301050f01120e0606011103070b0f0601050409060906090c020304060804080304060e0f0c03010605150904020a2c01030507050901050702090901 91
    0x558840c00070350b0340181a8010005004000380920034142e1011030904094210306000e01252040ca0320a5943d101d0010040c00b0540d0b500d00d15002c001001c24081c00d54103a200e84401c81545864804000b00124441d100c0070035100c01c1000058007040c001d541420350018040c5045a10b00020b02c58105105006141002405904902c1e205000c2c4a400200ca0b00c11008103910701d084400500071810800c0e5580d00c580c0140081d1001a1815151030f510860140040d80c0c582ca5078001a200ba000c0c603048520241d0619402041da585954002d1044502500c000d02c070f00211600107984911079030080c1c5001420400000700420196002190000d21800e400a030b00d1241c00c180034244407405030401d24a40001001040e58902401040041c01c3c08444842010760203040402591069560083c0503a402140f0000b103980980201001301600d60705010214100035004200424048041030120340ba140200d19020f1040b81521062801a102d0900c1c0680716001c200d044100209203400075 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 9225169 1250 9223919 9223927
    0x3071802030a06120507060e0117040f050f030703020105090d050304030915020a0b07030b0103060803090a121a040503070b07051303060f0e010c0c0203010b15030c0304030c0c030c080c0a060e0f0402 87
    0x28950350342105005000d030011b0642075051401c000c01007141c1400060401c085102122002d0000f0404682c000c2d0380b104a02d000700425180c09810103410041c48000c80c00040f44140c00c1c181c0642069118003c03c0b000da900301920035009844500007502c010f00040c2c3c41e0380f81030144a200c1035640c042c0161900444203294096a104000c4100895a00740029181c4107070701c501c0d5806001d894080d004040c06581801e0984002c5294021a403280040503c02080b8020500821044584101d8240d1020a0061400e41480c80d0f52340d208800c1194280701c200002454144203500380d032001000c1d01f4100700154034689610000d0084010261030710780d528040702e44052000d12400142c91306c29241d055845915004042c21940f42c1d421241c0951086104040d448030408201d0381d004100c00c21280c2c60b52254181144d00c4801c03044010b0407400b00030004004c0c0072040ca404030440d4425021190144003a4042c804002003600c211404078851011018292900564102c1c804001600042c10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 9226419 1250 9225169 9225179
    0x14030409050a020a08060a06051603110102070503030402091005030c0909031306030c0905041103061903150209040605031b120c0d0804140102030a0905090c0d0504050601050f03071802030a06 84
    0x1101d4080c1c03407071036580741c0c002407402c0c00c650040c20701588140704039810304d0705920302031000c3c21034403030100114400f00b80c10072080101405699030b1030b200c021600085403105010b143c000d98035841aa0140d129141001c005108441c226a22078103540014028060324840c9505124001c80c003d05403044a01081c040081040640d440c064000d08a960b000300f96a4102c0310084c296030025006280502c2c2090254001a0201801c598001c9015260b0a4110407030070321903140c140b56504020150030340c111041250411640242c2000752084904002881d81d48040503a942805646454428a125503120041c5414400100a0b4481500362404000d55400113046682040700032550740791b0100d01400768074641c40b0480100c1200b030000318030b002d9032240081d03e0140c50303104991107011040d001420b0314034541c054079480020000c092190382020710300180ca40c40b00340129401043d000980c100350307103000103c48046604420080c075580b400203403420003a500042928204035251400060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 9227669 1250 9226419 9226421
    0x905011406030c0d0504031115010303080a020408120f09121b0405070e040b01120e030304051501050306010909050a06050a0902040f0209100c0203070e070c030306050102070f06050703031508010c02070506030c0714030409 97
    0x9c041d020004010f1800e40c1036107030140c440c0340040c1c1040f6001c1d2043c00240010721000410364281c0300005089a00e80f150035224212724840d00c0f4071241c100d414140118101a40000c039503084030024203100301508036240070b000403a40c044400d0310004d10a001e1641c001d007065401a2012403040c50010340d01c500b00e90403401031741c0c070490303800c00194800030420041c440d05002a103c0980c41141d0350080303524000c006641d640040c000c12800a41e0385684c00e0030044204044042c6030390060050150b85081ca143d54001c016000d41a4000c03410250844007103a610320848800c10001009000106100ca1040300c02c0039100d0000c0ba05403182010104000300f5000784544502c06541d1803128440c194078004066507101c1e44160b043d588445000e000c41104202828265141c920f0215124640c0341000c0700980184407201540c040302c0200412a0041034010008270f0685801300e910540d0f403802400709908c0304880c001d45505041c0112000500b481482d440300011680440b801c094a40405038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 9228919 1250 9227669 9227683
    0x30406060b0f040603180201080c0a0207030c0e011d0f0112020301060305250f0b03010303080901020d050702030901030e030301030b06090612030c0d030518071503020d060905011406030c0d05040311 87
    0x1c141c1c80b8003040070440d00e82c0c58019603c403144400001108800c8540c00a003c1240c042d00340344502c80080703070902a561080201c64000c2d50403100b032000c99561032100c1084290280a0700c032156000c094a08041d11858405074094407550307200008076880c02c1c011b90240c010303d0b80f0417645035403155000000700f50100404a00120b86404a14014051100000f503400b180e030300c0300800e0300301c0318410040215210705032411a038250405601e1a5100803501e13009110300c0c611105451b15040501421035030010240900380000c0e03d04000c8141c00d161705503541d0100344002080f04400380300282c0c96080100c01c1ca904100007500040005911a1107582580c00030407000300940d010180321424a6458001d642d0402911140c001031450300c010f085449000a000c6c8100780d19030034030705800e0a0b1290f4115800c420281c03901700842c030786803509203003d02401c0c0b24a8401c0e424000e000a076510f400000c0300e001f074290f2040303286440b19a100034009040e0050058051201404699404d000144999 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 9230169 1250 9228919 9228937
    0x3060405010515030f0307060c03061203080103020415210c050a0603050a0501050a03020102060f07022503050c1009030308040201020a020a090b0907050a051206060c0f0609010b060a05070305030406060b 89
    0x124035880c1480c8146900d025040000d4442c5d800001c0b501c0c2441004421181c0c010b07040794010403080003554042c1c1c007400540e88500b150320903035034021040c90b5000000c14141c9208070b4040c00004140b245da42520540c500405142500075a54800320f03000c982610041c462241050081c26507030f03000000c0700307401181e1001c008244c507001008102e6095220300f6016107000c80e02000c10340e05580000790f4500c00202100c8003004588082480c0c0ea00030014030820b1604100030320030781c00c1c069006040b000301c0b0b480121018440e040e5064941d2900c58a900e00002d00ba07600c4a0030146035450407951000b0150080e41580110b0150300c0150700c450310104060841c00700e02251000a4405110100c500113110030200b10302480100c15090344142299000b91030350700342b5410b80e290b03600085c0c1c803803040404030718080c450b208151009020228000d4410034489008008103603400050110741e115104110380020420811030000901610103550410b010303200002c0d000351968490031807a4405000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 9231419 1250 9230169 9230171
    0x3012d0b030c04090b0301140109020304060e030f071e02030a0b0c0909010f060806030c0105030a0902011707020f0f030a050a120902030f03040f06090f0303080603030d02130303080601050a020d0e0402090306040501 94
    0xa01c0061107a0240d040d101700c0c2070b402004081810190342c10b0b443d50600881e20502d40000216040c00a0740c0c100790b03000e4042005495039140c3c0400351000c0f40d8030444045a00a288804041c14144d10b280c02c02061070300a000b40c0312041c034a44d600a0186001407103a034042c4000d0044212944865a0f95400381c191148080c80d080d040c0301d005840c17080001e00142c07082d07104101e0a559a6445000c0c2c2c2d40124030940c012404411520050f18171581c490307401101200500100903070701c2d500145212400070140d0940e061500e202c0304558803880f90100200c04207004110a0840310320491400f500310240ea070001403020143d5001a08000801081143da60710116062004442c039800a1000f4900c1c2d04100320030760311b40031030b4882c510705a21010f018402003c0009003c0e440c1072080328216083c80741d0441d41d444d04044142041000c501041d030004917044002181540140e0844000304801d80007064841c0940d00d0494412560f805034642158007801103500741e0b21708100e818060340c03050740 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 9232669 1250 9231419 9231427
    0x60402040f0c0207050f03120d020304020f1008041209031b03050606010c170a05070f0b010e13020d1103070f09060503010e0114070503100e010603020304021503012d0b030c 76
    0x10081500c04207000d01d4009890b05044940c4070350000b80a9044481c1035604084103004480002c0c24601c3c98001807011181c00075840c0c680da01d05a004511603403080300c07045040e8002400740640d60788803404400104044e04081070101380006c0074401144620300d0003000680d2070740d9400c400c2070314840803503400590340b000c184100402848525440a001c0c40c0052100d90144c40d200d024800c00c1216900c2944009207880303900d4440c5040390441d68002280381c02040240c0380100ca0300b4000d1003552421100040890101c1d25003ca820140d290000d00c1800c90810700e8075030310010240303001019030500c2045c1001803100c61400030340c0000c11040700e0004400b85810305241c00d6600554601ba41640750500310100001000381030b5801c914503141080d03d940d598040c21a000c00c582d044000c0841541e070000402c1680b40d001948103610035108006c0400d403001c2c41940c0f40c0020300446a140e4210240ca0640300c81b030205040e402884840020000ba56844d0301c1c8002e54019200b1500d00c134070000d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 9233919 1250 9232669 9232673
    0x20c16090b01020c09060a0608180304080709050604050601170a06091b090f0303050a052b02030402030c010c05070501030b030102160606031703011a0d02090406060306060e03070b07060903021504050604 89
    0x3114990500074140c411702402d00d003840000ba0044070034060a418400b4940105004130305000020024110070000c4940e11500ca1045036a03c02c0e15129507404135041c04001039043c105406900c0c01480180c441c1024910140c4030303850740010041c042614169900340004010809004d0050501c0401d40010f5826080f490000c00d0300780a50030411510840d2841000083d91020440701c1100851a2960b19002a0000425501001d800d802c9044511055200c0d01454070750055002d80c0c0300f1011601680c14120040d680010340c2d800240094001c52000c001950007a0420303065007100400040c9851000c1000b80384242d0580815540f00f80d40314014010817110010340c0c04110744012481c0d045602d02034202000d413082e490150700d032400100f00d4480b20785840e01a9810b40c3d500030803d012a03521150002c0042c280c61240b280003907030544c10b600f01802c010a0740030640e03000d00c0c0c0c4503151105a40781c28014001019080303045109541c000800140c500e07503024001c80c4640c0c05020542031074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 9235169 1250 9233919 9233923
    0x705280308031e04050a08070c0f080303010603060501020a0201201912020105010b0708090f010c0203060a150504020408030405061605060c04031b06020604030e01021e010b040c030605060d020c16090b0102 90
    0x1070818041040700070084c4404a41d000070700b1a0703d00c4d0300440c00381e52500c441c0780c0400d4000311a4025006060440004107404002102550503100c0c95507080092690b80d9004a032750f40e0080101a0105131345800c0b00c07140804aa541c91110310605040380c481a2605100c030300d0300700c1d11403001d613400c612048a2200d41a82030086600403d000c000c0d180c1491341a0b1146a00e170320a9564040c804d5616030816501070340240b100744415a001030949100745803800b8080b02508a0301819101211020808211880d0500c01e40f001d68045800550505003001d003400420b6202e122101d0b0900c101050b003000046040000c6403081050618060315146140b03041c9400740908141c5020707800340800c060240660014501d54815018500075080c50031002c010303400c1141035a5038000d00301c04030a00cbd00541c0c005400a1400c600195020010100b500d00c0440840b0594026150f000c2010007614507010300507000b5002e192562000c0d0351a011703803c28040c0000b540795012030710b02078a400c0710450707a40e01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 9236419 1250 9235169 9235201
    0xc020405100e010905070903060e060a0c02030309030d0203060d0204020a11010b0105041206050a0f020a0c02130e03040e0403020f060106170f01030209010504020a02191a07020f070528030803 84
    0x12100e52071180742000d4460000540500903504150b95503000114610302c1aa04103000b5900f0490070801c8080c00042241c580c10111494030310a801c005065001c50b00c001f08481c8a00c03034600c081c50405207403020040181d480034201c80e0340b100419a080b000340c0d44910007004039103042d880c3c103400082c41a0401d42034a41408940d8140320f01032008111001a000c050f0161550101001900d07540e401001d03401002c0c81c0416212081c40890560349103a0002aa10005030003140e03501010042107010b101950f0f001807850350190414801040103050703c0d040316400521900595400c41d400000b0f00380b0340301d000d90014002a808500d2100080101030551b500001c1002031503400c0d60464010442d803101c10301c101c5025036030008090007203034824040f00c000080729a042079000c3c6131506142103401028081103810040b100c002c145075500000307907041060b2a000150242510f80701c20400458801070340014001005d0191031000303c03144a20340d014601c1020040e4480c2000c206210790010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 9237669 1250 9236419 9236431
    0xb0f100c0506070806030d0309060f050103081305040e07150c05060f01090c020d0e010503100e041406060603071b140105070801061b0c03020f0402070503040e0403030f1b0f030e0307030c020405 85
    0x1044c03c0900ca00c03a100407951404d050014200401c03a95013614215005001402880c4106403400d0b0020003001804001414215840e8440d00109500c0314200401c50300c0040e00204a544040c0d801c1189207040b0f558040115550700304191051b41c69101d00b82803890488440405041d04401445044041d115242000419100030404245086005404407980a00c10f41c144040400010715804200c4800b00240c1090280700e14503062070314040e09454400303265007040703009400005159091080550341f2641c0656200895074612000ba030b40c210b0740c2c2403000e48505441810442280400b402134078012806a6a038038681c0d0314004008110f040c1d00d0101865155101c408140460480002201583d40403611215007100e60705c0020005d21800c9401091800301140010300d0500d1148014800ca020342c03401e000f0b11607032a00c03c00445022202c002100306003070145201c2140b140880c1c241c01d1330f680c2000282148500c542514641001c0c608900041002000d501103061070b000e80381d0844 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 9238919 1250 9237669 9237677
    0x200108100503031c0b0406060503040203060109090206031603020702060a08040c050a0b09011107050405100f0801020307080a05130209130204060b03060303090d030314010f03050c01080114040b0f100c050607 91
    0x1810040003d403a40f194803100045007850000c001d1001480c0d0b070003001803c2c002481040440c0d0343d04030103011034108940c1607101c1c0c003820b400042d035070801d80523000034264001e11031482d5139900b00d50300e00400015507408040590070700c500c20050708c86000400407a6899180c4a0741d0b458649043c09800350340f1b0b0400d07805501c014100308050780440d400c2e5103000c0b0090801820194040700040e00c1c011466103d19442424541800410031900034a10160b034074070031511300c406032629411800d0744001d6844500003500840050144007031640b00700d42100d0309501c9a420300030f09400003040005c056640715007403800d1002c41011807410b441404d001f88a42c0002e503042d0302e0442e00080e180d000c0e1800c198041c544140c034103070402d403207035219641e40030625041c030300365507155060500280001d0100b140c2c14031461101909542c090034030541200d0b0120b0499502d81c80000910009e02404042203230050315041046100303a4034185040c28101c1240e4070804900e07034900f011441c21170045e00400c244 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 9240169 1250 9238919 9238951
    0xf1a0301180206030a09031b0c05010206010605070b0103170705070303110f070305070b0304020d140607030608150415021612020c10020a06110405040507030609050a020a050909090703200108 84
    0x6071078403c2a02e0348840d00290000e0108102c0c201034030f80b410507440f6201201c110700702c039200b040b01c0300c4c0c40381c000e40d0400c2c0d0031110b483e030700c494056079580708a403070203025080c1020040000038030614180700304400c2180028140801503465500d040324540044000c5550507545c00000d240403c0500d41004036203000342403951171502d5060300c481e028001c0000e4490700000080c1551100380c105401d0030344c0200c21301440060180011346424054036100002401c009002071003500000e10922400d021141c0c000c2261160f644680f041440484100d03469038080c0301d080c40c0d0016040c075010025004e5141c00d406140c8504000b41081542945148110941190500d10340d9000500300c180643c0800005105100c0040301405030049900940e0b02c9030404007000081e43d81500007600b02c0d10750740e2080c040703030702c4005900c000d0b4041c0420700400200705111703204461800322102600030310040140c80b0b0941d142d0b00d0322000c025001010942c0148200b0000728075590040e1403646c010301c0b890f1440c3d00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 9241419 1250 9240169 9240173
    0x2270705070b040b0402010509030307060e0606060705100f0e010903030614090f0103080304030903020d120906050a0e010e04020d0603080c0705010503270715030e0105060d03090b0d0f1a030118 85
    0x120b00000d0006800421180000340c00c42e4060302c211100c5200040403240c40e1021807070800c02402401420f2910344c0281c20105d4010708004003564035a5a000c8050619584003c1e00d0800800744c007114044140c6e150860130359508820300c104030000c0d0295034080768090409034011500360708030b0455070055500804200400e0a0802c400341540d50014010741c0c1c0c0e461383c1c142201d4044603900041d5000c000e110008007004465400e50000354810380b42c0100040e0b5031441034506002d503011250106201408000040d0300c180c4161504560080006040031541010f85045504c03540088801c2040011030010700241000300000401c42460030324510302e48030745102c40b60400001400d01b05210025600f0034040c06000c0301001e80a64401526500e03a2903100030058841c9811002c42c07540b801c004281c0d20305288900c101c00c55095142c10130030610708104840140c2c011b2a12940f482d56458402c1c0342c0b000c0354013a60b441030305240ca0b400c11848140d03081608444902d100c04010716512180c0d100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 9242669 1250 9241419 9241433
    0x40302010c03080403140315130902010206011202030703060c0203070302161202040b06070f05030a030f0605030c0607050f03190306050103090b0a0c050f0c0303010e060d20040204030227070507 85
    0x50039a0340b61402c0741154885107820b807010402038a0089a40380048204020848030030310040425000300c1d0204007918600d91102c0403200c4c0c0c88030281c016004140103005490aa121515800c0e00c00b500316108aa40ca0b12401b084075411922900140c1001800314145903040081e528540c42407210f02001c2071400000702c0003140e900000a0184e500c0e4190840203070754010540c0c25131600040c180c8104030341c030b160494581d03002180460200b498180544c03220301d0a48182c0c0e046e2800540101076030349105041140e01c0e04122801c507003d00c01c10f81480741940c41400a011001100709034101c820f0100c940c064151461030700024105441d10424001056142c0d50711070304901d400400007900340a81404079043d00c40c00300c0402c00ba0740c1c0010407205110001001f58121803c20700d00b0f46981c1c036402c0c2086540b2280342d40c040c4c000109000400301c4070140d010540404071000344010f05d49940c80c0d000c9140074220071441c14592040c80020094035400440480c3e12195620f003441c94800c2a42e241e034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 9243919 1250 9242669 9242687
    0x1050a08011503020f03041104050a090f0b04020a030212030c100e0a02010c02010509030d0903060f0209010507060b180106080711010c02030406030b1305090607110d05160302070e190501050604030201 88
    0x14110b5000c11030320480703540260b04881d4080d21600c41990b4a280c00d040c04e451000240d2105800766181c035001481e605524401c40030107a5105080f6184d074002030301c556800072009003050368801e60402d000001641d890b00342101c0c0c9807039440616224043e82da03100d03007054113026418000508102a50081041c0803900c42c20b040c5e42400c1c03c3d001c0d0802c3c1c0c0012a001e020344683c094151107481400c0a0300d981181c01c400449200300384c10b1040c401c544201c4004ea004024025006c07500501c00344000030426000030003800302c06003000d030080700640d4a4002030781080c0c0c401c42c00b040c078560038050026031100700c034050500200001e2046c10701500d0020b54030300c0307148291420155203404c01a026a1603a0040c1100c03000101c042c032040c01c0c880b00407a03c403082500ca903c0031801354601e5100b160008100a11039100f0f5403030305801c00d5036425a800541105810890840c0580c1801003041505000c005000c3c9480100074050280000300300011108103800007485184248410001070307034010a01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 9245169 1250 9243919 9243929
    0x31a09161811030723090303040509090309030d050d0b0a0b03070521071e0e010c08030403020f0f01060801110304020603070e24070303060b03130b06031609050609010501050a0801 79
    0x9484040c10107081003008207004403000d00307400c0000007800b006030707845001c48aa948800014440070001110701902c280b03d01c02189130942c0041c0400c100901e09064504e50044110064901c2e108041001905116041c02100081340002c14400e6505040c0d00c1140c81e480c00a40c2c0000c0c180e824020a0040d502004014070204080000c440c8061030f15a41440c882c000030703590101007410b040b5009410381c88203034140c0080c0c007604100202450300c142c0cac60909150f0181c5400c1035120b9551250219640020010f4040d445010400d050f0540c041000c8500c03820352200000d101d5040816003820748401440038600044107005010240e0340d5002202e8010b40c0a043c14485070300c1140100d87c0b000c5411955054038007d07000c10341d004d81c1121000300400741c403031b44d41008981d482310410740290200340c1d240c3c0004801e5050800c0042d201001030390708504000d049598042a2190360320541c0d2080d00714004c2980c46070140945800c0040000c0d02510007401d0240c00c0511800008000040c140701e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 9246419 1250 9245169 9245189
    0x2011e09030e060c0c0406030507030b071b02010e12060a1b030903050306060a090302060a03051e130b07090906090b120a0305030a1116030206160201020c15100b0301031a0916 77
    0x41245400010072000c491200090403c2c01080d42d40e00b0080c0e2642d41701e21033543d1280258000604c40c600c03070014480e14454589a0709042a660740044413110300451070a90000e5074407804140f54041000010702c54a83d850021401303065000310050072012110001b82450304051203a00000d40100c103884c1d00c9413090b62259100c000c08202290041d02c554806500902c001540305600c0d9410b81003240300b41c101c210100d010003a07001c120151044101e03504c0590303c0c1110600030006000503211904208603240400c040307900c0da0f408108030f8076290301c044451645c4000c40302107401c001207620300184d21400605160f4103d510040c0c620300c401429243d8850f90340441030702070300c0c201d4107940341c0d00c0a640c3ca00325080301d14236020b07545440a070f40b000c0704001d0a5001e4007143d40f0500807110700d070122101a00100720f55a00000c04014041d240101301a4219004203692079010302031130086024040c5c0c0360205d0000c8025a10b0460b0241c81c140594000403020b01c11058124402c9003110441c5603 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 9247669 1250 9246419 9246427
    0x5010612020c15010305030703020f070509060607140706090905010510090324110301061112040b0c070512010209090705040506040506030a090c06031a0301090b0705030709030803010602011e09030e06 88
    0x4040e0b0500b40b4441083c82546400750000c001e0000000103810708078425001c0721020584c4251003903a40d030300f074415254801e0f072000000f0081c4c01c040b400b4209807841180d558010710741c1e01070128180581034201c80002070f1a20300c02c0245001d50f001d100d0043c03c0588507500d201c01c164200074450503c1e800082e141c001c1600d00181d14002400c00002507400748102045245030f16020802541e0003031003054001030b0010300c0c5640b004000301d00c810400680c403106501c0d262406600541682264103c20042c0c040c1e2100007a1907212907500032242c81016000503a40c00c02c59081020146000e071200c810007005100a01c1203803503100c00c070303016034400315640b94507a55080802005410584001040c0e0700c191780002a5054158000c440b21807030b13a81007880419844002d0508a035160240a404142900040344405000314025034100c100c80c03401400080d00c0f0348800449178801e07800040140c0d0f4841140007001c401d210b4401c280440200b040c00540e1448c0c900400c40074101c00d4082c0b20310740010b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 9248919 1250 9247669 9247687
    0x2101d0604080702120304090504140312150a030203030c030301091d070302010c0611121b070206040317070b0103050709060906060c060506040605180105030c0f01020604030e010c0b010e04030906030501061202 92
    0x142801c01603007214081b079690341d4072001c0340310251606842c200c502041111081000d00004010707101e01f1006809000e182d56100d00c0440707000ea5002c0760940d0000c4039100048096103080c8010214805404000c5603170394903100200d01140c00005041c0c0c0742e0601200d20103500e60002c1681412650246008991217500307040440007401c1c2042011f094040000354845d180740300101092068407d0140344086059082c0c002000b031141c1400298051002c0000f800000c84c004003040071146071922903070030200c071a950640305880a07001503030301f5402101c040003031140c82d00035900076125514051009600e84640504030b0000000020107a984482c00a000c5031903e41c080c0c801044020221260031702003100d80020580c082c01030601901821001c800700342440c1508e07000c3d45106a004040c1e40d901c0d500c04481d011101c0794001d0410031044400b0010900034400580a00001002d150960801e0b18002e80700f45c40c180d0040c4285418070004110223508017940300d500542c402030160351102c01c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 9250169 1250 9248919 9248929
    0xd0203030118021306020d120b0d020d0602040803070503040306050c041203050307020c03010c030609051311010813020907081801050106020606060708070b010303090315020301080d03020a0c050d02101d0604080702 94
    0x100762007204108130f80c0006482580010001c48002007600c9800c204401446400180e030480c50740c10340c01203c4900c40c00c0c0142801c8615105050184000500f40340d00c81c1030890950b8021642601c0035400402e040c030502c10a031050715040390048204030301d81441d04e64041c08503c0c400c130700641070250200000d00110700030310480300c03e40c4000b4000c000c40d40400101034000c100c940509a081442c01c40000c9910900720084020345400024a00705100c0c81e80044074490300c0203154200d0b40d035130200e09800584035070744054002c0381c0544403400380d032804906054000c40754407801e44c000d03810702004004141d000300d0710701d4004000303440301c0381e0750050b50810b80e810b80308410b402810715002030000000c1c9a40202c1100549100710111110901c4070050303801a80020b00405e031207500004884150039000380e00030305000307601d0300300021034904a441d01810105c0c2603540c2c801580090340062081000b601c1201c51002c0340302c3e110020200041040b07955004d00501c004c0000c1c1c4005052002e40d999 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 9251419 1250 9250169 9250177
    0xf010e03060106110c0316031106040906030503033310050705060c0301060806030307030e01050702130905010903020c01020d090302090402010c05060c0c16030203030306010c080d060303030b0f030d020303011802 93
    0x15007100c0c5039582d102c2000b440405010120b4400e400f450300400d801e032502084c01e240c0d44401d082d080003c542141c80c2c2c041001d45442510b5802001040002041c0503240945001540500c0140d83c40b481d103000d820300206a411980c96001d01e540100311501405124808940c031001c3d200404e107401d413224295010301c2980d0024065100f07003010058201c450b04001e42c10f0350742554038205d290302c525090580e40d002344440200450b40c1c1e1901900207505c10000340502034001480b10710100200e048840403280d1618098500b40d4586d04500145901000890107004003031008081107030280c10000c1c001d0f08280002845100d05030b022806580c46050790038401030b0071406540e00c1d81004015203070b00742e208904010060003000d07071206094144540120840f5006400703141303942d5078900112481c04600c00215032658040c40078007980d440a10503030014600c00d0300c1c0060f80401d100c0401c0f040301605100d1921070703400311401180207640802a00d0465000e55030564051070004108806401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 9252669 1250 9251419 9251447
    0x8041a15060f0403020a05010203030c0d020a0c080c010207020a0501050301050303040302040e010f05101404060320130e0102040e0a05040c060804050a0605191a0a0b0702010509060703081008010c020604020f01 92
    0x1d0081407003240198504018400c8030b20031038680403115030f120b005980741e0208070f45050100405110410303080c9065002442810b00c545002c28901081da5a5142c180c4c200c2000004c140c0e41c04280c1c0c0085081c82d090b820040c000909155085615000000e81c0e00d109030b0000900468640c4d8018130091000d41001100c58094182440140361091041203141914403620105140401010256040520418040c0c940200e150070791501502d05004041034204052030704030504981c3e503991242c05220323807075140303c80034005a0b81d20315000d42c211441d000030348001280751801c000d01000a42c8110504200c5103103051900841c1e4407810042d0614108841c003800b028180b004201d100c011605495441c40460075041107100081149045646150000181c118400e2501400420015400b500b0000c0c4140350542ca400903120100e1a15000f56104401040c00e0341c2c140b100b04506e03449440041c01d002002040303045000c800003590740001070006405180c1c00141288581d1144a142c15424 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 9253919 1250 9252669 9252679
    0x717032106030d14092106090304050a080c030c0906060d09050307061b02060103080309070b0f040812070305071e020603040b04120f080103020907110a03050d060608041a15 76
    0x91004800104014044918a1180c011903003559403513400b540075002c00440944a02e803e041c1c82c401440030300c0c003002c050310f40040144542c200b0074401c2000260301c1010050301441c1c4903490142030040052907034004004580010000481c15200003d42001d03210084440004640350740d03020400130320a1140d07904100d8200b041444c00e1200010040205a03c038030020080d00c8003510044041040f80d040c41030050304001c0c01040812354580c09190054440c0040d105031540d40d20744240d20740d000300c0350040d034800041070400068009100c010300c03250568120038a00030341781d90010818410171900408925402d210050f108a080d00d1600950780c0c05010a0b60300c0c240790071709102e04841114110b8000248030032440c90b0900c620040e160541854841c0724550b42180c0c00c0002c400d41c02000401080282000c0384260b4030200b0911414501946405554520040a040c1a074600d0740040c0140328a11081c000019840b80c9084a040c02d1120074050380d84a0440c00490100300f080c00d65804 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 9255169 1250 9253919 9253957
    0x8070302010b0109090902060a03090809030a0c080c010306180510151d0609010c03080402030c0a1203110705130f0605041109040509010903051204030c0213091101020c03071703 78
    0x59015806000c0007a8241c80308202c1d541c4d100245416111141b0000b50048000d006641105000390014000c05100f000d81d1814110380c2c0300860f19003400014151464403e446003080f4240c41808900d4201c142840c05000e40703410492030010300e49034801d4442d00b05507903c0000340059001c0660901034200d2070b548245980b18408001d0281c00c402d1175000c1c103110002d10051072803804100312064058180c513095101c00c165202643c068400030801d80e01409070081116030741c0d031381001c000098040101860001ca01b039046c000c1a2600d0384440c00c0c04c2e58012072040c00340c0c1d03a030003078009655440080c3c08240b00903001c80240c06089950311140d081410310820750b46004076140a400c91401c08d8804015030395407182c0c40b134281d40320110080c01141041055042c80148640e119610501034103214069000e20341c0400c01900561504812165071660300c0703410800340550342c0c00701920910062040807419400030741c07190220701c03c0c050551042005250741d45418425140d882c48200420011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 9256419 1250 9255169 9255173
    0xc0e0c030610030903090b0a0311040602030a020f01021204020f030f12030106030c0305060a03060e1203160801050117070f0e030624030601030c09020d020906070f0209060f180703090807 82
    0xa0303003040d01d040e03101e007880c8126600750310320074030504502640694640300a2031920008a546a0004120008040d1034400c0100490003450040c00104515402103560350b00d0b8030402828030310300f804880364590040100d40d109000044406800c99011181803080f4150800068602000502621440e0280a5081183d124a40040c40c100e5941e40c0b000c2c840e000080c80100d044610440b5900c0e0300000303d003018804100d13030368082000c0c1c164000480b4603e80101c011582980c008840c044408440151580c07580ca510030075060060200382000307102000e2040703445182e81c0c001000700342089038000410080f507200b07a018843d82c12000d01079031480d05107091341c1c408500f942c1301d1084041025421590b01c5082c000b0364103040fa608001446801404d00d410040a540401b61030b08940d9001e01105c0440d6980c10300515402d1711521b0b1081400440340306000380c40d44000c14862050700c100203d0015070f20703214810f80103000513100a11003907139501e40c10340c001d2003044009050620003046041c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 9257669 1250 9256419 9256441
    0xc02010504030e010c03050f030c090603010305010501060306050d110f04020d0603050304030507060e030a030f030603060501140306060402030603030703120e120309070b0403030507020d0f0204020319060801050c03040b040c0e 99
    0x100842c002d564418480701c050f030040d1804824040c004000640c00c0000400f04002180034507045100089440d14103010600054540d0b0005c3c1c10a440b1350755684010000c42d170301807042200030041074442d40c88951b090b8036812482e800701050306004804080038a0103658941c4d04843d0220081e40b01000903546a081295482d0400e010880c0d840c0304180000c98501c1c01089603104540d8010000c122601e42d984c0c044a4060b9004003074001d258a40d080440040c040313019040c080c083caa02c0c8170081c0c507803071802c041c0703070140180106015610410034014203407004003c81c1c82c510740508006402d10100301e551001001101c4c00801070f0f01500c07541d00d60402c044801940921131000440d00ca181d01d54100400c01d220b0340c4401004200c0030000b000060915100b484c01c02c60040038400401840c0350089001c2e60f100f11001e89003c8104444040b40301d078144940300181c043d2034004c1019151a0341680351921014001038482d0007441c0004080040b5008000c010303004044106d03d15051a0060407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 9258919 1250 9257669 9257671
    0xf0605011202190e0711011e0c02010b0d0c0605071104050703090b070206010503070608150415050406080c0a091116080304140307020901090e01060b0c07090605010503040503030c1605010c020105 86
    0xa11a03044041102c1940403000d40610070303201c03181c0120741d00c1e0f11541802c4c0c506513040d5070a1504d95494000c10b0200102c0e14000d0300c8c1c0d01e50808008104031102d050020308461a02e0b803454400d610780c0c0c1303516010984c0c9c00300000988500b03007001a620003260403e802c150194100e07403070341b02e03050004100302c113641500020303859071003004001e180741c0350f041c03040c1d07100c440c00d0180e80e41562002c3c40401c501807088008903000f04025442200d041e14080204050b01c07c06405400e01c02e2032140200020300b05403203801c0003002500c02602c44900c0200004440c200c46100f41c01c000c5498041d01407914003264110340405c081d0b0380c03145503a00418507203980c2d607400450b41a10101d2251040c0311816001008540c041c990040014020ba07080142e280e0080c401a00402c9041d9a15000440d00451240040c03402c950782a00070988030345049007050945005810582c100306080c0b0a200001e0400802e4a80001542c2200c0c1d0320b030300020304100c08d2050400c0001c2c04640c20102658802c41d010341c045 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 9260169 1250 9258919 9258923
    0x2100e031201050901060215070306081e0d020102090a120303020405091503010f050f07180f0902070b09030403030c030302070215040b12060301050c250803041401061208030c070f06050112 83
    0x180c11070741e82c0c0e02c0c104925000c003440303100c02580104191b540c40401084081368003005504000035816158403046140605810344807030001680d10489034410303804c100b05019120281f00942c5014500404540030030340600c280c001c040c0720090b50b18100b50281d01a207000d89400b60440f082407402c2090940790184060019010794a0300c4081c0400f03885500400c0e100d031300d8480c10404107032121070044421405107401d110006042080102d40c0225190402004000001c00540c84405078140f124500300c010b044c4054030791003040100002034002e22200f14041d05401c00580f140d074940045a103c0340f503d0481c1e18400b0300082d000c41c1d101590005010a615001d494000c156a401c040c5801c80701e0a403a641c000b100d050009401c101c28202000502e08020b002e8810307501e80581c2c070080c0e5504207a508580203515034040e030a03800e03024890140144403040141d0042d40c00382c1c681d0742252101412003001d4250000e502ca023070000c600312505207103510441c00c104070b41c3d5444030007480d081d03036a1b41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 9261419 1250 9260169 9260197
    0x110f0711090f0f10031e020f03010504050a080c01060f090905190c090b03030706020f0c0d0c0c180207020a0306051501091802030601020a050105070305010f0b0a14030702100e03 78
    0x80102642003601040c2d11440070744000c8041a200c1c10003401c900c3c10010b0030200002c01c1d44030701200082440010301e4041c10412140c1c044c041c52407040101011008002034060b82c5440d04110105030005540390010f900400f602c0e0380ca00c0702500090141190fa00480344510903107100080c2c000141c1d1102d10610700071402c0c7c44001c205590001c15070400000083d0401c8070480341448540966400114052001802c80e45031504565549060340c01462500d51450342c089003107466094107205105804482c0c0c42d2091540010355034101e9036041c14095008003203010340d04140d1200c0a64112242160010300c004581b0741e0340e1074081e000e49012140c0d070860765400c018054055010f4090103003a90a910308034560201c0601e11a4020340000f001c1c0c60441c82000100b2010400c00c0c402d00d400f0f202960740202d05036040c20001660403050703500440300300d0010001c0e580c446510004c1080340b00c1e5003003040c550720303280d0850407480c103816910b60b295514540100450100e0000004100380040e270f5013 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 9262669 1250 9261419 9261443
    0x203070506040f03120b0d12020307061109030d020607080a020d091b03030905100903060515060403060603060515011e02070b13140f0312030a090c0602010c080609150105030406110f07 81
    0x80c05c2410748490418013500203062411000006400c02c09048000c03240340b040700e0811545032031b400c06841c803241045402d0940001d202000381401d210404002581e80001c0145080c40d2200030070500004005403442c0d035000c10000481005504120003907604007a141e2845076413901d100c66a00b01c0e070710045000c0f58000c0f00029050a05005821602c141511458401e500d5611001c0c050840100b083c0c9040e4411400c0307114603611140600f01450190300f0009078181145040c4c0e00315680540000d41044c50700c50303d100342d030788d02a01043d11542184400080a0b4014609902d4034115070403100d4080750218441045010344011001100d0100d05403210008201c1c052114517482041c01c1a0181c0045003100b134007010080003560066003c460002e8030503030700d403108214854642c10201c0180d4440d40403805a075440105140c015108840d14035103818010807401011840000c55414001d002c8001414480d040d406220701144694007265903050740e07131251050754010b078400c590180c0006 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 9263919 1250 9262669 9262697
    0x10507030621020603040606051c061107020604090218060a0e010e09011a0f13030803160e0f01030c0e03030301030506070f0201020708031305010e01240902090609100203070506040f03 81
    0x810340b009020881510304242901c0d0303001e11500344d00041c8140c80031606d512001550b074403010a41004564645800203840c2c100340b61503802d03a09100f0f18050054000d00c180b20160342d403c4112000c8400d08080181d480c0b0b90348582c1a003115004161950203000424103a16640e008090310b00e41d08026640c0d181c0c01d2110744200503015800b030080f0381c00030390810007005803c15040001c00c0c1180400b02030f01c0c200458981c016038441035030f4008580d182008000d121611084607000e8000143c1420041403e2041002103040b40244c00e00060405485a001000e4a4018842c0c03105048018090700c0d1359603168241256140400d940d85000105058040e80040d8070620030740b5941580301504604d19205d49050450409020344180d8095590700311342c4e03201c00801d101e00104642600e0341c1c018038501a03040c00c1c0503200307181c0c404000c3c5d40c010041a00645d07140070884d510241c08a9050b0b44802d00540103d155014410000b801707845514140710034411505410464203100f96500d01b41c0c038001c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 9265169 1250 9263919 9263939
    0x117011103010b0a0e0a030c030309030b0604021810170109020703020c09040b070c081204030201060501020d050901050d050a061502030301140a061704080c0714030c06090312030a020f0406020105070306 89
    0x91181000a4100b0320a0b40b2a07240300d69100982d0185c010910b100b400d8807a12000e6944001e503104601040300c00804108104035401c080360301100803103086040c4a100240e2110140015890034804d600c91408103080d14021010110303044540b491683e860742e1a54009002948100b100b42c0c094440e00c1c0001026160010215114640c171560508045e140c62406a9210405241c2200e03403450a000b02c20202c841130380c8103849a40240c0c00400c0c6c2601d400c00290400103800460300c10001c0406c0025840d980007402c98904480e0028005044c0d42e4054901004080c40c2d0081c01b01282d06054854640d9800000f0f58103a810388000c40810f40d4440040110610f03051182c007010403400a411504107030900780c0140d005004a41080c5032150055149090003c00d82042c0e03000d03849202c0280950504100c0c5c08111702050714094984240b81d00021340d0f076140101744000324240000080c0040400e50152600e2020b0500c08589541d2100703c068041c04084038654002072601000055070164 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 9266419 1250 9265169 9265171
    0x102071a01050607060e0a0b0a0c0e010206010b071401020d0c05070c0509060a06050714070f06021509060609090709060b0a0e03070510030b011803050604050607020327010c020301050117011103 85
    0x80001d480c1141e81c1d07072040041c0561001d80955801901c0e584400f04881208c403606c20880c242002510204c3c109016084450001c01c441c115404000103201c400400801c03112201c0d0002500403525070440345040c0a4803c0032220301303106040c00c036a84241c83d0400080c203040c074880c3d0790f02541d05440e0800e0105906040303420760b600c03415082003002000d010f64024032402d40140c50348400c02420062a43ca4000b480c0e0200c622040ea90004101c019810b1040041500021f604199a4140b140071190769610141100e88101e072440e0106400c0103040048900501c1401818444269507204201b401d403c04101e00e0040340e050690706515180100714502a910000d0500c4003002c0300340021002485400d001506101c0ca01c0382805030001c234141c4010042d4402c100910b0f1a00c0c080c94110301303285000d0403040c25503100b400141155032060010b12010300c22100c081e00071440940049914440740f20000c2e4041d4a1703c40081403c8034040182d8002c040b9010080c002c40914a03100140707888 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 9267669 1250 9266419 9266429
    0x30314070c020d0305070203030706090b0105030106080115150909050106030f0501120b0c0f040506040b030103060e03030f0115050d0513020114070816050102070b012309011511030d020c0102071a01 87
    0x20f40e454071000a4001c60191000301e00103000c40b42445515681c010460728009001c1c0c1d450001000100090320b402d0041c080a06407000003400090000e2801c00d100320f0441c001c200050b0312100c0d000d111244540d9032140101071941c801c0c02156500e0902a0041c01442c02c41d060103030400e03001003001c8080c407401c07121055100840116690307814051459a03000700310045a01941004000390669030100500041c201483c07050b5500d51543c540749044800041000e0083d405c1030040000325014a80c003a41101c1c108402c200e0301d0300c0c940d002140e55218100101a4640c5443d042c005040c2540e0360b0f03800d0f868400e03266441c90315441035480002c4e0180200c0204190020010800d000d10395403151161544a60000340c10300c1031590711241c5d55102600718524080002c8410441c0e420310807018081c0d03000580300844c041d4100007480840800e00021001070190b10f83d090000c80e03c081046800c4204110411501c610000d50350314080e5014881c16105a0700e000000510b003d00b00909504030380c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 9268919 1250 9267669 9267679
    0x6150114040302090a050601021c020123010e01090504050c040219020706020f0c0f030f0109030518090105010807030203191a0405090106050607120201090606030c150f1d031207030314070c02 84
    0x10b601c00c0c10b01c5c00074100050007070f411401500210824800c0031400003000c1c8100e50008100350f1140d10251a43c100f0055007400f019140c0d9004104120b8000c0845040d50001e000100f003070355841c00e1107841c0958101140b5002407000800f09a4038480502c468090105176080e034140542d901e10403a66007209100e0038a03590411113a40c012850400280d00c0100d1020701510b031120006802e0310708440c400750040d000b01d5000100358811030a0004407041d06001141c0c1c0d18055418100020b158840083c442028184c1c0000494085603c02c250382c040c1c0e100c1d460301441502403c45444d03480030a0b0181e0300c1e000b0350400380403c20100c41030181000351000909014103009054460104004541d0711000c1513568804102010440502810f0003440c020161030710300d0344c03030241940d40011048120008025a094841e030116512081001c07400040c1070844070b07a81c510000090402028120418042c1e800142c014205509500440711600313200c9021801c0343d8a1142c161450101d802c030096000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 9270169 1250 9268919 9268921
    0x150504020a060c0f0614070909021201050904060e0d030605030d03020702030615060403080307020a020a050405090a110a0509010311030c090907030b070302090607030c0c06030603030e10030e0615011404030209 92
    0x503e200d0303d180d41866005400d02c2d05415895158a401c0b101240f14010380b10b080035040084a54020412030002d00c03030764601310700d0142c0010103c54481c2043c0185407151078184003003020b000b410b1304100c400721118405d61750540000030024004020a100e039034028050f00c0f04111620b0300074801c1da080c0d95000b902078005641d6120343e65802004161080d40e20941c14000800071800082c0a07502c01c01858004201d450204e00420400c40a20b510281c0302e0340c00c2404000210a0200f105080c0076442210000c480d200000019074101143c0c010541081180c8000000e000c0d031310b01c0c810300c5498282d05172468940700c003042c010400c800300da41c2c29041c0c5c051102040040c146541c0c5a6120383c4d03514005040402d91000605254401300c819000560500040c1b014407010f00862401400241010410355156542c082e002c0b1081d8036441c0d00c15440c4d0560000802c1c000d420521034111000f050760004d283c00305008440c00038003ca1140060f4075025500c0413144004110340560390000c10220603 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 9271419 1250 9270169 9270179
    0x50603060409210c0209060904120c0c08010e0105060405090102030f1602010f050f0402040e0d02070909020d051219051e07030207050306070c03020f01020405060703050313080304060603150504020a 87
    0xa00346002e030840d04041e0a030030b001144003a02d80080b4800c1002e5a807150308001c903004001000c03601600310b5220324000001d010015042250500542d070503418050110b903c0c0341030403502105154000328055090031081002140194016441804119800c00454036411062070803404121b4440000c806407070003003400f080d00480141e00d890801c0c0300105562200c498900281d4206850000c11407205a050008500d403e008450703c0040e0400240b0f660f01004000940e99582c40c070072198002d5450b02d00c2004d6454512605240c2604001100d60303034000c007100074520794002843c1501c10a07012010005a601ca60100d0303400043c4101c3c06559802c03c10f01980712a44141b00c02c50a5100b11030000496403001d0000a01c2254030743c9078038220303d0080c20084c1c1000d003420030f82c0c503940e44108000d04c12591240195050f5035010314220f07840e0341e900280001640038042c07005c0d045441c01f100304020080c00d5048941501c0c443c00000d8100281c80044a05480d01601d000f544619424402c2c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 9272669 1250 9271419 9271421
    0x9020a021e0d140c0106030804050f011d100c0501050f04020102071e1404090501060602030a090e1e04080d0e0d0f0206060108010504020f120c03010302010305090304060807140714070602070504060506030604 91
    0x1c00d07030796010f1420314040700042624210381081e030085031110000702d0104500c0c034100303201070640e80d400c3c01d04011420103448101d00c0b0285206d225486021014003a1050300d00c02c400215038180c1c01002001142072888244103443c004840490042c8a041804581040e080070840807402d14424403121300350a0110b00c01d60085080b4644e50044c0e901c00d41d810100f18240a400f008161036000786540d05995080141908151f81003262201e040e1000e1080e02442c0d85484120305000303031103019403a121443d014086100b4804541c24172410074542e040100d6000c118042d05071050384031001124001c200c143d0300c0305011540341c0d0100302904010042400c00d80c0040205440c3c01040c03900c0d00250005c565804142540d110b0b0000e41e0120040c001c40d60544503441e0002c0d048030003503040c00e141581c000d2086a000f8110410441072085c100d6100350090159140e0552040b8080708010f00c0028542d07460041c1c1c481c5800503c2080320010f42c83c04c240c070442054501c050180c518540d19003080c40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 9273919 1250 9272669 9272687
    0x7080408070b0a050a0605030a0503090d05070f0b19030e06070e01050405040c03060e0601020a0f03050702011e0507060501090e1e0304050901080f10020a0e0d050708010609020a021e0d 81
    0x103a4500300800c000800038404109141c42a44040300000b2541001d10869044600e07941006000768801c10f5400081103000042e07414010742280e5480306118140303421800c20826521819100c059280045032104601c4064450108020182441c810422000f10242c450310015103202f0707005200030900f0307544221403a103842003060420b1850141e551000c0360032980125a94000a42c0d140020310001020500558000c01d0920041c82403005a03141c3c005000c803010300003014040009060003c5900031655642e8546000c540005006d1000d0000742403980060000c5590300d2030100041a549424802c070181061024002d090201407000381c05d8682807101310188541c401448001034660302d150460740a009040040c03e1001d4820b0344917031900322000e0103038246074014441501200d50040c400400885c00300c846500d801c016007440340c10280190071403a03c175424894040790f085220b400801c14000c0c0da030700312200d1030100f129801c0300c10500750030b100045d0040040070902d540308a240d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 9275169 1250 9273919 9273923
    0x213050f0103270516030203070501050d06051c020405180c010311040905010603020a020d03060b0702090414010f0506031501050d0b0c0415020a030f0e030d080c07050601080601050a080a0506070804 87
    0x5010300181e240000864098420015804401d1115400704501031000305000d1080d59040300f161741c15640040d441c0c1c1420300036507041240c0030407141005041908200000c00003d000024244c2c12540402d58480d000c2c8820b9006504010201c2c0b00152001001030b12401403401404a0082c030400450141c480d10f58040c003004c0d001d01c030100e4114014401c0c4c070b0007052070b038900594840000c007010b41010b600e4980300003418a0044100b00866640303044519055045a4040e440c0e6901e20b42a2110480040007140662030140c0901185021341d11203070041a00301c084441d4400300b0b130700d003a015070003d01845802400c41c0c004240090401000e164102440150050800b40ca42e0003548072141c5000745800180c4c4003210700c03024950860640804108685000801034030310801003a55521904504405c1000300000200e180317111005851509512201340c0c0c900703503554a030081d0340e0f00f002c3c000c1e64405d0f11100400039030074000040d08030352154840c018112a544060064680150050003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 9276419 1250 9275169 9275171
    0x4020f0a08060c04031a07050406030209130203040c0e010b0c1902010c020310061e05010e01080703020f04030b0f07020303130b070207050409230f07030f060212010b0a080a0213050f0103 82
    0xc04145181c0c00d0001a1103003074881d500585440c038500b03203001c095065004903965240180144500e240d8441d04640943d1428280542c1c3e58a020002c1600c40701911480d038100351020040c4002c02400c03601319000c454013110a0b42071640c803215410032a01c035144440c1c0c1151300c0162081c40c001201aa0140c0040c0141800004202c0540109080040d00d050401107a50754402c2030000c421000d06188010882000d180802e500b0200003a04d10004d900840f0305001940c000552030903c20b2b011144c055581d142c58540710b503503a18204810250603101c141391040e1541c0000c0f8a50f02c0003041d02e100c1c0b5000850343c88202119190072401840c00b9141c44218003039403e0110f07032034403a40035140d4541d100d99a1000080000a580c0d003104280549100c090b0700000e01d16039440c000007400c8000d49070860024091300042c1d14001d4020320441042010303107000400009104030080703020304502000c85d04c3d41c3c0d0160b540c5100035412440348801c042c01014001c1005c0c030403410241c2c41c0540300740041c14 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 9277669 1250 9276419 9276439
    0x60a0e010b0901110c031504031803020105030a0509100f0902010806031209060f0705010c0801080d08010609060e0d0204140105011b0f080306010201020d050a0e0c0613090b061b0106030309080309010804020f 91
    0x4a42804100047c1c40c0d40d888402d000e101c205a8403441101b40c00c040711440c1c801641c2160300081c403a2002410342c015035a241c6000c030f401d0180c180300c942c1151190703c100304102803068500001408a10100384d020905641c00030b42d0340d00340411001310760308101810301d2170301c0c080600b042003640001040c02840751092002c0c000244091041e22060409611b8882c00384d858000c465180081c42154801040741c8080100b0107540c00403444001d0f16001d052400300408010086840c0e9600080081d60060903c03603410045d02c1540c1c603540c1607910a07650000702400d1500380103600540060002c1801c44915881000724071081c0223140c011005100162034403c101c082c41007686c1d0281c4240140c40d03601c25004004c9601085090b003040000d81c3c205080c001e03101c0d0700c0300500d41140314071580b03103483d4208094030f50b50f1041103496030000c109034440041305151003103008007994081240803442385440800c0001d00001580d5680c1d03416034a1061035a6560300344411003140070282034010034041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 9278919 1250 9277669 9277693
    0xd0203010902040f060e090c0c0a05070915080601060c080904090b04050708071707030f0203070f060203040e0a020f090f01180806040213060303080f0417040806060a0e010b090111 79
    0x40011802030510041c0540ca4605000315034031301030440e0b8008010300c104d20038001c01a4490412295028582501445d1a00e0504c5855814000000001856801880f9010681c90b42c40e90008404201100d1a02003041c1c0703580c4901d540304000e014150124508110641c006242e610003044c8482d0064001706014030701c1e0350b8502c800c2205450480d01504044428454007001b0042074000307000e29808046102800484151143c0d136500001d0410300c100c00101c4191b40b001c001003c001e00c0080242000956070703c000940b2030300240600c0209001403408a6504100c50081e5422840346032610b910341030001c010011b03089050440d29040c885100007100459010840d800e00a041420140c0260326003441006031400c011003084a03440e10b0010280003290f808041e0540c800565054030b100e40d1558281174840030403020004000c181c00140215140d14041790042c040c846c140c905400300c40e10b548005041c1070003406070020452081c031a5a20310341c8140c60040c8007051740d00c26609500c15034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 9280169 1250 9278919 9278921
    0x1050d0f061214010b01030b0a03080d09050a0803070305060105071a090c040606030b031501080607050307020c03010c11060f07120c0302040b040806060a0e04030807030b06090d0c06030f02040b07030c05030d 91
    0x48050f0341c40e40400c0030310310200c0b03c20b005000e8007010074642003002403110310006444518500002e040b00e41e0104c1c2c80458803145600c1040074940020459030b0f1803005107404101a131084030f0440003c0c3c242000305986502a5080d43c200603030007000401039009031000041c1c0500000c100840320b01c204e4002d00e82640300d030310940f00900360940e0042a0060f1840901d0300c1d101041554944100c2070030010000418013081140e009020351800540d00e40303071028102d00c0d22a0390701290f80d06500c1c044c03000e90042d420441010410031464169070301652035103601503102e401210b8080224005d0300f6680d180b0f00300b0b076000c00d904c5062070038014141a218244240a41c006030444c00d070550011007400b00324a044512140109502d0000d81d24a02d41076900800c40940a40002d00b0b1648070704490117555103d5007036620001c0c01030240e034800e030068100000102c1451088102080c907180100a000700940200e8050380c122495091a0150903030b01111159010300d801c0c0c41501080c4501c440c0030143d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 9281419 1250 9280169 9280199
    0xc020d030504260c01080426090418020d06051b03040c0e06030304080309040b0105040312030507030b060705070e0901020c100605010201060504020c06070e0406050303210a060501050d0f06 83
    0x2a80c81607169800c002c08034807030803035003101c4010710b040c80320158010340f0000800310212002843d020140380c8a40c5480c045840c00c10300e003510506030002c08541c5030320540c0040c0c0001482260305119440740c007951410b02c07154045002e504818141c1d1801c02041d6907030040c0c1e0b003250a401600c007401150100d04038442d0401e9074200e40d1100800420440400740c4500190844000c801031440c3c2841e081400f80d40b0700c11400c0c0d641c0115195440742060b43e000301d0035500156004158400c48100d01d010040007494100d8210700402c0c502103580d14141130a50a030752060b5070000003000000d007058002c11520100400c40d03a01c40d9001c01508446d464103004a01807107052440c04900103040c08000790944915800550142d48180700820061313000181d401c0e00030420b41000501c540c94440403502500503500015054400010060108240e00e40b4030140341c010040060260303104c2003d480c1c1130f9142d6119250009005000e450855521648590782100c007800c0f000810756550f880d04051607007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 9282669 1250 9281419 9281423
    0xf0402130c020f06090c010525060c05030601090902040503100209060c070f0e010602010908030106030e0a0b0c040504060b030402031c030603020307031112010b06180a03020402120412090b030c03070c020d 90
    0x409445003800c81c4040121a401c034205d0300140080d1171405000802a015448201940c034191030200c0000c54101c0d64010100c5400180c14032150070030207400b50060b0700503981240001c446000c00a100707901d5200703032001c0d10300c028080c11107540e83c0360040010350403a84189030b001200700607182001c60304010b200003c2498007110324680d890884025202e202c164001c405690404191900203504d003030449056513103504000400400704100589050000407009052810f00c50038032003011561400f0b40200ca0701100d040c44181c1d101c0f0701030740f8140000e0320020742540c0081c1241c100400304043d80103c40900e8034000400590b40e400103860070f00194010b840c0a0003c40a02246080141d02c202150348150020300141041d03102040c000c0c41420350013602004112000c1754030b40c3c0e481802d60001c1d07400a1055440b50304461004030f40e0201278031300300e910829210a0904860089030120119100501c001c0d0955488101e00d107085e91006040008001c02c044034400182d48130828415003074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 9283919 1250 9282669 9282673
    0x4090c0501110303070804060513020a03030809010b010c120c14012f0702030703170409020c0c030106060c0b0403030203060d02060c0c040608012c120d02070c06050f030f0402130c02 80
    0x6103040009010742c121590101400d4004004000e44590041c050303640059008200090550314202094141d06011500030750041a20000100341940166001d004600c4900208100049400152212184003c00074140303240c0314900012140180c50128a6074001d031441d9640045441c07046007100c03181c40000031700c0142c0502c100b80880100001d9100b440020148918110035034001983e209504d220041809801400450340101e661040e10020244030401b99100d074071110603140c556019081141c025032906170300064192040b00708090740303900305d0701205454a90b034074110041d50004003c5500040c06580c8540162941e00081100e1760301c101c003800c6901d0f1040e0422065400551200c80583e0600106028040841c902d01c0d492083c00440099000320030b001d51818007a83c0c81d551881c0c82000314111044081315001000414440d404040b40340792104000e0720b07203000d44980480e49210600002c0c8031400c01d0001351360040d00043c9007465030b148858404080e40c3c20701140000603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 9285169 1250 9283919 9283943
    0x20604063801110106060804050c03010213060503090102070c06021e030c03120907170307150c0903020d0c0308031806010e010302010c030f03090f0c06020f0606060405120c0409 78
    0x1005280c400e010902811010107100c24820a46000403a0410324020004124004600c9001da0140001c6000074040300700910103a555a40094003544080b6804e8407903000b680d0007500b981c0350610072941020300d2040703804240750800104581c2604028000f40740343d9820045200801e0034001c502008040035401040502c0000a4407041041c4417402c05809034818884510559008410398410404c980c81041c02591100901e904e0100c0543c4051b0160000c851000e03100310001c0300a0007040d020f100307008141089a4a65003c030f810815010f000101e00c000c06000507e030001140174001d0003401e0004000391603490b000c445620030340b0440710005038081c000d0300c0e290013402040d00600c01083c41441642c59a00080c141040e4610b00904110443d03407141500c038004da02c004049034120340c80342107500c0c1c1c503c0c6c15005440203000c0c202c0541303e4000d42c6d02d10710000081c2d041c810480900707a103007020710708802d000126080715000e0429014050100303286854074400c0040c0c0500540c041151 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 9286419 1250 9285169 9285173
    0x3080301050f0a0812090f0901141908060105120a1403030610020703020a050103230a0506011106091203070306080f030909010e130206070206090603040302010506040e0f070b090102070b040303020604 88
    0x20709040110721600403c14503c00308503410001c1200451620048021070f6240190070005140c1103a46a001c1c3c2c3c4a44108004181c0c80c907070316095581640140c800040d510868000002c034811148205001d551043d401803080e4280301c00380184c040550f40403160718102c1990746001013a00d8403680c0030a6030000c020000c131882d10210400034601e050000e4040103086401203090900d45d4015241070503201d0403d2694941300004800384072108050300c040d142841a1148080c00703050b075400740000c503610b2101e140c0b1900411180e000301e6000004000c02e0503070314a041016000101944249940d404002401c00d2007030100c06034000150b009190b07034400e00c6040080c80e48040e0820030036003003031504110500c00c0d0354070100542d64048641541b500880d200040c00d52144410040c0c0041c008400d0108154054000c10f00852003103030180720510301c1791361481d9034002d103202d010001c1e0300080c42041303081004001041d803904103106440340e041d250310003a03015030b10aa008a0059016904200c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 9287669 1250 9286419 9286429
    0x8060420062704061809030c02090109020403061104081009110d050f010c03020c0d050d0908040603090506070e010e0402070c080313060206010605044403070501061d010608040305040b040308030105 87
    0x6600d0780304440400c0b21130705003c5d5064041030010240c0d11583c1d96250243d0034103010318105058183d0003040d4030310300c0d82c4616110380a5009880b08a9850b07003001102407602d0303a036200355019110440c00400d00c4d1410785c2202d070094040315006a032010000c031044002501d4a1200c00a00b5000704001e140e24000c040c25603084440c002d0076032007018818011004201001708100b0f025014070700d00340751202c1c2443e0461004144d00d2034006c024020000300040c6164054011241e100d000f80d0540c3c002c1c1e07a810205480049a484210380003844000030000c3c24a016030181c600c0b140070310040505103071100d04892842d404040704501400a000c801c2000341d904000003805071079580741c0b042c282450004161080200031400007a100e00a151316140d10342c6900361000c0031240242103c0540528100d00c030b80f0b03588070420a40d015401c0413000f00308058442300060270311915000224031a0720b0700720116a000e002420440800c18100702c0007540f285481d0103000514051849242d0380d51410040003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 9288919 1250 9287669 9287737
    0x1002010b120a050d11010e0105070c050c030604030801051905040507020a02190608010e0406140705040518010509040b060a0e0f10060c020d1101050f041d0606040806042006 76
    0x1014540c844212440003800100e000c044c00042802c00c066440d03226031419000d4104507828060942c60801003241103584a101c0301003090041003a07404c10624001415110681198042c01194007a07004020302d003013000c0c40090b00403c00b20944c0301c0ca80c60b1400903094035815200040145e01c1010348400794501607076403000300300c901c2c0004c0c5c0b941c0f4038110004d00369410520915036074040440024040c0304441e0001c1410000300054406146040d410203401c0703400078021180112480f41c034100018801002e040d040e0340300100301c01440e940315511658154001090310340c120300d42a00004203aa84114901e029031045201400c0c14600051001214002a4040b00030040d420250001689826840c1e0399041d410002740c402040300d020060b034040c8a4518000e1410307400141c0042c2c18000c05000e10b42500c001a00ca0000751911010844035018034080c0003415089080031070001140c05031010401c21224086070550141a400140c0c290800007413150450008500e0380440c0c90880c80403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 9290169 1250 9288919 9288949
    0x3090a0b0a0801030b0c090d0c03060615020703080f13060302070605070c23010b0a06030608010506010903030f030506010309080c03030f0601080c160f0606061107050d020d02040b010c021002010b 86
    0x81820401c10784401004554184005800c205460000c01e6145d04003004546003203030058506c614004031461315407400813442c4402d480c214075010000c01c80604151100404101550080000b141036440b144803c0c0c1c0305c0d20702204005400c02a0207201c5d01258400c000403d000d46005840300f0381814080e0548000515070410081e0321002d220008460f1100e140700101010440c508102c640c0e240e16005000c0704071481c1d0721000803100040c2d44d50f41500710400785c5401400900482e2030381c8005480c1c0503050301004010400305407124491030712952080780e1240e0149008640e0030101e4840442c5a88a000c4d280c090f60400000c100001606501045d000202840c01a03a0307407900702c1030f0042d03c1c00b0710000c16055042c99151032041c4a40042e03041d2045402100401145c0d40e5140d01030403884405000c079505008010000403e07140803c54820b41a402410800d01c0c0c484660800000748841c03003100f4188201d600346140561179500501201100c1ca4000040191030442008003000d858001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 9291419 1250 9290169 9290189
    0x1060905030601060801090e0c060c030706141005010807050405060703030c08090706140c0109050f0604140f0627010c1805040203040f020f01110303070e0109060206040c051e060301030503090a 85
    0x1008607a52045011b41104c03514003000900000c24900e2908010620040590007807011509030019200400207000241c82030b0410018001c940c41920050b1008440304002140070b05010002540640550350b88040780e840e0071464180c41c0c50010b20150030240701078002960340d6400000c2603801242039074014076000000e040c40b51401038010800e03d0a034500c1d031082d01d00032801134651032094204c8004980d00005503008018410a0682c4d80e86040718161401d5410141c2c0800070350000ca40c02c46101c03800d6010340b145554110803034250030115403500c1880c030b00d1150f40311400345003880b4003422000c2959450881d1100303c0700d4559010611340143d4030840c03040051000041c1c1580c0e40c030041c281d041e0340b911414030101c001070f10692544180c500d0785000000401882691180740d1144044090302e5001c100c58466a0032640c4500465000f065800c03c1c044c01d0011b4035100c09010034410f140c144c0d11903245958004603840e0703002030b48211150362004ca0310351001c0c07030301c50805000780010302c02c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 9292669 1250 9291419 9291421
    0xf0114030a0204020c071206021905030702150601090b0a0206150a18090206040b1c060b030601080a110d0222050f090f0c040e010e0a0b0102010507021e07080114010609050306 77
    0x36200c800341c9000034419580010180382c031900901030394004010018035141a03a40c1424208040e50040e00b01c05422040300401210007030003002501e0203804103500620030304092007045900c466020b0b122070306102d1504000502d00250303000401568010361b02420103030412034840107040301040440c0c2e204444400c8140580b10034100c441c4002c1000c02004928141c4174004280c0c10700c215002100111000102c0101d449600301c0c1e40c105540313074640100089039544000c59500d00090751114002005600031801100b03a507049110003154080003140340901031581e032404c03640145d02c541c036030b8503008131394008447c0b03110700200c018001928034040210021b000524031039001050140c40e0f0680b83d001c40d5111500c2000d03200a400041482110703540c58801e03804181004840c5000c03014148075001c4074a52040c0070b004c2c060109500144543c200e03003d458078006807074030582942d0f44030390400050003010900403d03039001d050981c0c1131400e50400d400180102c0307103504041e00070b9000e50 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 9293919 1250 9292669 9292709
    0x60106021203041b0807030506060301020301031e030e13060303020105060a0e04080a020a020a030b0405060604060308090d02060702100305010f0b070c05040b06070c0906051e060706021b0609060f01 87
    0x104000311012071201030156666610300d40141141e8074949030000d000090800403d0b4180c0005e00b500a4034040c00854841d40c2c2e0b0383c01018281c2c4000d000007406000d00032807142824009200c14910548030f42441c001c14984040883c1c0d0810383c0c000044034250710348004005040d020b2180c25045041900c2044005040440401404c400600010120f9400140094031a442404086c040d40d900a10a4900c00d6481c1811510654107403020f80c0ca074003503140030458a140610030b65040341c0c2d000c50001d080900f00e4007000030b904200782003681c12002c1005210b0041c0c1e12000301c508040d6082e1800102941010034440f0102d041d41c100c446407490422145010501c20031003501210000ca402243c0c4001c0c2c80301103a154050214020000d411480c0c01244005503508070380c068035000c0d1034480f0460070001000440d01910200290450000c00110700403813510f4000300103031040360400d01c4407201342c1456076292400840f2a02c0340c0350007182c14004240750700c0406a00410b009216060b2a071205 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 9295169 1250 9293919 9293923
    0x1b0203031501051b0601080a0b0106030e0703060e010204051201020703030605030a050c0904030504090e0f01200d020901090305070e01051302030601020d0c05121305030724030905010b090405010f06050306010602 93
    0x81d019142c1403000c04540401881e8114140b0600e46030214152151540d403080160f94849402c281129070300c24800010400502c28803442c45a104c101005001642c503503280c0800034420495a440c4a54007004040341c0343c1c4030484449150620341000590341c000c03504008040b10540d820140c80303074000036010404290009103d0b40d429004032040c090343e8680b441c09031174511456000807041c0b8103005060703400c0003011a079003103030f280c050b0024088100660117035624294101800f050500c4203014a904517003507030707000d040c04101c18140819429100d880d00c03443c1600350342c01900800ca0010042c085401c16108241c1029803520055040d814190000f0751900031345071000c0204070b901610103090000402c00c0d4080a03450000c1c403680d4030b2401c00c0754121080c1601415000f480380c44030001d4480340910108204448814611a4080401400710050024020241e079079640310080c614066840005840c05103204800008186000c1000c00d0203588003a0300c041c0c46604104010080c103500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 9296419 1250 9295169 9295201
    0x181a030c0a090909060905060f0c0a050306030f0703080a03060909020f0f0310020406031a09040c05060703090b040b030105040b0307050303030112050304170f120c10020a050c010f1b020303 83
    0x160322999200c0204035421222001941e2104030180d04103854a02400f1103544807100f842c0c01101a50080c3d0b450300381c90004800284c0380340382c02075000c00444040512510155800190042c01d07214840203041c11185880081e030000e1710303c0b80001440108258040c07207a10300500c1620820300044800707400181188244051044c0109580c0d101d0002e01c0d03605102c44011b0700034110b0119203e0b5195903006000300301c0d800034200c50320300101d04101c0340d1a00110140c480c03680580b2001d0349038201000d004254103c040c1c200d0500415407008280624214054030241908000d943d0304e96141104100544103008102d60183d0000c960522094038040110707030646145145030310481034103241480c554800c84c0d0100060803a00a1046444140802c004005a003140e040764280f95085d014a901e038821a4042c54480d071149800128523100e54024060080c0c407420003d0400e265007840d00e003500d400780590740e222980c807085010114912801d80c5501d1945100450440c6003130b081e82040004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 9297669 1250 9296419 9296431
    0x1050412030902030102120108071d0f0402010318060c050307030605041401030201050901050403021203040305010b0303031003030e0111010518010c020d0203090f03010b0604031a180a0b0901020408010c181a03 92
    0x902e5201c0b200035914250111041c540f07040200c05055a503c00c406030312000180070318440c1c1030b0240f0600c00d42148101d132280c000d501c07641d490521500c0300e50040d030080c02007161050202d40580000300100700a845a07400c80a00c545482d075980c07030101c00003011102c2d503800081c0b29a103406c000500b54010101d009064075820b080081e551440480143c81a0040f540001d41c00b8030020314184080e075001c0042c2c000c4034854802800682040405c040d141d000803a01c2e4518491900c8003000407911428890320110b6044c1031048149070010f030300c5802d5807001c51308a207100c0000102d401101100740301b824412801032000e031490b1110b03404025101e1041043d07061003481301ea103a8001564003940404200700b002400721b43c0c5c8680d40e10305104542080302c0084a07000b481000a8007070403004010b01d99441250f005080e10340869540d032012500050304518040d94203020219204109119400003669181c40300340e00d0a10140104c3c00740c1c00a81c026107090440703e0801d515040e030704415250000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 9298919 1250 9297669 9297671
    0x15030302031806040f0f0504050a02040803030a020702010512011502062d040203100203070903030806090f0103030309060603050d020c040e1203130f021c060e060c0901030e0c031203180105041203 86
    0x3408090000f50316004681206281106400000848040326540300d42290300c01d5409210700c3d500e43c40c8003401c81c0550710600c59950403c0001078001d59035907008086142c41414050301700b000c1d090440000b0307d030982260324420343d202020440705804002e0264446100c210b508000680201c080300445c100c1118410b409010401007000c43d03805201700c21a202d001081151079182c1a08010183c012501c0284d000c1042d070b4001c07034091b007031940c145031003160701e140010700d50391031a5400c1b0000c11040e101a5011940c5800c0400020000c0c4203900700c0303010030f50007003983e003803000c00b08030480300074900303403512a0701403648030346a0012001602d6003d480a4116011702007503050011044000c0e0300002d500507902c01c2e58001c256902030031043d1080c011117081007031038122051a50b0750700d001d03500702c1354204041c0308441c010741c0700c1c1e00880310001403602900c0a030380c42d44000c00c1c540807a0042d90181100040104040c62400200c2141218442c80080c881e07801d29486000412401d144030b94101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 9300169 1250 9298919 9298957
    0x1e020c04110403140c10020a0305030c0a0c0606090f0c030204030b010e070c061401060f03050405120310030501050103110102010506100504030204020f1c0905070602010207020901091a0d11041503030203 89
    0x101e11403005070b50045801a0403000c50100a061640e1183d0410f406144950391401c80d44491520004211101a03415280d081c950707280d44905041c179810024101c4200200009070350005051405420004d003140740e0040b46a461025182e000e9410300c0c03141004245c0b05110800129200ca4000c0381103882100d04410b894071001000c07100f03800320000180c02c16007801d42c0350000e4448951002c0c1218031130307030300c1074181c1d00d00c280114140e480688001c2c14680c42034001010320380c1980019900051243c24242885a83e0b80e101429102d09920903150341070f40c0190482c0558081c010260300041c00c4925024000700b100c2c0251150240780000390140d83d0101d004d00c031801c030349000c8425201000140b450390700124000080980360b0110200d4041c011080d0009203d8014000c1d2101d843c3e0040c2810001e030308000660000b0580c03402c0c0b060b07016480e001e80c001f02d070301c80303071001000c4a01840c60340c054040703104140000d8070243c0556a400e48002c25082000c40d5000c001e442074520004008601 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 9301419 1250 9300169 9300191
    0x30a0b03030f0a0801050f0a0303050a0f030f060609091413060b0402070c14040e0c0604030303020702040603080a08010812040605070609030905090109020a1205070e12071d04031e020c04 82
    0x103140102002c41c401ca4500107003000b07455401801d468100c0700120707000c01c1c0001c491014420164034a200c0200420010310070b5124242c00707000001a025000c0c030b0b000590604410190044d10300c2680b1144c0450044d90080c04040c80030f026104410141c031020b0711160400b100050000c0581075070103403845658607003841e4542e64580445203040e4000140c00352041d2928501000c2c02ca01d44a603d101c1c514080c0050801200032941c5a5289070086c012030415165840c164082d600c162401c0342e10551328400400095002c402501564294cd920710495604003901c41e46040300b00002e940c3c0060060004200403684001222032442d800f000218041c02c142c0707030a8618000d55000b86601408102c0042041c500680c0a0240710320702c0c1d51644100045020800120340d0103496210000e800c030318045541e818203c9900074462002022107801a981d000c181c050615010828506c0c040040c0601c000e050b4080083c00301c0719449820300d21003001e1940b003c1e40e19511780d0385250003281c0f54001d00e49 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 9302669 1250 9301419 9301423
    0x506070c0602040e0106080612060103020913080408060901060315050405070302040b04020d110a090504050405060604050403110a060207030905040b0d1202010902030303100602070f0803030103030305100302100e0a06030908030a0b03 102
    0x829544600e03201550711508007030007500048523031a004a08000e203a4088207400107002d030480b5006000429181c80b5040710001e03800101d002a9040c0300300b0800024110401c01c04503204038103404c00002c0c024110f2a017544850511440c2805085c101428013004c16408501c1300c04403a0b044500003480e00940021a000c0c0c000c0604103019185031640211002e5001401803041500540d03642540c1501d42c2d08000448006840240c440d40c4000c000521504140d44040d402c20702900700170300b84003500741d025454025501c0007103800d1900401d0744020150040d03250740c060202110144211040383d80440c1c184402d0202c050300130021141e12040840c000c1d0701070010680c0103009d50380c0d6840d00d422800d02c603031040c0c814500144160040000c0f10008005038000347d5072020080e524592a58508801411020f401e00c17410540340c06002006a550203c40c2c5034090054540c3c0036a641840200f01462901e03900400030b02d82030007001400569401c0c00c03a98850010340001481d1314003400800c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 9303919 1250 9302669 9302677
    0x31e030a0605060d0605010306081914010e06070c0203100b012309040204060e150a020a03030b0f0d0302010509070608090d080a06120b09010507020a1a070e030115090f090506070c0602 81
    0xb0350000d6000440200305440c5030440d405560007a28144415555101b0444c1d8940f41c201980c1094078001a403180040e446400f6200c610b616038001041c1c0240c0340d9032103030a1441c140e8400012a115141e40000c50409000500b00c01660b40b2003042080044000a00f00c84041041c684080c1050141d158401800300241e541b001c901034401c544864032800083c1c45113840441603481504007030880008418031404440c3c01e00400e501400868076503541c00e601508501030925440914081c02c06c0441d1039240c18142024040c2d4004070b020300340307001c04508143c000c0d0026400c0100100410003c0c0c14001030061101803a494170000c2caa40b5041280020041a00110214210f02c1000d5007400a03280c41240190300d940000c100a03100c5c020180e940d01203d40d00182120300c28150b0488030301001e4052030380900c0301c1c203008550350007110000e802c40740804040044000e26210a0044450341d1140030440d01d59045c04120310032071611403507903030040100709004000c082c142c20802c1086d581c040da = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 9305169 1250 9303919 9303929
    0x71409010c150b040b030a0201200a05010504030314070e0f010507030201020d0f020a14090f09040501090f060c030e0c09010b0306010c050a050109030323040602160c032102031e030a06 81
    0x64902c48450040100280c80e005010074422428800d400c05149000324820b010039034141c46d154640007502142c3c88030420005401e000c1405400e410001140003806028800c038440c2c1da00241c40145050110144507010305070608000064800074100d80b80c01501c41141002401c0c103544403003081c50128064465024a140e41da818070900e403241032520f40292a40c40015100c90341c603541d649012656a0040c079000550040380d00128000f241403010130250064044e00005c50071410b40d403a00045240002c0c0e003121003940d18400110341c681e241c030131403080280a80181c891200380400040d01d400041c082c55401140000101d00580c1c0a101d6010950f0740c0030342921207614880c20503600074200302c441600883d0400c80d07600200300080341041b4010501c9980178a003502c0f81c0d21004000c0d0080210740c090303184505038a00c04110407a4a01006521841c1090840a501d400074410b8003007031124038065500c24480c8054400e50340d0320b211461000700c1c1000e03440e983c5204000c1c025205a03401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 9306419 1250 9305169 9305183
    0x41506170a02031c020309010c0c05030d0c0b090102040b090f0d0b040b010f1a0a18050a080105090d050304150b01020304090f02030a0506030c0d020f0a0306050907031101020303071409010c 83
    0x1803100040301040a00c1d906000700c080e07a4020100320f4981c0c8842e041c0010540050300104052501036028010403a0240d0040d001840e0381078031200400d242c110403007001408140c00100030400c02141c10f049036440203030030000f581010300e449400101c50060b0200c680c800c00b000c01e4a11129282c0e00d80f804202030300b180e1401d11034105810300a02942c001c0c0202da50502c1102c02c0443d0308012008540da2880e01016928500342c40c07004111540c3d40142c40c40049020030200c001626903d4907807100140c049100001524200000c1c4549007401e1003c56900b4810240104404906c10f42011101814214030115105180e100100d0940c441c07900700c0e1038032614103680701c0041d941d41e9010314400c00120710108460340301ca000305a501c601292605901004691910b0b005040c0406c001c40c2c1c0f440e01805201c130854030b075640c00c002c0e9041250780310941d9210010070820700080603600c004045082c0055499818201001011481861140707100141c0c00592070195074030404800c214540c110f21 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 9307669 1250 9306419 9306449
    0x402060904060303110d090f0314071a0c10060303050702120f0105040c05030c0d0203060106030c050c011805060a140c091816090902040815040507080d050904050915041506 76
    0x25020b00f25001250441721644035110038407803003e00071184102034840d120104e058452855407100c280b01c81044000043e8004c0690024000420f500e034840b240880d4290540c0f1800a044524905a035410100070300078241001000802d411004a0386540c0d0140e030b40a00c901150003160340341c1850383c0030041d007640c038010811050103451218901a290120f00303907111f1038911001c205c2c4d1814506006945504200b004002080c080d030700800303182c0305604040f0f09201c4c4002410b8216a40b108992400d800c1703078080101004814001c07164030105100b001c02c80d44555001c001906440104a0201500002a844650ba0b260049400e80300c5000b0705c48101484d0640380c0c3e1221130100210a00814848003021a00d420b050098070203a414580050400500c080002d005c1c0000c041e0090354140922440803d60b00424061458a080c403500c400380c2e901d0585040c002215402000100960803d903001441140d90340481500706030840701804034000d0707203c3e6143c01400154488000540300b45 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 9308919 1250 9307669 9307673
    0x1051e040906180209130f09020303070b040b060303030705040306050403030207060203041103011116120e0306070201050601090501050c0d080a0e010606090e1005010c12030f02270a120204020304020609040603 92
    0x14102400b503a0f407082c070b400c11100364400e004042e4055000095031045402082d440890340c00e41c410780700d00350014800314401c070035034001c03e0460780f180c4016038481c907026040005205040030071a400c900242c1c000d500d9031401030740090160046002c020501d51b190800308052510a070103548006400441c219902e041601c1c00e43c0d140441c1c003150600a500f072500c1003510000c21416120703003030301c480181d8020560729035030756070300140070b6215209010346000700c00d240b034604100f110310178640350300001418180740001616030300c00c503840181000000c0103202c403050008540d5410144483c10848c1058850311010b41c00392500d42501a5a50f01e030a20015980743e0104054003110b150506091003034640c4c82152410008a000d1079000c5071000c0081000140e0000d0700580c0705006c6d18002840185640c40b00061342d01c400082000f45105a5a4101450240340f0301120075000b02c800c070392013602c1e002d0080d03d16107507104003922407a03000c00002c1c150b4079914102d84880c01c0081040140b20703128 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 9310169 1250 9308919 9308921
    0x40c030905010b0301050c2b05040b0a060506070c0b130819020108010506030603060403110a0803011d0a060608070c030903020603010603060303090b0a080f0901140709080d03051501051e0409 84
    0x100c905403055800d11041110506041c41954014403011660a00d0405100c0755044405501d9881260030015598484203c04c0984900f60040d481a00f80c2009803c00481c10030644400341c21440c4074040822603600001c40b289050021134808031807042c1c444081c41a400642009640421001c1c011042c800176a807252078180ca001074405d0300c0300700c096600c402c240805030100720ba020b0b0305036001c1030215011a0191450002c101c1141c0221032882036071b40c0e200c1d60290400c1c1d10606c600c1100500e046605c10b05820943c1e4012680d850070449039140050041070b14801818030b80c140700c484100d00007810b1203100b00c50059600a000c055803540c1d035610040c01817200784010b400240090718007003002c1503c401128a200307019500c07240280c0340e00242e2209a0000b40c03070300000d0365031108442e00720750607040d0351886800c0b6a21061180c0c0d141a101c01d0602c3d11900f8260109454541085107480040400203080102860070030380f01d000d0901c14101f14105551403e4200102240010b4040c940d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 9311419 1250 9310169 9310181
    0x50a05060108070905150114040f090203070e030102090306060415030b0c04050301050c040605030a0b01030e0604140606030a1a0702160b03091006030305030a050a1d1606020c010203030c0d0b040c03 87
    0x140d4080f140556590344119045640544844056421440c04c12183c2d62181440a40390307008648510320f0142e80e6030030400c2d40840b65000868a0b500803040101841e005940965000c0c0d0940c001c1d4988140c0c040004d403030b120010a840d1141c0d81d1528503404010007400f00e07101440e48819142411f0404070b07001000f54000b4441c0910035030910380054040304180c400d80d000c40c0c480d80c54890544c3c6801104601030401343c0b43c020f04040d0744181c81d07021075404100d010700503802440a804401038070700040b410f000f00180174a0081d07010000a10010f8018003209995000d506910401525240c004a00f4841c07071203280d2505855946000c25075080d032400a500070b0011408403007a50303007000f05100a54206100140c00300360240001060340c281b40e003055502411410300000e03150154062140669681888891a640006800030040e44840b0340c4030301074842800100303003000d102c0000035502c2c40004e0883c001d403900410b002d0642da415400190302c00c1e900500911426824440007001001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 9312669 1250 9311419 9311429
    0x6050301020a050c010c02031204060b040219030207020406061107060806030a050d110606090c030106080703060f0b12090c06070f050309030d0f1701080d03020702030309030102070318090209010f110a050a050601 93
    0x11811301c6c5003c0d52800082100d50107900c00990712150790b40d0b030311414010308250b00d060350815000c01c527582d80d03980303010920710243c00030751001601c034110f40c01484203c81042e00082e0500007000c01521189400145d04404c80d0400d01d80703152596603603004030381044e000c144005d001c2d21440c3c0654801c0350b007084042c540b100402c411114203554420400059590640d141e0008120404c01842007501c2045a1a405000c505000c00d600340d4030f9060b4244044241d128180c80c400c08130740c0c8c51502c1a200c1559070031500306401004c0507520400020068030a50714010802c0800d500080c2c00c20000703006032804c500703004094440d0102c0400c00948881c0e1440b00e0200041e51600e444007600c070b1011149410707520780c00d00800b552018880140e009501c04033b4141c0e8507100c240090788907a9000d000401c4074502c031380e40d800b05d40e1011002c60014402180c0011704c0035401070000c0301841e648007070031085825031441d00313001030030b5818051814585070000180c518040c00303142000b40480002e08904941e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 9313919 1250 9312669 9312671
    0xa06060b040e0c070b040f030e090c0d0b06070b06040203040c0e13060c020105040b0601110115080a05010b010903110118031a04020a080a050a02060f091002070602010b090106050d09030306050301020a050c01 91
    0x9500d081d0f900d402c601c5200c01c020b000c01c6100c00410082040907040e640c2031403090405000c4500c0f9032000448010085601c0c40002800198031540c0000a01902c0b0369820b0690f50725041c0681e40c0d0352800b2a00000701090300a56002c4001001d0110b48140030000741500200d001d01e0b4140341785090070510030b0000079140c403428017859203074080c4144030343c40c03145420406801580c1c954a004456507540010444010b45d240c507211014440340444440041540c1070007011009202e00d031040c20349001e8039030541404001d0740100040744507103c04521800091030200c1d501c02d82c020391064965410b41005d03160b01c12200f2800360242d01d440503240603900031039090704025951007081c0e03601c0d007690500520365003209980c00014203080015007007121280b00312508051440700846d4202e820400058010303031286030708002c800d4080c42104060380040e54581038541c1083c00240c100e125055040460702d980c1c403401c60902d4460383c4450054080140255074400c909400108507400a0000140c3c82d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 9315169 1250 9313919 9313921
    0x4080c0405060d11040b060f040e01080f03030108031207051201090203040201120605060409021602040908070b0106051303110102150109091103060402030d110c0a180f060501020c0d050a06060b040e 87
    0x10f14045001402c3e007a0310100c0341901200380b00034480074081400106400000c24410b00c51421407140207040030b8a41c81116140fa50f140030501071510f6000000805180c10810060000c00c1000c01181c1c107111068244c0216a152070074210f0317240c840c0d6001c0500e2440080004184040660020340c00f0354002da9403100e407070504a500301c00f00e4400380302d080d80c002010441000014000d40203040300b0300c503c109100c5182c50f40d401040a45844240880f01400300040b0141045608040140504000e262003404c10804040360303030074003041e4000504240710218402545130310800c40c90aa1042d140d00d01c02440d6502c400b070741c0c068417540604a500e21102e4004103050300740003a1340761150303030010007c056450f0302c0131040d19440d120f040301152a0144001c51286501e400c44180c0c024590f4070500c4150880c0510000700322140c11104000c054209034041020b40c0e03000403000c040c02d03022036058018171540d20b0000c1c0b4000151342c00805403800c01000160800d40140608201c030321180900c0f5072 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 9316419 1250 9315169 9315181
    0xe1f031b09050d06060b0c0708060a020306150306060c0d050a020c010809030417070305071508010509060102060a050702010608060c07020406060807050d020901120e06011a040602070b09060f04080c0405 89
    0x60021480003002401c4032008002e18a02002c10240c12030141000044041c0c03100798080761640aa20340c0c061740d80c802c01c01040900d8003007240c0e55000081540031415801d00000040715001c041041001d98000440450401d40c2c8800451320740f00340550444841c0c41f1060005009034100f40064000750158803c112440d5010702c8031288100b4004000d11314050070300d180020b000d111041041c4880c420036001000058080080780c0c00380060502310121001c606000403c0b220058000c41e000b20402028080d259030001507003500300a0201c3c3c0415a0380d222076040f070040445600c100120720400041c020218006001081614003e40d403d100b40b549906054400c02c4003036079404006071042000d80e50540301640540405039051500580e4500184000d906449810032114040d0b0460300c0100700f560703041e5100003004d0b5a000712a40c181841e010f40030b900c0790301d41d206002000c18000b4500440d40d49010865091440308a8507548554a681e6007a55032500a41e100c2d00551801c000700380 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 9317669 1250 9316419 9316451
    0x90616030e0c04020a02010e03130e0a06080c0f01020c0d11090108030a0504031101090b0711030c01140a12090b010303020607020c0603041502090120030d0b09070f0f0e1f03 76
    0x5490101d01000380910200041440029400081d0030402c6550b20f4403400b00750102031008050f030700c40119003200c03483e013441030903a90f0500240c00ca00410345460320401c4084008203982d000120122001e840c1c0c584889d006178242918418030a51110005013400100400540045078408090b551029281c2c1c983e903c440d982d1044103a010042501408200700003401a05403600032103040c500382c16015a40d211094694100d0741d0300b241c41c0d42c41061450007a00302040310a07620179003443e04615903582d083c0d2414692241a100b02e040001d07101602d80c10300016005164102c3e40588032302d45a60752410029100e503015038101005014004a600d81486c00074181c83c001d0b42c1040b400720f843c1e0046900400250310440c45c29051264241d074a43d032408410800d40c10342c41c5450007441da94455048513400300c4d01d28032440b0707105c0c0c8150b8043c003003400d81c01000340786810040e080c240700078520604280c1d9a03043c41035405c1d40c0b00e070740c003200031a83c4038110111a05140180e2000d00c0f01c841e001d20415 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 9318919 1250 9317669 9317681
    0x7030603051e0703140a0506010f05120109030f030f09050f010e070608040b060103020304110306100501020f151f1502030901030506031f0507260f0106090e010302040f0b060309061603 81
    0x941c69000400510100b50308040746400b240700102100d0a046d20f40c1e81d02030a10809038003c00810b5070200c810446d5040c420b000180c80d110300710003004401c00960300038229032814000201010303a656181040c40c5078075840280e01c02e400030300322102c81d1300f20f03590340c2d028080580212101d03014403040054036600502c1e0442c0500e9100840503900d41e9075070f0046000350001081a500300c2d1100442c060036032814400a401502c02c03801c070301c13212804c0c007001a181c0084801c0d00010f030791020566a100748400e038142c0750040d0b9040b09128800c0160a030f241e160441c0b41d00020078003080048048071090b0004014944801d007a2814050703950754000305a21001e05101c030b4000d48603403071740e0f13400310000c43d6220503889800c0313003020400d000e070140e039143c0d04a0032104010300f00d15041d81441101031001892500401d55840e00242c11070030300c2c981007604c2c5018070009004d40c0d2124000707680842103030412850f00102a01c4a9101d10746244910799801c2d0589080f240c8801c00e20040c01c840344603001c0c0d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 9320169 1250 9318919 9318973
    0x706060504140c04090906091e05070f0503060417041508011401030e10090302120d02040f0902040501170403050f160b0c03090705011d03011b0201270204020702010e0303030703060305 81
    0x5603007845d10704030300700e0042c20442404440b044c0d80c9440031400148016030801400300b1500806060009a250941ca000142e801c050754070301106108101c1503400080c05a4016404004031390f0301c1d0740702d680c080040e0182c1c0d003220220110b04980010190703484013641d0304a5400400300c6c000ca00d2040d006401f140c0c0754002d0100560002103408124200301e4015412042c40f03031048030f503102c02101e9404000e42194444510658001074108a1031000c518894064001210f04601d0240b4100c0081d000840440a0262541c2900002000d150081050b1603171644083c8100341d80d144544400b01e810540701004036419858075000c500c11600304002d5034411490034008155040c101001036036007031030008400c0741203440420401001d860a00801480c1300081710980204082c0420203400e40c1d00d501d42c280c0c01c21518040942c144c4416104035400f0030f4046d1801030703980c0311600040f03590700d4003080165014400001403004c0f080d89984680200c2e07014109840c0700440e0140a548855038000e04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 9321419 1250 9320169 9320191
    0x903071208070f030b13050901020c0c041a10030b0603040602040806070306031119090f090b090d050711040b120610060e030309040c021c08010311010f08070e010201060902070606050414 82
    0x83c0c0f400380d00a6002100000c1c00400d90480803c603400024207075030302150710510994004c40c803450990300407c5000501d0104a40900548100c0200782079081c0c0304001c554800c601c10600160101c0c000e074460039001d50050f2100e0354034a41410b01002940c002d01c1500c0261003000b001900e50b6208e84140415254000c0303050903c00e03410810440203c0c400014008441ca01080020f4000c1e031038400d0040c00350021038045144c460b14140309212902c001c098500e150032002c280c05099500000b2124001d034020320355241e0b1084000400d0041200b40c0815420081005c40c050004130001030b4248181c140105e2400305a480f402c3c112271884d041c08229802d41c0c02070204003c80c0ca0142c0000310700040c144110341d01c1d418000071818090381e0002074000425100f10044c0103000040103901803c950a0809900c0007031514070080810500520703540070803004407020f100750380c07003034100c0340050510741d809546403402c3e0300380007006141d03a209551007549850091400d0b11028140c5070311500409103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 9322669 1250 9321419 9321437
    0x1140307060f0504050d11100503040b24030a030908100b010e0405060d0c1e1d07030b120f03040509100303020a0303050a060e0f0405010506010e0a0513020403050303090307120807 79
    0x1c4259076804280c1115810f002d824080412035444640400090342c1c0945600144e043c07603c014007040d5640c40340c0301c004101c42041040301103030311110350350f0300704643d0a1114103082a1010b004400101500c0c09a85401181c614800740365000b950b000a0b80c8160701a00d040d99101c0341c0d0b10040b04e107440100c40c049881ca40080b040c03860a940725903403060300234003680c0e00000b0366507030046040340b01e411182c0c00c0414958003400d18a092a200030191a000d1203d84094245030130070446440700801030400c01d9100c60051055450701110030400d00003070341c06c5818011001340b40340c1d1640c100c1d004030384c000c0540e030780000c00c0c581c2c02c2c010741d2040b290560003405500004e51811009044000e01400d5035071341f280c00001d03d0648450300144a480384030281d40c0c41d42414a4103d0a6034030182c102030400414004502280e51010150411240700302ea900c00180040700e2400060300407544098100d00020003000b004903004001040741e280300b0358101d00001c402c0728050f07491181c142e03400303030000702e40c14 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 9323919 1250 9322669 9322679
    0x30c01020f0c0d050f030408030d0e0a020d0f020301060e0c04030b06030304050105071209051009030501150506030115020f03030901090506010b0f03010b0706020c070602010605120105130b10030605010f0e01140307 94
    0xa2100e03c402d030240007511040d8030b40c1c0c07021a25591266120744156400040c25108800311741c4140100600440050004000d080d00010318005c042c54010340560140c180306400c55500754000c40041640c0800e1800070b24241452362480d403c688406c0d208803d41c50300054061902100719400e481c0f0586900381094055210600d1402d0399040c40010f1086e07141c4041525922200f015011240c5aa00c0941042c118900035003540c038483e0400c0b14406580d40d0a20003640d42d2400d5030306541c1500d41060b4001800c520492804102c01441c0e01c40f03010001c240100c01e101900200c400324000c500315001c07039988413180c00d442d10800b160144d4180c414001803000350103182c000c0c510103005910160814608821a50420080e0340c440c0002d41c0d0346400410081c01d00b0750021480d64103040080245280c200d0303409810140c0d002c0b008092698440005400c03554105815003d16000702040003d50b8440402088202d100d0040c6c05815841c0c02c00005ea10121980e001c03528403024020b409035520b00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 9325169 1250 9323919 9323929
    0xa0503060a08060a02130503060907140a09020d05090d0507080d050402150307120c0207060804020603130f05060402010201140112121e0203030105040605010c0812040614040b06030c01020f0c 84
    0x350505500050201e4001980001085124010042558010380d240d50702140c0c2515041c0c968800e0303010340c00c0759003040901d2001040b0070080b20290300b100c0680c12150000185101d00e40d40082d12040d00c04035014201c0790917540068400c002860450314500007555056075980a440001040c400d810048011180c0c1150401034009101400b00c1c0042013101010340c81e00c2e08200d0341c040004501d5214082410428018a071403901540090300c052421714034010140c0c0341c0103001034000d440010118890714038101011032040d070010302880d1403c19a1804640f00c1c1c0c02550140c2c0190309003680d00030101c0c00110907504964981c052514161000e81d101d0100b481c0b00413900d41800441020f501c4039141254014080c403c00703501441e62981441c04002c102c402c40d8104504210200640c140000d00c500110341040000760700c91030050751103181000107040d8092020680f0940c1406000801000080703540c0292021000e44039810014801262346a03d0140181250303480b0000b0303108030f4100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 9326419 1250 9325169 9325171
    0x5010327020f0d110307060503010501020706110f0307080a020606010512040308070c0b010609030b010803030403090605070c0305160315110d09020d05120405010f09060509040f0213030b0a06050301020c030a0503 93
    0x202410000c2c09800b144000307031401d50400c0040d82c0c86851140d0100a5250501c500405030200e410030504550400d00001c1d6106c459015a000740700c00c000f96240004810806080c5080b0000100c03666500c017841c1042098101108150142c840e9001050642d80240142d8030000c2a803800513000d075403603071401c0314024405041c0308107000004007028042510b22864a010704400d407100f10703082d491407920700c0c2c0584050b404440349800910500001a901001502c00c4411502d400b98035a04981040111640d45a10090051041403107000c540740483d48041d017164007806c40783c2c50500328903401d98140c450a06c00310002c0c80381000b107141500500d07405070001c180003401030303800b5800c0e583c0c0e803501d401580081002c5c1017201050070071466030f0100481030203601d81e01d0800e440d289040381c050480d001d4035021314031458a42c560156520203136419200b15907188503040040301d83e40d041c00d19004000b508e02900702401c017400412141014021150300900010056113400e140e20b8084900340c00c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 9327669 1250 9326419 9326423
    0xf0402030a0b090c0301080f0109020d060506150d060e09030715020a050f030108060a050606070c36050103120302071502031b0f0d06090b01050d0509010e0a05010f0605010327 77
    0x2035100306515a5441c3c00280038407800700030f40e42c00e0382e035410420900e142141d894a01a15a03040c808101c0c0180c4590517a00402540108040f40a4548030001000d0755100c600740428124081801982036107650050411035655048058507902c03008100c58880c840d40c4030141c00302c0910107203a940c01c0c51680c0146520009032410500b4881d100e500030103e54802c0c0d000704840c1c0d0010003804264a40e0340f15494000d0300864046d0301e4101241e8400040354001e20520901c8480e1206824220346045035117641078500015008000d1034111450703009043c02c0c0000e4410f0a08150b066408a010b80b0844228a0300b00701e0140181c11044c41e0391010f513000804a130780718810300540390300f882c0d00c800c0600701d41340c401c0700c0313040d2600b40c0c0c111044110b941d030350700c610035107820100307040b4040e60050121340b82248040d101182030350b00c840c0058054403101050302c05600c1998041024818103500c5002ca1050303010b414094203235180011016100c242c1407070401a040c01d01c3c1c0705664a501e03100070446038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 9328919 1250 9327669 9327671
    0x402010c032a0c0509070309020d0809030a081614060106050f090604090507050301031505061305070306080607050405030105160e010c05160b09030f06041709010c050703080a02070b030103020f0402030a 89
    0x9410718070240d00b80500c0c0c1d800b1034460100c1c2d0020b20891601003442940402c03c0e00d420480505640c00041c0d60000c1d100d80039150260000d9001d00302d44017400044c00d860342051045035101d048000c0460804445c0308191640c921803404180d032150041103d030b0482d606030f60340700d05210b07480822618961001010540c4603204020002d420400740c0a468807a801c0d640301c050b00c940c9541880c81100c4132011248021500d84820410b1540c0d6403464001c5290258030001050703a42d030310081d8004c08058102086602c140c10801a0103a40500200107641c010b90086c0080d48880b91004c0c10244074a13518004030b40007150000c015445212071100300d0303008000301c0303501c800c529006051020180d0040411175a00044100d010709003040300880c10b02841000b0316241c64680c4880036451900754465109c000300240403582070780300e4054281c09a4000c415643d00e20740d03d2509107042c1d444042c46501500910400044401c103050135a8100da80141c00080e03002142c1d030812009510080282c030002d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 9330169 1250 9328919 9328967
    0x2040203010b18192c010f060206011203091202010309050714040b01031b0c05071a070303110702030d1d030102030a0b01110706050904021e07030c03080105060a0e0904020a0e0a05040204140402010c03 88
    0x30005e00d14074107000b49001b8941c104030702c0c00c1400007070030510160000802a1401c1c06440c00013940500d80e0012143d00e00c6014400300100c0c80128045c000c81c940141040c820b440000c1090116a0805000920b044030200411b0b90b0220041d0280e800c5500003d86032034402c0c01c0004014007134600f86090300c1c842c0c8280c0700400d4440d08480b41c0c0f500d69241d042c460100105030041010b0300351048242142801a01a00b40303111075001030340d00c1d40d00e1100310b0b082129814065003040c0745003e01108070b0200400a54480c40e1003040724000b002d410022500092200c101c80300c0010001c40da01040e161142e880b5032500441206110195100c42d0f01c003501070340200181080404500c000d80001842641d0300340c901c15013410000d19007a41a007065100351001c0014a0740507411502840e0081d40542d81c103001940c46000240200c4aa80c1c03040a00162000c01c008200c203403030744a181f140b0f200301c2d02000003000c42100c4e5403190504070b4001b80031070400b61300d02c03021900031039442e0034401c10200e2035403017 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 9331419 1250 9330169 9330239
    0x4030c020a0602010b01090905010b1603030f06080c040f02030402010c060213030204050f070906020607050a0309022403160306050f010e0d1203092015070305040302040203010b1819 80
    0x211810715403040340183d548020056a56030f11a030703042d00505031010180815410500228050321801e0042c00404c03403203058110825003e9080404c070b000c11700b0000c000c0700b43c0d50070100784c55007041088a031050b0b183c140f080d121108284240e038000d40c2c040c1c2d04c40030100520754400000350302c03c030714207488119061000801030381da50081c0e52182082114113142410300420181c01440a83c01807419500607004000c95107038001e06075410400303d4940843c03150a01e001160b000140e0400c5000c8500c030300004400000310490045004140d4004c2c84441007603800c108174100c591501407598000c480302000440b9603c120010082d803507000700403001e03200071513403441e6401607031540010220f900d035820340d414010140f000d4071407800d03072040c04d691012002c40003a0101602c0410360b00a8030010499900b49031007041601e014550103442150780756140c601c158056040b046020340302000340080645241040b240a600e6143e0900082c1a02c030b06090311034584464041d18108074074101d074410f240c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 9332669 1250 9331419 9331429
    0xc0806011203020d0207050312070c0f060c14070503030426100e07140603060402071b0b07021005120105090711100506010206010803030f15010309020607140d030b030303040b04030c02 81
    0x4000e0403030a080d030440007036501d000ba06140d10042001c05541000e807080003680c5001c80d4601e6210208520581d41f00c00d1441d128003805600d410150040968400209409800c0055840264003031085035943e0850403040d04d0f1b4ada20303035002d041e4140c2c00030702081250310b032400b1100e4890031818024941c0c08080f011424944801145c00c0f040082d2030392416000e500040c44010040e1038420131510742120101c0100d402c5200140c03009002e5680040ca40060089a0340389a0399140303850140d44809551720369111258001140c00d0b4070403480040700c02e0b4070714010001c03110100d000a0020119a2801d400c22001040051a02051000a020642901c141400603c02090900b04005900d003003c400080c0382247c160800e200c15803041040c001142208101981c3c040c4400070242e400084406c0120003800300030030002e40042000c1040000c1151040c000007403e090502100d0b00c1940841044042d02c035068800c81e05600104003040c081201080c5056000f8040d06206815007860740c0414 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 9333919 1250 9332669 9332671
    0xe01080c041d010c0c1502090105070803070903020a15080106051c0c0203040504020f0301031e020105070602090f0d0506070305060a060e0d060902060403080408060108010203070e010305070908032109010c08010302010c0c0806 99
    0x40001075214910004011114a0006640e1b00100e401c5007009919000a4a24450040083e0008a01100090201c0e12407054400a1075014101c4500941d03070782030f8442d04240111010340415000c4d400400c80600c00d8050f10b080f1014942000d0140e030f00c10350b8401c003d200d080b01c0d540860004210104003030700c440c0024160396034900c00d82c2d5036030740c51428030a02606554450300ca103000540800d42c0540e80c05401d40b0301860f005400140e580803a00300142d040c04a9081c80794100c0b4104242c401801b0003c20b219104241648003404640c2c0c4a104101c260011350003010081000c0c8820b451355030034100070020240b481410000780903000b680014500350801d9004841c84140060240b095071801c0c0405801006007200a5003141003001c0094401c1e01d81e00b49103410581e40700006840390b031007105414024508541902d136240401c40400410300304565201e40c1205402010881d0420140b00d10002548aa981c40c1c0b0a40d007581e0044400c0040750509030b0703441d40040d001150002c810702c64a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 9335169 1250 9333919 9333941
    0x801061502010b03010b0a0e1f030303020903010e0708061b120c04030c0603110904050402031009080a09050105040302060a03020903030c030a180501030e0c15070803090a0b010e01080c041d01 84
    0x29516140303080080c29070341e0107804540a41d04100d00a500e5840e0000b100041e01e4410060140550310100c1440b00d803501c120b00b6200030320a81400100b8141c06034000c1003914000d8000b440140048401990760784602c0c0324400d91a13010500184040e4000e007482140000038104e480d1520300300d45c0c0400c40c40d8500f0b5601c090055130000703003001000210613005006007402c1c1428021984281c44d00d040a0185804160007280c0300c07400141159000d010701c150714614210300304205165801e02da0b0140e0072280d460800700d8000e2102044030340c014026074080360b90081001d4940010104210007a400c0003102e079400d84414040c148101da02440988502036055854086600c0101444107a100f013540c040c9041c5468071281150000003c42c1e900038251042e94040225044118402128854100041c0c078400c008014810f1070381c404602c1042c0c842c0079450071410750f621000a100c44180030320405045034410f074251480c1d801c181c0c00c40007400221a5005491464143c1c205081d20007007844 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 9336419 1250 9335169 9335189
    0x11030d0f08091608070602010e0601080604030302070f020301051005030c010504031707020a0f06020303040b130809090603070915050a1e0314030d0606050d060609080304030605190615111c1107080106 88
    0x105111b02a4244540100041c1e020005d14035545040f0055494600142001d400c1503000103a550a004c5100704245c00c8550183c020009807601d10360410458205004440c80782c0240604a00503620400540d825a034004c0c900f14102c04288024034a16407103240120f8000c0c4007034400190b50000aa980303c020a00c0381c001d151380f89000d1910300031181005010100c8520080e0310a000705403503000b0359003903035402c1e03c10a1860701c44a001038070380501079004081460614904101c0d0003a00c050300d00490718103880c0300c00c203030340c80b180043c144d441a20301c8803441780120f100400110304c0510030614101680400c5c1d80c9813050f5480460290f540b1a088400440c030b001503114100032143c407400004014034680030b60007905021403a0746910030b034030001d042951500042040e0103a03c40401e410b000f50a002000991b507120b200e51890b40000d80e481c0081a030051200c444070001144100c400369a200e040400300311010b20990b00d40d01c4060a011040c480c280001c0340441091050001030b103a5811 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 9337669 1250 9336419 9336433
    0x3090a0302010506010206010b0a050703170c04050108010509130b0403090308031302030c030a0b1603020405031b0306070306050a15030e0a050c0f1905060a0203070803100311030d0f08091608 84
    0x402038207643c40540aa8119442030004010750120082030f0f6503560106d1030900d654006a05040b5044000c0d1011088150984000d12000c01b1025004008646080e02d8084091781c2e0381c03040210b040e2003190000100703140e04400000246648203016881842410002030725600d940724118207070001c030345049401d98144201010343c6400c1110124200045004004e200315940d21003000020290140030138400b2803141e004801e0082d01504c3c081c1c0781c0035003140d554248400b0808524060000954000c6c01340501140005200b0b00808003510340c040c0403003103601c1c600020301c41d40c2405c4030b940c1402c0594420721270549000038400c0d00c0245000d10700a00718200843c2c10000310b00f01150880e03100d120792240084c201001000c2c0407007221000c0764840d46603904c90000307074103502c01c2e80340040c0080d0b800401c02240110240404050f02c1c000d6890f0400d02c186e0030300780740c0d48143c485154004564212102c00c030407480360b00b05139070222103070301550296000142e4104d0118003582084142c3d4200319 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 9338919 1250 9337669 9337673
    0x4030c14070e1806090c0906030c0d0602030a0606020307080906070f020d0b040309050d1104050709030c060503010608010506070308040b061201020d1406030106030b1305010207080a020102031806090312040f0803090a 95
    0x43c1107410307040c400360050405800c003414800c0c1c2e44d90081e503c060192400d43c000810b00c1d075007401034494407500940704142025081c68030300000d40c81203442d000201e181200c0450000d10020544a030385500040003460080707030070b08200d02500034440885000e00341032f1075000103071100c88100c03094500c2040c1e40145818280307030241c0780000300d811a034000c083d801044c101003a113035003102c12001c4007590002030549984c0800c0340d51032038980000e00203000740c1200048803a80080114100c03201503540180303691b01d0300c08001c480d00c00c109010380051b0303020001c100402c408405040c1c221740001c103e5080d03000c0c4904003070b00b03a070052070b147c5a40c0340d560825010030400c58104558001c108400802c045030030366680503031006010b801c5481d2074204490f80000c0200941c1107400003608960380680b550456030f030003401b0b9401151051060b40c182c0c84061001503000454074050b4004034082c50800600009a0002c640700400035202c1488010350180800c15903401103005010a901130035400c0118 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 9340169 1250 9338919 9338941
    0x20301050c0901090e060418050d02011b17070c05010f020c010b0603010f0e13020405040606051306150509030a08030901020301170a0f0210050c01050906060a061704030c14070e 78
    0x300001c5601c442004400b003141c0c1d101c14404181c40d100421030b030007a100e600c0440c0041003601440d82d50480001050710601400080d5084585881c2d07009120490b0660018520741c040c0b000044041600215241802125000a140d002034030703103070a481c6000903482d02030a4076001c07900001015800910126540401c0c002c225101505407826451949449010000c03d1030703d10030802c5001610000c24000b0302d800b442481d58940061090019007001e041ca0802400b172803051a100301a6001d2074220b249c03260080c402280d00602405072804007208003508c0d1a40460f03400350781400341003c01c80010b01c481015500401001d000142c40f90b0510500c001350f02d031380e000070052650040000c90009154090713001200c59040d01c11510840403020141c83d180210888080d0320b508000811248035070000d0011310440d81210218001961050180c0c0e50042042c4082200c195450000b80424081c040300c15000e0f100d85403407840396180403030380ba003010b034550004400103015000f408a03100d48 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 9341419 1250 9340169 9340171
    0xe010801060812090d0c090203100e0a15150c0501020d020c0c120304030312021b010b100512060f0a03080a051921050a0b06070308161e03020c1e010902030105 70
    0x21610092101d000f070f801d18440b50303000d61034800e80f0502460321083c0420907600403400c001c0c01e09150543d01c0c2c0c2084558070070106498096030000f003030145c00040d004040c9003e003032080b04101c034402d15601d0416210840c0c0c030308000d00c1d010a01020f8100d00c000698241700030160108803800c016182c1c14000c0307a240c00c00c1441203440e4441c05440b011041c1c81d10022040310126541800d0000f08000414200701c068040c04401545154443c0026174850398190440e13522944100c071721075140030320b44100352514001c1c11803443c1c400c80c00c00c000440500342140030003400b000080c068010ce558a61316422140d0102c440400001d00120f010041e12203c154800c81020060415513404d4a0100d440b060180e0391184811005840d400814149011503002062200f00130385019640c4403a414040c0c0254415907800075080c1c0400c03503400b0183e1082200c0741140e5004007901d500c22114a100b20043c1d0803c110a84980c05248680d46c0c1d07035a42141c1d900380d0503071030000108400b032541c0109421104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 9342669 1250 9341419 9341429
    0x9050105010f060503070e01020c0a03050303100b210901090609050a0302070f0b090906040608030a020a02011101020c0304050d03050909070e090708090d030c09081009020a08030903060a0e010e070e01080106 91
    0x1516420f1002c5a000000d80e80e000c94245002c080408100340100e1410005445007074000b50360250100c14003401000642c0b280c445d003020340d10780b20398440b02840b0901c12000e4a40d800c120300f15070f01d1401041c0c002c01507040010031300045903490098a815045414018003110302d0b500c040301000406406010680080c130485449c58141381c503109a20b1458400c80d0f19152090f101d6400194543c2e8a96018001a110314011240c80c0e054620001c0c0d51042014030581c046941071025940510050084030a80c031040c2002e50300f484c2c03821050215000c0c118004409108050142a48035141c211200d80b1801c0b9942c0da08940300d003e070b420700001000c042e155078200b011100410888040010fa12104181e030391400141147c00300380b0417550940e40fa04003e4960080150385e80b141c0300d458100c04942d9000b100c880ca09903a40f440c010b5980d11480044640603080305002500400c540c0d4048254420004c0000c190321100000c120b041121541141022a0080d0014007400900740706100280c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 9343919 1250 9342669 9342689
    0xe0906060108070e0f0f1c03020c01030e0a0f0602070201050c0a03031e02030f010605160b0c0406020f0304030b070c020a150f02060105010309020604030b0a1b0906120504031d040605030a060905010501 88
    0xc40f5a0f03011424140c4c0080009006c0c41400c2d1240441ea161502c4035054195002001072108215160080d1070322817141c16640003034148201c02c42c0b0311a02051989106602c01c50000c00301100303540e010f01039001441d060341400b80c01d11041000c044140010800c1501c240c0c0c1c00122624480241c03801e040408a0743e100b0380d8410b0042103050b2001403080c60655203541020f98503112407a1441c02414a0a0001058400d10350b040c0040d442285000d40b007621615002e80d0042620000003c0c0e6034051840040c141071140000b080100703018030320040b03d85002501122855841c0d002c111083c545880b4054005100202d00e000324aa0503c1081d000d0042441c0501001c2e4142d000180d29025038003014000101000c0418410361721b0340d10000c041c01042200800741941ca409c0544011002d22480b400324000c401c1d1030000c200c1c10301c07a840c41958551940c0e11198800d420f00a1913407081c003c0700350050354403840402c007503504000490314640701392000b04603210185040303825641e040e407048a42e2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 9345169 1250 9343919 9343937
    0x506041e060311070f050309030313030b0c03160e04060e070c020f040b030a080f07020a120605010602060105010504030303020a0201110301260303060102030307080a180305030901050601230c070e090606010807 92
    0x180400f442180d03240c81c1c11510114003010709040950a51150b204c0d10b40d81031100250384c004046400744682c046a000d519031001581d1030440b1003040344400c40b910840d45540c5885030100d070380540d01814612101030000111652120313560420280240c4000002c64101d4880d50300710316042c0c1002d004078030300740c0c0c06111032019180413940c1c50300901c600400e82480031600089544280d004e94040c640c004008a00341c0d9034408020070100030024060710045c1c2800008240107000088045c102c8206035149894035140d03840440080d00a46c22050840d502d440c10009003d641002550203400c1c00d05140c507020124084610100c504000300042541041c0208403560380c01009aa60014281c2403540050351034502c1d07d802418400002c00d8220020f1881d0b80c2131503440005584641d43c000c000708099142c110040d241d098000071f002d8000e2017200c105e2901040c10740e000d0250b00c500c0e0000c031266642c480350402e21041045801550700e80c020801c1203040e6903c00071142d0000703110305000b882 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 9346419 1250 9345169 9345191
    0x30f0a0b01050901050d0b03010207030305011509030302060403080c0c070b04080d09050a030b040f050303010303030c03060e0f04081806030103080a02010b06040311061605060f01090501080d050d0e070506041e0603 94
    0xb0501032403409905011020501c5a000d580315080042d007414010002c541d28401d070b01e0080d00074082800380105140050807104e010300c0c0a03510301c80980760140c0003040c00c0ea803285d0b0201d47d0040000c0035241900414030040c400540104a04070250280c048241e40b42e0b800c00d00040d01e40807001c0ca0740010440c0c40f1404000680b50314200c0025a60081e00740403090f80c0b40e081540140d099000c00500b548000000041030551583c0030020041842c0d40a0054903030306cbc5a00d014001c4240c032400410110900800c0008200100401d00783d019a100300b000d002a40b40007500e070b90002d030700035500d07580000fa6a00031103038280700b0031101c05d00450740603050500715202c8141d001102c41c000f50207000c00007030a080b03000403e01c100400c580d00070122601450446041d10403d0028070810166608180002c03d858034080341c14a82d407407541d540d8600b0410110401070203803110740d040a41c10f0188150118640d110358008102400510240803561054080c8102201003a548810101031030a0a4150 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 9347669 1250 9346419 9346427
    0x1a0114070c050f0406080307030e040506060a12090201120c0809010e070b0d020c03040f090f05090105130209060a030c0b0703080901050402060f0702030c0901080d020f010207020604150903060c05030f0a0b01 91
    0x15142d0540d41c1102c140c810310042401001142c12900c20b078840490320f1410164403040c2e4441e500c00a96040c06141c41c0c1d58140101409034a00000100d081406460794549082e44415060b0b401494042410310492144108484e03411400313000142d003840c2008080c0768240608440c0a042d08000c2024614110a90400307004880044c055180c00240b20205000c0810640c2c0103440782010442c001d1742d54010241c004c125510b5a03090060415000891440041c85030030300c134094a800c0000c081096508210741548000e2132242d00c5081600c0210101d0780c40144200a44103c1488c0e0355035410343d041c0900702d684020054a0303142c6c10182040010784862041c0d54109030940165a161000c51000a0800701004082c40d0407034040d0303000188505000030b000c01000c0e07040e003e0b19130348505866504c7c02e034450104040e42107441000100180030000664050441c018500030b91071946a40d0b0b0041079500d284040c0c40010004801c2c0600b511a1300b45481e08030040384420800c80c01c040002030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 9348919 1250 9347669 9347693
    0x3070c0212011103010e01090c030b010813060207080c010203090615061209010f05040c050a0b09090609040f0503070602090f060909040b060d0c080703050105060108040507030b06060d1a011407 85
    0x2402000c2103076076600c020409402c09a64406100680c984a603101d8500c80b803003140074402e40862500740052031403584e000b449106981036040c0e5800e005070365090324410201f84442c00442e0580d41c00c0002c1000701d04040003528025012400160b541d050040c03211f45454070283c20b40540640d5800c204c8016a070700403c9440c0328009815030075407991107607152801000004121444141460104810407600755000800e4907000c5a581100f0b9484004c601c5050044440c1c0940007102130001c1000e52400513030b0580c0c49441035120000c584500da03165400c0d81c002010490711150080341d500681d15102400140384402034030354a0410900e100003900c083d0000d0000307450464401c01042607030311400075182820350050f003420032050f501c03481181d4661103444196015441c200c00b02e8041d62255140c14000ca4026004125607811516909600c14010380030701d41c01181040072128403c0342d4010812040c0c0420140c810008449002614110003d18542030881c1d08001d00400982c0d1004c2d15 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 9350169 1250 9348919 9348923
    0x60402270403080c07060e07030b070f020a020d062403021807120c0207050a030305031807050a060509040b040e0a0201030506030d020a110a0314060702010c03021801080a0605040203090705120303070c 88
    0x40d505031242c50b4a803c0d54805c031036014105c14103002d41104401e03000200c80c41201d2203071101d04039a58030304c03400700e45001250440f480143c0003400e048016191440501503540d000f00c100260051400c4001035070300c0c1001d0001d40c1c040e12040401c005514000c40f541208030280e040b410520724206000a14842803000d04070b140a540d0440e4030040d40c402c10017180a000c000e403200050030b80303d0a018000da00201e90341002e1090000400058079804160281103990240003080002d040c0042039400e0f410030241103400030f903200c800403034507540c3d806680414007207000a000000e20303e0000600340c6000900d03160091340012000c908107940061040502034102c2071aa40300d1007201d000410b02e40843d8000391280149a04d408040040800c0c201c1c000c400c2a002001441030203130b01a810b070300402c441401c3c110441d00c283c54103540107100700c0754010706c20080004c4058992001500703d820589415100781c0c804081404542068040304030705440d110000c506524060000030400709500d800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 9351419 1250 9350169 9350177
    0x30906070b1302100302120105040b0f06070501020c1207020103180b0a020a120507030e070f0b0403030302090102030702030703060204060219110103090218040b0f070f091707030206030405060402270403 89
    0x80d0101054005241d03202e03034020004c1d04081008100100607400c600c0e00300240e11202c000000d01480c00780310310745803c1c90141040e101c5080030350030481d542d00403620070748265408100c1000311003c00d001d41e01d05044089c51050303ca4071103000050407a0701814040c1c114500d43c0c2c2c102c4000c5102400000d500c48015040540d035601120811602030b5140014101c041c0d003820140200c0e41e426030480c40c0560403400440340f0055a404840d585010148140141540e00b040b090022a209070020301d0a104107004580ca0080c581e40800d00d400810ba00030b1b03440e168003203400d02030960b0500040e070b6843c5a62503d50000e0050343c42c0c01c24241002400c5e10b050550380c1800d481151180d02101c1c1b99094286030031070382d40c60142000e10745c01000725901c0c401425000009182d5500074001701c0e018003e240d483e4140b4a0034441c00782c1e03201d01801d0420f5000c0c440e90500100580c0c0c4d8600441c4228403910150803d410705105001c9041c0c20003c1c0070700d030600b4018151225400701c800d8075500079010300d8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 9352525 1106 9351419 9351421
    0xb0f0705030705072003060901050a061e090903031d0303010f0b0a0c020d031101110c06070311030f0601030f0603060c0e0109121104060806010609090608030906070b 73
    0xc4080c041a0240001c5000c0381c10080c60170100403d05d00d40c264031000c4200000d190400807122007205a440d203081044070070309801a44000c0101d00180c00080460040075103000c1c1d80d601900560310390754807845d000d00d80b01c0e402c170343c1211004201c00307032480401048040d147e50007401003400c8811020340c00600c8401c0d4100b00c580c030034500e64038045004416420030480140841d800c0d4100105022010b10503c02841401c0c41380211106a980d501402d4514a0411000401540516103440000040d01c000d020840ea88982203040c44d806581d1080c00607001420b000d2203180e0168030b4043e0200803c0701a520082c1b440000d5140d4140c1c05003070800444140495024074684529a007169000043d0a481410500702c00200045403aa464201301403404a00341d004800080650f13100b0064903c1501c2a40c0c040d1102d2005903241102040c04603d09101d003440c01005041220 = true := by decide +kernel

theorem cover : BRFrame.Cov 9172669 9352525 := by
  have h0 := BRFrame.cov_init 9172669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 9172669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 9172669 ≤ n) (h2 : n < 9352525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
