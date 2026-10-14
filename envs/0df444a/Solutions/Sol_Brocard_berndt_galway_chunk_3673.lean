-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3673
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:21:04.210415+00:00
-- url     : https://prove2.me/submissions/9a364c63-38a7-46f0-9278-a9eb26a9fbea

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 660431654 ≤ n < 660611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 660432904 1250 660431654 660431687
    0x130e07020321060f10020106030b15010e130204180f0b0f01121e020a05090a15050307080a02040914060405070503010f030809060c01060e18030a08010311040f112503 73
    0x22404500c0c180c42d2804104e0440c0303001402940140c0f03054200034000c102c548400d444072285e15003c0743d150606d240c0f41520282041c1c0d284d10245d0500824001c0010014058100f001d50030071000a141203024070404051400100c046115560034a20704140c540380c00304503118081d0140b40c80b039141e8020241c4610072150260105880410900c072010042008980c20380301800096448240c035400f40040c0000a0211400c1e8111900c0d80310402c001c000200c48000840d0381040801c40440c0140c080300d50041402101601d0f00303440340880c200792001000090000c01815003800003518150068075805800752500604561600c41c0c18910400e21f48405001e80d403000850904607190102200c542c161805e000744451a0358100c0c1d03910068040301c0c9048034401991141013410008070454500c0d41c1c030359640100d142d08584514005035001c81610303070720a55681034002c000b00d05029801e4410701d1044101c1e124607141c1403080c003c120b001502e41c8903180f2403981c0c1e40042c2c0c2085401c06010100d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 660434154 1250 660432904 660432967
    0x7060e1e0409020d0602030705280807050f0412060e19080409021e03131b1401050c01140103060b19030506070806010c1e1a070e100c0602130e070203 66
    0x80f40013152502c403034410041c101c0d0f030001040180d159081340080040003010361409108031885400c2e64100ca01c0d840340d640c0059100360210f49160300c82e0026102d41c110b00038400c3c4c81c2c80d0391800b02e5640c0c046010b50403501c00b9121900c0c641056800c0c0590790300c0003403440004000020695031007829210718094401019804240fa0024500e140791102e002900100c16a43c1c13400c21420800a28000804c110340a080009141100138448000f030012680d040c05c1c000042c2501c1001984d942c2c000454411180d941c8040000d180c041c080c44c07245c000e40c000c2030300041e803688207001d200c2583c444907040804007011344c808000203400090100d071f2100c1c00e03203440560b50b160080100c42c18250303200c0280c400300b00c0c444040c0033100c4290040c03540b503100c1ca5003a907541c200b21140d0405c84038200c414601060130003880402d01d0800d42d001d1301c1031408a00d40840c20310142d1780d404040360082c000000700300b24000001d1016102d241a800d0704600a030006504140482c6514050051500126100c1041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 660435404 1250 660434154 660434171
    0x1003031d0a0306050f09120d0c050f18100327060207050a0809011d010206130219090b040b041e020c010f020c1b120d030e1e07060e1e04 60
    0x620000d200840c001401550016603908002015000669802c4540300790540890040c090008108003081d85000110741801d2810100e480100440065542485004c10810f1420382022004005480007213a515062442c08024031407410080030901c0113162502e6550030300d45071700303c800000c1c0c85911010740d051120300c1c3c030b07000c40030340141e24005009105921881d01088140d40241126404c00c0e40c41442d43d42c4001c032280d1a14010340c50082c0135030044804244159030f0140e00406040c00a4101907000c800381c0000c42e000c1440d6440001a9036450391040d2031840c09020380100d60200715014850a801152400c5291410301802078200b980042e2010150b1401e40003c0d1100e101c1940c21525151104162601d581f9070000390825682068008120307844c015504000008a10000b0680f0014201c8141c00070b00502c110f019651080740b00c1c904101154281200d18292074901520b1141e1901402034000e9054500c082e2055044110106035614443e90b0703081e51a0084801245559 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 660436654 1250 660435404 660435437
    0x150503031317071a030103110a0f0504020703020f0d0f0212031012050a06050408121f1e0305010905240603060402010302071505071107170a081e0c10050c03100303 72
    0xb0300c90307100044d50140508100c00020041e4061412680240c4030300001e14406800c0010610311030290080e02c44c00444203100c1810283c3c06000d90622a004803002651080410f500d400901c1c40d882c8005214100c6c000740c09541032100b0306052101156550660030700c1800308000304424081d900b5040c1300c4c3c41c003a5090000030083d010015405c030a0400c05402e20f400c150a540e80b004090407440f007004004140c5440004030304481c68079084041c0384000382410420040000c01080e21903e0080c0f151004c00411801e1140e0456284204001d0001c800e61001a858584000c7e040c84050703c80c0fa8200001900e002c549140d0056091a00580d034100c180f4094040f050800c90305102c240c074050820400b20b8001ca41102d0180809080b6543e00783c1c0c6e8400c3c17469003580f080b801441358120b04280c200040003100030340411404140c88d582040d001114054a6411030006000c180c3d0005003070440303001c081c0c0300302c036040310012940c60b1451030050103204690310a1702c4000d0800a00b040b400c00800f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 660437904 1250 660436654 660436663
    0xc0b0a091707060b0406080a0c180e100209040c02070617040201033c02070503070f080f030f0f010f0510110f03070c03050d08071e02030d0906150503031317 69
    0x30200744511980380d4407a420b0110090581c2040103000341c0c980340d008603035110300081003110982e04c14443c0e0180c5080134070008052151048514031580c8a1180c900800400d01990600f500000310060f03c4074030074000c00094800041d800030035500b00c007109104156109001104600b5110049180b5407150b1004800030980e512808101e9150784050801034441611031110308003c003000c08235407807001104002284150800204141d0040007040c0c0041c58450800a005004030841420103803940d04c41911603004844003040098403030204107508030b05201490240028901303441e03080742044d02180c2c0c20000035600030148864060101d441030803c0020404400089003960388440d81d910701143c81e41d40303600080b10107014040c00d5400d124441c03c2203d02c0364105540312003040700e03185030600041c3c51032603580c421800304003c4804000f5142c001c4034905031040704002a40f54001404050402864001750701c240c1041121650030b580042240d019948000c40000e0f4020b174140c0b405250 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 660439154 1250 660437904 660437933
    0x10030216060c1701090b03070b0a05121503060103230106030309140406090c020a020a0b0a0504051309080f1803060402060a05090a0509101d130f0318090c0905010c0b0a09 75
    0x1102a61002298405c0780d50010911280d05030219400240c480d494401580101c01c0e0040c0010400d022100c0c0e00c000e8a0041c6402650110383d10b00941d00c22030101c1e017021800d80091742e003220118075039050300000f8001003054014103402003041c00e06554008000002900c903405030080c1801e521042c50350303968403000062a10b40b608000d0842c07250ba002c1d445001e88603007a880717014a01c0000404600120440324620f040350b071060320701410f103010442c0f0040340a45c17005039241d444a4040004540500814050440c010310984030b16a2400b4805a40c820043c00c0d402504004180700058649000365009490b181c02c0042c0c4a00b01400480c81100d00759104a60003180b00f07050201001d284c1984500740c0d41c1141c404401c003089803101d52140c0106458910002c2030b00e41d010000b05a1100e59141c0c3c0d039100740742c0310310551800d54030300b11480003603000000f81701d40d03840c0c8004003e0740000c3c417000105002c1c2040c01c1c0381110f070380b112190301c00010400088030ba2110075141c20442d40500c035424 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 660440404 1250 660439154 660439187
    0xf0b0306040308190212070503040804080f030304110d030c0618022e09060f08190507090e0a0c0c0821070c031b0f1209090f02070210030216060c 64
    0x503249800e090060158034182ca012608100070080c0c1c55590400d4002c560400803050b1008005484442084a2a5000a0007522221428403001c501c0000910190342e030b001e5040011a16414941005400a055100c800348120000c19400000075007000381010b9080e004070000a17002e14400701074401c000c2000000354040b0301041c140903000c400501c1c0800703021400700c41c100800c162031420b42d100740c030a000b400302080380c102154006502c51001c0d1036010308882c064408a0180e031145406503141a960540420a54101446902c4000e00c0c5503601580b007039014018422952405800d10313928031005032401c0c1e000601102555070f1110b2003501d54060980da03003800d2a041800400d0040d00c490110009966013000800d121302405075814403c3d00581d031414a10079a40c0e40d40c0103441e190807181c0611041c1500000e01c01198450305940b6400188003586c2c860b41c9104003c00048542642414103105100010f01c0180404503105801e0f030144000400c1c03d0803400a403039443c200580d03002c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 660441654 1250 660440404 660440413
    0x17010e061917070306061403030d0507020a020907020606040c03061514070c0b07060506030c100810030b090127030509091003060f09030f080402060a030c1412100605130501030f0b03 80
    0x14600940018820101c03400351701c0030011a500c40940c503900c04500015075605600c01c1c082901858101c1c2d00040e040001c90040710b800c014903502045025200f12140005604840d04024450905d80140038055210345000c0204a007403e01c000c0a480d00038503410104a10034003002c155a8601048811160b0001c1080e0010343d66841c0f000d50350351140a00301c8406041c0004100f150500103404034024100901480842c90322807401c0742d85250080c01c4010003408003030000041400c0a01c01e030701903c0035000204640d4008104e501e640a86440c0108a10031241c00b84000310354010b0a680280500b202d03404596240c0510100000e0034503000503103c035240c0030b040103001003c2d60109281d44d11079210590301c0041102d054031040d1080310040c0d04a503040208520317661203940021011076150801c02c41841140e40324003500d800c10012034503481e03800c205028200d890090401c00412080c07070800e1070105452421821603002d8440d06048c180c8501c1d00c0c040c061139580104001c050701401b00c8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 660442904 1250 660441654 660441689
    0x7080d050907150c080901080402040b0a0b210c1615050a150501050304030c0204020d090816030e10051903090501020a08010f061103030f18070e010617010e0619 71
    0x42d403070b90034901c503091003c3e054442c0441128040d8103c9504160081042e1781418010b000544110100403c120303880380c0e559100f2485a40c8640c0154041d01c4910080783c0c0303c1b4030344203003070010341c800c80d62003003240110f402000410604d19080391881142d10b4180c1090100901d0041e05c0e4499160940c142070381064104515622541d00148092050f0000c0c0d071030b0b02d07a48070015103203440103035806000208910b02000c05424140c000782101d0030424000280f51401c0c3d2122000e5804c1902c1001000c0a0f58030207100303055005190fa425500c0448840441400d0307a01c000d015841a82882c0c8503112a0320368048081b8003036400072001503080b100a43d81d6000040c401000840c00740100f000172032102d0700c0450224840c05220055428a500461964031403a20b00540e50320020041d001d24180e4281c00ea81808050207035000a04091644e171643c2c0d410100d0152200e4212141185410102d0b801000030115094000340c1200741903500c607091450180303e4100c00302460b0010000307980c44800b030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 660444154 1250 660442904 660442921
    0x706060f0602100c050405130b06090d0309050f061612030605130507030509010c172d0712050708041407051e0112151a0c061302130b031207080d05 65
    0x4846400c00e2443c2000850707900041903945000d640611904141c811401c0200444031f9841400b207c1002000c0c0744c10405c014000807c1655460340803030005106000801a90038040703e1002c0840040b1040790510500201c032070102c80c03100c0d20142204103c1520111032030f010344d0005e4064100074001400d6000041c40380c5004d010180c844d00c000034680000920302d540c2c188118060000d040d5200310559000340c8055094042c0a03003544042280d494130420270000c014800340359860b0b0345451014a180a2001a04050090110703003038884c140020820401da10190f5035134401e50100d1200e82403070607100c180b40f500e072403178200c180c01c654221a450308010259003001c40c000070907030f90b42c400740f4000c580030400d0741d003036a4003000d01c480c21010502c00c3c00034852025685036484040581041000e1344417500e012420f807817a88000d01031004006c25401c004e049120b144140002c14421540847e02203607680301900884c0c25695030126022040211032402c641d10104100c1d0140540d0800d60103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 660445404 1250 660444154 660444163
    0xa020909010b03150411031b220815010b09101e02011a0f09010b031f0308040e011d04120c02030601030c0f15080f04060b030102030415150f09020706060f0602 70
    0x3442e001502402546028500d80340c00f400d805201094803043c2140c035581c40440c1030740712303080c0c5107050744205210b640c102e10106800350b2401080d500200e050541b030b02800506103c20401c0c0104421403540042c02600500021694041402d60320b40800f118000c808540f055031034958840060b086004040041e035054105808010f60440c0383d00800c01c824007007004012070303080754940100068004002d0f9410300c03005564402046102181125825288030300406000e41080781c1103030001c5000d1102c1c207942c0325840e014190200806210080a8401252001c0c000340010110300d01d01a0380344d8154450b0351f10484550f4003904a980c5540c40340b80030b000d4401c15002e401c03441c0c00240400100142550b83d000080c0c0080e40301d25603e0b840d20341d220085110024826904a42c64150407001c0740c50902c0298490f60059400c21040a540d00000055400c004000783720040c0c041c60a00103201c442c040102151041c0b4001030381d48415180a20113480b456110038500781000c10009000ca40119 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 660446654 1250 660445404 660445411
    0x190f050a140105011706040902030a020a0608010806010509070c0b15040207110414130f02010216241412130b040c08010f06150503091e1f0c170a020909010b03 70
    0x1d10000c4581c0c85000450790301682840e40910745462002082071414254000c018007400901500c2c103140454001c1100101c0703d6101030f001407560001040484020b01881e03006d8402250901a54180042c00501144805401400b040c1c0504046101d4649402550640b07090203070042d03442d2503241c00c09482d50592100818099820312401c040b80c40540e40040344224294802c8030480b40c1191203025540d0140a42203041d44208101010341c450040446030040820a8240001c802580001c2c2e6204410040782c00901c801000c03118100030400d070a80c0d030494817807103050f006943d03404c11702c0e0258952503501404107401c140c1800180700c9644002c074280c543c00b030024000e042c0c3c109400411603440d481200550502085400c008510620041d904502007208031214444266540c0060f0500700302506420350000d000c03000301c0d09048c0420741c40101d0400b4104041c800390300010701401c40785c05100300301c1080c000c0011004041342d41628120079014123081c0a660b100d080f420002c4c0e0054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 660447904 1250 660446654 660446681
    0x22a0102010b09010627090f0605120c0a0b0906160b010614031501050919080607020712050c010e010c0f0807060e031e0c031204050606100f08190f050a 67
    0x9218442c2c50309000c012541219521b80c0d442d0709024011070004aa00e080710f500700012172840e00001050191805103c1b0140d0f02a403001038200e01d00360401034010043c10100042d504000000c2e02296100144003040790505010540c0c2c2e440c2c0e0380300040b51442407103011070400c5c1c0c1802d1060309101030f500106060315410b445123034a44605020f50f01d00c07404200d824049290900f0300100265100e41c0140072f10010141c8600d0045070700c82958465000340c1c1d00644c0d0198810010030007019410402c500050110b407002d607881526589802e62208400201a03040c0201c2000c0f40505901c51030945c00c543e5000840c40000c1415494062525800a141a03d0081c2003504001c0c0581c1d0100844440c0b50140142626180280205008680011a040c0c6840c0018800f414140d4010015580300c2c61050b40a041c55241c00020406200041034000c401c000d43c040d80325280300d4200d0070868221880c42e03851020216202e01c52000381440f00301c03145aa0b401c0400340048000c243c0c0050800d030008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 660449154 1250 660447904 660447911
    0x20a11122812080115053004030e04090804050f030307081903150b070605040312020a0206090d05120106390201020d050f04060302030c040314060f06040513060507022a010201 77
    0xe4200c01c0301e103c6000c1c041d00e03407005002c0340620019801080107003003441410a8800c62001c940c80c04006103079003001454004c9102c1780811003090380c84254a142c410f01142e08003c00c41c07807a00c800107180140c1c01150f01800c95030341d244039a43e07000c0040e80c00041d0711810701507850460140154032802c2c109c00510100b4240034000200c04401c0c645041918901c3e240c0134144034243d1030382800340002400c15020b10484c81002c1206103801e000800c4829030540003080c09050000003e46006c070318040d00c50400c0b109016444590400d12082c41c110b81d01e510b01411400280d03000600344210304071044c01a00e90700000880d01181104034406d00ca8000d800f038500000303854005580e42e1040d900040d2004d20108402d000c0315010b030340a150483c2414074810300302616981e034000701c070b106560588419402241003200402c41e440c2016407204042e2030910440c2840079020402c282554001044580c4860004140d503200300140001c0040074403880c010403009001c800746400c1304042e118015400d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 660450404 1250 660449154 660449183
    0xc06050a1d0337030f0f020f040807140a030210030e03030106030b0907031a0415030b01030803011703040f031e02030607051c0b0303031605070807060615020a111228 73
    0xc603010f200c0c001c0032206108400b003034a07644210010302244080707021840c0d40e412000c0d03044c24103101400c0c06592100c54165200c1c10505000c0c40c1251990195061003604000c440081c1c6581021001300c95040c1ea448114401e030b0a0300b54094100030b070300c2440c580700100002404d150b140d0046c0500c140c00b03a45015041e1114030044007034401685040c0e89600344c40411110b80d042c103511402406040c02d2a283e91540c480da00d00075000c800303a006440c0058080010b00c00800d400540b141c1034030319040110310701450300301d2020500b440c51201910480c41c03164142d14048804480b04071841d80203050354418900400b0261140d00301a16100c120400b807111801c2000081c4203510b03215000030015415aaa082d50010801e620049920108407041c04844001480c243c0585009881003002040a038107150001010002901030002150b110752003100c0070611401c80720044550540c0c080700f0307112907001130783e1600e480300100501903044bc5125580050001003507412807803007818030008516 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 660451654 1250 660450404 660450457
    0x501050d020307060e030c0409060e06060616020114090306040f030305150117040314130614031303080603030c0a0b0402030c0a080d0528050a0f02030a0c06050a1d03 73
    0x1192420002d400d9804031205101ca1070241c086268003081c01003c988001c101071005c1403d498906d0801c40c2c40c551100200d5284c0e40302848050f0340074006072805810b0180c41c0b10f0050800810640c082d0501c01c00b480c2031004012404116404031078040c2c1201c843d4241881e20380d84207400c50360190002460040807803000c2500303182e0b40303001120507591082000716102d202c480c01d0030041c000f14248401c150410000c1751445014003503d4481c0b000c0d4622513894004087d248410350a100301c100d82d0100100001c400e8000c401085440d01450000d03510364a81010900e14407901c540c048052051a6482c000c0106d05085184a04c2c800d90640704010300c2c05040c4500c001c0745000b2000d1980180d80030030b05461181e000b40c61071011865050042050781928100d010640811100024800068400115070041d804450100329840150318080040340c00622900c10114002c0025840c0d074040741c421780554012a40c5140742c0075030754511001e004038055403070b0300003d451030400b15081c0700240e000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 660452904 1250 660451654 660451669
    0x1f0512130807030f0e011d060d0b03190302070b07030807050d0902060c37120306031707030201050f01050108070e18070903050f010608030d020a031b050a0905030601230109180906050105 82
    0x20440c0700c2c820502c07030211007c00c24580c206e03284404c27420340d50300007903c21070b94100240016100f034000c5141400e6010309009081120390382000c55010020012000001d501940030340e405003051404580382c40c403440301100a0300c80548040e50000e004107040c0419007000c9410700d200346a0400180340000f940e524800c0c00d140d8400c030440004601707025203003c40c01002034480c041c445890001030b0340c0e89a940d10380c40b070781030a50b10341207410011601c201059024460190000d481d02c5145a00358980030000703121043c018684410424151026041503e644146400016401c4400703800c1e0320303014030010701050072840259881d2051001200181e1018800d200644142c100a91f16054240c00d00001a50208a07203108040e40d80b4040d0450a000d2445805c1d540615511259203c102d00d20081111700d10f41c1000d48260031800040085111402c107a41d40100c402c081003030780920040041e640c514a541c015894500c00c8000202c4036003165114000c280e1159008018030307602d4805102c000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 660454154 1250 660452904 660452927
    0xc0c010c110703030c020d0b040303020304060b1e1002010204030b13020a050108010f09090212061905150f120304050607051c1403130c05030a060504021f0512130807030f0e01 77
    0x11500035510502c04a0305c6800c00241d039600103040d81c4441c80c402c2e5950a02c4802c11181540000c1e4040b050104000c900e02070071462460440d1116940404540a00164800700402c80d204035542150014014000c3d01074400858001c42403080500e03080e5202070811b00c9082c8200e2080c0c1d1603a03404a101d41c007815159040e0303180500000f0140342007a4154000345031800050fa40400c43c0319602512030001c1101ca4420450312080d60041c1800d040c0e00b0082c2c68025144110300624001001c0385604c0e003810180072000101e40391000b090302c441c0c00c18254411508542e07080400000d00000b030000014545e02220000070b50620810300d0480c044940e8495140c10210001c030410100b80c4003c5158012450301d802403003c424490740d40d100084c5000d40c04c0b01c040b22004e403140200402c0d440e0040343d00d0080d60481c1c1035074080722742d61240246148240d0708501840241031021416500c0c105e030020410ba5405080195110704c5401c0181400d6480600c681c00610031100c0b4865651145101809 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 660455404 1250 660454154 660454187
    0x8070b0a02031606111602011202030610050d0209041b08090d1d131508060606040302092d010b030f1003152d05060a080a0305031308120c0c010c 64
    0x3010018680207008034007280c010313280d03a600d0b600d0b60004951204000d0080308141c00d0b07600000113451001600300c5000300c42c0c02500301e1052041280d1a04c40720400d0a40c0c11007403501583c0d40343c4200340080203010702803116400924105032203003080398003408101a560244c03140ca04654030000313110382d6000340c06254000690910b820a1000724803016a4403d540c005003004a4915400c420104585a5480c1d0009045c1941d604100c4494248005500480d041e125903203058115000b20f41c9015000d002c0441c00800c40365440030840140340881c00c0d00c9060081e0070203d50f540d850100054100341c0700049403100c1e00d000310790110320301c400c0c08044a510181001407d843c14000800a140c10b080034040070f00c40700c03007484c0c82d00020740404500070103105000900382030402c01c0c04449a02d07508014000d6000c1302d0440d0110360080c0130b480e40403080035074188411400d481c0119241c001c0c4020810031402140c1880f481803ca500a01690418a0000c0001d10850f19003103540d2401c020b0002c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 660456654 1250 660455404 660455407
    0x1080f1603051b011106071206090e15101502030a030501150804030f110a050304060f050703120902040230102405091008040201021204080d03091112010608070b0a0203 74
    0x100f4500c2d000310405100c0340c05042600c0050304000d5958101601201c4900005a032500c482c0b044001e5440360a01804604104100002000d09240c0c1d440c4c400860310346551a800c8005420740010400c84800782c80001900350040300c7c4404007070341d2504152141c80100c3d003040004142100313001d500b0b1505e4172807552104007a4855850680d0810349080d5070030b00b0402d005021104d50340d030170090615414419001150741c7c9141c2a0000c0190b0400301c04101000070801c44080460b42c030000c4c088619028000000340c0012905c00100240b2541c42440722808800c081c105030384040940f142003168078011940c0c03242e6150400f40000340b04500070102004090180c10700342481200e81c003460f982040c01d141d0f142803050300010301cac8400300c08091000540300c0707020001196410300020a10004c08600c0e80d06241c2090b0a0984a0303801801034030415540700c01c002d06009480342a0301036000b000d4078075180455803806182c0a00000d0180115501c120f800014a608003002202c1c1c22004a90155 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 660457904 1250 660456654 660456673
    0x5010914151513060905030d02030405030618010f05250f05220b03040c0f090c0c02060a02010617030405030c0607081e07080a080109050a06030201020606210601080f160305 76
    0x3a5100d00b0341e00c2c0e00c0524009001070960380c00d00510210207000b95458100803e031400080600d000d481a0b02c10085400c103020400c080e8900040464104418113803242950300d8550313040d1f0041446440a80103c1d040a0911140c080c0c010304083d8007000100744884403e910315000d80700d4030300c40c0e50404000348003004a01c16600d40c0385081d5807100c01c400311003009179945003e0ba142c550000c1d1816500907804c15010030031a0340301e034800402440482c2060002107000e05001c0d140140d4203001a0040400090040289200794032904c064001501f9441100304c00030101a40c0e0b070450b005480c028410666100316614104080e500b19a41c440101d900d810b8543c2d076008428862a0500c0b00b540c10b05000440c00158a00040e166000b001d695203a0716600d00000744069690141c20702c0c03015407401000b400542d0717001c17403502c0d4010300655001440d01083c2035540b448901c0e01ea1208140d0203040008910020041042c0419651741ea00b150000540c8a451584c00d8440d0b1000030450340c01400e15 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 660459154 1250 660457904 660457909
    0x30411040902061c090c1502070e0702030a05070302160906080106050d17090d0f031701120210030b0a0f032a120f0f0501020712020709020f040504050c090607060501091415 76
    0x1c1c01002c082c42107000c2107403540d1b40e480e80095001c82e005800c442c4030024200307040f56410040c2200601d0b68421000050900000281d100c6c401e003010392041041c000f595205150082028600219603441c44c3c038030199494140c000284804c0c081d09405509103403000071585000086030b807115070445050024112a1030b0194901c0c1c0c8000a1150000d907448101004204c040c108900014065194800441503180c40f01226007416000600541744e030384109009038071134801388035001e890b47c100091041ccc900340000d00c03040d5107603002c00d00c03a010b100004406c1282c8403500c04080c03990000742d071b1030718002507031076070f0301e11700540112002c1c030010b03040c5c22010a020090030000c07503000d07440301119180c6546445080e45c1c0410b40035251610415020151554100003000007000710580071802e00c04050341c454220320903840703240d100e1512580429490803032501250900280203103800d079603010034501440502800d21880c0f010364a40700a072801c00c890102c0144c4134842c0c9240f840f940c20010003c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 660460404 1250 660459154 660459187
    0xf060105120c060708070b010509090a0b04032f07060305040314250b1503030a0e0909030f03040b1501030c052a100f150302090115210203041104090206 67
    0x10350490740c0c442c20200d0030894595100402a25002d03003031190f650203240c00d02001d00344041c5e01030781c018035204042142001c008607440c41c50a0307200360541c1c4643c4580c20225950252000c0c0b2076270000300d105030105440720842c5008440d107403030f0f025182800e44c1d4503c00d8080314030444010300402c19002104100b001c5120003070424402d102051948055066105c614220000c0011103217234803a40140316810860408424441c40100c006526000050344000c0401c00e49071140350098807140080350702c4400a100352045060348010054480c43c0074103185000c00b005035810800e280c11808641d0b05035102e030040d00c480d80300503207032541360010564641005002220807054001d40b6a021103036128070030301154158800d0804080740340b5060a0486080790350680400d1140c0008400810060b1510511141100e01340a900701a0381c01c0e803036003a201c06804800030b4010700c0d80c012038403988040742c1c1c0c041c6020f00c0c040c2c410913130021400c100344402c8400400020394401d4040c07000c4500c1c0a0f0619 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 660461654 1250 660460404 660460429
    0x5040812040312020a030e010b0d150b0a150503070f0203070c031416080601180b030d050307021510061b170d06050301050108012f040506030c161506080f060105 71
    0x1400c0e0501850703803d8110f040780c20810705880000c0e20f501006103019802d001e001001c0ca0308480100b18446540d44007100b13900321422000300c090f201c0e01084580e41c0c03818003500003803003541000c4e00034600e07001009100d54011518040421019800c4c4c0300030f18400002e03281d690713622054009109055848262340d0400021400d4091b20074118072100000d02c8050f00c1d4000e0120742d0003807413954180140c186145410310b0b00e01008600d00260f0000b6941d001a501050700514140203549441d035000c101d003031994040c06220646100d8040c0401180400300300c204a071803540d81c00c1403d801202e0407805100f20100b011f044040f0040d240142d41c10080c6c0104000e8914500001e8065554070100c3d080d50720907803080b0764a954407051400308903060b60305d19540c14815015881a410500c000b1140e90256029590007414007200140d04211460200d1302030440072141c0101408851900c0d0007034403c1000419151410302400107002e03200040c04ea12104a0784002d0302040e0300304020700540b20140e1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 660462904 1250 660461654 660461657
    0x1d0c152b0509190308060d1a04030201051807120201020c0d05150105040c050a080c040f060305090c0d0818040209040f020a030c0807020c0906211c0c0b06090411150a0201060504050408120403 84
    0x141f40d071710000e401020602d049055030107a40c45546401d00b4081d00316000205210800700c81c0c103160038850031021942070103480500c52142908400e0f0300040b4904824419215000000c0300c00940a2160018070f2002851140c4003607d07907aa2903009000c01e98601010080100d0700911021481501640500e90311806920f4100c0c02c02c0d54801488003003078030540c01080400d80d01c1c000d22603021070512006c6010b041c255144145054907545026040c810751040f04100099190641c0144d502c2e60100d801c804001042803004800c0c50804e04001e5010001d0480403134504038401c0102801a10301500c540c450b50058104428090180104001e00800036039006164440d441201100c03800c40050201320700000b004d020081c030b5000150300010010b89403c0c003200e8484280000e0107101020f50140003601d0780f501c0c5444518007a511541585016503000745050940e18465001c04040c10301986194000d101c1c803943d03401400211a003d45019009142c10098444421154106240c100d88607 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 660464154 1250 660462904 660462919
    0x3040803060d08031006170c1b0a0507172509200a080103020123042d031b1a0313080c06100303031d0c152b050919030806 54
    0x3181d880d40c400d603000321501c0d11002c02d41d02c401d2103a96400481481d1407ca10003030000b20b410290751106090141d61001c0c2440c0000081210440703000f801a1441c80b030340300e0b08646074241c403480c0c006003011800c0e10b607114511a4184017a1382c2010b105d41e2400c4007442c0c10006a056040024940c003600170f49035400d6074a8007003440c0d02c001c042c2900050482c040f0540d180c200650640c800141a81c0107407450310303194105c4004022082ca5288100c0f400c444080403030b420140b40c482070050305441e0030360002402c80d05d008000403c3c82460420808030948200c80251815110b103003649544864886031707041c1c00c409000040c10b03000b84500381404140a0400c142c01c040030015503d1800c20101c400300304103220507104104140e0107008001541c508000709a130003184066100d540c038400048024131030120206143c43e0420950300715808055021448100d228140d290f5003036580d8802503050600e86004005964080b01040300b083d038041521040329240910f440403500400c002e030401e07501c802e4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 660465404 1250 660464154 660464179
    0xf0f0c02012708030901030b031b01080612010f1a040c05090618030703260901020a0f060f0f05041205072316060e03070510050702011101110f0409061401050304080306 74
    0x45041c20302e00a082d14802507070740303901140004044e1151115001e0099000e00c24464a8404240301d9058111083ca4507425039070b02d190001e0600000c40e0312084680d4a410300880c10260a50817a0b041e07403203020030355200021003405000031140c0c11499500000c40610004d04180b501d840141441417461b0b15041c0f05000f17103c0041d0920081c1e40c012500400030114a54903503544148200c50a086403048504209410001035190304034824001c01d0f01140c02d00050810500d60303c031764500201080200300d00c1c0040d50304807004240070780b002d4030701d00b011482c12001c0314855401c441000b940b00000c0082030ba92900614007031880d4802c00e0041c0d0064001c409031256404025100600d040e076260310b04140071805043c28100d40b0340240e400b411480c3c0e031180721950080100c40581d40d080c40c18014550542140314010100c80060644000001074894511062000584160f80d40c0c0303074007041041d545400c08000203a401403664040344041c400035010903408400b4540c1f041c00500070712240030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 660466654 1250 660465404 660465467
    0xf060901140d0605042904060e0402010f02120a0c0201020f010207050c06360f0405010b16230d08010e070801151106040c0815010513050402180a06060f0f0c0201 71
    0x2102d81030703c4c2140040c90381c80c0e405400d4813190950041441036804000041c00d004c49c9120380100104045d05105103814601d03240e42c8200310703403800e200e04481c0d01da4441025400c001e040420020060740144103c0d21592480c000c10b100321503001d540603000340422b1901d0401d001564008044a80368600d001500c01080100381c0305990880010b0401e0652200d500000c006001204003100d074001e5142c04010b00108000c5030882e1135002d8200154000038006141c0111503540016240691025400356140c000c500084e040810055070707202d000c070613070700c440b01300d0001c02c0c0807540280052600001040041c3e0f8801051200d01030500e0502030804003500681c0c40c4c07140640f0221703050340414008000040060009001c0e00300100d08004c2e0b82e5162200080c40304c0c610030a0010095510b00c041421540c07201c41c00314012041141e48011403400c100c0000051840e48a4100440c100d95414520350344503810350883e92800b900c80800c030358100d80044402c13400b00798481201582c500300010072324 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 660467904 1250 660466654 660466661
    0x10510030f02010c0c0603050604051e0705091c082107080708071e0e0112110711040e1005041203141b0d1109040e03090d0f030302090d0605060f060901140d060504 72
    0x6d1489031004142e0b81005400d0004446000b001c00c10001d00050070888260095546103810011074a441034441c00c0000004400010300107407100c650020800391000c00001401408540c0c1c0d080c40307403d00801100170b181c4200780c81154420001103400703001801c018021442c09400030010315001d81c0e0f030741c0c5d155042d0b090080030640002c00304a884070744002e190307803051940702c040b03a13008018033990142407500345040c01511001443d50300f649c03074042015156035111141040700b00f01220002c201c3d0003c1d1100a18056400307481c494001d002180c07070070f4002c0c000d041d03c07009400d000184139542c4025080000004044842800c1003c001490354103929005410070f0903510740b002aa41d4540c0c0c030810007103c100e100040d80303e80080c07000034500d41d0390704200b2000e640c100300c4040c0c00b00d000b031504500900c54026850f901c600034000f400c05028507544580d120702425113030301c0100d8400104000c214002d030a48207000800e120508a665a5580083c00c1c842c510700c50082030a0380c030380d030004099 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 660469154 1250 660467904 660467909
    0xa0b091204061701051e040e0a1217090601050a0b030402030f011121010b040b0c07050307060903050c090c0a030207050a14011509110a081e01080c0a050102010510030f02010c0c 78
    0x2d1004030101c003010b030b94100f203180100402c440c020a2041d1808600e003d10300e02d0000d4038411540c8402c130798074030700c0f045c02130303500480c1e011200c40078018a04102600310356044044000491714600011501c090006841d416120000c7c581640c440c034010121240c2d5000400c00c0340c05005d5441001e2404009006600401d10346e1960291035070100c0b03500c03d0341041c480c200012030752102c0c001044282812030488044d14000808941d07520920ba07000c81c0b6068507903001680520030b0070b8002904541c030032001010740384100300b91203c030f00f42001004902102500c1179502c1c40020420241498040d0b4001c1038107a200d00191003410384035850340c5d060b44070103040070321540c0d4640c400c08a6100d64220010003030203003a40104100450040c001105002e807031028000d0240c0000426039585c54070140110415003141800b01640c0c6440c03409440c0c076010603105000d8103465101050940c018000c203846018508000001e20749103481c1c0303010043e0134510581c14003920941807408561240b030310002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 660470404 1250 660469154 660469157
    0x2011116140103060e01032a06020a030f110d03050915240102060115030c030605130615050f070b060607020612040c120f0b1005040f060302040c0507050a0b09120406 73
    0xc0c101d1500c0142801407900000107410545003c0d0706105040d035030f040140c1540e0304245800c852500d24502805469039103600d015205d04103001c0051000d600040e8500b4140c4030740c0c0c920b135603107030004803c0d145603403042c0714036080341c2091050108182c401da000c9070707100c0b54040c08c460280d22051085105d002090b102070618983c04403941c2121081c9050424200e0420301c002c01040d0725100d842071900c602a00140b00701900e40f000a103100c0d120b03800c1003004e442c0c02086403200e4040f01d00f40b80010845132080c038080c001920803150080c2e00035010f8414540348005001d18120740b42d9292a0f819000800341d81e44610284000030268032044050320070030707518608608072400c050900c1030000000d42d1105681c0b0032807421507c0042c20f0020500809640b008800c0c002d9210441c5100c048001a081280c22a00c0c0200d040220b558640103082180c0c002d840400604c140710004860354030403160041c00ca6030006192000048624400c1c070303400105002550103140c0fa010b01ca01d26940141d10240 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 660471654 1250 660470404 660470443
    0x16060306030b0609040804030308041b0810150501020706180902121014010f1b08220b0328060308040b0a110c1f050d05040302030307080c12060904020111 68
    0x1040b2048800c02d4208504541140c21482c0903519503285105602000b81040b40040c04074040210041c81480b501381138401c00c8642c0e0743c4911816980315981304441e2130007400e01c1c0380c01c110440500c01700401c0c0c83c010307030182641c80d0410000f81d0707200c81c01da0000b0909210207040002da542030b91010740b0040c2441c04108e90141098100d00640c00b80e05c2e08044030b018081d0b2880200c580c0c110b08000c2a0b0a01410440d81402050300460004050a5405082d0131000920701c204000304104042109550088000000f5190300340711510380022142d40718181002c0303140c00c3c0c001000c80440c1064451034040800c00b0741d16507545581a400a5110072030220020459103815604400001d442c228060000c20b45106010009007000c002d411140640601d00c801700c1901e14492422a00c01140f222014402e5041c149030081da290f00440340e0400240a06004c00c0e1055502130480d0340c00d400045918901d503c42500b00030400d01e014004038107001c07680208003007960b0280018900d0703410107410314 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 660472904 1250 660471654 660471659
    0x7031505011a030601051b2409072123010f20131403070306090b0a0b0d05060a02030c04091a0108280e0a080403060b1507030e1216060306 61
    0x40107202d03881c6000007502905104100c0d1a9a101d400e84594000038018150032000b641b825a0401178034900785501006000c00d0340c0007107840785144900450100d022201d0307296030754040c061130002c10220003c41d61010552080400e0381185103c05107000b070b0001184580c0900a0761307003100c0760441e030b03042980d407140900302049900740d03d100383c513003500098140b401040d01481c00461507030307003e40202e49121303900e5030a003501c0030030030034018660100041000903500e041039000480100d50a191b140c0c01c05d05810b015080a03e03a1510342944240103103056110302c403265000e504000c05d81c4581c1d0074144800100010f180c0192041e20255800c010b100303103214400103180020052a5203000c01c203114003c42010640c01e020074401c060400002135090b40c0184550508070442d001801c040340118000c802d00841d5804165003140c2103a40407810500310004180c01c2c068010054081441700403282d00740d0a05055408010607424140c407000306441c0081d00300564a07400440000b591154103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 660474154 1250 660472904 660472919
    0xc0a060e131a0409111806040e030408120c1c050a020601080601051e03070e0c04090f050c0909040c0e0106030e0c1507150b1008040221070b0a020703150501 69
    0x1e0036900c034940d41e8280000102c2403402080000b2098207940075075030b074214080a001402c0c540b6100440000d03c820001c407101008020660002d07940765110b00d240c03071025856000000211030807141d16401600b003403044142e198815801000c801110360003420200e46802040c100c40c03142560080d1100c1d6142c2c002e241b00240341c0700058003c140c480d444200140b00e10b0b6a02501100c0068100d006601c4c0c140c140d0010a04181541e4455600c00243c0e0302486010403d52000d4015170710805010400440b012040300b041c0c40003529200c20320482009821310600303003800e182d54001e00484420701b00b1599400c0a600d460000d0307009500080d6a4280072012480521075001d00392012141c0203070101c0702d55141d003100e208030800103100091007044002d01c80b4541e0440d41c40304500401d0b01c90181c030300c500060007500c0c007100c040340b1428000c6065110703004007984101840001c20300804200342444d803650310590203000c1090561003003010000000e80b400031944440c0358032030000b00710395240c0f101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 660475404 1250 660474154 660474169
    0x40b0706020703020613082d07030507031119080304020103180b09011404080d2c0c2e20061e01051512060f0607030f1101060506030c0c0c0a060e 64
    0x10701d0b241084500c60070346c00304a4003025918590381d1084040da221400020400040076107e0100862040c0820283c0a050700000544103581c001c1d00c9080d00ea008144145031200d205081ba41060a100203c1070081034426000c1c40d40244103040008403041200c030101800c0308010400c03101d0340940420484500300030301a66004005d10801c10346c450403d56945c00d00d6000d0400032400301595074002000052a0300700b0301030341c16040050b00c220810440f0080b41c0b10744130007200714003401d0a04250111000380245041c849410805642d5001501420490b00c1001c41d040d4001d80c9035120301a859521028000729009000d202c082460703401080001d5205040c05901c00351144c0301d0004040345041d00941151060002103840b45165a0b40b040007903403140300010001c2c0c0254002c1188410140c110300c840003480c3c400d89030316004080760790380b0701d0030380e62140642c540295040c004076400340380d44800340c00e8000100040c0e0384403103462004217241208039803001000a100d108454200e05003042e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 660476654 1250 660475404 660475411
    0x1b08120405011802030303060418020a0b03090d1b120320040806060603040302060a0c0536040b010909090c05060c07151b03110a050610031a07170903040b07060207030206 75
    0x2103500d9003120150002901c07408002d00b009e0003180c4602204d6100c0c1e61504006544a5004200d50131032600c0747e052846907041281c1e845000d201d041d0550240c0380c006c0001ca61041d10703c9450309000042d0b5515048103008404604003030644070903030021940f480000c071448071080341445588075403806e043d080c80c14074007502680c0941002c0042c4004a0341c0407840760703070064401001141d0511000c8089031300f4400c442400c07800c00e003600d00040304440d620303512003400004401011000160344081004a41c04910703020b0200d400e02d40100000c0d0b07015001082c0d0a8000c4840b114250350701c401040380e96210380c40c20012a08024818014281c50b00c10b101e1311003555203000030400d0780c443c3d191214400401302c00b505000c60400c2c41940080100302d00403180e40c0c040190390860902c208a50b80b030400d603000480340c1d200701c82d41c3c1081c029000403003a4442c0c0403540c1c64410a030300b184020280720300050b04604039030000700000305e00c0001180040c0101d034842e500c016558078490600134207020014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 660477904 1250 660476654 660476681
    0xd0f0501140d0f020d081801020708030d0b150c01020403200607030e041e0e0f01110414010219110f091303050d06030506040c030b10080d1b0812040501 67
    0x1030140c07001242088081120030b440348295030309a030510362011101090003d51203440c9800e12410060100040d045400c0a00b920700d0200c03408000590f107900c07250003450384590007842084c500c046950400094540301410807144080444100840b5611881510145a4000404100300301001c100040d070f00a02c8801014400103010005419110f15034000e810408031038580d42c12070f500d90384001c0c0c04010705411001894091180c440280ac50000b075a5880d001c2d04000c0c8819400c10700604c1c10314003150801ca0b10b0310342014569040000c05d551564110300c5468103c5891a40d8541e141040303d02a400c1c500754030031140d0400980030321000e481401005c00406003e094000b0403d0103240540c03500344961030380310000041d00100703625800508144500030a010600c85070a40003000c0e6400303002d8400300c6980e8025074a003483c03001e200e2007000354442841403403018880c90030001e2250318002e04071880703100ea40f0381c403003190005030304001400380c407105000401c04244079a19940f1a030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 660479154 1250 660477904 660477911
    0x40f03110f0307030c060b0402030a061a070c031b03080f031006030b090a0926070b0703270c0e0708070f080615030907090501030f11180105130f050702030d0f 70
    0x41d400316228003030460010188103000302103804202c40c5422a130450030001d030045440f46004158000940071a03c0f81401d2200c855440015002c040c801f25184560050b80244a09285030389101c036804440c01c0c0400c080f40642d502100040f040e40051966000342404152a4100400c4461380ca2149600c0842410710348008044a902e5203420346038464810b82001404080504040c0c0310022490300445204c1c0e8480d0440358940490000750200c680560280d2906964000080d02140c41b01c06c440e807035001445010f0034041c4560307401144402c1c86030b03002e02c10680c0c1e10146220010000d48001c408070b1034840070000c07210780c80a0760000c1155a494015103a0404801040e1250040941e82c1d0607a0030000003d10003801c1044150014444103500700320300e60350707424400b0040c5402542104c0c1c0d16442e9065540c0c0740741c00c07600c002440030034070f4666049074a0302c9c080200111480b0541902c042e2180f84030101200d4604c2100d100341040e4010b19503900c110790945040350800881da480c0310b491b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 660480404 1250 660479154 660479173
    0x30405010c0b06030f10090b0109150315091a0106110a03120b040204120c0e010e010501082701110301090e2d0307080a17090105070c1b0e040f0311 65
    0x240210041c1620307410011595081c0c036038501090600080c1d40140100c1c0c0b24244202006414a9014002050140c5803012031641c83c3c03d4010309030f0346e002c0c0f010043d0040040081c804140c0c8280d080404070b14408000484000541d01c1003d504607022201c01042c011000401c00d05401184102c80b000c1c1041c0030381102169541c0241c040c09070b030002400500d54400429410303880d00c2e4100d034083c281c5403036528049501c6181003155410640a05841404441d00018020641c01c02c004e0680c0d0058403500650741c0d50300304961851002c07414003400d12140314840310180c4020f00c54481090f00112407169298107100044040d2090f030809111f0396400382e080650038802080c4081181d15500240c41c0ea002e00c040411407a5002d10040546442c0d80058460021a0848010242c100c00010120141c3ea80e640e085402c032903046900c100442c88000d0120700059036207107191905c011030480e44202030b454210004950608030303000c90703524609032040304c141600001102d03071400e07821008215015 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 660481654 1250 660480404 660480407
    0x209090a050a2a0902040816030b0c030408071a0a0b0105210601020a1a0412050901020d18080d082e0303030509031b010207030315050f1e10090906060203040501 71
    0x4102002d404070003010700528440d01841458462425003c04030b00c841a03c030405040294450f00c1100c21501c0b85201e03441e0707a40c041601c000c04581d0041c481d1406651001601d0400e680000d104031006002040207000007826a4102140100b4050000e4500d140c801114000c807080100100e0620405020304800c126481c41d4080c0c5a580c080180c50050b21181c0050f4600080c92038024030300c070649002012030f644002c20952066000b0030074484003404801098505115100d078441c0141c000300001c0316100d004080300c3d00d2210092610b01c1000350703a00e40799403c0240c90840e41c40041c00503010712410307800e40210170703d507030b0044180d00c0205401a5000d8000510610000b0203140d00d1341d0025041e0310050044d2440403071b171514001c03195418101c0742c41c002e60201c101180403d01d00000c0c18140b41c43c8402810981d803000c1c03d0118159168410040c4035040010709110b0320000130302d41492900c44081210103512640c9600028501f8044900145e176034681005c0115801804100400d0303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 660482904 1250 660481654 660481663
    0x1c020310090203310605040f031202040b032202130c0810060c12020708010c090302030d030b010807110f070303030b180402060901031a0a060f12151518120209090a05 73
    0x10341d00c440d40d13400ba00355603100e150035908a98009481c041c0342400704010b110102c03614024140c845d5403011250050742815030124081c9000310b400a0b079041c00050710071051000c0000240741c625400703c441c2c0bc159400103080000755290140f410b91608040707920560001d02c51504100c00044c2e040400e82051802000003880220142c516600d104e0b001194130f00070320613072004c0d00482000b884401c01c0024090400b40301072000724000d2082d440d201000300e200b407144207485103050395246656280da00c0b0444540294041913001070103091800c1c10506020481a00110302c603403004500c0b081103030b0400c07030107111300c00030010028800001c01005030740d10022113803141e1003400c00141c1c10280c1340d0701d0110846043c4035203411002c1002c0c0803884940100c1481c54108169603548819407900b28142d040d62450416013200900d094024440854a94400d444e0300d0583d160101d0041100301240b070f0341560f00da0001000407400c0c60380c581581892500c3c1c41e4450210002005169801e9403450b0340d9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 660484154 1250 660482904 660482941
    0x450d090b040803121b031311010305090a0b0606040f091b021f020f0f12040209060d0302120304050f070303090f12020913050c060714061b0a03111c020310090203 71
    0x204003400b0000b5a81c1c0200d03003107419101080241700c5489142405404980d005070701d00540e0380c0c0380c5040c0240c00340d40c07280c040c55108180e0b000241480207126940e03100f0ba0f40d0003820056024100340300104403907041e115101c009054481000c5203101c013044103250b090703000380310003c2150404100c81078440207480000c103042113084401030399807034021850b40e814060390722241b510140000360304240403e2942464003441c021603118960751580e40401400c002c04603402009600440700b11031007000c051025650043c0600203451004c80500501790802c803182d081140031600340e05080c0550014000040080e0046034642082d0104903000221000001840c1c2881121014181c6040100c00c1c091849500d2014041d0f5440d0046c600e044105000c0c923040c40c0d84144500e00c00a600c548440c000813040b0340b42e010302c140ca080510102240903100484c5400c445074030030030580c00b0680d1450402004c040a03002c0040e2070f4200355042d103080d290141d11800f121401441400660a10880c40424 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 660485404 1250 660484154 660484177
    0xa120506160210020d0b01200c06070c030203011113060503060a09020a1701061215032a0b030a09140c010e06090d0602030f011d450d090b040803 64
    0x40c006821002c914100c1001e070310038103540c008030b074660044040780c0000b5610f50003601c1d0b803d0302c840c80394220100c080b501d469013141680b000c0031f00c82282c1818402010b0b00b03400f80112104c21038503a00441c1c00d481250030754490001d40062141034100d42c101113134001d0043d5260007403844c10302c4c4001034100c1c000742c054042c20030390024208810502500b45d04d0054600080c10076001e40e52100d0207031038020007602c0e0429880c100f0341c1c042025108100e0500540b0350081014042c289840704c61411002e22a0700640050311420700400e60400c45006940709119415000c10000c1d01490407079002030b00d03140c0704c5850360b02255610700c00b683c201c521009814030070340d1040c0d10744100a00141409003803540150086100005008484000700e09a0b8181c90050341c070b0303034400d03c07816281148514003210303080b800021041210141001c6181c04c082d09414087c41d9000e5021201c0289060010344040002681e101f0380f075100700310790803c084400400c1841212400c00c1d1408035095200c0c480d00d4031212 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 660486654 1250 660485404 660485431
    0xf0e0303182d010906060605091201051306020c0304031e12021b01030f0b06070f020a0f061d04090515100816031b080a03050301090f050121061b0206060a120506 71
    0x4540b070340c0c254043c402a030781110041c40000d94540000d415988140590b9005040c5ca80d204940e808050003036034000d07249143c901c00300d40810b46629009400c01e81d4020001d0004000c0040887c030004038001c01456a8590118001c1c040c0c940003220301043c451080a40d0404013082001c1070f481442d0000c540402e080102d5050030400e007802c010640700800325404480400c0c42c406200481d11196800d910a9400c0130001351111810341d80b40c6010710030000004d00013600c0c1300c1e10400240e500c030782003c0050b001251003249940c0707141c2031002030001074800c15408002c002c500d55040e070190001b04070100c05050703028502c03200103143c0c041e0740c04090010020005400c6046840e036425078000e18944090326082d0b001450018041d61080c42121046401d02d08601c0941006100d020b04803102d03608203d40f151321f0400391034005015203605403480c540d0f030760111074198021200810203002e50b601626040c60b00c03d0400c1441007072500300c1c030031005c640c895000009500003101604990340d4940c08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 660487904 1250 660486654 660486733
    0x1a211509060303041a12071107060e0307050a0b1809070f050702030a1a04150c0c020132091f0c03140906070804091d100f0f0e030318 59
    0x900c0c44c4103560103102030348110f400041c45d107140e10002d40064040c0764542c001c0c5440e80c1c1da00726100c0294682c00c1c190303078200400030003c036800b80601c1d201a000107030031303030784125034440005004500310741c840b41ca030960020b04030314000d940381d0f107004d80450100c42078040e41c14400001441d070203201a00700c0074800001004015580d041100d440d4031070380a00011850308940a01030403854040d102201d58040f407000d005850030960141940c1000d0580ea91720b44114150011101c6106641d480c0c1c00802060010110511500381c080e030840d2481042c81e41e450300351106114020350309035050807115585c0c0400001e069800701c502101e440c0c00d0b24141d00200c07041811105d0300e2180b03611040d4041c0d80040c50408106403440a0700448002050400c441e00d0f03a8902809510480411041590881c203030401c0700e5001071b4003620070325040c1d05001940308548418842110700c0c0040c005602d50000c010060300c01140d03440080a105c007480501b04a541480b41490324245c0308071030415061141d80314 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 660489154 1250 660487904 660487909
    0x12606010b0705010b09010311130e0a0803180106061110020414210105040308150102060603060109111b03041509080c010302070311100c0906090e0a0c02071a21150906 74
    0x701002001b04082503d5130741303140c410020304208622600071081590f00c02c100c03181d54820500b56042c032a001c5c20045025a0392913945920080898002c20502c41503c09620002d111340809004c02c0d4903040c40c4c0300540c407a03440c540040c00d100d5030002e50040005001074910340ca0f1200c210003003604c1030158980002580c00300314400003944c6e9515031a280c1004141f5078000c176410301883d00103198a6150130000012a113503041203c941e5010f034490001001401c855520901241809405082c00c0c081003510028082c01490340d84001d551000c00d00388400804800181b00061003410035040c410301e07000d501d90b101c02292003603506042e4040340b01802d01d40078039541c8040b40c102c1000d9a0841e03403050744520080c0300040d501400107000d00004903007a40503d071010151035110500c0c003c0303940c440d88420041d1420740300d91011801194400a030301c41d0b52245014031000541800e0740c4030103000d84249000e42d40d0703600a070060702d004030501194107540000c030200000d09540c04025540c40002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 660490404 1250 660489154 660489161
    0x5031e190501081603060e011103040807020a09050f130501060513020409241710050108011a0108070207032015180105040302090106030f15081f050702060f0907031505012606010b070501 82
    0x9c0c6401442c00410032041054120040408a100f280c51100003500c0713000381400c5440c1220382c4c000207210500480c103a40115100b414155100741d00203b0301545035004544202104040002000c0d0040380900c100760300c9004200c030200b800d520100c2044075446606c60350340e84ca40b1071005002581c090507208d03c001030006254510849006101c6941e59040311402811200300d44902481460f036241840d40c4221300d80ca00504041d802482c0c09c1c1c0c159143c0380c81440c0b450280c0350a07420700340600c04031a21411441d04441e05091641c40c0c4824041111814101c42d101006042040401046c00160386414400b81558840d00d400030350404180d80500040c4440c410311080b1a50058000900000c005100804004213002e4085812605550714040d60820360b11030b00507800c603800181c600080380c84410b42c8515600200c541d043d980e0748680d0200818920b10f03440261700c400042c00798440301030600c0103058410481e03401e01d00003840016150941070061800290300002d910040c03050941 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 660491654 1250 660490404 660490421
    0x3230c070303060e070c0308150a1a0702100201060303022b03020f0c0a080d0c08060904030302031e131e1a060f09240d030e0105031e190501081603060e01 68
    0x311131560340e081408015200301c00c2540f040300003c42d0b00001651341594504140071003100030b85400e20395820660342d404251242c0c0c0801400381414000807004d60740d1303410b03140701011141c1c00004105045040003801d0299107200c0400700305920602d81c03401143c2919600c0750344071501d40107031038035112110480750744a4028080424070a26004000307100141000300048281d9850400080d10340c4203003560814002ca443c540d110f01c11a00090200b0300980003580e0040211280c1042c450f08038850403103082c01651400e080c20740740a80c600030040c1d410760798402c254844000350480c841c265160302c550002700e0740202c0b5041c15030010a8103070b103c2038444085440004c003082d00a192408a843d200840400101d582c10a00504407806042402120301790a4059a600d0f003404607040040d100c41d40003a0002d41400c99a038940304030140d00d094010301405600311120142d41c8a60400415a14103803c41e849903005003c43c440400f03041c04081044941c801c40c041400c0648180a034014405003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 660492904 1250 660491654 660491669
    0xf12090a0315060e0612070905040512071b060815010e03071d0a24030b19090b04050c040c0215040507081509100209090c13080f0d03230c07030306 65
    0x1050040c4101d02c20b80c0180c0282d88070f81e0207070441650350704204240604000d0b00f415054200500a0090040640001780c1c071078010000c03950361011054000c1d045600c00441034480b0f803600000c1e21312003441c0000740c0d802441d1703e20f441e0401c3c3c00d18030b030041000101510100d05104401d140200320303482c103004000050a515040004603442c00900a41c0381c041190703015620b03440c0c0404581c0802048481411049c00c1503c40e41071203081d540c84000d13081740580070324101c1040c2c0f414181480c1720f6015900c0304511807075050915090130300d801860080c855214920650038040c880e500c569000452140044a41126020310340340e80c1071031400e11840342c0100b0700e640a04142c1c050301d2085103290034090a65801151450310a0346201000c901941040c2640b004804011a030070300900340290001101c2075034001c2c11103a80f000304074a440b0120b440c2c01d009402c813441114450b501f40c07080403401c0078101c0362520580d05d1015080c100243c004e0010305100701c045070100038503110790f01150190034007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 660494154 1250 660492904 660492923
    0x9090b0a0b0f070c0b12041515030609031205011802250f050f06010308030c1c06080c01110c03060c03090a120804061b0c02010e0102010f111b0f12090a03 68
    0x1160300b00055900040054803c01d800c400b00041120800080340d95441207880d07859025210355480c81c544404007140d001c01a51034103207400030b005486c443c03000110b114401c000b44c6070000b460b0180c0310031640c82c101c0c0f0303a45140400422122000740700f0201e05024080005a032446441c034426040d40d601c969165004c11503508000420240075202d10803240224200d80f400920307402c0302c0740c0d00c035424080180100c1041c008240440700310005041401100801d409285c0c80c140890400c40d00598042e202c10340c09024040d156580100d800c0d55000f0003500034140d10a04a8042540d131003000c0c0c0b0301c2441640000000701c40c0081400400c4a50740e0006c41c054081c03065000003040d028041d0780c00d4a14610b4032082c950010904d4056210142e0310b0340340e489101d40f0f540c00540e032011a01120320306654071140b008002c242c02d4810340c1c40b0303041c1c41a00161030b0144244130241c021b03a4002c0c0101942d100b40100c1d000d0b0030000036800324500c2d003808000d50302c0440300c0c042500c405080c3e1004141005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 660495404 1250 660494154 660494167
    0x618060d0b09011401050d0c05010c0c080f010f0b060a080f04030309170409050c04150e12011d1b0a1715010603050610020d120e211305060a09090b0a0b 67
    0x640014142807074030003000313401d039803100d04203c80807242210041054100c0c000c20442d95000e0150300160030b0103680490002c40d0f55103201c2d420300c0711400e5040102c1e5036075690b0003160122880341154522050710306a0401166041c06407580c0f4001e04141c4207800c0c4400082c1c10188240c00504203a5030040340d00006081d83c8452078420b8000e4000c02170141d040100083c081b0349284103480c103ca4800100c41103040c00d9010039100149509800c7d034001c3c0207a2004aa900024020700c0941a03105851602d64040780003076600301400c9040d185d07200128100210380540e19520317241e05030f480110120314090203d0503003525110090b6968843c0d8030381c500c000682d045e0140c0c440e034030a8800b529008414500b518040fa01e8442030860600410025025518031444660000c1c1a00b8073b46011100358141e5040705840c010400041c2840b812800910600b1071610491014018281910328a00344042d180c005498013101c0d00802490701d80d940301403282642c0b0545035000401280d04a00d40d00d61 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 660496654 1250 660495404 660495421
    0x818031b06180604094101030204051308160510060e061c051002031e0702031614010e0309030d0906020705060706021c020904060b07110409050f1615080618060d0b 72
    0x300c02200c10b040d031481c0c12903040103d0401111211190740c0e0046c81150f0b085a08001c02054080e040070403a5020b081e0403070025117176400504060041c41400d001311406460094544820124190f544034200031042003885500d4880703270b4012100b2102c1405120071101e014058281320880500759228500c0c9050001c80c55038001c60151100d000312414400d00350803d201360010544003e00141d00401504a054103030039040380c1c60724030400c03d42e110030000b03c101c10300b075075011514140c09410005c1c000324945800c0289265004441c105800c0e254a051000394442006216040c058400000ca03031041007805c0d411901100d07420240d80d611a014803158030001d4000c44120b6016515081d03001c1529010ba000755013807141c0c0b009011078001c141d0350600c000707841c03a424100ca451180740030550030752506210380ba0102c801001c824070101d244c044070300c1d402034110540c1c1c2c05000c900c0050102c1c940b190031803c061807d14418810741170b1210000710b02100c1c0754803809411011040240304802 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 660497904 1250 660496654 660496691
    0xd0509030c0109110a06020f0c0907140409050105190e130303022a07090908031f12080c010b04051e0c0c0714040e0102041215090818031b0618060409 66
    0x310802c2d6000752074246c42c0d0f80240e9071080e1070395010100358410402c20f82d480c40c001c00e019500500910308507006854481c02c81120b40c01075000042010740361801407010781407503108034100a40d425039902d03031649002a00c01802c10003030a40b052075200c00d00500107150013038040b41c0a007941803038803000740c0013058210049001707031030001c0700c0c5400751000c00102c0500070700680000d1504040c0719843c2d519411401d00851117940740609680c00d90600c00501001c1071851041007d000301026980c1e1f2413401002030171100503840b0184118905018004910313901e0781521181d20799081d440c00c0030313111500b1482035070080b010000c0180c4608000071508505819a00f11000c005440a0107083c0040c1c0030f4078240c1c000c500421010741038000700380e00800d07984000090801004200090801c03896250036003654000e040070600e4034034000840b51107041c01c21200143c458000e4504011b0408400000c42511400f40008040318400715580380e190395500c02c440007001401010000c2c44861118403486 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 660499154 1250 660497904 660497933
    0x90f0b06070f120f120f06050909030301063b030f060108070303020f0d0f0c0f050d030515041118040608032d25110a180e01020903030d0509030c0109 66
    0xc020090b99220302c1e00713001d0f1280e1103019030b0710340b07030807003048102c1c158900140142038075030032890f03143c02c40010103840d4142001d01840c0c000011b50781e25814000c020f80080624044142502d20b00004400c0d050642045120700b0000302e480c0c480c4084035940024078006071280c0801341c80c013480000082d17200340025480c003202d1003902034440c104201000f0940310a0044900000300311100303203903007040c0d1060f242094601d02c40c0181000254181e01c805203408440c500007c04a60790b902404652106043c0c0c0f055a503108403000d22424410a0340042c11f40962070240c0b0403d031441400c5042ca640f10381050025202040491307460700d100868042e8680072980e0f0b66000c0445001550340d400080004695034030a003044881b14003000c0900b90780b918492100f060320fa40d5000c0700064039949d50449412f0003000c000460140c1c0c1d0004083e2f50080b00c03a080714185143c2c1c41002a041d00c2d45010054880d4410544e00000d180d07a038050a45003540310300d9085103069440c10f2403000c00c0001c008040c199 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 660500404 1250 660499154 660499163
    0x1716021905040b01051206120715210c120e101103160c03020627030a02010c09090605090c030601020106080a03080a0605101d130c03062c01090f0b06070f 68
    0x4901c0000055516104030403e50b0a4006d5140c0040e403c1d05000e020742c088102004200c4481d076580d05040b481d000d81e40c2600d10001100c6100d030000305400c10b080b000750501c2c2c014003005034020269000e4448020421000071043d02c4040d0066512820b1040442c56104400c00303008204a07425007006035401115202c500c1401c20701c240c000c8520460030814032980c150014056901c0c5d40c1503420703001d1911210300ca4074210140e2151500e00003400a4034050010323800110704810940405080d0b142c941d0050f9003128a42101000346988a84d80c09401118100d0b5890f5652900c0c80100d005d8030383c40d0010754071807168441040425030311408180c807900485100f04800e42d15281001500443d461040c0c0000c1d0901d50b280d074a0401815006a024400401c2414031300740c0041c9038012b903802d02041c2c0c00826a00c400c100b0443c000c1c60f1080d15007040503000b2140010001403c41d01d0b00506001d90702d00c181c2c2c0c0e500500d180f5002030348a1a10f80c5030081c201034552420b80f46c00503200410100c00c44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 660501654 1250 660500404 660500411
    0x70801091a09060c0309070f0b0c0714150f0d0c0801090501151d01030b090702070e15010c03120b06070f03030b0d200307050a171207171602190504 65
    0x4801503000c4503414040c06021019090503140c4d10460a029040a05500303054000c200000911100345a4400c00420302052056220903c0d600c105040100366849100303081c2c40e04490500c640c1c0c80014280204084900841e12a000e102c20443c0364061210359000145c64036280039101c035007000c010350481d815142c090102c0c0c3c0c0c8070305450700b421208130001070202e01400d88a032141c000103030700405504410b2400250b401100c4000540c100c8051f41c00001603000400c0070301c0250b8200307000c2075001d205801c4480e443c074041c41c00201801c030b8807400503042000e0140c040c12805002d4004a03010203000701004d07114a07860400070300780d154801e4100e0100e81340c04400d804900b841c1660446040d08090802e850186042e000382074480900301c003d0740350203203074800b00303840c1d58518180003e03100c8403c20310101000424514941f0551f060b8000024005015400010b00c0c5e500303c042c814a415002c0da40c0316200c80c008079856038980e02d4020341c81a40010800e1110005298101c2100c00c100c8092 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 660502904 1250 660501654 660501683
    0x5040b032802070309050607080702030106170d090302060d021b060a0f140f0c1c0213031208010320220b040506040b030c10110601080a3804110307080109 68
    0x101c04900c10500014049548400c1c10889803400c10b0283c00c40038004d84040f07140107120f600007801c44860307422803903200f514002d00400301c22040118030030b4110706082c20803405040d13400041072401b503685034094141c1c0000b424071031480644001c520b5025994112541c03401e10b8010701c070107002e261580d5195185008048613810490034a214000c6600895808168540c6000d0603a1940220042c1c52002180c013207420041e5107d100a01900b402500c0b503030f06c2e02c2d00303615080d4801e09040b20f414040080c45001440820008010001c00f1505007903c0c0f505102424086080825031240f070484850000c0c4240300c0040032174002d000c110004035010003556513280200001c545100c41880c0d0580d004000210b500c1c00c0180f45c00c403044510b41442c240114050f0360f10303882c04600340c10031803480e00030080c40400c00180004041c4084034940004000c04031000c26142c1076110003c0bc407104544c00c4000c2000c1c0403a5001011840d00c0203001e540f040d68030341003c00c1c060300c2d1800003181e400f00d802c07801 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 660504154 1250 660502904 660502981
    0x1214120c01140c09010e0a1e0906050a050618030703080415021515060c010207020a030c031e1a18100b01180e19290103241505040b03 59
    0x4151159080410031404d08107984c0c01104c0888001c0f0780c554020f1201b00010400f0428803011106001091100503c564200701030340068900b2503015034010303c40310806100f40c1d555030003990350341101226901400b001c10f80000b031401c1911340c009450708a0004001ca003005004e8001510705005400f100c0074944409045011880c04035070981c60404c1c201460203051a00c1c00061048508900c000340c2840c2c07064001904000b5254000c51b48404180c40030010484030007000f08200c2c5106580f64000840e03500c03108030f00800300510013251040007000481d8100726112041d0000304000c1140c00146008015600401c00d0f505202d01107011201e40040b08001c00c20010281c454003040e544540d1116241041e1070300301a1002030200c3e0b16800e400c03034849411190092140003296400c02c00039001d10001d01122008000d0500f000c0039024011412004080c09004451801e4140110000d40980850b140c0c0900d82080c0291440041070100c40460800d03400c85034610408480402c0960010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 660505404 1250 660504154 660504191
    0x4270c0314070e130c1403010906030203060901090309050906061e030a0b060f0f1b01090507050f09040203070515090301051e060d0308060d060f0f09031101020f041214120c01 77
    0xf01140d01103280203209141488603040395407410303801d0510b004041030340c040140060700240c103e007511303030381d640710400c1075140401180b900024502d0003006681c0c405d0b02e0091000815000701070240448030301250b040e882c1c240445619020520045455030180348403203900e54015140d014610b410321950464a142010480e820400350b420761a02c0d00c0c0110150441715000004800199502210392000381d0f0420300030403600a02c524050f0007440d003000104100740391a0b84200307004040a88c10440180c90000b10541560011103990000070002d28407007a40e07102c0c02e40001d406508003014051181c401c9075089890b0030700300307040107038a03501c035000d0050750802060b0103000104014003164140c20a991444502030203000003041c1201ca840410b001c0d0f41c4c000c0170501d4050365031440c54060540c448250103190244c07900035403500148500e410b0b10b500841c0500d207010300b166041c050420104406030114900318605a07014038580001c10150b070f42000c81001d81c030394241951044052850369 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 660506654 1250 660505404 660505427
    0x3b100501020d080a091a01121505160809031303080309070603050f0a0b030705041109090c040b04050f0f04140114010804020108040308100b0d200405030304270c031407 74
    0x1512900d4a65503402540098024580107807000c2150413203800908040000c1c60b4084c1c000c8e15050004c0c070202d440c01c01080560000c80580c01c0d4a48018060140d4101e007034012007205a18144030962958041c80303046100b0b4500041c41b840003024000300b0001c2c12005144070780100c800b0350301c0866a840046c0d09585044441f03808503404d100000315048425800800828005411206410f494001007001c0f200813484240d83c001010411000c245072100300540c0c8408002221402c00d1f1501c11031805601840c02200d10811511100040e80e4036075000d10b012040d0020f0080c40000d84071090000c0c250000e000f2044007449030700304407040d5402143c609010744c1d4180d4801c0c1c055520354030f045400d0200034213104240980440000b034130002c4003001d0140800c00c8040060304d503491121201c543d4030f885403216203a0500b400100501d035404420f40341201c90154418a101c03040014070046208040586040f0b646440340080450707500d03900842e11080f0414001007903031950382d0155032107195003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 660507904 1250 660506654 660506657
    0x709050915010b0708040312050d05060a1827030f090611120c030d06030b1f0f0603110415080406060b07050703110f03010608060703060617013b100501020d 69
    0x66004103d0344100100a0903040e0082c5d50745410583c40b6a203404001041c400e04400003040800c403240c01c0160381c030426400507000c86072943c1071460141c1048044031800100c2401c1a07541280441301c2c10340c6121207449401026a1140000c45440c02030008540380c1c00d00b1300002e85080c4045a464082d40ca03240b1038055603c001c001d00e0300480040b40440e884840f40200600080c800c900100d80c240c09820080d51041d50103060a01d49180d6902c00c0743e10f0307c40000c50a50000e0820800c0080c1403401da010f440030303450081100100414144214030880d4400c20846038250b03290310189a000d400240564801c0b40b09100c00b5565502190250107040c00c0640513030410300c1c0070000600420040b004214000e8100d1118800c4840042c0c21a0b801ea8051846604100200402035515124410150059083c40c1c00004551b0b62891501c2505024142084441d0a2684070a5401c00a10514003103210414070410b419030074148103898054940480b800c01042c0082400c1d0300201d020020704805 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 660509154 1250 660507904 660507943
    0xa0b0111030906030c0d02070c0509060f130e03120a140c1c2012010806090303010807140105040e0c09030d210b0d120c0312060b0a0503072007090509 66
    0x10781d8104416a40081c0041c11460b40c10006c507081c08a40780041d00d2814041c88040f05c003a0701d0300c018018220302c000d106521a840840010280e6540d001802a0b001788401c4c0000f50b2240d4140f0183c6103121350a041203a17141c04c502004074107500e54201c010103171030b05d441903050342c4c44510080807140601400750040c200c03810705011500c1015485220b02007003104402403140400c035208001035001c3c0d044170107414442c10051200300c03407c018181e04441454000c0d0310319031503c4038403500c3c0c00d203a0250031801c1e0140c0c4a9059175230300c1582610081c084920705035000342800e40f2900219072098103501d001e402801c03007c2400314083d0508414810340c801691410101c203481c0e00c001030003000060740d4003e05058034440450001e60000035111400e84502d403c1c14007508014002c42080d00b03240076210b040c10420b001851303030113040d60800a074a00302103451f40c40d81d003c20340c0d15280751f41c81181c0506451058400394840042d000040304c292400c1000a51a40a102c1d91035510200024142c4400e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 660510404 1250 660509154 660509167
    0xa02010c120c0c0b0c060c0322080d1802010e01180611010f06080607090b0403020d0b15120607090b0c030307050a120501060c11040911010810120503030a0b011103 72
    0x40c003101003000c8003185484a0b51100550390405402c14603048076800403130100b642500c003a010807816030410b00e144119400c61800b51270201c0c0c250203040c40d000300d810b1011469400c004c114800d03500c13050403808090040d41400e4104001c00343c50301c1402c0e8001a111803501d85594040e0b540d0484680040540c1007425080c03150580d4250307620701605481e50341e42c1c1d40041040e601e41c030031035028025039000307000503040c448001884121940c100f4a01e0117820001040180d803031a61580e07079182d00c50825601a030b62111109502801c0608590f040701102c000762070b409001140703a82c030900040e10b0309041c0c1da031100030307445040c00750705010f620590080010554850160000d820302400500e00702c101c001c4611010816904203a0080c0003243d03c0c03000d09010040c03004200003480b0703400e507810040700c4041d8a40d11041d102c00301c0c0060500005d6004100340002141e03140000c1c0c16804203d08000c000762816554980c811101d5503a15450621000e8096218010841c0e00e031034480015801c182 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 660511654 1250 660510404 660510413
    0xf0221160e151e0d06020406021e06041b0e09070302120d140c0715020102070c090e060a0b060c0109030507050d140712021603080d050a0b01090b0315030f060907080a02010c 76
    0x5900c4805043c1401c1c010040b10954610f0504159a48121009610340e4a0500040e15104c2c0d40990709501900081c0130311904e0000043c44c5a1064100c030313114051809005800096505580000c085052040200071407008001030b801e0407680b00742d641040d00c03180c41840c20b07160012040c1100004501c0c00a40e48c0c890189000341c4400152001965605981c0f0b40c0909103031f0889045040140c0d401090802c280f1010440c81b00c020f02150209110400c9001e84954890000402035580103035210307035a00d41512014182c4040c51080300c000c003c92001d5007030141082e0002d500455041c414901d100300c1c100d01c14010b840422003070703000840c18a0384664860380c038109805846411403051112a004040c051a107240c000c40c012040b003a0b03201000214002030b140c0003006606c0ca14180514488643d1f0b00c9441c140c1294604004140c49403203003100034400c0f00380d030780b203259052040c0c2240d00c052000114205000c3e00d952403c41d80c1556a5848060f1113480300d11000c0e0110f031070350401c540843c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 660512904 1250 660511654 660511669
    0xa06110c0a121502190c050c041a0108040507030507060909051f060807020c091003031115060f03010b131407080c07060b0103140906150901030f0f0221160e15 70
    0x481c10000581005c41c070300561107501010916480003e8803030042e18082c080103105840c001e42c010360302403001c40c03a4404041e0340c40d4000348026040081d40e000040520406116010195922070300703480c4856900c1000601d001c1d518001c4d401140e141c80e010600038803070585c034044076209411054105a28103072065a212000500c00c2056019042c1c90311519610003030b15503c070700620038544a200d030a50400800c1341590151006499100401041c4013100c0e0b40c451682c4410210784000c0c3c5820940003080c094000c1c521360b683c0001064880c0c079020f50b219000b040601983d98040816603851a2040354108000d889022041004111030b00200300550051400481c044c14007141e0303100b10801910007800100c40c02103964000c80305002100c4081d1145501c860001c40340c01d0203650468840c5101c000120000401403a40c0071101c0046488400c5895407129408004810160850740d5041d11007682040d00c2684440ca160042145042c242209000d0700b40d0b11140d00d09a0070360700511054 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 660514154 1250 660512904 660512933
    0x610170103030c020a1802041d060307170f030c010b011736060f07030b04090804120c170309030105060a060806040e2e060501090806190b0a06110c0a12 67
    0x109060141c003240c0c401981080a46c0e101a0600050780c5604d000011000320300807034120b44c01c02024006001455400252500c1541c4402d01c041c0034031140701140500d81104441b10a02a000104d1411030080d41944203281301102a2503d601c0040c40340c210b002c07030085c01c0703c400c000e25615038043c0070301d06815542580340700440c0c03411403582c400700c0c181d2a00d4820201c4510500c061000100980181c0c540540401101d040d40d060110100315034556409000d0b030701418000b9076a4444035400e00144840d5a0020180d40e0789070600140300718241910f90303000240d9240650300300300105543c0c0c14561220001c41c4e040b81c0c0c4001c0c01d0340b034002c100009004000c0c02c0036001d2180d0060118010800043c0201c0c1c0510b042a50b18090140b00d1040240c50059001606014002c88200030b15080402d80c0c03a801560204030040030252807618000030f107140080c00d40c00c181440408034081e03030020400196091494119498041b818003001800c042d82d0180c20012007048000c1c0001031102040e4040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 660515404 1250 660514154 660514159
    0x3020709020f16080307030f0c0e0d020609120d140322020d0b0703060503101109280b04030302300a20010c1205060f010f110105010e0610170103030c02 67
    0x103883c141d0b4500394079101041d041568803640c00810700580581601c00e510084251107405d011f448890310000c2c06104070350008500801400a00100f1540d480e003c90782d5140c0300505c103003002c04050040703a175104041054130010035559120203840c280450709a903c0381c240000b04400d9148040305001da000200305080303030422401c00900e000100702c800030b90f00c41c605075038000030310b0751503e010945450b200640c9021954038110544009099840440714110002d50700300070b4100c0c42c030004040d85000060541c00300380045c0c60220341040150020401c9034003039404c88503122a50480e0300c3c02001e00c001000325200c100e038005554991550041c1100f0b010505101d0040340040c1001b0f40c0420158003054240e07552207041006c2203400c540681032140b4520b808100b00d20b03018000c01c491408201526050040804044080314401d00820748840c408200a10075565651403e8499032030a840403445981e40d50360681c0c0301880350018095150400c580c0c45170b01e91071500c054982402110003680c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 660516654 1250 660515404 660515407
    0x3050609060708070305040c060f120509010218060702090103030806120f103207030f050408040501030606171909080703090e010b0c0616020a020d0c15050313031d030703032a03020709020f 83
    0x2f22825214820f1a1054a00c50000341e5150108005000b41280c400c0c05d191284106100d03800142e150040c199041d00c0c0e041c100900300c1c0d1100000580001411048084c030751150742a02011f044001c11130707a100581d0120306100d00d00300010003030700982e4540342ea50201039051760003840311481e421110b82c005080d81400503010503010211401d40c2c40848065500060000d001c200951303052081a008240c07601d0f24010707000007880040928000500008846a40c0500026014801d507000c0b8200603400701182e50340d1841741c039001e40310000602c99808503481e50300000a411210b030341100ca00d122404081c04a41c0c2c3c0c0c4812680900400000010451045414007401078072900c038038101d40da01542c84540610301d400308407282c100e1118920f004210007841801501900d80e1401851140d150070001303c03c3c20170416081c250f0403d2150168580b098141c00400d140c0c2042000d441c0135211140c14640d0016422850054007510700c000300140d1010404112070035044d4064179100c610000510b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 660517904 1250 660516654 660516677
    0xb0117010e16050c0d05041d0702030d0903021221010b031303080a090209010e040b01060207120b0721090c0b03090c0d1b0303110f0a20040603050609060708070305040c060f 76
    0x5140170101035071a00410745c002024096682200c1d200401d1048134081e0f206146001d5200075120f0080782600c04402c0e03281e5513080105402072007409040090619215250080076116803800300321f4203101d008008030100081058000e10048030b1042e5541d684001d0820700d03594003150381c0e40d40107050580460b5291805001681c81940b654000d2a102c1101032030750a0504010796501d0b03060f0301c002d0640d0302c8a01d0030014403c070109001c021030381040302034601e039a43c8641640e802c02c180d10020910480d8007a505980e00d01c0f0340c01011f5150092445040303c070f4a070060302c0e030f0030310083c1c524826540c0201024070b21441c1840701e40ca500f1b8030a00c00c0301c00f15601c4021500d000181b6400803008070b00d60150300c0d58108020002c0050100000f0000c142817842a02c9085501103000102d107810381071101d07602425121500030f40021540706045801c0d51800300542500d42c0c10a5501d2400101d9a6004c1381000b44640203040c02180c2081d01f62001d0f51034030001f5900407400d0b4216070140504003c04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 660519154 1250 660517904 660517927
    0x50102040b0313050712050a150b04050705040f080c0d020405090a060e010204031103030703120e07081009030e0d081c0b0d0506060306011505040e0c0f0307030b0117010e1605 77
    0x3030b5008445a902501c2d80740e1143c60428180400f0ba04446070040346810290b021036000141d00302107a403c85911081d090449401e0b0700600f8405100d240c210f03081c0b00c103100d844c7d40e0100041c0101c95128400e41ca8030381c1c442d2821501d41606c40070f1f60b64801440d40c000303009461310354803da41202c07001080761010240d540d240d800f07844480f00c0d00340090754040b80400074071403521080ca03816402100518900312032958050006401140c00d40400ca54408a20500b820100300715401781907800211100e007031181d1101030180a44907400c8000a0038001c0e210600c0c20001d01580007143e00140079810850300c0b4110140d2100c4140340720580c55116000091961a00d91070042d207180034001030000d030314001e0281450104180d005800441d0500021441380b54094107070b60a80c1d000320a82c02c0c05480e00003c03543d0031b010310503503019810740000501201d150140e11a504041e000cbe01d51110311722140074440202c107024071030b0000c400c21032400a80301c02d200c10a81800c3c01d503503003003c2d814003001046 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 660520404 1250 660519154 660519157
    0x30102041d101a0a0e03010e0f01061a19030b04090605150306090c211204080304060207080c1509040e0303070306170105041a0c07050114040339050102040b 69
    0x80c4010940721800b4002c4001c04400350102038603080d00720010860700000a5801407048402d00350800c09924020160307540c0030340000d05070302c00320390440ba0000f0b5418841402010075205646501e041c2d401802c6402c00c0e240d090b901c000a90756081c24480f2a07140c002d602410a200d403995100381c1c1d601e0804000380441c442da501541d10b0300c401c6030703c18002c4000e042c83c110000d08030101c035070711007041d1007807540d9080c08003070b040ba4801c481080c00043d01c58030700c0d14001e0400d261140c1d03d08003003404190614000058030894000fa405c840100f541d80103203a845107041850550080781483c84021041c1d2404000e00007514041c00000f032012104541600356041034030f01ca40046d07100e035410803c050b0121001240c0081d900020001070600d81c0d07592200300062003400c1d00081007400003881031010503054904850304403009115031030058851100c13682040301c0c100c020400b0f45045001882d1140c100c07000c072120030185410004a010b8022034250703840394085400359020030020802070003150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 660521654 1250 660520404 660520439
    0x30f0703030209011d09010b070c050411030619080307170912010c0311040e0708070c05010f1b0518040209060c070e0105011e0e0105131707060f021906020903010204 73
    0x98005860f81a0203000603c0d4400032440c80c00c0c8802c103074010004507a2a070b4604c604441508050641d504010f1520410081141e4091070340140b80003443c80001800000861040400304c03903004000c01c00031402100d840c3c0f80d000c0c00c00d82c0e500a000c1c1c0d100103040710000d00225143d40c0b201b2400d080744a000034095030540143c44010386d4480084181150b010f0069090300c22a1220031030800c0e040440c40a000310008140804001031007010402c041e000301c00b500140c1c1e81060003031080700309428900f0040d050f1040940701607280d041d410340c8401e21807402d07100850026034907042c1c1d5000f20010040650481d00900c3e074006010070040309003000410000b0010150307a0490030466240200140c001e044900c2c01e070000b20032501c801c90030180d2142d2810049002420110788404a00211130030041c03c1d41c00c101c0f1080140580d44010800010f001c004a8040b039030303120503d00709450120b84903003c0b5454821108400c41021001444540103801001005000103090a99a05030490a0070060 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 660522904 1250 660521654 660521657
    0x309150603051002040b070210232701080a0b06090406090e1207031209170d05043008040213151406030606030402300d03150e010512030f0703 63
    0x15903041003044824010f0030044920040110300b424500280c1c85001e200300c04009200391484940990314a0081e080011103010034481446402d240020404807907015200b0000e482c91030407840c42400180c14042050b0802c10703904c202140d1034803150680581a02324005a10000c02c0c00b040400e40c40314070071a80146900d001c007143c4a4404032503a41083c450101c036840410003040003001081d00542e0a480012850200140c03c12490030000c0300f0160b81038034030580703880c00034404100301c03116007085000d54014005003c46030780c014004c500c9481c01c0719902808011481e0912215401680d68030f038000d0000c1c001407039011000500a084401c01e480408031681c200009006400e46001c4c0c2d4021708405075140c0b80317035062110010740b850200520003803140f190032012171a81801d017035036012418407100091211054200600e510303401042401800603141c1804150b040c146200c00b8022600c0010280d4034590808090014961344212809a030b4402000100200401c500040400601a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 660524154 1250 660522904 660522911
    0x60e030c0703021c0203120c0102040b04032001080613090510020a020f070b0315040504020105210117070e070804210512090607090603021e030a0911100c0210030915 73
    0x962040000d9030010911aa130201c3c0414240001602c0005110f500f44030061501515140c3d1411041c2c003903c610f4100c9403c05d880460000100043c8076485400d80c0041c000c4800c14400c180011904040f003182e0482e4003122101e030301d9039081103a903c015821801742c0152603050581c81d40f2442a603100c0040140141c1c4070301e188460409042c0402006050000388940c0f41d81021003491401207807248440d48540c5e910360114086a0140003111141c00c114021502c00c00c1c45500b4946074032609110300802c8929030100c0d0001a0008507940060b20910000321400e5211240d007164013000041045520700300c505c55500302641c003c0080103444c8856603c403a620813880c15105491400038010800c10341c4014207220086801c032043c1000e4404c545001615001c481c03800c18030405d030990880780b90110000600c0700c00070503030700078424590007680358002c425010428030800303c80d608024000200307481840b20051400c540c1c0e00d03004813400e02d00480c500340552600f200660707035508a0f019841e1b9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 660525404 1250 660524154 660524159
    0x304120815180121031e0909091a0108070803180d021c020312030915060423090d0f021f060b3c070813170706020114070912060e030c07 60
    0x8690f1039901d4020600500c0051880381d0f0044c0000000e41c000803c0400b00585440e1000d01c117507c0540102003034001804a041c450420106e21034040100002e01c880400000c07920314000140309045980002c0107602d421485c42c0d10740e0f40c1d254021240c540c002541e40704840035943d00204049501c42100241d800c14580d441050300d00420859400503170102403080100c08480420800c06022840e0629600c6541d54070000d001401c049840b0020049078002c0005140c0141c01d41501c64000d07031040300d4004003001e0b000d50300107012420b00700061303200302c81942c0d8410002c0c0424840c200203900100e000394940c00340410070740010811543c50322465270804900c10f540b15071603a003103841c5e24040001c614003d40d001880d100350040506045800a10040104001c0075548000c11980c128044000d80a6240540750001c41c41158015030074800c0700c007014481c404100d4022030441d110705034020728044441c03010780b02e41502900c42c9951110440c030602000d20003424024054005001c8450 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 660526654 1250 660525404 660525419
    0x160f06030b010311180111060112050c0301200a0509090a050708100f051e0307060c03120501060f0f0309020315010510050309032a0d0305070e0603041208151801 71
    0x48903001c41d54101410105142140c89880c012900e2001c1c0460029218003608001a110f07109496071030681840348000014500003202c849401592203542034030b03101501541010b003604d0868040c0801503a10f10014440c1141c440c3c001d01e20301400e4100141041c03040c00018016000864038a0021a100c2042210241d442461203920140300001404c0030740c100740304010001c000b402824041c400a030910703007551010072010030626100601312544141c80f004000c0c034024205170110302003a98044840030b01885802403d058030981d80c1c405c0003050058500303c0d00c1c80700e40710180302815614590007000d41ca050005030104007105114811952500e0180400c03010501d1090301040400e0092202c0e545d8013000310340d00154032440711060243c80c001440c1e0404140440d0306014842c41404031802038050b040f40d48030359215290150440980e005000c0139220445004103008004003d034605a402141a19001040350100f515031842c654041a014001920f6920f11240d50000420000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 660527904 1250 660526654 660526661
    0xe040605061c051003060204140f0a0608060d080705190c090b130e07050603070f1d030303060103091e1b08031204171207030902040c0e030d03020c160f0603 69
    0x201010380e04186810641900b8036401c00c400341214038440c3d12180464440e84000140d1409550080c06c02c641d01e5036104801541340c940454030341e019100200b1104200d1074440c146404848160702c810a0300c0e924442000680032144004484603c0180113083c0170480402465101c91854800080006040e0a2064910855501110999080c40180d0855442c0c0001529075550700f02001320f80461020125418505503800103900304002004114040d544848010524106030310303843c5c00d43c0605a07a0361310388814075898a030140c0c020004190700e0b5109034000751046002c0c03c400e088504801e0307000413903580b240b00160380050381007009030030101c2040f0314200200f42d0140210715121495a2010700c104001b0405800e42120080b6201016000c4c800c440d0507a00c02e0501c0610b610340054050020701c100328082c0c0c022490f2001c208880342c0030b16010070a00c40018001d01c0001e0200608a0207035220b4092950b05004081201c040d800d0210603200152844d004d82030030325400c1ca4801400c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 660529154 1250 660527904 660527909
    0x1505040f2409240c020706140d05071706040b100827150f060a0b070507030602040b18010c0308060607050106031406160513031103240a0b121b0d080304030e0406 71
    0x20744c0c41e20154118250300082c045044450608001d04c048022078190240c80c001c0e000c810503458144010090480c0e84031000c4461012508281c014036100e00c42407200b2261070145190f0001c800040c1840400c2c0940134555001072003103006071403500a550388500c02842010345809582c01000d14200003640d41800951040c10584407a0203031822600041c0351000c24404d01a404030b00080701c0d401d003c420301100e40a59000300b029551a9902d81c0700d102d0f164802e4201208440d40343c031a14829610440030041070680658130403456403528010001141e0220344111265035030340c0000000500303101280d1815041d44000b42c181841d242e8036002d00007000c000d6180401604101d050005007240302150f041d0b03034003d4030207208040720394086842c2420022283e280c0040c540741c01c40407884007094030342c41a401d0903401e02070103640c00c092216903050120030150a40040b101210074929150b130060b20044000e02d6038a0360307d03441c0c403840e41070750040e10150000313070201c26186990700349406800300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 660530404 1250 660529154 660529223
    0x210f060b040c030b10050f1209070f1d0109110403050a0f0308060a030c0909060e011b0318020f10020a0f0b040b0c071208060f030f0a1505040f2409 65
    0x201c4d0f408000208070055415440e01800404225406d000d1030400540b03141841c24049036125040c1068015030360003032407283e5805a12800004203c201d1440d0a030047c1540d41900900f040c1d0034001584060500c1400c0e06622003010b100000103c1c1c400c0051700c80c070340c0c06500000d244140301d0500428039a80100315900550110303c2c104002101307072996004031810b0300310000e010840b0345071100c05061040b05554041d803c101800c0c0c0c1381440100060440b80fa40c1d00c0c208164518114401c480c44800003010f0741c000491f8610742c10030b082007101500c0055003071050310112880ba5484086030001c24900b43c41c4440c41008010400c14815201908a22034107141d6040102d50359a03845200018910901000741210104000ea190b03080d1401c040c09000b0241d40c1c45000b101d103060b5490700043c00664946040c0041d0a000f040c0d144145c07402070750440490461901240c50318000352100355544079202d84065112500304071a84105c080040c41407940301e140c00423807008150036a680b203a0650 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 660531654 1250 660530404 660530411
    0x706050a230103110103020702041b090e06061e0d02030711060109090f110406050310020d060b0307020d05130b030c07030807020d0504060e06160c0f0b13210f060b040c03 75
    0x440414280c041d01c0d044035400701e100c005140c0755000480203409129402074100341090031a00c801200c00c1c445408010840d03840f80d41c4241d680900c1c007160507060314a10341125041000085038004541d81080705010180914681004140000c0899100711940c01c001403650030500c1e1070b4501441120300412120600b8010025191a4003070310000b01c0e48001e00c01a00b091120740070742c980b40c112a008140081c01c2da00312642000c2250042c0d400042c0a040c0285000300114050324624142c90003484541c0c005c003069454a00300341c68561000c4001030690510510003c0c000045400035880782c00021031035602e50120385005410b800b0013030400000d40d04081d844164007540801500c007161480d24000e840d0704010310210f02c03588600c8001250409810f11042c091010601802089880b50310411038a1542c2d1703800c1d82c205008030044141040302c4035004002d034081556490012480d01004141504c0340e56441d00c1e400c1c400180d00f01c40760fa480b0101c41615150611840200e80002e04090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 660532904 1250 660531654 660531701
    0x304030512030c04050405130f06050915010f050904170f1801020a02011d151306090807060903030518100e09010b1e07050102190207150c0b060f0f060706050a 70
    0x404460144d40034190040d0340d5900001e11361f821000403c40541e03040b0b008610407036030742d082500c05000c0485100c2064881d0951004a450700841e05504a4504000c0901e800d0304000c2040175400000d00700ba12040311110b212900c607c04100140040c113250301c0d42030b03540d00e103100000305060801c01e40241990008082c510250340c000f010024204000004104a140042d000910f04450074510307102801c0c02190702004940045031081c1500c4058035080001650b9413520740c0d0741c030664090740c000a10580000c00001c0c1c02080035109440f261600c807808002100041402d000721f1070b07a20000280c0101541500d4203100003942d01400e1690500380c5803201c1082440c9454102d245126035000c400110303079060203029819074200004d40601c3e50407541407418025030b00c4403603002c1c1010b041c5125181102c40b0b400342c007405006a6100c40c10071903641c1c031071040141c07104100c2d15140e0041e402e41d0345c0c15126035501c0001c01c03c85124400c0043c030350404c800e1100c00c58912504121510f220304019 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 660534154 1250 660532904 660532921
    0x6050301080316020334050301051315090f0609120509030d0c050a1a090d020118030309020a08120a030e191e02060d0c03053402010608030c030403051203 68
    0x102c52283d540e041d043c02c00c600c900d201091070100e154400c420f0003a1a240311140c1001c0030054407143c00212810000b456849104045c2250301c01d440000081c48a003480200090004404641c655800f40d00081d2003401074992011105d0010030480380550789608882c10441554142c1141000d107240080c20400c4040c080f96640c00d441e10800e042c00a000c00020410100300a01e10b441c1b948021540001d800950340c04240080a90702a2658080d00404c0268184140314407241e0516081440c0c1c01c8003c1a00d041c1c00401d8442d03001da07003111883c0d1000c24003260820107082103040c46903a040c2c2d100c0e07207844000d0440300d1100c4107075002d400c070317541c40842d020343c00710070854450b0401800d00d00070b0746500480c4d42c40224900006c2d009140440c0703401281032107a2004d44085500d031014445641e404024070420b03402c01118203011400d8207203000a00c59440c038840441c0010f0300001640b030342c031000307403070f1454100c01c000d04000d502c001001e1041100c1840600360051185028a00310300f0032160 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 660535404 1250 660534154 660534157
    0x11060105090c0c1c11060a050c030406090204021b03040501090806040510050c2101180902090a0c180806271c090314060a06050d020d0210030603140a0b01060503010803 74
    0x3880302c000401c0449280905004045441102c0c0b11a1a81182d03e4000500111001d41c1025103d004040020f00794a0b400e02606214403108400c461850381e8a641f980001d058001060782c1150742404116051152000318441e101115030045803100d10744400101800540e4000d113403660014024400001d80c005410010901650341c00301e01d50b51200c1c0b9101c220b0045a48440440701c0186c0807030050040500030078180d880f480404482d0310020740030701e0183c40e40b03403100039041010b901c00111880007590000794a28000c1c904444040700f484164078860380117410107102600b10307e00707006000d000c24078659544070300d02001e181111000c1ca902d9072114000300b1001d50104030b1000064000e4407407a000d8024541c0080c0c00232065140c5903c5958440089405094541c544400803074a441c0c012403462006500030564003414001c1c0d8240190884c1d0181000e09040d100e010110000e2540f000c4161a08610001009002e0780c5080040c10441d060f4450020300104100510003c0000310 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 660536654 1250 660535404 660535411
    0x10810020406050f220f0602120304080d0506010905040f0e0c03010c0f031a0d060f0507050c070303030f090614070215040b040f1737090303080a0603080a08071106010509 75
    0x4200c41c0e1110710300400b844800c405d540c0c1c042094458100302140d49220a0500300540e101c4d9822248500507510f60b540d90703031205503400f030001c1b60144441080d00030759030840ca51103030044c9000d050071303a40d40d0081000d54519501c000d0206450300c8448406880400c04510f10f00c100314020b010101c030450b00074040101d064401c3c01003586030303184100318130701404c4031650740100a069100d038030070581080e0b0004c21100c101f5024540c1401c0100d00d0840c8150309840d0f12400369005040800c2c03075a17405030300401c0c80c8900030542075151154000820f850f40702e40800700c40076030000c440d01c1c900b000d0300a04014000409403000b80014003840040340d4008146580701f50700010341150041d06003441005520068580700d40d98000040d03e4080d4400c2c808109040c01c142c121200d1315003a03964000b5009194010034000080d038446003003010a120b041c0d440d4101207030010005c0c40903100d4544c054903510150054020405030000d000c1ca0b00e45c4500b1045082041c00b001d810194182000034003081e2028 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 660537904 1250 660536654 660536677
    0x4140612030f030403051801080912180d050c0310020f120402040e0601080d23181507030903020f030307110f0112090507030b0c03010807360501081002040605 70
    0x4200100c0d001002202ca5011040394038a40f04d2503e4a801000c40d4490130480c0752140303070342041d11502d5006000301e5000700c4c12440940451054611090616041a0603005010040e00c074681c0d41e68442c01e01018900b4061000781807644090412b06140c45004c0c590000300c0b5104112a900a00a0006803a09100401d41d0b000d06a156400041c01500d88900404035500030700d000000d90110000d901c00310030075141c80c5d0307a5041104100501c0240e8620801c51040d0004001803624000544102150f281c40100084e00c0e0124107103030380795942c12944c1c003203004c1008808103005503c1c0200e038a034143c410860085190007801e40e200b00603580031003511400f8181608009019a02036540064a0f40d0700243c00c0100e40c0950401ca0b40d5404180b00541311100036201040b5a110a90b040700c0c186c4001f18010300d82e0364a484030744840b034440000d044d184c0e9004d200c040c50000d15a50840343ca0030100307210118495041048207400c14034121840c031415807042108018054200e0f040d1010178500c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 660539154 1250 660537904 660537919
    0x507030f03140c1e0f0a020904030c0b07020c0306240415080a050106170c0a0b030c120f070e01030c0e01121104030b1909030905040213180614041406 66
    0x407481c090700d06490045807800d07001004100f032200e2090006141c0304804900410706200c4880c4880c2944a4040b4088040b590b003001c001040542448070b14103070028424a040b2850000070340700c02618050039102240141c2107080c2070742c000d10307042051640140d00d0410204602984103850000e02c0d84074403466001c0c40d1a4042c4242d0f40012000340c1e002010004141c071181d00d440d04c0e0bc82d00800e00c1b8010100040009a0f0803440c50b03400040350085d094000c4c0c2460b01050070301d144285a03800040c00040c241900304422000c103400303091268010503d88086054506001002500039101c040c1424105490a00d4540455a02c80c4140200c80820708149521f071003510402e0b0050300e0001095018184002000000c00c02502b506a01c100c0c9507101c110022251961080180c8202440180002d04001d00038005440c043d801000d0480c800e4000c46440e81d65000d03803400d0402c1c00e04041f51520354401041103401d110911001d040e04044030100840300034401a2400c102d805090940903511 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 660540404 1250 660539154 660539183
    0x807030b0307060c021e090103020121090c060f080c0d15030b01080d1202030130060c02030a0f170c0a090b0d02180d030c082b02071e050703 62
    0xa035020410390384001d025505842d4030745034094400c003200345040f8018042d0b413841d0060904a001c80380c2c40c08100910708541646950011107900e0080d0b14203446070398413510309412840c0c0c54483c50300c589100700e1001c5211807904601030440140d403007130003040c05070010400802141c542c0448000b06a036200010b08900300d8045000300800c2500010301002c030780000411502800038450314488807503950840924128041101a40000c2c030404041c002c0000f0144228400d03400401108201c00882400e031000c2c6440d031300c0580f0100494500540c20000320910156030040f40c0e00304820700c40c1030865003034205661480c0c158100030a2a45040400f1032400403161046006100600f8900111030b11280380780d5041c0029030000d031509464041c004601d90082c1444d18405040ca034054440781030100c91629900750784c1d03008501d601600c6807603c02d404181260484851690403003080010384a80c0307540b800c08206240e51021199400802c5030501c00107400259250503640e1000e09000d4106 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 660541654 1250 660540404 660540407
    0x1b0a0b06040c2a08031e13050703030f030b03010f0603110f090c0a0302040314010209030c0111060f04020402190c05071406071712070f032409021309090807030905010206010e01060807 81
    0x3c01001000304551030000038013032480d01000201060304034985401e4042d448030103003141c25a03e2608010169040f0031000c00c040bc0c00fa104c40404500e05050104011615100107800c41c0c0d81c10020300c0046a8406051051040040000c240c0b6a01690b10314841d0420500103810b0b90001010200c4013800042c440034154440d405075401507a011985030102440d080c180d9010f900a28400341c080d10402c46051000e6100390141c41e0350118040c05040c03030380c03184e940d40c82c0009001041030b41c06c183c0070007d90040ea403040c0002c50380184c055130340c01801c049914246003070003959407180c031881140c0d0890142e15655481100c1019900c0740003503030000c40d100c1d00b0030b07414003402d0701d60f282d80440703202088401c42d080500d0440c6560715550030040c850045505018800980307403002142c0b81cde0000d090004c04502d50040856418048119012590700d940b16002e480c541030049170340c047c000c69030004154204611034080c1c0001d002801656040c50302e60303032280310140310700002c10a030100811200c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 660542904 1250 660541654 660541727
    0x31005130209070801030b0c25060b0325080f0c1201140412020d02072306070501090602040f0f141309050f0706090b030114010e03031b0a0b06040c 65
    0x60340680700c4440c43c642004080d040350713000d1009884040c0f4050002d0404094230084a40c40400081082e076040c8170180007070a0703a012500202c07661039541094000554041004011a1015240007041c8080300f051061116203607510a00c015408068031a0000e00c0200b017402800609645210440c5032603c007a034050091178070000e802e200c0020510090100500f22801250840d408460390085282800c07641c0d00124494800c01000440704480340f21203d401c40c10342558020b2045040210701c1d20f90908407181c0010844071150300103001c00404414024510052106038019102c16103001c0510304440100d07994544584000813000301c2c070389030340c1d40405400380d00981101c281800d45403005980303d46500484011a48462000403400d0400044a042c0c1d1036500003940094448001500e20303c4084001a034107000030300c0070341544540d09601c5625250a5802020020f20b24181070104a101510300d41c001d5007445218120315400580a00500e44140021040610306401070b0552 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 660544154 1250 660542904 660542941
    0x30a0b0406180230070e06120105010e010203071a0403020f03040303080402061c1a01021e150c04121208391c0504111212090a090e06040b060906031005 67
    0x2404c80008442408080d81000c40c420b00c8036132903110040c42e0742804c00105001340c401380c0d41640348030303001440303d940310710314100044106004890078240640e40b4030032054184528029010070441c10030080c164100f003a80c50402000e0017561402c3c0c11a240204030207030041010b4045d000c001101c82120190008504c031984290a007000943c1c040301c0700d48041045c801c0f4450041c80b89024035400c4410b041000d840c0c5111510090403400c12401e031135144900010080441118240400512120404c0d11000c5071407141902100c003102c503040141c00060054a9084906c89101c07440802d0f6105640042c3c404006003004408500290086000c621400c0d100c111140420040002e00000507006103000b0383c49003464036011030102d01406008034400c02241c01a0740100004d2514074080c5004102d101c41c0a4040100c080d10759481000b6101d410090801c0c95101c0c0081106210303c6145864121608964041440c207000c2c001076510b16a0345242d03410945c6d5600461142c903900d0003001c50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 660545404 1250 660544154 660544207
    0x303090406090b0f0a050f1c0c060203070501050c03100314120d0e060c0c03070201182c060103060b0d0c0203091c0c0812070b1801050c030a0b04061802 67
    0x412900c1d03521420180c4808443c9034002c20402898480515010104e50199000949607540c0702008008008030300d00d00c114500c0b07141d00d8022205001c6805803c000b40900800e400450341d0b400d55113451400c6900040c940d40c2c10f0301c1c0a20611201184021010741269007281c0d081107109407144485003020140c83d030825100c2d00c0042e800701c8040e440d800104003071032030320281c0d21955104070404505100d00e40da03003482038108001103801036000f0608000115043d00c2001c11840d1981d100c00c900050781d0000e44060229160038003408100e07000c007940e001000b86003d05c80d480ca0031004034034a01906145c85d040310340720340d03602c0c851034420000e0300d008060050183c040107200089251802844d46810f89610044d840d01080c40207000840c040d0074034140143c1e92a00307469403607100d05588090010340e05040ca488034400c1c10082405050300a264540c9443e81d80e08291300144211400781d82c00c0390103141881000c004403050711440035100402c0100140c0c1d1084068a20701c458600602d8115 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 660546654 1250 660545404 660545411
    0x120509041e060f0603090804050607050f010504150501150c03050d02091302090321070f060615030c11191115040b03060f041109010c080f07030206060a0e0405060a02030603030904 79
    0x400e407605810000881d01d8400d61000340c25100c51007102a81c6801c03d0140803c84200010002c508150004000450140e810358141e40360007628542903c200340c80076208511210742024070a00ba0b0f1180e01e0050150103a001c844551200c0040c05d00903620b4030180074081d000c6004040d01150750115140c443d00100212060f5041039280c400941007010038a00a10940d1900200304a941c1441e0b018104e0f004a51824000c09980c4c80c0541d0503500000c6800c00e4441400066081100f82d04024030811a2408940e030080c0d0300d40102584209000e1044682c0440b020190000e480c40d9000150b43d0046481011024402e0104001548040704031030702d80c00000700042c605110310041c0d8000d0108540c1d02d502040320608010a94454240b000c120344020050800598010351500c3c144911952000342060001c81040410350040001900903030040c01c200300e00c6140102240001d8200d05201c0443ca003080d4075800c0d03030342c00010a13480c105603001000c14855607040040c1c030b9440f03400600c06d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 660547904 1250 660546654 660546701
    0x140904051e10140a0615020a1104150b0c0d050405010e04330806060d0804140d064710110105010f180e0303150f0409080c1912050904 59
    0x90768802c101300c0b05241c05034540344001c5444200d034040400c1030380c025402401034000c1600c6580d201e1403a00c980b950b002daa1070002c655017800440c4400c0c02072882d049444d8442d001812610b05180c40c0e0303243c03a0100503080000703010f0742e03030803a540080740c08003502d00148070900c02d00e480340c1002c507184004294010354007a20042d00c0c3c0074910801507484e0724040c0c0c1d596171240d07814040140070040008042900c180000e201030000511000300c2060018442e4001d160706807130f8001102c805079200300d2128402d22002d8400340d02d00441e240045c148001200400e081810b0060100030100f6060303124504003200c0a100611900b1210781d02440c26000304680d5a5500d8a4442d00900c1d1140540c46081904004819000d81c0302d140204400c0501651441c0d441d10f04c800324101918050f294001d040945043c0152075903c11043c0b010b201d00c1c911aa128120102d0074a041c040e14050602005c5010101c1c1c00164401c001240032001824183e40356100d62000902800360142d903401c69036a00b8120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 660549154 1250 660547904 660547931
    0x2030d111303140f060126102c070f05040e031c05012301090306110d09050601030605220803060d050307200102070e0c070201020c09040606140904051e10 68
    0x11901942c0200007180c650034030005a03252605024400c00010f5047d043c004811041062139811560b42800c06803030807105c00c59440c0b01110103801102849010a03003c00b480300500d180c2504d01140d00c00b0081c9207945c984840ba8072100642d01890340a80d480d10310100cac10030801c100f40d0ba01c0c1481f90418032110b005402c0403070700a01c42441007440d560f129030030740c44130400c8842412104d00c6040c0e4821a409081d901c07100090002d81f8902044c07114104100701440384240300f02c03405580300d0400380c8810351440c14040156a0090a010011241c0700d2181c15180c000f000ea0310038441e4010002922a0f13600340c00100c2c011400000a0b01c030340000101d103002c1000130381c1025241d84501019003201c0755000300484e1340e0300007130080c4904540150b0100e1444601d0a02410581e403051045400d040200000300fa0804411b135407c41d1a1a140d01d401d0000302d0898000d01c10600302658402e154cc5095220749030b591100c0c818101c0002c540164100c0c0e071160600c83c642c2e030a50050018402d10300080c01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 660550404 1250 660549154 660549173
    0x905060f01050a05030f06011107030602070b09060702030a0c0f02120319030509150c0d02040f090c0c020604050603130506070c03120605090613140708041202010501030302030d111303 81
    0xa6840c4511008800800d2940c011410b484a03507855548440c1140e4030b55050420b80103010344501d0600c80d48200030100003d04000103400f46124000c050303111009071070304020198000d0300c603007506d030400f504000005900000f0f1b40e0a15150f0302e4004403a80d01030501600300d20388000065040321032010b10080c04440040103080c0d055100001404448014408904807002525012041c0d0071619a0428690345590300c20b070000500c4c010b552400c4811806002240d0182e88148101d030325840003003101c11a940f1518540405a050810400c9082e600003550381c811070158501c200e1010010540804d0140d682c0b8421552140442d202804c10f502b0140002c903188004a00040440d580703aaa5a0b9903401039604842e80034005020381e8a4134410085000158020345042035544c05c008101c03850781e540b55500a04c0141c4550304a81007606144500b4001c00011505580c10103004100103a4000103c581d6261554400074100c0c95217a0000c0542c481c115803040c1c11604068040300b84100400c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 660551654 1250 660550404 660550411
    0x10512150d141005101203050d0906051b1612020f0f010b030714031b060c190201080c03101806080a061413030903030c0f1a0105090703140c160c0905 66
    0x1080b42c0300c801980c1c0400058403812501185800c203100c800708092071b1251480703103801d4840e050441c03c040410300644100c505a05040d1072103601e40301401006a58400220208c89124107411314204400000c812909a203400c0145006a0500141040d600c01e000000c00070b0440b009448141882041d05400390840c81c2c4d01e0f510a00a104c1d000400c2c01203002d070101d0042010707014280d2000e004501c01c440102c0f58000a820030000c02810722200740c1440035415000c0002e40741c590126050000401211000301440c0c0740c4841002440f0030134140000c11000c0301d078010354000381200155142c4014040aa0041500d88294098882000540e030000d002d19403000b80c0d141c1d01956640100301162080c40409000724540700c2060001c28419044540e025016000c0c8400c3d841c0f6590780e40040500720b0030301c202d10007442030061203d40f400309010b60b04540140703000d1108034400c2d8800c501ca928003900c00422104005520710200200007144c44030540c1100d130000703072566071301300b40006080100c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 660552904 1250 660551654 660551693
    0xd06050a0b0109051f020c06030f010801110a021b0604090915050c090d0318050a090912091409090106030516060201060e010b09012d0c020306090c010512150d 70
    0x981d80c0c030354483c8440c0d00032500700515084401480d44000200e8002c0f91403100118003442d014a43d168035000020b6000713091021216401d98586401c0c1821641c006040e0700300b0b003a0030030003814215030005192035200e10b4510b401e5120881d2000003003040c130035603001c0b0280718104188a4244035203401c1910003892101c03424040c4e5602c280e12040c4500c1500301540c1c0c000400b88101c804203200b1040c0c1541d42e82c004141040041d03c50002442075440341e0705c0385030450f44400342c1004002c1c0c0c140b10030f0848a02c43c10418846410174084e1159030320f041240c607004044d0100001d0f0a1074007504040004c1d50400c05403596841c864111001054403401400f0141d070070550001001c80070100b8160484003000591401d01c40c180004684081e00c64140e03440a08080b030085c55581c5280741c0d50300c6400100d4464600d82c00140c030500d0300b08440104004019000058040b1180e60401c0803119110b80c100e40c055260354803880c0d0242d5881e0208506504810503094540c10401e25000e014881c6180 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 660554154 1250 660552904 660552911
    0x16110d030b1e0d03080c0f0f0702040c0314070f03150909020a0609030c05010c050a021315050604030b0a0c0207080d050301050406150c02010f03140c03040606120f08180d06050a 78
    0x718020006016450b8500d103800814040031180841c2c820280b10390030100106030f46180410f441010340254202240c0d5002c007400001d105804c5103028800c02003004054102400b898034882005e040315680107103050203000000c0194944540309500440c01401c04440341e010b45511401034000412442e00e04a001e01d140341c030701103446805404104210303940200503110043c141801100c0b8a01207200850b80e5201e045600030041c1c0e03a1665243d03600e51002c4000424150749401031705044035a901c0a4002c0400304000e0001c038440703500c40790703201c1c5054201048030142c5404c22483d015447e0b1081c41e5601440003048072035036028004504030303041200c4c01e004260700d800780c9100d0346241c4841c410224640c010944010350049907000610800e40c100001c4a00c14941030004110040700c0d02e4400041c00002c1100700070040c450440030b0000710074409500b41c919504c4007240d513500800900003810100b008094184080b2a422881074090840c1e010407100e494003501a00094915072000d509 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 660555404 1250 660554154 660554179
    0x50a0209090906090624060703020c041a0109120309080a03090302010215160804020112020c012306100e0301180605070e030d0509190f080d08010e0103030816110d030b 74
    0xc00261050048007000085c042c01d4440c20713174034510820540c2849002c0000449062101d581e101c014007085030013600985080c502c40010001101c030110b9032130600d05005800f0140d84d9a02c060010191480080140502603590a05403010001039011800078480c0b80c800604040d032014242040740c1c030030703000c840138426a5100b440009004450790070491081c000b0410342c00e8491005160458010304121444018004004c4203030b034003000d030340741c11a9140e104458500c0503030101171100d042e8030301000c420740c102080000c880810450451040041e05d0540345007a80e030031340c0401d6a0180004030041c20030101d2910300d0103050115000c0011402041e1485010700b00810b40c8130070003119036242c518080c80039042050300103145030350001445003000042400414030030050060711000e001403400c0b4002010081403100160030042908030b100c0c0040000903000405650410710498011204142c0458110303101181100c00c50468800d070207070741900d0b942541c4101180e46082d40c0e46184041c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 660556654 1250 660555404 660555421
    0xa020d0f030203151e090901061e0609260a0b061e1309060905010e0a1506050a0311131401080d08040f06051b0705030a0807082505040306050a020909 66
    0xc01c440c421010614500300c1d01c41032810b17003c9160a203d0980d1040300d115285004a03025520481d8a10150783d55040144100d82d003014015940166100c96030b0515070818500800226851103035480a001c030303001481c10300b81d14a4002189140321801c451081a160900b0441c232007050310400d018000134100303141080002600300010b141c0c007034085020401285d280c1d00007400310420541d0995540d4a52400044003805201c00c41d010903002054042c1150038400c03004904001500c508070710b406001c001c2a140d810a14040301d400c1021003025a00000200e03a440e203130032642000300c40c42d008000040242d5502c0f07440c180c809503000c03a9a0780040013403e69404074181d501601d030f004c05081380000907803c4d80005a00c05800801d0035250700c154a03400c1c84a802200080780c2e6904042185030146911090781681300740c0d0742c548031449003001d506000b2401d02d810350711180f030b404018000711100c0c0208100c50046038401010060f42c5010b014000007500098440e9210342c2c140d030082050131 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 660557904 1250 660556654 660556657
    0xc16120309050108060d0213050f0603071514250302010c0309023006010b0319110901140f0c032503050f160f0303050604151211150a020d0f0302 64
    0x294103846155041d414240151102c1c88010b00307140d441076041c0188070058488085075035181050364004101400c0000440e1080ba9008007014002c0c0e120220801c1840c1d45213460314446012030600600c07140c1196407160fa28840d02c5407400c280c840094108480d0700344c600d0b050500c1c42c0658020041440c5c84e02e000c03010750b14034190196014142c5050400c03000c050030a00e00c0784680301c10300e196150008860103410030500342d01c083c00a1074003204010882511008900385e001c4204ca00700311b0100d0314080342c0c40c80d00507240c1503410007810401a940e842030110440c0d040f60117811190f03454030241700f6001c0d035a0b4089510801c42d14646140b03688102c00d40c0c0920154a50701d922140d00381070620040b000507030841300e2101600400c0d1200a4042605d803000c480c491030080d07901142515122040c4002e88004181401360780140b28001c02c4460300ca070220741095540003a04828441e0a080000c20301c03a880304142c03602078000620b0803040394000404000d400c42a4543e641d40500c05c6105400f207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 660559154 1250 660557904 660557939
    0xc0901080102030c0406050c010f05010602030406032a050304020d20040608010506150d0605060d050402030c120d050c0c0a0803031608161101021b0c01090b03190509030f0c16 77
    0x91318144010b22640d07000d10080c101050800d00001100744030581c4039410781c0d000703901000142c0c000081c2804000e9050281d030351000b04000b089007056070544812b0181002d1100007804006020000c1011541c590108658160f0000c0101017400080c046031b07402000064441d038403642c030304200040d070004180101032107194001e1400c4d4002000e00101c6400d90300280f210f0344819903440d8046a103503212000b500d02c011164400150500e02441414a0208120f02131441680c03a80704085e040080090f60349600602858030b5520b4844010ba054a000c800c2c0e031186521859245010034481000000f8501c00c20290001c10309011040304156a40941070f9030f0000118528111601c026001d0465580c040e412100014035080d0b40c8440150050103401c0d200549410100c103101181d0380c0800b501c8060402900d0070b074690304280b919005c01401c030048030000140c45a00080c40302d4070910945a1541c450303d051943c0d003000a41050f11501e1403409a0b52100d010343c0c0c04108190700d13010340840c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 660560404 1250 660559154 660559171
    0x90c09010c050d0306061119080705070317070606080c0f040f14040501021818070c1a15010f050a12052a1905040510031a040f0212060103090803150607080c0c090108010203 76
    0x5162310b5904c0d4a0000d81c000d24040e29148240c070f01c004001401013070700c0cc00c032445404020351118101c3c0703480400d80d03900364081501a4409160311f01a50f6035a14140179801003110b000035108000326003000980203001006400c085180200800c0c0072040d0001c060b044d0a04040700319555003e410002100782c280e080c21203c11180d40000e07545030007980c1d49030005001e9010f1080e86000940001c1c0c1c2003c3c01c8903221710480d1400008009035030070142204900601c0c0c10000e082102010000f416020390341007a00d41c01d901d4101243e158600c01680b43c2850010a0302c1c80c4c404c0400c0c03620301e980c50780042d10000c100f07801680c08503100c0340f00e507065400b5110f000704070f01610548540b00718050302026125103040e450045030000c5d150780303c2c4540ca8040b41014005602d03000b404042e00c0110f50000c000d603041c0b5090442507000118480e04a9901a00083c8005007107041d510104d1458014900d00401d88000001c0d403400d14880002c50088961007256030440d2070380c07550101400c0c4d0001303407131800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 660561654 1250 660560404 660560443
    0x10204230d03050a0f0207050a1203020129010e0d120c140105010b070b040204060b04080708070f060e01050f0d0207060506030f0a030f1d030307111e090c09010c050d03060611 77
    0x2050034845c480442c2c41d0384280c030459180c1038403400001d81e060a80d0744404000c2c800c0034000d6080640a000e107440704264001c40000000ca030480300418065081d90781030401c103403e040a801035448998154241d030300240503181c101c0e00d1200c0501076000303c0d10705480e01e6030b421a6011403c0014090103060390781840d08103007041d800d541c0e0305407441c00c00780080768069144e04020400c104c80502400092080340d00030041185004d43c000d0405009402801e1003064088007444803030341220024222550a1810399512201c14aa0400f1070050010005040c1d000168078001c0c881960440c500409084040e9448001201c0c101982d03030900b004028046001a40781034503090089840a0060006146041c442101100003034119070142d00e089420303203542403580000d41440c407260030302c2d40c412000c0e403201d00221000007022468000c2c99900c1030200000d1680069105d4230720b09506070b034070004640103042080805805040315001c1d0384001103c107004058040b100051460911000c500340a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 660562904 1250 660561654 660561667
    0x1c0522031205040f050a03031b1805010c1a0c04050a0506120a0507030e3a0c1101030b0613180b220b0907090806010b0406020627010204230d0305 64
    0x1c0604001401500c2c1c00c0c0c80e480611011a505003c003100451007641c00154000b5841140340d1991030502c1c41004201310ba560765034805a00300d08203420384030b090901e40c1c8050070614101e114582000114404490018244071301001e180c4040d000b0b80708104d03505043c094403803050090074001c004250381d014440d040880c50b03092040d400950005400c1c600071801c0342802407841e107440c0c2e00c41c08548404400307241140b45484000007030042000c4608681090101c2108000c014080703158014158101c84000c078007490b0700a80c00113000e4000a0196525195201201204070b4824444c00c50704500c8070380010000c900c00e00c241c1d1058900144910000e901e426800300c14503506201d0181500e6541440d14859911161a0741c4036400c6540c07401007041c102005181028010307804002e44500504c401c1c040c0e603030041152644030520138280702c040d141c041e041007556441300958030030f99440010040348944031200c0e58505020119016a0026098000c4c0a05005800000b60000ea802c0c03050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 660564154 1250 660562904 660562937
    0x130b030c0d14011e0c090e1501090e0403020a03030501090204060210020913020f040f12021f120203010b090a0821070f0507140108060427020103021c052203 69
    0x590340594050000150b02c2c20008020328219081030603a0700300c241e0900d440510aa805008501a0021340c0c94803440d42031808000ca01c204c08003400c3c4c0425190b81c0b02c15030307490fa44030310b0140005000859851505e0b04140c2800b0391a10854042500020b00b42000031414103440c0c0203c60880d400f41c4d004218400040c1244802504111046e80d40038403140030310511154280040d1541c11100300035690344c0d42c50080358500a8170b03141c9c0715920310700800e0420b00150b0f40d080344a035041c0312401e0051921101020040740c02c1a180702c0f020301068400701c000710308815006e02801c400342049d101c00d50314640310700a10f55505040110070b501c0c0c1e100794107000c0064550710040c02481b885401d19102640c103641c0c0d00e60422910b80c000d8138210502011140e41d81d030384548141d812007000e5030100300301c0405140038501075000c00050445034484000c002c0071a44681d0444a581d124040580544105c4407602400380c10240c885071407824481e0183c80700d0300b0701c801c2401c0031542c2c140c50756131008240028 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 660565404 1250 660564154 660564169
    0x70e041a101d03010606020f0709060b0708071509051c08010b1911010f020d0f29031005090a14032b1e060608100e060925080402130b030c 61
    0x40750070000b60540342540389840902544000e01500d8000e0601149a8588240b600240e030303100d20100c40c01c0040c1000100810002c0740d6000380c0090344550f441c000c50401d43d0400109424150280c4e140c000308000713012000c16802c00a4001c0e187c0d1070a8420005c00c1207640b03100a000e0300d00c140f001006441340c620582c1402405030401d1307003402185601021610780c211840c1c204c1001120350001601d114840d0356118a0560102c43c0d40104010b56022084145244201245407100d40300c030b0045045c26641042034149420403000c003401245401700595032166011002100c450304a03284c0d400c0da504020041e2900c3e142940b001c141080b10454492003d81200401058140e696a451500504206400911000842401213600e9160410040c20904001c1a261260001d40e009120720582d44002c244c00000c100d400750361945032100c1c1d070f400b403085105004400314403610001780242c0c0c100500500c128021500350424007244066442a52a54401d040d490742140076100807510f803424 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 660566654 1250 660565404 660565427
    0x302090c0408120a021e070e0a1e09031b150c0215040b07090302090a02092407030c0804050307080a030f021519090506010603020403021320030a14070e041a10 70
    0x170480c1c0403601140148140108940c29040c5a07403c07404042c01128101121a50049207000082001c2c07a0074161101000c086841303402c41071a110740454003414403804a204003c0c03c2c0104038a0212a146000d501e0401d9255800e09001c0c209034590750510b00108100c81d840d04113146070601a6902e646540700d4090040031030040c17200500c00440540ca031b60707807418400d074800500140c0e0360312036400b00100c2c0760b48046904408800101d4010440d000c0070290750946130300d81010080d07125280b40c9800c0e94000c6800c102e40510030080001100c141c0054802802ea00949503003101a4114604036201d0a180e844083d50003209004203902c1400070030380302070310400c481c00001d0345545503450b2424010300380d0100e00001c2c0c000ca4240b05602d08011000c001c03c40e0381c4c0c01000066201d00d516058420f07210181c58218a0102c0003400d104900d410805d43c00d0b540c00092f40c03662802000103010078850301881070046190140455840b4584081c5988100c002000c0000704103030392100721240203218 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 660567904 1250 660566654 660566657
    0x7030204090207030504090506150409021e070302010b180906061309151a270402180103030201051b1e0c032a120a050f130b0706060302090c0408120a 66
    0x200400146609540b020b000c5440c440d542c0c266803245094001c40541e040905072500c10301c5d43c8554102c001100c00211000ca44480c480581c0314141b40250741d0f8504820948414101000504a010181e0661110a00d20402c444866240c1034401400e060400c04030342c2404150b00c80c0740820780d20700e046214050071a140041c0441c400c2040c1c1d603008010300d0701403000e0a00350340301c060320100914005a06c00f10004181e40010b85013003002c82c80794160300d0398810460704d03544c00e070042415034413200e1642e20303225030400100350076507540d00c0c00900030f080880c1e24503400040101101468030a40c8101c0e415203144202d001d140342e0800c10352082d6a4004110800343c3d200400080e80d400420190500c02850080300840301c407104444010b080c1481310600c140b04003010080800003540010591b0040003044c0303919508c821070303041c492446010a400128501001140765000c0003c00e42000058034401e13504d501c1c09440d4142040800d0003540075007500d980000521014201c00c90002c0c01c0e02d00c81c207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 660569154 1250 660567904 660567907
    0x50f0904090507150c05060f130f051612021305151806090604050103051b19080105070f0e0d111f0513051c02040f0e010509070f090b0a0b03070302 65
    0x904006011101101d104950541120100b00021040350314040d401c3d010358200040b0440050b40c40d00d445101c024944842c030190000031488564800e4031110030030398060301e40801112a401c05940e03c0c0d14000c0c1041e240315000a0200c0d21100718480714490580c09481c071680c2000c0c1a18034070103031100504258201c07145001480e42d80c1c2e2007100003600b8181c0032110130000d09000061041034400101010f0007a07041000400008000180d808d12aa030030580c0c052009005c040040d03078030b44e40c0071041c25003942c01c00d04c00700b40c103c01136000e240205500d031101049000084070a0b20b41c005002560341e40180c1d909030080105a40f02c1e486121110001c02080c1200d00850012507c90070101c0c0c00400508045616080d602d0504058009130034100c43c00c003804109035210b070b02d8128207518002d010300d484100d0602d1041d00d0340c000c08107000540009100030700e01080900d0b9200702510861643c0e010807480051113454522620801182c007405820300541044030100c160341c00540381c0010540e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 660570404 1250 660569154 660569167
    0x907030203330103050f040c050d0501090b070305070e0d0c050f13021818040803180c0901060e040609020c0a08070c0e040b04110105090d02010f0309050303011719080901050f 77
    0x940280d8008503000d110309070000b00d940c4000102200c5008158601154600c0148000f04483c401414212841103a420803000340301d242c81805042410801404a04d1030014032601d10f03016040783c2e100b19040e640380c1c0f80c01e100701d80400c092982142c60140040c05024424480c0e030400c0c00792040310040140151400244400402c0300300da101e1203607284504c81c0701a410b0f00700e1034050780035411a2103000039a00070f070030300782c9501ca02c1d440007400c0761090102b9608610b03800d031003c2c000040113000048c81a03a6640e92240d01a0108000d402e2042c0310f540351107004101c00105200b5103c0e601c1e01c83d00142680b021310b5680c1c2106500842040d07890b540144000079840c011030a483d40714601c2902d03000c3d00c5041a01d004071000c2a100e021505000007401002140d8a840e4520001d998091800d5100c15812503429030044c48680409881d034000080042524516400b40c03900304c040c1c0740110703009e5103c4541d02070350701000300030002e240480400c00400d0540c031400161803072a00000c9070915085 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 660571654 1250 660570404 660570451
    0x22404081005090c032b0c080307120506040606091a070506100906120f02012f010e15060d1b0b04181b051b0c1504030c0605090907030203 61
    0x2021141d464105448100308840c18400b4010312072000429401000c07406010360f4007000c1c0c4000c2c45501e0407000501684c0002d0588261a28019290414046c640c0e0b410324140041c081265404900381131424080400c046081c24881c641c107c0ba034545d074101040342040c0074440d800308400404080c04070300f4440710000c540d0610000d406820041d400e01c001030310b0880d0f00415103001e40d021028020485500402050241c0071000e01d0030b1b8246418000d0508200040c054a8070701d12078031280d1516059840040c0308154084c2d0030106400c41140d005e0000341052640356482213900940043c001590040010f0b9070030000701d80401e40c50500c64100e92103950007145604698001c1380741000304210044011240d201d591200b07050007101808212006e00007600301c1c4103030803140201e118100c0d400c00c0c07092018003401008900050003103446020f041c10301c107803a4001e0701003a5102100f070740000500c1e90241302120981540913020240c00c0d0340d201da007503000350401440a02c404418009006410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 660572904 1250 660571654 660571663
    0xa052b0804171201030b1b0f0a021c020a0611160308040302010f110304030809151b0f0a0905120609100c1e03020c0d0302040b12220809091302240408 66
    0x18445803d00b009601d18207001641400c003034002d401142070792800808052500301200e80244001c4240c1b9070f50828600d00300c2c41e0020842d814003c803c04210f9090840ba8045000181d803070040364240080d40d01c6c6803803003030b4521420001a1408414100c8100040e000d0748200d40d00070301034000081d411003529500c9080d2050003400c200d800c5400000c220401d500403450b141c2041d0004014041c000d15a0b880200300400030700780305224001021803180f81d903c20380440d24210b00355810182c9a600c07507103010307241101e01c3c011284180c90b03210760400300c444c0000d207007407045c0382c81d00042113042501c250050041242c0c0d50503200b008200c288640401c065284c0b61183e07955030755401603640400d6007456040c6511f00180c042054010401049040c0001007521005051003001c91010b481d08000e84468400b0618084013103c1c201030000b0a2059042c0502005e034001c0d605010540c0e5130303840043c821901d040d0000d40c07184101d00003a0411a000b8080d500303c4100d10300c02440c141e258425907240 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 660574154 1250 660572904 660572917
    0x90c0b071a2d090a08281706150c0303090d030605040603020108040209150909010c0f09180c020c120a020f0907080a0b0307050604080a052b080417 65
    0x30784000e04440c8001c828100c074a5440382002241c42c06a1030010400d0070030744a140b088200404848001c190140d03030a20540d56250781c030407440f590301d1146044070005001e01e1801c00410307000f45401d8003d00d602448200c074682c60300014106150f59418104600845020780d0180000802c0c0070041c100c1e14108000c50181090000420940404800050556120350407550059051140c1080140d801100c0d9540069045902d200e0300c0c0d0392107a10b20a00340103003142c00d91000425062001e1440103600c4100c42e4070031540c8018405407026000d946529440c4035004001c1980060800b00c100309500c40500160307148191039900d11a100060400b4210754603c09090700f14910385421880c22a0302540403c0007078841d140c81d441c04000290040c400203000101407500c4c0c0401c032030740c0e075418801e02c405000010039003030b110381d04d03001130130350341c00c031000f411503541c801d180d00a00700e80c01152000e41c2500117980c0000344c040c0405800c851081000d84200c80314281841644209202e10f00601003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 660575404 1250 660574154 660574163
    0x1e0911180f090705031509030c0a0b0405150c0306010e0102250e161710080304090c031401151112040305010b03100b0616141e0f03090a0504090c0b07 66
    0x2400d200c20203080a5501402c000e6080c2d02c10481009191000700300c09031410807422052134140d881c24100c0742540b10b080407440550058041000c100520400f413680203a000342c003207500a24be0322042c4220384030196504c51840b0f40900000706030758820301400401250610548411540c1140440a0500c2da1403201b5003041c4038000a0110010860115500c5901c01d050217482907640900988505181070705600d000701c1840004403004d55900343c40c00245004412a42d070b565071144000c0041c5400c4698500090500300c00d044100005880d0703a0503101114a48940c1c0070702e411040d00c060028100480c0c55000314580c1d001e89039114005032000354000c90021500b14902c1c800c1604011949440c410118a00700341e409541c0c07111000e80d010348030342e8a010141c80c4844e04100e9080e4540840c00b03041d5208801100400e030b5400c010707004070303000300004481030383c2c144061064990240344002c503003003d4003400401c0303540740c01c2c0c10a00803030b80501c0c10034401c16155490300850703070300098090f42c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 660576654 1250 660575404 660575449
    0x23041407021f021608070c0f060f030606180b0a0e03070801020d0b031504020402090d0b0a0c02010b1005220803040b090a0b12061018061d041e0911 65
    0xc0944034000b9000d1811402d50b20304602d40a5481000c020141680401405418002c140041080680144400902024010b1605035a40e4200003030042c1ca000d40002c001030304003480003130898010b09000c0154611000c0008085040c10140641c58011810940802100441130041ea1720b06005000180c1040c05c005a07544c490031103942c0581d140320100c2c50195204400b803040c00b1103020a2290020790456001d40c0d1007051500042c1c620290200c081d042c2c600302018010303880341c503610060800c07499400904c2181042001c2114400d1070501c00c10119004021240c0090034400044205445c2010621016070305d800b200362031a046504450341c10400001c40306020303d030142001c0010443d01c001c80c1c5c42c2a00420194005030400b6000d607006d50450007009290601550b0104540640140c80128a80c0e40e210300030064042c01042913251104010f01c00000e003018080c042825950141c40d401342401c841c00c0c80014040303040240c84821079444003c9055407408280119103183c0400d14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 660577904 1250 660576654 660576673
    0x312051909081b071e0f061b020907080646030807080a1101050c0415090b0c0d03060509070806220c05090424050105090a0f080f0d05042304140702 65
    0x181003824145810200104006010031003071034140e03850419a041f034900501072060b0440b602c1000c61075404005c2d0f001191008000380c860f88200c01620503401265800c1008440c00343e0541d0707280075411541c201e9186030755030082c4003c03030f10700700c4c03004502140780d050300d8a40c0d0351100300c041e800c00d40d800c84c2d1039000001c8600013240e00034040ba18010062008001c603040803044040140300b107200c1c18603011000007401d40b070240111401c0009042108095583c0c00c41d443e02c450f2980d4003030001c000441c9c94020b02007010f040150b581403096005885200c0d0350f4442c20208003880c4c5c2e030140c400300d54000325009044090f0a81c09004858a01c5855481e241d65095040009940301c4004409035000480900092030240e9034180003110000e003441650303000d045000c42c0000e009034001582c0d440b0310380000598901d0004e40d4402d4140074a041d42e4032035500a60423607881c8140e2107200070082d61014030640c001d139004003500c00000001c100003410034040d0050181001c04641d44009a046044175 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 660579154 1250 660577904 660577919
    0x90219061d030a0b01030b062407030309060212040302010c141201051903120203030103120206040c0308030907030c080a020405010b120c0a0512180d021527060a090312051909081b07 80
    0x80701c00040070403500792002004005034205005480c0c000c0c003053740320500c01c801d201c20369046414181c050786060030a454241400f07800b0b00304d10052300000882451000700d0080b41d40c0e083e21034860403501c0b00300300d99280c070040021140291a03150b00d104030700c501c0003002541082c070004c030b1018180c010350b4481d8507504281c0140341084007031805540254040100103a00720300c0f044140e0741d22680031074998861001d02441e0013206e400007060b03001e401c0e001107032a41001480c1201c030b0348203e50610951b0f880380c1c50200c003805514480040592004086140d9403092800b1300f500000f40d190090401081080c01d80c80d011041c4d6102c10880030854080e0700f0144244281038500c0b55900041c20581d80e0b042280c038003210010210109030350309000380b103003008100143d08a2800c00b001101d44a040c482c413150000c0c511140201e011403050f90f2500300f14862070045030310500145046910341c813028401003010b81040e4808945003902080003c00c000b0302140c81480c8441160028650b00307040c03290 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 660580404 1250 660579154 660579169
    0x271a091c0b010e06010f030914030c1c051c020d110d09030e010f090303180f1701060501021516120204060512060a0312120e0709090219061d030a0b01030b06 69
    0x2000640102a080120998104601b110131101500d000540255036041641600c0082244101180000540c011035140e0008402c0b0180e05240251052800c080c0402d41e101c1c0f28034044245000c882422042c04056158050040d115003032002007805030040c036089149a0080c00401c220740d9680003144e040c50303885032114181180a0a00340c0c14081c640c0c40c05801c5042c9031100a04014024103d0700754100512560401004151a0b000e40b103911030f0900400c01d00301001040080d840c0c03a000003007640c130000300c0601c61000301198a8460f100d01e4131000300da10004d14070006120040e081e18561440f244000d100819441d9541515805014a40140c1d1000588094461020110180302180240360300c860034a0079030a01c050480d50b51045000501035440040c146405013400004504440d0703000003510901c203e039074030482142c03261140d890380c01e640580000100708e10240201c044d41c050b204074000c01d00804441c102c684540d00e13040c41d00b200741c2084903a141d0301c00900680d07041000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 660581654 1250 660580404 660580409
    0xb0a0510230a0e0312030a0f0219030c020d0801031a070224060a0e0402061803150f0118051614040306020f0403060509060103030210110c0a1101271a091c0b01 70
    0x14090424070302c451a45004a0001407c500c810a5684100c0484e00560b40c0c100c0e07004130f51001640108094684d0080d008000c6103002d0809400740c2020842da06100751100ca058982c0070403860214841c0c80080401d00d00010030303100551064a1403d401c0c402021800320710900b000f0320310240d502d405400e0080d080c00395400b288080424405000040c1c0c0c0c0c0718144c48811451002d8806070042c524000391400c00c01c1c08000740e0501381c03c014002c6050f070b9100c00a0503188034911081d035001022050700100d070380417100035261046144013540c0003482046030802c1c3d188603801c00ca04040e02d076200d400c200e902580000300080000603041042004601a00c0d0740280e4860241c151589540c902030b45400018018001d11903036414210407000c81c140645000220690444030391903030920703240b000c8030030142c007050118000040d040c01c20301070040a1002c000020003003160301482c202c407101c014003074102c81001c0359001380050031070383c0c407100d4100e20714117081c84110304100d085080c44683c0c43c0068 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 660582904 1250 660581654 660581659
    0x70c060905100504030b040807020d05070302030118020f01110705041d061008030414060d0e010207050c041505060d0608063d030b15060d021c0b0a0510230a0e 70
    0x4040c42c0c0c0045402400361000c5039082450081d640c3e4a52400446612504400941c0580700c0003803d4107100c8000788050650713209600030450104550403003038265030f12200003544208100c40c89141944500d207240c00069242007207074105912440090251030301c04802801100e042901455403102c02c10141c0d4120b0741c10020032900301d0a00315200d449200f1070103840c1d81c80010b107848848580b10b040845044030b07a211070401c019001c0e100e10070b002c0c2d4800e80003580c0320b22480d8810f007030301d291500c0b41518560b031015802c54418508414842035800841a03145103658542c00000e507514140500d610032051200f1401d1100e11034410710340185d04200d081d1000c410b0180710080b00d10700c06c601c902c003aa508080c0050762543d0382c2d644110300808601c2801d0b00b08001255440d8004003d40141c030401c81e0016080745511020300a440407101144071050348600100020402410041800d542c96580d6290004907005042c45c46401d00d15410b1940d044148009020822035510185441800108 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 660584154 1250 660582904 660582919
    0x14040e0705121b0612012913050907030b09070e1216030b16050d0b040b13020301090b0619030e0327181603380315010608070e0114070c060905 63
    0x1002c17505444203805010721501080860200b2403a1290003c00d068441e4500c2441a69000c1080141001c42441d00c00e85008a50810101b0021800385c050802c800001070700300c6900d690b600100701d0b2951444502150018040310300940e10010030301036500321104011914100902c1c626201d0788000008021440b4048403005036181c0c0d03a1721008803000792054080202d02d10700588002001004200001c650003c03000c2140704a0350450f4000d0350403585515000c1003000740600a002081c400c40c00121114080701d00030b16922406988444000709044003181d05003a420316054490150904803440c3d00148217484141034030348000120402c04107140d250040d4141000014403a581111f400001d01d62180c50703404500c500804440100320420403460490404040406c0b100d0824600701d6010307000384101e21005405c410b1200313040301c080d90f80d003c0d1a60349140c01203030740321501c1032503c0c1080602d000f00403c520405001c0c2403000d0140e140044130031301d8403202601c201c4150344464065640c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 660585404 1250 660584154 660584167
    0x60c0e0a0305151b04051e030105091501080c0d080a05041205030343050c0d0903020f0409030c0303020d0b040f0c110d021905010b0405010b0c06090714040e0705121b06 74
    0xd8034050354102c40c2d00b03a1f21030038659000040d0040740803aa0000c140c2561906040007211000000c000720842c501c0c068064042c0d80b540401c0c0e441e00065050f807034000783c0111540c00041e041c0340040070521441d19020741025112140d4070012140d480b015104d681c80441403000b0152110807418040c1105220050305072405510803000f284404101d404c4040c01d0b03070b00e030140240248100c40003505000142c40c000e90100d00c014181c1c030542c1c082a40940c10a2420300c402d81058461081ca480d0140c403a01c07401d4000740e0b01100658412403030025188d440f10700448054803240500c01c01c4004a18010816000003130340184003054020801d5030729481400a001340d10f402103070a07407400c2c110150503460035030142405801f52070100c12440e0814a40400003c50000e1000901082c5a0b02402d80c0c0ba56220902d8483d03030303407a0310b01030f41000c00c3c00c0203240b804505d4598403000440c1901c5003034503102540d076800241e2040710510a00720b15000001241c8882d004a046032114003400c50b511401c000303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 660586654 1250 660585404 660585451
    0x16051b0316031202280e19060206010504021206090421050720130e072411030903060a1806050a020c070503060c0a08061f1706010e0d060c0e0a030515 66
    0x140300d012280020300e81501445c20340e1144150202d016005040d03003034544804075480c42c1034005441010014041c9400100746454540201e45080d0700098500c502e58032400100040d548014004558070000324201d10103007920508040046407850f100e86441f40601c0c100144c20b007101548071600c0000001c207944583c0d83c1c1a400b034400142e4a1030000d94282a480310928011540c0c20910f01c402030043ca00c01c00c8690340d151806042166036030b000072014a01c450b80d59a020301480349926030842c100182620720581e10900c0c180107040c80e00028200c2c41d4032010210380c0d0580b01a80444e400103010030084030300300407500050209030010545464190310602060040118860401c4015808540703d40d80340c090300700e010101034007400318000700004090490420341c0c1d600007100401c0e1000821541c0944507811408401910b0080c80301003d548080003041d480300d0f001d051004894903003143e5115940d0b99000342d44210b00030003a8170750109811081650080c88421119500200e241c3d214 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 660587904 1250 660586654 660586687
    0x1060906030b03061b2104021002070e01030b2502010b010e0105040810020304060204050303180405070e060d0510180f0501050d031202071104020720060316051b0316031202 76
    0x40c881001000c0540703400105805184581e04e4041c41d1b4480c0030440e00f0a20720300c800014002c070320031110003040662aa03000d03070b120506445100c40040ea14001000864070b401c0c075450703110b030340b1800ca030103206010020580d9048140d90200c0042c1e40d522520328155070400201000700c0c8007400c00d5400e003460841038030359406003002070801c7c864006c0b01040400000b50151000b80c000141074a4135207030400060100e01d0950106c2d030f44601d00b4100440c6002d0301803083ca009143c07020f4852441c14440c00460070103428060492041130b0402c800000b98041074092503069029000c0001c16981c0d840c004840a071041038000920480140d04e001000039000101740041448091000d40c07564541d00f0040015540c154040da041400000c1d840d042007420b6411842c0100f0340c0041c030080030031682c240200c9000c102d5800794540000c10b040222180240050a04902c1540c6030410b50001141040e096400c107607155014458801003682c02c040e04010641d4414104200840c1020303c401d843c0881c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 660589154 1250 660587904 660587911
    0x506030c0405150a270906020906030708190203011a030403020a120e0909012d0603060213080f060601080604090c0b160309060c1e020415030b0105040c050c0309040b18070801060906030b0306 84
    0x117aaa0340000e8041101a0301543e174030040081c205a00c03460507140180c0350650450749940259000d0101d884200d0140c426a8180d4250842c070310310109a0040105c60784c3d102030001d40035031043d60210b600040c0c82c64190302405d24259034859040d00000c0a101c0064005400840c882e41000c0e88070301082500010760010f1070105480c01c01060b40d00031610014079441e0401380c0150300000c1da0030391300d04d04031582d28120788224003150008144488096111241560040e000407140000305403d49002c1c0c1085e08124042d180700f01c0c8055481c0d83c9071400d6407160150f090602c010078800380a146c2c00c0144a8014200e90504420491842d42d6041c0f0040d003060355a030b15140c91010304403d6440b44d40c44044450315841a00030550744a0805190380b160074490b480c803850078983e1444059209505980340c0240d244011030034001d10b14200405000b2050090740c02c800d611481120341007940c07605034024151505c6020035541400720040141e80c3c160401424181451414401c0703490004007a0352 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 660590404 1250 660589154 660589229
    0xc050f032a0111010e010c0e06090901090e0f01181a040302031e16030e030c0a0b121509040308060103051b071506081005010e01061b060506030c0405150a 68
    0x10269a01c40058603c40040145030226600c4c2116030803500d001548400d030198100d440c1e104451005c4400c20219100320104580c0140300c2c60010032489001e44c2005105100c444245c603917050740741e41c010b801c64548074001820b00c48400154400e101d00e06031080c0012464451101c1d42e413a15403000b80d541c2c4500841440c10220403400d20301011803c80aa03144650018070440e40301040d4100207000d94a40c1072481d100f4041c0c0740030f504440c0f4040c588202100d1102c20000d05040801540c2c904564000b032030540728400310b802c0c0e511036607281011113201d03902c280c40d0408581807200004088400061081441e6021190f510102600207016600c1c4640c1c007541c072040e2070342c1020000001e403450703a04c00c10141c030802f004149043c1d8542c002c10705a078050080145140e076142400c03140460043d0900e040a034415554201091442d00619030164000e000c8035080086900442c003112400c58404000700740c142d40201651504c03420a0300280b0301c2c032001952444c5580c04010503402155520b12 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 660591654 1250 660590404 660590473
    0x160b0c040b042102102313171213091406091602070e01090e010b0906060f070501061e0602100b03030301060f090306020301031202070b160206030613090c050f03 71
    0x4000420148243e2002680545036180714020068090480381060402e070712404107012039161b400c0d80c803000f542c0000d4810000e45000a18103004413615440380740f01d2428600845035403104101a00000706060380c0c0b03003540500301a290840d18812034020241080c1c4000c0c440050260ba992020329103900300382030010854071481482030030703881c068a681c0501e041c4018070740006283c0409a001c000c405020070300a100c0042d04408100c0d03440d01c200d43e01030b0301080500030000d014003c5000342c01c4051007800000340e4140c40c4c0d010305540e4100908054080c560050080c8021903042c80075021400c5000001c0c000c4c550310b600001d032240014007400301001006042d0a410922408924005541140b030856403942c4904103e402801030500f0384025108101c00003450010100844074030598005100750682c4265003007222542c0050000b55000c1d002420000c003500701442081ca0741b91041c82c01800742d5182c0020300c00820107810525219400c0080062080203040000c201c80d01104110320 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 660592904 1250 660591654 660591689
    0x203030105090603033a0506030304090e070b03040501270c0e06030114042a03030207030b07030b1c05010c05042411060411012015040203030f160b0c040b04 69
    0x1078617501901d079100b0420031a8100644100580c0c46484240c12403c2880800c40020030560001f9902c0590344680c040d0310030042080740c5a101e41c4800040c0409005980c0010755440203103034980c000b594251096503440e9801c180d150002e00a02c03e140510041c2078001400c0c0d17440b0656140860b100388004c4541a02c0011401c0d5820341c09541600040365000400b41401c0c01d114041c0c2c884a50031048601040c5c164103001000080d607103003202e13030540c003c21001d0b041da0703a0f480c96214050240000c1c19201c0d40710014503a50600c031481483d0b244104105d006542c0d00b40030742921003504060742400020801070040713800108041110809c581c4003220300e83c038035610441d540003146a0707040e040c0c064042800304024414002040b0079401340e99400c0d0080c006c03d5443c03410130102d0088100c5074417412002c1010705050ba5800c1d4081e00003003d5a040c80d00305510028140e0200d2084210302056507013000400a8945545400492a412240c02c0c071742007840100d0213116a0142c5849410501c030700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 660594154 1250 660592904 660592909
    0x10f03110c0706030905060105060702031e120d0218150a0318020619030506030610030b04050a0506010902220311090c0702180403030b01020c22110c060612010c02030301050906 78
    0x45a4041c03021000310340b0401d0340c8480041c01007684910499840c003c0b03100004141c6801400e5a96068004001c1c22200030120000c00610035a400048198010000d42007400c00300040606104801981c0259441e0448054a180202103501031481400710040e0300c0f8144003528252940c100d0981400117849141201880c0402e8204070001e600c80000980d101c2c4c0f90760f6006180b1485c2c200c68038140302d5610350508264a80c2c0c01282d00300c00b03115141038104041094010308a8001d8007480c01e4660309080e548031182845401d0b080840101d4000900c0c0c0a50b01c0201511001d144240c2c0003c503110713081d0356032600700b044000e04c0302d07108880c441d022031114540002241c0007075600904010803d03041d0700750b01441c0e9000316401d5003c41e1034016030000d41d5001090619850500134461108400c54600360040c1c00c040251007040c0c5955000b51100088801008102c1e0030100c000a0800e4502502000002c0d441082000314690501c4000c5126540020640381035810888400829503540c002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 660595404 1250 660594154 660594157
    0xa0b070f030f050c07150b060f161b0f050a0302030303070f0909021216051606020a0e030f0a0c0f0b030a0b01111b120327060c1f06060e010f0311 64
    0xc000002c2c5001d050245401d2040010705c140340c40b07401c00c1e0301c8910070b02494004a400f006a40e6401c24410004200c00307914200c01042103400140c209001c11030551036000c42458082c042c030300701106114061003103000b01a000001000204d9200b0041421940420f8803804060905c0302030007070760305038165030a01908444010f481c1c41c803400c5440d81d203581a0961441c60030b40f690f0502c203019aa900054901c14011220b03201c81c190280c8402c40d0300391b40d8500003507000e07581c80300c10000d008d00703201e16540d0700340414038090400300c00411542c030307240c05c00200b659400c0d801489040130041c0204400110f039019a540311800500025400350b14600603101e000c913003043c80c038203401607445038030404407485600c40700400156415505004503214165803807140404d0343d51001145042c2c03da050100c10b0154421074400b800d0b5034180500d100c6003d1a04c281400758a0100c1c02c002c5200b01140c545209220007003800c0d00d01107505403035120020740070f00d100d11440d40406459819030140750400c0700 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 660596654 1250 660595404 660595421
    0x52109040c090b27040603050a14010b120a051e070303230703050a030c0f1407060b040c020a030e0f0a03111f0509010e09070503190e0318120a0b070f03 67
    0x114030703a580d01e144454004d11007080f20b200c8281c0800d50141002d604181c814101075982c00320092640c400d8680f41c0050841040c1a0061250340700d516900890310385002c0600700c02809130041540d8101407602604000c041012460100340030241407090b6100004c0103001c4075094241a02a2004068403116114650b0340c240e590502c001034800c00c042d488070013003c61584998040000c0c1817541c00032a010180c102c0303080d0002e52507000744001c2c240034000400d0264032507032001801d0701c4000081402c2d54062500c50b230250300600c501c00281500080c40c41e100c000c080701c8018015065400280100e031035070101902e081c5201f0350340042c60300c8420100804c21608081d000075170881d04002005030340428159400072721120b00107011420107514071130003810b440d15481e00315929041545440c00c0d0034544011000c0d11000b8200040c00240010069070a45000030000702d81c501040c001d010380c0c1c1c6810b6045e25484204031034080f40980044580042030b07403411140000d010b500c01c03006001900d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 660597904 1250 660596654 660596669
    0x80705030403061a0108060901060923040c0e18011d04051609060614040f0b130f0e06120d020a02060f130b04031a070203031302130903080103052109040c09 69
    0x104c0d200d11500d840100007500c0742090340c602c07030385903079020510003524402c1c4280f0b404101e440c402403109044240300401c5401c0c0400c0150f40f1242003600007029603419800e101c020a41c000701c540800d0602c1c11140310840b214802c180c0f895450003140c0c46550300d581e080110b6010b00d400102e02001010b01c12407203c204500ca03c08895a111808100101594425600843c9034082c220041c902c2600541d0202e80310029418455403502800c4d042035032010400c1c11a039103e140c0c000c0340300c08091010303c001e010130360b40380002490940c050040e10205a80f005010b0307802000c002604c01d0340014181c2051f5810b56003992500d0032100c0548803801020480f03004001c0c0c54501140000000c0d0280c403c49000702c505004445802c21082903080040d1442e40040c0c00400024012815240201840b144041d180003921150040208102c1c2c0c0e041c41e003200010203617001041401010070a06064100951000300074a1841c82124002e00c071b41a0524002e40e1100c0c000c170300079800f403840080223040c40b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 660599154 1250 660597904 660597911
    0xa0312031503081903050a090206030a0e12040902040608010b070b04030f030e1f0f09020a06080c0d02190207050609030712020604030c0b12160c0620180f0d020d08070503040306 78
    0x1519a113004003503541070741c000040d14210000b80d5100f0503000b201481500640700500d5902e0300907610780035000543c00506144504200b2401400a280c000c00050076000e60060704c840c02c126009140742d5047c0c6c0449403203507042c442072011500940c0150340091b8581000007195802c0c0c403040d4003402283e44a10018003a1361810b0b403050b442281010407400c5503e104010701d002c2a1520710440e80194406074202030b603040203001e89070046c80c9181c0c00c1021070002a041c1040781412806aa0080c41d408c0b044d2822042445c980e15010404503003d0401222030310304220201011a6132400c2c94845c0080c404901e141c03080c1952110340071603001c1c1d9008240042c1d03140d1940c610401d168480446850761000120000341046c2c404081c400c000404d503030f0b4403100c840b00c9031120009000c1803c01601010003040c0c1010070150540b000340100b00050708000700703402c03661080014005071944648e009140120304200141d54480c0300ea003105500c01603003620303510380b030804c41c0c0756006940004152034074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 660600404 1250 660599154 660599167
    0x1a0f0c04060503070e040b1c170c032d070c1401230a090306240f0e0a0902061306091a034b0f070c02011e1103031f050a031203150308 59
    0x140c0c14401440e990082404140c000c427034408505140c40f5160240e0900e405c28440b440c0b4900c1e04080d4144c0031b00b0040f0071010005070042c45040e10742e00042c021510752030300e40d200704200661141c00c0c50f6080001d00340f842c01068042541300484040d2000340d502c490000480000e040d0150b01e64074007441e000803003003055240c006002003024504402e000403101103000d001038045803504840c01a264500c0842c00340b03440309460a00601269a0100e80c424801e0041c28040400d141d101002042103682c1d04c00854680b04028600c0e045018003124404001c2080111420f000302802000c13903144110b4003081404440381d454458031404401da1144665000189502c2c621140c5034019985801c643d9265203641500751038504000314000d004c1400c8030301034940e40d820790030b01c40c0d100e082c81e04102c140b030900540c400b411a4811511080c81d000b000c0c1c080100522005c4c071510160500380c13036100d6078600710380b1104022019a0380c81c004041c0c07202044d850300c62840c0012001140d000e54100e40310f01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 660601654 1250 660600404 660600439
    0xa0b1305150658030c03030e0307020f0d1406070c1208060906150f0403242f04050d0f02040b0301050c040515071a0f0c04060503070e040b 61
    0x140c1c1aa406481044420761409218203c80e0b550540e65141c241080944402000490342d1404104406444041007209000c00303581410900700420380700c1d81e1012140b88543c0780c050b007150300d90100380d074480d4800d2200c0d03030043c0c0b00c2d01e458010000c02115551100c0e08903203000751a031240d012a1039402d00074407041c003161300e0300030388600500ea120304c202250744001010300311500d074012a607456010000c1d001040740c5040600d4a1700c1010340d0604154600124660910000c0d442640100c03582e42c01d00201c0030020240396440b148081f40c01c60240300344500d1600e5003250030ac0300300307903070903051b00302c02d88280c454500d03900b124010328028000c85c0074040b440c1842c400c14812143c0c1a03018501b0022529010714040c85420f220f820050402d9050be42050140825003400c441e088000e41c50400c14540483d820750b039011310700c0300c441d01040c000d860080c0c1c0b8000d1a203406055520ba8801c140800d100b0140c02c041601e50200c05131a04005912902380050040d003410b01489800c0151400703c1d561a4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 660602904 1250 660601654 660601693
    0xf0e0703030816140307030f0908040810060e070507020909070503060c091905011e02031e1c1109010305090c0d05071508091005040c1e0906080d020a0b1305 69
    0x2058030f00c80391a459440810242c40c25106503032014840802040080c200314000c3d4441300c02104054000900040f0598685009a1050300082d049a2120300041c802d102039000d4003001e040c0761442d0344024140944040e00c0c6010380311009101307504a40001d403080da402c01240005150040c00c803240c6060460405850342d21a004440c000c1c030f1134442060f281c1e00000400000c40304180e42c1c60b00403580d0f00d20040140780141c040041140020044d07840c0c035040b1a14403104281d100c0b6000d5503a1f03000300500450000c0c4480d00c0e600201d04000b8281c01e1100c0b41341c15140402c0080c03d0100b9541d64000da0213060000003210298001c445103038180903c00300048000540701048004800181d001c08142c99004086804080d80d80c80641e11141841c0142c02854100344615201c2c41c240e40c9980d40040813200099200301c0e001442c1200704000f600a00034440184505005812402c104602c002c0d29090f81c100050075080e2a40003040405202d202d4071510175030800141c80f4186c0d00403948900c04e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 660604154 1250 660602904 660602911
    0x609011b0309051e0d020603060a09020f0a180b030402130e060f0f0a06031104090606180e070933091416050a0203071b240201110c100f0e07030308 65
    0x70101e18113031428810402c90f05141d00c41c4020244030342c41d0b60319800c001013640000c0071250094040765000594122070b0020b1300303200100b120800d4a42516900040a000051103030a00c0023140c41c134200000c410f03e400322500141c054940c0348034000c620303c003280030701010440a00544516802c01c100d006417051064099038062611452540395011180156500c0340406071400004d25214040d40c5041c2c0c3c040c108480c490300d03020440036a01c00b072039501c03000480320400c00c082d02c821a024411500b406a41d0141030759500409c040b1042120341c00380303a0015101e1044481040801c8540070207555502001040d2801701031007a100301003040c0310422825600144004182e002d2920315030300400944084015030340c000c50031f041c0661120180144007200189122401171000f24590990301c00c200c0c0018110b42d40c5032440b85503040001d003150110030250982c8001130017450321141010403501044010347c1404180302a848219000400c0024a07110291140036400800c040e08501040d20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 660605404 1250 660604154 660604159
    0xa020a030312052d060a050a06020a0308070f0f0302070f0b0a090b010503030a050702010507030311030f0103110d02010212250b071413050405070c02120601141206060609011b030905 80
    0x740d0b403252901411854040303810a181d190100a2041e1615080644d40b5802000113202c030b010b141c1c0c0c0b140402c11502c066006240141c000c02c10a10905400591607030300081c0e64504070b031500103c0c1c0d0700100240b1140030000101900042c50200740004041707140d82c42900035100359002d0030701c0c0d10540000c201c0240c0c202c1d590301422000003240e00c1c010050358a51885602d80174074120f0180d00448582c1d20034403089081c599221014051254840003641c411304107142c80b80c80950450400401c105d4440400d581f080c1610b450350030060341d0210b0540455100160100d4807540303010302c0d0060b100b00c0051000d0b0344807020070f0004184425041018005d4400e625a040922070841704a00c2900c00c405194810151125080001b4200380c0d0040d54490304520f88080f04840550000b200b905802c80500714544c059001404800d84a4030040402041110a4842100c820540a441d45d000601c100e2080d00040340c03080c816409480030b140d0908a43c590801451303028540039000700c48078044c150 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 660606654 1250 660605404 660605411
    0x601020a30050306100e03101d030301150306080f1002030907050324060d0f02220e011d07050a03060e160f0303120501140d02060d0c2703080a110a020a030312 70
    0x2074501c6e01070030700080c12580150252050710380d00c0a03e5806460b441112000e145101b84482c0f24030b0a003480594041c0843c01c160b0a140c0b001c01074020305403070640d00084950703004103079480b11800300022410000d000301a400b50b00c0b0340e00c020710181014402e40c03120703400d80180d40e01501d500c6661100803005c4c0c4071000e204202612a4000c1c010221a80d4078010302d00c800003a04a4050329010404003a142c54100383e0040410000904100307603101c0340125185a91110000321020180b80c13184282c41d4491001000994640340020f0041c0241d80302c050602076a8509080350302d801844002410b45c0b00380444c400040d6203039980140826140300580c00a902140700c0440304109015160481d20007038a4141e40621a4003000000301e2100e5040707030303c0502001000c0f00f2029034000e24050901549924090000031007034003d1205403510b403a11603c1141e102440020300460070b80301084c600e0b14180c0ca07a4080f003020341d85030820110b0060740c85042e6480000404da0f004154a090074007032032050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 660607904 1250 660606654 660606679
    0xd0804060609151208070c14120c031002131205100f0218040b010c0b0a1d0c18070903020603040b0105210303060607060f06030501060e0f0601020a30050306 69
    0x40781265007001c3c070192215601d0703804011004290940c1900c3e180107100c1c052601c0c1c0c1e146e07602d645200540e4002c401003007030142c0004e02490940511003440380550043c0c2040b014841c00a40c9800c846100b001455602065062151805140b0103000d0301c180361000e02400703214146140e444220a14101c03009040001d0005c0c209081c0c001e44050020010007801080b0300c000800c400780a8070303400d0a040200c139081c080c002c62040004c1034010180c00c140055842418004c01d10b204ca0b4946070402c05500c0004c04001c5512171100e103454400030080800b6440e04c0754031048842c03000c903600c043e5001c0030110a102c10301c049041e20604852045032000c03000300c2c144d03039061800d8a2001000c039076a001400000d60500301240203064035841500c00185892035400c0940481d00c15070810713105695100700c10700090318083c845903040401a51011207510709100001c0d5204032929000b088035490008440b10740c40d20002012407081400f10740026407106501c0106250402c0341d21074491840001e04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 660609154 1250 660607904 660607919
    0x110702060c01140a1109010c060b040f240e01030f03050f03040542060301020423031504110f011707031401060c0302070909080720010914010c0b15030d08040606 71
    0x181d0172085001951182071100c41d400540c0c003040001c80a03150162100c02c580c0140d601c43c402c100a05106c000300141f04034113031200c20f114049002e81845100d4080c00b09002000500b1070043c1101e44c41a04c1418038402c0b8981251140602e590041c081000030051004000d80420f008245074400035000c0900d00c002d0804148483c071118480d11060071940f0003042083d036421200d40d20900c048c00140c80c0c079695010983c0c051814a110980071001200700a080f8034080c09800c800302081e2050141600785515405880c80b42000482c3c49201269400c1c032859000b40a4220890600c5a0300942e5151040000e0081c046514907480c9801d405400820807030f00070303c0001480ea0300341e401428000c1c184840c03c8000c0070705a800343c2c0c4101c000e210540000721307066030300b5860040c1800000c2c40c1009502c000352188401c0c0e000003c603a1503001c80807000b668406940820590030448010072074807409048600206c4084655400d4022082d0b610a040c0c1c0000c04540110300c030b030008000781656280d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 660610404 1250 660609154 660609161
    0x90a0b03092a01081f0b0d0f091a0402041d0a020102100507020c120705042a0203040b03040312111305090f04030206070c060e060a0e010b0102060c040603110702060c01140a 76
    0x10a003189009488290b22194414a0129840852103031107460000311031440c10803500d880c0c2e1012142803800a03281c200744c403840c024540c0081080405104548255403811010400100300c60342c080ba07000002020340da00e03508101c00701003020400f0b070351034994620a02c0d2121b94401d016405445844c3c0d85c1c103500c50151007040d100740420350141c0b0f421512201000700541142c0c076105c0140c0300b05240403400740d44921880400961160b201c82e14a04908074845c2141d00b111700d514103541052008001805002d000c42c0c0d40b040e890301e411044021003400741c000821071107000ca40c00b40000700b012080802c01503060703007d82d4002c9482614985e41c1401c021340c551421200100103802c10400310354194007420b8500356861003994003050f0403012001051805104840d020a91500c84602c1c924403a428810410060700a01c058011407a05460310b0500d8461481014201581c40021200758841c84080e0355410b5030082c44666074113007034206940a05104603000302843c0215000c0703180c0504620 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 660611510 1106 660610404 660610453
    0x2010e0f0303270d0e0d1b05040b0d0507060c05123f15120304140a080a03020c040507051603080a06060f050d11090a0b0309 55
    0x4a031440c02c0c03c89840310985500082c40344900c1e002c282c03008410b00741c1c145011100c049a0100b14105600d10000d403480c6c40b4000038254078545a0108002c50710100e0303003404160040c1c8204151500115002801d40d030001e4030030002d070780c0100e8014003040d0240e0141c4180740c6450080e0f601541c4102e403d03508000c0340710130144112040c0510302240c005003080c2c042421340100f446c2c5000c1c42c000fa00c20106440350203228402c42e50b8a8a090841d02460000d503a11150b40d1003550349040744200847c1e1081080041c00300b50030000060300041c494040e4020803040d811002480014000a000c032800c01034204a1144199400d60410180c288283d0341d495540c03810b031000204940994002d142000184062038078295401015141701e04041070000844540244a83e1803c1c4501c901d2700d50400304046c000101c02409102a5100342035000a8136940c81394000c03454109903204 = true := by decide +kernel

theorem cover : BRFrame.Cov 660431654 660611510 := by
  have h0 := BRFrame.cov_init 660431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 660431654 ≤ n) (h2 : n < 660611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
