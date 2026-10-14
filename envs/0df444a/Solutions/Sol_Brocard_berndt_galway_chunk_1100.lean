-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1100
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:14:33.019322+00:00
-- url     : https://prove2.me/submissions/194b8ba9-bb1c-4f9f-831e-dbf362da14e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 197661870 ≤ n < 197841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 197663120 1250 197661870 197661917
    0xb10031d010c1202070305070b04030503071706060f0c030c1501030606080115050609040e071706060405010e0708070c0b04140618030d091b0f0e010603151a19 70
    0x4040ca40c1c5090410101907400c4010805144103100015036946898034046885000d102d4004103140d4001050208054100d00a94070410f456910302c004110030a41d848201d61040d00c40540042042202040294207140200140c1071100308407850724a15503030b50380c0b901060a152181c000c0003540103100b0800c80340580e0340200350b01c50080c00741c1c4a40c00307a0f401040090384251442003400140f01c0c0707420746498000a44c181455025100e45c07950b120412210b817183e640c043e04a03405624005019440c0c0380c42654143c500040c0c2908440d5100001031b1900c00700036001109208803100c03141c0010384c00c0c0c0d00c0103218500c00c00b5038440011203009803520305000541615018103aa18900704d41800c0041aa405000e0300031000c5052562402c00c0111550300d00308007650140c0c244004107290509501e1482214080c16401490381e036110310403800c5404824507040e40445040c03003080454408084e000030310724908030103860100c0f5583e0740d0742c0e064200b500e150042030b69101d95210860100000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 197664370 1250 197663120 197663171
    0x30901120501050102060c07021f0305010f0504060305061f030503030403021b0d0f0206030c0405030102070606081917130e04030305010806070c0f0b09070312050c010621150b1003 79
    0x7800154103080000c0d4841d00d0090084d06841c0340442c5000070340d929041c0149030b001c641c400c2c4050800f0041c0380100545400d0251400309081384034001090308080c030901c002c8039009809045036840e0412101296060694900e03c1c14401c0700000c0041841030005501483c400d070010040d2890903000d078a5103071054800d0314400c0450305105400304010402807180103504440c020b030390f03680740c10f00e0000d103001c1c0b90003440c0c043d032002c11800208103507580404240c84041040b0341014802007540710051200c4078004040c00a401d681c4100890644003074000c40b400e07801c25142d141e03200c09106404041c110340c146d001a0b10743c030040015100610159404c0b440501e0301395034a814036160f410500b0050000103005040c21030001d503486405211003000340d0b81c44140c0310072101c0e125070010800d40050700f0b442000d51030a1000030314500d06442030400c0031001e186000280360382d52101200101c211500441d0380b41c0310040d03071701195240d4040080c0e40105842c0003ca280b1540c0c503224561400503030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 197665620 1250 197664370 197664407
    0x30409060e010503060a0c020f0f0a0605010e270a08030c070606050a08030901050c0111040e040c060527010212041712160219120305220b0a03022a030901 68
    0x18040f50710045401c0d40d01c1030441402082e50340049108038a080e21940b0907003041c0c05001103004403054040340346801135000d40010701031642c8030403410360740010a59090500342504c0e040c0303096504800f540411000a8101a144690119155090340d58803c0351740400c61480010300004114580c0701c0c55000d81000e0350241c0ba5030b0309102ca03660b034a10900d0f031010305101000c52462010b501c01d400c5840d0b043c00d0070302c80588403596180c900c100c03150151012140d000d0b52070404200f83e44a1000d0351105002d00c0c035004a030380aa40318040c070360351441419078110300a240d0714004a508440041004103140d00e6810301d0000648002410003102d4041c0d10360307a440811203840440e10704140a800e00d50101c94298910200d8918401c8885240e80000600d040380319400c0c0c14180c004016000d10743d0050050240c881509032500041009401002d564032030a00c02c18000511035405070005425040c1000c43d45040e10714056059101044030a44036030000415110300c0d40d110301210300c0b030359641c41c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 197666870 1250 197665620 197665649
    0x503220206180409050a0b0403023705010b1f12060b030a0507020f0a08070c050303030708013609031808030702010807050f120f060a08060a020a03020403080a0203040906 75
    0x180051000c0c420150148030781c1a9000d0ba40d01159590340c45003405941c014221180380c1024542548460300440e400e901501546081d44264201d520b004000701d40d0388165000c10140b003c400c40c00b84080d40000b640d00d5980c80e074001d00c4503110394075007441140026000880b0a2100f040060061981791040b000280c03d044007045400c0b0300100f42c1c3d40080d4001404681e80c0d485900403450903d400c901c0e0340306441880341081c18030506600524500340945a91123007251a83c01f891307601d12040d02d03450001003c80c401002410040056091000040d003122011050040d50001e2141a510400051160b07034100150415400c206031080501080001910036880d080c040e5459003d0380034064148080040000ca41500c160b08451044041c44000d54541e03000000d560103500341250383d00d000e854210081201d03840e10400034000c58039980001c0040e41d17190343d1030a001c2d4004441a01c00e041d028040400060800c001925181809a00854903580b5044100059030703c1580b107003100c40e038244c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 197668120 1250 197666870 197666873
    0x90f0c0f080307020607050a1e060f0203040b191b1205060a2603040f0308120105041e0908040e0f09121c09020111030406020c032b121407050322 64
    0x2c410b0712015074046171400d445910380d05215041c0940a0f000070001000382e039080103070820394425807070300c83d004200c20048410414000302c12031001381c2740544609140b10005160012807a00100c60400101d408900c1c8520b171040d0320403400b51000c034140400c210300c59480c0c201e00d85114042d44031004443c812906403501410982c2160900c3d4001c1c484075514521401300101042140c0003424804c0c40c11110550340d08200c0e146070401c01d031032240c005103100001a1803a181c001c1001c0c0d0f031159140a1440403c00701042c0050802c00800c440c0000144030003d480304458085a100310b01c401c0302d40c1301620b1315810035410095095080d01002c5000e02c4a50201c00c04c8046843c22890b4040000620750103600040c2c46031041801425254400002c000c00c1460b0302084407520480190200c44512051116112003050304005042e01c60f0100c005002020f44282520010b1402c40f000008035070301003c3c04510f442e0801c4030544003042001041c803a005010b000b0400c00b08107141810154003125 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 197669370 1250 197668120 197668123
    0x302060906070c12240606080c160b1003021c030906030b030c03010c0908010b01030209240d02070b040b090607020705010e040e070806010306110a05090607030909090f0c0f08 77
    0x101500c403401010003040c84000c0250918548000d810322281c50099900e0b076150001144501c2c4660303280c2d442690701400e1565005020300d500740c0302c1030344500170203030740c0c0c100503141c543c10070040a2100c0c4000f450040c0801d540401c0d850290704051815000d203070450062110420078401e5480d02c092a8801700c41c0071a502c03408000555160349404142c2c540028002883c2881e100d0080740c0c99403800c06049502c0303402c01c3d42a0201e510810081c44056680320042d4124020f0794840c0b60040c6070b941c0a50741c0740907110300b03011100b0f040c00031190038681848a100d040342c101315011a01001e80009110610022009042d4000400b1004080510380715000070344444035841201d0520519441403080d640e56500521001c1c8c2d1000c0490710f030b290b070301c3d4103c940d41d40081c881924002c0c50800000e9410081208943d101c2d480e9459091604c5056014020964005a410b9080000c0300750081210b84613400f0701c03030320076003e060103c3c050b51503030a0805040303c0950003503160700d08c10300042114000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 197670620 1250 197669370 197669377
    0x503070507060914101b051917101409041109040c080109030914010f020a0308040314070b06011d030d1101020717072006040306051003120f0315030206 67
    0x4191030500c1d201c0307966141c542c010780301211000300003140703007000d80c941444005084403110310011000c1c00b10340e4000185001c0c18103c226100c0c0014000c000c40030b049100d009003403828908a1805413400405c0f2240e0360b000583c243d408019004015404004941d4040411501c0c030740c0848800c2010700b0b040d80c0310b4400c0c0c0e065000e04e50051100800050a00c892407401c0c1c0000d005603002403001c840107150080404605002d004000d0b040501c2500103540300300000040900c803600181100c241c25182580c0307061000b0070032030400240c8410801001c0c50007000d000141d10983d00010f4a0520000240010542c0f6603410035010702c2a0405ca40c2d80e40029620401c0141402c001c060302c20707004600c07030180c0704000014081d11845200e001d0b04d44101002002490b024144c3e0307a90034a2100c010000040f84050350a502034824001031021400681c81650040000481500c6140d685c1d55100d060b40091068003003c40d0300d07581e0701401c01d42c150040701044080c0c10b52420302581103a000801a01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 197671870 1250 197670620 197670631
    0x1050f13020a0519060201140708010b1c140603190b07030209031612020a1706011a0c100203010f08010b1005032716140a05060a0e0a030602280503 65
    0x3404655400c0035500c600b109100a420083c02d02e1000028480b4241c44081d01031007101d00640c6000c2e512501c0302500c02d180c60150768143d85004699107001300882458201300c078605030ad100341240741e40349401640701c0c01000304c99180031400740c5d01e0700904050074000b000e011804a40c1e071401c00d04000400302440640e00c80c000c3e0400607103401c02c110120341fa11200300400800c900340d021011030102001d540c4281540d00c00c039641000c01e5110110001c0c0780000c5000c88000b584108018450806030706088544500f0700310324241002c101e54601c1e0f00c1c2c00400c808001061f94008014012520715165020103010110024014840e120010500d81151607070b450040107008001b00318002d030b151804c200c42c0c100504d184402002206000c6898a0900380b050031290301a1200061207140c0040c6810007040040c000086245410240b0061f9400000d048080083c6410345000d00da0340c06c03192901860050710016101c46681c00c414803204085115007041000e900001c0ca040350340072003100e9110 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 197673120 1250 197671870 197671891
    0xb1c020315070f09241407060f02031008120a081905100504230c0702010e030a0302010e0c011d010f02030c01020a030e0f0610030807060b130b03011407090b071a01080a05010e01050f 80
    0x5c1d8451006d5002034056030b10010030280c1010303d40040741c0303200d801540c02141207200c181c000903520003c0941d180c00002e070400b074504045c81002c0035640210845507104184211079048172184072141000c036002200c07030720007024009800f8445d9003801d1240742540f88002c0d007a2082e400710b0740640312040343d00500758030321200c3c00104502164454102528001c0016044421340c50030b52402074041d181c40d0058003441c2c4214003504201c4d41c0715485084040302c003001c02520100898004481e000011341c07241081d031100b04403400504a003440200303c5020a035600040400304509100d0808a250141c03050030f51101040c40a0550015009421079174020341283c3d0f14021494880c028115002242e5441004800e540b29402c01540103000703200421402001741d80000306c2e00c016032140070303519040000c071010001c0c05034075100070080220a004004c1e141402e110719010b03c42c0901c00360007862964204945040400c0000d000d007001802c2444002e000c985003800007000c03155070090409a51 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 197674370 1250 197673120 197673137
    0x30c06111c0e01060b04081c03060308091c02060c1f05090712151103060111060103030e010f090807060c12020319030b01030f11040f06030b1c020315070f0924 70
    0x10b0000c250301180003084c14114483d100c5650740302c099102d0004880741207000102a8251000e03a1203445490162640040258284036610050161a1044860244a14401003286805652428060008048500f00510116502242030001c210314102c04420352030030401484541c130804034001054410540b0700d541d82e04110300704012a40c506840c1c0d41d54403403a20a400c2d00058028005602c501c500b83c8030312607000c0e046044295100024032002d00010580b03642c04160f58452b2540580407200c0e864030340109616852107a08007020b545c490380102e810181b98104100064400440100107400990b0500101540d03100665100d100e941e02016594041691503a0195220000000000204000c1c3c04002c0d14a404207034014060404545a20900026868803a0189801941d006021440c3c01034001407560080c01000d84203e0341401812405213420211a0340103209000c65034413115000d074900d002401c1100c80340c214000720740d0f00200c07000300c81c0d401c03040d9008064282d02d0200ca0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 197675620 1250 197674370 197674391
    0x304020a09090f06020a05030106110d08150a0902040803030702010b06163804060e0c0105070b150d03050307030f0b010c0b070207080102070f02090702161a1204030c06111c 76
    0x180c400c0803c0000d05152010409071aa01d80c000080c44c1651010f48440f21401802c0f213032155102042042000081e0300320002840d0130f540b8000118442502400b0540300030784400602059030420b40100c080d07948040100622103509020b41c014100740dd40d4242d207410392100c002250b80b000c800c40980030124180d040000c1d4000c20082460600c1c0b04140f030921044102455a03c04006032010340ea454100000011810002302d00001c080e60161900303443c1c0001076407044000c400c014401e40c0c521070340060340d41803622004d1002d06120300c039039589660fa14162401030204c030112032016404a142c40c40c222039503604410004201a009440c07d1022350b1a004101e02e4007001c0d40101c0000c3d4008140c05080000750130003c4c83c050710807120302207140e4481504903520754440391a1961061090403c0011131003d00541c04182594a105407400c8580c807202d50b40c00380140c03802c40008401014000a11106209001600014108982c540000103602e952100101641c2c500c0c1d0540d80c0c1890710 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 197676870 1250 197675620 197675633
    0x4170904180c12050a03030239060c031e0a11030702060403080f0c0403030c0203100e10110a050a0507050109051b0f0904030f030b040e2b030203060d0b06040213091d030304020a0909 80
    0x9035004440c04034800d020b00c9039400015900e0036413071001c0b54030032600480d62f0103c0000550b8030031034a01c04c0f200d041701401000b0580e040409000c0100c02a9a402508106140c02c40118454140c5800034070190400307190003004c100000b4038030205907102105222844400c04110340480c0d40500c0c14070007400c554000071f42080314513070400003000e01c1c1110314143c00c1000b184083c0d2449940c17004000001e400104034000c0e12400304080c00083c420000110b1182c02440a008014041e00c0006901c4c5c1c0190349581c5044100d0144490403000300e1781303800c4a40b0703014801c0a11000e064640c65268142684c024007511200c44500341490f890315500341c00c0344c480b94411808440086c048942c5032034030022822048100c1c80403000b400c1c02c821400c00d030590090003141d0041304003610307402d01e890007911024018040a844c0e030764021780802038403812040c0d10310a00c02902108000080c10300c0310048500b4188000407001c00140c009000304005030340d0700411a801ca03010280040740d40416440c0a5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 197678120 1250 197676870 197676907
    0x6030603020a09091a151003230403050c030409020405150c122b0212010e0103150c03110a02010b0a0909110d0302070302060c0a020102060c030c0304170904180c12050a030302 77
    0x8581501c41c17104100c1011808586400250004d40c1c84401c8010040811801d40701c203e50101440a2411025440e02c04103440140d80140a0310f002c0341000f83c1c40a040d4210303030041d48030103141600407030144520b00c3c2504250310a070201100c000c0ca422015804680c490558102c00c940d03400d0003007400c0031640845820301c0c004900c4500301890800d4910b443c40e00035001303a1001c91000c0b0b0b500d000840c0794000f40f104681602d410052451026220888034000b800010400d6803c140c0c03a4411100038420010240594094580002c2203c040000500840c001d5a9000e041c196091010020104400044484013640d05849002145a2600f0140e140030565400250007100c002010000403101207207042c7e100e032007642a601c00b03440d5034940c0d1440d4001696103142c660800c01c0803d00150820090b0040c1c0c0d550070203150305140c14400060110f600003c400d107140895091003004004000c5001c101a04503040ea40b448081191100c030359415a1b06c000034207040d0b0001d001c4600010b41e20b0300c17 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 197679370 1250 197678120 197678153
    0xc0e0c071a10080109080d11070302100207050c090403110f0607050703050f16030c050609010603030806060309070509010807090b0406034b031b020f011803081b0706030603020a0909 80
    0x1d01c1050b140c1d203440102030348000c1f8014125413030b009400f103003528108111885260580d00900001c0c110500c03030300095114503011103091047c90f4200503103403a50301c00a4400da009480c0c02240c0d0360041280750415003d0f0b0f0514074035421000c10000c441360894141e5044a0705032a02c151141020026294580b1656108a02c110403400c0d140c0c6c02c06511007440f80d1840c0c402d1003950003540711540c1c0c5509981d1103000040c00700d034450f80000d0b01410480c026542c00815141150009665207012901d80e035400c1c1c00c03514140d000190b0900330f40c02280601e030700f20305080da0b042100c0e40c03454a805001e003401104408045854011b1030201000724001002405660075400c00f0700b2440c0d00f075070411820740d05411008a042c000001030341a82a10b40c0d0b10706207401500000c1c64101080045410300102e80c400c41d1034601c80c0c400800451045d0740901010391010506c1040501659042441c0402c43d86c052000c15040040600060f215800e40c841241c80c0c001c004207600c0c04600e0b114680c9012080d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 197680620 1250 197679370 197679373
    0x1602010609020d02250305040501050708120a020a020c011419020f03030a060e010603090b0a051806090307060b06430c05040605010c110609120a0c0e0c071a1008 71
    0x214018991030513801011007062455180540007580c2007401c400f17000680018011071070a001c00c1090754041c20003815028814040c10785400c40e44188401181410703200401d05541c04115500015010000c00c15005024201400c424209070500d0009100d03c10140b040052921812071040d4001c100c0f0300301c4c641510040d41c0d1640380c54240c6400070240c81c4100814008181c000141841c024413130400d62581003624880e0541d502c42040300502006000d819000e5a05c0c140c0d40c00501e401c2c442180241580c0001d140d81301400e0070298151581201f50b40c3c41444d08000350a0100780d01c2c03d180291544241103204140e003070100442d021043e00541e20b81540c44c5403110070030041c0d181e4804082c0c4a0840b0200121900c0307100440c2c0300f2582c034000802c81042010003410074601076021700012f0320014440b14004c400340038074904000101d90112030711940c1070428042550700244040e48690405291401c03d892600c61070a45079200402c424050000c0e0301161140350a940044080e024810 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 197681870 1250 197680620 197680627
    0x1020a0f0308040c06090b190e0a09020306090c03061e01030b090c03090601080c030a0b040c0b07050d0f03111801090905070908010614060f030a020d0c0807020c0f010206160201060902 81
    0x1c02a12902c000c079001c5400d0020b804000c1030841c0030b0b0303602e03a0a0303a451000450800380d1015a8800e4010150b410742c080c040c10104c0d0b89155543c0400b1080900f2103c1005a103a050003414030500c0e03d170190058005031070034020001b8a443ea68203070384603000a0900350043c3e944401c016402810780d0306185400003491003c00c04001d0703044004600443d140c4049410030381c2ea5240140d207442541c070519030303d031f0807000b07650000c103000e50b0280d40c00c0390144818150341540e52104040d103501803e0300703c40355080001c020b0043c94002e09c5030000529241018008110101d0f914143d0344510001804007500c00070107820030b40d10410080000e08910351081000d400c0003440a0318103c01403203494a250b0074001d01160440d00809c4070308990308050010b0341011642d001403005a0801031109024903807d0000d004940c0c00750080f942440c103140c40c0c855480c14100d0000741426030480886024501590240f191a40d000850550020300600581884000c03030404030302401075640311504090010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 197683120 1250 197681870 197681873
    0x1b03040b07030e010f091a0d051501090e0402010804060207080c010509031806070c1a0c0a1506061b0303022b0b1c0503030a090f06020307090306050604022701020a0f 73
    0x1034005014103402521042c0d00d9140c1040115481d10b0940398120003d129088100b00d500a5140c605480b18510100a410410341c225490100d400803540c81041100c040403110065030040c00000251181090600451800382c0020b4408480504000e14079580068035106114000041c0c0c0c02880046000707110740d00301005010781e0383c0c0005a07140d07410000ca01c0c20202034036090301118015075000b000d05030301074501000202d143d54020349962075001c00700280c03000f1404c140a2600c40b00d201c2e6481c21a020007148241e000c0301c44607000b010a0004160f921198045560720003d40c003a4103180269035800d940c081c5003400754081002c2013804000c044c00b0404e00b40c29070044d000501050340d01040861070905100c100d00c0c08444068125001000468038140254014409043c0500411552100705903110380c201c0c2d104a991000080120306c09204100c042d024043e00700104540075414294130b00000d10441040000480c00c2c0c11201c82c15208030f9000781300048484d030700074204d440b940e80a0b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 197684370 1250 197683120 197683139
    0x171b0703090b2a0f100207060e06090d030501050a0b0d0e12040f0e0604020f07110d021305090d1d06090a120305040312091a130e0a06060905030105090a081b0304 71
    0x21a40f10311040707591030703560054845000440c0c5190310460802401d0040c00350020900070350004c1c1040da25252100f8495249d840100304490042001e02c0003043c0350440200024200c0e101a04040d22512101c04104240000700c000e4860341070381c0800014900300f408102d64545810141914110003001c10002600f9019904003000c07541484089030042d902d00040000b02d114200040c005d10b103043c00071002044200d0042c2c038005001801003001e41c0f0280c2c0010384d40031814503052000d16100c41c1040041c21060000002c1c28000c5d05281c03190b101740e0400c84142c980341c000d86a02a25010400740c0450750f446400c2c400412903403c018541c40103034280240640c0c41800159050681008440462449100b07000308031600310800b0b2150700102555040140c0c40b01a11400742c030403515000c101d40403c00311050280140d00b030005040e80c502603000e0301c081003642c0413500c03c3e40362804019940fa400b1a695010035406072140d5512100100c070300d28541c0307400c00340307035094480401e001c240c0a28 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 197685620 1250 197684370 197684407
    0x5040303030609061a03070c1a07020c010c02010807050d061802040819050d08090a0c0611151501052209091505060a03061a04050c0307171b0703090b 66
    0xa50303001c0c00956100c603c0710040d5882403050005078200100b42d9036649501c0c1014640010941c60240303c0c4004584072854440045c0c003030380c50082d001109101d16207404010400b140d40302030074071000c494120340000e0049a0f00505c1c031814080300081d20b030b10b5242180d02243c090880f9080055000091a101368025002800f60100f01d209001c261400e07440352100f620044c41d13004c401000030250840c81100c1c0904094446481032180f00900000250034840580203443c4a43d03c0c00148610030895614102d05486000081429681030144c0400d6980d90401083e80a0178142e50781d0442c601c1040185529008641040018000100301c04400c1c0c3c111810b11402095601400060440440100c0e4025070790550b00540fa050200b0009003243c1124050071205941585c4029400010070140e482c00ca030300c146008400010000389030340001e4800d40c0041003602030103483c41c4c24401c0010308105145807041440c4c0c049601400c1500c1510240301601014140b9602d480c555401103803142d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 197686870 1250 197685620 197685623
    0x61915080d1709120717070b0702120705191a07080901050105010e010c02011409030a0501020301030b0901090317060d06020a050703020c12030405012001062c040201211506050403 79
    0x1201e4448142d000c0320094280b50240ca220800352460301490001901c840d0721891040300c41e40712054141c12100c0c0e07408082c00009001d21105070a0b80781c0810000d007412180001100044c000384005c03000305c1c45c00100074600400d20361650007600c49500704400340c2d070314425141e110500c0e02e0f001c0024242d408004240907007814402404242d80354401560b481c41d204180600280c42d01d0204800342d803003460701d40300c200b052988803442c1501460102e070800320b28240a481982d0004010420800070805040c1c2c4082010000c02035000c240e0780c0103040b40c0300c5251500c0b0492141002c030f0241d17502d420304c01075102d511900840d510480d050740a003c03030f04007000030750143c02078207104001414803002e003d034208819006180f5047c00c14005441d0002410100e89502c5002d54440c284c41e4400d204060240285400c80301c3c10000c0c58400381d0381c7d980950407030303440d80c01307104144001030760400001d8102c1903501d44000401000c4c6c8122000400700e0203c80320500b0f0044100107031080d0410010070642c1e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 197688120 1250 197686870 197686877
    0xc091505040506030f0a0609020c030c100203041a09100212012d0501030c09050402041e081219110d12150e060120010203010f05041d061915080d 64
    0x2406118162601d02a40c815103800c5841080001c45074900d40054561000890000191664a0b01d40c07800813608160501d0055602c00203002c9010481040340d448800e5144100707510b10318095803284164480b000d00c548000b0072180118003607a4091001c0201c60711002c2046407548003080346034011100c01e224220126030001d42c0700e400b8030054400000341d62075511040b034901d4600030045000303080c1d0340011420404100c40c08151070351f90780000c100400e1300c855042c1d02070005120000761500b40c0e0380f01158a6022a8400c102c0e900c02d2029038100300800c0503090707002881c2d0707442a1454044198403811a001d000e0340c1c194100c0c0c1001400354180c0095108110001100c800844400d0442c012405a41054000210958411400c02600c811814511a8030755500155242a0f030000e170402d0000c0c0340300c034409000350300b414420707000b00c02c0c03c5006003a4141c6040442c5902c1c0c04000d000e0f01c411400305401005202106e4000500c3c0019444001c2c45030b603602d04405890b09a40091b00001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 197689370 1250 197688120 197688149
    0x6030c040e15010e1c020108061504030503040f050d0302070e130f0605090c03010b0102070308030703090b0a20070201050315210303090105090a031b03030f0f0f0c0f09050904020f040c09 82
    0x5a0400d60b00c416139400c5c681080d40e280c124250010f5590410040105510100500301700d0801c5045c080508005c51080004640310703820062040c00c10f0707003541c004501408100e442c03440400d03030005455003140c148020a058541b5894085801c02c2c84011740a0020300e15107020200708201c41d8095032141d0030001c1a1000b040c40720082509a503009004280140d1002000384081051000119000012800c0000b00107106594501c0c55240441305829260f41d80c24800d0741c9602100c080e18161000b012401c1d280100c1540083c20500004e080300e4408880b005400603030342c845c401044510700803d80003060070300c41108200c1d83d03944111100102d030750a040203d100320740700103012a0303010f5044e2150070320514640c0d2428034100078100180e01300340e12007000081d0104607200d44d0700494040c41d40811f102e5108207500e0160707134400000104201c038208042c00000e40c44142c480949904942c3c007000354480d80005850040d040d5034003640039243c5480708403001e401c05124011200c00c41ea10381c92 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 197690620 1250 197689370 197689397
    0x60109020405150d0b090f161418040605060301090603020a0504020705120c01020405190302041514040e010f1a09010b0712030e1e100b0405090c06030c040e1501 71
    0x10390180d40b00d01c80d000302d202c02010800d40d003000d01034080c94210040029014102d2000910a080c0907210541c04485100a004000340403d005003080e1140d8100300e0249001c80419001e14450311042100d00420708884822680e50354000798000d01d40281a641c99507142c400c1035008012a2200724480d0a022100044900f054020b4a580ba03401001a00c07919542c01174150080d448404210b025560800c000f2519940d10b11030800c004043d0300c140c0150343c2c214410301c0115081c10f452444c0e0b0104008003000962181319540800c581c041e500030030818864240329014261080079140520706141e449a80c0b00a102052a0021021207501942d642e842d1a241410710a070308001e001240940440034415001b60040420702c0030f8602200d01c5060590f40800100141c5540b00b123550300034400a180c0c0322854001ca80c4003107000c072000c00250400030b81c0d031640c40d145100041d024803808030001d044201404281c07401000308040340c681c5407900c0048102800205445c25000c40c100100409 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 197691870 1250 197690620 197690639
    0x30603100911150c0d09090c02012a02010e03041206110a12050402060c010203090a0c1d1f0510050703020d0305070e040b04060803070f0c140904060506010e04020415020601 76
    0x40301e0a07000120620990340c0e10080c450307819040c080e9458201000c10024400c074008020070305505105039560600c060809040500b91070948666a046a0401c1d04074010001e4842012440d0b8805640c2c3c03c03a84000c0c600c080e4054484542d014a1a020100700010741901242e840c401d40c80c8503040422600c09034295021301401401c1401002802d191064a44525140c1c003503608140010300ba1401c0c043c40034055801d9900413100030569411101000e0104440303600550040e02e801002c0424078143c80d41c1680131100300800f8204042c202e02460140400000c1852014000103040c00b8080e100000f0043c0065015007005c40040c07041c030036414052031003842030074018141b90742ca20710b19103550f00801c009052100c2c000f66206030b41d1a070004042008100901c185071213034409120700c180038141100c868445901c262100c507083d800043d540e81c0da100620381d03c142e11a0700000c05895450040340c1180301500d5050300319200040105194228460804840131643e0841e44a82c0e00c814055 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 197693120 1250 197691870 197691881
    0xf06030903080f090307141e0d0c08030a0603020a08061b09130b031006060314061519020a051203011e080d0c020d06050a0c0909020c031225020303060310 68
    0x280000748041c010409003c840d08003a0342040d0302c1d0040741c0c2001001d46603000c0d103401a4410b076a6030f0b80049051300d050340d0040303100c0c2011900e102c0078148115882c00060410400d156000701b00d414000b002a0003005180c0c481c07030285802420000301103441e0b50341d9a40d00e40307040d01c04e107011003035207403031103400a11940c03c440b9000c201801c190601c001c03031a41c0c000588010b49100d0340c58040d529402d08807040346d125081c000c2501e583c0118141a015807061003001010701040e010303001040548102590010890701b000d48400103000c80e01612800403070420154541c01015406856070f00440490018040d506851071011030000682401c0000f074039600c2d1611038895142c05c4205030100c1b1901690b03034624040d0014010548460043c3d0b036404c200c460840784007085030f41e2428040c0320030b5402083c00000d4465840110714040d0308804082d6a0702900e94090510001c403000245440b030040e814101141940740400b015940001d80691241c00c2100c0e00e0f8085e11a00300002424445030081 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 197694370 1250 197693120 197693123
    0x607051b0105130b09010e0d09300803061f0f0e030c0a030b0c1e040303030b0d0c09150521010506060403230a050708070801050109230402031c03060f060309 69
    0xf4900c900c2c6540341424100000c041d145c40707560381d4080ba680c00c04144905840289070b552001c41d06400c00401094500040c400c40703170412004441c9030300701603109007502c0b80307a0b801c40d500e2500c0765220800a07042c1105284c5c0c15031000c2e07142807800c0825402000d07003c1208441d03200c10101440b01d606242c0d454003c01502a84040320780d00802c00b14248c1e41d4184d07000007200e20518074000c00d0065200100181d19480d98131913900060030014550315129160321a070084a0791603a85190380c40b5a48980038900503402015581e43c40210703401c01100d030321001481c01070080c076043c03161000490311403105502c884c0540c0d4208000039905140000440d42540d0740450045000b100d0701e40c00c013042c003620b450515168860f920380f080124100f0066000140030032001000e541d41007410781400d4480c103900c02c0c2c04d81818481e00000c1307a40c0307031102d010700750401d4004203e059880d8000a4646a81c0303034102006854802607900d0b005074550050000e85000f41212036210740d84110480496116900 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 197695620 1250 197694370 197694391
    0x3130b07050a0b090705030d050c07060f0203180d120c05010f023105120601030606090b06070201030b010309060e210703230d050a0204150207081b120607051b0105 72
    0xc0d25800540c2e5003c446801142d0601210559a15107000c82e14121a000b94030012900c041501e01020700b007044050040c180616156004d002054406035890141d03214410081d00903141070203c540f13510115094994101c0000745861403500000f07020142c00300d00c25500381d420310316003004c0140c440c000c0719220480e42c2100110030f42c0700c40500e003840351048a040c01d100e00203c40048c41e030b5140301040c85e444005902502441d49103140c42c004a90440c0d0090740c1150500c50001d034030703549420035180c24036020700300426800d40e141c004074010110314500038681c0b4130348400300364581000600e01d2000a12104000c1d145030050074800c844d401010001400a1101c5c15240ca000d0614515154030307400c802c100d241024140402542a41c0c0c04650000303d66502080c200110003490542c24a030075240d0000d800f03140c4c240340744c0759280ea420800c1c2c0c09030358043c880106825101c3d04030201e03d002502c1d042e94094100313048014403c0d4085610924a690b151031444210841803080344c2c092649202c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 197696870 1250 197695620 197695633
    0x3051807151803140f1c0507230f070602120f040311061603020307060b060c0601090209030f03070b010602060f0f0f04031b05070302030d05040b0909090c060c03130b0705 75
    0x8411a000e100c00030302d0b40765110030210b001000501020f00e0900e43c138114400740c0220812007020b50700c1c0041b4000c5031b903540151080440c04507074219048501494002e604074009441e49800e001e10842a0b106c529203074492075500344a001000310fa44010356806074251091641c00f074646c48004d0040595401c1074907000c02c400c20024210341548007500c27002074429400d102000300314042c0c6e80403102c03060300540c0001aa2208001c824440e005a2003000c8034002d0800011000c991b5840b03105000d08610650300040c507080c940e804010101010f0203502c01c80755074915515090380a5034080c401c040151003890049000e0007668541180300d12041c5c000f800042d640c442d003030b0484240c060800c2e424030181005503005210449030305402217014500818103546507105040ca84240e015580b010420103010900400c3c072181c00301d80091004480300c4500303442e40030105041909060600741d01c0180013418114440c0d010000c0c1051100316090344c443c1a66880c04000140310f0304900504503000300c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 197698120 1250 197696870 197696909
    0x100c170a051c0905101b0c0f03030c11030a0203040e01080705100c0303020909010e0411060306060a0e19180f06061403270c04180308130302030d02030703051807 71
    0x210011122440311a0740820800f1958603410b0809603507000c201c0005498215406001225071100364180307849190910f45c80e400ca807640784040a0426000342055107915990003200d118066903004a418001a02e55035001d049010f0b6980d441403040801d4100c0329800050b19003000b04802003200d001414800711041410001c54105800240443c24580d00f44060702050300c82201280c042c09803049620b68605007800c014411101c101e07001d61040303000300300700185074458000751030301501d03181800c504500c0c60000040b08022401c3c0000b41114098000143c022072580b641c2c007200307004410400140508c00210b2050360554042c1c100407821002d00f00101c1014900155401040500490010360030f480f10301c10441100c0c002c461440d0701620851545103070500c100c0d60208208214940e0072504d03030380c0c0942141c000501c50180e003219020060117241c001d1088802c01080040c085559144c4444054000c003070648998018641c0c40903000b46090740014483c0c1601c0d00e0194009124024 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 197699370 1250 197698120 197698147
    0x50f030a0308040c090504230601050609060d180303050f070512011505070f12030c0809101107050609061501030e1002030c070b01140411070305070201030f0902100c170a05 76
    0x9481103e140d442c04d0800980340c0d06510030140101d104c1c11a02d011030110071a80f2241c2e81e1402d90300c032a5a0041c9004000540c1c0d4001100c0c00220103445032911048045100ca00510405c0404848800e00e025080b040640c140d006612516503020540d040f17071103a4008560500501514420680c1c1c1280140305e0364528010513144504145052450031400e40c2d41c1c1d4400030800c100450310040d4001c220b00740c841e094050003030300214502e00954a440c01c2a110340d61a54400301c02c40c25039580340c0c081201c040f146012101125000011220300c0e081540e1300940e2a0350480e0828110030682012001d00e40c464025504140048402403694051a00e0710500a500240c49000300c00313410000c14000544006845000349000300361803331210041001d100641d0f2111004003c401d004000501c0044e030000305542903aa028070b80000d1141c888032950004210002d8069448501c3c41045c0103400d03401000310400300e2040c20503084200b1449980d24860085030520380111b0400d010486c4070109 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 197700620 1250 197699370 197699387
    0x3031b03040f12030c03110a0c060c0216080f12030f04030806031c0e030115030507030813170d030b06040609050609031c08090c100e0402160c061206050f030a03 71
    0x182407040c61958550f03145010110031642c1a0042034a844401ca8044d030140300d43c1d1001c64241c0c0c050717450300e448158001c02c0302c80c072108020080360b62562050a0f080c820080c03504558811030000c84000d80340d03c005951804041c0130880380c0d1103243c2c4200031000208050303070302880000105010079150b66a0583d10910000c1c03403a41c040c03103440480c2d0a81d4050400c904161a859200c1c6c0c01c00e07440c50800e150075181302958620781c0ca04000c10400000d4000544d2804807030300160b1880e200d0301c240340101c00f24201a800052802217940700c1803081603000c01c0c5016082038035101000302842640c00d00185000d50301c6401d01045076001d0820940c105803000f0100e04d08005d056540001035181e1150428035021110800510107900b04204013800304450200c0074004c4030806d10700ea414180003001004030714496800b40fa00400d80321402484040c034803180a6112405540f65034817140c0040c64005000d105156103814a5400260350134a86100320b00380c0005806172038a942680c030161410030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 197701870 1250 197700620 197700623
    0xb0306040b04110f1201080d0206010303080a091b05090708060307170a0c14010206010801051b0a05091e01230a0f090f03030801050909010b0a2601022a03031b0304 72
    0x252510850b00302c034200000141007404d0444280c903103c0310f90322400000031405820140e1300343d001100803581260005603460440790305143c0011039a480e540f1543c050241c9520040c03e0415106a207071a0f0f002410340042520025920044240e5441900b281e01c500d056600c640c00d600180320500040d0760800360000c062500f0400c45518585580e152039080400d036002440c1406094800d0803a0f40c4c1c180f084600402c5c510009000780c1c141500d0300c00e2440c132901c240741000400011610384060090060303460800c0b0080c510125400182e0100840314449118030340050b46691120365003043c50040c0241807107a007801700d070401d0072000d401c0e03d08440380d07030b2031901b4455010800101c465411251a0140d072099036802e88951410007401080c4001030038101c5182d0526800343c07190303229044418100c4e4400d807c9080030700002c01056100740b000c100c0b20f12840d400000d00520f442caa40700b00030302c0921480d001d891600c8841c80f0b00b60304d9000c2500c2c040c40364071242c0040d00030030812038040c50300305 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 197703120 1250 197701870 197701879
    0x70b041d13120e150f03090606010c0b01150e03060f0603070603021321020604090c12090515040606090606020c0a06020a0c0b0d15060c030206150f060c12040b04140303040b0306040b 80
    0x2114013510344080350072009039800d410f0301c00020070001503401e100c0c4540000c0c0a0900009a2109035940496500140101542d802162100c1400c5611500c00d5140c44100a803d440d4181013001080301000d00c101c071468000d02c113240000603100c0c803074801c80d482d00d0412113605400504010005200424490000c9200c0340704001032805030341d40c1402000200820f18001641680301e8034083c0040b0351184078242158544601500420808200c09042d041065100142e0b0f0713640d850640000c004a40082c50424a0300da40459125000035200103008804c4400e0207019a5400741240d6800400390010142441c0407020865054110060070780e01c910001c021a10402c1700d00000d001d0480d0307504c00c20008500e2816403080c550184040303504030108000000c2d90400001c003040324104900820741c01b41400060020b04030740d052001001810040c40181e54459545100c581c0640190040d04115414030340c1b10034251600004030b0f000c545003190600e0031980c0d1081004010031444864a410 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 197704370 1250 197703120 197703139
    0x130c050f0607031809060b030702010b091504020a020a21172a04030f030f0e180c09010c050a1103060a0605030c0105090315180705040e060c0c070b041d13120e 70
    0xc0b05c0300c1d401903030080e0504408a41e124500603d0003402d40300300c0e20b4618000c0f0028014440300804440c0180300c4031105440c0940c3da1086110124a011b9660201a0100604c0800c0000c4810b4101d911108500c2a03951502850b42c0c401040e4107030101541d80c01100004681802d80b4a030040380c0c4403035052030b1101d002c1d040640d00d1b140c88151804d0504120000341c101e0581d800d041e40c101401940f00300f030030b5030150071085030100c108a603494090b01181e00048041201d400981c1b04a0f0300c0c50600354010b05540b050001841c02c0040b000b0075009041c400c1c0241c8000405614452244404803800200204501d40101c00152100d6001e54043d43d05405024000b0145143e07110203140180c05100c0d00c56505044900d40034102041900081d10880c10544007000840c030008566030030013140c403040c40e0740b00f85030607481c3d181180940c8404030001c0e02140000700f07001c592400d00181c0e040407100e42559519040101c44191410700003c100f500703d440810310b0300344213803d80c4c1410701014084204 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 197705620 1250 197704370 197704379
    0x120a0809030403052506110703030e12010f0203090f0628020403060e0601080706021519090b1302040b01030b1807020c1e030c040c05120901020f03130c050f06070318 73
    0x18803855042c5c0e410140841040b071141200e441803080000e00075442e0070820b07c4202034146484044920024003000a0603c0100c4680e940f4030701041c6440006008000d160062403025000e504102e4001c20140a0036200718500200440ca507881040c40c0c213454401000e070b086600d00300c00000c200d0000b009509000100010304984900035001203038000800141d032501001310300c0c191464100808540024a16058000c0d0112a0701e070011140d42081030f54a401950b80402011569009445c0d0f441203000e1110407850540e02d1321070680240e80c00d00000c2100b9005600b500c052861080c2c100a142c903402c1400000d0107042c60308642c6610585010711058000911014000f442107074403407210000850540c03608001030700c40c00c142507500340301e0714020b048090f005024480100308640a4140003942c034220a40c111540f51614640c01a00e900780901344180c8401c0c1900c04a5a000030441c010902e0300d05440500311150307000300580d292203400e41c1c2c2110350860380401001055520b180c00714 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 197706870 1250 197705620 197705623
    0x61213060c0206250e01050d0b1909180819031d0c03010f060f050d0516090b03060a0501270b090405010e10021305010305070203120f0711120a080903040305 69
    0x22008480350707004001c1070500313219411044641d4024070300d07409100000c003082180c10802c1c0c0c070280002428183c0d1100301e004c4c200e40240101080741903001100c00a910344200040924009035100b41d2009c0002c04030074640540ca2000922016150900a120b50200c00c1640749130402a10101e10700420064185c01d0941c403081c03041d0f01391408035044905407034800d0038244100108a052101e050000500e0b08002d102540d141d0300580b401000c1e52200c01c4148a02040142e0100c419447d40100007a0346102010007415541d0106119000d0440810b034035904500420b4180c0d1030703002d90548001403051442228034640020022100e449600d4081c03996144601148110300840001c5489440b84924504002d101031103010b165106100407080c0d04401480141611800e080019041d10740c520309070b107180221001600061400c000f0498524108003840d4080c0b011500d80c00d080c04242500a03450301194451042031003014401c07469075601c5400c281340c004903010190382c9441c0d201d03242c9a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 197708120 1250 197706870 197706881
    0x90501140a1401050f0f030f033004031d040908120901050609010e04060507030e100c03060b040605070f020d12030c08150618040f020c010f0b06070206121306 70
    0x109251031800d0401501581c07038029140000489065990300b58100b5000a8840f41c6207041c02c0d000c5c0c0c0380300d4502d4070342e0f8a0800140c03e002880008880d251a00301c6034040c000144a140c1c0781e4040040b0308107811a07c0c034002c0d41c9e802980c0c181c0391100440d6030305407000b075104103500a1640c080e0322042c41d0400f080c5000010f00c200c40c0c0360380400a592806600ba142510009400302d4080c0070108010400b0410801d845030b0080e501c410007069503100c081046014180d10b040004003070040c40c280e00f0102c010f583c0403070703491b448a4805210b1f00b90b54628203003050066200c3c21010480410101c4d0008014180c186015480203003603408030203107902c07400b404080505164010076a58200c40d044207030443d400e00c2d805000041d60020035844240812802e0190488582c0c1507040070202d90345e265070700c0d0401c0c1c400c03001203c021901c4d0004d040c0c04a0191488003240804907140980315202810083c0440d42265009010a4604540402d4a4501c000010a505510380c0c017203010900050381801407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 197709370 1250 197708120 197708141
    0x150e061b07051206192306040b0904080706020c0c040509030307140a02280516080601090908071202070810061d1302010f03141320030601060e15040303110d020c01080c0d090501 78
    0x11b5418034122044c4403c440111202c1c0d441401000c040000045054046600240d480400503031580030b941c1e181490040345841940c1d02c981000100158488000302541c454551940d60200b69110310326544840d01c144d004801c0107800004816544001d000d600455410100051040441d0a81c40c3c450505449454141d250341ca020020420060304001843c0509046101008030912176581c4803114813400e0402042030000d4210005c4036802804128001c0c54400b040d1540041e0107480c00c402001c160040c1180c0c01c01c40d1a1801c4050341c1c034120140700304006451000500031540040d01c001c80000010b10815440b10b40611400c540040254045e1714058244080d02150f80740280d003410640c0e02180405d40c511a0031850350b5000101c0d90b046403450300300007403441085404198100e28409880f4100c4500003000400c26600c000a0301c0c00c00c0711301c001d4601c50f403182c2d0300490311020350150f011b001803840340104070280c1d6040e00801408031100c9000840c82c0d0550790b0750b42540d008105 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 197710620 1250 197709370 197709431
    0xf081303020a0b0a021e031308060702160b040603020c03130324052a040504090c0e1f14011b0f0605100e01150e061b0705120619 57
    0x6042046082c400201000340440d004080c0c140540503134000e43d600807001d12000c030480d81103d05046820b0a000b2140d680d1110341061800c56150440c940d5900015541c10005100d03203212003c4484005000310309a804000c0000c0c03401d403408900f24080c1d080100642242d000421001c24194240c4151400031481100f100e45244040241c420815041d205002140350400081240c8420701907001c804040104000c403822000c0c0041810980c021a040560854500250b400c14001c010740e8610032261055001d1441c0d540d00c05c8130b820b25900407404100c540d0003602c010721090559a4407440c1da05c0043c9000e5100690792a103e0304501c028140031740b8680001c4403504280324107801001d6100c42d050903031001c524640580381172404014031541d00c242640000c0050350911441c9101c010f102c1c02044180c4400e4000e00c0c05064981d44480100c082c032070b0b00c00026507400c10809c0e040a00000030040c003155624071182602d1179160900791104c4540d200c02c5016901054030740c42e02d41800910 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 197711870 1250 197710620 197710657
    0x1603030f08010611061303021f05060301060501020c1008040515010611070e010f09021e04080f06010e070c120905040e01020903010f0213050d0c030507030303020c15090c010c0f08 79
    0x1200904041c0301a00240100410a8010f10040c4000512981c010503992940440c910030340c2070803410030401c8045041c040282404c0c0e548101d0880c5c00107401610110000c004065845006a81d140b812040094018041101401000d8000da80c1c40c1d81c480d00520a603012030f0200400e400300490300b6045040441c0c0d000c205560960000c01c038040142c0713040d8440d80e1242d41005c130503880303a5400b8841c2d11a41500040c001001c04610b040c20700410f00a00c04241d1103c1e1a04a901c1d00c1d01d04100700c10301c5a200b5034000203000856842c1440c0079a140303480c3d911a940194581200d03000d8050700140910220510014103500c43e48078001790040c03070500042c2c5901d454410142940c1c0030728080dd1117540107120207405499041904422142c080740d8400c526070445c900300b0048504d960002d481802642000400d25400d50000c03d4105c00c0101503504400141c1d0441042e50000d8034051101d502c0a1403500580d4051340c00200c6550156548200b606141c0c0c1d030300b940d198060706014000b9003008 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 197713120 1250 197711870 197711897
    0x270106030f0b0904170705010b09010b19020a0201050706020a20010506010f02060415021b0304180606113003100f0503060c0d02030703140405071a04080703080309160303 75
    0x5100b482d407903600843e240c4203141040e03200d41d001c00c0714030803620003203050025124040282c00d40c81000c2e84072010f0f00b0aa410341c2d44007104a0076400042d82040402d5200300582c070714510106000c29101d505840303490600d001500c9038402500041e8481c024041031003002e04556001c140e0395403d2241c16400400c00f8909400010560b0904030f00c0383e070940d40b01034140400a807080c0e22070700c40010003540040e140c510502040d83c0514104460100d00c1c0400070b008107031401d4035603d0240c1c000c4084000d00800341d5500084030348000141c20118103401a1200341e5034040503080c140070040000c82d0110355855924501c0d880c90727000352800407401e28020000c0003a114060124001030070214040c03c00380c5400303480b0103ea0f210300820010f90690000000311501c0c001c1d8800d00c0c81081042520302c95107401d140ca183d94107000d0146c402d5111043c240a00c1e820039501c01c5805441410010b8480d0301d00e5581d0362a00d6401c0507020100c50702407401d407101d03210242c0d89960001c500950f2a000c0141c240d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 197714370 1250 197713120 197713151
    0x31902040c020a0f0602090316030507080607050a0c06050603030409110405090906071e18080c04150f06081506030702150c070c060516141e010501050f27010603 71
    0x410141d0010b641000b02c11002080f48600c440184c950052009a56030348040c0000e4103107010b010040c40c001245031004000c2c428001030a0040d280f80d04110740482d01c4a200503a41c0380640740e49000003959803a410000a0003542200c0d0704050043c0c00c0303904142e11488484169900140201d440640219042129151464281d900030400002800311030405000082c03041480f201140c40c140c909081c1410b1043c490350031410b4854800f010041203c1d107a42034070351280925075203544224145000f0160200d80350414404442c1e030110318010035850160180c03030b0010010900000c04028528084203070315003100941c4a8415035001d4a0740d058a000c40504815003e050024120824015000061105800e10301038500e94142981c8901c00c1d0441c034201040500301c010058409403540282c2d00c0c1c4000382040c0d045d08030b0790350ba010202440031002c5c201c641c01d1190740c0d80300e40401807448040c00e02050f801692040390848200315409980741d90003440307003a880200041d42e01c4501c010704045 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 197715620 1250 197714370 197714381
    0x1704080f06061027050904110108160228021009030314070c03030c080d0603260315061b0106030f150213180213030b010801110a1b0c030203190204 65
    0x102ca14981d50310004400520744810103001403a035042e84c844182d11181c1c0e40031000000c0000070480c40c03003840c4c20f20780216105140413456000c61605400704148640070480800710755199030003130003c0108113820802c54004d0300c02e1300326a204818805400b41e2200c1206100c500b5158442203003640c80c43c980103111401c000480c502c00c0d0b100f485074a0000d484018040c04403500b5140282d240c10b04c500b8128001d00c10705850042d2149080400010481700714064040150700c070088000b441c80d1603000308450711080720450b0620509030009840b03032401c5406088005680004043d5030350540c5416421920340350411f45000030150307180010440e0114005c01c5140c1001c105604005001c02c90703020001c1a0b000d55500c0d0740c5828100c181e5440f482e4181d9403078660340c0c0b03010b81a0030b5980c2007440d0200300038010840c955080c1813508281c00402800c56581a420390781e02c10340d8942e40041c0141c0084490011212141111b10000143c0d41c03c0040c0940001c0700c1c4240e0007503030403e104100460f00c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 197716870 1250 197715620 197715631
    0x1090911090c0403120e0909010515041109191703030114011106060f011209060221060a1203030f0c02011a040b0a05040506030708150a05010911030606071704080f06 73
    0x744240300704861140c00d81c041d101140d510200511030002c1c000001da40c01085030a1a98202d80031034100408106c054001500500640070022003032501c13241400280d030b00b11403d020748098100541d6401e420980e071202e4180030803403408000c0d152140080d402549266056105a078400301c014440003099043c45c801400f82428010b6441d601450f2482c0c80b003400401003841030b0403a20155142d41d00030b245000d03020207a00803c0003d41e20501c0e000c0020341006400c500091004018000d9070158070b01071600903d001021507090301c0c5001e24422032038500030300c1101015214108103c9054140c0070b20400031009130001701c1c1301c0200804100064a40a40e980c0c440c60410b000502581c84104912040d6441524003103002e9072100040f80c581b038280d40c0a00007500c2201241416144c5042c0403d0241c582c003030301031246076610b402e0041991880030800c011481c04002249461610f0401007404512554010b032801e1007000c41824076400c00ea20018480d000400700c0c0001410a010075039008 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 197718120 1250 197716870 197716879
    0x70806010b131e1701020c010b120304180b040204060e1f0906030c090b07030302070c0e100e04051c050c15090604030e06070f060b1003021e0904090203030301090911 73
    0x900100001c40e180001032240507a4066188030104103d42000d4602c0c000d003102610070004d1004030103c0d43d000b5408003810f05940c3d483c3c00d12200031450121b10758880f40744184003c60400d4140161600e007412031040084500d981c9149000c256121400548010140340d11840302c0c010307410060004411544c0e02e62035106c422402807034116504458800150303561450001038482d42940304bd00c10303a441d90403504580b80d000c6444404c056060b0010b2040d41d01ca40f0049d010b8583d00e55030300036440416145000e2000c1512428844121104640c45c0e105019008581300241c0110358241460303002d40e141800600c001582082c1898208090007409003c07180d070307554901d018641c5c03507114003001d0001001c110084009505560b983c20590300f05640010907642185444c1c5095402032040102d42d5004041441c42c00c03911034002d10079508490403411894203142031801c002901c60344610080d80c4d0040e541c0d080a030140c0c404001442c0a421058400583c00c111400c000110460070f0080c903104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 197719370 1250 197718120 197718127
    0xe01080303060a23030307050102040503070f0e01060309082a0f0a0b060904030314070c1205090f040510080102311a2b0b0108060a26010b040905070806010b 69
    0x194580d6881d0303600300ca0302e01c0c0ba0030840540642113103100d0401920403a85c10b01c0007003003400c240074065000b00215041107003142c0a640da9415802c0031040944075200d8240480b10040200b00c0c002e400c041c01142c4216401c919004000c03d91191840c01040e240d01c1ca0310400003a206074130300c10004130030300005000c000c01c00443c45960300412030304010320f800d00900d10789021504040c02600620440c949100e14580207103440308005003150103400c400e030741298041d111803102c14020f00c2207510094000d00152540d100410900c0044c0030003800d8190701a9404000064a02017071000d04640d02c00e501403004211000180c45005680ba054100300307050b89600c080250744031045850300202c6200800f207445442c02902244840c8290000f840900d800e00304d2413418152590150404000c00d0300c60040a88654003400038000190089011000e40303000c140091140c02c3d005601c5100c5a1400410506c10f4500400c0580c0d250070400c80305548400d5080c03002160038065603000d03102d81e5203e9803e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 197720620 1250 197719370 197719381
    0x20316050f060714071104270b0c03040b0604090c0302030706050403110303030705220e0708010815090c0d020a03052409150402040b030f0f0304090606051810170c03010e01080303 79
    0x9101701403004081c001e0310048040c003601c40b40c00035948010081e906c0301174140314506480b01d4a00020301114001852030000b40034464803402c1e640140e80200000c0c03080c0d59a4003e1000820a64806880d041c006a90000050f9401c0104202412090740d809031554610f15207a036001114000e19480b9070401d00c10001c0003503110040e901861101000c040401aa00004061800868222018004131101008003c941150000f0704031020401141ea041400a10601c408401a0f0b102010354002e401403042a1a0213154001d031140010f00031080a41d6a507501450048140e02b2050041d124007c00c9004c1c450f051195580000c1910107008100d03a071602c0300c0078001000f80000c0c0b18030342d941c4161101f518100042a5541c1031701040791071103c14141e069680c0d030401d1290307100403414401c011842920480a540001c2031143c07540b60b07442c800c41d0030060500003d11181c1e0800c0100c14080b000100c88001e02400307214442d030b0b40760381c030350400c0945881c1d8841600240400c1c0e000300113000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 197721870 1250 197720620 197720657
    0x209070f0e15090d020112181104050403080f090f070806060f010c0807080d0f1a0a0807080a1218030f0506060d030503060904060609140a0501060809030f030601020316050f0607 78
    0x1040302d10200c13a46101c10500d880140e65500c109000c10002600d86121060100a241044d861041c0540d600300054800c0a04000c181d0304100c2e0010009203003030002c549100d019080c0e0b15000310700708090f20050118402c62901d06410780d800901030750302600500417035040c0401e4100b180030302803078403a1003100207454030150b501c03e54030b0041020b580014603540348e40711680091100c03410b03010709010740303240004110040251800365a105a030f449800091001e400281403003283c444001030407408070962117042c100125030003800244031920b0455554016200d03450707006148541c81550440300e060401700d1070008000c200501603a400120013002c241c100043d00d40c441c6041314106c42e01d9a0700d1510501a0007140e1180c060903082c0303075044003600c0b000001030b407045401c04001c20441e81e07940b104681407002a034415a0a40007000300403508031180c001180d0012040c01100c0c03a2a070010440b038400c02c20380784140ea041c2c0003002c8201080009010440d04200c40e441d100c5c4180b00f800c1440c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 197723120 1250 197721870 197721877
    0x30d021f1b110309040513020108010512070b03040218190606080f040f02040e190203210f0a021c030203160c03050d020706110708070506130b040308130209070f0e15 73
    0x6020300805141c2d00452080401c11107100090203041400942003540c600c3c110700018442c102e01141aa100114440c207112400d00c01b20030103280105815464075864130300990024009a0300001c0c1031410301030100b50150401e01420f08203042103c0c604244450004840341a0001c80402070320f2018032001e00f103040c5c00150010307001046103221202c0c520005000300200c3c0248400360207410460523200b103150001c080d14074020740903640d01c00c03007101d00403030b00e040c1086110400f450103020016603807810a0183c200c0f41c0d014011507000f16116a80359081d0546c5c0c001040009070004100710925040d10700390f5001c001c013800d01d030794528034584e009441c40c06403220792050140e02003480c0c418841c007900b0548007044c50f0041e407903590446082c1106142d100c004113940c46e2048001041143d0818800044200c0d006400050103880d07980d01207601000c05001c04040c002515000005a90b85045050045406450381c140c3c850310320b14060041510508181d1080301d400300c01004150b440400c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 197724370 1250 197723120 197723171
    0x7051b090121050601150909020405060708031305100209011b020112022101030c06020f071404020f0d02190201060803121f030503040308041a0301081b010509030d021f 74
    0x11010103030301039465102510b224190182c01842084000181c10b005c04444904400a640d60b00310010349800b514030503445070740305098001c00304102c05008640f021025503041080c61941000c4448503845d01c601e8901c3e14061100e16035400103010003550f1300000c170340d00031031039100b0f401003038a0700c030307000a0840c8803418942c40f130031600010000000c1001030f00740d02400040500800c09035840782000d94500186008880140c451003106e0103904c2000955041143e21306054010301c207e494042c4000394000c556141d2042000348040c0c0308803105800a48000c1000c0380607014501c4045000a007940c845030302500580e0000c00c0383c445040c8035403070110380c0070000c0540c0c803202c014000c00f009103242440d03201034224000860080b040100110081c0100c0d0340d5040240b400088250f1395003103611007807185140551241d0320100f4542c59000d0440401c03c814100386050807408804281440352035484400181c0001d249180c44442c2c0e42c030030140800401c2c07004c2224894031070441580d80c46541c503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 197725620 1250 197724370 197724389
    0x9010b04290d05160f03050111041203030c090f091a043312080a08060307210606210204060816061b05011b0f020c0a0501050a0c1707051b0901 63
    0x82c070703400340241004022990580e6000e80741100390340e046004a050f19502048481e9400c0c80701e1403411103039050554003502c1c100210550551029030301940204400c036907010034050484c00005112503600c142a004059015010484814400600d40c18000326048144118540b5844603010950051003050801c100f0041245201c640051940840456403018080b0170032220b030101040071920141007000c1594985023150f856803010151504158060202c040b0741d5980103d0400d6141c01012003e035001d0840003807107544451180c804400c80054607100e0a4a4801c10011800c01d44581001804582c000e0b0074080e000314800390010680e48184802c00c5280e50000b0410310b5691198400d4036070110080080006c44c0b1144010b5107000100f80d804500496644241140085a900300b00035004002c2c0c645541420015240381d0000e0307007000308202c3d001600c50300046504001e03d0a4010412701c003510b424941c5001c43c5480e0984240c21400c20700d1410044d280d840e0480e8081c10743c0c1d510381 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 197726870 1250 197725620 197725639
    0xd0b10030e0714040b0603070c030f020c06030708190e011505011805061312060b01031b090b031003080d0501080606061806071103060a09031206030302191a09010b0429 74
    0xc0020007170448007154a500000002c18014038940040d04200b8542c0b0a4480d1810100e1054080e038540030000079540e0009070400010f0b940e248603e01041e841088061002895845804110100da42941124040d83c4d540c02101000c0502c02005030004d0609292000100c00300c80d90000680340c42e0300c2a1805090003248001d682e01c0d050303078602e01810940c0d0706c140c20340c20141800405400d07511000c5012901e031520200610211126680b0415019111000c0451804160122503840207051030300d4259280d90200000e1224070040c61034800c03010010455506050b02d950402c60042c1016105a80030000f00c40d1611224000581c076810407036900d0b407107210034240000401d03001107000b41d06000f20700c100152a1240e920250300360340603940d1074040c000b020004200701e83e0329000207000f681c421000c00c8100a41d811108030b0451203507440c400460010006c00310003440a4403101c0441e5100d015454543c14680310703c00c4419014124200101c815020100041e03403018842805024901c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 197728120 1250 197726870 197726909
    0x20406080607080609060d0302150405011b1701060f0207180f06180b090601170414060c190504031203051b040605071a06090601050d0e030d0b10030e07 67
    0x6511a000818050054503554500900700610416084034903d106040d05c0001c50528200108440d070781552540061100441400d014814601d00500031101592114030121010407a5030743d0070007900c00c41c0c45085162044040040580314160400020094200201c10f0a5030f8002040f00131900e0440c000036140c455882104080c04804802e407180c1c3c0e0030600e00240c1190780200600800d42c055a007001101d42c468104004058143e91040c001007080b0303401804000350700b15041d005442217445030b052140844130342d41040400c031800ca025040c08992450060a5035041c0a0722094500c3d00f645400d06540d2291840c400d400c1d81c41080541c0d0f0000607103104524588001c43c09005200181c940c0c0d59900014501da00200e01220207524840c01001200030010709503010b164018030402850b912803004403440c0e085070f9007050400da2140e040c209018402e01c01415060106080810781071510000c3c001c8280702984060105846e09031210155680400d2031010b44841084404101d0150b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 197729370 1250 197728120 197728129
    0x8070c1a091305280e060c040806070206060f130b090702010c02070f0e01030b060f0a0801050105040c030e070501030b03031201140f060304110f030a02180406060815070e1f0e031e0a020d02 83
    0x5c80144116407041c0818822801110307409002101c03014011074419668440e4201c4c0c640030140d480a82010550034041d0051800a00f84034041d000031000040340744000c0c0002d02000e0091b030780100540d540e000300c40300b203d1b814070801e409000d18041c040b1200740b4040e010303024190144000313047c0746115404180c0540d030b080f8000d400008000c0c1025040b584400e05a4001c100c01c0c4902c900c59458182603004444c0680210690740c07102c10b010f03014041c903090055010b40011424035904d8042004080302c0440c81b81e2003a0f010f04010b03091100d96452705030074410058070a46219200d103006104120004200c030340c13941c0c6190001d075200403940182c10f000c039282030303009540254002c030b203a41c10701180400e00203020311030b501130b2105101e03150341d5840041d260302c110168443c2903a60f04000818803409040e000000b0030000c2c0c41940840041194a0175010002070300400041c0305100f00074a5160030420090100c000340d01ca02c110421265201e581c441c2c546c68024001e80c221a442003d5554 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 197730620 1250 197729370 197729381
    0x3060915040b270105012121020c13020307021b0603041112010908090321030406020319020a0302071203051311180115030e010506010c08070c1a09130528 68
    0x42d0701c03003011400884200d00c58040d0101f4001d8062a0241000c401c44001300c0c0748481081c5038000d010300060400b20041c48030f16006038500d603c03c3d8821882000c240d0b849420715001c03410810031005072681040c010003410310511010000d084103c0180d0305c10306503903000c1101d420030b40c050500019101082c3c0454414010458610b40b15440c0c904513000340090f03400100710b0800200e054606454801c40740c000c0702c1008888a0070319a206000140005803143d0085070070201d000b203040d4022044040e0201643d04c0940314000003074000c903421081040280078040241d503d820180190315041c0c1d004001c1d90583c1d580646600003010f14440039884003010724041008020702041c0c2982c40e64280440c800350b4280307120000b8500071005100081c10b116150240c10140c3d205008403489840d40c0509401c80e1005651040205800161803508050b51900305040e451540d03446040380310810070706e241c2c01c182030000d050501c01007240b050f000c0220071041c85035001c40400b981d20345801c980010030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 197731870 1250 197730620 197730661
    0x10c0c050909010f0c021e07030302031b1606120c030e0c010f0c080d1d070803030c030601020c040603050c0a1a092b1112011b360503060915040b 64
    0xb0b01e0040d40e040206d40c04030b850440a2204903414100308070009000c0d42c1e414680c44090010b8209028481030300d40003002810303910001c2c404450b411034a55100c04c0104243d5806800810103a030000d10f072590b458094681100c220b03003400c02801c01d00303251712a15500a020b09604211121034441c0f0000d0246089681058001c0304141d11000f1400e0b110001301a842c00c00d59010003268480c0486d8403000901d54151036400010710b085480b40172404000e80c10150565065004168490100c3d48030741c0310312001140180b0040400000000c10710805490070307000504440002000480c1600d403c070115a940f000c240d48640d644e010001c440c040202c4098a0006000a44c840407003e0000e80c1001c006a140304484995403001584420340c01c95001000403080780090300c60101d00c0501905100103040c0740341c400800e00144c0d180c2da110381d04034644000c002e003160804e014003803801c0800035a80d02c0040c40000304089015a20402510704005000a02080c1220001007160080408000444 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 197733120 1250 197731870 197731901
    0x10c0213020a170f060301051b07020120150a0e03041208030606090d06050f0606190c0c080106080f010c020303040b0f0907030b040302030c151603052505120105010c0c05090901 78
    0x3400c090740e1a0384d81301c1d4192001d44c07180d82083e000c10010f00400d41815071f0b0811051920b454142c00758011354610b0f001c40005216148941012720b004030f41480340141c400c0e000494003400740740018405d021151050318086841d4002e100074420080c06241d030300861900840e4031900c0ea600c00c800100030303105586c4e02c0c94000804803406403c1150542000f8010040055910120340ea0081401001d009030b1075406140700c084030f000043c140c040d47d1a00300190045602c00706058950003100d00750b41e00ca40c02031840d5409411407680f100d40038030504500f4801c500c050351a5003465100e81d01c8501d00030301707401c00204102002c6a060b0728200a114001c6900c400c40480e14582801c0107512a0030401000569010390b1940b05030071500700e9503a6200321100c00e60009c88010301c0380100e00400c4018600501c24400b845031076403501000350b0400141c043d5a0726296540c1c00030401900390801a4002d6040c000000d03c21400694011020015108251240101c41d642c000c3d03000c1c09041c1500c50361504 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 197734370 1250 197733120 197733167
    0x20d0f090b040515150103050406110301080c0a0f0b03010501270f03030305181f0209090903090a090216031101090b151002070b070609021f03060311010c0213020a 72
    0xc02641440141c41503000b14142d80c000c100041c130032180c002c000c98141c0d0030000b003400c0b4521598001d034071940e04540208000140d004d10540d601c02158000c0c0c20003c078aa0141ca211840d526200301010302a1088500c0c0031259407808241d040b00e408107004140c140f00614400c210b4a0100c40083c624100c000291004580d0382c420482000405034001540024104400542108642c0d020069420b00e090010107000c404402a800038182c001e8801400c00d4080050724201c2d0b4400c2c841602030003286014654540d10f040411071000d8840c2d100d03120f20390051007a0444031038a00c28190005405081022115440255650061614101c01040c2c655803005000344041c500c1844c50030244103844100d0000b500c01410780c1d07034080d28442c2c00d4101c002003203c2c000041c0960000c4010034030282c0202d90350b4078047d0324403a607424450b1460001130f541d05420000c1c0560034500c00c0c505c4000f0f00b0001c002000a40126a00700280014000020f0b00022403000c41c900c1101480b507046141d0204804 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 197735620 1250 197734370 197734373
    0x11502151b0f0f09090a0b0109060e04021201230109060c03050304020a09020c06010f0f030b04080c150109020d050a0b0d03230f120a05061c02060d050a020c0706050f0a03020d0f09 79
    0x56070741003104210f014201c40c2c0000392060b54107201f032010314101615409803061801808640c8030106145072500107800344484110040dc0a00d20b40c00380c007400c1e5030104980c80d0b60103060601c9203e6540c45041040250b010098980c02c0200800c1554052a2095484d03440f070000c92823a04c190391040e07481780d100044003105810049207590580300c108450107401c5984a03502c0b01884440c0c0400703054041c41e44c02280000b80c101009128001c000360a0707a00003550640c011a199100340d12500402d0340002c1c01a403181c803544103441c1e0101b0403038410400300800b40d000c90001c4d14084001014452000c26240302d840902820080141c980d00c3e599548005081c0c0058260b0400c046801d62008500702090850045019035442203101900c1180e807582056500d2044014401c0240e0704400201703c03d0880d03802c10b008451007020008000350303449181c4407145160070b50b103520250801c482840181141303041032084074480c001c030b8a800f580764800d0300d80000c0144010381c508018507281c00740d50700 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 197736870 1250 197735620 197735647
    0x4030201050603070602012903070306090309090e010207080a0c050c030715090b030708040f0609060203040b180738071b060305010b0405100c0605040b011502151b0f 73
    0x40c41542c050b4159454550359013010381c243d03290004801c0c400d03140840d03d440006141c01b00d20080300070050440d0710301980c1e034403910112a8011020b4002880704141402048964040d11000041141c000c500d80401c40e1540d21060149000a200300300c0080070181c00e0190030050800802e034018191101980c4d80c884200e143c40c03040c215034002c00c1100c40001205071819059174880c600c1511112200da54603907800c04900b6000750304444040e511242000880d80c05d10141d40f0461051841100c1030801a91520305182d60400c500c0150b8803204c41844500d1482041c446502641070f0f00c908280d1142c80032449048428100001800c00800d01800b13200c060400603d994140c0300e22001040c1c0c441274110141e41c4240100111244104420400307414500e03e00c0400307242d98602032a00101c26541d40050b1841a03400780e40300d030805801848140009c0040302d40c2d18a10740011301815085a10b90b9001d40401484101080b1100503c481e05403103c608a80051004900443e9070340e00e0400f064 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 197738120 1250 197736870 197736881
    0x41103010c020717031218031306090317031303031107020909010c0801050d0302210c030307020a0606050604030209040b0c0c0f0f0106270c020102090409080903010b09010b0f030c1204030201 84
    0xd6400d61051003110644203000c001c440040c0303400311040002c0e03618441d10302c47c0c0b06003050300c20046110401c054400c0201078040c41000d40b5569540b400f0003031450030b081d440c03803100480382c103c1802c00f0028000841009c1c1d60480003540d02d41808201c0c0100411b0004850080b9440030b0b400c803c040003081680301040d0301c40c40300d580950310381f01d00707076600d503014050281c000900c02405a0300c051540100d18122801c00c4040c1549800d09920b0440a51200e50968200341d03540c2015078080d0390280c0070020780740102009084240c500500703081c61500040c2c0010340107031016185001c0c01e0301040049850380e046942c00d034004022a0391f495401510703160358100d80f011030a825440c00c0000701b071500b016a107800c20f4403511400c2a0803443d10b100c0e14001007500100c0070065640c01c2101c4000c0d40c95034007403900706a008400d4540c58000c00014542518120104544114120001800f2413454130f81550906002d600c0c0540d2265601441c40080f481200f0b415454a044482040101603054124 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 197739370 1250 197738120 197738129
    0x3032205150405090a022a0d02011a01050702062203080c071208090906120f0f01050a0e0703080c0c040f05070237020102070e0a24031a041103010c0207 67
    0x81c0c034104001040900100d0007140a80d952010701c20000c0741e24404a81c0140c007151625060100016802d00541141241c02441c601010341003e0700e001c001c50307020b11980d1390018508544002c0b840394480000c0040c4903010f0001c2c41000040350004817070b05089010f820100a482d40030320015201d003040031075500301c0f20319650315105d4540d002c84d04903401c006883c00b03954404100346c2800c46c190100300e0421402404150410302a40000400e0a01000201c141d40d070004090005410b0744146c207425903000421818445007000e0016180703040004001c405c0743d07041030500b0740b00c0075080c200701d0034031301c80701101c55101c0c0c1071483c0721107030403069800399000700255002c990b08994240f038001c0e0300d194003158211a801030014030124821500c440040128414810307510340648480d6601c40600056456905466030303030314180c1a00c104410035404502080c108610458507541e1809189840003040505140c4103101190800c18101d291004121009000384986501040300075500c0525116 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 197740620 1250 197739370 197739379
    0x51e03070c050d020d02071404020c0604140c0d0c0501111203160e0f01140a030b060c06090706081b0d0e0109030206100515030c0304050c03030a03050105031005071d03032205 77
    0x41070442d03d4000a07458a0340e850030b40260409038a071818800c1060130341c00103c3e400580030052405440402c0c40250b208071711030340040b00c003805078a00003440e000721443d415005940500b10600414111030f08041140d00c2440d06604014400680c01e080820040041c0031070301002c410b106500026600b1070405603103581c1c403242140a00d0041285191380200400e010400d1070f450b02d00302011040c01060320080781c3c00d021890054200c0402c4190340300290072200c40d0001b0003402035201e014040030005001a2070320403c6414502c856400c4100b0340a401c4112a00006065903151030315040003420100e41e10082000025030f080203919000c1c101e50b4094640301d003481c085540d160050f80c03a04451540c020607400c507514000206131640c000380040d105032080002c40b400694007003008045076aa9654080344951508003807501c0d01038580102c0c2507c6003032808000c10703650311010006850700621460078180d164200401c0c20352140d44100b840411401c10b1800070822003034400c1045030707021390703 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 197741870 1250 197740620 197740633
    0x100b2a0a1208101215230402040b0405060603130f0c0b0c010c0518060702030102040506040803180405042a0302060406020d08090a0308040201081b16050c040e0d051e03070c05 77
    0x1d4a0001c445a800f5078a04013084003001c030040b5808110400c080a200d2600060702102002002180403145812400b2904110100000c50400d80998042c0803000c3d1400c0c4607038240640021034030300004040710301c3c0d20308104c0c40c0d4050010783e10080001c2d5811421400d0381d141c541c103680400c1e511403440c241d50341d801c060031006050b10a00417038240c0080d0701450741000c04000c04000c0355901c140c0c030690b4159000d01c4041050380c1c511004000601810005540c1c90540c1d0300c40001d00070f2003810b4984030b949004204004548103407010103030030140448002d00c2d00220031100c1d5001d12180c1000e90070007400320700030401e582c00052808030100140c03a00042030b44c0310401d0b541c0c0c901d20130000500159001e80490015409900fa994101c01e00c0b0080036818101682040381c150414070741805400d882440d2002402018488a12105025181484a80f81e40d64400340d480115a030750301c00300300e0b00290f9403614035510740350784054a80100300301c0d07560f0801c030300001c207850381d9800240c4040c060700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 197743120 1250 197741870 197741881
    0x6020307230910110105010602010e060f100506090d15020307020708031614030d02130e060f1503090a060e06150a0609180f02030901060e100b2a0a1208 67
    0x300c00c200800710a07840181c1c942030404040c000d49495040010050010302a554654803d084c003803140603210070f90001039141051b0184610f0408081c02c4144004001c8042c06100a0390761100815900c05582895440c4522000300c4c4900c404404042d000e80c00c2040e8800c040d0b20b5a4004601450303440e821a04102e03164103615407607109003561100c0b1a0119005030000607060180403980d10101c0341940d003131480078040e50050b80d0010709000c03240d0749035800600801c40c02200003608034100380c5220a401040001041c0424000c440c41044120003000013560403c082100018070355006000b40f00b030078070071000c855035900184c03000b10b107214240c80c0796155800c0490a00003103034410b58500c5c076041d18162003500a44078145800e29000d0310395840f13407000520341c00114040c282c50301c00042c5035407078003641c01e00149001e0030000c1008080d82c0100900004141034030100d00c452220840c4e00305e40504030b00314400d21103882541500400741850240705c25060715121441441c0c8501c9050781e1071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 197744370 1250 197743120 197743157
    0x12080405040f090606320d0b0a0207150209062d07050a020411160b0601090317030a060602120409020306061902250e070c02011101110a0216050603010e0c07020d06020307 75
    0xd4660703071b001d584085060794000c14000030500590300082c011401001054580003103521086070403501641c1c00003845410400c000c1040314400120620460600e65034030f0004d0f2107441a50002038151000207200700340300c40007141a2580c0301041200d1075490000c1e00d080b541b1690312030001c0e03109519008820700141c0c83e69007221211840c24060300040e01c0955a0b0008510020344a0380c10005036070804400a010099617000141e4000038990300d901e4082d24230425030b0140d421840454014946000404103807000365416516101c3e0f02680b26074a81c00800c03543d0141261140100026401c45030700640c01041c41500300c3e03100c91071060251a100c03000715218a02e48501c000306030715200082d190a201c1c031441007082d441450403020001500a0850079207040e842020344c034210003d601104181c0401440300d926201c6250b030304d2041e180c8400a4414013052045644a101c006c00040030090003504641819600810a0480b120642441c80003034104807944404244007400e0f4803c80d108 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 197745620 1250 197744370 197744399
    0x170901020304030e10020a0206070803091902090a180c090603031701050906040203040503190816021b0105091302070506040c0806060a06030c03060305071203080c040f12080405040f090606 83
    0x8268130f4440400c419103091100a480c003421070800c6028034040440160380d020014803a0038001c40106440782010084c040c14080344d0362400321201440150b201c0141c80e105e14484d03004500b050005041000e108034203480081c500710050900c00782c88000700b00c02c02d107903109000b43ea00942c0c408148040c0b01200880001080c010143d00c4030b5030718000341c014a4190021540300d4410010380f420403500070f150038035054140803040003080011042028801b642d900c0c28209001c1d0b4402005c149140c24498104d110300d0341c81086c1040303000254006551110741020050148a007030441d61912203003030040d02d50009a4003118203101d1040c0c00103240a00103080d034001c010003002c141c005403a0250507070040032004800c206240e118400040030840038071441001380748a4100c0c4040c01c80721725002b840c42e80c3c01451050284400e2105008200840b007a110070740324031051100c0700c00c0c080d0420b0701a82c0150f50040d03a105040080000308049190031181c40c5038403640003132084540360400b10320b2660 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 197746870 1250 197745620 197745623
    0x703150e0a0309091e14010504050c12041704120c08010507050405091513060b071707120e060d06121208090c010315080d020307050c010c030c0b07020f030a170901020304 75
    0x30f948140600040c0203da01840c01c032010703a4482e455111250004c1d4050b906101d440308440d410300c1c40100a17504180c05082d500c100c529030114544414800151504030b4050400340200191180005035420f0724021200604202c4200c0048202c0034a0034581100082c0590000c5500786000f2520050062040d0340070750308003d00c0442141c1c0e403080880303000070200229540c000060018011514154818407025100302c184a99860f61581401400c0400400300d4440780d1600f04800000702d000d40c5940b05c4404030911b0059540c50003040042c8a50081c2c2d003c0f0302c0ca051400310001004805044a480054842c070090a040844000255a004403c8900d0b500d0364000f90003000e602d61181d44145c054400c2d0759004900c8a4850340c1c0740b032404140464203170242c3c0c000500001408000c00ca4501000b4091030407a1483c40a90703030003005411050b030000c040f5000103000c10349660017842082c2d02c0c03160300011139803154600343e4010030030325141e004000000c101c10089915108103000310b91045 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 197748120 1250 197746870 197746877
    0x1060b03070c1e151a1c12021002160201020d0311030a020c01060f0906051206090a080307032301051305160c0305160804051806090a0b120703150e0a03 67
    0xa0100d40702c424005040030f030b0010800d081d07407040b1400100780c80d0459000812159000441401c1c1c02400300e0100039400c101403103032103000e03580010001200801281c17158004801603140c6409070302a850005c1003621400c110340041503003008410009202580a4001d908880b0405000c82c4250125074051004d42e806140410026201400c00e400510300040e012000007101503171060310122894254220800f0142c80b1001001145812503650a4032110040a0541400c2c00ca01c5c0e40d80c0e40718103200c0106a4103010000a04d19802640114010031842041c0c1c52841004039214801c1c60090268901c2032400002d0b040b681c8000e840313803d2188840d0500c0d40400004c1040a9555100d074002c04c504100b0100485070300000181c00010b0020311610000e5100e500f4481008001c0402c01100901c503c00d0904121480c0e8500300c1c15038005215136800200e40c844803020035080850004541a1071145410010030000030b040310504015948400700103840c403541781e50340c54145a03907014002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 197749370 1250 197748120 197748137
    0xa06060e0306061504050414010f0f060e010c060b040504050607081614090a0b0406031a041b201504060c0201050c0706020a0201021201180507020304061b112101060b0307 75
    0x807403d100c0c840319113036850059018246a0345000050940307403d00026013180002d00010818408204d0465020f004800b064550309810224000c02184490742c4c0c060401c082d9500305030038007101358000380e98440003070000e000f1443c0c94240241e542c0b030b09851a0380001c0003840040c07695000c1c150301461034112913403a042690300c018452203007a00406e80c080d5011075501c5d4000b407600a040010030040030719480100300000180d165030107a0148108040c001ca040000340640b10b00901c1510f0385a9185007080031340446c00032048014600001c00c025407134441c642c3c0e84424244e08190440c8564801d0750280710040c41600202d00341c0d0300c10361794582c0c2002c060090f10002a0f5a80250403082482d00c001800c004140340c0c014120f00080e4451004101400402000b603c094000c0c10f03442240c50005514280c80c0010040c1210305040d0040504032101c5403102c1080411028520b2039540280baa9810608640b05032000300c1140724511425842c05800248603001034060b01d114102c0e43d1a075401d17 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 197750620 1250 197749370 197749381
    0x30b161b02040504020f04140f13030509010305090a1713050315180f1c0f031a1e04092a03030e04051e040c0f05040e0a03050a09030f08030a06060e0306 67
    0x30300f0340a03004990190380e0480c1c03404292118400e0b103040e00714422421000f400c00d030f480b17500c0540001c1c041c1d016210900c040c11010903000011588003080078a00007426507510844581002c40078000100405010340e510000050100040d10704022b40c03000d0031800c01da540c410565a00603800340445015001c071b00140b2155002c3c1400b0003a01c86032800d49001d480c0e050200c07414001c010600d803410349003a40000000c9940102d200003c01c019040c20050506c0f4074a1403c105640890024499030307891220079503184040304e0f0307031454030005441440a0303e042c6c9400d183c100080c0000c4080b0500c40954101e00e41c0c11182003504898140e1a10b403a80b40d0140d00348000742000802038240000044801020445042030342840b40d4040c8011444a41c1408529421500d840c0c0c130551290b0304100300000700c7c81002c1960503600e5454144150b43d039014003000e4807920215403000c1c01c950070301640700041c400c942d001180708100e81031003000002d031035030001c3d61820060600150158000c000082 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 197751870 1250 197750620 197750629
    0x6080d050a1701080303070e01110a0b1305010e0c0f0303040e0103150e19020301060602210c0f0a05071a07150b03100c030905070b031b09010e0a030b161b02 69
    0x208001e0345030110400701c149440302c003845401c0c1d00c0600143e100004020120742d0007000b4895042c3e0034a4207070190208a407048d6540c1e045c1c0c0130064170406003900803850b00c038083c40f0050452a444002400b10740a00104644c458400701c4005004000720310014002d4a004000c44040c1d174200c0c400e00700300da420b68a80c035540c0e00014007a06420360f900c0001c03c80310207040000d040714039280142c148400c185c0f44145800d41c0c1031540010155841240703c094070000341c185181c1c4440d000c040441d00c0c1e070020f40c045460300800d05d14104d00c40c0202c1c40c1d81c3c8180000460180242c401c080a01a00e190154110920f40c0c440d02801800030840360310405c120801c50740016000120040854500d0790381c1c0d417011000c0b24a5a0351040100c0c1d99071801504011062004000912170203903081d05500e0081200c03001080d0120006030145400900060180e018a4003031001c090054800c10035152a40b41504820f14151070f02440010b1411401011511075600d102450101c00e624201005030782c0d0921 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 197753120 1250 197751870 197751877
    0x80a0b0705180a03050c180c09120313030b0a0e030a050415030f06120506060307080a0206160f08030103110906011407030207051207180c0f1b020306090106061206080d05 75
    0x308542c07a0302659005465940d405044050b40c0110040c141c510b82d01d20400801024500004003d65a03042c10003004c56001010b641030b8000649544c0c69801c40740154034250f200d001e082070300340c0311440004818006182c103098403644906a04009540d4050f005e20365900a42c40800001241000248200024029140d00009581c1004503d64a02d008540c059901316000180b42000325620a824401c0420070260031040c2a005401401e050581c3c0980302c540890340640a03d100107503030315401d44403000000e0000c0c0c0011612700030080e186007080f0702d60b10078072065441070400c2d4103484082c40c1011f0180d00600058495a41150350050400041d401c2040141c080d17016502001516490b640b40004030194a0000f400743d4a04104031b000840d450003c254203000d01d0080c0c03c481c2c617500600005445211818114040300c0b5850700306084014002d4025054042e00051009004054000005481d5107449481d540000880c1d02400c9985502ca91405640401004a8503a0044008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 197754370 1250 197753120 197753137
    0xf020907110c0f12010501090c020d05090927030307030b0a080c28090e0a0b07090605030609130609050c0f030309010504031e0c06020a1203110703080604021b06060a080a0b0705 78
    0x248040e03040c0000b8035403c55000340c0c00741039860345a41100907041e60601a10bc01c00d00107091180c1020100d1340805c840c4030004007140e90f0000c24488580c5610500e0150713020302410401202d5603440d14030401000f402d02c1c0342d00903011740f1184d440031885880100e45c120180502070044003050740d030203214156040040c4150748044c0f0344141d01103100c14042c02628101c00551303009100f03c1200f403030541c0c84d400c001041001044018070041c000c103035005044a07002a0b0855100000340c0790fa40301100c819020300c200030081454840c1c90402c0010200d800640d400c3d084a0f0354260100c00f00500d40c803841803004490001e00208024400511000003c40901c0d00f414080c17074440d04969100014800c15411401c09070380005140d0040203543c809002c944c2c2c2c0f191905000c44009100c9080d054003c4001c003c0074400f010300041c40030f0321f403075040d43d035084040c0005255200300070f5103840d10358609840560250030381204c04a01c500001074000d4480d41c1c00701003011196900c8a04032600d8001c20308 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 197755620 1250 197754370 197754379
    0x102030304170d090c0f09020406020607030b040b220b0303030601051b0a050a030c2d02060c160b0403110402030906040308100f09270b15060d0204030f020907110c0f 73
    0x100c2c0304401c440d07204e030207101842144100e21190808640e041c02c05200e41c480002580108014400d0702e80c04110980c000206080108060070007100080c007070112441d40c1a00320b51a0040c0a500781d1203501031015298003070000300f1081f80820285034980c031080710704a011440070040c07031002181e1124030344425080501030320b0245045541d81802c020720400260001045a641d450511504062201562903905042d4a40e1502081404044c440c0d00300c019208207000314180744504c0042c0401c141c0ca03814941c2e25881b00381c071688070884942040c00305694035104481e00007480c0c00c09200b26801006d0010003040c80b80e599903011a4003040c02004000b20134156200002c0003960000c0c10720150125500206a100e14106003480030841c43c940d82030808446a52140401d04000d685904030180d18101002e61840b40003080e4039109403500c50300317100d01c0001d000050002001d40b40c14901d2007210b824210f500d4402048900340c2e08100303641380310b0b00074500c0300e8802d2400705ca504a030b00e10040d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 197756870 1250 197755620 197755627
    0xf0309061b0102030703051e090d030221010f080c0406140d030504150f0f020a21030e07080c030c1203090d02010c0213060303020c1012020703090b0c070f0f0302010203030417 77
    0x31820f80c0c20507656640441d4440091010851032100d80a06001c909010301c4a070349418080240da520301d5110010a040e800150030a8035001030203c00c00b800205102800c0550303441e4902014030b87c0c188100f0740c403402500030f1031103546800c5c000c1c00c00301c0301070710900501410982d042141102ca8100100d0600404000010b206010040e001c0f40e8034501d9114141c94106904018000821a800d0101103411020304100010b440c0345644503000000d03815110381c0d01d4100300c10350081180c50b8000321184030362400000c920100080d04e000c15a019400e0315118080c50003481450b88a420a8803102c0e0000d00421701181051100d02c46100e00500d0040e0942c031058003ca0316546070740d41c0f11103500b511040d00340141501000110b110400503520140c041010b101b004000043c103030741b1941210303000200c00062510502c130704000b52114030003140c6d5840c5c0c203040041d0307601c0c1d251003100342010143c0350002304101c0d4403903040e0403240c060b00658550b540b0755544280194051001e502044403d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 197758120 1250 197756870 197756917
    0x50418050601060c020307060504151107210c06021c0c0813080a26040e1003020303040e0106030507050f070305070309170106180902030a0f0f080a030209010e030f030906 75
    0x400c030950083c001d030349400c0e80b05921401414213100c2a0340001c2c0030320204210800103200040400c200444051412081c080c11180c03281e8207080456010000c0d1581d40c20218614070958440040a00d1007216017548081c2e40b010142c1e259a20702e1305540444440d80701d03100003640542c840074a20380c0300302c00e502e03e0311107420300118180405400c040400d0b44980c010f41c0401101c15000d00c1e0065248a180d0403d005526100b01c840c42035019812001030400086600f95182e441c0b484003840e801015640c0300d50704c841e442680c1003000d1045c0d43c0040e0500000c22203c0c4c1c055405c49020f031b854441c006245c180306031805e8031150710450044040000e07104d4000b410302c441200d00611038038050004680203240c91030400304c0007243c1ca400910a4500800c140040e500010300c4020107a00c42c030320303100107100341c00d10300010302520308050300400000861001d8142e1541c0100b20742c6c40700340c03078080390703e0ba00c1800e040e51a00c122040b203609900401c030843c51841d280b4050440080c03044605d01500340700303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 197759370 1250 197758120 197758123
    0x19030504081f0c020109081e0d02030a05041707081803030c0d020609010b090f042d05060609370e030c0a0204050c0f031617070807030e03120105041805 67
    0x28040c00c040d1444480d079031032000c2c034668020b0181504161000340039107030aa480301400d41c420f16a20b5070031484036460f900083d850b00000d5642c4110307101011501c1e46001c0c0c4003900546030803102215800c1c0030000c00061481c500b0242c3d0f8101303401c03000b03143c1040d03044161b4a00301d6440400301c81d4140300030300540c00420b80802103810031281e298042c0045050045155095900054410f4491402e12040008041910180d2980305030411742c03c1c42d91410700080c0c0b400312508407558001001884c842503040c40000140c9500030711090300d40c6610b41d0f0b1030540c00d07081414843c09602e2410400c5440a0040c11034055112084004800025000e100900f8091840d440b1907224982c0e030700300f9840c05040d8541413050b607038009240011540303490401c403000400383c80014015111180401c802440c56485840d58404041e0725504406650410300006003500b80111440000282403240601d05138402100340c035109200c01c2005240c80c0d003000304000251503004180c9a0a03040702045031f010840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 197760620 1250 197759370 197759383
    0x50f37150c020c040c050904020306061c0510150c031d04020a08061f0c06150b1b060709081917030705030403030b04020403020607021c0210050d0609060501021903050408 75
    0x380c0200240341400010064101007443d04032a01c900e1801000800b22500b0030101d81d07042c0e0003180c0c0140c1d42c5d6030f0103000941700d008440c0d41842408001d0301300200294903500090080306005050142980d40715140102103074041419000540612008800240500944246104024080980d6480b8540810102d8110808480000b00420240410b40c10080d588550382101503918041044042d58090010b203a841e03001051150796200394941601052000c0d00580a146034039a61402d0100c030b8031142c40e03070b4074028403c24000c50020404d894080c138000d0741280c8044001c1c0c002c91601e41c21100b9032944090040c1d88400c0362606507030940c060500158824278441d2502e54817414141001004c440148c514107002d184100703c10b002503580c050a9415155040700c0205840d09107181900291120040c002e4000c600301000205c2d45400001800706001d68600810055585500d10025901a03200d09070140c1c1090400c81e44406e122000d4168a0740a81000c07860a0b0b5519045460b03d903 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 197761870 1250 197760620 197760653
    0x3062803050f0c01030e03030606030415020d09200109050f0d03020102090d2102030408060a05091006141314060f0303190804060c1d1216030f050f37 66
    0x104802061003c540c0c052040d52115601e490045007145010300101e801c503c0040d0018104050403a075103a00e05003c2c0d0111042284d51610500c4000720b6440c10300800e00080b401425640c0314060840115442540741d0742c02c0318030040c1240c01c0304056000340540710a8020040e07045540800031850b2070340300c404885440910070b4000402a400120385000000f6a003000081150000c2004104403540082ea17180c00009461001071103841704032440345003518103080070f030301c8608202c0e0004000b4035194468442400c107645c403441c0301ca0512001c50407241c0540d0f80b02c001440b05030101d492410100c5c071444040d034001d01142d29243c00201e0018002280b044031400041c400000c0004009041c0254104222a0b01b00440c1c2840c60107241c3c031000b20702d400e0039400b8014801c0c0c04000303413070100300440100320bc6108a5042c0e5450b81444500241c01c1401500c2ca4415000840c402507800148140c0da03020322031421802c05020f16603000040207101003101c20018001003440829919408500d580 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 197763120 1250 197761870 197761873
    0x140705030904060509041226090d0813020904110109031e060c05160f0302010f02040801060305010605060c0718020706110901080a060b040b03090712050703031403062803050f 77
    0x6809540070030041e1003c0d90000307805072119405200c000f4040350110001034840341407c0400c8401d0041c44681010205084091002c0350020b000503814045000c03180304c1a0b690340c0c04043c1c4c0d141144494402c114000003074004521034000303004583d8154045e52186014500698890307075070785802c08001548403200200c5684103e000d001c0014a101d000c03044070060900c40d050802180c8502c0041034800000f8194020451401040510079130007405e20106409046444546030124140242030500040310150b2030414040b17640d103416010340724000200402041c03524103002410816800003010742c1865130b001c2c0311038000200d16003e02c600340942800415240e07001342c0d0004100c0c0e81c8c05400106214074140b000d00c13152041804582c26588030b200c100b5640e444118001c5d2400c49250300104941000c04000300c108640400c004045900a0765040008a44400c410245200980e1207940c030070346030740d506a54000e460740c4582e6100302c2c0c0c0642c49841652511202c0c00c0c56600c0c040881c00e07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 197764370 1250 197763120 197763127
    0xa0c061d010905031801080402090708060f0402030106090f0504110a0f110307060b18040308060114070609050a121404140409020301061403010f0b0d0206031803040e0a11030603070b030714070503 86
    0x590745c60f450030104090007484d1184c0a400c164000c1a400040504840200100007001401c5511800454500c0601c098000c41d901d42c0e440800606010040c0030b000234940f20444005500e281031301421801c141028002440d00c0ba10303250568030414680321000600801d45101d2140300c1040c0f01a1a41500600010402c01200300c10040f024422408000c26603680f0400d12003ca5807007042d0941c040c500382040141f00300c3d16070885015024158000340081d050401120070004041462080d4610401803021254241d030000e83c3c40c100c0303d14103c514450180320411440b03011540c1801d15403406000010f1400d555001703e803d48819400107248500d2a2850100c182824070400010200c903803010003030880c861001074544000f100003c0e200f90001b01c041040b0303d01488c1041100880c41c0201c0c0d07a500d540700c1e4450000709003103c0419005150000311220300320880111792282ca0014081d1441c1030a203840d280d560341002c2c002c1020040b903554a0003400780c00300000c101c0300303002d440119103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 197765620 1250 197764370 197764387
    0xc0506010321020f10020d0603020303070f1403030f1b210123010509130b120109121106061311040f030c050d0f08181c0b07050a0c061d01090503 64
    0x119203245820b000c045502c458040c40c1519808115003011003c06000580c0e95100030601901420307840d00301940c50300001544000f0003118000418420344103100c40b003038030685020900c3c0c40740011107280300080c004000086800d02c040c4069400d01000e0081c45041407480800c030b020f1924041c9035441d00d18182d074010303c80c03916801c03001081d810340016140e840103c4000002c00318015414a1800340c240d0301080c902c03010250f000025a40f070040c100c2d814128500c0030b0a806008115815100780324076140e48010980303e500150610718010780140900d07124901031008041c1c00b600f450740c2e80e50b0b0328018000111071901c028401041c103001800701e03060079420002c6074803013a6840075108103030481100d400035807002d070200c0d10240c0202030300f03486000e107005580c842e0b21104c000f154070000700202c1d28404540d448014107818001e00869440e5540c003d82a03449102c2c0300e44180100e40b1025031400043c1e46038005020074500c0c030404d181e49001642c01582510100030045485030000700c0d0100c13 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 197766870 1250 197765620 197765663
    0x20306010e070207050d1a19061202010807120b03072706051507030c2907020a02010518010c05034003020906030c0d0501021b0a080406030504030c05060103 69
    0x60150800401d01c1079a81000c0c00083c0d99901c1a2140300c2c05002c5d0b49200c0002d102189100101104c000c48031032a8618010fa111000c0b510881c088056442c40e280b4013050f0160040340b400b4941342c3c107841360003103a240c454082c2d03020300249944400d026242c480303213091914180b1182d0014050085034140351640e2803e000d810005040300341c4601841c00320208803598031a041e01c0350328a0a0019aa55000d4504007140c1210340781c00e000c2c160b004000100e01560b00710400c103a8101203c02022502611460800c0781c9500c1c221102900044090141706960348007100c101e0042681414842d054203d81c0d6101d03825608010b6440c2d417100d60340440c848001050b072403590b51502d0074206100e1701603169284003441001c20700010340500b41000c001019a101000b50180d591001411810703e01690f1409074040d6201c1900d0800030203013455a6a644000001c1c00d60b1440c0e8020f181e5410a81400400c400403c0014016000c01030040c40f071002107082030012502a600411044006002c0d228108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 197768120 1250 197766870 197766883
    0x60c020d2f0108240a0e0f04290a150906080c01081e0103170d1b090501020a0201080c0a03090807151b020a0b07090504060e0f010902030402030a0f05011103090a0203 73
    0x16060042003410051400c00903503010358005456483c2020304c0b40490301041002d50181c1007012100c1105080c882c0c1160070000080c4903501c602110740322008408a440d1585000c0400c407074481c16164007086282000d504403c1040324003c1d00b01480c07540d1040c0e42400d64045070f21410807500140d501d50f0107940d000d07420300e03402010422000303000444080f2a10881b5414070000e40340d0407013035280e06100e580e00d008030b6050003003415013400080020300c0d04503c03070740c2c03201d000301c1c041011003400080c59400131880c0b08500e60140c4460130b03542e5841c1d00d84a400e5101038203802c20595501d5003d000920715201034110180240c03080c50000001c5500082216048240c03161042d01c8010303541c0d185680040c041d102541c0c0321031036441545510302d003078600c001203402490f030041c2414000b003050451249280c0c45488030080500766a6a141c42e080101d120546c0c0c0079400d07401418000f40410500319510743e141e80320300700000c0c1c42c5c840d803101c1c403456401c00c1e80c60949540150394040305500d03042245 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 197769370 1250 197768120 197768213
    0x609010504060503060718092d0b031e0109020907080a060e1b0702030c06030a0e06010509040c0308030c0f031003020306150109140d060939060c020d 66
    0x200942c03420880041e6582c10300030110300c02c11080419820400407241c0100008181070b034070034044840c0c2040c80411002c02803068025a9000d6280c03000e00d5051405181d088170009005064080340b0892040440b010302290f0030030070342d00c0e940d140b00103031210310140380325100540d40c000480c105030210809982140d80410b08882000b024000c0e502007031100f8104a804501a0b02d0b6585043d10119040c500641401039228002008115900b2415000026040341c0704083c2c410356a20781c020440003550030355016021000b0700c1c80500c0042e200400035500070f10013441e460706100178020010125441192810b454042e912030420131404c040206a0f0040f612800c00a0441c50400000345003110504c1015614225101c0784802c513203503105000c416a410000c00d20460900b8200048003681c00010440700e12184c0071840803074901a00c2c00c240154900c4040901c2c20300d891401c8801d401140360682e481302d00306541c00c0002c0e500b0341410020280c0210343c40244034046090840d1b04020603007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 197770620 1250 197769370 197769379
    0x70b0301081e0109020d060507301508070306090303061d0a050703140c0315010c05100f020405030f07030b0703020906030417250b070c080910020f030d0506090105 72
    0x10300c04140c01050742c040303509400c0214405100c045150601511075010003a4005020096581c103010b5250080b80c41103107a5200e0384a00043c28920041e60001000ba88412481840403c201240c1641111401010007450503080ca500c1d903114a0900c4c005030f004458113550350304040c040580500859006003880d01c00380e49802ea1581035101441402420091015512000100f95a0190744094031894040c840103030907142007103a0014561080d150f0841503030031a00c06070181d6105260300045603900c000a4244000c4913801240071b41080c13403120180070b4080c0404201502c1c20420903903a8030b209030040c034180e461414044142c82015040004140c010880c40e50142c903080101e1f908541c5c0042c0300b100b4261031050f0b40080703000e01c00703e0402d91000c4c581040341c090300302051418214040d0302c1c51a80c2da11074400c207945810300301c0801011068180000c0740d030383c901100d2004144040f40151480c407215081d05c94155444a50044d07403050340d840901c461800c04a1126000d05010789 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 197771870 1250 197770620 197770627
    0xf03210301051302030c160c080307080903010506030d0507060504050718050a0e070503070b09030c0a0b03010305011109130c140c1b0409170706110a030b0f01030b1012150602030c070b 81
    0x185001954407e031000d00038090803044103c001c000305004a03000030300324082903a4542603a40b4020301d2541c080040303a0f21035801c0c40b012654500d400704952004280c582c9550f443c0c0901541c5207800340c100207009503068002c02e48009210031020b06101d080c1100c5413000200c2c2e1800c440c10504855034428510440d40c042c000a0180c2c1d240050300346c0980d400c040086840c0e06043d400070340340c91810255240c000740d41d0341000516410010140d416a482400244a108505481c0c0101d5004692015500c00c81d0600100c2005541c0d520903c2d00c1d4000b85809410003403103528100065014440048072a4030010b80202000c030b03d04030908002904a6050010400c203441e00000f01c0a019444041070100041081c20042144d2102a0305500108219140d00c40b544003e40103040f0004001e0180503240c0301c0d0140c0358400e100b910240c0703400812622004003ca81c0480d00209018065600a0b549081c04002c1c40c2441d014100103001c258015a80da1807013440d42c070709049150303000c141404c0c0c050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 197773120 1250 197771870 197771881
    0xa0509030d2007060606080703111206010248150a0c0507061e050702090408090d0f060522050709020d06090504030e010e030705010206060f0321030105130203 70
    0x10003103030300307455003503401040c1c892842a141e41040e0910030480030b800800500d03001040101e400c00401c45c1c9442d29400400c1c1d0794084244c054070050581c0c1031060000300b00000d581c0c0c85040916402c40c0061049130016040030b4030b1000710142030010480980c0e51003848910680d122011004003a180a049001088050010407050540203206101c07a07140820b080284a200f21810200650130604651420341d485001410308012101c1076040f904d901003446001c1401a42220300a6901420040e0955500c3e192a801500041009030b4440700003203281020a018003514865240900c1d40050203041403403514842d402403e6142c0507881c8600100c00100340080b4442c0b080301c5540c00d0141e0341c0c2e603407c41e4402c006c1c10039401002c0b107545400140818940d02c141050440c0700280c96050b9280c1408082558480d500d01c901c900681c002c40000d8040d08118180d0040e40364043e003160000e400b00b02c80d0741d070501e81b2980546107006020004111031300d0401c00091800d010034008510314100b8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 197774370 1250 197773120 197773123
    0x20c03030a0603120f1205130b042913020108040c1a0c0f0a030203030f04021815010908010209060d1802040207121403060f060309160906030c0b0903190602040308120403080a0509 79
    0x2c40b841c00c0030f01d41d9070380000300614080203002d052075901c50727842015840c1c54035004c0c1c0c0c041490403000310f080011892001d4084012501207001e240c4001e90348400c2c00142d8011155200010b008450810444100184003400c121200c920302c2007910107981c544c507581001e10328203021b100c08000507a103e42114008240c0200441b0340086104017802c1c891381d6540003042844081c480415422200da40801101d02441840180c0039107090740c2e56032007103070342d10800c6080c2d0080002c21039003c6405c020425001109600c034003031662541c5040c000265803a000070b000ca17000002c007915025441d5046d003a0b4113600c10b291554002174602c60314114100340010400ca040c2845405d400307001c0006c04144000b034104074074582420000701c0c048000d44c13940030040150a40380b100712104002131002080d0480c10100340d9423450009001003c1c11402c2d00c0b42d4210f00a0b0910054403104c0d401c00011001c01c1d02400102008148038401b05c546040c9031800524042d4024040842540740000340100e0342c50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 197775620 1250 197774370 197774387
    0x40f0317091c030e13050105011727010906060603020901021005010b040306020702011b1211031e1e0a030207020901170607050d020c01051302190621020c03030a0603120f 75
    0x106210140b00e0030301d030707140a552031210b04c9102ca0703124440c00c41d076400c06010750304468141c0354203036105e42e0705000c3c0c40c03003044c5820342c1034a28500038110766400c070010b80c00002c80c52070030000420000ca003850389030301d5003800c480c5642c0001002940000d4dc00382c1c0c9580410000d4501d4500c1342080142e9898540c0800050203140002030050390006101015680304240c0740105890760899080c1140c140c0c503107000c1814480c0111000b1400303081c2501032691021055580c150841b20503c461102c070184803c4659020f14505d80071130316510b00d00d0b41e00300c290801510110382503440c0140d81341203600400003600b0b8141d01090f10510b0400611001c500c0100e8001d070000141d007020740c0c0fa0811040e00002a00640d0030404182d880c1000300b10301e0001401d40015014025100b441501d00802d41c2c0d0780caa030100f03000305808a0304100c84d01c03400e51540880d07030219100c5050018100b1000e100130a046500543d014441182c6910040c01400820725504040d9241070401300d2140c410b0704409008180b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 197776870 1250 197775620 197775649
    0x80304031122051003060c050708090f0604080d0230070209071e03090b090d08040809061c0906141302010c0212011103071205040c0302040507090803040f031709 71
    0xc1100c2c0c444820207944060941c08981ca210620851400c0480303e00f4251603444107032210f90400c4c12082c4528050001c8407211600180e95500d000c155000344240b800716200c1d6280c00000402c400591041c1c240300c2c1200d071035166800ba03c020160031401c0740ba0807142c5240e00140c18001461001007809403807c031401da0303034150707201503a0365501902660341c03002c08550311907a4908034150f018515416881108c0c018032a22081f091030321011081c0c2e030b80381103482c084000319003000b000c04c0106d040540a401e003041c0050189240041d44180b15128004c041030b100c10580d01c0e00300c45c42c1000190301403d0142d070300c10403180c00d41e494045852443d172540e070840641803101c140b80480075034885090204200c01070a00902c408040224107024981c4200e60380c2000a50011010000e07104a000b042e00803a000015a01e815055408100043c00041c11004c06e2100070080058028003d1021300001c00c5c501c440907100c00d01c2c60511505246d0300190104003904100a00003259031580d003800c4200c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 197778120 1250 197776870 197776879
    0x61806010f09180804090e12040b04170a0c170d02010e060105010c03110706170a0b010806060f09090403020c0310270c09061806090e0a110117011e0803040311 70
    0x40d031003070f40d2800c9400300340400a410854006004502c40102d034100d20f2016070101304499040c0350a1548003500c1c0264051204040001c000801611110320800c4003d521040140c40c2e03280141e82c3e4101d440a01684050f203041003501208180d81c0060000c41c072903400f035000a2205110702e4007515150b40c0705000c0c2a0520118035204d40a0621866101140c22040003c0310308083c1c5940c000ba00350a1205500e14034101c1d92400103504503101d002d80044060103844190b0b46844641c1001640d40004040703440e103410900005016a503622070241c040d500940241c02c001e6880c2c814141084105040c0e280107904140803030610384a02c00030250080d25034158a9444880c5250072913505906520841034123050882c0400c080c82a112008800c3c1d490013801c0000554589409007690780c01c2844020a4111000c00300c08142e901c0d1003d2045c080500d0481c0701042841c1e141e002c41c400030f802c0b800c82d2004007e22102c034024030948000c0a0f103400001981041c0c40c5076100b216404a40340c619005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 197779370 1250 197778120 197778131
    0x1103060a0501110c060f1e120a021809040b0403080a02070b01150302130b03060103061a1819030303050a05090106030506070c0c05211c1719090302061806010f09 71
    0x86a0f06021624044d10014261a80c4101c40c0d90103240c140c01440c1c0307081c080c84803d0b2107443e030319030036204407220f004280e80500502d5840041d032100a40091403010303040d101d00a083c8001c0d80d1004070301c500c1248290710081003802c2c1400c00401c01000100004070141c81004002c02103102034a100b030464170031411800400311200301c110068010047c59404a114440c0d0200c2c07050302c8400590321071403080e6003c101d003544c0c826a000c00c49049d1301000b02000307000c02c0580c180c4e080008111744400070150590362040015400303145580215402500080d0741c13034082c8040000580a000d8200912000070f0000b41d065850305526408041c0c1500280030340313500c8600c104900c425003c1c3c01018000c00c951040c196140103414040c01140c04100346000341f00c0c40340303d4441a81c0c40326000707907030555859108081881d040b001e8418040c0071101d4003007844040355144c09d418098103122510a50282c07503039052040446203801c10500140000d80c204070014440307000301490705030450b14110008941c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 197780620 1250 197779370 197779397
    0x15030a0f02070f110108010b0a0309060b030d0215060d0305030106081515030103140105010807060e040608010228050c0d030f1d060702070501020307051005070203160b01091103060a0501 82
    0x409040c003000c4012400482c04030140a0b200320300030081c6000d01c0600d9400c0d84440011500010f007400784d401c02d00424130542403e18480c3d442410090311074000000c03040402400030340383c1000b03c59081c0c0107a02c0340c202ea2192580804226810800c15508622014050b81c0d0241050005001d2101089044000542143e10b2401c640c0001e210240403009605140c82d180030090b44240003d407242211040c104034030344414450705048034061000782c4156414008211164aa0414620352042d29004080762030306081c4002d0048080e45502e4040036181100c12030156040c0031080c0092200a00032581ca401010502c01c2c40d80c1c459180c002080200304404c1c80c01444024190761040c21403c81d00e42c0038800000300507000d01300c950202c404003035403040126928410b0740c80080454001c0382c0c0d400758451190304016000141e900640341400c0c00324a00111004086005807000780c10f010042108100394800d003007140740d81c0002d8a00d5807805801103140d0780e4a9124250402041c40e00512 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 197781870 1250 197780620 197780641
    0x21306090f050402090d0803010807062601030209060103020d050a0b0f06131e1205010b091b040b0d060e070c030905010c081c1b02010b030c0d0507061b020402160605060901051503 79
    0x13070309a1f485840c40340c495843d1501103031386003050f010305c1012403042480e0030804980c02c08040322208a1929016142c0e00f1513092100c503005c05002e6506141e0244000c1c0301544003401a18401c07410090b0006049500004100d004807020604a014800400c03040310200303003028030030065480c2c08840248c038000d004150106200180d100302107003000c0c1d080207801c000d8103400104103003204907400d1031107440d10503030500e0b001e0350400d00140210081008012000715007014100d214090b0b00300040003a50741e00b0450307084071700710380c43c00015214440283c101a0007510030400b404080ca850380c074400c11692408014800d624880004003c046012001400030b60440e04060340c01a1a12900d40b10140c0080c0c00781c101902d5552090003000c400100c641882e0007402c0206404c41c00506003280351500c113590601c8500e404140c0c0c1410800310001584940c0010100c1118810310058030701a41e08224080750030251049125140341c0e0010015550ba1102c40c010203040c6101095803a04c4a12041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 197783120 1250 197781870 197781889
    0xa061e141b0a120507060509010203060a060e040f060b0415210216080a03090512090d12020a0c0b0706050601030e1b1915020d0201020306090414150a021306090f05040209 75
    0x100980f01c11001d8110240d80304025002c042d21030641400a5180c04103901d00341e020171100190031800301d18082080901c0740740e0b6010708100217130000a40171186510741090310115002a488804001410080c003002a210b10941020500c5d04000c000c6001d1006a0481140030b80103020307039008074494500701e075101040f05c4855071082d103031540c3d8803007040301a02801c8035540c1074509004911040e0186128030301103500c40c1100415440c80c0e00b403543e0361041c81401c01d0b401e40046101d9a94124005041950008040d1001210081e10f40410b40360100c165000108503d0406082030145000321070300145012170104140720b2030310040108004208502c4c4a1030010344d9442201c2d00010321003d00c030b120202081c1555094a0002c148241d059081c0d11064072501e030400c9032200000e010964002d000301c0c00305400d42c01d40d41e81d28507400d00e030900d00d082522010720141e800a9110050300745044035a00412040c144a203000d480e140414021241d00d125003401030780c000a06090940d10480d12 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 197784370 1250 197783120 197783123
    0xc05070b0a031b080108071d0a02160602030112021315090e100f02040303020c01140301050409080f03161b02180603120a090501030b01050c0d0c0305090a061e141b0a 73
    0xc54801c41c03600390004e20340c0380203105582c520301850170702296003041150405c58103842e10010041a859080c0b01c03074000e500100041680322262446400003902d140000d40c028061458045140f083c41d0041000c069801051341741c40034506904142c60200c009840c400b1160109400905c200d8054601410308c58041810b0346102e1508400c00c0d40d240d81e0742c1c09001603e010350300720340d00780a2200040d1200c05003090400441c50013440100554502500320111892003445118100046a90204000e40080e039203c8221208404c03501080d941c44a446240c0180c4090941d00c80700b116000b1400e04c04445d80e00399a40014200014060b440800c506072011400c0c0b040c80d65900e20518004003607141302e0248500107400c14164101542c840c1055944010080020300450000510305584074080180d0031801c1c00410304c4424216990800b101e40184403644443e041a440c0221705260900f01102050500c001144841c08466251081d0b640b1b584a0000e0050404444040d0398908403c3c1c40c5c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 197785620 1250 197784370 197784401
    0x60f03011d0703200604150c080706090b090105130206030907030503030f0901150303050a03090606090e1f180f0c050d06020c0c03011e15050301060905010501020d0c05070b0a03 78
    0x30103106407400142e2804480c09900415811101030f030b00c03519038005010420b54803410510060000e91010703c1280f209201d5400c0515050200d50b407100c605070005401655200d80d40c41c1800d0a01241c6550103600c0901305008110750703c1c2402c880512520980c4010f4080c03880440000c1c5020720070801c1c0c0001c2c5070800c003165101d1801c8a980c0c0311051040f58640000c1d4241055406201c11003401c400650b035040e2240f43c02c000c04070608500034191028103035081c40d225100095001b95521a0296000b10107014140d280c1c0184001c0703030000303603082c02d46c0351461400e500c019a420204a071a102c869101300403000043c0c65041103030a0640d00d800842d400440c02c5825010044194010420041d004094601a40710074003054200c0d1046c4420044800002c483c0c100340304a0b941c02207514112079502e5045c1c403503e41c80440d00712103050300540d2200f941d590040c0150b42e0104400f00b01300809251a5002c000c4948c1c559445024034498111141e502003400b2a140f802a0800c0e45940e141c0c0c1c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 197786870 1250 197785620 197785661
    0x501150c0804180902010207060f0e04050403050d0908090a0608010f14031e01020d0b060703080a021b1e070b0301270f0e1f020c070b0f09030d050403031e08060f0301 73
    0x44202c00505010134100c0c0544a40500003422500174080280202d004da00c0f0400311340000001e11000d010011702c1201040002c03c1410051901840b89104e268040d6075603a0b110000c0c202444270214290300003c041c008038500401507807140012200907035000d8103800380e00380140c4010902c1c10804020b0300f00060040860000903c00550143c03002a6500b482030280c04d10100602c4002c0c444d1290250000700c0c1000043e4510a2039002405451b50b0ad180036010340d01900d5150707091a000301c0d40b443c10796210300b070752445004c5d08000d02c0000c0e0995540c020f2640d45800c20a4904582c5884410100461084108100c0303201d54030406a00c2c404120511888400d0341c03280d51550080e4046c824056880ca04400d07482c95144251246510701c0c100611880c2c2c144090f110094001e80000482417130100000b6001d83c0307051002a01140c101e03181c09403664210301d0047e28000b40300e010b0030311480500b41c40c480344a900c0080c05402503c261b408110049aa8000c6405041c0003400303140500d0b000d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 197788120 1250 197786870 197786909
    0x40b0604230406050f0d1403071505010605030705180103020f070b0a1422080c01060609080105090307111e060a0504030b0c030f040308070c1b0311040501150c0804 72
    0x306404541c41070703524641c00c8980002400c001c01c841c024051345070001840c09a82e110750404200a103412402002d003981c071404c0241d552855030340806000c6400102405251540039024002c02e8090956410b0007415440d141c07400a0850103500c0c8120140200b16813403211a902a90498503035441d8501d03c08c2d607842340e170708166800f2001542e000c4045450281c201e00000503200b89103005800c8034014200da01094804003009550706517040da04410b040141842c201c00074424907009050540341c100200c1c0c588641c582c2192002014100580c02c10011140003034202e8048050404049a08101c0400030b60089920019032000503a0840000518000032a42000181045a204002d05200c0f13685030442000c1034003040d00c032400d0070313443c004c0420f0000340920003007a0b008206180c16099507010381c4400801c0c00195600c4103404620a000380107101c4041220003625400392010b010315498001220524003081103140100319222600c581003010203812280203110000030041c1c10740c0030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 197789370 1250 197788120 197788139
    0x603100e1302030d0201090b0117011116031d130c1808032a0304030809030f011811010c030f030c05040801020301080d030509060f070e0406050d140123060d02040b0604 74
    0x540c1c805078403900c02c0d640f101950900c14010005440c0c2e20180d001d00e1a4070f007060181c1000d9400d00e509110395210040381000404403000381010040b20360081c641d503085805c02a2045040c86e180383c03000554000c917120715881c3d1070358103080c02080e200b00056008180d04103d404112401503580303400701d11074001900c076600002400200704020650442e00068000315a04110103403000b0045802c2030200b0004101d2a0300600210840501074507130b5070400d680010b084510500042a16240008a580900211032120400d0500138284003c01000d40d4030041c145076041150b940400d52600f118985a0b171040c0251001420400000c0d903e03940c41e9004117884103c2d9814400009190100040c1c00110000d09207010f09503600320300501d41c980040032544012442e160030f41240e20303240001940c3c1c4072641c0a00c585401001c80c0303035060285641007030a5076115051000c0c16042cad03200c09880514000e1000b500080104c4020042040174400300b00a0a000042103512240100b40020081d20 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 197790620 1250 197789370 197789401
    0x10e19090c030608070308031308040810060501030b0f04090309080a080315040209130c03060b04030b0403080f060a05010c02040e0d180503120a0e1906021b03070e060603100e 77
    0x400101070207441d40e00300048048810900c40c2e031241354045402040822500070080d44c110150354941503052290f619660b40c243d0203a0312600725580101409007195040c0d00c16413001d04024039003440b0303450f03011000035650110804818811507596910030300b014040c1c0c641000410303042d400c0d00c020b418503040c1202d50f070300201c80d40c02e14800550740d00308180c6054400c840046000501103038001c50541031010050007210451424180e488001140e0002c680002e030004520331004c1d08036510b01440c00034028103020700425000c1c2640814000160b80361425682525000e18080c6030507181c50000138054000c038050700c4000d010700401c0040342640135181ca0403001a2001d4086295034660074940e03284104d107003083c03c225082c002104900c3c450f2841598045008020203100c40401c4c9104e004101c1c158420005a0b02c43c852480c24402042c0c0746141c030074000c03005840f02d580750142d81c07408030000400d124400c020000000340c3d1100228040006003103104840704261404460401203042e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 197791870 1250 197790620 197790629
    0xa0b0702210702010512071202040e040203010b04061a0a020c04020c07050319210201020918310303181e03120b010c0201030b0102010b090a0b0411030f06010806010e19 74
    0x5940300a001d4190301850440c0d0b101a4181e5407540f8005e1745508418040001070701e82001c0000d0f0038100d079203120b11400540007510f01c00c4803444a03070400344109821160024440d6000300d003401c008101140c4e034041803084242c10b2401041e0344905480003241000d40c2c0311a0554407500c0030820480c91400007d010302582c2c0183c0031101100b15040c0440b955090413007000b040744440b102590800154140f000c2071900090001500306001c00d0001000004210400030344040c6020410002c0014410780d1040024403850601030028218001c14045950780c0010703090544402c05010344041c602600e41c0a19001100f03185a400740c030722a90b00098203100c01b03030000740c0c03000270340405241d03e803044160100c4141c4800000440c03e03401075003c2d250b00109141555600c621944803500c0311200d59103d8040c0b040c00061003403620341040700715031900380480c080e03d0090040228107038100020681000b401d00b4034410b55501c40340101c602091801d803881e00441ea100440a000902452040558 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 197793120 1250 197791870 197791903
    0x302130b040b0102281a0901050910060e0f040f0c0303050904051501020d1116170f070303050d0203040f020402040603050906010e19020c01020c0706091d010b0306120a0b0702 77
    0x324682c0120303650303200240b02d8a105d15040c1d4100706080c1c0406074940d4064450300103100c0365203d5a080310740c5850100e43c1303070a459442d8001c0140c0403d00f401440d44002500c02c003001080d00b080164082860300078000002d006901c4042000d02000700c840441c0240d0240c03002c82507a032a480c0042854003e40416806541080301040101444020510310000c040c8c1c02410f103207a10303660403100b4607206a01591140226603110400f21a4850098060004079445020200c401c1680b2403030040011f811096542015501f0700000343e11504907040c400f064200507842c4d032102d041580f03013901030885c02948072b81700107400202580c05070412130bc10612001507607540e80c0d850010080702c0c001225080c82c1030100d07490040503841554050f095201c2954001070038050003a43c1d1600c0c00e803494001d080419030f648410081005170b030300c100314014405543c050040d49401d1100c0b445000103040d0b94450380c04d0300510401650100305a54500ea0045400151400d24481c080c0d1030b038150a8103404003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 197794370 1250 197793120 197793131
    0x40e1609110a030b010c060e011d01330806040c0611060403090512030d05010b040806150d1106090a0b0414030307050c240a02030d06140d020112060302130b04 70
    0x6204a07481400c01c08550038500a10706805100100c0c020705083c2c80d5681070180d200e0146000c600584546101d500e000400000e0104407904030030381800e000c14000540340e040c400000010310340f9440d8000c100c0e003404200001c08409041c81c0a591060303410608080c41030b20100400c0c003419903511001c80b802a02c648421521080781c03291103803c1168040e011031240c03d0104411308201c5a8140008081d41c2070b02e08181844c12090b054030030031f900c04580d030400031800380b00918090000581102c0d036540303e0b41410000f0404140b003050200c0000c0c1c1300800720032010040ba03c50904840000d2001070450643c9070302c40008411742c2d082070062022a40b2080b0510010742400002c40c2d4072550010000e0032049001020042c9113481402c0111580e825441c80181c205100300242c00c02c8503103600039540f0b4140940200c0308951841e4030403c401d0191a81d1a201c2d0344421001c29421034080c45c0c0b01c8a02c00101826a000d0032050703000079000007012002140c2c04280791301101040400310390a01c40d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 197795620 1250 197794370 197794379
    0x150e0705040e01080115051905040e030c0f0a0f080703031112010303020f010903230705030319050a05130311010608100603060501120213020a090914040507060239040e16 75
    0xc80300740c0d01451b0300440462005000030f02e854500b207000b032a02851814407181e1a880414159207085550b04a143d101281c2107240c880c092140c19589001b440c014505461540c4561828840c0b4400140c01c0d484009406000c0c14803e401c088090400807898594441d030311800c0c2041d21001348070560060040d9000e07410307088410f00031201c0300345d0155103100c4103494030b40324440811204241c0b0107000004103d00000151306001441c0726003031400148100001c0602c448085c4c0788024414254240b2305410050800c0e406080d60000c41e07090303c4e05d00000907920b10301070300418031900030000034411130144101c001066040541620301c540010710040e42c0e1078548034104080103a000394020aa0924003099907101d9000d0f142401c01c40c5001104076941c7e100220403500c4880d158468030400c0c1c81000148102000018014602440100100700318149d001013440308002c20601c031003e01d03034003801c40c0c3c06180c1c16102582c1002041001560f000c94481652040c1c82d08019030001030b558000a03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 197796870 1250 197795620 197795623
    0x27030e04020f0f030606210411091e061305100302040e06060105040501050c0312040803011e0302010f0f11060a05040c14060a0309022103270d0303150e0705040e0108 73
    0x2003118814020640c00d06500444a00044d08010901c45d0001001e00002c0c0032030307810440203085901507801d001880d00341410302004040b88001414003d55010b41480062200001c0e01c0b2940c10a81001134000e031a000c000510641442180c00040d500300801d20002003080c0c1c603d038048070f00c215000c020151008000c9521072908440c1c50b800b08006000401c059405803008000203400c01050301d240c261515070101035080161000d84043c00c001c4018026500e0540542c40c6031228901070b05078981c03440d03000800c40c1c1042c140d200304010301404164100382c01040740030420141c40c0c09a0768039140007400da200801c001c83c4c0680341c3d086203400000c3d188402003001c01d0311020242c642c40ca0074110305800e0f405009143c1c1c080383c110b00c14000c5494048400f4010401e4400150007642d614601002c04112030308000d1606420403101c0942541c05644244a00c0040ea43c582004168901481c20021358410540d000c030907807003499401c01102e541d118009000362070108500f0311807071340c880c20100d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 197798120 1250 197796870 197796877
    0xf13081f1812020a05100b0f0301050906041103030705011a010206071803120e091e07020111030a0f0e03030406060509070c0f0311010f060e040b01170a0308090127030e0402 76
    0x3260034070301d00c1040004900070000c0d000071a0030724011200c41c10300d01d90f5480d03d0000401020a610760341c90740d4110040c6070008190076403100c1200207001906103095841e40710750026000070086400518102c04644040c030694900320f402600030060100340c200104901484511014018091600081c060501031060315010324501c0381214005411030381c075060020944240107050016201c44020640d4804402c1440b81f40c8501a0b40c50850341c600003a125600080c0144003564144840c15031103681c0b41e4152644003c070b0003000700e90038840101e03a03c0288200400301c801400b0000800c01802103941206044642c01d40e8082a1607882600c00c40302c0c20340a000041001c58030100344008a0b100342d03082e1760101e003424000218401c01800c404200d0b01303540d000c580c11101ea0340801c002e01c2520568140103060302d0402c1d80c4685e980400b180d4a46101080003001d00100c0d202250301c0890940c00300700c50b400b02c100c0c4011900d0707400b8244440520003180440000d2510188840305090a0094 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 197799370 1250 197798120 197798141
    0x10f06120b0a021c0903111005070c031803051e060105040605010c080703110d020a0507050301020c070621140105040c030e03090d080906030c12010b070201140f13081f 74
    0x1032000c00e4454040090195000b00f140010701c4400000c0c003411800031788a0311565500c030392140700203c000300d1035480c14504c110792407078080c500c1d00041000158000c070114105584c1407030a0101d103d842840c07402c0c0f8220681000d869403041080b0600000c00c00c060300000c00781601d08461036681d03504104010b036038080c0a018006001c40c000040040d0644000d80302c4240300c5e0a100f070300428603444080c03034142c800c03030f545c40168070034800403052010a1007104054130342900254500205841d8503a40d503205071140300e04001014440c404001054280d00401510400c001c2c0b2030b20b4002c03503c4151840003801914801c43c605000c58001500074030800c42d0440202001d1814034000301e0402000340c20000042d6801e5004004842656541c40000d510035480c0c1009151100070040c1c00c0c0c425408140c1104004100820820300980c1e0170040203488100340c46480d030b5540d683c04607980e6640c0503091052644100344d4101055140c80030036007111140020f12030403801c094194136501a81c0d04640c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 197800620 1250 197799370 197799383
    0x120305011a0a140d0e070b09011409040e01050910150308070308100803070f0c29090109031523010609090f060902160201020d030b0607020609030319020601030b1819050f030408010f0612 82
    0x100020a80d90758004c0c1c800c00000400010720b61110f004903500f0345504300c890051540002000c020340d0755603481002580c00fa026004e00b4180c1c00d6984d421458403030140040e0900c824040064803104011000002070b15155003607070340f212040e25000803c26102003003250a69100e00000c078446940c642c210040c1d041c0d014141e9414074807048400125400500142d041100a0380080049401443c2041031240350f20070000348001c007a801e8180702d4540c1131040314000c0024004000c1568091081c10a860007a039000404940b00d0644030020070342c1e40e020510b00c1303001003003c0180b525208811509603001381c007036900d0f40205104c22012a8031808807207502c454180602e13009070030007001400b0300b09000f600f105d14088009542107541c2c8141285000140d10080040c07040001d60718425811069413110404615a042421900c0d065490000e01702a400000e4000074410200094520002414140d0f59103035201d01e8400c0c00b030411240d03500a9142044000140844001d10098070141c1048 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 197801870 1250 197800620 197800637
    0x70e030a020d0204021e04140d12030b01231b01020319020c03041208040602010b04140a0b01020a0c0f140d050c01050a0c1b03120305011a0a140d0e070b0901 69
    0x1d0030054001e020a0301660040d40c207101c0303500b840341d42410b001500100107540a4490385455292103001a00c00704032405641410710a1001501140f00081e003113000f42004201a04407000403a5084c9007d00c4001c0c0d92261200c6c0d912020200c08000c190b101c4550820250701070365074401d5400c0c0d00c02501c00202003140c035034991001e82040e034054000d035400082030fa45043e0b500d008420741007500c2c001c21340c1c2801000600700903042c1c0911880048400c150b80510800303042d640ca943c90704c030004040c030b28421b458941c19010b580c402e1000b0088030380c3c0501e61710403017a1190151100260380d03020700c002c070590408980d129841c108505031f4003544d000008021280001004448503000780c4400701c1403081640f00d0000103140315044a00398003070720000e0b50100b403070740c101580c070402e440300100c05040c540b00040c003141919415405c100c00040c0b070a19640d4500c2c8034101c525055604448104103c04903170588a00c02e1a04008144880c240468461075243c0c9100c03140f610510071308901141051 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 197803120 1250 197801870 197801873
    0x9070302070503090904030e0306010f03080d0e1504060209030106080312010311130216060c050c070510050c031303030f02030408100908090315040b010801090809061b0f060f070e030a 81
    0x260000c00c0042d100d04252414255040041448800c00755000c40c0498612140407605003001c00c45c982c01000f40c00b020f0118540b56458401051280e002d0ba2210540c40f981040b0624208000c03c3c0501c1c4c8844000f0169442d0030f040807030003904101a410710a50a00400182d10070002040d00c0728145503040c9504e4903460344d602c615400059610203900510324088001d11048071344040d101c5c4002650390003100034441c0c54024100e81003241c0e5079080c0803003401402051840003034204207945090702e032500c0190303001034292124060b1290341e6660348000124240c80040b010300c007104480c0301e80c4800d0101d40700480203076200e01550041046651242042034030303504054224060107070080000c0c51418030a04040f074180820588205581a690000c1c4410008140000d07801841c0c0b4070001c100c0c5000690310702174a40301e100313000c41c40342c8004200c1d02555003840c1101c40312603049208860841140e2001d00b619803138110790180ca8864284009504180145c0000780e0042004003c0c2c01e01d034100f03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 197804370 1250 197803120 197803127
    0x501050615220806010603060e060a14010f0e0d06060815071704030915020d0f0f020d05090a0e0709080d0201090b0402060304051c0302090312041401051e04060f0e040b0907 76
    0x116410003003805060030001044002400139a003c1c04a03913074007148030303810000c46545084000d801a401048500030030406641400354201c0310003000d20700000151845203088803800e030029207165004001e00340440130044994000e1040b14103040c250703841052400d2001d2058038044480c1e201286d09418080203982d10201c0d043d034041d109023004d00102e1f4031a4007440340c4891901110f0302580c4244040c05003990000b00e5140c0181140c58008100304404000a440e40c410310300490500c00e001c201d4a98558850032041c0190484000d002410310f4021401410100e152090070000d02500960340200f81c41070080b0450142c002c030040c40036071115801d001595000810640701070103501c0c00708a00c0788080c10300640c2c0b8078040d640541c80304044000c2506015050700071000c540070401c410015030007900403280e2411001d0030040c0e245d4400a408451100e4608001c0154650005008c9800c5030010100307010301c03c4580e03c80c030808013244240000c0390450040c40d6805400034001a922070b10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 197805620 1250 197804370 197804407
    0x90d030201110d050106081305030f0d09141606080c070b06040e010c0201060512061b090d080435070311010504050306040c0503060714070314040302060d0501030501050615 76
    0x10910000800a88422201c00d1640141c010f0510350b40d20f4000420020b40e00108254010803a110802448032180d0b807040d9407031080c00041480b0000c0860154007802e8642e105040131038011a1600715150f65651503030711101013211040e03400b0700c501c07000304403503100707001e004d200d0980303240300500d00100ea07141d65070703030b10380061080d503001d61180c2041c1040602030042c200c8400342d980011130214208030030418440413100c4103100030307032100c02049460840d40000c0d541240c0c0202d1003542d148280030126100e40354900b006003d00c81c00003000100100c80041c644049414990740c007040350340681c03072440c00c02c0e0b0b8015040c1c09035029500c1400414418041c200741c640c0305041c901e2805540d00003007428440d045030160348001220900f0080ea04050050035030010282c80c0480d01c4030207183e107804031401350050140030003241c4401c204413900c1120407a00610303001426980c0313900744072070f681000c0d140900080302c0d19400d0130b0109801e400c20804014000034881130b814207014100a50246550 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 197806870 1250 197805620 197805623
    0x1205030a03020f160c0303230304260307021612110405072c031023040204091a060a091505040203100b0325090605040e0411041503060e12090d 63
    0x10800c090280c80303001c608000040c40c41780101821907031550402511003050000d6880c5079109000181d02400c5041d82241d500650000d40c0030304441c0030089040b502c2c03414080c451803500000082c40181500000c2d0401d0800c01040c200c2c2556032103816030069540f416000810140c0030605800b82c0c0d00e455040316500008a1415000300942030341a5212080051f031070410850089010140906003031141d484055002042030001440c00c840803c00222201e005c1c08100160300c01103002c55551b9009616040d4014440c0710741c002c40c80c0e501d96600780341511000d01c110312a4100150140b0380e070055581500c3d00d02e10040c0380c68540b03030509c40a54001800003100809500002c1a40f910410140d409040420b0405c4107840c40c01144000d0602e0401c0fa080038041d40380c0c01040b41d03681c040200d4003a2522544080029211803030608440e80c0405c911782c1d0701c5801c10f05450141d019101c1d01d4400c4900400301800101c1409a40b1502c3e0043c5104100c00e05030200084075460510303202000074039 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 197808120 1250 197806870 197806897
    0x6081c050c010e03191706060702130e0a0c08160609090209041104140a0806191d071415030f0406020f04031a01030b060616110f0909030a091205030a0302 68
    0x303415240700f83c2580d00224900702000504c034081c1c1c02059201c03030645a002c1090030604418104040024101c3c06403060003413081000c80c0c10500e81c0c2d20540c100b4040002c0300c40884800905600c1e20441e401c6d03944c02401c0080c41002080089a01d1420036082161082d0b00d0b104800c03800c042c907501c0a90700400509400c6a102d00ca8003041095800041c00200060729400b04881ca200c000c010038181c181d440010741c2d900100a0140b10b00300c40c4140c01122554040004944900c101c0c1100e810881c03486902e15030003130010018021800442240405008132050355004500c7d0801c0b1203640000d85000544503030708400680011200d9000f00300d40002030703042d0fa0505a582c0d541e00c10741882290841c0041a0f903e004004111100d210643c005208903415400c0104120400f46000a803000281410f601d400c1c500103070383c0321444010251000a00304e100e4a01c1d042054a58941c89483d4043c0005e10304500011a850307c1e0307603e400f007140c2c42409145001c09007035080700a50007603020301c0d024 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 197809370 1250 197808120 197808131
    0xd020108012309040503090f0303070812070309080d0c0e0d200d0b070518060406170a06080307031805090105060403061a040603050a03080703110d0f060e040507030606081c050c01 79
    0x140c0d521008003e100c0c0317101380000c5589080c90f000f03100c1000c14910b101070007540140728440c00201103006540d01e07a03d0300c44c0160003d9944000c01c6025140114007c2c2c0010f02c0041d88084c040083d400122003401c0300c0c0c5980b42e0b04040001070010400d52481c014282003400080d102120f07104968406222200a0600341542000e0312008440001030f51440045a0300085030500c43c90340d0910300660507801c4840c2410b051405101400e00400b041c0c10040d410702c4040041c2007071806d0350000700500078180860351a02141d10b00500030b501a81c65081e90301500e010000390910b1703c424100e05070348003c0d110780e007420710719500c22002c1e29002d19040c5140c0c96000b08203055468911480009500400091503044518180070340501e90190604042504000075030321589002c030101d4044804002c0f000412130003101400c001011560002c1c00016103101c1400184000002c240c03050303c0c003800d42002201e81d100c000668491203040444458141001071410701c0d400780c00a004c1e0b12100200110700b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 197810620 1250 197809370 197809439
    0xe1012090b090609061609181d010204050909010b0a15050702040908070624120303020d0609050f010b04030201021906140a1d0303040f0215160804060e0d02010801 72
    0x350040e04840c2c04545601510800c006004204880f58120440c240722103155031081500404012090003980d83c03da05c030054070b6645c0d076220b13802101401030900440391408501a0464082d40c068400c0303d2044d000400440d020410602c1050000c081c01044126200c0c46c000031b5016519074106402d05110041c010003026031901c0c007e980715984205605ca903622020318015044501c1704290303c01d9009054001480007a410b403141c0d090750081201104000c40914007140644284959285583e04141c130008015130b154028501a00802c0703200103140c1c3e20307411100d080380a2880080d00580c004140c8142da15101000304075500e02411001c502051010380e00c984004c0181c5850242d296588000544803a000a005001710300c0080658514282034030780c0f2004801c1140068480c08184450030000c01d80b8508580f5a4007000050522944050612120030341040c8a410045580d80d02414400e20307080c03c402079650741c141c45800035a400e0114000c00b10084a008094110720b00b1030400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 197811870 1250 197810620 197810633
    0xc010905060d0b1f0806100302070f03080a200406020d0513030f02040605030d020c0406060c11060d020903061014092203020f0f0c120708070303030e07120503030a0c0e101209 77
    0x5160080d81c1c0300e908950901d0800c7c8840104451400c4003010300c18440500040c0840740100b0090390140b41108298a42c4041040108280442c0013100310414181058022071440a8812104150262418014500c50030b450303c3c452a40c07040c5c00c07000e044c4c0050000984001d5030903249400a800000d0f01d40d1640c0103c0e1624803400b030000301680c44101e01c5640c520302806900060062032504100c602920303983d2491803017071000703407500c207a40103e0100b90041807030f415620220350007421540c1900b00ba110310012030060740a02400c199400400105a0804100b00b41c020f0895030300c1a019180c0303503906814900081c1c50100e08600440100508410003081900007180108002e000602904020440481c01c1d5034802c1d045034005407000c00007584c0116400e02203a8060030040392030483c071101982400c0c5240c2001d620141c13404a0340c02401400406188030310b49140302000f540e1001042551025403541300303185e1080143d2040412588030325030004610030300c91004100c400e110364a06 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 197813120 1250 197811870 197811919
    0xc031009050703050421020c2223010b03070509060a0c022706041a2403010f0305150411010c1509080703020d17040b040305091002010e0c010905060d0b 67
    0x2c00020761a68140814001519071907943c1d240c0020b1442c55005168501a4542450300c010031310071a51080501070b1020a003411812003603030354a0800c5182070b40703903010450806100321b0f40c03880340059001141d04841c0400316801103090352642d5040240721010011107a001c8010141005501c4440c000161258904442d00c00c01241d800d140040468400d0610800c0080003148164140044417044c0c3c4144140e1445100060710114401003076540203608485c1825a01071111000000005810031000044800e4034445c006480310480c2e6580000745c00032050320007410b0950600880009580143c1481c0c09a83c4251140b8000c1c0303003081011411070341c1c089800e4585150008201e0109a03040c4440d880c03110480c242003103000741070780d960854243c009100801d00501c030004181032601440540303001d80d0303004041565134201c814009003c0d200d070400d0400d9511030603101032015805041500c00303451001e440c05007003a00303220303002d4081c06800c60704541004000d48441304141061454 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 197814370 1250 197813120 197813131
    0x8070213060b03071b0c0e0636060102160501052a070303020c0102070f120f060903020f07060e01120b04110d05010e070c12080a1503030e030d170c03100905 69
    0x1c0f0f40368505030304094100034a5580c58440700056001000006a115200100ba54064202a4038540c4c03200f001c00d6040500a04041c44e0f4400640e1581164012500310407200f28042c444003581c0d1210300c01a40c0d80c0440d20508808032840c0d15040c0215445000a0644100801d01402c0c0301c01c500700f88401103030380510881c091a00710402c10b00c10305404100000c2a01000e01c010300c08a89428548204407a0b0707409403400c686204e0a50f10706221218824810690b0054820041d41c060351134046e50b20240240e4004040c05020000a0354502910300c2001d41d84042e15031101340c00d01a54004002c1200c230740e6a5900070303a644004280c290100c00070b00304903900b085d00096071394148500342036448401007e070020092110503c0000407007000584d000e00c03e140c00c1c94552a125401030001803c0017404416500400308000800c2c0b59104c80c010400030000d8080c0d948410480340111b407402061880101c0b80701c04007010807206148040256400f102c04000000101e40304c03920402620000d480 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 197815620 1250 197814370 197814389
    0x915091911120c040506030c2b0b03012f091507080705070b0a12020a021f0212011202010c140f070611010f0c0e010e0a08030409060e071b0807021306 66
    0x1407015445140102c0140c115080f800d02d682001c0c58000020031510009001402805010405c1043c1c6110712052629140c002d007016020550b00c054031034024800c0e02c415603c03070743c2481078604800c4030551080c00380310304420307451410040825902e062030740904002c0c0c0d04404003000c0071410069134800340040c00e04c0b94600035503030f07a140d06200d440c086440d04001c104d041304004600740c0e03e0308041c440080a00c01500540c442d031078000e050707040003500410200c0ba00690900c403200b000c20365000300242406104020400d03600c8040418402c0001c1600a000c10b041d040124082001542043c003ca0704490403102003c0c040310f440343c1000f8165100402103800300c4400c0462800a0280c14007080c0100003c10103028040303401050800c03c0d030340c0c95040c002c250100c060341d80c07141e03403071f103400b074a1500308481c1d507a030f0713214074020040582e84603e02e183c01c007403400b0400030b0303100361080c030381d01102c002c00c680c442d65098440750410b40c413000c012640050103508081082000d405282e00800c996803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 197816870 1250 197815620 197815627
    0x12030307090905090c10110703051f06031a0c040b120a0c051e0a0908010e030d060501090305060705301803040e13021c050606010306050915091911 65
    0x403406810a07840b41c0018001d58200070401500070400604408801c41c215180d460707444400c003041e509650b4451107000301c3e005104000c401d100740052b0f055010524968049000e071500d820302c800311030107404000c2c0038a03c0c0080e080703841d90344002507075007103102d1088031440d040d600c01080b000c82c0d1102086520203094541003288089036885204071001d064102585040e5550000182d00004144c240c0d030040000300300260010721440500003d00b114000800001c0041144107540307401c520500b83c211130808101040302c1d4450700c801c0c02100c0d4020014101034590041c240c880340c0041801c4803900c6083d04100e01e2418421904a412039000c8448519505000302c02c0c40740207180c02201d1066a208001c20032508030000c0c030300c03a44004046102c0c0852802480055039200ca07a03039814080405100090040c0840498045e020350800d89040006039a50014815040d02c221030200107030406140051084c180680e505a002e8030200d01a0762002584803e94100c0b00500aa840b40d07800c0070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 197818120 1250 197816870 197816881
    0x105040b0a1503150b0703050702042c0718090c030609110a0909021e010c030806030a05030403030206010e090a030e040203281406060c0607050705010f020301092c060c0c0c120303 79
    0x7070030500c007405c86069854a88195504e02410f144641000240220380e01d850041c07154220056040342441c0760203000311200308010a45aa81c20b0034010390740000201852800e48003090b01c51807245e141d2000007000c01a195855807802890103440c10ba070740720240c2d800c0c59542d6a03070005e18405081001030015141f80710340140018480c000608030b09590011a940007240e03000a400040c10b541446c28071000e5880101081c200415036800601620000c540801010f03000320340c16041e203840f4440982c50f50380b409c12107561904040c40103404105140d0441c020390074150000d5501c9219110280c0f040c4582d45401d0021941c00c6405c80e108540c0c07000c90020050600075002d412800480300c4030300b0101180c103696141ca13030150000080c071100103076501c20441e080d0003400165643c01002c640f00d69490002002808090340c814030180007642d0602e40e400120001201101c400c1c40c000c210b2980ca01c3c0d09080320f40d003d42000364562081c0844628030369121400c120540320018042c544a0814 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 197819370 1250 197818120 197818151
    0xa09060e0103050f06041e09031e0e1503090307050a060f0b041109040c26040b1609060f1404090917070f030f030212040507060210060e0105040b0a1503 67
    0x1a803032250405040400f4004001640110242c0000c01243d001901545089500e025541c0c0c4c441c50051681c1003400307030b40c241504544400034015031104100b41104195100f1101203e074000c0e4150b120382e452144180200007000990380c03101c9201c0c01c8a252560540340c4600e000c6c0784c81c400703c0f010394031100c4024441040e03000c2c00e9400001903806000504a001142c61a0300480401d41d02a036a1080d060f0b01241c498141d5006440800d5601c1910352100f001c1e04103140c0e42140c05640d84400c5c0f4010a030301c10314814422080c00465a10b440e030700d0342085d07021140000b2820210040007404020004040c0d651001031000f0a03481c00d0014420402d8500304410043e00071001000b88820300c00000450307070514100d06c085606240c00940e034490110103034002d0058400303540d90a12100c08100c100080004e581d4141c56940d002c650003c5030086503d026141c81c0c5c001c21b802c4400d4200100302c5030600350030082010340d004040000f40c40d110a440703a40381c070b88210b11500081d100d0b44071101c501c50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 197820620 1250 197819370 197819387
    0x901060812040303050702090a1401120204140405060a09020a05030d1d010e2821050f01021801110708031204030e090402010e190f08030a03050f0103021f020102040b0a0906 76
    0x40040020b08152658802070002e0184101c0a4000d10303100001a03a401c81561000325604210070080c56296103600a08001d031030106e13012030040d4079203c50300700f1446142d1622485190700000810b21a954009510007600d1400c100f2038020200c0940824503507020b100000c52040d03250b507a99055007071100042010b1132410710303840c180610324171040703803e40354624501044410a0300d540c45603485110107259111050384105070002c41d24500c5102000411000071143d4000c41c100c61815400d040e026080344510902c0040070782c01c0e042140c41d81d5004181e1041185500d01c250f859080c1e5075850141160700074403070348801000f030780c003004101030b00720080e43c0441c2e07004e80380403070329103050350001c0d00151200c95443e2260600d5843c0903960364000c00400060320f00c4104612030240e480c2802036a9401041007540403900344000035a904420580d0581241d8004240c1101d020010025480003900e01e009642155020040800c02c04c20a0700201090100c3d650380c81902450008010000c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 197821870 1250 197820620 197820643
    0xf07020a0e060603010b0f04080a0c05030610150311190f26010504090602070213020301090b220203090319050a090602010e061803040905181c0206160306030b09010608 74
    0x401c0300e001e01c9999200c0328140c0741900c960741d902d169075a5039520b0401040c081c9034000c01291103505461010840a050007008551069089420035201c0008043e032500b8a0700405158050013036544a81900c42c1c1c01000e05000d02d10700591070105420b5010300349229004038000443c900082c0f011042c2c0c2d0001d0440500f01005002c1500d040b03200c0c14400801c48107124140c403441d1114658000e0081303680c100c1d406968002e0200c480324003030100c030310080d406c03d1181041c2c03145032051300071603818080302d800400402400c0a40b02102a102d280000790400390640000c3d00c0244080003a140ca01d411000038150640c6030707243c4400000100400989103500320b4011139040c004156400c1100090f03968000f14944072603591b980d5180c100510718001c0350701c008403040c1801d0902c81c1c20809114001c0381e413103492050b1105a46101074080c41c0d241a04400c90060b0b0000c4001940134510414250400d86580341c0810219542e45840510510644026034140d41d60042000344550411201061b007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 197823120 1250 197821870 197821889
    0x20d0903091e271407120908040b070311070b0c062d0402060c0304060909060602030a0504030605040206070b0a0c0207050a060f050f12040312061e14010e04020f07020a 74
    0x40d844500160002d014882e0001803c03a40b6007008105180641c0a5422880340508019203c0c10440c41c99001c201600e80d030b030210b0641c03007462070f42c003065000d10b00c3c0141d006004103240c2032900041c0d01951784545420f40c05c1214000c0c00850f50395041c0406d034028600b04500e1901d4844450300303503080c041c0142a051003900500c00b08840843c441e03c00b0440000d100740303d1040da60361030005c01c50501c6608000e0029000c00500415001d1300200c802043c0d030780c042c0d0108021074480b0000d99032482a1150000400d4083c001040098000e800080c5d00500c0034006608001407660b9000d14100159180740342c0c907850700d4003480115410003214001384811100f00008614220014060010b11342c1d42070100f00d40080d036084012400740840e613400d00041259040e5261509004080441c0054840c000d41c3c241440050403184688607061665103281d000d244041c544291040302c02702814080b4140000464495007607611440641010003102e04607540d038802d10b104018a5800d00d030800c4060 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 197824370 1250 197823120 197823149
    0xb1303120c020a03030305040317090f060912030c07030207050a0e0601030e010c0914010903050a05030a1e080703020a020a0b010e060a05010503010e0606030402010c050f07090e010504030c03030b010e04020d090309 94
    0x541d0350f034485002125094240040c80380c4031410100c0741c0c103e8826010141c005007406101468000144c80e03000d07225603006030f071415112140c1c40c07600ca0811100094803480e050020030550904075006020a40c407034012101c2c03413aa240c0201d54200b2040c0d100300b0f200c80b142401c20003a0350f09400382110030303507440c030007002080d400e040c000e40b04540500405144002c83c000030003180c0d0195440c1341c0559044402c172500c0c505240b911560f42c4e88031244001c00100701c0d10010741d802d100701c075400a40c04038030b0b124860207a8a03940c0440094214110b020f0031445124100004101002d65050103400c1c01c038020303200751906200b804100c80c111b5000c80d0400108000400005400200701030700803804640540c1e880d181c90004032403805000e4406085405202803242c01000001420008ca0700400400c0c00a403160100888c00c0300e00880380074000c640409429000070348240e000014050050400010746204400420100e800501d84541040c1d0307903400540030705401442c000000c01c4401c2c03c8844 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 197825620 1250 197824370 197824373
    0x18080a050d030606053a020403050a1b0303142808070905010c08030f150913020f0906010c02090901181a1b071401060b0a050318060714130b1303120c 66
    0xb06081c0f10319410a444106c5c503080da040401581c510002220014155180c64480c1410b03070b1070300c01c102d0b400c0b18801103106000c4074402d036100d181011640c240d00ea0040d103001034444108a5031115403a8406401c8000da40c5003019a10504500203807480c5c1e0b60301d2031602d008000039080c1c6600c0d8011a05001203030401200249803141100d50224510700c1800071500c45404050b069200c911819501c0350110003040920404c40c0d01d203884d000c0c000c480f1001c2050155060040c285d0082e02e20500040701c030380d140005418058803150f00003040c00000503c1100c02160b010540280d01c1044a060100c041d4008550280b094081d1700804440d506c51941d091110391710700c25100b0840018014403000c480c80c00004d80030b62224004020a60345c040c1c2c7c4c3c6080c00d03402041e55004540404507031101110704000c007200010310611408043e00c3d1341401e40d4800d0050001500100340b1800e4207022400c010030f1952415000d032113948068031058041c1800c61420021444450345103c0030000307020451070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 197826870 1250 197825620 197825647
    0x301080c0f150a0309060209062b110702010c14061e010e010f0513020c03030a09061d030f070c080f16090c050a0c081e0912030c03070318080a050d03060605 69
    0x110795503c28180010344032040d28252019000c1c0310000ea074000804140307400c40c94050400d060401810155116120505103104400c881d4a00071030041000140312900c01540201c00c14415140a00409100b0350000100546021000c44158001242e03001c40200002c1a444000707025241c4082011070641c102200820100f5491280c24810302a007442d10300c80c10f00d180d040301d00f406604401c0d80e41e00d181155084000d03003681441110100d2404203e50180100c1c4c0010240d00504035002d98a0700781441d0780d40245401c054002c0d5a01c0b2400d000010340000100800c400b50310040c0f010700510340f0000c01c4449100e030103500910000d4201034070507080d954000c048078040040c41c00d001180145904005400d40201c01d008007a00c40e80100100c1441d0010010305440c040882c0c1a4040c02c107044000c90f1a0f000c0c06c0c04408450380b0903c04240081d0141450140c18030941040c11003a035651040c0503e0b041c080c9000359070030341024603a010407030741c54098175000d8040c4e400c1c41e40c82c140b8205400c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 197828120 1250 197826870 197826877
    0x306150e090606030c041a04050a1d0c0d060503030c060901060f060c0b0a0e030307020c040f060b18010309080a080603011103010e16120204030c051003060302030a060e0a080301080c0f15 82
    0x1207209100000c0000c240c04003a005440c0941000c000130781d1b2402d80d0300700001d07c6500902540e4801c84928400040074842c04905000c0751520030b1071400a81c43c1d40004c800150068a120241c4a840305004125528100f0203002880642d00c003c0c143e60410409537401c4a425400002c25103000420520402c0e070040c21402059900c10444d04680c0d6078420044c0080032099448140b03400004140040c1550000349035400c5501110100688030401c0150012510540301311504c05c5810b00040d240000782c3e1803064400001814046a00310995684003002c0e88200003c1000c6584881880500d00b0244036002c1500d4413441c5081c91541484074403100c0c264014105108072114003104692148074240c8140110ba5004003075440340d442c3e16005030703429510f0080c107006000c00441e070342100d48a8012482100d40180203442d021807030307450f10800740101c0b907000d82641c813501d0105000140000d00841c001c1c4440e10181c0310400240c03003000207200c100011079101ba021f10803c0511f60103c2c1048 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 197829370 1250 197828120 197828131
    0x1020a080a0e0321040615032a15120e0d080a05010f051807090317070b130f0f0f0b010314060708090c01110a120806030d0504030503070305160609030306150e09 71
    0x214400c0780c0c0c40d4500030001c5c200a421002e007c9010100c004100310080000140e801001000c05183e01c110903d40e005002c19031141c5024141500c46003051140507081450610714141800302d94400500d100d075140c00c40001c2c000e00000c07082c90402c11138528610a5602409081544502d03003482d00b000643d00304040810f125610740240c001c43c0b43e150140c00c1180003541e01c14801900d1840030501c00610f80c000a40c00d8942141100000749501410b614011300d86601410040480b415903c584a0b083ccd403441e41190802c840c00c2d401d0000c900408107042c000c600c142e591004c4002c1201003103080c039901820b15000e0012030710603c4201d060115083c4410346003840c060740281150160399140c00755014029100c800300c0100d4a00e060751080120380b1030f40342a81101d90050780b6071070071202c0f07208610015005800c18050342c07001910400042140807000700c0760926410b001c1d161403045416901044020950343d07102042000c04441c4d0841d0003400c80c0c1022800340e00340ea40840c0d90300000604 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 197830620 1250 197829370 197829427
    0xb01080a1e111b060118111b011a27090c0d0b090f06010e01060503060a0320010801060513140607080d0e10020705030d0902011101020a080a0e03 64
    0x84800641840481e01e8180000300d041c280304214018008102030352000d000708188680c1d40f80c21040c40500016168121030405158800f03103c05516100e000785481500b1039101c01c81042058000c4450311217210181480c0b500016400d90180c03140d000507803030a50590300400040455045c119403881c001c0c015603040c00038000c400d5596141c03a80c1400fa032034004582c00054580c011052140c0030203001d00c2181103508981911003103241141d40c89a0902c500d08910050800500070320f4414409075400c410090425400d090b140d5607404030200c1420f40c0041c00ca90b00030400601d560b03000e000d10b0300411007400c5c02da160070020701d05019030081b5800344001d10520b2002c8140140c036041c00703e640c4140c2140b415a1a4590408542c0103001e140c08000000c0c411030a907424080c80340e00c00c440000c1e9019000303600e0606010521070252415140070703418040c0c01c0481c011440000c0c0024081a01c00d9600e4002e0f516040e1289011600c46090750105984180000400c807810780381013044590100700e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 197831870 1250 197830620 197830631
    0x301271203180305130f080a030c020102160e1b0313080c1002070516090b01080f06030708010c030b130608120f0c030712110a020a1802131403100b01080a 68
    0x100a0740a0028003520610360642c0003540800d055004015085e000182c0c0038004205542e600001c440b81207034041c0c2038030394200e0300c413690000380160030010f000b5106005884220002e8500c540e21042942c0c044030408a401041140103504146c894a50304030804405045042040300e5007884284030303500400c90140021402207a00c0104039400c42c14921100540d5101d86038601030391200020302c040503040c4004030b00410a60860f00651441c0c100680d11020241e40c0c181201240310307000b030501c0c0d405004441c400700700110300b80140c45030b84400352000324140310108140035100c1c40b0039500e22401ca140510034002c030600454020a907203403201ca0940ca84401c00208030aa1043c655011818400041c1c148200841c041c0034024803041c588420034031000c41d00c03261f1345803480203100035804207090005000b0380303070150400c3d84444104603005042444160700c4242e48070050f0003109000b09c100344c400509160811070114583c034840002c2c1301244100d80040c011920180c003050146031030b503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 197833120 1250 197831870 197831903
    0x301090f061a0c280b04020418062003090a03050f160303050618060f1309020a0801140c0c0c0f1804060f0b03120f090604170c030127 59
    0x9801000141c410036601c0307080509000c824400580c8992814100f90041000e190581603a8018900020120100190f402550b903a120311030307054010400c90b841940c8030148224280031410260100b8868007000800801d19842c8000303041803140441c491903410001c10510000200b20514400d60500344103445c0c0c108500050014001e41443c40304c42c001aa490b007041c1541034024900500098030800c14503420481540040c40742190b040360001c45061081c1c1450406030400b550031002e5080c0018032500c25070016107200d405a00007a01d9030b4480041c0b40361900074400e515000031100e1305a515208002c035400b82c49101070900c4511034040910b0f8040181c0b24200124080780681c0c0442249241a06d401002130061400e115003c41c60250030244900f0005040b00d20b500036281b07010b04200c4c00429100c459030106c12105e030400300500002945580003181101a0300c919000781c04100608402c0c51300312001410504000c039a044100901c4050708003801640981203088800043d604 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 197834370 1250 197833120 197833151
    0x30212280302070305030310060318020f010e0a0504060905061314041205040e1807051002030711060d1107051207020906102007060e030309030607051b03030403030902010206060301050903030109 86
    0x244d9202a106000000c100100380b14a07c040c40141c2c3e4040c0c030100002e2100f0000101c106c8000c14009420090f01c2100e4070b8998001c66000303039441001000c150009488a021406866250344200700d001d481e14240540c500e800c1402c07198407800c05030b003008900241410302c80400380141c0040d2112601d41c040f050b00d5071080c003c55000e0181c02c8000d0f20142040c800d00d643e51040c803c12a020350103a0240803d40d0301d42030254a494032100d600031410aa465111141880585003527254031034400c001c0e404803509140100c246c844040015180c982c4040c0c200700d0304084945201004e0500104242c50047e9901900260400003d48402100c910350041c207a641da540320101c07038010045080d41034002400081c40e44141c6000d6907810313603414000000e041d540d006414070ba03a81500141c00107200d10307104e0030140020350781003040320342c7c04040b881c2150300350340c001d172400d50000382c0b0340700ca41c025560100800c5403c200d055000b006503244c070161958a038081801031425281d180d54034450b00840c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 197835620 1250 197834370 197834383
    0x905130c0506070f060c0503090c150d111c02090310060e01060c03021014090d11032506020a0207091a010f050d060504110d060b0a090317070605040c030212280302 72
    0x500810070080c0030320008000d07040f9041140c00300d00b5841030340c1404d40b80c2d0a00310bd0f00c2070a8030780c0921450516924101c00400343c51320540c451080309042c0715884410a07410840d035060040d081005a6900780401410300b40403a0246141703005003420310412890042080150444040b0300c2c0402e4036052624003242070103411501103455600344110802c00a02c02020b29000301040c0040300c0f0404c400030000d40d03031418030122421854109208488601d070540c3c0c90740346042140e065491a529690f99890201d801c42c10000b001070784850010302803001a4442c070041c1b10103900103020302c1c034919000200000d410012000800401040700070b80b800154020101601000b001842440c030305500074070603070b080078035110b50060500100040071201b250480744920038a55513669000e0841d02c0e6403001d070300242050521824100024008034401e4031a50340103500c01c0c8101600a480c5d801001786001d0388000f08001600989680c6034191000880b041d02c290241c004400140d074581010707420181c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 197836870 1250 197835620 197835623
    0x18010c0813051c08040e07020a1a0609070309050309010f09120b04111f0c0302030d060905090106050307060905011d040903050a0306080607050d0213080d090905130c0506070f 77
    0x10200c0c4081d50280c41d29a14070070340d041034642000c4503080c082c1d4021050b02c0700c24040c015070400c20040c0110110042c9140d40300109004441c001445a607800c00d541403142d0b0030b2300b07240d00710100780261071404a040c203130840e040d8035060020812684416071684500360b40c41c0c0c14088003280161045014240c4003006011441140c002d0260314180341c25050b81c109c4080301d080c0c071105818a4a49030080384201d1030030300d03010820780c1d01c0d0f402c0c48103507440306180f101070b000c0d840240325604400700b07075000c0c0d0000780905403000314080c20040c410f10f0030746c2d100f07822082c400c5d00101c100307012844c0e106000004807802468221809a069074060411141540000f40c00c2400c1032004014903821034028080b84110b0343c1d007008800d558582c9a902d035201903a4410000744204080d581d003494607000b42560b1645212540d4030541e898120070710300200e1030091404501060420030408000d0b2154075802454172000085100c040d03507070708061200a00441d4422400410003005001500141e0300c0e80c01e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 197838120 1250 197836870 197836883
    0xb010c060c030e0118080901050705010b040c11060f01060228050f280f02130b09090601090e0f0303010501110a050a0c050a05030a05060408090411211006020318010c 73
    0x1c544a04005014040089040340c9560900030820602c90700409911684e541125016003840701140c0110f0380d9a00c990415039541d902d80b001082c1c542c4d203034410500380d10101c1d100d4045540c00300c0c421034200300e0000d200d8105e1003021001040420307000b007181290300c040a04901420191011913246d0b044a13000050214402d02c01e400c81802400203843c8680d000500e1000907140036900524216590a900104400c210135400001030070312845280b5269900d80703001c1407486040300801c0030142e04a8600d503c5900080040281c40510300c83e480e401e1807104040c220030041440402e80c0c074071041c801d0398100312000540c880940810302512402590100135640c0030095402d00c0034620400c2d008980c4101c445040c000382501c1d0010744008034540c003501030401c030b07034031512801c039246c100300140758100b911400c004030f984556000900100c541c00c1c0340341d842403100e2003102800c410020000c0d1000303551800c051050702e4002081c0c440300c100300da081003014a10f00f00121035084c66200d00030443d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 197839370 1250 197838120 197838131
    0xb031603060501300b061513180c08181606050405011b051e071703120a0506010203030f0c0412060f050705130e101a07060506060405060d0b010c06 65
    0x70084981c10841c126501c0040000040c0000300d445a850180207144c00c0c20035850f0f518080004110450403648100700824071b22504000089040d540d610030040f61840b000c99141c28846c03850500d15800480301048000c001d89000d180000c1c1c044040a410303404e54280c07802207201507110401c601e051920300080c0000e411569500c001d041a0418014a40412008440d002d6200d9421320b86008031504140141a1401508030305105036115444040450050060100300c0304001c03000881c40141c501300030f6503584031510b190152070801510b000c1006050800f4071165030b07400003d0b01d400071100040700c1003548841808180c28860342e840540410844511101805090b50105a0519801030244915074400b00b04407018403643c0d060a841480000c41481048401d580c65640300c110007441581d00c0ba141c04c01c1041e8040e4034a6030b8911201d000400d04104071482c01110342088083d40d481c1e00740f9061200041c100c0c02a00c0729811959542d05102c00700303a1040322405000ca4100408005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 197840620 1250 197839370 197839373
    0x1602030a120c051c050d020306010e0901061205090a0203070303082509030302151b0c010e1501030c0b0c060703180210030c030605061c0209060f040e0103060f0903020c040b031603 79
    0x10900c0c0010282c643d405003507080703002c1c81040300c05a070800c40c8981d40c407443c08000c3c0710040d0003900090040c9040000d00010b00c4100c0c0c80342d8040754041d00190321001c0b4a0034005440e0826164010011030703a40c0c208841100058078000781e540192985810805041d554202c016405c444c0080c901404071780381d08102078240e5810008440c00e5900075801d5540c0b1a0281750003524080c01900c0150a106010701d10642503225200500a411010400451605500c01401e40b41c81271048000c41f0702903140340108200041000c02200800c4020b105030700300008201100c1d21030b40003c0c0500c01780354941c8160862088550580009264000c01c0d03c400c960b0758541c000c0041401d2a014004039107810004141803800101b6501101510741c02e2009041e00c0c04030500c06500021043c64225400380a00340d00c500480d00540040c140c0c29400315450340c95030814805458020030301d00c4c1d603076140c15590000b00c3ea011580004251065a010074dc919405c8003203031400c81e13452066101010070362070100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 197841726 1106 197840620 197840627
    0xb0c0a170a1d010c030c090303050a03050406090506070c0201110a020619020102040e010305030702040b0d11041a030313140907050703081b070302010203101a1602030a12 75
    0x80c0000d9001c0155040b20300441448180e07516036100c1868580d16104e0384201110780e10740f640c0340900d151405061449003c40510416495000141c00c0c440b464008041c0340c0d5100b8202c0348540ba00450080c040b904204003240000d4100803900c0325180001840c014036900105050724200300b041030404202c00055400095540030b12000854821940343d5900842c040ca01541d0f40d509140304010880b070b01450043c2c46400107942c400302180081c1c10089141b007040c4e0340011001130007106540307402c805466130761b41844001000c0141c6580d50700c1d007004586030004010b40c1c1d00102d40400000880c1194041c001481c20700100010074469801d154200c9949800d031803807a071100800307044d81d500507401a40540c1d00000cd101540b80c45440980050684000c0f031144402d20300080d031380c0c2e80b0030030500700306440d11803204174113550f01480228041640a000c21000b40c1c90003001a = true := by decide +kernel

theorem cover : BRFrame.Cov 197661870 197841726 := by
  have h0 := BRFrame.cov_init 197661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 197661870 ≤ n) (h2 : n < 197841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
