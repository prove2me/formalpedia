-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3104
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:39:56.043702+00:00
-- url     : https://prove2.me/submissions/765efd55-1742-405b-911b-75db3593b77e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 558093525 ≤ n < 558273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 558094775 1250 558093525 558093563
    0x19030807060e1f1a01020d0518010210020f07170901090e2d010e0a090809060c010908210112240f1e0b04050c0f0d0912200705010c020418 61
    0x40c0130030300c401071100d1a43d005001e0f9400490102e1884010303542c2c40c0e19007890988400f03d1001942e56043c114401c80c00d2035078044c0700c94400740040940248401b680d4030580c0c18441c0c4401ca503050170702071001c030030880030545a82101d0403400b1101415031260721030340c6030721016028031902e00850380c161181000d40301443c0c5103801468162382c105040440c0d203869082581085a08101d00145480c03003c001440d290315040d00500a905201360001c9a0166155600d401c0b68024070141b10300203851505040d00c4107450076106002d084590711203001c0e4042070b114404503100c50007002c21141c5c1c041300030564104c0540c0141001c0941c11805202d090411500914840300346108442d07910319020180c141d070704c0c0900991b405182c001d0020340c00d002d84d0b803151941079484010241207a581d98004200003525003462040b40c4407003500c40d041d000c0000070350150391001007200d0f9065900080304c20b01a980c1c0120000044680503503000034090082030480348800704460010701060400318401c3e8003a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 558096025 1250 558094775 558094781
    0x12060a0e0f0f03040311040f15140303160b0c0c03040f180207020a031707140102040504050709031a070507050f06060102010e0307030c021c12080619030807060e1f 72
    0x91045200725455002000d40e042d8566544566800d040e8008010800c0806c0300c000d448400250f009000042e000c00c000c0001044424100c2d0300c4542102140041020b0606092030500c881402e030091884c1c07000302200f070140c1c034070b80c1c06c801808001500041800d00c0108000d64402c518010101d80c1c0d12919106150700d40c90251007015000d5080d00f002c00b050b859a8000d40f510580c5c00340040d00d40c5821584e95110b100c1e030003403e85d581100107005480126480c10148802401d0082c00180d8843c2072409000a50300014400d9082c01040314081000494042c0c00300c900b11002591080b00391100c80040780d4603c50000003920318810042ca4040300c03400821414051503098000300012604940d00365200d0003095005000314847c0e121803005400c00551041c0b032041032088048048203242e50315000d0481c60035541000a10540402031b1303c0c2010311000040b60141ca001511561071681c948000717228490004216548401d1118190001001003035100b0100420035400c401e0f5802040c802 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 558097275 1250 558096025 558096041
    0x50a0905190b0f07060b060c0a06050910020d05011404050105030307120e040c031b0306150e0d0503071a1308030402120c0a1401030510080601031419060b1311160212060a 75
    0x4410701d0410260703414600002103c0303003e01031001900e00c1c003155862b12401042e000308240800d00401310110401c0701c20b48002c2c0691140c40c0000502941085c3c1c003e0000c562800b01103014a180c503005204656000040c0e40025071300c40c410400d03c01a81c10100c89011f2500441a0010f05000d4102e003090b03010341180702c41c0d41e1521200c0c111445011000c400351440392064505a400303030090780c0d40541c40f50140780c04d8184050480c0f002c4040940e6003034610303403040d1000e4401c2c401040000881800b01c540c09078000c041942160604003194541320424400075200a11801d40c9030007071011641c003800000e1003a02c1c014080c1d0b654a90b5545504120b10000080e607000a140100003018943c1d4881c071001601c201000801aa17821640d840b010850300c0380c4800c419200307400465103082c900c4c41d030b5a82858403070346001c50300520300018410b4003d0036441c41c965060804528140300940380c01914141c0e0200b585550114585002280f1403000c000790f01d9402d4011102000b0800206c0d81003110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 558098525 1250 558097275 558097283
    0x15070f12030b0f06031f0b040b0405030d03060e07030b0409120e031018080c03040b0d0b0a0920180d0f121d0907050c010c02011b050a0905190b0f07 65
    0x10403003002504101d101c1600c805501d0b4040b0303050001c24052a030a1503d108401c0461419001b025250350345000707035800c903a00010100c0400503050156080603c6104070b10102401d0038813010b410908035400e40d42005007104d00305540e03007100c0ca01c50340d0f403500092034040e08282c00d40200050754200901c450380418030755000b8491519042c488241910500d490550002e91504000301c003551986407550102c0c0700261a44800c0c0b00c0802c840510a000309840c2400c104002400c8807940c00f400b00c0c891240d13000a55880c6000c010440c1c181c07100c442d1585400c2462001603131000f06030440c0e04c0784040c40d08000d0f040044401040100246800c44ca9a454000c00c0c4c91445120034079000c0360300b000d941c03001d0191075445040450141c100081529000b01143c24a06d050050840b20380e070844052410000050f034481d881100f92104100050501801078509140740c401408006401da1220f4820680107840c140c40c801900302951081c5009052840c220950b502000c0981d00031940115009403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 558099775 1250 558098525 558098531
    0x2d191509150804020418051507030b0303030a060501020613050c150c03040e100b090a0e0606310801020f0f09040204030507030c031205071e0c0f0602030a03050a0c09030215070f1203 80
    0x500c280c69054400000b50700100a060310708c071000e4410381007800903110702e00781a1149641c01c042c0c0e030148045c40c0b1640e240c510028255141000082c03900001502c1d00061061800f01e08002c0b81c40030a0b0102d10341c0007034030030001c460b0740c1416550310391203003d843d50880c3c00702080100e680002e0480040c020202c6828805109845d40d4130f90a4900c504500142d02405d521020440030703212450740c0c1d43c000c40090045e0f0901c1e105036100d0070034528128200140d0a24400280c00500300e203d01907000d0002d02008500b0603081a0401c0307101d00c118041495207000129803000e03640c0d03881e0101c6002c0c0da03001064515540d41d070301d0304904144140c0421501c00c1803858841c0752142c8100162404150020201e6400841c030140142c061118031006450420b62042701085404a0500c02c0300100043c2d0700550350f52000910003811035502901c44081982015810a401c039405160070003030342e0301100e003c09840e0000e080300c0823620078110024000b52804c2c458505204020b1200800c10913552418 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 558101025 1250 558099775 558099791
    0xe0a09060825080111030f15030607050c01020c1b1c02060313060912120f0e0a023c0a05180a0c09052d1915091508040204 54
    0x890950300d040c01030078180e42c8000c5a00d10032072202107200c0d0100c000301424201168864241a09407000c00c50740d81d42000001050006a0150f02d84d49544055004503c034501c40c02140000d03211075006d00118100100440d030000a84020343c110703203021401404030b0305000d402000700700140007501c060300d2249160030400e40b22544001e01010700d46034000d1102c0c1c03850b0303100d01d2415090700300000165010350781c41d410000080e015040341314030500d2684654011261412009098480010b161103141d82070040725444100300003003a24450b94110303600c681c04506410072004407880101000303d5445009081c4200503036050040603071840544040e0a00790329070040c440d60b00b02000c05850b80300c400c080042c40303906e4564400341c94005d60345010004265101d0005059940c0c5410082c2c4181b00b188a41c00301001c02c0c08414903244094407200024040300d898000742e6030562144003030342c0d0182140b202c002880352a41502601780b4105030307814140350160040000d4000c44040380603910f44080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 558102275 1250 558101025 558101039
    0x160606061103030c030105010503130b090c0901080a0809040b010315030f0c171b04150b0c16270912020d0f02010e0d0c0609020405130c0506121f03050d0e0a 69
    0x4030fa20640c61a40c281d45180d00c0c140044510b90300007089541c4121100c001707000007400342079a150260310701307400400c02031408104100880c1d0040c2d0010341150f20025000700028015400d0725502c01d02101c002031242410030059020f03060b40703640102c0b1070301c9545d004401c0142c4117070320045542c0243c1c58501d2541c0c4500d248a1000d80e104211506580000369040410160f06510305080d40e015202040c881710682010110369481d400074554520041020780e0980402c100081903080e44101c1804140c1c5072221414480c103945146080703600d080100320204c80100e0704001071140d4003885298075002e2044009445d03800034105000010360500e00410136510500900040145000c0a8034040b5072000c41512102009003044654944689071b60016a40c2c41c42003921600c403421280300954424a02419960004c3c0c02c0244901d801f80518003030060410f07951544150314400c0000c00441d40c1e10b490300e40c0e02150340010141d110360403102041c0c95005102803e01401034420301c09258039118 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 558103525 1250 558102275 558102277
    0xa0c0312050105012a050f2802010806060d090210030c110a080a0c03020705120102070203070803030709050904022101020d180b0f0c0c0d03090b0106031817160606061103 75
    0x200c0d031800140310f40c101715045000c003244085074a10310380d411a103901d15960b4142c1082c4120030410056007150358801c004184c002d9511600c050001a50008800c0075400602166006008035001e00c0c0e002c22480051030f92039002c1d0240b81d400401c540c0080c42c034520028003804280c80c1040000d0003400800034202c1d0000743d80e01070682d00248007410105904021601c000b003c43c019811803113402e02c001840d40301c6c10640210f1302141c01c00560385100c05e0061601d002d15a030b101c5917480e0300810403c110302c3c0c1d004a0410070f84208980c10350458880e400012489901b900d58849221031003d075100b1107c41c150700424014591080620200d049002c0b81000c0b50545a0060010301c040b00c005000a5403400045600507403d03019581030613041d910985c9850741070007528001c00d943c0c0b141081841405000305004040a140501060a010b41ca4104802c44284004e04901d44a00a800c51800b60800c2d260914246020818014501d060603405010036120754000f05410603440244250044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 558104775 1250 558103525 558103529
    0xd09020f22050604180b06040606021204053610050a1a0903011e0207031d032a040e160503010c02190201050409050723270a03080a0c03120501 63
    0x8040700c1240c0c0310841020000c0c00006205a60080da1950342c24003081843c0190003015000d1442d0402e58605007050100b11052600094295400100c400990440d00d40440e0f05491041e134a18864070705800404800e0410308141902801540080032444e14860b00903611400c14403103c299030b80c1e903c3d0144403100e141409810301d1604000450308000341b2400003401c4d82c00c40a00001024826098114121056100c0d110146a0005640e00a165010140300b4036140322030444080700ca803440010342d658903000c20a1055824110030a07440c02d401c4004803c5415014200303010b801c09040c1c2080d261000c09400c1d090340800d00e40041640e00381441b40c500f0641d80d0f03030020400701845959525081c2c400c00740c124100103082201007204c000c07500138a030142500f41ca55021383c0114441c0102103034000e000021170004180040010082050120524001d105040007900716070000800c4130900c19410141c5682e90014034240c0565101c8810700c86240269240c1c220b44600c44602800e07030300e0038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 558106025 1250 558104775 558104809
    0x4030c060305091614040b060d110c010b010314060d05120a0201020408060c09150c0f0312010806181011071b03290c090d060e0d14030c040605031b0d09020f 69
    0x5800c00c04150515030f2147c0004400181050300740400d086441045d030707400744801500c110010481c0030303c1b00c2090040107062202400c0c103101c0c042c500f60007a070001900414148c03045075443c01d4901480030038002800628452081030703980350a0440301a010b54841e110740c9900d8403c0d030001034440080141a20400800144000030f00e4260407454a244d402202640307402e8060203054285070b240400041940d0907d0701c01180d5107615141c103460400f140240084403520321190703581414100410030096000d140c81000603620034120302c408880c01080380040555a00500d108104000000318100f200d10680c44000350409241b620890641300c042c200c0d00c44500d00c804605148419009403004000180020138555015290a0700740d0300c0084402c22950030030300300f88003010343c020404011803581c3c40c007030361031070070b01c808803003010310031031013040100100440444d50121501d42e8082c8904141645c440d1205800000a0010260758908130704c40d03c1034080c3c0483c0ca05041c2880742e01032041d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 558107275 1250 558106025 558106049
    0x715021b04090309080d171e2205030c150610050405220525050708070f03020c0d060b010e0f0d0b0403050f0c0307050115030c1a04030c0603050916 65
    0x200341840041d10000da000c03070900880c290081080d0108020040b600e551030b59825041001c1d014015100c000080c2102d8040c0c201d048174400c00c10501c46040da004240b211048a074882241c007000c04002520310010181d00000501449014000881a6254815492a05998980e402081501d010301c80e040d801252040c40100300074904400d101951800e29003102400780420326244080302d40072261510940101c0c0107182841d2303c0d420221120031064205a4034061464a41e1100d034000c014006084400311150340007050310038082c14918010192068024511500c0c0032000b800e03040d0120303030020741d081082c03207038503d00110f000c1d280404c0940811a107498945a28400c104001d0060702070080401000200c10000b500500101c1e038880044c5403248206c8c5820303401d58500c40000c0c203210000075000c2c0081b03016070b1224001c40c2c0000050b918441404555005503003c1c950020301184408800001e0b0708cd01a0080741c4203928100a58650039603e5206058008060240a0300858 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 558108525 1250 558107275 558107323
    0x40209011e09020a120b030105060d0602160803040308041101050301030c091a0a0b071502030c0912101b0e0102060906010b0d020c0303070c03080108010b0f0d030c0b0405071502 78
    0x452008508010001c81c84488901d074455034100c05a038011076801c80084e1403a66900b002102d07501c14111040000c8000740318a0410000080c280784089401034466580040d080b400000c101d01e80802080c0d200c3e01290b2a490f190602a04452f01201e0030344402d1035078200c4240c15031042e0100c90690741e20000103501107040082d03420050031103076090440e0745000a24040d207a42d80401400082002601540e554000392800980700203000c401242600d0040c8240f006510280c030541c6d085007002d480c2d12011946c02c1d0641e07032034030b840b400071030005da40740240008401201000420b1505056180c021240d404c1900490f42c5020407104811150010030060101c412404c00411300500414005130501d900c5680050455105903505001304402c00311100406410240d86801880c1c1c01c80200b200314255004030700120300101c41507114400798440307002010f018024420360a500300329020450314242c5001c079500c000303e02030020200b031b406c2c60556a161000a01c101c0840c3c448003000120302c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 558109775 1250 558108525 558108539
    0x5120112030f05070224250f06020a0207090f091103030705060f060312040f08010c0507080915041d010302031605010905060a0c051204090c050a02060415060f0e0604060e04020901 79
    0x50031810007264095112000c94120380802c20180b0180498580e515942d2140e1807050847e28044584134448031030018812000704050012072031039140c0061016030340740a41601281007144a40140100340d01e40716400008024a611900107148507044100501e0f00d0032041650700d000d5000003c142c1da120b407000074000b54a00b2084c540101d4060700701d40361805215000841c40e001030700409046041ca450411801d00d00340074000a40c041400c205203000120f4607100c4542c030034180d105015400b13440c200950303611072800300d41c001c0000d0045500e02c0d6955000301f0411120a1009078864070401610400800b4240c0d00b480c1194416107d080046240c68280f103d260400e60300801807004243c20074001c04c200f480742c0c42c000548500c82aa55600344503d0004407182c0120b1707a802c2000601800c0f0400740c0020b4040d40040c0c008100c1103a40d4a030049520150031990048023424009040c001080414100020701881045405100c0d040c0c6030301c41418843d0342103030040e60182400004112413 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 558111025 1250 558109775 558109777
    0x10b16020109090e150f0108060a15032004140112060e010b030a030c15020a0e010813080f0d0f0b0307230a0b040806280e0c090705120112030f05 64
    0x100d1041c10014030080e5240c607608212020b080c03255400740c010403c01180f003407034800342d150301111400da05031065050410050340c8040c01440c43c4062980d54075101109140d100ba088000e41e030115480d600540d00c41c01d02c08040402d400300500035410503080482c40050102d503070341a41d40030005a92620600e842e010060140c01c80c00b1503e41d540c2d66045204e9850034000801031078003030388844900c81d505140c600da10894403100c4c80003183c03041c8240c00206a00800680d4121000d2a0030300d40c84d03e03007640a03400c000d4081001800e5880000390500d2501594015000c00718a0501c108049a05c1038010740544410242c0c41e64103800502c1c090080e038820903200c41208074054240c504980e801402310b01a12101c0e003081051120214080200c14020010290300c041c81a48585140b40e58281e0805400d40591640103296243c043d4500c000310f0802400f009004010b0141314541007400d40a065644040001c6803003200c07000000c1020f1600c01041028180e01d81d88404084103402030489003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 558112275 1250 558111025 558111067
    0x4020a05070206030414100504020612061801090507030b0f13110409150512031216050706050112060e030f070b0c04030506090606040e0d05041a040503070602030c06060405010b 78
    0x5000d0248000c501586503c4061352180703110340401020f0061340c5184900c2c04e03080002c1401140d0804080000688514060700c01c1101c510f54090301c0d5803035048c0000c0d2a111800c2c03c00c480b11801400024a500003a00400d00808198404000e81f4424400344030006010035210380d0000b820b203200807841001c0358806103000f07171442030b96428275032211490015940c0030b015a0441040942c001c0c00140307403844010b481a601d00000310702c1d10414034500105010018034503130003d40c41c003544001d058040c4003165202503102c00304009960b100d100002d42100c0204c1e042e9802807030003141240c0307204000103e80340000c48001e0b086c2040b03441ea58017580903a004018000d140418000080010700401400e40180242000303001685099001d101c00c846c0365400300b101030340c4440c0c505040710390080c0464080d42c08605080024084200c0d000c006486183d12698052158590018050f603020002d030510b0705c044c07001e0720b440341c451101300019900300380600070540404211040c0305d00c0341070b404040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 558113525 1250 558112275 558112277
    0x5120a020312092d0f1e0f010e03030d060e010509010308040b0309210d0e010506011d0d0219061d01080a020a0306080304261b0d05160b1903061404020a 67
    0x7164484400d41100400d81302a0150803590720071285180e62604011901c0500c0082c0c82c40c1d040050200200d4661410520720613003c1c1810040000300c0340d03c9559144008140a0100d0f03030344410040d512801403600b4400c800041c888031002140d00c2c6802d4042c20304917031700000d0441c00c103800d05025110b9584040c1291419108200c400e0392240010101c410310301c40004440c2d6220310342d520006069456404240d03d881c0d1401041100c03d03138201c0b0740c0b1100d812201d458902018001d502040d02082e9034100690301102d21130036105001600c2509609a409a80e030717000362501c00ca403412032412502c04401e8089071501000510700d444590190a0026251401144260380c0f18034071401c5074003a8101e05105101071030a01700090b0020541d040a548000c018070a2111041c01782c02806200c441c500d100307102068801c014031001f0002c3e0400303449042c46003d5281e81c1d0310801001980b12660500004101c0d60802c001103001c3c2c030440040782e9009842d0503a0b0b540c01c0003048002d500c1441a50 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 558114775 1250 558113525 558113539
    0x307031704090606120b010c020603070e0d08190f020c0d03080901290a0608010e0a2307030b1c05060606030c1c02070309051c0b04080c0105040c05120a02031209 71
    0xd14420b19004500040070a61150640301e0038100016065505515202e8103002d04c0b6980000144c4806044980c410020b18150300c0d4050b500001030034410300810054090f0f200480e8000c0d00c0461121102c903209a1a241d04043c1c81c4200380c16038698084c2c0c1304150b8009007107240b420100380980c20140d881104c29000150486243d002100601900c200c60040c01c0800d90140dc0036007030606212010303200504103504503614050394a900900300a000c05241c50700c0b11451140d00180e40c03000040070540c0640403c80b4640320b81e0080007004100304481c4500c140b80035440c1140402242c02c2d000e0703604007010780040da94440c03e02c034031540058220301d1010010030001020808460180c101004444400b40e69400e507400c005150190580145200382c0044281c282c1480b000c1a51800c03460380201c41e02c1d02e90ba1542030402da10f010354840d4003665400c00c1c00300410004116080350607114201d4801c10003040b811101e5549503c0c004009406901c01d44604464603c108081c01c01d44000604034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 558116025 1250 558114775 558114779
    0xd03020307141303110d08030c0c0f0604080a120b0303070b060f10020309040c08131502070609081902010e031b07080f160515091012060f0e0f04020307031704 70
    0x500ca0343d4400b10720000c18000110040c820404031400704004140211131691315102c0301d844210303040c070000d0154580701c0400594041410301c20301c6020350114558013603401e94070701070038003c000c0d512902441c0d0029680c0000800d40050610802c090010050029410304810b5946c07402d401e100508019030003c02008418101e9450600c1303200302211660185803101008010311042d180b134070a0020a1110712070411150510070201110159002800300d00d0b03080e2444180402403048180c094006030074040d040f400c1c440150024001d0000d49283c0324021040300704102c4c04c80b965916141c40c0b54008201302c06c1c030706a4400d292410f4581074070075141030a07640c1d80341a150100c0741c1040071b5143c0114054100144e0403071100701c01010140c40700c42402142458030612849032640d080c3c0700e801908a6542043e01c5000c6d680c10340311840508100854075808440c21030000c1b07114460900c0c45d80e81c0040d5031044041542303802180e019004000c00c5041d41d035022010040f8031062050400103200c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 558117275 1250 558116025 558116057
    0xa09090501060f0314090d0c031205010b03061311030a0e011d240106170405031b0c100e0a052b0303020d0509030705070902090402160605060a0e090d03020307 70
    0x80c290003001e564403840041525410043c00303031100744000032100310300340c81000003142c0041003e4000700002d00c1c240d09060810301d4140c2e2240800150908018a0300c00082402d2002c00010b42c0a001300725802003800c00040d0b0904191510f0b440d40818000341400401ca403803181d40c00c0b507580300013014004146802d0703090300c090040c034088074180100c4e80102c03440122000d0480c80311500b41e04006ca807190543c1803d40c050701c1040386003050b0a640c0280000181031084c20300075108024040c4511020008000d1105940c1c0c22100f40760510401489191900e910b01520070810014400b5010424a41c50002040151456040d03c6d242d40110011220740c840148c01185012502c2078030010780f518810b91440e400c40d200140301000b90350042215070040b800010300c81c0c049801810025945001500207d0042e00a00d07088400407a4024414010041250843d52003044140c43c4808544d80c0d940c0c0004065100391003045484d041802c001d0300039407090b00119440318443c2018a200c0c1c0704098 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 558118525 1250 558117275 558117281
    0xe0405040605070908060f061e0306070909050919120309021503040605060d0203100b01140f04090b060a05120403020a020603010e151914030a05070303090e070f0504030201050a0909 80
    0xd030880e2055990400c02800d180c03c414207101815210300108035a280c0424442c0111001819661040403820b110003000c2c0c80c07920001042030700c080d090354900c2c00e02c440c02a10034040780c001d050500d0708240010ba1a0540085d2203001e14505d6500301d4480005a02c804c4500b00a05503010300700b507190f941c3d00c3c01507120f90702141078808410701e80c3d0369245800c0c1003401c104c1c0c80150009100e042ca102c41c3c04096500003541c5107a00010720f5001650007036510051340c0400040040160350b81002c02d0604000d04800c1c06403040b9651110140301c2030040340100000c1d4841c08030030f41c2c08110309026078000701c5810740f4142d03400741c4a801100c403034594540005085030002d90000740003d1000c0100701c0e0034600c540c00c00402a00580d00c1e00c403c0324550400e800803189501450541e4036024600040751b646c00c10002000c1307504007040c2c1f40e200340c4a00340200f0010342802420042c005007030105211070300c5100e1104c0d07106116a182030429046500448256002e00900d1302040705014010a24001500c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 558119775 1250 558118525 558118531
    0xd021201080f0f060c0904020315041a03070e0f040b04060b0910061b0c0b070606090525050a050706020307051c050105030c04020f0a0c0f080a0c0b0906091c0e0405 72
    0x14000381911141d0001980c5014010a1140c10640081c1c0178003e15407103950540380c210408560140e241c1d514500c9403140ca00900045a40c040c7c105420400c0030100700c01c0b4190401015000d0b80e810644942900c1003600d810b5540d54030710000c010020300450788001d5000c3d0420b1055101140c025103150015800441c2a51400d03115a26003c00f0000250400c40000301c03070414461030540088030383c6174400755080328411005590400154201000042e510101c0948500901005203041c0020303d003424088441d001c400d8001d0f00201400c145010342d0903240d840b280c43e07070f0b02440c00109a50711000703500041c01041c00e0000501c81501405444464040c9003500d05100040661611042601d800c041001c1640160720402c40805480200e4044031104030365410046030100c1e461900410b0030a9000c4007400745040855055456a40b00c807108510b04d006010b007054a4031001a0305403201d2040e1200301c855071040b01d0300c50300c9400e82c00140f0259007050602d2599840240d003c14203a82e011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 558121025 1250 558119775 558119789
    0x6040c050c07031212050601200f010504060501030614010806190e1e061005130213180209040624030c3020040306021e0d14090c01140d021201 63
    0x1c0c04d991031503035006030b5850005049013014400703814100000b030801000d481040202419172400c003540d40740104440703052540741000070005072a10b4108900144002e000440d441c505180f62880b02c6800084040d0507140d120000c0c100603155844c0c0440251000810b90803c0d0780c542c40429030b00001072103000e07a0345180d04803800c01c1d00d121040803402d0940c000c0161005003100c002c24080c81d18ae106480400b40300d024001603990740b10700001d800311000703070303114810700e00c0c1505c010210182150060107100d0f40584040c080c860f00e0f0600700803009010014524001007444108080038420781002050000030b00344142034060441001c6c00d5290080d45201c1c1100625010b94610300c198451b4013a00d41c03d505030782c6c034040d00d0000000320740c0c0318521018002d6030300850001846541d100c03070414040d10a0140fa961500c3c25039006010309030a0b0b0392400200411000110580000b044205030548143e41f0820b041d5060101c8070f0842c1c10690070742c0780d0b00e03030300784180030a445c0801d1055028040d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 558122275 1250 558121025 558121043
    0x11040605070b010905090d05030406140c12070c020d1e06050a021201121a0a0609022b11091c080d141609090c031410170c0906040c050c0703 62
    0x842c24a00194001a80011280d41c5401e08000c03001c0c0001c5001b02c94060340c1c0ca40300d5600d0b00c5904048000d4212a250051240350803418044901e40c00c9004080301c007001c2074840105c1d0f0380c4000640d01058150000f0350000c0101c6107a00004d0101841440d02c2400c44600c010122019100c07482103e90846561900c1c0c0da0020310518500365105002e40140210840d04a0038001c0e036031040c4080c02605585040340850300e000c0341c452100707600318002500700d04400315125005800a484954003a45041e128034200705880e40904130759015080d0702e083d5042c4031518003202c0405201c80c01070022013502a416016110a00141c0888024115401e0300a0301044450700006c1b01c0c5e4274100c0140c104403158000c00848004543c000b1009021146420b00009003032403010300943c050b0611003046a110301444c030400240c0780710b9101e202e060701c00c8090381d400c14a0b0b103545020b503540040310500d40d2003001d503400120985015002080314244c249071080c1001c1c40268501e240c04501e801c1203403e005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 558123525 1250 558122275 558122287
    0x1209030303310b09070f080c06090a0b13060e0f10110a020d0605220f0f0309080d090f0807140d020a03050319020115031e020126040c06080709170111040605 69
    0x11300300001c00142280404035811030b032030a4401c0795034032821001a806201d0100b15402299916035040c001001c8c45410141e0360b41201e2400c1d250310b0040d001e88408541c1001502c5100c2c202950340300b0301300401a02581c1c0407403010006540f10542100c450a45204044000c001a211501700d541c0c103521900307010070141030070b00c000344901e5440340f1080a03540402d03550b600850380514248940e15005003100b0f0810209003002c43d8164032070b4000d20003500c038a200d440d4030681e0019880b0203c800303408941201703680701c001554440d403103841041004030f81d40d11254014600307920003c3c881d07031005082240d082d42d01d40e01c043c00c50308400032820848000510802c1456028012090079011000c8103800d49810741c0d0304c01802510b2010050041c00401d81b102045900079018000d044006940c03004a4656501080211071011036048451140e2010300056881c040c0714424060103058880940b50ba080034240803a01140526000b007030b64881d00c40854440a400081028042079a40c10f80d0b154 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 558124775 1250 558123525 558123541
    0x10b100309051213140114030c030609010509010b040e0a020c070e01061b1a13080417070f0605191206031a090d020c120708011104081209030303310b 66
    0x4040300b8000c1d090014200030807221301e0002c4c25104241d4800d1540800c45400e400c004842101080a60386107010340002030140c0c003403002024510407101103418540d941e8031041071080e250828443d59900e600140000e000507032000c94003e0340030b0401c850040c2403468400c1c0741454865180d0003400500300e00c00041c032000b076101c111580a811306179881003810b025581d60303040c0101c06002ea10017104031070300410440000c8082c00440c2d01c0d007210240d516a500e8150f48502c11504841c0c0051034400d105000400c818460400400c455603500d900d07040002d404030404260701011003440812844c9141c90b00f61405900c2607a0145000f5012100b0041441403013154050000d0240c80d0310381c0c082aa480f541c3c0c0d40c0000c91441071042550034143c0d0008503071000d0320b000d603a50892091542410020b14001c8419409003040b152404100c0b0241e074254001c45c6c041d4400c1c0d402d0190160000c00001e801d4200081044403540b01985041229218250070a00301410402c02102c0106840c41800030301 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 558126025 1250 558124775 558124783
    0xb03010305151608040602071b08010b18060928020d060801180813030203010501180b06030f0106080402010c120206010911090604050f030c090a0c03150501080a0509010b10030905 79
    0x115104900440c5410481c50f0b6000f141501c1007040c040141d0940020300300566a0141c03400c01d40d010451640d401c10751440d6248d5410b250003540003542c038000c1c102529141030201c80021417141d5440016503203900c020711001d240010108054880035540c00d84070140f01c140700c50038415008000684813150200303004260341c83c581c04241a130781050096401103105d22166844568000c1c0001e82e03482c907a50800e100038042d0703400a0362552030000005406c5068107404041082c01ca0800c11240140d40100007403030000740c502d001400349000050105600802d100380d08140141414002e8148659a80500c1c071130000d160070058001c84010000c4980a002c3e14600c40f12160502c0c0c03c0100400c0401c006006610a080c07041029007100002c6032414000900880c00140601c0c07400c0c41c0054000028013450000301001034a00612181564a003401c001c0540d04140e495000c03e4035140c0003803015180240034010a95070703901803203c0e2540ca2500ba640071041d140c80203c1d0008540c1001820 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 558127275 1250 558126025 558126043
    0x30a050f1b0d12120f06080a050105070306030c0308030c16030f09091e02091908071805060a0302090612010e070905090601080a030c0c0e012423220b03010305 70
    0x10040c1c021071000081d0030140f10000000350f450301c00c4c0b031a100451402c01601d03010040180d868a000300202d00c0340c0740420803040c40c6000318001c0c002e9841e0040c0441c00c56049100140a00c0a04803003480041c410343c00568100740301c04041c80c200280801c00d00330220300c13080c0231000716100c070421240880d040a03080000346408402005201040f100c2000451605102140c0e11a030004442c041c42d510941c04071500352070920803070412511840c0c421f13902d14007030191645442481080c0300c0c5800c180d0203241c0c424040a82034518461a540c24000d5400001e014250300008110175002250000d100320045512218010181c0c1d43c58030800c1400c0341c00142c199200c40d0086401030201d50300c005002c5071401e5052504096044e414103004603115003541001ca10350841c60000105034a061454100e4040c4900b00a681c0114140059440c0220402c85c0c0c003800c9a0100d440b4003012007a8041c2020410204040b6640c5d2100b049034800800342d03070411150b0a1011005200744517040002e580 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 558128525 1250 558127275 558127279
    0x201030b0f090a0903110a060b0a090209101d0d2409050a0b1902030907090e0a02030a06020912010504080309070e07050304170d020c0f0111040320030a050f1b 70
    0x150703268803402068403a41d00030820301d003003038030346100030101032080540c6801e104059050783e141d0765080c50700c44042c0c110200564804c441d51100440c00300c04a108403101030000034120695544010010b9503450202060100c0b0144079034050400c680fa0040354280305482070f60b80d8802c4400102000105442002014140302e15151903074000800006065441c281c00003211842c40c0e80c1d40002d4541e8400030761652500a00201c140800d0040c00500e03201035401088050015204520045995640d0480c029600d03511583c80000481d16980c000d000303143c4080c0c19446042500d0562509466090740c0c103d034000c0c000010001d1821051054502a1204140008081c14036120003019400050b1000e030038680c0100078501c0c6100618101c03048510303030741c00030b5440d2140041c059488442000c40301c4150b500f003466061181051034200d5007540d512443c01c90285858a07024000c0042407004a0340600c200e90380b100c0030944c100300a120915081000780001d100c40e070000c005c1c2ca003903045214 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 558129775 1250 558128525 558128539
    0x1e021003090308130f02131b030e0c040e0d0809010605040c0e21030f181203030f01080601060c080d0209151905120a0f0902130f050c0906090112090813030201030b 72
    0x60005d0b00c411408858140c04644030150b0650b040799a800800f10684880900c0d04103c403000803041e0035401045c1e48040410503121074891900a02c01900c012050100580d0880865240558050300c400ca40020404000060030354482c40417138202e801c041a0240440d403010b034042164504100c03040c0900201415070300c500300c844801190b90340200414112403090205080350492a01c152082c60094014030f05802c51070030840d51034480d03005440010141100c50b00100d401607000408070304030340c0d071581c40160004682e1500030294211183c0550040e0302000540c1e02540c507030800004a41004c8002c9a580030040c052f141d40100213100802402420700040a40340d0b081b00c030b800d50103c01341001003140201c01450301d0060950610003075018940e2003c034441030482ea84100004030510400304003a486d0040d001c0c4c001d00600b00605e80c4040d041004039802d501c00e43c41c400388064601c5006c00c190fa401c2d640c010080e046401c85030307010508100b04005640e4140100105903400380c2e200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 558131025 1250 558129775 558129811
    0xf0d05090105030c070614070206060d030914040f0510181407030e0307050a081b070302090403050f12010306021c0b1e010e060309060105011e0206041e021003090308 73
    0x2506034061512101d05200000c0001040c03001d0340b10440e003017540d200d1801c1222512402e20b03002c800d60181d50140040c070038034001174224104176800403022601501c03400c0721189000c0050510004200b6a01e4200342c07640c9400c441c800c054003450303006103845400448100d081c20007008409030108401d0441d1400d101c1c0441c00c1c220180c20498003c1c2032880d010a80040f030340d900d94510b00c40d801d4014060311880b0030840a00c001c6002401c1e07001582d04000030101104a20350b43d45090340d00004c1c0d840b40140340403500190060307000b4035003614001041410613510141d1366482c185c0c02d0b40203648960700002c0050161014184403401c41040c00001c228404c10078020036003500544d625109440c0e80320145d16060380c0a400303030811241d00241900e6503846c0803064a41c9582c000c0c466a40815840d01c04001310940d90406906c035103210741c0c005c3c1025915900c881c031510070318030800354003000c683d05450056104c5030b5103e03a50328020f4a0101d0001018a0018541c1d00e0041000040a42c02480 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 558132275 1250 558131025 558131027
    0x10e1302030f1b06130b07031e090f08011401090203040212070303020a1a0c0901030902040209031218030f0a0602031012030c0b0c03010f030303020c0c04050907061101022110180209030f0d 83
    0x5d442540c040b94500c80d25911246410784441e00041d1403c41e24a60100914507503907801100301e0701f40d07a61b51440c68000b65035503034003e007a200704042e1016411190f20050081aa550b40038550090008084141941700a004242811341c10303041071300140c0004a0300801d0100740701c510550300e01007145102d5145459002200140901c400c3c190401d82c60ba8001d00c01d42d983c2d9010340c0c1003a1001010b981c140d98810412144641c0602c3c11380c91408140c4005040619011490000d03124800c00540395038900c1385d550700b00030f500c01400300400182c0384038049000c0312054200300515100b9143c41c0b641e80c44a08200d03d42010090040d584c601040006200e10060362460601b10b80c3c5c181400340c1c4413980c041c200d41c1410862800d4541142c038201c10030180d101c00041c880100c5035240c6a955855450060340c0b802e0380700340e00d4046005840100104040100c43d40c241e40c0c801041401074145d50b4580d804c000c84107080c410081586074000c41d26200700d15060101d6051480040c00811140701c1d1828 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 558133525 1250 558132275 558132307
    0x2802010c0b09010e0304081f06050d0f080c0102030a0c110601061e0e040c091503020f070f0302010b030a0506010f05061204080c07080111030f06010503040b010e1302030f1b06 77
    0x150080410261402080700036009421034520401c13410b0503039896540b42c45089a40e40d003034440300c107c0540d94001c2412010b4961003141d0030343d18050031202d200e00c42030301c40c0300100c441824202c0e20140100140c442803e070a1001d1405001d80c040046803a500070f103070082c210041440c105145070000b00c01000741c07507080791122082800380d0940e48000744603200c007510f0700103c4a000a400c641041c400100c0150700040c0003060300c29510311042c0000c00c04104804074007500c0000014a2400c00c0f01d04007040c42000107a00c281c0c424030020404040e0400803a0400344000000c807045c0c1e00140c010b0282880800c8041b01812058070440e042500318003041d8200f51000d880a400c140d4005850070040e40240403800281503070800a100400e90512410100d134402ca411040b44600100460b0043d80700c1e03402c503405039420018010310740c1d0900c2d50901c440700001c2d080c01015030700c3c0140c401c0140c5041c0714401540c5640406400c0481000302c52400034001a000184a500c0170850309810389a004c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 558134775 1250 558133525 558133547
    0x120c0a0603050c090d0c030605010e150409150906050604050c0a0e0616021002030301030605060f10030c02071a040312081905060f0a03110a1505070201050313021002280201 76
    0x700d00414070742c98119000600c1d21a81d88aa508049100c403841d09100c0403020050449101d800e080202e40e1340c45d0b90a02003010155004200c001c1550300e03402c054a0640c203c1c00700140903204210228582042d00c00813500c50f00380c111002600d42e410040d003032516218541e4404864440103103042e0b04500010110902c1d41c0b0705034070440300452415641d1903e0480c6280d119400303401400c00b0201618003130f5a98009101c00ca902c941000005040f1b030400600b5881c07010806000c1380ad402102c8041070307000d40900e80c8100d0441c480c0c2540000c4242d003440c0c41a4044400000d91a500c0e801c0d4100f00d02085000582300040c0001d00e401d00440d1070b4203c950740004108018009620b0700d03002c00260b0034030054245030381d00400d00303040031050005400c008482240122a00b20b50640e880503403000d940004003051002c54010b10503280594064401107610003885415038050401c4d59000618401e4a03800c0d40c40140d201d054414590001d0406210041540e00041142c00807240d00084c6010140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 558136025 1250 558134775 558134777
    0x90f09120f09030308091c0804050f0c06070f05011b03060806010b12010315020f121608240301020409060306020c100b031c02010b030a03270e0109020f130b09120c0a06 74
    0x305c0000380c03100c003007480000620403a010340740000500441008040303c00542e4161a1800f441144207080c8100044c0d0103e4510090551810007081d82c0361001c081c108103e0940d815500e03a0400e4074003004218001111040d551800030b5040d003090070442c03414034141c00c040d1080d5003c212088000401c0c088a9045a6004607030051a100100e1044083d0043c2c03800e0380c0303504c1c40214207102941c1d45658140e01c107a040c00c090302601c0c07680c508112005001035500e100c1034185640e0307501c1c040d44014455040d034000500017503e803554880c1d018003246c0d140e605c00d440c01d130303408142e41c1c80041e13040c0700d200d0640703071640821300c4024200c41c0002c2d1200c020b502d400d00030012498000c00c2c8a4000c0d008201980717001000c1d5410203c3e1810007410041c415242a00d041c0c88450400300003d600150110507207144108118060b070826555100941c462409038038003a5092111541a000b280c410314080d0940b100c2c943e480301e000c4004d110141c41d1950102d240354000f50320780c9000b51901c241503802c0b1070017 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 558137275 1250 558136025 558136037
    0xd1404030f05071508220b06061b030c06040302162d1706150414060d0503130311041a09040210050d020d02090f03010c020d050f04090f09120f090303 66
    0x45180031450009281d002040f0240040701348200c140c0c211902070320588400a140c040c90400c07102d01c0d408203060b90380040000c1d100c0c0020860609085c1c0140c540704551072182011020300d03504161568003d018075400781d9100c202003008050303040c00007a80720f10481c83c10a100d14201801d8030a0020f42c0e408030396050003642003014a65a081c2c1c0c10380003d081d41d048401101082079040c94503180101d4142e600c100e5580015840e6040c1403150629420b5280784011041d02d07045e00300301c201e0b0100ba0045d169840b00340101d80c0b18140c040e400b00e00840c480c4400c95503c0901d00c0a1200380c618511080e5030800780c242008049031251902d1690199040f2280c005800038440242e07207174000e42030390380a11880801d105404c201e441e8001c0100c8030044030323201d00244601042600340c40496040d0340068000100d440c5183e8080c1c0c2c00b40c52440f0010700024245030b210041003049a04291190011680350755640050241c0840d8117500d01c009450001d200c40c0390888050254003461000604003d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 558138525 1250 558137275 558137303
    0x30d1a032e0b0607030215090628020f0f0c0c010203040f03080919090905151501080a090b0717090d080c09010507060501060305060a12020d03030203060103090c0f080d140403 77
    0x40310360b01c0310186110082c80d031a100c02c11402c00940d42e4001101c01c2e5a58442c440c04205208000a100c0c0e109030140f02e80350007150700030070040d00310410910381411350070b800703100b04515070b50030002400030b14a1140520741c664224903280e52074901508200c5040d0340040005015030320400c50350b18103172a0802e6449584130400c00206440220803240c9820042841d0404100c1c140140c210707098981c0144119072401042d05008031450400b61000300201131000d1050b081d5500845d08030f0b50010840d00c000a061740c55494040f246402107422000140070340116404049a28850030741007510140100324650311000040d1903130302d000e040160f031110049a140150b0b03109800303d40d0110381c0f101041c002541d60b2170340a03001d44001d0f1801c0c0d11414907200c0100342c0c5100e0040110a9a8004150348105865a28154029440038108a04158440380e001000c12039260840700146018610300100c5480e1038030807801c148540c1940c40400c42240150040c83c400e5074107440130390350006009401f040e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 558139775 1250 558138525 558138613
    0x2a0613020a0e01180902120601151709071401140d050f0703140621010204031b17030412030905032d01090201090b030a020408070609050f0901030f1b0503030d1a03 72
    0x550040c0c41c607056231040800100e02510228020403400a10b0346903007040b0380c41e100c02201c921808480c004801c0d80100010891110541503000940c44181041c1002e910104801050f41c3d1002d1004840540c0701c00a2110503209051100c0d408603c1d464208110f05110b01c030fa418000003c1c1025110701500594191b09600c203207812050f85070140c0c02155119940d20301001c0040001ca1800d03980400700400145820103c000300080808507805145003500b010460030701158034490640800ca111070300030a46407810400d0100d400041c0c185001894444901030341109130040c0c0d860503e074100f030300020060741c009a46400b5030320090041900e0f0341d91020309800901461384160310a10481500042c1c5580002c401c40558805803040806001c1d441d050042000b02840010301e85404100400007007812403a1680ba100030010329440c6196960000a240d50003801c0f55504165484c10301c009804598103500400f840c058001e4411003503590180d1610303a90f07507914030602c0610031406070070354 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 558141025 1250 558139775 558139789
    0x1b03080306191508060f06040f27020a120606030b03030412021201020301061e030203040c0e0612030a0203130905040201170717070c03080a05010b2a0613020a0e01180902 75
    0x1402d03515841583c01c1600802c010300355070003a68841d00a9a4413154500c0d81d081c040c0807102965801301206422920b0090405071220780550000f000c0200c2c900c41e14a400c41500060003c6500340d07460a200910510000d000c5840f20360181c001d2625045054413251004003c1e14110750b01140e01011a5a40d4008220b1440302e502024035103505c004000700d4602d41093700b0380b84c018881104610010300020f001e4080388001ea0b805440040610402c03c0b0704c4200044840e130060000e442d202200d900380c00340520f95000300010f5000b5070808a50018404150300c5100c0c000c040c600014000b908060700042c081600f407076444018030203c000050309040c0201c2c9404246400941550401d140070f600040020001d49012800200d0307000204806424500030207041e03841911209d8070b0042e20340c0d00b0f9150345007802c1c44010000c036106044550a207003801800d101d25005620800c8040d96881000742c102160341250a20700c01d408010f108ac2003d101c41181c01c0140c1410009901c41ca6000003065 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 558142275 1250 558141025 558141029
    0xe1f080702010c140c1f02031605120103120509100f030f111e0f0403050106090c030c1d0310060e0a11041413020904090f0201030b0102150f07110a0309031b0308030619 74
    0x2920b02210007078224203896500843c810f040005922140310034521084605100b030390041204402f10400610214a2181b40000d5035459820440d2901403c20041070b109442d000300180414840d8156240a03a010700a14003c0d400600c401c104142585254035160b001c0c3c200f41d0340c1c00000d80d041240b0356212580403503640c211145046901d41e6680d10f0400d000e441e0034058828080c2c241030440c441c55002c6c0c05132502d00c019036100d801c990156480c10904425203a55002e5041c03181044001058245108680c05008115080740051802400e44006e85110788500c1080701e03000c201c1048420080e00801c86140303011030b0326500d5140c8001410001e07000b0b40200d25801071900c40400d04200c103810400340e81c54404e13207040c400f150421004be61102c5800180300d01c00009480080d1800c210502c28030751001c0541401040e48819a003210303e8905607620440206003045d00a01c240521140c01498a81c203260101168038119629501d00d0300015000c0c40c0518a40d8507031201c0c11055182c3c1e000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 558143525 1250 558142275 558142303
    0x60510050d08042303060402040b0105220f05030a03021b0307180c0809120702060903070909031824030207110613031103060411100e1f080702010c140c 67
    0x6144105400c00b11081d0780240314111a21040c034008040d004a000482800314000402800550307486400303100180610007170190400c0070400003d05103d20200908089452880c00da82d4807604042c90405c0c0c0443d640c01046c4070364000102d001c0020750029800c926040c4000c00000004445c102003460440560411000d400e0b241401085034045940300c00f01824075079440641c582c40381d070010717034031a400440c18440750740d020405103025003804070090a4000016044800349a03540304c2010454851041c2200000c801030740c1c0e4580c030301c000400000038102c1140090890b0700448040c500a40c90581614185500030890006014180d81c2040802c00c004d80b0782c640e5046a2800840342c1400750004450084200440c50414100000c00610459000a1303c10119141d802003004138205500386108100440b21400041c0e15501560040c0011b900700d06401a03d400300c0c041e11034017000301800b04580c50401c0030b18206900c60012058010240300c0c540e40c8890a030b07004c0d0306101c1c1083e9004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 558144775 1250 558143525 558143539
    0x32d070305011b0e0109030c140105190c020306070503220206130605040518060901050f150f0a0305070206090a063303020109051801180212160305010b07020d06051005 74
    0x805544101c44020180c61642d84c0d0300318030aa614006440d48200c0380000740541810303500a0100c80b002d06044440780405040440c1400399001c07110340302c42c1000c01c14400040011600c1c1c01142010010160829180c0c20700714113514200395205661820f001d40d0760a2506e1202d00c5c503082d500c82000b100d801c00ca0700446808103a4540001600640c01849418001e221040318426202c0ca486045401904000c000c0301c01039190000300000c1850b52204a43d0140c2000201e003038000c81000280031710901c020203607031503644010026003201c200815080954009804002130320b080411a01000c03903000d5800600b06440150103800701c142309410040c60f5007025502041c1c002a005002c0407a40300b41c6e01c0302034580e1a00140800342241c900c10380200d221a000510100c078062a041030250320b410001818460260030b4000311450541d20385540c3d01e0108994144650b040c060346000d407217000003c0f072520b8010760104140c080b500001070030300c81d82c4401240517140290500401004d00920306 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 558146025 1250 558144775 558144791
    0x7150f110a0c14010c02031602041506020115230d030516050609102a03110412051002031b0c0f1c110c01141c110406020705032d07030501 61
    0x2e0208140807505841c0741c2461503110103064070500402c402c02060780d01441c00c101505000c00a031041c01d01d003c0368401c2c0c58103002170010105201440080040d81c0c000b08030000504a08101c24220750040158094150070342900c4e00160360081c0345250741510f40c04000401814211147c3c00754200501c0e5105a54203018103004c0d0000e26203015840c0b03101510b10f0828104c2c0040222660006130704200c10314801105001c0e41c000c141e481c03c2150500700868041a2018541035a5101e500082880d0b5026840e00c1b0500c00f003000382c00c0317803580c00810441c6507091880b645400c2c080400300310441c1c07940003d03000e00003140c140b02d4014000c0c0c8420071540b0403241240612440d4482c495014000b5a220f203004860500001d90a105200107848407009898078011020032036111034401c1408c80010101540e58001c0c5203c0c1042c61211540d5141c0c0b9242840402404c000b4294000d912070b03401b0704025108070780020f800c40d6910100441010041c008595140d0a0100b1a48081c001d54680102 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 558147275 1250 558146025 558146027
    0x506160b0c07060b040c0219060603061404030e030601180207141005161805040f020c060a0605011103031e041515050406050108090a17090a120302010501050607150f110a 75
    0x1d4070b1114400c250600c0581c2c51041804200c40b040d10103640181d001c0001101c104c5041044100d10a005900106559403261500310655140d032240c54800c0ba178070b004000606520020007603985130206c001d410075501d0002c005d101c44900c000c206441550010344070040001c000e403c0500d821540b81034402c014030142800e001810f084820385005008100884402485000600c00030211030b052a03070034070700305002e010090516940d0302d00303400c2d801c1000c00c0c0980c00c00c0299504c580112000480d03501d081400061520140b402c0b440002c1d0b00520a00281174200c14480400e030450a45a01140d030748c9003031042e401000c0c07021515030140f03000c4005982d00c10242d0240c0942c0ca0943d0103002180d0340f40011a007001c002c0711700485039080307022000b00007a400d40401800c40341c541000d605107130401d0001100c0554a030310080110210000c1c0030201038080c09000e0040c1030823240300742841516103a0b010b0aa138844d43c0000d0070359071495003008450465105000c0303d5200c1000585480401c50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 558148525 1250 558147275 558147277
    0x1e0c0903101a09090a080414131a01020d0306050a0b0f090a03061406060403030503150a08031c050a0b1c0309091407031d15180d0818010c05040506160b0c 68
    0x1e03540200f6203000040c0c07015000058441c03202c2d500054042c50a850410400d84070300c422120f0326409a035030b05403540d54100e030f170080c5c100031409200404c190718643e00001e0f2610500d41d00720400d05081007010050f698580c00f24604882c0600300c2665100c0720042c018110348181c4240c1c55202c2c0004001005100940d800210340b196a40c00719007a44c1c640504100300c1e03005074400140010010000245000611105c20f0320184020b0b1180079200c0e1299003850440d040070302c44101000d40003484072010b034410300810350410041401000201051400309110001141082b44810540d07080c1408040c407070144a001001002820071040100c2109180191419151600000d080c50b40a5a00a076940d0030140d1422068005043c0b0280103241a50040c80c01401c1143c0050303081244500c1d0302c0207021014443c0026600d5403400d02d4852411001100703004103040b00c680c500141060079580244c11038050b0380f000c6455540750150b0026100007200301d1200141200c207890240710603804000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 558149775 1250 558148525 558148571
    0xf060903031b0807080726091806010509060f09040213030614010e01050d050a02061b15130816020a06051e0c0607051b0105040b010303081e0c090310 66
    0x1954501d003803503030b000340d412200050a60140885404010344000100d10304018070040b440b8108980700c10010307890341440d1003c3e194542e10401c0f00092407800070b14114458105c074200740c0344a00f8850401c440003c1c400e0183e01700301805103d0004485c510014940d0907108000c1004006540e1076911842d00094451684403c684250078540059110b001c8011054182c034801036600748507a00c7c00c0f0820164040c1103500383c40a0142c88440400b5840c2c150040c1840d003528000440320301a1982306030f280102111a05401e88142414402c4c07048075410300030792164102d0801900c40c000d8803600154026550f00096000f48100c0740001c0307154220014007805624030318010503204214074000d0701440340c1c10f48802190800e4000540042c054000380c038405981103040f04051032410045030840c0c00035902541c102d10741d07000400808da40b088819600403c1304124a9041500501051555a020304078281070000402c9039595a00c0c10050301814800b019070038040981c0c40b85500b14801444 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 558151025 1250 558149775 558149777
    0x72418030813060e130f06030c12051509030304020d060e100f110a0507021005120a1401090c0503070305041e2316060c0201050d0509010209040f0c21060f06090303 72
    0x29080000f1500d00036a01144024800351140703480705440184000148038015848031007070764a030380100100f40040700341c9010708000c10407401c200e401801c18510300340b8103515201d0000340031810072403041808015a074100da4155074025550010307282101c06403c400449552904c10b0f50b001228500d05908580352408184000700729200c02501800d03c0341c8255010707003000c550100120307801420400301c02000350b04503280503801c01400040307121582909850241c1001d0300c0342210039103040c1007044603005100b0100100820254240060564040101514245a940d000003410301c0b114051110381801c88103802d8080005504c0d22011132507800c0d505800740074015955040c07203500041c1182c286d00c11076491a00355403a2010454080c4080141241000401d1000c1c02100600e802903078000c6a8030000562a4a44041400200c42003030528000785804c004003400055040402d8000d248451400c43c040a01c0030815000a4181c550014030100c052920004165501101c0071050340d201e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 558152275 1250 558151025 558151057
    0x30405130f05090c01090501080a1401030c0e06010302040302010c060b010908030a09141206180f01060308041503151a210f1806011205011e0507110724180308 70
    0x510700141d66a0344c2601d000c54040b61000f0000d010541c00b403400d00317900014800c0c3c0032a42c0c100003200e101814000b81c0c807c45c0e02015034107041c4038102507032b02c0d2107600142c01c3c80e0031400c0c6451500024160306580c50090010340d514400303614964415094440030700121001c0340d585010044c402459801c1c90300c0348603115039041e01d500c84545410000703040b042c101d200040c00c140e1500410107140f4a200b14a880b140d1040b2104850551028010b0600941c0900742d20b6444a2500c030749151a2015400d0582c20149031181450980035070300c4110f015a03d106081c8007640c001c104401950348100c02d040721201c00c6404035011071007080301c0310031f200c0e02c0c40d842c441e0b1241e00c030744c203d0b0030310081030890008164018034010301c2521070358007120348464000d0001087e20030410348a40c42a040200340701074903a460708200704001c0d402c550b1207840d290241c0000e01c103ea20748003407400c40540e00111180c0b84150082c641c40030901c01c007103031380c015851041c1190402d07035249024041a44615001440111 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 558153525 1250 558152275 558152281
    0x40906090605030d030209030a0c030b040b0a020304051f090c030b040309120302031e1b0c27010902090f090907030b060d0b07080a060f060203031b0307020a080c030405130f05 77
    0x203460007100d040741c801800500602c0e65800341038000e90030051401da0144a00000c100120b16112401300c0154003c460301c00407410141010030b8210402404501d81500410510000460000c1d5040b602100c10b00da0f00340f07107689002c2e0781c809000c4011010f010f22803010004414460f611881502441c460307119005000d640b88900451a0703400c08010b40944c1050042c9403082c1d902c414127803021a890181540380035020081000034211102902d4841d0740580030441e00f500700b24018580e500d400104034980c100100380c0000041c18140584d0f403480e03402217002d103083d444203401480b0440c0700030303d61142841c01c4d403840c0343c1e101c0c150b01c019200e05500b01701150700ca04091000314000782c3c002c504003a490b920703038209130744141001d450101c2060741c9040000e2822680301c41704000d13003059800307540d0300d041003001c5401b100d0104040f80501c8000b08203008086800140301c2028540c00440075807240101c4000e01d06600640c0c1c8403642000d00000360000c2c40140c1c0c0c3c01385014241da02c0040240361 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 558154775 1250 558153525 558153539
    0x11071715070e060f03040804170a301101021e0a090e0606090616020630090622060203100e0f010b0324100c030f050c0d0f030f11040906 60
    0x120342a14000d420107010490900c01c4c3c0348490046520074003134a1b2292a107661000305100d000543c030603030422070f001915828100301590340f04d0b200c03544991350010018016015082c80a07101c040c007642c1481001c5848a0041c2400e4058030035103980c0b511200c1c04002082c10321801c540c8190f031401d0000d5044500840c1040803038480d6070080b0005011a42451510b20900c20580e10090740c683c101e9001d01e03030090051307880c00b00400c0e8200114401d040074048045091003000c400003035000da51030300b0340100040e00600183d4903a01500050002000400790102c80030048016074001d001240000100001c1c5202c0e80305d20270440b103610358818aa55a402e0405075188800e0140000c0480100b011030840c03000311809884a010441e00c420b182a4850000b82a64414102c06e0021034030702d84c003000525400004620044c9078a0510501d0318410302200c648070740301d809680302406149c000010b480c5110b03503c1160280503001040200492400b0040480e030041d1080700081414214082102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 558156025 1250 558154775 558154787
    0x8070302030702030d180b0405010209040b03060f0a0b1f030b0906030307020d110a0b0316020f0d0801060c030306090f0e010f020c030301180b1003020c15040f031107171507 76
    0x245060341e02441c00c00c080400c5c110017414003601403410084224250b140401e41034902c0302c2c0100e1145000603940d000c2c410074041070f10540d038200c51094010404100b90810032201d0a6401007240c9800a5100030003000a140c24140d8400d120000400b08100981c00e501030348481c0e00013200311a40c42042c1c6e141810946e8074441c04800030f41120328001404002550b1f2184810f44240c02848040c905480c0c06a200c00f82e0011100c0b81402103981051a250580502420440d00c0d0440040c040b280301000d4003901000707040c0724840401c40510092000e052096020402528031200103001402020f84800007401e198017400c0650f5191000603486031b800d42c400c541107a10158007850550b0710340111848280480348400e0748250311842c00c4c40b0503680e024403280005105440050b100e0510503c0c031890042c0c0040c110000c1a120300c08c2c0008981004040d10030f5642c14074000561401000c0e1450609920f80e101444510508104003240c003404103103211000b1112070002842e50700c17840c1c201d0324 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 558157275 1250 558156025 558156031
    0x61407080d0b03010b030a210e0a060509040b09010806070f080721110a0903060609020310090b122d06010f18090807031d030c011e1107150807030203 66
    0x80c40c034104808540003036150015144a20001d00000c0e03288049004241001311302c0e4001c9440c0d200100207000302c10750708010114680300d01c0c904022010304450201c0d00444042c040e2070188000455601e41c150741d10b420000040a0140030302d00384c1d5a441c0c5010b5518802522420081101d450229501c02d21905031244500d080c0c1d961006000405450607404480c080b490020f00c5440b010451038540d5400d0041441c00b91a62752501481e00d58188079085404540044810b0340c01041801810098503c1e030704103441203144001001c01c071680014040b40580160910b05004915852a00080d440004641000301035002030240049541c010344401d000d00403501f00c86602c803002c1c4031541660b06c0c035581184840342c001610004948943c00c054002030011000582180c0301d10005203205c03608200c4224080d40100020800040003071b01b4103008510003908038800c60308036144240b10b140304000b000d0440e000d0302c0b0300342e40300d016100b213851400203010701280480d00491607191003403088030700c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 558158525 1250 558157275 558157283
    0x1e030607080c0307110a08040e0714070c030221060f06010e041b0507030c060608060403030605010f1d06040b07120801050109210c210605092a030106080a0309061407 73
    0x1c619a84d140c0c09542e80e490202e100d458070300c00c070002400001c00300390080025100056103041c1c1d52030403070340c01444000c0d01001d1820700c40e81404048000b940007004072081c0c07a0b04032206c07100304041c4000c000341c0810b01c44201100b88509401d20400310424900390307000300001c1e030310160048540814001600c903040f6140008520000102d42410f2041016125140c403a14004802400301d448100a466440d00040030580200341400205034042c4513400c020f085c02c1c2425400722240820260000e90040e01142c548451004004525a20841114007800c5185070542e1100b100b410040034503074600d802100030034007240010403990300900c40341040f600d444072100c00410040c0d20020424aa1907030440e101d01c540300340441c9801700325518460075250740410a015403e070341000d4080c1c800140c450710b51034102e900d6090300703141c00c04503c40b10812404095113803410128040390042190760301c94941c03400f50311030310303020140d01c422407004503441c07980e40054111803070b08003031014821808010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 558159775 1250 558158525 558158527
    0x5120702060f09041b0305011503050403020c04111608070209090303010308030a09111f0f03110406110f2a03120d1508030d06180902010912050106051e030607080c 72
    0x142c5400700b41c0c4020300601d500030f0000b050917911556106000d00710b81a0f041c2c0802c0d15403005002480c034003051309418161601d410700642c141174030701940f150400501e060007a078a0b440106442c0d8030a4045a0000403010102c2d07260594a050460041e0070200c4103d02c0b030b04c0740c0800b00307000b00d50020989060301c0c0c0001c20145103444030441c88000f40404501201c200e406803c1035400b03030352031214200080344816081a1040001000101910011400b0001b4107103010a002030000704031042c4d6080d92428101004010604400e4501d030440c0350f5041c40c0a032203005042182614070131648010307400f800d821010561f0a03841095190300e07049107924130fa10ba0a105601100100c2d800141c172001000a2541c02941c440011038210341c4070662820302982c41c0d0300204000c0002a485140c00c541a0707201300311160b402d50000b0030782c0f8814414003560725803080d200c000341302081d4044c0b001040c3c01018134800303186441620f2072458000b11100d11900502000030f450030f025051085c404c1014080302c07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 558161025 1250 558159775 558159787
    0x70e1608150a1e05040207030309050d031401050f0111010c03090c090e031c141807060c080f030c040f030c05040e0c18100e100305010e0f07030818030a03030501030512070206 77
    0xf000542400700c0b90301001d8050194002181d03110792000b486002e0096401089103102424070a05d0301032030300a002c081501e002c000c2c00c282409403d213541510811200810401c10a200484a100760154041100e518000005c00125015803003050310034400c2d4a070503062680c4400c0d0f24216904103d6056480c1c000700714029030a0034202540c901d48129040000d8900b242c40c4020342c140030111600c0307150303c0448030b484008103004c2004070300910641c545116584081d0741c40c400d4601a01e14602c40c005d102002146804071201c0655003c1c0000c00b40d0a05519560300f00010b401c8064030603a805245800749030a610040461a8a030f1000040e0004c440500410300390010650000e05044045101c0100881c03030700d100c02c020034000c0c0d02e126a55071005007141005d40c2169000b0b4118100b9a000b4180414014001700f100c034220703504080c00e07503220341c0450b41110024030311404080c0d25001c2c200050007059007540c4030394182e034040c400b291640071b2081001d030000d10038044c0280d4810401d20035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 558162275 1250 558161025 558161039
    0x5150403051221040b010f0b040305150411180703050f064614010c051f060b0a020318031209040213030f0c031502070206180102070e1608150a 63
    0x400c0000c03e06000ba48900c600c5108004000400b520211103d040e000c004218072254200c03d903001c0c004070b1b05210301d400e15690300c0720381d00c03422001c8030702e0001407003400142408505540410b95003009061462071202c001d804a080c00c00442c0c021020038075040114280007030190b045413040f1409001034004958441003d07030040000214031032040740d0710307518040d02c030241190b0111a0950340300d00e032509424085810048000c0c41c3c0ea0a04211030000340d0004220001425060700f2046e20f801d0242203080c1e41000302400340c0d074003c900300781800158004000d174000014441d100381c005c501611515110101511403041c90024852000140041c1c0081d2926070300034159100c020002c244030b030741c0d00d035520802e00f204040c0503901464005010130500588460400c68000045002c6150410380e0b4001403907409030803003030714416a14291071003107a4020803030040502600c07040013803185007111351040010210505040052032841c04144e0000200d039401419513402001114114100a0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 558163525 1250 558162275 558162277
    0x308010303270609050406090b010813050c0a1409061e01031e061202100f17280203090d0507050607050309120a0203131d010509060d020301050a06051504030512 71
    0x748481803500b00d11081d00710003100007112401880c032030f00c0315113490785040b080008503800e0f40c8c00015a90f040643d0801a46ea2080041e94008070701d00c00898894600e04219141c164140c0c01103401c9242c02c440490182c680d03060728185054212401502c0da030390380041c40744c40d04180d82c800b09810f034040d0f0411390945c021780005002e04468140c40d00d00f10220304965007034600d039520814000209005000a5003442840351003c1c0c03581d4204511400a103400080015403134012080d5003c0d803050128028420410885d64015881c0b08410044170072450b03940020342c01175800c074101c0e1007080c2c010000b043c0a20162001c15420201070f100c43d0341d40380d0013502c543e40014482c041a01032a101d064181050380d014020750a050360046441e07000f00d0041c80030100094012241002c111866540c1c035403415010316042d9042614403542c542c65000100394019121440294075500703240070080c10400d55800042120802c40300508403400d807038003003500c600c200e0201400d26048152900c1400d0410700c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 558164775 1250 558163525 558163547
    0x1305130c020a060b0102010b271602030901030b1305100806090f060c0a0e0d03111002160f0203032505010c0c0807030c02060909070518191202040f02040b0705190308010303 76
    0xc000403600580450020b104150003640c062620270b000124500300c00518180d580d0302c245001d0064510701c00341c4001a40c0d03805403c14850406031180c2c904c132000d442d40740394125500711514050206050036454490310200302d004410051282800281e5a484001075020303726036100003518803030712003880549507507000445000501040342e00c1c0f1115515051750810055000e503807001d81c24000051240d05040d0051400319401c0e0050000641c40845446043c0039035a1080803000d29100030f1000c84d046010740b81d1243e030000302d902d0200c2c51050400f1001c0e80c4030740c890b20080081e0040e051003990910103142001d804410309010000000307000d06a03600803107000500c101d040950a00c002400329000302c816900181c40812203842d04800b200c640032510404a90660150b000c032442051040120b00c100c0840040c1e21460704150745076903024070143e40c2e00010a6559079101c0c0f0484406a020318000c13070b1107105521103250fa8541009140c070710307aa45556407400c140d1075921308a414507005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 558166025 1250 558164775 558164777
    0x90510061a030c090907120b0a030809040207030210050a0b03060f100506130839150f07060f0605011202031506030718030c06091205060604110705031305130c020a060b01 75
    0x1001070307901c01c0c1d44101d91503100c0c003a50b988a080d907c40121100b020740c2d44018499001d0080c0390002d000044801c2c7c25551100825030f00181c440000d824202e141008406050448501c2c0805000c14032100c0e41241d01d5003801642100d6198440340390750640110700b1540031503581c4411790144450f00d0508010032942290361100f264541d100d030b00050400c460801d03400105240407800e80c940355030200051a42d0111503041e51442400100801e40e01142225600c0c0d00100004130380010845038001d480c880b9801c07a500300309030340c440c1d40320760010511030140f180407272001100c0e54104100f900880e48038240260700b441900135494203220154001518520600480c107850408920545034008020340c000d80320200441d25064000d88100c0054021044040040313a6a10204030000b902d00d402407000d40d40003a1681c480d10b0780c1e007514002c0c054000c10780d010026200c104010741d0042c070000c0c0c5408882d062250b0580d840c4110031078a8405241d009600417035103c8010031140c0e400b03001d5907041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 558167275 1250 558166025 558166027
    0x6160c0927020d0203070e130209010501020f0d0807170a05250905043215010302071e02030a020a030507080c120a02013002030a050a0c08010e0c1c090510061a030c 72
    0x84180e8002c034a0300c00c8412030b685448c8071a00f6802d5141444d0a42d004010a00180008800322284c058580e0810200310701030041d10008039100038030941d030000302c0e4111000740301c0407801d02d074194a0142030305072003c81d1f200e8508082c1c1c0800b4052070100c2c01c1204c2d401d40351004290b00d00f100b804090212034002c8035480c2c0c0340382c5440e01002c420b07400c03201c4c1b01a01c10400d1206454000c01000d654012203400c681012b1040c410300000903020040c04144410420303501008014500c006486c00d28043e10080d00928141800020440700103a000309540340d04003986c90310749041c0144240100b02c169022a5948615001d030059402141c489114105108400402c200984904112040b603c003500c190741c1d41c00410030800300000d20800c0d07000002d214017808650003810000700086018090582c2010002d0b011480942c020405c6400520742c3c1044100030f190340a180718018005000d040e16507029100180c001c22020703104560a8500c560f03980051f500b050b62954410381c000610103420404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 558168525 1250 558167275 558167279
    0x60304030309031403130204060b040501052505011401141c1b05030d050703080a02040f061d090114241c06180518120406080606160c0927020d020307 66
    0x111300c001148128201111481482d84520500040300c07500c0d0f01c040350080003070105010310380c0c1c04400c80d0881d4040c50b120700354829041900c2d280183c03500400401e21340ca000c8401d80900c40c03105100d07048884001d80035031a08030001c1448041e24800000710007150504400c1000603c035000d00010325146546400406520b45000c03a24081c0d80284141c04110082100010181d0000b20558007480c64042581003030310700140101d03266014058801409411003035a020041d0300c00c2042e1282a008010350810b59450003c00c0c2c3c0159020b91403800340400c80a01009404011902e130516070b62209064a001040040740d038005d0410000405130030b8a641000494807140303000240301d0404004002401d05000c0a00009101240c8518171150846801c2481c0c0800e0030b0182e0f0100c4205003808125a030390f100000b0001e100e11008071090707403050555001807100d0100d0100540385848000c004400444483d601c840400303514181003060309805900050426454100007684064204c80c01c40d5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 558169775 1250 558168525 558168557
    0x3111603060203010f0915050906360f1312050409090c061e020606011b02031c27050607020105071403030603010605060a0e011d1503060f0f06030403030903 69
    0x2111984140c501540200c01440350101182556009041107901088400600207241014070130503c2194801d40c210b41c00180c1c0b0b0785401c452482021010425a2641d00e200807074011300885140316981504401070000d220b00c150700711018040c900c0390f0b0300c1080c6030105658400c80c005074200501c08000307040c00001181d140a00500c1940c521800e400c285903401d086000707200e51007a10292207054800100d00c51480d40100d10150407200038a81240104280d005d14452000303000c800030f4051150ba0410360404444d030812014a030748940d00e44098035030071502d25041c082d0030607034490100c030903803410030082c40e0000050800f0751060502c0d500b002c01a0311210070700c80c0b00154008468000008111032441c1c01e00c1900302038002102c881d41058400c40c0d000381404011030816043c8000c01984c02850088881060b410300340040082600240c1900042001d410589a281c002c11071034060011300d19100e07502d515019806802d160955680c0d4074124081e190f550b80640600c0240d102c850302e11 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 558171025 1250 558169775 558169813
    0x20307051c1109100603200408061b0c19050109050a1416030b27010c02010204210302061b19080f070311090409060b18010f080c010c0311 61
    0x40301c0c140400c429281c65030300b404a442c900d41400307584600d1101d0704018082c1c42d41d44990081c0c03200e0b440c0006130100311209012440d400b0540c0035004030790104000a590100003071030f9110354200309503a00d0007407007414107850600540351100d0664210280c180503651f8000c0c4602181c81c0103000104008003251126804c2041c0034005aa100f4090300d40c1589400c010803503000d00c0302083d050102450320b50b0711030b84103100014207013500d02d00060390540242c141501c40040b18003030840c0208240d10640344064000d5109204003160342045001d07200c3c02d014120b40221285405030040d010565600840c0c10303060401d501c039039043d1701c020700c01c122260780482000074850300381d621401800e0814200b50039030004003c4c0800101400c0c02e0711580007600d0381c8141c5000b01e409403000302e44500c3c18079080c406007050f4000300390441c0e950800030f107415010f04074981c12039901492400c1c11540381c07a4500d0300d0b4101c80d242107010420074400c81000912601c24103e2450500e4156000062603000b8111700b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 558172275 1250 558171025 558171049
    0x105010e040f0f061d091902041a040f0b0f0109030237060512090105072001020f03090304030201031404050304061206080307120809240705091c05011b050d0902030705 74
    0x2000b07038000c10000c41081741a18550401e030303004000c1011241d8810400c3c081040000028002c03501d070440c1c1d40c40082541e1b565440010014018020070500070b407032000410218000c40d00c140c0390380c0c41e00c100650107a00301d0001d880d0082c08040d825031110f648003e007901c4001c44e40d4140d40c41c00840c0c164440ba4100e840018050542d19a43c3d40c3c40055850a4540e80103810f485a40e49040107211175a500401849031411540c00402800b2401c96500d600901620b150315a5008000042100d40c2c403020004000780c0f071003600c08110b081a4115401c03031001c000c0301e004009030710401c03003485441c0c0504205254841004004030740140c69441d03490554002181c21144143d40c1005c0e81c03051070f040720217030740d004006030010503603880011185007050080c0803842d03003050795000106580318072510458400702c00c068400c0c1909000184851100c050301c0d181521203510b41000141080011624404003913000d0382ca16050100515a18008140f0f810b400c076450701c1800d80014050302c0700100856 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 558173525 1250 558172275 558172289
    0x8031312020a06050105010306140f041506111006080d21020c1b09190902060705060106050c0d023d0c0323040302030f0a170f07170105010e040f0f06 66
    0x106460b501e4640260384068114905041c01c0c10380c20300030034284040344001b280d0112240903000070940007240060058241c2007000117500400800c0154200d601410291441000c40b16001c41c50309200080710624000d60465800c800f0b068903d0511940e139030484250903680c4040342d00c80c0c24070503000b280e06c41125030403075410103a51701d4114880a920106034003000c0d42c5d11140383c9083d032101d80b00c002040c803000511a03655442c01040d52102000d480405500104030b81c03036941c45110141054104541d075242074441c1102c40d170b00d118404140340d030621240050130000e003085c507422080503040081844e000e000008400484103541802a080e86002c96140014038080300d03c02c034200304150054a61070030700e048040c0000654000110755440c41500031054807101610740440d00c0da4400d8401e841021000c0381445003919480525a0080e680d5443d584006062200311104030300d0244038503400310340a40e061078100d003041d40000040301003080c0009900110f01d101c240072500c040e04058 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 558174775 1250 558173525 558173533
    0x1e0f071b08032a0f0607230a170c040f0512030d050a05010501090b030114010516200f0f09041b0807090b031513080f120403030902150f03040803131202 67
    0x20700e00b04500b0f01c2d900102c800203010304041d0b00715011296407503d020707082004110340541c100c110100c1440070014014080d80790b45680703683d0110000c1c100c0c07402c0a11038a100d040b03640480c1d01820920111000c0b01c4249225480b40c81c0f6010410010040340c0c0d203c420540410080900c81a81c03d124451042e10f00c00000a80355040000042034089140c1201d11003200410051154205121008020480900c1c000f0740d039040c030000700c08404402c0d01c2e00411818110100000c1280100c0780f030024204251a00140c01382d80c1003c200c4503108070112071b0341040d030300c8000c03601180140d030300e8100c0d40440c40544481d103a47e0350001c5240c0140342c2d02aa01150b61103c0280040c50103211400d41c624801c3c9000c2c009052101ea640c0708080c0c01c003801800094002a44001da0b070344101a91507440d40e220560b51585802e040240240070385880880c072405400742d017400c924a5440c150b500140e249031446045550b103aa400200d6030028104904c030407a8020008005002400c1004955266502174 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 558176025 1250 558174775 558174817
    0x90206121003030e0a0e0f0c040807030c031703060f0f2b0227010b0a0309150905060109020f1204050a1b1a070206090105070609060609021e0f071b0803 67
    0x3040e0f1414000011700c248580c0c071040203d81098000b980d0050724410b0540c0c815280c011282c1403610890380080700a028010300042071007a00e44465040ba4060000b001e540c154501d8840c0c503900c01100d0942c2d0204012401c08458284074140025229010b00704480780d4030605c502500b4150b014401c01100030030f802c081001c6051869a03103a060540d49040c0440850344003554240101c14010100500e1b0080340510708140b09400030040d540c0c10a00f0609002444400c030409465681c005941d40c1c4909400018422602e10886100c40304881c2d0312810007040746441d5119400142c400d03a464803502c90b8007c081000321111012000c11501c0094000e42b4001590101010050b0540711550042c0b1a1a002d621000c1c22900280b000346000c3d55660340a14101b001001d13407120160103035240010218042e84a039006203400660528400450724a11803800010f201e101c1640034000001d111100014007404c0d4800c5c0e482c080d50090310103898032a102123255400011024408640460303079 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 558177275 1250 558176025 558176027
    0x20f0d050618010f080c03031603120908030a020406020c0f090a022a030702030706090f06050d0e0a2604030c0e070203070b09061b03040201020a08030711031206032404020409020612100303 83
    0x5640c1501d01b040d4050b40c20801031240d102c1c075640c1b442d1405000d0100a81c16002c0500147c5e0003485000c2d40702220300d40b04c1c100300026000a420a00035100944215405c2442c580340c80b00c814880030030000c00065040e40e8620000c4060340004218141e01600050031455429148409018050018000303649a2134036004040c90840a5070005007030190f0500d0500c1444d6107a41010146c441c1d40c2011360f034500c1c8071a0608024407a4020100703039405040342281c10030101c07401d1101103209540c010418103111815a500070321441c4402411108184400c2000c0107859510a43c8942d13607005481c00c0c941d054650a20131502180c001c00c1c260015400c202c0d080c0b0311203c01d0529503030003200d118214905640040c0d074420040384041d150100200002e10343d980f01e0f03001c52420080c00015291581d461030210b44104030240c80c001d00c01d010300705c2400704020b040c036400c000c41140e24161110b16103407502807000402c1d04400581e007145c0f0801a02600b1184805070074007804400203000492403440c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 558178525 1250 558177275 558177283
    0x30f08120c030f13080c0619060b0901080103021302120109020c1002091e03010b1002010e0613030215040215030103050309280303080c070f210201020f0d050618010f08 74
    0x845011454240700f031040e550015107195901c1180101404402d07185030410480764090940141058865a0200540c800300b001e10501d09900c40c507814030441b81c0303941d002e071164001d0040c6180080e03807010041025180030300c1413006001c8444c200600d054046421200c802000b6005242880d40001c0c00c0405014204408115000c0ca00011414000e1100006440303403000c140ca00c24000d50074403021082d950a511842c916000145102200c801c5104041d018200c0e08800e410306004e00c01c0062100c0182a0800350042d50650150800562a0204100b600780250090380c01600c2c5c007203d003460283c3c5100030341c00f9500810086458000240802052100d01d23020290b5500d500b0380074451491581c2c2d00201960750500386031800d0741d01c464071500180504000501032202040c65001800340e4a006a200c14101c0e1440e4105982003a009900780d100300704440c074210720100501800b1145c0ca0b8060754000500528440400c44450424810f01800b0f800c0303100c104000500030094840100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 558179775 1250 558178525 558178531
    0x8030f040507080604020d022701090b0307090504080406051804020a11160506030a020a0509151b0703022202070203010c181d01062003070c050a060203070c140a030f0812 75
    0x80000e02480c80c1c180d010880502000700000e028150b9a2140003a5064126409d20103803007070150f80b002980d4070701c0b404000c0c00e42228202e000740200c20001c50011014085c0a224a4015905034909803810000711450350141182c8200500e83c2c29509081ba82c1e20300040100c042c150f5640e100200030848030a003400710654117401031144a44040100c0d4a408007640e0340300c1020340e001a151201a10261500e00c140741d501175020780d080c03207104104031014002d06850b40f0007000501c0c1001c0ca0303c0c0e0040c0c3c3c0e1803003808060340c09401141604a081ca80c40301c900402c1c4007a410140c14001c3d141c0c0401c0c250b03420b651a250220740c1c141000300680801010407802440d145140302c0c042907a20303801203003889040c001d44007040701c1c0c4c82048200c2e41c0ca02801164100e0340308203d960390700482c20f1540d4404020301a179840b400183c20000303a003503c0001a20710440e0400307400a12a890301041c407901a244202268010407181c83c00000701d0300d07081300760320b0050207011901c3c0d40308070150050790481c81c02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 558181025 1250 558179775 558179789
    0x30d060e0406051f031e1e1110050f030411121b0a03020a05060307091a040806011d0f04170c010501080c120619090f060e121608090a0308030f040507 66
    0x80c40c00c20b00382d021080780903800c49412070400011b0040c00e1031451561900c031100585502c58207141d4865054a0605c0051080c0c040e42a000e02190b505040040d1000ca040c80c020010b0420b100900c038401010b40110b4002d480351900d51803034410100800c90023041180404800e402000741e2030101103608041c8014854200d0383c541915045500040d10303a1000c1c00750394003c81c00400000c03050f90082070326170080c01c1840c1c60b0711203044039940a000340e0b60090240b680c00d809074400005080c0f0240c8044603a0518500450074640d80e101c1c08003059840007041992102c503201061821032102c000181034040c00d08002207019030504280620b0b1907550310803940190000f140348030710b2a8009c42e805821000d03440307400d00c404440500d0300c1d01030031010001400c860030948041c020450264450920019500f064440e40f070f00c00c061000c001d0003605112464107200c102803c0010f41200f0007420b0885005240211054036510f400741c40f600201c0c2d0420303451070840244401d01104005600c014060 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 558182275 1250 558181025 558181051
    0xa20100f0f08130303090c120f03020c01030501050603010909020102070e090c12120a050c100c05041e0b0f07031e02070305060906250201090501050403080601031406090103020f03030d060e040605 86
    0xc21220f0480c41444009000c06076100c680400f00205009240300510668040c40d0903600103091220514042d0740044001d4802c1c420040e50755400383c0201c03812500300801403801d40c0e04c2c04484d2409410440001c038114010144c0101d0781b204454030507802500c0c660000e01c05165080c2c1400300200d43c002c148103080e8132100d6a1903984100c4000c880062070980741654403191003c10b0945045031808035404680c1c1040c0707102400c1c5038414050421140d500e4408031903203142c11070401202080303010305009003004001011038508220002d00d00c42d807007803900e800e143d000703c918003070703440c190040300c20060700404020414850100101e50300300b00c00c64080c11490411580f0524110324403003c041248001c0c0e2100c0304181d000b907200055054011009000b54078040c58006d1400500b120345501092414000d510b02140704e0807101d228520107010601030307074216000c000d00700080c00711082e40f5210420062200708001d0050704002e0084440100c010b0800345069001e442004100c1c1044e108 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 558183525 1250 558182275 558182281
    0x306071814030d05220603050a050c0702011421090303090f0f060109090807021e0a06030209221104080102070b0c070201080402190812040f0501030e0a20100f0f08 72
    0x3030045081c0c00010114202181d0751000c2684144840f8036204407170300b0103400e4000c005000ca4060b00214896010042d0400c81595040c080030307000d01614001074001000c00d440710080d40390840061110581d21207444800d66881c1c4440d00c0001007c68075848540c00c0801444500401040746a140b1140c00300581244411001115514801403040b44807036a1184006402c2c4501d110444d00303815000380940301d90f00b844c907642407020000e00b6011030260201c0e24001444601c00c1c0309031203c11100400d040503080c3c0c0040b0307a407480041e5203086c60b29695074100b050901040b4a009100608410700056113590950829251000e0f00030b0805888103030400114006030703030007054168482d0b8100d4010000309800c4803a20f00304056500b004042c0c2c41400301c4c50a4030040304000d07204a40300007800345c4e06103443d0401142a50031201001d201c0e0b0b8040600200020078910714541d104c502c0d45104445041d0007400500d8200945110782c021070042009069401c2c0e119400c3c000d02c540d07038203024042d81 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 558184775 1250 558183525 558183529
    0x30601050d0917121f060207090e030c1504060b1801230a08010b091303140a11060103080901080a060f06031a0904241a01110c0306071814 61
    0x200c208010021060364400d5050300f00680104070242c03548940c9201519040d402601604400d429640d0020202020b402080d803444082150015500316501802032185056140c0d0003403c1d2180d6140028001807080c40c45c840e1040060740e5031207080660002140c2440c1c14004201c0700c41c5403000c0d009020740c4003114103031808451894110380902014500c8140b84c402c1d41a50552603150840d449020200c0005480d24150058050b40404a4600301c00f03484020115458001d140d0004000ca01c100c103903000c02110140191448103c1810f10491b070b12080e400041c01c01800b42c2048541d03007800301d040201564440d22280c3d100101c0301081040600780007200844800c1882a0020183c403a200660b801640c1e0f06c0c00c0b500040301800782e21040c1000c0c6003050411004204603442040307203409030040c54013503000d960306500c185004610307803605c1c42d001160805e81108800790188544030111400d42c904200061165200d95902a02080312801c4075454280340c1c0e014080303010742c2c280b43d00055 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 558186025 1250 558184775 558184777
    0xb060a020304170303010503030909040633051e0f0316150801060201150b03070306180b0405060d0f080d1407030504060c0315090902240d0c110c090a0b040213090e010203060105 78
    0x11440c11220040bd41e612440d0100190540d4601450312202082c641c5043d03504003c0c00d140e5200110980c40c07035850700c44040c02100174001900030360441561074030f0300141c1403480c500b1034191405010b0300d001704220700d410b0303141c01050342c40310440b16111041c4480659210340171901400503480280312100070047c50710204031443c050300e080d030340700003020420340380c069480310340101511000c0b60401c0289440c120020035195403118055400e000c0082c62601c1c01c4c034207610616500c04110b20200d00c958a0f0340e0129009100a850b1b184d5440015000c602c4a110445100d04025034003c07400e464145484010348404528600a0508101e081012003a103140c60605649551200240c3c00d60385000044c14030003c510560341c1c140000150844180425000307110485200400b80082a00e50608940c0103401190340b040940203401c04c0c21080c5070102169420041c05d140102d403818810000900700c1c0c0c08002848105844020100b01c0d02071513008007100304000c038008604603d020000a005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 558187275 1250 558186025 558186037
    0x50c06070e1008191a03072c0601020a06050114131a0418020a080a0c0509060f0120061509010e070f1227020f03070b0a120b060a02030417030301050303 67
    0x1031002d14000104c518032280c0d506100003500c18814000300e2820300c4070b00d88031211800c20324000d02940d100814241040001c8201190051100007507071022407030b040d21074820181925045000d0b880b18000481c5103402140c1c01f9044c002419191068441c0c10803007141041c495a071806424040110945810788460111204055401040b40545800c46020803443d100e8001e41c005241da6001c58201d600007408581d4600c00d28500740003d88810400c02c150100702d4030035134403444180c281d0b0700c07551080d5050160300740c0c242d10014110a03510100b07403d0030340441e84540072840c052000c449515080b00e10070300500c2c2c1803011240a04141400400200c0c00c0422502407107901c4803400001c01c0d0f5684005202141040544d4070403040c19001c40c5107103200f640680c03040d1f41030901e0004174a0041407030801c030340c0c0e5049150301d050180c403000e58a400401c24441c0c1039650b81d040d402c1090325164005c00c07044540b07501441e60380382055180d030301c0d413401d44a80601d543c0c018001441280c07270000803116 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 558188525 1250 558187275 558187277
    0x2004050a0605010806100813052113090b0604050d021c0b1e10030f1a0f190506100e0310020d020705160f270218010f0c030504031e12050c06070e10 65
    0x1103081501d06000380741007422115402405603000d0b49004ac084210050120f003040400390700c3c85c50f6030780d4600b402580c0c080c8509903030040040100f04000d00e8540e140700070144c400b80100c0340c0001d089800d1240001940000d860700b01c0280208006022046c81c07600700119040e100d1885400d214420303010300c4615000051005080e43d17880b20510559444200200140602601c0030345450b0340464510002a141c41c102d000c4090345202c0c07807100d14028a4400d0001600d101c645004a00c412074004110811741034141c00b07240c1e921180c01c4900c2c00104015801c000e00545e481e90f06240042c98240300c54444841001c01480a1041c1c0300303010381010480701c00091303182001c1060085611000c07103107013005100c20320014590907481d441c01041072100d0801d07216404040c03c00c600645e000001210014006042004140700140e040e0408110090100d541c5141c1411941e0300c2000d105aa8100301010840c042000700706890200500c0d644a252850641c805042a4010554192461603410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 558189775 1250 558188525 558188551
    0x210320120706020708031806070305010b120703020d0c05271e0105040f081c090513230103030c110f010c02060d110310030c05030601060c2004050a06050108061008 72
    0xc042c8072550b01614081a0003001d041c1ea03030300305420301c04800f042d04062041d0a014050018030030601a200352030480c0e421225103454802151a607140d102c0b402086401415401c1c040c44551100c144100b41829007a5150240c8e2805866802801c1c07841d54845420000180c19a049541d01c072211803000a441080000e1244c0740e103140140e0f9607015a41028031001d5030340320001018036002030106007031225204e461440504038801150303444524040c0f280c0004041034404020102d07a40403036011040c0704e803050400980785a4440384400282d009800048001c007c9505122080b07107686560882180d08205884028002800d0809076900107441075002003403804440c580d9403c5405200e48082510782c1c0c3c1c4c1340120790b480580000780400c0c0c400100d4004045028200050a00d05031121070321040011382c1c05a44000d0349034601c6031159000c1c0350b80b01d8408402e480302e00038240103a00080d07020900c40c1c20f280005007444030081680d0303c55000c40511100058104018980080d0058139035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 558191025 1250 558189775 558189787
    0x312070305040503060403081f05150a0203121602070801060f050d02120601031b05010306080309210712060b040504150e0c03061602060106111c0921032012 69
    0x151400c0c02203902c010b0301400317900c0402c006c255204d101503100340701d240258200314922501194541d0303c14010940c201c03409c12103100110030303424050705580348103104807413030190101041a0b0305c3c0740a5980d00070076030340740404010880d010302025014048072002006036524103107290b5030b200344622503107014078120940e400564464046020740a440207084980a50b50303843d001000404101801d080c609e207086000c039007076100340602c004441c4000c00840c2810481e00c1040702c0420220074051201c01e50b104103d8600710f06214180091046500d1107114140904020b0241e40f02100c0c0a80310f2840c0008100c00602d11281c00c200c210940c090001e20b03d55206850703440c064404a100c0d03410300c1342c6410070508000c1d607041f80404010030b41c00c0c0c40341640c1c1c4600030303039080445105541640d0000806101c0c841c0000c0d10802512400340750924205540346e001c01000c8802c1000f0311031044002481c4018035412042400795826420b040f401d054102c04503640d04c1300b441c076040d008000000102 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 558192275 1250 558191025 558191027
    0x2070b09121e0307030b1f180e011404022b27170c010212010801060914070e19060302030f180c0603040c0e181911010f11070801020a11010b03120703 66
    0x1041c17100c0c0c0b5000e0700c4507101c8001c030f480d504107107e506503c00c4006200f10383c442d020010210032507030480390403043e00302482e403c184001c07810614514400d50001c5d8203110501c001041c90038442c3d510307011458480382c13590302d03070860030185c031442f84922041e90318458030b82d500c46114500c0c40d0051504201c0c0c0c403e0121004968003201d108422502c1029030001c690100425401c0720032504075000400200406550341003031000b81d0302200b8204800034104800151340d640a4404139001c200c00411914450a00c2030b80c003403200559030802d80000350302000301302c1d8000705250140e03084010101188041440301070402e5603071590141c03103406143d020000c5010000300301e070303420064130351a855036840340b504400c4e4100c00c0e003440b241c4c11000d214520047c41c1c000214041d9080540d040100b40e540c88814000644c0d11560452011003004040c81c952003e00c0f40c01d01c2500c0c00b401e08407002507610198400010100044015556001d034507005860407140c0c0c1c001035588403141d903202219120b80c900c3c20 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 558193525 1250 558192275 558192281
    0x120c030c0b010902090a0e070905060d06030203070909050105070908060703090602040b030a14070512160c060e0705030705010207080303040b070903050a050114010902191407050102070b09121e030703 88
    0x740355501d028000b081049064001d40000e240a4910054540c0d9506152492810646001d40442c9007414140454100a0010010b6941200340440c4255581d800301c0e241c4407980c0d101c4c208039aa0707207058008101007170082540100b0b281c6081040d1905040d0082d40f00d10010b00f420003031550b220f401e4401c03c111901500c0007000404007950f00c07072820941c003902404000b841e820b80e100c01d1100041e1028002d6080d50f0b48044200590f602c42d59840001042d424100e4408a082c0b0208440180018256000d0f04111900d0312000c2d00f405482c001c24140f80c204141c200b04d0548d048814180905a8004183c940c09500000c08420f42c1e103a80d641640c403d001c0390406000d40c014810804284101500302c03610020025641e2406a0707a034804000c100c1c01000e0401c2c008988880d000c3c40c503d4803540031010742d407003440070300380c41d00500f6a10142203911002c011110300505004210b13038404244070041034469200301d500e160005801d0f5160110b004c181d5480203084021020640ca04d03c694 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 558194775 1250 558193525 558193547
    0x18010b0313061401030309080706050a300b040b010302070201020a062f1312030512070917010b18130611090406060201052703160813180c0507120c03 66
    0x42c04200c2030a05022801141d0400d010a80100d0140d04001a0035000002c1d842c0c22036402d59a03d6090401c5c011007280e0883d60005071900c3e400e00d200446003081d48402107520b40200407140040d00482d8081408183c0e0b604d0b203c1507061502c180080300150f600424ce889403203a00c002e0000c2c09407020321040310011506108070101c41c10040b003c07041c10702400020406071043d201c566528640e0b0381c91164000f160b40300f0007400201c06201d8469482c2c012280103410070004c2c14054001c5445513180004000f9456840e030b13091b0344400320303181d40d07042c8041000e4030b02d05460000410744c40e0402c00e00814041c074440080899645240c22140b14446600b52075401c10300600921a0503941d080c003d01805095541e409080f50300d0300c4e03e41501400d0019401d1444003032014508083c084251409448800b00c000d81d403028080010301c14a5074011441d10103441c07188002d40d8200d0000d0490b5040390712840c249000d00200f0007101010840d00e0110901c00074031031808a0000e0380500c1c003190484260 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 558196025 1250 558194775 558194783
    0x310030803070f030614132a051809270f010507050a0e090402090a02090d020d061b0912060902060c01050f011401090b090613120803100518010b0313 66
    0x8402d0104240d40103001010552032681e041c0517441d116846980b00381c0c442c252040d4450310561840c03008069540140703600d12440380c0d0342c0582a00c040d03030780e500c10fa0080600500040700003880340e0f00214a5005100d4214042e03512120520300421700c4000e0b07141d003107444038a9500c280c5071000040030030089101c450210400a200c942040400034006402004802011400d05410881d150401441c410310440d0001e00c1104240c0303c90038520006d5000c01070168120314418040c60150311903541010000348a54000503030090003030303003501c0000ba5107046c040410050031800c100001c0c030602c1483d0b210390852400140c5e030104c0d00c0080d01922415042011a5003003800300300c6c04c115144c105038100c54841d20402c0c1610006401100c0603031250003a02c9070703580d090040d4200c905008001e4510401325451454510f500d4846a88001254a00840d5018030010400c031005012140680040c038065801c00084044c000102d41e60300c1050242c0d0042d040003000103541d000240da2100d16481e00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 558197275 1250 558196025 558196027
    0x3011a101110140f09030715020a0e0603010e0a060b040807091806140405010f020903030d05040512030c03010906060e090a050402040f0908070209072a020a2301092903100308 77
    0x4860030703540f220340212080e105452046000414245010085840d415030200000c0c00c1080e1f011002c5000350000c44420080080861030000310740c03a0500118044d040d01d0348410340c1403a180600f038040d40d4282d08916a0317460144000c0080c842d00080c19801d545145501003000005120100c0c2d0322403452401601d02411300c054501c555001141d00303405a1b020744002d200075401500420168443c03d0942074055000704039240711000c540d07001d190130500c518180c50208103c42810b0842e07400941c0d00e1100d461000004001c403a6032446003000810b100d003003c00154034041d002508040d0003c2405504030303198400201155650b6100c54035001d015042040581c6260800102c20f80000354101d004900c17143c0071030f00701401021068800722a50301307151180f04040101170410b8006071422038201c07080a1020035170710b030201c40c16280704540740e900c50035442008000402801450303009101740000b403140200b200a405582e000c588200e100c595503a6110700910081901c40c940c00909000c0c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 558198525 1250 558197275 558197291
    0x30a0207061404030c03090803040f27051609050f060f1e16021e0d021c0b012d0e070c050a0c0b1c020c060f15100e03011a101110 57
    0x45c114120314440c9020b50760301c0118580320860301d035403071059015100096100440801c0f04140780b1802c0040402c3e418070b0616a84070303000124054440070355038640000e02070501d03603200f40d6108207a08000c03c011208401044885004682e0a1107400c0380c8141002000408044880959001c209c095658402c01d81d580c0d9001014006030048615049201d444410410b4041a020050080300860024240001c08109508120b035014580800c04e154207144410030002c100080c4016008107032144bd055220386e1a03060b0785010b0307040e0403013928134642c20a0081c08080d505580e2581c2c441c91a0509e41c1690520742400c9280030300d586030041000783c0700c440c04602118014050310500d22440342c0d9101140c0e8003c0d40000f64000c05001c01410362003000002c5030b0300b031080c1c95903030440305096654090000d028007084041c541400d144d2b0200751022500803550a09108100a0300890705603425411161b800054800441e0440c840802c03a40b0710400085000501078140c0500c04c241040100b40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 558199775 1250 558198525 558198527
    0x20d06050106030b04050408040603091a0a0501050406060f0c021e060f0d1d0c1c05060f0912072001050c1c0e092e0503070b09100311030a020706140403 67
    0x2002d0041100007810482000590b00345401900c2c041c5501104283c00c03d810843d0490040c00340c1d19064520484454010506109003da104d0140803d80400b0903d98103020501027507650a038001000c101880d5002420142d110743c40350b0010703038121442420386200d06254070310100c00d80322143d84880d00041072898105814000c21159070500c00510240a0b07020782c0504c0400a458600354507001090484070501d0f140c2000c0080303d0341d8800b00460401c1035162185000002c80d0b407a08404110b5081c001001c43c1000101d000842c4036407114a0f00545a4450080c00403204028103403d458019102042e80a002650034400c1070104442c81d18003018007812604050307280b260b010444948500d409401d284254a2154a0701d070038040402014404002400d4019014031030900c4040311f01040c20399050000c14001c2a104100a0301c5894106c10400c0c903085048111007410b1820340c0601c00000080306407580240343c1e4a0043e11b540e25030038003038041c04440620321050620181007100701 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 558201025 1250 558199775 558199781
    0x1091a0403050c06030601120e0a080f09040b240d390801030b0711010f0606051e0a08060d05010e1f0c020c09060607030522051002030a080f04050a020d06 68
    0x8900a00c00c0f9404604802d080c02018801a2100c90009001c156503210026068021610500c52202222241c103100d0300e071a6520340007900320404042c8005454250ba15140c040c10b80100350407103113841c0b1207241c0d480100a00c0840000b914140b00d000c83c4070b090a441c0740d800103646c00040ca060408003e0417100065528580d0316505801c03840d800300b01c4642c01e105114590507a9805050103004d921021410b980090203042101d03d01d40d220b84601c1e1014400c0d004010040c582501c41d0707519001c0765100126a40300342880141102800e025021305240c1c42050640c104400355505000c6540d00d04240d405080942100110b41c1b02d0400149008503118078030b80c625401d45c41c01044a5003026030100c1e110380c00c4075411903000040d03902248962030310300010080944281042c40c0703414000d80c1a02d51000e0905540c44400c0a850001c01903801d01381c00018180d503007480070b0341c0707041398010703016005040140401d030040f020781c40002c007084000c012800b02c040d0001c0c811450a1200e00c1c00d503020b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 558202275 1250 558201025 558201029
    0xf0909010203010e0901050c04210f0309050132030c0f0a0c12020607020c100201090b090703060606080c0414040e010504050618010e2512050c010e09070e0d0201091a04 74
    0xc0d030082c3e04c0050b21944062151702d020740214490f0500c0c240c0740500030500c10090500414155078200512400185008000003815200ba10761106452504c000500120100100ba44041c64000c0003e03050680804101c035420000344071103901da84030b48803842014000c421000101c1d00000810243c0c0325000b1301d501c10400d200d0180c040c8501203412040340c031000e080d550040584c3c000b240d0045145451000d03804114a85d05c0000b41107841034440001c120025105000c0a030400c08081c01448200c1c0140b50141c80075050000041c1007460700311144d0720682c4900c1d03410030b00400f05201c50780d03100c2c0c01109141480d00000d1055040505010f610344030252918050800c0d00b1410403189203040c000d07445003510681c040c0c001d80b103d0b10000121107203001108110251038800100d000c2c10303501640360400c0d0280006280444061002401d0306070310000082c4a901620b042100141d4807080e405400c0e030f81070307800d82280045440144c859054581150300740813100d500242ca0595403070080c0003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 558203525 1250 558202275 558202289
    0xc0c03010501051f030b011b1a010602011103070305060f131d1c05092b0605070203040f12020d050d17060a210c0b0a03060305060901050c16020f090901020301 70
    0x40182d0b03030f81040041c00c07411600c4a525580b49065400c0000c0e000b0350041310500f41c1030409001d2080e64000741c08101105807012180c55030790b800c0500007242800103540c003404050008005410107510506094040100b20004040c0c49000044090b01c580121880f50080500701442120183c4180d0300502180031030300c09240143d40c030b6090507420024141415a005100120603e0904a070442d480e6002109a5800c420003044022031840c00c0603d000d40d12131405035004140382c1c6480d00c7d10a5490183c04801154170a20041c404100c0c105100011554001d044000a0302144046001e0b105d0004002d400c0d4043d240d0020400d90b009112a0000b0240c81c4c850740041d5a07502c2003046a40950081410340b1004554182d5244e500400760344c2510700034003400ba540c5030ba406420209500000a180c0040d44684c020000c0000c05c01c10b25401060f210005d00c683d00d46441e00001d01d00402e4805680c08208076003040c1035480e15040040c4011000c0e10151007441d085180b24080e41c0b080c0300e201 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 558204775 1250 558203525 558203531
    0xd050703121e02010605090a090f02060d05061f1e1e050a0207120503030a0504050307050f010c09050111061b090a1509060810030f0201140a0c020901082b030e030c0c0301 75
    0x8002c60f071041c4201420340300010030303011071f60700d80c000f1600c001c00d000c0008507904032a003100c50025035220b90140c030204904005c0401c0d2864204140300c0f21501d2400c00d110405141e40c8050504e41e0842c1400c60300c0b0300299001c403040b000308441140c0400b03810380e40040e240c0314008941001c0364024001d04483c03003240c0807651070541d1032400e038041d00c0803003202514030340061010941e00308881e0805a080307402602160300704105629542d060401c10030640000d07039550072050420a0f0014500c00041c8424201440110b4204032055110200103041194070540205954603000000056465003040a0f040d0003103152580700001100000342c503140d011070085034002884030320840b01107101d240103c1c0121001891943e40080880051b00f00301d052100d80403198001c0d440c2907020380204c6070155601040350000b030041c00b204201c180c005443c160402c00002c0380008031420450401d4082c1c0c011000c0800c0003e80440041c400c545000540303000c0041d488506420020b003c000d0607c04500030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 558206025 1250 558204775 558204827
    0x2b06020a031d1b0109080c06071118010306050a05160309020a0f030b0a060f06020703080901140703030b121902272503020a12050402011404080d1407050c0d05070312 73
    0x541d201c035417921a0950aa000502c411403600b4036102414805100e43d40800340240044002140305d1111001c6203c00d1220000401c01e00a150252030f42000d10a4010401410061712600030807000d82060000e140c1c4594804007192646446940100107004105800646918144842801c217030b424401543c20083c0c0414040da200c403440007162003607002055194a155502e420b03d800080903941400307e0600440d039042c51a80c01044c0c014402d5a00062140301d100c20407106196541c100e03901e5920900c5403241c911500b035640c0641ca50115014120008181102c030128201017514003c01c0090b88140405104040e0407101c2464040004800c801d224890480403401003e051a0008030083c032400c01651490b40700a82080c0189001c220101d8110300745200c1d940503034400203655002c00d06031450503600c032a07401c0204200c0c54180d880c003107680d02c480f651030040992682c03203003040c1543c00b8100312042045d80c0045034800e07814401d041121101a15100e074440100c02c2001c041111 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 558207275 1250 558206025 558206027
    0x2010f0209030706180e10090e07060206150d0203070312020d030b0d121704081c0506060702040b0325030b0601020a1208060f03030c06062b06020a031d1b01 69
    0x1d075448044041c00a10560b494258105c800390b4600e05503040c51008414042000f45840d090203101d0840141e114007840d10b80031010003250040600601035821841e000d02016902044231600030030b5590300710b070640c03c0100c005516460304100096140c4100c040c00000c002c5903606410746282aa020b0f030f070902c000148141d040c0c483d44800198403503a20310102c40003c4903140c0010000c0010b02d40f40c0d042e15074200c452041c0d81c5050300d0540d00c440b40420003080200c0086c4040508c160400c10a014605001001c2046070003031140007031199444145d1840980c40411803241040e1f03240081800115012460f08018110350100b5a101d8000100107140d80d4000a100740c00e183c0d0080b050201e00d042801c044503010006402d069010844081072805030358100040d0042c504440c0140010b03081c0307402000707524010f1046081510381c030345040e2007180b4602061400348035000b01000d42d0340c1100030f104070001c00d1000c0352b4100c80c284405c1d400400500001e140e01610103546e1251084140000c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 558208525 1250 558207275 558207277
    0x15120c1e182b0816060e0f1b090a18020310060f05040e06070c0c08030f030a0e120d0504030203041206140108120405011107080105160305060d0b16090801180302010f02 74
    0x11019682800301e0004900040f40a4020003080344000000b021040c42c641e100003e03624181007056469000c0c031407601c1017403414442003c40011699002d00710184100105140e50402081001642e0b42e6100b0b0156136194241c1000d86958014165501d40d401d40c0c9101c0c0003081c00740920b21b83c150f00c400011420341414468a41883c592000925580c2d80d11041222081c011318030440340c40542040c0040d8441042000d00b90140702003003a9502c91404400000c04c03214070880707900c3c03194000c520b85041640300000700c0b1425100402c020a8951b16800d09a1440c0301d0f950211340d01c0807101c42ea0b0380034441a07030b0101c00c0c254507210407500709076a00ea000c0c030356444030b5417581d5881072001c0000b0402980240260183c10000134207030340075550b580d28220308640c1c00b1903248015440c3c041122248541c036110b401d920010481c0c425080b18066156000c0c0d5010051001000050f440401590300e4003910003a0b008001100084c003135015291217001c1d80e0070065804601540c2801000200306903240 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 558209775 1250 558208525 558208579
    0x6011706060603060603040c0b0a1d031209010f020c150c0c041e230711120c060c0a0c0510020406020c01080105030a06330515120c1e18 60
    0x400d0541103413038001c10080b0a0b80702420482d545941c2e00c10003d800d40307008010b00b00d088015141e00b04540180d40408003c215080c404034400c0d0032040f61000728007483c40540d219040c0031b20f05130101c05034001040e0b2178000030b00d05483d800f11243d1506203540d00243c0c02044a880c01c6825544006910030074441075804420b07c0117681c0246031042a5800b201358808140c1d003800080c0441e8241c020020254551720640c0c900001640c0e1f00c80414500300200925142c07503510844043c43c04c2c003020480d5072103500c064406030700b00d00c0002d8060b18031740c425404000744503002400c0d100c410801803c180d000354880d2040d030700540201c804000541d80038901050407298041c0c0588040c141c1645c4078001411a0003190000111114010421280c00e42682c510b040c0346516402c2c00905003805c004007002084115070380c540082040310003c4615010b543c0d0450405002c1c25110311104c0d1b07000140c48041251901d06800c04030307000141c03210702c0d204005100f4040e50300c42e2009403c081409100c184807 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 558211025 1250 558209775 558209779
    0x7030f23070b2a0c1c0b040b09062202042c15090d090b0c0a0b01180b06090d0f050309030109060506120304080d0c060212010611010b01020304050a12081b0601170606 73
    0x84144e000724140000320741300da1600800019640c100e5035550a01403030b000e40b030683d40c03c165034003004001201001800c0e0011390610241d4600c4400401201031810f00b20300003030007103449034407100340701703401074148042240c2910101c0401925a508a0781d81d129040311207110040d603a000c5414594049212003406070aa92005d60450a145400d00340780d0041c0145d45140c0310301c0c2807001c0498820000d8601825030050400c0130317070308030025860a80b2103284000303115202c10846481c80e035035000210f845440d40029141030309221410441d0031405501e4080c2e03010350801d81d2413400c010140d40a0340c810241203941c0c1d007548540110895480c002e5000b00d031200d5010801400445d405404004c40e45440380e4000340c03810910b501c150424050a911402c0498000484007882400c01c0c01400780d030300030070b10003141030900d410000f5245551364030400c034628110140c41c40034042c14130300725001140011541c40d100b503112040590380354000d1007147c00c18803c2c10796441000101040b060300400c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 558212275 1250 558211025 558211033
    0x10030c0c02040e030405040c050a020105010b040f15021216031b0201080c13120c0306180206030a1d0106030f02091303050f03070c0c2607030f23070b2a 67
    0x38950a0000500e040782c401581803106210000b66035850307000d8942c52502c1a0360320740d01c0b41c0c0384072406403c0d42d20680040b0135030a801d000600691002032889800c44140301c480302c0510b0140d490a034242100c10001c42e50714480002c040d01c520944840c040d1880d4030a941d58110f08007041107000c2080b00e80d58000f0f0003e0071840200383c41000c510f001d801070726030280d0350380c40042c0d46507541e0141c0040c4600890310140c0201081047c03040600c5144006405100581c860b0700c000d90004909200081251400036900c0c0d0f040c200b1001d50206e18025400c0000003006900e8482c24150084240c00008034840d080800c0001e041161600c40b44010366410384610b410940703038640c8001c007a0002015001000090402c410100f50800d5240000307000800021000c1e032000c081d21400208010300200b982d80c803101082000421440c034042c0010780114100c440100c0c8080540c0240011005407109445114004104021201c3c01072054520b000000381035214012401d014000d4420520011504 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 558213525 1250 558212275 558212297
    0x50301150809160e100b030622180b0108061b030f071b0606060e01050c0309130b0a06050c2404111203280801030210030f0f0e0c10030c 60
    0x2004100050300826420243c4400e40c0f0880c2c4074400d580300d00e51194140020501c144894075041c80700352805024041102c0f8698545280860707102814902c3d0100f0a005140c510700b1100e919a1100c13000386132046510581685038140f03110506001c1c020501940510300200381c0f1410707580064080d01c005038036181c0c21035407a400c124459002c020810390a00c0540744400c1c1040c83c0781d01c0c80103a024442c400c0001c00c01d0811170b00074001101400c0150610504001501c60030800009550f600b020456184072a414030300700c0200074240400b89140c00902071800403a5071a0031002400c4015408001c4540d1101701d8903400789031041c1400e80e550340390743d0303107000c9800705112030020114100e02400c010340300218009010304d10351044040c0b04125070319551054980380c400009603020061450a4800307035045400044d1102c00000b030b118141545c3c2d80300005014010340000d4041d1080c0b42e4200604603021070216260050440c102c2d114005c1250303103003001c0e4041d02c03c007200c0016503940c00e50014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 558214775 1250 558213525 558213527
    0x1030501230609060a020d08090309130f0f0c091805100302040e0a0b09010c080105030f060c070f1509020405061e010309060204081209100815040f02090904080306030d05030115 78
    0x1030048449401070000c00c4052500e8440400030210104150700618a400740074100030700221015080c905c27241c00811034221309680340b080401009460720701c00192124103e007a00b0040070503080c0d40d48070500f000b031841102c075005840d55007142c101c000503e0058034401413460848104030b84034100c4000291040c0054141a400b82c00510b603514100c40421009032528100c0c00011100301c442da071744940410101541c400116401804207600800407601c00f0a807441e20340341c000b0283c01040350301245020a200b040c1e5100c0c0001a001141042d10b03070008401c10002e011541c20076030140b81050042905818200400310002c03076102202585600d50800440140507021400c0d41c42c0ba0b0240008203000c102401800c0d9100700441055656040b0f035000c2c01a041e03449c10780003052140f00010442e5800e00d21002a00c1c400c01240d0010b0701d00030600c001c0c4000d004441080d5002407a0358104420050164011030080108504644419100c501d007282e5070b100c00d000307090003205030b0b030303801c6a000d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 558216025 1250 558214775 558214829
    0x10305150901150b04230a030b07020a120302030a0501172d0712030f0f0804081b0105070201050601120606120509030c15040b070c02030c12030c0118020f01030501 72
    0x815024008541c840d0300031841483e22289400c65500044001400c1015a202c07040c1210014940c500d41c00380a400c440010758012a14400644510f030981e0000d070741584280301e00406c55510051030f0300e20511030742c07004001303402c12144280180d01d00000440c0c4030390003800080103901544002c02c0444444001c582d0812500f0020000d101d5a608a10050140c00d10070100a40740500f015804181d05080060003a410180c0300024444100309280326a030348101030307a500c01c3d0828078090340c03445d18a281c40c100130f50f03005c0c00200a51800040c00180b65040d0001d5008602c00d90701e07030f285c1002c0d0381310007012140c451140b50041400b04403c0112202070760007240d03000035004e056900b44019050700c0c90a01c01444440282150104100401c000d40c002d0003680100091074040400c10282e40865a280e0303045034103911030ba01c0b001c9241d10380b00c1c00300111011416154003c2c040e001403c0c8031038030b010304048030491041c0340140003030601c0c0d4401d2080d0350403150126080c0043c0c5c1804180b00102c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 558217275 1250 558216025 558216031
    0xc080703030c022d06070801050a061b0b01080a0b010b1305010c080c0f100e0316030804150c092603030c210c03090c01030b28030f0c0608090601030515 67
    0x80d07028204c1400800000c41000c5030032400382d0700041580c0d2000d104640d0030070000501c0700061168100043c0f045840381270a90040e22032a00308a070a400901090f11610000104001c1000c5201400801e6020000c00d10420300d900c83d0580200c6a40c81c1c0040720301d180071301c8a0304050151200001c10241d031081d99100001800f5001062170400d10044183c1040c0c015042d0106540c403401003040c030041d66101d01448070524001031800c0c41130742880319a0749030b8000c1c00507003080240c002290921243c14242400e1f22070012341082040f0b03480030060007400203841909140f000903040c11084042c003071189014000510040e40c51030307840b690382d601643c004d044443c89030f40c03207045001d00c0c414031080c4c40d0380240020070411741c5030b2070810702e19880d10070308484e061704040c10400488e08075243c0e10b04480c401e481403c0429070641c280c000e007032100c400b2548046c00f000995040002030100c010616000e03542d040e0f40c2c0440550350f10f500c0c940c0d0380c1d02c00e1000401540c444020f82c65000b5a0f20070443d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 558218525 1250 558217275 558217277
    0x20c03062a0f040f0e011502070501030c050d050106020106091d061f081002190c0203060a0f090803150102010501150206070503071413081908030606070204020403150509060105010c080703030c 85
    0x4107044400c441c000c400d400640141c1c9021301182410302681c030484010034010301003448044810111110000e45540861007054141a12945d41403240d41c01001614101c2d1000c030380c01c22140d0395909000340038100714480d501d24107252200154179001008a102e803078081c0e460003008691500b900600031440c5000f064a40b4210066020aa41e0390038480610239924000c00541c990100c10340c00b841c406505244030050020807010304006807030114034194001001e02c070015000e29811070180150200b0380c00100b145c02c000040100c10508524034441040080c0e0082003661b803954541c0c03015544108071600513034801d100154501e4840c4006550200700c6280c040304c00307a1480300071045500418000203070094080310900c6620380c01c0102c18081040d5020000700690b075621500300b144005042ca5000c2c120004404040d504c0710340484000b55444855074401400704166103004100640b040b0049002d6a400082c4540c0307d0414a2110380d0000c034241d1038884150303020381c014201c0e50660f40c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 558219775 1250 558218525 558218527
    0x10b16080313150c1d0102010608030c1f0b03070905061c050f0d140702190e190506040b0f040506040e120c01060801051005010819060f0501020c03062a 67
    0xda51880a0350007a281210750b0b0300c00514500d0801c140a8040280801180ca002e0182c4002daa11855018807084215090380516000b000100e024003041d400c01c2c5005e00c8002490780d5a1035000400d000c800c00d82160301010400d00b811080c05036107100c0c3c6981d5050b40407000070f00000f4210381c0700540000000b04011005400d091540b000c4020502d01078070f075608920450b4000480070700c04001c401c01c1c6803500b031922210248626065020b0680d0203402500d03911004500100788907000d030301510031902488000e00d041c00000303040060f4140400b829608000214a0070709003801100b42c2ca01c001054042000d0b4400140720040c8001803000d50711503120800808001424001410b0b84a82502100c0e5200c50303d190701d90035038600b0351151103940e1600c402c2101d198062070301d04080d110b091900c0200c0361130f41c0c02d2a1b4001c00301320624090b0145401800a0300181e05410202125030a03002d035a20385000404068890a04842c0501c008506a8002440103040c480301c0340c0c4d440b8024080c0d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 558221025 1250 558219775 558219817
    0x6030a0e0607090e090c03120a03020d02040b04051504060f030902030c0d14011808040302040c2a1104020a090e180f060612071a031003020d0c050108060f09010b 71
    0x380c0d00d03151050700c6a03008241c8081003403080a040b9056035038440401d200414001010745e000c20742e00d60594020100c3c1d2030703000c9100e000c0a44a42c04540c45403144940942d04c0b82e8585034004841d41c028454144540e18841d03401120a503004190b40c2190705d9919174149541034603005401521103040c00320f0381070150607814001507441c0071061420f2801040c4040320051001001c80c212081035a00313410030600f214910000590346000c5038266581a00c0100d984500c1034025640810f04c080c038440e4100e80144c010700d44010340e88454481070700491409161110000c2404124483c0288180005a43c141d007030010000c8549880d030051105415002e105c0710b1048034500303010f18004120002c0e00705000340702c035038500411030301030403c1c900005d400030350718004003007038100780261119000e00d10110005000c01c6440c14000f0003141c01528103900c0203050f1810849022590054502044130500030030114140860145c40100014240c090aa42800c2040ba05500b1060f54656403028101030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 558222275 1250 558221025 558221051
    0x6010c08270405150d0807030c0c0b03060a0605090603070c03090b1c0b011e0c0309170f0706110c190f030503130e071d010207080607120b100e06030a 66
    0x40707030038480c034400908203800460300300025140c001e40041590464a00c0da52041c0c1d03101c0c002c2104540c0d201c0022643caa070180b9041c2e800e281e506030040d1140400002c00140b505001006500c510740864032040041e40301c000c141d60310300071391107019084601840020b41460094480351030007030080c100900e40581d6801c0650441c1e002d5040042d0b810b215081c03c1d0b1601c4224021210070002c24200340d494441c0300c0040451100e5004400020060003214500c107160091080001070700a082045035000c01303544080e50388804855082d0600d108000340018a2841042003040b06080e20000d84107414a50040003c1c420107031b1000441c005604000183d00c0b160300c90050000c520800c059520340401d51000c5011401d107078440ca00c000c0c1411704208505a10956901307040171049204465007600000403803520b0705a810000c140d01c100c070244410a80c110b500801c0701a980c400a1001d50b03207850501c10b00c00000c004074004102c2800c0c01c214a840d0007806503500826000c0c0006034000e460b82 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 558223525 1250 558222275 558222307
    0x7120e03011e0b0a090207020f1309060513260a0f110105011205070f050105040e04060f091401060f0b04141c060b09010b030405070b181f020c03070e06010c08 70
    0xc0b00c0241c02e9035400340801d89041c00e00d004030040072140740842c00c10450b030300450a6040418039961040c03028202000307090083d0781c40b03c400240c001034204040c0c50052400d000382c14030814140c6c0c0c90648884812000c0b002e11400040d8050480b0b02c49081179041a004c0d121910700109031000e00412009a0032294002d225190092211031243e03040442070341483c50134424182c000110500702d240c428400359030880c007110308403132000c04412040d6659081000003089402246812039041c6100c8400340140403071214a003102803070003044250364504800c0003504403803007075402c50842408200003100030190120407002c80034090752012003045d1494000c00d10650004c49410703684881424050030814401805048410820b0b4070303506140c4c030f9865440060348100c1c2244c0d440052407040c062000c080030066510082c0c0020f0080c0c1000e00500002c1070340d00c02000040c0308000c20450107250001d0a9030407202d403180c003030025448e030300700446a619240b9020b0340c50030300400c0000c1040c01985 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 558224775 1250 558223525 558223571
    0x3090d0f020106170601052d102a0204050c04080c0402130b070506070e0a06020c04050a020d0911040b0303190806010e0d12030b01090f120c03020406080a0b0603010207120e0301 78
    0x1381c060a0a50305180c10030000301103080e0503009010342d41e405004810284514520b01e144101c1341c02c1000d0611542c125510b0f040c8462580741502855403c16010070700d8561240b50510071582030100c0d40d5a4810401b0700d004030702c11250168058890380585062590003010062302c1c1e16400307500640c8960300d0120131b83c0800c1040350194040001c204000317a000ca01a401c0800031075903200401e24161002b13584900460b0004d10917962480414a0000541e04403000324074181d605020201003801e01d07030340c24900240d1260080b410a80004418500032045651070760150300c03d4000f907204424216140c0c1002080390b81844401c0380c06070b0317299072150701300d608091150346102c40b02d8a0b030309001801d03950903c5261b070602808010500440b641c51111405490004201c81122055402c1c41c0700900309551020790800d02d0a14003049400c404035121000c68013858034100e0980b20202494201d204084014000004a864a60b2840d02c00c8a00050100c2c1c014000b181c0c0b81e0b040080c41c1315000000f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 558226025 1250 558224775 558224819
    0x31b131502030a1b02090a0e1015030204050604061d0705040b120103060c080c03070e0d140a1704030f1101050903010e0c120604050d050739080303090d0f020106 71
    0x42903915103ea4040c0807a9000ea4021481c00308245042e404219840c4018043d4100142c45030b034041500c1c10200f049030345007001d42070700380448600c0f0504e94105900a0000f64081c03800c000c00030b00241070074001d20007141c5005c00080c07a44100354000400907030018020740c0c20090b08000c00a480310703d4101a05440b10030601c907040d2549507207041e2080355110917003c800e005140081048400c7c540d000d60b5804401ca0034404540c54601000441c0c10781808001054a88508210a25108000b03508500c0390300c120404818490010035a5071103004034403008190940382880c603c00590355003503101c40103a041c10403a0030700b65000e001034251000007011200c55030200200f0784072454031101e150744100030038014026504141d11341a803203402c154440c00030f211380011442d08019084a8134022000d08007000c414041d04c04d03c006062000c040928101601900f0300420080c2010084034000c100d914020b000044018400769080102403c0c0c03941075540c0d8582c0064499900c0106100e80441 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 558227275 1250 558226025 558226027
    0x11090402070c181d0619020d110c010e0d050c071a0d1838070e090903040f05120c0409020a0b0403030e10080f0106080910020d0b1302031b13150203 65
    0x302c14425100c2c121855403944117a02001c280820092100c00d585214004a040540c3d070701d0a248610014100140320600102000587e11500c01e0040d4880e91300c6007545026220b66170481c500c03c890a0081d1407500d00b040d0070a4008016850300702c0e004d460200c21944000d414100c038035802000315205a01020301504641d440703141088002e410521411400103524441d850102207110710841c4400c84007101c018291000c40e0406020702e20000c00e0090080c084c0100b880c0441020b81c80e50014810061200c0e151540400c1500d41004d40d84514240180100403d104907001c00014080200c4241c0c7c00c01034103000800c14251800052002d14000c0e00c40021009189080c80400248101c11508002411040c001d01c014540b40740d604541251030100d559494904c50241426040280c541c80144001804803401d8115001305150010032a2601c0071908102c1c0701c2c0040c0e02c8100c03848024080c42c600024032a40361300c401b60035002c910110b644891303602c1e500c0d082d1400780010320700c00150340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 558228525 1250 558227275 558227291
    0x71d12010c1403010612110f191e1e0e2106370e03030a052d130809030a03020a1704050a050111030c071806080111090402070c18 57
    0x504403000304400346002241e0303441c3d5031500e04010038002e00d11840100180e01c0c0c05035070101c903201105846001091041050341e8000d041025452030b240100307064041409805a845211729051107510010320365203c541150320240341a0191986044440c024021409848442612214907024100000c0910107242c07080703529145290160042ca402090310404d085604070421941106c2030034007170300d4610b4070b030000d0001c0994040c04480004010921020007006070010081d0025801100412483d580c64903002300d030002c0c800d21141d0b9440d103155014000c0740d582580e800900e26024000d480807030a00c460710380000d09041c070280d000e42c010707030200711000c05102e400a212010885d13220005840e00b407525000c41c81c91841445a40c0c1801070207441c0313054400307052049441c03240400c0203035a8495141c1c0601e50541203011010401589021f1000c580c40805126034000030b540c02c00a035081c6400401040065400184202c035412410103001905203000d2a907000203a6000002040e528 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 558229775 1250 558228525 558228527
    0x20a12020f0106090e030f07230601030c091517030c061e13050a02130209130507080601090e04110d0b09010e0114041a0402040b061b15010b03071d12010c 68
    0xe81681c01c0f0810107031524405d056030070300000c212041c901101d6106510f4028905140790101c03580c80c10b0440c4041d1100350010380c4800440c05034162849402c0340170300c0588a0819008554000503070341c88006072080b00740401040392500900000c6000c044074540185003061a04080c400c0c3d400c001c00603004001c240b00203102484056004250804c1260010b48540750b040e9101350005019008004506100850108a8046840c03a140141c00601c2d074400c0b614807c8010703e01101c0c9a00001c4004010134030325807169144a04441001c1060a22a1180c4c0c0307407966416170101141d68003040121501000584031600184a81448000041d034040b00c00001400d40d24031400103001a00d501d001c101c0000c03402e400388520b60580c81526840380d41c0c0c07032011074000c00d548200141d02030808035003c07040070b0300301401e00440030014040e128102c603500701014020000b0700034071f03084c100c00b4070000b983c141c8680003005030718181844a601850060020444900c0342803401285a5100c10004401d9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 558231025 1250 558229775 558229781
    0x10f0b040c05190806060702120d020c0108060a03060b030102091903050f010908040e18030c0c13060605031b130b04030b0709060f030c02070e0f090609070e0610020a12020f01 77
    0x2180900340140f034607003860403848607034004001c82d1041c40002c401240b1aa143d072003d0319019a4050040c01138003000041d40c0f680c410614000c94014481c0305030b581310039441805081d01507540500781080c10b0742540e035120042c1490031200e6030559803e0140c01c007159222214003004902c80b041001c01141541030140c01d000368903040c140d1a038103180c0003900003405681280c0444014002da0811901c4840d00404120f86141d90561244000b141e0074200e0b84002c0b8000da0350f4102100c01c030400c0f4921007404000d4030014810100170500074800141000c668051154511007800c40452a00d000700c83c01c4804081030750860180c0001c041740600c1080041640300750040d0b03603410a105a00e15050000b054400c00340204001c01d0f4442d00034078030300340c02044202d02404810708118081c2c40c10084040d50010115542e1200740b1030000420750b1a4000b29141003650400c100110f100c1d61020280152071424030740280c1140724004080f40851002442c918000d00190302403d100c4188401241c25 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 558232275 1250 558231025 558231041
    0x81c200703081e0a0902120d031506230702061207080403110606100f0c0b1303020106050d0f0305091f02010c080106110c040f1d010605010314010513050c0408010f0b04 74
    0x5019011001c035881c056103a55500d43c04260840086172a5a07640b010031a210300040158840f031152401a880d10741c0c05030408442e2014941c0d415402903980c4074100c43da2203501c0245008400145a103140c0d121138000204000d0340082c0040d8a13000e10319003882c807000822203a25000400c03103401d0008050380103065044518510700201000c1c01d126000400120711703e030005061064840400440d180a000600621038000303900b400203280c031a126030744501c1d01500c221f0065280c00d101080916265408020303030ba8000d070301c24011004541c1e05880715402403070220343c000902610305402c4c41e004074042101c01c00c10780c0007003402818000082d04c040810f8002c0c205200203440100785003040007a400710b4101c4102c50200b4001034003050207008140c10002c1032161000c44070142808001500300c103040301d070b0a903804c000f05180d001103860751240a000b819444010320480c051a901540c00c50b54014a00c440450f141a59801515084540ba00355002c1039503103400403440d4505e440d22278210 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 558233525 1250 558232275 558232291
    0xa06020c010f0305011520010f14010b0a021507050d051513020406052a0601030b04031e0c0f0c1e03060b09090303040210020f060a1b0309081c20070308 67
    0x100650408001080a01c2c0c128100d00802c0800f900c2da54000d903c22080d40741844000b00200101e1081420301005440c80ac44c002d40009144400051080031080840705402e9031540917007031005000c8000300e0002c0300540034404106040c400e84000d0710151140c09d0240c60000c0f00d118940c4551814417010641c44828848400d00c14001000304942210840390345a12502245840300c41c1c02c41d200300c0b44000d186034801680b01e0710002104115280003d90701440c040e4071201651590020140d80010000362031100007110091204000740451005691480c4070744005809680c44607210601e00e01c0302001c000c071071400d440302001448a14400e88801148c00d0b0340c61000c41c54510b0f80c1d15038a10000d0030003030044100d040d203910748601c20700650550825038402c0c0e0300142400600300d000b43c40002542d003182102c0c07404074610076019118075540c16512890050a0254402c070030b040e8856020182c0d600c0d6601c69000c2004201410101403c1e20b031500f9219441d0042c0b070900410032500141206 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 558234775 1250 558233525 558233531
    0x607050307180b040b070c03050a03030c0216120314191d060408061302030307060f1b1b02091e01030c0e101206020d0b060a02250515180a06020c010f03 67
    0xb2107010f0f03180d012281130351403030004195210310910b414007000ca030b144c2c0085c015020700104c00c000c0503810b801103054218164200c44200c40c80f8108000200d005102d05d034020202c118008002900a5948070010b180490b0303800e041040c0a9071504400404d1400000064070000400b00b081e88918014800d04170306840f0f050509040c4100142e40d800c3c0a0b1004020050405a01007103680070412101c0050b4440001c0c424514652003007800307071072440a412420307001d000c0c086c6500c510500c1c40300c0700c1410582051000018540900070768410182030020500c0c04203c048403110802c01c60300b80210703c100800c00000345080030b5a52003801c043c2600d00e2080d01c1c001c3c01c010700304100c801201c0850b004440180e070307218801c203100014440c510b0516080040880d0307144425030041007150002034030004c000704403c2000e200c0c030584a4035000702a400f21800c03440100d6110408058280c001281002c01901841c050004802d00b905500242c010381c0010420001c1c1e5a10840c07110900300c3c241028 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 558236025 1250 558234775 558234779
    0x70b0414040e031603030f050a090f170903011a0301060807080d030b0f0a03150e0f032a0a0b040c090203011220060c0c01030e031216020f060705030718 67
    0x11000351066418a44910b4541000e010064010310403669101c0078450341a50180303051a024000e000c20345648041945024005850512a03020b400341c0700707a021407074115011090380c0d8002d0907003045e082160303880b07024080d1100c252000d1150711010806030040c4840700c40070710201829103915070490410350304019410842442c0c00105036501220508011841c2001040072034201944c00f03460990100d50381400206020204011205803002c884007408900848000a50f4600005000603115842003000c840c8800c0540410780728413000140a0710280c1311409075034035040c00b0320b40179145182050140000c00070356840d080700030660307910b040d42950324000c04603c0302142d010003d025400501c43c100e03202c1c006080211010000240025102c0702140011035544d42c1c10030106000c207141a10b12698502c00005442c5074008510741080300d0ba8a0142c40200300341d40d0a408800d5100701101c1d904400001d000151103410a03598280c0c4903e0500d0f00280541003020f020f0710081c100d8082 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 558237275 1250 558236025 558236039
    0xc0705090a061401050a2105090d0305010b1b12030702010203100608040c0510180b0408010c051206062109060402090105010c0308160203210a05060105180f0d020303120702070b04 79
    0x1440084102400c155441b00101130f015152081009800711a02d8004c1da07509049100c5035000d14001ca003100c040701c6c0401807102c4103404941081c001c41080316005c1c800314100206007008401d000002c0019030754249409021100c15410588281c030150b5008010001c00b00b80c103000e600010506807034180f5180c1070540314011000d01e103000e11401402c0d17039400c2407030103405145031015103005005c1022140b5510070900e0059001409031420315400c04140000d2203201d2801d541c07907110004800d42160300c2e09400c018140e031015005074001c10307040041c00e2260f805c4a5002e441150208090700b500d1800e81304000d254281600102e0500c500d0a48000201e0390240c48243c4c00810491003c4800c0080c1006a21f14043c82c1c607102102d80000385140c1041c240ba20320340740112102c9a05025945820005485a00a0041c0840c051001085000291901c14282d6070f124101600003a00c20300030780c003c2411035100b00303421702a50703a4100912480680c100b20f42c000030721204d03403118201410101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 558238525 1250 558237275 558237299
    0x1050f1c030e18040f03031a010504090e010e030406090510030911010f1b050709050f130809040b040e06190e03070605100e241c02060d0f020c0705090a06 68
    0x5005810820750101d10242c5860f500c6031214064000c94800700546414a020307105030500c4502240020300308140110101414840d01e07040010585525080c541080024402046600c594100311340d2240c40075143c1a0782800200f018100c1640d5001d01c3ca8104030900c066150042c0c240410985000800720205050038211411603009103005a440e03140080c040b26403000200d02001e21a100903a54410418000340c3c0100301d074000641172180d41c1d559021507210030390440e01451288132a20507480021105401025020401080000c0b4601c490b00030800f2241e5088030740700503500034004e003d00e82e403038200c0781e40c40080d178a0410f0058400d0001e0003a00e901442070014143c030340340e402203903d00b45010800d0002c1d20201c0110041c501d440c00540040c441141e098803a12805101e0000301c5083c01044102101004090840c2001003030b400e100603540031102406405540c2c00d42e00c080c1d08070500040418000b000002c05c6194109810086203100183c40040034500c4c0030010040380808407 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 558239775 1250 558238525 558238579
    0x4030e01090b0a052209020c0f06070503070c08040b0d0e06060d0c180e0607021e0d0c110607140d0219120804021c0f0b13031d06160b01050f 62
    0x129009403140359036801017640001481349220034088000e070124070003c0c039501824003403594404444a03038900941c03868403101c040e6490400030f18108009684180907010001019109076000d82c6840ea0b1010504203903040320520312041604c13881c40a034514400c10003d504103004039a0701801c5078107070382d40011070703502403049036510f82d546c0c2c02c0d03400300c20b51552040d100c404403a000d41c3e1452a01c2240251070f0380345400071503014030004420507040400013686842000c41c40e141c0710001242511035104680210711981d62104041260b5400604980e03441d080003484540100070503006514064100001030241e1201c50380b9400080700401d9008065401e401501e0400c1c50301922180041108902d40803c8201d0801001110380d007001507004003002100c4c000c0c0415510390b00c41c030b182c078801d40381c0c0460003800060011841904500781c04400d4441800c00500701442c1003400f1401e01410401101c081c0c811240704001005581000300107100c14820440d0180714100d442e02141c075514880c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 558241025 1250 558239775 558239777
    0x804031710060e150f03011e0305031204060b060a02010e100c0203040509310203060c030f06091f0303020715020705030601090c0c02041d010f021e1e030f04030e01090b0a 75
    0x15050140658940741d12101424090130f002c65580c40781d00c2c494010552082c07096200425404854210001190202d6001e0b254088091440c0140c843c104081007100500152034580c4c1c0d60078843c04642e9460020014400990000319100380300c0320300c041c00c00c1c80d500110100d450400c1c503c011080d03804805c9809613070007200d2001090b1980034080084000d84c0c50702d40000c0c4408010840c2039002e804201800707610881c125503280e640c00707148680e00d000c1907030003a40e40107810002c203034980f030302d4600591300a00c1d4002c040454101208a0448034000c1e074025005070304420010321103459a0f6410420004540c00200700451601c00480c0d602d4034144503103401c181d0b580440d042c00c5441503031020b02080c5c00170410b0088034004142c000000980f4010801903600c0c0500c41518000d0718000e9452184d92402418402180d070030b0b64805603400140b103400b00c6042e10342c0c843c0c0c2103501c00002d940a00013503448808286414078000d0441c1482d812a9410f01c80d82e211704021040e40403084502e0030500f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 558242275 1250 558241025 558241037
    0xa0c0606210212120f040e090a021804050c10030608010e121219020a0509010206070305160e0105131403060f0f220204060326090f0f0619080403171006 67
    0x1454500380c04c040301e44042552101001a5452a41c4c181402030010b03208100ca111090ba12032070201580c0b460304501c000e40107450403242c4054104030400075540507005d0001d603171600c0e001d400007517103503540c0c440480007099480d070051084503c00d100d06008250682e00510306204152000326007030142511822000c00d001c0006040303400c2c800815400c0c402c45090554032001c0e81e00000d170071a0001542075005109800000d00424442c0c01218012450706045c15182c1607250421a0b00401710b641a07410305c101004161503540782c280300c250082c05c0e4036585590703a0b1000020141440e00c0640f079864500394910500c003070409113864040d00f0100400d0082c0710940450f044d404006c0300c0000195009240140c0001440511500c080311100502e50b60a05050502c030f6042d654011284600c0d001a040c892a00d02030a168010a0040d400240840d00b88400841d40d81c04548070320888000080194040c0001c05803c1002542c945110313450394521440c0000d410080310207144200300030049 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 558243525 1250 558242275 558242299
    0x3060c090315040c0e0601020c130c05210117030c0c040c090e1f050a1a0a03020c10020c100c211b02060115050304080307031a060a0c06062102 63
    0x90100a000c000302c020000c107840625050074004d0080000340f08007030340c9000841c0007a0302980f002c1000c005c3e00380000d00300c981c5a003076649400000c000014048092220400c040102c0001c00309030458103581d020340010440d8100841300280002010084515600c10702c2034482d07000300032500ca1550740080c2c0300001d40d415100c07801c5813404096800300c502c00c90507200707200381d051b20307101d00401518049100e0a101c1c3d80d40e1f0207111074014988141083d10a00036026501c07007144400501030b44030710740f802504151840b401c640c03c1030910b142da101c0072980010600d145501c2485441f5510717110720020800d060480f0000350402880c241e000348040c0300300904840306c0151b68468200580543c4081509044c41c1401070340d142001e010f000c0c400c000512252400611800c00ca078400c41c0e02104a41c11500ca6020903405428207591220307003812011404034503502e8040140206141d165140482c0f10303024102001114001e400500c080d0034101030b216030702030040281d5842d80d58103803080304582c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 558244775 1250 558243525 558243529
    0xc08360f0d1509151a01020f031c0b04020c060118060e06270106020d0206090d09150e062a010b01020601140a050415180501060f0f05090301111c0203040203060c09 72
    0x18043ca4010025002c01024100c010703400da00010301d48011200c10515000c07034070300582c0c0e60342c03403080c02002c01d90080000c034040001c0035403000d055820110b0081070f4800801c3c0041c0a0b600310240303c02c900d0f440b407401001404818004d41303102c1c2c16101c40400c82c0c1d0341880d44207609444010046c6000360f04083d014110114803102d01e0360300f107c0d0441c0d208241d503111200203480e810444002c1c0e0051041901041d0402008a40d60400040b0b0307840c1c0d0400140343c01d00c0c0c0c2c0d4440908014060a00012a800e5007541d01c80d2001013002c180c0c03400c2000c420040980e04801c400c0d0f098000320050b03a141980c8146241d070000341c00c9055903034081200c0452460140050410242341c0c0103e40c0060a18414140c04000c46840009440c0003200c94000e000102d4040800c0300c800b4030035400007034203490100c0c8046000f01e10640358104c26203000ba14100c1400b01181c2500c15102c40c805040c1c100003160460418042c005066080c5500002d524604040d00001d80e103120250480c424000c00141c0c980586d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 558246025 1250 558244775 558244781
    0x1e07050c090c0901030c1805010e12012a020a030f1409040f0204050103141015111b0301060812040306021308100f27030c08360f0d15 59
    0x3004008108448500e84642c0800c01504000403032400f00307080c0050724555502030b40410030700701c0340c0c0c0c000b1a00241c6014011140c90004000c1150000c1680c0d49032400c4c010280076803400454013160715003041168403619800ca4081819500464010846400000740d01411071060b80c502841d026a40b030301d994000700c42d03503c42d6004c0700303a0140c9481228a0386100b543c028008680302624200400130702c140a40c10314000854204040c03140030070092004403c004a0b828203101c980c60145405203590a400f883d115400c1c6050301c0724031440010801e549000d02511010340a07070006010594120a140070b002e0213180001024070b6008551084440d031050810b01c020603583d030403203103841c441c150980010a12821800045414240d1a0180e448804040c1107055008150080c40e0500342d1001c48040c89800c5d8225010041000081188154484004c000500f0300034515185c41030303241c51005000081046601840c1100d42303442059480c07132b42d0784140f02d81000c43c52141c410b82d90305410003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 558247275 1250 558246025 558246043
    0x403021c051b0a06050a20031302040603050114091c050f070204180c09020301030206040e0601020a0b0718090e0a030c06060515040e28091704291e0705 67
    0x342c01800c00829038001070000f00710070004c0c0101c900b0003d50b02c641401d04140d40840100b48113411202c2d103080810880940116408400307001c6c01c00881504c2d50014083d035100b0362041d1002da4444817815000088203c0c9660411714913402084891184081c41c2c1c0700b81c00c0480180d00307210300440c1070340d04440000120744c80c9a500400030070184111070445142c000050005903918030000b040030a0350280c92007124140ea80041070701d4140751030103440e515154401410705045005d04600c0f4400203100c42d15090040e19949c843c401440c280c141c1211a986107070f0f01010b111400c2c585d20002d6078a02141c042d40b901c0d01860907010610711030034404090b00c46c0350300080d0802c05c000100780b18801e00001500588001a280752110344139078080044600e0b8110ba400c00348198800103400f101075560101301c2e0240b1421000c8a8503c0c050101c2c03805400c194080c80e9105280b50601c43ca00702c00361100d549240e050441542072203480104d900400303081031461400504000352817000e11000b0446594 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 558248525 1250 558247275 558247297
    0x306071b020f100206070210090203030306060307030e010606050c0c0f0a05060c0f160906090213140d020a170706020d0c03051b0109050a020f0315060d02060c101b080403021c05 78
    0x540c003590345002903941c5c40489964006008000c554003642a01c2e00520030002d030000e006605544070842048081e90000d010201803554901d07031644c4103802801400e008015607110700f13480e1045890824246101c210400303218047c0c0701c09000e0035a59403409601640c0c81604c6898550603101900d81c5480308028420910b0301c550340d02c0c20b40d12802d840305402030b5900c00005004803903079440204284d015a10280501940c2c009003800030503258800940350b280c0041140083c0348217a000319511001a4000c40c42c10f410071040d400c1c95010401000000f81070034801400203030306012004103248290540101000030004079945641c0f162600c1492085605008010000c83c52a1060741e0b80c040d240f04070301170051402241c0c0c06107400725909060f80100e0001540c1641c9240c01c000c4808080d050403a0311030410701191301030901c200700c28482c0786108440056624102240403500307041c000c004a04215110b02004006540807840880002c02d0301c0100202c405000c4060b2404c2c050307080315032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 558249775 1250 558248525 558248539
    0x1309030203120f0415091a1b040b03012103021507020102130b090406171b030a0602040608150f0609040504230d1103160f030e04090b06010e0306071b020f 68
    0x704600340d40c403440f2405244905015044101c412140c5020760f0501103000d80851990082d00c134403210075420440d80040c000c10341a40c2412100038083d050340054000d00d9044102000620078480c4c07140c41c04100c1002040250000b854542e0000d68501c03510304505440c151410100d445607000750140c5801181d601c00d948000c2d902c1c2c07050842c1540045c1000d40c4035508165000803000a404400c1d506200420301404c020050241844e61030f40e80420041c1d0184a22484100400c1c41c030b1000d8405481c042c0d80700d111604001c0c101100c40c140490300c9501c50400d004060306141d4841048031407181040e18007051956490420b020080352240d81d0382440c00210322640f8a01c3e20200341e0311805051601e0b00e03a814040d0461141e03617802100005c1294244125100d00811181c4c888900a28031034a0000500200100810107964a00e0310840d440c0720b0b080c2c140601981c01555018025409400a2605151010005242c0c40e15403219178040e90b82441d1000540d181c840144c031040340064a11 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 558251025 1250 558249775 558249781
    0x803040b04030f0c0b070f02150106081008030301050105090f18010b090a08060603300c0109060e0a02010816020102160807060c08010f0b250c08100b130903020312 72
    0x1803500414100d40840000d500300500c80c10050141981c4d01c4000c0d002200799103240c0e078822090340c01d0391280811406521810098011020380d1181c002d02900b69642c4e81411800e06501e50800803030990000300c207030b130400d100610040e43e100d42a0f0301c1109040310030420311840c80703000c0341041c158640c0540781b52000d10004203003038201c0401800c0450043d50080d01c40d542e9441025251081950b2072581a04460110102e20502c800443c4070303401c000510f620a1210611150403552050051030201c1e51520516400e20000344200414410890045c00c44813200350700003480401c0c014a41000c5005506c08080c8603032003507050300c80054003108400c0c0b1040d46810800015049207204907040360070619804800c910480f0214100c40805941e2408182085174450481d00031807040481c0c1070807a07603103158404507285029840c0303004040360548070f0308000000c1d0030042540c5804042d45d08140000959480f000d510500d060403405c0c0001c0c8441462a08030700703603c110018036856104031018 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 558252275 1250 558251025 558251033
    0x15063004080909190504030e01111504060f062301080a0b090412120204060503090d03060b030c030919080c060a0507051c060b1201090f05070e1e0402030106031410120f0f080304 78
    0x580c0c0c141882601c81c0850000011004d641d41c0301d010300400f40d601c508bc1e01003000110250002c509450410101140944d2990180c0012400c03402c01407819004a400e4411296080707941c02e50807404d005000d0051200002c0447e448000c0540002c100740705441d016010b042c4914850749000b140c182d8203660b62039866a0040c00c5c0d800669400745980900804070607003034045d1050000311030000701c4040c00e517580d80c2a0320720300e600024044030481c010040288102103802c64990078051107a0b00140e10350f070078910101d240c400003d050180c0d8928040070300400a0f048000c7e982407992007080b90b0403a800640200707015255580c0000c0c44041d000c83e900750107094031030b140c42c141e68020900b04640c402058981058600030307034098000c0b590251300c00345113040941c4074600c2d450314220409020400400480d08a900980c03240000035503600e00002c0b04040d01400c0e5410064000381c03c1c140302c0c14400003940c007a900340030042111045078000c1c4200280f61504412450704040c1c032a880385840c0c10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 558253525 1250 558252275 558252287
    0x3100f06020f0c030601211109040321050601050d1d030307030c1e0903020609040209090403020601090b0102030301050a060e1504030b0a0b190e1506300408090919050403 75
    0x10042681c01800d107051a10304000a05c0c034121804c0389082c1c1098164015030802d0400a2030090f00d2047c1d405110003802d4440010144c0107501c00c1e52580c49090704200e441c45958a076001400e0207038180014820a80e03400000e5400d004a030450015001c00d4a502440d100c0140100142ca280000720800180b5605540201e40c001099107c01030900507401644105c880b000c40308902090300301c40c0502c05401d28101803c02c1c800b001c0e0005207041d6030700001600d8540200c40850040c5e100c00018000340d105130050040c2801c007030006500710b505207030001d00d22011700c0c0284002c200c09408500840d17900c2c2e803045505486d100c122295103580f60305000c4c101002c122002905181442d0001e001070420301a40700c0d64002c8400d0342c1d035645041003407908202c0005007440003082580c0b1224041a0740d0f030030080c40503101c0d14500010401d010804001010740054414880c9000b6904001c081420107003243d000240c01c0b9940c4141c2d5841ea00a200c8002c203288401060740e150408000406030401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 558254775 1250 558253525 558253543
    0x712060501080607140a12020d05090d020109050613110607050a03080609160c1502040b030103020f090c030a09080403150f061406070605061807020d08101a03100f0602 74
    0x16000d01007a0b880340c081c0c40da6480103582000c00590500d02d40e0f4420042c100140c9003581c8540f03040300841c03c020f0204c6040e83c0010b002e45030036a50b11814081420800c02810150f903c4a00080c0180c9030304e07071165512940c009001d01d0082104103412010491000d13504000f80c0c400602e00e50710345500742000707542c401117106c080b00800c40401c046400e510b00008000d2080c01c0c50301d120510245001011980c4071a200303070403034968824040a8403422558000b910142c00ba800f02103880798514010880d810507811041030180f00c0b2041805000c0c501c10b801c9941c00503000c4000308000c8920b1401d10b5180c8110352018002030101e241c018803107081a00b1034050750070000b900b8002603488005c11030f5241c0110600f84d40c030400400c002000580f0310740205070b01c40030060030b0502c100c00040e00000b4240c41154600016005100c400c50020b402441e4a9004501815070251031420f050410a051034540c032400b0300300f84084000341d010713008041084050103800002005140d40c5150283d50703940340b1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 558256025 1250 558254775 558254783
    0x50a0912020f060708190c02070e0c07031b020607080f04180903180b0a030e10091202061302060405040b040e070e090d081b0319060b1312050d050c0c030712 69
    0x80020a60462050320a03034001c40c41119422552010300003106e004100b81e9148900354003c100d000940c094408008912a003644121a41d03038615510300180061f010a201d40e840308100c0c001d520140e101c482c20b80d40d0b02ca500c60038080d5521022080e9540034000c640c4916202030459800c20914081d68000b010700c1d80c881d4403000000c1140c6022158000b40390702800c088140103020300032455102c1d03000103400d02d0285042d100f0360812241c120050701c0e00c00000b590f540c640c58000d031a14075410000c540e0700802e007101c0142c6c0320400b540000c055106605c82e981c8a291a40342e400610f80d51588154030111908003103400c4160748540307034594a803040707804410380d00031401181c0201c0d009001c42842502c0b02c0c00c0c001d21304190445038508580015010150040e6040c100d0400300c5400e12a40010701010702040f6200d98004080d052032001c0e86c0c01c110309000450095800040c1e0001d600040b6000d82d0415070340b5118100c42483c502580c8207141035240c410300e04001841d00c501080120780a000e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 558257275 1250 558256025 558256033
    0x6091103151825020a02180a0603050303040501060311090712090204061205060a061508040204090807080d05010510050901020319030f2f0901020604081c02030c0d0b030d0c0204050a0912020f 84
    0x801c05042c1d80f1748080c01c4019421080401543c144021003501d00d542c485141500001c00c5520303034a8841c0343d50000c46040301c00c0c0e95520f000b802403103220f840aa5445000300c9a00e62030380341503000105004c9128402081003a202c1e04003c04550701c03a00304801800c0d051102c9420f0108a081055032100c6c283c8030100058a03010012440d40da1618200041c944a9100d04143d601d0320f03400d2100a1440340c03402e4842c06010f0000400155040005050702c0d291130f0008070387c55041208000a40540f0715801080c40001c11800c080c50745c0100681d50a2001403407814a207403a24070060340038001c20350803204000d24052004c02c00b80c0c41c039000d81c200b000c5900880c00580e0400c04419625120303048007140941d10500c002000030300c0745001060601c0c060b110300301020107044141c6040e45c206403242e204070080422140550400b41c403410f504060704500401c52850f070b00002402c9080151000b0713000359210306c0000c2c9101e40340c0d0460542981d00000c5031440c00140800291100100701502d20640a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 558258525 1250 558257275 558257341
    0x60109060f142a0316080315090c0c01062c0a110c0307230606060a0c0b130b071d040b0a0e0a02040e0108070503033f0a060911031518 59
    0xf001042d504507103d080491300c07101e056a1100d110303c2d0401000300d4141d8454280444240c0c50704511035028002403003a2940b264104203515081d1a001d82080e10b8003641911845881c00d89615508000d44089000d1400750312042400300180c000c55940d030000071400100c0055200300000200451401004840010701049071f40c0300c0d64a560050400c49684103201141a62901314000d01c503041c41e03424406000782042e0b50b10681508101e13520740000c1c250900071828802001d0b0a2940804585004108410022003502600e080050041d020325584d2007501d010f6158a54030b003019002c22092620385240c911011000780d030086c0901242200b540e4000910130b007000400d02c0c141d9400401071414502d03001290110311442681400c402031100d42e1410904011000c400704003503006603000e09500e80000701c00c081e02c015900c000d400625020265141801403c140ca0f0020f07142d41180400100d40800a41e02c129130715085041000000d0910107107440801c00e400c01c03c051100b2006c1281 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 558259775 1250 558258525 558258607
    0x30518030307080a05091309060515031c0e010905030f03091216030b04060b040e061b04060c0b18060f060f0f010f0e040204091404020a0e060109060f14 67
    0x2c0540c4500518011040c00b0b5940d040c3c0c010000b80c03801034406020324101101c4980d4030740950302400b02c1035840c1955001404200c1035031001d0380062100a6008014010b000051007015601d0428418100b0149103802c5c88540c0c0b00e901c4100092000a084803035480d03503e501d50741c40e0751000700481d114071040c0004100362500031034064401e0080700070300c4204514580b110324454900030300454181c0d13a540607245a90f40c492042e900d86030b500c58014159440d00d0035400312103481c103c030200070020051108019095001c001c2004290340701e071481081c1e0b110f0b1900101104100118000d80e030054401300048020600380c0944622411603540051101c500240b085a03c0c090a0079400501c2000c0b001001c0e40c000c01c03c140b000100940300528003a40d0354074400403605480706c001042403514042c40300758036054805001030b19850b440f61030079051050001c0d00c824240e21501d414851004e880004003030181c40c04000e011407691650b0340e10700d401c42e8130660714100304a50b02003403800c1501e00c240903 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 558261025 1250 558259775 558259777
    0x210e0d0906020a060e0c12060709050603060f0d0807121d191412030c0c04061d040210020a17030f0f091b03160b040812120a05040501180305180303 65
    0x4030a0740d0040c00300c040032a122280034100800c0454010b1194042815654484618416104c186080a41241d0038003800040c80c401c140d074032143c40380005001344100e60703485241d06244000d0458000300c580d991341c940309005009140020340b141011050540c010781c0c00860741600034414031500c8004801c00003c026034514420140c41e442d401c006010b2006415501c29009404002400482d800041d064000d2231039001d03408014994000030b00c8000e00d8201405820301800d4614603c0b00010343c06106441c00000007400603100e800b0921f00140300c60f0007404059901030f08007410712200051403d040c2180e03442614160220f045000020f0103e680780100a8081c0700960058542101003074404035100c0c906600007689802a00400c1c1e0858210040c040c0041c030121b00e05d180c80c1c51a14880c14140341040d40c0f81d2241020070090307070044041c0014440d5000705a040d00050540340c6090090040c9000c41540320305000f00050700c0140750304007001c3c14403180301d002c4c802d0080c003c0348145038417 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 558262275 1250 558261025 558261029
    0x70c0806161706031e033006010807090b0409021c0209090402130e01061206060609031a1905040b0402031603050a0f1406010308070c0504020304150c210e0d09 70
    0xd40045010361240c0c800210083d0000c200070f0803103a00c417240e40016690ba038103002481007194400104040800b100103603d03035010740490b10019001300e011046070300c01d40300100203a0410001c1c40000350b0050143d0280380103448001409519541c607148180000d510040c0e00aa403281141d4500a0b02d20302030003140c5101e080a041c0c40c0c0d164486500344100110b00e01c29000d02241c5815000786010000d10900c8010144042c0060341000c0504000e801c50b500c64110108104001c8024000b02d440e0140111161440826000e101e5680304800f854411801c111911050300b0142401305020020300d605000b1402202076803041007200200841c0e85032103100c000d210b44c00450050001c1500024140b85090060341c0c202810a206405a800c040b0241c00c00c541e42d91000c2092001e0181c2c0f02032940c0604010b46046280d81400e03141d0312074049410b420070214544581703101d44d80c0362083c01c4044440c0d22940c405e0301d860308000642c00103020303008080348243c4915501c0c0310f0b01c14821154042 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 558263525 1250 558262275 558262277
    0xa05010e13120201182003010504081909050d030201141602070e1f0f06080a020a080105190504060b1209030906032a0703030203190506010207050105070215070c080616 74
    0x20502507a944030144180120102c4065560b510b51110901d5801c440306800316110b0f0000e030780e58106803607520201e05084095135003e40e140c403081000241c0307840e044605800344900e901032503d8003040101d900c040b45822213600059010484403c06030150051007110395032580010311680c9500d12007144c61040310b1000b00580c08407008200c085c15030026690001000f620207541000140c0e5881d140011550102445e0204402c08211082d403113074105401060590341589000010302009040c9001805224400c124065a01c6000742d00c1044420060002400a004c5a940e4250380302c00364021002e106404c0c81101e002071a9110040708840607810001c10041c00c580300c10324484103405c0f0103807402403003004c0505205070f010000c0c405010224030a6402580c2d03483c08407610211010070010b801403540c2400b0901002d03a801103400d07000c3e24000c1c80e03c0e0382c071140680000f40e002144446114054280000c0a5051003010745851040c1c0300340c80b0131100356840b00200340d901d4801e4403001324 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 558264775 1250 558263525 558263551
    0x19060606030c172814092802100c051b010f09030203070e0c0c0a20040b0d082a010b09060105070c0b13030503120a110408070b090102030c0a0602030a05010e 69
    0xb40d132076044030200d01404002140210b080c26501d41c81e0a08075441424201e078040d5040713040001001d410000d24406205402c00700c1f1190941002583c111415900003d1081c5031500001c031205104000f032113003064210045814105880c140070700510700240c45140000c0e000c05076000900c1c05458440704580e400741c020907400c7d15102d10940f22400151514031440700401044000410070045032000350700a966401040000117180e0300312140b481002c600850404000864660f90541c4220345a1b80141200703035181031020541c01e182000141034003008002c640a01f071175480c15400301c03095000640351a0307001e4444200540d5076000c0c004d8010b044616480091003005042d8014150309015400c1440d5065101ea403418150782102049012102c00c5c10104031017003065000c0c803c1006030340ba503420305c1d0038142281c2c15203492141c000c12a501000003520250780e403003042201c8039400780c0020758441c6400742c90280081d51041d211540124184000404c01c0c11030f480b10740d801070001e10f10103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 558266025 1250 558264775 558264781
    0xc05040c0905060a140309010f180b0a090212071e060201050f15040b04050a1e020301060512060f0306010b04170606011707030b0909070501020f0c030a0b0919060606030c17 76
    0x88154058480d03c81001821403000c1803032078940b000355000300e0400001182c2204140300c070f03504840010403501e10076030948030074000bc520404c5d08075400c01090a80801ca8420a00200b03081045024585c0a9881400300c00500804001c108240b8185180540034507603540d05400c038282c850075612810540c0000c00810b10b4200781a8250313111050240000c9880d0b85450009422588110365600900d070305c4031352845611414000c8085903607403001045040d5410700d81c00400c3c600a40c000d1140982c03261020450980c0c0300040c506900c0801812500c080d038581e4541c0301140c103d40b007480141400d002842e001d01d10082007031845200c0c1a900c10b10703010362846016428460182c10f140515030390345e0b000e60316600c2d611b20355031080101c0c1d00240301031071808000910349910700803000901e4200d0543c282050b900800c00c130004a4120a089800f0707200e01004038102031001404204210984002e24100700882c1c0155045500644040042424520040d105000111480004a0000800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 558267275 1250 558266025 558266029
    0x60f14310803040b0c16081902041404050c0a1211060a0513081f061a030702190302280b0f100504090804150c050a03030513060203070c0c05040c0905 66
    0x801920312402000200040d640d9462035070950f03102c1d0304007000b4034400013201c0281c070343c08100e1039007066030702130701207220500e0204000d48960780c4a052104034030100c1110002d5548542210104e5003a40180404500f01450100d640340c03090000180100110275000036013414120a18101982041618203c2d00c42401000229409581700005002c02400700300d003244000e103441800b80007800000e040d2031100c403540c00e03040b14600070368480040c1801c9050140c0052200190501200620748135142d0310740c01407e038100110700c54008000411001400281a80040c500e01241c801c1d9421500445010300545c0241410034009029807140c580424909152814502e511030404410070030103680f0f80d030000d400d85240b0b00c42512050340c04141404040170b4000d1140d01c2a025003091489010142d5840c2d85401802901030141075940340004d41664402c5d0151103030a500560855803498103000280c41c02c1d445207800d450000710341e540898241803910a4100d141c200340c8605007000c1c50081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 558268525 1250 558267275 558267337
    0x2210105150c122a07180b1f03020f0310090b090103050c0d05071509081203130b06040908031f05041e0506030f16061d0901031104060f060f14 63
    0x28851340744121410001e002c9650b005040e404a080050150082c2440c0c81c10302000742482010442517a444c1554481480c0d50300840a00207480f100420569440da417003040d0002c0c012900c1070005c030480002000680e88540000805498402c90201f10049a8100780022246d0074000248507900c500c100d10544e203007000d80341c1200b61048080310b06464441d600100b040104201c40d00c04506e91060520410100740700304401e489501e03950314110701c0d140e600c01c0300030054003901070f2150602c18086000da4a903034200d08205500003015558030304007011039501c0d52890f0303540b000c6045846c0e01c0100e150714141c0603144415100700e107003500a050351a200002070601500c050703454072030050340c00c800a00510044031201c50348a90103510078074100000d82030041c0c03000b00d044c91075588039454080380e45100c220380c190381d003007101d0108841d444804200148200d4200140d10900070304001001c13035211084943c90308050303842c0d074043c1024044841c45402501c0c0703403400c3c5000810800c010824001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 558269775 1250 558268525 558268537
    0xe010e07030609291f0c0308160c0201050a0e0406240306030c05190812040819050718090f05010b040c0c051506060d090b150303070b1902210105150c12 67
    0x404100450b041425178000c100702d11031503540401d14228684061640065600f0b502c00c803040d024211380045100d008084840c101c000034103001000c10b01e506410700c1950203032405900039000300400ca448241d200b220351104410f650880743c005044c0380c902c0d8424003402040b03a521600e4200400d040074100300c2014240e94401c10b4903034800d94001810501004220303420360b620112103907210f050401403802c01c1e904c0e00c110f1820134076106a00f0300055000035034000b00c038220b82c680070001c44043c1620028100050000d03000c0340d004503003d4140081940710313007811802240c003008000b500710790036070b10301c0220130000d8202c1e00580050b541c4594203541d47d543c03007030005000503c1c11883d1400d810413142d4801c0107481101ca10401c00c4103421018007c5c0e420410700b00d00540c2000c40c55a500c1d803c0e050f00a09505620112007042220001c03517405403800c0708202c0b192405101390702098044030300e6091040c40d10900d49255400c290810b1a003c8bd10381d51400c1e0054a241c001c14240e00402b80c0c820 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 558271025 1250 558269775 558269779
    0x7020a0c060e0102060402102c0a0b07080a260a050a0b0d020a12050309060c030a021218040b310f0606090311221a0102060717100e010e0703060929 65
    0x82848044040c0d2705900c20380c1d203641141308910a10b07511800c1c00001c4849401100d03409008201f00408a804001034460350510341c03078900c1049071108850411105110070885407180c508050202048840e00182d1048031004010000032503e50100b002d4040c604c0b0303000c0c1d00000304c03104c00c3c030030344540800500b00d803030003041100c0c1390403548000300da21513000b00b640290039040071900203603aa42c180142400e0b94004564142410b15195040400740c4a1070a114412a82c944c6010007a885d40c2c80ca00300d09600d40e0b0801070502850340c40030002155070380030034a42c0d1031801084403d0902644120b401f5641d080c1e41d0b00b82c110382544e8404143c4455019456480500c6840c0305900c0701c00d51030343c01100d110014001c50301c003407000c6010301281d20064600d815500690108100c2c16030052038000e030030f242d0310980c16507500c2d0850751000315121900141141080c40c00007040502565072080d000c1c40196504114041d5901d4824040300e81e0180502c001118003201b040d149062107552034540c2c030b40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 558272275 1250 558271025 558271037
    0x7120801150c080c1213060903080f0d0b060c070e01150903080d09151406010903021c0314160c0e040b07050702060c0d090906080102030f070305040804080607020a0c060e010206040210 81
    0x580402c94500113004c0d58002171030a001a52911545111000c1c000618490501c038107120b00310f68032641d07940101100c40c00c640202289509240d4282d801c44140703008050040303035035400c0d1a251b25840f200b20707001d81c02c01210710f40c00001d502030307203622030388240c210650394101c255080d070f522207110f540301c0707150b00185540311413581e0081601650002c5481d85a540c0000720440c4a0021000000c001440e46062190f9148100b001d600c4610050080865a10544904040301d00c1d0036a0704002c941495180001e000c0346610983c0c00303600c00d600265000b0f19603480660303a5580402c41100040341c0c01484030255501089580c0d00580140800794401400e190600410b00c10705450140030b40c280c5000107010700d03010042c004207880340f50b028100e60300080d40755240000e481034803204058140c80402d80d40340c00103000e00428005075009402d00009030303030003400c0c07800e0000e42d103a454900640d01025076040000d500d50059100e05000181078000d41825a282e030200328500b42c08189203400e1000b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 558273381 1106 558272275 558272287
    0x1510060f1e21090503030105032122050306040b060405060f06040302091b0a0f1707021b030715020a060c090614071505070507120801150c08 62
    0x450b800c001d4007004099100c101032109405004403000d2030803801e10f041000c0407001b54100c0e401202140c115048241c00030001c820000a040c00c0075000f0441118540300c0580340c0302c00c000521040c440c00036030b5000445d0074504100e408075204034541c41000400e14051040b20740211050b5800343c0307014840004503046103c0ca0001900c40e0b201c403400203105064100e441c44448010349980d540721004220007404501c003143c020300100c0d0039680c01c101d6100000d94a03070b1046009500500c01a43d103200f6044000045002030340c1c00d4000c3c80800705a800c680c801200310484203a0003040c10400e0f138100a030407218560036036010014440c804202c0154003403141d1100401c01410123075103480625044141c1d2400c407040010b0719090108004100d0b803c54060000700d03004480c500000ca0071100111240700b001d0094501c0160011f02007842c07544181c100000840c814507044c0e181030 = true := by decide +kernel

theorem cover : BRFrame.Cov 558093525 558273381 := by
  have h0 := BRFrame.cov_init 558093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 558093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 558093525 ≤ n) (h2 : n < 558273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
