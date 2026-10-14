-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3055
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:31:58.816636+00:00
-- url     : https://prove2.me/submissions/9917402c-a63f-4590-9512-4da00490630e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 549280575 ≤ n < 549460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 549281825 1250 549280575 549280583
    0x6040f05090304121118041a01061b021801080a020f060a021903020a050a1401240506070807020a0b03010e0c0a02030d0504020d050607050408100b1e13061d060d 71
    0x10882001203103007903131080f003000307114903800140f20404a001a40c480c4010342250010500141004208007103080c0242c242d050014102c0c51039410042c004000418603054140e81900d01c0b0800340941d40e404000c94104d02d040020810250f84a0703581586034100071800b00d01506d00002c1500340391400000781c41110b4400d41c000e180c1541c240c0c56440341041c4122003502035000c2c281b8140c01180c014403005c00703190b00070066081c010f4031440d900c9084447e03030700410906e84008100701ca6844058140b03030040341c901310354150b1202081c0c1001a41445044802940a8003085001500507502005981255500000380f1010350310105050403e100714400e002c0103030010095011003550907440300d40c0060001e4140c807065007680d03442614083e000d8402101060002c50100400d100404c011151204002000d000c80402c80c000716104509044a10138110100141c09045444000040d03c80c0842c00300c081c03040c0c1c1d5581d030131102100000121483c4209480c400100390382040f0701880301890740 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 549283075 1250 549281825 549281827
    0x8072636120f0322050d020703020f040b150a1101020c06060f100903061e0c110601050a050a170c0616030201060b07021f05040b07050f0c0306010510050a03060506070b06040f050903 80
    0x600b48001c010301d100d004414070980002103d40e13000c18020000c0001c075000c2c64005200c510f06500401a15034134001c140740c880c609016480396640c85440a0200c00114001c846460b81014542503880f400d5000a46001d5071001c0741c9010034100000700703e405000184e4443c10031a031540240600d1b010b01000323880214203050700c100005100d551000c1c070300f586031080c100c00c07480d0492035030010b60303002c0049100012045460300e00607540900546006100c103c1d0317804c014600c0e00c004106103086d1840744c3c014200d800d031041072131660107119680c128200248400c2d40e4518101125139510311011041d80190701e02a0040b070380d4550a0211400d03550010411748100c1c01400031018103030b000111980411505000000d0012640ca000e804040d01c101e000d840031034068007600e4a008626400301d44658004c1c0c0042042e03490340c42000c0012803081c07410a54460b94280246e0103054158411350700301000003180424400b0201d0601c2c00b4001c122418061607021146504c00c2c0d600a460940c50f80d08 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 549284325 1250 549283075 549283081
    0x9070215240405011203031b120b0406030f240515061e0406050702041503080a080a060536040c1502070905011508072636120f03 57
    0x9800004810000c808500310301d6009107441c0072400741c41e07003a071100d420407140c0c4d101d800400d034150054510030328484d14600c0c139156090b50010020403060640b051050fa580c481000e058640760080ca01440e040384050302d10403003c0c07900000381c6940c5524104681ca41103003240141d421402014050300c02c05984001c3c03407c3c25410040790754001403a081c540e81140320098130305c0503140e001d040206a6034540d0b40d20742000d4010320080d00c903030020f05c4090703590300a1b00740f001420410603140e080c001c070301d0800d85c0c0b0303552420804000d14850b00f005901c1400b40001050500340c0f2802d080000e800a950441e002d9160203880b0504001500c00030a84c800040c41400900d090701707c98400306080d4812a8006941e814840040302c50a030001c0004c4081454445c600903045007100750484e201d4500b6150001030b00c0c0707070540d00803210781d441c0015229500c00305600c1820010303801d1494900b811050544041d80c0100c00000005075401c8a0714012a001842481150f0060319200041450103070300d169 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 549285575 1250 549284325 549284341
    0x302090306190207050601080705011409030d0c08130b07060e1605060c0111040f06020705180408030a0e03130303110a0b0109050a11040602060f010e0118050c090d1109070215 77
    0x8101240107101d2a43c00d10449010490800586000700b0b0302001500d240b50500c800180307414044e42e000e511450b801c001c024055140091100b860000c6031800352554049440c05500501c9071440400300201c860b0800300321141e0301d00083c8542ea01ca42403c005003090040c40a03103860820003803001e03030785142d08200074500300f1000070410007400d4400002c0c01c1e010059182001e4000740c1150341000d502070700074481c5980401003140034142c201c0c0c0c03504a01c5082c0c00107640c4090300600041141c0008404030720609082d4000007100c00114064944494903904092600401c520054000520300b0000c40480403010401040294002091411030303030a10003480702505018100c10038607565542805040c520301000b500c054191580500389500b8164124110740c0c0c0180c1000440510380d000411400b00c0c60011030301c00c42e0440b88041000d0b0f881d040e01c140a03015000040341c10100e4090500c042100a55000c0b100103012541030406469440040341d850000403002040748a403100442e20302 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 549286825 1250 549285575 549285601
    0x5010c020d03120c080901150807090c050918090105070f170402030c09250305070f0e0a03080d0e1c08130c0801090605150f0604060509010309020a240302090306 71
    0x498003908002450582042c50f800842d84600380c03180000f541d240900a6880b020b001e2004140051424064020705103050f07182c44131038501c0760682195503600012030303550046045e6946038100400d07400400c4c002e848070001d03000e0100ca0000301075203481d000801d0140503920000b541341081e913035001d02c600040400300b0480c1c405001130340c2c0341c0b03d1600340c1200c030b6039808203e40c42000c410350310310f8060641840108580186017908418075090108000d080c6502404408410409103003c1e40e40b03000a07404240451515040988070030390004031401001e0194002c2c0614195030011507525459081c1d0104102d40601c054200140700e650105a410303083d8400c1f0030445000e101007103186c0f0740d0381024500311184c00c50104c0d0080d454004000d6035100801100031010350564a030346609410000150240c81076024480601c81c000c02c80601c9a4030070351048043c00c1e230240c4000d1200340c640d00030189041083c181c1101100008540c000154404c0c000d803440924094000d00443d25030a800d4109 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 549288075 1250 549286825 549286849
    0x60c0a1506290f0903030d09080a020d14120c0d060602011a010219080903120a350a0c0c080c0102040e0105060f3f06211906090b0420090105010c02 65
    0x8180306c28840361031030b20400e20465882c68442e00c3d4440d0f9403522080080e0620350705159003006d20400c0141b40c1401003480e130480d5020350700102200c40540d281d140c090395900590301101506880d0801c08520140c055110601080481d5980380390030000c440120303510928000c1891b562804400d91400007502236024104040e0000d064030042d0f540c0c440501e4403078012119900016100441001d030794259682c0c428041c7c0740f00c1c91402e6220900c004c03a20b01c9004080e01c1c445000e40c4e5100c5c039001203442104205452030748480e03469546c410f207480c002e010b500203006a51814804400029103072428404603001917182c4158030b8201000d021141a00150310305400c410750511401c221690310121030f1482c92003201c11550009414240107000000c0c9050b50329840181030150141c000d034100152184c0c0b035485030110854214050310300b0070046d0404160051420b00300030240410000740c94044900c0117084a40d8410301c90114080194491080c41000d02142c0c001940401500f081c031201c0c62 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 549289325 1250 549288075 549288079
    0x1c09050102070f0f0b0a060509041203180308010f06020610180605040513060b0909030414030c1915020a02010f0c060e060702100e0714060c0a1506290f09 68
    0x1003061020340b80e122204000403002c9030942c43c0c40361484100708441c05e0301904071000210801c003007030800010800b10003016101800e4482d0000a54000070300c00c2d08140c2d40c03280701d00036143c5014158030b0301502114081c001c041110b085001d022039910310000e4590b111320301190500703c1c8680742003011800344600e800040c080c66160807000c56551500e028490256003200414610b40d0050304147d0100c514929200d40304985c11020300c03407950800000c0c0d070291502c1001c8d600804120350006480d092603040c0c5182c0040d41d200d00d861200c0100e50000d012140f0321101d400d50030b00450b41c02c90325882803280003030103c0d02001559001500c03d4500307070a40ca1040314006060191310b00780e2032034040116901e41c0180d03c03841041d00070703000302d0081684107940a001880984d0404202c0103087c000316181c2401004046084603100004106070004690000410309120178000f00d000003030003541c0640f45c203c0b4441e0014144208603070201d4100c4100c0300010a042c03110b085007415090b80b00e40c022503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 549290575 1250 549289325 549289327
    0xc200a0c032a0b0903010c02060403210b040507050304120203040b041a0702030114070207140904020f01021203090a2906011d09010803070c080a0b06090a090b15151c09050102 77
    0x114600c10411450806419031144142c0c13601035044c10107094601004560045400c00814000040e801c05d043c0e00742208001203048500311301c000b410307004000228034641d0060500c4103101ca281c1c0c120000f0341c025400b0700c5992641809079102a83c0e6440750340709440c20707201c04120400079007400d071218505a0110f080380d00d01e00501074000900f903502002d41440075a00b17040c00c0c050b4240d010404080203051a103444071184030a81c1c0019400d44000b03102901a04880c5505102d982c400d02c012101d42ca40e401c001c544070f0401c400d98a6540600080c215000b100e108030100e000d1043c081106c03401d10160040216683d01e46004640a80b031880000c5054403c0d4205084543e0782e0300a400c0c00b9002c00c03802162600b26505011f034403018a54850807064011510210205042e40e015a83c8000e0540f40052240c444040c4800141403400d00030b4031088141045c45280c03c8484035660030880c0444805101101c2c000d1211528414140ea00395403e086034011072803800c154000a00e6140190001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 549291825 1250 549290575 549290633
    0x1050d06080307061a010315090c0c0209100306113105040e0f19020307061b12050a020d030513030c0215030c030108160302010c020f03010f0c200a0c03 67
    0x420300c2c41c0c020031400c5030307016155028105803017890000041014002d10701801070390b526104201e81e4140034080c9240303060b21065503a500328041c005082007e030303024220305100d00d00408407240c1803840e4041140c01d5410f1401c80070382d40c8040b40503074004400c41c0c0300903180032102daa000320000300f040651081e54840b10340009440c2e40c82d44601000b817403054000d40b080702c51241c891800c1410302e40c0750801d501c0210710b035040980c0740042c8900a0707074268106144c00308101204240501e0407804002c0050400c03ea85003903083d44a80903003071004041c2c007104e1406a601c80250143c4004489404201c1c2c1500200004a841560300b169001c1c00980701d61024942c544402c81142d20496035201020f0002004000f055000c004881c800c100d0311094006060075980003d161329420792010384101c460b00000c99a507074080d440300c28090200013041111301200c26002e17181900b403400000100311f680500b644003400201d000c411160b4400c48000c0064196515008010f02d0407207400789610100c680 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 549293075 1250 549291825 549291839
    0x418080a020a0218010b07080c0a0501060906060305100510030b010c020a0603140a050906060d0302010b18070315080a020d081201060509040e151b070b100906080a030e01050d06 78
    0x240004000c40d40601140000e0740144910211483e00904500c000703c00104400b441c250700f070f500560350240b0a1a13407800000c1c0924580f8211a20103411075103402c100041020369940107504440c107a8501b407040360b4612000004072242c034859250005004c40c4003c040d58460ba09c08400c00005041c10700341d41c0041e801048495005030000c5010a42e6488868002120383e1801a44480c0d003800900651505001b00c507107401d005403489002c5d12003101c071041094002c1d00315180400c5c0c0a02083ca585107412031148511109a9040d030100b0f18010f0f44a880240030200da4040e228040003c20000c0015428070040c5080006d00303030382410050090554200c404640240288241d1765016107403802581000119400380c10031508961001002440c0c0d0301468990036031000780440342000391640b40b1218142440f0380ca1000344210102c504015009807450100c2096a01140e02040b0705503c8100307603903658070324160280200b0984841c1000d0303584070700010640303610341c85004a0040e9592038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 549294325 1250 549293075 549293077
    0x4030c03110108090a1a1003120201050601111209060a031d06060418050c010804062007140d0503180a0609080a120c0f0309110901060f02060601030b010905041808 72
    0x2003115440703403280126801e980e2149040f500201c140000e854158403503916680c0d0300012039804021240c50000003082c892000106e0320085803c902d90100d0004000300090082c9002c981d2a03003c1000c0603200d0300d10100003d07c640c520f1010102c2d036864048844200440b0303421040319441090344400c00d0700c1d56010401101045201120001c00c01d608210701000155140b81d80e4004241c80c20700c0c09180490300005411080440c2800d050300c250f283c5040184c0585a400c03145c6012018446051054031448001042910300030031440e00024249109581c0f64407001000100060050010684062041c040040404001c004491150304c2c80d43e00c04e0251015841c050f0384401d80421002c1129070031429050a812101c81c0412802d0003050010b01240214a845410540e81d441d0b108104910389191001c40c10009007004c0c007039030b9074600c02003000b0482c41c1f00c0001402500701080d0294024080d017081e544050311a040707120302302424000240140c070611640e009045e1000070120f01110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 549295575 1250 549294325 549294329
    0x15060324010e06040212070804140712050c090f0115091d06130b010f030b13090b010302210304031e06050c03010f05010c020306181c020616030903020705100504030c 73
    0x44926980c541c0340c40038050808600821840c025030040280c4040e6070380a061003030b4825400e0900a40c1500c90f400d05041745026120301e44841c0c401c07001c000c0351103402c200013042c680d442401154101d0310341c0024407943c00304c103a51400180c1c80b81c800603c54500d240d824000c40d0b141c2b44c5072000038076548012290301e02c040301c400c05070115119024083c140c1004480000d5502c03400318144000080a8002030000c074042841c04101765603444007807807668540605050803124041c082c083d001b01d0b400d004420050a11040b4801e40e504000c1c0350788281d003c20817520010050001e507041500d91307220607004884a03c00000c0505100c5502400200d10784a001d00070311014107015100d41c1007045a018444068100e641440050640c800041c4e40008420b0781c0301d83e1002900d403181035034000c5185000501b05141e0398400c101310311142003a034005540351040382c2400c1d010341c580c0001c032000e5045500100002e4016005144c1c14011420080c800454160842c90010311f0141d0302d440740c484800c00d42d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 549296825 1250 549295575 549295633
    0x1062012040f0b12040b060105090303030a061d1303050f040b0d0e0717070b0d0605130b040b1203030708041506060306080607080c16030207090905010212010e0702150603 75
    0x1140a02100c2e245424260103020070754209854164110707030032440c06500030001089006018001001030b4442c5040c3c486802014040307036140c0c1820010500078195070300407020400c842100900d241300e0101e629502640018680785a004010386041710903611107184036100c4002000009901d000110041c0040e000020000942c4001254010705103003240d80700c412103505982c00140c080001144070700c11644250301c91035855540c111041c001d000302d0390020b075101400c903181440380700d4590841403041d80b04480030451144040c00300f000d608041c00000318140d0042c000200d0250044032256005400380c45004d41401c1ca042e044401c0e1001d170307009a00061385942c010003200c0c504000140c1c001071141480d00642c505600a040d46004105189000351000d40c0840705160003400110042c0021070002c0c0040e00f4039080ca1030207584081748c841d02d030a8100c0c1c00020341036003c0a220340240d01c0e5038040c0c200c0454240703225141c924054007055060050384640040c4000031560381c0d42d50038003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 549298075 1250 549296825 549296827
    0x4060305100b0f0d1505030102190909020a0905091302040e030a030518060c0d09080d091b030506072703140d0c02012a0c230f03030301062012 63
    0x3000401503460601c5074404612220240b00700019100c0110640d01d0711040641e0010341488401d00b0404681801d0340482e4041d480002c03e01070700e900c000301c80d04840740103450b0015825503a040c10320072031103010605000200300d80000c1c0020328082c11840d030801e030036101c54241201c0c50707000a021100040c81820540d400041d254922070b4050040075030083c110b1281400c0202d0200b01e1985900000303000c0745080790009079072154110542c1c040c1024580107011203499007001c9200300700a02e014403042c0c0c1e1100d100c0362980c038504807480e4501d0590f6406030180c000d684404030103480303210088450752049408040c0d0a4540d110441030310000714082c1c0e0b911020b01c04608090350400702200b00d0070302001454440d440250348c10a1000402c1500e00b06d403001e2008011503481d48002400320000c1c00e07a145e80d0f8000885100c1030103124154104605090040c411980c20000300600c40007a8070f030150014401088031500880700f00e2408005852072402c04400c2415560400925008038031080c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 549299325 1250 549298075 549298081
    0x90901060801150810170a08030702070303031a0a1404090203030c030d0c09061707090e10060e01090311040908090d05010f15030f060b060c1501080c090610050901020a020604060305 80
    0x86801e40034411043ea0510f2200c40c01c007202c1d17100043c03a45004108400612410450410200300003c00445400411aa0302c030300300030740000e40701d1100d40b0090307000070f0404820015508019403481340c0118010070088580f0300e00b1030101000480000441c0d8405d0b564014000503840c00d0005208031560000510f6640c0c121024020480301001281010403408050510045400c00e1383c4e8142c08000a000c081c00359180b07030040300c00c1036694208130075240d1031406000140d07201c0c80000b0140c032015200c11038100c841c1c0c2d00440d5080c5003880f001d41a000781305030555403420141e1104c00c11074042c20a680c42c14107401d010403846028040c049603d81e548003019030040780648100025444003800c410600762039915080310301d0740340c210701910a65483e4504a41c039514103044908010000081c2d85036a6407461000500d43e60034810010140110082050949866545244290b5006018160401c080541190b00d50440703515641076100385c40250303015a50710b8002d070006144a54003c039141c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 549300575 1250 549299325 549299339
    0x160510020d02032d04320f070b030c040311040f021308060703050c0d0c0c140d0905030610030b0a02070c0e160e030d0e0307030b0f0105010f0203070f0b0c090901060801 74
    0x40d2103050381340c04103291040c003029150003280c1080e0495048030100b0040205400b00c02211444401510910501c04c0500150011701099010b600052136007600c1d03000d079407420500058130048420356021a410881400000c000c403450842c8010041e00024840d455003400104a80c040201140b00340640d0404100c010001c1041c1341e40700c04030f858280601c0c100310590354454014151076130143c60b16001d001c0b404900c2000208002d076040018902080c004003a0b40c0c1c0c070b441301008004005508000045094100000c545000781071101c100d0a40c00c0ca1601c4d01007d15101a084081e115000c2085c1c10104051040060107801e41079201072060a220078440c0800710704500c40e0003842141c11864201d5640070030002c610400d541413602c200340c613100029090041c2070700001e00c0803600d102032004513030390708003e036042c0c503000c0e200d113a50780601ca28166940d02540c0c0e0014520140445010000f07054048074a4110f0381c284002410011a200000c070020026080b006c0001c0103030004201c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 549301825 1250 549300575 549300601
    0x121e0d020910020a0308010303031d0111090406060c02090720010e07060801091406120f01051602010b01081003080a030b0d030f02070504090209130f0c060e031c05160510020d0203 79
    0xc0340d603e000600002130036981c0544569014440034050580c0e50002021040c1c1054020b00c050801d48001c100c080d5410402c1500c540109060f18062440e100e000b10b4124014075180030a180c0041102203103607281e00086600c040c1030400211301a0310506d203614001c80034081d05484c111198003600b04103007031030780061042d10140c1c090f51050342040d0041208a50564603da001207041c3e0b0f982da50382c00070000e246c0c41c00ba180200303e003a661800d4104072148a0035410401c002d102c0794024044e102e00d1200448113500181c0f03e90394480e25890041000810004c010180030001d4200454800c035071500140107500403060035004641c4495000c44000e81c1404030034050071003124100821001a004980c00010007007a040300c402444c840c040a11040e410100c00790741e44010202201030325a0300040800799450056402845444221401096082c103041c4407040507603203550405494486400980c04c00e00307800c0d0b940d030050003201c0b14582e0143c0010150070482d84000360341c80c204014041d1304 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 549303075 1250 549301825 549301849
    0xe07030f0501050f12190c03050c0d021003051f15032702040209150c0d02010c170708190615020f03040f061d0607140c0a0503121e0d0209 61
    0x3500d2800d00180a40e94a42441034007241c0d0644e01c07503007400c02c0c075070b5860b180241a10300b220710400500380a5042151480610054910401c2502c1700c0613006000e0010580340c0b82c00003075020a51200ca141080d00c03a50069034000030403202c1020310300310021010807a070300315081200319041e1000781a01710380e050f000309030b442e0030b0000551050079030342604400303603074118240240f08540003e101640780d501c4c541da41e00700c8034522001035510748600480c0c598809540d88144090350030f0030785901d20203000d00c0c1c100d6405468505404629075905804030750503030b00100105038800c07183c00850b01a1000c0e2080c41c028000c10b000c242245004039401902c0e02020041050440c1e0080000744032040601d4140d030100c0744182401601c01c00f031101c101c60700901d80c882c11500004041022010301040a00c3c01f071602620310b09481790240480c0034007952049502901d80c055000000040c0b410030413600a0801450802c03840001e0001440c60420640c0080440b1403565004181c0301c1c02490420040c500c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 549304325 1250 549303075 549303101
    0x60c1b03080316032406080703051b0903100510170f07061b12020703060b010e03070e1f0306091205040608010b09040e060907091109010c080a02010e070e0703 70
    0x156616503540e00001d440010001c08585040c181c40c01031141c003c1d0403032454644240710390b01883c1013441801d03629585522910001640040c08952028040d01c1150300500750841c100704403982022244940d540001a0160075104400c1c0002a81200b8413602d401040380e0ba014100f41450401c021028641020340d08a160704555000c454041c00014200c04803510b508114080343c940c0300030000146c00c482005480c0d10103108001c24807175408281402500d125450400400c640c905c0111010b05030141000e8269204500510200d596071071131aa0080d1700c0b24030f00000d864400444808401540e0044031410345403200c000410401c101c0e180200345162500d60704051501500401e400307010700c03588100381c07000184080c880d25190401c48001d105001100c0701400c00305200d542e1a0403510400d00003d28103142102d0441180086408100d0142e55110401038983c4400807140d220402c2c960642d03581d001c20704c051442c20b10180d8000d04020780c0c8400d003440d185401074141c841807001d5031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 549305575 1250 549304325 549304373
    0x510030518030a08160c0f0c060f0906170c0d09060506040f0506060301032405091c0306120305130305120c061302011b020d14010209040b030d02150c04030804060c 72
    0x48681c44c2e0180002d5030060341801082039501c16801e080d290800b801c0c402402200200b030200f814401c03049078035405c66070140d0790030420354202c3c841110f215001d401088005241c0f040c1c22600c0b008441110303a001742211005074a03241c920a641c00c1201c038484403c503403060b00c800811549142510911050303914041c01400180b4200300080c00c3ca11050200500882090b000c00341c0c806c540700c01600e500030ba16003040242d8204100500d60700e00b4024241c2c80814401c0d08aa800f00f0301c280504400c0356075004245109039015507040d612a0046201200c40001d0414000080703082004822055265180341c40d5175030141d0015141044001031102c05400350000d0401c006036402602400018100050720030210b400e480001c400b40c043c808060b10b40340484010802e40e403410b40c02840c806808480800022662100f416110504404002e001d41c21101040f68201008c102541d8400761081000e0300d0542c4940e5101e06603000b0360000000103400c03041d60010000c003503142d02c0002403640c0300c103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 549306825 1250 549305575 549305587
    0x100501050d080910091508011e050105041514040303030e15040c03022710140919020a11010603030207060801080a050703110604080f0303040209071103031b04051003051803 76
    0x90082403141404142c0618000e51428115a00c105213000250080c455684030081d04420011f104100a016040c00c00642540001d004030090f211003080b00c0c4107071a4541828584241c5950005041e2242c00c184008298900c420b0903026004101451081d140080da4071028099075203804003405c58941e11401c12002d010101d58030036954422668100c2d561100300c400101407010b103c0c00500445910481e1005115513110018060001d84012002c002e54400640c820842c44003004d4410407000d8295003200c1d60201d180b5001440210740c2420100c122039000460a03003103440d0f903442640181c12186041c01075552040341075004010b0640107002c0c050f44c640300c0f141c5900c5948401400c01441d6283d904081d1103210030784008013440800c1d101d50035030400915850703500450f0102d1085074100700094900340a0404514022100001141143c2d544400d900b82003141c500c2e07000f07000c2070500000034180d0700c0703400e110780307501d180d582c040741030f040400e00500b02e141c0e04c140000090300184aa = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 549308075 1250 549306825 549306833
    0x3061d030d091106030907030636050f07090605090a020a210b2d01050c06041101021c0c060b0f03030702060d0209040c020a03021b0604060810080f100501050d 70
    0x16601c8800c600140091031115074980600103815070360701d6940144000c000c20060680c0819a6022070703009810920549041e0415202020842d881031014115142c6444e000d60340c0c0201c180c2c0c102d9120300121005d0060280760f40e07160500b150b00c1403503e16200c14040c0264100040450380054602d4400c0d800d001a0850190000105684000101c03456042064182d002c0d070700030002601e0f010344561503180310340301e040c00b01000301c0059052520780d000d9080000d500c18002c840070303191000090a4591242d944500358040f4010302c190451003158040c601c1c84500500041c2d016159458620030042c00b480d009055901140d1541d06c581d10002d410310040d2030110441d45043e17030407113071a0b59410f501c244440c003d025000e000c80d0050320700700075101c0d03098000801b1500310307000c1c1d0200c0d080c20044807091407130a41940e11305508100c092004018480c0074840c110780101d400c5450b05102d5403a140b450b440e0440c0a2110781c401c4d80641d4007000c6002d1a4411213025080a4410801390915621 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 549309325 1250 549308075 549308077
    0x70303050d0f060f090f0b180601121e050906161d030f0102040b07020a0b0a1706040f0c0e100504050303310e042f040b011103031003061d03 62
    0x80000c181c0342c4a01040708400e600303a0054028003a41c2c1100441e198a40518500a12041c680c00100750301d4560369105e146041000c180030340d4218841c8044990b03520004440c1607420303c0c140c1c09000e4480509292103280000c10315400c10920400107205c0c41c0c0180504c1c40c280c8007906100e440f8110030700c2111415880581040d4a010b66815800400480d00100e4034002034980040603552001c18082011100e4100900445008079850341a1940b110210400c03071007910300b540040b62182070302e03008502034002880d0340504010b00005001002c03001910540b500851031500040900a51002524201016004110852030b00d03e040904010210351b603031048035144006041841c02c55500780d1403500300c800d4940c3e8401082042c0541d540c7e00d1240d0103800b51421200d00491004c20001005c80d800044400d080c032801c1c451002c120b103420b000041a0001c05e017410401c0d030340b00034604148104020b50040c0c2e001404028918950f0070910110741d4030700780301da891030302c06043c240e10014000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 549310575 1250 549309325 549309337
    0x91609021c0b06040b0409050907150813020406080d09030203100207051e1c0f1403040201021b041116021f05040603051012060221010614181c120207030305 69
    0x4200050000051000a842d80150345c8212820b2100280c040b41d01c070a640c010901581d07240f0110307141c1c0e80c3c80303d4402240c0b500322000da00006009400040300a50140e4150f0700c4180050800104aa25000e4490030840310305030680200300c0392181003085060802402e14000806c2c0000c6090135045e41e1129200c502003011b02a52111039040402444000d022407420400c5036034608542407164540500320348801404180440c500c01e40828400344541c044070311030741d4141d000d0191203047c9001220300702606032540e0340182e0b481802082441050008159140c00e080b0311030000c605c1481040000e00c440841c80110114141040e040c05130010240e40c142c8038036080120b6544c2d5460410355003c5129803005403034001c016910001c1c00300c103a0041203444041e910042c1c0820b48414500f154960038458040001c007200d503a52044040d00d405071010400003d803110701e00800400050200041d40c2c5440c1d0a107102d4070060041088902400e01d14808500103440018919100a00a0b010326 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 549311825 1250 549310575 549310627
    0x111031204110604030318060311040902032e170a08030408030408070b040f12080106020705122434080a090f06050702010c0905030706050c03070b09160902 69
    0x5100450204142c41241c0c150510000d05640c0c0c50325a03034180148184018401c07180708882c6807a01081d020712034001d403070402c650442c04602e044e203020300740c800950000386140e4402020050410145041c11030020007586c03004509002c888c240f1800b0b803c1c01041d0602641550702185407000000c00c1741c01503070b40c080e0f0040b1100f07889590b1400d03c1400383c480c4010041490000f0320801c02000a402e040d100980d010f140150000090000c00759030b0308100b8002c0d200568800681006a864011505007420f11480142c6900003a1483e251b890951802c0d58440c40354000c40801900603c0c6404810482c25540c4004030100d414040c005600804218010200100d003400654100c005402924807a5400307051340303201c00c1a9051a030028903083d12044d006500b810182e0180500c1000c0000a640005001e0031000345884000e8030b40d64084806600f642c0814842d5501151114145502c5a12510b019100300c40c01d00306841a6a6001c2d0445c6503050710510a000400e244415001642d49030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 549313075 1250 549311825 549311857
    0x100f06120605070530060609031e030d0f06090b060a050403020103050c250210032007050c09090c090a11070b0703060506180405071106040816080708030601020c011103 74
    0x143c441c04680b9442419030f544c21039007a031901171003c0f46141420040040e1582d41918580c3c0321941000814480c0041680d4103a20015020b095035110001c2c214115040c101124601598801008266503107403054a440d43c1c0e5030b803170070040c0f0360503401005d021040c12105d6501d011a0002d016040b40a64000641059951800a480004d211040b1041212030101c1100400c0e0802c20300b40501c6c50141003240070b003600b60810180342c1c3c082d000d110703110504681340040072524100040d00036000854151803a20036194403a071180c56940301c8601890601026012520741d204c280000c100c400f40c00c03101203038500000b180510700101c05681c505903100c6000141c41d00e4880049002d40030340e030010b03a8400740015041030744e01e14911740c100f413841c4152020b100355030ba44481131b14141d03c0d0780403020b0603800c000005000103162034002c117802400004e401c03182c60a20340f60615075801c2984120b45004002060201541e0100020205080d0900c1c00340c0250040703480898a0b070191001030021002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 549314325 1250 549313075 549313081
    0x609030506180c06041514030106090303271d0c031603020901030b060d0f060510020307080a11060a0e151012050a062c010903081513060602100f06120605 68
    0x6120b0200c490360f0050160751501e81755280c6403041e00840f02c52402180881d500e4046181c003180a490484415031244450701d071a64800b603c0000d2030b001992240d412244030340020110788030012000d40700440b4204030300d150703c5500801d510001b4007444100c100c18401c0154106600b2056149040c480c5400b6890b4035448005a0281c40714401055005102244242d4074404560006080c44c0c4800d0003440f60b65501c0043c0602c1590034000400142c208000100c04211103000502002e50b0340c3c40c04110605151050f84c0c2001000d135044440f0a840710301040c0c0c0c455007008021803a2054500291701404e1600b420002c1403054881c41e0307038100c0c510720440300f444000e0044c600e40d650441c8003480707800d6002030301c01d0900d080c80054906a03503034000c00c08902d0f0740510682d4a51030381500d442e0075588a52014840c06000c59042c0c0b40d0213140c05020701071182d41405075100034000d0f50014082810003d111000342c9417600424402c4503e01402005076160310030100001e6a00842c1c0000d10352 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 549315575 1250 549314325 549314371
    0x518010509121c060806091e0c0d0c08070b13140310150f030f0311030a0e130905010207050c010912080f09240c0106090e0c0f0103021c05010503070609030506 70
    0xe9540f818a040d061070804000780900c0c3c040342c540e124007048030a51300c840c5120921884051811a81112254405450a00541880090751400900036003801813801d5071044c44030f02e886855007142c0f200400124444a4105d808100300024041e0300000e00d0012001001003035407034034440c1c40210280d03151810708400c522404042005807080c00002c820b2a0380380d0500039140102c010085000640c010b080810300d00021095038900f250941d00c10b41000740e8a010814012018030900383c40d10394914074500040c100f48018070010b482907010301003522240d000588241116400030308080c07404510b5000190003402107480c1300858503c000c0d118a02c40c00895100341a219001c6101c408495082d1b245403d00405810b02c1a00c0500901c502a00e440c0a0401e070345682d8a007110350390040c140b10106123860220020358202c1850700604082d0050014403111a040c0800001c1642e07410041c80345080601c2114080c1c40e0b58142100e020b4955950141d6864000f800300c8030795454034070140580 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 549316825 1250 549315575 549315607
    0x906090a0e070f050a0b0f0304290a0902090601020106060f050309070509010f0306050c0f0403060f0f1104030201120b01081b09040203010b040816061413030602040801051801050912 80
    0x10103490001c03900c41e15103c5410703111007096400381d18401c0008000006001c1043c004036030034040025102421a151651110144003149004180c070741040c000c1d80a061031201c0c0400d103c0c502e08000031075014040c2c01840000ca0010b00410304590600b07d00f03005240e0040a0343c01e00264501c0c055079a0356802003a10304290071034010a40c805007200000400040703a12218094034050782d400c003d161070760400d03100640b15901c2c0012408800340000c0001c101290f1001e00c41c0109080e000c140c4524007141c0d44c0403503e0611240703200780c40116040c801d40d640181c0c0c40b03d5041c180301c810080003d2440010300026401071145022524100003000450700c01410b0359039010020748190345a58440c1100180c03500700780035030100340c454608101c49000d094a0004102d442d103440740c0c4644030000c600000b41c0d902c11800001401c1c98580000000381692005000606043c3c000050a0411010041c0400c45c41412400d00c4d82c10501400505c900101d04a281040800e059030307540e401781001a01a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 549318075 1250 549316825 549316841
    0x3091211030c011d24040201030903170705311a0408060a0c0305070e01090e06010306120b0f0106230a0e03100c0806061812030c0a0c03110f0906090a 66
    0x40e5007051309400804690700444042e07655600c0c16510054144000c5086110610710344d0401034501c07201090142d40a6800600514040d152940403120880180031244400380c50080c00a01c001800040000d548500e89030440200400e2250407d40c0e95241240f110160050070212140c107140b614041507800308680c000c10b15070041c0d48107880d00c50707044001880030f03c02a0001c6824140021030f41841201600c900d00b40c1610b5041c405400c01d0000b4000303507801400036040c10b50342e00c0d010901012140c1c001201724801c81811a0918000b1076400b402803060b40300a00340722100900d03030101600e0103c000e55030b0780c24441c03003500c0b03441c2240f045540c0300828103041c0e01402551000c040140041c4c1080d00150110b80f41c000300c540703c000901080d4402c0c0d5904030703149030204ad00c0a0540c0741c8500c410199066030001c4a08140f10100c2150400c1844d08084079001c260300010000c102e410701c00e030880302e4001c40d0480d0b02071880c00082501d4240060180348240030300c000095608060358401070b4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 549319325 1250 549318075 549318097
    0x7060914062a0f13060302130b03040308070e040e030c06100905060112020304020d020409061a010809030a26070f020105070504050105030c0a090b0c030a140408190c03120807030c0309121103 84
    0x5010b03178840340900254804249448084400000452230080000407203000e16410f554041e0a682d442030202d401c1903030340c0482c0e640261601d020203500c03a0100080c041004d80040908458102000c1ca23442049095000c40555810134003003000a0380c00407004000c524568070090380d40c2e40c561000515281f01c68034000d610520300004201403000540c888040020031148065040340f444006403060401141d256a45920030070104030713800d1185205404441da000d412a15071010202801880801280e10300e000850100c4191403096090203260741003089030501c140341c0f07414500001c203584001400044e040c140083c5802c4d0052140c4072100040079a0040f5507100c001c50f400803074480d801190180c000031070740301140810f0320316142200c086400c20700003001c01034448000c0a4554010a0f405c1c2e9102c2c910080000c0445c104e000401c0d418031b09903448032a03900c1c0c8078001a003142d40c03001c01c24040503e0f00030040002082c88900342c1200d110313420700c10420400354409a10314864490851 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 549320575 1250 549319325 549319357
    0x1e0312020c0a091a151605010e0a030216060c0f060515040606120c1103090f0315010f17030a020c240403110a1211041107060914062a0f 60
    0x382003d1107902108400104075403006080507101c0c2041144500d00c43e801031304074420084200d21040c1c2e42c002c03403400d81c401c20000c5101c4006010550800301811003c1c5d000d0303000302c10030500c13a40b5004040006000241010745144034191160b55403002582da0050070241c0d910081500c103410350441c04800400103005005207074958000404440344080740c1410681800701c0503d2660003901040c201c0340c8403900035810300703000401704031040c00000e0000e81c15000d0492122400488250128007a00010103180d220500d0000c0482184c0307a04040648507401c01e01066645070707808544400d000b04122840400c4440e00380300550045a10103e2801d019000100001084600a0110181101210003140d04c0f0340d00e0b004c1510510105000504510340c5262000003403500d81d00c084145080031b0303880c504000c500d03659101220b00901c0c0540765428040c080308043c403401c00040d0380c808a400c442c075140f401030824810580803008884d0308080c0c004184100b40400100944060013030b003401d54 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 549321825 1250 549320575 549320579
    0x61c03031a1003090506010b070f02040b0a0b03040b01030510180b060a120c090506010e0109180902300c0a1206020c01140103030f0207060906031d24011e0312020c0a 73
    0xf03401004400340446150161500000f004484401030b2a03005c2e80007680070036061081e900704001070038620308407980181420030120343c181c0983c0185200d1032164007030f00c40950450070964600400b1b0a907020040381080740c03450b030741010320700c031900380e940d02885a40c036a450710f0300021100381d16504101d039200070041081c0107118422540038101c0324a41410000340c1c46a00044401000702256180868000070042006404500c0c10800a0781ca8003000594a011980081c1d40310140c045c0c0030800e0743c030100c649100407402110751210354a0480040010441013808105160118890b000e20415484282414045aa012215220a00304c000c01202e80300c035100300140c41c020b00081c0c00042d00d105100700784a00022311340085e1540c40c2c0712012a03c0ca000e800f00c0140c03a90045112100c11a1079000c1c0c241c460400c03100d01d200780b060104045074076000150b0880318105038405600c01075000c95035450048600c000b8020b0700e4020b03228131100c1802d03400a13441c1c2020070b43c1807504185241c0700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 549323075 1250 549321825 549321827
    0x304020109210c150507081b10240806220c061e03020f0301090c0e100801140d11040c0c0c0b0d2d0c02190b0f061c03031a10 55
    0x1d256440c031400d4900b0503641c0341c0c04018100150000b214020900400074180807075010009041242d642d612001c1511520782c8d100350506d600c0058085520fa110124004880030071650310103a582102c40103034503607180c02e0030141d5403000500381540181c200c5098182441030100319080507608180c5448115640360802070269480d2a842040c65040f01a242000351090003101c2208425041c11820342c0d0902d034090005141808a400a218441000d51095190082d003404141e100e03031034000c084d43c5401c21100140ea85003184e207229000003000c6000141010b01e01d645408030640340050448519030041d500300d61580c01c003034000d202d000307000101061000c1c003d1001c0c0c02040c400b440b00c0907030340400c2440840040020b1684a1202e49916868261680880e40c02015441182c161142c030001c5000e15a60300d14081c3c500000d41410007042841d03070140300742c2212003911496907400c1034100001e500b02000200404240c0c40da402c580661039031134102e504546c0c00422444c940042c440c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 549324325 1250 549323075 549323129
    0x60a031415030f0a05070608060d0210030509010506040b09040b0a021e0a030f0507021932010c0203070c03080903010603080d0c02010c0f140d18050a0b0f060607080304020109 77
    0x5a81d8031a115440440f40200408510301c200c40340d101c0f0041c0002400d2400c181c8584200030002900910344003541c10160340e80c8000098035071419140015141024407020342550f000401c5035019170b0030403404036403a480e0059803030b40c00b41e0001c3c4000c01a88500c4500ca0180c86014005c000c0011300d4207807500069a4000102103403c01d070745042000b030142650740e009440085031960003603000007030b0002e41c0d030346000c1107000414030481e5601120040c54940585d07140991050407801110302c801041051024407900b11a46980e000039420f048860380c840711224110700000349000b002248201d07217500c0c250001405140d015501644400c121080c550013840f07144580c000643c00c2148003481c5074056400c03d4140381540c0e403000014402c2841031406c40e03005190381402c0660782c906100966030140b407941021031240014140783e0300315041004018101801d039031b0070003211b5018444103680700011260070300e9004500546035600e600040e98030038040d5010702d0300c0c542510f44080c007042c1000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 549325575 1250 549324325 549324361
    0xa0e0f030d0c0311030c070609080c01140907261903080a05150a06050c0f01090809100e01050a11031614070e06060322080d020301170a020a0302060a0314 68
    0x10400700607400001c5401c40c00e4428645113006030fa442003010902c1440c41d02c00404282d0f0180d84007003181d010559800101da404100505210b075036400c0442d0140e840307001d0140d0002c8945e0024408623040c2000c2c1e482a260704650456080c0d6440c240105503c01404603000344140c1740d11140d035000c0a810007800241c030888608411929000000704074181c0741083c0704029202600385050a420031005840d00d070310010403036825205000d405141c400d000d000d078106044c400c600d400d13150840101440001d540e00310644040c0031410f40b10306c9883e607100c0280c0305848242c0c54040c0c042640a00300b242503109080141c1c089d10b60301607604060000c1d8210740c1e02055081c00032118100c2da2903c21440468094801300d030320100800c00f04081c8005801b0501104a03001c42001101c04107560300c2c1d0b40c0e07602800d407031000e458002c0010081c6800300f41600b5441c440c11030150010000c81c8d80003030300307800e254040244920400710701c1a610902ca50f010180380e80707542d09a07001c0c40c107003118060b0044180b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 549326825 1250 549325575 549325597
    0x210609010c0e010314010e060406031e1101050c120901140d05011a040602060609060a05100c0b011512091704120203010e0d140a0318080c011109010c06050a0e0f03 72
    0x1882d01c00c102540309200d07603182e1041505800d000d507404e04402d002000809031030250b01545078140400425000340c080002d007500044d00c1c42080caa28505114402d800c5100d683c1800401e1042403403070303c1c0208020462000c09102039554942d40801039134603840ba103025002c032550110700c0100d2814290700c640c1c10b80d8452030340e15a610409164000c03e40c4198000c80d0010303044080070822a00341054a640c00140041c0781d0100b054a9201203850381c0c1c08440c0c0c400c0061240700c0700c2001d0000c0380142030301410b00d80300c04594590080138050304040100503242c95003a0b1b152140001e000222a04c03000c0c01303400d01c040560345c0e0780d9003032510300840b4844016482075192180c0c01010310b0300010102e00e640020b48a420030340782045034001254205102407030500d5260784039a20700720803048400c4e103464800d038800ca0702c170400000c0260071504501d001580400041040741c00980e0000f0407861a00c1e030000003c90315030b940c1c50f245c2c0050417403c000744c640c5215145601c04a4080480900f08040074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 549328075 1250 549326825 549326837
    0x519050f0f062b0b06090c090d050c120303040b091507050c0f1902031b2416140f01050405030904090f02090103210c0c0308030c07170d060b090f210609010c 69
    0x611710400c100900161404450110100404c3e403007401c10940a218182c021020fa07606074600b6000b0400c848121006105030b0b0b0400820030040201d44c02580d030300140a07000500f0898820035201e01c031040c01502c10014003c0124140c06a41020410840410314a0741603800c196070400030014115004a0124070900078013601d03410100d850b10802040a81c02072290040d002c0b00000e06280740d1034006c035034a40705d00401020303001c413101c2c601003060700388195100d05800321480324050078505080301d0100580d040406020110f20004269042c03e9001c580009843d455840c3c90403d400302d044009400c503520900000610800307031240c213655a41a41901e9840c0708040702210700411071203000303000c561858011320110302c0c610080c550028400410320300e04007064540001c4036402c0e1040c00960310000600c200e1408190254400a01c0c0f005200c0741444001e000042401d55401c008a00480c4440402102e94080c1409c6071449840301044d01d62a0514501041c0a0101110218003085d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 549329325 1250 549328075 549328081
    0x8070513020c1b0303040e0108030a1119060e0a0c08030a090512071a22060e06040308090d021f030b090f0c1e0f0a030519050f0f062b0b 60
    0x50038021140c0007032041014100341003044800416540c0c1d07001c03d140e0503100c1400301013402d1115030903c50180483c1c038020760701c1e40550203008002c0801000c1c20440c94104110200791040004040b042c515480840444d1443e0f541050526000f01c07050003502d5290080340000703140d41d0120040003124995a681900c482e119028400c80c5400203000c001980d018000070415100d09907100301c8140d000024051820300700030054041d81009511105400c5040c0b80b042200301d0704200c0d0901d4910090f91041d040c6455511140c825001b00c0690a00580c1e1200b020021552001205a811140f88a001240351801d41005004088200f1500d00442c85031010403034210580f41f00501c2014500d203028030344485041c000010b208288100b028407c0c00380001498500b00314003a04180e030407641e0000f0580b5190843c2c03a074404401c401c03901030300d14100500024404054031144e00402090402c0d030503407074240100e4029455682c0f000c04800c400c0812102c1c140c841410a41c50500a00f031100c800e0b2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 549330575 1250 549329325 549329359
    0x30313060c140102040e0f0c160503120f071202070602040b03040b0f070e060d2a0f03110702010903020d0302190b061305190b01050d050108030919050105040515090406080705 77
    0x4862405584440b468980004803140804501c46a200d42d840f00305a017071209c00b140c40e0710f03007000c04801160240c10100b0001130381d500c456001c0c3d5100b81c8034243e007241130a01040c0548405c100c1010151029000034444040c804541c0460f0000c100e524603041c7e503880c1c031b403e10705410342003996628030300d40e0741e04c0110322154840d00440d1245800140200d14003d001c80d038040c01049020001d40010109201041c07082800c01641c000c8151184c40d152048401960001c0c2140d98851500100fa0400d01070310001d070b640142828166075050340c0c1d0302001900d0f82401e030b14013800c0d100c20821440c01c092480c0208045c1c04442030003010141c8509000c160030880036802d55404450008e6003202200408512500e603070802080707220181450307890411000000c4041d103400740c00100036640002215581814180751014000c000481e900e200141001c0009005200b10b110300c500c03802920392448407101902d07040b5401c4000061041004940d140031160726140d20b1300c5a6445154402d4104160b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 549331825 1250 549330575 549330577
    0x607080a09062006012d14030705040509030a051b0706020a17030402010804060c050904020d0c170c030403080c04081606030617060a020a0c0203060405010b131a01080402030313060c140102 83
    0x900740003020340b68503820154074006401b082ea18001400e2035026140d15040507660001004d803250358042d149a58070241810300e010880d500843c011441d25041041129000c429102204101d1034015036481540e85c000e800d00c18854070b04903003809860400105503400280c00c1100922403008000d10044490520301580421200640400c048900003000101c4640c00508a2090b60a0003400c0410301004601240c100581c0b01410342c0c0e6402c10184083d41083d0b82c2d03030f0302984405a241052030a0a80b00c625400090401030501496201280f03c2c000402d003918083e00071103046a220301c458258100c2ca00c2010702c114401300c1d14110340452441080705450304424100380041c2201e8035000c0001c4001e6210104840420040d4a00200113a40078000a4001d50040c030011030034550882c01c00040f14028024000224600003000703046030fa03054040f48526009080c813014a41d01d13400424207500c10b11604140100042c240814450340100f942400540508442d0040301d54442c001800c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 549333075 1250 549331825 549331877
    0x2040605281d0612241905240f120a201c0510020301081b010e0f010305090a080c01020c0105012102090a06080d0f020607090e13020607080a0906 64
    0x60040250002845418083c5900343c00e205000c040703500c0307265400b6090f802543c5608081c05c281c0206400c1c0005032121030311250850990a03c20029420102c01d4820304080c908055060800491100307510395845402c2001da00d01c1c0506100d56400d01080456141c0c03001400440da042c444c80101941000c0c0714000d002e004c8800780094040070200c01c4913030302001d20351800300c51501c00e140c5030003040100e07400078500a0600000500c0d2041500b00741208410201d5032050402c41441d8012929a030b40c8600d804601c5400e003400a03803902c0e110500303030a0650401000e01207200c0081e4885040e881540208031071100e05000700080d9888003025480000407e1084102204002c40d0a0144c0360903040d0540141b1602000030740c0c03542c1d40c8504d07801d140b4000302141c08a825121a01c004a030180001703540495640342c4850000c2c00d004402c90510030103814006800c0071010860115141c4a0440d5417a075081f141c0a9100c2c101e040700200100051b00403100001c47c2074105804000b013200d04104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 549334325 1250 549333075 549333119
    0x1030c030516050708090d08040302130207020603013003020303090f0f0a0602090a12080706060506160803060f06040801061706100e04020a09020712110c060d05040204060528 77
    0x20680c01d6010202d07965045040185ca80d85c004001c480d5031a590003804211151240700e015499034510300410112905240b403180000340100890340042c0e445c101207030b0645180c0540c0c105910200442d107007444030005041d0482000807202d04040c580c00201951050402000b154114110b0000a68480e907000280f40987e034402c220120000340b554001c0d10043d04003600403191a40d880190300b074440d11090065500c541d002030320b0800c3c000303e40110b9020300000e555280c902042100d200c002d4088100000e0301c0d0301c0340071000c6403041e91200c4100d00d4003240102003a49071500c40c0078182c0244030340c0c800e0800c982c4114004100b0100c0106609110780143c034412440c10380383c101c1040c040d40b0010000c0382d01a03500880400c0408251000e451100d00503140740c001300c41090f50207030020000f151032318420782c0700b00508540b0b5625001111031805a1240202e50394845202050140103203802c900d9000d041c1030400c14145080c2200c604220301c8107944030300e078181e03030780d80003645006034090340a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 549335575 1250 549334325 549334351
    0x1e0f0e070518090f10060305060f04120804020a1e210302100b01210b01030b010509030d051804050c03040b0c0711220e0d0e030303101215061401030c0305 68
    0x8407541510b0348040d5215042e0b00c19150445100710345642803030100014000c00b00e54505091050240c10465036902600c51880f0a5607420070352a80d0311074501601c40b003400c02c82c2c8040000c0c119221440b1740c2e802000c11f0501ca0400046c1d20b40284280d440300d019412030344540c01401b6082514500d0070f2841d417609500540034011403020100042c2c600b4035140d03818440900c2140c079000e800c1d840f40c02c81c0c50341501c20002c2c030004040b0005050301c070645070f07140c10820144001c5210382e8000c2001000050316040040c0e0b01c603170054030600c0255510180c80d50042c038080401c480091520001d52003140705402c075034080d070b550391116000350056100c050680c0303805410601540c00d180c04103552010314003603d88142c1152421140a40d100b410084546400c0b13a42203500198005d180c04455550413006542545421807400c008100d0034890020840c80340c070030000038020070008410718103040c50000c1c4a05030b1120070f00c080358080350007000d000900d0400c0b0001000d11900c1224041c921002c660 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 549336825 1250 549335575 549335599
    0x1110105070e0d0f02091305011a061b16120314190c0609020d1119030b0a020a050d020d050f15030a0303112a0105070801081f1e0f0e0705 61
    0x12049000d000c9004442c0380e01e00500800260f0356100702c4c46e124040c4d80c01044440801843c108e401d44003d0741a44540480c8609c02c0045565698103507526207900da0106c1003800381060400f468519032005a43d842c1c5003120000c900354400482ca401468000d458980c0c10056500160440e8410711010340c002c0140703807848560541c0300394a524400d500034034000c0f50341c0015400107140d52070441d0040740ea1040e200c009403001c1c100b04543c0648402c405d1004c40b28246161980914080c00a240003100e0760300080b40030b401805007003034070f9201d4007074070003103444081e0b080940000f00806d440e11050004418000380911580c0c0c4556012160058040c14401c44c059030207802030040c0781c41c0414040b20a000800072003600c8041d1417101426800c100003002800d481c083d08583c40940b1203020032190f400140100c0400103032640c103804410060503030503102a40d6107801005080f0124001042c0c100700e0700c1d91011950001440701900030403c01c4410a441300700c641d0f5811a1258980241e010515 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 549338075 1250 549336825 549336829
    0x121b061f360e010b0d0203102c010b03011a0f010305190e010501051801060801030803060303070804090b0307090608100f09020405180d0306050603040b0405070503010507030b01110105070e 83
    0x642000142044265544100c98181881961052440d6070106a0750200740d110040240a1800001c03000c0ea0359000000c400d0700031030b40303400340220b01904090325102241e55010745003818072040046004640c00c4243d00000c00d501a241c40e0b42414800d600700310003440c911642c60b540c001200e0009103d00204c840d50401500a03100080451501007040d181d40251381000d07020b842c03542850100001a1581007204001c207000b15003203800c00900803030006010389500030014a0541e40c01650144d1a40c1c0d501c00040e1441c1300b900c1c0010000c141c041070001e441d030700e1074000146403442201525802c03911511258115070281c4111080c65021944006003c003140d488200800000003003c20072000d590045001d4940a4880d407200402c44070524411803024003800741d4003003091900b4000b451500c0b00041030307400043c101030b00c504940e401040400100700200301c01040060024000d1f4074104c0d60150003131482c0202d10703000c40d90391004150881c42c1032189a10406140c1c44404031952030741c007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 549339325 1250 549338075 549338099
    0x15020609120f0d0f0b06040b12011d0708090c030a030c030e0108070509130e0a08040501080a0c0c0209060118030809040c0206130f05030d020f03060406090903080f09121b061f 77
    0x3411300b0301c0b40d540c210f40c1c0190b0b1503610090000e0b1944a54940d61003505400d0342c07120b01e00590001c1109020080d145402c0001040915040020391034040b010b07480c1c02d8036081c1022000301400d0b5144c400c01c2158020160800040300301e00c2c1c007030b03124000c038004400010340b5400021503184000130030030054180036150200c0f03401d540c005e0f40100041d080f840301c0915444c00f081d410040d030b581d05010508101c690382c4800ca0940c4144401d400340030468094034027800e00c000c9588020b100d0010b031400561164801e01014510340280c15407035042650724146090b00783d20a200c0c0d14020760410100180b41400080c0c801c0c09082c025000c41c1c0a11015120b41c8071108410034211410f010030090800210464000703011015411416959039040c07100421003102d11907440040342500300004400440c0d000307421954422005102c1512543c0c81c6101c4500301003051685040c01d09000c101c070394900200e40e0100415840c082d0480c1c21a03100c40d0403404424506103070a4800c0030380c440003404003000c402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 549340575 1250 549339325 549339341
    0x3040308012c0a021201060512010b0714160513021809072304060216030b040b0910090f0c0e09060c07060609052d01050d061515020609120f0d 63
    0x603050000024101c1200c41c0044150780343c00d840c58000c9a00328444000551860040195081c80d5203400b00e5844594880101403003607021084010800b10309001050750064048000c98090b9400180c21418134810520140546809042c1485001500c02814801c0f80e40d10400d04941c40b600901d9081001b01a120080501c3c0801c50702c4407420318605951b203c0d00d10362442d0b881c81b0315261400c1c03480003403600344600d40801a81488600c00c2000ca40103129071038129030842d040601c6543d03883c04152032701b4443c00180c00200d01c0d002030700007400610282ca14105104260f00410195210008071340e80c0e9054540c0901d5800ca03002260b0101102d000801a07544600c0d00801c103665a04489000c4036011a81c1143c1642d80848040f0000080340d1710655003203e010301e40c000d950500011403401290024014074940d5117440142c506041c00b070074038006001c0d4800c14064000498002502d503401900c0158061203500c0c000d0100d0003020064540139600301c00c0c0e05007000343c0840c03e40081c0c8424 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 549341825 1250 549340575 549340619
    0x6080403122706020c19151e2c0a14010501150525080d0e0d1d04060e0703140703060302060307121401091a0d021e0a121101090b0304030801 62
    0x2089035805c0d688041c0045000441c48001c2c2881c3c414050812010308140f80074065001460099201c00c0d011020314034100b0300c02d09040005044000302011440040c00b1f90001031101800f506500c04e00b800025103940092107000a0200851400030050a0380c00a0291091803032001611101851040f030150019081c01e080c101140c1003403007995848486650001c0d11601c200103003000d0142c40b103002e1290040080f81c02001e04005100d0020144c00002c50301e078030a481c80f00344844080c0d403283c1201015100d81313800c031300450800740c202800030109215001415604900015801c900900c10003040729000f8105070b00d150b403900c3e011545ea44010880124480e950074444c8080038142500d54080c000e02e99001480c0c5011440d03a09482848900f018410f449801c00400180c0750b64000d4030201448080390200c03520741800242203031803d1b8100c0410464401902400e10008803411008003800381ca403541c03034035294030b4030031694070080343c0c0a000b00b0706030001040501e440b448003081071752038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 549343075 1250 549341825 549341827
    0x92004060806060409090c0311030303060a0506032a070302070e09030706020d140403200f0a06020304080408030d020d0b01032703021c05030a0e0601120b060105070c0608040312270602 81
    0x21742400800712502000f0030785048035299401d00420818691010084408900450035450902c000038000403460203014003550300800403a05800f800c100e410700c0580001502001d40440001071441600014002e60042c031035500006a241d075501c4040380100c03102c10145242c03419941b6114040e512170054002e1031641d50445040070f00d41c440809004522aa4a1070003909002c84600310640c01500c1d039841503040102030300c1c481c1400051a80c50141e00140142c0c0301e64840c2820700b40c60085522400c454000040c854640e0b1284e907005004036001c24904110008454004404650780e0705842010300e04010882c0c03402441941d14841d91501c80c0c0304540d00c5a01011814601c2e442c01c003952008a800401800b0301c3d000c02c0d024810500c81c1110040001e50b151481004843d00494405041c40300f102d0302283c03159105e5000c5511594010720102040d81d030b5020020700e890000c84090300054032541400c200000305014101591900c2004208407244801120305401c4603440c08070b8100c0c3d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 549344325 1250 549343075 549343079
    0x3010f060f0519020d081014090a0905250801181e02221d06070f0903080703051209010b0102120a3c0c0c061d031203010920040608060604 61
    0x20038160b444803c2d102031342c0908542c000c1c801d400b0b40307084805001c1003103800c0806410300c06030404c0302c8201b00c011002c551100b040d4030303080003010080c01804800f0300180107215210758000403900310444402240c546051455a40c4c2c081c580c00c8078171860000c00d000c000200c0d1180414200042ca0300503c07005100032802c090070b0340c0050100f441c10500c1004207010801550700e00d810300e1080031000c1c86040002a8000c420400c000c0c1c5600000b410b410a0018940b02a000c5500c500301c10009107501601460340c5004500b00a007464100503d80510003048000003282d03a00b040c0962140d030340040c0c00919000c03603482d8118840f034205601920030000504400c0b403003540b001c104060f05050600728215001501030303e5201800c0313207800b001c0c1070106912241c070018000365031042c115281c41c5005080c00748407440036501c034840c0b0805d403a414071520700201d01400d88003004504032002080d04124070315244030300d0b8400040071554040c07210b03000e00041081c0e60060041d50340c07148008096a162035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 549345575 1250 549344325 549344347
    0xf020d1d01170a0c09090504110105030c1308030706061211060a17160809060c070602030a0f09050d2307110a030c060e0316080309010f030e011812030203010f060f05 73
    0xa10110b03000082d80d91100184d00c20581c201c110320000c0d091000084c061487e041e103500349640c3c080c0c0501b40c10404000002140202e80005031180d107024000b904075102d0b0342d003001c40d940c1e4002d210240c80b001e207841000560040c40c08600e48d06540c0c08200030101e0400e20303040107042e4000c03030044001c3c00101c400312000e1824003088203100304000b101c480000580150001c2010300300130000010750344040d050000c1c0126840640f151075604c10000743c0d413555142c00c0704d0040c14004561a01c1c2604056417501003100100c0c007a001d81c10301e41e80700710140b1905c020305415954035002c20300120000f00400b03c0440c10200121401c12006421581e0050356a660328003c070a0301d60182e0300042a804265100d454184410360a007017408421219032802d00d1702e140d40320300c2181216814803a250388080710076400f0790419210041120000c01000001c006800c51070b0200c101d0441b400302603190549503560281c420350381600c41c1040114400d5050550070340320f5041d2840c1c0341c1c052010902080001c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 549346825 1250 549345575 549345617
    0x60818070503011508060106110a17040e190b0109230a030206040807140108190203040c1e0815130b07020709060620070501020c0103020f0d0504120f020d1d01 70
    0x7403401100200101807178183c10505068040e0007910820082d1841003108010010782510351940200c6103c800820085074140140701c0d55202e4a91a94001e040100b801450721040c001004180010b0046208140c0111448081c9014081d0028a903503208141c2e541c16805044070000050144440203803241c00003007040c1c10642c443d0103140c1c0242018004940a128850071908003824010b4036410031810800300c0c500203054030020140d0100000c0c06200d840d40f42c01c0c0c01421043d01c070301e0100035818049981a0041d001780c2c8003521407a07807901c607103a0407009114071400c03030300d0b06d0b1022507500d41c2d5588400e107070050301c80c00851082c01000b00702101c9600c5103000030240790300c5402d03d1640d20304540c000001510b41c401032940022030100103998020032103591a010901c0c005a48240c403040b401c106005114861f00710f03074a00001c210400a20b10b50144401240e0b031a0352845480440f0f01300da82d500343c06000d070009001015035000c90710240c030700702300d40c5001410310544080800100c03643c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 549348075 1250 549346825 549346841
    0x7050a0204021b100e0a02121e010b0103061a120405100507050702150c0703060506040f09050705010e0d0c12030e060703090311100818030f030f06040b0a06081807050301 75
    0x140f62072410b490300110b00d0030040d81c0c80e030301c48809090110890b0424016200c111458002e40180c0900190b5154480280000c01c1c000c850407401071010805c1e0704800b0b00a1586104050100c1e00e0010302051714005080d55440400c004e45030245085949070310414103400c003500440d0305102e107940c8084030310001d015943c410451035403501e8460b1810300401a54807903130421300203200300400515420100c00b24000c02500d4022201140c1619044c0101e0010010002172528040c500060340c0100704003c9034030411603c00343e0310b001500e2082ca00308407001492107401000000d40754010000c40000720304c0c200100e8001d003400f0100e04a00d8010070b03800c0d032000c0320880c002034040d2002d004010f03042c040d00d266280e05a52a41c005400d506024000d440c0180810008440c0c2c00f03840c000c074000400c1115001c40d4071040a5859060001505605803c06e036002d6110790304001c603081c55800c4c0f122a6408585050340c42c600c1c65250041335101c690910341b00450a401048004503007901e09001c0c1140c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 549349325 1250 549348075 549348097
    0x1a090408031005010f020c040e16032009220302010617010e120f1e16050715030c09140f060a0f0305060f01020d201204080d0305160507050a020402 65
    0x81d40e4901884400d0321124103801040c10300000d40c1c4041ca009600140ca0002c000090f14001019901003418614061210083d03078556825500302008001955609610200d07165045055503603c907030400142030000c0304c444945a08160503a103507114001c04140c4000d0007800005811911041004c5c04002080d80e1134110340e454500f484140081002041103000244024500b00080d58002c050184030708107220140c1c1102c0c0c4000703041d180312001107a80800244039140c0c40d1040c0c51500c1030701c2c0c143d0342c0304d0040b00154070028041624002d0082c1107180101d41d03581d0303480d1401c000250082c1c850407202a6041109000c08480c039413a20750040801c84100c0e02e038450031140c0000e00600f42c035002003d5500841ca20122000141d030005803c80d202c1080d401e08010350140e4480c86040740c1c004210403562485481d4034030700e0b482e00d2200148240d84030402610013848907600c00790140e51050760000180d8440001c01c0240f20304c50400740a145201d0001d64000e08810380018050f0380000110f14 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 549350575 1250 549349325 549349327
    0xc010b121f02041e05100311041401361205061803070f0305040f050103020c15061206010303170906091b0f03071e1d0703150905150103060602031303061a090408 71
    0x4450b901c0c1005a0b10f40c0006646010b21204008c074807040c01c5800307640b20300e14000080200c0007503140e0050140c2400c80060f001c608950404151850007116000075403005801030305138020403018030070b0480070250764010000300b1007610b4811a081d5030400c0d41c0390310b0785140030521946000035150444c440c0c031903000eaa10f183d2910704000500c0495003055100703031f050510401002d2030017000842c01da54090845046855180e030b401000c40c0000090659516003401a10004010103070420f50b203049488000d01501e07035580e40c65025030303901c5000380c43c8048642d00840000402031802c1541600d0820040c0136800103142001c04245084610340140d08074510308442131304024989500740c0001c01d1240030311600305614000f02d85851101401c2c4208250b1a41d07620301800b40d2100c188002420429420031240c032300f402c002c0303c000c030009510a00080c200b003000138245100009890040081c603285800451075030741c1d403400070004040894200303540403001e007845030340c1d921800f13206a009802c41 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 549351825 1250 549350575 549350579
    0x1c090b071d010f0e0f06040302060403060504050706081e0c0409020705010b09090309060a0f031d0a03020f0f0712020d0602041715010b040909060b03010c050c010b121f02041e 77
    0x10403900e102003100904000c4a110300c45022603001c0b038482c249407800d45d000e400005805010a03040d124a8001030740146000500004001040d80164404c03400b1324240c4520b69192001110214001d503990300f144040d00107120010010029800d400034681601c003403a25540760a02000e0740c00050b01915965134800804c199410450a000c2c0e0100101c809549001c0004001661601480d01c0d05020030015000c0c01c100140030b9403004182100600072805511103126140703503105982d0108030014000c1254049855000182802d02c0da5020406031410906080085051118000382643e0200c0c00e00f041002080c16403000308058040c5c0720851070944441003c6510b050242200403ca41580c24010003035403d0100c162429602041408100c9a0f02405c1a0703018002c003048207a0701d546070a0091780319507088401404c03c45502c1009005002d0040708001c0561403806800b451504040c11000f8040303503442d100012014400c2c4010300b0b243d1580408200f0300c1100e00000c0054920a1003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 549353075 1250 549351825 549351857
    0xf1002090406080c010906080c0f070606030317190e1501120b0c0418090201051902071406040803070b070903050706120e0613060b0a090212061c05031c090b07 70
    0x40c2e400a0710f02d041c01001030360716100000700101c946106100400c14000301242524003240100c8003641080c00c1c89a4842c54642081c0006081d1480114041a003d854880c1400140c41c480e901c19000c885007031a4a00281034400080c0c421454040654001c00110041d0b40c1e00e0403081134040c0c00c2d2800a5525041ca61800709100071000c4d0080710411018001003101805c031003004480030380800008a03a0290910058506008005040d01c01d4504d41b032002c034846030b000411034102c41d0b00b6065581d100303400d0010b0102e41c0c80791b8002c2010035002080300401284210881e543c000b04203242c10038040381c0e82d03100d0904200460b0800d20000e9104030b14045001102e005501d4420b00000c090180c90404003050f030041c0401400003090700380c5400401c801c0f503480058800007010041c07825955603517074055907000e0020498240d80701d400590303130381156441c48000e01682d0aa010005514040b10101c0300c43c0c107862001e0030307422581c2c0c540381360500082e10004484e000b10040d0f2520f030103850a00c01d07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 549354325 1250 549353075 549353081
    0x307030b272203140f030a05190c02030706020703090b120910020c1b010201020c0d08090d0806130b0a0b040605070501050f1902030c0c0a0f06060504020703050306120f10020904 78
    0x9080c90000803110b80c10520800850354501680e01d41081c0002c90a2640700030000d0180d184080500b00000c400c1001d0030099800c46845100b00700c604014203000d900000701111408a180c0f001a0b001340000c000285007a8000d0000e40d00906009100960b60f031441c000562043c506e00f890b0424540500911000070032610158401140c4c042d030900c00e00c0c034942c039030319030394000b0006a808104417140e9099000390704641c035021480055035030070b140d0010003070036807201518100d01ca48204202004814821748040b0300626000380982c6000c802401c401c406000b06405e082e40c0403000010004451341b929004000402064803030030f480b41050304156085580042840ca443c40c1c40b03070200260403080304040d40b00000700382030060701c0761551854445540203180664515100d500101c80a0102d10340000a07468450002800450348400a1201703a004282c40200490010300c08182c0500e07140e030400450180e0301d022101c0c40e000d440d0749030b8030f00341a044403603015640c00103806900e418540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 549355575 1250 549354325 549354331
    0xc032103020403170d0f0c020c0112090c060f0201020d020a0c21090605300105030f120702120c0d03050c0c010806061204020d0b07021c02010c140307030b27 69
    0xc2011410503146440382d110101c200300d0345807100503002401e482d0809855000f104150301d003c03802c0007445010b00001e5a10300404e2a5140440c011800b6240314591a014603484164465152000fa5107030280075900c1d031a00885ca902555020f10003403899038060b10141500c0381007551554181c0340d0341e04081c0054814407800d60b20241d01c5808a41d81c41d5000880300080b510203290480d41c0d00b048098520019015544c80c4440d03420600d000d0241c2d40990410a042c0c0d50210700762000d6881c0c2023007d03503642c552601c90400d1500103101800140c030349558880444444001900c1810000d40f00180e25041e8404046001c6807020600c9a02e41004000d10202d1001c20300700501746040400000300240100c01a0f8410b070f8076504006811511010203105410358000807802c05c5003080075000e07445907a800003903400132060006407000107105008801100d405030b2244503140516118030400b5074002460304051507101c6940e01100d49501d6111061280c88403181201c150321b00400d0011480f020f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 549356825 1250 549355575 549355577
    0x6090512181f080628090e0607020318010c03030e030a0906090f062114040f03020105060a0e130503041802070209100b03280513140303010f0608130c0321 68
    0x501e6901242c6420004042e0401d5003124038488110300c4d4441c28900e80e0702c1c0383d808015603104103400150900740d500000d002c211100d046c0c0b2241c0da9141401c80e03482c050f001145040c801e0300c4409002550062984255007030103880c000c80c0701d40000405038519841803110100203012104100a0942d122005602402c003030800000c9291400c0f400408845104d5400901c62595503802085110380e03034000c01c05c1d800c0005803040c09103010f003001c502d030400c00603098016500b0000040d289144c00b110200c1a201308401c4000142c480349001e07182c85241100c00c984a110400c4003003005204010741e100b5070514028003507500c00461061040700e150141c40c2926040f2806814000741c5940d4058075400120501c150030f40498002480000a24110800d82d07014600300501481011a801c981c858034000d074540411500b480460300e549100074480c1e10009260f544052084612034541240c0141004600110512003a01c070510303c400540d20894845001241240c00103520130041044482c607 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 549358075 1250 549356825 549356869
    0xc0f0f020304260c040504080a030501050306010e16020c031c121b0f0c02180f070c110d050f100203090d020304081504060f060b0a111204030609051218 67
    0x40c12203030f18400000c19103400011400e215440e11418000c000f0742c004240000c1040c80035040c2800d1079581a48141101d00000c0c1c200400407656090018401d41240d4080c20411080d5480400c42c591600d440c44900d0308600030069648030300d0b50200710728003041390400003151003516140c2000d031480d0f1040c1842215182402502020020704001c000342c507801d541040400d003080d04808540c0710603035035002980040240941c4041c01c45883c0040c0c031802c407042d40909551900f0100365180342e0b181200418039a9800d44000300b9040292500100c80d1103003041310350070521590001e040c007954052100c0d41d658084200940d00c01c0820922003e01800e00146140600b05000275031900e80a203039800040482c600801d04100450340003005141841e07604004007071b00d5440c405100d920100300c260000c2c803000000714603601e000c41ca181001140751849491320f031450381c40030041c244100c003c1d1032602640090b4040c1086030401003031107001c22a55240c024001404110300fa05000b1401400004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 549359325 1250 549358075 549358079
    0x3060914090703030c051005010807151e030b030703050601080f0d1b2303070c0302150421050f0d0f0815061b0c0a08100b040b0310020a050d0c0f0f020304 68
    0x1001c90b000301569058644a0071032074050505514110b0f0324800402141d00c2c08000146000000c84c484099500e4100d4404000c2046d10003107a5407012036240400d00d0003505840700800303002e60700591040c2406416614480c1d0b49403910350400c1b009074451740031900f001c08503c0800c1001c2c05030220500041c2840307050075400e1106029451110040100000e0070f61645411031510381c411b0000f13041d0680e0407203581f20301c2d500e00f0198002c241d2104074002c0380c00c00a41214505080146c0b4103070b550b00429007000f1103610000114a48031b03c0815a030328081d00da100d4803100c1042c030060110050a484040440e441e042000344544001406001d02034055411114180d88240803125180d41e243c021814071546081004d06115503c2d0445900118210b000540b560000c246400d422004c4001003100401c40e03c28003054420b0750350003550542202180c20508001e650141285000900d011410002400f40140c1101d802032a507001094406180c40301c265400040344811079041e01c00f45003024 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 549360575 1250 549359325 549359341
    0x8030711041829011206110a0f03090f050d091802070f151407020703050f19021e060315031903050415050702040207080318070605070204050c130603060914 69
    0x200402100820f203081c070b40c6000d0340c00c0e203030050344a5403e45050408820740d42e40b100c00500050304c50074101c80490a140070000c00281500036650f10900d107441f592541080c40d00c0460003400c0717044003107071881f54442c021408104200140032010b2441e03164508264103001c0081c80800208503000307042401000041d00107004000304402c3c02e58018080143c04090f129a007001d44082541c0d1a403802c190002c0140007030380001c5031000c4a00480542d55035048049606880d191040810b00f4107510214102c001410b000040320717103a50300046c1b0210303081c21640015071144e10550300c070194082c801e419800c5e2450140601c0106100030700d035001d0280b086503000b4225015034800c114170308540b44010b56417140030b5011602010750041c0219a40c1300507180c000501d420a5a0f1581100c00d40c5021004070103000a050054032503544603941011410340c00c002c040c2c08020807100f00f41505000f69240441c800380b4a4010f4615910089101801c040315142142c5280c44216990083c000600083c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 549361825 1250 549360575 549360611
    0x30903030f09040f0f050a0e010b0603010b13080609100e010b090a0203070504180501170a0b0c0a1e0f0e1512070c0218150d12270803071104 62
    0x101d0a50090035114540400003c006210400c00183c10034106440d20003009540ea0105118918501003086081080c1404031300701c1c0d1000e9a580e810100400061200c4205180500104140c24000700750540d19030307118600b003280a03165001d191340006030030a0010401d000340119010301100810210b40e091b00000d03e40c41000e80940c0e55203034004040380c1d4a5219008450283c40c1c500e481001c11488040c040c401030409200f15050404d807258404042d4602085003c1c901c0d8000d00e81864548801400d003a072039101c6540c46003403001007001c5c2031503041050201145035219071070310700016603211005442c8042d00200c5078801c1e40180c2d4030036611240e98060381e03d40c0607840881344450f5105070040c0c600011380350000c0d41c88040c081e01e249820440c0e100c11071007400c0f41904540e188001100340020100f40c0070000344024102c4a81c6014144503c00c5c001c1c80d1a0100c00c101001c1c8100c2c04000c5c659521f9412000498100003003400038001241030307071036405605550030444800d04101d48106 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 549363075 1250 549361825 549361837
    0x20d140d050a1b031823030303070f05340c170304030303020f0d050115090e04031704030e0a060201061410170705070c1502010507111216060f0b0a0803090303 70
    0x1c82c03c40e51100405140c480c503480c3d83d08054001c803400305035403a50360b400e070076170682581440300d001c3d191400d050f07a040100649000d0905911054500c00c0040d006850b503400403030f44105014411240e5104850889040049112055840c001208010b04002c410b280e907036000102c0c0c0910032a007500c2c55200000880e41107030b405107401a10f4002d031041a042902c0b58500c06601c09042c60000b207090701c0440b40b00c80100e42d007a11400c0003150b58240c100d1649034202c0d00500410f400100c0c0580100f6140c142070341c018404d2030010440da41c81800950801b0b480d800070f00042c3e660703038400d000f14074480c070000c0a21042216090700422104200818041d45100c6041c0404002c4000c00c13101030290090b100b400b50300c42601034415031aa40070612481ca030300d041c40010341c08d11010541d02c0380200010b00c90a4a00c501401042d5180004051a94041c105040580b1040040003010840c0c80c031405400c003441480108000d40d015040280b0010183c1102002d5002004440000d540010403110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 549364325 1250 549363075 549363107
    0xa0f0f0305040c051014030a0b01020d031e020702040b031b0120060403140403080f031501081312021608010501030c060203030108100507030e03030403120510120206030c0403020d140d050a 83
    0x20741c00c449020200c03440e0f05020303601400706d400401805900c0304190081d240c00002a03080300c1c802e40c01300604906568800184e01490312101441080c401d500d81c0040c802c9900143c000300301040003101081c0760804d4011a9051506c04044c1f5603020760b0b002107100703a180454040d00c140000c1002c03205482c0d84016000409100c0c2c0024980c00c00c040810035a001540c00408540e205d07025a094082a0b5008541d800245c80c0c0604022586600982030707203024644d40c22906020311065030f03c64041104c130018000c258850300140c3d044082c9040c02c1d12015019120000c6601d503d1464203400e091102d402000035504148018822007500080c0310381c14006480003c00c80e41c50b1418140c1c001d200742d416414450200000b08801c1c10b07085146024040c0e01c01d0001c1000fa80c44c1074241c3d1a00006005004a12542c038200c1405450700c41c000c0e642042c01c5252007031900b0754907400203ca10344400e80440d54103a6030000a180ca00c028402054003400906000c0e180c101e9101c801802c0c8000164616 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 549365575 1250 549364325 549364339
    0x90e0d0212030a11030703020d0609050420040222090605041b0c151a03060a0c0509040b1504031a0c030f040201050c0106150918090201020c0d0602090301020a0f0f0305040c05 77
    0x7400180d03e6005400c00e8410600141e0b40ca0400e00c4004004e9400840d1004034682071000004104034584500d138495908121150001881105265410b40c0c003400c1040c1e12a0b028410804c0b0a101c00c2d00402c80c9202d4559905d2101e0703d031905407801d4900903402a03119a02d040c1d5605000440d50f5035400482105203441d241000c1a0710b0001c0c41480703d2008003442510740b000100400c004410f0440000208030116500c0b0b913507011102e01a00d80d443d1514000a205000c640c00c42e007000d030010701e01000014281c07074200040b00d600c1c1c01e01d41c0003a801600c4980c10b404072100c050220125080e0414000d41c040c61540c0342118112164030300141c0000e041001c002040e00b5070074130a5110f41e000c1c004842103082c0f1200420001020003103540200803050112441e5801c031880705d40b140300c01071607044e0045c1860b884038008001c24040741603030990754103030204004070140d0340a00c000c0c1103000d590b4a0b0015084102c4100410f284010000c1009041ca4003052101090140040d801100c004803528 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 549366825 1250 549365575 549365581
    0x10905061806131a0702010201051f060509062502010807080903042102100306180212061c05010609090b01080c0a030b07051219051b0403060b060c0d030501090e0d021203 75
    0x30300d00c50b111580c0408100c504d4083c0c0300388901000300041413458000da0090125854100d42e0800d0728455048214410310442000c118181c0500c0107441c6500004040500740710789580100350340a041e6004001c1c000d0803130341403021581c0050104d5001a80d03403400e5482c2e454204d0241d9528807650042c01020030101d0450321041c80300704000303401d0560180180c20766844810300a00900100c2c010744007031066000c030020555800b0b00c2502c941c000c10311000c51360754548034144505015008004802c882c202024200804d5003402464000c00110350300044e48149418443c1c50b5140c1a0010740c1c15801c12482c548048d40c845220b503040da034105104416a0302d5000064419101fa000f6640210f0343c00000c00903030814020b210304078005101c40501547d44d89414410f803181000440c01c94100040c4402d0001c60416400840b0801000d0822468a011610080e10300a401c90041e000640c0301c80040c405128070303010300159a0710301c100030142e0310764850000e0345501c00c200541c004e0301004000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 549368075 1250 549366825 549366847
    0x40315090f060f09020306061516050c0910050f040e0d0f2007090c020d090b0310230f040c0507020d0203070e24090f0105060309012405010905061806 66
    0x7180c40081d84900c00300019940780c4200d001505001d2416440790086c00c0c0015058100007d0252081100302c400c03d1400240c1c07020402e40c13103034400c819120f62080300840d000035150444464000e180c60300380c02035002e24210400c00c0f1103031033307180041c0a035080000e090080341000450000300716541c204088403c43d4944210b4101200c0300202e0415011120345101c4504003180603029580310100c21b0102907507184c400d80c0c1d2018050341840000381c641004010f0065030b10084c540100741f4400c03007045656201200b036190aa800c8040c1e81c900c140815140c010b252100150440f41d005440a110071100228040c145000700d1034042c2c00b80d010300d000d0030219a41401550301a204001f14586c113410a0040070322640f6100421000c1e0b05601d54440d102c900d40007081c0c030b00c00c5442a014442e56820030040c030546030005012800c45640b41c0c00032490000308240c0c0100320011041000c40e4507468980014401e0940340d00050241c00100700c0341d068080b0740051080440019181d450b9500308a0503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 549369325 1250 549368075 549368093
    0x2102010b150408011805070b0c010f06240f0504050f041d010618050912070f050105011503110405060a11030f030a02090901090b0102102412140304031509 68
    0x4416903018a40c444403048a100c1c0c8009881682c0000c0002c0100380e00c00400c00c20b00d14071803640a0481d0384005c0041000940c25002030458500c5503001140c007007007136250741c415140b05800026040c4410460359284032400b0044011000580c03900c00402c0f0b41d007640151851060380583c90046042d000301e410640c481c0e4104881c0021100382c140c1380d2012000c2c2050080c10103001d556452440f401c1034958440c07079802030314090791545011b40b40841c0d0400040e0581c0e40540c500701e40310701d00c103502c2101003a001c1c820540244012243e0303003550b0f410650018102c44164440c10481c0d04280700c18801500c4030400c0c1c0350600e045080105008041c00061031039030041c031005800d03000c00001000103d203500e8000d4000000c09490081039a600c40c5c13800001c1e41c424507403035801070340600c1da840c00c0001160043c0b502c042403c02400c1c070120b011850b140d080d880720b1b08030070122a00070003508108091008407001d8003c00070040c41c1081d046651f8065030107006a401e20400782c0b19190300c414008004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 549370575 1250 549369325 549369341
    0x10e070c0c03050601060206060a0303081501030e0a0b060306090a0506040b1e0a0603021e011d0a0b0c010203090c1c03050f13080a02091605070807140109080421210201 74
    0x7194525540b8644180e54110034090100140221070120724141082d03064401901e50648ad92000e951b00c1030650703110945107401c424101525030860007101a4140891140e081c059403985c5114a02034091510740000500091502d0b400030310040040307000400d0042d003180d03120350604403a844105000c145050781090007a07200c4000010700ca044405a4460300131203101352400300901080d010210714400141c0821400700342c101711200000708103180d4030b2811000040035030320485e0701d035546e442298000032084d0680341e6000042c04071884007002a003140c61401c460000b694036040e280c0001d00b01c4a1040102486000724020304450b0300c0505a444151501060054090755030300500d980f00d0007400240d004100840220f190250040220b1010361126100c5515251042d540d40c000c591000c42c1c1070f10034851006d00c04043c00c50a02403558804d00548015459500f00b4041c80390742c42c2161228120f011022a1080c0055018402e20b00c252000c45021042d18400001c00d03400350583e5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 549371825 1250 549370575 549370583
    0xa0314070212070807060c0b01051003060b030a09060609090827030115090e0111310906080f0d08130f0203120a0e03190f1509050705010e06030f010e070c 68
    0x100c0700650b490001500b60032250040c0854100070780c2e404050703890f01800070000d40041c6501006002e01d041c07140242440c10014500014210341c3e0341c011000641007078a2640501e5142e61220080c0401030060201602016104000406550b52009a148a104000d0040701303031010f0780c0c110305044242403160088024009000e42c0e400b417007420904000b9805101c0d401807509591400d8214144116000c80c5008401c50303161140f5100750586829500e281414900c2010342445040c4aa0a01e5080100a43d050110304603003081f005905202e0042058401e65101004207140c140e4880041a0017681500c04480f0b92009420022400220008003035094803508100001c03501c180c1005041c54000c90b131701e009120310040f040603141c500c1111103805085403100da00000c00c504901011400780b06100707192031074803003c1c1414265166032001342c490341c1144000700304075608001e4910310728108076880c91440c60300c081580c1c5c0d1080180500603080801e0000503107520700070170381c1000081e00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 549373075 1250 549371825 549371839
    0x6180608071e0c02090a0c1d03011508032d030403080a0603020603090a120315230a060504030c090b1f030e0f030903010c0504050d060c090f09051e06030a03140702 72
    0x140035001e0a2255203000480c041d6170642c00052040b4114490300c010310019641c3d10318902603a0743c0c4240d2500794000f03001c2d03040d56500c203000244101642590000c0000001450301c810152102c1c81d48401200c42d80c42490591118079a480c01d000400c49500ca581414654242d0b1102d01c4428010030581e000250030080010a0040c00c1200181d000802c0d40b160b1982804020004030480580c1c0c41007488941c2e8880c0d24005020002d0f4400301024040c00c0c0306c0300c201c601510000010300c0c3c002d141d4410008a40c0005043c418050030300312000103002152024016080600c0c0800d021801c0205190700000307007565080c048030b00c02d8022240d4198045d00300d6143c1c0d074a01400580321303400301508510a6180c6800c00542c113001b20192422104010b110380d200812948035103024000322180041007140544003c201005100c002d4005400d181c2d50005031450171f01c03983d04000c05014074030042c1035051001c225107913500290004000303074035150104c0c01001090b82d40005000e800402980704c44 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 549374325 1250 549373075 549373127
    0x19030219050309210a02010804021206040b01030501140601050711010c1205040504051012080a0e10080717191e020d151203021e0a0b0f07090618060807 67
    0x10004040c06014204840074038204506020050f0342041e04038081c4e00603042180d150000d0760049500c10b51150002c1d00c032070220810071109a0409008035400c40711501000c2c018402d00100f4490a0000010681007140a040c4580041c0c01c41c0550319008101003091320b50b00348143d1203801a98001d41c0d01a0620042c50b07403201024141c1d030011300800d4040d40c50a03000922880d44000d41d1400c80d9034215082c00c110100ea100c1c20f146034001c1c1001c0d414801c80320708155213925440450281c801580e5111101e5080034540240120052a010f222600080c814000c80c24600c4103009400501c17414005050450440820301c0344c0c4180c483c2410051010030b05442442594001c1d01c1c2c61032501082402103625001d01d5031411098001c085c0050780504440c1141e500c0c00300b01f032088071041c900ac6a1480c446540c40780301002c1c08071200e0400c42e4140003801f64403900886031801a22403400c29200c0c2070394011481d1041500d078411402040948800f00304214092144120701504080030340c12840b03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 549375575 1250 549374325 549374333
    0x50f060f011e0b04061808070e0a0506090630010e0f010c051303021302040305030c070504060b040803030c09040608030a020c010e06180d14010c0e2119030219 70
    0x84401d1040466004022104082d0140e1104031101620310302c802c0c1c1828076041407400c0310007005280201440c3c54018101040c000010003918000701640200c10a032458004810f005441003e00024002c54074681440026540c00f42035400c402001001d41443c03401700016294401c07441c94140602d540390600e400069200800c0f41c89528030640001d02c80007100000440c0c09100d1407642010943c8031650a00c0189807610380c00c00b941c00e6071a0090300f4242c90b5121103080d44c2c810351900e08a41d02c400c20030001400c090081d480100911180c15003814900800940c0740d07c0000d017000500500040d24560540d141e44c03000c0090403043d82182c0e120205108080d507642da1642e0b5581c049280300010300281e1034400125881c03105000c4080b10540f205505104409000300800ca5100403509805120000f0903c02e0346c491365000d03504c00740958400701c2440305040080380746900c032002194071002d282000040050386400702c1c0382c521400f03e40a00b812824907d2480e03e9030f004840403641e0138244 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 549376825 1250 549375575 549375601
    0x1e060b0903070f050a0b130b1b010506010e060a2a030203040e01080303060d0b040501140c0904050a1503021504150806190317070309030b0f0403020d08010e13050f06 73
    0xa1502079049034400c1c0e888a101e80380c88081ca1280c00c1e409050f150b070500241d0303c060081c01908005242400036503844134641c0d0510303004100141a18548102c002c1e41c07001003402442d4003c04c003170070045000314040c2d020588138450f403403141050003040703103c00308075400c444100f0b244580f610958001988861070001e49940c003600c0340c520810444000401c40080100c01c60380070310002080f07002941c01c103590300c003114500103005481c29543c3c0c075200d02035080c40e01402c5105911034803000f0b0b038038071910017040116100982905403140c98100c80c5001040e0201e1110140e0303404448036080a5044800440e6512454103c03e481d800d5034140110925005644207026000031203e02e05244a00ca1240e418000580307c05052400140c0113459040c0241c40200741d03043c0686007040c006500ca80301c0b280484010365a141c0340a200340104428181e06000c5410041e0852400d0202545000c074000080e020107041e400d44403030000811000c02c0f00411070412450b03403000550342a0320386060183c0708 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 549378075 1250 549376825 549376837
    0x20d05101b03051003030c05030c010f062c0114150d0902011403060109090203100314070603140408030601030b0f120c01020d0201140c070804170c01032304061e060b 73
    0x16400a0740c00300c1005030081c0201c034490059100000d00c1c0c1455610b0031110b0782044201514076010400c04039800c0d41080c00341c1035140c43e03200303000701e0322a140006403c1e20310f0708003102000000b118251141081c01852000d070446941d01210f400c44c058120015480604500710160300312400038850f0b0200265411031032000b4000d89621740c0031304841524003030600c812289180003d540c5d003c14080080c2c164040d6800c40b01040c8541e000d5526a6036851032100105984040c9501c00d800030030400398503015100d12076000314810200c5042660303510400c2d0102405450505071101040c0d0000d440e110034902010000a0480d1030344e2a02c0d01c449a1502c4020705500d005004040804400c40d0050003810b03d61500984160440c1d928480c2d00d05558121060032a000c01d4100000a07207019821519010900c801000e40203242d8040009070450708504c070f00e8804c41890000c88031440c01843c007800d50094110b075002c05c0c3e046061078603802050201d0307548251302d8641400891628510005004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 549379325 1250 549378075 549378101
    0x403140105070e09060112060f08012a020d050d0b04050a0c0f02010e03090108060d050d1701050d080d05040201140a0c110306060a180905070e091c08060d020d0510 72
    0xb51a02001260f0581410728180e030010010f40218540d94810401c1d44d00007200e0000019200ba2109152003000156501404081c1e4540c017110910300c0070b0b104001c148480c0216403181030211504080c1d211580018100140030000c00c004e034041c03070940c21503110a500107100700081c1c0381004003400100388540c44800020080c4000710146330051050000a03000e050085084c00e502800440e4541030090071107408c603480c5405c400016a04110b240301c054103a450703550303001c0d1484c0c0c140c182c5800140c3c005407041c10007083c0b0f00007065102d0b08441c00c3c1c96901002013090b039914001a02c126810481c2d04001c5100019150040f0364002c0190700198411010840c1c0100100c1c2015610700040d100d4940c02040c40d50100107007444ca6032800940c94102502107000400c0391503007810800a54045400b4800700d000b000100075084c00841044412510694034403412070400410049000300411302850a5452800035503881151000e481548103080b50048080980010007800450000c0c2c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 549380575 1250 549379325 549379331
    0x141e04061502061b0409180f050d1107060f03050c13060206090c09060a09020c100228020a03020c061e0c0307061b05030c03060406150c21211104031401 67
    0x40c0b020b0810441084040e9100c004e044e0426060101110003005100f6401e0f0b0348402c54064580081c0d8400c0322101e40c0d50252014200c084191040a00700e2807102a00c179410741c001c0358040c000b00e40c100c10010703c0c003c401c0c40c1c001880c1e5179140d90101c4903c13401036007024102020b14000b80b0b40760700041151090410f4400c1d140d000c07a01a00340041410280ca545a00424a08040c0030100180d03015001280000044a00240c02c08507002d08030b90040c80c2d0b011441d190004c480110340103450894182d040ca41c802401020079035107009454001c1c4c03c0c0070034407a24000541001002e1010703641d5100046030418199991200b50b00b16949034441c000413a046801e000c0d003c3c40c5012101c41038039820200f03842c1c0310315558544001c2c1c40e80740d100402e2a40d0040c2d582c2c1000c81c2441900d00c110000110544aa0307440d04202c0c03c11410104200d40310000201280d0540400c0b5580081d0f500d22680c0325070608110441c0b0140008050f199240d1040400c40c000b00b000000e100d4003408081001079464020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 549381825 1250 549380575 549380581
    0x40c06110d0c0609080f0f07030e0108060f040903110f0105100b04060801030308041703010e0a05240d020d060c0c060e01060e010501180f08010c020c0a141e0406150206 74
    0x11a100c0750018400307000301d844400ca0a000c03408a412100c06188210445031612402c4500701070150400d01c094401810042080001c058001c4031810484009013401007091408a0001d42d95080074035041e40210344032808142014055446802d9860004003516010018801c0c2d050080c82c0c110b642c0c19503002d20900018a0245400480c0c0036141c4590360a04540e0941d00c09568061010340110740c21281c0051141c020303e6848040c6010304082c60f081589418001800000e440300900506901c1a0707060007007000390150900c1090020003039511404108880c0001410117400101c00380c0150304280c50580501da02012401102e07105001c04c1140e012070040380d6003210890701488582d0f400507c014469176000d501c041c9040c07128034030802e030496210b100b01440780c00d142d40200c107203a445200350740c0a1501441540d103019400e9426000780f9240a0b01d0115609041c0001c0e4014450800c110400426850601070f0340e103030140003480100da85001040d641300b4244076850041c0552004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 549383075 1250 549381825 549381857
    0x160302070f0303021c050702030304060c03030f0e060a090f0204020c0601030b0709030302100b06130b041a030903090411071202070e0c030610271d010e0c0313020117040c06 76
    0x8020b0300e4156004080703001da04080010200d07040d00c11802400700038814100180c0c2c0401c01000a0034090fa14844a01601c0ca800350036151559100b1032103a0400ca600c030441c5a0000341c0e103620024000f00480c00c2c50060a0100d2048038100d80650031500009102d159145c2c00240c0d107040781d00c0341c6407008281d51078000449880c4070a020040050f084101c2c0c9641145142d08080d01301080184864a0002c3c04031110001c814554010b8602002c04282000001801c40c4644141294a0740361451407a09406150706c034071a4403201b80c4030756074906088081d042c01800751540aa0321800084000c0d40c1082d02035680c030281d1060204603100d5900144400781610150780c0250809807280c414131403440c10591b80810501403810844920f200e0142a00702c5041c2c080c0010980820081c40605911031041c1c00003405030071903d203501c44101884400724100c03080383c2d030000020300c0350f405952080c801251642401c1451407002c1481d1414032080c000401c440b80d044551035207d1031102035201d40c1d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 549384325 1250 549383075 549383099
    0x803031b1204021e060a090504050c18041107080d05040b060109210611040603051b04030507180902040903170a050c0a120b0604081e01050609010b0a1416030207 71
    0x1c0c0050440808400300700103040100011038412840d4121141364030706103001c0348a940042c840400042c181c00750400c010b0620303100302e6800151001c5c1091070300100d80c0f80100b25040200c0b4003800369541e0850b03c501c2c0c282d0f02007a04c0500364400161591110320441e242c028005c295010307a004144100801c15640c020588002152104030800b80e880800c0507481640b17406411044d80e1172611003007503004d54941e0384000c001a100a880000300360a01c85d500f4281b82d844034000b8400c03040104020b001003500000c089040754090344446250100d814408070190442d050000d400508102e8140c0800d50410307404075407403072140e040c2d500640e1080a4036087d035005403200c5081c41c504200d14000e2034440d08001d0120140d40c072011804007c9080440c8595200c3c0d03002a185400007001260340741c80541d070718038000d40004000c0c070a500b00840010088141071107099040750300052440401d42c011020041900e0419a115440e15082d0300d441d00965003002c4200c0c014041c208001c00c004443d20 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 549385575 1250 549384325 549384337
    0x1060302031e0a0902090a0e12070b0112031202030109050103151b0f03020c0a0305090a0605090112020711180907081f0513081908060913021c0b010803031b 69
    0x2058226242007034004118114901030075400715207880c0d642c0f01016868540c40d090040387c911100090501900202c2800c114400c81036a003001f80411803100440c09101c04541982c8520302c0101024400703140550303480c5250014008621b00110001800b829542c1c03145048a0040003105a0540305a013030360102c4903070324a0924014039510f08800c070140303d1910600d40c075842d8280107151900c00c2a6240c54034140d400202c0000781c001410300c00030300b06031113100000c0245040880c140360034440041d05034990000c00180325075010800606020022003d554214409081c41c8030b0041079000d5514010400c0318100c08030f108001c0c0000d01003000041041500d40f0201d0388013249008441480081c000103800da24240301c8801c01140403c05034030081030135a03604130758841048070300c1074042c1000c0c000030b060314440c6000c1001c100c1d01190615501900d90780c11901d200340040100072b41c40c25050f0703907000501076880080000c944040008010f40c042c0c0341d2601d00f0003a03c03004044481e0240300301c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 549386825 1250 549385575 549385591
    0xa0206041113051006180806070c1a070807020705030c01121802130f150810090602040f260106031e05120313110909120d1b12050106030203 62
    0x200000502040c0074444184480600410b00b000940c118455601680c2056a040001c000241010400242c204005032149203100b42900c01e104e00e040d450365101c5d1401000041400109821a41001265203d84190ba4250400400d4a042c604002460310008071107141c0075101e00710000c40c081c5000522141c01040507550170300d008942400c004042c000f0518001001201c0e8080c42c00169510407464001c04200c500c002000c0d0003060b5a8016030344a9442070100030300d601010302c0032203000304685034491919400400c0145840ca03241c0003d115a03409030b10608402c2402107800784118441c1a01000d82c205040c40d10324a90103454200c80f5248001403c0c0842809060a41d990300404801480e01550682d103221a440480005951040b113500c65481c203030030b20b114204240e210f422110780c881030340c15240c5840e040300690b035544031f0603582910804001c42c001074501d0072030b04048001c004003400101039941c0007001501440d04141a1072145080c800049001440b910030f8a20038030311 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 549388075 1250 549386825 549386833
    0x70603150902070c05030111031e040f111305070c0506010801060e220c090624050a051308100e1c020c01050903030d09083f0907080706051b030a02 65
    0x1034840714100952080a08441184050340006026502803003916840d9003070062240c0e403843e0214400c01c03a0117000780342402c0710208900f4400031403a0400c812280315400003c2c075044101590000d00747e4024481007a061a0030030041090701503102c2403126150703110368100e50490340c9032400c60703081e5109070007040400a180000545100104114103441c0703100f0840036051075041c1e0300c4451010820b82c009a011316200d560410a00c0c2e070400c41514036003507002e10401d0300c0c500410010101e100c1ca251102c10044041641030203102c2810010300207088840444a082a0501e10702c2d003d482c115941c1e070054050343c200480c20040b100c00020ba643c2060340501840c5204d0801074402d60008035401c1c0c0c062009201c4078101140c00e104440c90b40f80642d44164803000402400d0b070440c0a011455107a0510300d003a40f40c08a083d45000086001d5071094086660761242d030f0140c130b443c0603980300d038016200f0381000290142c1c00c007004001c4280c0e10440190514040c05000f40e5900c50204080e005900c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 549389325 1250 549388075 549388079
    0x4170c0d0f1401060f060f1809021809040f0b07080c090d0606080a031d0a0f170309060304060c090e070804060c02010b12010b0415030804090509032104020307060315 73
    0x56880e02071a4030038400e200c0412903030408040341d404c64400703410003001945582d0042c020140c00c091034512950452030101d1244110300044c0d40c842400740700740c0e50764540120b0f0410311480101c1080000c050050303d07090091500341460819a01c1c10901030343c50048440102c1c85013486650004e00c28044011014034084031601072140d40071813000240c034a20707030324132000c00e050ba0288510140b02c5d00950750005419641c030004d00c030905180845074824080e80004001e402c98a800f04011074103803104c07900c60399403071038a03150452143c0c130b8400d50301000001c100301c00c1000e103900002d0301c1c0c2da11341c0d41c00904a403071303019242d4180303011345540020411250000300042c1094104042d001c5441c80080355041101000c42d80c407500e00050f00083e40d445845409660400740701d44030001c83d090f48001022440e5444110292044d40a02c40125841c1c00001c2d400e00d100308119040851a90010707120381020704c0842c1e0100354165400ca100f40101c803000a84a0f02c0f900400c2410b04c0c4024071520301074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 549390575 1250 549389325 549389333
    0x1e0609050408040b160c083412020402040801020a0816021b06070f1221060302010c0305030405161503180308241917030a050d05040201030b090403030204170c0d 71
    0x1400030100902e840240c2c0a00000240202d0b80c10070050100000a00400c030503400c00a0490108912300303110b01c00903801d410402c00da00c2c03032014102d424091f484c1c0000740071400424040d200380d802540380e075800007611000d89503008020f00c1c401c225000d00b210b140800344a080340c541070b04130240001072000c1003a881c00351034500c0c001c0484520503100d2800351640d40e40c4982907909075006050108100302c003140440b001404003400130710282c2c1c604005260a550000c0c0545030400f8020303041000c048001003c00c48200300030600039000000c40c004456450310000b80d070350603400f2407400080c2841110407101c04900c41e0600c046038181c41d40440381d03441d030190040c0c4040000d06240c6801c0380c2200c1800f240c079418001d00400404e0381411000509203907000e03606108074038000100b0740c070401c40040d18917402030540d881008800d074007240603292070004a0181c006480c4465105803c081030004158055005000725400807180c1c0d06d0310341f00d010195403600e00d02c000700c42d0000c1045060310005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 549391825 1250 549390575 549390577
    0x150a090b0d0201140d060905060307060c0f080705071a09040c0833040e0c040e0f0318120102190801050a0f0510171003020315010b0901030b01121e0609050408040b 72
    0x1810411951345c28020001002405e03284680d20040300d007585ca4060041c14203090140e4005407507036050405080e1004c0d5504084641e480e84003a00020002c2540c00401509101810040000001201c0d082d10401c00300c41c490340c08903d0703452080740341120948481d8001e006c2c01d40301d030407203542d40c0d005080a05d5245601400c00c440d00401c0e01c60039103a04030181c5c0c41d485031036129003549000b803a0f4020316009000868840c80e00310704066124562980c1c280500000303c40403204089071100c5500401804654890981c1030f030500154008101120320005a01c1100c900000c184e403040c5c12640e917001171100b44513840c081c14004156900c07050029040080150303851001c40e103446017149154210351701148000741c030f05091a00541500300b003946420444007074805014149004954900000d0116900c9480007071411f0648540d4401c240d07078000e119414480000b01018440301940c02142044891500d61928007513192100204c0d0741003042c82200c0c451030b07101020728502800e02900c0318103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 549393075 1250 549391825 549391847
    0x6030e0d0f11011404060501090b091801090b090a030e060a0903060e1e0a03030501060302180d0f060507090905100302030a260703030e190519020d0803150a090b0d0201 74
    0x1d00542c0940006070000c02d104e0000d0b98000d50407620054201441c10106580707041c0c1c40450009c2c00c19006068544d183d004032500800803c05407104840807001c02405010240005005203400b60100800c0050104441482030320995130013980d18080800c21800d8044c00401000107a0784110070f10001d89075a0141a15a5210049901c16040c4241c5a07215513690600c030f0841c0e80001220608258050080d00e001d04040d04003542045e070070100f41d0983d500840b012904c90712140e0389000c00d2000c1c1080a08841d6013064023840309207403001014018042e00e02c6402d500502d0040000ea80700c071103c0b800310541b980280507201d52459038449041540c52004591090420302c605c1360300c1400b0190041000c60300c01c1d140400d41c949100d80060030b200a50303035003684e01c480c1e03c0741100000c0d00c08600701500c010141104401c1c02c6440c0003040d007071050008010030440c0c0000a1200701e00c075410a090284508442084969407900341817804e554040e643c05030045014068200190300440d10010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 549394325 1250 549393075 549393077
    0xc081b1908041505030103110d15051518040c09020f1b1011070b0615090303070506040507080d080a09151406011e05030109023009060106030e0d0f 65
    0x25051a5034040500340045600e003190408000141040b0040ba180c03140c82c0003203a40e041407800d41d0300d1511484814603461084a1050310303480c6a03c4100844d4420140000c08aa8402c2205141100c105040900d039540031a210388000b014420600c4c40c680001c510644d880035001700306030b00d403082c860080c1d0400c03503007071500c40404d00102d01e1038171540498031b00d800700541c002e2500b40c8507c00c2010440d40702c11a1615003860410020000c02d000407407594100d0800c1d209150b10441c4a03100541500840034540c0c0e041c0000034083c2d05000c40000c099001d980100159007141d5600c0c11103960307800004d00407201040004000545460465101c035a940380140305080720144039002e040100c400358100f4000f601e16800a00c0f0955034004002c88020784100007810020511200c041c005010500c15441083d0f0000780107550341021078500410318801201c0110703041c0c011803040441f410b08a491300180d00c242d400000d41c0750311031700400c003c1c5442d55001d001e6501050a0407074880b01400c282d04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 549395575 1250 549394325 549394333
    0x6030307111e12030414040507200106050a08010923060a0b060412030503070e0f01020304030206130e0c0a0e0a1520030d0b01091d06012114060405070c081b 69
    0x40080d100c0d10f101c041030003460f2001d1944d49040c006840010107030172120500851500303040190480c3c0140301c03491001d160740c0c403079100000c0402825000d0051074210507003042c0585400240000d054001c4074078070380f0400500b0806441e000880b00d00b0300500a1101969220300041154400954030506010780c01038481846c03d600d80007003010107820118201c000a000004014803147d01203042c14039503204690b03194015800c100000d681e4010b5000103440b072100020041d000c4048840ca01005252000e64014189082d0780f940210f500101c200310081030041001e0901c5181859030042506c02480e041c031124002260115400b0071001c1d0914481d07089501c0d03107401c208040020349000b9200c0030000c1550940c0e50f00052006036280d0010098030b00380d03070400f040154668907a9a2200382840c14081418501c44035005c50400100291081d614100c00a0484107050010798402e05050f03606010a0b142c0c0d1401f29550000b601010f8081c2400b440031122050b0141c0c4d202400b8041d40c004c813 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 549396825 1250 549395575 549395629
    0x108040f11101106070f02030418020d090f0312020c0601030b041a0a0b010e04061d040c0f080d081e06040e010b0a0b040e0f01062312130203060603030711 68
    0x400c4100900b0024400455000780305004141001c010050340303c1c9461070903102c40c00310030401075030742e000354022105407040c103c0710064400b9155050f502d102c02105000e0020400700e0401c2c00c0030206520003540001d00c49804221031101ca80201c403c0c4141e035200503c0c25a2035034894002020001e00100d800020040c00341403403607064840c048c0620030301d020000724103007610000b41543c1c45d5225950701079403d01c04200902c0d1700f84241c4032035600340300c0340851595a0310300d41074003802c3d080e401c40605110b0001e400b0130540000170f80b503008480c0310b45890907071380c950b40310044403045807400030311614500000181860603c0d81141d5408580d240002c6180c034000c600142c01c544c000c4c1c21805041c40003003010001c801c0032182c2e442d0450109854484154108000180343c0140c1980000d104400701c1403940b00103122004540382d081401d21244001e0400500032041800110010f030b211740301c0c00300401d40c1c514010081700c5001d030344020711000300b03003085003030107408801d04111f807c07080001034203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 549398075 1250 549396825 549396829
    0x9020a03300c0201021005040311060132030a030c0201031503050c09060d02240d0212040204140603030901080a060b030108030c010e0a02060f0c0f190b0901020304020108040f11 78
    0x2090076210031440201101d9119011610101d10342609850070000d41c0d040308000350341c000c140c00c84509020b01e4003154079502e0b41002d40b528888004910719030703c40c0e0300001030025a614905c40619154004070040b0b0084864108607801034850329550540285103e40f0009000d9000d03520300744e1040c10041200442c0c11030249040900368025180c5820850780380080746840101658801011201050b96020907004501510740c03091540c512070184240d0018808811810343d211800ca000056580c1c2d05000340c0204d011000343e070200e001d6070811514042c15802c5881291050300058001d6040c100203d00455038003a015042e84001170740c4440c08203500c0f20000042d07002c0c01d4039000866880c03800842560840e0040d00303000b407407a000540d0910059440e00104d0f0b4903d4001c08140b5111170005a8082c04c2c00d1100701306801d540b01d52580c3d1607603140400c4002c041c140c05440b040ca0250b0b6080000b07401c0c0e21080301c0090000348800b001500150340c1134a8a0041d500503242010a4106040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 549399325 1250 549398075 549398093
    0x60315080d090302031608060c1e041508090604150f020913090c0b040f060e0111010507081b040e0109091a0c07060b0d1505060d0507092c1009020a03 66
    0x4440000035100c100b040c030a40c00c1c1002116513240644a000f1540c40c9000031b040c0e01c44402070070209204174001040740d200d8034004550904224000d640c0f9607210b0381c40407941001c07003110341408041401d2000040107030401050541c8070715040701c0015a2607a40246040c020f0181d0004402880d40c00d0101c03034941c0d01d0f000710070712800800317242c001444502410b00e016040640c3c0d020011828040200380b05490215064504503840c1d420700313400d03030040c80d001a5410380284010088961800d01040b1003280d1108856015041181c800c2107500c01c2342c022483c4502c1580510f2403020810301c010041480e0590150713200c94050204001c00d180d61440070801d61005031a1071001c1c00e004a207403001c0c44124400c6d4a0131000442b070780700000340580d0325008075484000ca5080340550f41c03000a580d03502d80b6000d031051598090300341c0d2101b40d15402c0d68402410040300c0030002c151000e050070034030008099031107101001100184205e1440c005808003501d400101240c03c04545100080041e081038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 549400575 1250 549399325 549399343
    0x7030b0d0b091e010209010e03070303020316020111012c010204240309080f07020a0e090606090a020c0d030e010b03010b0607060e0c210f0102031302091e0c030f060306040c06031508 80
    0x3d000540e551410400041182d40181e0b5030030f201c0d03002240f0030030000b0b07000401c80f450b2030005968a400c401c22400140c0f0420b1282c00d00c44a17950a2448410005c898581c2e032085400390415007070000c11208800a080b401131b0b010f08850044e410620f003030305045100c00d20401807014a80032600c14050343c1c61244640220612205000d00407607080214648068140f018000c0b5205542c52031800d064010b6849038081d00b054040d2603080b01255000c1410b80496500c40064811941000700c040002801001001c0d40181954a051100016880c06008220f11224003c00050a011240d1545401000d58807884001807040849030010351b103e2600600001b6840c61505102c4206150250704081114809491507481041080340c2c100d03401c480180c80c15016030700003000b641c5108603000d003059804140e00800241c14104810b0080440c001c510031080340c24558060b8460109241d03540105580086c502001e45034207012403440390b400f075030446c80040030240d152555000c3c03050804e8094 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 549401825 1250 549400575 549400633
    0xb0306060f070f11091902070212190b0112050303240a03032105061018030602040e060a06050405091519180b0105032703070b0c07020907030b0d0b09 66
    0x150354407001d0060a01016014031015910421756191040d9a912084514220395810a1f0f01081410030b40d143d03441c0a000000c8040d00715502074844a144161504013900f045451445200020420f062548042c92081e0b500000075810341d111074070501c034017072400e042051250540e040005169910689048010342c003a841e00c1412544e49500035041d0380b40c1c0c40f08460424217207028800d5a4440c50888040741c000b91402c03640c0800d0102d000c10035a04581e00143c64140082804205021005a000d024a10480d132143c0125034680d016a1a80240d104169001e00640000782c1a00384d06102e20580c44802041a001034400c0e81d51000c1c21082a003107a012412149200041c040c4544100c3d840c2c00001d09003641140b41240c1c0c034528402801d68660700c808416050391108040401c1607800c42c035842404001c2c0703841d05000d1807a40c0e030820310003a0311880e00b44001ca1203d5019108458049101400c0044803401e2501e8840c1541320103801e00055114002001607503d2091a842d0030046030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 549403075 1250 549401825 549401843
    0x20040603020d0b101709030c061006030c09060c0204180b04110a1d04060207170c0c0f0105250507050301090b06040b030706020a0312060b040e04020a0609050a0b0306060f07 76
    0x32808404507445001c0f4a030052070080058107001e03410130400c2004103001048820596030f0100a0344c210f001d445548400c9108020074005048400d40d0200306072107266400b0400b40103078603002c40d80781216200c0c0300003041c258001180581480c2d0843c0c4014003603581d84c2c1020304050354420030340000032101a41d80751000c0c0561005460401c0701d5500404d16138070305070398001c16604825040f40000e032009007043c0c0d000500310700b0007800650160301c1099103a413603070f12449034103503d945a08622203113522403501c9010480d1598000c41c107482003001341001440f031120320300c81d0710340e034883c40b40378103803054480c500d00060f070b0380e6003406040e100d180710b02103d1400d4100300c002e100035103000a43c003611981089000740000c507800110404926010b240031a84420b0f41c8640c07200500950300003182002d400540030500c0d41c0c0144803280920710990354150325540ea020111050f4030503008595120084c0e0b00100103003601c0d132020f5500184001c15841c5441900006003145070b01515003100d007091303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 549404325 1250 549403075 549403087
    0x70b0f07031409030a0c0c03050f060106090905190c02160611010e0d0f0810031505040b0901200703020111040306060302090108010c02070e0919240b060307032004060302 75
    0xe4940202c2c8100000b809081d403480c20030f1400207880f40510111142044841001c1405110003145041d0045411000381c5a07060880c00181d44c443e5400d01803040443c1054100244c0c40034030380300d0780d03118805901e4014107240c030301c491520203001c0e400341c0301003148a00c000c1900c41f42d4155802c080100070946886903109407925009080d41c0000c0d100e00d01c582c0024441c801c1158000aa202c040209440e0840c2269940304100c01c0f41c00103034001600301c150070700100740d4101542d03200e60301583c01841041c03401e5448400f12820b0360014410004007100d196001c188149504000d8107800f4802d000202d9842c91320319200e0b01d142c105074000c0d1021900c441782001981405045140500b8205000740031224150101a5407031002c0d01c12014242ca076400042d03e00c0c4d50034405007090031612002c0400d0040241842250781c1d246441c0c103050040c4a240001c4059150321031461592000341c8035905681d01c0b4441500185401c1d14007207161101800b04015602150004101820f901d44006131214 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 549405575 1250 549404325 549404327
    0x1a04050604020136080d021906150306091a01240f03021c0f0513031704080903060a0c09060507021e0a0314011a01050f090927011a03010903050d0c05070b0f07 70
    0x410100c0150300b550083d00f641e403444585010496001c60b001807004c9034401003103000d01100c1010b41d1010b00b0185c40d0507105410004000842c40401c9084240c3b0a20740e40c031040c1003101ea03280314081c5200e81c5240140f210606004110490058520f41401814a0100101c03034940030540b000074600540e0b1103100b0540b0700b066128031a00b0600590311400d2042c1c450360050840000c08100150410702c544c00130f4208485c04048034640100603082c2c0304c803070810380b80c594041c01e44207204d040410342c2220045601440b403410748800940060055052200c0d1881400c5a0160385d090365800c03416118001c0040ba00113214400950035507000000c1c00240703220480a2049014203070f9040040420811500780228401d031003940c034084031903600c2d544901d05028001c5400d0440d181c5249640f40c040031076600c040d8802c250804101c01001421990001003508942c01810010081501440307000400d0090350b100c4008031005041c0240f410106480789070b1912001c03140c0608005c590010000b0316 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 549406825 1250 549405575 549405583
    0xe060408070f18020c0a03112415011103070b1f060801030b010803130b0d0914010c020f010207120810080703150f0e07060507080d0f091a0405060402013608 69
    0x883e0303480b07000c504140498000b152685a41c4c50060f04000450001c1040c00c1020702110b1800e144034801d400e484200e0045005650000b2a20400203540010340c52400b540508030220b403080240c070180d403403d0341d180c0e00c61400d1400a40360103481d0140080c1b08401541c4040c5803000382155860b040a43e600d507241210b607400050b00101709d41c0d0000d1000e030303100050184010054a2240c203059440e21000c040000007008451005000482411400302d03016106500c0b400f609a820307801e8851040c2c00700c2c0428243d10602e000140034030740c12030001120340c2c45a40400d0300900d60303d0b0801c002d142c2ea4141e0a1030200260801d07a4022405510314582c214035114081c005002e806050040071032030b421039601c64540d03124440038000005a8407007004101c0d005c807207101c40014810400b0b401c1d44800342d001090000c1044070030049109000720115841c020a0b489036901c507004100720f5507507600445103814110529034058020036061100312030304101414220301c082c0050b030b9440345003423181d03454 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 549408075 1250 549406825 549406859
    0x307030f0c080a0b06061b0706090801060614030604020a020304030807060510081c0e01050405130f0c183f0b0601031e1d060108070905010518070e060408070f 70
    0x500d0b44681c141d40e0009000240c050303444002151b0143d120305034840b9081c0c3c0c1540580c8150400e00550401203031940d00004450142c1d04078100802280340c031001c0980d808522240300c1d001300c040c1031000407428940707600100071000091040e64140fa0340e0303561313480300c070b030801801202c0d100e4542040201050b01e02c4240001000390000a00015400c1426032403071503003001107201044801d581e441856402a4111001450003030500d07000201c0c1c401c3d008004204048403d44501e0900d206018568800c081072100ca1a944000d41641441c0c414050340f14015190012454001d6a0450341e103126040d20888808407940601c00e406902490b04c0d02141c48020310b040e0606140034844404101c948540410008a0000000b040007410200160f0403000440c2e001040c0319000004c40c0c600c0001c61036204880c1c018070240280d0340caa0003080034041e0750500c1096603118003000150036611030800d00c0d255501c00b40c49140f9241d01c03071400d503040c02d000350400e40181684207410440c1e00101118054 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 549409325 1250 549408075 549408089
    0x1401050a0b130906061a0310050303042303160e040201020606030d0e0409050708070b1306032003060d08130e0a2a02010f060e0a181713050307030f0c 66
    0x5255030703400000d01c540c521030b16103106140c3c1d1401c208007041141e82c440c1000d0240d00b0040405082040c11064031580304407017040107110101400039281c03c0c00401e0703c0c10f0310219a103202007422a40d003180741c48550f401c5035907414442d0002c000d00c0c140351100b000001c0c082c60011f1407110b00e824000603241c120003806090080c3c0c065250440c2c800c0d4001d251081020084030003080b070040300d0616520b802c080e13800c40c5000c1d0003050000110300b82568010030100d000356440510303980d940c0c5e109500311001c4003121502c82130304007175880c070901c000b100840e48503c0040078101c03004540d4480d0241034201055248141c2030314201800324aa808400b03691100c03a40380244407060b01880100711003540e100c1c40910720307001d0842002c50103001703400440003420300c49410001c040e42e4035007540028509688410405103040780c01000c81100074004a8070580002d41c1c80725441c412034010041da401560000300e0350101e0310010450f5503050022800541c0600c0c10801d00c1340490801e0030380d03000f480e800300d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 549410575 1250 549409325 549409331
    0x81e07050a080f01051c2306010602071d04060203090307050d231309020a14070c140d120e011b11010801050901030c060c110d12030f151e050d1401050a 67
    0x802c0c0d40b00141c1b2a402c0081070402c3d0358101c0c07645010241100c81c031812000303409440124204403000001c50504a81181d800c884030542d4800c0c1d10400050400b03112292120300a0005001c1241c03a0000c540100d040c0342101e02d8150350351159070034213001544c1d650004001040c0c0381d04410b1074000e1031545510005541d440d01e0b0032091980e0b81082c5900c01c00d0901074021a03201c4009004c2c0d503100c401c0752070290080c2e0f039450707042c989100301401c9070080344c80b00c000c0c0c0c1c0f18040050030710454440c04190b10141e0481d01602030a825a034464091242038101b00c0507100d8000e10401d400e103001e032140d2041f5180e130500201100050301b50841600414010801c0740c004102082c0000d807448100c40990404410302e1005003048031821500c00100340d000b01e0100340c0072003042000c0700000c20a9140e590100320110505600c0000c2c1c450126041910f640140002d004560303e084500420413251600e0100d0140e075940850384104d41c0300f80543d000400b813080540c00b07480a01501d41d020b40301e01c40070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 549411825 1250 549410575 549410579
    0x27040501050a1a090604090209010308070203070b120711030f07050312090307030c08030621100c030501050a05130e01060824060a1e080f030d0b0301060f0303081e07050a080f01 78
    0x44404241415810b44605001310204100c0d8459600500c07004d0380281080c4819078590078020f40560050008030700078852848001044889a401d4070f481d03510a451031115500c034280100c6205241c0080444180810003281d113010103c1401000402d204401858444810002001e444180100900a035800400041c000039500c0031840700e60a500150664403510f514011131119840c101d804148001e11000c0c04074641000940340c00325078011a018060300305542401c4043e283c082c804c5a4101e400300c60f040c03000c0d152440d00c1d4078241120076000922421031030b60310303805c1d151140e1100c0b1039a08040990b0100040110440e08a03060340e142a041e282404000301d201200980b241c4c5e441000440341e5540010302240c0410001e0604400700d928100c10000140e0300c03a4043d0010781c90051401c030040e1001d09045c0206030841c3c1c01800e2200c05035103951070544e12418020720060720100404c1c9404007001116030020300a201c01d503103d94849124640c081c1107440d020300781800b810a40001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 549413075 1250 549411825 549411851
    0xb130e0610151107030501060303171513090501020d060609050102060a021903050a09050d0f0e0405040c03141011091e09010611070503030708090405010e220227040501050a 76
    0x40524a0651503c0201c40302c0f402c4942c1e04001c55900010140d50915130000181030303001124140d01500711307115030015111a400c5421041c404022190803040c511500480c0300031542c000c1171860300450003d440c0c4425006100d0032501e06030003000108540305d50074071080d64101300c141d40c4200d100b08210300e029001424440f030703e140c5034901803c00d51502c0c0026144012900586503070365000c070445040b030b1040140900311800c4104807034009003102c140740325907242070b014450084d508106c0141c402403c41c0c4030590406002d0255074038500c0742c01d8034503804490030b2180d40c0482e1203130b0400503141c070302c0b020400601700c59090500040315080010a074032666510b0b45941111528100841410b26070111203007022140e5000035854000031901406002c4650010405940e007201c0c20000da03078850012403100c040c1951180130044007040c0304c607180102c0c558072000b1180001e1041d005140c1d016078043c819a0aa980f85000c03494410a100400c1401d00039650002c070ba0141c00d0146e0560012 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 549414325 1250 549413075 549413099
    0xf1401030507050d0b0103170c0f1c090f1811030a050613090201020d0c1b120501060e1003030e1909020c010b0922060b030111070c0e060f0f0102010b130e0610 70
    0x141448ea00e032000c544600310940d0032520001d4205040d50440100c2101d425226003910000c2c01e19101490141c0003210720801d0351405860005101c0710010741888084900d19602e0710300070199555070f000d01e40304250319802071849511a844041201d22b0710748240408500040559070f01c940c2040c3c044030050381c02041410701440140b0302001410050f0031320381140c92400714a000c0c6d5508a10300070854015840182e04207030300540c000d11101c0e03550f821400d038118003112242c0b0001c00316078090001078461042040150130060140f0444001841030440c100c0c0180e01804c0201c1d40065007000c42d400038040c15010034412035600c00f481ca00b42d070016900914219507601c01c6050402c0c40b60802c25268001440410080c0007048078500c0746c00d0591325540450029946e104c00c05000051354011000c002d44501c0014102c1c05103d01404240010301c004c441d42141595211034280030142ca070b51106031a01518040e02280c65940c840350350f800c2c031001614540307462038032910a201d0102030807 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 549415575 1250 549414325 549414329
    0x3270201050a0c12020c03120c0c10050f030a0c0e15040611030706060b0304031112090d0f390503030a0c020117070314070507050c040c02010f1401030507050d0b01 72
    0x7080c060b075200110b074811550050700503002007031311150006010150340c0c005120902e0580c01d034100d544940f080c8882901c503004040801d041c40e84125803041c0a8185080000980c00c1942800f41c14111081080c610a800850390980d000d82d8035010021125844a82242c448805a8003806145500c0b141d4410a100e207018540602c000f52041c414100f808100f152b00403504400100001a1184c40310595603000b86c03029800640b180700401034103103000c510703400c081100c03c24440c40c0c49a0402808007880c0e90103825901410207042210205284030852012081b8461860110207080210b4590035141070172202c00e064146081880303503440010460b507042e000750130441105071030380c40101c07215028010720030500d541400a00180c290540c0001001d01e0307022012031115a40d8140c101d8140c000d464015007164081501d01009092031b601c1480718035043e00c000700c2c0340154220100161880c4401242c041c0000000400c2841024018517015000071070380da0755010419152a0b4501c0c03818 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 549416825 1250 549415575 549415577
    0xe061c0c03030e0d020a0314390604090e0706120b0a090504051207030305040201030c0e01021f0e07141207030206030f06040f142403031c0f1b03270201 67
    0x140f50034003403590346100030401d8a500500504869440c0d280821031075250b188401e0443c0f00d8034240c124510100c4144960982003948400d10343d4a00803c01c642d0b226174041015048102080b001c51448841d0154a0382844003000402c43e992400000074542600d80f06114242403900044035200e40e221845241250b044560100d11034845040641c20030021402d0303242503c1001804408058054004610543c001d03281000381c405501400c3d0764a51620140d04d0058200210482c4c0f448003c02038020030b00c00b48500080c0742d140f00b00c0d4107480c107582d03500002d81101d00c59140c250f1a10344400920f11220003000034140c080d213141d0204101c0c1c0405080236003800340d810b001440701c0e02c0da60301c02d201c00c43d5103081c2440142c01d680b0000b200da0100360340c001d1038501d00100a000145808005240929026005510b8018070480c01d011342c124090310000ea40b0344615480c10341096501842c1900c00d5081202e01d014884c000018007202c8601d290b40303000b6000c5800714540200b0b5509803585007502 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 549418075 1250 549416825 549416837
    0x7020c0d0804050415030c050303030f010308031302031608010617031c3917060103202a0a020303041202031009110a14130902190e061c0c0303 63
    0x500d2038006070341c0c0229000160401d00c0c02460400c07008a4000d09800c41c1c0c00780c64407000d110384480038141c40b4070045903108401d0032072000400001b140200115882130150350040c0c070300643e60740040e06002c00368102000c4d100743e074403090041c49003c1c0320302001070500c1140121400c480010309505d9018043c1003d612101d0070320441008c410a8004041800d950030300d04240d541d16240c41d00510001c1000428074241949034052540e001d5003000d0042d20060000c1c126a585010044010300b100307150034003802103030030214102c4020082c06009251500c8051400300b0091101002d0f44440032001301c1c80c142d000c0000b420258401000b200c1c155820f8004e01c552082030350010074a0460340340d2402201d0307841c08a0134000c0c401d400f07140711807491049902c01011680d070a1201c4d0700e0100b6140a076072100042c13340d000c00c905a503000e10b550a00c0a4001d41c40362992400041b01110389501c128008030720201081400e140842008845903034889a00240d085a51508803410805020041c240030f0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 549419325 1250 549418075 549418099
    0x1d030c0c270c070b0126062403010605060705010f0c0801060c020402071103030705160b0a090509181506011b0861020319110a08060712020307020c 65
    0x2451908444540307420403a1442117580d60380242d0f50a464007174200c64202c2d005032080902d0000420b0482c000c040c04c070801c400e010812254a4580c1c01403021245d4190b58603440043c4076100c91028120b0746008800004220403000c0124064584000c0c4280c00c0200d03000050140c01e800ca45c03030b4008a501034600603100d00340d40c40c200c400108090101a410b100125405040103000549400c40f031400441400c80340759a500c601480b8060003400801150302d010043c406808e2616074503901150700c00302c0b02140220503203440c0c1403406c00c844a44c483c8105a00700403840d6005281000741480303522100b10002c4260722102c2041c05048100c9000000c08809001620400c00261801d01008034101d106141c9042441c3e640300c610425010384010000c91b801900c6501c0c0c01c142280b10380140203444100c0320900006502d92640f18100e802041070300d80001c1c9510b8500703091014100f1080149403609110002400b6908546036100640340104200410345601241c0041202e0741610160f030058 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 549420575 1250 549419325 549419341
    0xe0f1f060804060b040e0c0a08010b0618040209060703050711060403030c080c070515040e0f04020307170109080414040e0d1d031005042103060806060f041d030c0c27 73
    0x4200780c4c2d1025072050400d4180c8107482c1c00400c240360103200845004012075602c0d50400c2c00c0e5040301d004181d110000340945000d403e8008142e55800100410051a10100e0800102160070240058000400c0850010304100032079407401c9031090304880f41800c00b49999001005909043c038000c05c42d400129044500c400c00304100009820000d2003008040019050008550041d10425080070b0918002c03440015040340d920340915000303400f0741000350500c5990100720300544100c1019640e20781c0c40303a002c104001c0191019010f4034407511003c0c02c50000f0842a510420f40c000060303080805d4442e2620340005940507010700c518055004000b100c0300013801c10442c4116451994200000c002c00c12000225820b07601030b10540c09042c00e11a0035003103007210140c0c005e00c181c0e540f0032400b2604038074045803480040c8000030800b00d2400007149020210341d60314411800b40741c3c808940116005000d0041441d00902540c2d20445100b192540360303113800c1021040e43d00c0744030a0001c101c00b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 549421825 1250 549420575 549420581
    0x17070c44070602030a02012405040e030c0109051e160509070302071b0f060219031d0d0f030306060e060301151803030e010f0f0e09070e0a0e0f1f06080406 68
    0x540c600000d03100307042ea60b0403019450380d000c6081000154600011003c10000c501c64100d200f00c007080140c041c05040c441404000c2000c0802c3c450303148420b10001d080c03024240170340002e951242c0054402c48010721491821044402c03118a40ba42020301d0080c0c030310301c0c0c00d200f00c011200c0480d0b880c0781a40301c0d0302d0194000e00c20164043c01c440c8a60f00403520441d032070501a000c0343c03240507007055440e968900c12a12034200c1400c10b25000200c12403440400c1c89841c40302004a0400c2ca01040030b0421000101e410511100899007031241c030711603a0038540c06114410090080341800d40c00c1d40200400184e151005000c1c0400718449444109032241c41030781c8aa22440c52004084001a240e05024141c0c80080216030b000840700d0301030700900340c0706541c01c462546094640c0c0d65500f42c0a002c000f15800300910302410801e00c180c0c9440140d9580b1032180040902804c0000c0300c0c04c010020f01084400181880f4503000d07001c0082c0910703012400100215007091405411684441c901078002d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 549423075 1250 549421825 549421949
    0x20f0609030a0c031a0106050304080a0e0d05010c021002030c0f0c010f0e151612050601110111041a09061e040803280e010e06130317070c 61
    0x1d449494440310402c4400006241584d0003080030884400c00410460504d1109008100002d130040c8049000100603030058010740d40d075400c1c65020f9a148102255094150305800c1d20309a468152005005405102c4100903441c0711205600c2c40c48c000700e00b01210303c146a00c40000311070026040e0108542940404141508204140b02408810310641d560703903000b00f0940300103009003000c03692940e02c80c0006142900729489040320305210719001b60040034014840343c1030000e890040042e02c10281b1940d40c081c010030300c0d1652264207113024691000494000e03035a01400c100804000340c0e4441c0d0a443c480301d00c5044c0c862060400c0103140c0c145014503802009a80f00105000c05004804410300b041130800e001505c042a5a0b4242158000c5900903400e000c03401c500105091410030100030581d210720310300320012035a82d03607541d03148041ca81101002c19900c04940001001007441e0400c000740614075065280c0501d1400324440301031511507281021007075401100c10000c588080100c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 549424325 1250 549423075 549423079
    0x70512010e010c03060531020703110d020601140303030408031f0314030d0b010c15050c070b0f01030218040305092713060501050a12080a02010213030f2d020f0609 72
    0x1000c3d0010703025000d41a180101845103030a81407441c40120301e01c0019600c060485120822804090680030003984201816010440e000400c412042c00811500c1f0020001da4010102d540c58a00c90f00000000561840c2c4203400400c00e00010501010503260410614425040c001c6403000c840140060282e00040100880f55075030914804040090040c0d08c01d500c105000d0010b60600440d41e0320300ba82001414a04450411b09102002d0f901c10343c0d001c03400b2101c03545410350315198414080c07421100c540c07400d109440144214103115003208044880b81c0003080903820660740c081c1071800740f940258011040722100780401c0f01480c142991481803c0c2298065090a001c91448851564015541541043c00000b002d0411403c0901100c0000240b03400e450b081ea6142d44c3d00380c0c007840580c4115034003400ba1800c0c1010b40303120b0380f000710300c14804140c0741d40e01890b1508603295801044034002e074225000b401c243c0c08004064000380c3d812102082498103070300000d000790082c0440c0076 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 549425575 1250 549424325 549424331
    0xf050f0a170a090533071e0c1d01032102071401020c130507020c01110c01030213091b14030105010801121403040909110603060a0317090301050a140a050603070512010e01 75
    0xb805e1030010f0a280000c02d103001c1d41c16500b0111201081d0311882003050060050340c9110b404401e80181c14981d140080c4a042c2c180c0318140d88120014020302d040020f2007034005200010400c006421a1004c0c000d6803810828400714056503007c2d4880c200c0348110000d2841e21036180c80942c0c8288451007075000300400010384134500c1641c40c0000c00c0b0844200d400b52255034180100c82d0f010301d02c258400150300008000b045448001100690040c0d1039840001891340008a0400f03114040d03030380d4001755003040c80000070900702d0003405022800300150001c00d081005000716603002001c6810750b065501d082a402c822850454228000405405198040820003140241c0c040e001514014011841b170035410b0810001c100041c413042c1d41c110f070300002c08101000043d1030881700f03010405010301c4003410403240d0804242520001c4564907c02c5540d01d40040307070034901808498120003900c4007040141f400a020a85d680d2040c02a5481030301e941908403840f02c02500441a400c0e111310081c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 549426825 1250 549425575 549425599
    0x1c0c15020c0318190f150e030111030906070e06070611070506040b064609020d0b010801090506010801090b040e01090c060306151e05090d0f050f0a170a0905 69
    0x11020451051003138803866006103221214811540c5020584010b04d4034070740128a400c4210040715400c4484105200b030040f130f01602d6950038494207845550280c40e1941d07a03d010f003803c5003421402403003041449900b480039101d6445e0103040c0e0305900c0d8480b8000030409410b005010310350013403a40040280c0324070000c000030020000e0340720f4000c000c151003170902100c130703504280c1d0b980c1050060546581c00c01d45007440410058240d450340d001402d80d42c00070083d2164000c00683e4001210300d10b00c0358070b0301e0320382503e568801d44082c01000c544800300864102040000c0c001c400c18400d02c0c0c025900c90410b9641d50fa0f4a074007106d65120b1010080010300105c1c5030400341031096110300c4000c82d00d441400200c440c003000c04a282d00d82c1564903500340d03280c1242a0302800d0007061603030003001410300450348241c0b03803942c400c150b00e4001d41c0c90310400030032884c10a2034031400d00d050f00041d81004c415600020101150b144038022080e142c240c80300d0b0f8641c1c0450348100c00354403c950000c14003880b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 549428075 1250 549426825 549426847
    0x10c111b090a090b1303020606010e300312070206071115061504030f060536072706050406080d051602041805060714030109050406060e070201020c1c0c15020c03 71
    0x4170110030b84070340c0aaa403a80e42d4200151981c0803550700a5800140082d402c40c454120f0040e03940f504c8034200b494100a0703d98000c0c492864008520700b601010303006080c800940e4040100d00d0703209640d840c0840c1224007200c54036413a5859201b8999440707181402103078040c1c0d16107a820048000700042c0b0b6850700d9803414074110b001003891003620340524000200b030b00c5080040c0303503002040548402c0640ba20340c0ba502408814103c3c1c148803014041c0c0c140c041904032040c40010005000703940c141c9140701700314058030212400780d4007291041749490300401502501150480f143c4030341d41030a0b9101c04204d03909488003405200f009510a2603c2d4400034140481c9044001980c0100101c0d10b055480c0722081d5805901704c003209035600c0c000e0004001100300b503001164407512489022825555900c41a03400000603119100540d40100381a04004010462402803504140d24289402100e030350140251225080182034641141d9417220b100c10340e90101c4000d4064402161f41d80c10b43c03080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 549429325 1250 549428075 549428101
    0x906020c070513020f0327010f090b070201060e01120804051503071202040e0103060c03020918060316120f0203070b070f14060609070e0102011409010c111b090a090b 73
    0x20b2512884429100300003010b403910030f68060328503082c0c110703107507488000120075200340b8051030100d00a05100824442e0000b8000e81c41d10342c1c0810004103d0340424980030008200c001c1044c011a0b00d0305e00104212000c2c801c85a044490800c900000000d043c18428524807070781d00480e810400e11100180d03040421001548160650341c1c80c03244a2000c040031805030721951241100c4d1161785001440480c000d503100c80d100741a107040062401c40314001282d014229400c2c01010b110b64003040111398281800b8401e442280802c0e80c2c400c540c107000d2200c19852040d00e01030501e811210040c0d0440d107040114502402e0356102168642c0010300d400580c902c12840c0c200c0307401d0101880e164580000150480c06500c00514040d595510548100c5103c1200300401d41190748038541c282c2854902e0038581d00840c40000080f694004410303020303045092001d5000829485501d12016030b0b10b84007819038814800300c40d1442c2d6904c0b6110083e01034904402c0240c00309205805000307220074000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 549430575 1250 549429325 549429329
    0x601350a050c0c030403031214070c031808061302010903080c030903010b060702030a0b04060b10050309060106090305120a1403010605070203060a0c090b0f0c0d020d09080a03050d020d0906020c07 86
    0x1080c0a140d039000500a50b80c000c24502c50a40c1e4000d00c814400a4043c180d1591007141c0c09000081300031380012906030708002a10288080389140d180002030647c000c5900c200c0011030619081c0851600801c581d48041c0140030100080c050841c4000316131050061070700540d0010300c100d40f524062210903481e548101d507a14032a603e045506a41800c01e030054411068000307001d014580140d03141c1003c40710005100b01d81c40e6903640150a41c95481000d8202100f0441c0e07182503c9182942d5020720b041e1041e0000e000303010001c1d80410020b100082c0c102003c0352031066080d107800007440246d6030078009900d00031a8210100c00400c0d04c5134001c000d0495a07000301c0455200e84c46400402044441c5806c840300000c002207024401c20040170010846586002002e07407030300c0c01c071881850900c0101e600c0c0c5401070b04900b1002800e264040d5008022301a507001800712803200e40d402800e640320f02c07910404216004200d241c2044190f81c80741c030a2541200055690b0800e1070080c9489160074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 549431825 1250 549430575 549430591
    0x20705032703061902030604060b0310060e060408210409050c030f0709050f01110a0503032e150e0d02030f0d020d051306030504022209200108060135 66
    0x7000303030304054540024854000d110020001e000001021030090103540024003594105454000000c1c040c0e100c4802184100e0001041698441c00d01c000103100c0c100c03c2d02d6a501c9860144001e22100c0c002086101003049001c00e00416a040010342038494015503014090040c54402002001d0280c0c034021881000f551000c3d650396542d81d001034508003401c2c0242a007045c500644451954002c00e032045902c0e00404c1120381904160343d41c2480c5500032140e000c00b2103103105801130485404403036041550211ba6074840880d080c01c240d0901e0390195440e250401c0038500d962190390702da0000c0545910713009400c2c1c480d0110202007581e80e80c11139800c1c0740300500c11190106a010322030800d551340340788070100c1070f4111403502304214064640030b0700a0f03a0000e070030300f0501907a0f00c81e100b0b40600c0340000d402c0418660450708001300000340a842d01c103003030b00d40b219030142503a03403180c00300340e0100c0242407801d00600c0c00441d00b0a010742240c1c40c0c241c09404039812802a015003455980304400c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 549433075 1250 549431825 549431887
    0x14070606060e031506091306050c19020a150f0929090c011b051c020703030305010b0414121c0207050a1a0d020c0c10030c0f0503190b0402070503 64
    0x840b070103055540824000c8003989070f05a102141440c40c2c800491500304003910070b0300c0d82c0703107145841d213400311082502c2c2c4402100d00002d050502010641203100a44030f2030010f04039200e200e4075070031040055091513412580d59844c501d5019601035108402d00c2c1c3c1c00090620824034001c2d4850000d00c80140e0700030180c3c1c01100041d084800c0010481d00403001a95001b208030400491824607055001e4111079600a414821000c4100c80c08401c07440ba440b41d000301445481c60901a0480d141070b0007403000701c0c0082005109062280388404c2c0e042c6810b40710915071000304444a81001460005850415041144510708a500040d40350a88500700c4514610640e260000291803c1d82c5c50000584441407010344410f05042c2c3c064114441e022050322450030740340c1e00150102c0d14101900021035600c00b1300740840340d840002c88490a515051040c6541401c0d0ba0245130204140581d50201c0e071128031201d60390303c03903806075080154403e04580d10f6402243c030079503070a6100d011580c24489 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 549434325 1250 549433075 549433097
    0xd39210510060f1407021c121106010f0b03100321030606052802070306050c04031a010302150703020c06070b04060506042a03140109021b150f070c0f06020306130902060d0c1407060606 81
    0x127008200c1030304171410400c1d02900c003882c280d950304158100070311228021030031440010200c1c8081c610206251f000001d440d0340b5101c4010041c00329546e80d0050401c214041c0300d482009420460203820030700302c222442d60b02040d0200d04038546100e41c0c1006150a04120520812031152806401270b240310340450008070500307000e1650600c01c248000f03035211501301000280c4ac2c1c02c001c02041e8042c024030550b0f11121561021804036800f482040f0340c3e5100f158100420300c40700b8420103802030f80898041c0320081035a50041c60310004a440040641824180203c8090096010390340303114686400d00210341c1c2d10038a20009412514140038030040c00c155500c490746010035035401d04001c03490707244016240c0300d00c104044070f030081148060003440c100c081c011640d001c1003000e80d00e01c02c2502603513038542101841101403000c84411141e81c10203601d2801681d8500a4405a0070100d00000740344400b443c0407140206041c1100d142040001941c805109a0740c00c038009a9200d51580000a6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 549435575 1250 549434325 549434357
    0x2032a0f03060f0106050f1902150105010206091c0513032a0b180105040e0f07021b090c18060705030d39210510060f1407021c12 57
    0x10900312040c0003004404001801001e0040c2e014002031520410030354104494060000090070403181108e01503071080e4a92220301d1512200d4901504007840a03106a041c201041c07507680c00b80b4130038400f00c45d0450f000009000d12500548481484400b031000705991340b800d1020124210b00072000c040c1150100000080b0914500781046440000c1a540b400c202d01686841c40d11000c0105810442c04101c00500009050b10741c42c003600056884641da42461030019150101d903e04000e0518032000c440380060741e4010185a00c800341061132513582008030740600640d610702d00070a5100390085191402e01c040040600104060708000b040b15030b030b42d045c900111000389105c1d02440301c0040600109010440a002c807903040c207052220314014120421040c644000c8030340201c169441040042d80c5240c1801e50700240304d01c0c2800030007050758500003004440d0203808082c1c11440010180c0031034403054101003c40000d1003007881021024542000c1e40c1c6922121000000e2031305a003c4160707 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 549436825 1250 549435575 549435583
    0x26070203150601050d0b0402040f0306020319050c27060c03070618020d12030908040902130b0306030304170a0219092406030c11010c032c0a0f02032a0f03 68
    0x700416100c0506290141180c5d0b40a820840c940c150002c3d02408001081d660300350200001c1c602c40c08015840380303012003100c10f00645110100d16000c1c104414407481c0014401290407102e51002108240b41d240306c00e64882003482c4030010742103a40059402074000000c0050b20206200d15014041384601c806403503010488001d0195000300454001d000050a1081d0601214161300380450302c001e0b280c4441d41980c015501c02d401071030b00002c50396008503c43d002e0381c01a1007020141c6003103007841c2e070210381c0e20b0055014504501060100818681904204104038240e0007000e000842e045071f00000c02c190410700c00c2c0002c02d802c2c290400202203a034911003900384d01400107031213064604442100640481181c207000d100b645030603802110343c2030054140e1000701c3d4034089508400c00c0054500f488203032285074110080c1000220650030301050300f42c405900f242040d00d03442c0260000a00300101007043c6006041d2401405040e45240c4880c65503051049034000308581d41d05c000e042d11 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 549438075 1250 549436825 549436831
    0x9051006020105090712140607030b01020c0625022d090112031d13060f0f060819020307050c150603070f0b160302010e06010816120305030f042607020315 68
    0x1145c0c005000030700010906118000e1035901400c8520305120310640018144542565500e00180d19040d9810380740d40c0406c244a51113905a80e528502845100300240c0811401c5102144a85000b004010b540e5120424101245041c0048441d860b544c501400e1703142c0f42d407000a0094a83d000000340c60041200c508462603010b0301d410b242a0719684251303858212207a042e030b6210001d01d204841c030300810b1280c1c1c07002c0c22110700e81c42101c0e0b0810b5014403200705c46510020070020020200030307050350388400f15001c802c070708038001d070300c03601d8021007615035009400c2e80038000d10800088204810114050601400f000c3e0140c420722602d40d2045100c68440b07015000c1e410404104181c1241f240d00c0950780d495010b48000168429aa00b84605160080c0d00945865000b00165442894001d0040c0c00034655080612030100c0340e80d8014200e800000c0c0130f0003c03200088006024010700751000d41c0e030506600d400d039010b07000c80c024000c02d41d00500026802481101c0e2800301e101003000b403c0380 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 549439325 1250 549438075 549438091
    0x1030504080d27050a0b090c011409060922051807060809070509010b03011502010606090603090c051026010e0117030d0c050c010f0507051606020408030409051006020105 75
    0x3242c100b01d01502005040c5203d20340d5050494003080010f030910700114030b4441845030015007030216260400655000028041c0d4031541c05c102040e405030303a00040d5100c91125603035240c548401510300091424010741a01c1a00428181c0c0d241c01d17991000610030901d24203c0c58204003c3c5c94094580d68004501a400015075210140500c00b8600600b05190300c803040f0000c0380c5204d070705c417004101d003a0020303400700703c1c601c001000501484036558555589600780c0c0c4001c001c1145002e40007080302080e8400c91080c10750703c0700140140710000400c0d101421010305901803500d0b003c1001040021030b0810b098560010048082c000030040310100d0494001d10b4114050f6420242c00705081440480e12000b0b91008018059900c9110b0003090320b00402511540d4070342e4980d201042c00e65031006407039032115280500f0007103010f4001096a8a550100074441c800b441a803030002c009100e00c0c4c0100c0000d110118000410148603082148111130b449a1403c10650ba44001d07070230780e401078452803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 549440575 1250 549439325 549439327
    0x20f070506041205010f0903020f06010b0903060420040e0322050a05060309150f0106170f070e01020705060408011a0a21020d0605070906080108070e1324050103110103050408 77
    0x80814641c04043d50038050740000030320b4603140022804880100d002103015800c50300740108543d0f0f05103c500d0040c00c00c01201c51510031083e001903220750b4001c1c0300401030509400c001480d4081da80031407a050384060400c1154881058800381d403a041300600e60000c5d840d5542a4001d0045003540100f2a03101606040b01c1c903042000304015030708000d103012810311810380c2d1061002a40804c0314000d501111103000d85506242001b01401c0b007450009140740c1d000c0b01400069040000e207076500000c02c0c0391800d4004442e10040742040c89540c0129400b0f140800c0104040d8010360107030b03400402c405104d0b241100c00e0310030300c401c48585108254000c5801101100c0000030300c0c0d035010540e8401003003081030448079a146001c817003060f00ea410002d000f80030184101500902105e01608403600200740d06850142d0340300101c01d00901c61040c0c088049180310070820100c4101c0304143c0800c618080010007205a0700c002d010902c0242c1d101840b52603169059406440b0b940d01072a000403202e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 549441825 1250 549440575 549440579
    0x20f0417030913050402130507020604140c0a0b09130c170a0b0a06050c012403030509130222140108012303010c0302130f0506040302010807030b090c0901020f07050604 74
    0x695011a0200318490090100b084a200b0650700c0c2e401004166050b0540020f060401d401400700341d004035903040c043c440c5000e080c0710045400043d2036070b01943c854492403400c4201984103040a10309070240da00244404008200142e0031001b405c0c0400b802d030358100005141032880d4064403946089807020418101e850f0303807000300701005e03181d2051116201184005010300403490814050b0b000c240010700200741008030030801e021352899010300300301c03d41d2565495080c00c4d90050040c4401020b00000250090007a20b0304c81140c954410446c0045440e011800c809015a070016081501049029880410b6445082e80d0f0807194001c10b030740390400c580c21b100213018081700004605c2e60051060501c01d055076000d0041c2062046980d6000d41c41c1e0764403868030303503209689400112017200010000d000f1615040182e0f000c0b02d409181040b030b148c591034000d500521142d05120b400014020800109003130307100007004000e07403e030308030f840011a5110071915141c0901039603512001c20802 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 549443075 1250 549441825 549441839
    0x3040605070b09190b01080c0a050609010f030f020c070f0801020a0215061804031211030903090f1903030c02100516080c010e01020414150309060f070c080a0908070504020f04 77
    0x400f40d2000b030900481c1e00c02c001c802d07240d08042d9a8400100c400b280d004006010b60342c01030152214042c010743d00000004c0c10000001e405010f000f40c4541001070030785a07a09054400e40004c1c083c0d868611046554200c000d028944400300c501803c03a07056260000011410b0051080f500c060440384d0241a80c094048000c100d0050060141d46d8400c651aa1000c3c1440340541ca0502a502c40d451b454640055042c107101622904d44450301010800d001f0072851101c003000b11842c010048400a010018810010b0084c0c4540007040000c0c0080c01030200406070045007a9041301d000b02c82c41006020004000ca07044d00c282c48100c00c00100e0141101d0005400c1406000c04509500c00890700e42000c803481422601700340d00080d2107006e650040043c80c02c150905641940e82c61030050300c0c51500b200995511000a082c41d07044501d10000600003030300c5650400c202039801703850b00d80c0d21a2080402802e003000d5014000050141002c0010985800d02c211085040341311103c81c02c01d450080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 549444325 1250 549443075 549443093
    0x3080112021302280e1c031119030e09040f111f0504091401030b0c030901060f1d090d020a0b18060103050a06050603030406120f06030b0a0614030304060507 69
    0x18040341c00ca0002080420300d000c45001030514401d9601c8042e002580000c02c040000d440b031800007003444509503045c00c45490300e60b440c00420b04249030801880240c0d141c110381180041d0310044c4140103a00c21100c0200700f40e0620700391213000740d442e2645581d00c40c5c20840e035000103460007800e81140c0494200042c42d20055039880038001400825500104000d00c4400043c00c84280009140003e0078803101c5114401e8403002a524a1004810340c1196102c00040c4405001c004106601200087d0410b00941040000d4000e440c17200342c849941d002200f2981c0c80010451309240c007a0b0b000202c1c4808006212101c2041d540d008040c9a959130321001800200540403c00c00240440ca810305c0c18001c2013101d009503c540300800d03e01c2d0740340c1027003411074078050155071007a0020402044110b610205160480c007190300e000920300c0303189180400400c42ca07800201001c41c032508000d291801c03035001d0030488120107a00720040420404140d1248034034003485010032410301620001c100601 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 549445575 1250 549444325 549444359
    0xf1212070f020c031b1503150d1b0308030609090d09050118080106030b06010206090d053a020315150d0c020f0f01020304140a120305220602090307060507030801 71
    0x10055469005410740828200394401780000d0182c1842491000103040910203155a014a046018198181031104072940e80900b04020311828486101d1014011040c880c94400b05004610101d00ca9032490720030019001102e0452045d5007900002c2c100b0031010501040412075543c2e402d0800d820580190b40d07078020500800c0440d02e881e500440e40714130034880c15014500405404c401460540002858034600801d890b94a80044c1c0302400c1050700031098852901c261107150005880d40542103020340b00036004007280c800c41c1c090f5010101c8003076000b035010386003142080a91124010074491500c55612001d10320328410001ca803c4007407140d120b1116880948161101c5e10305103125240340c005962a960202d942c008180030400c505014000b00300064080502011141920f613450800c0c400300d115014943c903000011224038101000d5210f949001400544c0300ca020b0408400035003080e1701e494024820000b000c10528010815186a103600d0799460032030760300b00805807603032684032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 549446825 1250 549445575 549445577
    0x8070c0c1a120a0911010f020601060f03091e02100e091503120414010806090f0420060c0c0301060501020a15020d0b221b1710050a080f1212070f 64
    0xa008010710401c8402d1036500071840d500000c640040e080c180845040c0d07040880c1030500030002c0c03104a0320354010503254112920f40c03c005084003604001903002d03041e010b40080c001c8100074003540002e001c9442d80b205850081d2124034802d42c40c4a0180c501c2c580703500105500c80d161350001030385800c5078043d10301c8140e130140030b48144d0307600124050070581258000b6a000d41c102c80d0404100c1d64041d041651060302100e00410a0800840818041d40d02400160080000001a03c0d01301e00b1070b81303040c04c440c0010300890345d0307503041542c00c5d40c55001c610407041c840e5091141c0041d480d031000501d00c141c0754101101c400000480201c4500951204000840c1c02d6140d0454201d141d581d50b007210900c40c18480c41c41261040e0803003081c1281c0e130303000c1139140d54174841c45441e50307699100c05005801415030500d6031a135110b40c515507120112a600a0307902403000c900100e640040812001c0d954202c3e901110b00c034034000d5015901601482c0d455680c1100706e04002002c40d0b01c0340040400d18070079 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 549448075 1250 549446825 549446827
    0x546090203030a08010315051510020109050f070906090b061c0902090403110c0a03110f0d05071e060c111c020405010f053a0804080a060c08070c0c1a 66
    0x194042400d64020f00d10440100c2c0004d40104107220300906000b01002480804200340d260200d0301c81c8100c010b404d202c03406030ba80d01000030f9540307000354020302440c0e400800300d031031002588240b1a038a030060f01800102d07074100040050350341240c0c006c2c2c111180c0b000b000c04d401d004200d40511880d070b079011302c21b440c215180e50394900583c98183d212402030340255120400900c82090b814a4204017001e0309000c0c446845003000030900592035103000309030881c0d40c40148000c1c00c0006160300d411480183c1280550040000c841c071440030102c2401c609558240c21079651440c080d614241808409030540721041900012450490403d00210401d5603010101c00e100350081004c94100341c1010203004c0000409025620348010520084400c10340194620000c680c0c00c1c8800c0f03110340c811421038400c8202c00320200000e200030303900034001d0601122003030001810001c0203015088a42e03400701e01c2ca40c011034001071040d00155609600301c1142d210741031400b182d000c03446034028244106244 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 549449325 1250 549448075 549448091
    0x20315221406040e06040203070504051b030109090201180e07081825080a0f020907020c120309010f0c03050720060f1c06030f0b091905010546 63
    0x94038400c024021000c1d0400d8281d518214083c0411140c0c29103c01e0f00d031703a111004100041e40c00084e40c2c01950340c00d9801060b580c455115542c2d5000b0300c40b1840050381800300010480e85107950040c02e0142c000d0303803810300e08404c0b4113081c06480000d001f000c007041c50900000e800180200903081e00b00440040700f500b01100d04138030380d04160b105a103404400030380c540c0303242d0040c00158490014110702d202405041c0c101d80d941c02c00c54030202c00000d000d15059000110314600a2000c1c9481c81805004030303815207949005980c90b503000010340c50114048019000509210b040c20445059040c0c45552030a20310761220310000c0c615800b00a0306480160404945031140f501404280c8601140691036050036202558106030780040f10301114a800c5040021807140304000c80c05607006540c3d03000640b6040102e42c1441c41c0132101603050710301c804805040080540c44188a0800a507128151030035407900b502d40c04081981c260070300c822202d4404500b100302d01e1300122044100f00c0c0002e2641c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 549450575 1250 549449325 549449389
    0x60a0509041209090c0e21120310090203040f022e03021209011a221a03100506061b0c100306060206090a0302100c11011103060f04020315 61
    0x10204440c11107580244a90609205402c80d05a03805811001804c2c41780001c0c008000b8903d4079500d036241e200da881c03480c0e40242074204032480f041045d03022050342c202c103090302e01c0045207602c155180011040a180002943d6855200307403805554420406805c1340215002c0084030400c100d8240e280304141d042105901c0360105030f0442801e0291005621280c403e0341ea28500e072001800543d80341d0504480b40c20144401e00200c0c114030701180e0b02e90364132940c15003a15403007880d1810880600d2400a580c5c400c5d01c810101d5510061046003150000001100700005441d0203481998018030700f4441854041c00d481480b400741c0d505901104c004002c0c0300005060120380c00315001c0070a903280400e02c1000c3c2e0500c1556441141540140f440710300302d0f0b8009544560700080000855a10b101546501e4400c005060034000c100d0001d01c8044546060b5240c17960041d503040f48100d40c4c0b0808a4410300b400d0007903d00c245104c071039071034030240818244085019520b4000403503120149640c05c0300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 549451825 1250 549450575 549450589
    0x72d03022706031b0d0f1505040e0303060118090c09052704020f24030a060b0a0203070305090a080a060c0201150f0506070f08030103140c01090e070c0302030c0a0818040209090c03060a05 82
    0x40c4045d04011501c040ca02c2c7d0000c0d42c03044240c0000f130080e410320051002d03100c000022a500300e032083c80c200c1608008504440013004071500040c01c02c50610180e03250480c1c1c07114220301a12012654a00b14091202141c1d07014a04c01e0004206410540001005403604030907040c0c00200207492035505000d40002445040d410300d1021a40d1318000c000e200a20029220307881c058680040614640380031304c000a0b41c1c17230040c3d004c014100070380002d84080c1c0d070701c07100344801c01003038802c0450714103004514006004d4582c1905c0000190b190094180c00018103010a100b08c030403007a82e032070f1041d09003c14001540c2c010401507074072003035065081d000100004002d5008600941c41c1604c4410360b9803078541402d404500180c1000040f40061000d00b0380303140c1c01a001446411710841074211458141e00f54001c50302c10b4220b6011781200d84c0c00f8020800000d00031001d0a8540c06842d2141c901040b040307000391300344503400840721070000c0c2202c03e4080056800c42d030000c110f900002d03981d6000400d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 549453075 1250 549451825 549451841
    0x307050a0e090118021c0204060e040305070302120415111e0a050f010c1d0a030804090c02070f03051507050c01060b090f01090608072d03022706031b0d 67
    0x9107203400820400352010a20a015a0600b00008442c0b4408185c0024035404211002c0c21404201650071004564481c1d00c103000030809910314039128506420041c0c044d402c540c10a8015010f0000081a410214400c4038141c8039140100b0004001c0c0c40d9040340c10b400c842d0880815807003524126030004a10038401c5a501c2020700c002d15400000f403a20300c0c00d18003d2034240300503a0401c00c00900c40c0d03800c00d0303e6900c0502c0c80c02c4421740f020f03e05030000e01070400641c0068010100041c4c007203025000e0b90001c10312050355800f115802d41d42e81e0b44000750026244000341c02500f005808980074040c64a66a0700511740f0b00d015800c041c04444d80c0ca08680040d800064a8000007491300f81d0342c1080c0b589204c0403442424420360302440d12401600c22800101504100034842c805040b10301850b201d21803da203518180580c101500c9000600290b010890004d803071030030b250070203003035016881c002241c1e400090a05400d40c0c5404030300481c1020f14100c0340c0e00303810090085e05041c0b16a4424807403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 549454325 1250 549453075 549453089
    0x190e01090c061d1e01020c0d061d0319030e21070c05010318030f020a0b16020606030a15021305030604030f030b0f0a030b040f0b090604061a011d0307050a 68
    0x1c0c41a2502c14050b140d070084002d0b90195141c400002c030707215030301c00d00c0b8000040d007500d10440307508021200407424003050070f000341c1d400f882c400c0d00d0000b0302c4803d5008583c3ca001080c100ca9103000500d40440e540d0003664000b480c04c15001e149010101c2c407076080b82d0385400c2c80d80120b0300c11041170020108480a25030030f10540c0d500100e00b0701e00384809500a0300007230070203090400000c51460704c0092402d14840024060007202002480414400c00c0700741541500140c034140a414400c46507031465401c8400280140f281740003203109460701040800d2299231002c1611040c0070b00280e40000b0b0740012a04610905d441d02000907151401d000d03092065110381c1d24501c402600304400303021207110f042c04502070411121811240d80b41c40c0c1d2041d0580e604034035647c0301c03980d60385000e0036032300d022040040110321428113011035002c002903c2406144a201c082c410041d40c03a00c419402d4980b404403500080514011448954400032140140ca1020f015501c2080e1550080b562900c2d8903400300f1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 549455575 1250 549454325 549454343
    0x7030816030306091b080c040b070c03020906030105060607120e040608153304020c030403151103060901050d0c170a0c080102030906041b12080306031b0306190e0109 73
    0x10101580340c483e880291101000400078200d00ca840305209482c442880f0091029480c00b0a0311025030780140e038020300ea001301c4580da405803841d24030088052840120300685008000c10300520f41030241c54458640a804107003031801588510340d0122074031818100340700c1211202040768441d806a8006464260003c0102210f107c0c0e6072000a032004000301041d100118880340044d250405441c64168041c007041081c04130000010000d04c28860400400d2000040000c00c00044281ca03544c1000000d400304408044d0002e02c107803520003101c00b00ea000c8030103001440285000d00b00c5820640c040c3c85501281d40c2c45014080c0100b21807280e00800d079118104003010000c1d0070380301c000500301000083d4214281135170519a1100b01500042001ca61020764500d00c102843e11900144006441d550701086c003400e243c401b03580241d91a5010b4010500e01031460b10507103c07014070200000e0020445642c652400c00d602050b0340b41c65510040e1100700e40915013109008001c04140905011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 549456825 1250 549455575 549455617
    0x3c0e18041101080c0d150b0d05010e0703050402060904020711190510020f060106030e03070b01090b1507030903060c03090516080618060a0c0c02180f1008060a0e070308 74
    0x45100000d1401035040003c4202040781c4401024181d0fa002d42940e000805c0c0c04580061000c500320080c0c21420310703408081000b0501891680026040310303600641c07a41261120002181074601c1201e000e500500100079280ac2c0d414198000c15405010340314071440100c2140c0020030540405034140c003407400000342400a1700e00302c1100301d4008001d0000300380c005030081d40d075921140144512030905656240c295131802040c8100c40b90036610000c020055030716415081700a1509044080c00b400300c103402031380c2c24441841203403c0140c041d201c0781c803264030f15a186009048000c902004140c2c4138482e04000820400035500d0640802166210482c02c1c803502c00c2c43c00c000145404007060a00b164580070010224665030070428155010443c202c614a0a407032882c0d80034030007500300c96030090f542501110600b005008915040302904a6100d0768490419000c42d405042c10303980028000c02c40f40d40565100c540580c030200d05072100c03242c3d6030f212444160400101c0c40f44092080d821 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 549458075 1250 549456825 549456833
    0x30807150e1c02010c02061b12070809330c04050a030f0b0a05040308150a18051b03060609010c0609050604051c030603080a0c03020f0601080109033c0e1804 69
    0xd0042c1101d40d40c4000c03c1003d8500381d001b9600c0308060301200d0703003264004a035004442000d04503403804248402524650420305001021104201c515080c0b9000d40101542c0c4400540582c100301d07c800441c443d0641e41200c2c0516000b035010b080300b00002d07400c110000f65070f100d4035004001180514990010150703542008004a000108251a00c1c0d140c90700300700002e900080c2d0a40c20190b200c82c1c11242d07240400224010961720382024042c0c98884004c0c4581e44180e030050361003100d05281141e11200e40c1c41195425001c01d5480c180d1205081c0034064441d44039444030240580200c40111740a10940c0b01d55082c030b40c0170b07101a01c0c1a0403550040113058400c1c100c914a5190500c2c0801c04079180d5190410b41d03008224400b0201300c1a00070040034184200184c0c0c598195020944069594440c0300900918009404401040d125104084055440a403220113104858034020078541c6100402c88600140120319040c840756603000c45682d11201244408000700f450f0442d0641090b0074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 549459325 1250 549458075 549458113
    0x308060d1407050310020316080c090406030b1602120d0e150718120b060607060902120709061d0402010e010c0609080d0f051b03090a141b031204030807150e 69
    0x4660005c40d004206000c42420704035241c0d1400007940ca85049280c6500342020f51511455002c0e031fa0044c103014000c01803284070a240750040c148442d20b520f02c50401d0106a0321141d81d90480850500c0600010744c5100d19078011a400c44800c406407280c00150314040b20b403c20701620103c002078144a40301d0764000e0700e58035040181c80c59013062240c00c06070f03594203250348a0080030b2a025140218415040094a802002c4850b074028101540c405002d0386a5a4480c1d032071184251007412b145002400e01c0b0b000c401404a0103522040d0b0700380c0d036905c0c0c00544032600d000e544181045100040000820010f01c00c05843c14480c0c050309a0b103080186080058400105503108554917003800d0011212852a40b080381080170b00b01e854513603564008241c28421190001f1741013040340f00d4024540c0c44007080140419202038001d68807503004505056070384441c50002e845000040105001141d8410080c00390140329040c1007084410300c12a003400da82103415402865445240340740c66031041e001c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 549460431 1106 549459325 549459343
    0xd0605060a020a1e0c0509070c0803070801031a0c071b0f080f06091c0302030c0d0608010b040615121121010e060102060c03040308060d14070503 64
    0x41c2d00c07a018444121160141040713140088a00303501c034010940d0f00b085503500114240b80900013240c001401c0310301480610507240c00001c01c0d10000718407541c600e9075019510b525529005a603c5000c148c0c1c208207044a00030040f240c101c141c00d40319466008180d84040c034505056107001c01290b0781140008411500c00464564000079039005040c00ca0803c40d070f826515280026110072140280f05d40984584009a140611980180d6084544401d0492804146007170600071680250b202a005945403450031919140a108840c001c0c480008480c0390b01c20342400080001120030302c0442900d07500c000c184110708581c03056440308540031826103000840c5c50030011040740b00b4464800a4200080010015407010446a01131801c0e00300f1903047d501e46030340545a1500082645420034007143c003010200b1005070400000910b4140940800d82c01e16060600b040104 = true := by decide +kernel

theorem cover : BRFrame.Cov 549280575 549460431 := by
  have h0 := BRFrame.cov_init 549280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 549280575 ≤ n) (h2 : n < 549460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
