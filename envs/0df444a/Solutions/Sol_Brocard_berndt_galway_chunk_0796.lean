-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0796
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:51:11.464681+00:00
-- url     : https://prove2.me/submissions/d27b7ef1-fe56-45cc-97f9-5fe66877da38

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 142985611 ≤ n < 143165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 142986861 1250 142985611 142985629
    0xb0a2309010810020a0c0b0a090510051012080d0e03030601090f080307020d08040f06020c1f140903070506030408040806010609060e010e010c0506161e02190501060f080708010605 79
    0x251030b4001c140400541c60040029400f006a5070103208014585000040319140c03983c0c4501e0902c200451400c3d0107107801841c010400140c0070701e00742440100007203201c41ca0245411103032a007d0308075100015040040d82840b60180310f140c21401d118494034060000002503028540a81e14a0b402c250781d00052824035400f130040010603007080165101501e4604000050240100030241c40c180d1f40e1030301c3c201020b103030341e0000c0701507040324110035664a091045507c1c07990340d0a229810350810b01c0742c014104666a00c54003424040420000c0c203d840401810003e0030015042c1c41d0303039040c242003400f00c0b60003d104950607481420004203d46204407483c3c5d04842c01520754041191028005484800345200d026042100c40304d1a8000700340100017107800750b620399402c228204e14800004084014440c6000c401800c014203060700517900041060036912110001c9001500e245403030340c0901165400001c400c0c201c0030000c102050701184540031600300034002c00c00b0316699014403c13521 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 142988111 1250 142986861 142986869
    0x12070e0f03120d0222030302010c0302030f16050c01020c010608010b030a02150306030a020a0b09030c04180620070311060f0f010e0a0615030c1805031c030b0a230901 73
    0x500100301c0c40c0702e00703090003000d004440900700025040c00050740c0c014065200c43c101ca00d15802c501d00e42082815028820349007910140c1c0386c154998036000380810800742002d01001c480c0d01002c200380300c2d594840c9080e5800300340084002d556440c003108200b8003070000380c01114100c1d4030740100e101041c81c000501011455018103080254001161500340741c3d0130041a0742d8160054291420050352102030180c0a880b554081d01d858800f070340c090500d4101c100c0583c5000342c1c900103100d6402d41400032090001584080c010400e50b00e0540907618002da02c1c000c0c4c0c07480000201d1540201500100c2d000e00012402c07003104c40d141d454002c1815a000142c076041d04900c515030060200c850320b010300c5580035039030100c04240903a035240035500816400021030300281c1c1d42da000c0044654000e08a03251801b00000c00031300f160900c00029140c4a52103ca03c0d04e103004942d00040c0c0038041c0d0024000010000c00c0200f0540c2e46844204003040d888480b00d42014804005401510346041c03c10705176 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 142989361 1250 142988111 142988113
    0x40603060807170d050d0f020f0409051006080114010203070c0e090d02030f04031520190206061c1a01030b0403030c020105070f0302030c0f0c1e030f07170c0312070e0f03 75
    0x1307801e01001d613810740c42690385107030003078448600b2026258036000070440c1e64110a205943d5510786001d180403544041c100c0d40b070210040c0c00070059294000615030550f02d001c3c10a62594520500503499403103100ca00804260f00c00c000025003032105020769204101050507240e1007a104642241c6900c280a600840c2a605010600c04039041414040060400c95000102e107208241c0c60130615a260307a80415640c0c2c0055101084100654403084202c681d00041c012414640300107502c400024a600102d11501001e000070302440c440d0400203000040301c00303082940c490070054135407402201c0560100f4242865694154030512500d88103c4550780c40c80c00c00f0700d0415044020f0350002e0919135030082c090003c41c510b002c4100040c060f2201c1e1034000c1c120f0503949148081808445070004e10302c0e400510440d4941d2501c8421030b03000f07a0b8400b066403c40d000c04c40e80b0480300d000301301840c04603200c046040101e58881442950141d00740c2e45480c0c00f1072011908001c0c02c100809512a05 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 142990611 1250 142989361 142989373
    0x150405100c050a0f0c090f0525021504050309060a030c1701121203020c030d0b2803061104090e0607030e03090d030302030a020702101215050d0b06031204060306080717 74
    0x100c0d00403c102d0b941039101d1179004010996900c0418143d51420302e58022460761407040c0041685030509038810a40c4a041c2002107040c00f200184d1144c003440c003082e80b4401d003100000c04021080c0b049840510f0000c144a80340c0c02541d0303000303000f003250100711004140b0312011101e2003141c0703e98030b904813415801120b24036040d6540721410160341030080b8080c5a000d001d0034001c8030060020b480c080c0d904450001d21220a4010800c961207891410f0311120b040070068500c80c01802c60745000d40e0b4200700e0215a00c01a840000140d1095a21040b0070914008903110800e00c0480c1d401c0c0030300442c2c0c3e404c0c03001d0360300d594845840788200c0c4031440d4000440d0040c0800a8041d030041c40c0d0000c9003032703401070503d1441d401044c5283c070001c0140002911070440f001505001d8881c504d031a0000100420381d05080002095020300341c5040a000084030000180d0241da081005c0d0b0701790030722803004c03584582da42c5201502410b1240512a000d004045001c1410100700c0111079005400c5401015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 142991861 1250 142990611 142990613
    0xb1902040e180f01060b1215090c0f0702090705070b07080f070c020f060a03050f01090203090a020d11040e0c01090b090904060b01020307050307030207152d0c02150405100c050a 78
    0x300401c41c42d5580110b5006400314400400030130301c40c0d200244a03500035281d039002a031a13804042c4e88020b144903810f80c400310851806445400c01140c0c00711010003041e0b60f03040141c15130300003405614802588103400c0010001c1865000014040c0c3d54451006d2030225102d9500660700000304403030b2590f443d1440c0002a171504e200700d0181e8051070018102006107400040411469030000c580c040200740c4407814842401082d44240d4010003100381c0850540c00c1c6080095200d043e510300280c031942460140c1c2d404d1005070340380d001038403100800820100d02e0f04c80200351520103a281c6280894041040080c400841d18100d41050030300808002c21940c40d1760300c000040840c00001030442c8010b100f864002101000240403250094006003450b9103880341806c00b2419a986075810030541c940d400039040362002c2d203032400d1080c5125141e0141e0241501311402c2c502400c029504c01c1d440b50200f041c10b0062801007068035021784442e60b08402c2884182d50404003458000c0146e802401d08070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 142993111 1250 142991861 142991881
    0x1b03250c0201020604031206080105090f07050306012909040906060f0902120a02030414100e0d0509010804260406030f0513050709020717030405010b030c12190804030804030b1902040e 81
    0x507c011804880042c40c2520760808508641c021252101d103640f000d03402d180045c80c200402c0000b000210010b005960600f482c0b4801c41c100a60901c805100104440814641050944c2c580c4000a0020000ea00c03082c101400902298410a4021986000b020880c076002d03008641c120078040d80c90200f143c071881e030408025407004000750b0710100140441c440548061000312152001103101060001410424500703040c0035151702024400100030001c03a036600640c207030f50b2260300141d003654040310201c981d4002043c0040e0500d00c6500015000c90310540540c04040c214002040422499907000c00c100c4895207192800f030940c1d88002c408001440c5584c004002c801d1050ba504070b00c1e0b462042220b00036400a8070101c5660351900c0080a15080c100040110b89604455095800c0301d005192a2035400c1010b4035407940701e020a4a00c1400854011034000350b07400640340341d9130396481c10002c140480c03c0d03844401c00356100c42d450781200318900030b980564251600d08903403030325440c1c1c4c11 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 142994361 1250 142993111 142993127
    0x1406180d06091b060306060f050d0b1302130b040311090c120f0103030e031204050d0302030f0a08330108071704051b030715081b03250c020102060403 66
    0x59100c0c55840c0414001a52400742c52803a52140300040311030011101c2c0306214075610b812500805292100401c40550b02c1144810b414440d4241550f6403510450550080d02819030750700e8000d06421f0202c40c0c1c40c06958000d1542541012292045540b0340703000ca00c6a20039880702a1540d0083e1891007000c3c0740143d40c154109504003d60752419604842c59079408008440d80c440018100d0010011325802c41c0c80c0340703201e0720200e014007901c0110401c40700035800342c0c1c0202c9003d076541106070401c050003041110010b17071890044941303800382d520004041420032520101d603140ca201f214480c0c1130440c0220a005d205003400307040c0d004801c100445441c1c00040083c400c124050301c2d8001c10041a8020900aa0141d0003510092001181c408942800945040d00a40c0031000c104420724441070841c9140c00780e454203141da9252941c100c000284110710107841d00e000001400702180404500b00d818410030a0f180d413800c810540d0a0303801d0324040d800680503130003d20020f000640f0034104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 142995611 1250 142994361 142994407
    0x10608060f070207080f0a0618022b0602030a090c060215150402041502071a090d0210030e030a0c0b0703110d0903090f08150603030c0d08040206250c1406 68
    0x121114203a440040c18941402003048040d240c07c00400300382845190300a488403601c0d868107102da4000c2503404a0900071020216000c80340000d240b2440c000a8014161151900204155100d08001c0307802d0f4000c109031102102d0320705140d2000075243d4008141c000f1412540c6401e0841d80c0c1d5030310858004410406c40072035120341c1c200004079030003511044d00038080440b07500800c11181889812004c2203449600741044441c14000600d01d90340704c0001c5c0c0c541075810790310700b5000602c10b40107030042d04002c50300d641a40400b180500d006503026a03003403013990280d0001070141d00c400b9030a60448410b181101d506150800c00f007200305103103401c40514140b00c0d1034048080c80da00d030a00201660583c01c6044240c100354070a10300740241c202d0325904800101d000d140741c81c00c0707444801d55a040b0803912074140841c2400240640d618803007940d13203030042c010030001da421081e80e0a0340d0642511804076160701100c071000c89c00c4101422803624400c005045249400e80e00c806c000110055460 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 142996861 1250 142995611 142995613
    0xe040b060a27050603010b0310020903101409190b071b020901080309030c0609010f0c0305091e090a0b090c0924071401090b010e06040f1d0c03010608060f0702 70
    0x140c10700b0300c0d040100c0d60300307210080c04440303252514000d0700381c40c1d0140195120303a0500c44d03840101c0e030b004504110500841540181c0c0d43c0081c0e001300f0f040050310b0207000d4100e4070309515031500f04400c140c518402c007003460070f8401007460380300d00300076508001c500500340302482c40010314514000c150001d02c2094000c10b40c080c0440d01d9000824403c0c01740c0209145400c0421910340074141000000410b038030071140c0c1801d1070311180c0000d084d01182e400ba00d041011350740c00b00080c0360040c03089510548018280100b020f521010b08020f04030107500c658000e80b0002c0001d0aa40c4103031042d2415804000d10420454681c68811811900001c007041ea000d83c820481c00b03030718413075400c4000c10508414100c42d111072007400c25042421081c401c2280c181d04140450000400483d055815102413480760581a1207007404034005000310b050504031189401124811b003040c031807898070702002260840310f010405600303140c240c40c90380c850421180e0101012030080110090101e1340204e10f48 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 142998111 1250 142996861 142996879
    0x10308070f050a03120b0f0303120c130603060315021c0c050c0304080703050f03070c05040c0c060212010504060b0a0e040509250303140307021b19030b0117070e040b06 74
    0x18071524141102c160044003c11170040d002c201743d0009004034080c0c40d0003258120340004110001c281c880c80f4003455080c190103081700050742d0043c003d064480d10711003444034605180d00c42c00060002c040c0c9000c1514240d060351407800440d512802140c401c101c074104c2480c1d90007120603080c1c000e80314111000e000d008042c03056400800041014100400004009081040c50740c102a030614021002d4014640c100300071703d01c0418048101c0c01704644058400286c03003104c5a00803600c200d40044002c008a00011340f2240d20402d10100c54140c074002c0740c1c10489666103800180382c038401c0031204004141d8201e0301c01d1b51450305030f1006e03900403528816180320b166890440c58035804142c48030840708600074801d2050640c08810f60488481500c400c2d0715500300030902a503150000f80c8111710500c81200030004a4482c8401e1440c0003100603030340c1c54426103d01d0903042e8203100b4000d090b04041401c120084042c80001c5460031654030300050a41c64480b038403041078440008000d250001030300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 142999361 1250 142998111 142998113
    0xd020105090d0f14280809040219080606161113230a0603020108010308070614070504060e03011b0c05010615030506030c0d02030c1201061a0c0709050f010308070f 72
    0x604540d00e00d500c80d010700c608181e00c3c2c0c41c20034250710130a07004400a51044050314903416540901c00e120207031010340c0d4000070100e450312044506c070f168079894000c0d0000c510102071b013001410310b0f91a150640c4440400ba0707250350030701c142800ba0341d0a1004512240081901144250710806800040604240300b05010101c4020035244000c10103000c0c0580401102c01080d5211002600703d503506074140320140c550b4000a00c0070740c06000246c424440080c906003045103650110340d0010071401054498036107048040c0c90758000b446400c01050380411317200050304d418469401d60712118403a601080301c52400803203c044000208039465903031a04c001c204900c945894040c04016940c0200e140d191183c1818107280124880500525615004000594000c108100000026145407189001c03001005001d4615540301d8228040826904519885c3c0003000f048404400001c17904801e546218050445c1c1c012600302b007030740e1810740c0103000050f001d000800149002c1c2d040d1310b2111640d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 143000611 1250 142999361 142999369
    0x6040302040615021938010603060f091b180812030105011106090c040209040213030f02030d08010b03010506090d061d01050702010b031f09050f010f0605060304110d02010509 77
    0x6140c20401c0f1401c0403c000c142815410800401d103c0300790548030250306481c3da80c0c038011110900283c005400303006010303030810200440641d4074140c50701d00c00b4050f5a4a00001c2d004082c5401800100845d181010139008031034002c2c401070710440d0365980d00f0075051140850f81409100140110881c804c500058034100030400c940c40b111924124550302d514060014190109642110a054002e00f0401c00c0e8048003007841219403d0591b070150b50346026200040c000d11400e04540c0501050000100034030188101d414050352003501101d8038040b880005403150502403040c402803040c00c0006104c1428860041c203200035029100c0c080000f040c0e501c0e030065070a8a41c030310002c01c0c40008007034407030b2000340181600b244c01d03400200310080e81c010100ba115070b0360207600444013055181c43c02e01d080c0d9030351003160b070036811030240d8940c540104201d90183c4103885c00c4800b045d09104000c141440c1c407100700c0780103a43c0601d4420500002034117003d500448144264103006042c0001c002d20b0311 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 143001861 1250 143000611 143000621
    0xa0203030703120b010e0310091110020a0636020604090f1e05090a060504050705060c0610060f080f04140303090706020708071d040c15030204060f180902090604030204 74
    0x102c40d4450500c8082c4100c0e0000c101c1d41c591601504104203141340040b15140410351900a01310042c010803400000d08028035495196800d95030001850280c082c507a44c2d02141c0301c21440e02c03641044c02054101f8541291062031401c060300700d000300c40307a000c02501c2c180c0f04a403221440035041509069440300081d080741d10290f2500001d60702c469070042c0035086000000074101c0c6c0c0b00410049810030744038140c0e4640044c2d200414281d91040400c09101d004c019281c020b060003400031341ea854204062035161401034036940b060f0041c1001c040b80c1d0b00c2c000c0701050618030255a8002d000d5843c102d0070240c1c0b81380903100341c5000480d0210307030207121401d0004500c0741c1c2a02000304101854220020701d09082d030790107801c140e000f43c074061000944028100034612001805110103484a00f018071207049035900c01c0d00300120003408005403540513006003080b0749450711034202000c80b10400b5260718640d62095420b038003460006018035051540a42403407440074051506064483d404103040b51 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 143003111 1250 143001861 143001863
    0xd110a06030e0c01182904030501090c09020c0c04020d0b0a030c1505160201030902060d150f080c10050a0309020604090609050106090b040608150d0606030605060411070b090a02030307 81
    0x741c071550304103102c01041103203140a500078030f005a143c6801105008043c0c038140100c102020300130046482c5a042c82c140c0c40707070700c1c0714600b1030642e62035480c6440d900801803094111140007211030009545401d91003030b248440b118201074400200c0e0003007044000d5000180c0d0164071984c8403118500c1ba01c2c0c800c000c6015612505614150314104801d80c08185020320403c0d040060400100c280c0c02028076000200980c2070034045204241480010018022488494a5240760107070304140030540c41d4000c0d048070702510342e44040c2511040341588800c60315114540110f800401400110b21681c000c0000394540d140004e545241c81e800151140c1c4182c5c462490982c031100c0510a9468601c034480c01005982407072031041e440c00046643c50702441c8910401e20100d040001c443e0407105090005402008100074901e1081d8505100203207011700050b1225450040096801d08203032180030326111482c040581080300d19982d460740031000070103030960303030041004010058800700083c01f00f035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 143004361 1250 143003111 143003117
    0x905070501020c04090f0f1406090604031209030804031d0d03020a0c080d02070b030702070e01121416090b060d0c0206040b06090403120209153105030c0d110a06 71
    0x503160400080c6002002890b80344100d10300f05200340024456412100340507840080340c40c940007a400c200042140041c159150b90041804000d449140171442510582c820340b204240b900c4036400320822114000001404102c004004c1408a4010400d800105805e019105604050707000070070b50608502e20103c004d40c0c015143d07102000000d40c0c2d15001303070461070000d220709100c460700255616614403030b0720b840500000110301500d200348103da001e0b1030840320792400c07542c0d141415a59000d0018043c0d0702c01c0c000b514280000f00700400d8120501c51000020900942400011001402584103440d071100b02002203040b601050b00510b004403816401410351442c00c0d0502075000c10380140340390f120b50510410400001e4000d5802071284129110058130b91800c400400d00000010a030b50081002c00b01340c02c2950301d00361125400e40c4040d610303112007407848010380c181c1d0040385018544e415001030074005840d040c03400002158601907503041c00d03401c0821011851040541d0409400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 143005611 1250 143004361 143004373
    0x70b130914060306010501050c030403051b040e1606120b0306100510030e030706090f17040f0506040506070602031b0408010203060a0506270105070812060f060f0706110d0905 77
    0x25149500c5110341c044181c20080805103031001c0000e8480405001e00c0d41408004902e0b0007a1101c104250b5001d141e00604503041c0c0d1000d60740e140010f01103082c0081c4118100442903046200110704800581e40f4000403c0089040c014180e41d00e4101c6032082d0541c0f0303980e0b070040515035020440940500c200203030030b4030034508100500c41412050b11480c401d240c2850300401d44603200004840120340c10420005804402c0e103400410a45004400342c82d46400c00c1e19014181680d400400450700c102c0380003034074180d0398014440c2d140110b00c285a41310406120640c00704019400840d4845010526a030f0301c2041451044840e8000b5001814160350203c00c01a50b400e24041c9480030701800c84880f4100521302c24070340c089034139207951065103e01d428030781845a4003400554001940c005149501c0d004504040c665648017212040d1203800a88a009032a0801e14104c070000741e42003029501d403442940715400900960f002111582c4803c00c0210448081d40c89512202442400030f1300f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 143006861 1250 143005611 143005619
    0xe12060f0610080c0f030a0902100807030506030a0b0f07031d030901180509160207090e16050d05030318120c1507080108210d020310080d03060e0117070b13 69
    0x1410300152940e4414000c01905001a201c03100003505d80e141e01c03020b0513641d69603c004504c1c001c0c0c600c4150007900b01089080001c0f10341d800034075442c03083c0290307034040000341d0702c900030903603240034501c0003a041410080104003a4200103004662140803814049400183c0b89081e844c400304401e42c070b00c5c441e000440d020070b5a41e0300503003031445640e890546903481410000010a0000d01410b0164200140d040100b5501d00a0041400070003641c0c00030841007029034640b075141c0e40701d5074049020303140d005401324262030002c10807001075400c88000c40c15a610b00c071110f1210a12a0002d800607c9072818105111000100500007140b102e0041c00d42c00301c038002e000d4001d08000c0c001c00c0900c1a2107005102ca290002185401800d0780341842564006030190f130803242c03041210300701900c0e00020401074042d20300e40800c8225005281280d001c901040811003c8481d1801881d4005401900400070103401c8801600000c0c1080c0913072354a2035840c01340c102c281e40b0035804e0500382481288104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 143008111 1250 143006861 143006869
    0x6140c060403080a0e120306100c020423010e040b0c0313020307090c0f09061b0602091e150a080711031c0b1201090f02040519020a03020403230c010e12060f06 70
    0x1608204801006200c6d220022100ca54a40401000280120100c00050a00c14400c102c52000c0c90b4001d0410042c103103805280c3c911040480d160300c02003502c100f0001810180ca20f500520840d000003030101d2a844030040c4001e1640081c00e100485000b045015025940c14001c000051051401c00620043e0060f0007900607203545c000501800f4402c2c60401c40e003500000140601320791a02c5914080d070346071400710024024103419070f0301f040500c40d5882905000704050001d02070102d5085511444c042103450291040000c0100003910240100300d440e030107a0010303d200c070303101802d59003000800509031650100540460884649440c803c4545040860500407c8908031009202c030518580310098451140c020081c0103d68500004210462403611001c03214182801036584440f0650000c01075049800250303101c84000f8940030002d425010b01844c002d01d00c034041c0108071011801501c20303048810040d500041802040c03062202c0c00d00140e4032500c1960404d641d1810540140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 143009361 1250 143008111 143008121
    0x806040c050405070c02040c03110d091a0114060a03020f07050a020103050601020f0a080a020a05030706051e04020310050702100c03060f0801062301020c0a03120305100f06140c060403080a 83
    0x40340200d00d44401d110106a01c2419990b005c4e40554001c01c290780349140c01c900401c00e208100d400310101080b000405981070300040b170b0183c0911408c0d03030506440e03901c42d01a00030a1203606040140f0040c44881e60520700040c25400445040040c14600025a02d20b05544844c10840d403a8110440740340c00c5603054442c90381c21a0080c401070040c220051401c5179650070990300034200c484085401c450540c420004640c8659000058039111030301c918120010b4002500c14413003c161b000500f894007208034a003280310b6a0018000c0400e140c01c2480749000b4500509400c0850081a4102100c0760b1507004140c0c0d14101990005182860b2140391582842640c1112070540d04044c5c080168075220a10aa4001400c580840240c2c424100607444c1c030f00c002076042e40041c054a400418444040a10300511096072010b1215544000c04130904140d503020f00020b0030b500c0242440405c0c0301d1b032261420b00c40120001c6140000703030756070940340c03610454080380042c1003030040000b01c0c80f4a00030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 143010611 1250 143009361 143009369
    0x50702060d020903010f1a010516080a050a0807020a021c0303060f080a020406050603100e0c040305060f01050f19150908070e0610170c07050a15020406030c0e0907030e1005010806040c 81
    0x1042211a07850019281402e004171f4400e81040b402103940d50000960300055000c0f96030150714291f42d1142c0d5100075015800c500b10880200710310b04001038420b800802d510603806c0e8005c00900e60f2100403502e41c03202c0340680406034201540c6c0c030804140303842c18034000005440c15500420f1040f209204000170344a45400c014060710050084c03000305035142b503801c000d440c0c020000194580e40c03211106c1c142d000c0c0d07074400742540c4909018070030010134111645060b6101510b04c410702a99010a0000b0315001009001c041c0c00c01c00420090001d007060102c20600c80c924000060a40d01c46280f80381490f03942044131118454410f1044034a044c0c452421000041d052100c0d009400d200300040c5880001c0101d00c1501e40000c1c42c4042040074440203500a5000c00c4900d5514404500c900080d0068000ca00110703140854a80b0b4140c012120b0705160b54005180060a5855450840261081d610030004900c10a4120700c070444140c020b447c06000310400910716450542040398402c201680 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 143011861 1250 143010611 143010641
    0x6070303020d0f02091203120105060a0507150207140a03080a0506011b11091b030c03040305070f05010509060c040b03150a03120f0905060405031005061c0f020901080c0607030f050702060d02090301 87
    0x20044502c090b540c1e0480d81110030880728181c84045803207045cdc03681c0c41401070080c0000b020308030720350600c61180c0c09840118010a420500e080140404a541c1d00324a81c001e0080f07041c05001031500c00d01c44d0001580900189000c0d1825a0542c0c40b2903032400d030000b021180e030ae18040c0300e144a8244030100c0c40d404030700c02d03216450f42540101001010301c00603102000c08140080040d06050007135040300c07035281c4d000a100681540c0750816034000c000680c0c049906006440c04955881c44000541d829101c401650740e14580311184003c2c03082e200d42e0501e5410dd11344510020120f900e40c500307440b030780c0030f551a40924000000c0c402403403010389801580c8240d000348001c0c05980c40000e00b00c18094200840001c10b46c8641c800a2204000b80358030b601c4510100e1f2243d01003025240b240c401c0d05100703880722042c50341c81e15082a121700c1c02040080c0c01400503c00b05021a200754010ba81c11110b03800c0c5249810600d8000c191107a201004003294035400050b40a84c60a09214210703440075128 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 143013111 1250 143011861 143011867
    0xa020d0209060f21130f030e030a060630290117060c030601020312060d1a0130121e0504060e03070501021504081c05010611010908040b1c0603030806030706030903090506070303020d0f02091203 85
    0x1002c0e180c10a4140140ad10143c4cec80920031014034030180e2040f00050019400110f40e592000310140740c00e50581c1450b10b0281c10042068094580107072401490160044d6050a00d840340a05a80e00c0040990382e00541c0071039140c1c04199030782080800b0880d0724072900345960418501006007514422949243d1034041d0006035000e05000e0100300040d40020001e2941d0b444500856541100e050b400d0381074880354102c00c81760b91300400100200d41c5181c46602090f80c6110030151100001e20419002d40c20041c000803440d1503c5c00310303d0740940f190101d241004021a02403441c804001441c08120f0350302c0005002071904128000d240c607400301e0090241704056a904c01c285d00407440360707464840e40426044503401c42c0c48911500d0b10360b00c8600300001e590324200109441002c4d11903501034020603030003181c01c5110303000d8004031507007580720744062030324000c180403059202d00300a508040d4207002030f0844140c80c0c0108200d1100300740005d0303124141501003000040800940c03110b154820 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 143014361 1250 143013111 143013179
    0xe0303091b060706050603031b1c140a0c020114040e0612010507090512070e0a0b12060c04050d020a09142d0a020d0209060f21130f030e030a0606 64
    0xc0c500f21182141e02c00c034080341a445202c0070a1440c05910719100b86042441100c0814501c001042240903075a10201c5040580342c860030368200c5042c0482407543c1c2c0c81080265121402100946546441850b2010b03a035000d034151000706400580000101428050501100d45080f00000b00044003c0c3c000b04414245100c1c0604020010312540340903c170310781058121100140000340090440042d02c504519014000038010407007801c0f1180f113040e603480c0d07220111100050b143c0c07194445040503482c10b400c060411522603101403080f40e02c000020700c0030906001c64095002100550581844039040c201808208851591625a006004411407c030030500c140015504404050301c010f03a2032061044c501c000c1d01c41c0c1000241c00040000d15181a10704100040405030024010380b400c1e00401c0800040c00d01e0103650004d903507003402c90b20b1808902c09455080c94203200f03040070f1410440240c0400c0c00c12803514420f44401d40e80708820005080d141c0101050001050300c50000705200c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 143015611 1250 143014361 143014369
    0x10606030b030c09092d070b041203030915020a080f06060901170603010e0106080304030c0b07080307031d0607030b040e0601050109061404050d140c150f0f0d0e0303091b 75
    0x283d00c01c1a02c110301982c0452401c0609000d0584140320301303118103041c1008100c0741208000040c2444100740710700c880000d01003000c1c40645080e91102c410415907400c141c0c4045010788032201080d10b064204e810740c0302407415544020441e0b461303251556001c501c0c0003000b5a4039024020310450148104104a000c180e1340410500c124103419115802540c0b502030200380103000e01407406240d9031130a000813600c0036000010f0400c0340e1103607410203407c58860717614a801c0c0c003403030000512360301d01440800c6c8402c2c0241c00510b0f4000c1a4111502c144900b07a0b0303403528142040e21401c0c08260b6505011031241094003402c0d4101042d070b001030982c1d524000c0000c18000091044904000340320b5800e91541090a0840d0006e1000404001d0144c1003410407240140b008600c43e0200d00c01d1030001007090820a10200c0da041c1000c58a6060400040180006901c070848000e400001007019807001425407140b4804a4003000046031249089078149283c800c454403068005c02c0107440c05030407555 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 143016861 1250 143015611 143015623
    0xc0302012f0705190b0105090a0c02120901020c090a05071b020603070305090f0f0d03052202060c03040504150e010806090d0f0e0d0b070305070f050d0b03071a0309010606030b03 78
    0x441c2412a42c1e440c000d600300030f03040000080342e8400184190070080e091011141c030285c1601c4007103072034140d141c80340481d2070220364240c2990805030b04000e0540c5551000080641400001030040d106135140d05000141e03280d004480450786d581d51003082c000200e900450800c003645900d9035003400300c046038000503c1400014001010140c40e1400150381e0a4148101e10720010040102c41c20000081001611209e8501e8080002490000001c05081d001000001c004101400d420b0b100182502030150f1381d0b002c1d1201c0c0e400c510040000141603200c500c64490942043c8899250f11404c1400c01d40c017044041c1d05c0a006503200b482484448040413400d4002a081428a0070741070b1040c110170360315070b000c1c0054954420106c003540014040c01a248900c1b41456a03000c0020342e543d038100f0799110132100540070000d182071046500b6009180d0105a1002c00102256003195644040208450158018110101c004014440b211409000311000b500c0141420301140c1042400310303070341c0c2d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 143018111 1250 143016861 143016941
    0x90506060609010302071502070b07080103020f01200f0c03010b0613061805060a1106100b0714100c050c0f0c0d0204050402222007050303010b0f040b07030c030201 72
    0x7000003951804036070003541240c0342e581d0702100072501d404808243c0030003074020b0078040c0c8107003408000168240d4030484185041c1c0381c0c000c00c03802d008804100111024079000c0c41e031084144040c4402d04950204010045141c040720300245100d80c8101e081c0b5094a0f0100300f5240182d2040c0020000c0103200c2000c202907850520f423040d2414507501040d03507294000e034441a000301e4000b5140014940c0503228501c9414000200d6410313480703407000b50642c2e40c6c051140100102040c84040001009203c69000f01295041114003c1142d0f04d1140100d4451450b444c021410002e4039580040c1c040c40100c0003240c55138003416201041c200454a44404c0300c0c4028400c0c3c0d50380d4009411590345544030040041c03440081d02035a9041c2c14108010424130840f414034028440c880e0040030340d503504460340b1a41c04006103042d41d00c1c042100e05140c00103007114204010500c4081004a03424000e89031003802a552421400850709000e401c54088100d040176039034819200181c030040b1140c2c400f95007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 143019361 1250 143018111 143018119
    0x150a27080901050c0a0c0303090311030a020604050607050c04050705091504060905010c1a010f050f060f0d091e0803100504150e090307140f010b3309040903030c030c0309050606 78
    0x101e000f031345410700303110860100405402d4442008400d150384074003a402640d10442c84411440f01c081c0415a88980d20072000b948004104030901540c00d1000c058032685220fa0111800021114005419200b0031a0800001040450340d040d0078038003180d18801a0540000c0d680c5030605000d0300501551081c00381c2c4d0f051004546580003000205490903110400c0519060020b50311117050004003400340c425144103102c9080c240d00c4504d400d0b01112030030684149140d01d410308159941c0091304620b0360a40341e02c0704001c015040039001400b500d404c40d00c0b4420741603503480c0054403200c44082079046903001d6807800d907140510481e0a0415410344048900c0c842141d90787d401124a5841403040c000d14001034205101411000000c00307241100745900244101c46c0328805000100748001352065100744150314003030b09486140005001a000d4003402842c10103240040f4040d01c50030041240066075078880345010550502c03031004592041c1c6810701101810751942503036808060401071003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 143020611 1250 143019361 143019367
    0x1b0a090b07032a0201020d050405010c1106040506040e0406050a09030c03030f0e031308010b0409081903180506040c08030301050303070602030606040f0305030d050105180a0203060102150a2708090105 88
    0x905020b030b121186030712220343c00e1641d00c03160102e802c48074401c81142240517128244400406a0081c02074a042e200181e5803071092186a444140b6402460300003940c004000300070126160310742d04010400352041c81d86195140c201443c09008a44000300107800492500c103400340066440a150303c00319400d85000305240d90a1008500185500400c0c1c00c502c4c40b000800c40c141c84c03200b80b1003004a5a030780008000441e04001404242ca0b04604000c111034002c024903001d584c2441003441140005140c0050ba110500e0381c140c03402040458140c580d03500180800c020045001c90b060b018041d40d00141d800d5500d0640400d54a0084400090001d500400001c0060b214031007039030018510154030b4614180d5a00f05141c4039800000e060180b82e041c0f07000441c1c03900301403a6908428492590319070711a80d50480b0340317000703400140509045001c0c1d103c01a2180c921504500d005e0300a003031000402c041c0c4c0c802c07070a070500400b400c810181040412100080b43d15901a0b030402c030401c0c200169 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 143021861 1250 143020611 143020613
    0xd02031c0902130218091611030a0822050109030503090613020913020f0a060513060f020706030b0120010e07060c0b06010c02030f0a0809010305090c09060f01050d060e1b0a090b07 79
    0x403542d0001039015089240300707042007040021103d43c0b4547c00c0d03860b06c80007251030282c02d20703035241d1244e00c40d464007180301c8902154074402501d00007850b0780404e048518a002c11551a9030a41c0c6040e001035000810200500400c0a41441411b410100301c581c0c0d6100c41d07070542c0c04900545401010011000c4500c860300f02952540001c401c40710307400804d00e0308495180c15025281c1c0c3c002e04c106c00c40c002e41e01c1c0e00100f01180074140d1440f440e8802d800501d0803e1408008030041c00701c81204070704020036040c003511403001c464019000c409800b00081070859085d500c807460505290302c5181003001c904882800b013068124020342118080c60481d80040321800070a00d000c00380d030802c0810f031045541c000d091154800103403580e84400da8003480380e516031880e015a02c00035400c00c15403040303254000c0346203483d2105415051a03018103000d0b050000c400d22200071515a80e0096059544410800c801085d0a410440c41000340002c03560520081060003400c0070001c0c05050238100340001c0d200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 143023111 1250 143021861 143021887
    0x2030918130b0a0903020d020f03030112080906070c05090a0b130903020c0904120905010c12111e07030c0504060e040314090a03061a010206011d06060c0d02031c09021302 75
    0x1050090300400400041e050143c0100300034541c012043d0010b029118550301c0091001c0361103a011146c10b0019810359003402260b03140d44400000c215100304c01000700d49c026440e14400341200364010100000b0452030402070100b6080000c0003030150071b00d00510752000d944e400058100c1c080c0c0450002510301418a81a40303041d8840007000c0c0e00545541c00c000820201e042d0142d0103030036650351011055944e0006481d00c8004841c018080b20b504101000500e10030880300d01072100c420704407a0240100c6040305c00001400101422a40240906000384280028000c00820b02582c0c104003c52800401d009115406000241081400080301c2001d528400660300c000d51300402c0c040703a00f580e81c50000020140846505d1015010315000410342d030001c46c03d00e040340c90f6402100b1110404e40300c0e07001d04003c0100740c00d0340450103204102e404c220400c01030100700501c0e0002c1d940c410511903101c5a010014034955001c505002000c070058848031082c0c07240d080d00000168842007151448 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 143024361 1250 143023111 143023141
    0x30d020c0d110d080412060f0204060819061e0e061f0c0f020402030a0207031d0a090c1101060e09060a110901080a140901020d0f0902180402030703060203070f0e0102030918 76
    0x1d010350b0008174010407150403142100709003030322a5034204004800c070600c00090380118031451002c0b90b88000000c600d42c400103440480011800340010b1b0254039000c51500e04400e003100700e01c0c10071040e030061020629980c1d2241d04034000325690090314003c1030500c02c1280000300c045040122043c207013020400c110262000241d4000c2c400c0d516440d1400c82c4200035007000708280c2c00201c0d00346103c10070000001c4109844078002d001d26041034107100c0041e000d00381900702d5400b0050040010300b0440c1083c8a404003030041404504503908110718101d15201c00a40040a020700c0c1507241034200c80746030700703c0f0703001e003c01e09001d005540d804101000514004413081c01c80710a100420605100640c024020004418810401103c044200390100c8820000007034114031141c01c5056200c0441da0139a90107071008085403036603071b2266509030030ba8205941e070f02e011031201112001c0e441d8112032601ca0143d000e20046003003d0420002a8411040848040082d540003002c241d10f10304949030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 143025611 1250 143024361 143024363
    0x7030b060f090103050c120f0609030a031b0804080f090909030409060605190e21010501050102071d1b070503070308011d2205010b0402070c05091f060806041404030509030d020c0d110d 81
    0x549e4002e02d06a0001034880d4440d003846000649000c42c60b84c0c0000d61800342103211031417581c1d030780000e47d00c1d55220100390388072640c1141e4050b02400020240ea0317540445500c00e840031701c0038540308c1c0c1c030308041070341510480d41080c418881d0511180c4050b1104200d0051213140c1890900d0140d40d40c40c0201e5500e50314400041d0b511503115424004407981504918102c402c280c4c02c075005103907680c4014038480031015481c5c03400e6040c800802e190384080101049501003440300d647c40c0501550f00e1500d550b011050840c0810240780040100313510391111001c2404402401c9082450002407000006c1c000c080700c0410140301c05a4041031140075800b520100d00003070421903443c24182000b0642050910603244140800c5000450700c1403106965610450048403926000741451360991345c039071004100c1c0d90000d07a00c0c0d0403070521400a14005e40030b9402601c03001c0e03461246506142c01c007503401d40760000f50342c0000021001c0c0d850b6a002041d06541020300071180c1840e64000411a07024124 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 143026861 1250 143025611 143025613
    0x503010c080c0304030e19032009011d1b13030302011116120e10050c010b030118020904080d0204090b010e090f06060c010f0c030608190f03030f0b0307030b060f090103050c120f 78
    0xe0110800c85078518002c43d04040d00b16800c00849d840d003c21030520400d02880c0c04003210b064230400031010b000c408541000c00c80c0d04a0300c4c18191288900032581006001200e40700444104006040c0c0a115144442d00140714081c070741044001125181444454000d20130800284e0303b850040c0300f908180e09030030340106007142d100140031000702544c024492444040d440c218000c212440c0c140b02e122400707803503d060191120403036002c111214400a209580041c410849060a840c041c8001c0000e4044100b0001d45030040000042991281e2802d42c1c0c014001e05061203044803015410582c441c80031a05146e9034504e545000d405050400d00d0b02122500380b4440c8207001d5095040282500d0a010032221214a005ca1200313003c6403540707018220b0500e514100c00802d11a400c003880042c00c000010841400d60740120345440c08540c01039482c8070940061000303e18203030b14009000101107400042039419070701e505071200101c0180078800c404001698604a9007071000c2007210741440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 143028111 1250 143026861 143026909
    0x30117011e0f060e04050a1b15050301030c060c15020c0a021801030b060604180906060e0f040b01050402131502011409030c0706030203010e0a0902060408010c05040503010c080c0304030e 82
    0x3000030000e040c00d0085110b815080507004920140c06043d007030702c990340000041c16600b0454540204c00144803916004003130080802080300da8865128401c403101c80d644290b81d0b5890b6052200702d00d0110b40001c01080310b522442d1000c9842901208029a1307856001603450300f280007002c3c64000e10f11402034111801705482554000700c41c461034101c9026400e007049a6a0f0030082100310701c070701d00440d400740c40c031440060500c1c840f580c4244070180c81307400c0014506848040418481d00e00700c80350714141002ca000c010400502c1d182840c01400706030303019405e040020b6061503202140d0702990000382034409508600f10303c00d40001c002814241007a100906168070230644980c007000304640a489000c0000442c80d10034403c032412280b40654405080e02c400c400c22001d000d0051045e03030300c140d044c800402d00322b400380300d070005103a19a1680e95469161905140c01d4801aa0704203040c469000201f211032090802141e61180d454074014410203501800100c29005215070000d0210000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 143029361 1250 143028111 143028161
    0xb07050409110403060e031c0e1e0c10030b0102030706020d0f1805010509030702011403100b04060e0f100905280306020325021011160501140f01030803011701 70
    0x242c00400030f9078054a014803415490141959407481a99000f00d01702c0100464040c45850b5948921100360203601600c5142e001030b81202c101c00e00718190014183c026080e00c0640386010045502c3c059003a05040c006041000c0010303403240a0400080c00c46030300054031580c0c00a095222079082460390b542080001c460f82010010400c1e0382808440390341c40d101c0824000080042501d8882c5d905a5030141b0221040d080b1024907040a0908640c1d0101c0f810017244c0c0e028040044c1000d803002e680c030380504948010800c100401841411402008218419950b40da8002c806000340d950030f42c1c0558009002a502c0d048616003030400300464a082080401009140d4000314041d00e4001003003c1d5188607484200d241e01c58200350600541e00c00c110410000c0265000b00b10030785e100500080c00d0407122541071284030154101103500380d40d110703070044c060031090050320b4200b580030014031406d60666a440009100c1805041d20100204411003400c4070300350411072022a200040c04030032100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 143030611 1250 143029361 143029391
    0x2061c06050d030906120e07060309020d0c080c030d1416082b0506030303091c0c02040519060e0108100f060b0703120507050901080f0405010e060f0403030b0d0206070b07050409 78
    0x13103401141c000500d50194640f840c4c40602070785503a42603041c00307400c0c62441e000d02500200901402243c00c001000d003580046180741c4a84c000801c0e20401500010400508050510644581d40030500405406541c2d0311802c002c162500c44491b40404103603081075050200507806105408014040c034250018110700c4c1c817801400100d0f4248409101c0c503196403040645038001101ea6441c5503010801200441000104216518400b070904445520310781e0045400d43d1000c0312a4401e500100c48100200d00162103020000c0200304144a03095050403100c903101c0845900d1040a1515020301c400c1c1103146920240c01018842110f6988800914002c2e0003c82c40b220000602403504000400b000d00400442d4100c41050713440c1c55032540c404030014071241001c1d00030390b629035035451210328040c1c08004e49809444041c0350200c03d407402c3d1400509030345007141e10f81d0107003400d0402000161a41c4054805541d809148028140d542e004225103c0c010395110071003203401d01440e8081111 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 143031861 1250 143030611 143030627
    0x1207020705091008030304021306050a080c0f01030b01020727060602010b04060501080601050d0f0605030601061715010c03050715020327030906071203140a02031608010302061c06050d03 82
    0x16034045a1643c0d40210401600c0c910b4840c1c02c10301c1e041000040c0051401c40d45c50004004052400a482d40e1076502284141007a42c109028591000300b4490441c42d18610ba03100c0e83c4001d203418001100b060300001d4803101d89110303103100c00d42c141c6400310340080300e00c4603032403040e1441d131007048480c0d51000000c1c080e04a504226004a05c2c0034004103880d4890300c01140f0070314041c0c550f0b81c80d0904070014903008000d8a01109100750350303001d0200d11340d0780034807940e40201056920646072901e0780c1030b080c50140f009000d90f40c9600c6e1040c0848401d0740c0050821555641501703095850301f022b400c1032400141c42403160346501e8030010410004a180327000010681d140a00001d60b805041d48202d81d403031240100c251b038007050612850000460314211082104e0f5035180115492075901d840701e00b41c03034082d01c4940c0d0312900030042000412203030700e00303040130451460070a0311941f5540105a180c03103100420500488280c03003c01015410b0780158000300405002daa01e02042814001e145030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 143033111 1250 143031861 143031869
    0x120201110a0b070f390f051603020a09060e0402040e0a06090c08011508120f0d020a030518030702130507020f0f010203090708120a0e041112010812071104050c12070207 74
    0x480303110170322010703562150b030255040c2211400204407a02e481c1c00d000751001d07884c104131a031542903500e420014a050245442410100d036071103030001d01f03600c1000074100c46a0407038402145401c00400842c0791101000341c0160b010741c1d0002d1400700c0a06450305142030b041000e0071041c01c050404080042c540c141e032088805c000020007003141081034680c918011031160f40450f6000c5030602d461558480005c1003013040c800d480500d04640c070303881882681c228a00c1d550103e5500e078100000b060075101c2084c035010340c01c809545850301660014a80c0e0302201c0c02961030b540e4410010784c04070b0080025513480d1400d6030403111110115000c01c0c0c013035030003200c9648141c0902c1000052a203070010304240c00d22070b1101d66504010b1068000c0f10001d0180c5042a80319855140b03030f4403034002c50b070000c01d000c0b40c0c0682e2100b075640c18640c1140c030302105030358080724680c030402071032020541403408040c5191048901180341e48030080711000d14010740e030300266959095818032070b117a50002509400c035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 143034361 1250 143033111 143033117
    0x8091c0501150602010e0a1a060d150605013b0a08010207061a0102061e0c04051c1101180b28080708060603010303050a03050601110d0c030e0a120201110a0b070f 71
    0xc10a41d046d540c03581e07520000240b628282212000100a00c074800b0360f404500a402586103002d83d40356140485100e8030324022559a50b1000d0006513401080003c0d078844960514200103080711110b880d82c02051640403c2e0003119070310125640d00c541380300c07008107800d100070754a80c00c160400740c0050503401c0d191052041c042a49800c60350001c0340071403107805900741d080c1140c014462510071030304004054800440d4204400f0680d82d9403804c144010f14103c5525400d00b80080c80e00c0c1044041200c0540d040c441c2501d01f240d0610010302c542025103940e003001035210703001d00008004000107860b003095454205170380b142e01c490780b024400d4400c3c41280c1d5506425125882070110511080c04042c000410403c00034260743d010f50002ca8000300185001700d50304903542a00d501304241c90f06a4800900e0442181042c142d04c98030350700c0d07035000c11242007502e58a088050031016020312802814402e142000400202040c01007080c7e994020910040c503103480d90740246801a020564404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 143035611 1250 143034361 143034371
    0x31002040f050406050901150e030105010b2d0301050d0c030f0f051204080c04090f05060103051e010b33070b040b01080607120e0c030a08030a0506060708091c050115060201 76
    0x60b5150a01a440441d00d000d40344900b6a4280400d0320091071201c2070503010f1208009203a040c07602c0900c1210300810b110140301d038881d0301c9c034810390702e402d0359108141d400103120b04441c00802004108880c11204100e039080082107042c60719401008903640f014010501411009051040012035080e001e0f00c11000c2d0b55101d1140b41c2401c080303003ea4081c6000950004e804414242419888680e800e030050316141040081581d40a00d0070609800c00c41da00c0c0c00440c80c00b000c40c82203856800c1036070f401400921242c04404081245030140350040d01c00c6040041c02020400001c6401c0d4901c13840e03031400183e403100356040c28060560291003c4512003501800014183e2000c42c0142c015400359480c080c1012821f5a003102070000241060400c0c00f9068000b41c090354200305100c4100c4c411141c2e039889147c020303e08011190020300590040c00100920340c005104041200d082d40d1007100d07044640d0f4042210440308481c0000020030a40c40c0004480700c0b54088165041103945560003446 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 143036861 1250 143035611 143035619
    0x60b030105011b11040209060702100f02011a0108160e0d03030903120522021c0b0105090f010315150902070f0b0106030b15030c0705010c2001060b04120203010605031002040f 77
    0x41c200c0780f000740000300520504c03200d0b032400e50001c0402c4040240b2060800405400050050105a80c548041810340055010701902800340c0c000c2559032040c1680c41e045c03403600182884800801035000c0a54640c0d4440a85d030266580f03182201010301160000006032401170001c250484042e40403138032640b00280020514010184101c800d0f84d400c40b0f404034a00043c40e891241048102d903c500c00c4806a00040307011a110b1101501645071400c0725490007040c0b10201e20007414006880d0714141c0107102243c480c8440c0000616907440004100c4605149000c3c0421180c0000701c0030b6000003503020502400302ca9801d800c60194194021a0342e8600003981103c00950500b5001400780c40f407104071081400240d0360010b040e4442600c1e01c03c580c0d840301d08441091050700041900311605282c0c0410b0b4603040e13006917000000800003141010030910f118000d5200780d0307001055011404c81152800e4110100034036010781160401400383c00528040d400500510f4001c0040310380003d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 143038111 1250 143036861 143036897
    0xc070605010b04060f1209050303100e01080d0f0807090305061003060b030127050a02060409200f03040f020d05070305011d0111090d020d080f0703081303090e06040e01060b03010501 80
    0x1e04503039032510354202c40700c20b1880984000000d5070300541b13447d551b0300303d400104e001400110311030340d560320003822000e0510610300e52861040c3c0081026a1219a030140c8694201c02c9004101c50f8505201d512640e501d40e08680e40c0b01c03160401800350062206201c800614a100041600c0c4120001e000040b0800305041c201e94a02404c601d00e10780034009411710040200d156103110f800398064400c0e414064001c603140b07030b100354882400355540d0003076044016103100300c3c090700c074100d450714030302c0c141100b4020f0b4028080500094001444d00003000c046644090503008600e501c03a060320842690b90604c0c0f4001c5c0559520b8206156088100900c42ca0041c4a0860b40051520000d410140a142800540d0443c150f040780c001c5421088035002c18005000f0700424a40d01d2084c81d41c481e084c0c5401400c52001a20043c0030380c00d0300000c00002501b04580c1c0068a414003030ba29482c1c0d0310366002402402407181d1042c85946003200200300840060000d6058940c2a02d1391240201d04ca0241 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 143039361 1250 143038111 143038117
    0x708390f040203071103030405070311060a0804060528060807060e010801031e1e020117060306062e0207031209080d08070203090406121506150302030a0f050c070605010b 75
    0x20560110080e0003803002850300758042d41e0000c03282d140c84803000060200f2285158002c0e1416a52036114070800c0040040645502005100c285c036070760705004034100050540b040181c0000c140c95250000a421075500c0b903a40c0b000c0f00e000e880f13039075210b0007400408001011180205030690245410100701c250080c141c20104880c107940c0c1d074a0700d030710390744854007004600a80300d916040404110404188400200c0095a00181c030318443c0c1803072032002602e5041c00a000c064071340910002c00c561039074045822035100500f504c0e2981c0040c0003024108000d91030641c240e02100800c031455005030340c0055050166031103200101c40c020100740064800342031900c16011698002c10181c2c203e50b102d01403003608807100c1d00469084c84509000103040d034000341c12a116803d002d4030324a00388500985154200286030900704011400d056240c0e014000c240d80e04000d154000000c500c544406034002d07440011914410040ca0411203030301c505a40c040d40003502c103d41880000304881c00c800080b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 143040611 1250 143039361 143039473
    0x20405030a02040209040e0a031d010206040c121506080a031d0d0f0503040f0303030c020c041512080702090403020f1b0901050904051011030a0c030209060901030e0708 74
    0x4011000d002e40c01c0002960043c0d020b560490b456050a20305044108082c80706184a9200d0481c1e450340b00000940300c2e00700040f1181150701240502022400551110302940c10201c0324000e212014200b80940a064001d8044a01e02e014030000e0710113004240c3d1500d951003903480703011070110800c0d10300903503020701407282d1700070184003043c80000c03180b403103003003041e44540306890825982d40d1140103e00e109900c190042a101d00e800b1005a82c18400100c100908490401c10b000c04000c0001011000c1e00a42001c0c0d41c1000715002440704035000e6170341040e0f00600f0500180741c42c1c07900035150f25402003a21468418600d5498804003200c1c0b02204604002d01800c0e440d0b86004104001843c0c003800540b914000c0d140c110100c000301d801038a00c980c54241030304e41d0f00d051401900d800ca0708510401010984144284a0706588031001c8400e009001d10380450401142c0c25114200001a4825011442540c00b1217070400ad61a500380c50412200382c49456002c402c0303490410b48001814 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 143041861 1250 143040611 143040613
    0x5061f06050901050315031e07050d0809100c080313170705120c030d02190f05040b0304060504060e011b1103040e0604050603150412140306030d080403050c1e1b010816020102070c0b03060f030102040503 89
    0x12002015041030003041602e3b110504d0090b5144080342c8690006034070a54681808400c101c501c5002d100c032071019490007540c004c0010340b501546458950b180d45100307600d4095204001100c980c02c1d04108181c2c0e0185101c01d0702150360304200d02c0c800e0700c40c4180c102c60740041030701d0201c04004c1078007400a50b4100e0300705280e00c51440e92030f41c0e01c6c44010314004104840f1255900794400100b11f01f48a4504401358400030658a00c0f840840a09038581014400340342c5e84c400c06c010310a0300d03113488126401c4441075402243c0c6481c3daa00190a00d03109000301d03002c03a49440308202c1409900c2242002071201c540b01c00f0030758003074141c0100c903038802115841d4160344001c100d010340c2841003000c5607201e402803401c142000d18040d07070a42080505815040940c030144148100c100c000d210740501c0345070200340707401e1545900f8000303801a4001000c03c4440c002c0203c036400154003c2d0100c8108983c40106400e081e03485110a0405c2d8100f907951034022090308038400c0250805108403020b03100014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 143043111 1250 143041861 143041867
    0x304050a1806030602030103061e050606040e0405150c03160306030201140a030e060a06050411091f09091803020c010c020f04020f070f05061f06050901050315031e07050d08 76
    0x7058400c03403100c20070307402144181d550a000001c10510710146000e10322583c404182c03d01085180c114035920030a40729100c920300010b10926a1b07400044804a03184003000040503600c0e81030a42c10405d40c40d10341144407800c40100219064a000154800c04054402881681c2d0b15442142103911303d002c0203020a070b146864590000450340a414107061616012030303814400048181002c00984210f240306494030f509010900c4c050096504411109030014200200040004d09040e0600c1c03000500c404008072001d0514468000d4001030840d100062004140350480380140750344d0208194014003589003020318548c0b0403202041042d07002011002000e40c1501000001e600580b0030307800c00c01c0100441800219598000d0a445024030043c1c9414600801000c003400e40e1100a2040f440010074180700ca1034004040d250407840a10b8190303165640d48240c0300003c0b590704010740e89445091807880ea40f41c00348500303010240d081001d07136100503a240184410803c45030002800110f0174 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 143044361 1250 143043111 143043119
    0x103170309030706240b25081605030f0a0801030b091f020306011101060902070605010e01030b01030f0305161b0603060608011221120507050301060c020409260c0601080304050a 78
    0xb07410217a21030000040441181d2002e6045800660183c2d006000c82c1760081801c01001c8a029210268403003080b844140c2012203070f444803103038410701401e82550441103180009004080095072082d065543c10165103d0100340e002e44884c50921048454400c0f00000840740140861906040b0014030380d13840080141c02c607801e010750002440b01d810041d56544140b02e0303030424010a40141500362006a13100502d0a1410070766205030060750000d8010401000040d0b51080300c41c0c110398000c03109040d5082685400c031520300c83c1200c011040070590a000c0b0922a9aa44450340c071240700b0942d03640180d548100f40c080d01d400b4407440c80400d031208010040a60348460340c42d001d5203e9184e00040360244007000700b40405210401c0005584c1740000c621803100783c400e07035801158500300706046601d0f01d200140f41c5031f01c1c82c100034041d40d03c070401c0c00100084038440c0072090741003c01d0b20291202080010080d600040c1196081c2e00c144030001829100101c03c641c1503460103415488810f00b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 143045611 1250 143044361 143044373
    0x503060103050c161b0b09152b1d0106080a021309061503050c0f09060d150e0a020301181a0916060905040f1415030106030807030801031703090307 65
    0x8010508090f41c0350800070b010b8140805081041014401c0700f40f12401c90a400750560708032600e4000c4050a44200030b02001ca0740c450a0b491402d2148402d0f00f40d840102580710b41d9940114220302e090820030701408445c00205e03401404070500010240305221030007054003401d9402510070f0682c0e680011598001500301500c40b8000c0300c04640b40802c811810740d0718170045802c0107280e00e1101506034814010840b0034022417001144c02c8608401e10381e4030000050818201500c0c5d00e1040700e202078000100112401c0041104000c40000c00054421944a40e103c0e024403034100d100703503c1c0a400c10340e4006d585041070180c507000000c00403052004080d80c45440b1019108107214410350301c1e84040003d0600011003d0b11807a920028071914000600c810740b9810080401c406007042c0d00c6501d400021111141d010340d58400182039605800042401411241c0000e800b402c80003c55000741504141660704891084006540c82502c04d03040e40b5960100362070902e09074000308280c10100b40c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 143046861 1250 143045611 143045621
    0x20c0d02060423090703060e0703091203020d090b1f0e1012020a03241a0321040f0306020c07080a030206060f0a05271501050d021305060705010911040b010503060103 73
    0x1030043c2964942d07a1034800003034548208489100c0020380707130304042c469460041513864000413141000c2c040020f10fa5141074020303010402800806601040401798001c80d0740081207001d812500078115030a0ae0840e102600291200024900d4207141c80040d280e281d50380c4035403140c07541c1c01e9003000e000c0c20300148051300303c414101a41d1207850624040045004806c40540710121011030039403014000200c0020b0303c050184551403501c2c1401424680e850102d4050f0005446140540408050642c0e04203103005940110341c040c401103001200301704d09540185440301594013111821035491510966402c07500760010010f810580109485050501c0310360880c03000100703419481a20380020a01121105401c083c0f0204217000504070307049802c0c191504054030207101000090000300282c9144075502a844425a0020341030b8140b0821020880c05071800810241e9280460b09000f4060001c21509035240707035000e6444c403440e2070148034810103494180c64190441d9103000c01540208 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 143048111 1250 143046861 143046899
    0x60a080406110f0d0509190218181603050f0304030201120b0a050904200a0807050d15180b092a0a08010e070305121e030c0d1a01020c0d020604 63
    0x52014864010052000800b0b040d800d106031354002580d18152041600e0000c4d110303038034041c0310b40000d160340160f202c1c1d800c9413068820069070500c5e10b44828110244601d00309114201f90700034900038000d007000c0e02c42410103e03070080080f6014201c60801030360f180d226612009001c50800400a4480f46c840d81042d90302e48002804504440d640b0b4010400e00482124122a50390700300445140103a005102d2000c8078a051300c014200710705208100341ea072f1249005292007191000d113a4420480c400f0302c00803142150000502001407415580555400d298504984480c00c0e040090b201500000e00502c0400d1038106c180f04910801c0401c66200703a0f4815540d4004101400104410300300b4020a1541640e001c010000c540c03a5051107030404136134003d031144080c000c0069510b10030079000e120ba410a00a24a540c1d2a2220410030040d84602c18005018a04248803c06410040b0080c016106802c0e020f03903031000016810452070b01090300000f903210b5130600040c00210000300ca040d0f84d40c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 143049361 1250 143048111 143048141
    0xb0424110307030507060e070806070318050a26030606031b071703061002030304050c0622090609051609061202210105010306120c0e040809060d06060e060a080406 72
    0x59010541610704507403040740c060780030507070002e41c0c9020080c59200380c8114152440203070070781c941805001611740d040a09a0307010541c40310050644824a2001a07540c1a03124040b05c507030209500d001111444404070105141601801805000b54100200ca21840c001024907103541e890000d1300c80840c10252004403509402e03c04140020741c10701c05030070b03400400c0740381d2074507494036001304910b000d00c0040d40421508184240070006500042000d00c48900715126520b920840011440510301c0b580c0780643c000350b07107800043c015040e038814804d50302c21020074001582c641d001e0310900f80941411100189201c0c8040240718429218007034000280c400252408420584400c0c00300d80c80d2107000c0603000100010441c541e0036119410040543c0321941d00031002c0d0f0385900040d42d01d184903024040000d44000380800c000c1d042102c00780c1e00f004280030b45590700c83c08813400812203409803401003402c00b00c41c84081c0c603146c07083e640c65041c65554030036240d403156100700140042003000c1000b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 143050611 1250 143049361 143049377
    0x3050d1403090d2d11010b030703020d060905011407050315180403031509060816052d0109051503090601050111030403060e030c010912030f020906030105061b0d020109030206010b0424 81
    0x10b1000e030200b500340344051580e03882c401c680f17030481c11600b1101c0c0380a446110360b216031020001a03d49070f280d90207540e00400c0001e02000103040050150031001940f161004c0c0c01410072410b10780050145015050a03503a110f0040403000070b1100c12281e4000c8800c520880c0400100042d00c20f4004a030745908001401428542d05c0e048001550465000b165042e005001807490540502546d00014042210003c0d0003018003082404011070000030b64910344007110076401c20f64040d1030f500000b4203021303040c0c581d822118000040305400507200b14459008540000909601c1052806002842d0300b014501cac207441d40c0d507800028950310b0b6020f0306902082c041100304d11030a114000c1c8040c050304105407510b0b000c00f4014101c912851040d003003113106001c045615129001520b064071800c0d50f140e9607590386100b605100725950004840c0600c03c6a50000b00b640d41034015094080c400d800700d5980d030340c0350780c4580424011801150b004140c80403200c191019010005901c40130a4104200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 143051861 1250 143050611 143050667
    0xb010b130909230708160b040b1e030a0b040c020c030d0f0e030a03080f010b0406090306050603031308010b0a2c061206040516080a0b01180b03010603050d1403090d 72
    0x5a07020400100704402c0c4c000305020018064180a06040e0b00f94040314400c965052910030541e6004601074007554410100c0c00d2818001c072468541c00080c00841030b0303610b9281c214410405441c3ca0340b0389a00079070409202075207050002500d5401404004c000e0810202203030421284e030012240740070100120409007440c0b07520140038001906000b035a826003035107014041c0b030740c4070b24040c0e200c56a01c7c0740400007041600d600c1190241540d0744680c000c1020340307d11000a1940c012005186104011008000f900820541c00900d0321001603c9182c2041e580d4110b00c08915005100c1c11a075428010008000340c0ca03038129264412401040c2e10310a40e10b5401340c0d40780103800c8800311680d500212641034848883ca1311900203020200050445940c5542c03800c03100d40040c842e801c44c000003a0b00084880100d034100c090340394000350080103020fa17a8107100e136039500c4800720280482d41ea080100e4400c580c02080300c0c4640454002003800c0110304104403040409540131000c02c00b803104400c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 143053111 1250 143051861 143051903
    0xf110706050c010914010f05060a120602030408190c03030b01090e0604090f050d05040801060b030105030d0f091d06040f050603060c090609120105040b06030f0c0d02060405040504050304030b010b130909 89
    0x6905c026041780005581101ea55105040300c40251080348144034003078003000b034451590640094198848800b5890b80c2f41d9181c034050302c2c01402e6690540201d5100d040a40381d83c085000b8507954020b6406118407505c1c44015a80d00000340214800401c254002420038246500300e03802c076510070701c01590b080500c1c0e1241c0b4101080e0f10a00400100005001c20250b0f00901410010380418060745242d5403500300002da94211716030401042c001072198086240d03004404a1b0006c05212441c1c0c60403500a4601410610301119100e22072450800c0f9003042034003a00c2601d1003004058000c1c81651a2448080c1d031942080c07165980c4500c08025200e10b645840c802104c41c28603a800120ba9801d05150400300010014400e900940c05041710348001400040c504420f058281c03240c8800e1015800455490f10858000b10340260510080c401049800401481120f00450444d00c0f41d0b6283c210750452449051038070308144131400c42c02c0c041c507541a0311544c20140b00e92100d03034598051460807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 143054361 1250 143053111 143053133
    0xd08092d1c060c0518100503070e03070f06020a050f120f0c070302061206041a101110050106090806090c0105070b0601051911010c09050307060c1a01150f110706050c0109 75
    0x2020000d84d010a03504215109542c20741000c690403514402c0c01042040c0c010107074040100f00304204503800c050801161400d215180140000142610f900f41e11044065076405410600301c0740d0f13100b17003512419048404500c07071003c0740060448a10b00403d00d18400f56540080254040a00407807800100503a19000104140081108048001c0c0303071807010002200c4048071542e0004500d04048032484e6140481c101010f43c5a0500c601c0d6a1079503091246031040c1c1c91200c40c0103a20b0300d400130a81d03070f401c50420b03411903034a5421200d0740d9982c940e02903201d864505049001c2041440848006070192408980c03008043c50803a04003060080120310b0160305a2800020440a241c1d40740a400d00303024100809021742000700c441450580400c0da514000e2143d10204039101441310100302161000cbc44141003a15a0000c140d61103c0024003406444c00720070012810181c00300c02640d001d1036040c080076902d0070160203042c0c90110b0a889a500c5550021802e568402d65178000980070030f52 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 143055611 1250 143054361 143054381
    0xc02190606030303061e0b030a020c0a0f1103030a1d06090303070b09061f031403090d0c080c0a03051009031110060504060b070b040305070f020d08092d1c06 69
    0x400700e1114075609001e001c40d110b941100032150a0752580c1800c00080c1e04480b42215681c2c030400d036403580c801999800034082d803100c0a4440c0204008501807041c8100500743d024000c02c0c1d0108046a20010140d9034031652242c0f0011403406111605890090200200c0564026099038508101000040c5c00d60348001070880e05800904c01388013000360100141c0350b00010610100c01103486045451170074104510000f0f080e840c500841d03c006e07082c02d1054400109024140407000383d1103140a00c100c2c004c3e401090800e02c500808001d003481c21041e008102e98106018060607a2000b00000141c1b0b070468083d005e12912850484145104200c42d108002e48035800090460401c810001511802e1784000210903003403040704041222010410307001a414101241d68103003614050007840f80030f4401a51104078094001c007440142001014115422030745c40c0c82c0b040e4034266404501607204480006034000c0500340140741400609031103a034803152104030515480380d5500c000e484000c41 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 143056861 1250 143055611 143055623
    0x80d03140f0405120417010c1412040219081c03090b060f0a051e1509010512070c0b01030b060306090d021f1104080a0c09050705030a020906071403130f0f090c0219 72
    0x700c0c2406d43c20288109500c0341034514000b000c180094500039418044c07443e25840150581d004a011960741d40385080055005c0300b40002d02d00c0d070300c0d000f158442c1d2002c886014050510680b10004130710070710500040c01e52000c080d44554507540c00f4015103d03c070a07001d0350844a000004102a910641d001c004201801c5600840300442d4042c011640d68020741e01c404e84c0f0781406880f8a43e80c0107000d4880f0303814619102d88480c2e0750460f0403a0500c0b00d146000d803015041c3c400102c18021102081445010140c040301d096803980600c0c19654611142d64800681160420114440c22041c03030020b006490703900030800ba902c407000c4020395401036201030025071003440c641c0104224011208000c0000e11401c22151600a0001d445840700820406020340d0014a00c42c40e5035400c01903d00c4030790800b071466015107484114030b40e00c1d031003000780100060b190100040c203186c850410100303603200014901441843d007042440a814040ba0310390079406912285400e0100c200310200c03050380645 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 143058111 1250 143056861 143056889
    0x9030306030c0a12030f18060201050a110316080613180b0606030f0601120f050f0a050105060c0a12020102040e0c04061205160e010909090606080d03140f04051204 72
    0x20042601e405911180a8010001058204200c010a014114005405d42040c91003001c0601c0d0403180c0031101a490609540c000e200424125030540c0b20720321480781050200000c4200d0741c001c01c600e010072185e80c1e000f0a82c03841c1200c0d02d64820903001d44c0107240500440e0720000100f2000081c1d071800c3c400309400b0451140c008041c011400d440c507810a00958189140d170800b00245070b110140100301d1414000524825010401140c6c070101058040f080204800d0500c1c00d1040d82d4007900740c1d21080000d0614001003114034109045070404484c420041032101010707034032130030010040514041955401c1c8000a400d582603000c640c03181c55080c0000341e036207040000c09000702449024210703145161608024147c9a190020550300700c5a0a00024155400c070048403106416000114028141040c2d1010070003c1d4019400742e4400070240c130303801d07481c07a01e046003200e91202014051050910101c5c041c40c1e0184055038016001e0401e44100b103c400344004031550040c0d0203005620032076 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 143059361 1250 143058111 143058121
    0x5040e10050703091e0c0513020901110f0a0b1003020603010807030b09030a1d0d0804060207050f04020304080405091b0708030702101505210d020106080601080c010c06020c0114090303 81
    0x684a1554014100c1c1400c002c07600c8039864030840014051a0304040c2c485009020051040301280403001f4070000b030141ea248008041c10030080d4200240c0c2c1804a0321520030b4010016011031640e480e4020310004002c10166901c62810010002d03000822a0320714070700102c0543c5815000350301805541c402841c40c645103280074280040e0007030035000703da0424445041b00c2e03503004c00b40b0604100d02e0b02c94850b0419442c0c0000e031000104680080806100007000a96141c000c41c001c01111b808403003000d1806086006d0000303034442190003c1282500304402d11542c604818210f41000d2a11130512024a122a40c13188583c00390340c0603103491030084104108aa4100700030310323031000764410901001e40700d09424690041c10380509031040b2248400e401020541c020300443d5042100c04030344240d1421a400b90080211707000702c0c0700c2030042d44008030302040c00050003441c030741040c1c1d039509501200e41c4890f4025008072040c04541c0d525020242c40d0b10b008420402e000c1c070340801c003175a40d0f4200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 143060611 1250 143059361 143059393
    0x60c1c140108070605040302090a0903030b0904110a0e160f11010e03031801090507140402160821070504050103020a09030b0f01180c0507060b030a171309060b090d05030405040e 78
    0xa00c4d8041400c001c800c01080c4010f07162000d4042c1c01c03a00150000c112403001f842c00350041c00c086500300390414107a504110605c18880401c17040d00c1d9043e107403103140720b03110301d440c0d0340003c0101c0340300714041c0c00c1400440410340708840d010420090b80c41c1070b0300e40710501102c01c5d0940d510020400299030021081c813554418840c1c841c0c140642c0e60000700309009203941c8241c0c440c0301ca4410314004007042100610251120b0701180d141400c001114a0b2034440303071520440e250042c0a9100314030041c0000703083c40c0740000503400c0c010180d5440f003a00b0649040011000b0358460710508040200c1c1c4100040040c482d0740c0140e005011000144800e581030031508690602d17003030409103445042440c0100c0349a004411528983e41010020903c00e01001c0400d14255100c40000c2030707044150320a4034080c140034003412954681040340415299901300e00c00517a00030340104a003c0c1c2c401c0101000350315020540c038890301d20034010f99040a80e200c0000b8122600bc02c2e8600c010782010100b840b00041c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 143061861 1250 143060611 143060623
    0x303090801110a0e04050a020c0d091802090108011a07170318070605040608090705030a0b0a0c020106150c06060b0a020a0201090506040e01050910080316020117010503060c1c140108 80
    0x22003030b54141101c00400600c1c08550b1440540610ba1307030b4001c20b010011580413606110488012a103000c00e2000005194450754804c0c401c002c8e00c040d00785045e0340018021141c1040059440450503401c041d0500003c805d040c004105d401d02c10001c002c000740c050079002c0101f03e00714007181c0d12403074907a00480258010484146003500603840500c5801e4002041d2000d03a81685880d0040e07545400c0d03500d20302201500306507414403408000d0410401d100310f40c0341c42035503014801d124100c04044264240c48050017041188015100c107802000e01c140d0307051003168010340020a8480d039805101e09698802c0882500507081a00b03544203550300200030308010401500d0840c5098907004a5020380038041c02400d00c1000c0c200041a105d182e4001000003401c081c0b01502d0b82c4901d1841c4020f0113035190394040340840c502170180d0340c0342c11644080c50b040342d2000c2c02030041030741c0715040e0070702590240818800903c8015016010f41d01c05106002080c0c80c58203082007554100107855207010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 143063111 1250 143061861 143061881
    0xa0e06040f0201080907030b0720160614091c020303070212030a14040806010b0a09030512090411030f0f07020f1501090501050d08070809010c06021216020f03180303090a0303090801 80
    0x20344140010000038009140783c5504c2276542c07820040301c030480d0100c030f0701c18840c401000141c0d200e003681060341c09010079001c1d0100d881d44e480b600d040390203c545e42c5596000e8042d07038590140144145231201107644131003410803407005094038945045540002c0001108254024569001250008900783c0003070741c10074903180d03800841d4100703890905a03954a090501a022000d000452500c804c00d00489085002c1d60b44401550b42c08002013415000c150030000c2600d03c03903400c1c0200d8226544c018800c50340965038402c10007095039501885807500c5000608024114030440ea560015018180030201c1c03c0703100899140d240e54034010200702500c4040c0c1020f44908000080780d40000c008008031844281d00054a54a903009800140d402c00c180c000e001d4506400064085404901560158850519142d4140e82c2c8000040100c0e925881030b0000a4181d204000000c50704038881400345600d200101203a02d04950302c0040b401c0b084140e40103c2c0842c400d90414002058280a0501c00d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 143064361 1250 143063111 143063113
    0x60302030d031503110604030b090309040b040c0c020f0310020a030203090708010b0102070303120b090108100c030c0e041104090207051e0d0801090c11010e0c1c0206030408030a0e06040f02010809 86
    0xf86000742c240c0b030504540381c48000c021803500500044c0a44480090790019074000540c04500d107081742d801500ca42c080310042c1d10841c500240540240307007502c10301c0c000000715642c001228509a080c0460b08600b00c030102e6141c45042c22086c981d16450008000104241da0050703240e0501d0200d8500e040080c0e0030003400b40e41860a03070080759a00042b42d804172a01450300080014004060000902c020380e1080d82010182001062a40d00090f001241448144003002030039041601182206e01d15240500058200c018041c014646500990b080f551f15a4050345032039a50100c060480c0d024941c00c03076060300b041100314001c80d48a00400c250310448009411580801880189454014090301112a50354905554442e100e68041d0301c0341030b07404c00204009540800c519a440c8030556045106120040100301e40c41801040c50f02e805501416040c11600c0c0c60ba1882695000100f0081c603d030303274501c1c04400440c820040c81d80200d00401071031007032101600005040b41350080c501482 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 143065611 1250 143064361 143064371
    0x90e1e0a0b240901050307030b03010606091707050a051e0604030b011d16111e011509150e041a01030c030b0a050f063f060711120f04090906060302030d03 68
    0x401c10000c2e0803100b0070242440c3c400e603291f59000042d0020019006003d804d503103848408120300c1e410650000030b4614003c04d541150001c2c680780e80d550211400780700d80140704481d0805c800c0c00c0c0b01004002c802c40e10281d11000d242820042101c607080b69109880c013a110340010803214004063705a5020010201d60159240540c503c801090100f0710071420400e021280240a6106002e035900354000c03c03c1c3c5800c2c0516442165001e000c1c204424141452080b00000d502c982c84d2045100000e0540c1055084034901501c03245948070040094912050380e42c0e802c4c600c940c8400265000c3c2d445072412012031030550030a4066484000c05028442e850f20040c062002c0b5000c191941c001c0c42180e4290f443c10398055100c84504110030014100c80306e6072b070450481c5141c2e00c440013104410030200c9406940b864030491343c6040b600340582ca15000620103000f82030075280200f10b40010142c000f4940782c1c1d190203c80448408600c11703105551780c0e04c030600440c0303001d0020507208a658501400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 143066861 1250 143065611 143065669
    0x2071b091103041e080702130c031a030c040e07050a0b0d0605060403110907050904020c03070204050601020a0f0b070306030c0305010b090f1014030a0f0308040b06090403090e1e0a0b 80
    0x10359049401c4c1000d504c46008000e203007045024000c0300c6040d039015049007503c011120101d07015101110010022034108000010700040749000750404c41001002828980c03580400d21000b400c442038107072994080c1100c04105615a0321200005082d070020440c0d841d42031b801d100d41143d1440e00f0241c401c084c1080100080385000030105030104040716001c909868001090703613540300c0d1342010354100d400400c0d502280c82c4084050003417a40261b40038061a9140c9004a0b2a1980c112008044076805803004010585000d0300071740c0210319050004000d510390700c50300c000c6201c9500440c0d071a03444450f2180c843c202665903603085656071417000503600b4005140c0c88181400d000d03030a2030b1030b0040510003c907a0100b200d1200c990300f2041c108205040c60400524030b000c11a01500c1c46581c07034001c2841400c0800380c1900c5640c05503a054402406c06a035940700c090040d01d0700c219080400070110b264180024040d0003101d601d4800982002224240070460070b039002c100000b60740741d00f0800307 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 143068111 1250 143066861 143066873
    0x3071a130801110f0a02010e01050109140109050c07080a110a0b01091b090614040b0301080705030601120804060c02010c050d0f0f020318040c0909050a1a04050412080a02071b09110304 81
    0x503402e130f880011070340c0c9039905031200300e005100342060502d140d801d05000113240000b5922000c02d450307080240c140d1980e00c8202e002d00740c400944010b80c0c4103c04004040204079010064020041149002c880c01c01440340782c04d150422a0a0956001d00c2030300041003283d019110f421740c1140c0120712100116207045001e058440c580c8a01c109010b40580b0141040c0f900c0400c440141c00d011107819120358492140a513508514000c10307010b4030512001056407184441071a13401da03406425180b0340b608000d0210740380d0070202001c0f0305010b115003850300001e00a00c04420600d24030366803010380b0343c11500b009107001c2d80d5246040554104004075140d43e2030808a21825640a5601042d842c0309501c044030b45001c03980c001c0748118640814801914400c0c0c10a034518060f407500b480804191130104000ca0f40242d0b00100405650740e146104540a88480c03580100a248014200300894451030490021002c115440c07414208003444004030910502e6606400f0001c1c1c9030071031520f69109 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 143069361 1250 143068111 143068117
    0xf15081302010f030c12060b0403020a2115060e0a0e0105221101020a05070b090103051b16060e070305011401060f021b0303041203050304110402030c0403080903071a13080111 77
    0x74010107031501e581143d254010303401b40144a016020401000eaa50424501e264006002c100d110b0407420320000f230241d50f4404000401c8185030b0a2140714026955408060408100080c1d5041d0700ca00002030101c1c080340d0f00c5803080c1d04090020424101c02c0078241d08540d00205050070f519014415090b402c4c00b440070300c581ea00cbe44891180364a0f480c00005070319143c200d110041152082c100b01181d45121000509080407003070300c00740701e1901d4107118514414088254400026010b004c00324502d454803000d56945401104c0004880c0c00f00c51155007070441c03680050350075a445a62441d03804891a00b03d80c01440f4134a8200b10343e181c070400003912031550400c9000c807802409205001c039501030013103500070f114a0f490071440818a00c0c0103042c982040b58161000e5041c518804014180750003103902c1686426070741c52820341159544900e54100210441d003500c0750000102e0341c0402400b00c00744d207035041d122141e25961804c548600d02c103040c0d00301c01d805034101121010000c04c04026 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 143070611 1250 143069361 143069387
    0xc050a020c010c0c030506090f101803031503020a0807030b16051909090203011d060109030305032a0c06010810091101050a0315140f0105030105090103030c08040f1508130201 77
    0x110f88800d52143c10520701103040c0b41c10151903801403405101250300c000031140184080101941e4901180111041c111074980b5144a0844030385001e00c000644070368420030324a000b90003e4250701da1207801041c02a491a00400c181e07902040007401800b8038840c1003035003c0b02040c50307044003c4078484010b00c680200400142451040c8100394030260088506c003029051a91086441c1e40c4c0d40c0c2c5518903801c41011005030030225180119031030b54401c80303596081c0c83e0152140381ca19200d00008003a07071400320240f0411b071041400030f40728038840d41c8001d01110b100840200b61039418078040d01e06100c2c2d905204c0401a19100d60b04000030928803040c806050300342040b036229483c03020141c01501028a2002c811b010205010410620350f03280c03101400d80903120554142e101310015100c51000303000d0158050041001000003034818510100424401c1501e682820360f52a581042c0c807889800030090083c01d044a24201c5074001c3e080baa1040f41e40c400304400380c0158001a2092280c2c110f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 143071861 1250 143070611 143070617
    0xb04051003060b0d1209031719110307140102040503061305100f09050105040308042901090e0304080d0f1d060702012007030305070204050106020d1227060504060c050a020c01 77
    0x610b40300a0350b802c0401345546030080310140c0d41d4590907900415210444c04121640c41c0c03030050301000d0025150a4403407411987d45004122444600150703003c004802c4180e0581c48100418000a95401074240041800c400003580340c44c208010141494401030051000180c0c0051010201d00c0001d221004480d010100040c581e607940c917200c01804600740c003e00300e5803c000500c0b00b0503030310070380040c071031402400300880708a0038800c554070507000f6403080342107148101e00500408100f45d020304400f00744641128a030603075071031515050003550707810100868030103001401e0b4560041d01905004440802d5234400090400020f41e843c0900103000c0d040010790060000f42e54021000045820710002c00c40701d6407652032a0090141c2d000c510101c0c0030354100400042c01c9400040d82e401c200115440312402c21180c0c0d0441070007000300d9445d40301d24451030510382c290070b2a10004410400c0c01003902160034542400c0401c295a007283c03001c1c0c1040400c101112a02d45d02142d20480e4070700900e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 143073111 1250 143071861 143071871
    0xa0303090501230a0c0509010c14030d060f06030f02040506070609060605060408010e010b0a03020901060f02030f120405210a0309140d02060702100905030a050705100911040b0405100306 82
    0x424564014600428840050850081e40c408a05400f40c0c030184a0000d0b40c1c1c00b0322501140038412146c0f4024041c089010841e0b80e80d1100c00125030f40100d0200f200714000b100c1c1456044040f0b80d040c3d60380c03035014241c21805484180140340e803500070301c1041c0c00746200640c074252030324000c03500d54841c18402038070540d80c80e8a49020002c0a802c864020180148080e0300c03180c54411207070086c6a0700429100b59881d00b0140e14407420141600002c6030340007002e49019030b00e0500c0a580382c00c0c920381c1c2e24003140808c000d50441c1181c0d00014010301246501a03224030b140c185001c502e00b504201040e880c0c82d4040b00b1900c2c1598451040b180018542c1c580869991140c0ca0242d01509400c1040c201d50b0013400e0721000d005900040e290f2142006508444102c40705081070012524042e1018050750030421580c420070b409036005100d085d20580c1200d0071445202d28800486038284812a90760407205070249a034a040c1c001c2005008003241d0400c0707075003041c44034070b0544030030740c40f008000c65156 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 143074361 1250 143073111 143073113
    0x12021908160c060908010b0904170f0f0403050c010905010203070512090d02030106090f1d0c0118030605070f08090102090607060903020f0a1401110304020f0d021f030e010e0607020a030309 83
    0x101c081d0703216941c2c0031450240650710344002400380045030003010181e42ca050943c1e0007500e0100318140c00b540d007000c80354203110901c5401c0e0816600a400300f50400e8010084a864859824020702c021406100508060901e1100050101050b40d0089045510600c00600070480108400411000c000a01a910040c0c1e1020480c4102c1c43d5001a40c55440c0c1107001916103696004918003131359840d0208282c0802c03001840c04400200c0c10030002d6401958030840c954040e100303070b662245a42c01e174208141d99a6442c20305a4200300c40340b1000404500195001c01c1d004901d00e0f400140c65002542080c048a0118405000312440640495265a100700c1494024441030301c48000f110141d070712003042403c00500d013940c200e103c011150304e80480514200c41c01025603000b1680105812a458001c0781001040d030b2114209aa10804101c14a4140d402600010010740f80703d0300c010925010110800c3e0031075008540c00c1000340c2103c030810000c02e5011031000d0005515042c001410041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 143075611 1250 143074361 143074387
    0xf15081501030518010e060f07020313090504080904110702010305151819020310080d080106050405010518060c10390e0301050114190302010801210213050412021908 73
    0x3c1c10a604441d40782841243c5003010200c7c82c10f21412004600700e030551609081284c0c7c92040040b240b1700c07403d400b44c080c0030b6080031303800490700030380501c0c61a0b080410b107200041c11241041136852040c1400180d5000710358060040b680d000407007881c0300701c4c2e0404100224006c0d00a00008451803141c1341e00080b00d00c0f000600003050f20b900c080c8215100d10301030030f009641c01c4450240c0e058511500c031101f460980700d502500d060f1350146c0d5849080c5840d00b00103507601e030010040ca03070080402d03901c100116101d18001e00b0039074201c01c0003072250281402e001c40460740f14061282090a6544800380d100000405110a0368810300411240e84a05e05044940c1100411500d915508140000038000b00203e80c0300c04100049a02600000d480385400c51426400d120090200b041d90380100035107180d1003030420f101b4020321912001d0f10420340c000b50b1100d070741c20341c2401010b95441c1800148650604148510041400102880c030382c600c54049003041583e100030400c8400240d001c0380064 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 143076861 1250 143075611 143075641
    0x60a050706021801390f1b05040b030102070c0b030403050c0d08104104060e150604080604060c170403090608090a1106030703150f150815010305 64
    0x50070000864460455614070307118881120f5045000030308810100306800314042080c040800360b10720030950043d1480481e2244100c2c2041511040c0070f0500c10404120709201c8221b03404882000c5401c401d040c0000c2000321002200454026031044c4038580000381e44846078001d88001e000081e071a59a00d107011a81c030320920607170303044501500b043d00702819000b0308024042c00f13040c05050510307500c80c000043e00300843c2c4020100500c04204586c01c00065100c880000c940d504d030000100350365000030030291600b80d4800020401c3c103500700316031030150400c1141264000c5a20f60315080c540b8518960b284005000644041e940300b240c0da41c003d026000001e070380a502d00c003000017883c01d0f0802511011240c4620008a9090300008451f00b8001c51403050782c550002c01d42c4074094181c0140180c91700000e05480a240c0c0d21078961003103411022010000303014076610341192900b80310701d444024214012401c10b10800340c0510070200420b4207601400e21007841d000031b0030b47d1803031403000002d5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 143078111 1250 143076861 143076863
    0x90910050a0909030f1d0d060e01060b03010504060e012601020d0c0c0201120b180c0f13090e06040c0b0c071703040609050604151b02031006091406090105060a0507 72
    0x20008480001c0c000b080e80d0485645a4000d40301e5845c0da500c2c4072010741e08460000e0f5000810170220040b4152131030801d2002d412580100c4000410f103400d070b4003240c2103950035042115000d802000400161515000b002d000c0c080d4808628042e51600c45112015456540301c0b2140607540b104110b0041401d506440c0480e9981c00c2c284428000610050031941070a0800d900007062510410204020b9000d100d4a12030040c01e24a0348007000b80560720302c044060501e1044000c00c0007240c10070381d07070b075000740801c010700005403505c1e6454810448101e84460720441c4590f0820030401001c6654904c021044840540025a0300c051201086041ca511782d0052003110ba200604110380c2000000640306035200358481c0d05000391984100481e40c01284100e5401490003c940000184a050011300c200980e10802c006240e05900007402d0003c641c4001c070720309039074800030003954816010381d503c0440c40781e969150504200001c035807002070501815002e03000009002840c01e20400032140c50b2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 143079361 1250 143078111 143078119
    0x2040b030105060c1f0914070b041205070302030d020606010f020607080117150109020408010c1106270601030f030e01030903020a14031b031206060f071e0b180714010509091005 78
    0x9800c8170701c14010700a0440942d40d010140d0410320a00400003842c0d001c0d25402d901081c100b61912140c00c09820b441c02c4125080d00a5031b00000060314100300180c401003943d0041c0255140450004015010008041045510030341c00c0c00a01c030f40007100700b0f0641d10301d045ca40000303a050700b803954546030240490258038564140001981c117603560141050312030300002401100c009007030856007040300510801c05504034101140310107210000d0840360a0516018840c407030b00200100341000c800740c0c4251110140c020030401090303400300401d451910f007424100320000c005c2e14003d66a290101c1c004010003146588030400c00010020f451008010f90003806114420ba540c041e16030300603800307200b01514808081215458042c01340d4618904501109003404030381d454480e407111010b01010150f00107c821100801d04005e0002e02c214216540280028404c0d43c80d03034501540350f448a0005c000b244082d00d22a80d00c181168148002241e03412015281c40c1d50483d81d801c05a8449030b44 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 143080611 1250 143079361 143079403
    0x13140406081006050a060c0506010902130302090c0a090509190c050f07050109060b0402091c02040209040c0509030d08060307060509062101030c0e060d0305030703110301081e0102040b030105060c 86
    0x10702c0015049070007621002e032044a62196528811740301c04880810050054000da0014810448280d018005416582203d0f8458542c0d84e0080f8415103c00d40b20400810710000710000e0f4a5000f03007002004103019240031815160001d04100c00000200c650110075882c4c02490100c2c501c0784054031014242049034076500e0701c01b0300c0c00341d008011000007200c82a0500b041c0b4032161030719109132901e01e04080c0c8441100f0b07600141c8281e001009800480c5d02c039a0030f10040709035450b1803040703200003103060f2211507503210040201460520038100440c104080f500406c8865100441c3e104105c5059080041e1203c281c580014030314003904111681c0c10090304a0341741041d1100c807202e03040380d0207460010a201d4944402c0d9a00210490b130350b54018891044940000f4428401154030900031321303000492880480e041c00707240d402070744100d607540c1c845480d80d6100d2201c0025030064000d0304008502e0075192010403000307400f0500c01c0718130984003c1075081e043c0d242485031424404403001a04a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 143081861 1250 143080611 143080633
    0x3040905010e0403142101141905010e010f0215040b15031f0b011430060f090c1204050601150305150d0c030f05030307030507050c0703120c05070f060201111314040608 74
    0x103040c4482324141e2083d440380f41491700c0700c03088409820654806944855020304142c006540000e80c4425040862141c1c9500a010a140401c0301c1d000c1c1d4410390070099182000006100c504e484040c80d580310780c1041060f10074180d071003403800700340345035801000c203000802000582d40311410300440c01070b020000580351807a0484a036040c0c442c449010055030007990061072035280340d008035481c60b04507102e10a8030201d46000a4041c2e03004108460704c91401400c1350000b21b400c031040d90700300d4040e444030005111140c040110185008441d240810a0745084281d003540700d42d010120a000c0c04128400704103010751a460b40e0003031a04908910f0b10804580350a13540c9034811503911001916103804034070401c1c840d00444000944030001020740da825501e412525040c0c4181e050240100c190034403001440501c6a030300240110b01035010803514241c4040c2c2580d010010410000d902001381403450711080200a040d41e02c0d4940014a254580c0c0c0410001c1800b900840450711801c245c7c50 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 143083111 1250 143081861 143081879
    0x1c020409060203040201080115050d0203280b0901120c031101051603080103030e12061f12080304050610080a03080603010f02030901150602060106050d0509030409090503040905010e0403142101 85
    0x3d0300840c0700b80ea981d0070340e0b83c1c1d0b2014000c0b0303d00000383e02c4002032801c02241c00441c540d42c0295411401160040345003c00c0280c425014091840440100d9030b110340e07036214185404800703a401040031424580100309d0560794108400781e1400010072520800200c4e1300141d00c00c2e01650a42d0001e491035102d0101d090501810102c800d100880c005120f207141c05070903041c40a8442640b481c280010061034a9041c031940299140c0c0c04c10811010a038600060040260860806128003072005144d0740e0825040207424140d0041241d40c800c40c04072030801422500050581c5030707079050b207450491500c0c0c413800a800b600c070b144181ca6030706001200b4042411810351040d894890150410703104255111000e0b45c913001c0c00d00c9000c0202d1000c1c0b00400525100d0b0700110760056121041c0e078605512580b801040391308944003951a0760000c80e0901c071000c0c076842103d0150a101e40764011901c0c150350010506203001e8800c00b02502b01041c12002d000303003403a0843c10048071250f585030540e1261018 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 143084361 1250 143083111 143083117
    0x120f15040c080a0201050711030a080f0a03060503010e030714030f191227170406020105010e0a1506260a0e010c0905031c1815032403021c0204090602 66
    0x3500c41c002000700000e22107034000794500800e42d068559034288404d80c2c07155200030703070b08196298040c041c0513078010010b081070008265240c2d000304540c0d21080041c10080440700b99803c5103009070300d480e44101520a0000030768814130f500c051001c01c035000d091552815409102c01400740e243c804a07044c43e80c2d03a84242c1502c02c0d81400d5072400e203901c107810f5000c03090b80d201c100d404000e40001300800d1803000400c034840c0b81c0280038600110001c606c03041850f0702c0740c0c0143d01520050b55507000500c10045400704464000725805800c1c0b1804440e107010381d80c01107061040c1d0050010101c6074010500c500b01424490030406422013810b89002a14100540a0000c242804e5407030940104c05143c0100c00c82d0082e070b00060001c100741c00030440802d40000e01000c2041c05d000708060612807864441c0b0101002c0c0c864180180414038201c00040d00f9078002013141ca400c84008203d01c544200b11920901c120381c1c0403203100481d000d40e200c803160f280b4240ca03000b07074026091405038010b100880e001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 143085611 1250 143084361 143084363
    0x2071509090f050601090b0f0702060d02031e0c03070f0903060c0f021011182b1106040b0306010f050d0207050a1103030a021005060303040f1e0801020405030a02120f1504 75
    0x410b00c2924500240c40088880484455010804030182400810350440c0030f0024484c007561024a0100c0503000036020390464586c006400d50008204054004000d18407011502034071425070300c6041480781d030900c5000c0103040c00c04000722940c00c664110300c2080450001c54101c601046241c0000c2e40c01007403200c1004451001d88501007171620081c00720b00c40d1a804502a0840c02e00b0280000285520006040c441550080c40009480040741c0519202d000107400780311229240c41031480c0c00400004c8108403a031054106000400c0140c00d410100c3c2d07840013007480c002203c07260300b01d000d403014040d1000c0b42d03108500c04a100000c1010004c3c450540500505e5424400c084503002c041d42d034441d00d10b00c0303001600001500c2442070b00300c1c5c00194100c080102600d09168542c003400b651900c5a03480819800020750351b41002e44810961000a0308a050003907141c18100b0021983d6440074010090184004071007828101600317200c9032400004800075920700050604952001250070b0750 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 143086861 1250 143085611 143085629
    0xc1208071106040f060c02132301050301020304120305040309150302040e090a0512180907050a08060102072105010f050c09010906093005060a0e0f060103020303120702071509 77
    0x20740e80e41d03070b241103010755007201c03110340d000c80d1058248082190700b069030000498020146c00c40c07000080c034040c01104588000700786081142205200d4030f100c1e0480690045010364410024480401c11803510340040c0c880600740442d1070f84561030100d50301d40c2180d2003601125000c0c40498a4142d02d500104112901900d412140381c0311443c80b140c80d00788481c0001d00c9540030445c82100c0346206009082140c890810704414409844041030301071a003250503000003500003883d25080c0c1d0b04035070b42603048803080c401000c4050400901c038060800745c9441c03689a5114000c46810000c094020080b04111072905004a080c03280e51054241c01114440c0e0108040d40c3d030110b0b0081c420503440040f60031801400c50142d4240c10140740750b11a407076444100301490040000840d00400134607005d546030210011725484820001401c0441e01c2e010100315401c2800100050307540002901d010902c0c10050300740f29111000e091340f40c500190720010340b050703403089540400ca0300f208281c0c04944440e1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 143088111 1250 143086861 143086883
    0xd051006140f060d0b01050c0f0706080a1a01030b06090d05010507020607050f03061302040905041b151e0504080601060804030210020a1209020a12060213050a030512070c120807 78
    0x20040000c4510050203040e040031081c4144103140c4c1898009034071501060400a01c0c10701e0702e99000d800d085003807901c080305070301402c1c04000780d903405a01c0c0341c1c2c8041b926034100045040c8003607a2141441d8940c07210704042d201da0000c40c0d203a03640c0d0200c914590000340403100c2e01400d46889070103030504492110260080400040d5824061401c07103614200401c6410302d140d456504011001071400500310102d9070078480401c20910b41c0c46a0360041e030249211841100700710b010000304901030f070030402c0005004510348403440d400250600c40c55502c1081c0c21554414040200ca0600542c0e102005500c607090000811940068401380942c0c000d42c00d4418102003d1010300992261001c54000601a884200351210f5690300980704a48020603203806190f46e014106100c0040f4402501c03082d5000852812030f80218018034001d04c015a000442c2900e0760311900d80700c5030882d400d0881050001506402c00c000c421b4401d01401800c030f0940020851801e0407009074010500448540c6030407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 143089361 1250 143088111 143088149
    0x3020f070f0b011d130f0804060203030a0f0209060405010305150d0b010806070f14071407080318090403020c09180d0e2d10050c0a0f03230f090d051006 67
    0x40e08081c42d020004c070f004400c0c40e440e044428a980c21084c0c0090f0b40711200300b4021400602203000610080c4025401581ca0f420802e02a1044800c1c000000342c10b0340c4100200c0c1416102e050a0b241145c2e42402d00060698540303103840004c1110614050340100440100030402500280da40c0c1a078031082c1c222040795a80807415184c0e40c58a0340c0d0000420003902000f100c403880d0400504a8500c07840302455901c0c81e268101c0d2914090340c003e0035041d080400c00303202c01c0342d0b0745a58521548044641040c1814681c601a444082d00c031400ca00074041c9000080000c08494480c680c1010510101d46041da8003c200916103049004201c0c450045070121080d41803070181e0a4048002c001c90908030540c4250401c100d00d01040c14400c240302d018040704401d04028006d040e1342c180100301d00d40c06042c56203001000e400d1403540c080551b04004c10b04460b9500301c2000d0b1172020104407085580c50510724005020074045910082c0705200303031310318581800026000801140c00f00c0300000031403000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 143090611 1250 143089361 143089379
    0x3041509020d0204090809030a030201050105010f08160804082203020a0e04021e010207090e03090a080d0c11010c0210110105091b06090d020a150f0f05070b0703020f070f0b01 77
    0x4480082e500207807000090015140c10383c0710001c00e600c07818984e4940f50001000c0b03418134544040640150f55214010003495801c00500c2c4e00000305450004400c0c94400b5400d2613110300308851104000d0700300f000a04101c1907400700c2c1c0501000340e0885118000c5200c1141c0c0315001e03800100d000d21000380001403800c00c42d03501c81c1d0283d58000d007141e01c0d0007402035800d2801c0200025460451188000c00503800c445446068550f00b20780c0c02640d13850ba00380e400d2106000c225406024640d10010032034029540c03011004480c0d6911120032203982c0030110040356a07420110019611940050811010715000039001c1e0714104014000d01096864107903c940754141c03030004900500c12520882680e1414200a100600c0000d09500c40b40186401099048960360400102003264114044034030b40c001d06000c1001001d450210018810365130000c1042c052800d00806a43c030710341c0407a0045007e501694a5041048141c0e5214003203400c0c01c06100c0b00c403800a480103c5050000f10f1040780e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 143091861 1250 143090611 143090621
    0xb040902060a0804020f0406080105060418050a380403030e070501051b0316030822080a080a0f05090312010e0606030c0705070e0a0c02060601080f150402070f08030415 74
    0x40c00400a9050040c481c200f6503060400400c00ca9011840c40c80b9400a5070b228420503018106003c00080c8600e003840520084901c4e0300304000000102500400c0020300c00550904010782c04015002a808010304e02c154140d01081c0c003111814001104d0000c41204168940c0300d00c2c040c0c0c0c1e0612007046041e070110385070403e6008450014000300b020102c1c0d40990280701a490b004101280c0c500b1b100412104402440c1d60000c90000d0004003e000e984500140b00484481e0610065486400c0b16915841c503481400c2611040c442c00301c0000300c810180e0f03801f03203044201d41503044c007003131802c5a405603c1e07500050000c000000c9c1c0a001180045c40550498450603001d0080e51450321103102c10140303038010103411100c9200e090000b090386074020300300030301400001c0e001142e1645a82000380c00c00030f0041a140c1000a450100a140d10003241303615001a0002220040d54083c107010401905c11356a0103015199415140700400c0401d100544c4182d00510140f182c40c6818014481603030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 143093111 1250 143091861 143091863
    0x5120d0c0f170a0e100c030c1d01050405120a0609142a04020912010609050609010603090b060f0315240102060c0d02030c0904050406060303020106050303070c15180311040b0409 78
    0x1034482c10008000c41d40c6035110403a082ca850307040301c10909003d6450340a070380310926001c0c00a61074014154283c0c0c0c020107814211007541c1c400030300da45007440c002400c034065031017410310841070f0510001558000303100804440e42c02000500c502074290802d81301155250004003c0d910812641c6100081c100a0840382008010013241640c035a080400000c2d420070181c8560002038043d00140519007442075400401c80c0340000b140610301402084802170059100c0300c2810704040c45140001c030784000365540003000303c0c0d13078415010a001c0400c0c50480a0001000107580790018444420a561500d41404c03184c214145040c0401200480e00e889040e250000010414807086e1860320803500a142d101d0851040c09040c01400300004094400949e4166601d9540305014002d041d030a002e10400703840b01780e009606d4550503688030140d04500340308010707070902c1e00111202c119124001120110107041c1c0e81d9104907807207042141e0104400440d5034440c038508054030009043c90b014241400b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 143094361 1250 143093111 143093147
    0xc07030b06030f060c030a0219030b0f100c0303050406020d0f0506100903030f120b090a1d010510090203090f03070c0602010e0a0c0303051b0706050a020105102105120d0c0f 76
    0x13a84401e030008515802c00b03040f01101a40a02030003100019981d0000c040054030354004c12542c600b0b00038010440301000e032040c000d42c0c0a8415050103504040e5011045505203000180c0780e8031401d2040090041114401c0c0d40390900e59000000340e90398020b45d020340012515111310f45000c4d0301c10b5921131345c43e110042c0801c1000090007021030051103000c4144080300d801081640072240013508040c4201e0b41c01c045140c0c2c0d4421036001040c030008006561b405e02008000798106801c1005180c4900e103d113000c075a400100003107003104203004404440e0000e0046030f03120590382c40e05101010040c015400158649000080c594100003850720b8400e4101840c5401c0340e00b1510100ca807580031401440c10114440407024504604002890051000f5035401c0d0b2143c019100003401c0d11406042564041311148007070120340d460720040c0080d60580c11070014484010f14040e824404d01c0000d07039102001c0461000c07078528841c3c121907020b07203c55456006922081005944441c40910880d6030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 143095611 1250 143094361 143094373
    0x509030714070e07110120071b0501140c0c0301050408031e06010806010e01031b020d020d03020c03040522051006030b01030911041a03070f090605010f0c0807170c07030b06030f 78
    0x34080c040d507200859903010300000700747c1e410807403103a11100c07a41041c0b13150581030000303012081c0a814107070742a43ca42283d808003203c5180000007084210300029803519a040003803c400d200b0001c1020314500c000103002481145040d080070340d40d98101701c5584420200c241490112411803034030240c4a036805031507900c031940341c40c80110f4034500c50420382c4d4141603803408016581c10b41c1c07030042d040100c03203a8002c1242d0411200d000381050070f03d080003010300d030041c405210310071004000d0b20203482050740e03011140075072203003501d8bc030792100c002d00c0420130310b000c0a00c030240150300540c10a0340c5550700c0a00c8070044920045003290355000c8050070032002000e0b800302c05e190681003e03085070001100d0141c0b4601c5c07d40040d0501025038810b0120401d001810403e680031401501d00411003400c00c0c124207031000720050480d03094424020800c03000042c07004101f19801440c2013071481c1090085844180c1d46140d079035915030601040c1e42c4d00c5404c00008500b8500040c2c0c0d8500c0b0090a0083d08c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 143096861 1250 143095611 143095621
    0x20f060901020a021204031212020d09050a150c0509091f031101080709181d010c050403020414070203040b030c0d020c0c010201050f09030f070203100c1e050a0e0d0f02040509030714070e 82
    0x20341810303010708481aa640800c0504100e0055020f00e54025003700c01504014525280c00310aa98417078419841c20390607c10041e0580e0341010a86030540b01c141ca07802555911107000c5145200d031100d03000b040e035800d150080103101040e811917054134402c1c1c940c4800c0703469a8a098400c500c55224000e0f9200108901420660498001d03480390b00b0100b000c0302461108002c02c5007520b90101c0750400107000860304000794078060150405010380001c4110190a140f2070007904c0344a43d02954980440010210750b112014400311190003400803008c541301c0350002c021680310080b6106041c015800c043c0440d00c076407109422240590a08401140b80241c1c44504410750303000528140d80c54024030300400b01241540c0569450100c090f50b07000c20813040383d0202040c0004480c082c2041100501200345c040350044191503c1d440308940c2d440d421b607064900500c1c0d803e900b02000350001d09120511641c04800400340c82c40703d119100314460030b01c4900e9403650f40d0328544102022100340b000868 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 143098111 1250 143096861 143096867
    0x30501061a0f0d090b190b180f09071802120603010c1215090e0d020f030a020d03090f0606090e0c1507020f060d021204060b0301140610020f060901020a0212040312 72
    0x2024211a540104110400383c5441c00c2d00d00e0211030251b092000ca00f40c00c41c1503030b00c600c81d502000c401180c16aa03408841c0c82030300070325040140500080c25410011030103080c02000091700509c2003075000507148115100e10300194005610101c11894003074089001340c075040c041ca000da0925645c5454181040d50382d08009002840d80c1104c803803058a9002c10001054060140c80e11001001030020310b01c203c00080c40c19100a544854507001403040c4403ea50340418405403a14040c980800d01d145103050117090b070301c1200d2005105520300680060103043c1a04052b05507a00c00003900d04503d40c480034400315400040c400021342804201740401031070101d266500b024006001e00d820408034500c54012a0b02c00f640b810030008810b0304202c204002d030b018408a140080d002440844c400400490360703400c01421407071052044400c4003900700c0c801c1144100f007081c68422240d26040c0180c29038002e40c0b000700d29a006000344100039803503c04c4001140e080340c2d40040b0503c8800701ca04021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 143099361 1250 143098111 143098117
    0x30917100c12110c1c05030a1508060403020d0816050d0203090c030f010605090606120a2013031505070f08040f0210050d1a0d03051606050c04030501061a0f 69
    0x900705010b10a80c10b490114a14419200b508103040300d00c540d901d04140c241ca10303050903402d542400081140d05808481e52040680307030020300c58040802c842040060955041c4a10340140c41540300d00e070700308014107600181401c030004003500d40781d4454803008042c07600c03a41d580e043c0c400460803c21001c41400c09030750055030302c03044400503076006085880020b03041101c00c109003a2560b464540078800b501d0102d03062078110034115a21442c002e04005a02d80031100205001c0701c0d80c7c0c1c0d5218114a502c00031804007005d131003031002103544035180c0003000400451400142c40380c44000c2d852a040404520030303240a006151110088501c42720000c84400e41c006000f00c0300c4800c1c107000d040041c1c440203440c034000c00544e2926504c3d6186a0b84210440b582654402c4848803007406458036500d03030b1140c0401c12509803810315505c01c8029014880d1050391074009151902e0102041354000c503101c0a0800e0300d110307400074071105688440c05010390540558030050030100b081500040c4503040c001f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 143100611 1250 143099361 143099381
    0x1b02060c07030c030c0810020405010c0201080a2c0601080312040b07050d050403030e1605130908040509041103150708060603070309060f05070311030c030c0903070f090903091710 79
    0x11244202d84035521540342211503413045600404a82050180c03141c2800700c8200003408132021401d1a00e483c000a010080c6100003a05001e49100480e11442481d000b100700800d032014010160034085150f40f010720603408002d46240500800425044004000c0b2441a50040b6001c0440d4549880c1c10101c070700301800744010300c20100050b50000c6130500802d8410350080d2000150071910002c01030801c910030f040c1d04511107401000b440307159219440784600c070055860004071001c01e0302d8810124800c540059500c2b0046d5020001081240c07502005480000d6051303410f519440104001c2101b420344e03151000c5503848000aa40b410002c0185512041900e0085050011a02c40700211902c001407991101d40360000c02c00e00c81c0d0180103d101414455103c03925503d40055810410700015003516810300000071604084c1d0f030104202806000380c1d04080b1902070b0741e520031000500070804110040b41d590540014900c080007050200c91640c00041e180303614020342010018803503210 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 143101861 1250 143100611 143100613
    0x405090c070605070e091f06050f09030703060609180506010e0c0d050412080601020706120f150806012c0601030903030f15082e0e0111070b0a05071b02060c 69
    0x4100c402040300b07030083d00d02031104c0d031311000904107145050003444e03a401401c4490000b5031084603002010480c05d00b0003151020b1400035155400784802140302e2041810040d130510030814044180801540004c040707410343c1c2c1c42049203624034400441140100c080c054001d811503801001030702a143c0b29590b00021000a4500d40790a00b080343e001c5440985098581d0300043e070f01c0e84115500000c0300c5400c843c090009003890351801a005125131012000885090f07294444c0c109100703c141c00401c0703212000300c20b0741c4a40d40c507012065528030b405d101e0100b62138070225003640503281c0300300b4a81442c3d0070014076403210799541005402038007514108608050707441085d02030301c401a11404054995040d900c4028520b0480781c40c2c500304000c51410592a070350075400c0f1101d903c001c45400f40c1c03c2550004a2510506566903004010280c2038040c40b0310700142e00c108001903000350314820340e18090108065115800119131605d084944280da0b1181203013171001510746503002c0c010f031400141c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 143103111 1250 143101861 143101867
    0x3a05101e060810030614040308010e090a0f02060c0304151b0218130204020a02030a030b03010e0c010c0305040806101502010627020d0612030909050603060a0905030910020f210405090c 81
    0x141d1040101c1e01c1600820302c42d002800c6c01d2004159001120500400d4141c0b9140002e0420300300d05919000f039410003c00232a0710320b88140131522204160f848900203841034030345499461401c59522040c00c4c1818002981a80884a00d01070390040c0501094018107505442c0d080700244040c9086d02907d02d40d0440d50305924840180e44a000400240c82e10390b014580700e07801c00d034018007910f580d58140b80c0b0036410601c0d070a610304030000b04507291020920301080c1610b107508007600e41d031080d038010b40c0b801e000701000c11030a01c40c3d251240301140c0700009002038200012400300d0072110302d80580b948034041d80c03411000b40d40500d00c445114064000d0010314012011185a080f01c09a0b0301540c0d81442000f5898203040d001880403006000c000810300903481d0050020f900c806000301001d00c0c0c59a10089042401401c1058415110000e042a0b0303039481078181c00b96480d050360030140c00500c0b51340e038001c502412002d2030f07500b0b01c920180110304041c1401d00304808088010484d4681010034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 143104361 1250 143103111 143103113
    0x3030203090c030a030f020c0a1208070206130e061809060a0e0c04020d0b040e1b0415350106060504051e19090b01030905033a05101e06081003 63
    0x2400865504c501c2601d42e440582000b00010f42408030000886203c1c0007010b004200340d51341003455616080c0c3c0213144070781c0c42150340700140050040b0300900c5400c81640d040890071400049015000300d90885203080b5000c0041c000031040b00c41190803004ca50046c401285820a0342e8000101036034545050343c2181c11004041001c030f8000c4002d03481001d444120300c40302401d05c2e1103803010b0004102d029041c10700880301080e143c140c41c03a0b1f03120b000e16543c00250703c40032400c0b00b5803009003410344180a4462018280c0000100304038454141d901c1c000e041c21444541e052088c9030407100c1e592503031400c00e842c0400b040039100e4503580207040565000100701c150342d508426040b100080c010000d040a0a00f2914012200c038294221f050502c1c2c55601c401041000007501e808445881000d20103458000112812071224081c084104404941d80175034101e554010074850b40160002da040c0c04d80ea520580010110500e100368441c20081060120034801c1c080e0300d030700100444444030040e0b92 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 143105611 1250 143104361 143104363
    0x80912070b121603020403020901030f020409080c0d08070810031104141317090a03021e04020a110606090c040303050c070b0406090302031c080c09010e190e0903130303030203090c03 80
    0x200c190080d8110340c0380420400c43c030031861811114410580740442c2407500f0742d80484d8040806000281c540c0310b0100c202d80031503603281c001d0008280c1c030501464031031814000c002d90310117120078040e0200b440800006c0c802407146003c04d1240b01d5401b0110041842d507100d8894411014800940207900c80d10300c07540c0c110083d0400c1d401000c021440000070740c4a800d1014410102c8441092441c2c0100038031080d0350f50320024402074a404460301c08240d4010503806501610341c2c80e030350f0b410500100d041c201c401e8104c04d22101c60500d03801902c0880d5281400c11440000468044800220078442403020921a00113441411198000c0340c8495840f031150001e40d400941c4008001040c51009004509040c081d0140200e260501d00602128100c00500f50100080070020341f5200401c58445c1d50384124004d0002c10400307400c0311990300c2c0840e80c854070082140a02c49507145a5008199000301c0002103488482e0306031180e031482ea05503641100690320241000b034403449400450580c0f6a4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 143106861 1250 143105611 143105617
    0x100c0c060c0f051606170103050607080a0b09040302010203150303040b03010e071b050606010f030516030c02011103010b07060605010801031e06090213060f050d08040b07020315090109061107080912070b 89
    0x4190b0140c50861171504078000e00314100e1052405100c858100100700264000a90035000000d500f4030521940c1c4410684004040c4034031075030390000d845001d2100f03064040d40214041c1004080e00e100054606060569920603407007800c050000800c010090f01002c2904981c01c410070b481c1250483c201100031400c440785601c810b8030316030411400d1144941e0800722141000100e82401d00082c940110302ca407141c2c2c0c0015044091640350b031403910b1500d200303600c11505418012044c1c0c4e101d58486c0c1d101983d9070010103044480c41e02e02400818550b0285200300d040f00e0748000d00c15000300102d00c41702c0f03914401d0001203441c2501c036491500180e03160760038580d101414900008069142c03958207181070211340c0c0103a003d83c00c1c0c0903078000031a580c2d100300c0d42a201628030890b903502551020914203c0c41702a45c04100f44071360144540620103401507a5480d0041d44103001122200c8205400340c45408801481002d00300720004503800d081054070202803a09040e901b10030b664030700214960f4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 143108111 1250 143106861 143106883
    0x7090518070b0309150103260c0102042402011107031803020a060305161e03091e150b0406141201060e0c0a170f010b0c010f0f0506100c0c060c0f05 65
    0x802c011041105458041100202c0380703140c1d031682440c651541d00c1d09000712110010407521811783c540714441b100a40c408032111118820021965165503400201e484171072100811000185142850b0100c0d00c1401001c0c168101c0480c030b1450855150b6080d02c0e01400744000d105204650900040560303603800070040101210389021606203460b00100000b141d05240000510115070412210004010755a5140000c83c2c01e001030356081e541491281000300c0d410032032201c114021403204000e0750140210b00905079104c140000c00141c030800040d102071780503080c400d003603800d000f800614004a0f82060289940f00004819403107041c0703a1003402e0116909503600c50b0000314094120391021412030f440c008140032074580e050003c40e01c2d000c58018800c0000b56440899011106a029400701007550700b80201003004e203852100b0240a808200c410034400c1e00300390340d90030726140105000352006a02043ca00e034068200a8165881c00d1406401e945d001d0b92807111000041c810001d00b0444 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 143109361 1250 143108111 143108129
    0x10902040306140c0405100504120305070212010209031207030309151a010e030d18120309180c0c0236090d020f150c0c1501061e020709051807 63
    0x51401d50800d803040d60304002da00ba443e00c6032142040081034508003034500340c03081103410151016900908071b403a0702582e00b20824881191143c02c082582000c0100811442a202036101c541d0300d4080b07600700e0080409558260b00800311644070200d20800505290f4070a09001507050748540742c40010010a0501d680b401e5a51094452040c12034a4400b00d200c0d000d19142005a5203000031039180c84075444100c05010704e041e40380780104e071011380710005017007800b44800c0c508006060082038100e1178810340c150b450341031701d00b4010302c8418012501c10481903140c007900d0f4a101d600340420085501903c11241e0224036070803030184842078840107403005407000e00d2444e0404516071800e005048908600f554014461800d8002022501eaa000c582c00c041244d21a603c0d190002c01d14885c7d038405120038011960b40c0240f14248038071300c6058400c640c1d6607040c1a64004c1c074030005884612840809680540e504100804040e008554011003000050784485e02c052106864044650441201c3d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 143110611 1250 143109361 143109367
    0x402071e020a0f080304030209130f051f061220030d0512090601061b02010338010f0203041703041a03010305100902210a0209130b06120c0d05010f05010902 69
    0xc1d03141c0b004042c1c0282401d851180001450900c040303641e4410752200034000c0a80500040180c11020b402d0001160068110310120706a40742031034445414081c01c0e011184c0e46c035a000795a510603c151020703142e01e9402002d081c5d00945847c3d9034030032107911030303036a2042410315440b5580381030024540c4031a490b1120b039181d47e9560141044240f00402c641d40c0c9900c150010081e15038403002a070200403800d20050085043d0f4001200074298181e518991300c903141203800d030204648820291009800074010440c19103a2004603480b1000741d6410300103a206110a210500041000034220410042102d240c20741c0d428650450604a050840e05141c011004100f800402d12413444018100303001084041403d038000b07088000c0003521141c8010aa01e00301042071410011080595001080f0034150702c1d1410301001c0007010840226110140360002c038070142403518001c41100898000f030405400150709106940740a000103840c1c940d00c883c0d0051842026214483c0640380030780d00036036 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 143111861 1250 143110611 143110613
    0x10b1908010e060601021c05090a03150f09150b030c030a05060414070609150c0f060203090d08060906040509150108010218031b0f0a03060204120b100806010509060402071e 76
    0x1c00c45a1141d9001142e8100404000890703034003107850522050206101010f400d401481241c0c0c034091054a680c0103040d015010051003c00090000040d0900708103020480440700d51780142c603040c2d0401420400400c564035031a000c50307040a180040c001d4200d5000c03e41c2407002a02d4280d002e0829100390304098188018400a40c0040b0981e04001c002480110310307241c1c000348016814401c1c5101002c1110760714080e54815100800500e4201041e40b10b80001d90400b40300030350066581c03204c1d45c4108100001c14a002e480140e11940004103084010368410b42408084c1c48001c10340f011500401070000d003c110320a0800340648180c100040c0c4441d07070741141c1c1c0140b80c52041e03003d1081e40804410340c950001c0001d0b42c855006c09589036152919000d010400e821002c1e000100014004280403030300a2503031515401c41030003800c92a5881c3c8950400440041e158050b240e20b680240700140018140404031940280300648010301e40b0341c4c00c2c4c948240208185001084540502c13408030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 143113111 1250 143111861 143111863
    0xf06010906020708060103030f11010c020d0e010906050405090705160c030b01050a180b01030608100f1a03060703230403030c09051906180e070810140a050f03010b1908 74
    0x351a41d40010101d50f82003580c411744e0b58005110007010000040b8880a83c070b4420824a812100d00100030300c005006641c02a444440e204660400100c880800a003070390700c02c0c00c90304200c5405132584c62600381060107004549200816600901c8420032041000b86205000031340c5440c09105c0d0110090b04501c0d040000c103506a0205114046e000c10622121044410001c000071800d0400940410110300603000303809150700ca0452030292035031004071400d95820001d8003071f9007a4401c01c0b40100b0721035289070b1501184030041d01603124500144582c3d000c1e51004606d20211046002c0c1002004644500e80804a07401c600080e150034000450942002e007020103014110742000110071081d01050349442648185800c00440d52041501500024001f401a001400c422001da241810b0b024101d440161400300301080c41d140e00285004402c00c4030071850301c0086c40c10208a1a0608100307007a0564071003103905550b40d04c000003c99980030103610b86400e5111585030000d180116007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 143114361 1250 143113111 143113127
    0xc200a05070f1d01050f01111542011b0206040f06030c030504030f0c0212030307170a020a020a170c06090106050f01091409180d050711010e0d061d060f0601 69
    0x103e28520194001440b07146d8450303d07001c8440c1d0f07007841e1441d160207041c44103a282c8600401ea65041c8503602c424880481003103800101c9100c1c801c1c214601d005420f1020150042d000141070585580b48400581c00c0c3d8171500c02244021410507215076203000076000101540e0080e80140c40200381d0340801c00041d601030049400418180c2400c000c140b43c5610050040c00075084103604020f2171402300303c2150784282581c03000540003821642ca03403400442c094240090107007075008644041000500411040c022100700c1c40c6194003030812001d86541c0d4040e00000c4a600307625120050100d0700184408105440c03046a110002040d054580420300154603121321246040110314202400950410542e4150300b906c03d0700c1810f09903442d03500d60309000007048003003846409070000e042e21560b4404040c103c111700410074040f00c2c3c2080c4006480c60311000b03100940110540c540310001c10b0341580b06045812103c0c0f400010b801074100301c0c5003030050840341c1032000c00d1500c00380921035900c800c00d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 143115611 1250 143114361 143114399
    0x60e01060206070c02060307020106120b04110d0c06120f0e0606040f02070209060906030f030408060601020d031e05180106060203070b09160e1306060e040311010c200a05070f 77
    0x141c6068102414004c4c01100d1400000c1d000d039000102140a8902c00d502c4140204100544401550032a2612868044007594140c0d006212041e0081803032803d006400300290340300751150041c600d0040300b540c500d0004180d150101d41d8031800340c03282403400d000d0780f000740304e945001d8840e40c035042e010081142d4803e507804242d5403047c0251401030f00c8006940d900f165080b0365111880d40c03200c00081c0380c80e000100a1140f80004500041d0f40c0d00000703400c1303018002c00d0b02541c10103400394008804441c0760320540414800034a44989500140394441500282c1410714540e5074602c411265081d250141e110034010703800010034106000e51142c0300d0303800c5019074000d0f0102c800703410009801003082d40146042a070800d004503503021a0303803c981d15550f40c008014060941d448105010700d245c00ca5040d8041b40180701031328000c04041c81101c190058503103032200c146058481c007800e1f090b10250750411074031544c0340e0311001c1041000904001c0a0282045200900701510070041c50908a1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 143116861 1250 143115611 143115613
    0x120609070b04050f040f0f0905070f050105070818010915050a1206080601030321110a020c0a0e0c090607060e1e030a0c030302090402120a0c091a07030305071110060e010602 76
    0x40c445595600344c4035403609012240400c11740100c078601002000c15425a124480c034142940f030411001040540880307182c1400701c80f03220b43d2070005451074407034010000d080700000c010500000800030951030308000103140c61135005407901514540c48404000f2a07000c6407003c100401c400d0f9110b49102180a507081042c840b1614108807503076035400600004042c000011810303010520001540110403a000f002801004000c0d05058500c1c0e01c1814002e0042c003c81e1495680d6051080e60001220070f9807085561558800a01d451541c1048541a500c4801006a40049403c501800000e65801006040ea02d10401960800e000048540c0030031078005210302c3c2c0c0020b400000b081c1d40c464040c10090b07680d030008000031b03009114000110845200800500c00092541e502500b000000c680755a95500d4075601a40440c42c8200d92800c64400100051070000b8400d400c0036420001c02d0400c90b045401e41200325046c0500206010030341a5a1001000305051403085c1d01c1c01801140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 143118111 1250 143116861 143116867
    0x30d02070320010212182704080307050f030406051012050c090a0902060c1f0b030a110a03050a050609010510060e15091306080c0102030309190c05120609070b 70
    0x20752031032420540303844042d0040702042d900c5000da034000c0c4089031083d03c505410300c2d80e41d0b01140c80c02420040141010f8002d05264100481c1e40e115079011101600540a10b50302da992141e980045507440204807100300442805040d20309480000134600641c420b131404581843c00401c10101c0d46010b50ac941d403401c10361700f1000042480413655151351041981c001074255142203540014000c040c20003908050006a00820701d0790124503058020104442e45024003584101d442c281c640102c41c0f680d064220110150000e070600c002c101103054040d1031f109800d41c0da074071101e051081000741907940d0f03002030042000141c400c0c802c850303010a12210303c41008d42481c0000b450403240c034000c14012403d03900060f44a00d1510155011060000e05c618102c45141c0400b030050300031881000460b104040c041800d540c001300035a8820112301300101840c245039010044400e00030101911403210030310b000309103a00c52820700c104444081e401040181010703d40d40c0e2071700c0c4a0742d0206480040034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 143119361 1250 143118111 143118113
    0xf08010b041b0c080702100f02010b1f080406060801060e040b07081611010f0501060f030b090402010f12020904060b07020f0a0b190e030d09050306090a0807062f09030d020703 77
    0x800b021860b2206290550705002540703001c41d00780c072a000019600c5800c0b070201d01012a4403640d15960203055500a0090800580c240400c03885c9020b96480490f040b180460941c606c6206100c0c1d005005017404588c0c66642d07901c6500310752450f00250849a030500c108420f01601d1801c45070030403054070740300c3c40c10b20b03250304440300ca611207003544820001c2c0e03814541c820301402d4003c281052190b210400c400d580d01e2601130240e203202c540b40c0700445e0406807407044501d00711030b00314400d0b81c041c2c54915004100d80c50803107044d03201a40c4110a0383d42407048822585603481740300081d0182149540d904c0c1a03070b00400400140c407145492203039907102d00c103010b05400740c3c080c0d07840321540020a0004141124058500001e812001030b058811016524000703940148004102d880603400d55046884081201d82c49103162140070700034403410040754000070165401203507a20206020b1030b210a0b13141c03500d150305410145495034980070101e004025071030f00b8020345405030201d0004080303281c51 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 143120611 1250 143119361 143119391
    0x201509030c040504050a060c0e1002010203090618120d06060e04050601121a18040303050f010807140a0815011401020c03100f0603020d06140a0c170a060f0f08010b04 73
    0x41c0a081d009503180c80224080140070808110825800002481640000c40006125103d03a07640300b4421500300181c82c08160041c0708070307802010b248011b0651342d502c2884040da80805040d001d034191141e4404684190040d40c0030b0a8405040c6001081280c034005001785001d500f481c8161050b0710300b800780440c81c0e800845000c0010361a05c4089071200d010704141050003041072001c1d80190041c6038000a00c46101e051510031403003034030b040101d9101d041034860744603405d01400c140381d400b1072030078806c01460008603021004010031055149403202103250412a56100252a4004180040c41781c2182040c41d03600c0c618080c070062109a00c2c100c002556213460505000703080f80c0e903204c102c103840c44540140d4007854014060440b084140d10701540140404481c0f0200300c0702c00030201c0c1000703003a40181d2441c00c4017541e4001c80044140303a00c6400c0e0b500a85030003203c41d952400014145203c13a1404028924101d40d01000c51402100a09450740c008200d40300d1450f1880d455840c080d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 143121861 1250 143120611 143120623
    0x9080d1d0d06020d0e06010911090d03110a0804230108190207050a05030307051908040206040302040e0c0307090209190509010b03040609020630010b0414060720150903 74
    0x4421560041c015805003405002486030307101e0854111305115940d50901d0001135694100c55080c6010800c203c0303450f07d12440760040e6100154003c010440c0b2801003072007003800c0302c0880ca1200a560904103242d0b58141c1d1075202c0d80c84613102104d0401102c00004010b100034071008020f00780340031603141c0442c5059050801c404d0150059601280c4401030180c00c001480c1241d60010469550b41000a400f0740660450f07003a040c47c052100e5513a520280c0705070707000c0b40260740c090300b40340c280b42c00d55007000054081e403002c403100741c818100c070180c060341e0801c1944020b0030302660050b0785940800900601026001c2400c211020301c00d801c00064954101c7d0a0465503c0002c8940300d803110324000002c0c182402010303501c81c0c40411135214201070360207545e151503404010070145071444903156030b040400f40b0401001400602040044031800b80d01000c011800401061500c003113903032400e9407100744010300c64a0b82001407407911982421a5030014000030710b141c0700d0424242d04000790313542d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 143123111 1250 143121861 143121917
    0x604060605040b1305030303010e040c170a0204090515010b0d0f1802120f06071205091506091e1303020c0910090b0a093b03120603070e0709080d 64
    0x43c001580780a54400240307030901508000381500da407541e40d8411490f02c26821746040c1c800c8048020001030f00440e442c107004901071840302500b40340d0380540800008000030402990345010f0700b000f1040701f40705e09200750702811103030038180e49a42510041c9001c4441c08200303110000e18084040940e6480400e0002c0e030150f0481d41104a9040f80d044542064120301d489a0184105018091140e4111103c210526042101000b00307580d200b03116139aa015200d101e04074211030350085220b030300340300340390b07035809020100c0500225144101e0134240e045d00b08c821610b4032140302c00030030805506020100c0759036000c5480d552141425403220309418090300c00c0c1c90703106a07200302d480d9481d203c041f1800003c020f407800810140c500b8070700028030501241051460100c000c1010500500c1c03200c0c1c80c0c417070340445800542c11304060101070700741c001010b41100d07410700c25160002103450b01003051520a18542e40c0d901d5803103140c104d10910700711401d01040305004440a1740c403201d088211040801c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 143124361 1250 143123111 143123129
    0x10c0b150a0b0d020304030e0f011205100f03080304020405090106150309060b040f0b09062b06060b160308090a020d061806150608010f080705060a02030d0c0314060406060504 77
    0x4400d0380028500140c254488030304440045402c960240740365000d184640c2c004d0b200c219111641d13070700b00807510036510241030100d000010440d0300440d080d440103903c0920503030203058031610741050550041c0c06a104580740440041040700310f0402d80a1070742c00020002c000d01a80f030400050030031003899650301c101055079840741030b0240202c60300301c2d10030181c0281c4104640800501180003414611059138000c0a4110101c2d403281001c1840c0708001d040304140050b88540d203214a2018000d90f0000d9544907100e4901240704403501002304043e68400e061003503e28900c4c60f01a0012400500c40809500f0400300031000d070b05d800d900c89150075440070380081d15642d122001071101c007516038042d08a034a0001400f5034450078120000030794985e501e8420300e40ea600c07080549440d6240c003c02c005a00600306c10092804e04502601d2640500e0040e0303814000d41c8240d00742110314980c04540001d4442c100241402503150310690007203802e643c140304103070400768040c00d07520681c851701c00c80d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 143125611 1250 143124361 143124391
    0x1e05120c070509010e070f020f1b0a0e1806010b04030b0a18140607120e0d030c2a0c090525020a0c03080301050301060807030b060f12030d1a010c0b 65
    0x540c0041c81008040c000040100300b00f961100590303601e4210444803000458091400e01880c5400003803011404042d07440107010000302200d4140180031440c2d0419000704c5020300100708141051410b9110306540e4655840500f02214110300c2c1c00c4040e40500603041c010001800850401c011156001001d8940490064001d04920796038142d00680500a5102c11103003800c0108042046402500590355003a220700d2a034138031204071214200b508074a0f5000d41c8400c92110b0298014038003403021410060a080036441c021840500e1111540b0054244840003030308202c04914000050f0401c084104454600603e00301e969480b0b5000c2400903600b020a9601180d00c20004c40140300d9002082c3c0d141c09903a0b01c8c00c4202901b080c0610341c13183d400c123007003c5409600010650b089135004601d942454070740d281030110881d50b0445454102c90500340c5041c072300e8410002000311102c41d8000080072402c0c40911030030b080c2d51408943c100309081c016400400c02d10009642c2241c03204c210040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 143126861 1250 143125611 143125627
    0x603140a11060f0906090f060711090a0605130905010e030c07030c0605030c030f0c0c19021819020f0d02040b0a0201380609090709030b06030106030b010b0315060f04031e0512 77
    0x500001d200e242d10b03440306000a5450811801d2b080500c0c800c1c00c00d0310800324507107401840000344e4a103800b8840d000341c2c400d0800d80c0320002c1070300324540613409140002640c900191041d070a541c00314240c52015401001c042003007040c8881500003c1c20746281050450616a071400740074400542440081048070010806005014003201e1151903d40308480c191045210002c030781e002000390507441a2813007050078182d1012111068402d03200f1814000700c15440520440094205c0fa20608291b04180101a2001050710050028080742e510050706c901003c0303402402c3d141d804e447c0300d50351162901300d44012403001c25010001054080c1c4082e52404800201d0072501030010055444602e403018803034001d0704605540242ca0003030320000030301d55a0205143c03e035007061200600c210001c00040000c1e241001c051900031895000c0382070041d1300f460010f0b105420032000d81030404030002c0d0801c100000b41700c040400141c2440000581111902e407151151601c0c80c080502020000e2044 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 143128111 1250 143126861 143126869
    0x1050604060e01110607030902120304120206180901170d020c01020c100c0b16080c07051504030e0d080a0909090803010501050a1206062a0b0115030603140a11060f090609 75
    0x4e550f0380206001c5415030f20b00040024050b060120069000d0703213612450b40300e003140200407034040d255602c40f0f03011039100ca5800c1c40300d140d2000521030442095a62010001d03521218094000c24086006110340420303584041e0030403401507480000e56000140e0f01d422a60003140c1034955040c1110b000c00f200003556800e07100e111a05e1402084070b0210410002d072200c0040000c091050079030341e020f46a44d9000709101d07580c81a00405803982e07101c5c45210b840c0040919a89a2080c424500b46241440788004a0102071030b0b030340102da0841d4080382d24170f07a141d4421500030090100c000b06100c004565158004c05100600489042200009890280b0b5000308030f54241c00c5149041080941d80e0380c40028880c0340780440070440d01011071100804902c9074400c40f150242c000d0b9900f8201c0c0d2802f01d0515041ca1140585424180c550800102082d00c95494400c800c0c940e20180c5580e90161411920850007900220b00c220014885a076004580f50151924030354243d80031650b4000080000b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 143129361 1250 143128111 143128127
    0x4020c03040b0705011401050a0b120408120711010b010504060903140a02060a030b0f01030b06030720070e0f0708040b1909060f02210106120504060605030601240801050604060e01 79
    0x12042141e0002e0f03e80100441507101440c4d011348801e8684d4540d0b00e4070108003021820384181c421130002481083c1100b108030b21603603000b504c07655000d07140011400803180100c03421960f42000c034240211201c00000c0038055461002c1007441e080346068102180a401c21182e8040607100c41c01d2005c003504160000c00030051580d800a2000707447d460403440013400f50840c4205207000d075840c000a20038950083c014800f401e1030003403005045584072042243c9ea0054040040c0000c060000b4000c00c41c07500f0700a0388041c0074007405d000164036100c4901c0c1e0344241d003d4080c104000c00301e000c01c0302140d901c05100760040d000510800080301072040f028003901c0c3c4154083c20980c5841e903150714000460f07006164003075a402841c1203440741c409508030600300034404d0300082492580d011013a06001d90100354808d10510000501c95140c00c04286000000d801c00b00c15021091281144403020060600720000e070341c50550360540c10100480c1d42c07030140b4071501d0280070014409c10150380c00b90000d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 143130611 1250 143129361 143129369
    0x20606180912160c0506040f031209030213090302060108030906030f040309181d0c01020c060915040605120a050403020d0c03110d02030310050109030c260307030f080f070e04020c0304 81
    0x80c89032128600201c62841e01d4207443c044a1a41040c070300040e26060160640f011070741100d40130501a881c540320001000c540001550810880d070101200580c0c1d9030ad030700f80c540070110b00300150001d1a4600a0b25022068221341502c5d403051145412959600e01180d5020200d250a050f581d00c881c50700b500c0060060300b0806007280c1c1001003121080550380003a56800c2c031003545a40416014110640764611346030801c0c01600003046502d100d08190008040220000d804250f084c0d440c81c40c2d40c0c0f917036042600084c0c00190002160811024102c00c86070304803107444000c1106091030350300030b507440d1103039010701c400c3c00303001c00b1007c0c141405040b04a0b40314031b500098030640d41d42c4007030007522a8421240c8141c4400c00003804241c0c1d51185120f0800c1d41d80c0300146a04103418401080046c40c5a484406100314241455000519040c40a05029403180e12010003c007118030000e41081c000074803c0b4a8064820108661168030500d1001c0c032030800e540040e5a241c2e400940c82c1944500d402c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 143131861 1250 143130611 143130643
    0x90207020604091103061c02030706081012050309011403090c040c0e12010501050102191509050109021e01080a020306010507020d020303130b19080906041106090405011e05010206061809 82
    0x11070703044c0c40d0852030045109000031113020b01c0c10071000fa2800c201102c1d08001a4146d40300003418492180903050070354204080b020000e031074540c0e9001820307c5600b001001c031500e401c04210002156007006071000c201c07030322810036811844c004240b03654860390b103501c242c0304a8880c815810031900462040c030460b0000f50018511140c01450703240a41028400d50b401841426648403400308003d0719100000c0c0e105456410140785d04c0c5984d809001600c0c002c2d501c5550b501444401651006614400c0900c1c0e101c00c0c110741940d86002601c2c1c0140206440e511a00400400940c0d0780c3c00011100036580c11100c1d0202e40d52580042460f60265580210b0000000070012a48808005c0540032111001c0140c0c0840345101d1003c65030b070300090720320800300d82c0000c2c00319001070342001e040c070304950700070b0035150038140700c100001c0640d64203900650040032030280c40c02c000c001040b480e8024000a000800c075504140021919001c10109003100c4041013101160365a2300522800c1080c902c000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 143133111 1250 143131861 143131871
    0x90109020a020f060c07030e031c08090c04061206151a0d05060301020a0813051f0605040f0603021e0a08060a0e0601060305061305091c030b0a0b03010b030109020702060409 76
    0x4048180207510014000015100760140e5110268000071240d1068030191a0107040200d5581c007505c1d05506059180e81c140100c1e00360101c1c0e440c014000c0003600e0595542c003401420314000d03c40c1001401000b0502490030014213100307040006406405d1a5885140000c40c1240344580d0902203056030090a415140720342103a6662030440080d01c213240d1900c0d42003042d5142c050800d801c1b4883c10001501040220000034103001d400000104041c1c0143d09482c1280114410720381c0311003103d1030481c141503032020306100f141071501c50090b00e1110244200100380c1183c00041240c0c401d84074a02103244039002210441e160144c00b00e00078041401110310a052400200f000b408034902d2031070703e82c460b510002519a10a006480c040d280c090211000801060390000c05064001d050350141c3c0300704003003c1403081848015294485056800003980d030107000400448181070783c090a0788001c18001844440c040034101c904441000c000181d481e0307010720205074640219805403080610300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 143134361 1250 143133111 143133119
    0x1020c0709021e04050f0f01020a060e160626060301060b04141f090303080c070210020708070902181309080a031b030507020c0103091b08010234080307030207020901 73
    0xd402410501120034419071180f80a1141c8480c035004030722034a82d01c4001b032002c14105040100080f0350010061054426144844d190a410b440145032072107220381c00120222603409003007880c14040c2c0b0715450890342c06880c6991409580d1800c48420600f9051400824079540c0d095100c08000c002401015450702c4d03440c10311130f034002c03182c8498130300507651038440003098401a07980c031496001c41e8862000450079902d00322003c41008041e020078600c1084410007607500d00c03004160541c0664000d00415003007001441c207200850340941005801440650324507505480b1155a66030240c0e00d500c1c10b00d01d2441031502170150b81768003401d41c5c8030015031000a26495004182c1c2e8151039107465041d1200d40c0800c40440304120383d99070041c3c106c0c95001c9019071003900f0a03281207005000700102040725000924481d0340d154405c400513036000851484500500f001c0e03039003030903c4022a8801200c000c0610b504020030480043c003207100000040c0d00fa900940c152080d0742d4016050f100e02d5a11 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 143135611 1250 143134361 143134379
    0x10909050a122303010e0705040b03040303050604180501330501050903151603060501050a080a2d0207110301050105030309090a0609051006020105060a03030519110102070c03030908070305030a050c01020c07 91
    0x2080c0100454541c99000003441f150291040758200c4c0c03901c0e81020714503075858030101c00510004e04010f6001c3e403100ca011544060030070041e01124060f03000000c2c802201050300b820031000d100501040c0b00e0b004c50140c07100a900e02c00404640c0d003800c01c0c41d0350747d600340d000078140701906c42118103c00e280010321040c0001c00e81998092903060310100304c0e09844000650301d0380900b0104800080c401e500058100300d82d0f400c01d007004540ca64804020820341d01e502c07603180309540c070701000315940452000103000c800702ea075060340201070b0000c01195040c070300402d4503485040035090050a859001c1118003410f9408035000f0440c1003c10003103410455003c0610070554801d010044d03007898040340140c9080c43d4494100c9038181c84441c84d2140224280c020440c2c2614400244481804502e62451080c001001000c1c8a200c5040300541135282c040c14002c010b0704580d880364420b42c41400040c030008116000c06225007461030300da0b9468043c05001e40709880d0042650300501c5000900c400c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 143136861 1250 143135611 143135617
    0x819200a02060906011220180106020615040204030f0209091e0706141303020132210403020a06022b0f0b0301020a02340305030c06010909050a1223 65
    0x40d0342c01c2514440d9994580d640c00c80c6d511403101810782170354000d0144040000420310f5081e000c02500d001c020580c441603c03400c441c000d03031021016030040c03010400c180c021094079030f00c1c3c1c03041210114241400c6480c0c9042d80070900400a0048401e040800d41d2020304120250344000040b0058451449031400301d0745503503a42c420440801c403068140c410b442000c0c5c050f950181008440f81c0f040503d560011244c44100e840c0300f50020983e0103003484000520013512400c0e003d070050703d99880c03912201244421000701c100e0f59013411450b040c00002a0b010500e4484241c2241c400340c2c89016060a11131887c20b00e981ca406244c4005141c16424401034100c0c2242c04c14000d4100140181c0340141402e0344100e044100068001c0000c25204038441300c4c59150001c02d8006c0e007175030f5861605030002d4038000c0d034005072015400850f04082000c0c0800800707015001100b07091043d25140d5070783d01c1c0c1c1c41140840c0201118152a50400c6091003041031440840001680314032102a00034030076200d80c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 143138111 1250 143136861 143136871
    0x1e08030a020702090a0614190b0a03050114090c031b041502060405010c1805120705040c09080c030c0d06020304020409080a0c2d15020c0102070b15010819200a0206 72
    0x4d0070340340041c02e060940e110744801c4462140001c44514605c1c0c00b00040d0592412200004208082d400f00e1800099805050958400d4500017031030750410689000080c581420031340b081c0b07400020854800c0400e0103403900009100000c4403000f020184402d118040c64004d00c07420a203007100055516400100903015070300481c001c000e070603003d0b00300b00d552030b06074111400460b58684082009041140d41c0c2a000310441c02601d140301e80342c200060986900e1603481000900120051024503000d00c0040050002100140f044a070b80c100826041410003001a098075400300c0001c0564403a0b0b081501d48551004245031344c0c1071900e0340940740c4070f0750000689015060f5105050005840040c9400c0c40c1021405400800d0b005c0c1c0d280740712100d04028114a0940a10448c1c2c14080240090480540b162180d91550b14248807400c01600e180e0045904103c0714106000d015101c1c43c0094181208409000c0b0b5410140c04001c2e0f075111030204c0c2028080c400058942c401030340490414062 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 143139361 1250 143138111 143138119
    0x3021c021209010606020c0607020f0909030304020901060e0a03022206030308090d030e06060613080d051e13090f020f0304060614010c0317130b04051b0d0506041e08030a020702 78
    0x42d854108505088074114040c00700942c0c00910203070050b1504102a0689a100410341d514640d511070100704071075004d607442c507502d070300100030b0100b1440c1500381d0074050060791030046288108480000c1c1840d07410b10029000c1c0742081a090384010160459842c45000a542801a15960318008240d50b030100c80ca100c05009103860b0180c401c2c800d02500000704081070080090713031903103003c00200e5886039a003416011541e280c00520010b00340f084805c501d60644270540c4640290715110000009030440481c407400810080084049100800e01982d070361b18000030341d07a00c8a0f51700d9130091146084c0043c0130070000c001c210400c00d20342c0026007580c054801c0c01c0c1c80040c5080041d01c4016450b500200400c031141e42c002c034580d0440640075404400105070780b1615009403140980114103540c255420303007141120030081104d181008801d01020f4403c448014510348900b40c031070032f014000809030507920041c482c00d803504205101d5002d8104075035076035030f00341284403a0095000010403406 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 143140611 1250 143139361 143139397
    0x10050301110405061b070f030602130e0106080f0a020c010f0617030f040312020c12010b12030a23211e040b0703090f081306120603080a0f03021c02 65
    0x1d20640760541d0b08a0700c02501d0310742400b90703c000d503440501078401d4100c014801c80f40c000410508090711030000b14000c50006964034140800351080394141e4100341c600d241c042c2d00421159500801e110307840b00d1101100e03240d50320348180d00c03c003a00c28644138441941c2410841c030038250f259072100c4201c41c0700044500d0b175a200c0203201506e901881d8000d5420355414402000411500c000782407140000b44182c584040000001440010340000f1303403d080e1f95900b540e03002c0c03400c064801e061461002402141440c8091000601e0418030300241c642c0480700e904046000003076601603410710140755028000c40407260f552000d40900443e15034000a1111210785030880030b541c2c81d54000da410001c40e0b2030b07580d61b000b410f40c041c01e140d401c1144d50100440701100803071803c2c40588000300384001c1d500012841c0510040c048604c0021403d400d034904401000001d000c2c8045aaa80c5d519080c01c506510345580160020b001d070420907803200840003006a950040caa0051114152850003a85 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 143141861 1250 143140611 143140631
    0xe060d0906060f0518270a0204020708041403120901050919081c080403050d050402010e09090d0f17070c140109060b040c0e010f050d090f0c03050c01050a020a0b0711010510050301 79
    0x310300381c15100d14583c054580004080e043c03200440604a2402c42c044034901d00023580820101d0b48011000e4490080114040c03007110f011112440c50048210000c1980c540d140441710f0b00c91180609190512400203200d00d03154456541c2c4010750303000c0e0040f4040551355805045c3c0c0b0fa210f00e8014035203401404030319a6070207008a20160041d034150f0340705c0e4102403806107030800400000e0300907070621108240f8034015940e07400083d03104403400f00145c070b605480781e400a88903160400d0030f24180030304d500040d04042080003480e680600280b400e0000341191342460101d415050750804059420000301c1001c1c046c250f0064050b545007034508010040700c1c4542103440501d1b50300e1003400103003490392400b42c4512490103048801041070300051102c01607a140e03c189003c10504640018141c0b90800a2060038820008c101c1001c1c20018039103400417200075200d14a4403c0101001914030110700158841c0d10b242c000b41c08280002c005609000d880f10745039800b5403003403600c01d6003040380100b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 143143111 1250 143141861 143141899
    0x905011803020105130810090c06020a170f040503030f090306010e010b070b09030d0603031701061b0b090a0b010e1006111504110603130c05040603030e060d0906060f05 74
    0x48040904546405555045a00444640d031100f41184d0800318805e10100f4031200c141302c0350342599805c220008910200380784c11381c10070310b80360f009500f9504001c2005020440284038110b04651a0100540d0b840412400200c42c8c0255001a5003510000c0b070301c1d41c5007100907001003941800032000c8a20580c6d0300e1590a83d111070074011110200020b02803c00084d0b4181d22082d080300d0803905490030041442c0341c0c0002c8811552050340080d5500140c1184458540100360242000c0d140401914025456886c03002001e040000c0505248a0001380102020300c400012607038020403060340c2d56511540140c080c14161500804500310000001c0e4070360060b584901c1d0900b10401501392080188845850702c840100180c452200414504e074032507aa20f80114801d5000c00403101e004252030900d0703c0e41042d40c1c1c0100c0e003d86e1800005101103230708008406842c401c12514607981704a012042c0001e402645401403001d4100640402c50020000520040d140180c3c1ca1510b0101803c0d248 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 143144361 1250 143143111 143143127
    0xa0b0409030c0308090a020913060608070308070b2d0f09160512030d020a051b0307110d0807060c030e0d17040b04031710051509180a0603020a0312090501 68
    0x50201e00b81401c544002401503c1d0a0350040d03041042d00d0401e0050f401042821b80101d4520380038082e140d116004220f40c0c1e01c500f00140082c0b000030a100c0e030a5039100b14031342c440d5050140002c0040c2001440184440300c0c80e0711400110121440446100300e8072204c802002da6003800c0c605001350004d00d40304000110682d0002b80403d9100c0c400e80780006010040310402189041400100a88400c08006000604206241c5c0e84d42c1607440040000d4089034143c040704c3e01c04107800400110000c10304a404566014104603204c501d035180d545000034451003007680091005080051400c2016050b622034440d80810400351100c206403040c00722003280786070088008a403040c20104003c5540c058000343c0c054800d0914007100c04c2c0c01381d00e07400009000c840c1c2c0a05402d02e804244121305180030405001d446130310600c0d040020a400081d1144a030300c40440d250503001d000955160400d400500003140c010f8000d0260350340b41e09000804904820022010036903102e800102035201e5445 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 143145611 1250 143144361 143144363
    0x705060f0c16170c0a0b1303080318060601050406140a0905030109050a0606140d060b010c0206040e010f0b0301080c040504020109121505060f03030708090d210215010b0d11210a0b0409 81
    0x64005481d042c904400e0b00ca0b00a121f29142540c2c0b08140400080c0b0010011130040ca1101c04000929032001c644600d0300000504d031038100f040034001000016007000c801048003602c00d92858859001050032186405180c0c03215626600300340c14201800004280102401e000350424061103480f0080960031100c0042c4040e001921058480d010560a6000f030884500c145401c0402c83c0f140e40003d4095049a0441c043c1c650030040100329581405d40124010944e22900c1400d642c0f4100d000354032000507152050103251610001400c41e8403d0188401500c03039074000090400603418042c252104044c9070058042c6440c01141e0703140b0f0013100e90001c0103001002145011001d41d1159802d80201da0096001681d010300759001801020b48070f6804440b86030034900075034190b20000d00d845018041844007000b00d000610141c8540001c548025102100104002c0e00181c5072380018411440380082010076424425a040800b01c07641c2e003d0a050101072006e00d100e0000c01c4122121a14 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 143146861 1250 143145611 143145619
    0x81b03060d060f090b16020601151e021608010b0909070305030412080405090408091305060f010c03090905100807090b0d021e0d060b120f0705060f0c16170c 69
    0xc9400c00510250840f60b5080c0140402040101e1281d442011520042e903c51044005440c5031100c51503042041e14014130720030b001c0f45011100d8002c0074004101c2545140ba03055146a1590f1071350303000704404004810300180c0109800e27902c640180c001d1642e444428810b1a45102140c07984d800042d010040e070b03402501461a1914011150b80b220b0480c600807100003106000c0050345940b508c1820344500c0c0544407055a07068071104004449407264030b0b41056034600703000d000740c988800010b413602020a0802180303c81482c2800c1d11400039590081e10094200700c10025050740c061084401c0311000001c80e51000d464079440b105544075807600d1342d00b01c880703010f1810161070120a80780e00c044c50604005000c02c01407010419440c4068010b480c2e994a440d00e0924034104072503110801050b02d03029180c04a003850303207943c0b42d81701403044600c502e001082d5141d007e0317103240464107080e0203101140c1e0740010304410348551203418400c03d180e140301d1f4a8907500e088008501d1210340c03030f4018 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 143148111 1250 143146861 143146879
    0x50c031207140a030f0605040516050d0e010504112418120f010b0910080a08070825030815061c02090a0b0903010f1107080c0c0a06081b0306 62
    0x400c50040d5540080030310040020b180060202c5802e42402410000f07840c2d90042400d03200340740c0010a480b1294000c5001e14074140810001008d980030307001074001c03079140903039580ca90489802d000e003001107141d01d201d51030300741031104100c020081202129010745241d030309500b07170182401d4407105100000c1c2d48cc48080015041c04414408103103420a4014000d407102c402503001245000e048500710815a0341d00d8002e13101500d0802421a4044002104850740c2ca090145950300c40301281d80003014201c01059000030083c0c95801d4038070303010040049641442d14a40300e04c00e8504005004e40106a0314004255242d403400da040002d0ba0740030300b405203000500142041111a105040c100d025404c0c0241e001c6544c0d100503e90080800c3e221668880740040200760844443c8260741030110b261045000300d40146c82c040e104401d400c24186510f43c0554064107040030309051180340d2043d907240700441c109801514260082c034140054150360b02310703144410040c2c40240d07440b40e4001814 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 143149361 1250 143148111 143148127
    0x6080a110d05030d0b1309060c020106080304081f06150906030b0102010203070c02010c0c0e09031c020301050a2603040b0307110706080109090302030405031e0d0302090a14120604060b030c01050c03 87
    0x54203e00701926001e800c150384d1b080055030b081c00b11030760000225101500c42140345034981c1c0c2402414007900a20024500d010300d01054607a803200300d00700c00682c10380140b0040b080521b0951109000b000c1524443c803032404005001071543c000d5005540100b0b02c0d1441000707131544144281c03031048095440300d44200072950019a041e80031000101c48103000d8420201d008120220700700c0c090780540000396158406001e010301e1207103101e4500800d00e441400100f00720341c0d824901d541164901440308807506001110080760898061010b0861b100020b00007843e079031000003c0d44108803e40d22100d0f203001c418913180e101c2401d07214000018503035070014041540140e01200c0d045200f401140e20707242d0790700003003824455980f080c1e00d00c00c070b4001c081200381141406a14259199854214a488210070024065410900508904041104124246841e654020101d00d15400c045039000d19140c60803a0140c803c030a00039000b4000c0040a054550203134081d00e254000b81c0c0055400d000c02c1d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 143150611 1250 143149361 143149387
    0xe100c080a0806030a1506210507090e3d0b090c09040e150105010224070c020f06070b0103290c07020a050603090609060106080402030a021002070906080a110d0503 72
    0x8003422481d45409030317212200c0010005014034622800003d40400d0491601019460380c13601d120306006403030141d041d54070024001013101300c01d03130b40c005400140328014803060502c0c02c1101a44880c0c0d10346e10b06005601041c2c1d2a443c242d50042c61008041d420040610341d9080d24103000800750400480804121072036050000341c04198000341000800c0c2680020b10f07442c00403010144401500000b00501043d681440790907280204000741c000001c0c6050780090440b00010301c4541040050700c010b008540d0390480c41c0c1c0b41c5030002002281c0703030342042c00d01c21041c95007840115424a05030709000c41e04406814400700c0c02e96006040540c40d640e004035a00e0702d03408441d081742d00811103030001c01c031681c0300f0010710300850700c00f80282403e01d0154002441c242c41a00410203001070b0404010043c0d80018000c01c5460303041d00c400501001501c0140c0c601a82904006039080c209003000c642c541000800c22101070003024410f0700d2200940a00c003c4002c0c009000c0e049810802400e42c003664 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 143151861 1250 143150611 143150627
    0x40803030a09030e040603150b0f0d12140a08101401020309040207050f0105040f1101030603110d050c1315050a120f0f080f04051915030b04090c060e100c080a 70
    0x1001c4d0501c0e2400304050710002e02214210b4004403084c0601444c5041c0d0304540c0c0c4164450b40750141c0b04d00410032054000208030b41c03600900109510403030700803078603850301c500714203208070b04000c002c1c82d10340324520400b504004040361b0454004104d070707800142d0196502410701034004103801840c5072056510520000c1d6111100a41e100d01c580400c000490f1400d10800380300318090341442184090500e0080c2002208403078150400d818980c0520202c5e5803103d0b4074000000460b00c152841c920b900d001c5051441a00321a6407010051440300300d085016085003207039161000600c1d0415031598204007094480c1d0003075802c3c600101407440e000440303441c0d00411290140c3c5501103041083d0f5101030302ca6003c0c04443c1031180c0041800c000750700340403203000c4004000c200d0a030555420b020607912080c255400d40d00070036468a2011500e61266803000240e83e806c8030f0801450341e2120f0703010703058204c100e0019010b49801080031000c070744110303a080d0500d980401450301c1c0149146080b00c850b5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 143153111 1250 143151861 143151863
    0x714150103031d0f03070e0711060106090909030c02040c050c01110f0a110f0303011d07020105190c0c0503070c140306102912010f05040c02060420060f0310050402040803030a09 78
    0x70705504c2c41524a0340c3d041054400500c0244800f184502c1c005400801c2440190382401f140d41c0040010320581360048903100960f01c01c5070b000200e03440141000c03070301c034940d011000c0e41080c41d2000b00706c8001e61080c02030081400080017801800c0c044030f6261140c2c4146051000648018890070301c01901c0b03001002c0d5808030803012241e08072070003600e50341940d100780c1c400380448070503070381261a00c1c1c00c01c60aa07901c10b099000030012846c1199115100c540c04e009640d102a643d10640755885009038840072800b40c0020850781c4402481c0340642e0f0b42081b03801035000401d1085208801490006401489003598420000c650341c58420320132544135400c01c0003131020b2007022605031000c0181000d0582e030421300c2c0c0c401e000ca52410031481c142488a400141c01070b81447c080c0e4880b60b400064040d0450b6000403071140107170f10b25560620044011403200d601480020b91200c91400ca1030185000711030000580d034400c0c0e5a003040100f01d1280e0310424600790014000150000c1040e40110502 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 143154361 1250 143153111 143153119
    0xb04290117030a0c021005041a0306010e01091202150408010e01050f0a0603031202031504020a03021305100504030b0615030c03250c1103010906020d0f0b091b030c09060714150103031d 81
    0x410b4403070401e007408141584d03c1c4d440f27090020080120a69112000f258003007400e0038014102420120f040c54086800346019000b4030070446030005c1c09403000120b0300208040c074000c0100c84851035240340070382001e490511502d540c8401081000c0300c14442c640440341d05480e240d5030300c0d0160030b07030300c0180d0401412148480c034a852049901d4640740000c28911409a41c010381d10828000280e41d50003081d00000e000d0403101d00c0c040c8802e60007400b1a070540741c0110b11034150340e45420010b821074505400f410b09824010050083e41c5d400303600614018001040c1500b100700910700451484802e130301d244030004101c5280d00d000b086085041e491036039405400411104010744940c01a688280301c4000d83d1070b680c128001c49101c09110394040701100b241c03211403905029241c18a00040f0108068101c1000804070702c0701941141282c601c0c05007d0701c403075200c1c040c504003188200341201440055000340c00302444410740320318000b0b060740d501d506c9003800814809141a00381103002d9286e030b04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 143155611 1250 143154361 143154367
    0x103021003061a09041514120a05010617060109020a080c0a033e16020f0316030c06120203040302150c040504020d0204080d05040f030b04290117030a0c021005 70
    0x3c5088030150344041e0b900300003210f80c0e1005100d0074001203404150498468a0700d03480d01303100b000305917011032210f080111b4000c85501382c0c03809954103150031150300401c07940c40c00100280b001c50303038500d0201200b0007000b40e41d000c1ea681c001907000d0f88140140c1c280082d0504000801c2840300f074014014151680c174002500500d14070003030880100c4000d006d043c03411f8407a0324546800684030742008544030800c12505004845d840c022400120030002486245056121002d5031020003030480d4200320343d5a10b60a1035071380e0a00c1000d58409009030000035002070000e0501c02418021031380034540c0355000304a440c5220910084001014268000500d02008001060381d00c50001c3c2c0b00100146000680d0b407440d0a40b203614010040003072006005042c0000c009280e560040308003202d800050741007d99940c5d2034a00354a211031400080340d2140b284029420006065681d03068540960311000c0c4140c10010f05070307581c0a40c21308140045d02c1c0106140050400f040c100c15a143d43e4100981 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 143156861 1250 143155611 143155619
    0xe070f0b030a05040614040b061c03020c10030e07120507090605060304020d060209032d0f06190f020703080403020c04060515091816090b3109020c01020406090902030708010302100306 81
    0x2006505503025613a4002400600c152840c004442a80300921400c64190014130b46cbd5010b9107503500200400d10408000d124441c801c0e01a8121030049001c2c2c200381d41070943c4650b2012410000c0302d109681034070402d400130601c090140300301d50964a00510150a50f40c0c1c0307908224200803540c01c1210755940a0060300010b031420015120241154071104100c94910808022050340140b0942c0d0740e0740c0107101c10b803820300e00071071789a8000c0000c000080ca41d0700c807200c51a02808003030310995a12440081c00e1010b0640c0045100d000314801d03400d4603c0c800c0e0510410042d2005401590360001c00740c07908410301c0001c80e0003820700303c8000d0060070140705101c02c0000d146100316070f212019941c43e103140d038a0700c1d48100c08401804106030080e0900d0141860941501c848100c200c040e001c81c00c030009014680380e01c450004086c1c14105543d50100f01c00002e0207074000344280320204441e4680460030103064006d90703101c1c2c111603440d1307000741c0e00e10f800b00581010a44282c0c4181955070344041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 143158111 1250 143156861 143156891
    0x6090312010b0c15190b090609040305070609021003020301090f1a100903020a140907020a051b0d02041b0e010c02060f090111060106030207120c030c02090907180e070f0b030a050406 80
    0x5e1140700d00c1c002100140d10840e0307036441a510ba180006100e4103140080082039610210459005030305450f00c16220039540c070304100145030480c1c019512940c404480e4030500c0d4590015810b0b209002c005004500030070f0082c1042d181c04218600d21011252107030384050a107250010544000b030b180c00c0050715036a801040c01d41d4503d0300050300242045500a4080c1071503515103030419924801030900001ca0f80301e0688442c180c440e07510060b20007400d000ca140d541c0c0d80080c0310030382c1c009004010104004408185034517a40350f0f5900417480d1805030220960040d040001407a40140c2071a14000918a800304180d2025001030705000000d16121500302c0d04014807800307050359840c01652494181881803241c2e03286c101e8881000304039203614000952105256071141d038182d40035038158465111490416040750054410580c0d010500707810450a40c100045210104040c7c030502074458000d00c0510446008501504004202007401440e0b2907000c140c0c094020782c00003460310a4a0100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 143159361 1250 143158111 143158153
    0x303031a210c060a08060409080417010b240304060b04090507030c0e0a02032206240e011502071203020109020618120105160309140a030c0506090312010b0c 69
    0x1140d03114001020080e6005800c000420181c0403c640c101d0070030f1a0610b00401c10000284100c0c0215107805005040180300030070b42c0c001d005820780114007000a0308c0080c1c003d0040d030006511402085a401c082d0550909030b45c0b80d10f1910010491071541d458075500060020861216003182c1d8510621010800a2111001440c814901103503100d2178100e060078210b00c060320151a56104006101101c41c080e0040030b01100c0008a0314182c0349581810001008171880385c1e40d80700824221102669544aa00304c161107201003502e40030f0741c803055201c5a850840d1401405a40650f43c00d0207076481d1076542c071807001c3c4617100101d65500d03660f0109515400840c01007507a1102c2000e00c2800b4030b00001034618400f042002000b880c50100b040b008886080d0500005040d6500342400c00e100b80d0100c01da0030070b0307002822202040c0c541d103402403980d500c46a0580c0c1602034507002c02d80c49030004c8226500785d4032650032042d050f424409401050b40c00482000901d214080700c5010b003500c00884 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 143160611 1250 143159361 143159389
    0x305131a0a0606030612020f0f04021306170603060f18010c03020309011d0709180803010f030311060402030c0111030d140907050301020c03120402130e0102250c0303031a 75
    0x580518108144680141e0b28103400102c189410030b0b50610142d00400f4041c0ba1064049603544c44035203000300031135080081c1c400c0d0b40380c220340002681c2d00f0301e581e2403902d242201e142c1c0d650140600c041c240c040c400c4410686405900d0381107140462104100c034034030709401001428242d004003040e551545d00311602c2c11503c03004250080104400d9032001c0c400d000f12071209400300d0300410740151010762603841c07070b0041400880d502c6000300d2003024134440681c0d5959108280d00d641f561521402c100340111403004a00064400b00b12060006001c1402c0f40160f6016000302000052035006541c4140b009194888a2200740803440d0219031900900c00c1d1030100305003501c1c0505010b001036090030010340001e802a0300410039905403000020450f41003502d4642540b5858595100080e082609684000c01e52824850200a214010342c001c00140c1c07451540948a10003051800300310341031004002c1c0c0001c0780014104046802904040620044d40301c1a56031901c00b000084c001c0f410713500b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 143161861 1250 143160611 143160653
    0x60e030d0203130b010e160f0c350403170901030f021b0f0a150e0a050604030306091a0f01030b041b0e04110405060304060c09030b07050c0c09070c03030513 69
    0x10f40280940540e045003d0890a9011040c0c0d280c00315003924003e0403071014408101c4131445420189104104c003109640c2e2018141c2c0c5082c01400c021003600f01210801110841081840a100011314085804995010528120070700082440716400d400601005044c1600c802000080b1592480100404441001d05941000d01030008914004c401103105101e0b80c482203519000c03448d03443c080800160b003207002082c984070901200c1e04140c2e44003c010410710816041c881015015003250707007954614441080b64492403c48103180d030385d4402c8015000454480c91101c030b0352003604142040b0502420101c0c21440c910800f184040010b06d040c4000799803980d1144c3c4500d454080e414410381e1001c821030400f82080005003c9100103000104400e6950400784900c074044d468060066400c0202c0301254640b104004d40f80f90700014540d0780902803864039052614103144020301800007680c2c0c0240c404207592b4250700812010b40f1214212820f01c8400d030010f83c10980d2000d03517454a80c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 143163111 1250 143161861 143161891
    0x109090e0a0b0601030c1b02030c040c21060b0d09020a051e0f1e01080a0905030d06090b03010e07120507030b0901090201020d171314060106030e0c0108040807060e030d0203 76
    0xb00301444484409080301d4101400c080c510140551310014040803110f03440f01c001e880650601c0024500340781000a41c0e04139041c1240d00426603001305843c0c2c80f035654007016020786106441e1410071129a8005e001240d481440710754901c43c866403200d00d555101034031808800c2c2e2144001000b155001e165181e0000005d5800c8100d4200744488030f28030b50041d20240b0300c914144440c62940448601064100118900054541000c5400900390160032a088d83e582e401d0403040d080c080c01890284a03822800c05035129182d04052054403070440c00400900030490906410143e00b0f01040015501d0f0f1113990404808601501c41260080b4100400040c2c082114400681400040d6543e03805100002c00c55200180300c0f4844d40c0e41c8208224100c44148a4901d00f840080c0f0541120100900c101720001c942c1640650042070980c00003821100c404510074011651441c04540040010506000d03440005c0c4540d04031130140b011145c262820000d00028060032a041210460402d40c012 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 143164361 1250 143163111 143163113
    0x507150e030c0709150905010e06010806060708041d130506010b031003060e070608010b070f08090a08060f07090812250506070c0219030b0f04050c180a060605090102100b0109090e0a 80
    0x15600d0b05d0002e081141c0c0500596140038003203040301c1001850329060100380800901036540f10812545803030b50002c2001e441c1c0b40c4805828142030410700610070203040040100b6803d81c107107500c4886080c3d201740180400d038240b01c5204c2081c1c0000d055080c00c8044c0080c0800040d86500501c1104031b0300310300409500b0324203c0020440d440c181c0c84194818800c2280030041a0502a00c1800f40c1d00820030782c0c0d9544800d400f242008180350300c481100d00030001880301501c0d602c100c60717014800541d1588855510350344241e0320381d501c10384000b000500801502d51854100d281c0c0481c030002c0b03041c0b0700440d510b140d05c0351401c0c8081102c440d40064001500c00d01140f030160001500710780c01800a0102c1400c1d6a10b000c520301380649801c411031400000034080200410840c0c416007806042001c1d24690350319190350f002e6041e075400c07600c41d00340000421042e2142c01500c1c10020f0590041c0800e11440c002c20b001001c400400d64108803480030045914140340c00f80009200c80240208102120303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 143165467 1106 143164361 143164391
    0x5040b0a14030901090201080c0a0c0f020301090c0b030403031b1409040b060c0c0a05033c011b080714030105041104092a0507150e030c0709 62
    0x7000041018191040d00685000c0f4400e132200c80302c03a2182101001c96015907403a150000391201c0380680812550602c1c140d1080c00a40001511a89511418003016050304034441c0417200105220030168540300d43d01c415080e21054060b0348a84003030007405071000d0400c4540b03071000800d00742a0359603150b0250401c0d0600619155a900301d0b4a0026110400304580350b1140c100504006a542804245e10308804454505418915084655103011a51008410b0102c0003180c8202e03c8000013446910704800380d018032a0b0200034214802041d1006c0101120b0401c408007240700000182ea0065a040d90320845021490700d045040220883c0116840f009880d8200b0310400e00004007024100000e020019040d00c0d202240d1034252283e11803440003c00e400300c0c00c107080860027039680c041c000070a05002600d107042c400c00f891528020140e04400f2015541c1c84a440d06008 = true := by decide +kernel

theorem cover : BRFrame.Cov 142985611 143165467 := by
  have h0 := BRFrame.cov_init 142985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 142985611 ≤ n) (h2 : n < 143165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
