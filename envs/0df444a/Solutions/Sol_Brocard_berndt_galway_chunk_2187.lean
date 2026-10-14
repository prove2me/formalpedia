-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2187
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:55:19.986926+00:00
-- url     : https://prove2.me/submissions/16a45885-f7bc-4575-82b4-fc8ec11ead48

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 393165467 ≤ n < 393345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 393166717 1250 393165467 393165497
    0x90a0e0f030301091409160b1c0606020115050405090c012111070c170c01110f0102040b04050405010806071b0c180f1a030c04020f0f071202060105040219 68
    0x1852184818580072030ba80c0703681d62401d943c010111001c11482002500c0c02091103100005992003210000801c0e001e01e203450003060304081d83c008400f0440c10032005e01420840e006a215404c0140441e40001c551404a1905451102e005411080c4118a0f2009008188030002a03a042c0c4140038200428034800c1d050604a400c0f0180400100030390600c0228841102c40c00c0217009002d2150f000c400c003403503d0b0000015200540c9142002903401018498070540c07150014a0790f29034a5015605d03203c030460440c0342a0303801904020315403040080d08110604052040074014900000a000076080c03119000340000700808552001c004542e18010034001d0700502030004021803100740da851400d0455400280c1900c0101940a41c60022201d00280b1041c40b40440f070b84008000e4410070b040c140400000b50400120380c40140b07001d000c01c07101a0030a0005107c024046d900c03100d80a041940000d143c101c05800440c01580140f01d42245a40181106c0000c1011805d104c4001c8441074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 393167967 1250 393166717 393166723
    0x2130c0201150803040e0a1e14070f0c121808010902130207050a111306080c031b1809010b0405091c02010204030f02060a17071107050d08041a0f070b011d010302090a0e 74
    0xa030380c4c031500c034468481d107023802d6100d0f480604011000302020f0400d603103030b200a8030341a915003000c0300811701429203500090144281000300500c24241840001490114414802480c0c2c200149583d9500e20203c1545407108055400d80000d00d402c0d8a4044299643d80c0c40d01d260050060140700110504c40480d0303100798444000e04101c0c90108030040c2d6450401c1d9441100f054214042e0003840d01c40558002d5403085200c032904060003145501c0003814043c06c3d086801000801d05540c2d5072100c0c0341d41e03138640c0100c1c0d0103002d071030b0010440364812a4244a0854146098905582c4108000c200140c5416414003440d034044908079100c410804068840103001c0c1580e40c0c11762030b014100030483d9041203130050300d01c0c2c5090440d41c070a40c0320b00078031400308503070f10b00a40034500c103100030403049407180703800e014a88907991201d041403814000040190062402151500700910042c005404080620900756007010382d404a90351441c1c001c0f6a030488050881e2490a8460071491034401c010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 393169217 1250 393167967 393167981
    0xc010f05090603040609060b09060a0b0d0209090411030d050301050307140111060103060f0b180c22030b04030e0303031005120a0219060f0c0c0e060d02130c0201150803040e0a 77
    0x5031000380d4134039007850108000c048000c01104d90750310380f004da02d289080003034180f4820301e00600119041e50900241800e5034000340f21014156808000486054464031513482c021445182025040c64081d02003604002140b600c400411400f0b00c0108955a00050b684c4c1c02c0307580446c411680d494081004940b600c82c060b9551501d40308220000080288952005d03040b116403500400051040c042041a083c20654840030750031a80030102c5c1082c60207400030104c5000840800d03048910110341c0c503001302c40381d51080e20300f2440e0100b000280368120154001d290350032005580b4502c0d02980e8030105881c28051030b8040c070a10080710b10180030400000c152650001c0c00c80103c2d4507203609401450620f80aa040054034510200c6031090048036121075140d03000303100005041c2850486a50280d00824050b030107040f080200303000d6120a4401500002515804079000e02c102c2006402c1d106c0301c03680c071441405102e01c10816a08044180d0f002e0761200185180161034000d5003074003134045 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 393170467 1250 393169217 393169219
    0xf0303040302071a0d1b030e0c01050f03060f031f1823032b0b030a08070b060d060c0305090f0c0a03200406180b01140403080304050a08030106020c010801090e0c010f0509 75
    0x40c1211035070f01b446007031482c02d00481882d5014002420100c00703007501c4d0602078540d240840e000b0f100020b04c200946000d540d000c50003030a030120784c40e40c1000080c038224002c5c0c0710410140e0303550390f851442c2146024041001c144407600e0040e2070070990703411600818007030141d40079a01c0718580c4210034600b4411200030305841405c20060012900c0c401e00d2001c038291180d5841460311055038000d05002c41c0c2a80c1c5580c000e281103080012940325022443c40040c0301c1c030303800b94100070300e000025503600c21aa402d502c4c03a5400901031400100491908084500741402a403009103449540da030b51115400541c6c0e801019540c81c1c94001700290011800b4544482d80326007070400103c0c803030075000d02c07400c1d090200c10750034490882a140191200f105188100c8003c410030402030000c915194000c541240c42141202e0f80c000700c6447d1000705410a0300200016004001c00700815a84200c055001d06441d4a0401c2000040d00039541d4071081a101a41401030800c00090814094000d440007454 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 393171717 1250 393170467 393170471
    0xb09100612141611011404080a03060e15030c03060c090d03091d090706140f03040813080c030106090e030403021026071407260f070b090f0303040302071a0d 69
    0x9180300340f02041d05946400c0000944444e0000903074220500613030035400300380d0100c02aa51501e40b10700000c1d03885090b406081c90f88404000410902500c02e1030b11425490080d581e0a01030360301011304007074640c09414465403201061240103a80f0b602110b14010b01110103950584d13503403070181d401c1c411503030081e0780180520401003d110f10038652540b0504102007079a44007600d448040c0d4071500f080b0044000c49906000e0990600608001550854064031fa501c1c01c02021301842040384203160090b80c0984c100060f09240340c142402a0f402502c1102818011101200c056954a0241e4400644109d052042010490380203081200070748121340e0549159044403900480d01d07041c262410400a4940703000750314940550b8084e180925482503d4040c804da07554030b07000c460703101c43d4003034801100100076810544100b2001407448600c00c4200d442d10385490780c0e410b82005260501c81e10380d90402c008001c0001d50115101c015505400b109a040383c00007600c003000360180300386070400340b8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 393172967 1250 393171717 393171721
    0x40603080409330b030a060e0421090303120213080a1a071e1110020a0207140405010b0406031a040c02010902100f02191a040f03030b0910061214 64
    0x1400640110300f44200e4440020321400e016125074811914010202030240040700050043d038181c4001950454001d80c00492005d49030560041500d10a64049131410f403100c0c0c65801040f8003200200aa0b6881c1c20010007070b42c50350303c004d0030515903d0510290f660340010505c925500c401c417084060500d000841c2c89075090f81ca801d001c9541c0c0d8007509030818910400240c1780ba0300c940c0701e80343c8800046e206858204000c010682b42c105c1c0116155006d03000745160030352003410b2403001e00a0000c503640104034143c03402c030701c8149011000c0c891501440c1000d00500c01803148400f1282250214a0002001c8940001d040301c404004d02d4090b03445402c281f40c100c01c441d81500810311050088400d0240f85284840070758105041d80c0c0d400f0056046080982418a0440200c030102402400002c01041f005284a020004225003c03610300c0c10341803010042c50703414403580380054015103108030681000c022072000300310180310701310401c0502c810028103402140c01400c1540c01416110240d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 393174217 1250 393172967 393172979
    0x302061606090f1104051e1008060907061b030c0f05010204180209040f1e0c110d050a0f0c020d0f0809030109050d110c0d02060a11030c07030c0e0609010e060406030804 74
    0xb1502c00e40f000c3d00c006102507030051140c0303042e120b0180a110645e4045c164000c040b0f07201400100c2c01446520001082079000074000e0301403000e54845e00011010300000b074103009024200e0031500da03a00000f8410a204240040d410805c0c46a416800c001d400c6030400c09445c00a029205a401c00c0c00418003c0901080086e2150040c00005100f25000e0000320302a00143c821200d40e1600360340200c0d0714090340401d030306c22903200c19070054103481d00d8071032102100b13031441c40c1c181d003a0703500300c005070000410020082e4408070940c1895854605603603c0ca4031500002e0014005180c040c200356241560001005044011940c16100c050300034001400c81c0c2c01e0080d01c901140801e0804a00305841040c5810000f0420a030702860041128004054503024061250442c520b00014080010404000000200084c000105420006244590443c85c0584114540b98001c0d00c510400c0001c1c070620395912008a41520548125015036946820005000d01aa5800078150b036074006004114 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 393175467 1250 393174217 393174233
    0x1b080d120506030109110f03070b030c09010809120a080a09050f06010513060f0b030a0905031b1e0d030905124003030c0501060320130209030304030206160609 70
    0x618502a4420001c0d5500c48040c142038400420000300b802c90340c00078081c6607103080301c20340c4440480070381118041e545503100e650140d4070596a00c2c1d6406c4001c0395040141d0307480000181d0049601015005144044481d28118020095034038148026000001d0ba640196442515100d4001e421102a981c20b0300c0d1007030321a07400f80106409840468050300304105a1f0046604661203018103a041300e03d81a6004060782024040342070450700c40344140e011400c2007010f046004070603030002042116448010303281514860003c00312a01b10010000900d801003040d0003000321604010841101601d040e40c20300040741c0f0354015500011038844080922061804815a501c182c626523142d8400d001e41c108040030039500044c0b850440301400020701c580c84044c0036620900c00402ea103174030780e80c48400e40060030a5000002401c40c078508207502d09105100310b41088000c08520340071503000401d03180e11450001174000d560000b09003031580e04610322502c003d030b003100c000c001e402024506091703 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 393176717 1250 393175467 393175487
    0xe061b0109021c050708030a020709090606170d031802010f030b0a0305070609050f03010204050d021905030102040b0703030c17060d0305120702010506010908071503050a0207140606010216030c031b080d 89
    0x4d00c2e204090020422441c00001c444054042c2d4005203403161400202c03801402c0103800880c0c509494500020b90703030468000400e802003000001e07180c0040d40c0140202114103198442483c4400c0d8645078015036000203102000803158030740031844402480220369005c0c035a070b200030301a101c0c1550005d4503d030300410f0441036400445001d030341c51850200301806d074000c074001c05512000352903081c0018903000408545005030706000010071350f0b035080000d0881e00030303501c11907031140001994010164148100c110214a038240ba4034a404400f011150b012030040000c2e0003190100b181a0a160084040d030f07038410044641c18441d8a44100001e02a2005540242c0170503c1d40b60f0206410b00c3c040348400a40d0503100f8001400e4109103400c401a1001a0965628940c00c008103000b283c4c0922000d044d8810610040199003002c0e40020b103000b04180030020b00e0707130b82400300b400000c52180c010b2084a41000c0e4080d2050b240042c803017060308450b4082d40341e81c407030070014040146d04403600f08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 393177967 1250 393176717 393176723
    0x30c0510021c05090406170616120204030c14061309050711061e0105030f030d02030403050c0313050a09020405031b0a0f080601241b080915070507060e061b0109021c 73
    0x44226071f0b40d0003200449410300c00e08000c054000c0c00000b28622070440010140001c98030b41041188840750010040303038000c0d001503459801d0580d041c4509140084002580d8105881380340c40d1902074020008191118080d5242054540d408540745d0761198022400c0d01e24800e040e01c0013800e080329120340c0d00c0043e540180381d582e4504000101031502086c007100002214001c0c62419040006960007540020012010b010b010300c884040e4440400c050800c500d84a1000c14040d803c040405c4207601d16503010000f4140100024003854901154240342c83c2c4100a6081da94011203000503010318281d00002104040d80718005002d280009119049416442c0a0700088034844030000306a0002840728000c00c0602060384a1074400e0312101903003502401c01181003050380000258180c0000403d1408444d000c00c81c80280101032041000815450408001c242105408100c90303010b403190040642c04101444c0300660001c0d084102403a9004281c090f0480f40c02003500d03103201c0360300303029 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 393179217 1250 393177967 393177971
    0x402030127020a1a0301060c031223060a0501050702013c0806060a080c0c150106020f071706130c0302060301060309150507140c0114040305041e030c0510021c050904 73
    0x4050404c00401c6081d200e0760703101c4510b5a03080030710940d0102c6c9110011410032500f010324503c503074800c2c8111545036445080040d80f01c0201c602c2c140c0700b110701030042e500c200201d500400031a80c2003000c580e0078a5081c240f600f1840522560005000700e07034101c4d440d90b507059400024190300785002211450b070781900da2560945907401408518001c0d6404d89000c101d52901240b418131a039005412040303942e6003110240c00240805501d100f03000e038082405a0f0003009902c02030081440804040c0189840c00108039001d1f400f040e9603524054040c90b440b0001e080c41c0020b10411203000f0703014503005020b281e501c0d699241c008009089144003540d10106c1ca401c0d040307443c009800b5140c0201007036910801c0100443c0103038440c80e0721400892003150740c3c030342c03440c16030030102c082c0140724501a0700c525488030b1500100550b02050034142201010300c2c400b09200107912030760101c00703030b0b5802d5030180383c05200d0310016032030315110142000c1420035070840319054035800750041080f5034040ea02 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 393180467 1250 393179217 393179219
    0x15080402031002090d060207060e0d03150603020f0d1d0303091522060f1808040f06050301061e09050303070b100524210903030405071406120402030127020a 69
    0x200b01c101d01031a42c103d81c0c80094203011001095164000e000f00500070302c80060102c82d000240d03407a11035100c0080002c242c5035942410000000710040e0b004045504040d03292006020b610030031441031102c401c0f40540c0c1c42c1900c51560109066120b40034842c0d004880d641d0924010480c0d85007150b03a01c1c0c1e418101400d00084480c071a0200c151540300301c0c9841d00030b0300d520f55075a00d07010f1f007000c1d170000001c507941d02e001c11110080403503800d900b94011500180d40d2030420700d00c10001031068120100340301040004118407680107001000099003034100905180070480212080b00c3d060f0300c141e0b4103200125150f024010380d0b0f501c0c0380c001c660603c000304400d13540b00180a41c3c0562051319082c0100010322041c42400c154009000c42070028100229a08548110201071041514071000b107500100401c07041040410a800107412100c100d000f000201a00040091180465500800d0a0300d030118046450075003051140c40c084a003021030b15a50100003200f000d03110b0405910528011034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 393181717 1250 393180467 393180493
    0x304030c09110405031515030106090e0d030b090c07231605030615121002030106170106020606060a0f0e040509030901091d0615070503030a020304230601060f03061508040203 77
    0x100f00ca08840014010f408001c00082001050710801040c13a8881c0c05100440c0b06556400e2044102170119100001400704400181c0c4c0e140212040302d40c000c2c1850003101d14020360f580080783d507100b100300240c2d9984440e10300d44034850140a500321400b10300c2021681c1d88904000c1605003034403070244040c0c2041c07503588081507919a030503141441c02840b03141c000d2a203402d007183c2d01102c14084004480c0602e50705407824080341d109a1110000941c200d2400100d03624420b500c034010701241c4004c0410b0b05058000503601c3c4030308840310051054600c8000e022900503a60b400d140f20300103208000c14945402e000b5184c0e4413155410f40010440b100100344440c010000d070010281c8281c890311a59620710a00060803612220403000410070700070800066401c20045109070690000580c0b83d050a00e0011190035020403018044601ca11209040d100d0005d4400d0440d42d09d49010181c2c2c20030044c0075002400c03950401540e003400c03034104030180c41d00005c8140c081d074825000c941411090f04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 393182967 1250 393181717 393181751
    0x4051507091805151009080703030207170105070806010503060f040c0203030a0e030c03040303110304090c210b01080403032d060303090f080709050720070806150109090507110304030c09 82
    0x21402c001e0011040c02d041d40c3d42c1088185414a0b841701c0c10b1180750b6a44501c0c4542c9049982d42c0102c0060344502d2040c8003801605e01c5540c10341460a0091000e810450000380c40c1e01c02c020100c50400001200140a41d55150f101c030130044800350003000340c121050802500c0740d0046600c2a00182000010043d8103000811102083c000401841c00d080c110340e401c4860021480450780144428000810140b0b4140301c1c8150300d40c850f482e0350511404840c0c20501c074a0359a40c090350814070b40165180107036008490381d03501070b42c03600d4006407080542404e15500d40045010f1001c080c4958546100c649880d4404826640203440b5040c035542d4641c1c00390450a142d00a41031507400130401045141c41c030f40c00c5903402c810709050442e901004511189070002807401343c0151544151400c200ca014280005608582e26504500c1090105000030b0000001d5101d40300e02250f0b91000140221b2040702000000304540060b81c0c0c0d50b994030f0900c07801e002e04a01442403107914100c0e804444000903 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 393184217 1250 393182967 393182971
    0xf020d021b09250302041d0903031b0f07050307021e0a12060b060315010e010e240f0a0f0f081605090406090f0c08010b04031a04051507091805 63
    0x5641c1c1091103484400038081c81900240c0b1440d00000c0c0d03003a003001c8014907040f0320b06904146aa0050301e9500e00b0603214812062080c03140c001c0f100140621000000c017004a0b5400362891100400400300074840c91103501c158a00800a030340e021030b06c407040003030200040c030915008880d100da207509100c420030714058440f403031f03141c0c0040644410400c48807035005d013501e414055840068010a001c2c00b00310032307601c21030344081141e0035404851482d40e002070000c00704010031300e0800f503405180d07001700c0c00074070611032030800701d4500145e156008540b10003150070440814450540301c03d0544000382165100901d00c2020806407460720800a00c11b02da001d01c81c43c0103149801050228074010b1341d0551060320044d400985032400440d8036020350103410002c41040200280588007104001c1c201d001c1a080b9280140d81000b003000800d0740510040300c01d540e4101d020005894500c0c06030320f002c4215801c0101d002c200c80c02c000c1d00e40c1c3c10441e15000c82c0c912140c0c2803050021007104100711081 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 393185467 1250 393184217 393184243
    0x5130501060203071b080a0b0708090d0516020a080a03050c0d1403150d050f061f0803250b0112020a0503151602030d05090d032409091703070f020d02 66
    0x140b2042c0c0210b00040503c1150105d089081d5030074036100c076005810003042e40b0061300c442030f030407051020465100d200310b03034441080c80281c9543c0110200041c05407044035084090b80840c4583c5030103555075941e09000034a01002192181d1480e480c01070860742281341c20700c0241c00740d001e51001e41802558100c1c0111002980c0c0c914556580100c0d016011042c52000c0e04120243c10080020b503080104102c040030080c02860349261640d4124000e039201c05203031601c0c0503040410084c40d40000f068986144403440c001c200001c0101c5403040c00c00e10504054403130f07442c1500004d08a2272240d80800002d001350b17203030b0076016120401d043daa2001840804155034032403000030b8030f0800e40b48a003000c2e07680c684150b0b071404903031000c004181c030400d440003001904280000038019401d449411900801d91040a4a0621200300071082240c18807501d80841d49541100e01044003d007250604944820044c81e101c2c00d10390001003841c002d01c2c6225015104554a29010b81e000140703012890031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 393186717 1250 393185467 393185473
    0x3040609050105030411030109030c0b060f130c032a030f02181002190309140907170603030d110d0b040605060d0b03030d020c0615180601110703020a0f051305010602 73
    0x450301d4011101540700410603229003984011031050b83c0d5007030080307550141c042e81d02d082900d50b0a0030440189039024000c00d103d01000c904c80101a11000c2c0c030100b40c032901000004044a250300203401a0012011840c01c001848c2c0e014130007940c0401c0c003054011076541e400c10003980005072a01c128412100c4c504080707007158980030a6407500d1500c51002040502c140c40000ca114500c04c002c40d06092030450110f21094400e000005e0550018482d2007402c841108140c00c0c40407002d01954100212644851500c0c000900e06440c208112040c0c40c0320302c2c80400c502d440400c1030060315008610f0880449082c0702d14a0090f01c0d090260005a40004201a140c18207004107140201071281105400d40400e0242d034191079150b2002d03103100400200a41018a01186003003000c1440c0010b082c80f964400c55110440600d0250b1607500680a08285c400401d00c40001c1c0e2512805070f00013940701b0000c00002c070b4092140010707001111415182c02d002203070111000400da4000f4065500103038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 393187967 1250 393186717 393186719
    0x70512040f150905130905030a17090102030112030f0c02061308010e061014190803070c1a07060e03120106030b1201020f090603070903050303150907020a0c060e130e0c040b010203040609 82
    0x41741c040040a2030034000c035000200d040303e55075410305680081034408049800a07099081980c404c0d41840e07481900a8000c510790343c1030414250070704404030000b40801604078824400d2902481e0281007003500100136540301c04840311005d1080c02d25000714078407542041030030a0104000a04503000c0e980b903001c1c02e0303820340c2000d201090a503002860340b5485401c401c008010707001c0309422071015200b014059590380740641000441c0358220f601201002d480f03040440985c1842800761a0059440ba0003c15a0101c04803032500c2c502a0035051140c9942ea01c000182041c1c055110404400d8280c5a07070042c440051030807400c07406810555585684100071040c854544240115071082040c14070b0700c145078898560501d184c00c11501400c10304250721446207540780802419070b0000c075906c024116503201d59689030021440b40700743c1c418841350b40000b00704d954a10410304a1462508c4003000201a800400c903a1013081c941e509000b0391420150100030b501c04801c48068400035114a00c3c82 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 393189217 1250 393187967 393187969
    0x105060102070501050c071a070632040305070203160905010b09010c330207030e0406140405151810091527050c0a121e0209030102070512040f150905 66
    0x51b40c0140108003042c000c1070404180a080000380ca451500405804ca86a07180c41c6461002c4900c01c402c981c00010a402d00c0e40790310742507011420810710284c40001d81d1500d03603140668803801500002541030003000d850501080014000100b1100554020b10082e42d03035841d01d040600c00c220300540081c2c103459241c804a001d055034a4004040204040c07880d400d0074124680b0300300303021f9051011381c1d000a64403041c542d0102c552185a0307000c0320100900c5103041e4400a14008040103940120303211030014441c0c5d5405810008510303030241c4220b0f6060b83e84500d4501c103400880f030980d0000343c5c5c424007083c24040c0c0c0c8941c3c005070310301d483c114488034101400c9000000020f94191039890314440c01c40241d1425028030b078042ea6924000d942c035882da00030090b080550002c0161a003178a481400d9503030b13820456503a03e00988100c8016a11440701000c00c1c0039100380400500b0502c00c0034070074000e50348028010b10444030700c40210007d0703c0d2120084090010102811000904040c50600107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 393190467 1250 393189217 393189227
    0x3090a0201230a050a02011104060f12091704051311120c0717090120060a110705070303020d11060603070302060903010906050f060118031214040806160e030105060102070501 77
    0x9580c0c402424192040c90310b00e0000e0295001c02100300c00160f001c10b40312803042d02402010401c040c4034480d6030606040c0100203043e20034040450003080348111308190419840c4d44a007203201d130484000150203100441161199101c0d00c12240607100904c0c400c204440e062040380751a01d0344080580c502401e5040d405d1120078007401f0003054010402401d00000c0c070390300055047c0c5500111440e00c481c1c2d14000508038001100f002c0b880d1114000701038480500204005a1081c515240042c00d000610200c0d00640682040140107124042002c0103042c1c0004416800300078a588202c55400c03400f9006445a1080e1440c542580c0854004c0c001403074048054840e2500140000944403040d4540906540d425100f4112107540c4406024555a100f00342c15190040c1d50031010300700d8038654450300882158031440e401c11202a0100303407402441000c031801080d45108651282c10207007044108200d42c0e80c460070101d05103020039071380d608040c02624400c22058025291181c9132000650b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 393191717 1250 393190467 393190487
    0x9060e01230c1213060f08042303220905100b090904080d02070c050f0303041d040c03020a03050705040b10170907080d02100c031107110a090c0804060b010503090a0201 74
    0x9118007411074143d0300040d1103800b42205a6000f80b82e00c020360302d0440058280c0d81c24085110810441004000101d988445c0c0a80315440e0001c4541c59400700801c501d0440c00b0780e012280401141200d0342c0c1030440300c15028402c4d00c4141e1070410280d250189600d100c0320785407044194110007804040c51915000038200d40c40b80c00b40c60000d14050070005600100d0b84150b404454044140b5818046400c2a4030001ca000c03005070019480c0a0404113210003a6804010040080700b040000408000c850f81180f4025035000d0b102d40c102580f00c0c0f5040b91514054080d0303d01451900400110b540340004c140d0441d8002d40d220b038140c8125118612a2056000302603840c81e224408000401c01e00402142d40d010001c1d6014041c80c100f010580400e0311a903448a600305070034031210301804000802207070515507101000c00c042e10303a64004640c071201d5a60190100340c1c502a1000316498002191900c034a210300f604100c81e00108006513100e00007a02c1c01d08031075100c6002e03034005500800c0004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 393192967 1250 393191717 393191737
    0x105063307080f0c07080138030604050709150510260a020c100c090b0a12020a0507021305040510020702210a031e02210c0d09060e0123 60
    0x80c03074040c058480310a660311003030401c00708100c00901c2c0507000c0020711460000e4903041c0000c0c4240f0480d100301104410407400c45000000b074041200249520b86081030002c11005400c2d50514505810010780b81c850034030402a4007403c01045007a02c40c031840d030520036600c004005400441c4224400c8404070401b212841c8680301040c2d00c4051941c240711031602ca0000e006000d41e641d21544142420034094200a81140713041070305d81d220310742d00090002c1c2550b142010f01500d900790004120b0716801e5038060800fa4a20014800c0b201a42c071070002c0c82e07503a000395191106079070348100d00022a842118040c0580d08151004410840150020312025000420340240c0b120308110921890003540e800c40d505074000b2840134101500602a081440002c2c0340044c5d00a9490320044c1d260011a002c50b442e00c0340001c1e100040340d00030800d8403903400d89201180c44840d881100a09441c100380140c0020503e24406480c99612410300c0000c954820108801c0300c02d0030040c4c1c1c81d0141c0041100d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 393194217 1250 393192967 393193069
    0xb0a0606021b060327011103070207050901180209031c0905090c130b0901050706020c0102030f09240703240f08010c0903060e15040f02150910110c0a09060305010506 73
    0x3a008a05c00340144164955003200d60b640da8200880301902d003c410303601c211701035803c10340100406074040000403030400803c1400f5907144c032008002800d2442901c0c4001e55010b80d083c51814040d40b2804000984000755806407041d00c501110000c10b02030f8039072456003181d03600800c2c040500042c0c040c010550301810100d060038002ea40702001c0e80c216070303506c881c0d603903000c01000300101c0403410f11900642d12101810403000c0007034001603002d9404000c10524010000480c10a601c42c1e130000103205001d0f182d260141c40070700c2d03403000403081620580d0340380d4103084404604480107101d054051049525800c407554690f54070070001d881000803244281c000c4100a0244000c4600520f200d5481104c000140c501d4a01c1041000d844001c0900c0c10440244000c2c0b00e261109040100007a0003414205441086050418640820900401d030000340f804d00004402c0e40c241c00c5002681c0c42080280119030b209010310000c0401d00e00030401030401c544101c1c1d607a0a000303440c01a844181408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 393195467 1250 393194217 393194281
    0x2030c0307230a0e040b0117071809050c0d11130303112805101a01031503060216030e1c1205040b03010f090b030c012a0b0a0606021b0603 61
    0x580ba80e50b402428000001c80c2c1c921000c514103240900c03844d40c1d030340001d0a00905e040c8550b0408160200002c0c109000c0c0308034004070080ca080d207010054010140650140980d2078402002100340d008500d2404800c0d040c442403070b0000c08542c00703580028203102004074445245450883e0810303e648440c01035401095030180c450200d4500c40120b0b040c0d2220180b071980440e02c3c00c145401801c00896000ca49002010081411480185812554240b0b0086007224464959802f12445503000400061000880056501010b0401008a402038885034041324485052108030b02224445201070745d500360000780001d103008a0003903e0703500752800905160710fa084801da01da00a810002004040e810104610302a5014a044408094014184004580002030300c614400d00d6006da80400041340050100c5994219086c103540120986110b0300301446140e00421302801030744018061a0890001500c00c201003290840014010500e1a0740b100d0303d1207920017041a03861801c25455032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 393196717 1250 393195467 393195527
    0x702060310080d02030406020d0e0301020c0d020c18010e0a020f16030c0b0a0b01020703020f0f040f060527041101030b1002100e07121b0512030304050c0402030c0307 73
    0x203184501980488144010b04014959243c04641d800c8001150300c200400c1c44025804500701c2119010350400049562410000a0190107007850100552041d040840e103519800600014150425540c50b428012600070419820200b402042020039280340403c1121134a40d00402e0364100c002d4500f0300f80b0070840e024031072410303e100c4141d0003c9e65580c0b240c01880300d0004415000303000b904007003200e4104800041e496108511019104084005c1e410303c0c00e484082d82a5107050006000f00000400303003603c1c80081c030703050040c180260700c654000581004207400ca00480b1112000d0000595520340e18080301803036802a060415840da40b1294286d10703500680e1382284c9803034010b0090fa00e4540c581c0030468007487c10406655024007810404e03080d0018815103803d0700601d0096a900c215400c6e074004d2116644080d07003281d940b80c0310840604001c0302030340c0100c2c410800c0c0c45650307400b039081006900080d500b00d4000101040841c0d900c0d8062180c2d40501a00703100054407100700ea40d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 393197967 1250 393196717 393196729
    0xb060406080a03020a200f10050f040e01080f01021e070501021c0b1e010909091e050f06060d150902220f060b0a09030b1306110c010f090803070c0204020702 69
    0x10782c21809a4019020841000618440001389510f61280001040c82000004d54030440020a1901551500c007000121621807000c6406090b000840e5564507540d81e216546030040900c115980c03405040c402c000d190303106000f00d690b0403d00842c0d0a103c0060345641c485268003289044031103660811800100d02a06400b002c0c02c40d0240e42e0000d141c44c122410701401240e08501d0b0303150034000c40012099603030800c170010b096075040b000004c2d480c074040c50135250720201e000d050a40e01114004400402c480001c1c2240317149843d1081c0c0d6403680380d2a0600440e5070810b0b000070410b48080b04028201907140c0c4c40007210500041104c2846d032801207200c1d50040304580030b4050203446400a01c2021254042c0c08000e02421202d5440c210200c81e0080c007044440c0001046001544013086030b01d4801c50035400341d10307044003040105c0c080f0300a40c0c00c41d590194500c1c0030305508003000740340f80403401c0c45a00c4020ba040341e10540f45541d404000c4038011510320007240c0c042c1d401d114007400740c0c640c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 393199217 1250 393197967 393197983
    0xc0509090a090b07030603020f0909071a0705010501080a05100605031002090303090406031119081b01090f15031811040b0102100203090705011106132402030a1509020f070b06040608 80
    0x245c070001542400c0d40140300b42a11072944c1a4000c00c4900c06008004000240010841e9440c8400c1313000812043c1e01c1034403512a254020744030b5802e000c00810300a1000c07070310f945a01c3c0b09004032800c0908500020065500511626505401c41401602c24103581d8005001c4040c004080e00c6c944111325001800700d881940054910079104410560141001148000d0300c4a5540c0465042032400640c5585c0703c408032699450802e011151507410390244441c80d02400d0060401380b1203940303e000185400d0011807200000a0a240888070b101f00c0c1a00c1185090f030308091800b2903840c864040c803024107841e00856046100c3c046c0708481c480802c0c0b02840c0070360b944001405c0050f242c100010903010b03071411180007541141c420301c05010044c0d030001c500d10740d00103500c0c0881d501c0d0f113a08011400c0503458215199000008000010745554040315601329000c0b008884c00303403105502c004070300a00060040c9940b08000c0758012480c080304060b80701600410124119441e007000034207000c88 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 393200467 1250 393199217 393199231
    0x6090e10270e03070209040204020c0115030f05071d0a0e10020d02040e0f1003060c0302070f05010203060415050117100b070c181104060503060f0915130c0509090a090b 74
    0x248580140100100b40030700c0044031605802541003101c02e400151210202401c001d11540d40007030039192880302074201e2a22404007114022016540f4200040702d03480c294001c803014050380a000c5200d035440601001c04a122135281e0115550711003a00b4010000140803a580d8425031068500440c0c0e180010030b03842c0360280d000b5840d186410854440f072100500f841d45612659010450f02e00b801c5c807117500449801c180081000e07112540194001d03c00c0e04009001e40c6130780450803090120540095010f003809031020001a9500910500040c2c011300501d4001120396640005108441c05c0013030300121810100c0100300d54810440103268400c150850b1b1048100340100716500559031160801c0b8419803052040c6400f0128010240c42640202000e1150100c042030881d02d0710307403202111070805020a095070920020700c0003020751206c5414404d40e0a0103a66907d21414024104407080544403141055244010802090001084401c41d1a40e6081e00380110b01400141402856 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 393201717 1250 393200467 393200519
    0x4120c021e0102070f0806071b0f0b0f130b0c0c0c100c050f010b0a120503120a0b042d1e09030f08090102120c030c0705030f0306030105060a06090e10 66
    0xd8500c006818282960300c03c5d00301201d0030104201010022901c0c0c3c6d031210705031a224074054413143e06007c42594065000d040c00d02944a00c4080249006a1600a4001ca04900b03420381c0c64400c41050070384403842c000c00180201300461039940b2000d02a0036040b0076030b8140c95800e8280300c041494100e4654500001841010031042400800d210603940a9103c90080c0100340042022884d4041c60340b152103410b0803060400c405100091040d166900c15850b0100d4150801703445200180a8905440748100c2c90015405003c400e0800e10361035401151110020308503403014103000504084450440800c1d600d2810842d0742d0680c46040033b0b80d4420707101c800c2007440d035040c0140f45180060400c4070b140e00c104219410601012030aa03441402a1821503596541c450301420a009004008029100209031405015045809140300350010b500800c42e6136602c00c10041c80208030f124101c04140880d030f01f0710140c01c0c4984030b40d070b00400000403015150398482505420100700030440071840d13 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 393202967 1250 393201717 393201769
    0xf0301020c1005090a03050708181903020310021c05040f0f1b1203122d1b1b330c020c0405010b04090513050f07061103040e04120c02 59
    0xd0250f11426800c44c00c200d000340008201940c000d0301c2442042005040500c0110711301c603d614041040100190001d000c0c1a244840c510044100c21043e0100301d107e4040d5400d140380510080c425210000103034004d40507800f070030000742002001c000d0000d41301803064100050102e00c40c0103441e5080c80c1700d50101c40444070400c59001c900b83c2680c0001c0d104061550150010a03849003414190042050000560b00155154101880c800400000c00d54140c101b0003540a4001c6d40008503007040d50b202484129074041c003c6420b0608020a0034a18a240c10190081404014803d210b28001c007104040400280c0c00c03402e0300c0d0b40302c9004110705510ac5c40c0b0b0382c0784175034180400710350020152401c5c8450750400300d2440b102c0c0100e015010205603548006810200c1024840c0192508072055030080c1d042e01600b20f46900490144402140e181c00c0d210180d0700c0000b0456040341d070140d103110896215030b40c0c2d50740d442c0e490403410230411001c0215840076a0b25601121030b0300c100050710000f11 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 393204217 1250 393202967 393202993
    0x5030108120f0a081810060303080609041e1e0b040204180209010512031215031603020603060108270708010b041406090709091103061c03020703020603060f0301020c 73
    0x4241d0401009407619018842940a000301c14181c2c2e03003107661801c11a000d9594401d419200e030308129100820b80c4540400e084184010f54040c100380d07802655507050f583e40700750501c400d2800596004060b00040100e004410340d42484103c5540e12410090080d841c07440e0f25940000018107098030301c00c00103400d220843c43c2500ca00c2c0814a030205400c880d03c8855000920b540d401489a02d010f4028442d8022803020113204030b4440481c00c62103050345003000b9420960a040007410503020344288480003048410400403407080720760040c0f00c10301d16a200f500444d00c05002803c1c090504642c2d030802d00115040f10210b21058808000130249549003090107800d580d024001c00340154034007004082c2c956020a00d5a0307000d4000c0d01c100700ba9480d1600100c80044c8282c2c80400000d20f03004a000b0548050002107000d91400c448100a4100112014084182ca18001009a0312036441040181044009541d110310002c01162100e65440b002c01c4c2a40c0c828070460140780c028603000700c02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 393205467 1250 393204217 393204223
    0x13020405180a1b120b0a0b01090504050901020c15090a060f061502012702030703020402180d1407090e03090103090204020c1009140f0601090f02070c080d0909110a0c05190305030108 80
    0x10b05040581602d11a12174403141d0042e40040e200c110b0417900c0d810080d550764028000b8500418015004004526100041d14001d401200303a0201c1805000b40500c03902c0700e0220b0150086c0c5020000e012040e05c242d0706e5000034480b140484802d907848180005a00c01d289189004016803038002240c3c103801500d520805a4400501c07a80e9840b11240940158070001450001d403a0305860041e03440c038840b030f569000c0c00b5158241c80c0e84103965166000c1003003203890010788550760001c112890207858288150607101840c000412640c4144100742e000d40c800d03001f01c1c64040c0054401482c2201004005003414241c2c0403842e407003600c6240550800903900f40828900280c200138081003508210540e0b1604010b1140d26800c0b0b464000305000d481560b81120100d550102c4043e40c59943d0b01c0c0500e84400c07000e460100452401c85c000510742e995030040b00714000002031507600d02400b0100a45004101d00c805844900c56004400e04c004202200c05103520300070b44945441c0e40c940700c0b081d42307 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 393206717 1250 393205467 393205469
    0xa030509012f0304050a23010b010e010503040b04020d05030c0c031b0a0b03071218031701210f0602030c190c110d0227100e13020405180a1b 62
    0x580c0048425042d4004550020342c1444030610790340c4280d5035291410308a00d412400400a081907440c0c3d200c031600104840000c904020b15800280700d0010b03c4401540c00c20100355140b400700e101000020001555501155407042c4001c0060641a10944540d40381d07421020000c411684075150102c040d14040050500349184040c40c080d035134111101043c101c0400384507003000c42030044041120203000d60b1504041001401c41040043c941e986040d00003c054901603000c100c500590400000201046074141c424030565207050309038404141f41040040541640c500340111540d8001940c240001c5014045e90200261141180b04055010414000328070052000718400c2c0c1001410301c50000300158803c41e60940090f10600129501828620220013450240844010907140c40c001c03030b5000d42d404401c007101c0f65448280c0c011b443c0a040d52100700c000c0ba404030801c014601900030302d03409042a013500038190401c054542c40c0ca15134035021940c1d01e000c404030005900501d48401c2c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 393207967 1250 393206717 393206741
    0x40e030306130b130f020a0f03090c03030f05120f07080f0f07050d0f0c0804030912111504150f1e0c02010f0216030f2001051b120a03050901 62
    0x5451070a25100085111a09001d2250090340710000c0360840d0f039030700e10181155103000b0070a026204c0b100c20040c000b9401200300401140d0440803120b0094400e20400d21040e9004180002080c1162010b88650200c00b480306e0070890300300509480e04035003241c2d0320b000f40e00b08007402140d8140018064000c82002389281407020703070f40c3d007000382d116100303403815400203102d0400c0d0395524200d40d00340010700714002791020054103081d0703000b9800e42d0102406212b01d0003595505601501c2d40c80000c0200c0e030002004d04003502c00c1803039640c9071803e005051140e034201c5100c0b9280a075900c21020482c129000d0040c04613407200f80d642c1c00d07641c204031070b8030b00135890b40c0b910b0328014180c4802401c00810070030080e041041515110381054002c00c801c01880c1640700401180f19900d00e040c030550020340c4800c0b9184d00c008105981c0c8010004151150391030140c417800d092200e4815003800d140302e1103992544500c124202e501c10350a09000522902e030543e81e003c40c0ca0703d01040c1581c255005100e441c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 393209217 1250 393207967 393207973
    0x7051b22050f1b043321020c152e0e07031b050c0f07170123011205070302042306030a02011b03090f09090314031e0406021c0b040e 58
    0x4600c00441c07030000c407020350305c0140c2440d00502c08580401c0c01c110340003052501201c1e1400c4c0c100445074100150030444032110303000540e0040c00449a07001e07801015800466139000c0075510031650f41c04030405500040040000080a2800300c4039519000c1204001da4400c400c10414404203110510780e40ccd0210040c20700b4054ae4060b511403001c841c0d00500c0c1e10f001c207e8081900030a41c1424030000141014a030103c8510548800d01e605155844c2041361000d50301c3c01b4020380d0303c0e0044d0040d40740c81700c0140107030524607032801140c0c170903450005e40304440902030f1000c04070040c0c0c0e6600c54030002080318060b6800000d044034503201c00354005010a071003503200042d01c0c0d00603a0b01c098900c107000d4400102805101c2c045c034056032200b400c0d40103051100340800022500845681c4006001c3c0c0c041d68524401e19020004d00d1028442900d030615009600309400800c4285480e400d60041d1141c500145400c2d2560b80c5541c465803c5501800410741b1039403050000d2410307001c1c0008544c000006 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 393210467 1250 393209217 393209251
    0x1107061b03050315040903020706022401050f0a08030c0604020901050402070f080a0507060504050a020315102304090b19020921120f19030207051b22050f 68
    0x18100412840c440282000310020005140d1020307814080c11402c005001800003404a19010307480d00d1981c050400148079441b411104045810740400000502d5a041007c0742d0070817040c800c1d0500300303086461b0840c04901c00021201400c00c001c021002400026040506191040004e1400306a0256216a0040c005600402c2c88010100c008030b5101c140d440e660414035000b03544034064080040c0c4000c7c684401c0109201b030105100030380b584200e00381c5e00404003206151070041e1040d541c42c098401c01c50320500c0645580a40c0c900303c17401c41c04c24866120034180004090b9007980e801128200134140a1107100c0303100300003880050022074015030030603010348003041008000a1340c42c18210001800e1800301c4000b48810f1a82e55402c85805a17604803a0120043c198040030804030140345d005030f0140c86620910a442206620401625000c3d1803200989060550082565401400040c106680c8109203c04890707504a0340f40120701c51400140107046148001c04809011950001d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 393211717 1250 393210467 393210497
    0x91008100501300b03070801061a03160f0201060b180a060318060b0f09090d0e040513080304110402031305070f050d02060c0102040824090d08070f03020f0a110706 72
    0xe11001c403052101e052001d9000c080c1e250013030b0154519103501030180d180c010400350010341042081e618014080c040e501c40200c4c2814140c841207492a218060a02009500031b201d181e0b00c034130182d4548008a02a40c40312688a0310307610074424140101e4400c0d02c6000311b07041400e14400280700390709082080710030300c442403035083c0c81850005002641c0da40b540c03031b65551071140728009404040c0aa0340285440d1030b9040e03550100030143c502146540001d8091480c25005c0c3c0c42c0715928240000c4c00c0c8281541d20002641c00c050b00860701040740100e104025100c0d8400344d4402d03240d181e02d00a868600d03007403a5003001c0454000c00310307040d40c02000348200c0d02c071080c0c03110001c0c0d03050360b5690b0340701d9020008174021301454000400c9409400101c080584003804218010034081e00c4651907901c0d1005555134550040c00c0c5940801d0084000a01240c042e5800c00c8a030445410013514141040741d8100c41c40c0d202d168a6008200410b520700c8401e0380c1082060007400c4541044080065008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 393212967 1250 393211717 393211757
    0xe0304060c08190305010f0f0f0603050403021011090109080c0a1512050c1305041b03020a0912051e1902060708040905041101030b0409081e091008100501 68
    0xc02200c0900c1807805003001004007600031554881d400c01e10041c065a00414010040d19080c45404000c0c140080c01289010740b00010500f00d4400400031100c0f189811130680140000800c02d4055000345580313000c4079442400760346803401e00040c003641c1e0b82c0400800544541004d41111100d50301252002d041034403000804011344658004000da000d01002d1300710703000040d1002c111850303403c3c1400c3c80903282c6400c000e400b9044114a0b40f18415440b00c00f07000445211510a00c0030081500c24012080e009900500300340380e680c13601d003d1b026203e610450542042c050129000d9002034200841c400400c100c8228036000d841c0a015003040c03032214099840c071a00c0000e8405c400c0040d82d50100b0800800f110000c19440400340070a151504010050810700d54401d40802d007402501c1ca1180b51503c035092003103078026034250602104101000c1e0041070000e40303120654080041c4006650703946c503940e2461070380d80d072000c0740d1745400d107884c0044060b554855030500412040310082d0081d01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 393214217 1250 393212967 393212969
    0x20d110115140a03050d110c040504020906010309080d1409210708130f060e0f010e15090609150429040608090a0c0602030c061305060403050d0f050f070e040e0304 72
    0x2110b0404440ca5214001803142001a84010f205c0c0c81104640941e00d1b07084a4480d1a203040340e03068840200d10b4105000a0740c0b0102e500941c0704407000c002a02e070358001e6100c0082c0710b00400005081102c840e000d0030491b46240083e890240c0341c1001c0080034007040041400f5015001000d143c1401c3c1c0184600c0940500d840c02012100040360444040d0301c1c445004005001e00000070107401c2d1340d02c90141100103a00390090060b13544203d19030040d4021301c000e107051f040241200d400316170601c2c0c1c0b0342c815412031150035034800701c00c00541d29075a030f4028a001d00502d4403802c0c240c1d5546000e4a1881e1a400303400240c1e101514507001913a801ca0003004e4504482c00c1c1d0400000d10b0341c8a01c011810400300c0705008003601c1d504031020407000d40c000050b040c01103482044410507140c559004030070000f11800241203031300160009001034030800140041d590140400701e46110081d80321000c3d10011602c08404a6041040000c0d171640101c200480950545041080c0c03804030030615224862 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 393215467 1250 393214217 393214229
    0xa1205070204180f0f032601030303051e06061804091119120305092403011706010b0d0e030706062301080402030c0f0307120b0117072403021603020d110115 69
    0x1050245c403c0c140104c0c1c20502c44200c180c0c030075040707040c00d41e41c50403551400c0c0800d5000a05c1c1100080c8aa403004940094892001d078001c01d25a607403000304030f660b610041c811000034114001c3c41d0495242c0d401041c2d1070500c51501c0d00006032221040c880c03402d6403408124102d00440f08104220b20700740041c82c20303068151070440d5503030281c40d0129101c190031143c01d081150320300820050288180d00550306981403408082e02540c11030303078041d942d5074084c042c0d5290858100042411940d10364000302c042000c04c6e00356030800382103854410844859a11140700540300601c0070089150306958181d86202c00d0034030f10b805007030030340210b503071000c084e240300b802419441854660395400300049002015040d250640105070b83ca050041d1140c28030801400b11000d0b00b00c4501c2e0307840417031014280c45a0784a00400c0c941001c0d20528100c100003510000c0c55803c0104091044108040e1881d65020307030014890781d030003110000e100c0c00c08840b1541c2c0a914090614402c600b0017582001200c0f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 393216717 1250 393215467 393215483
    0x10e0a050a110c0105040c051008060d0309050a12030215071b0203030c0f010207140a02150306040b04110901090e011d0603120403300806120a1205070204180f 70
    0x41c0320341c1c5400040c507158003108446031011550419590301500030314450362040c0d843c0340d81c1c2030b40c3d542480414601c6060f01c0b4003080c1040c00044440c00c280366900d020038003c2c036010300d40c2d5a850003c2141d006540e080340355404058a40351051640401c01c5100c900e01c4c4917006581171038102d000a203141c00703500401803030101d000b01c01d00a541e41041a01c100040c1e4000340c540040a4207807150003540107030701c21103484e103c007010072200140c0031074402c0b82c241d000341203103041d10011440000203500080400e035009035100c40c1041e098403076206071142c0501d451056551100c10f240050110b4017254007450310b000810005118010a005d04008980d40341030000141e921003200117401e1800308816483d030321001050020a0001c07902a0301008030848001d0b0f107400d030807485086556a81c21a80360089440e09003c100306082203414010b44488039815210340300525507510010b8401440010001140130510034154505403083c2030241400403065861b501040d90b41800b019943c0b0740140c0400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 393217967 1250 393216717 393216721
    0xc091e0e01170a17070b060d0302031204060e030403080d15060f030917032805060319030c0203010f02220f0504091b030f12030b011707110106080304091103010e0a05 73
    0x1c082000101150342e40900f01800302d030384e951001401500220b10681d2a040c90b600400c8690401550034030b031040e0141c1c0607506d4007240c4174140c8410703080648101c0745130f540c0d450f031040207041c1400548061407050303019541da8402000d4039403e6400c02c6181c0804a07400900c100b15031034000d9411010000281004600542c550170021085070325007842400d003400c00410040035404505140d2200002600c0d849098040294804100c4400701c540e0342e016841504079102c003601c0548500e00300d5109150000411040d80d010901390350203040714019064012514013000d0500442c003015000030310512108051405004441700c5006100b0701c0c2c010b56951340d00c88240f00c0301000301c801000360421a101010ba40740782c1007255001c2ca00301656000c0b0f03200300500c44e161007801500b100820580d00c202107034880c1081c011450350044c00484c03d00c010417040c051024428000c020043c50b03504090742c0c540b4944181c6200750741c541d00e08074000c07034020030051000168880185030030042e02d1344001855 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 393219217 1250 393217967 393218009
    0xb1c02010807090902280f050403020607080d021305040605061608280801030201030b0a0e0f180d02061b040e0a02090d0b010305030325020a0318090c091e0e01 70
    0x40141e138000b02e03241400050034a00148094000241a241030300c240d8003503040c40072084444404191031200054020032080016203040c002905010b1702411f611898400c5c142c00e0a4100d174070005d820b10801c901080300308918500392252000038002901e4052802d81d1030ba00b071010f03c070500b0b1002010741c3c4010410b031080d01c10301c0034659440120361720241c0481aa9900282200800344000ca001a051003104411414119981c00484138101c0210301d1503210004812008900285428035040c041d007519620400204200340b170410854018040c4dd0030110140109680391000b21044204204000c110800c035102c102a440403070b8040058541c003885c0c00042c8400030510300074049811030b50000c420f1000c080021402802081c0c4130342d02d080e540d83d24400440384840b4441e00542c0040c61081e010a01032921810016194010070801540340c806400c1200c1214850703100155028005214200c1600895581c8034078520011804902e40580c003101e21a0502074003030b220501d0a009030072 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 393220467 1250 393219217 393219227
    0xa021005040c0f120c1202060d050a0f05010b120f0402030d140702090c0a020d020a03082703070b0f071e14070c1e05090c0f0f0c0d120b1c02010807 65
    0x9000062802c9031155a110113010740b07515892401d882060041d0800905880412256560582d016010302d041510b4118148010800281007440070b0b5203c0f44a50801181762050341d02070b02c000c080c07883c0c071104641e40704044100b00504152080000f8400d000140e0b40000d1030401002c0c9528052840c104000c0501d030b240d025550300250050b0149003800f00203e204409404400e64036030884011b0041d41c034080341c0c2d440303030b90102038045106100401c501c03200c0440e40603001149a012524504c1c4014038182c40c560000905460701171000f0280511040081c4603540c1040c0c0602c1c081c060440940032076200203e401803080c00b40100b8400d03446801100c4c0c001d60f010243c00103407104869a58143c070790801703503020b050b003424541c1c2c4c4200401c0501d4401802400f800030007000314101682440002076581c04060a040000b00030311841c0c081c608100180010040c09540716040c000d4003421120a4544100d0010704c0f40e5140300784121407804c1c0d040a20a030380e80900e8070600c00e469200d401d4070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 393221717 1250 393220467 393220469
    0x303061e0303210609090a030c030e12030d0e0706090305030a030c0e0612010509060d1509081308150109020903060f06012f0708030406080103060f140a150b0a021005040c 75
    0x44107044440f54529000410f4540c500c80c00c420b41e02c42e11240da030200120f48503080080003c012030f0301509100c01082c0f0503000300720007450280c4a60104111a603101e841d50700070340080c00d4540c2c7c5a4030010030f00351302803044d00020103040c100048440c1c255074407540c40c0d0090032000c804044c1c4d5104800c1e102445600922408000a07010702d9039203040b4011030706280024058540507020840c0072440b94105003078071728180303604121ba00034620440c00d0540c014007070401d401d8600040a02c0f5154161103100e0010340109181c400400d0a140b403c5501c2d1404641640004021841800350120586000c114913910a80d4002d203060a03a030f80c3c0f4016942160503d119411480202923054599501030401c00c00071240705084a14042c2d40304803444d41c92266008050010749890010400a6030580003e007116004040c0814070422030000c0302a035640840341c05c40075503210464440410f500420503000f41c520344200f40d1031311412010103955014000e6060031030641c1c42002409000e03441e142a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 393222967 1250 393221717 393221737
    0x6050a03060323010e030a020a031b0203011506020c0f010e0103050a0e0f07030506090703020d03121112010302130606210f091a010e0708060409140724020303061e0303 74
    0x15003030560202900c201826030f02c588041503180045400124100006449010446900800e80f10005039012500c3c0181000401d07881c40c404a900070060341c0078010301d0f046000150703005001503c0c00f20000c0c41c1105130006c40d4050000c01c8402c046590703016403118403128007820b011625451724203815008194008050100c0e009080303500d04854404100300c42200d000b041140c1143d156034880e21f4441181e448020340c0a0615981280040c0c05207044c1d85500140b0400050039850a800f002140d90081c9403082600c900d0390011b00841c40c00b1013a0b0240c515038034070100803207402c00300c0c0034044442c01512814004070002c1704400c02c41c11500854210a51050107011083d6103103002000c05010090000c04410b81600204514005003a0140300c0c802c17a43d5201d05c2510340805010090100311400c4c1d070210450710303407a4800d950401c18000148403c030000b81c070341c150f201c02c0300074014040c02948045400800c14888a0307178600300d07554440080112405c000030041c45c00203103544200c0b00d0760 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 393224217 1250 393222967 393222983
    0x30705160b060102210901140c070305070302180405060f0c16111c0b0c28090906080114040210020309091306151809020102251e0f06050a030603 64
    0x1041040040c40c070050103424281c08a82451100c0c3c0c03545003110b0358601d0402484901400f080b00301358854145440b0009088007007a140080342100c1d40d04110658000765569880040c040046040002c00c0c03180c528914440460705080c69a50a600e90b003002d007414041c14a0703140841c01c1c43c40381d002220030040a4880040175490344d8941000400f2458041c1c512440701d240c141c401120940401180700c960001082120340e803840c01c408165000a8181c00c0301294203012001c480c9419021a1402451341d100e0103603032450000c0e0701c426101d0640100500c0d9052800301a10030000c48090780d005a0704a40443c02c2e034004035000c9141d8000d100151740d22400c0b410500c410790242c504815040d41c0104410300030030380748c961300102201e600c0c440c1c0d400469a503404400f040541d13a0204001a20510503113080305140c140213011600c482c0251100088205000c119100064851000041c45023580200303141c909484049500300718030451090240010380885040c0c401c1d80401c010755800103031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 393225467 1250 393224217 393224257
    0x30305040c080d0e030f030910180902040801020309010f02090a030212010f063201050f0726210106050313050708120903010515060315030c030d080603060c13030602030705 76
    0x100305115a41c4402c5c02406030b15511114424048201c030642e05003e4003140c0d50100b165401c60310304504041c100c1241c00e00203804220000345000078401003c54100140e103d040c00c07007807a401c5688032001c0e100c60174410003181801d5110020401d045a4044441d00345d000c0600071110b0145c1001c0c40e070f88100520b8018081035440e000c801c02c1c52146840f80d9010a001110a219500c000429401300e003c07039000d03c800c03100b100b0208010852584a08548901091400822011101c05295600c405da00100b07a00311046070004a0303008010460709861070b0765140060180c424800601507030104000d005183c000e02c0309c100082c00c004c00c3c01c00129405141d00502d9400c05401c40c1344030310300c079500344404981c511005a1340414805030091000d0706e1912840d41c41800c40820714600c2c0d0309406070009003040e540d03060003180855034290712004003c3c6000000c03d402c04500505010000b8400d000c070b02c14000e5075415070300030350351700203001650382c1c90f5254252a64000c0c460410f000c1040845 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 393226717 1250 393225467 393225493
    0x216150603030f180b181815030c0a0b07020a0806011e0905190c03060803131511520902040605161b0b0a0f031404030305040c08 57
    0x80300500301d0b4002d56038035001c690040c0003200c0b400f40011032040c030785144001c1800404240d0004040f6803080400b4140c1e01c4800c0c602158a40b41415a1003502c558501c08011198001d0007001011030404c07006003100105c2503001440040700c500500900c15400b04201c011516613010072406032507120100c800c0c941c4d480302801041310030280c251407100c0540c4400123151049001c1c943c022101c1000c5e148011010143c500e0091201948140805440b50000215a0b000740020b200504c02022040d8083d4140004c2260000c0080c4030038003040303801c10482401a0000c190b00c118880c0c0420030301d45020007a03003109402c40410484c603042d42041d0501a00014044004101c00410407041503401c5e0366a6166a08900541c8142e00120750200300b200d0074200c24444940702c052041680c80b10701c16441c1e00f0555141402d0b0014800d860001408007000754025412450620062809116000c40002c1010300070401a000a0625840380301007010403111005e1180500700c1c600071541155001d071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 393227967 1250 393226717 393226721
    0x406020910030203130b0c0d0e0106091503080322020603160908060615070512040f0e1b070809030715030906050c0301030503030712091211100b0a09021615 69
    0xd4502446903914007003420301a4028026603100e14064664607803140001e4840140a880c020103041d620041040310070290701c1d01c0c1c411012486004000010010f0034400342800f1118140341515a00158050400000340b1311030480e5030061032004503c040e80800300c4410040c440d4800002c5d03010700044208003200b000020016085d089698840302803560358046580c9034075007030f600c0503000308001042e120310110b070500400d0198810030484002141078050014290040e0304021070080c00840d042001d43d88003801c4582090413030844118500640501c04130b0752007203240043c140315011500301000d680a112a1000b020480c4078801c2d2000d038150024001e04092008441380c61400000c0759180c2d0881007500d0690f03610000945c50360700ea91205941078a500250700205503242d01080000603840102c2c5900c002d440c2d266090701040d100000340c1040e003680350560301035191185a035000c1d41c41ea9280030455000d8580165100240c105d6200004207918006e0f022105881010507108030070b03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 393229217 1250 393227967 393227977
    0x3070f021f020c060c030d0606020703050d020d0f032403060e0d0207050d020405100f0b04170d02100e0c0a030b15011403010608062205071101142d040602 68
    0x8484041c0722820000c1400d140ca103040c516103005a002100d1811282030100c020003505810b4004c0303d081c580c0d412148002ea48c019086040160001725013002000420021441c00300b41c03900150180c100c501e0001003903040b64800c0082015290f2588800c0b030700c0c6140141140d030100d1a41100843d07200e0401c1c802501c285090130100e0311a0740071a0010510115258080d25801800d4507003414480e02000050306014000341500e882c01d002c00a566004070407040c00a064841c44961030300e281280000c5000f000d4030000f80c0c250044988040b02660100f116500300f9281000041c11000d4040454078001403030703d041e500041f5903d00441440040000c96202d10070100140310503215181c01110031001c80852100301140a0005000040c019215aa401000a819144020200c0c0030307141608030314121804d4501da4827000c9c4078070f00da031201346528180c040340002d0040441c0044902d02c4a00c00805406a0b10703014248243d0300307034002d10310943c3e1a0b4450751900046c205420110025404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 393230467 1250 393229217 393229219
    0x60f230c07060e0d080702061b07170c01030b130c0908030d060905010b071505091203190e0607170a060824010e15060d09060c1d181f030503070f02 65
    0x341d4810b8200c0d1600c0c3c2c0254110a500820281c02c0500903400c0c0035040d0030000c140d09d04088840000c0c40b18100c00c007ca0002490000182045a950b41000a040c4003100110b54100350500d000e0081c0f07034a400130780303407408041e1030400120150b80070012181d540c4540c1014220380400075490f04410300c3d5400000980b91500030070095a41d07254642501881480c80c02050190008060002c0d909580d0245030b200b07040314182e401c4407074161000c4016900884400c2440000c144001e0459a0700f44645a0242181d000510071403c04410241c41c483d084801801b104d0107580c0007134011130341c64000c0d00040c8948030480e024032002c020780352030290345800001c5038a600c407000028064042800030740a40030040000c403c00400406112080c1d02c0103040d100780d5519002900300007201449040c410404640e200080c000080e00c60f0b0414100000c901c5206181e040c03440000c14000c10001504050b19190f40c1050746140840b10a90030f0f91a8405400303804081010401d00001d5444201c034944 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 393231717 1250 393230467 393230477
    0xf03120c050a081e0103030c060603081c15030822051005251a04030e12030d201902070e040803010504060501021f1e021308010e0304060f230c0706 65
    0x7940c0001c10b00182ca000c004c48011801d140d0041001c41e0143c40140441c030f010b4440480c0e042c0d00c03501c980c42c0d9030340124808030142191480e11880b424175442902441c00c1c1c0e401d14124400d02d546c5030203245020b0380c0561080d07400c0000e54104c0d00501480242d00800000d4119038a00100100c0503049411680e4080407003101c13109181907030030401d841d411036140c1c08280d09070b08043e00d01186c684441c3c010012414000c2c18894100c45030740c3e445c40f4001000d402d000071680ca0b2002d28640060300c80714400030107602048207030144441c022600351001e4004503500b0314030303d124090302280307000041c0e4410342d403400c41c8806000c280070802e4000d50517110140c0b820b002c481da0724001281e50380f18218503506000d104042c80b002e5034101d5040340e003e1071598a03000300c00c0b194100320601280d000c0032184010210100c000c000041003030140740c0e00035040070043c50505180000c00303481c00094284080c00c011081c00d5200291810396080b892065002c01c0d01d80d103403030b02200a41d0f030f500c805025040c0419 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 393232967 1250 393231717 393231721
    0xb09010201051f0303050a030e0f0f0709020403032718050405120f030a0e010f0e060f0a23060d06050403020a050705100f14070f0c0f0f0b070f03120c050a08 69
    0xa03040c09140c1039103c038200d40d0107019a18540302101c10f90005803100040540781d1041c3c0407140c000700800300c10301081c40050089165047c8000746004003030b40c0800056030044c0402c0002c681c000007002c2504024074103a001e44e56140d051104640e9081c1c02c68013550002c01d00f14841d15a090780a036200d02d00c03c00450350314050320b01c210300c558003c859510b4540081080000c042c1d1100340c11440c503a0081100208140e41e00d80c4c82d075803e0320038102c0386007080d0380f2020800c48912040202150032a69410041094a121500201c0300d80307180f1101c0c4440d107071507001081560700e42c400b50400ea00d420035420003c40c201450700a4551840b00401e4605214001d4080307140c0c40d082d40260607282c01c1d52507800d02a100c025055a0041c010b500c0e0103641001070000101042500450040c414885c0318422a218100b2000d882400c1c119000200940f0006e4414002e40b8400c804985600360403038000402c070b4001e0300e4202c49850306a095250000e00704440242000d8000d4098150806607440c0c40d0119 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 393234217 1250 393232967 393232981
    0x10b030712050f06011203032c030c01060509060a06050f0f07080a0809010b010504290a0314070e09130807170c010e01151214031204020a140915030c04060b0901020105 74
    0x10384002e0203000c0000801e200390718006400b0740e008101c03038005044003051090709c0043c0500c440041c0380d03c0b900c00382c0002034103d00201082c03007600301801c01110405620b09020000c605200264051501170000010728030540301c0e803600c240d58070b00000d160200c1e61015285413030301c140c0d040b218400f07010416080101d101d5140c180281c140d03590040c2c0d242420300d854000c250403181d006c4259803403943e1102d00b40203030909000e002042203040984002c0b40341c802c88403240221a4000b0100c07401c01040c01d1100f14030369100540142c00c444141d0140e0300040040c24210280c0c41421001070541e40c04030b024281e02c0981034060b051498528008102c150800e198141c283e81c1c1180c0c0a007080c0c3d61403481070100700480171458146c1030050451446920403031403140c2c82c680c010400c8145e4031070038504100c21403500140090140c013100d4200c10540c1d42c5000420610700c00540398402c41002c0002d50205900c040080c44c0b00c071500100180040c0d5070b10041d0b0210b980c00001d8460065090100107644 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 393235467 1250 393234217 393234223
    0x12070c0605090906040507030902040e030c071205030f0904110c0a0b0612060c0f07050f07031e150c2a0204110f0711040b04091208070f050a030905010b030712050f 72
    0x1511001603c040b0701c503914903081100801d00104960145a5228904405a1101d22032140c0c14030114000b0741d0303545a0030040030314110742e0303501a45021604000640010704084103a440c01c200001820f601c4040c1000043d0250010106802e810000401c0344070182100140308040c0c11300410702d210b513a8580c0c40170f014094400417800c1c503039944400045020301c180f04c1d0007046494120002107051248540d103450605045000000640d1320101c424070501c000c10b030310408692620b1010046420565490f0a052403040c2502041d02d9912070500d0300a41c0a20080030000704c4250614900c8c10351000989400b40c07071031400b64015413900c40e861451903600030441c0c1808091000749030501311556a4001c4034082c01e241170f80c002e501d424044100303031150f005201700c9a104d0b1904860090003424020403042000385000d0411803c50044000d20390080c0841c1d1010280385400715180e410703410914050112000c2c0c0310740612a0f04c1000aa00c024501c60722040b038800c1c01616928200342040c030356 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 393236717 1250 393235467 393235477
    0x70803041e21020c0d02151e04080f0307020a2d0815130305070803040c030b01030c030b06010215070509060f0a0c030f050a0e04051e0901231b1b12070c0605 69
    0x900800c5d903160720070240ca0302e011541185030034800007a1500241220883d00c0c0d03444c1503146940c4a1000c202413229080030700c01d4000e0300c480701c0000c501f000826000941510136034441d41c04844c4240001076016401c0080740d1406030104142001d04558807191503980700108010320005e00381400104444145915041c854544c25984840c1001000d413160740850740090401c40b441902d68200000048642d4519030007140140d280c002c203103140d802c12501d40305008001504540005d42e4000a0f0102519000e41080152401649030410b800103c0c465203e00100784422107030100c1e06400d0715a0011990403c07078802d81d104400c81c05c5903403080c2da16015a283c41c60206407201e1503440e1508160b484150302011000c801c007e0750b403140088101c1800306903089002651030720300e1146c44481c0c800c2104005c0044a10002d40d40c5014034111f60403611080c456054040c002540318081b10501e50203400d8600404245c0741c46115084031609a58404e0408031038144404400184e0700b40a0b0050f64 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 393237967 1250 393236717 393236719
    0x50f060109140a15021c0f0e01030e0601230607050705030d050711040c03060306021909050a0e01090b0105090a0f050918100b060f0406051c050c070803041e21020c 72
    0x101409084c803015100100b03403400c00404500c41e00d8103014524268010356260440181c507065000d0b2103494004194040314100319050605200c0c0e031103101ea00000c1d8682c1140c50b4081109022200c0da4080003150b9026804194000c1000c40c3e0f81c0c050050101c1c491044640860407500e00802e03000058401d03014441014058070344098003c55030382040e4002c400106028a40003c405880366100e00c200e801c04681584c8180c2c01c0c540b00803140f508044404040c0200701c038035114041c5000f169107075554050241d043c0301500e550455906900030310503611a23400041c5040b1145440351101e1001040500c28240305401c0c0c000403502d4821114102001400500045d00e10061810498400b40c61111481500305e2020410700c014198030078050310241c80c540e80d4656440400c04000c41102685408083c1c816107400140003259200008603201282c3c05049603403240e4403400e00d03a43d02c000310621a00c00791040603a010811100801c8089840254608600003246100b403c81c0e813000101049 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 393239217 1250 393237967 393237979
    0x1309051006020c06180607060501090b040b010908071a1201270b0d02060918010602011d1203040b1009060e0a0c0908031b030906070c17030a05030604090510050f06010914 75
    0x3018a000030317104441c0446405024103240055554030903084a809900c01d01002e503440030303281d0380c4c0e15190103980c0402c0300920f0b00080160605070529100c00052245143d002c0b07144500c00ca1007400a000c0c0e641c1c080721815001c0d019a0745e212116015240c803680300110702800c01e14141c1000302c0e481480e40318213020b8039035012031034147d00780301e00355200c540c445a0018031090701c010103d5405a10383d000e0061760340089225040d08412010911559048404580001d2a0440400380070000c0c1c075403068200c698168907444041c00303103141c201d49400070f1400c2c50400c031f400b162002c0c030a81c641e03020b0025000204800035002408071a0000c0c00d00070200150010071045840019407461043c001e03020f2004d8a141080903c0064240e0388640011610005101010009100c80c0b40786071480c072441e117024510b05a44050002c03c02d100090400d03200340e03502c0c498402402420410b04082c00e0700d100080113103090244400001940498403540010303100d58020a941000130b40e0305001c0072001e415 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 393240467 1250 393239217 393239227
    0xa080703060b0a1e0608071b050c1c1110110307050102040e06040203041511090409050d0201140c04050d0f06090f0219080a1e1505010315090f02010f051309051006020c06 75
    0x469440d800030780001c0400002310703010a403020500c00103c164074401e100514600c80f49000b03121042c0480403800c00d14210250070305c000f080b6400c50107095280e0848081c000c5040d52001540c018103d840d88084030300c800f0480008010b01540204151071450b81a0b200319074034001084140d2208940040c00c28030601040300e00194183c0220008010035070080d82000c46410201d400c81d03041081c05e40d4030368400010740c440184c0a10403031a0300c00303010215110350700e820304d0380c0c04140c416442002c1c000c0001ea0703076010511107010082942641d126100340500d0413142024810300b130f17900105038071550709810310000c072070709101521040b00d040300701030002c411b40c503110054510341c2d41c000076070300c582500c464000041228801c0101c03280e14800000e119411410300164070400008402e0609241c50242008101040d603245031540c2d0900e0301c12608515441c085400b4012a072400060140016021502c00c8145e001180b040301c090120300350080e6500000c0fa902c80000600603040345003000303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 393241717 1250 393240467 393240479
    0x16051c050a061505030a0819020d08071101020706021b0c010305161b06020f07060b09040f06020a0905040e0102040504052a0d0b091005030d0206090304140a080703060b0a1e 76
    0x202070485020070141da0300c0d180d03413003001c641017540b03074034007192016030005111000d64150349583d40c0000481c801485440703032014002c0d00c031040280c0200c0c1480112050034529031802d40449040caa408801036488504401044e0410348200c9015040c5014024506010754860301c2154450190035500c00382100941130255400e00c80e058050054103421030400010508900003054509010a007031642c402082c01d18600715a40c03104946c0c4142600018000800d034030080d51000c6175041840140d44a00d41034082c0d4606410341e002c941c002c0c4c101240070000440641c06002101c400b40d805114517503581980503201b469110a01591050180990003603c0558028040d00c0030712000c002a808064000268003c0c0100c41c014015400204140b2041c01d09210800c94000c450005000d14107040c1b801d55105d000d1801035200c0c0303050011030003c0355134810a01000038103a200c02e8441d8162a4104940600901000d00780941e405101c002407040502d15108485109800040403003030400c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 393242967 1250 393241717 393241721
    0x20d060608190b0c1e03010803071a060609011214013c12080705010501031b080d20070512100b0a1a07170c1b0d0302100c090816051c050a06 62
    0xa07017001c1250301044c08100341401c6440083d03018003098001980c688213940f07000c81d17908078908c11030070590100b003082c4092600c6520507915540302c02d0819150994828100400411810326042040c070074000000803260113890124081c3c0b0a443c0e481c3e50ba1410801000700304804102c28022200e02c0800204040050700412403901485101e402d85403080948800d425140700703030015100c80c460011100501003041403401e00404451016100202041201810080212030000f03a1400b004914a03800102489811f01415000708090005c0a8103048103503503108650b801d4030185c3c83c10718120013a107021401c1c8021103200380400b5555210071481e55613a90080034003210a42c0c0307000c02920b9030706035800c080c040e0304401030014585901000001c5010b000098643c90082d0107400004c00440e50100c0c0c49c1b5a03013007400c040464050a840070071a0a0030607640884d017039000c0e0300f19410038044528480c0d4200c0b10f044545401e580342842e031801000319102e4005160341d001c4030300c2200040c159 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 393244217 1250 393242967 393242977
    0x1030221090a0b0f0106091403030a2a03110d0804050717030d02070303140609070e060c030903030715060f0b04140d0510020d0f0504020d0f0f020d060608190b0c 71
    0x1071015200341d5192076580950302c5100b40c50001d40c500d2000014000d80754041b0b16440240164410b032840341d1040e00209880b072092021010400110160f9501e52201051841101c0c810b80032024000000c18140140300071450020314881d03000c0c3e01c81040e00b4a00c40c011450080390058003401e4030b94602030b03900f0350500d04022456264082804501600b80542c03001d8070001e400303a00c000c5003900b413003e00b0803102c2a00400992003031481009000206900a80d440c50889050b500a907482d050600c1d03c5c3d1443c0900100e281d89844002141010040c0c0a850109220180081480380984030180e01d20561898058103113418801e006c02c000780c1240d1201d1a0503841c016211b40d441240a880c0c00d41407150300d18607698003c0c0c0003e0304810f84606803068414841d003801080000b800c065000030400314000c2ca018042c04010200c410610440c01c5055014540c010700c4440440c65900d001c0c0081c0045100355a014020f008401c15000c0e030701c03200b620405a0186500c1c005a81c3d09000c80000d07040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 393245467 1250 393244217 393244231
    0x190f0b03070309120c030809010621030e0901090b120a0f120e030d1805060c1005190207060b01080f0f0103060c0e030307050304080705030d050f090d200f01030221 72
    0x781e0f4074a01c0403510b0b4200f282100884da64981d2110211070802901c40c03480585524541da151100401084051182c40b8000e003843c00f044003d4490a418100c42100042d800c160380800101b000044260466206a640e801b0a0356044290070707000550a4892006507400ba0541c03041c40075a80002d00c4604600c80750b035141e405e01349141828100804e142c040841c40da034001c60300380380c0440c1c01c202c404807030700b001402d04854240c917100d030802c882c40d115051001030401068a940c0416000803940c0d800c41303896006a02d0071900c5580702e04008016200a2005a0115101c0008030b0240b66044041e9407140b900110919200d900e580d0b2560002c11030340c4209010001a0844501c140d60b040c0010804140200011500c5a040900e90b40c18950300e58000343c401c3c0c3c01412494440341c1c1001c240c2d0000e00500c91819140e24121011541c815031880d0024001c55561502242c2804c8c80001820f0343c2c6c00c11b82d501d104d002ca04000540407481940181d07084c9040c5410580700d03860207410354651043c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 393246717 1250 393245467 393245471
    0x30f0307060f140703050718140909011d01140106170609070905030307260313120c060906020a02120405150309010f090b150306070518040605030f0705190f0b030703 73
    0x10310011000c50642044d81d40c400025102e8050002880c0c1c843d0805144441c08001901300514003040c1810100541ca145c9005403c0c02000410900007035210784540c0c889021684400343d10905014001d1030b07540c4543c4944101e100003c940c1910900c003000c00c40580d41d00b01c4903a40c0341c903810440c003120020b0145040106051021072140c609102400c0c0203841000c010003410300b0800c2a80c0300e00407000c23018145840038001c001d00000d1480b1118062500a04c0d0038401c450140c1c001c030b48188a002018009508109507282000616030041507507041030743c00c0d602c2040d07440c4a0f461462203544102503011000440111845202400554111000034000039001ca07080c0001401d03502072490a49001c1c448408001c036002c071207045070300300c0700c0118050600c0d0720704190b01428074003e0402101c410003c0c803c00e060309071103981c0310802422001301111001034001500941c1c80245006d114082c001807030516a500410441e2801603800c000e00c4aa0b101d41844c081348e030160801001307002015 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 393247967 1250 393246717 393246731
    0xe060322082209090807030c05160303080106030c090305100e0c091503121216180807140a030f0204022203030503010e070f170c0c1504050c030f0307060f 68
    0x140584014a0881824a580040400c0400d40a010703014242c0c031008000f420000c0c0600021415400c5424282c7c7c5420b000c031601c3c255042552910b0001d0074000303000f11940b10040181508011a6412590b1695091180000011080701e840e41c070391000405075884881e80c03001c8481950801001c0c640e0940450754a0740d007401c0045c00051381610700550000da048003851040c1001d101e03255500520320b0b111442c00c00c03800b140e8a03035420700030030100c040590078004441d503600c00c8455a6036150443c6c40440c2203915000c24030384500c0c4500c40d1800d00307007850440401d00e04050041c50101e98000e100b981c0414000d0f028040654424900e2091200c00020070361550450414054041d50081c1e8070b5a0300d07981800e4150b240e404c4094001400c0c40b0f20811011078035035001c1c042800f5005d01124014903900d40c0c20060040b8020603048007c14001c80301d0b9816030440003c0018460f40c000c800b11034410f81e000c028152550444203e10131f040c2c10400c5903001145070703508075000d0250582c90001d07040e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 393249217 1250 393247967 393247973
    0x71a0c01050c040302040b0312092214010f170a0b0a0b0613050405100503030a0c0303150905100f0b0d0c021c03140109050c12063d0e060322 62
    0x140d07011101940ca40b07401040602c19410300d44030b06252004e00394002d184d0007900c5243c000300f50040c0d014840c841c1075500a00070b0700781012811401c40482e01e11003407003103030424503007100f45035000d01503002c00d4502c0300b10008054400c0e10042000a00e104050710000d41c041c0c45030002181c005020302d11003034a4000c244d1190b11090b004002c940e6055043e44040c50500c000c010a4805c060410315902044d00400e0021390b401208076031003404142480c0181480034074003500500b0162032a929404c1700c00c640040d4840c015001607215100c40058a82001d03140c0217418094403a0b4001c07404022024800f8019a0100741c5c004501c0810a00481e103a078000c5120032005503849086050001e41c4490704102401e042005c400d000d003000000501062a00700c40c1a05607000354200490401803240c00301c1c609481e1401c0500880301d0880b01d02846e03840803001d84030301d03d81c03403a946600c10b030b80c02440140061181081c00c40e0310340c00911484c6180ca8440015041070150100307040080c01240302c031000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 393250467 1250 393249217 393249221
    0x11120604051c0804020f0118090501090c11010c0905010813060f02121305030a050a1101020304030c150506090c0912071412010207020306060d170a03090c080a0302071a0c01 76
    0x49144290001d058096107841001e00c03041da807051110034422550241300044e600c2e161148030200c420320b85403146103030407074100050304181d60002c04410300d004000b00e043d84080e00009964080c276203503c414007a181c04241c0c01c0780c1d0380800326400074a20200c14042503106512042e0444d0a4550000c0600201c1d00e0300d40807205e0000c605840c0d554000b600340403203600c8070305107a4480040d03400c0c0c0110300400e0b01c602c4c3d241d11070702d04081e041020000b80d00e001c840c064a80c1001c3c1c44001c01c02107440b0316142c80e026140554850007540c28044501040d81d03001000c1c09520305c202400703400d10b8440e880c1c4112605c00703a04001000c9503c101d18101c40c072049102004071100514400e400c10440300301c3c0d9418400780c2a4000100502d6900401c83c44025071000901150041c0003940d2805060740181003101210725503a02681d6030b204001850005c59605420011a00e4013400c60018940c0d581c031039043c1d4458000d4001409a046044104201380b4903601010040c0c05114126180091150701642 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 393251717 1250 393250467 393250471
    0x902011205070203070b01211704080304290f2502090a0b01081b0f030a0b09040305030403080f040f020904110a030f05160b1b07050a0306050901051b07111206 70
    0x44c1d00100388602485022880e043c010030940034204801c100320031800d9801510244043e00c00400360780200c20b040895000c071401080000166522607465003900d000340d0003000908602c02d0101d903d0210070751500411a01c0052680420b94500320000d4100300000700c0710308001455080e00c1c0480c6c4003507141c01e60b00034030941d0502000603030324031075000140124101409082d0180f05603a00c0041110b900001c031075400825400081d2a5a103506030b41029201c42c1450b01d8001c03000c1d40601c8101034000e0051405184a0741752410160340b030028070580448111006002c0d8042003c20300c01606092a43c01d400134094451858140380c02408205d0818956100b11600b0090806c50401d022090040c0300758150352604404080f80f901044800381e01941030b001d040d181d44100203c9240f0020450180141806043c0059003a41c034140140101800c85078007a60354204000030742069046103024400d91100e0500307900f04041390726144c40040d0034106ea9270b081807140c0507042054001700441c40c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 393252967 1250 393251717 393251731
    0x20d0c020f0a0b0a09060201022706040302030d09060207121a04030c0c14040510061e02071d1f03080a03020c1e0303040c140d0f050c091609080604020901090902011205 74
    0x10f0390724065134074002c1c40703445c0940c001c0e4216441030203020b100120088240e101003101c0c3ca00300c6624401d00002030344601c11640001d60522582c9911030440781c10800720401c1340c04a8003542c1841d40d40308104004494450402070002440c1c2b01500d038000c10f04000b03150464000e24168047c00910b40d00d0407200c900030340250301d102e200f2940d500042d107440e0244641c40007409607419000d0b80391a00c05171290a10000005c2194926080d28010902c200a200d005010301c8418410584445004600e12340c0184e829901a03480d0862a40c9404036414034041140d601400c580e2420110100490003500042050100d5010f010700403810031650705442c011204d100b002443e500d0501d440c10302080c032020340c4041c038840c00c01485c406040e03039120442141c0035040240302242008078035009040c00d0540041661220703c1005100c44810342203010501101c10f03465004203562100d9401c2e40d40d5200701e600960105880005000300c0c0c202b0303009081580d00c10706100320710301d0300344180324243d9904131426 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 393254217 1250 393252967 393252989
    0x3080a051803161503060b03150d05010c1e0f0f030e03040e040b070306120b0610110d020708060a1a0f01020c09040b04050c01050a020a061a030d05040f08060106020d0c020f0a 77
    0x24007002010080f1355044250a08041003541d2915aa00e02c441c04001c181c0c00801c14070141e8148030782c40d500c02c040c10442d40074000f0000e04070801809041401c540c1c0c068501c20113800d0040858034041c030b190810800c4aa106c41c0c032104c0300000220302404581d2000c103641c0c00203100001d151032041804a010b01c0c810302d410841841c04410060442c3d25035400007010000b80d44641012942d170ba00c02c107030080010788a860070400000802d032003146d050304480f00b031449034000940550303502150700d4003910312070402d460b02a2290071865003038552004a0982c1002d40c8080d100b0301d13103018a04151701c800c06005680002001d0b100090044004850507105510b012080000f0000280724000ca125005d007072046c1086003044009566040e0240000e106030350303c1c0e0f441207040480c07041000c07501400908079255590503000c0140560094031401d8801c034070200340402c0001002c10700c1416640d25500a00e00007002090864682d805000b060740c1044480600f01e410703880d0311014001602d15040c032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 393255467 1250 393254217 393254219
    0x20312180a0507090c05190f090f061d030606010215061503010611010c0f050304080913110702041404020630132a090905120c0d11030403080a05180316 67
    0x2400c0c217840300c4560726820031508000200c2d200b43e0804000c1d100740c104d450040b0803100c00340403d40d0803143c26001168598403689000030981d0307000c0200300c046c010500b0384040090602e401e00d6a2031301c0c140e981d1409030300110825040e1403e0814615440f14000384461044901d03c0840076040c0d10a8215000140f500041a0035040090203001d0000366a450440380d00300030001c2c020114000500010704802e0005a025044d40da000c200c080d40b105c00c0c5000308120209038039011030603880b045080f405141492a00280740c0340c0060780a106903000341010b4030b08a1070300b40d14280ca5110f950701d01c903e03880340039050303040e03031401103269100c2c42041104401d00c8016061071f007200d150f44448413050041c2081203002e010102925441154101d040110300085030b071402c10304004014082c810620380100e951001d85400081d120659000d03500c44040d045284852591a48114013001d84076100401620300010b200704003d00e01d50004400300650650340303c00090070400081d070203641d001c0c40700700 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 393256717 1250 393255467 393255479
    0x61b010c0206090708030f07060b09150f06040e012d0e07031103060f060a050d111e070b04020603040f151a010903260f0c030d1b020312180a0507 64
    0x100180d04012200000c040d200c0c174006003940d5034411000800342ca410040b400c00200304154108000091004110b8030951402e8400a041c2404c5118240c0c0703d2050f00390700207064108401140c05840c0003c115040326070800c007a034144a0401c50502c00c00c0c0090402034103a030160100d11030042d1034209107099160030080002000d07140c0141c42c04110300000c0050001da07550b101442075200c0750550340c0b140c48003403101c0c0a4500d4012105041e0005090020211142490f10000d00b1344901c45000440345d191031954010030b5010340e5000810240c583c001081c05468144003540d070161040420307800c040ba0315680c64540c00151034914040d1038070780200504500411407840754091080c07030035105651860300c0e0201990014120000d800074440340b2070341d54280e62401c40302044c5c080c030001e40e03484003100c01c403a903070323601c40070140c800146003030403255404108290400c141a60b41c0d00843c03c0003948003a06070418030140240e60341c5071500200658100007403041410b5140600c0140018030f18100d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 393257967 1250 393256717 393256723
    0xc0f050303041709011b02031011070c15050d0911120312250309060209040c05120604060f090b0d1b06090e06060f0d02090411030105040b0f0907030b061b010c02 71
    0x2e0f10005003031001c2c00b001c4216603000004954416055240030b0b40c1e402240086420044c0a985442d0030078100031052064000900041908038450207850140d2039a62401d000d501d40c031646288002b81d020080300390342c10000c0d04044001c5024080f1140c0310080c50703000070350800285404d811281c00100340403103103155a8a40e26070141c2000c8000c8024080e0391036001250007a070690006041d542c1078250140521030b8181e0346a2034016204000c2c0b0b2420304809005900704214204030030340e8410000b0a14146801042d080b5401d0100c0d1840c1e10b418216a03070003500b0221249034001c64404241404205601c0e02d2141142c060542c81c1c90f241d050800c0100540d00399000000001d403200140200c81c0c540200b12101000e4001d000c588403448000303c500139200b48012a40d0187c20b0202503444201040010750403076100b264100100082107049c8800106208100c1d40c0c0a002070740005d045038000d40058112200042001b4030b0130b1000c00301c2d0144402405a000e08580d51000074180e890b03010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 393259217 1250 393257967 393257993
    0x270109050f090604080306040f1404030e10050c0303010501110313032102010209151605100606080a0b01021c0e060301090f111303020f121507030b0f0307050d030c0f05030304 77
    0x140b014120a14007070316005410f01c0301038082c501075a95001160707e80511540304909140b07001841140ca410642002080c031007000000c14440c103001604511458020b00032035487c0460036002c0d5045a01e0301c001911a012070390401b65060104000300052070400140450186115820300d144154003181ca50b4104c09050210b40256841000346036a1075075900002c0c3d014a01020901c5c0c1d41701042d0120030b48681ea03400300180148102101070052903050b0b0054801e4510940d03803002180c0e0790741c1a60040e5440400e425001d81c000303240d12040d801e5662629102e2121504200480c0e0171a0360110700070307500c240e0107000b03515600c0d6802124000c4600404281b40031504020382081031648101e405100a448001e11580b040d9010041603241c5880c802c401c00240c00a44184405d0343c0c40d580c240490031503100000070b1800d04c032007501e03140c514441c0c03016201c0074000300303903541c00c1100b80002d600407184c0179000e01c040304c0c21500015115202e28608036108002440d201d06203031824002d10309407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 393260467 1250 393259217 393259231
    0x506070f03060333061409040f02031f0f05040b0601120b0a030f0506070527040603060c020a02030c03070f0e0a022803050c0f09040c110303090706110a0c05270109050f 74
    0xd2000400c46c40300040e15426008500f1903d407200754880703107410800c240a40c40000e40600808a00c840d407400d01c3c003205c000840c4910801d10620030003420a41c02c4074001c49006000c40d0f02030340481c2c0795522400541454201646000503403610f1140010000d0406034821100120248500701c1004010300800380c00005a040c200d05015100300ea00c00105805000203c10340303031031036510310b4580d00c035040303100119000a0200610401c1400082d190701d50000c042e8024400d100d8401d21509000580c03d04940074800c0d0b0400090412258240b180d0002d030640b00300039020300c0781c01d808081030f40a9483d8a4403040c040c034884440700754040c05545c0c0c010041c5403511410320a840c500000c3d0000c031044017404450000b9180103503030007501c3c08111504002550300c03003c4208600700600080c81401e0b02c0300c3d911424001c0d0000b80c1101e86c3d540032007070000c2c05042400700820584c18580c141c48030603049004850340e2083d101c221900c1c5103009074081000d0301c0e112020700c10701161300e850b00742d00024 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 393261717 1250 393260467 393260471
    0x50717130201031b0903020d030e15040519051f020a080d09050601060807020a0803041a0a0221160309330507020c030718060b04090209100207030506070f03060333 72
    0x842c0880140c46617003148406402810354143d0b044c10144950f0590209540c01451103a842d000440d41030583c0d04280207003402070494140142680c44c1d88070000d0100e0b203004001207250420324614550446000c002c00d02507110340c45100d40000c04040191601640c281c07400100c040c65420200c4c070304441030340a88207020004003800341c15903002c01c00010043e04210900e03901d481d50300c0c10310240f600700061404002c04240038010340368042d800410303d2038001c2010000780d9000742401c288204081d038542c200401250020300d000c9000307400084025000c1e1181d00003008a071441d1540100080e00d0100d5014003410551258416620801d601300e031440c0b00030a211103142c004650f4035a402d0058110f40340e40f0800381c88508410340c1140000e880c0820840351034941d1360b085680a0b4102001d04d510820444113081c081e00e20008499080b6504400102a252240c400544010502c1e07982182055254200400407940c5600c510321603180d00c03201c214001d061410705800b5860340c0074413490aa4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 393262967 1250 393261717 393261761
    0x13050d0f2102030703050f0903060a060801050109020412020411040305030a02070312050309030304060f0e0f0106030c05011103030103080d0216050c03150907050415050904030914040b0109030605071713020103 92
    0x40d500000f500d50f40c0d0303030500300079658560114447e03009018114410346d2500c81c440c10840400c1d0300760854811a44050000c0c016643c07070f104044140d02850265940490000075a074001d4a070580140180240c8440c3c41454240c813502c6540c2540e12203a00540560310a4000304108542c80038610705000c040e190550941c100344880c1a1280f0010704040c140f107840f8404502c8140c0a82d0206480c880710008032a6101d12500c0304601030b00a40c44160b030701142c19100002c9550050350070404120944018521f50b0b230071603940c443c141e005041c007d940d00d90300b401911004841400da0f80205800b45c0002c00e181c41c0c08400f01458410800d14420003550618148050300c080050b00005940c0201c401094a002000c4400c0c6068003952040d940420383d030b024002450341051000c01660108001c100141e1403001c241b205690301008220700261042404002040b040d5100a4004200303150044008144e00c02500c100314080d12046000c54151a04008640c1c04d44540b027020421000454118 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 393264217 1250 393262967 393263033
    0x20c010c08310609170c15010e09030a050705010b0901090e101a0d030e060a080f22080f1903020405030c19060807020f061302040b0d051213050d0f 65
    0x24006102008058a8640081504012200c09000150012050724a40b206d1040b40703800c1e512840c43c07a010080034102000840c007842c0103502c8603c9000150000c0d480e16a0500088031340741d10403442500d01c0d559582c00018199141102d0358020460254007090f00107001d0011420101d110820007015486c2004180c400c002610404800600450b02a05146000e00b0169540460801000d603c180005001a81142c2107000c0d140200010f4007094982da64000d080d8540069020041480c4000d00f4107800000301d02000800d45071a00403841130030f160f9000d884014041c1c0341c440c40e40100350082418072140c10100400d0320000002c44012062202c000c40c0c40010034242e02941c410000b40200040d6868000c1101c00b0321101c0c00c0b41120f040b4500141c9840702c0d146445402c07032045060800440c01880c10011501c4241d4016000e808014801e5514917980d03031060026012551150600242030750b00c2c0d0f000b41d04014058840b00340c19103864030b4a4460010088110849102c650180b0125 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 393265467 1250 393264217 393264301
    0x20a12021e0901121b03050106080405060a0b061c060503100b091801020f0a08070f030c05030a15081006050913031d03070f030f120302090f13020c010c08 68
    0x31040c1c1500002d581d400040d0049030a40e40d0840d410128900f0441102c0883e020070906040301c50403a0b80400407641c8961080351320900988025000364444070103d920300d030081c2e01544080c40c00400e00c5190190802c1c126103880c10403000505e215603214410089410180145220420101400c11002070004002000c000d0041d117010b444441c0c0781005010658254100d48158110034256510389080790002008282e0840e145000030b5180482480c92500900480c020445581c0310941185d4a40152070003d1003412000c00e6000840c205c0080e0141b41809100300780582c1e4070010584a0070704041c00590103001e0044a03000141c1c00001020a40c00f0401c1c1e03819a000c24020461a102100000d15048483c0c000c042c00020b0301e038002007000242d88004d00c0e000e01c560540c0358901813061040e81240100c10b052600300700c0e06040010507143c0411032046192194500604000c941c0c1c00181c00c4542c0c586820011513852000e1000c869000300c1c075070800800645450f254031484425082c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 393266717 1250 393265467 393265507
    0x120f160503061801150f020c0d060b030a0b100e01080d0806091321020d020105060a060507020a0b030705041805012105150f07030b121905030c0106030303020a1202 72
    0x4100000880428143c0c3d8070f0003400301d412100181d00034000e507100c2c550300000c1541d16030700c1c0d03003c24244402c103500303035001103484014050014000e1000a100d5200c0d04054000d4240c0079916018404e800c1e1700082404840d10f01a0100900c0c01700801c1c1048800c50301c0c0001a0004581c3c0ea021401d010043d90303002c100507501500c01d540240c1961103421940000c0003900300020320312240d0002003007041402d00842103c0211070380c2107410002d44000140d00701c0300151151600607118020501c4680e0041c0300500640d0f20260451070000da0710701629810307400036104080040c60000c0d04110240701046051003800e482c2d207003000507524010f100c8120009880802020440c140e44920a0090038050405800c40742d00b0403c02a1810001509540c0421101d65001c81e207403081c00140c03410142c40d5130210489400040a21200b4001d0024100803503d1080b01c0d54482044150f583c0032007800381070700962107034402680300c00102d03d003c1c0c601803030441c018031064030620418a140814080e003074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 393267967 1250 393266717 393266761
    0x80c240417040810021c1404060c05070803041a060105030106020c09040f020915120f07030828020303060103050f060105090d0602040504090311010b030123070201060e040503120f 79
    0x12100c503410110406480c081c650150641340200000007184000c260010002000210b00040244c811520326404444c1d801c01c0d442c4429035680b00040000c2c4139640446016001030600e80d00305081d070343d40d88000f40e000316011903007806102c000f80c2d41042c041c0007082e000f003030034200035040d58180a070095480c542080c0c424400c0a0340c8010400740300c0c4640c02109500e4001d0700049413442c0400b0809002d07643c40704542d0084003146044004c4c400e000c11408410030705200500110b40c0b8503241c0b18a140c20508180e1000301c0c0c002d0942d00000d141c20b100c14806403a6401071500c0f454000700260450764018400d594401d4002c00300300c1d85a03400000c982500c0c100700d03441d69040109017404d400134002d5800003500725203031070462800c0c03541103030a03000c802410300002c1c44001e00c1c0205150a880c09600d03d070106000320250b0304100e918803a07103a03502204601c00090b00e9561844512185002a101621309410009a2007040c1c1d0a495030554800041e48860b85d290030b008420614501c1e01e09689 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 393269217 1250 393267967 393267983
    0x603060d0624060e0102120f300f0108010c050a08042909010917070c2706140108060a210c09110c06070918090816080c2404 55
    0x61400b085031002030600070424805404040380c403a80c1c050400807041c80e4442c0584602c0e040507945c1d4152800f180c40039103d0081080c2002418044100007500f5051440350b400c1c84450005841d06a40b5800c0e44100a86c0c6440405549031281d440d0846200c01c40311410007004010120a460300300c0c2c840b513000341d0b0002c80c0b0110410090b0460114419540164900086500a22465030015045000458040d00e25003c504198101c2c42071940308010004150000500e810050441d1010010090301d06c50300905058001012510003210001c0d000b084420103010001c5441c0c0d40d00c00d0ba15940300c6000d03201d1621007402c0203a1600030040308405400c0301c1d410000d012081101082d091001880181010301803c00c45206c120010b070132035568039a8607c5000e0000380502d118040304800c032841400c607001d9046d01c215000707001d040c0d0450261110a0104039900341031151042524031940101616615003411004040c1081d031a150b0340e501d41515030741d100020440525542d60000c1c0d100c140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 393270467 1250 393269217 393269231
    0x71209050d120b040e06221203020901090906030501020d0e06060906040b130e060a053106060b0a110d0c240b0a0609080106060f021e0304120f02040b0603060d06 71
    0x18100c0601443c000a41e005424050501c2090a002914601a0001020300d0010305680311804950300068203019012103143e40003030a940780a6130080c200c290042c903210400b9500d6490f00e90039281c4179403080707405170360024041801d04464071900c04c14004c488081c0c801802c2040002e544100040e01e0548215999162518540d44510301d400d2024a10031084c80760901844c445911828202e680c0049107080600254105180d186c803840164440d17408011550700d50104480100c504a00403102150b0301d10020030550030756070190803c680c0b10303521a50703a8040e8000490420b5294111074050048007414400012101c246081c2c0000750480410b21040d807098150016102044100381c002081da9070118000d03510000001c1510300c214002d2098039a500c5046640c070280c82805001130b00a00400d80c442c98941903030100452400781200c2c00c0540720901c50503444d0240c00c0845c1d0059509a002e011402e06001c0c044900d002122454107515001001c10910b9000860013010b89994102c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 393271717 1250 393270467 393270497
    0x24031b0108161205151203040e0901020405010212030703060e010902090f0a05060a0c020d020a06110714010e12010605040c030e070f030812071103031801051b18040b040c08071209050d 81
    0x1700d1171000b404000d010350710081055200c9501caa011b030090040b04002c4c1800640300d14814000c0300c0440308181d0080c5440150f1080c017104580000e8100410152140c80000d004580100c2d2580a440c2c1540300503614183c100c100110340d0201400c182c060000d2100402940d0380704400d03181425503d09210082240610004451590361040258420314980010070401e602641880544940208a500468803000b0031a03604107043c40c0203001990810142c0c1c0541808142007038816140c034004030700e150f180c60008051340c004550310400259202c880208e40102000300600404008040c05190703411500c9446240c8105121201c507000604041a950b6209601e412021540d2100781e980b00c1c00c0c0108500315000c1c101a14480d0ba43c00c007004500e10208150541010710113103548a0315208500b18480c0850302c4d40b441003a841a5611548091911113000b801007440b460b0381c403840103180c4079201400c83d0003c0c060002d040c600e8501c0280008000141000e100303102418a4541e003403a80c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 393272967 1250 393271717 393271741
    0xf061012020f0604060c031b150c0507050715121109062d03010e18100e150a0c090b07030504030206181306060f050a0824031b0108161205 61
    0xb03009030082d030002070010380c01c2d61022940b03c045210b940c4001d002c800034454442030034101c98000d0140d0700c90210426500b009540315202c1c8400c181803150034094a5201c440c205590740c1d110200c00c0c0e41121352000000c1d40601c01c1c0c001c4105c00d103400c03c06150382c00840040c9000b414400c0d0300803080003da00d07100b03481140c200110550072050b600f0840a21401080030b6400030300c105c0c8141c0e80c52402180003103e4104801c48810070000c01400c05a4a01c0350840c040e001014000c881401707007810b1170340000f0241007042e104480c0424007103000316000000034100c002c1e80c0c2c0700401180d82803000d000001da121048404694040b103010342c81c0c9503000b20065103945005d407160352080c2118080c0401950305d4100b9000c0f00c80b0f40d200c5040f000903a9405880b10f00c1030124000004003030702c00040c1804003503d26900b031483d11200c525070301a5400c002c24580542070540e2000e005011450354415a4000c071100c0d8003d8150400001c0716192550280498000d0b0380081d810f1501c42001030001c030060 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 393274217 1250 393272967 393272989
    0xf080f0705060705090f0108010501020c0d06110705060f0a0b010203030714040f0315050c030105010c0816052a030c180a09080f040302090a140103080c0c060406110f06101202 77
    0x350742e401e0820010141c8640e0281007034030f011300800d04411085601070a600f90481d20103070050600482d81a041140020081c0c0d0200c4081e5503d007959000c1030100009411450300c01d20080c00c15090040c0621600300e001844800d50b6810003c000740c2036680442901e421041ba8201091001d407951000e407042e000e0741e0454085038448440000a004059034011551000c1c10020012621403408410a61100340100fa002c101900c1c000300c0003628400041552402c155411151070a81d0b07601c1c00d00701030b03d064400b503442810740014401360307042c0d07a201450410b0480003080c14044a401040740c02402c50002000e0380940380000301d01580c0c41c1c00241d482984412600ea0340c003280c64103444140c00c9030100343c2c01000c55000281006010f0f128004020060000c0f007a8143c0c0381d07a40d41c0065621148030103080317000f9441e02c1d900a44916018002510345a01c5d4501400700010701140b130503c0e41e014a25156100700c06000b0301c01d41102600b801e407414240c004460040e00c4c0003249403c031207 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 393275467 1250 393274217 393274223
    0x140703050a030503010603050906060604050f18010b0c0f190327060206012607030f080403080d0605040c1d120a02030a060e010e0f0d12060b030a270f080f07 69
    0x44415030020190303c800114140c5026032000c2041d500c40381c0c3e0156440e041143c0080d0028010001444a0701e0002090003d20400410320400e0003403500c004802031100380d120440410020130400303003955050203100128040302004141d105800e0081c1b0b040e100d5100000342c144251843c2142d800d00c616282c10104c0c042150340000e00903600c00b0002e50b200380900c140c01d841c803848290340d5440c071014455160501c1640000f080d0490850715240c2107000d40c1c200032a0100c0d0200320002c0020380d010702030040c00c1c40004001990503c0c0c40240000d4580e0300c0f0801c2d04001747c005000000c201c0815030001c6001c000daa013a0403a05111910034900b590303402001e5030511416540404200ca40e0300b012102002d518000e00c04400d0a650a680d02d40403010050529080f10040d6150248074030544000941e1345540421191b5a4040c1610958000c0c2c6054000c25207901c446030b0b902a050803002c44810f48200229051000360311422030390ba031040c500500345000001c134481e8450b43d0000303403142150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 393276717 1250 393275467 393275473
    0xb03100915260d02070e011a0c100f050606210402010201290a0605040609060509030c0402120f060603241f0c0c050306072001110f040302040b030102030c0714070305 73
    0xe210265440b42150720800c1500510410700244241c03840451030200700d8100f00c3d2100b4007a420700803c5901819918030300d4101d55404d1000d050410010440d904000300d054000044101442422005440000744a10b0244d201001002554081c0d003200442c03080d5201c00e0785005880c5c9100403405024041c103003040c10800e94056000001d4100d038140ca081c101111583d1045075940410340301c0c1e00452144001084034102c08001c0d99004000804101030014191250715918400080407604002d01c00c03500008880e041088080d132802c0f0309030304910110307099819807908005002519502c0f00349900316109a11402000703441d1500a8404107002050002c460481c908004144504040f0151080700320014001240d042c0448c0943c003412440e0355400085005081c0ea0741d5200d1a1040110950744e103503940707582c00d14a100500212a0a03a4845595920b0b50041106075540d02c1d08551217070f481041801a1045041c00b1580902c0d403210040b1520b10a40c0700c03890414205a00c00b4040f40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 393277967 1250 393276717 393276749
    0xf0203010e011a1801060c0f0c0e010b0316020c031216022e03090f0201080c07052e0b03061f0308040605031803030f1b0d020d0b01090b03100915 64
    0xc030202e400b0b040b03030302c02da8042e8000d1301c00101c4c40307401c40401c0c0f0a410101e002c244003000866405240c11001c10b00416119800594604031010003850983c131600c6464404410300180c800c28140610b50300103d1310040c15801d81e528002074a0b40041d0300300310403036a070000701d00e4040340c94220f59190a0b07030010580f00109010401141c01d00200680c0a49011442203035092801c3c060300c116140ca681041903198050296401560b10b068081d088007a00c440901081000520404c002c14140c1c3c2d0b42e042c5071403e162500b2008854001142c10044400d0500c89802230680f0000340059000500128204040d075500170906200c816640000c0d1080800007000f00b2019003102c02580110b048240c0001401407134017405899010507140011824410700101d1061111000b02040e2102100308181c80e15140e040350000300d0b40b00841c070040702512814024440c1d82c015040f2801440311420680c9546440d045000c503002160040c1c0300104e6641c00301e0306029001900440141100c945c880d0645 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 393279217 1250 393277967 393277991
    0x6050c07051203070b070f0e0607030504031407091805150a0204030c090212070504080307140f16050f01030e07060807030b120102070606140a090209060c01060605031b04050d0f0203010e01 83
    0x907840440169074065151012541c0d0171722401f40068841015904c41c84103031043c000b04046688004c7d030540400030700f844040b010600503450000040201402407841e2403400b03c0c9041581c4101d400c2291035056400c0c80404908042000013110320240d0b98190259a0404c048000380600d40000c4c00e0301308064800300d0405040e90041418201d200c018a01e0365440600448292080c2c1c000c0d02000d4005100c184005640d410003c43c4240c0104160b43d01510307000e518501d420700f112050f040c2542810b408000c641406402901031500a00c0d080c0920b0300b110026a83e2000c2c07922030081000211400564054481c0e44110841c0800402d202400ca11800c1183d000c0e42101c50180c40a40c902880003840c0c61140c09041c0d82941c0c080d1028003120718000c818030003074102103051742e00100204a0003c00030020302ca03040c098205915810744905060340f084403500c18005074241503da0800c010b04c016500c0110424105601c116913800d40c40c81480464090302d55041c1090003582010f0304840b003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 393280467 1250 393279217 393279223
    0x10b12090721030207080309060a03020705100f290901170f06010e180d0e04020706021c060e1012141501090501050f06130302061e0403060915140106050c070512 71
    0x2c2501a074200d0301026160b0003220703100c1c4515600039a110900b0004201e80074043d801a0948600900a039080c12000001c0c940c20782d401d0000c0c6800392030755180103d00024540000780c200c1c2045a01614503214810007040e040101070150302400c07000c9082c000d103e120f04101c0c019010794010241ca02950751030200c20300c0404195850480d80c1d111070f100760952071001a1011840e9000c0e5550440c040042c0148002584030a2040e100e96030200000c4e40b9900445103c4180b030308060000082e85807400d400442c40380d8028045c96914a000300007080f500e001030f143c0e0110140c000c1804c442c00346c0c2c85108140391000c1024401240300c0503070000203074800c203980b005040392025248141561088401c00c00244600e0f2404141c4041c20700007800982000300192180541149100c00c0e0392054141040503500180d000701c3e11503480c0c1040c1000c0040c0d2a4444240e00503000c4c05000060454861002614050052104002020402c0c0c07a07420420059880100f101504a100a05000d002c80351 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 393281717 1250 393280467 393280529
    0x90507052704080306120109050d020c0901031a0703021207030603052e180b1f05040e03030a1e2f0c071404060b0a030504120206010b120907 62
    0x486903115032034015809010982994120341c00e050040074642d40e5680300452600041d002036000524104154544071003446107007030f018002c4d401029101a40c94000340743c03070f8030f40351018000d110802c01040012180703500780b4a80303140c90680040380d550f6000d04a000b030041c2101c120b400e0703070300c0002c1c05425071701030340000207481c081c0e001d50714001441c01454400400320040f121000480b0112420b044000d1350007060245030360030340c100c2c4024440e280d010055100744c89410f6140e0b1840101c0201484152880d00104010f076000d001e039030303075030038902d922800010901e89015440b07203111040c2d940c51125004808d08803040c100f0080b2102503034a4601c80e0f155a81c60080c2c440c052181802d2041c00f02919003103081d05004241403400d003a81c0704a01e050f01901d09412540f51400410048180b50103803c200206030790000305482c060a018442c841c03405c9a040564220320014000b6554810454901c0702c40280300611030b4850300841450101154010340f8100380d4080c010740118034601e9406 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 393282967 1250 393281717 393281719
    0x20909040609060f150e09120f030108010e0703110613230f0d0507291c0b0a030203060c0c100203041415073c030f0f09150b031009050705 61
    0x8059500f03001c0804503600301c42c21035075840c4010030030402104080c0b01e49034440040c03000d0351006541050006201c0c9c10030b02090054440c0400107100d2504240f14003021103c50600801110740303142c4407122074603101c1d81c01078020303280099089502102c400c0014000c04000c42c0d50010411000741da0100303042d03a1080e540c880d0882080c100541e18080c18a101000e82200140ca00249442ea0381e208034000c20005c000507454840d1806032100caa00003421002c010030790a24800c0c07842c2103102d01241c0c40c010007103204058040c01400075850005449a0008510007801d40d55404d542929180c07400c8104003124a038000000c2101304400b00340c54140c0b80710010111503d40a11162490040c501199420300050303141102d2401d881c8002d02001d6048983d04245202d80c00c1208070128440d1040200e801003611a4200c1c83e640c405841210349800275034004102d035034401c0c2d4401d4408032102c0c0c0325a4000781c90319241a401c0d174007800001c1020080040412140c8401d24015486070480d01c111 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 393284217 1250 393282967 393282971
    0x180c0618060305010e16140313030f031b180b070804030308160203030703052211011d06091003020909040308060a0504050114010810080706020105090f07150e010302090904060906 79
    0x200503010b8068907041c5c030040044101c1a03038034040000804040010044100880e104d20034596288140056000ba02d4190030300640f06200c0c20301a003918a00c00d052410540f4180d042c81c020b041444013211181c3c0e035894548500240c100072501c0c49201a085154a000300290724820042c982005004072807090719000304650360703895010943c0100c0340207000960010000258034500c41c4d405070380c0c005002054002c400e1500241a6112030701f00700200c0b8034030202d42001400b503030402010140161800f4010601020300e8020804034040c00300c0b41d1f80100e0411480c80052030003501034809075100609071611901e80303401c004190a000f9074007240185034074000403515082c03074007130b1a040e0707610b0041e0380c0c0403914444011650081c000740307004c408404010340421100014440b01000317061070780c004200c50802e441440d041c81c224214244465100710000c200811244004000310740e181e04240900088550040c0c001c5d1160100d9a035000403e1001c20041006036408424a28041d82007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 393285467 1250 393284217 393284219
    0x70b0a02070f0929040609020406032c0d0e12060c130905060603010b130b0a020102130e15090a0b041e14010612020f04030b090a33180c0618 62
    0x40700c41140c04400300155046a10200460341d0380c0355181d058003804c1d01810004000760b9a02404003207070403580184000075181c03190081c42c512108090014829280e1a020015a051050543d2282089600d0061080e5101400b0641d540c25101c0600001c0700d0007500c100e03161184d91002250301100081c031550b9003000d000f1600c843c0d280b09aa1103210301500302441c59081019a000c41e40207207120400714110460b02046100080340540500f04250300050380340c180014113410824003540142036012032440801078208890413945410140903501c40354a51581c07030510024091108405805c18100305081c01c6800f060202120301342e5203a04100001a40c00042d00c1e1812401e20540c0001514a49070b840d450302d865008006226281284501d41562a0394220060804644281031504a8110030341804654901803100441440c41c0070607034014006400840d0382c4c0d40541d07940c003d0b580d4050401c3e18905020000350b035500b080c4002c84007a41d41a004000f01625100b0304020011118 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 393286717 1250 393285467 393285479
    0x231c0308011d0108120c01090c09050105011205061008070203160515070f121a1302031b120c0904240312030207020105070210050f130305150c030f0603070b0a02070f 73
    0x311505981307a1402500c02d14000b0201c0580c143c0141d81c00c440750b95643c018100c00160070094100040c40100c0c0c0105580d89064009441020000611480142480200803150303841206508445803542030922044e1601e40080307142d4062042e5910b28040540452018031000003128074083c8904120b0404035074560600b21140c42a101c3d164012880505414074580710b203401221040704114013a40c42504c0e514000f0300714061040c5020817840d8000284400b003200100421140f011211800780340c6090b5650009030120010550b4101810228101000e5503c0d07410031440e104c00149021114a00400f121462603910700c01140c01c00c85101071908003500070f000b607a1000340c050b15054107000c02034090180e005900d4020004100c02007283c0803060524401824180030703401ca00c40710350327403c1d883c00a02e081590f00c0500c907a42134030402c00400b007c8802c11264086003110740c00180c0d884440119141069940041d1914034010440071040c60740080e90300d04982c41e41031800381003603580d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 393287967 1250 393286717 393286769
    0xf031e0601030212130212010204090204080c03010b0d030305040f0b070203030618090a0206031e0103050f160f0902070f12022d030a1803020d0f03030f06231c030801 73
    0x407841c1310440c19500004200c1c180010542003030710300103003a10845441a41e44542280d000303400000007280e0206083c48005030402c4801c001d100c041c1c00810800e9003843c00540107440c0c9240040400d074a4000140410514501c440b01c61039220549801c2402c204070085c0d143d4104440302c0d8011000c0340f1030480c1d10304940d520710b0702401c00c50019090822b100e40030701c06a42d000030000c0170380724000c82c0b02d0078803c44209815402580550058620110081000e5061603e001c0d60181d00d62034460080c005804014159011507007003040042c0d035000c103460041074140d40448044c00c000c0d00da1185240c0d054020820110010030100302c203c6000032202003000400c01c9080c501a154818466622140e01803101005480c0e0b800038801c42c100e41e41e50006e10540043c120444550803110380b4003007010303014043d03024094481041449000e0030429009603903201c407446219a8248090300ca013468560f2902408404c4651f07902c2c507038030501403c0c041c1104100f03101e520f03010007401201c151000d1101d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 393289217 1250 393287967 393287977
    0x5150901061b020d0b0c0306031b01020d12180803100806040812040c030f0f12050a020a0209150d081b0f03030a09031b14070522050a020f031e06010302 67
    0x150b118a203403001107140d0341e00b00e030300900c1c0100d0f0003c000b0060400030130340380c80c1c005200c1e005030742e40e06a030b07071400303209060a103118130b9803001c800358006001820aa0300031400b800d90003680d06d814095189030040309809089000d003040c84036030401000b4030901c01c003000110720072007a2900032100e01e075640e85d0b0144d0b5803004440103882d103030050002410400c414001030b0307000340c0164009018662691103c050715980141c084441c512110000030400505121405e01e90541c0c0c2002d5041c45034860011f9120a03034410000c0c820b80c0c54000098955032010705030000c0903030140ca0380d84a83e00b10324141e180c031340c000142d4044030b1600365082107003040300081c00b4014401001c040c600b5a200c0301c1e405005803a00300812000d01404071007103100410301011048541e4058800c02c2e90701c4c40b84140b6503003400760b25044940102e401da00418560078075500e524001c4d1b800c404c0000366aa8802640304001d00590004060710240003007030221420303140042d9285d80c0300ba40a051510b80300d4000550880c411 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 393290467 1250 393289217 393289229
    0x10c02030708090d050106080d0c05010b011d040914190611130b0c070b12040b060907050f030907090c050301090b0d0209060402070203101d07090603051c0504081005150901 76
    0x400c2143c44078280415507042d403d1042d4004648603403a41d103111300380100110801e0014581c02c0d1241e05000090007445058002800c0c018924100780070200504030014121502464480b02c0120410481c0d2686071031104403c0306803800d09480c0090845140d28041e01500c1060500f00d082c480324006000301c0318880aa08401403e03903240100403c0e40d50881d01040e4442e0081810025400e0707000c000500c02d0020b1340c207140b00b06181034a0705003c60f072405042e00340a6000340301002940d51b0080f04440603144c640b040c81d07403265100c4401038540340194100740b900754180f45854060a40200c040c5043e201801028419911208140070038504980c801035400718095021914904156004221890001d02a01c3ca020030289500054480404a0700c800c1489045810398000c010303c051000f51160800510980c1d144d82c0701c441e079074170701c1c0703558941d080e1452180c0a0307015010750126001003002a069680031030034520000001c10f400c0b10182a4451800c006414130701c0c01000c1607041e915 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 393291717 1250 393290467 393290483
    0x6051806100506070f05010e340503190c03080c0321090312060103022703010c020a080304110619030c0806030d09061b050609070503010c1818020415030608010c020307 74
    0x58075172120b04544005a0301a03031195641d00d034084079280c05100822141d0328403942c1140c3c070400000480500850400725856584904070180803d65000c14001e50141002d1102c1c0402212410007007484140c0c0d600081c40403e000034541c44500300480034041c1105a480e407440140c040c2c50070400c043c0c00849407140550030400c080c01104074015543e58024070706160040c1006030136944507140088240426441e80b140d2910280725140c2402030100403e0540302406070f03808607035101051804050802442d09020514542140c0c43e5101558000315001c00d01e030310310300035241c4013500401e10300c1c40020028001c00b001072030504002554480c40d10380340e03440044441c9000da0454940c0312180c49003071840d5401c01e841000c0740040094074041d20540d0064244589810300f09400c650036805403005100441d80e141354443e0248405404403031041b0f107556900c0b920148480024403035600240c2805c42400525403015a2561040003071b1200e140c000c2003145100e1209903682d0041c1d10004000751 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 393292967 1250 393291717 393291727
    0xa05030405060a030f02070c03051009020a030215091005030f1005091902210a0501060e0315040201181e051923030307030c1a0c0a0c0f06051806100506 67
    0xb00b02a0002c20001c0c0b014540000c030b0070b030405a03020907030307100741800e851545860409005200081c0702120b02511b40c001e0812501c45141d02080010b6510300c07010380316406101c161038041d0050b500b02e4811800040445c441301d188802c1c060002d42058030f08280794401e660005080061040581042d220000c0135606560347d030001e00600701160542c01c01c0b4658091007130f00400a0741481c140c8921918200c0443c03145401c0a07500d00b1070384164807060030003000600b210b18544010484421180802c1d10800082c2d54500060343c00c0b031092104400507040c8207100003000029503400710b1220841c14984551607a031941048030f240316010302c03c07401048104040107001d040d51f00b0892030201345cac10051510045400040d0554108030025404030341d9042d130320070400201129945040da202e040d00006400c00c1003a0320304174010814003405110b4845414030500580c001c402c0e840e0303039010f1000d01070b52601d412000d481c00d0310854840a00e01c0750901090115071401041c81c20b640d00a06403174100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 393294217 1250 393292967 393292969
    0x1f23010e0702031e0a0e06031006021c090b03072f06151c0f0b010303020607080108010c1b03030b030a0c0501031401031a06060c0d05190c23030409020d0515030a05030405 75
    0x90b500100c00d00040c0300071b50b0801101c83d150100598400c84521071040c00c4549004c801034282111440c041400d000c041034034145080c1c00100b07072402da5103007020190700d91717880940c192521058402e00c40b03001d4074004d55400d41024100000c00111074500243ca8290300e410703640020040d40b4516486d130004d4101c10a95440700240c2070000c569000ea5031405800c1c0098540b142c40e42c0702a041a80103821007030070000c003e500000402d0040103040004c02004000a400501103400c00c3c6188082840c00084c24060512030381100242a1005056402c0161140341c03007005c40d2003074441c9034080780c2454406590b41300003501c00c60480f80c0010541103040300c001c0500010302d0b4000c1c81103600c5001800b0005c00b00c034017089003054903055600e031203684442d0720000c002e800442d10480c101708001200350000281d0b9800c2d042c0c0c03141540b00316215032091884111811801640c020441161011604240000d8260821400b0700414440c1e003107008035003018952142040d00003d400780e48100000c00c12 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 393295467 1250 393294217 393294277
    0x61503051512031b0303041b0e0c0904090203010f1413020f100519090f0e04050c010c05031c06050f03010203010f03030f032703030e030307021f23010e070203 70
    0x1805020307245030884d4403644004510880444440b180d00100410040010b0340b4040354142d144003910402481c038140d2a038502c0640180607800030700020507558131035100c981004004580c020002d001c040e01c80c11000c0010b2604441403140c10507003602017400f50300c004000002990b00507102122020a80052106841d0400c2c5004200b00040120307000503400300315911180c100c0c0b6076a44100e1842c0450380071584d400754201e0a0341d00c1541c02804002440018910a90b66080c01d200400380c0c1103050960443c026100c4082400b03804420351191006540c1c03000d001e41e20104d0b0780501d40b00c1c199007818201c1c0000d0050740031300e450b020350520210b40500f0408040005510340807480114829034280c060500001f01300401c480b0b000940704158040c0542d01c01680300800550540c901014001c0d07554141148201c1d0100c049065150710070301940203404600480d402c05850204100101c660b84030092250320500201c000100b1040e0788040111002ca041c01c140c0020729624040300900 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 393296717 1250 393295467 393295489
    0x15050405100506070503042409090c020a1401020a110109020102120d0e0a0b0402040b0414010611032107020d0905030d0509030c0904060b0a083d0501090615030515 72
    0x1c0304400a400081998401009045240c800e4018549962602c0c904102060310390324203e11400c2d2501494100c10f90020502086942c6400c005ca61200340d00c1d0142e0034403401d5a0301402e17004900d42210000751054004141d048816920f03001c0f07031807140309540c1c2200c00ca054024016040141e215a04400c0b00c4c000d01441400c40800081c4c0d140920103aa2804c011940205d500c040b03510200802c0d85401d110b402d980340c40507035081c015641900c00f414501001400341c3c0050200d00403c9004810040060354800e082d41511003600350010000035030550801c0302c0c10001403055149107240b00e4442d140030f10440700081c00508103100c40103010b95050b006102034a07018441d900d49a1803d40d28504900e0185000e4140050544078800901a012040d50015001070b800007403005500c540c260004103607001120700b0601d200b010044801c4042c01c841d1520362155050034000318400078141d06c4041143c01c4601060a51a0b01c101c0944c2590710880f4220380113848841206046e05111400700 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 393297967 1250 393296717 393296731
    0xf20010513030b06120d030c1412011503020c010212010e0108121602130f0c080903130905040201020316030f1713110a0503030706020304061104031e11100c030206070315050405 78
    0xd025040176202c1307a8508590500154006925480840680c41d04a50071604070b0306103030080d0b4501840000244145034040c07042506108845046807903c44c072070340c151a135501c8414000c1d0341ea0020a90a29090003082c0694801c600724240005111007000441840c2d4041c15003405090030140c003541c5d140da0700c003801d090303801098240000101151a20440d0070503072004800040c0492031448c02012440d00808038411a03200b04402e42c5422140008039007141d00c00c44001c0360729604da01c0100d05502030420410755040d074a64144c41055000002e043c2d00d13001c1c0341d480075003c0301f41d822443d0341c000302035076a0038044c1204407904002c2120781020801000010303001d05c1249a0f40c40c00701c0d1840c2e1204c01b0550b89180d0100c00e01003003002038000c1c003541c40036108400f070034a82036482c1c03070f44903c4c90754000750391003400f001c0540100500101e0f00d8400510041c000c0300d61141d0608080c05034065854120b005025160025411500034803075001001c2d5004040c5a1150505050100411025041c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 393299217 1250 393297967 393297979
    0x409020a141f02010e100b180a06050405090a05010b0a15050307090315060302040b0d080f0c010902030607030c020c04060806060126070314010602031e030c070f20010513030b06 78
    0x148000d08441c1c6169070440d01c46a00000d12900202c0055080c092000000c414007400c7c8449451a0340d02c0c1d081c02003080d030508000740042c0d00d03a591400c0040619500c800e030071a080c403040041e06030021a091044a0148000b4400410510b040284e061a0f0340030301c0400f981d0094114501c607205101565204449080070038450391a03032546004087d850418589003a00d4030014411414140141c0c15860400d44005d10340140598803c8a0360041301c1501108000204251140d06002d40001d491b250f0042c060b10b40364204032100031301400f2080c0fa00405441a403d140c5458101845074008440e1020050030030b0b900c4100044030816041e8040900d0340007072448500408403079103040fa002c0c110f681ca0006001e192142c003d020044140e00c004103540003803001d4510800b040c0030324104c80368410b46260b5a555040f074036030081c0c01038880c0541500d02a02104003008034041c1e01420340300e11030f01000110300281c1e00444082c410410703003005900b8202810800030b40843e8000e504444d0052603 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 393300467 1250 393299217 393299239
    0xe150303091e101409060c0a0c0806060901150e040f020c0601150f0908030304030e060c1f050604061d04021206190f0506012001110f12060409020a14 66
    0x1c0c1e02261080010495200003107078034a860310b0082c0300c1c503442045a003000140d135200c8a81c400118004d059107180074440000c1c004055420600ca402492940030300c41c00b04c00e944880c1995611b039001c4880724000e0203ca800411950044141350082c2442c0c1d50300c00d80b441c0e01e1481404042d0030b55418021400d0707000c0c8400b65a1010501110b07010b4210107850300ca115000960042030b07a0400c2d061201801503054003070101300720110441e0351040c1c250a007031440003002400706005200d003040f103a010303008442101c0c1c1c0c11034a9081c1c02036410000c583c1400b142d01d8600c1000116040d40c4102c0028850200389031003061270300c010282c2d00500051003140c400184001d01410040b00f210081d446200070310a0b2003001d05648588020b11194543c00c000b18540480040e26107503841040c0918841c002820704002d54094000c0c401d60351010120984480c06490300d00150740000300f0003d100d1640c2e90005030340d42400c0c4256000c0035001001070140c00d00e8001d0000300101003240c1683c01c0965280d07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 393301717 1250 393300467 393300469
    0x9070c02060d23310206040315050610021c030b03010e0a0807140a2a170d02070e0f011205010e031c05091621150b09010608010e15030309 61
    0x100d4002c5031009295034003800322000016001c148001400003640c14080341c404182c130921000301d440b080030b8075101001040c003035000213600c2c0c1c06103074401007002600494108100c00503801050050704181e8400c502c040340c40205030386502a9a843e01d18000d2035503102008a4426042649020005400010202d0459402504003504100b06950740c440008004041202c040c6c0c540840d0b03c0584c0140c140344d902d6565611224615180140e030070a21510b803410f0714900c001c84c05000380001031210f9644009030040a48a1581d04144009401005800503002104e0110079200d50107001e01c80c441c2d41c0c2000d15aa005074001d01060f0344d15940c8500005c0400020001446130032408121201200100c051010550354014801215070300b0804544400c0b0107011607000548004001643c202d0f642d8024503110050001c802400300c28080c0540c9144e000745506c081108001030703070700142c1a030320340308259030b800820b04c81c0e148041c0c400c00002d506801500d091140300745000b01981d2802e104c0c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 393302967 1250 393301717 393301721
    0x3150406170321150603041109010303230c1011070b040c0905150102060606031f030c09050c0a09120809040f0614121e150a0c08100509070c02060d 65
    0x10700c80350301c1d07038400601e0380a20030900c038001c0c401c074000c07084000c004e1400000c21401e0841c0489024007445000c800305003044003c18948501d0a0040c10000c0d00d5a52820014020704050f042c8070f00307144840403640c1c1081c03000d00464111461780c03c0240a40601a6410390003070010501526042405103e2500010703a0b41030510b000d83e014114074080b9906205190048a1000d000c6241c0d080ca04c2a9a4803542d030085411a0b00400c11180c17151030341d948c10000380041041b04021014030b50a040e012041004a12842d000c1e500d240703030100f02942c0d9031154640c080c0720740000c440c04142104c1081007420200684a0b41c0d0740c0c440d6503100d040100103000701e03003078a4240c26005030071910f0308010b1041c080c2c540c10000e50140120790303a040b42c1603100755084c0c4a0032520210900e501100c10303007070b423014001c00040643e035886603c1c0105a01d03051201c0d8000f45001c0c090600025064000708004890300320000080e10307002000300303841d40c490650540360745c2d01008080f038205106010b0110840854 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 393304217 1250 393302967 393302999
    0x80f040309080f0c130c120509100903170703090b0c220308120718050f03010912020d1b03141b030c0a050606041109100212030a0b090f070503150406 66
    0xd100420b41140804100031410205d1201c0d15407262400c04150310301680a0706681d0400032079403002a10752502084141000380b54a00141901e0a2001c0c0ba410503900c156003081c0020440652100e90701c40aa085050740e0780a00c028100030f09502c049101c485003a0002d20300d10300d440200381c0e600382011800d00c1c0403042c4c541c420b50b02600d01240d80094030030100900e55000c0d200c2c2c9881d299501e035515000c284107505000309802440451003803240c9490940c0403400301c5400886e030550902c14614000e60382c00d041c003070050000341100d1284000003000250b68100540c941c81d006200707500e201e0325003229002042d00d8106107400c00c1012101540c11300007003004050701c1c0701a01ca089c1c15814018035081025040d24020b600e04161040440001400c0d105c140d0421540f1890001d2080782c101d1070084454041d40d81103000200780000c250540d4040304060106560901a580d00c0e0440b8030010001200c0d2040842c40420008110204485002030b4410b002000000d0503511100010825086 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 393305467 1250 393304217 393304243
    0x30109080d05070905131509020d0e1b0105030a020a020c0a0602010e121905130914041703040f12110a0c0602070b04080c0103110904021206041b080f04030908 70
    0x558141801003a00510b603010310380741402400b1510381360124134800c0c0d501451b13500751a0749032a402140d00e500b0000e04000c06c08070380159182c81406c1491402008120b2450141d441694205818100b114580d0818804140c4415046a450126540181d40010440030450042800c401101c0d56070501e041c016000c00d43c000100040702c0f29a151030001c02c10010080c5100a000414051402441d20300071283d05240458807805a180008803940840d0040d009690824007607052413000c40311040c1c0b28078000e4051544062180188000d2031000780c5d4007500b0716040105400c040380007003414515889051524501c414100d0b640e050400e69095400c440d0310303180040812800d54100003030805043c1181c000e43c03500345070622036507607a00e640220505054448200c411507981210580e01c000c01d002d0710555540a40f211244510141240e10b130f44030301d01e850349031800070b0003596032000040150b85840019407100c4c144882c015100420890412194420210310744805019811062103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 393306717 1250 393305467 393305483
    0x3050f010f03020a03151407020109060b0d1a040c052d0307051008070507060204060f090b040b0d05040f0f1a07030911010302160b100e0a0209031c0e030109 69
    0x50628000a211106901c4560404800d82082c805a030321007100000f200da1142144000600411502c80600444042c21480c0111381d002c00031a00c0c0c0640004443e03512550040009800940400005c1c408112011b0300c285100c00203a01703448000400139800c2405400c607101010341e9000028080072540d28644801107203040180b1804032956030404a8504c101c02800d1080e0500b8041040c02034018030020401c80d01a000c204494094021603070305036006041550b42d103841b00c401801c41c40b101016080002c941810005045c1c80c00e8090368203540089e5012450312010041800150402800940c1c1c503c0020101d000041e50240340700c00503610800c58102003509070612402d02d284001c1c4441d00307150a10103094002217000a050700c000d00e0908005032240d202c2c1d009a8400060070038003e10b80001c82081c001b082d9a00b0703c50204840e842d400c0340000e9a039072440e02c0164050651441e03090b90100c402040c0d24072202c42c840d40a000310b454a90114a9413000003400c2d00e400035000d0b50518 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 393307967 1250 393306717 393306721
    0xe0103021c18020a0803030121060608191407080d0f261e04020a030209090c121606020309032d1b10080403080417130b13060c0b280c0305 61
    0x30414155000c005c0503c0405036065625050449a0030000041c0c0c0074003107009000c0c40820018143e01c8880900503000c00c0302d100f41c1c01909000c2003030074016401d4565030904c01038802d42060000e1007009071058100540002c120881094811640c0e07500c0100c14001c20034807171102038600c0c020184111143e2940f9484905000c20011034018a4901411520b0182401c100158031062020070232241d05580c6140e440e03940038032081c104034114003641e62001c50301040800940380040d8000c203107800d8000e0f10f8100c59a40105a0b542d00c900440d194064200072440700501c000200642a840030404a905c084c00c2c11840440c141115242080c4065811034a184880d0a0481c54801000014180301511741415100980240d500800042c0710000c80c003007200d004460f04042e18012401c0b11a212445a100c81c051501604040e08031044460107080c00960300380f1950041900d1600460402240d49922101540b0514504040440300c130380d44130001e49c1c034225440f501074100e580d56800280380c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 393309217 1250 393307967 393307969
    0x7050303161e0f11060903060f070306050604050a090c090506040f0602070905132604030303060e1317030604090822090b06041e080613060c050a0e0103021c1802 71
    0x2036000701031500c0b0724484000700c03000090140301410841c1a0810100280300c1d6180c1c000803044c1c81021413268050103800d06100800301c0504c07400e030160301d5a8500388070542d1140d0601142e4085c6101d09076201d0301da070b402005085a40d07882014021303035600c1d00702c103859203d50208400782e00551000c045004e000f034040000a50601180c1c02405c1610010700440c18880c4503800000074070342c800380c01c220780041110142c6c50340011004594170b80003002074540b43d0b28240a0014001c610540c0801100c400000d186410800e22003402c02e0ba10a103c84c02e940422909a103040d0401000716410030717074543e40c0d9404100403001801a000f03270501c0140060400449441e01800c0755880400410b0401e00a0512a074884050313900b0340d806144200d480d882000d031043c0c1c0d40b0307951b030707104520f213014100911100e5600f540304c413140c940c082e401c10301408054902c12a268403580c0103840004410110641c1158405d400801085c80c0140c0025100480304c102c1408843d01c0310704038416554429051011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 393310467 1250 393309217 393309233
    0xd0312090c241e030507021510090e0609060112030903052a0411030a0f110310150906170403050d060f06021209060702060c0703060f05060109050306060102100e0705030316 76
    0x502d4149409580440c4601002028040c0080e034070051588850000e06101d108121200d0b14480e4100d003c001e900f819035034580032100f54000c01001d141040030044d059440000c00d540074001c508003c194a0b80f8084845c0c2e05159032400840400150040010100b1070404c40003080e0031030320791464400c00ca910350440c10031020303c0802d4081c0d8185690032200000100039641d003c18420b502041c03048540d104a001060342d41822400904003109100f001d1a040350804140c0e464092518142c0d07604035010b6880c0b039914824100000d17101409000c10920300700040741c01911908120303082444002c03d08090b203103140c000702414030b1300407c04c000301e5504024130100b00124064143c07910b5480300205c0c0c12071041040181c00344100186021203400f04000d00701c003c541006040101200c00070b1100007901c416140c290016a60790b60101c1c0307a10300443d100c2e0089a050700100f03a0305000103521400740044405805850203051000180ca480510003451200d0700d00800100350703440340ca040c00c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 393311717 1250 393310467 393310529
    0xa02130207080c100c031404050d120b060706060617010f03020d03050903030d0504020a050109030c120311060907030204050f0c09010c1b030305120117060403050c0106030606060509100e0d0312090c 87
    0x1240380c11401440040345001c81c084031a081e061500c4403404001c1d03c0c60030301338180b50041940000780020054188a03240d0f00c0300c01a00c0e986d40c1c6002810300038004c3d0031251030080c080c0700d149040c1010200010301d0180c0e07100c01903901c60b00b802418007200c200000d0460b0806001ca000860310b81e003c00c0110316110040f04040c0c24242800030b603103810358403107000720011400740c1010300d1100c9503100b061501418403481050200402c0f07030b1041c80c0c02010140c507105c03240b004038019801e04000c42c9542c040c00300c001d4420354900884e641407101c001c004640c9007006600564084603040d40480d92044840b942d60051402600c80710398480a110040c02d000340d0584c4910131b20509141003110720308011075007a8206401d4500740c0d84541c0501003039801846c055000921701460310000184003500034018000300c40040301d1040e814282c0b414195005e9400c4000301e80c5c400c245040e88000640592885020308403510f00000f64240c035650707040c0c0e4456054110000040320100c030304a60030f0311b03190961 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 393312967 1250 393311717 393311741
    0xc010801091a01030e0f0706020f010506060a0806010806040b060a03061a070c03020d150510030302010c020c1c050a12180602010c0c030c1109010b040f05030a02130207080c100c03 79
    0x3541100a560012144903841c2c410b04064480c072101280321810011601c101d4058000e07603c1460381d81001954900300188171244c4c55080100043e51883c00c0300c203550400b80b680d02c46092035030300e42d070046030003020042c0015441030f55915032090b26103a8a004c0c0040d0b00300c6840c005680c0e03007006072500c000c102c248240c8000100c100034401c0010403549a4000b1030fa810750b290107902840345000d0008140640c019458245040100311603250b04c0b42020741201c1c0290001c20410360100e01c00c0b81c85410f1400480c2d001703252807803440f118420b00901000f005000304160b612105d03007650f40c04c0310130504407000000917844a019902e0009861540c50050403240020010402d14040c058660b11544c0805418881850102c9040c8021155030a07070603100101801815078403503040c41c40940142c01020100100140007056030304000881d1454160014100c070300302584901e140010b036000300d0007103800c4041408110003101c010081c1d0007581c801210086094102d0140007011224521884 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 393314217 1250 393312967 393312971
    0xb0a0e0f03041d0402060901080606070605040308010f0b03070e010e0103091514011e050907031413052505060f0412081905030103150903090503030f0d050115021b0a050d050c01080109 81
    0x48001643c03100207d444055003802c0000582c3d40e03840000c3c406000d1141c014100b50704100401c800c06500c0340070641078039514100c001d01c10740c640061303030b840340000c40741c020215803c1b00c00d00003150302414529212080501d030208954400350b44040e500da03020210640016111235491034900201c46025000d4011001e140030581100341151500074558407805005400b07110201e1200c0344260005148040402210503542c01e241c0c290300b07030003014404144c03028010160700590300311407820442103104980f110345032441d040000300440f40d4000d0b40d560301901400c00c000201c68203400420b1260901520400d615044a1400881d40c01100e5100404100c0f04000604c001840c0e1145441000784485002680a0052805588010090f001594188808503002243c0103000b0020994144406d00130300c4a80d0f44c0c0c44590b102c1c4007100100102507000300120400f04691582d0892240d00c3c001c05001c03002c0d945030081800060302c298255038a80281c2c0b41581c1e21f5800040e42401442c043c001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 393315467 1250 393314217 393314221
    0x501020a0302030a1202040509010e1b03090703020909010e0706121406210a0c0b1b0a0506040807081903022809140301020403081204120c0f0b0a0e0f03041d 69
    0x8001d403030348103450203801400031803159600301c5d41072507042c1c03001340c440a020110705503105c499000c00900100c4007103080e075a4007021050803149503801d69018290784e10080c0300c45801c0d5402c01404c4080103004604940da6056000c3c1c040c00700700005801001c007a101d54940321006150340c01039515450118041c205071a09121b4142c4070711604010180c00864080c1c0904e100b00086810721176004000f411913800c14401254806428005191074130780e40300304c0807000b43c4421703a032a196443d508010f407140e009400005c1c0800c4c054802080024400d00c0814609108540b01c521110101640d02c0002075011440066515090030b025501e02c0300c2880c100c0040f401480002c00b85000d0b07000d01c40e0001d4000400545030744003501583c02460b4001c10f441d03107030f60000143d03802205d030031141902c1e02d03414244071204460165044102c81030b0007003030603607003400c01e074542078280000502081c50141d40c401190302000001c5c0b03c21f0240c00362040103966142c3c9041140c203a66146800c20240822034141 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 393316717 1250 393315467 393315473
    0x2802010f08090312060d02040608010c180b070201050a020307060501080303160e0a21060f05060a0b030c0d0b1807030603050f070b0418090c030c03030f030504081e1e12010501020a 79
    0x6070b844e46807051380d030f61800da950b21001c200d50741503415000350010305084c00031a8404043d00240500c030700540d5952210b82c955262081c2c458258854500341050030414071026501c198002d2180014038011030740741410b99951001144c800764407004043e003000c414882c1c400802d10203010741841901e4803045200711340c0001444e10040d41314201000110801d00d0380c1c03005100b881c4800075030300400100818006000804081c003000c48040d44105030048001c901c0c0b801890641c2d00070043d85c405181043c01b09480c410041031340d0602e00d0340c0020780d9001c1d07500c0740000d1900d40303209091aa82c00f280e05403951406c18502907000c201d4880e5600050001c1c018084440140c404680e03403c2c000080a404103100701e80100707030800e409890004c2c107031804024081802c01440031203220395200f59261400020840c01c035001558000c20400f000c00c800c0b80e45030249181001c1c404804a41d8900e040030301e100c640445004c0002400340740c2d40c04200f4010f400d010072032040c0106002e001902104140750307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 393317967 1250 393316717 393316723
    0x30e0604050906010f031b0815091902030408070609050c0307050405070e0402031008010219120209150306011101021c050c040302062b0c0309060f060e0610022802010f0809 76
    0x1c040c2410410741c404c4c5072241e1403280d005410400340c402448015003040c40801000d060003128140343c00141d1070195030050504600240c413610300e80c0342c0181c0440040bc81d50020b9480640f0664100c0d00620200000c07604501c10200e800d4440c4d802450821098810716060003003942c4150321035841c040812003140d401c411955440c003000c40b00107030343e5590221110040e01c8aa00211070070b610206e2294003081011143c0d408460750760b2034030031075100d031500160164400e2051041d04031034000341c0c2c01c004c100c010703010315088070301414160503000a43c24804e00f26040b9106580a5041d03064007102950080c0c81401d800541d9100e0303d624050031500861510300c5403502038004120040c0f0070b03e511108000c0c0b440c89000c200d0700203000480548000502501e003401c4192402864034030811000d00340da110b404120341c03c42100340520390f02d20003040f070311940308001d5005501900311000c2481c050500c400a900e1942d004064414209000052000c60441006c80500014001b4404082400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 393319217 1250 393317967 393317971
    0x3100902090f061f030227010801080c010c0303021809190605030303160c031b0b040b010504180b07020a0204060e011401050a080103110609030a05010e0d02120d020315091003030e06040509 83
    0x820018074206840324404c4009108040710355943d40c84202c41c19152800d007540c10365407c00f09a0303915a0698803030103650b8031850100c280c240403920f0418190000b90094014080304411481550080c080400103d0015a4216066144010550341000e42c5649a10401c00a0501940203600b1898012269150544a0340d0311030b017441810104081050300c114141507007084181103520000c009440c2114503400d00382c80807909640100300215540c2400e00c01c80c024100c15005121800440740c45130710b400d82c0003801007011400b800240c2409a01e0b2801000010000380110450039854400d0311345281c1c0c000300005041000400400030583d43c40a0090b056a40002003599060656800203802c2d120780c00381d082c2c142c01001d562006010040d8032522150040505944030401403100807a240e0850b40810003203180b080c095403059242c1e075409503a10015603402400511042c2d000105490f03012a0400860118240c1c14003c04d035000c0f820001029043d20728606090a00780050181580 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 393320467 1250 393319217 393319249
    0x15130b07020a1b05011709031b06070807030905150c0904062603091e040b04050901052a0d0f0609240504060509060d020f040501090c08091c0807090503100902090f06 73
    0x2c500402d1040e402481260801080542848040b42d4000c0524ac1c581404480d132101040c0003600056629020780180300c612139129001c0c0c1150003a5914083d0701e2107014100030000b10f003c2c400c4490b02e48031841803c000c1d0040c1140316102c0c0c01c08201c403071040948841a61002e81040c442c0c400fa6450f41c02e0b64202040720300700e00296100c44803000c100240301384800d460b803040c281020b12800c08419030013603000b0040a201c0480301603e8103020280022070504c1002881001c0281c000c80207000d5002c2c211018030954007060340e0707a03101c40d9601034a01e90114100001c00d82c0c1502d441107441d820307000e4010181524280f210500d03000009009003c010030440c02000d68880c00411581e500100c6181040014020802035071180c04c5440101801c421038008168003c0101ea1b000b000000c400605400d0841c11001241c0100000c560740c5c02d019156000344080c0c100040b5581e13070180142e01c580e0b1080707000000e414030399004000041d4800f602d40042540b0003004d20401c1e071101c103003020921503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 393321717 1250 393320467 393320507
    0x5120a06110f09060c0a0f0b04111e0f120a03031d06150607050a0f06020d0f020319090203030412030f1409030604110a0e091e03030915130b07020a1b0501 68
    0x50305d2440d00746000e06400038211200f60800740204441c190703045005034000c0701c2a0a4500d00101846038850340051308100f0401c004560300c0d80d42c503140d0a02e240c3c000001d44580c11003000300c42c1052521001c0841100482d4440c02098400300300301c0500c4228220101c010041c0e81818000c5004000880704968080d6100064103c1400010460b80c9540e6a105200304038086c0d103403c0000c02034201d0344200420904001c18440c0c03081033802031700d0252800307062802a0700800d8412100038204148200e82500081c480004d500000d001c00b091211700985400f1900211720000804040202d1501c0200c6542440401c2082d100001c0700c69110340d202c9500c040b0701140000240145140d40d0100c41c0460714941040341c1b40030049007080b2102c41402800300c02c900d403100019200d000490384600540d00900d8101d0003072009a1403031390410515102441031a8290300c800654190480761140503030301c0000034a081152658101030715007800742111062509180009217280208903681c26000d0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 393322967 1250 393321717 393321727
    0xc080f04120311030a0c0306060320180306040305181f0807030204050402070528051902010c060203040f0c0f1a070c090c081504020f09010c0c05120a06110f0906 71
    0x5000e82d1105402c1d503c1c4545a07030304d0389003620703503040903000c2031100d14000780c10000005030282c003d001c1c1c0840c801c0400d01a413406d0f840c6807450b00494000604d11700a03050341644029281c3c5091000c54015800b82c1e80e42544d441c4070800d0004040512019580108001400c02845a000d500282c100e088180381a041544400c8011000380c000c60304041d030700610015020301000030010720b802d0358070900b1204034078024100001d0440303508401c138080e12030740055452803600c80b540d1032040d0402c1d1050401c082c40d404180c070340d01e0803a0800c480c21180d00060f25022070502c010807400d00300402c0d40f40502c02129040c40c103001c2c00341001e8080300c102d801010440302c080001001404000d002c000c42c04011282420038000c000030400d80c2d601d10001c01c0203510000a06080c022501180c4441200c545060095001117601464002c4181d40411803034001190035030312444090b0001c1c03444001001f0280250525100719040720610294806c0204004a070071505401981d04140045405540354 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 393324217 1250 393322967 393323003
    0x120203040605091306030b0a0e102a03020d18021201090210030908040b0f0a230304241104150507120c03050f12152d0406030602031302040c080f04 65
    0x85c00c000d800007013032209a0000c0245000740795100f540c0d031180c118112021480c02003500003c0711800790241d1442184950b24503400b00d80103490540140d801d20300185840d5100c1007490841d011a54011854021145001e0a525018028100050800d0004c218100d100d0340020303454051303002c5080034951141000000e121951090307074010001281c1c03c90387c6011040489405d541300c0840c9401181d143d607500705903080c040c2e5001104450300c0c84282d01c0c685440d218451500201c40a5403200b00306048142e42c0003007107029102d50140c0f410740c16a00c8500b0074084141c04140d401c05082000024000701d00464040b8900c0b0103154003038141750028000c1401c040b51140315082c8070300002c1100151180d00c07003000d129058420700d1a441c55041d1400003404000304442100d0074940c40c600d0280b56006005c40014507080082c7e402000050072941d43c0d940c40c0241e81044565441d0025040d884d2421360034540150500b4802034a01a43d051074501d407200c401103009031028100350399102c03e070030031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 393325467 1250 393324217 393324221
    0x16030c052815020f1002091008091f0b060a090305010c0315140d05031201060801120b1504061e05091b0307081005040e030307090609080a0f0501090f08071202030406050913 76
    0x1d400c04071801e4401c400c044001701e9011b540075442c07850240166922031000d5500c13401160b070203480c0100141900344c8165892801007504995071144c0c465030360035500390325603a8034018000700440783c0700c00211515509099084803040703800e1409050428102c4d00110740c03071038006019030342d1030f02c20541504d200301c01140d00154400070042180c800062110341103590310071014100c0301a550350100a80c0c0718010000491001c6400404001014000c250008282c0c80c0750181544050700002d40c903030340c403051400440e040e100103034540c8444005c10312003030802c1901154440c5ca0b840d120001b40000e0a0302410310f200041c81481003005960101d2401d0744040d500c80010200100113202c10b22160f607200351607a20030380d403000208580c0c24000460f940074101c0b03101290054009084e851025494010488c1440b0404503055580c50f80c10400060030035141402c01402554045c0c0c07a140c02d4035081d404244c6030714403002554420b201c10061982e20800b11084d4003410707640405007491003000c0e000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 393326717 1250 393325467 393325483
    0xc011101020f040308041a09060a08070212190201050901090206040b0307170109020a0e0f10050702040e03030a06051e09040f02031c0305070e04090c090e16030c05281502 75
    0x8802d8001070000144070205002c1c0c01520000050031850950f140391104840c402d104445170040400d0204110b118011301c0c1080c0e2000d0180180e078110403c100c80ac2c40e07103a11074115400001d12000307801541c0f07542440362580c0b002d0404020801c029890300050501d003d68407a8030000200080000c0c0c0b407a00c60440c030300600d691054607da031541c40d800380001030340041c194040000c0036083e500040c0d1a192560f4805080040c00c01c00d0030700180c0e030b004c86059010200680e000b0780c0f10000c0018486003080114840c0140c92000200e20b414001002500382c10480d188030800b40b07003000c90145a80703191764030750000d40c4500345c031030038490710310210342402241d03404c110502118004405515806400c51031207100c513075075500410004402040112440c040018091002e002c41c1030002d20f83d1036208a0000c15908100c0700c143d04195102c0a03409003e4104643c08042e0070001c200700e0403d00c02102100c10060381c0b00d462404146404074036503400f0b00c035462544207400c8080d003a45009221042d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 393327967 1250 393326717 393326737
    0x51b040f170a12020114070513050f040b0a090b101110090609050f0618190807050f12070b0c040e070c0314160c0602010506031e01140f0a06090e0c01110102 69
    0x1088803d80150041c2c02002910942408440180e0001c1d4902d4450803c980d144200b00c40341c0100a400c0c4004d1240350313100004e51903045542c43c0c03440c20003036568400030401095240d00c04980f1540d0b00e424000f440c1c0f945480c440034400b020341c071f000da0a000405d00e04401c41010030000341010240c10040007810f8441009003540c042e1032204618940702045840c071a004085518190050220080703540302c4809030014900c2c0b003100c40c9000000e803900000c1030101c2c051012100d542c0c18141c5818209a902c3c5904441d8060002e0f01ca03040195001e242940700360781001041c1490f19111100b42031101c01001c48082000d0200d600b001c140c0540241d8105030400100389440d005440800e16910449007002ea582842042c0d001484900c14083c0b684a8400a000b0340309044501e15041000010b0341c141404135500c0d00034101c032251042c0b100382e201b071014980d1b10005080014002080f1041c0303411588826003441e1813140c1c000400641130450880a2030f0401c0c0d02d1281d0641c241c0240910b030100c07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 393329217 1250 393327967 393327983
    0xf050906190206091f02070c0906150810050d0212070e07050a0e03011a011b0609030519020106030302060606250c030b0109150506090607120201051b040f170a 70
    0x2012010551501c0000741031595000c603005500e4040305a03076101110280b44103290395500400c2c401200c00d40180c14128451010485541d0f296a070b030106891450304103c054814101490480c29800030155400110441d030f0707801d0f09070074900031131500c40760440040e000710784041d56440c48040402a1800400f0008011039003410200c5000b04154012000140018291021401d0301d2034184030f00541c4082d481d07206030003401003e0054030847e06859503e00b0114400ca040c501090942c05050300d03540c82035503695580c0350103303012014003856031640821a07240a40c103100107900050039075004403049480a0b29540311821010b411000418016500d10300b0300880360400c40003140e204181c0c0d114460107081a81c940418074100c0e48800c1c1c00c51400d01a10ba420001c50600c1402002c50180180c50103241001c10344412030400c4500c8000401030399a401008404510401c8422440906a20f001e14151030103256440c1c1c0d071028010030145911110388220118800c01c440b4508030342c00580 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 393330467 1250 393329217 393329227
    0x51509090403020f0c1f030b0d0c1203030501080f070e06041d0a0611032415071a07030605010c0204020903150916050a03150c050f0403151112070f050906 68
    0x802515465004070b00440f034403c1e1089210071b813134001c0c6000c510316018101d40d10301458046041b4041c0c03408556081c1c0114800d00e41102007240035644030b02910507449514407a600f00e20340142216016031008070103030820b60300d200b020345001c01c1d8201152950700c40e140b031985805000600900f41e000404140e20001031800e01500004a4003480c2c09001e050100710500c2c50a601441e03511044500c2002c4e80388400c0c00100003a450400342840800150010291001800c01c1c005964880602541c520040007002c0c0490b6060220b8141d001b1058074003072007028501070001c1c1c03030001f841c20001e200759008104000162810031180d59021943d034800c000c141000412243c40d080c900000c42100c2000010100d86410003074210001c880d40a0040e50021400040d5900106492810141040410841c03840c03c050158054400303103010301e00781c0d0354503079480072103c1c12144000c1c01840096030134819910a2410919a6503000c230007814840a4203e507920116020302c500f809580e8040804a8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 393331717 1250 393330467 393330473
    0x60403050c040c03020405181b0a02010207020406080102090d1e240b041109090702010b210609060402061917040602030a1d0d140910020a0b0a050108070515090904 72
    0x241800051410b890402c07242003542e000314242e01c0381c0c7c003c01d504400c103404c0c0c0a401c540f4200106030b01010000d10f41c0c901010791720703207602d840e807109a0b942c0040c2e4000c54440c096113030a1180c4002481e06d08021807410b103181c00428044444c01d00f0281c004001c1c586100c0c81038450003094405207510540165019441048080c11a818400202141445e20920010354205841030701c00305801910400d09180d544001c0102140004203480115500d610002e001d5448403081040c04034108850b40b02900308000c1c500d8a17200c00140b011006911030814030015031140700403180210030445a00c4d201280720a82a218040e00c011442c451031441e1080000b403090303540c061070268508010900c00f001e02da082202114041d600d4105041e00910100c420b0340d0b0140640001007514060349509004600300040e4600981004030780250b00b000c9594000c01c08980800c1d0780c01800604e0800c603a50410720069680d02541c00350602030450b0700c551710b0700304030398100f640c01c3c0d4100108040310500c1d0500d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 393332967 1250 393331717 393331723
    0x50c0a02060c2104050109030602180a0312121b0507140a0b011502030307020d11070b0706091101300204030f14061b030406110417070807140919060506040305 70
    0x841c1240d0f00340e184003071410314610b502100c08a8805950b1010b6460460704d40c00d000758004540000b050b040740b80c01d0038082e111000f194000b503000b041202400030003401d01818030209040780c000d542c3c7c0307081001c600c6403804080c015403031401c5140994032247c05260a0b01e200c12120803048991007420004001c0100e00501070b4160b80b08140d140d1040070011500760707a00e000c240e400c030003d608070f0602d891400344107141e030000700c40070001200e0101c1c0e81c8200c0b03180c00340d11907441510f84903103c1c038104080c0031202141c072041100a180c4002c13a0f490900c28030071032010315243d11a60300c492420081200395940c040c2da01541c0c0090040c1611029031a14490a668884413020207028400000714032320445207103400980e040b078400c1440c59466503038450007400c9a80c109000c000d414007001c40e20002d5001d0b038004110080001b0061142080f07003081c0380142651006403617100708640c82020380c890401c0c0341d4001c140d00c030300310220000240031580908443c2c3c11a50700080089800404c0c40000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 393334217 1250 393332967 393332983
    0x80708010c020d080717060406050d0818010206190203040302010f02030a0b090601030c050d02030c041d040b060609011709010e1b041812110c03010204060c03020c010f0f050c0a02060c 81
    0x580841d504043c001c030042c2ca000204954400c0412801e40c1c407019a4151142101c0d802000108001031081d200c200007011300c074000005a03200c28000c00c20382820402c1c18800d40e0981000d000524541c41c3c0f2040c1c0d1051001a00f000704411134000c80481c01f0907000750840c41d0201d16038001035450303252080c140e5000304403903154a4411400c810120784903500901c00c0d22080e00995031228608841c030f0001101079400038000400b41d48041100181d4824540c803000214130724030072440300d5400c040c1031400a8040181c4010310038034042110442c3c0c2d03a00320052405030888881c08078216a5582340d00740c010819140200524001c0d1185400c040e0301078110130700c851400b182e00b00120328280140e0f22141d81c02e07800c02070920340714400070a00c641c01030058031503106220003100e4900741200042801c1e84c0040d0300c4440416010003140b010560144504078595030b081c0381800950b8540030001780045040b920003030034807800241203481c00d4018881c54680680240c1419500d0b410b003040d4503501c0310341c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 393335467 1250 393334217 393334241
    0x702100e1809030301120f0b1e0106030216020d05011b030509011518050402150d02090a1232010207050c0a050604060f0521040b06090903090901180608070801 70
    0x1038208a501c0711000c410454018000d000040d030440c0c1c202103c1241916403524240ca1610f281c211342e80004a00446052051003560344140e001001560440d81c0c012044e007142c001c0c1401840140404241800311040003a0103d8001c1e0040e6490b040084c0101400c242104c84107640c140000381450f01508120b0140103010002c00c10b40c100c0b403424902c8001c06008226407e0100e102d48812001540c101a8009000511020343d038105e41d40c88411590142c0e0300040c03100c0e0003003800c0b51145800041040200040e240510301d0034140c0d034401c0e201d4141030b041e02e01d44d1034410400300030040100d85c1ca407400502d514000c5640f10214144130344d44104010009200d0b41a896000c51681050400d0b40c0444441d5243d0003005142002c05480d950020cd40210484a4602102000080d00b000d01402107000c0c2401c1e1609042480c18064520001080180341d41c4c800c0114141580300c0d00e04a03411601c5003840501049880c025450140001c2d80c04801c2503c1a864045100d0030190700001c94106 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 393336717 1250 393335467 393335479
    0xe010903020601080c0306010905041106030a1e05040206031305030d0e0609010615090902090f0a0303030203190605100c0204020f0406080702210d050a060e1302120f0601030213020702100e 83
    0x1307a580c0c0039a9491505000c0e01d905508040c004210052140c1c110580040c401c054070000d102801000c03e10503001250480755550b02c4510780d10300e044003641c0f41e090f0300c0242e503014049442c041c0c01007070352803001070588a00d13214a0074590b4180142481038440d40d54103084280700b48405000c41940d602ca00b0f8a50b400ca135482e050001030003445a02007850f905a1a0700c07402c00080c82d1980900c0290070a8480031740000f5940c1c0c1600c19540c5c1d00c5040341c09035110b928010384a0904000c07424082e40b00c150b24248030f0380341010920156480d200781008807215441c18000d900414404140a8050306a41c40d01c0b6580216020400715080301c80584240a01d900b200e10035030303410585c41320801148400800c00c40007081401a20002034000e10390201c01243c1c00308055984000000101ca41118821140b1268003060000c628254840080010042c402000b5100040c03900302e4817a0810700c002032240c1c2595010840400c03258056031441a0000c004042d941000d51000c1c21280042003441d100749 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 393337967 1250 393336717 393336719
    0xd120c08030c09132c0703051f0c210906110f071529030309030a06060602012f03040c030c030606030308090607080f0915150301060e13060213090e010903020601 71
    0x1019030310440c010b00e5000403116070101c0000000c5d141c042d0700d0440704d640c1c0d03005003240800071941c20012000040304022120243d007a00c03040b590220340ca800a65803c02c0701d244845007a40b03420191040841d110500c2c00259801d1500c0d290000b4401d14039401c040344ac3c08901100c442c100300001d4a02e15018492180907500c140001504450b0480700403556200004c0d52140d140100700d014250307800014007180c2c6801c95100000b890405100c004450701515820140038184c1d081c000d5103034100c01200780c03925030801c071001d048190510804903402c1c050040001424030a07a80103100083d85c203c1030511000340c5a080102c0500810301007034001c10901c0010071551000012a10700c25403540d0355050341030315550b2018141c400080c103000400c3c810303074034a0f60788a20761070300c44d44c00340002405042c0020089001d00d8291200c6510490b082c00c00d0314100700e000d9650a0441a000e80d11140060740c17080340c1d04600f4400c00c0c0030340049100306c0c5000400d1803181015409031205070300a4080360466 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 393339217 1250 393337967 393337999
    0x3090a060c0c0308070f0213060807170a060b040929071403070e120106060206090706020604260d020c0c151e07080c15010303090b090d120c08030c09 66
    0x32203091200501d0036206550400101d031120000d1702c0818400c030480840d1000721703000900e42411104010881540e641d03800c10441004106010003401c842c021004000c031240c6800b92030300355518001d4129030319403c1c4840e85907100d62100d00555406980e0309800c01c0e0030031540c01c1800589140304410b6aa440100700102e009260b001d071500004902c50749107a076110003c0380c101c001c602010f41c0002e2102c0e4550f009400030301034400640307110360051002d80381840c880c0d80740c40361a5100c2800d5400150500001c07a0481104c1c2c0e03ea50b04100100e001000c030341c2d002c0070041c03003054803d403a078a1003c2000c4140700d02c0800c66080c0c4480448100c184480d10840c070b40b400e4030864014250031282c0c3c044843c130700b40000000e040d1a07406502010b04090720802c0320f80c00c1c2842040c40170301e03c110460040c801c2540080e03c00024290a5410604000145000c103284000210014003213085141030044540e2003580c0185d0380315804146107440b41003940e9000d0007a04800e5081f0700c510b03414104054a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 393340467 1250 393339217 393339227
    0x503040308092a01030f0501080307060524220c0f02010b04290402040909030e01020d0903030f110f0f0c01110f0705041e0203010803090907170c0a02031b03090a06 72
    0x90502401001804120f11440d0411091129850641416242c002140e1282c0051003654001c001c45005984d5071840342c80c1100072550300038003180c2d40705000c03100c1c1181c0c2c1d080416040f110107001d454880d80340d25003045444c03660b1a003d540605003801c00b51390f69122584a401800503540c0d94000b840424214804c1105a54441e12504c1401824210386100a245144070760002e001c040c000500c0d0944401c1c2e06019a00040819004100c2c80302c902c2280e03590400c8801030340300241c0b030071000290071a50000c100d003204020782c100b001030f4003581301c403008170611042056003084422070749480203810349691120a10b821041c08512030305096501050085803140b00504100c0160499504100801c40140b0000c00c882140e089030710101c880580a034070086002c0c1001e24001e40e111581c120801c0321290008165030308101080d43c0c0000084c961400780c60f006900051129182c4000010480c45c60041c040007480024481401d00000440800102842002610480780e159180c90050b50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 393341717 1250 393340467 393340483
    0x304060915020d03110f13050a060801120f080f0d05070e030a110d11030307200d020d03080403050d090f0c08030406020303070f03020f04231507030318080703050304030809 76
    0x40980c00002d0500120340c80b17079000c0312a2580d041a0b01d03080032802d4011000980140024120180c0c0124080c052480c2151031b15004111501e044a015818000323594013071496800c0060200c06080010410009043e003036685001842a0003600c0c1d000c8107840c100940030130340d100c5022803601f501d144a01c0c14089102e18a15410800c4200b04005003001c2c4441d800c1c038400c09591841a1241c03200296600f1702c0202405805040182203281804401a8020b0384494039544540045844500103072100d902d201055038160903c10740703960342c80c00e040d500d9100d09419480c000b458002e6510421042c0c807512880c481c0a0322380e0a802c0703512003412a60321701c102e002d0350000d81d00c00e10008448603c117100b440502e01c0b491401604041e5440c0c0f4941c41b540040e08040c01012914011843c21800003201c40701d00c56080f16641810311000080c0d461070f00c20b9020280c101912280f21070804e080100107501869800800c80741e6604c03c9003402441a001960100c00084485000c1a10007900140c084 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 393342967 1250 393341717 393341759
    0x1e01060b160c1520070902031f06030612020907140a052203020d02060313050607080108010c090b0306010509150c0610120206030112030315060e1215010905041502030903040609 78
    0x30018500c1361070350543c00d2005049812481c410340c080401c0306d403118000755000340c5034a0900d80f000c080700b20700d020358001d0f00c0d0003c1c020149006001c0190907210b11400f0241c64041d00d48201070303100e5078411a0100c40340c0d0710001403030171f0001d401c2b82840e40c8040100107020a0411251958002440d00708a60340702c1e20000e540728603102402d81c050702e4030600841d044001c00c1401c3d1300207625580c4a50410500f10307140c0021031000001040488800c0c020f908404501e0716008150340d042c0f00c0a44034501015000e641040000f241440e000c1c1c030f0f0080c109150300c40912295485a50b000011580d4500490380d20040e1704500c540054148041400c0200c03156000f422941140e0800314021840c10040100381e04058980768032044803211051500041d0401e5074a1010001402d070a000d8010000c081004036507010705000350350306082c40361144c10345071350410102e21601c1c0c4c1c0c1041090803100c6685501d89903c00000e11040920005c0200121021900c4182215030380f00350704003900504a100b2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 393344217 1250 393342967 393342977
    0x1f0f02070c14030a050601030f15150905071110092f0108190504050a020901140f0d051c03022221050717030414030f1e01060b160c15 59
    0x148030b110004052400c42e480c0240449901009684820346011020303071003030360a05d111414440c10320803900c08595404d262458103010400b407000c0c02a0560400d4401d581e0305030355410118100340e1290080340c1c5c082100c10100d50015010520740c00042084001c00c441082c552204812901458050f11120101c0801202460340350b200055400100082844102030405042803030b096815220b00c6020310301440c000c01c0135180d54410f101c40060103070080d038145800c1440329041603079601c28405007054107031034003604529213184c243d1030580c0303110340541130b0242c42012a600c81d0b416400b070512100b1800c940328061080081c48032100c0847d004039034801c521718201813030003240c401a10324040d21031821100b1640e901c04840b220901541e405d10a15000000d04010b04840c03100c455074400000c5000d494a146103c4d00f040c2d440080100317240e210204442100c1090f0429030021006111084050381d1301c1d00054561030b17501940150403079089910b003101180704450742010b1400200c142e101d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 393345323 1106 393344217 393344219
    0x3071e050a080f1b1b072301080f0103140a05190b1005010207051009240305091b06090f0628050f0304030509040e1f0f02070c 56
    0x142d540c0011203401030012041d103490516090030313520683c02c0c2c3d85880d0306003512204001400c40603610301440c000010032041c1e4a007251403006d04000c01102440c1c044005545103403054441c00d210303c032000010b1001680c414585230028144004450140416548852801d4680352039921140c0b13040320044208110749070f10b0368110b10031906518145082100007551000b851244a100e0342d242d442c48455640600181c0010388000c015091031000da03621582072170800202c1e404002460000080c444040120300c4c894030352070000e103001c06c0c5131401c800c104450b041201825488241a0710745802a0707640001486098501c0044944000340890307a1540c000c400c43c2d00c00180030b400c100c00c1c840700b0581c004596000f645410320644891075031001c1001801c1d0544054540d1160704203980c4004402c1a03071140c0c07850203000034080c0502103021031081c0d000340d00c4010890814414 = true := by decide +kernel

theorem cover : BRFrame.Cov 393165467 393345323 := by
  have h0 := BRFrame.cov_init 393165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 393165467 ≤ n) (h2 : n < 393345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
