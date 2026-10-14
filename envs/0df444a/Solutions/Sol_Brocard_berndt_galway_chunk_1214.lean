-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1214
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:48:14.945123+00:00
-- url     : https://prove2.me/submissions/bb816282-6ae1-4ed3-8091-5bd4a1801a86

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 218165467 ≤ n < 218345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 218166717 1250 218165467 218165489
    0x1404080307020118050d03020a05102a12020f2d0406030207050a020303040b030a06120b04030f0e10090906140904080c0c0d03080403020618060c160c0f0320130e0c0307 74
    0x3c00ad017040e904000d907a9401e054080d24181203a1442c1d00700c06405ca00c5401484100d4100400300c0ca403e4501c001c100c65881c032400d100240d20440800402c010340200000c00d0380d107a81030709100c03c000500c1c02200840e202400e07814403040220a100b9002042081d10900a492000708541d01091854019402804003c00044200510382c0350a101d441c0c0100382a40d145d10a160300e644403030441440c050320107000c0014079413803007403118010050b00352090405809401ca090092000030540a118000c62202070b0400c40006040c07682c1d500d032007140050007846110755840316030343c0380d50b0b5500080d02003000d4060740302e04131443c1d501c6560700f02c1503602945a140051400f0f1030002e00b8080010480b00820b0500e20708103020901c0000e245922844c0040025500c5001060007250540064401040c802185034042011801a0130345c0c021244122180c03800241c440244419082c0020000c580101c8004004080e103500303500211110100c090036a443c00c913010021a007401910303002282a80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 218167967 1250 218166717 218166733
    0x30d030903080901090b0103060b0609100e120303100909021203070606050406060f2109080c01060e090d0e090406061205010b01020f1515030f0615011404080307020118050d0302 78
    0x1580299480750f00107020030080014451a41c1c4000d400e0f5810b0201401c60b580c0ca070b101840c1d0f0b132617000480e1840d100042030707140006221440204103a0704400d51600904c3c1120030392a04400000550340100c084800800d1000d01348240c9100411604800303a80c00240146400c18008050004004040c0180404030324107003032a0901081e51441ea00c01810410031200300c012a550216a140004005040b00400343c000c0528400181541c4040030b070100302d00240c00c54400105500c100103c0780c1840c0040115990711111644903050400c1e4000481c07000040c1035500d16240844980c031a110789000626180c407540c7c4030741104079201c011955a1b40d5140c4840c0c0c03540e010408034408128250041c0300344a403000700d1000440002c1c007a14001500401aa05142d80c01c0c061221050b10700b01c121041c0e45810740000d425101d0107851300b0f010400710040000c000402d00308503019280004010b502c0c10b402a40111180c2e4482c08070b419106168201c042a26a10544030855843c00f0354010702000b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 218169217 1250 218167967 218167973
    0xc07170408011b0203090d060f020f1c110304060c03290a0504020a44010905060d0c180b0301020a030f1a03120c011803030c0e030d05040909030203040302030d0309 72
    0x10340310403180180c85441030b80d001072103c1d400170485220007000d4510100704c20151034100c0242050b14403002c1594000307e1135026031203404019040b401141600c02c15580c05102c0e00c00201c6410b0400c1e01c000980c02c1000902123880c80c0c0201d2200d0b131851600140c02180414000c00d5025030803070340b01981da42d07020707820340754a40034510b0304c05080d088138114904111a14040d044080038401c01c10112803095524200f0b051400c01c1041d02c2c20b0030900c180003850101c0c94180248000d0041d0102103141c10b0100380e80c0d060480c000c507440c0764450340c00714010342080081c803d503031850f135100c81265880780c0c1c4461054074280090f160005140e200415405868003070310040d5114260385120201c003580c50030b5142c2d540010320f0100280b4156070385035100804c042250150035000045c036040b1000d02ca040b01010703416400211000090baa840c2c416600c1d1101309501d8034800525040042c50500c01800304a6031540b140501030321900460b45055581d5010909018000303e840c0d010a82d80c0821000b8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 218170467 1250 218169217 218169221
    0xb0301060f020c09160f0206070230040b090312071101050c16150905040902060f03070203070803130c0603090f0b070504091d0613050a03050d060302030f010c030b06070302060f0c0717040801 84
    0xa2041c11f002619992038104002941c40404a0152406660481c4015199045e021600c1e4403203c44109a17950341e0703110141944180d120641440c0280721b24115170312181500b0b41034840c1941d0052000c00c400220200450b0700d900240c01c0c0310180e020707a82007040c880101c140024020882e40603003070007044045101034421a03440d404140280e00b400e0090005a5440c03040305c4405003001c40b1180c0301c0d143c4041c101c1c61800344010040410301c0000038086218251071120050a128041c40e021181e201c1c042107007942c1350004010a100e10301c1d4007040004500175005940300d2600d15203d400c1c0781d0340700c05034410707151003840101c0c0000001441414094090080c1640408017a0000c0755108040e0b4490b680c8003e001c00207400c200000c81c4800041c4030540042004540040440301c10080d103900c5503000303126802c0c001c0007003841e00d510301c2036a0501c04181c90340c4e103406401078200c2c0d560305c00698002480090802c00b03040c00400c94000050301c904107050446a40451003511203052480f01d80c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 218171717 1250 218170467 218170487
    0x3240e010b09090c01080a05180304090603050d0c0807020f360c04050a0e10050a0e060102011401050f0d08160506010e0108012c0a0c090b0901050402040b0301060f020c0916 76
    0x1605800c601e19004d0310303903041742400d600103140d168002855510741d085034014080c02060780580740000980062192102d8004406032801030043d9042000602010344002e044141d00500ca5841130200001528000030b07414580000900320115410311924600301a0500540600180780c41540c101c810380d00d00402507601100407000c041c985418000001c42003241482440e0b442959031740050070904e414610351004040c00360400180d00d0b00c45000d038510040403a12503005600c1c088080580382030303210b1410304a81e400f61101c20a081480c00b400b0035a0b5004006486814040100120038158441101d00c41c038000c030090301c200e504004961441e10340683c030208490b03040c0034400307440c901d80c00d00300031030807004900342100105400700b07031810040f01e140302510700000c0c507900142d1203016030002ca000c00401c5409200c182e0b219030403c001c0b0b0180d070095a040310130900041c007509000b589465602c802c07500460303102c4010100051052203040f81c0b140602030300da031052207034076030440b903400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 218172967 1250 218171717 218171731
    0xb07050f030429030105030a0b1012060501081603080a0f03090c0803030105010813020609040b0d060614040b01020a0c05010521010b041404021611010c050609030304050708150103240e010b09 84
    0x9107135503d40400281d550340b68450103000a0300e44004a0160b001182024008101d00f0382d03e00740c1c1ca00d8504000300140802d02c07501d046800785458180c0009518006881541e0303019076460b081a0000070b04460724130b4030b1100c16040c1540ca4201e0400b040ca208a00300c000c000705070040d65131350705204c0010108503002e0301e40320854586100c034030010382d10107095402c3c0350b5040e1800500712380c0820019008602e214005403105281c04400b00d00b02042282d00d811042c0140c0341072104c40180401241e40740a6202d000d480242000400d0060750300c21001480c10030201c0140c00d140310710400b868a00c454081e40500d41c54070b400141001562400c8541c940207410445003141084804441c102d6014140000105200c0c2c0724862806a44e011710384134202d40340c01208842003880c015140e1a544c1d17205490540b80e81c410341c1f030000b5143c4000030748103800c04c0480b0500c150b2a4a1036550b14003c00b290881c04003000401e2040003407080e983d00c103060919856074008640100301d2818443c2c80d1502a00d02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 218174217 1250 218172967 218173049
    0xf03040e0402040c0c0605070207090b010905060f0f040308120403080106050c06040b0601030e070602060603070801051b03070e040e0c2e0c0503070f03020f07060e0a0b07050f0304 79
    0xc021210219164030350064058030045200a8200e00484240c105044010241e40c605018052641d6001130380300705456070341d40d04201d13511405d0015104a1518800d01d544804100715601030512028003900a406040c1c600300d003429240c0c2d42c0c1541542042c0320007804400c4042c200302c180360703002003200d00419143c2000352a01101c092225100c08004201078251540720380810389a9110b90b103d107140c220340c441034844054035550003d407110003ea505510903c26050003056088041c072515000d0514119245103102810700540100d80000b81708806200d03410000040315110ba02072440d0071010a07000e001c01000e0b040400109841c511040e4540d0803e00c22880702107a01e1500e000082c2e000b904016440101501c2c28a01d03603c030b640341c000c1c03001001021103400c1580000340c0d4021103194105030b814140d1156012038455009001c0940d01000342e4004020484001009240560080b000c0c1c484080076131000038030b50360040d4003041000090380f440700c4105244d90044081031001e0114 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 218175467 1250 218174217 218174219
    0xa02031c05061003090c050402030901060e0108010b1f1b03080612010908040605090a03080a2c010c02090c1909150806030703021210050103300c0308070201110412050f0304 76
    0x206495180b400003c1d000d140d901c0ca0003105106d0141a90001041c0041007950749140201c1c4075406840d0358454003100740d1908001003a80e0806004031890036001070070414481003003c1141c0c46456200140030123202c2c400e480c651210800c0050001c09600a4403180e0441c1401824850543c042c20507a4245903d088965800517684504070707030446180f850b000d901c1d0001640051005c1c1e80550004000020015504000b1034000d400f02c2e0700c401c00c41450648580d159640c0e009180303882100d0a0008840c41d0f40c0b1b070300500d0107400e01781e08124601c000500301504070001010300030011301030402191180340f040060038101c54a294000ea06440c01c060b031401d04601095455100d030000034411002001441d01404081141c3d034404144000180519656400c000003606d9580ca6a900d800c03440848441c010301c0c405000d21000b001c5030351200540081508e0403109901b01600d44401c40d500c0d9804d02c0e03ca8038807040980050443c281f41c5064407002842e140f0300c0c010420411000030741043c84 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 218176717 1250 218175467 218175469
    0x3040608010608160e030115120c060507081c020c0a0501150f1a0a02010e190303060e06010c060905030d0e0c13050c030c0d060f0e04060518030d1d030a02031c0506 72
    0x40d2114004d0107030b0030007413440701200b0006070242844080e08074101910000c0040c00102141092142c103000316410f42c081603c4840495a07031144020242043d0001c01a42d68110b00140a403100c03040c01810041c2486111540d407130500503280b00a0b40c880c1c1d120302501c03000c1c03000d524000c4020300d1045d45e01450345182900000303442200c0d800b034030908180882d4050704e8600070742003d1040c0020a040d102d1708910684e410300342d522001c0c02940000d203042004140c2421400b80a800b4100507103c000b81126140d5070038000e005103500482c5c40380414040c2d4504105540a003455500e10308000d4111603060381c06100d0b03120030080b4000f920307074184000d1042c0d29811100300c039000708002010b1340c0d0302c462101c402c4003d01f50650061405501508001460314800e2040b1402a44508400d010684036a18024911035201c0c0162545800801c0716003800c2c4092791102d444d1114251a10041800b100d480500b15000800c4100c003507000003071003805030004941d80da001c400c2d001004128a04107e8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 218177967 1250 218176717 218176741
    0x714030c2b08090307020d0c09062c071106010b0702030c0a030c03140102040f060c03020f0d0806010315090e160608010e01060c030201021e0c0714090f0601120e03040608010608 78
    0x41100c6040c040b1080100740c180500784111000a500a00364643c8280381d854880c1e00c01d176840c807943e0901460b0180205a0900d202c1d40c0103100140d181600700c9100c036101c1007a0380e410300903004074240b01044044400c1c4180034490b0314000c2a00c0840c5a448001d07c1c014182030580492005201c1c4284020038000200403002840940760401d240c0421340f20307251030550081c881ca4002800da2034240800064045c0c2c090340101c1014460303400d0b40c01e5040340c0c000940d645d04c480484103000c0755800b00000e245500c640d02c00d8000a41201c00d00c1c640036510980d88044a20180040700c2e190448042c0350f001c001c0c00305c401030007459185090152980b40c51001e000028041c0500400c0198034802c02c420315200b5019140c55103101d0301c809602015216550101d036008800e01c541c3d5000d201c00004481c0f0007810b20b004501c0e070140c042c210fa40da9001100c80400030080c01d0b241442040310400c00c81c030120388900948060101c004554035428040082c01c001016404401000194420054256444 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 218179217 1250 218177967 218178043
    0x32706270c1f03180c09050408121f05060304170f0904020408010209330f07020913050d020f03070f030507050706030504060b0901050117043315230103020714030c 72
    0x400700240548230380c500204140306510108007084180303424440c01c0c5c3d00328082c079940400484c011070b140c03039038440c18441395000445c0c2c003501d034001c4d42e0307060118090008001c2114410a42881c1d00d0803854100082c00c0780c110780c00044243c3c1d404070745061103003811140340080d02c0103600c0c0d40240510301d41641e141900911300000c00c90340013090b2180340504210641b119240d0041c00045540307090840064408804101642d0510840c40f2001e003260002c0b40c2001c0c507012440282d03281c0a51512409100c12020404408101c41000ba00010401c04e1000b10058041c50303801040504260403c0f500351040700513010303c650a1080100150780c1c00c41070400d18030f5a00c07204807101d5629414000c508040c0c81e40d01580c0b0743c201c410707151190f41c1440364002100c000340300200100491814151060b00d22806a0281d10341070710003406100c0203051110542c5c8005143c0940f40c0400c030f555031071000c080c481804905510100340501d500d501800001450383c2c0c0302c01c600c4108a40684e4201c541088 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 218180467 1250 218179217 218179229
    0x409200f0a03230a0c05130618031707120807090e041113020a090f0501050913180c03020102061e0a090606050402032706270c1f03180c 60
    0x10008408480c14000e400c0f000103c100d4000c0e80220074803912101c14400300884090100500c0c011103150854080e400303840031400310b041168442420034006485024161040315002c264880c1c0010000700700ba042020003c112000752510703584585030040c2c2c1c10302401000001d01c07440744204650582d100c1c0902c422280103040708046603c1d40e00341140c1e81074420b01500c3c0c0200c1e0b400440c03030624400343c000700301303001d02a40d4090340c450340da500c0ca0080b10708501034240042d60800c44000c5900d80094000c04508040c40005040800300001c10b086080d6190115090700c1c402c5010000d41d078050014640c40b064088621820745142414150b151070010316465026607600c4e00d080901602d5403090300a0a8064400c6503a81000d032403082c4010800100581a500c1e540300241c2d00790300209805028400700d442910502e4a00b980c030300342024401400c8031051041d000c215400307070b96240c41d2180031400c40c00440302d01030094600070f0603503580f0b510702241038070700c0c0d01c6120001e01101d010004540b9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 218181717 1250 218180467 218180497
    0x42a0f08040512030604020c0109200402090a0902030711010c0e01080a05070e21100207110102030a05070303180b0403080403030f020a050f0903012306180c1605030c0f03040920 78
    0x75402c00000d0080c02640000090b662a0440c018200035032520a200c0141004004525030102c1074104400d3b03201c0d504465800a10f0b80e4002c0042010b990091500843c1a041c40084600c02d124403900310b542103840b41e000200c1e400601c940035600104455005080514144660b02d08224080c1c101003807481030f45d004401d0031040303000100740742640394143c0d002102541d1510500042c104081d4209100564034080200d03103d17001c070b60001023252810255912001e0520a040d142074008086194a059150302104000e10001d40c1000b01a4400d911a4503089090700345070400500b120300148040d20881c0c070402c90468156042020f4907441031900c2c03070050ba20750042000c240580340051481c0750661140c2c8100c40091a50f0f44403a1080ca800e03602102c80303e112452151442a041c2c0300040300c1e100402940e101c081b0390303003d0011003a0280c41124608804038181e5460122140a500d80d83c1e00b01240c2404500b85900a580b02000700f50080c08071411709402c0c00344144203104190030306013 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 218182967 1250 218181717 218181721
    0x1030f020301260708070618090e060a150e04080a110f07050d080c070b041d0f16021e010b090f04021503070c051b090f0c0a0c02042a0f0804051203 65
    0x1083c10424100070780340c090103489265554000c064200302030094080c4440305050f101103613400691044c80292001d88000340300584581001c01e005203900d010040160040b007401080e90124030100f14000c0c2d00c01c0354400d44d1582e0150004204c500050f2410000350403146100b203400000040d45c0d03040d20b004a45810307080c03d0074900070b040d52080c41040b10203030044a500280c064501c0014100720b90000c0040c1120020759444d0425854049804100540c407680204810070a09040728400c2c500701e004030b80700048881303002c608880048a070401d032a911002ca40699041c03089990b0b800080400341601941050b0340010410205000003440b50100070000903003182c0b0401c00802500d4002c4152003904903413008984d0200c103a8a01305003d03560440c00b08402e030384c0c1158158030440c103041d0305d94100111080101d849021864060764003948484003010180a4500d5180301702a10407015000a00381d07030006803110b440792005200784080107082102042d40412032042c0d124860703030f01319074035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 218184217 1250 218182967 218183039
    0x61e021e07030b040b01030506010e0106050403061a09041b080703050618070e090109030e030c0d020f0a1a0c0706050304080301060c0305040e101a0418020d180501020901030f020301 80
    0x200c6907035403015000740c5a03c0b00340702c103008040a0060503a8015816078416030303250b6100703a8803501c0030320407000010b1303003000100081600d81d0300402d10410345400f6583c0404646000515004041d50107840c801004a02520360744200d035030b040d004203904006403061a10719112a5250000240a032903014102c416840c9542e00c180700c0722010b440c00000a44030b508140c402c540c0207001d04482100869003041030f50306c41e880c0c00a88010707480340c0140b0f0305d00ca0035010f60034440b1580340d00e514640c200d80c48400210300c1c2c152031800e5201c011401040b0035122005112103c0c5007200c01d070303ca481845030030001c0c032003c2031030316081f80d05585150034811406061850201c6076485107910090380c0ca40c8841c14801400040607030b0f141210240742100d0070070b2084001498061280d8030802c100034a000c1411000841d040c0c010706034000c1c89000c0014052140c1c00c03030041c0701c03000300d90859a90b5400500c1e80032030360b0144582075005041000440c219810032542200500850f10040000c807030b48120380520f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 218185467 1250 218184217 218184223
    0x2016030602180603090a021017060d030203090307061206142409060d050a0605060f0406080627010e1308030403050c1204060903150903200102070602070c061e021e 72
    0xb110010341880d40c0e0386400954140c4490a44d036040344107040404050140c64425520122a280c0035a40410350b41c503007204020700c2d0002400c0c12015404180f008401c03030340e000e1100e68020611501d0300400442c111004a0440e403017500310742c0041c0c2e02104081c480f80c031803400d10901d8090303400c070219410510000c122094040c01201c0c9074000000511418811416003100e4050700101d0401d001e1030b07880d542009030138003503080e448a1300d140601040121920804980f40c011101a01200303402c5041c614885014411282112510780200b00400102c2e80740800c60b548025444075905004c401380d60384070032a100c0900090100305000c0f0b2000059078007032016525050710070811950f1240c0d104405045110300d032006035140c003001c0b0f105824150460007640356aa41c1580d60b44500c1c84640b0203849442d4003803041d400699400c2c0102d10020700d10384000c00905e4000d0907a60003580c1b801c00000c0402d210307010981d07030b03030007514801d4404181c000a0303c80c2c4404050940c2200701c02c4040e552b40c6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 218186717 1250 218185467 218185507
    0x30518031207140706020615190b19050c03070201030c020316151a10030c180612050106170a0b1503040f02030607020d1d040204090c2016030602 64
    0x549801041e001a050803020001000384038440c00001c603000007403240640d00c1c1e55940c801d007000350704120006125a00e1001002c0c6803601c0043c080221004d910045103003003e906e81042c94031490004118440f44801140f200800240c0c1c58540c1c0391901444070540c07070340101640207040c5602ca07a60a0300c41ca00a2050700c0300060300303400018a204103800d01081080c21000780301d0300c1c5444c0042c40620180b410314440041c48018100003032480050500302c00034407507001210104140d6080221040d24a038401a009142966440030382002e030a07282d00444006034040018409009000c8400031f00c199106a0301c90540c0c100012180c18040100c0e803048074a061032607094200004010400036070610250b03e6600940032650310b5601c4020691703a900d00101d03200c1c041500d006440a02044204448400f024050005414141e4811180c8182e80c1c0d840700c00382c003042c19003202440d1b0601c4602d44883c01e1000d040180004203414110030801034046c00040c100c01c0e000a82c91680302d07200d00c0d480c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 218187967 1250 218186717 218186719
    0xc0504080607020a030810060c080a0512040302010504110d021315050301060e1b040509040b04050a02040f0c020c01020304291201080607090b070b06010c0309030b100602060c0313030518 82
    0x1e00d01d45008000251a041c00003001c80c081114800800c41c000320503144041614469111120300c0c0c250703034846040d5608048040b400700310701000a007400c8203403092210b001da4441e80022840d41841e25100c1301018002d03c0300d9014103544124800503a44410f034542c40890440000151010001c00a61041d42c89410194140d82825000180003484000080c030406500f101207042d8000340320b0700741040c4910704c1303241c0e80400304202240106003140d03070b02074009100d0002c9480d8541c0307590200f03095404d410510b0403e10b035107452440103144c06000142d2070403800d2014501e840d09100900e140d00705500c000c1144010001010034500a610342150682050b1a107100d60a40e91111926038a40d41110b00d800010380102001500c02009800d450328a9480030212407140d0310785004681c0980340e02070980410a074800000041000d400c00a4000c080c04904104854201407001e803a212024102c1303541c1c60300070400c01001000440710b00041540c50b19041c4e07664141f941302c50780d80e004010010307 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 218189217 1250 218187967 218187973
    0x10b03070b0c0f03090102071703041e140f010f030c111203060a14010e0f24031e22030908070602010204090b030c030a14030706090f02010e1903060c050408 69
    0x45a800d10035000b904001c05010125092040c81d07004651312401101c04880c09031b44140d03410b026000b80c030fa0261061400a9089906040c1d032405000310007624a444007c64143c800b109004061090b4050800140c050f110800c41d0381480c0002807014a0100b04a03003010f6495081842081c82540d04150f0780c4541c070211618108805a0000d4551042e2426813083d406400300084540b02e004c0031054001c8142c50704081c03d050304e070511141603201e101095000c0401d04c0520800041a0003c6d000314800d080c6c9076440c0d2410020000c141d00ca04040c41d400d04041904102512802c01400c2440a0849801c151b0400d4107244c16203c520098010402c14000d0040c00b02c0c0c116415400340049541410702444003003c40c50a041e21030041205898243d0450b07080003022030540690301030710b0183c1c441200c1c90290300d9100c0700100c3e81000c10440380c0c86248101003056603130001c2007070401e40e02180d51001d6241880081031961400c3e110080030340783c0ba0555005824021019280240030f5403040e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 218190467 1250 218189217 218189219
    0x10b0402030f01140a0602030d050a0902060c070f06110307060e030f0a0c0b0a0504050c01180902070f02090a020c030a0e0a0317090a06031803110106080328050f0304060509010b0307 80
    0x882c9221800074024032003018a210b00b844036902d4211820002c841b42c54004c0c6d031801c8940304041b0040c1c0b200822862049482d0381c10700d030041c0c5900000349410b4a80b000503040c2542840c010041c600c00c0783c0d1000c0f0402030719014444618001004440c9150340c081c01c0002c1030161041803500307500407010540703d075940100300046034942018040100f144a004840d03420360f074036400c6d0030460f8025240904a0f601900c022a0594007030700301c0e5847c81000c0341c1e0b800d2216070b5a0240310140d07444000304803200d540c1d48040e070b021800c1c24491203400540301d21056082504214905903a030203202c0709807041080e01c1c2180e01d4a5111030750500007030344d00258214249208030214512030351041e401d06000d20f203103c00005a11f80f2901c144910015403107042000480c2c25242114110140700d0350902d6035585001c00200044100010581490a99041d0040b9000380c480078204100c440208800d1110801c174000b81c1c900d40c0e8007243c0e4441d62140300000d46403594085540140001a191501840b81c004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 218191717 1250 218190467 218190481
    0x2030c0a1407330617060907030f02060f12131b15050d0e1c020708010b061b160806090d171314030d02210f0a0c02010b040203 56
    0x80500c400c581d01c858111074038024021505116082c80038100840c0410b00f03ca5a04295640e0303020b4a014515450107551061481d40c1184d03c1680038030780141d8000d44036100300c501403001982c4044d5800c0a00503007441c41c0c80701440000310790402481060006200040105000c0944e00300f043e241140006524001c2003580408031301c50070640f12400d5216030b031031740e5101c40d0000400f69004080c8200566144280c246c426400626000c034055880364607020079413000b04809440d8081c03c2c205241c22034200c40020781402d00130b41000c3c00726410043d02601d40d44400003141c481d60703160382c20000000552a011400c020070010354445042003a00300090285000a02c00d01491001003541d1070b16029500c146d96515006842141c00001d03000010481501c040000c1c80e80750042d010341d00703200520407400d800e650120030b000c1d50780c90b40400c0011403070340944130322006018080c0075901301d401c28403a80001d21a0003840225081e40740c41020b01d40714401e4200f40e040d040007510664581c1001c0e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 218192967 1250 218191717 218191741
    0x27070b0406020105070e120a0b090a020409060506010e090705160212010e060703060503030c120307020102070218070215151e041104081002070f0f05070e0a140606030121050106090203 81
    0x5d58881d0001d45507107240d2690f0310f454904100070a00300700c001c0a500d000f03a6100030740501c0c000c000d402140141032811700035844d079001d0201d080c2e06c44c08001609281080014150f00b0404210310f000c0d550030820085407541000c2290100c00489d110021030751050b1000413449a80b0500d030361076035400c0c80700c001482c850005030140981443e0318180301c0346480310103150f500d0060307200c070070381507448648030812661b139200c0191340042d1284000340c50940d240d000f003150903007800300d9144030042030010000c50550602030302c00d0130b52251402540e1030034881110350842556041d458401d40c08a400c101c4044a640e8000d6842840a04103000d0100e2040401c201600103228840d002c1c001e40b2207010300d0361424070031a0005503220828104021664a4070b6540700340b06038080b9280d01c0351103004a070504490384d0551280d10014008109040900c4549492400151000d8041c09081c00103211003017095940b2624584c400b00c04031198186d1f0700b03105004d0400e0b5031200030700300d00c00424884503030007035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 218194217 1250 218192967 218192971
    0x10b0315041e050c0a05011827050906040b1e07050a180801020a0e09040807140106050918010e0c0609041a061b0d02061009050402040207120306090e0627070b0406020105 75
    0x40300c00075a044c6d0368a006440070f404071041100d403d02c0c8031a051001c0b03442e02c00d810b40c6031404406c49030b03605604201c10400b129001d5800b40c05950200e410481000181c0e032641c0c5d4003002401c081c1440c40e48030703d4510b2018002030b000c2810700c2004640046003c2c802c40303c0e0845c9812010180d00801d983d40b055600075030210091100040400110440074181094210b00490b804100e440c03030030b0941d40f07810065a0f803140f100750340d40d525100e0004040d510003141e14040c2285940c6250980304940c02682101d0340c0d4400305030b003078002010740342c0c02d90782d10829103c00480580340450051001e0b5070f070215241342507203c01d40c082d2020540301c0d0648080c84001c0045584d0340111160030204031016651030508403850f030030b801c1d00d03140c040c050504541c0000c0e8005202030000740c01c1068a981c0d0751092480402c5503400a40d80b80d104000754410303030061400070b0f41208050104c1d4184204070314a85032032143c035000350b8600a0281c664820701003003034800500b07001d00368507240c07034440a000303004e840c003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 218195467 1250 218194217 218194219
    0x50106020d021f05101e05040b030a03080106031107050f0a120219031b050d030e0705010c030e060304020d080a020304090c0912020f040b120c0a08010b0315041e050c 73
    0x4080000c0e04041c000103240803005840b401d0708a901c40f4845029020303200040050030569081d9000250705011400d141a10454030000c902026051805101c11600d01758041c620991141c0c001901007604050090305560040c540414008424100055280314640c0c0042603882a0000001800c0c00410980030b0705204401545850f051104104d0f80c0d035140c40c06040d0000b44203006140007a026500090070302403d0806400030a20355101c80e82016103882d41840400e440d41d0a401c6075202c24004140642002d092400340d11440344c500518000c41e0303583c2d01c0d000f800000041070a56903000090f03040d42c0d074003c940d95074034502d1078002500e036003083c030030000246e04002a840c106401210005e055885600081c100300806408200d046644014a41d4100c0d544650300c50141c1c84001d800c040c12404003004000c0c82c0e2100081c000007924a1740018030991400d00120116600400c0f01818205010240c1c91551100c0c10b1071110a10202024206c41c074145007850100040403a0390700140030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 218196717 1250 218195467 218195473
    0xf032309040506060a021207030306150c0204060b1606020702030f1c021005011a0d060503010203010906080c0a120b07050c01150302030c0307030309090e100207050705030601091503020f0d0c030605010602 90
    0x3c0f48400c0c0106406114070f01d20250f0000444d141650708904e0180c09050300900c3c02044040c0d40c0c1414008021000c1d020000066846a0030780039070800307008002c010041c0400d080d14121994172650b0040304030fa000241802e400151440c103540d010820003129180150580f41070309030341c11f103030442c10503c201041e015000b04c000f0086034903d85d205031412550038441c1010f40d0b044610003c06103522890740d40480540e80c0300d0124003501d0900c0a036000cac1ca69900c00040d003e041c414450315141020240d680324198aa07414030003c0c0c04070f03d850600f02e034441440f01040e00c88a00c140c1d0a4060304210b07410540c030b000b204801807064240c4040c100c0e13000f078040d10f0000034100281502da0b8200d001c042c011840c400c0003080b0419180d40400030750301102c403d843c05505400c0100091f42d104841c00d56413607000e0402030080c1d245c1401001c0c0149031440c010046c40000420440f00c07800c0c940b001a01c035144c40402c078071183d114200d183d1038065102c440e01640c13503141e10300000206800e00031000144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 218197967 1250 218196717 218196721
    0x80402011205060f3007081005090705100c050d20010b030c060901090806010e0103060b010f0e0d0c032301050114010e1009030803070302030106020d0314040f0323090405 75
    0x150501c900342c0150800390921000c1c0d0304c1070003440035805001480d5182c0c001c0e40746000d003080c8150300b0310250300b42d03100c00502241858103002c0c81c94040c0707a0340c2d1142c891b883c00090142e01c800c001015421500256200149805041c04c140d03a009140031000c0c12600513050310701c0d40d542d8880240042d4507a1003000440d8400000002800ca9150b074009580552020100820380d1808034050501306005141070000076440c0c0c40b041e4144103017a40000008a4a44010b10421072240a01c0e00710190a1030003000504104c60020100c030000c14000b0b00a42031081c0000c180103000c100c2c0c101841e0018106401c1c51f02c0380002d03071402d00100e00c01e80c01d654070b020000304007518080500c00c10010165140300104900d44100a550084020301c001031020345240000051405006507200e4800c42e10010f80300e40c5030041c041d00b090003603410030080510701050444080c2c09141169082034003c0c0342c1100c400312614003a240c0103400001c900c0341c010030030304a09190b441c140003010309180a80c2e040c0969 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 218199217 1250 218197967 218197997
    0x1104081f060303021b0604120503030a0b0d0c09110f0a0509011103040501050d020c19050a030914060d05090c0418060609050108060408030417040e0115020f1903030603060c08040201 80
    0x99805000090058000f44650b000c00303045c090484c81c807a08004e00040c506130756070202403180e0340e08450460361500040100000c1041f01d01c150040c440382a0703607000316260150b807141007803440e9000d52a60f451366656800c00c144222002e0f280210320342c0d0701303d596440d0280c1000c1c010350003020f85280000e003003640d10700081c1c0780801030b5011150180c4030389052564904c00310000c0e41100c00c00280c01e12840c11810070f03070b0b200c1d80c0a081c200350050002e00300031500ba003001006003026411180202d48400070115280e2180b0044400701da154000004003600c692841d40c0c14004031004250380541440d1210103001c0c800108000e40303d1182404000c100c0d603420003101921400d105004c010b030007840020f400f1446460066030321510425a4441482d1750320300007001c80c1c019800c80c130004c0b42102c0040c04182c5050301030791000c408030300040114003481c20034507a803825141d203100d008801d283d001c401094042d8001001655200b4401d0103e0380410780010405001154140d0000b0484039200f080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 218200467 1250 218199217 218199221
    0x705010510080d030b1309030c020d0311121612020a0219210510020a052106040501080c031b150309060a0b10080c0711060316110706080412031104081f 67
    0xc8040003404201c801c04d11098050000c0401004c04c8d0240038214503406d006a0b503103c0c0c0065101c0c07007900c4000007000309051304c500d002d201e41c0d4803032100385040003418000244240c80c0543c50381c1c444d4009015000a040c128100107a2540003074014600c0491031545485448a04040d10f05507401c145c241d41416000c49130f403540050015007540c020b6035080040210540081c1401c0000c1c2c10010700d445051a24501c00c1a0f454450b403880c200b548050049030718142c003515006205400040008503641c3c000a5100c208580c01c00c10295581e50a0803a42d8a500c0c01c03d0700380c9200107070000d44901e00b50f240c50303403220700c200c542d00c403002c0c80c2011044942ca440c14900400315101c0d40c0b0b0101c240d031510303507042d140c0c0d000030010b80754052140d031200815502c8500841c85405c81203510049455113440c06000300c0200b540091090300402018010107502c000321550203074010040b451008400e2000360b0040100e03015100b000100054080f40b4807030000f1300c00088030120704004801007011401a01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 218201717 1250 218200467 218200481
    0xa060303080f04030e0a030503210105061206121b100f120f0f020a0c030914030a1113021923031302030f0105070215060405040302060402090a020705010510080d03 72
    0x4501c164011480c030100c00e41c0107036030003803090130102e40001020000416806069104403280e40c00050700f85821641c100000c0c11185038490480415410000003500704c0c022000789400024a0328009116641d0b40350f03080c08084445001d40b0310a031491205074031520700007009280130302a21100412840d204100c3c0e0802c803c002c1e560102c448060b405d440380501030000301d4600782d40c1c8a41020f881a401132000701031000650700d6895441c0c4241c039020713040441561000b40400f402d1080130b0600e44011035001d9160780e00040c007415140c1e039440010440400e020407178100c5840032400a003410911071b0000900e508640b54142d003280c5001c00700072154030103a00c0e080903050501c00b0400162010900415151004050b0f48811042d07184041c00c41301c003265034000580c490241100c0d50840d005555801540c156400d009503c0c0545000c1d6513801c020f031009004922050004080500302e41c191050315a1100c000d02c25420030f141c202c1c2220390b0310b01030070440d80520700c0c40b411010300078071a4007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 218202967 1250 218201717 218201723
    0x50a090501050121150b030d0305150108090c01030e07230315040302031803031902030a0e040908070b0c070c0303200c0f09130b130c1211090a06090504030e090a0603 73
    0xc0142c01139036942d10700241c1c107202064400d50f00c844241c0c105503418000c9540c04010759800044601d8020045411041c1c4901d8071410704c004078041c01100000881c4607003040000b8200031036030394000d0f038001d80b031700d8103d500000a1144442c00031801108010003180c82040c12000c94200003010384646032840e005850080c003580c0208035058940d00c01c080a040c03081402000d0702d09159001c00e21280b03040581142c0001604001125034a1726002454041c1c4000c082d2410813150380c99555041c2544140c070070140c103130090640080c0c07001d07001a0444c2c5801c1e41c00b4680c1031800d03aa910b0003900b1004005200a01400c0d24940c52442110004601b202144000d0210490048810034481e509402510911388405010840c00206000c411082d00511076000340e0f80e038501540c201010004210380000d99241d814009074030200d080210a000080070848120240e41c640c09a00d40080a441d032080d803469060404100506401c80450709100c081611b8801d92660340354010000c440641c0001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 218204217 1250 218202967 218203019
    0x31b01060e010f03060903050712090f080f060408090d0c03051b040506060a20030c070e06090405060a0506011701060512010801060605040b0d0e15090706051804020913050a0905010501 81
    0x100302140e45500318006c10f40c0642402c170701d4041b60b07442e811902111404032501150b0600810080d410040048500400003000030344440d0400c086120303143c0501400c00741800401003500c00941d90744040c9525000d600508a1403410364916001e074403880c22940c0c104c4208003481e0003840da81043c0c003842d4811040101614640f9051050680314060651044d0403032121b082040c3c20480402c00041c00701100d00c4004100b00380c5000c14040050380010042030062141200b0300c4006000050629088188a00c0100301556a4001207401f01c0a40005c0400500b001c400051404e030880014483c0e150316441901e06170380c0311070382c1c03d00340c031203c0c4109000281c04100401442642d00003410b41c6404100c0086010303803900496600e40028141c860004100c0182884100001001510000d2800e810060308140950b0412449130341070403512402280c00080c20b41181da030718030111146042e030701000c02190a1500d1924000c0c528140111055032804002080180d00f10312400d44001c248140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 218205467 1250 218204217 218204219
    0x108011208030702101d011b1b0f0f0b0f060117010911090405090606010f03050f06010c03020109051b010f030e030f09060d06030809100309030c060c050903031b01060e010f 76
    0x103988960b500007040c15085005640040b00c0585950181c40038481c1c54a00c5800661154032050b030844010008e009684031080c5c0303134402081c1d00804520800403c184003036100c00c215040c800c0826041c698010440c64000030244100001c40d141e00d8005c03540e13684114500d42c2d8003001035614000300500d6840f8601410010041c540d015007000b10103003421403081c1d080140c2100403c05444040e680a4032039000141042803d503031210300100e1500c003914003403006007481100f01d41003001c0030380390034100100042e000003854004d40140321280c1c0c2c8001103c06002000d240744c01016200c02c1c131280048c01d0580c0c044040d074030a005050804c40107002551909409070b1180d100d079441054001d82011091101c0c50491540b032003180000c40c02101d074582e9a44440c0d0401c900e440390316103030000b41841c2c2500000481c1d800550b01490944c040d200103017282c50950107440c140200c9035129032501c0b00291540501001004103802120040000d00005844007075401007502e0900503d041c400c076180e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 218206717 1250 218205467 218205473
    0x1f02032a0a080318010f0b0405100b030a090303090f0c06180308040506030907080714090a0204140409060b04060f0801050108010c0f050a17040317070908031c061d01080c01080112 79
    0x8002c40d0042c40c492140038804a06068131805d60381151702d6070340216542c2030488034509060199661000851034045c40c12410116800c0c0140000ba1104e1a155603074440d402c2014004c0d0b0140d03031040d4111400c40b0301c5007020b240c2614442000c0c010b400010301044100780103581c3c40c02e036072800c3d60b50240110703040a0412050180e2604002c0003034445100b40f003c00502e00205012240151400d40300004034040014107000424801601d00b0b074400384100320411181c403001811501641c001c0b00c011031a0071043c28500007400032a50542d034024a842d800190800d507418030034046230f80804c000e0056070b98034150306080f9610b440064011903014000300a0442c400d40081040082609220322034800400b81d05e1042c2008890480102d100300c440b507240b01c0c0d81c5504242d4001c4040c6401421542040740761030300c03030160040800e41114000d01d03036802951141c004002502d5056a0441da12062041e0701c00c0d8188203200c0c003840ca0280340d5041c4560351190781d5080c140c5542001258080c40195 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 218207967 1250 218206717 218206733
    0x70606150c0f0f0c061d0a050109060e040b0603090c0103240303080c13090b03100c1b0204180614090a020102070e04150f0e07141c021f02032a0a 64
    0x140115081c07003c0d002540700081107044408050710304e44e600c804841e01c211503240e030115010000d15100300080c03003040000b40c0e400010103090310400d1401c0200a040c500103e80a8240580754990001011003040030390207000030345000281003640c09000c0b01c1000c001d20054204e100c102c01e01000901d0005102090050b010b031604000c0c103a201c24940324008220710b00c00200d41d0400c8000319143e9452040e1880d0030401c40765044000b03803041140c1d030030300031010345041d4662445448208900030b0507815503440c1e600c6601802c00d5031245015500d00c1d840c0000007424803003190b800390403a5201080100c000080c180880c0e5038182c004081442c02c060b01da03460103000400c2200c25001c5510107c4889451340103580700ea007a071034400f007840c0707607491442d0b030401801d0303004800e10600210a20321581d9030303d01440c03080444428600c0b100341140c0041039110040c5410b0050610350741c0b02ca0880c5941c000010002400c80d6090343e6110301540c0700c02c4c5a00103052070401015840b070b20030940840d1010b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 218209217 1250 218207967 218207993
    0x905090c0114090d152f0a0207050f0d0203030f0901140c07051e040c0f03050c0f07020409031403180c0109080309040507030e0d08150607050d0c0602070c0b070606150c 74
    0x30f00301c00d503441700c0800b150350603942c244440f095040d600b81c1110010b42c8101010405102c0030b50707601410b290003000d0096039202907200b000c0c814583c41002c2d50b06900d56141c00d04032907402a0503284d032407404640720a030680c46210842d000403c41100650308041103020342e5103070800c1001500c010f51401e0100030113030754a030b80c29803442081c0803c0703403106c1d54941c42070711140001d0761070b02c0c4c401001101c0094100c950041803a0380c02030080007040c83c1e5500000440d0000e65040f140020902044d0030111908941d8a4542c20b0140d400410302040b58803076140325545c41011021a4002c03400d150044a0184440c490f00309154004c1c4440c3c240e0745015044503a101c500c038980010303030b80006041140341410030500140460012014040c00d4400c0300c1c100041c6080a95490740352507402d5440c0740c5e55072400724000307040007004030602c4200f08541d011030728a6500130b0608601a92503401098060380900022901c06103460b00008030600c4840b0003807094400c6403103292030510152149200d01c500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 218210467 1250 218209217 218209223
    0xa030c061e050703090215041a031e0906010812131413020406030209210307030513090f06090c080f0c07171201051c0c03080906130905090c0114090d 66
    0x210700c40c0034046000e07101d060721a000710390303010698258500501c45001070b0790880000d0400f04000602428070079034550b80c101c5485414590703807070350380240c40c0e8408030711210005c034004071300018890480800902d940c1690701d402c0c251a02c00c1291079101ea02e910400d04001c1454107a100d0800420070007030082c0c008400301800400d171408203140300740200d0384250020340105e0303400708038000b440c2061461145103489840070b40c1040c074000f80b540c036607e00950070000c1c200080000c501210b0748005502800030100484240040c81034890004042c2031b15004401013540703000d49040c1003d00c1150181d0084414020700c5143e40c868000840103948084016030300e29900c16544d0421200f014014001642926400c81481d41000c2c2009071071002c04800305110f0844107100004206d40000810840f03502114241d6a2005600810114000c9407050350700c3d52004800060100460b400003886102c0d400140e5140001072001518540c03000f415003510400c05201450403410090480002180 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 218211717 1250 218210467 218210501
    0x303090306040b0a1404021e0d140a060c0e010804110a03021306090525030504031b03030e0f1906150f12020109050f03190804050604030303021306020a030c06 70
    0x65410003203072074414252021501141c803402000080782d41c922594030082c1d90780021600908090b00060501c1e003030303071402d5a0b060307420280e0419150341c2c00040c040708903840310107159000d030319908103600c40340d589400341c502a05118096444c14400d807107013011032405869500650f10b940d2102102c0810301c411560300b14007108808400740e90b69100c82c0040c40d601400110744c030303400c040c0c445043c1e80c0c026054058100300061541144550102a5603000203245000a410741d524181101d0462007040c00c94a4640000344c0d0000741a03040d007080c0641007005040344d081c0000d8041003551201e5034030030100404c00403203100c00000c8803a0040307110035a04411009044e034540307a40c114400307010b500584540022071500e90455800c0500c5500400e0203c4104d0a650180d4011030744800d400d880d4000601045411201000394030000c0e1000f50901402c12510f554881ca0040c0080d070202d000b00d02014803070342c0000713000c5200084544000c0d80c596580e402d141215601c00c070150042c0700541402e42 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 218212967 1250 218211717 218211727
    0x6070212120712060f08030403020a05031f0504110618040b09090c04021c0e03040905010801060501080f0a06090e010209040506060309120d02090d0606230303190212070308010602070b03071b020303 87
    0x1744014a40c3c0c0074240031006150780701e00c1c600c1041003054282c1e0165001e904144040d410f1041c0c0300201e1022264150800b0401da502c0d40751200070800b4803c0c0c22580004003241c01122003040d0800d901400c6400d6604104155410b0100480c0d80400c4442e00c0071075020380303003038080c80c1041d40141900d00d2540c0c055428242c01c1d14000d1003505c0c1c0f09081f81600b0f42c4007103805c2042c498540925401480074100801c511810840001d02c2d8183c0100b5000882100c000884c4843d10076500c124010700c1422002c000d01000c188425020b540445074140c810390921022410615203401240d009001c12001001c8201e40300e0441c00705504100c0d0041c0c0d9066003030240c0620b80c2c5684d0341b95910340b807085400080241c246804c2c407a00c1e0f01c0510664019038248551040c4039200001140c5100741180c1e0b4603409161420412071030500120103c0d90b42c0741000c25038004254100d40b009041e120310782c0940d0741041d100c030802c240038001282c01d039001821941084c54800744a0700b98007001800a030030f59142c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 218214217 1250 218212967 218212979
    0xa030f091a1b0c030405042406090503070e011202040c1403010306050f0a0507140c0309041a030d020607020c041503140f0c0d03020709180c080607021212071206 71
    0x680450462200e00c500c1e14020000d900034442e030301240d200c400d80c00d442d0410720039a802903601e0040b8040c0500503a0b4912204174800b58003c02090145880034195070f081d0384420000340400e04a10072940684941d00010502010070940036040e110300003281c900c14a0b1540801c0050100c41d0030000920200215022400c0c602c400194061401804041214185103a0418240c41c004280b284503034074103001e0080b0b25512004260303140071500401d0b81c880135100100f604512804601c83e900c945003503c40075440c820b0080340707410309500700c059400c0e0064040003640c80300e030100c58442c010b03040345200c46180d01c1c0680c0420411540003810002107900e90f07813008040d203c100c1d8035001c540d0007a8002000b0380780800c07039604c40d100309603010100701100780e60180d500d682d14016800344603100c400910382d103542c0729000000c440e0007a03d140d21203a65020b105480b54030a48648006008103600109025a00c4007240c90070381802481052a0b40c800c40c080b0b45400c410000707000c0c5940c89d03a40004503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 218215467 1250 218214217 218214233
    0x40602160308070912020112050903090406120b0610050d0903052505010b0f0109090e01020f0f1e070b06011b0210020f070e0106051213050d121802060a030f09 70
    0x640344a502c1c0d107885418146009041c0e4403840d40882840f014503544000140d91000c0382c0280c0d0396414502140340e490304c2103043c4c00d44c0039110039940c001e8500f80380041c031958111000303488180190f02e40780d800c0d11104180001c40300242000804a101001700310b40340b0400e688410100c500038a003040c2408014140ba920001540360a80c03800106c2c1e41c5410140b007828404c0908901085540010209542c40041c1c040c507075500ca100c4100750b030740ea01404006029011070707680e040c132901055982c90400c50f180c0100c1e0442c12030418048642c10502c4481219401261981030700b248203c07065591304070046072600e0b041041d85200794425400d14005032100140c90901c41c4558002d08504034024281d0ba00d801c5040e403081c000103c00e100100400b94001041300c1079200e01c45210311556417140301d003868400100f2001801803040070740020809600c44160812150701c0745e0103000b01204100e007212040035024000c0d600c088200040705400d030080d8003100030302c1c000030404105010b5a80b2101c003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 218216717 1250 218215467 218215507
    0x50c070b0a050c010506040c1409010c0f1a150a050603130f0503030a0f15030201030b0d080d020301091d0d05030601090504020706020a112109040617011a040b090c03040602 76
    0xb0680c04200703640800001e010b22944814103540c1005034000030b4a000300340800d03404880074030030070000e903030901c50b441040c0c14500940c0280c00c0441d0740340e0324074040d0080340804e54401400001040030a001d2100d00c810214030400040c5200d9801d820041004031070741c00501202d084209510400001030210354aa820346030248014540341d290116900065680c1e4a9281041c50318040b410300702c0d0403084400c44141c0760280b90005040b0044004140c04920840000d000e88202144148c0c800c065600214165000e03000c0901071030420a11501e04451003491000146c0c1154136240301c6031707100d0406964070010500d000d40e00300d40e03940c02150407070340000c1e41900d4984d00003c502d9610f80d0050001e0a012107680010980000803084003c400c030540580c1d4500301c400042d8940181e0f0f1141c0010300900000b41c25071500008081009000705268601c0d10010448101d080e6000e20385482103054844014101448999072410321080b960710081c012075103d5428010300002c2ca0341002c07100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 218217967 1250 218216717 218216737
    0x30c0917101a010816090b0d0506010e0a03081207020304121401140103170c1c0206040b0a060b04051c060c02060109140c070308060310110a031113030201050c070b 72
    0xc00000c0081d00320a03a07800e0507000e8003802038440c0365440c699200c40c074154000300701004076103002c18003c0100c40300640b981c031486150101048110b4403640b10703406980078030801d0700c07400c2483d9191014807107403560510025120306401e200391000300c8503d954881d0700114a01c1071380d00d00b0351500c4001c4190b0080715401d85105140032a80080a5000d1103840060351003c0314101741c540c5195079040f560502590000c22409002c5014400074108000807102001d01b095080703105801a04002c0da0b43e039041714180d8840c540000400c000d14214441c102c2a80c48181d074440c5490b0030003041c4483d081c180c4001d02107041c1181d01e004007041c410710401444c54403642c050280355150841134401c0d20180ca000080c0320003500d043c40401c50511045850070395040c00c0554840d59020006810402001c0f9071f200c0160404440202405414005105101d4035032001c0000540b121320020840c040c5c4020f110161149401c148050340c0184041d050f09503040e000c031000340b9112080000d998201c60201 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 218219217 1250 218217967 218217973
    0x2041a030726160b0c03040306051311041407030b01020f06090c1302040503030d1805010c0302041e05030a0b0903070512040f050d02090a0f0e1b03060906090607030c0917 75
    0x28560301480302d02e0240c498151407005001c1050016000c990303040f181c0c4500f4403080300000d810f82d000311060090b20001d58104c4000c00c80d610b40001c4160341003400714001c844402485400d022117280c80e106960213039012151001c2941c0e10402c06600038107001441c0c0341584180505130400c5c4c1001c20025104010360005010581d8218090184161600300c091545500500c4284559180002034984c1d64000500c01b2560281e4002d00f500c54081c000c1c001381580d4240360800100c540c0507002071041b038625120605c03002e40e80c0404026120380c00c0c01040d078150800c500c100003003081c4a02c040c1c0c20400c030005480c600402a80d5161070140c0420b0401200c0c400428200015500c10b540300d03006100646541890002990000300d09490003400740e100d0b25a14052035030000c10076400039084111b04c40454804070300b0902d441c02503000b0800481e2181c442c0d200098030150011402c00c0c040e600c84802040144c48441090b00904410070700c400c1040306c017080c0001e464150720441a006004030003d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 218220467 1250 218219217 218219249
    0x60905070305010c0503010e041127061c0c090c050c03030103030801060e090f13031206090203061c08030a0c020c21010606020606101d03070e100e07080402041a0307 73
    0x16013551400c250903002d02c0010700c010082c5400c403074203080d400740c0c1c40b0500e1200000d08000042011142000b620b48280c0305a03401840c2461011505001d10401c40d4020035590494000564103c80c400d4010b182c0501c3c1401006126071540140c82d4135445030070100d041c0f13064404082c0c5550000d03802600003419200042001c290000860001400d06403891000d43c54001084c049804000d031524000314806141d4000740361040800c15100c070384c44207043c0105643c0c0d4054001075001650003500c03503000501200303c621300ca44020001d85501502172401d40c1d0b2000b040100801d0310a8645041d03001d00c01680b00580d44881d2402000c4018500203120109072440c2c2c02d007142c2d015005003096500036002d001140e6201c00d0449101d00961038008003445140740c500e001a186141000d80511401d4004100c0e00d1000b40b03114407405116200b03070030303003682d450f00300a60700c20a17644440802e407040c006c10701505240e085106020040900000c02c0100d43c00424904401039100e0010101902e030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 218221717 1250 218220467 218220473
    0x90904051b10082703040f050909010b01090501050a05070501050403080412020c1e0126070f020715120b10020c03160b16031101090c060e100c1704030609050703 71
    0x41c1c9010106401c1d20b0304100404814405040350a014100c51481c0c8052100034455012201e01416600098020b4075129a030326108285007040310300550780310741e0500d8001100380405101313a1004160581d10055401c2c604001581c41390312070341da0401000410856400841c0d401d025031405144aa0354000c0d591626003040003040640d00c4641d02103410242c40660300b42e5036800c0795658080c100d02c00c00408810344d4010381e00402d06c1106400d544498600341009410f50210701c501c980800e8440d0080991184400ca03141c02050042c12800c0110918032000540b0a100c1e03404d8881c105c0700c00140700c20703500c0000352840d0003011f1508016803080302715104a05003070108400701e80c06001039031019420080c005005001740007205030034041c80300903041410b200d940c4810705805240020404c0d4802410015452400b40c01000040b07103020044021a003030501d4500311070400b542d180f10380030b041540c4508003071188901d0b003512440144008004929a4802c0c070300e910744280d00514103986145 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 218222967 1250 218221717 218221753
    0x60a050c101a280302040f0902090a0c140301030323040e10060318020102030d050702160f06181511030c030a05040305010c440f090105060a08030a030e0309090405 72
    0x4166076810f814000300340240312105003a00144c0754100e402103003a00e9884405002421079a9010354080e5107030b41404810351480e480f02c084186a6600d2481112070001810030381c2c8802e20004000511440e44400c8180c814403081000c080d0103510145001c0c0e540c1d070180804641650700018a028801041201541500c607141d41420088400c01c140156600080d480380100541c03a00c411f9140e20010301040c0c402e2015541002d44400140c80d00781e00c034918203849401e10f020340800304641030510b00c0e00c00446040c0004403143d000f14142ca24242041c21a03005601c044010b03414070042c0901d02042c3c000b03001404000030959590b0f03443d07900d5810400d003922010f1050b2824441c07140010060981000c116000d8501c0300783e4210a60071000c00c03a07081c02c0043e022041d61446020082c450101d0a22424a008446060003440161100b0b0f080001420a0340f0500382c056108102403100580240c0000018036101e40603203082c00500310107e0500d010440d0700700c99603040088a504550341030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 218224217 1250 218222967 218222989
    0x20114060a120f0224030702100b0a210b0a0f06230625060b01020d0807020319091502031905090a0b03190905030d1802060a050c101a 59
    0x485514107031915100c504003085000040241c0741074801e10000c015500c410445001e8464104103601d4480c0d00900b001d0500d8009859140060085031107203400740081340500c0785030307290081800c0c0c1d545160a403440c0301c002c40c242510070a031001d0800c082c0802c410003c40c6208590030b0a02203401c1d0038010100701114807540020740400051071000c20040e4110540388404e5206485113556500c03800c181940b503011440340700c040b2004507407070031041103a00d0700244080c0c40280c007102c00c5020541c4003030b2140c0e442111014016841849561032002c25880350400c4405a820102030054a0b07034081c61005050140c0c58000da840020401c00c0d203200105000140390240ca000c0b41041000d600142c2003200c14801d07180c64800102c08189005005020704c0740380c2011308400c0003204443d00c3d1860311703604005421004545030604862100307801d82ca040642e16402000c003441c1c03401035102901c1e01e030018142a8480e2141d914139007a041d610348511303034482088408642400c894602044500141 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 218225467 1250 218224217 218224219
    0x2040f150902130b0c0a05070311040e030c0d0509060403050a0c0f06050c0d051c18140d1b03030e060405100507050901020d030c02010213030803041707020603010909110a0602011406 80
    0x304108a03ca4400303081c1e4480c00740c440c80289180c0d9085500c41c41440c00c6506940a0214002c01c03200008118005001c6451481d0603601401095540c090942d00d901625401c0105900421100308401d4800c41c0103198480c80180705a00381a101c2d1100e5140c601c022030300321101940d10b00107100011074100740c2c000400441c9003151801d1005c582003521107150b180c900040c0000890348080409645075070124042c440c28040108030b8400030150843d55680d031064406102180000480440c0840c000b580e07141e41d900e0740010494040c8621348004000ca00a0741015941c94020540100600510340110b0140d4000d00014904102c00c0c1f0803a1400380580301484410058200c050f43c0108402400d00c0032030400042e250fa402105901920030b10914801e18440000d020003000b1161010394020307400b5000c11070300315101291240480c410b551000c1d5100c602480104107640c201d40000045611131303a9121010380c119004100c0700384090700071801503511841128442c0b00040c0086038080d00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 218226717 1250 218225467 218225471
    0x803120c03040c141807020d030f0501060e0f0409120507030e0108040209011e0b030702030a0806030a020d02090406060b0d0902090702070e0c0a02010213080a030807030204030b0601080402040902040f1509 90
    0x500390b40b45100c00f400c0b0310690122010003594000c1c5075503442801c9400b40c0c22415004000e01e03022200a445081c14091003000c070349400c2e04207907452064802e4505991058071100a901c00c0d40d001c100000120001c03403540591640c0340b25000412000503441d00b43c0303071616200c1e02c0d0303802c83c40c02505002c548111241003080e5881044050380d183c3c01c0440c1150410611a400380d5045807501c4180407158101103d8088000180302c0d07115800001010450740e90740d02c031170044d1039207410180c90307001001001c2e40c0145641810009450101708194101e4400c140010f0016a544c140350b050340c00140081160381c3e82c8114040640c20410b4080d503002c100361016018050402411104084010f05803048003800404c03014400360003581203602001c0c14813455060599140451591200c4440007100003542107030101d00311078004d0003600e0a41c0e601c11101c0040c1c1d03841d02c0c0116034041005005913032040d2950b2502c800342e1500d114a00d00040000700108813031909802c26034060040b60b1001041d54 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 218227967 1250 218226717 218226721
    0x706020706021308150a050702031603050d0f061a1309060e0103060f140a15050d050106030302010e0a0507092d1a12071e08070e061903080706240803120c03 69
    0x1001660896002c6c41c0c0050000315a111100c04a107036001d51800c0f40d000e40b4920f441c00e000d25420070b0141c206881c007000140504100401c0d000c050b51400e200d51022444109140c00401007010f018100541d40c8841246600f540c1d588440c0545040c2c0d844010502399510060003448424014000402d6058505201804050f00b41e42d03202c40d001858141400e5460000c82004c40c642c2448a004203c01060703038000607aa4201360b40208100d100c1180550310781200720514007000b140080f0700b039030480d024140052500d06004054101e05610700346801400c02850501f400c0100c0f40d00508030841c100103540c0f002c1420b064400b294910041e4031a02e103041506481c004002014801d81d803c044031120401802002410100095008010741d8041c0071800f058102900c00c0481c46900112070045201900703013110556040c05002c0501800e10800108003c550940c20205400000910701c00ea02d111400b14400441c02d941c20401d000d40000132091884c81031050544c1e000540725034600c0c514 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 218229217 1250 218227967 218227993
    0x302030c0409140d1d150307030207030e12010f0c0206011214070b071209050609011d0a1a040e0109020c0c09040302010b190510020d020706030906020706020706021308 74
    0x80ca100c4944a8441c41c1c854481104005410002c06185441002290f030329081c05503016250205240500640300307042e10031640707245071402c150907071070284100d50b41c5180c48804044000e5449464160309001c02002031a0841d1914a42048825100c2000080d00400003002c101514500303c44042198400c0d00180203c0b00804044208690b20402c5e481d04048417050645c1490b0140e84416034056010a496007841001803040100e0400c550b10a08920346820401c0399900480948900182ca1104151000007444844511801008248000c02651040c14960182ea280c441920350b01020500b00148020100c1e0180501a118402e60518200c03411842e59551038505052140d040d080105003494003e500c0614201406007108804001d0f44200e075440c480706224550246400000c3c10100c1c42c0301044542044035103501804419280960803006809540c1c0d060720155402c1085e071001400d98801400030701c0c4035000160304c0345012802c00061824070351040300301d0f4002e02c00801036 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 218230467 1250 218229217 218229223
    0x308040305060a0c1e0e03032209051605221503060806090a0807020d0b1006090e090606101206080f01060b0c0309060d0f15140109050a0513092102011401030203 71
    0x1c0c0190280080743c0c1c0b0000140111440340d0301b10030460705800000783c0d0802d035103c1c062400b504016407004000c0d0041d070340e000440407038000b110785201c0d8807842c0c6400499203100b1001400100000415a031040b105011005081c0070b0701e6200311030341807503081c009458030b82500440004140e4503000d001245001d01120303446030002c0034000c210380000a001030440d55880078211410b504003c0070700b82807401c0c11418110074414000c85000c0740c2d00190009142c035101c40761034850800d200140405c2d03100c2c071050000c1019100c03658414070902c120020a0070b0454811000100f505e00c00502100000c03101040c2164078540205100d200208003440c4061000000c4820010047e14015510205154600c0c010029000038910090a0031018000316401030f101030103031082d1401c044501c00890380196042102489000d03088002c0600c04c015610340640070b0003440c80d60200c0412612001da48410a0100341c4008011348604d1000080c80c5030350900c5120701402c1418100802d43d410740e000655 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 218231717 1250 218230467 218230487
    0x6080a030e04020c010e0f010c1b022d040f0501030b0c0307020303010308090a03020a030b040615081506031006060807090f06090b030910020d061701140c030a060f0308040305060a0c 80
    0x3008030f40002c0c80340b410300003d60010040580b9001034400b40c1c030032400b440e03000c1c1012299031300c00581d181500034001c40005a040030f4aa9000746498280003441c180002c1d191484501546501c04070000410340d41c071603002d26075080a4812000802d981540380c5001500405013a04a403110b00340100b0014a800108480c19290010390107074454480c1d00000c1c03c41812031700029088040360070b0000030000e0f00f281050080b8810350013031140f1640e15811480441141c49068019440341074a09080109004c00c030780c0021001e42036680400b0b651400c039043e01ca55900000000703211038100800303181e1085003003000c3c02004900720841841c040c4014058800c50190490008000005c41d00d10345040103462160b04e0030700c10a545410400310030300002e1509100384594640d0301e6a80b1140960188902c4041c100081ba9400840d152070914402c4c81c3c00040000010566804001c47c028801043d90801584a00310155a440c25071400070b00340b80c00a00321000250400c00e41030300103508402145 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 218232967 1250 218231717 218231719
    0x5011e0e01050907121b05031602120a0f1709060115110606010f050d110409060b130e070c0804030c24140c1002040f030201090605070c0b0f0405030f1006080a030e 72
    0xc481300c00007185d6801000900000c206030104058406105c0c0d401001941c07180c25100000301d5a198203030401c2e42c8a01d000e03030000c60306500030001084100c2c02121281c03851041c1d0302d80242018810320700c9200009007034441a050798410380041202c0c1d168260200038000381032901d01200b0190242080ea1120040c218505110a454554026900c43d205655000c403000d0024420424040c5044503158454000d4840107810038102140c40c003440021039400c1000780c10040100c5150000c0c00440ba14040c227184108480320341c100001c0384215004c0c20245001e054800b407524501900351242e4019500c1078030410b80f5040c1d006000d242c0001240d241c0074680110140d4072a140501141800070740032450010902c00301c0c0100d400210201c444003628400e8132001c5d001d0783c0714001601c05000b0000000e041040041003072051031141000313411001c0e035407081d02d070a094440002030f080070075011844c4050b500109031031195800500034040101000005024400380300d0b24001d2038021816016 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 218234217 1250 218232967 218232977
    0x50f031204030b15060304030909050112021f0309020604060201050105100327020f040e0a020907020f060c0f0403060203040b1905101a122a03011202010318050105011e0e01050907 79
    0x29803d1081d03103510000580f00180846e0356494140f80151051040c1d0181008492611001044803601d00c8a00385100d41c0041c6040e002c8480e89034183c40040c40034444004040e16040032800581f220750160000c1c05494001041960411060180080c44c03a0000d0f0101404c1c00c58400e0000d11450000d41154020075a40b0040d04950020880458511800c150024581400f401c3c2181003c80d144181c0740c4201c5041c1255114001e00303e1780c94492143c03000c05500280003080409500e28000c001d050b600e10341d050704041d80c079160202281c00403542658411140300030410b0004010900c1008a08040000c201c1c6007040340d103000c4002c50b00e002d201052210466421180919082a180038a074840d000714038070314009240c4191000145c403060b1040c00301c0f03540c01000f940d0250540f8180c1e840b00d1807280201c100317900114064151005192100350340d6652100200b4020f0244c00d01a140d05038101d440c240c2440041c0200c143c8036841001c052040300c00511190b0740f100d41c8140c028a0920b80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 218235467 1250 218234217 218234221
    0x901051e1506180a17060609090a0203030f0d050a0c0807050f040909030201021c061406090d0605010b19080405100e10050106021b040b0907140d0501090204050f031204030b 76
    0x4002003900d00d0085950b80481d001c200400320b00c04045000303480321000d882003146903a68018010460700c80c07803a018601d41001001440508008903a2584004010101c429608040c1c001c030342554854141304101c41c100080f08503101055003c1c81381c002404603020031413103980340d6004180010240c0001e0400c08000307066420070305804240c60242c0f030030400401c21101c0034a0040e000390f00c84c80000200e00d8224050003401c001b00d1003054120341801c5440050b1410708810010306501400e011540819443d0101c00802d59030303c941d0780a0200510b0300ca545140f802e40480030b41903048a400c04001d04c4034100320020703030080740e0014005480c180103d2600078a59074941800c00e40110306a81528000c00020015800203408a10b0207000000c21360411300c40c4140000d5810309044560000d0f80d4801048a40b8030900c4600c034003140440800c0e0905e16450081030a5500070384c4946002d58000c141400180750421540d689544102c0040c810210250a020401d004510010308401d43d8000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 218236717 1250 218235467 218235481
    0x18161209150207030e010503090a0204090204020c031b0609030a0203250203030a081b030f070807020721150507020703032304030b040605060f0105070213061208040306050901051e 79
    0x80314a9011450030310015410505400a40198100b900010316010b48a01554000d20807030f8007c0700f4041c060b1001400136000c2c04050002090103c0c4c00c69801c000c6550408002d001074400701d542e909420398450030fa460a0303886c01401414001d195002004200003480e0004101c0f040c0d031070711a05402001d158501c0d2070085044008010390140000694442400e81c8243c449110304008290001031107100d0000b01c4450100301e52000c1c0c2c1301c03014400b042c5500d000e103807295031007051841221546a04c0300804a00e0042404000740421070403d220010010302c0d00902c0d942c61403804003000189440b43d00259590400d210146c140220044a41c0825003141000c0480031104c0600f07036075441e070781e26107000d0b20f08007224203660442c540404500d00b4600500344540e180016901c10342085035035002c211460440b00320141046907a0600001c0c0580c00c80c80380c0807070b1b900071a010f9482e1880c5050243c1500c80c0208a5411640762608008190b42012010600740003d240c0e040c03e55900c0d02 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 218237967 1250 218236717 218236721
    0x911090108060303041e060f0c030c1b0314030c060c030f1602010906021803010c091a1602031902120109030504031203140a0606170103020f060a12020a090302181612 73
    0x1400c80821110b01001c600c02c152400d00c12070046a00640c1c555020319605502111a6a0100c40c003c0004800000d1100840c403c02501414a080cc952888090341d590b503600341907e14801c0f449800d80c001080640c186001480703481c0c1c1c001d110991551640c0b900c8158545619401042003400070346c00c4002d00310301403003540f005842c1644008115919441c0c1c00d40e05016a8000030428801d60805039020715a41c403400203081141c0c141ca1007100d00203c58010a1180d40040401c11000220b0010070000343ea82006498284c825810700419800e4250052006ca800c0001113036016070306040803c400280d0141c212001c80340c02440134902c0c0703805810f00f14041c100310703030100c4400d01c001c80900941400c10340c0402c086a00580f50803250f00e407410607100080310f0911000e58041c50300c81145046003041001080e000c2d50502c0c0000034400d0310003520301243c104036240b50009145030014011030614000c18252186140d40d820300c1171510101850446030f00030202001c0015800305d18407501525 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 218239217 1250 218237967 218237969
    0xe0703060b030d0e0f0103050717040c0e0c0703020706080c130306050411100903120e030f07080f071202060d0608100204050405010b07200102190f0b10060917030f0d0c02010501091109010806030304 87
    0x8400c2b8001103050500780780e81c401c21180200841d502c6000c020540c070203500d0045030103296040d000342c0502e43c40c082098415160040c00340c100764100700826044050424401d0f00a507200786c03000206402c00b8140300030f040b00507689072030050b1076100d00c06421603003100801c0d040f641d1045a42007501c840e6401200e911041103030302c0340c0610031580940e01d02c18010803600140c418442c21540c072448000302c02035a68141d4828070700408480201c203000750130020010859000030401c00b040710b540c1c84e804185007942e480025118164042003d20403490075010340d80c0106202401a410030200c0e0b22a08040c6588010448003c0c140c1d441c01d0f47c0c035034002d00c0804610310f80b5000d4000000c4590800d030040e040f07500030441e901c044c50b00004840082246951054030780759900c016120b410450301c4c080d240180c8a001d00030384814400740c400b4a2040c13004000440003c440401d000c0c50040002e800d613034042e0001d003c0b02c0e00300a43d541404071001c060301c24200091824803074a07252040424214131072 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 218240467 1250 218239217 218239247
    0xa050a14010303081503010b010e0f12161d04150e07030c060c21050714150c070201030b09010b031605040b0705070e2a0d0e0703060b030d0e0f01030507 67
    0x2940d4000018180c004400d948610320900c1d09a0110948404260032262a04805408140520440c01c0f0781d007003200c110200e04802401c20703044100300c40c50180c44e20f100d0400c2180740600800d01880009a00d101203040078510402401c40d07410310b41e644044102220000341e42450f50f628880e0302003102000800c0040d07811111a016040e2101002045074805000940b0810258402444003c240c101d80351160b60165903240c8c1000ea0581c2c6000240e00104400041480b80030b0868402200c03000d038560042c1100d102aa51b2004a84009401c0d907031500740387d912480c0307080e00421140e050502200d5026900f02e51965490441d08000c2c2c40e10f005a401580d0008008120300040080006104059030441c030038000341661901d5180b0000c1041d40d02524104442c46032904c080701040c0054410020041d401080c60441030580390319014180c3d109480e15901d51001e003203030781401c1c0040248805545007080b9800c84510116100039114540c3c0ba04065440c030025220741e02c140d0410605841d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 218241717 1250 218240467 218240501
    0xa0503040501090c06020c04110f04050907120c0504150806010e0f0604080601171e030f031510030f0507020d09030f0203160b0304060b040212060f012007090c0906080a050a 76
    0x1441740c00081d034420914410b540107910700006492811900c405a601c403580e50b01e045440c040c2002d0607c142a1005080e103002d10122144000041103580145201914203a98250320351303140c1000203900f0000c00c0545014040c03558107000d0f02d641d05c00005408074100383c1722040d900140f0b1002c80c01e14403c83e03001c48264002e0100118055482120180b51140100219401d80403c8039080c0380044210075903a100d0b40c401c1040795503090011000d1a842000d034502071540703241080c0842c040110740311040d00007a6440740d01c0341c1101460710402e41c100007a1b200920f1499202c16000d042c0320490300018101018180240086507400c100080b0b1251900d00c0d40805d440d51010a80c3c0030340c00035242102c0f8103081030240b80c56807c01e44203030740b15801861100c200716120802842030210040384181c0c1000401900015032824011a0406e0281c40742c00514404e032070481c44000311681100031000700000d0150030460250b02024203030f000191050000340503182d1030006001454a22903e8191340 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 218242967 1250 218241717 218241719
    0x1303110706021f0203060a09151505070309090501050f06180409050307050c100c0605060f0306190b030d0807051612080703140103081602180906180d050a0503040501090c 75
    0x3540400d820b020100ca038080f84441e1003009a202c000e80c00300300c0f02e1036003180d060700b0704120859858108400440c4660200350f25580c89145402c002d40007201c0c11404100005202d074109948103512078000d292141c42044594100400140c6000781e01c0341080c0718840129400ea56224041000d02c807001c0700401c1005031003064901180c8903003101e002510b09018014400803d810b1143c0c0500d8025030a55808640b507126980b10401864041c0070389030041034031610400c10380c0301000a00e009180e102540c0c10b50598205080e01603d20152015000c5e402c44111a00102c3e0014046600441c89090094495010200d8001c9800304120082d050b4032109200040c81b540110846002d03030480d9405100d40d00032215021400765007803100034030016007003007281280c600c420660309207184020701801c54800d803040c5140c2c5142066486d0002500468180b010488500740f41d4110100041c029106000283d04040e14034080d0310f07208814464008000360401500f0743c8400c58560307124201c0603e403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 218244217 1250 218242967 218242979
    0x405040b042301050a0f0e011a0c01090305131703030c03090a151d0c0a09020c011d060a0b090f2a0a02010506040c170a0902061c020703031506020613031107 69
    0x240b8820f10810380100500b01c40403501c075002e111648262440007585403901d034607040d01a0711045807503943c000b100b072051241500b1084203006080405001b0340e140750319280c030780250780709911082c1e2142d400d81c0d1503441c04104c00e1201005aa5101e8404490942c980e640c40703800324204801400e006158208000011380c00e03c02a41c04403040311042251803050f07030200c0d0b41070f070f60743e52040440c01e0303110034881007c000040543d00140f45c444140400030801c18842501382d4160301b0082d98a840340c0d0045002c000f1680d0085c81606a15007040f941d0503020b0034a00304080035410082d007031507001c00c0949030300c0c00030041c1ca080c0419201040c64200740d48030300b0060024020041a5000d601c29801c050fa00007241c4e00ca040d00ce03684950b4605105030701e072240e0888500030038411500300c5c0c20103c00d1014280f2450b0034400d80d1455040c030040582e0342e030510b280040885400c034814a24580440c50144200ca500040965209040090b03224040d6250305003596030b03401d02e1a020380ea91040060104d21 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 218245467 1250 218244217 218244281
    0x61c020d060522030e3705040f0903200102040b190207080706050a1d10021b0411180d12090602100204080c0d0618030c020f090601050405040b04 64
    0x8109808510b00c0010090807500b896421944040500000d0410010042c0c0e41b41400002d130f4042c0c00d10141c110350700340845010b04c03540802c44068a002c044c0ca00100f080781070a02880720807003003003801040b039000140d0f005406150451500560890280a0000d208900b54100c402410000e0307001c6407500000003130078418601d01d0174400b005000d132a2001417945400140041a550242c40d51400c0142d04902213400c540c0144000041d041030003101410703515050460450820302d41d01070000320480804034108444d41003171240c0503500e04109035500d9903c03e419121540c044101500e808001c504c00a408560b0219014280d480880c00303a01900b40c0001655080322007a03000d0f1094001d40b80e58040c12030050b446002c030329030042074194100c3d20701460300042c034602c0b0740000900c0392990340307034150992400b11381200440c0311001c600041d031034110000c149500003144c1107103040c900003000038030a00407446124040e544900c0780c40341c44d580b150000701c0c45442c80c2d4900180341c1c190841d02c1c55 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 218246717 1250 218245467 218245471
    0x81b07080f070813183602090a06170a0302031c020904060e06012007030f032c010e06090a090f0b030f100b090f060904021518010905030102070506061c020d0605 71
    0x140d00b850048480c051414013031381c01c04c3d1880711034100041b00d00980c0b0076007001c08004074071407404418142c9801a075400000c5400303035a5960001400c00d003040c00c240c4866218500d6000107074030004498002a41c00402c50300102403200c060702c4124154070141029010301e1414a92041c100344000c198102c52060041c401c40c001d0340d406d03901066101018004d1401000c2c1480d40e50840d000c10b001050841e121482c2c000e00c20700d0300171110b00f03500d000c04083e100d5469041484020403418a0810344e48601011044501102c1a501d0006c107680050085d030a180320b00384100d900c070701d60388078404003030f5004201820703016060301c070702200f071981660300d500148800000340c915003402c2c1003c508000e07182c644903981c1001541c4440d01d80d4000c2002800005000700d900204a40b0804442210400500300344c2200660718107114442c4070014140c0741882e0400750080e03106211100201da00061010340059050b6101014009a4154103032418001907000c0e401801109401d01040490b5002d18 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 218247967 1250 218246717 218246729
    0x15090f0507051503040b040c120f03030b0916120e01020403110306070302030433180b0a110901260c07030801090902060a08060102210a081b07080f070813 68
    0x619020b8a86080100c0d07195103400b00818020140700203000507140ca41d0450b0064002c0c514003810350b545080c2c500e000d40800b0000c44000601d15403080403d6054000cad04c0305160300315060391b041c0c034040346452100c06a041007101000000c205412180b860381e40325202c0c0341d1500000f595219100d06081c4010802248868082d225050015005510a1080c3c81c003680c0d01940421202010030b24888451244240003503030186400e844c035901414a10440403007500d01c80000480e0441814103658400d4000c000c0d003101402c24000c01551a0108201d0b880c1c9042400c1c130b03c00c0385245003102c864014001041002548200e03003802081240603002e03141c0d0510070b5540341c860b45e0b294012241650f0a024009410890030300442c50501d000b004625800354061044502c281008240c00d000309038110109140d2060010344842d4041c0d0200c10b541d4840081c0320480392720001c94081421900c03070054094180c660200748034199040c002c0c05c41d0100c98000d554240c0320108081c0d180140c80c1c040c0f20309 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 218249217 1250 218247967 218247973
    0xd030e0609030c07051522210201020c0103151205030910020c06030a021b060a020301081005040203060408031f061806110c06030c070515060406120506060d15090f05 73
    0xa49010700000c00c54440341200406450035a1600c82445004c0c2c186180c0045045ea0911540d0200c0f862400c40411100f0600c000441c151b16010300504100d403240142d2803c04402c8000b0030150f40c0002d0381c50000442031900184200028110400303e02464024000800d901c1541005104000025190128046522401c4003141d07400507079480c82445642a08000c00f400040c3e00c051080e40502000240f0b03034040b0500404441b2070310300309007048444200c1164040b00511031180c0c20020070507041082101000349081940000e5030700e10700207100400210000000419503050008107160003c010f07010360005680f07409000e0103800310084c10f0900200c0c03c110000300c587c4200800741000000e0700c0580300c01d8400380300b8000582e1004000f007000070340c100564000110f0030801d8030060780e240710000740513091a0080005541aa41c01190039001c0050410007251010901e9038101c4001c541c0707068807102e41c0c0707410080c00810140f10003144d45408a0320007800b40200041d03030118454015 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 218250467 1250 218249217 218249221
    0x1106090405091c1806080a0f020c1501090b0307030b04110604030302070302030c0105030c0a080414031c050906070f050a09090501030b0604270305070203010e0303040c14040203240f030d030e06 85
    0x201d0300c0080d00d140008603440442d9040201900580c1c246402040c0f6100204000081d008c255041e0b9110f0308101c4600c1d03000d0041e40f4004111070440c1405092042c2c2c00f071040e003440740002551401701d80009015004403402090070803450202a480216018185584442e540d040c0a51690208d1106074060300510300c01c152950711a108591050001e240c1c19414141038401c2280e0108004000710350782e1841c04154241c402d4100003803e0031041020200d1190041852540251140030700140b01d1a0300440900540d643c00120841c0a5125490102c0d200d0203101c60440340c0140d540d02c1030300020724140c004024403486481d15403241c1c4d429a0103201011400b16880c45c0400c04911500303d903480410010001b9204000400c0b515000500100388552940c0100c0e0030365000360345c02c880192100c00c1c00c00690500d142403800c0340d4001c5401310b0451604441c1e40d0a194001018812840941e09940704e05580f065951a0f100f003028003240d42807410080040d0051180419030040c40c0300b00d0b00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 218251717 1250 218250467 218250523
    0x50415060503101a0d0e0d0c030e010e03011d0f0c090c0706020d020301060f17040c050d0c0806010806041b0503030a14070b0c09010e0901050d0602070c08190c080c010804110609040509 81
    0x100c1e00d588011032354441641c882c440c0ca0032103048109000c0c0c28100250a001260030340c0d000d00494000c0c1c007517404c0c00d40b0451480640305151101d030050041003034020081032111951030f01c0c901603204515500b1103558a410745032a00003442100056008a4400710010034500c3d401002c4485502454480030101c14080000c852012402c0320b004003040340c1070b1018400d1f41081d40702c1810451240c195101c6107a100e41b01c543c1010782c00d03000b02c10207074400401c000a000115481c40017a40c441c0091505050528000c00c5d00c174400c1481c14014040c400d0080e0201403c60b4046910b02038004139811603e041c061100d00b01d503440180c28a00003528003059003464540900d0703d90480e1402004000d41070055910b18019400c4920705403800042400001440e01050041c2090385640c03d050311100c0710245003603400c10800380c00100036540704010800041c3d810402542d00503801000e100c1114402000294091281c00b250b550401e09202c144209c003600020564550070b0409001e03003506004030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 218252967 1250 218251717 218251723
    0x70b0a050f101701090501061401090b0f0910090312030507120b060403110316030c03051e0a14120a030614040504050a030309052113050415060503101a0d0e 69
    0x2807039a802c9560560010000b030341851594411030b607500d1001080e2400651649402c42c0c1142d40024070050b54262003000c25039010038035034054442080c0850610401e03045020507400f611401901540722200d5a01c032407801a0740c6580110b900000c0d006a4114428009001e00801d41d44803000c1690412804003054083c064a105440c016015504151958413500c82c11007080301d070680c041c007403111004c141541c60140040518020b030280c4091038a1850040c0c58000e11100d1300d00514885603c42e03916040100d015040c09030007101b080304004285603660304000e001c501440c4966030003e2012003c071f80503000030b02102d44242c00c41c0c1d220f82c0c64509110039141c0c1200c00a0079a0003034411200000e00940c4a14a82c0e40910121f809103041e0b0300c2108050900540344a51942012400f500ca440907140e0a0b40504800d49040c01081e4103171080203200400d07401000d046c070a0100001d9444202c5440d02c4000b413810403205907200782040043d00c20350344402082c4e40a94201403800200036400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 218254217 1250 218252967 218252971
    0x60504020a0f120216050604050d051303020d0203010f2d061a070606050a030b16020f07050d060209030303010b09100201060609030204110d05151c0507090b1302070b0a050f 76
    0x1503281c45040341080b440c02c4840594040f0304820307495080c42021210603007800c00c10300d82803040005048900706030414a1600d01150600010081c08019602c130b407882005a5404407030741902d10310b080110f031744000ba01403c5a071526020083c13604044810342540455600e440191005442c203030780e01510201350950382c041c054007007202c0032591030b11120300c00480109429401040c0005041d910703400007429200c0903070b100f0b0f51794a1070304042c000d24810b041082140915580000c1811400314028580c4604092194900c101040300303c0d881400165011100800380050549989684481003640d003500000a454011040301030244a81030052185100b134880940f240f102042c40e560810000c1c01d01c0c0c40307200e80c992a050002100e010701c0740c0540c6029083d6144503c441414480c18440c02c41d040c102c0581081404505582c0800d401040000c00d89007150004100e2000d141c000c1220500b140341c00d0f103051840051b402c1d061041211200340248201030080c00640c0702e2140d82811501e003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 218255467 1250 218254217 218254237
    0x10509100e240a1b0b09030915120c1b06130c08121603030209210f010c0822020a0602030c0c2d0f06130504271212050702010c0306050402 61
    0x1040203680007040c0914020f00c650242054814200c81091744d80c01402c280a4844160744e60011924245a203405118150000401119542010400c0310301d000506e90203403060900307040018134003459560034400c040030325404004450305030901980d2503252081d0404183c80000000c400456a903001060491171301103518121410040d904490f03500d2515a042d0131024150708005c10542a25540d000703000110700c4075001b00c00406008071803801e00c0c2c0201018001c50349840c01c11250b0030b812001d60b0340c001c030002c1ca40c442e82460040b22a00300b824180d501a600c0074424100203529030740040180180d5045800740c0d420280701d0402c0c4820104041c0158246001c0590b8558050081403c007803a040c00040ca4140940250740c00f0504652103001c035140c0040503100c09104608013070054007891008010074820345244000c00d03082c0b042072400c000385481071200c48101d1a078402c0c2d080518129403204100042e0a00003000307402481c04491007408241032000c006807074a440c1c420385da1008a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 218256717 1250 218255467 218255539
    0x17030106020a030e240304210c1e080705031c050103030c0206070c090c02011d03120f090705041407030506030708101503050111030106081012060b010509100e 70
    0x10680d03405a400c5200400c00a4000c1c8604440c1c005c00d1603828500f021a4504140d0302da03980c10035003086c03240108882681540d510200c4425181154030210f40c241660700000140c100c80c80c43d07a04010304098418002c1c0179600c1c0407698105110020005184012131000040050003011910b201a80d8092001402203032403c0e0315003015043c0720004001071403045005403409030720f8108000445200c0381003c00180e5603405024203800c80c040c0010f101030301c0d5000950810055100700115580b0060581908a5410004c030f4000b00b0100a003601424005000307004600c0c8040c200040f25508a5011000a0820010804504000c21502c043d5503a41000c1c201443d400036100c8007908202c490100b80a40301040080407031001c0c400c009441c140c07046240d41c0e0307501d080c1d00102a40030107080c00d41d22501e80e0008024003480c41c0d0710031f5036a40e80a9804101d030086540141c03a00c0c09000001900040c464183c2405248d2207a400034041000710343c20030b1400600302d244c1610380303600002928140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 218257967 1250 218256717 218256733
    0x3111c08070831120f05070e090f1203070e010c06021c060902340b040c030c1517070e09090607030509010209060301050f030307020619020c060a020309010c020604080f0a1703010602 80
    0x80e280e07405031404940103001d501080031046e0f54441c6407a40a502c214001c1c0000c03803e200304d1140c28840c104003100d00100500c80d440582d0903010300d520000d003c11050102860305807606901948554080c280c005c1011502c42daa1299907524420500b204807200342e14041021413482d04910070759050b244a4074a40c0c1e030340d010f002254480f007031f13030740456280c2250000205800180303036000b80c0c1d01c602c0c8284640c02000340f85280c00005043c0b50f40004540c00c2d00383c8020414250b0000ca04000d2240d0100348034084d4841c0c00c3c4c199100d210000a480d00482c04104002e03106000040c401e0180c2c0f12590100a40e035a07010341c883c203d0045540450348458200010009403030004c0710707209207280040c140d91034110746500140143c1d0106441e4600d202103090303200e41d5240c050088484045040e42e0311403078400c140360001e40320722078038451a05109c0071448900640d103440058030060300c44007049403070300d0000703610296070781e00410011940d820030003800105201240091380d0403100a600141212 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 218259217 1250 218257967 218257979
    0x10915020a0f020616060f0501050103060305120304262101060e1e030307050607020c030705060708030a0f0608010f18080909090312010e1602010603111c08070831 72
    0x422050401a60b1000041c00304035410f413417048001c10b2180c07248000050142080f007412060381c1050f03100c135041c14500802007021480102d0059134600040090a589503a5441c28014440d1411904a0006a001240140107000c140103214240402014401c800000d000d902d0162800b40190000a0060044000582040d10810500704014607440d4070420341200032910390340004030b0a560350b521243c10300c0000b6405110001d443c22058000d0600300c1d080102203181441030800082c0420400000641c40590b00d40c00340c8441049480d0902c0020794a148090182102102001680345481c25617000d041101e5489001b19034020b41c0c0e5400c2440b114104201c0041c020103040d400d00003041080d03503036a40240121b000e840e00146408050070041c01e5090b14000e400198025607140400c00c1c40803503643d00079600580c000300c0b4107140448807602e0269002000b00c600600501c400b281d243d00b0080e140380a803100043d41304410040007000c0f41150100c81c014807a40c12602e207040c80078066 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 218260467 1250 218259217 218259233
    0xf2018090d0302070507090c1e0509150d0905070e011707050d02010e0616061406010503270c03010e030901021207030801030602130b0a0201140a0b03070509071e02060402010915020a 80
    0xc82ca000e5410740d81840d540387c0e004d80c29544400d411500103a8035014190b04800c0407109007116400d00d14105042010301c40200310032001014807800d0400000c695590078906a402940340668800309481042c3c0d40d401e02c00200b50000c1c041d090b00c82040c07580c948590400010b84808440000f441200c210304241c00540e812860703828500d0304000708002c00c0ca090005000030412082c8134490001b141007903c1c40681030050082d10080c100070040040c4440c0721407014004800540c0c030420300d0780d050b0305603800c0c510f8100401e80c169055400c05000c0030301c01d200800070300200c2d507003a02a00c0d514070100c6144032440c499504000c001c254100c006201003040f56006d803030000280d0b100c1d9540141c855600b109580c1140342c0d4500181c0d11903208071081d4110241458004a81d00e0040c8400a0319500103601c55006009040c0200840700014503a58441c21000c50707040419405500304403410903009407601c80440d001c0c1d0200e2500200010380000460700210020942c0c0c1c041c18040d4255030310110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 218261717 1250 218260467 218260477
    0x60a09030201060506030907050901151d0f10020a0c080303010303120b03011e0c0e09060a030f020f040e0f060c1905130816050109170304120f2018090d0302 69
    0x841d0368843d80890f00c0d480320001940035460140092804514000400030b101c08140c118821115400c0c1e0410390a45d0440d200500b140020401d003030407204c0010100380100c02006107190300801d018812101c10340c02040c0306100c1d034014030150f80e003644c0311304103030750f0340d21081c400100002c11882e20b46004001c075500c42502110020700229a500c10a9050381d8440e00d10b0b1103001050b55551120b020503078001d007818291107010b036040c4503c2c0c40e040000a5000709070b440007504110700e00c40c0c12411552854254541c0802c0100100310740d0002141480d9a540c5000c1c1d685402d01c06c010129401402d0039080d500030030700d42035080d100c3c0b03644900103d403281c05c00d045110501074a01000b0680b2041031181007009600704400d103440380d15200006102106503400301c0c0c80000240c02d011140b20340881142c0130782e0b40340c1000ca19032500034a490b1001001c00107004d000b50706607010401125890130300600c0c0c00a800c5a90581003c000303004d400070240141c1d601910343e4485041801094040d8001d00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 218262967 1250 218261717 218261723
    0x8070911120907030f120f0206010303050409150f0311031b210c03010509010b0102010c11060106260408030604110310031b0b0d02030105151c05040f120e0906030a0302060a09 77
    0x1202d03e540c0366180303501e5040445088900b024a00305c1200d080d40c0c0025891100a1244014041940b450302c0260691285020f14158151598a101030501d0100401402000c2421100d03031115074a0030310341d5030016014403080c400d0180005180d040002100300c1010800c0041040d54901014450070801085039168083c05000b0a180401c96560a224140c8546580000407540102410009085410b00e01c1d1035014040240c2d0071068607a400151241950306e24100182000c50b000d40d01080002e0f0b04c040c0a04074203410b0108000c0280b008040c6003c0c1390180e90034010951450700780c003440e000031038640d9201041100700700040343c440d802c8803006121b0075604840207615801c4840303650340a086074011142d0008010461030500c180b42d04001013015003401d080c1008001e60052002c000910410055250000305c0d00b4806100c04c00d008841d404000b640ba40a042d59002d400c0d400c9001c0c04a1064240800141c4503040c04a4490700b80d940c1070303010b4411a51045048170007005012010303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 218264217 1250 218262967 218262973
    0x30e0607060e010f06080106061110020a11030a030605010813050d1d0d0605061f12020a03110c0c01080c13030305031003021503090f030a08070e0310060b04080709111209 75
    0x4582400d030280b048500d13122612a0105289083c00012401e50326154070a000300900400d01160844020600740a11061100701603513803110884111404886500300307110600000030a0365201b5099403045044a800381c0300c00c042940d0301c0c007400b41c2400320714002034403d4110007a10f0500c85d01c180700681c074030031594412005003141080440e411800044040722095176070001c1c0f200d80d05d00544241c650110741081c415503040000f04c028085c6c00041e83da8100c0d641c0116410102c0380c06504049007501400505c95150440d1100590351071001540050210380f0842c00300309034810180c1200c10403100c41e00102c00c0c3c9459954201e40641c0000c0c4119011040c2100200069803011615012001800a81612820425401380c01c0450000100c81280c0c400c21910051582041b00c1c00e038404e805061014005000b0004a0304107075185110111140c83e0110100d040d04c41500644182c03103c0100711910b6645404a403c22241e424020001072401409040c018451074110103034031810407415 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 218265467 1250 218264217 218264231
    0x906080a090804171009030e100207080109060501090b0406031707080c1501080f0d080105010c02060705060a05090c01030b032e0219030b040b0d03050a090b070f0308010b0304030e060706 82
    0x82c032120343c0140c0c0140d400c883d4120307141a1200d0b800c000080d10f402c9010380410240b04e1955024180a56450f11280210380802113820b4460083c0702d000020f01d1042c0003401001e0741460500c001740b509000b258174451800801c00c3c0c3c3c1d030505100d500309403503002e0340825680c441055501410781040004440804040065020310841441183c001c0c2100300e4140380154104000740781071100100840c00d042d0b000100c40702800ba070110005045031400e0800008018860011440e0781c451520060444c0c401c0006108100e0171542c41240304400e0703041a2000242d40000450a03100c8078441070390300d640100d92a40e07156132001c0c41041e0000e40c0c94104800e24088d1350510050341c100303d46807017070a03844a1045800c035402d4010380030079a50440f0200200308804d00092820f010a02019003040808145403400034029880440904007003621191940480e180c590720035421202c040b00000c910800000d55155100103403406941d060f00c8074600d070050f4905204451b0400c1e601a0307605030300c0355a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 218266717 1250 218265467 218265473
    0xd081806070b010515070503030a0b0d05030318070603090812130c08070302040f05060d1218080601260715020111120a1b050702190314061501020a030906080a09 71
    0x900041e03128140450507585403100304403950321540020081c10004000420001d44c0c04012290f0111044c50006151103055001c14004060818018135912000091240450340c0504800038600302d4011178111700d803075078401c800baa400120003c10310101030025150274004854025030202c2c0c600411071010407130b5140c0384809805a804204690081d139401c1c025030802c2d01a02030145814802400f140c00e200e0040b907a101009540944030749205040c01804600c5140401483c0c05685002c650064a401140e0744501c821704c200303e503464003403041c4c9509640c1c00d881003114095040c050081c4034a001c05001544400000c02d808555030b03007001c0003030901c400c0e000d4001c0708a2861044028074100f629032044580c0c0114000105440289000207903070f1140441d048643d045e43c0c1a200b0510504940600d500d050f0001000b140101180c502c600e04001005446a82044c030081220a03142d401680c607810404d2000e00080c02c100d009004203030140440641020641e034001800c141652 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 218267967 1250 218266717 218266729
    0x1180f05150f070e01020a0305041e0905010609090f09030903080703090810050103050c0d020334060201150911030f18070f090b01052d041203080a1107020d0818 71
    0x102d9004841840b1014841d120758424040590880c080c0010f096510094401400c5130140e88604249000c0300c513075441708886004040d80043c0000760090000303584802c00500500001c1c00f80c80841032030100d1441c914401c500900c8441030b01511113102c45411078490540f5030344000020707400d00840328000100084100b108170120391f51100c0000e6994150b140c064141000300000c54450603400d0741131030141e0303000725886d480d501030207202d041407a85035030039160b01100c01107015403600c8d409140007603415010b4100d01ca1510242c0e00d04110580ca64900400b21031010481c10a4000b051001a40701002c00421030380188074211101e80c5840c28a88080c900010742c1c0001100c43d403072503030800c40c004480c02100071580007401c0250a02d0160105262082c13100c20701c0d15044002400c1c0c0c80c043e01481411500600100761403d452115a400c002e000c1941c15141918003610f81a00304000140704000e0300c0b500d0b41d00402c9c0d07030f4080c81e60391501023854000c03403904090f501c050090169265906 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 218269217 1250 218267967 218267971
    0x61d030301061d0102011406120109021804030e030304150e370b040e0402130603020910031b0803220b070b0901050a09081c06030f0614010801180f0515 67
    0x59a0301c12400c0043c4010b064448041514203066a0621240c1d1002c42ea1020486502606c2031715a4840702111404442c05440003c002039000700081c10170b003800743c0d200c80c1d40c5c40c820760090f2a481e0248100d074003403560340c0c85035100721400101e10f180c1110180e4803c46026000000c01482e4444c224000380c030a0a4041c446800780c4148424840c1c4000d14613842c41c03a8200504070440164100b03031400c66040c030b00700001031000780701744180c10300000c543c201588280055074024154162500e071004500c0c1c40341c240e0380019550380706038010340300b02d04000300c1011065440d000c0146040032051391049209002c4064001003641100720042a0481500054908680100e182400c241840e41d60142110000b401d1612054140b1030b014000c103943c05c0031150000384125084003174411403d1081d000b80002d40004220307158135492078040c04072980180141001c0e0304c045000690340d4058481c05c850484c0384100010107100035241c0818110400c52000074024801d40340e0403424022214079034441 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 218270467 1250 218269217 218269229
    0x8070602090607020a090c0e010906090e0406021207080a11090f01120e1014061917010b03010203010f0302031c1407020a0312050a170408270d06020c151003061d030301 74
    0x241c1c0b03814210321030340920380c08d403020020702303003a44210b0505c1c0009110032072070300a24003c0c03220040800c040000d154115190001030340d210545604080300f005001513400d0360800081d908142900007001c1d030394401c88502090040000814104040066880303690040c00804000c4c0d4800310400c6100c02440020412040f000c00040c0c1004c111a00100825020b0461030058190144802d04d5840c40c0d42c42c40b040d81c1a40016804130041280d80501500301425080e81650001c0000074081d03c0306407002d8280c0f88201c040c1c03400c41000940005240340780c40120310020702c021040045100e043c2e0024160240094086540e6039203079100d050303001380741001090006200281e40c007c2254400d100c3e0a0b170880344483c0c03101504140d1242c0030340c3d014465444c0d250049645200c050382000404081c0c0980001e005407100c00c246013402c0000b07403c001180003050007030030f03440b00560728100011481200d14164900da42821031b106c074802044038004c1241186140035020103240c000b040031314001c0c0b82c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 218271717 1250 218270467 218270471
    0x5060103110a09020c030a050705160f06090803030906060f0d020a030c0f060516061d100c0206072c010302160f02040f05150904030e04020705070e100308070602090607020a09 77
    0x204902407050110b11a808101c0303507031050010000c080d4012045440c48441460581c0c1c40b80c1060a007942000503400b103c129009041c0e1001955142400d01c0f001201c503152a10354009554064a64480c4811681640b81e50081d4001800a1402c03210b0304082c0724019084036802c0b039441d80400c61000586e0415150350390294010003d80f54402d07020000b40c007440c81c1180c280311040c0209620042d92403401806940c644043d00d1059458810300d555203800710b000c45028810650b9500f009000310040c0380014010038000418050280102004aa00d8031011840309440c4030001d2141c0a403004c0d14604150b000c10408100081b202041060b40d8011526a2406007081c07041104403903003a801c10041c1800c00040011104401441642034603041c0c505c0d4805642d0740c54211032802e100e415180c0d009101094090911500081e000b0540e00fa641c4084502d8945251660b0005410b100040200c40c0c10031014000501c540c0107804007400190866003044919030014920b1401c2e130304080d46071a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 218272967 1250 218271717 218271743
    0x30f03060801020a08150f13091b090c030605030607211d160603050606030a05091509070f05060301050607080a09032108071701052b031e08011d0402060705060103 72
    0x3e00714445103443c107034201d1f402600c20002e10041041081c400f20214100d0350349220712024810300e800001901ca00d1901391500b5282c031180000020081d0070743c4240024604000407609090009020340504c1031601c0e5901c0041d43c0c0c1c180c540c81155a056410700d159100c0507034803020a4038148000d90941541c015040e0a542c4110120781c180160f0700ca841098200020300849888540c1141d411051450010030143e65441086160020407903070f01c1a1003102a003086600d0380d001c5044000e65404464881041c0c2c0d64008008240c0000c2c01244d50085e0200070000c00100108020101c0c002103040421500350780741ca864800c804e190204400441c1c1d078020112800341d000d1160b541c007007041c1c100459001e84004a060002505000d0580608141e40f8000340350a41c200c40d01d80303259170001c5803032211800c138a001403e8040c91140c80c0c40b5080311001c00c2e81c800340070300303007060503035042d42c5c50b4001c800d41038840214000401b5200780d800c8181041110040346060040502a600601441e0400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 218274217 1250 218272967 218272981
    0x40b040603030237020d03020a02101e020604050312100f1212230c070906090c09050907020a12050c2406010c03090306050601110d0e01080f06030a030f03060801020a08 74
    0xc3e810468909060144d44040d0004141007021054045a0142c0c0c016014a05070328003a0f1078840c01403030281d805410080b102851036803000803c0d418007041d0000402d84044108103070f03030301e81080d50000e00302d40052114991103081549000d500020203a051090f0300c2d40c4006206c3c56002c07a4122000051014160304140500282007000700400c503d42400401703032804401e000c0040e820487c2c100c2d020005a40411494108503000103003145000c100005951500d1a100a001c0800c03420041203866000203014074145e4545442603846401800101c40290307581d0303203001d103e4940001442020f1118003440a0304000148128480300b0038a91402d64102000d00340000003007180c0d0400621642e00c00c0000d0b4485c10400032668400000301c2c1d0f0307488002c0141e5000c10329811106d824400c0c1070f2005081503110b9900b2245140030303242c6000750384070b035400c2c0014480300712040c81c1c141e40110032030800031703100320381040403203c2c0d905d03001413620780b20402142a60f002601d11800101c6140170f000300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 218275467 1250 218274217 218274253
    0x7051008040b0f06030319180602030705010515011407020406030b0a090308011a040e06030c03012a030b0f120f0609010b0306010e07020c0111010f02030403030606110601030818040b0406030302 85
    0x71140380d5040b01e01e00d4050700090b501c0c812a00b6400100301d00074003490070140298088001c8e07510460090610035110746009640f0f4000050a407800e6081c10302240701c41174841e000c010300407012303507070414842181c03007201505600c15072049130010354841000012800c1340250900410303640c0c10210300c0321030b2810020400c02c41030b0880039804a2070145441c585d038041c0126021500b011010308003980c1e030314001a08169284000c0c3e80c065082c030f1818070a0410790a5820501140b00312055008046e150301101220900d100b61a0002041d141311803240c1f520740444010001c00100b160b4501c1300002003242040415035824003107a445818192003407405010203030244c8081e070620a054680311000a5440500c00032480c10710140068011500c02d0039007003000c801000c003c0640d40c0781030034500140244820301c10400050720350840c04003043c0000c00c21a048035048028941000d00221110b11101d4940c08000c0e0301c15641c0d0415412911980030707040040d0301030380103803810b4140c601c02104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 218276717 1250 218275467 218275471
    0xa0f091805061201050c03061003060e0403031e0b011218061505031504050717070803071b05030a030e1e130507030c080f01030318080303180c10120b0307051008040b 73
    0x30f40d03030341410100515076482c038094984c407800c21210051601200c1030240c0c000c4c002034106140ea064850100400d16030990850b050b43d4495480b40c00d0044442c058600865070031304106400180c54200c681c4a5903a25000001e0a0340c0079024983d5800c102d6449004842000074817800d00140350600300036032b00c1c080c00b03519051600210050403c0c41e1139512140c40314060301603c44440c42d07110f05610b030690100700840c044d1082c0c1c01140c0c2d8a07142424040082d1440c0d280390000308070705030400301d1282404034510882035071545921143e2800d40040180384c080c80c040414800740010701010300c9a450080240440010520000325820403240080541d04039415400522a41d481885405905201050f04403074040c80d050001070f901c800320503d2a900eaa2110380140300102c01e120710b010f040e0306064100001c84c4110340c2052070340b90511260386010010b800110303400c0e418003c4401d07502d40003100c003030b01e000b0250340800d510b80740042e015488198408000901c0c09040004000c030800e4125 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 218277967 1250 218276717 218276749
    0x1c050c060a0e011802090408181005070b070f08071409150c0c011106011a0906040e0f0702011a0909010204210b060a1505071a011d0c0903030a0f09180506 68
    0x13414528098000c42e10b40c1c0c0016100400f10340d00000c41189814108045020003c001040100302c10140b580003001600303d03800a49280702c001001c940c08500940c84021644000d0302c83c0200356071203c03420346003c0a075141c10800300d0010800c2156981c0c8440c042c088002d0b10103005030711007030b03242c101500d0070885042c0541842400701da0000584400521141103603000b4860916a85003014082c42c01c1c01240042034001602150101c0d500d90500d021a216038403101c16000300b42e80d040000c82c20389a106880b00000c080710f240000140c01c0541295600401200c00903150640d01c85412110301d66610038403c86841d21820002000591055150440001c0300c5148103503003403c480e01a0741c0303104211070050281c001401403c1111003070204030650728800180006607911350841184000b6440b502ea0300c070660303500152816a1007020b454080c803024000703608200c0c0c03100054541400352020a000d210760f80900040e0b10801c41807000c80318180690204e000d08252007800309403c0d11581030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 218279217 1250 218277967 218278001
    0x70c0606090504111e04050c0306120c210703050703060b12030a050f03070e030a030201060512060912130b0a0306060f020606010e012703050102180d051c050c060a0e01 74
    0xf10002c11000701c096a01958211070102040c00c4411074640c1c4146590302c49074120317040804100c00c2c9046000074610800d0180c80d81c240d940304191039140c4603240603940c42d910900c84004e04454070072500059a80715010011589415204d80754146041020741c0704030703402c58507a5000116810710390a440c5000d02a40015801d02c000010058000e005110448030f90010110005200c0d03441031031070a1000c0b1026040d944072074038030b0030001e01070141c6002c3d00b8014014401440c100d2500010194818405000680016416148074180750f501007010707450080030700180455015940001881109025280020201d1400d0805231400418540c0078080d500024200091644c015050b2544c9801c00d1801c0171000035180e480b0441030341c003006204103415442c10048200f000550007007160a080d54064001c464a400400680c0f003032207d8024056042021a1040d04501c00d1041c801032620b810101d003800200c40c44140750881c1140c00c8048161254208080d1200a10460b0788800514a034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 218280467 1250 218279217 218279221
    0xf01050307020604120309080c0f0706050f0304020603040314040e091e060a0b01050d0903031505060304030906140714030d06090209103f0c020102030402150702010e09070c06060905 80
    0x203500c40f00004d2001d05007504504074104018401d0b0b00180ea00c030340c081c2c009a2100d2801c0003650b510110700025141d035105002c00880c6003400b520958880c00508a102407031a502d075401d00c51203404c0039004405100181c5400340503111448094005030003d00380c0c18160340f400c440000d140c511400d44001841411900e44484400d010032081e174000800340000c601001848012103481c031400460303290132403030300a11404155140c1c12032546084651010744000d91180304010346884180d0b401004209140e801708102030282e140d50300742440e420345d482d0412065031140d0140c6014820304000b940c20004213007070200618800c0740003425503040300710b007051a05e1021038032003541401484103100c11481c0f0309154484050b0904045409101c0400428212540f0004480405070000c01c1c1c02d0304141c04d00018510501c2074038400c03034008003104031800c000002d10034a980680c0c0c00740e041008065a000083d03c40041c1d481c040c0a9a5803082c07482001d50a0000403070302c03a5003201c2034550612003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 218281717 1250 218280467 218280481
    0x10140a14070804030804021503090106060801090c171005030106030803010e070c120509060c010e010902030d0302160213021b031909120212070e04081c14180f19020f010503 76
    0x19002d640580d042c00c2c421603d0301c650000501301c221200c0d41901b0340d03c1c00000c00c10303010410341000040341c0d600d03219003880380d0300d64014100343c0c0c0c0020a840000b4800451030541c5032403140404d070300860740041ea50462901d0340e010900f56203490300151808940040100078201d8600c00d8198490050b20781018030003495034a80000b00010001d1008211000c00d080c00c1c0c2d43c0d0b03000c3c11140d600341600003c014010012801074040c00410b04160700c00d000301031980c00f540d4000c0c000c50701c0000d60350481c12003681199003045000308200341c502c000140d09006d032503900000c40310800610700600e402152150249529000b603142107408120030070140ea40208100240011034241a540c110b4140543c602d0042c40180751507001d60180041c0340c0b8003818402881302c0d44006000c95200215480304821102801105941456051a104d55007001c002010500c00320002900c0815542c19140c5845c100201c85113081d07a81030490034030510b0710114104501d000034031a000241c2c01e080260131813400c12 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 218282967 1250 218281717 218281727
    0x40b0604150b090118080d0801050901060909090c0b0307091703040509040b06120703080a0f090602030a030b01260618061309050115090903091e0902090310140a1407 73
    0x200c03920b280c801c004280c6000c00d0380a1030008070300204c0011080f0364503a54070300465803219240ca000b4003040d201e0001245504041400e181030711a10345518105903e0550b0010050903130903c00d0350952a50003002c40c0343d402c050011405580c141d9120300240781030640d84199100780c102c6210150b8001c0004001d140c179414002d990044c1c00603d2841c1f9940e445000c915a4460500c401405000c0c1c41d40110410001c5800380c249880f0640d01e10110743c035400d0058071100c0742401240d01503407041c8000044180f082e00300710090041850f003500740040191106242000741521404002c1101c1c040012a09011f4020361001c40d401d400048942414000b050480c01e411020701c100310748800c1d8000910200350000010000950721400c00c8542c0d9075008070040054540440c00a060135100040e401c21500302d4034202030305140c54480007032030301c6a908000d500c6014081e415014203581045950818840c24211303950075503000300c2d0740c60120307507403003c84a10311001660740c0440400e100609901c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 218284217 1250 218282967 218282969
    0x30316090503070b071407030c080105060109030c0e09011104090c1b0305040b161a0906060409020306060d17031f08151306020d0504050c100503010506070b07180e040b060415 77
    0x60f2104e5644c0c01550800004150304089010b01d548034900c000420405070f00518400c880c80c03203000700280e4031500700450b10400d00b0320015000121201060080341c20100680d90009110000000c801c800204052001d0300709921803002c07182c0c3c0d04480400d05e904a04961058a25071411400d00307070007a0360242040c01203006854072a000880e50081c140400d01c0e80344000c58001e00107420000e21055407181150701100c5190140c05030038040341c040e0800380170f4001c0c8240c1c010082d084550382c1c18140300003100310348810303030740034000c007200484d041d0f00c01c001140181203032803031496007140c4240440c4000c0c585600200a6038454455401c20104500f605071b0004c0c1200d803040440da0880c180f0801034080c0c0100050304900d404148000c101d40000e555040300400ea400e038070008003491040e1100c0c0404d21606070401d00c10000ca1000071402d41c41203510422601b00180000c40110664103a220340703030860200075400304144024050b84c1a40303150b00c86411075090046400500003a8500445 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 218285467 1250 218284217 218284229
    0x1403040503040b220f0302150702011d040902270f1303051b030d0609050c041202210a03020601091a10080907050613051309120f0903080c03031609050307 68
    0x102161541058405544d19804018100607180e0a9030701d54607020822100c0b4801203109a00e0584030244500301841920380d0701d0b405840e074501550400e0703e8406503145082409a00555501a002c0107030f440824812121456640c0d031071401000c11050f00b240c0e440070f0951280c40720001c0800c902c2c07015001549012035410b00d0516280c0760102d100c144803000c14441c0b200c1d10301011982c0741c00c0410b980d04c40401c41e03030a03002c01e00840c0c42d0100440c40511450161008036440903802c10701504144031450700741004490101c42c07446101c1c3e02c19040c403c07074500440041e0491001002003d555004810102540680d0143c0c0c0f220140d002403030302c1ea8031844502c01e102c000d000280340900c0078401d05004100107811299901440a03c0c003400030407030f0160910500d001120846405201d00c24080f07041e40c404100b080f031003c48101078a5442002d03264000f006000322004c000601b13040040c0c081d006061005540780e00f011900300048500d80766a100800224180402c02d503275000030114100c0710 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 218286717 1250 218285467 218285489
    0x9070905031e0105070203070b04110307090f0507090b0f090f130c1709071401030504030e0919060b070c032d08070203010e0f030406030b061b07051804050615010e0a060f140304050304 81
    0xbe038000b09040601503400480c1c1d9030300c0c0940f01c40145c00030303400051180c0526600d504030541c076100340ea1800d00544442c116848400d010403125030401c9615440d6104008100400004448404078103850032040400c0c00900007203401c1c0c0364181a83e0440ea0015035100141040d00c0c10024016054501845000e04064541021800b814020800d40c0c1200130090007580c0c2918000c3c0c0301d40e1600a9107020000070302d1501100150151603202030324505030780889a688421b107541c591052050744120056510f41402c0700c25130500c01c240c1c14040f600c2d4483c5a90584400c40d0740100340c01c50f12540081d400e0f54206004141e0302c1c0e1000700490b81511004d0400080428141d000300700b6030b004040300e119420300b000c8070f10540400000381680c01c0300c50490f10841480c03000c1c9590000900107a4000b001d5034005408074500c000c1c0e400b035050032070700103142c2684102041d800140e40745280d41e00220120f00701003000594658040c2100c00500c185081c8070307296003000da4400c0d40d20321440c4200c0c51800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 218287967 1250 218286717 218286743
    0x9030702090c09041b0e010207061b06020a050c0105070c060b0904030e010f090f0e01080f030f07030804021c06090203010c0507021c03051605010b130b060909070905031e0105070203070b04 83
    0x740c4d0b0b5a2000102c24844880e041c107600644201604403982822824094030441800294a52103400141e940c4280b001030004030000c207a031004007a40000103202c042c8002400040c2e2030800901c5018400c0100ea910a400034545040c142c04454000d51030790301542c0d1200801020a40140308181000f000703107400e50481c02401c10440d00b0480642041509407a4460000340c580a80c0000c40e069440003000d8032840304404500c01c0d660702c1025410580355005001d02c40200f8062645543e0050010704110030340051110742c0401c9015840049460300d81d04c498920560800b480f92580814850510603d85120354001401c00d032840805100041c000d03007da10105072007401502d02d51401c000301c003941004246000d50107001944801c41c007a1400400c400c0c0019014054081d150700003902c880d280c55002818048c014500511070710a1258003040056940c03030030400031030100c50f1f187e62030050b4407682c441c0c1401e5a40190000d400c56106000340004560f010907256003060348060241130b00c3c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 218289217 1250 218287967 218287969
    0x418030e0a090221070c170c0304050901080102070506090c130e0a0f0c090b060a0512060a080d050703121104060c0f0b04030e09060301050709091a060a1709030702090c09 75
    0x414a5400c01e1140c94004140c8050668000402010304d200da90350f070500590b50107000302c807104131441028041c100e03021440c400c80715038070f80204040388840050301d28103620380c000f040b4020020b13808086140e60006c1e50303005110301402020741100d4140f02500c04003038044002000d1440e510408840180c6c2c0c2c0c46942d5144e0070801c1800a2140c1c0000b1408211445003401d80000d1030368401c1c9280c0c0b038204090492240703030140841b0045440c41e2142030802c511102d090b0000b207002040030760451007112011070440000c1041460010503640c819648203010300e001804002c80410805c0c1c418189041d9050b480b0030a802d89040d500d072850f0080010a55050502c1c540f108000b0140840103060180014190310035031000c0910b5080e101d0801c16265038042c54202e81080f43c3c21000908070000038410b0b01c07099082100800c04503003040c00c00700111000038829034490b81484002c5030303002c4451070318000010b100541c0941070300b000e18207000540d00440d02c405402801c4066558000131a5852 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 218290467 1250 218289217 218289229
    0x20c01080c13090c0e130b060a08041e081c11070204230109050f011d040b190f060501091a071212020d0b031006120f05032205040b0418030e 62
    0x2420000c0080c00013200a04000e0800c0c2d548244c0b9500500d0b082c05000301122490040d10000e04028041510b42602d050044540da003014004440080c0c050f1170541c910042520400070305802540d2142c0d8a2410390010810f41c11415160308070300e800e0000c8280340c3d841c0c0d002601c201c2a01900d000c10f8181031081343c001da4541c5011a0224010740074008192040c5551005200c0e540800400400b03076224104031802525840301e003c40a074081001400180c4040b2610740c120725401d409000c03443da0b0b8a41e081c2940d0b00300d903038aa84580d440c50104142e41e84420341e0001400c04042d0340e80c1c40954095168441d02c2600c0000e000c800400c40c064a17118420444103c1c8042034080441d15007407004008030103005555421880b9204584040c10480254402d541c11039900000321524280c5d541d0310114811802c0d23800b035170640403d01085c8200c40f85001e0b0100952184400354040d5400c000400089520014180380224038081c81c80c07071520300301045504802d402d41810420401c00c0c100083da = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 218291717 1250 218290467 218290469
    0x60a0b0d2004061215140f0307090908030921030103080313060f0506090f01080d0809010b0a080609120406050421050f01090201090902071a070507020306010608040210020c01080c13 80
    0x1c50294001070015070143d1040418200302c0d41030506002c0f25040041031848080b0078003a100340d03081c002d00401201e10f44895118074030310000c0c050310b280d1540c603100c00e0226421004192203a460010400c68032030300c180302c0c0c8c03003403224003010001c01d02c1080c420151190105010051004000002141c0c0380c480c0b02c51280c5885a01c03082c2401240100359402014000079501c032405141c507140403820040f650315209058480d2500180340201144004550319080035200c2802d5542e2442048026101c8604650240c0807141c01088581482c0310342600d0400d402c00314540c480814001804055400411201241c40340042c04424000c508409900748003d0301c001800b600c5030000b04103c00c5c0f819006003c0b000c2c001d80300ca1500c0d13a40c4130042001c0e8441c549000b40380d03449020f00030020f072145e0210690803078914500541410760036030101e4134240080e005000420158030411085181c83e80d10442c240146201800b81e280c01c000010f0111070025200c135401d50008210078041c01c0440d002c8078 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 218292967 1250 218291717 218291771
    0x212120708070501061806080d080903090409030302040e0c0415020313030b040221010608011d100c0c0b070c142b121a1801121e06050f0f060a0b0d 65
    0x20540541e80384030003442c1c10702c14800d080c0906000c01e035149000f4440c0ad4440c5036202c5c080c0d4908020141000001c1c5a101c01c00c80a05a0900010846010017514070b88111401c9090541e6a82000c40c0c2c0000800520f00800444d401082050406606c814140b0104c0c2c1e400045503c0940f20307840000c0510504008024260541d12084002c28074150801c1d0119003c020080141c0f6030305a610780c41300401c44009400c0c030340c4000143c064040c0a5844000b6800c1540340200780030b512903603607640070700090f110100050340020084040c00340801d00050521354100052007042402105101c212401c07045002e03084441c0010780c80c04c01c0c0191190505107030108020400b0724483c82500c8000d44031512410300910302850b072601001d4896101d141620329008400d14000e6541da82c280e482c1100b1000050049031a92004001503918000d503805141500d00c00346181ca0720213103002500740020320750761186550201c10001d4030416400c445103660940004503545081e040380c0360ba00c019481d0780d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 218294217 1250 218292967 218292989
    0x30f07150902120106060e060405180702031605030a030f09050607080a0e2406040e060c090a05061215090c07030e0a080a05031e13150201110a0c021212070807050106 73
    0x1501e001501940b00c0d006550042d00c90306644107642048c00100e0259020307068008001d50041502d48111001282d1b10000d64811245000003486440c0d40107034042c0f20071100c0d0707800482c40b0742d6106d40500403420091541a82004411604c0d2206540c90341c1c00b62510040c00141000700c0c0c4914065008803107460114400ca5501541070780702400c403a4080c0f4054412b01c20044082006854035020702030b4034030b520000130a9035841c0e082c1c2e56140e0742d0100304060f0303010561741400105a00c0303c03006400103000070f0003410028640560356856004000030964850032103071040112000440d02507521668251030201190a480d4000c210072130f8681c2c0102030380f8850090300c0300400c44000000c01681d0103540b00d400b80715080c20040b0300d0303d000b00484140e04061400091050851400d0008441c00c3c15100126189042040d0000f1a910400c0300c840020403240140042d814259111881d0042043c01040360b0700c0b1170b00c01001036004440340100305910004400007403003025000540034150702c1c400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 218295467 1250 218294217 218294239
    0x30f090f0a0f15030506030d080121020d080c0d0c03050f0d0609020408010504021314070e06120c03060f0d17090607080c010b0901080a05060c1c0609020705010e030f07150902 77
    0x10002c1c074076482c038003c5000904140005200303040104a44181a00944801130281d08051050341c200601c130542070000d031221010000035aa44881074503909001d10314046d9110710001f103050804100c0e00314903084c00341c00300d807a0b00001d61003c11950b080c058920032903103907003003801420050012540146a2540040380100d130611042d40640e005038800c407200b4458a00e00e20074002a100078a065500d11012640080c84150140c403140104120003040d80c0d01c1d0100e12041e0160001342035a0a40b400341c00481001020f040542d0130540700c0f40101c4100021003074980d0f0720320f0058062610143d0702c040c0850303019038944984c3d00b03840c0c80703590000025484004501c082030082607000d00300d030302c01d0200600005800c0c4012804850181d0441e02500ea01e64520040e14050b500c840040307100000050034182c0b00034814441c02e40540016800541d40303502e90f00f0000c0c25103c12a200000e5a082040703003215601003102192200781c0e1044207680d500850498640040600100c041e40004507540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 218296717 1250 218295467 218295479
    0xe063903130801140c0a050915120405071e1203090f031515030f06050414010e033001060309020f09130c0f06120203060307031b090e030f090f0a0f 65
    0xa88405a4071044000c02110303805085280442134265178100c40c00300100160075046101d10000c026404c80130304000c0002101c00120b0089607c0b0b40318010000c4041010f100030442c040c0704210090840341038141521021010318810407035503220701511000400c00390300030180945108401400100c01d4500c03216901c0c200342c0120580c08100c0e04219181200e1703440d0308a04c1982401c01c3d01d421407501e441e2a00340c2d03a940801098050020396000c40d410b0701c0d10030800003d0146046200160b0043e40d215a0720060075048100e0004110108200c00c0703c078412480d641c0c492450448006160200d030905050010030903200002c2c3d40d00782c20440040811840203041c0d04440e00861103034800300403076a0340f94216003500b00036006010010742c442d900b0035078400080d0051a08400000c0030380d40a80c2c0d596594100000c11041c00b0f1056a541c034500308207c0c0403d1043c00305401a45002d9440c000e00e51504070f0441c4600c0c070880e84034142ca9034440d1066201c1d150007001400d0003081100825440e05 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 218297967 1250 218296717 218296747
    0x1b030e07260f030a020d051201030b1503030c010f14060f152205010f08070e13060b030a090b0108011506210e011e09020f1c05010203040c060e063903 66
    0xe00321005d4420308212844492280046518181d102188410580d003507035105190b2660180088500c40054150310049607424402044410314080c0001007502c950300701c5105450a980b450858513194404200075511159030070000550112806c914400030825294894080c48641d85042c011003180161100442100181941c100741c90b503042c079030343e24070302100d0014040760002d001506880c00c5410500b010708640c4414001018046880d50300e03007807100384a402c221030b0085940d8441c0c1c000b10030b001141d17400501511a08000b80545c885004400c0940d841c0c5100300010003940341c0c000c08458500200d40c1046441d07946092080070080e03e4038901900c00c0c03400b042c0b04007403020380504e8850614810002019400b800034984420039104120032052801041400403900303050366000100207100441c822403140b4920414641082002004c940595420501848041060450180726030301c620300141e10302c004025807400c040282d042c4148003840b038403c651002007914200a5040703 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 218299217 1250 218297967 218297977
    0xd1b08070e09030310090b030705090a09020118060914061204050606121b060d090c0605040305070f03110f031623010807050406080403021905011b030e07260f03 71
    0x2010400281e9142c01c28403940700d01c03090381c94070b6403003251100030007202d04c5a4001044802c1c004007500e4403141d4810200700020750484158202d01e5481da0b419045607041a207611001c4c4134115050846030038000080c0c00c0007280d0050703280760304001c001b405295442604440390f50308845264201e9050501d0000d980301c40c02c0d64a51701c141011040c82c2804800000c0710000030180281041c2074900b008184079a5900c81030f8240101a00e40c0d119401040f80080c49a00030f2140b070780c43d65600d03440d50611600f40b5621317420180c101d8402c102e0030800301d03004030862a560b040498074403090464003000a46004641403151110b440d40e188001000c560b0314804d641d2261380030120301080459500116500c0000b07c0c0c1c02c0e008a4010320051081502c80c00320300b0b07841403007030044a03581420506044103218840e4801c482d5131791201c40002d1000d24240f400220341c04941018041d19601a6034a6201d4030300c2d004458680c1069004400e142030309042e1480c3c00c280400551f01a46401101941c03a541301e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 218300467 1250 218299217 218299229
    0xc090f3023011407081003080d060f0609060e01090e040b13022206090e0703140c06030a0903020d08040c0b0f1c0204060908030307021e030c120315040513020d1b0807 73
    0x12203c0014126400303040100d2240e108007041c00c5290b4195610003801341c0104075910b007619916480812130012418510000c1c3c500f070349800e1400380c601b110040c0b000c102001e0007410000c80361303000c0210100300c00030b0b1600315074400341440300c80d0b03603400d02000254603060000e58408015001002c0015080c1c211500c0c03040403040038080139031240900300640e0811405030036140d01c254410004070300d024035105564a050410b03144022400c2c0009865a0816501c4050181e0b8030100c1c2400c0640402808100822a0600c10311170300e020740394a0f040a016100b00c401007500050240070106129045541a086940e01994140c0141e00450000d4009001c2c010104000c1d0101041c4450b001060320303c2842c6560050071700240d00208200e206103c1684400717144810b0040001340c440612510f1100186500402d44074030303100003810200c00b481500c0360f004518080a10024112091100300219019034030b451010003103241a0449183c0c0c0440301511002000c40401c03d043c012840804440e5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 218301717 1250 218300467 218300501
    0x406062705030312061c03050901030f150b090103020c030304150b030303010312230a0c120c02011706030a020a080319050a0503180c03010c090f302301 67
    0x84003a9115000450600039180c0c943d000f84550302040d2028503644c0d0780414007810b000c0100000c2d2030785084610040e142100817807008200c1c3c81095170300d841144215803100c0800d0090142c65040b804a68041c0e000c1d0703502240d000100054281d010741c04540c4605100000c40313503070b403420b03051912984030081d80c0800540e050162000e258540001941c1c16640c02c41d55003540078003d4641550b442d1000458418407800076003106140a01d04400fa109290058890080c100e01c185000860f0807801c10780c003814020240700800240c2d9001c0300f0801a40385240620050340c81d50310010f407600c07404403002540000101c00c080303203882c00031000d0040c6100503000541c2000e00400181d8041c018140f000300020414000145010240c078014100750b500e0300140ca080354510004a4207680d10020041301240f22000208081001c030307400040105402018121182e01035881c1c0e000403291181e055207182203010360743d01480316141070150680c0c1c0c0302c400605903901c4201c807a80601842884001e0040d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 218302967 1250 218301717 218301767
    0x110d020309190201050a0516060603150609050705120c13080a0b0901050606031f050402030a0207140a030807120e030a0305191505060c030c060106020c13090b1303020309040606 78
    0x740e031042e104000a50503140c3c14140300c1d0780082101c0355000700ea01c0d0100c201c40e20b0f0b01c0700045446845018091350050200d00c2000c1c8650107048180d40e402d0748210306480c54802004483e036442000e681b8010800c3c1405d94994a4020001800f4002d4001d5144119100f40000541c040c0c0010442601031143d1601da419550344c5004e142203403404c5810b1504107404000040701c2182e05001200040d483d06182c0100d40d88400c0403c00704e81040b02d0120790203600168103c1800a21a032407110b40e0402d4000340070a0855507001000204041d042400b8016445d01e580440040e030f400c10040c0c00980821a42c0b02c0c001d0000003406828182c1d6910b00b285002001c400324000c8a0150b012300d00221444061321901c2c02041c84055440710040280c070b40428031121900d01001d0143d140205820f42c02016030f03d14160401001440f0342298107165854a0b030b181001550000700d0550207803005c003a400883c9038504090341584644d0502c03070380c040c1c64070001081240e002025000340d0a03807800004488 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 218304217 1250 218302967 218302993
    0x302150f0906010b04180e0a05011118030c0d1101110610060305072606030a0b0115080903070c03030c0809030312010603050a021c0f06080321071b0209060301110d020309 75
    0x584514000c5414003140d500c00c4880c640c01d01d1f040700002008417811110a085151036885c211103e690350040000c0000501b03c0315050070702c0504002a8044014001c280d070010009001007081400c001d10500148500804c0d580c06449860071a0f201c9a0030b0360114642881c0c07201980c3c05d0b43c05400c000c289041c0204030501c0c410542001c0c01c643c0c1001020403140b05d05a8285002c800800c0aa0b142c411040d03000e0001d41c0c2007100301d0003000018041c0040c40321a48003d81140d0004000100c21361090003c140410340c200503070000c90f40c050a00c010410624100070300f241c07280c606540e415201c00200002d604d0401a80d2030304031009640c04014a0322588510003c0e41314441d602d008441d50844040c41c60506a844070100954a8100103451592480c203035007160428003050907580700050480c10301011040f600c5502611a04e010855000c3c90041c0c1e24080c400000d0282c0100d0b5500005a0192400d5000919031031b60074401a4441c040c02c0207030b134041c0d4400c80e080f01c1c29010304d809640ca0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 218305467 1250 218304217 218304239
    0xa0606150509010c05160b0c0d1412070e040e060403020f060c0409021803010608060a1401030b070f021e0a0302072907151104031b0605030109090302150f090601 71
    0x280e00031075460500c2c25001c000110340040c0407140c10340b00c0b0f010704080c0750001c440201d202e00051880340c1c2d066464124481300c1e682407600700d64028042c421b400010860142103a402c403502e01407070000700340b42c54440d0842244d141e4524440c90390020324002e07810014880024180b44180d02c0307070303007103d8148401c0d0315a1034070744e801070341d031304144e403e0511061040880e1a0080c0000c2da8000714084800f81882e000603007075818550016a00e50072003c180a0080742c00e0003050303814400c406209590394555550b548040100602110400c0300c0440911603040c420300620700b580010400d001d0f08400120360303541e00c03480b40c0b900890241c400c050340029a004548181e48044a50141c0c0a20200a03006002d8050384200c50480720480c59071000708140c0c0c003510840001441428910740c85600314544880603031200a980c481500301e560301040101c0c2e1280407a4107460000d032000c03500c00001d00e01640f40c10011040000a80c1c0004104030102c00e06189061194041500303c80d0181d90322880c980d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 218306717 1250 218305467 218305499
    0x1060306051f150e04090c0f061704030e01030b04020717040f170a03030914010903021b06120109020d11071a1f0b0901050c030a0c030e040605010503040b040204060302120a0606 78
    0x10903980c5850030f10070034501400650310740c00005413000c41c40440a0f543c205d145a0260415036801d00490360510160340e01c1503882c800001d4210030000c0508041c1c50241500c1c00000ca642d0415844161f04c0045454a0f010340391030702d0b40310785800105c000c2d08024182940003070080000301d494028002078406548606034046091520142504e18882d031007c0700a86000e0030107a40c460009a900b404d111004d2090302e20301c41c025800303002501d43c031070b51a140400702c580140740f24001c02d00c0b00c41442c0000028090465546850042c1d80d401042e20400c040c1000f048130b00c508070008a0301e0014051603401100c031f4007269014209099032910781d00603a55907803009103c0c0044110405003c10003da000400c12042d05061007030070720952810892859001e202c0d00c80010304003140120800da0000d240540800e8119000d02003107040c800000c0044c00010300c0600350200c180007027801d54607150304ca5005940c01400d015602c0320621055036440700842d100315202d03443d100c07000030510b043c4e1059030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 218307967 1250 218306717 218306729
    0x80a06140402070302030408060a060602060c030403170603190302030301031505010b1c111b0606010809030a030f0216050604032a020103152d08010e0c0607110301060306051f 77
    0xc401862000a00000703400400b000c406500c020000171851800401c002807040c5250034000c034100d41000b500030705140d03003d400a100030300103005000019421426403030004500341c02440540d940c0b0f100007803605062910042d007140646e41c541c81131540c084001c60680e8007030700c280307250b1407241a50744017110030902c1418080481485020a02c1208416402c2900d43c0200c02044519810744622000d5000300110b03182803402240c150a0500144185d69200009007019801450070f0102c040e140d100300d2038100b081540d1840e01c000c00184507816194070404a07581e507141982c036441e005030b4503c001d0300c040d004100c0d4000d404498403802c412000703080c20b0340003403140d4040b81c640c0103601911400b490380300302c0219480c0220300b58004e5101c4240755403410b0340c1f0098420300035031203c0602007142c00074001a410420042140c070000a040e21182209644280c1c1d40d0103d0304100ca0010820800503505509081c1d0000a21042da0007640c0110946840c00403144107a0310f48440c0c6190300c1c4581c4d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 218309217 1250 218307967 218307989
    0x12129060a050d060504021c1406060919030501060807060912120e0120030318010b0a030f0f0503030a0605040c0305040c0b031f080a060608070303020606040906020f0c070501080a06 80
    0x1d4003190300c40d4000c0e1801c07000380c207404590243c84400150681e00407070b88485c0301101c0d005400c01131212501882c1300c2000c000041c107206003010f20100380a407240f80d04584c007a400307100702c6441c0c1c001040020401107411500804c21540c035910020744444070f5204000c000744020001244c1d000e9606044400c041d4089030814040003e80300039102c1c03c08070180d00d8140442040181034440b88100700d410603008200180d83ea9190554004001e0a441e080c4046140c0c98210a0411511040340c40401e403500600100c2140c442c0d0714220301a6011420020080e0001000f4042440301c1178205d0000e8901c202c4042c8505500684200c040320340c100d0740607000356048501000305a0380c90f0002d58201505080705480c0d08800c0c07180c0204030140394092101a48001900024405148903500240c00c10b8070281620074030b5a00d00a5a81001900140c403456813400040c1c20048164110b0380e20150030f0505949410500100039151a2103101d128041222000040c60030320342803080740103440d00303c658 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 218310467 1250 218309217 218309227
    0x3020c09070f080c0c1006080601210b0612070609030b0124030507020c030a0c090b180f071e0507050f0c2809050c03090708030703050a080601212906 66
    0x407203d80303202402c50303440c00a04200c0207107003480030f110300b2200341555900811114504000c07180b500d00140d00466600052240140301d89c0d118425014880c3d8100c10400c040b030302c0f1480040c40000d000c4601d11001c0c4980c00d80001c42580064614007220f0003000142107580e078509500d811450900042855024020004042d4500950003103070001281d1046552080802c00404d00e8509011002d8a003485540d40820a6075864002d445840d5410384880740c1c82102c003500c60350803003400381203030014404d40c00008072820f200b4824081e0310b480d40e680c0114280380c02d0901500ba9401f503030302681d03540520101d2903031700c100001c0c00700320340e60000d03103420028441180d82c80c02690000100c2c0c400c59405aa00140c072503024041d2a00944810301308640c0c90500403401454403503103501030043c6400500c0a00040303a0444281c9000101600701a02e89960b04030040328001c10141c800f2106000112401420840c3c5e6440ac00907000006a240000144a190340d5035141030449640c0e0b101100300a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 218311717 1250 218310467 218310497
    0x80a0305070903020901140909030909060d060b04050f0106110c0109060c030329120a05030403030309060209041e0e0f1009050304080a20010305040f060c0c0b0406020703020c0907 79
    0x800107a12400600d01002c6440e1a5800500003800a9201c1100720790709498044981c034054407513640028500f0000c1d1320300303c150740204035031150083c9840c3c0309150700400b001c28442c0c56009440f0750200103000b00b0040c500b544182154100c28080d0400065030084400c0342c3c281e000441140d200c00584810700e0311840c0003011a00d035504000704404043d29868121540c00103042030300281d0500b91100001d202e000410301c408011241030007071455028044040104902104840a59805250210ba118050b082070800b0303101d450071058000d844d0540120050811605504801d5100e01c0140309c11038112013501e948030503404210106801103403107101642e1a552251580e01d12030000d0342c0c10030369207003800c40c1000800d01c426100b05081008080c201c0780d107034048400504090800700498141a1101075880c40880b8004080c0743d5613000d240e00d40d0b40101b4041c140341e036100341000b2192a052918802135007110008030054030440d6500801450481005441042169500a041c0b0304e0a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 218312967 1250 218311717 218311721
    0x507030f2009150705012a0e04020304030509060c2b020705040b01020a1211060c0a020a110a08190b010504062102011e08090c0a06020c0112020f1c0f0504080a03 71
    0x4500b840e07000004a40041d10806100d02900c1803a00500000580102404c800301d03500c8084600d03100c1c0d40082030b079840d03002600507108030200b44d0103490060f181ea640e842d040d90036108541e20603038082c0f404a00403915910004140c1d040c1c8040c11045003401000d81403001282c2c02010b03a034005a00f1226080c04681040c0d03101d698846014411103014944c691a40080510301c201401e00003000011030b4001c10300d040000581089013240003070715212001ca00203458503036241d001403040980364680c507087d0b81c4443c0440f001d804408282c4031200c28202c41100342412855080703403040c02e640300001c0e662805200e505c04a40341c40e000285940000c40055800c3d8400d52001c9042c400d1000501c5401c5171010b90402a41405071900c06d11410300040b01c91401488405140c032605c070f10f89080c490305a0100d91280300440c04c0c20403060500588a689020740201e07000550b003000003040b8078040702da00d42058604031403038580030021242c1a21031102691000c84002e000c40e40c0402c07040012900c05d0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 218314217 1250 218312967 218312977
    0x11b05040302090a0b0a1d0609070e37060908030301050f120102070501050708041a06150c0c10030902010f022a030f0d0207090b0a080d081f090507030f20 68
    0x1080004108240c40000b0745c036420079410826411000c0c48810541030b507952641f54002e202299407070450301d04070100402400c01081d000703024a100c100f042110600c0d41c02c109804002c6070601440c03605900400c4402e0390a103200c0c44001030444280025a40000b004881c10f85001420702c92075400240d0a0148640c0210b00481c080d40d0700300300802c0030401c28440c40740291107590307451951b0300b400e0806015440100c54800c0c03140b8071140c03d1041030350707601201064200990220545600001c441c039802d1424030002503410160501c03d400300c00358540d1050f0b251600c01d0300c988803480080042265a241420a051405001c9591080c68010041c14100b41c0e403400608039200c409040501314100500c00a405002d0791003444103000c0250725001d1185014416104071010502e400d01e5030b5941d80f032186060003404101d001040b40b80310f02c10654900c40d440a81d02c2c0e203d5950700e020b03038801002c048810900280c0f07048502c240548041c081c072904440e4040d4440c840740f540e408a07000c0d43c0d100b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 218315467 1250 218314217 218314231
    0x106030c050408061501200607030f0605090c0403030f090b04030602070f02041d0606030d020c0f0a1a13270e100603110f0108070801092408010b03011b0504030209 72
    0x380b00000d108074003004060703c00c4607100030061181c602e4000150443c0c40c252405001a03040919010a4034000980c0c154402100d10300411000789000300000102000e4001ca60040043c004000d0344200c02001481207030311035610b070140c82407107140071074120b8403034082c2000001382007104002058090b0050070203907000c1ca8020010003400d074009411074000c1024208041007118012040e01c81c10b00034241c0c4054260f005d0b11103254032440c0251280500c580d42032190f4010f0b000c3c4109a10f41c41c044401809418841d4160300500202900c1e058101510101001e480b098010485e0211600c244405084460882c4007030130b4480a414041d01013a1844581340c407a0405000030b4800c07034064140150300504e07802c171b0540c0500c01400403600f80149110706201d958000d00c403000c0c0e071003d0042e04660250b90001507802040901c0350105200349490811201c16031004900003030113500002c0701c07007030880c000c103d078400d040c0380310260290200591011900a03c000c20260801040071640100307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 218316717 1250 218315467 218315477
    0x303060d0803270604170408030a1101060305010513120c0803010b07050f01020a0903060f090b0f1b0a110610030203061915060806030d080108060a02090d0f060b1801030b0106030c 79
    0x70f1540490071007600f0000007605507070112003070006100c5400c214100d040d01090009203445c1c2800e1401d40d813440346107040e400700260803041000f890703070039440b21000e10b901c1802401542803010038000702c954420400d5030702d0040c5c842141e1109010700e04c0034980030b500002090840e840c03c1103ca600f50401c030300c15142c41c0a00105501001c100303200401c0300c1003181e121114001d045003800c030b0841d0740303008203203001a290080300c0001c1504584c1e01039110940000c018103603138035161002800c3c0740c01602030003441d0f0003042a59009802c083e80c00394031580007040340e54540c1d404a4184c0e001e80b00c3e00c006074240e0031400200f400525141000034060141c0c03c00814458600e200740921200268001c6002070600d0003400b00070f2070f09104614100c842c51038008150f5041041c2c5c9038540402803c280500c542c0000c000b417058503500501940c903a00074000d901907104030f0404602900c07180300702c0351080783c50301144a0f81003216100b140c140da0f04012311400d9a82401801e0b0f000b440184211420301c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 218317967 1250 218316717 218316751
    0x709020313020901031b140f040902030f06010e040b090a0f0303050702070b0c0106060219170d11121009110702042705070501031503050c040c0e0a0902041401020303060d0803 77
    0xe01d41400c0742d402544506c111415030490803407401c40c07803000c40d08641c48421440d0340c603c095a458908182808a049400003506085880000d18090713825102200c1809040000600342c0800c103c11031189014544440b44d50791340300b500d1911800f11039001011000d0580c0e001c40424481c1d480075920103460700480341030076140c002011a41d00408992009a0344803002030100c0b9a0501c0018581259039181d1094000d0700d68519041e422002c1507201c2e013410114000740515140d80280c1610204100791560350900c005050050b0b4504950362901c10440c40300000e1440c016100d042156425205607508201d01982003101605411100301c5880c1d03c10103000d400401500001c1c0e202a214500805820745402c0014041c5d50703000590b15140d4032448020000701d0004074940760030340c1c0d0440d000503110496003005d0f502000240c44680d080b040c00340012640c950640d0007070040e80c00d0600d034500590200c0c001260351340b10444910360070018a040d0200000c3c2d4a0000d5078002102990113070b485 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 218319217 1250 218317967 218317969
    0x150406021309091e080d09080d0501030807060e030405060d090f2103060501080601050a120e010c05040806060a03050703020112020c03191803050304050f04270c0f0503070902031302 80
    0x1c1026004810349555407400082042514500b01c450801c50040256403903125403203280280c000c002400440710b81311461321040140c084115403884072415002c00095840b0706040902d41c00040c012140700c1d141c80402c562462001040c0c0d4100d6070000e1250740740c00b01081e800d9000e4004440102da5824900079040c0001e4a03200c2c0d84502c40324007460014480c402d054005080c0c4105501030390502c182c1005200b0140da021080703803100006410a201e261482d015004010012a01c840f8400e500e41100c0d0591181d0000080044902e840100e0f00705481c0c003005c1041d060313844d01c801442c9038820b8004000650080f114903500360f248030380041c2011407580328682582c0c0007010002240c1e4028065041480e04003885408039440f003182c200f001f84c21580e40c40e95038400e0340902c61081d11250b1503e000c554564010170401c40300da9417400c101620614a80c0319a4041000481d940100341c0004a08010303c02d4150341200c4c00100101081c3e890501d01c84004d510243c11009183d041440c2c080c09 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 218320467 1250 218319217 218319247
    0x60703020f0a060203060310061208090d0b07090f0501020708031207020718020301060801150903111306090501050f01050c2a040e0c01020609210a0201330e040515040602 75
    0xb4850107440c2c0542d0744e00e40881014200280681c0c28442d446ca800010f00008090030320f00008c4550224405940781c03060300001e01040c0e03100e1f1000f0100c1c0740490400c0555644503030351004454600245542450b02c49005a8030b071800b0f4014081541c3c0140300183c540d4150b114002d4001d10341e8010369403403d480d141d4440d04007098401102e001a00000100049540010618018000701d0141c0b0044c2017054030041c44641d541c4000b402911400110f410141c0d140304110000c1c004156003044400d03510200017001d8202482042e10504a540c030350003465014504940c04142000301802c84010804804645126043e46104900ea407030404000a601c1d644a00c0100c124550300402141c52070200082c6061002810030030107400000c001a14400d10f5175104043c01140d016440d01c82ca203a40c8100c3c01401003607158400c2c00c2660340712104200700c407810310351041e030030345540740d03449444969500d07510070f098070b00034002c2c1d2180c1c0114055000c5001c25a0b001841070f10301502d0a840c00040e009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 218321717 1250 218320467 218320483
    0x12030d050403050f041508010f050d060c091211040507080f040b070909090f05010f02090303090402180409030f1404154508071d090102090a06081611030306060703020f 74
    0x1410000311b484510b04990081c2d000c42c01400c404145206407814031000c41c40511071248000c0480340c8074070784007011034041c090b5603010781700050b0b11845000607420031403c5025003000142c000d0303143c00042071400d031091b002c0610440c015070341009152600d42d41d0081030800240803200308000007a0115809025014820f1190301400022111614070304015085440d418001400b1920412100303590b0380340803090350310009046500503292640ca0000c00003c102e0444117640c041d242c00c051404042e040244407142c444507584401600b036803601c8550580c4a6401440c0c0c28626118061102c284103a500b5564022100040c0401d10905e41912031b00c1a048180441c032254129004c90001401140400c018103108000f000414030380019200c0c0503809820807682e0001400005035200d009404842d03902401a00141c500340e51401c00501c0300380259400c80c1102c0340b0105210078944104d038210b01d0301c40c2c01000f80d407039501d45804011039070b401820120154040c00440703402d06030f420700c1016 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 218322967 1250 218321717 218321729
    0x2a03020307030b25090504180b0901020a020d08061318020a0b0c240a090807140c1c11010f120501080319050c07030b10031202010c080612030d050403050f04 69
    0x4007080c2032103049900100d114041d03040e015401000c1082d00294051078000c1181c005450000c8c0b00a0f0b4042518440280200c025124084100600c092210154028485418039500303071420710000030300c01c0354628003d44a5540c0560541e101d00301c0116a035104612484034296503112081941d40420705100043d40403080c4007101242c805000076003401942162100400c0c022406200807030428003100001c0d0500400e281e50310b50315010485080c0841e075206801811555502c84001e10380f940c0d82106034001c900510035198498842c4003a180c0d0380070003980c401c0700714230103024200c0112080c074400806001001202e81410900c208184100342c0a070405001542d03541410302c0503415901c1070a510707001040070401204d0301c4580003040b86010350b07901c00c5580f04645c8030300d101a445884142c001a20860b240c2e000310f40700782d405510954500e40c1c0b649440c4d00558440080203554032004000f41c0d002d82007001001442e034403a0740081c1c0e001c3e102c1d00785103083c080030340f51130025500103401070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 218324217 1250 218322967 218322983
    0xb0c030a180f0c120c09050619031104321506070c1505040e0109050c0f040b072a1404140f1b090f0105212e032a0302030703 55
    0x51010b20202d640ba841c040e160392212070b25102855074171801e0300c0b1300a11a884c0c5c5660b860b030108800303640f52416024541d1501644811698a030301348074899840c00e9a02d40c1c07281e403411110380810009402035001c6040741202207590001309041a02d08070100070001c0c480914070011410081da210405040c50324095002c029040e8101a00603c1c0319098000007020b000c2c043c80b040119080401c0d5445c155034100c1c03c042070f503881c1c42034480c900d070040e0b0307200003040c0c80c0105021a0501c0f03920003401a80303005803642200020700c40c0d0300400b41d5041c00e000d4665100341e124240034420020f20a0000608003410000e003060f40319120b12008042616601001e04000050041c4419114076050080d030303659098619041c0c40400280c90901c00e6000203052100104468080508800788641c00c01319034030745e9903e1454601291141000b00d220030724900c2000341180e80c0302c043c0a603003110503240c0c0b01d4202600d100c40c0c0031200000103045003200440300c611070004001078070207100c214000c510071260 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 218325467 1250 218324217 218324243
    0x30b01030f1e0b0415064a04060b0a2610080d0203031e25050d1a060406050913110304120807020c060a030f0519050f01030b0c030a18 59
    0xd02001e81c3c51001205100728201580012900c861120800c103c2c0d5650074880150022100c51b5000c00320746c004654440300d200390303c2e110f0b081601c4602d000042044450400380c1c1c6026030030031040b20390030301941c034800c0800c0c0702d00881c6901420782c082154a42080d46e002e4010200882d80c4000d0003203030710342d0030280d0751041085004070030044000c2045690000e5811464040e003640a0b00441c1d004104a10b22a28041203801daa00c022451003000003074404d070410801c9250180c800c1e80031300007010b0081d00d09200c0c141541c51580c08001000c9005080f02d14051a15400310b80981013806099071100c0c00b0400d40004042c50b00c5080034484442c004c5e80d44030324143c200b4541442121102d007062140f014100042141c0c0070494480195044840c2c0362a41d0412204400071701c0190f81000c0d40c40c2c908010721030f6440e41c0d20240601140e0302c04060240c0d680b03041c0742c00d48000080c40004e158100c140003040350451420051548802c0c6a02e00180705007081110386403032244164182c0b4007403429a1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 218326717 1250 218325467 218325521
    0x11030408240c120403052808150607030206010b090402040b0703181205150405030c150612010e0a0f030302120114040b040b03030d0f0b0307061101050702061303030b01030f 76
    0x10000e6200794078602d081d0070b200c002c1201e4a444030300100b000b01002000a1004200c45510f00c00f031004500308040e2040000c1c400070007900d04213090310305800d010410070524129182080c101c2c3c1d0307900d42c0350b0301900c1142d07e0800c0c41c03041904903800349030b88682c082c04040390011301c240150021502030707a180c1c0440016a50800d885c0c40854101070303a051260136000020070310024078210704c0d00d403405e07440070150390701e04002d400c500070304440050601500c81d0784808100c5050384640118400c492017141c800d00b50b580c8608981001d40d00c0c29054000e9070355032001c1558082034244a41c003030b040151410099003c400000384090300081c0391988424a40212030402c0c1c450811042c40503581006031f01108000203a50b40102d24242181d41d48030000b5818000d001e8010704812040942221541511114003030190300030442c00942a42c40c0c440013441c0280700080e05e90040c1e804440d071003084810b6480c01c60151201c0b1040b0741c1410703210800c50712401a40e200d44407495240c080d104400e585698 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 218327967 1250 218326717 218326783
    0x1002070e06031c05070201090503030a0309020315371b030e0105060109090906061203050c190b0103060507031401060f0f0306240c080f09040605180711030408 70
    0xd0007160007507000714041400a940305043c1200c540d218280103803129003600c0102c0f800c95494001079018080410305801039a00342d00400c214a100724142c8065210140010706140d40440e8640c5c0714051341766001c42d001b07411411080000d0044420260058030040c0040305858100a16008803102d8070007403038500380d0502c1040394000216001380000d040c130344002031045013180a010362042c0d840320b000080080c0c40e0b005030014001340180389039000581c100600240c000c002d0114450188480303032051081d14021019806500075400e02081c1d080d901d400c8000d2a00400ca1018555204400003818000002030b85c02000c056503494400c00c0070280090a03840780044503000c0c14100f60046c080c00c100700c00198510800d25550085501448800700e0714107003a030784007074090039001564110720119400104410302d4141c509112860781c400501510924402001c6032000c212400b10320030910406611401441c64001c681c05e05031079098243c200641c0283c200101e92403601c4032600000e0035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 218329217 1250 218327967 218327971
    0x2031e0a05090705040f06050d0c0608060901032013090f12050421020102011b0c050120030406051b0a05030103060501061110020a02010f090f030306270b06091002070e 74
    0x290014000d40c00c040b110b0741ea8504250040300d210b9a1a5112038881070311a600c42c1c0c1c0100002007039408030745910700341445041d0181c000c8600054001c1d0006885040429a4074120303079000815600c0000d040000001c0031031610100b07030744484a0400420b0264280c080d503c060390003104506855034562402100c0b0342038071030001d0244041400204842042880c090b01900d0dc00c00700003220100920040340103154117031000d43c0c5140c4290112110b60b030300c0801c0310b501d588520003c0010b01400c0c00b480185003840b5503800206402000080c000400348e41000390008180021000748070080c00d00800c0c2a00240d0b510300000d24007100420a01140740200340c0148400e0030840101d0010381c0c01c9903102c046441e140c10b10181c0001c4d60035000384c800d620804102c0a010400c00c00d6406500d04041c0061a02006400090500e4030200b1442400d41d0680c51030181040401c0c051828841040080d201450200760f20810600c11145661520400b49611341419030291000d1030804220700000600 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 218330467 1250 218329217 218329231
    0x30f0a0e0c090603160f0812030411120f03030c070b01120503160819030603050d030b0f1e0411030601091208070308150406090b0103060605030411120f0102031e 71
    0x1456003142029802056900c45a03005450400441d80c460010916080f5100503e0309200311448002580c001c0006100c015154240b061b1884201c40568a100310300050b2805018000f0703c540c0d083c142d15116915880c401c0031039055a0140321014400350450300100c0301d030b1900781c800241c0c0c02c00b003140702c0c0411800352a440c0c404500705110350712060f999005595040f510b0f180e10f855440117012981080e682102100f004141c80d2200850004010f41104e210440d49032040175100f00c10140079004074519100054203000384204044204a00d4504122140c0711900c0f980341c10500ca500c56001d890300d41200107154aa41341402400105034440ca94002084410a01d000100156144044428198141c030f071001107500c07040c1e410703100c0c3d0f840c5d000050340c418a000c0f400111071195030031004001600340c0301082011f94541054503e0312003210300508203030704018000028500344002d0211406810101d441e010302100c1074600f2a4000e40300c0d01c10702000a00d150000b000e42180301540210 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 218331717 1250 218330467 218330471
    0xa091818080a0e030601030c1401020f16030b150d112202031e0c03150a05030a050a03030c09030302030f0309010605090f010e280c18090506030d09060f1b0f0503030f0a 74
    0x81f66032540036103447c450140425185010000c22803ea100b0801001c07449004800d50303201040070341c030110040c1202d01c812180012840300107480b11301011f9038004c0700c6070041c00c0f0b440300310307074541e2030158100f0484801030740907141c4501307503ea00d1a000920700c081c640347d400042c0e40e0305004503d09403203001d0030b40b40140e035030340c2904100a00085400b584c2d0041d46064412182040c040c00007040e4450540000e5018411032400b030f824072100040e002560f50080c0c0703040007045007420007120880658000500568001c00200c21043c050000441d404030000307000259241e2610700242000f08161495001c0800510060084441c8490b64903004403101c0e030889804000015003001c0c3e1006c1c804082101951000041140303070084e107019011107845540c41c10350585030043c090040071306075034840c000d124103100c4d0071001e400b4800140c203992850721003c1c210b4150341c208a071444038a921143c0f95014015124002510b02441040c00c070307210f40c0103035807207140400b09100105001025455014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 218332967 1250 218331717 218331719
    0x909060f060f030326160f08011202010c0501020c010207050a0c0602210901020a050102030907080606090906011a21060102011a061608130303090512030a091818080a0e030601 77
    0x10702d4034407422040b02d50504210810301c3c06006000a403204191a11051070313080c41c2004044410614650b604901035111f28610b410b140c2000c4074411000d008651405031000c1c240380c0590f000e10391104a540c403807800540b6001e4810340b504d0990f0806038045409500415424040240035465040600554401892100181145410400c10202201c031b1803110019181015034400d12a140603950000d00039540c80c10f09182182d038a049500c0750131040c2c0030b4080031459901d0140c056034061420b0780000c000b140d080000c4440301c40d060320070302800084208078400384c42c042d110148580301c10b0b1921803880e80c41c00380006420340300c0250000d105000c5800e00c9021aa07118001d0700c0b20490905d444107840c02d9076207401e80b4244151412441c01d8184414000300b0140d004c1c0000094420540d10a42603444002c036803170b5680240e01e25403010414015048c803044070b0303103507030000c02c0380240d40041080c980c110450b96096030018020b940d146000200300d2034907070300b250140402c3c020a0f80141119 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 218334217 1250 218332967 218332979
    0x12020c1b0a0608160e060c1219030209030a020405101206050f010918080c0c12010507020f06070219020a0306020a021b0604060206060d06060305150609060108130b090102130909060f06 81
    0x18110f84d481c0304060109858a41c071076526040c06580801a220003240c0390914040050182a0003508810300150443c10340048081d219009a80400e00042e0044c035488a00394200030140600030041d444404084800040c0c1c844034041003e50240903000000c1d03207040031515420020380c1600080c404074207086040800c40881803002c22100c4c0c0007007200d51079501129100e4100205540055440a11119403810800040d404980a070420380c003100c3c14000541d5039503444040c111195400b40e040014940d1554200d400529080c44c8000c201011182c1c8940d2074000300d030458040100160703c401c004224211002c088c80c0ca043e9002c0710032504141c0360240c0255034580060145015134098407144007044103503080715020303603407181c2034410000801c416480d0400040700d0f40c910810340703040841d82035401111198080c0854012569513007030140c4880c01034030b40c00340c40c800080d9402c0080c860480281e14080c8054072003403001107001e880909144c0142c94030400030034100c41ca040d400f000b003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 218335467 1250 218334217 218334241
    0x4121d061603030209130212060118031205070611030612060c0d020903070f080a050106060507080412050c03010f0e060f070509090c070803070e090a0605010f12020c1b0a0608 77
    0x4240da1812094200740403074a0110044d01641c506560445540000c055501803560003400d03c2564602c41e40903242d945200440785071444490340205103041c00001d0020032240c0100314038141250501c0c03440c1c041c1d0759440b001129a000052145d00b4808400e00c400c0b450194090740f08120b20000500c91810840f02d0154140314402102c14200c0d40000d60015075202480f0500c010710020200187d12a034891440351160080801140d155280c1900032403440e0052064801c83d68100441904090a0940c8250250f07604a0240c030a4428900d00c2170145ea02401a40c00e40c9511000c041049444140340600d0620054a600380c190003010421100d0307a800300c2542c0801d03100b00c40020003503d07000d840104511072000047e00703e0600008100e032483d0840807600881c0000e488030000b03613640723454020850341c0500410740004c240340c0583c10314620840800000c002c07070309001803800350000c542030702c1d26407458114882c01e001407500803d10700d4198051001004942011451440c201d000c1c207070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 218336717 1250 218335467 218335477
    0xa0e0f0d03090302122b020408030702060d0b280504090b15010504030b040b0f01080a050c041d0307050f2401210b0f090f120324030604121d06 63
    0x4201955601070b8030605100f0040400c1c079803d5160383c65954802141d0f881d07900200d034201c0d0703040013100150341c521090140c0308079411220b180000d98186005a0308000c1c0b285e01880b0f0b00c504d116102c00308456a540c5014481000218088840c904100301d0344038420803042c168445e900c500d01e441d1500001c50401654194051600c403100a2281050b00c01a905402203400107172191442404110411607d1aa564064010215400c02c0c680c0d03250000c542d40d0021a030020842c0c1c00070348040a00b410560132442c503890301098405121181605102e02d541c0043c8410b0b561a446112a003000d0300d01030216990000700040399400800e05500407001011040c4920703029101d50b441c1400ea181d410344074914466600403a285501d0a007e03910581500c401e65149941d402402d1640c4ca4071072002440030a10719102c102c1604541e0381e6a01e20000c04000c0a4000742c00350f00716000180d0340d40610456110300d102c4c484400702d546021070014102101061106441c2081c20f020b10302566541083c2c1e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 218337967 1250 218336717 218336743
    0x105010f200a150603030206060d020d06151a070b0a050f0408090607020d0302060612012003090c0a1d0a05010f14131802120607050a0c030e0312030a0e0f 68
    0x8103144406689882c0382c01521000544500400507a0102e8161150010030890303000390700721059a00d5010030009a0360b00c400c0700941c004010034106000520795001040384016030310260020681d21520700907000b03801c40c10301c52030074000138400c01008a004130322600100200d000304443e00d0b150600018480780070b0406081e510303003c149410300c0e40d280421116940e50107032600d0102e080c10700e0041e5858505694013403084088400c1440302840c140f0544080000d900801082c40054540800d91580083c04861082c010140d000c1500d44a030400300c4e0007800d12100403c04100040104210404c015280e00601800c010041000c0c040d03420194083c1d94801200c00030250512000540158000c081c103c0038508000d0381003644466031015005443c001c1c3e43c1c04403140c400842c096101d210854102c8041601807243c5503003240315107c0800c0c118070904020600d24500c000291610510359414090080c2c00000c200c0700c1c4405009100000380800c004100080d40107034910b072120a048000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 218339217 1250 218337967 218338007
    0x190210090c0317041211090901110a03090c050316051509010e06210f1b070f080f07080c01091203090308060108100e0c181503060d150c03140105010f 66
    0x1422143c50700d40843d001025510001e2020000f1443d00d003c0c9855222135261048003800d00081080344117014204000700f802010619010701c5030300c103030010081754000b5652076a00314400308042d201000b688121034000b1040000c007928140c100400009038140c1842d5080b03040c42403a0305641c02c1400440360080031900c241d100c61003201c001500c1c3d0600089081c41403003440901220452442d0402d0081d0044800f511000713159800c2c030140b40c81004001084c1d41c29420650b0302291144010300b54440d00742c42800d00d042c1e600d480d00007458010302c44001c0141d640350590003c00006001005031250241230070303c1580120384015118550042405061000d1603001440003400c0450100248c0a03800c0c81c541c140c01e1141c0090443d41005403003181030010301800100b1890003000495803403904003111071a664030310b014040c1c1550bc2e51b0f021201c265281c280201c4840c414000d0542226007a0742c001111030743c015030b08508950690240d41401082418034460b00e5001c03003060140e895825407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 218340467 1250 218339217 218339243
    0x10060621110d0e0a05010c020d02032b1802190302090c030405011d1606141c0f0608100f020306030706120204121505010906050a0306150909260f031515190210090c03 73
    0x6994010310080d511240152400d10137805900d00d005025064500945000380d440b1001e100b240c5000c04a400017070b40c01240a0001100301e01d60500951b0300a05c164000709400c11004c120905445260ba81024a40c000d41c2e41407800c4200c3c501c01000501541c0341c801601c074a12301a00b5407900c20b00c1410040c140b01102d000c0849009500708001400e03108004004155a86940d142c4590400028401132811702c854900c08190030b0003500e018410003006045d820346032501c183d43c0810700e482d0b117891450b0207100c00181380803000b05c01014203000c2d400540084020a0912044403c140c100684031840c1c032000380640d4039014110003c0d2a80300c40000340c00e00b0206603c00141e0015880b6102a0f42403554401c100000c076209040504c03400c2407407015a031030700b0000f0b03400c5000300c15550f0780301c2501b88000f8202400c40c0000c80d058001c090b0070001d0380b40c07140c8513004540d4403512000036120460800803480f142d04000c003a051460007001000402c40c6951403092040172403002400268481304 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 218341717 1250 218340467 218340517
    0xc0b040b04050a150213080c10080a0f060603020901080603070806070509030a141c09050f041805070626160507140303070210060621110d0e0a05010c020d0203 70
    0x8510703e409500441a450280c90008480029521030180700001c2d02002c0c02c0010111000103e00c545180c0051262980703404202d0101c41e5200000c0c11102c11340d44441e10945964a42e10803400500641e542c0981d9131140507001601a10025112038001d80c003c00d4204258040070503465000100d5207007599403105150001f0b4548101d00402401d6140d549020003011040028130f1444400042c0301c01003d42d8080da41a0340f80003503407041c650840d4203400303038600c03134036040d40310841c01e07680b0800d100b2400e1800d8803114030304600c2c0d8201c1c2c80030030781d800103000b41c588002c03c601c580c016400034104d07024640744d41b025000051814030002030100115100d003c0201480c0c0d01c8541c0c070742001c1220340b00d180c114802540c600c0320071a02c40300301d49400f40102d8039902c01e086a903405581e0004c5004185800c0802400406d025008414008400c0c80090204002c07030280d403858540c9134000b40b40c1d40c400d0341403c03800c507141d00d407021055610070406162010380200564101d082150705444900302429 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 218342967 1250 218341717 218341723
    0x907140f03061303090b0705100f0221040201030f0603080403120302041703070308010b0307022d0111181c0f032303070e0108221e0b090d0c0b040b0405 67
    0x200803160305020b0074040000c1c91019000001003c1d020342d036030002c90303540c880f03100400c0d128048001d4103035041064001248800d61f000504c486090440045c07400c89640a07140c031004001e164029100300440a000640d0b070b01d402400003007500418200000c603d995a24043d5100d00d100041248105201003250f240c040d42c107840092900c0d03981c005c40d203103054120079201d5100900440201e0300d0324001141071011041601e08c40c3c216038000307000d0b040003103c105000c07001c010111002c42c0091f045000c1c42d20030a0007440c60410004084940343e41008175046031030540b000820340101c8078031514076040b0304070394807101740c0781c0d04011070500d40071036170800310f82050070714030100ca0b00c000c1c03004041c4003031140d88004d510690340f82d511442100020401100c10386030644a150880648414a80c0341e25500c3e040c1c4048541300f10326404020900c940709030702418289409079195000d100c10019a81070038094051104030700e18241702200d55a40c0c403200b451002500141082c44900006001c1040030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 218344217 1250 218342967 218342989
    0x60506060f0c0d12020406092105010606091a16081c06030f060c0801050603010603151a0403031106070504091d01050c030603070506031009180c080c01031103090714 73
    0x109201d81c0d680310b4984915590030068803044009010000c6980c1a06070b01d2084d101510065910f120350a803030708824003d5910300c1c292601203924411502c20006030700b481007400900030740d114212103d1805644021505585080c0c0d040b80000304a0000c4014148a000c01c1c81540b10f140303651908071302007640c01c103140c85e58483c1d00e03260714120010080c0000c000316668554400c19007848900c0710354804490b8104280f00390b9410610500040c80724074025008074000c03c84c107901d00702c400369480100082042e0100f502410b0104002401d10a0590102d145840040900001d003614184032000805a20a030311902802669440038002c24100c42d410312414882580b000784151f0600c9096081c00e075000b9911940300c0e21840e2000500c50508070107581c81000c80c44440c514036442c140d41380d009402c1000b001c0406005020500c1d002030304480004016010000040c070701604501c00250489049041040307224009000700a030b1410300040302410f4a0001041c2104068604007280c202100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 218345323 1106 218344217 218344237
    0x7120c1118180a020a0b09090108070f03060c09090f0509100c0206040f0615060804050607091809060f02040b09040f0209030d0e0d060207120807140706050606 70
    0xc1c000b000380c1612020001d907001c90141c2e90000356441495044049810408035560480d810303e001c0781d9000d05042c6c0014116503081c9441c0e4081c0c1c00c11807000130291030b182c00c05241039921440c4084018a500380d4240302070040c03440d240002c1c100480307091180d8840c250108454003158000c112846140c1d802401882d202c54903941592100c3c181c0031f079a01c2d500c4407941c055003840d11041d032008107411b5503250041c3c00c00d0f141050404001818860812041d5401400680800b20864082150b4004002840e81162410718007070041d9486080c0e071399201240005503900800c00519400b00119010400816050b0003c0204c1c013500074420f40503030140c560080782c140070302203907082c014000300001100b1394140c4c1c6ea0b20a0340e20401d411501c1d800810f003601800b0790459540f03078000f500d506000580c04864056031406014070140a80f01c1c503240c1011602039213541d012980c040c18 = true := by decide +kernel

theorem cover : BRFrame.Cov 218165467 218345323 := by
  have h0 := BRFrame.cov_init 218165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 218165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 218165467 ≤ n) (h2 : n < 218345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
