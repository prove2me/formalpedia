-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3229
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:02:49.827295+00:00
-- url     : https://prove2.me/submissions/01a04013-c48b-4fc2-a3ab-83e0d8b6f818

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 580575539 ≤ n < 580755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 580576789 1250 580575539 580575557
    0x1030c0501141209071403070e0c071a040605101e0527010f0e090a0c120c0b07050115050f0a031412040b090f09010e04170d09061e09080415 62
    0x1000a8a903c015903010089034031000b02042000b40a401485040038114041e04003a0320749904191901c400521a0075a0140003924104010402d82c2d810300f01210400640844d21b02403070030b40020311040e624022050028500003962444071020f50748528000e4444070b2070140343c00e050000c515100440c2d41214848041d800c021484040e101d140204503001050714a00d16040c4e1800002c00003601a0060f034001110400200f1a07201d6000211502c150000c00e040100381800940416180c00c288145e500004401037032010540003108550300043c41592001d41e181b04001d0b000300c889600a812092009040010464220403003281c5480101600c01e2050a45c5824a00c0d5110343c200300c0001002041c000400d040418815000d10750030780e00d407a40e550500005502d2074800800040024100c00c400740300c112605815902c030f0360054502440340240a25011000d17100d01d41e0080e0001c500c60100d00c01c8a18180600104140c100c0b60451500d17040c1100c01e6801c2c0343c00b034659000c0c071039410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 580578039 1250 580576789 580576807
    0xd11010b03120310060e0a180912080a0c0e01140c150f04060509010501030f080d0f15050f19060f02030721030b0f0109060c0c090903020109140601030c050114 70
    0x310001d004079005800c043d5481c60720701190009402660000002c102c50180741c08403036220256050192511300300c1c010303001020382e105034020f00b0156800800b1507003d58104ad041d150440c040b10300500546005010480c0d0b1144104c4580c034003605034900150b40941d4541f00c0d414550014070000001d982a1000c2d0800694a642e1001c8143c4881c8046410700c0c1c00c1105101151107425000403c2034028012135245489005072a9402d0340c1c040c20140f000208031304c003403031264441d0a00300000c42c82800122a40172015000c4500392060a0140e40d100320030042c1e0b0b00e084407034103600d0400305250440860609d101280d1046182e074081c010f511007000000d002c00d04031042c492048524554900408541a40c003d00781c44d290070705540245649450714640d42c0e04280090240c41e03407440c0800203a04070b0308051069100d194020010649040c1e8a00140b60b0f06410440005015100c5a01c103a0352a10b546030392140c09100113080e00c1c40542c000c0c00300d0341c8244034040206924001c0303581842250 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 580579289 1250 580578039 580578043
    0x20609030d051b010504051c1b050106080f03040f0b030907030b0c03060a080d080a02030a1107050106030203070f140f060d020a11061e0621030307020d0305180d11010b03 75
    0x20701c410001140000ca080341c02200c0b0400c00b100b041c0d00650090141c0d050a5803400d94644514440c04a446404402d010015128445c031201c0080e00e03030068604115541010360083c40c40c4d0103100214043d1500031100f5901c0001140c0480e81c6104a8907841d0380f4041c491000f0341c00251102080d4014034900001091a50f1801c90080604800301a039134203008080188107042c40d40441e115802001036000c4043c2c000031083e0b40609500c80141e520754409805a0080c002292215601900443c0300014800154410800d8910a070200d454054030f500e4000c0e0361000a2040380d9a035000204600c2a504044ca1024405c0801416080c14051507090080c1139030440c0c1210000104001100c441c1c1c0c8500b00f11207608000390b900d1210710074024041030025000020842c6014a4100c8100c20b4001403051138000c460504400b541e4884c146001c00030745940038001c4640003c4c0c00d080129a6010081e250b0011441c804030041480602289003501d0300e5401843d0540315550780c1a41e50340e55142 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 580580539 1250 580579289 580579303
    0x10c0804260a08102103030c02210408010c0206091011070807150501150c110607020301060b03150a2318070e090907060c0f1b060e041a01050a0c02060903 68
    0x340380c03186407061504a05004200c62030b640403850040076081c2c0c03861413034840541e20000715014900403948c641c500c00164500481081200c81414041a010a200a032030000c1c00c02c0d0b41c007800090016800c00034049a0b24881542c807101607070080c10180c0713040c95840d44800c140d26a5002d001c1c2c289500707901d5004540d04445c10036504031403180f82d2540500400e1050780c1c003401e499a4440c04024622500820400660b5030040166500503d95000c1d0b0359001d05603100b01e98014024003a036501c90300c0181e00e0f900241c0b000200200d0029494039503140641b4610151408551180810422614190300319180c00500541000c941078000b403400f80c0a90016120f9a02526907900d0800b07950248071071070100070080031158015420a0203450f03031111900c05120b401c01350b001c44000c981d0901c0b598501e02c0e654052811080305400280c680e030802c190210500007101c04101200355085110221641d0449150006608210b0f1901c40e81c022040c00710303103d0000c1c00403030500384103030003003498911 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 580581789 1250 580580539 580580557
    0xd1a19020a050a0f0306061d1804111203030405031e09040c0201020c19020a17030c03070b010302090a0c0e1002071703040e0c070b040f0312150f0602010c080426 71
    0x90010300000c40703a0300310540c1c4c0c500400c0c03407904004091801500070104801c407000324902e0b0448030003000c21603907084080707081015858245106070901c0d1034408158403080c68440c0c09411844c40c00131412030040107880c41250448065494105c480220100703824030030084029140f03041c041d0204070340f039502c0b842d00b800070349800050391003851102180c900201c1c0d010b42c0c92030044580d20f400060315032407000000ca4101200800c10300d45028001b500f035000d9a0300d41007442c4800728803074060000c003260080c100c074000e580c20400c9440e0301e0940e105076200401183d0100b13941031381d682d5060825610300a0030302c01601c156080661240a00000c04c162414000426800800c080c009007550301120383e000a980d0700400d00d0300500340c4e100300c406039000303001505100d0008602014540214400701c00c04400c2c0100704001100030313020740d2540c2d006000d0b0f912016001040416070a00520424074002250745031949030366502e0b683c07a64502400042e82413064541030b1641e030800c68007000b8040e000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 580583039 1250 580581789 580581797
    0x15061e07060c0206060a0f1403010207020d060c121a01081017010204050f0a03050601300818011b020f030102071b14012a14030c0a020901050d1a19020a 67
    0x50500b04009103000000342109208100101d0300f040f005808078891802c54240c44205c0741c400400c100000d009018100029411aa0030a00c52042108590009a0009050300d40100401240340307010202ca100891282d0000d2400c11044490341c09640c2d0941c0c000c0c41c181c1c08040f1161116222264102036104000c0ca5030b401040c180203d00d4032a80e5401a1f203010348044c90781c1d074519143d040d91001d0601c12622803559507440030762410110140e0030058950358031507a03a0302405190031052640041a404003980d1030310b0130100c5a611588003034040c42c00c070742c0406004480c140c0800000200350001d2592640d400c001140004d21420910001c41684008850304075141003000c8040842c401e00c0a0704200e04000301103031a4181004e1f5800e42866040400392090f9a4907095583d0291541000310354880455203c054840006c3c40055079807082d68260241c0c0d07601e83c2031041944040500600c074500c51034600e40d030a4181c60000b0350086402c4119507061101c02c0800d0b081b40c0c80529103030006 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 580584289 1250 580583039 580583051
    0x2114010c09081c09030b09010207080f09040510030b010918150c0807140409020702120703060f060503030304080304080a18060804020108150a090c2c1815061e0706 72
    0x10070700c00e02c1034184041440c002c0d40482d14040400802c3c00c1c4e050300000303080c080c640011038264082541590401d51340000d01c20b03500d0827001074508454001d42e00e80c0d845681444001356000c0200002c06040b2079200e22403001a074203140130031028000c2060880f2080043c4c600d0400800c035094003205101d03c0e4601b0000d07280c030555400401d409002402c00301849202e280d01c80510404c4000c41c1c00312042c203040143c4400991001a140d094480390b440d0151050000c080280003440c1e000c10309410400030b00b001203641d241c05068880c001264080d224040c20310028010490031401031480c185a0f107000e80305040d60100c5928041c6440c1c05c5000000d520070200011560402d94598221406102000c96400c00c000050380328503c1d80030712110282c558428a5205001d8008840c00d104a8014200302d4011400130340101943c64500921038507981c1c481101e00c69a00c12058040d070700c0840c0040740080714605001e080d030300c92403061407100c0c1d10384800280a9140005040c2c0a4400d41010400c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 580585539 1250 580584289 580584299
    0xf0203090d0807060b01050711100507021002010609050a090530030103030f021027020604270624080903090607120215090a0b040c09050c21012114010c09 68
    0x4032141c2c0a505ca0501c1810090390001c140ca0480044081204484010840e84280c000700c0d81c6000353341c0000c2d040040c0005815002d41c06401820554059100c200019600da140300005d442c0c2c2c1140241460300709c0361100c80d0344076086200851072402d0a031440100b2810111b5203003d640240d1060700018031100c80c2c8400d06505000d002004d040c10241401a1802c0200d0301010740800c80501c0c01c5401e00540b03440854079003100384c60003082046041c4462480300d005401041c0f1040d000c450b152860210040b6000252410181d00c420b030500c1c0200c2c003008814000e84d81e802015200000611041c80b8010781070f0346682c000c0504502c04c420184d1903c8460178040e10785003c0076004040005104108542e0010019100d44003541104003c3d441d82c540d82008001403000307130485a0654103160401030715a209000071320031011010141c2c4e4441d584000d6500440000780541580f009481580e05040d00c401c44c4058080d90062150030340724890384020500311040a08a44045140b0403c2002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 580586789 1250 580585539 580585541
    0x30304051203010302150313020a08010b0108010905070e0d170f09040b030a080904110705010c0801050907020f0607031119030b10020c0f100c0c0b040e0601030c020c010f0203090d080706 82
    0x40805500c01c80d0608550660b400a10709001241c80e03c69516400320001d400c207001d60108151154001e09201c00c4e940c7c0b1000524060f2020580742408908001c0001884100620869100791710b0740e551800d2080c6490108110010082001ea542664140d00744000e41615030050109047e46240599640601e00070703c0107468410400d24403a4002818181c086404c01c0101c5240d00f204031400904c807002d10450710400d02955401500b00d40ca4074101071445600000194142d0350201c4960b801c0d5074810000700c3c0d48400d80d2503140626000761000c503140d1400380e0401c40c0b4240032a64010705002c40164252a41c01c0c40e8440480065104c1a5107a03450070005550040c1070180e2020b400f500c684440800d80142c610700300240a410701095000c1098030840d0420070440c1d010207070300c815aa40320300da15040d82041c016a1035224622001c01c01560083c0b140b94460079007a0003500c105215500152090b0700034a24502c1980002c2000c550503584074442a21064441e008440e10780c54a420000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 580588039 1250 580586789 580586803
    0x15071103040e160f0c110103020d05010b070b060303160b1801150302040f021e070501060b07050a060f0b130f0e0a050f100504020109090b0303040504021b0d09260f07030503030405 79
    0x1030921514113030f0f168200364882910707040a070f00807a01040300040d20004038000d1180c0140e50000f11307e00000030881c4e90810000344102e0303008048800caa915810105912072003140315400072440b20750801c80010f51400209684902c83c0c898050824201c051400d00b96481220141c8069940500a0045203800c1c450b1819529001608505180304110404030b03001001402d28680800884e4220400c0025085407000e4203c4440c81c0c0d481d00d505d45041135413101100c0c01200d841d810700b5a005401841c511540d009408000c000300b603183c9050401200400e600c540501a01c0e895410340c100310300782042882610341c840e400a144011405041030300300440800d41425a604080a11001d80e0b402004d42050f17800940d00095624060320011380345114507400150010300205446d0340322144000f41c0c81c6a4603002059a46030704d2812000c40394070110703004141503d0308441c15105140c00c0040c50b250604041c504803401d0024a0b4149460901a94000c0714142d20000070002000801e020034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 580589289 1250 580588039 580588081
    0x15030308181f0209030c040606020703210e06030604090b0c1308060606030c16050d03020318010b031b0f1c260406121d060108070e060315071103040e 66
    0x5440d0440101d0440664002c07040c000d9149070780c01081640e52a60184401344014000810030400c240d69000041e40b01d200ba0312064424114110300a121440e40900000c00b100e2103950b05c0d104804a6820400c01c2c1c0c002511076030708956622a81c20000d0211070341c281c0510a02d0300010b4482030280943c2c002c1c104103800602940e0403d034184001500c50100b500d800ca00305400b49500c40031500d00860808900d0080039000d441524006004140c26500440c005d100600300700400c00901040142602c0e1200c03a00e0350154014002046030f04000b004c40003140030002d12081e854601800099045100e007103042d1095540b44903080c00704207402040e00c5102410600404002d08503000070069406184202c00c2030060301071004840480540c400c42624000e1214190048a8010081e55440b42400f80603000e109054004c0b921003410b4030160303c1540c0060041001500d4600c80880c4028040d016000707100140c409116030340000d0028102500d440c2e288150281b03009051810f04041031480703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 580590539 1250 580589289 580589293
    0x1509030d030e0712080c030a030f0b10020d03110d0501090506040e0714061e0c150709120204181e022704060509070906032a0b0307080a1503030818 65
    0x2d803804011a6481c102e89072400d04503205034613810961800d202da0b4000040074000060010034035505644007000718201e195003006101c1d028001c0c0b24611500e0020074016a00c0040c05442c514801e80000d02040c07074402e4150700700480450003000392802070b0804294140c456003000fa03581054424511a0004000140081d629065031103c0325000700103030b1801083d0010b030f8030301c0b80b241c0391f46114141101556415031310030038002d929444000c04881c8000302a03420003c642e18031700c10401c7c601620030400510420280c15400c100c01040412254901805107200d00d03000700b9411401000e540181e441c04001c40a064810882d883c000e5007201c20881620b128a112001d441220950b44598400c0f00010641c0300d5140b10b518003009a03010600460802d000441000345550350034402040c483c00e5050025084003410622134698011007001c002c061000814461040d1210750700a0211040028481041e640c045c80d81401608141c0206001c14140030350b2940000040c2011030503040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 580591789 1250 580590539 580590551
    0x50a02070210030209011715040e0309060d0f0605040203010f0906050d03050a030507030b0603090d11030304020303070f060f050c0405031e030d0c09081c08070203070b040308040f021509030d03 85
    0x200181402d500707001601c2c105a800310712119107900075010702010711003040c1d1560752403402115000d05145035a00c81c5004606180500c4600034001054403a00c4500070812410120030300361000080450700c0c80e50400da9103038100020a925140b0086001c2c04603540f106244508140032072043e10115408035020700d01641c2c04001084c0d03c44141c40000701d0500c2e001c40c268540d040114041c00c10300c0022a40540000107010507075000240107087c440054881c446040601036840f52a03010031a0f000e500340e00200070020000d2440b21090f07a20134400c0200003682c851601041d021100121030310038244000080501080ca810000d00450200c56112500c0c419086040103817640507492501070001c0e2a50000381c8103600940b50b000c05828100201c0c1d05c1c01100040c0c0840c010440d20411010581201c007041400340301100f00d40c811604082e5107521601e440d42c00f1640800000c000b510100d141005040050b0f85558050b00c00c0e074103001c501174803982e030001014145090512006e0a06107001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 580593039 1250 580591789 580591793
    0x1b21020d0c0b04081c1b091a1e0d062304151e030215030708071107140409050a1b12110402180325050108010e060d030201020c0a0312050a0207 63
    0x4540158015400038120ba145c04240207040c852022281c80d031640b41d4100038513003601c031807001d002c0c03092040c243d900c0c5002c0c00c1c0d480342c142e84956030048801c001c071001000700c030010700d000c601050010941c0340c405a181003140f000e88404c9641c0c0740c004a29002d40b94880c6944056030828260b100b210894040042d403000d0340029100c00e91900c1400914070030040c1c50340c042d20813404c0080c019900030f040399990442803610320400340d108941c0b00000c200080013003050b89201e468010350701c21040c001801607a0800b01c0c0d049001c5840420b540c0d0140d00c1e54a0000082c1c0305004414805102e41b0b003002040c11104180c40e4542c1198229007800b03100001c003800411601c1c1e1018101d26015500140d8600c0d00030300d0300000000b8240500c0d014800c400d2100009441c03c6680c001800741228103007419902d400044603556801e208001310030140002240482c9011104150740c14403a0000528000350840b15500380f0b41c041000360042a103c141c0480e000100d0f000e070584c00f4190fa00214a421515 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 580594289 1250 580593039 580593053
    0x70b0a0c0609020f06040f03020411030c0703050c1207060207110108061320041502060f150108060109150906030605030307030f0c0323180d0c05011b21020d0c 70
    0x41c14072a200c2070441e00b952540c1e81e8a590020000d0101e60b602ca44071004140e4102081c4022030240d46400c00c800300740b501c0442030303030301071405860500c8c0303861450340301101c458100c03080b959007601a1a04803104901c01c0ca008082051123042c0140e03e030030f070500b094545000c56a01550521985604000c2c061b9141041901359040303a00002580e42a503018910b8907102d10040110403c0d4002408290384039158010240d03000660708450040c1d850040103010598152007501841880e01000c05166014031810341c0d0011061610382101665031040d490400c0401500d4408103074410000d004641c0e05014100203850706030011850080c003580d0043c03d0760700b817030001e0041150420482042501c01d401d5050ba446440480040643c00c6220080d1142d0116030705054601d5a8a9844500d0600440310140d00e5000950180d409180600641c0d81003400701c403401462880e01091300c001003025400c80081220703410890072242c0c0c00100030b45010080848001800a802c0460b4005048 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 580595539 1250 580594289 580594307
    0x1503010c2705090c070203190f080a0c06050c030a0e0a050601030303022b0c0306050d0507050112020c060a05060907090b0a05070204110a020a03120c09140307081e070b0a 75
    0x640328003051920250855801c041d055041035038010820410f001030042e105014210355802141a1103481d180a0784451030340c00280b800400380d01c0300100c00e20200f4100340c040d0900580f04c2c100b11407007900e40c1e07541c0300440d24200c2d0740740e468200c040103006242001d0b100b01c1c215411140700500440030540c850a503910707414032004041640000e440d010703006210f08101ca00c540340080c04080003200c048132501601c3e01504010000c1d2414a0010300c034a07001d172800034840c2e000005070100d1428600110790003101150000702c7c2c550200301907018440e04110061040480400020780d41c1411340c10013211407c09401802000283d80041c840c0ea9140e40484046c0041e1303040860b0340c0c1d13241d44040f5015152266980c9044400070402c003208603008181410801e1086c0da031740c0c5102800121407021200e5281002c1c001500c0e4860a011003c0c2c10b42c0d1801c0c1031240201101c440d25a14141940342080c0180001d5a440c0c410940c085d07031440401024001d41420300d03440e42804d000000040408807 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 580596789 1250 580595539 580595567
    0x607080f1b0313060b06070b07032901080702071802031504090309171903020f1606050706051305030c030a080a1802060306010c1e110607020604120c0902030403081503010c 76
    0x10f456008041004601c0d03100c0800b08101070b0400b0f44401450130803070200803007120910003207030030040032045001c050441c8107030101c5060030703c0f8409240c0c1d00044482c56001488002036201e074920204080c400c032002c591850f000c2000144c0d40e80340445590030405502e41d1441e018034200340c25940003076081000c1c08240c0c6c1440c0c0301444556280711a80d80341c18a2803180c1d5450103150707035080303061507804101f9070b01b0031508001b2a03c81e12030842d0f0510341c4404520031080040c0c0300740140f0340000c4040c0c000030b4000c00503003203464580340682c44090569020035066151580001122141140c0041205500c02d850311800c00c1040300e5004004181600200001e10405d070000010700c4982c018a0a41503450b000b01c54401080b501c001908071a111001c01901c203040a040c10003580e160040850b49a140c1c06040203062502d48402c004c1201d12460007121100c0003000003082c201402c3c07016500c1180241d0f105d241e503081281d840c400304c514481d8554043e9050610900c002600b00e51900c181c04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 580598039 1250 580596789 580596811
    0x503120304080f19030e0d020c03031e0c0d03090c1a090103050717010306050105030c03061620101a04020901200a05010911030d0504060c06021b0607080f1b03 70
    0x300440e09065064420040d4400d0341d20584c2d055070201c01d40c50f61001407401c5c5044102c4420055020702a0390390962003850581c9507201700320010340915401c07045105c8040d840219801c0c80208072a107030900d03074807452082c0000e85d9078003080103000c98441c002e80100700040c14288841c8540485140300d200740000d01d818143c858010451103489200307500e80e45a405a20f0004550f102c2c90401d002c7c1c1001c1c8221440703403280541c20059445d01023a000c1c0a014500074405090301210303001da61007607021076800d240c1850b007100b444c0860414807225440f10a81c110008852001d19a00c502d1010200d402c80d0040c0d01c188814036040e40c00c480b003803a410410821040200511420091070014440c2d00104103500342081c1c6070810481d121142843c5601f10309031244813100070400c9030700307000300d01c00c03c2c0018642d01080c2021a0582c0c0c020810b4a1483d803440307001c8038003207103298902030003615448001080e07003003040a107410120340103421003124040d80c9250031118104440c17a00000e45900d1000d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 580599289 1250 580598039 580598047
    0x40308090612150a061412040804120803060102010c03020901050d0b0f030138091602011401082b090501030f0204030b04031e020715080703200a09050312030408 71
    0x41d589003030965000b200d03503000501162a06000e40180021000c462034043c003404280030407040e0180d4107000c0d04100c1c2c41e03402d07400c1c505142680900480c001d041503800c000100310201e07400598190003022240074003c525035138107244000a0031642d200c803900c010944103000c0d0b210030b40e03403020894008403400724000c0342c500c94070b40015100013036407020181d05619107002203820742064000c172819690200206550200c480c0810080070f000c40850700d03446900380000500351540c0d0040000040b003d48000680b40040e4400c0f2101d0550a801140302c42d0312404451841040c1903024403030b003018030a0150b480d00011900a0010001c60052505040d103036440d09051086a0781070b18000e54000c00702d00140c7c10f040c2406441006d11040358141e036071007420000a414000100700084035001003204040000c038080483c1e0480c00503143c60100740c0c070340c242008100c030702c008410342500820410b290350b14480080034104030100e600c114000e4014807013410020881073700391b9034400d80107400c565513 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 580600539 1250 580599289 580599307
    0x5180115020f0d02010b03010b120a080f07120e030c10020304051002010e03040e181906110d05040809040c1407170f030a0204181a120c060f0a09060f05040308 70
    0x100341060011420b144168140c0345030071035054100d86001d00094000b0084100200300784008140c4030903151605034804504040040c0c0410300a0200e00a055406414411709954a10340210201500c200040c5402c007800352901e028003100903c9842221540c0052544070f42c040d440740130b50b00c20544513234180d210341c8803028004e400080900542c00305072035980d912409030040010003920109002c0072200310101c15050002100c15010480c0002504406403941e02d07880030305000806107003515024400001960300e540a0140100e104034040341e21102107009000032154403441b0320301000102c200e02040c000702c4c4d508030740c0c0d0240c0000d03c0f0b00405400000041980c8201c0c078080c1d1020000200b009081c030900c0e4043c1003622011921090000b0700941e103001540c052103251035850071450f0b2a40e05510380003c601c0341c417000c03c2c400e0700e070f04650683c000380e0b01d40c010f0100445502000144c903011180d0045106c4064006420201032034641844000c250340228000104101000529498 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 580601789 1250 580600539 580600543
    0xe01080609061c06021c05071103030a0903050418090203060c160809030a05030f030109060e010311011206050303041d25080c1e070b010806220606030f0b100518011502 74
    0x51000d030002005d55407101d0090440301c0c030320303e800368500040d403404011034041c40c0b00300803030096140700701c00031421500c5404400f001090303076040c1101803100c100800244601c0c41d41004030542c0d0b1040000034045098014141170060082540c0c9090908207c3c01170b1001000112031000c58100306090340f84c40101c000304c2c0c42c210038854045c00c0d83c80042450031945d55440e00850584c3c02004c4140106507442100c8034140c1400c2c0401080020310750203440c0c440d40705103014900e0500d40d15012981a98440100e810360b40a41c00c01100c3c0c1c00040085d45141486000980c1c00003051545203104041003c220401038011144a0040020500c00b007800009460305440c5280b990f103080c0002c40a910001c40225400700b102100d500c2d860b000002030071440483d00300e10480300044e8a9018154242042450b004103810071035600b6951103011001c101c0d49030204078828840d00381010f013030406407060084e5a00c2c2c2e0384094490034580440c56525080300c00c84504603000c7d02501b200e41918060264 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 580603039 1250 580601789 580601839
    0x181006052101030b040c05010906050306100306090f090c050315072006070e091006021e0a060f021b030c0c13091a150307032a0317030402010e0108060906 68
    0x3000310010000f0050181d0140014041c40c402c0e1414001c0c5503540c001510519468031480c00414020b00000790942404580c11072943c0c102e250000c0c240303031243c0900003100d01c041d010038141036890b0030a40410840d143e2a40251000324000c080c0d104d4828030060718148010400c608010069034550040ea96009030102c052418005580540c40d2424005012607900009640710303940030004299540741402049056031026405011180247d0048555065080150075150f1003447c04a0010807030070300c50034046401d0002c01681d62084550310218407580000aa580e541007000102d00c02d00e00000e480640c0d503400d8450782582c9001000240040c140c8007005011084c4d41c0c1e420341d1141010441d41c921403600c825441076010720b0913040c16a41c4d107450100034440307100102c100b0030114071942c8d00560100345078201d40b0000d03165954101307031031804035810075288000b1041c00210b6811800a10144500b031804480310324004000580c400005060706000d00d411615004840c80c00044232 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 580604289 1250 580603039 580603087
    0x30b060103110c030c0d030b040221070c0c090c030b010503100501141213050708010903020a260d0b09010504050f0a09080c010213050918070905060109051002060618100605 76
    0x44c986030340d541240a601e4a8850000ca8006403425083d01c1d803620301071090352483c43c40700d04010b050840c07085414101820183c20b43d0180035400e41001c0019000a00035806031049850100c0c410001e201c001d005e071401402c00c2c45c1807103402e00c10403111a0014460703504954003481c00017400b00b103100350003035644500e040c005100684134042180d18003000c0031b64801248154203d03801141e85407885822034032030000c0100140c00201e0701c1c00101310b044210b0315107000110312031186a6803e55040036540e00491104282e66150050b115840c81d11520103030040000f51028855480c005d100601303010780c01821000040d54a02c14001408022001e44070010880c00085568064805a039944040c040c4a082d210f2802800081d10301c10f0303548403c00c00c00c184080105a5641840072000141c0401007d150410000002c00a0a56212400d16240c451b13290090300090825205009001d40a2542e09064059803000d001c108031302c4103030810864040e49007a90302e0364403515030100c0242050b209 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 580605539 1250 580604289 580604293
    0x303061203030b1921020a05030105090708060a0605010507030f030b0a090906051803071401090f080a0e0901081b03100603060c0906021504060c12050a020c0106050406030b060103110c 81
    0x403400805405900484800508603080c0f601491001c0c00c00c04440040d01a8034801089502c400d01140b00002c0c6206a540c0b0080c1558902511b4801080c2103070000c50300340d04686c1c003003202001002002d02c529a0028155101441003e00307040001c3e00502c6030300e400508220105864080c000e11030303800810412801000160140e07565000240035100489003580c01614040118400c2e15001140c215422101000f0318202a45902ca20340000c54080c03a048041d5250200c42000540c600b800b03d02c424456400180c46140005c4002e00000100140070b0085840c507006012041d0006024018010900c08003c220f0b2804004a814001d90070042c2440c5070500301c0101c104a031640003244d040d4080d03500c040081e59030324000c980e145a102c000e4288000c00b0030215000c0b600c0c80d000880700420a01340310b90380c0380a503072151080322030031036103009415404154042843c10a01034480208406c17103080c0310040c00d54840d89480880a00224182740c2d98005400708806400c056038224295201 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 580606789 1250 580605539 580605569
    0x9050106080c131b0c050a0507061d0102060403020c04050a0b06070c080c01180920120115020d050d05090f0312070311120a0f02090418110a08060f04030306 69
    0x1c0385a954620080c003640c454880c0b650380d11020074883c4030f240c0e03800c018a180842d006a4000007a94201841c1c2e40540c0e450090002c1c140c00b094080000d40d0003820150740360844a44250000e42c11007010360591411904403c0a00010a90006135a001c0400440780000c1c2c50726520409001800190492600308a000c5804401d1017a402402d134200c5100c8401c1d508401c2800e0b00444100d4101c42180050b03800b0b80d50306001c98421075100c07054a4048440c541e110301000c0b10050b4154010501380303028511200c005014001e184445400150001e000400324600c56007805806800b50010714030301c00e503a400c00114198010404094945009000d480c0c1ea02c10410954500c40000c4841c800840e084c02c80c2c441c0c01d4510760003100c00c200044404440b158440e4000c0402074901c0c1910744100075001e00054030b030759442c0d01c244d41d120b07040c998855200b40307070600e42800360b4090140c1152203050311345410060502c005c12890b80c000220343e15a041c5d80c3e110314040d0700410a83c1c0201002d41ea40790307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 580608039 1250 580606789 580606799
    0x40c090b331e03011d130f0c0b07080c0d0f020a0809180106020d2a0615050a0b090102010e0f03090907090b2a0a020a06030f020f030a051b09010e0603070309050106 72
    0x1507050315a400b0074401301d07401c05c13040d4038a07210080e20340c18414810a85e5102c08105102800c00945100f0030b4452592581c45030380d10601e400c181c00903a0b0f0385800041401c0490001c0017144245866404e000b420800704810103925091200310203410000e0000e074940e0b003555a6110701c54000a07841c404e603510b507101e181c020b40c0d42441420b08800700d281c2d5183e084605005d00c9801030348084103240d11400c003a2a58511000d080d480006640c6030840303c0d0081b42030b0742c40005850103880c0800b5404e44540c0540002800d580716601c03407034003640015400714003500d070110480380641015655117002d502c0d6078500301c80d051080d81c01503a070408013066406070350309010000017018011a052900134000c1004180e150303450307000029440000362908101880c000d4000c16280142000c2c0103040c062580320269140d401144c060a100341e4500c10080e00356011000d28884480358103485080410150001c1c0c0940a40002580b10750300100010b40341b18413a0f0000415258464001d003c115699 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 580609289 1250 580608039 580608097
    0xc1e06021c02270d200918010b0603010506160203070e0403120b030303100603050a02070c08070302100809060c09150d0e07060f09050f0402040e040c090b33 69
    0x1c105500040243e01410002541c401c007210000c40d038020507000743c00c40c40365290400d40b0904070403040c865000a29070140c1c0d90310460200c0c415013941512005402c1e40e18101400c40d20b250b40c4140c820034003400140300070703101d0710141d8140302d01032040201c0302021800041d1601c9402d0380012485100741041004155021002440301c81c1c031014144600028034080648a000881c0c044100c0c1c80c800d0702c1005258400d0304402d40194a800005140010545a5a080c0c4850360080c0450790b100380d4041086061500d0301d1002842c1c1440d081440342170409140b0344400001e0030340c0b448401c000c02c0c804015942d40c070000000d191110240c940d6189080d2481d00601082391204a613406820000a5564001c18024442050300d0b07031820101030a0204100c1c51444c0e0b840e000d138000303900344000300b910000003c00da4000d9010b1800003030011720700750103031003560826a41c042c0101d0041c200906840350018241581c0144e04030011806108460001c6c102e0007580c0b98600c200c848020171000703038140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 580610539 1250 580609289 580609297
    0x20a08060703021905040602060601180f06051c0b06070b0403141911010b0105040515210a06060e09010e04150203070504030605060307050904140a0b0a02090f010c1e06021c02 77
    0x5000084c0380e5038602100c09070707480d01842c861b0344096040f0400090540d0b1080b40e0b00e81100fa6a0303803030600303459100c4c07235211076040490b003285001c139000055410720031910020f91004031040c000140141400c2d8004108a8000d443c0002c003150b5085012500b014040d198000032400094921a181d8119031032102450540c0051040420070f642c0e45800c0710b00042c080d145418406850700340c5082d14200504c0702d16038106407105607240050086808103201e005034454240e84190b090007103401c12981c00400c9400960200040c0010030f88643e1039619800c3c0d0460448415554403e501c1e40d0340c2c2081c031500c500507045421003d2000040105807a0004041c4c820381c0d01900c01007049646a105055880d02e02d8000e176a880240c803800100004c0113840d003000c401030808160303480d68515598241c640401903603001400ca07000b044012990901b9070420038004000d1804400c10201500d4600755411044c4a0344440301880440b40180410b0350102c0f404500340c0300d881014100401e000c0402500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 580611789 1250 580610539 580610557
    0x7050a03360317151507150b010302090330030f15060d0e060103030807021606110106051306050f0a08100f06080f06040311070e0a09020a0806070302 66
    0x1c607000741c8900542100359150340c6030100300381c1104460810303080c07101040d503098822410071250740360300103040d6410341c5854001c40c002c0d1102a03100b0890703801c01606181295454000303480c24001c200104205060300d000c1200c0c2c0000000d010440000124080d10508e5100e43d01403181c5113142c0303030584090f8102d00c1089410110900201c11000086190b4803041d10340c1a413150718100132904898004503a01c03440c0030001c100500e003c0500304c008055429103031441c56140c200ba001081413503000841d155000400d440582203426000b00d4004503400c0f580140300810402680c4111103207000d51040015260062040f0768000c2d200c8540d401070312042c0140d600516980543e090349090140f06e0109030351b40b0074040c148540004e0b03106002003a048214401c00ea460302d00002e55100207011031600446010b01810032032030141409013404e180428051116132111000300448038840d00d0a50300040030305000301e0902598000188840160340141090b40210002d0040c0c0503010750061204d85 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 580613039 1250 580611789 580611791
    0x2090412030e0102070c1406070c0e0a050f04032c03010905010510062a030c0209041203050f01062001110301080604031704080d0213260f0105041707081207050a03 72
    0x74484402c880c280c1c051340030020002c4d01c4903003003031004542d1410309286800c1302a00ba2401d003c99512100400446a407101c2c0a54140100740045040180074042d4802c003400010401c506203903500a01d40300e10405054111640801c0c0d6082440f106109d03400901001402401040076a0501a0003407606540300a0aa03e400d00006141402441d1501d000e070b40a00041c40e011401c03034084074505e643c05400f00c0c10000e040f015030005aa4640b8158020750045210194403510400301034221103020301030107564003000004100341584610740c3c100400e000c4c0440d25691807038107442409001a00001203400a01100210701003400044aa102d98042e59545980040c0200060a0400f00707650280c8100d008110020f041c940710740090440e8000c040d44030302c40b03658402255110440c411101302503640075401d2080c036428104400030000c02044001c0206c3e007413a5840581244034080782094020000c100c2c2000d02c000c030343c1580e04800c0280d200c141c1c1403800d81c0d4005d2903584548052008a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 580614289 1250 580613039 580613051
    0x191701061d0106050304200a06080402130b0a092003011d0f0c0f070f060f020d0e0601140418060c0504090c1e1803081810020f0307110406030209041203 67
    0x41c062010494102c0714641c03100c0d8a07584032500c60100044070880400080000e4501c460704a403214442d41004000d640d071703008228102441041903104083c0c2c00190000d0810600484540d28035a0070021588c1e02d400020700407003070070a0803400b02410107000844803c040f00000318504001c04200b07040309441302d28003440d0745104039031544074820748043c5030100040c0051100039400300300610a1b90701440d0550703880142641e9140a541c1c0d60740006a42d15008100880c050b4840d00401e40080c0b81c00d005000b4540c1014a460700c88940800304910450311507040582c400b4006103108085a0803c0302402130710304010016150f50b102d0320800d52402d00d010b2010f100c5c24864454510800d492008840f201071001204952a20301507000050000c400b00b000400503140707000411002d41018444032030f030240e41c1e0811295080d583c2e800e00654100030380d180c4ca904c1c0080201c0391846d90001807010000b42500c080740041102c1c0d00020342184000d4240000c2c0894141104400c1106039030070300ca0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 580615539 1250 580614289 580614329
    0x90301060503030a0905040903050409050420032103071404030c08120a080f0601021e0c12010e0706180314030903060a11040b0705010b060412030807050a09030219170106 75
    0x80d074404d0300d149500042e4001010b1005183c2a00400c1d0207074002d20f001c80c02c264440a00d10211030741524122044642c001c540580741108020b0008a01300403400703410500c04540091800c041c80d09440c50808100000144540740140b0003a8400103188200315103464503454030b03035800d00040c02100b0706803041d0301ca2180c4140b07501040340c4441146994800f4241c0b210755080c008000301508540c154028a410700c0c0c078294038041c401400110420003410b5440b003000601ca08440f6900580095904105080e0700b10b01000414400729240c9250106416907181c411041822081d0802800c00c034082d4607040000b0b078000098200c0c01d00441c00d40e10345840d6804064103d070360303401c030b00001c8002c00d00042061a09010140200b40c1c01540042402304070507000480c84d0b0b01070342201d81d00d890220002000d1651000c0926030051041c1085881c240070000701500320081444000c1c0f1504524030409441c080040703c000041030402020703c40107420807141c5002e00700c01d0203041240156070b80003583c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 580616789 1250 580615539 580615543
    0xb0304260a0e0f040f090c05060f030c0d0e010513031d01080114010c140a03090b090d08070201020a0507242c120d03231608070e15090301060503 64
    0x1030321200503000c00e464140200015903a000b6003085980d07100300c0d0391a082c40251104d02a45400130f880ca60300141c42005460400b00098160308070038000d000521464030303005411b10490303400080000380c140c0c5488410a0060160283c0e05c0b801c0255401c06d0144000c018414200f0181c982c40307901d805010390b04103138554243e003012001c1e840c0018078907c010050b00902101c1c425007102c0614020b0380c440340340d03280e1001651801e411b80d020369010b000080c3c2450340c02010745d00644103e100c0186003c21030000142a04a2400040c10000000035040216070080062126041d803220a68800c180d44000100e41d25071044508a01e6a2a11007001c81980c070a200c0620300744d0360240881d400c1c05540c003030381d0561403030400065040780c0c09084003052844100014241100669008a071307442200104000d100c0e003100d1018a180032460a0090321102c1c001800b0050a642c50401d0b9030340e4480c101110425402950aa080324000f184003904502030741c0145030041c402d0b402404800d0ba901d080c15 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 580618039 1250 580616789 580616843
    0x1290414040c020d021c0c051b120601030f1b08011d0d0311031302040b120309030d0c081b0c0a03230303061503060406091e0b0108270a0c0b0304 64
    0x8401600300c41152102e42d00c21b50110710a200b601e00d0100045d420a50301d80340f8284030144400846520311107605060300c3d1001212035240c40c0d0300050b04255145984901c2040aa032900030007091044460010003d0406213400c0144401002880401107034403ca032100500c041c2c62240b43d008280900e02c08900030b000b050b07200c513030703100c7c01d145142c0d159070b03400e10316980c1d80e0b004070390240d11485e42c0f45182d41d810034848407040c81040510740d51280c11080510b4a849040d00390103000b8051a4032011442010031788004011f4407034070003a44003044070307000d040c141d81007a169404011140c0c0441171002411103841a50032544010180034142951203583c0e001c11661140c0c001d10f013081d210741c1c5001d12005140c100ca0702500108206031640014010b5070340c6100c040c50003c020f041c4441e485042c0f40102c0340e07205401e092642c3c003403c201a2945500682c0034208943c0d42840384842201c0100b0880e06000a8112078450301d001c0e110300c00c00c445980251810784121001454040003010560201 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 580619289 1250 580618039 580618063
    0xa0504020f0d0f0603020402070c0603151a030601020124050108010815190b031b041404030e04020703021903020601030327060c0f231902060301290414040c02 70
    0x2070030042e600b21110040c02d22a6403801e6099210000000182c85030300140c44203500c0f840c04001c0250408400408444540040091140215408110b0020300c00017006c926484080c60f583d8035902c40005038050b084202c00601e142c200d2440e0141c180046020200561740f003669071035410f0741d8503aa51350b85c6074a09403003a55a010b00d28042801c3d108410088000860000c0020030415140f000190030844811101d4a10300400c0c03000203120300c2c0610418000c6200407042c0302c07007410680c400a00b075444513135802d409190f0000c2e60b44c0c140b500800507420380c074404100720a100340403442c0007905c0b95000e100c102c0101e440c2065401c5614550500704803e0300e2130a0001103a10701d81203048500e0031700308905441c52100407410202052040d103c11150403014006800044c8840c0c40b85c9181000155140000e0681000300800507500d40d0304507811142c403030401469007075644c40040719005070100001d01da00d200140002d0858041140d007000d04404480401c03151440c848140d844152451303070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 580620539 1250 580619289 580619317
    0x1020c030d08040312020c0705130507020a0b060307030b131a0108101136031623030303040308060f090c1905040b0d0209190515090105120a0b0a050402 67
    0x80041c00790702c12015181d1040c040d00c1c244940210901c81764040340d210a200041c00e410040d01440b45044c0b0319042e072940e600643d420000d500c0c201d02c4c001c2d00e4002c44540140780c84100d0004c01c003d039808100c4c4001541e04154000d9450410307900c4590507201c0301c201100d8056440c01ea5079820007401104034100c483c10f0014200c500c050803403520090607140002e070300606080c810030135100c0e007550701a01c1c0301e85901ca58600083d400d00c03c0528500281e021103109503c0180c8008451405080d140101c1d02d80c030300c501000c05c0030a2114090409003511054161201104000916500a01e010301810094801d00c960404d450b042c402c0d910300896581c1c1045c40104001c002e0b5500f801c0c2c40c918408018a0020b04164584210340390950200c410441c005401161440d90340c900b41c14000205903400d101c94140c2d5107000007160300c40205410208020b200072820308034503402407040300c0d20b90003010861649403900c0280a0020007030065402c0c000c038402c55010409040c10300c01c884900c080040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 580621789 1250 580620539 580620553
    0x40e0a140a02030901020d050c0a082202010e03070914041401050c090d060626070f0609030305030a0204050603271b0d05150106020102190f09150c02030d02030a0e01020c03 76
    0xd601c0d0040e50016182c1e0784599030030000b0507148592880b45600031511185031507607a01a101c1e0041404d04040c101c072602801c840390a5018107554000418120703030a080800c580404c0400103418100c0035400089580d003403449039400b03103804440251095200c1d01400d03e05196218006088032070807210840d0104040003400c0c4185055984020024450070000c642c090f02c9081e880e6070f0b1307440348500042100c1c1c0c14202c00802601440078034040c002c82403080c419a441e12800070f00c004440d10004c3e05101d00000032a51082040c0c040300d001c1c10b40506900d940e42820544200803000642c2c94441c0303100c0540c2c0c6100210f90108969982c0d120304a040001500f04000300245d8074946c4800304d8141c800c6460b039044480c00c1c3e50844c2c3c02002260001611082c007103114003840700c00c00315407004000030000103440e4260460914001e0b5a551450400c100d540d0b0001603866041c102c401961612880800c10500341c2d000008002d002c02d0f0342d9400c1d04e880c81440069039070f41140d03505983c0c1078000384 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 580623039 1250 580621789 580621801
    0x2060601051209161404061208040e09032506060e04151a1203030f10060c060f0209040905101a090609090a0f060605010906110303071815020102040e0a14 68
    0x3985180c00078500070648100d0180c6a11503084c3c84032139400f0030700d0188071101c8464145058401d010003400341c820400c01c843c1407652001441d1196010300500c282c018804100c0c0603000708244e03148444806500c2c0c0303408a000c06001851400c0e01000c5502a04148001c100e0950341203896018640c004034214006031540d51203c0a440c0e0081d03901c030401400060303902c4541c3e8220b5061603055610f000703140ea0382011202143c0c1500300418541006c401e0120400100d6480103d641410790408800103000751080d04580c06445a416130711352060400707150313205000380410540c019500c111002c01218412604208400d05060903080c0d0000c80000003072000d007044191030ba4400d40840175510162100c3e41c948402d02d80200059940c151350744024000c43d608890400d02900340c40c104440d0301c801507000c4650f00c0c80f000f002c9104024480580c410b26800c03144045005d0506071505100080144000034000d40161042e149141c0c4100c02040c2e20303481c688505e598500c0002e04a00e0349581d45 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 580624289 1250 580623039 580623067
    0xf05030c040c03180b091b01141303080406050a0206060a080c1e0612040c0501030908040909050c060409020a230306010c1a0a0509011d0714150a020f0d0206060105 72
    0x82e030200020b00d0f40715108051541182c2c00c2c41c00036648907a200840c2800c2c8203070800e00e0020740b10700039560030070042d1902d801d81ea004403400b45c03031070f000409059443c48406861071060f81c031940001c10f0b81c0004603021a07038a8100d00a0090b250140d402c0f5400e80c0c1d1464100030a0a03050f1140701001c0e006000c4041580c140b0b502401940c0e1115500b0030f6600c840e07640451380550202101d440310060200900c4200300d40c1c00f02110007420240b170144801103254840740b00d0340c0300314410290802c0c0e5071000441000b800b0300c5628080d00009000688941c3d4505800019500011234903000410391030340b10f100b20901021800d0406c0803a0942400e641d900300041d50f500349c880500369000b9400001d100030706a40d0f1a402c0303210350800c0c0030104041c101855064250b52304014030924118202031456121040090900c048034800300d1320030458400c407004600807045001000010300400907034800c00780d4001441182d00c0020000712900c0c0c1c00d10b03c1d81241c070384c1c0060f41c11a000603410043c2404103400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 580625539 1250 580624289 580624301
    0x604020705070509010305070302011205010303080f041a0a1d0304030804060f050d06060c030e0d0209041106090307080f06060603040b1f090e0d20060408032511070f05030c04 77
    0x104204407410b19071144001402403409a10485080d40045001d00465900c0b40390402c40c00c400000c1882103505566001d01703040c000a0420b03940c03070b40c044006010b221002e40c18802c03100500b5403240c4c81c1c0c1010a0403401514518210b000e0303d5480c0e41074011001000812076045039006919142883e06004044a550858041d60420440706100d000c546002c035110b004014a056151290041e9840c54090640c0e510020068410954212078002584815042e01e600603030003402203910512120025200d03004205030550144205000420346003400114482c001507060201e0b42c107651100108180d9200c2140c000b030030081400e0100e50300440075841e201103400424411880e16844a078080110343c0301c4418102039500c03001001b10116001011480d0b640b0100c41e00414501000000b20b6440c20044c0c401040020000001000107a10026094283d0000c07400c4020300e070710b4050b000b0a070f04100b18114400c0e00a020f80001d9000d641032000f41210400380161280c0d41d040c0c0100001010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 580626789 1250 580625539 580625543
    0x1a09130501060e0c0c0601090225022701050f100906211b140a050412020402160503030f07050405010e010c060e03030a09142e0e0102040603091202010c0806040207 72
    0xb48401010a01185840e030f034a12900701c855105440d00052410b80b8509907040c0e001c2c3e06594410881c43c1415488010400d2071780400880c1e80c00201c42501c04940010003403034501c48050403980080c40c1e0300540803002d0341290b104850414101c02040304020000c3e101ca426a40800d010100070082c481c000c2c4c0d0049102c0220460041000004a503c0c0040d6039040003822100c04134020780408582c1c0100b1403806000410701a182480c400d00000b43c601d1083e401020b0550030018682803c641c0c1b070b41c048a15841105000d150300061b1854190303540e810a44040c050a403100000404151244e400c0d0740850744141c1d06c203401100408019541d10508800c1039810544400c003005120100700000c5001c1e41c01140300040d02c1000382814150a1046d40042d0000e4002c0303811040c03543c1b4005115401c159020400c6900f082c42150b074031005011110b01e500040d4000304000980c05d415510225002d4001d040442d51031920b100206d00b02c940c00412400881c0801000c03411904044d806016518 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 580628039 1250 580626789 580626791
    0x102090604050d0c0302030a03030f0e0607090b0f070f080910030b090c03091005071107091103060103020c03120406090201080c0a440109151202010c0f1b03061a09130501 75
    0x3901c5c1e4000ca82013103000c090a0300880c0d118849040100039030700c107145403912040701a045030308150701c008040c0809441146d0807828042990340380d040700017080342c80d0141d02506030b0400404d10301d08000f50b0b81040041c58420030142d400c561070a80280200e8204071002402c0b200c0b99505c0300c0b0352030030503003000d402c1507070600c030b03201320743d0300340d1549105a6016036260303201e0041d2540c403031213898580303030498111040305410001c100320300d810207005494101009090168035043c41b031604610354014011a040003103d11814003050001c8c07a80144803d85c002e0fa124200e07030f550511091101e11a252103440080c0c28007840142c840755880e500c0c4e000c8880d11018016607000041440c030009444003440380081c4011004211090030b40c4210307000642c25100001881d0315200011204030349050340681400b000c0304112040004560481041603070010443c036241a4a03482d240d0036011a000494805140101000c1d0980302082064107004000701501c045642d84e81d8610017000e171131803044500d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 580629289 1250 580628039 580628063
    0x10e0901051003031b0c170604060b04091104180f030905100c020303030f1f180b120d080604060906060f090503061302040902040902030a03021b0a05010e010f090e010f080f0102090604050d 83
    0x40707c10101d074031001603000010141400e090400104036902500c84501c03c6142ca24010b000a4120b1035000304880d0864000600c080c2d403a28480d0148810340b40140309184500405c0708168005092034180c0b10b0641d010320300c9102d03d030415282c41c0c08944002c2d500d03130700c1800060303c45122260001d90040661030014007000d0360124000c0120030302d40107001d2042460903840210034152184103110b01c411510750340d00c511401009a103036a10302e20482c0030030070200e000880548447c7c0110b0300070200800d017088065034451000b44440c8a80a5100000300c031080c0010f00c43c0340000c2c006010354070000d6080e202d8580c41d42080020128104103d8020703803140740d400d015179000c0c01b0741c512060080c4c02900c8100442c010032800c81658613842ca1182a0f110700c24402d40c0d074840d08924072064282004813642130003040039104540756034495000202e000300003040c81191a034948080f100e00030704035140301d05502845400c2c0d00502c000c994108200307020400ca0b80c5040102a40c00e540034480c58104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 580630539 1250 580629289 580629299
    0x605100518032d2104170a0b0109062603031311090a0c090b0c0a060903020c103f020912060c03040b010806090d080618010e0901051003031b0c 63
    0x2d0110000d1000030710526601c04810f00c110309021402812503502c286020800102c8600410382c01140541d24030240307103032031903046000d0400201c1d80b05a080b00e4405160345c0e40e80d480c10054207e5000e008041c0060040880f20302c51076441a201d03804580c3c0c080c50455882c1c030100484181d10407410b44170160350681d80340850315054100c174051000d0280205103501c0d02c440180400a0382d5020450741c072402c005255041001050b8511801e50054000c1012100e0b402c04a2800002c06501540041404025040316400862841c207004040c0e26082800d003d00b88800b144154030300311400e450741849280307840540360303a0041008420040c45d2024141c88896031a04d000c1044500034684030002040c0024000070511150040050741c0003049c5e03074035102c0c0c4c140b81c44a0b0260510400d1150f6070740841c1d59903503110b2200c1c00184000782d103000991780d150031501030001c0036500800f855281c1000328410001c03200040040d250940c80390920181d41c0c2e450f204410311041010303106880c520b03501090f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 580631789 1250 580630539 580630573
    0x1091a070804090f051e0705070c050616060516020a2a0801020c070b03041a0c0d111201121707080f04091b02011a040905010615020303040501060510051803 69
    0x5001c0040c800038a01500d00d01e440110317075003c0c0041010580c076026111301e0b4907000801c50b61024807032030100c0c1c599140b2310340041018410781069900610114401d04400030712520a101103010322418401520b800c0341c401d1500003a40b5101005030000301804011400c206200d200781c03031121240c0c00101da442c1d04950603281043e00202d01c16500050312050f0102c1c1004240082c0c00c546042c40c0c6141003a5480301001082074994212b10206036000030402c0d003100303054a13007940401030188a00c00d030400f4102d03090b51110300c4154801114400118900c1010042503022075408110401185201d28220f01145c05c101401c0b00c080c1010084512041d4010020b00000c20b500c02001c2415130015010440103184e0303180301400c5a02d403040d1081c80012800900d00114002e5a0000d00a0550304225015040e942c1117085000c95010452400560000c015071049025200070001503849034100b00c246060b6040840000310107110300c292400c00841d0000d192a0001d0403140c09100d200741003c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 580633039 1250 580631789 580631797
    0x9070605160303020325091d0c0301050f0109051f090803070f0f0507090c0c0210021606031a0405040c081002070b040b06010c0506090303090706030b130b0307090218040b090601091a0708 82
    0x1e1041608101d0100c01c10100c01241d00c82303846110f050301d080440611070740414401c0d41d205000c10003110343c01d030b402490810b011b80005420304401142c00c040e02881c0c2d40d4075440e00c1002a2180c000002d101c0800300a98010650003402019002451f4031100e00741d8869110a40f850701401e0303400501c2c2d0f500c2e03128013a40000d15855450b40c441c00c6004011003090b04c0f144100954208162074514001d103e4082d005660981c100068030000800300c0c0003202040e80c501907003080c9450203010510404014400403100c480d0129600c0360000c01c0c1d1340c42603001d0020010092415000840c000440711040c0c0c07a8081070615210b554040540c58040c40c1020035240301d10242c0000003800320030501071200304064512814144164565100450713041b404454490183d5542c80b0325a03015941d06001c0e110080048110039501d80c95081c11a0401c0508980824815460003076810680e08000c1d00d020b10502c1b050b1030705500241362081e000000c82c811504404503038010841c440021302c00c00042c2c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 580634289 1250 580633039 580633111
    0x18030503031308190f110c010f140d050f011703130b180d0311160b040b0a050c0d0e030c010c08090f1c060603060513200103061a03090706051603030203 67
    0x6a0740b21580d55034098121035104100c03107040c1d0000d61f0b00032496600319015066000d4940707070621402851560040042c0901c0e070f64520041e0914091080e8100c0d0a03c43e58141c0d22210902040074908210880c1c1d030384544003440071120640c01d0200110700d10035020b0300303203200544003082c043c4400c070f000282c00c0d00c04083c08902140c03201c012034020520401c215120300101c4011440f440b402d01511110600071441140b0f110071000401c08200e41c40741c41518030000c042c1c030449101c00305444d40900781180402c50740b0300038801c000f01440158840c028007410580c00c003142500d48400707038060060342c20502400e207400040c070346006202c1b0800c0a1203251518011500058081d0031450b01e00291100503007100060340d0150700c01804104031201160750070540304d800a441c0309480c8016406060b8a5114010441e01d00b450505550126001144a5901c09007591402c6480ba00161406c1c003d00100d60041c3e055240160300103400f0742d0007580c02c0002e00d005003031012081c1550503201907908001d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 580635539 1250 580634289 580634297
    0xf17070e072c0604090e011808030108010c030c0804120e090a0f0516080c071a010b04080c03011506030c030b1c050706051603081305100605011803050303130819 71
    0x20280c03841194111002c2041c4000c08440442c0d62880000380c1d060189004911074241e0b611800307079004a09620009001d0020000b0100310040c5040588581e0000d2058500e10b50800e0310301c103441ba00c17a12515020031001d803210411615291140070b07841c00458003400605c407007403104c15101e03035504048078460b07410100041404116545103c0036643d020b4001500700c0300c0500400030480d003242000750f00c000c00e2980991181d8003400c0180c200d9110f10882001e0411150000c00c0a1444600620507195020221b40103082e210050500700c4001c0c0c01c498041001d41c05081c004140f2940015210803090725000c6900000e000003d414903480c03095010203a18074281a000f005000e1200000404c074604056040491440400b031030788081020060070031041f540003a1f0610400d6540014442e00201204c0c040c00215007003a000b003446000305804554038060300e000b40114511280180ea80c0480610b04581f21f00c24400b003407101f894070072180184103206c4031144188200c0c41d40c4c5040381035a5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 580636789 1250 580635539 580635557
    0x3010e070825030203100b03030708122409040201110f0f0102130501080708042d030206150a0303021b0d1703060a0605160b1f030c03020901060206010f17070e07 71
    0x182800030b024000410058203441c0080070400750360301142c081014800084e0204081c801000044e00318410300000800624002c00c0e41c01000c1d0152940610642448009450b561402c210300f0720320320801414650300000181c0024019486170010308815000542150600c5190601c03a50071710302d001040d40f40b140e40c003289141000040c012000e00411080c00c00006038141140c0081000c00000c10140c51182112400881032070884020400c0301801c02c00c0442c00c542d14980291074410a8418051540304008516014907014000301c0440754140c000b0281000d554011507640d800102e20182d10011b800d45003404241d90358201d03034002c800b04403819524a8107204111084090360400c0701009400d0060981e0404007603108407245801050507150340d40c03075003180320608088481001480707203084000410400340e5a00b00713003500e1080b900c00380da9a0700e80a049941e600f092240003801c141d4030030208001401041020201d0490800f03540743c00b62118019181c0c40c0054810b0000a44030b40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 580638039 1250 580636789 580636813
    0x10020c18041203050105060403080a02031c0f06050f030a0f0c1d1f1d060a05120706020709020a0206070f021203011d060d0302030901030c03090f030903051009170903010e0708 77
    0x502c0d158261050341410005075041c0004a90319005038000141052400542800341600810a40f803044200300b0400d8030681c52a01400d01500c412100014010300381170000ca01c0d403a0104814141040150040c0b5080791b00d900c511002d81a1040c041e1500781c101c26022607070b030881c508941114010b0070b541c51050700300340c0d6000c02990300b070205c0440c070340e0005c0406022680d560380c0b070201c0144010494420ba515010001071040c42c01e40d03c42a409445001d01c03440305030020400f030041b9980c1e6000c1c0d902680d900c0920b80180d119080014005821540020340c007207010b2130300e08042d45400d1040b600c005040b030800e2a059482038000409640003107144483c20521100040d60004080c0d0300c40d049001e207503030081d6036402100522410f050b180d961001c0349a03c60742c80185810307002090200410480d003406801c07007000c2d010549050003001d141c094801e21a00581000d603501088001007a11281d09540310340d0440d01c0080e606540300c032126100301c0d0b01040308401801e1001c0140600113224 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 580639289 1250 580638039 580638053
    0x2030403110f0c0a060804110d14010c05040b07080724020d0515032a03011b02060f0f01030b0601170a0c1b081213080a17010e01120210020c1804 64
    0x402d0300a01940e216104660b0303952510351809088541c00e080c40000c1d6141da00e03000c103002d40304c103600c69002810044620240001d92a588150040d414003c114407103030000c2c111540d1042d40100b4001030400c000c04c20018142000800a07207000710360280500030402510541c5040140c80d48140c541c000c541e01d160b91500d8400c80307400c504401e40040c0700e032013101e01094403164444495140d148008144400303150340c41401d4840c0d00d80050007084003807004a0301c042601c0c07030681484010f1107100e0000c3c008000d0020714a010710b40d06a40f000d260381c40c50741c0e22141b50000501450400c0f055080032103d07807004000c1a405007182c3c1c0e10202d00a0340180004001c40d101001c402c400003060000300700803a1184084800e00d07049001ca040703003982c840c2c0700010441c2e040701c0010701406000138141012070384005022800b0460380c86003502170760390f00010030329502c003800f0382503c101c0b20520840041c90b103031441c0c5840c0000750040d101c2c0d140c140400500b80076680503820f0901040c0c102008100a00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 580640539 1250 580639289 580639303
    0xb090408090a24030902121911091b030c130b030a050604020a270b071202070801020a080105060901120507210203070c170403081602130e210d0203040311 68
    0x19a03180071243c20040c80c00f007103c543c4004a5a07081c541d4501e0704006541f184201d41c0032007610f25040f919000c0035000c4c80c0410030160301c0191501c2017094907002c8180707170411012b4081d01180031302044030704050030100c2c69548090b005040c40c001c1040040340f800d01e18170040340108800e13024107407285002c0d100782056030801001148654410000c444015130040303440c040c169000c066416a10302d0982c000114903156800080c0c1380c95010610300300704401000b40300c8580142c0d0707003a80d0100d555045228280e00070045c2c26004246142e00501190401c20043e01c07110318140b40c83c03221040036a560400315003080d90f00c200028581041d401c580050a580f1901c00708010904625514000300020b000441421000300305141fa00802c005130310040e01910040e41d00b0007046580c2e070241150b01c0c0401c03080c0c42d40880c0600060000301034070381200c0c42000e03501103080c8064002000c04a86101400e5040381c4a4042c400c0103002e0300c15050b20030710145100310321946602c007610910341411407800750 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 580641789 1250 580640539 580640549
    0x91011160816051f140c37110409020a08072d0e131e0210020303090705092701141602070308070204140f0103121103090d0201030b090408090a 63
    0x150880b01040345403039a00c0001400464600000200300c22200c00b154a130f20301d040034080c40362000c244603da000303001c14030b110f01000c0c5480c81d01203500d01500d81c03158000c0c00003001225460401e50000451458034400d00400001000044c148a981d070001b580f03550250006203031a444a5014006003000759800e03210449070140019003074802c00c520398020191401968a40e082d4180030a40013648615900441c642c401d902e410b07421088d680c611f80c2e040702c80c203090b4801d03d00382d07003038002c1c01e80088100c07030103102fa00010381900c5042c8014080030010280079280e1941703c0d507546019a406095a1001c5014040008204031444043e0503a1441d0083c00740314000c84011541d80c90650009031030000c030ba0313001c0366072a25407219000140c002c0040c0484202c442c02c41f10100b04095068483c40d82c142d0344204040c421400320704000b01e41c80060956801e0980e4010043d5a10920f070a0f014003440c1c900c149401b09416400784040741082000303503801c0322003150100d6210003130700d0844d0301040606 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 580643039 1250 580641789 580641823
    0x20d0504080a29010308090a051e09090f15090106050f0604030b0606070b0a0509060c03091203090a0503040b071401020f0702040b120304060c020117010b0910111608 73
    0x9080a2540361114040755004200914002901c030741c89240c2c1d03809064203881d0f06622401907a41c0d0818059991000540e10b10424141c140800c803407403d40c3c4c092251540010001c10000003203070620503803200152022445208007999000d00d0f81c410090134840504200c1d406a00342040442282500d2a80d00083c0c0701d03020440c0c94401c0340c0c80c3c05098070700304c90304500700300207a8640b400803c80e58882d100d0058011800282040704449071030308507074001c1c84030104070754040d42c0707001401019010984400050360030211500d0702030030250b4003554001d2200e100b51007103408203540d5286550301540c05003920420229904e018032116642c031860f001da04100039491300d841d040701e00200748a540300003031003903a480307031010040d0319040c00c00205161128116941c40361982409400c0d80100340c8100c0c00603061500c0c803140c841000007050b040300e600140380d07410010349400300202e01c604407a81104004a10300481c656250402c83e456000c00c811429141040c02c080c101402c213a18403010130002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 580644289 1250 580643039 580643047
    0xe1801030b180f0f01051630021305090a09110f011b21080f3106020405040e03040f03170c01090b0105280504021c06030c0801050912250210080106020d05 68
    0x10b42d0040b82207230490591b03d00345a85510f00c004401014040a0048e13602244041940062584100c0c0d082c0b06640040b1490900c6540315555030043e14183ca03401020300e101111001c0b41402d08036000300b290001410181d502d80400900140d00e00c180c1c20b015105200b99441001e099130f0000a11000290341d8600a605417501d014180b91404014040700030101c110300200400035541d0804190780d03408100c001c84e4030f80b2503003070041c0a900305000e00c4c0c1c0300c0c074034041e815010800c2c0001100d086030300c002800c400c49407844d11019070004035800c000c20302000030005024106801e00c40c45d03501c64415240c17490709505140900004421003001038400143c41089a19500c2c0c08105c208112181244c0150b940d20002040b020503a034014204049603040034004407c124010141100b84c401c10002006181d03503004000313658051103462580d03c2e103000c1188640ca0b10741c000c1c1450744030742d0a8400e080761a003550701040c1544400d0f5541c200207112100148810340c0e05201224130284903141850074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 580645539 1250 580644289 580644331
    0x300c010606031b17041707030806090709080c1011060405071a0c0c0f01020304180f0b03070f03062007031701050a05130e0f01020406050a0e1801030b180f0f0105 71
    0x2c5111051204400703600301400170307040080c44032605a910f4680121a80c40301c0c11031902400d030b52400d03621548102d9080c1d00003506a8400c1c00890100d501810050020100e080c1c24005070701d041040c1407040050680031014880402c01c145401103101d00003c01419140c40d00c008829080740f015000814400c01c030f454152003000450401514007101c030481540340040050b0728500c00d9511110031522011101e00c4024070321b51241c8040248510188454100c8100f0983c41c0c280d10300900311400310019090020845691020f842c0d8440305010445000403a0000422500000c400b00c2c001040c468040d5208074652403001d0045c039065034224807260402c0b002400a0070a4491401c0c00c0d592252501c811801c01c00c180352140c0c0c81c0000071590303070f5100c235001045580107420040c04203080c282c10710140c2c141200310940728240d0600d400496421540e07001d61140000d0090b8100a01d050349802c0e200c18288800216806000002c01e5000165258103081d20030040120891005200013014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 580646789 1250 580645539 580645547
    0xa08060a03110f03100c0f0207091401060f030204180204061209050d05070c15020f1b01021b03250513060506090105070c080a080d060b0309300c010606031b 69
    0x1da8240202c41001d10030f610440860310700700100c400f851a4034103006050343c0380364000254604843e095802d540d18030b030701c507041d14040e80c03400366171340c0c1181895500400c0403610412a41c0203140c002e14004d850290f5484281c0d90300c0e0901e600304040181d00107800c20015401924040c809080203c0501c40102c041c1c40e059210708004030741505008000440030300700420044d03240040c05454440717001c004880207000396100035900f1000350500c46c24081e1000d4046200c20360040c0303d0164000c2c600076000202640e1280c2441403940d40504c501e03002400003191100d00c00da4480b50110b164100707140381400308410740d1741070000407a40c07500d03000c410700281d241d66049a240030020b0a02c61364902c148e04d0700d102d0003c1e969220035a0f6004041c0414100607841d00107080100580b80306000c10f503110f01c20101103100c00e441d01c5d541513214010050f0b600000c0c1e1414650300000c0420300070030f0189003600e4001984034801c600c4042c4d541d41d00a100c09509803040c01850b99400e214035044c0001d800b03000d4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 580648039 1250 580646789 580646813
    0x70c02060f04140f18041b05030a0b0a1d070b0906040e0a090309050f03031803120c03072003060612120d02041a070b130204020d020a08041211030a030509070305070b0a08060a03 78
    0x247c203445840d01002d038035102c051038000c0245005012a80c0d001d1181c20070800342c40080d03800e411503904100b1703c1c140c00300309104007107102c00c0b010000c1d20185161070b41400055001c82e41d2030745c10000601c00052955904100d840c460240d0b010301040c41a0780d071030b00400441c0c158000e1842100c440581e039200b030301c00200355504032895003201800b4108200c0028500001340c4909400b441001920034041440880074080c0c051040541030f1a01d01c01d02c500301a2010168503054041e8003400018815141a02040003c0d0b16141e0982e24042d81002440ba401d9101850300300380903030005820003042501004180646d0100c1c00602c0c207014a0b41d030380e118500400781c0344c840003400c0707140050195a0f859044600302455a0821035544180c244041c001d40c0c822203040c0c510122064144021a0180d40c0b440d4110707400f10040c500c1c008481700c0030f5004000c0a0a061414442c4100200028000704401c2015101207045140c0f1070044900040190100608041c0514030705d580410010303440080300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 580649289 1250 580648039 580648043
    0x5040210080c041e03020901123012062301140c0303070c06020405220b0d08031f0807060315081903030b01030b0409240203040209070c02060f04140f1804 68
    0x2c0309503010704c2c4d8100182015a80c0001e50f114406000000303c4440d241400c4048501c00d0945a0f0400750404901039005007000940a080c1f90f404a4a144584106141e800c203035490700e400918540c07100003603141e03944040484800d400d6100f134107491035a00482d8220842680c0c030b0800d40f4104101c48502e45900000e00420306019804000b2000c21426070180c1e400b420015112440ca0070081b40e00e032007400700c8003039001c042038501a03d0405a00b0301102c0d116046400c0000946075884500315105807c0342c1d040180c00e41d0304060400b09071080240308101c0281100ea030301003005d0781c3c0c2c580240c10181c80c95100030700d1540441d501080003001c0341c04040025803d0305000501c841c0320001a005031980201c4070b90321500c0c0c60f2150003081a01807506600c2c1519030b11050b0544008544401240300035100a98000a020001001340384540109804d03944098003071800c0041603407803801c40e904280c01100d101100600303680114102030404440362074041310021010601100107480710107001d840 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 580650539 1250 580649289 580649309
    0xe190f05070329060702060714061b09011d04090605040503070219080d031e020a02010903080702010902061905040510020304090510030807061a100809010c300f0f05040210080c04 79
    0x742d01c20f42d40c83c0e40a07a10520703002004200400d031a1315650340c40c0d290455503c9104bc607910b00407030710380c1203e10640b00d0380710044e150130303982c0c000000d040d211103076510300041d03480390b1942d0699000510074050341d4080c602c030b20020741c9c941c3c440c0d00c10814034029500c01400c403e191000d0411a490000980f076003000200d00b00000e203040c4020074a0740780d60104004000007400021044895507055112403005800307581d0f19a0b95840c2d0b07a504a09850a0034800f80d880941031042c49080d18203211410101c000b5410840c1c64039a460020a441c4007400000d00b0160f04085030402882c4100d016465004807042c107605807031425503840807910b0203007c0c000b82c101e41d0b0b5150034180c20b850b0405855040107006110680c800010b0a00034040c00044408180d59400c107c00b804155005241c07000c184078540e4000c00d1061580003000c880700c0700c1640255942d41d10340200a405e500c55110744244010045000f14991505005000c40381c4004a0410700300428641080041001502070f2001d41d50702181d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 580651789 1250 580650539 580650547
    0xa15020d02040306091b14150903031204150b0603041e03090503030310030c08032d09131d0a0506011a0c0303090d1206030b010e190f0507032906 64
    0x1039510001c1c05242c10041c0107070f2030502d118051101c928102c00101d4030900f020701d400346c2ca032040c9440145840e41016000311802ca0002030980c0d00d500035115111000c0c003180c1c10800c2a039680b001c1840300340c0e002d41e00c68000e49081400c1202078010342c1034030300d815240d152a6051941d52070300240020700070144414170603c119410140f050a0100040c2402001c69840e0b08102075014041512480100c844030740c48840001d50b2200403003070320f100030714102190809007220504001c481034012841c1c81c01103001c010103203217a0b944000720303905410010720018414a41001000c90440c640d0302900f00c0790f0200c90a10700081e00000c405055403010880040c58009030600c3d569507010305a9175009900000c1308110000d40e00185941c442c0c0d06035914000c034000c0a0b0f80b00000c4422902000d801c04c18058018010702c01042d481c1a0080c402e40d52900540d584600300d40215078038040c07030303c1d940794851007030141c510f0b4940107003000c000d003806810300903a213400d6030303241c0c2c0d0070300040090b01a00c4081 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 580653039 1250 580651789 580651807
    0x1080705010509040b210c010c0b010510051b100e15190e010e03091503071202030613090c060305011e090c03110301081c0801140409051e0c040e0a1502 67
    0x9041200d48100c09031140d502282d00501b044261040d1440c0045144a0310240030450343c45550040300c21a08aa0074281603400c01c030a01103122540d49000341480010442800c600c0010305144010719110409080c40c0b942180029064400d4051a04034543c0302d03070f00702e03548101c0d141220364115813401203251000c40494403032405070440703210003140b651a15550a640c184080024400306d075040312089000014100c401c00680000e941c450f0000303000414581500e030352507004581041000701140442051004484184c642c0c100c4110344100c42c1c02d108021150b050301505000d007982140040c81e043e0952421044105079120301c441a541310701112170118060761180008a0960824903601d40e1a8040c043c2c1e50740c6292150101d8800511815a18502c160b10030760588282d11305208910ba00101000050181c42a00f900d490041645062442e000840001094403003440580040d21900c020841148c002c010306a4864011400080000d800d407200b5441d4200c00940042e120300c108 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 580654289 1250 580653039 580653041
    0x1303050309131e0f110703170f0408070b280c030c08070c020607080f0310080c1e010e0325050f100f080417040306060503060709060206010b07020102010905060c1c050108070501050904 81
    0x900300710410b1250010300101496800700c9484042c41031640288807540392781074245400c0c50100e5020b0300050b024003000c0c00090a501200350001098015044c000000109021184012003004940c0d03580d12061110361a03094000d04400024a00304258185082c2801924102412400911841c0c00048810811560405a03071298220b41e130050b850b803900000c1040c41c620103000340c80b01e911404810a0700e174604101c0c050700c00844800408002e1300800c00548036120691040340c0d040c0107500b060042d10b680c6c030b00c0d01010383c298200103c1035145440d05020f8003101c0300b000e10b07000e01c00d001030340014a600309500540c9000d6920746a001650b450415021060f05000d050b100d08100150010034080f16800207816100200c0c15503910741c80d0501c066442040c43e100c1d101c0580c1004004000b0340300c0304400350080c40d00600022a81284e41d07540c1c68109042224003007040100414602140c94800d0010f1181074007240082100e5410710411035510900780c400d950401200003080d081039211 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 580655539 1250 580654289 580654301
    0x7030e0f0306072d02010c0801120c1502030d110a030b0910061404080312160c050a060e0f0601030606030c0f031a0a060909030c06051e06060d021303050309131e0f 72
    0x150344c0384a4401954081c1c020f02a2411004403030010744910004105050002000c203655684030510540d001d00c0d01d8119150304503808040815030001703100c8007240c548180249611003c0400a09a81c3c1158543c007030704070f40d0050380300c038018444901040074141000c68100d0945460b0304180103611401640b06100c0d10958004075581d000100c1c85001c1803040440d96401542d001585203c2802c041c0c0c6d04440911660cd409010390740b02580c09004a03c444c0d1120030030400690aa41d01e118030350300b626103001c400381c0c4101e40183c3d90300c008009200c0c91740f4403000501010060801c505286856a030108000b80ca543c81150307000d4000300f5002849903000a00a00310f030f940a00c0010102c1c100507080860a000c00e80d1403505100000398100c07031160f030482c600d40b40040034442c151941c1e400e0249a40110907048401c0d5402c0140e841c02c1441c51030038000a5209800550381c2da070402c0305000c4185c0e460b0302e003260043e007850044440321200303082d0303240311846501c0c0025861040046040180c03403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 580656789 1250 580655539 580655597
    0x40f0c0b040f091803051803070f0b0702030106060e092202130203070201110418051b070807061a150c1f020a0905090103020a06120605030106060507030e0f030607 72
    0x10300080c00040790708002e001d02040700d0080b0000c006100440564851a80142100a0008008004031001281c0d0705880302c41560f03024007110340c00c588401c2c0c0f91400c0c0c41079401ca01d20040c00843c440e01149000d0181c4c3e030107450300f03242855072440d40401242c00004058031102140c1c2020074020480a007030418064442d07002469400b1011898454200960080d0740c1c50006509080c1c1212070001c1400843c1c08403400704140d02001d0b0fa0145102e402008003605100c0c540201c1000c450f4420301d601c0241c010795004040550391808645488800c8600c0086000741d810030104109030142e54034004d0803005901b0110036607881d40325442007410300410403031001d20b0410301700021720a1031459000e008038214030384842c00c1c601c0d202d104014011b4801d20000354404440c02040c40814440d04201c0c2c7c04980191003c680d4546039000a825140c0503003180d0001000800c40005041d80b00070600b05010007944c41400d10544600441d888907801002c41d0300b03101c09440024940448050044d06440c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 580658039 1250 580656789 580656809
    0x4020304030c110d03090b0d15030302070816080c0d0f02180610031e0207300e04020712080c131403071a0a0e0d020904030e0907030603020108040f0c 66
    0x3103400e00e00542000c0c00e014040e03882e001100c0c1d0000d62400e00d91540a2aa6099220040540c2c5451101240c0354421a2110140c50710340060032a0591043c5d0450080c5101e84c0260040b40d09080d80245030042d40004041c458204c2c88040280c0c22001c121300008500989035001d82c0320f07103030600d0312940c0c0b18404000e4200709148034204202c04800012030186400320351201885800c104110180d8070066800341d0300301c0901c0c0d00001c3c407500035401480f816103d0b4460074400c42050603000203200b4180031000c900d1308520b658a00702a80900c0501080b44220303811414070819440f04c4d00062030824284082c402c60313101050301803055409850742d032a88130142140c1e00e0b0b00c48003065510a0404a00b60082c81075030340c0420354000e000641e00d00b00c1c4100400c142440c01c080400c07500001e11200706500078440c5096980941c0750035810307501c258000d0300c407081560541d40a000c0600310041c807030010545051018030060307900400d041e801c581c00c0703049072145001505228038080b045901441102c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 580659289 1250 580658039 580658041
    0x90c071205041806090606050c1b012001061809080d0f0b0616020f01030b0907080a15080105090c030c01121a0319050c09070c1415010807091104270b040203 69
    0x11068100c0f20948034124170038820a41d60711401c0d00c02d40640c0c0500d040340d4121410710340070276a400311a21703c0c0d0070051400c044106807000d403040141005082e0f40b0800e0351035480500161100041d0281540c4000c1010040c55146441d013142502500f80c030040704030785640161889090a420042d411034005090950f21080e1265401d01d9040034002213004926225610125600910500c44c004001a145d03c00303e5641c0039084a5004008121041c11680c40b00141241007030b49800f031000c1d000c000000142820240411842c100c0d1503d119440380c0c0c02996484001e9a00180001500c41d02c080c021030b4000d64162582d18402d00b1543c0700c0d0305449400300075115140f14460300002e01d8002c005483c0050041414001c0c2c16200303d41041c042550300c0c0c8a00000b51804144980d132503940c000351144042000c0502035001000e0307110040c150320010081c00225400c1c4126001100d4a1000764070b054545000400c4e00d45040a0108071080c0c5c0301c007450251111a00801d036a51802007007155070b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 580660539 1250 580659289 580659329
    0x6030c040f0f4a0a12081006090506070302010e2d07120f02120a0506100b0408070b07080c0d080f0a0203040b0a02130803030a0911090c07120504 64
    0x50500c2c400d259012420300d0480d0440781081c020300c581418082c261102000101e00e8140c0d1605019900c074003408105006a04041506100d051200d40c8500d6044004400b0300a004010104c0541100720074080d008003041400e0b00800b200342102c41c16a42140c5030041800c0503401001100c00100c0b940c0504e221b0641908521040f1200100c1c0012085000f07550401c0071175594102d5004030001007401c01c00000100b40c10341c80400d41144000d1450228102002c441410b200008508880c0d6500500234040141c01051800010b040300c55043c0d410716281022160703807420b81c0e109110b07007094005208000c0c0440001102c00d1108440700301c40300956801002080201c0840b090a001c5079140b0101d4480030050003202d01580e0400903941050310f074404913800a502000340d03d4115080200e0002c0c1804051000d140b00350f6900800050118041c141320800c072180720000382c81801c880d01040030348400f84040d10070a40e0441081d180c06500d545054900d44683e4100080c0c02c07042030841d1407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 580661789 1250 580660539 580660541
    0x8060301231e0a0c11031206040203060d02040e07081b0f1302041a0301030302010c36050a030818010f021005090138030d05220e0403020a0302060601020a020105030a020306030c040f 80
    0x251900e40c80d0345031385e0003400181d1865102d014049100c1902014034001c600f1614164000e50b802440003046409115001e074000780440303080203d02d5159070444201042041c0c0d0034440c944885d100120490102d000203400147e01e00301c11524948916250803c20505020710b505640180c1010a01c03c0c00d901c00c0720026003010341091004034010b608000794400010311800c000614080001c0e411109814404031841c40c40000c3c0103090100c2c540c0c801c001416a445107038110040d8040c910241c1c1c1d40031949002161140500700490601802d0129071040030f60004101d22850344e00d08001581e529083c9800740582011210fa028880082c0540c1034031140907401180050300d107000d000c06d2903024070245501d4058506114010a2051101c1c02143d42c3c805e001901d23029000002c042c03540e441c5c1506001c2540c044e1001e80060b44220004010950100721040d0042c070240010b01584259500080c01391100412205013140c0210102c0c000707840403c4100208040107100703102e0981c518035290 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 580663039 1250 580661789 580661801
    0x50a0e24070207060e100c05010f06030303050a0e0c0d033c090b040501030902040e06010b0702090a06080a060e010e06180c0910030233070308060301231e0a 69
    0x5a9001214012810312800000e4203030454080b5205c00c20010304400c00c000c00e4030505440302c4248650040030b040015001e00c12041013017004080080d850b42182001021600020b0800903d10314000081b1652240082c0e078030a0040c080b10f40403180c03034142ca42140c8031400c04a0401e04081e007444100344041c1c0480603e00e5040714a010042c10100400044030400c0076485121001d540c1004180400d51080d00081c40c080c1c009000811590020000107117000002d0341b007540480c4020030440110b25180d03170001d8002403135660034001130b0b00b04110319817580240c81e40240142e6540b0040241903000307402007081660040f040d204685010b011b140340c0036506d45901c484901500444480b0340c500642040c3c0109140f035410382c940d038117680c01d100140c600003811089402c04107032811210742c82041c0c5801500e00c13049289803201011f25000d0460140604541d100f641043c007400c3e112441a02160200000c5104520071741d11074441c0c03441030310703000c4c01001c3c20310714003d04001c40107007913030404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 580664289 1250 580663039 580663093
    0x31080a0501140618013b09010b0604080c0609040603080711040501150c02060711090c0d1107020d06110c1005041106090a0618090204060c0c090e0c0103050a0e 70
    0x58031240d981c842003100314528840404c80300750030390b4018418022502c61104810100f02c851b010020072409801c802c00681414640040c2452410400e0241c000e002d070409a07031083d02e1940c142030902c081281c440c034046142c0782c061080424442c02503560b903044240110f40009030b85545800c13031b040401241a4075803046019602740800003681c20b09080044698483c503955401181d4203a908200b030650000d2800c0d21056102d964000b00c5656020100d80184c0350301c5503459507011303100c101c3c1d01903d4400d902c0c02c81c010028000407000d41c4a15240f91000b44c1c2c0000001000700302e80f01e043c4050301844074050301311300c070302d00282030031040d40d90156019074007030a10b2001400d10030040000510a5104594001100c0c0c1010030a150250850201d84062080c1c0301d444c06894071645412070b0459406540024444204082444102040a405080300c0c0760702b40810783c150305d4529520007115240d541015a01c00000b2042062980540c82c4884220155070f0a500c00004508001030207400c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 580665539 1250 580664289 580664321
    0x40c0306051f0e0712090c0e2e0e040f030c080a09030b060405151c0503070609060b03061b0901020a02090406020c1e0a02040b06070c030507140631080a0501 69
    0x3042c40e00410401c1407003103001755100b2020005500c90140174140d510421548414000400306070b00040851003071107120030940f01030172030341034018211060941003014021600c0b21441030003000000e40c1401c3e03115808c0701480c07400c500b4515085800c180d12600151521801050504034194030600003411a80075504025040d16001c0c02c010884400381e440440e506944582c2810740c0c1003020652103000d40c440c1164a0008054584505682c040c0e441101d000b40e0307a514413001c101c2c60748503185e8010340c1030700181164a03250048200000404141d480e07520008078040d49681c0c400c10140c0c60165014003c05030a003030a19005000e500300720315901a034060300f10008000182351901580440c3c0500c000c0912101c2e0341c00780002000d00c41d0b01950480420400d01c00442c002031750301d400640c42400203080315440e02110100801b0500440b078032036941001074084907060b84401001c26110a04000c070200b03c404005000281c580e40000a2401110005000c1c000c0c1988070125546a03015 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 580666789 1250 580665539 580665601
    0x106020d021506190e0108030918040b28021303031e091a09030f07051009030b0f0a1d0102090117160c03020f0304080106050310020708030a0203040c030605 69
    0x307036240d0954149032100242202c000400341e24100e10106000c0c50700b050440030083e202d03000100d262100340c0029242d548005402c00da68184078002d1038a0150b036040d10006800c1c41d582d0300c183c0140180c0385078482200c900300c0805c102d521700400c60704c469100c0402c5581c2c0151084968081903548003c0e4040b951052000380c0d40c4994900400a00255980302c00d8141e0400c00d201034444000910101200028014040f2686041040c0d8000f0300c14940204100c518041c00c01c580516000b42003010429000320401c0000c007803000f0130b40c0043c1014514441584da00c0816401021043e104511300b031200c001e4020210781c10b50050000780000c4c0c0c1e0746981c02110840c910b580407400d40340e18900d00c2840200d14140b6101d00020084540b103881074440410020502e41d103140c1040d0040c110303a0f5914441085240760402090103c040450b400b9820a4140e443e1000d090000030b0402c40690780010000b010449181c01580c05154402d40420007420b1000f04000114100c40c40b52004140c190 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 580668039 1250 580666789 580666813
    0x30f17192d0212220e06031b010e040f0b0a06080f0f070903060e1002040b0a030e010b032509020703050a0e040b0f06090111030301060225030b0c2d03010602 69
    0x3032800c0c080d07080c580c00401d90182a443c8403440caa12001a21a800500c1480382c101c1210380d5202e013005145101002c900e60074450101818030b40704943d0081400d02c54628003210b0f98104201c64100c010440e400517000d0f400c030000c032000d400803c800940c0070072081c5000c501e281d040f41c000c50160803140108c2815584060000108407029500440410b14201013040050201d800101e542c408480c03e132111240e159201009a03007040d006002c0d507100c0880e20b070f900158103208224521412400034010b0154034400700c0d86031901180310b14000d0900000f031000045520043d030004042100003159110000d0900802e160020311402001030f0304800ca10056140c24026040000d0008001c51103403581d100800c103481d0f029240150501103848ac50100310002480034500034861038000d010b01c01d039442d0200581101d20440e4071344d00c0c01484070600205003000c8441d6884440070000c903079038441c28080d02e6021038512892100c1d041c40d11458204490149002e18121286502210141080c42e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 580669289 1250 580668039 580668107
    0xb04030807141c14040834141f0507030b010507020114031803190e150304080703142b02040617060121050619030f1719 53
    0x351654120107002d01d80220b0700d4000c1141c14410361400002c1c81809010745074036031341d000b11803c0d2055003011035070449070701c0c0c02184200f252900c9450b581c045001070031440c001350390440c0042c088504000c0f8a9212135010419541c2c2d13220b54038010b8424000003075601c0f0161404492010009051040e02c458a5009209450300340b52b058682d270382d400d00003201c040700b00e030001403401442d201c1d0304006140f070754001d10003420145940803800c80c503401c020101802a410000d80786000c0e00d502c00d020f040d104425800d8039041640401070b036903144200d044c1213803624001c0d0103c9201c5040010307410742d00c001c0103a40b400b184600038644c80c0320440c888803103400c901491103450003192401b04203803034640030035141c154445014100141c0c96002194403203600240c844c00404159592024040385180c0010140601d484821125000c84e0440c1d039003810b00501c046009040300c00d5440c50a100182d03023000c1d160842020221a004020114001440a800580c2d140340070906903a0703903c00007401c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 580670539 1250 580669289 580669307
    0x5010b06030621011b090e070c02060f03040602070b0901020702040b0909070521060702060708010503031303151b0207030209061212030c040806010f140901050922020d0b04030807 79
    0x3030441d8602c0c0e15802059440000c0c02450b62044d55035545043e0b0600c0080c20803152050041d5900f00c0b81a042c000007100c5804040e01c10000d20560130801401660f5850443e4403601d0b00454064583e02c8510300f410103402140350083c040b054041c20002d540405501420341580200c6040c81149503407400e00180e00030540e20400c840d080071805000908100300e140c0307000001010079020383c2100c804690700380038040d00e4844c0181c02407070511a000741d01090103805040120003031440c00030041e08a03400c81226100090400e46c0300300143e420303025144e01001c20000f80b40c4440c0141604c111b0002c2d01d848090204910070510b12010405c4c03428001c201100181c890f9004045c003001202c410b0340030b0380000744043d540701b10800010480d50824000c4900a2841e2441c090344141001d848900014010807114050218500100b20f55560282e125410200a1010203003d030a2042001990306241c00080d400a040c03403198010445c0b21b81700c55106070b000740d513209480c3d120010100c80b03d2407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 580671789 1250 580670539 580670551
    0x6031a0709060e27070315061b0b2703090310060e0414030d020a0206010e1f0e060409020307031a010f030b010608070e0909060403120b0a18150308030405010b0603 72
    0x2c520400035001c1c100b6294103c03980d101104294140351303001041d5014107804a4000000a0f201d95680c0320f40c1c842d210000000d407146040107115408009031804014040000140103210b1000108480d045246200e0400c43c2d2000e480a507440050143c0556070350040303000b1030292040503000e40e94031246200b07090580d082c1c001c42036400d80340da44400c0000201490341e2107543c08200604c000c2e9481e1071004080359007481d0050030f9290704d0f00140c800c0d980340041c40c0400041e0403a6000f984c3c051604000000e46004280002c0300c1c5c2c0313a0388003040040800741030094061249203004410701032040440b01000300c0e2500002410781e229110008401c031a84401015582c1c0500180314490203084450750215040c0b400849044032440003c40c03c0340181c1d0ba1700d078a900880140801e140e03004020503865180010b00740703e01162100415040c107032a1141001181e0304858540c2c480d0f0040d00305012202245170980d1800780ca07801c04010503402550100c0d9150310b4150211164100a800c4c0c0744980 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 580673039 1250 580671789 580671797
    0xe0303131802041206051e010f03021e0f090403050d1409190309030b0a0b0a0303030b030c030d0914030f15090727092102030c0c030105010b04050d0305040906031a070906 75
    0x4c041030741c40b10040c0601400041130150701084031441405d048203001c4c001e000c00b50064040501d140148060007044564295006000c4441e440b0180c542020707000d186182a84d118240c2c1d521410112524003c02120800e02800d040780d9100f200c8040141b980a021020191010400c0070840f090300540403001c0140403170003030b580800100d084101120340c892420480072403a54400c1e0000707012800d26400460100341e940385100b0042c1420810242d80310404e400426120600d010003600340003462107140480d501c4c058407004c4540b414460f45c6d000d1107002040f02c4a5204140003805003000458050070248603100c8005911a800c481170a102c9280c1c031402109540c68021000281103101c1d019944030041480300c66070205044504602d800080d07000d551192083c0144a050a1088070428807aa0408005120319031001c41190100c480403120340410040c1c920702600c450180b41d20407030380d140c40c01c5000024030002c0040b41c0601d14200c00d21250b1a17403842c0701a2140212801540000303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 580674289 1250 580673039 580673069
    0x2060a0203221a0d0e0715170c16050307050303040c05090906010303050313030309020a0905101e0504090f050f0303070906031404060c050d0911040b0d080711010e030313180204 78
    0x2c14903001400350036850800800c0321000b080f2410700d00815075002c1c0c2d441e030480140d2800c0c426840200503600c1c81e009203600c421818007050382000c2b40200410303001e00484000e0b07940f081040420031103050650007025a9240d1030542452203840403140f02ea94007032003a030000121030074404100c03607041e40e600d61205403d41c1c854500c0030501051080003181410344d00c58a00c00580d0703864a00b03000034881283d0109851030b00752112810101d4643c003e07030040841c0740a140b90b0103c030100d85004c5e2403050b10005003204060030840403035000248050024021040501d160ba072022004501c5a04940ca8070008181d8a100071011a0400602403442d0150100458009641e41d003041d000c60125180240c14000c2c0501920100c0301f52480484100b0740e80b202900322410980a8424400b60480d00300e1040f620319202c0b41c101d4403a05030010101540d900503100140c1c02082581d00346600030702129101c14401030605a406414001da84125041d1000b14407a0041c1c0c0c000c45041d00c01c009407507180c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 580675539 1250 580674289 580674329
    0xf02030313020f040f0b030f070b030103020d081308030901020d0c0302150612010f0219020d1403100b0403080d1a01120207080c011e1401030c030b040203070302060a020322 76
    0x9282941c0d0200e0b070008005031041c403075644a0141455145a96400142e50a8a50105460600d80b41d10000d880e4000d07203070812100362401d040d0380c1120f8041c0c0c3c0e449001c150501e0142d00f01c2c4122441e04007071072046240810711000001c080c2004030300c04c0e021140b5089503418107603200100d01b40c00034010b921007084820070000d902405508070f4805000f1040c60048002c4260940b045048001c0c0c156070701192001c8060088840000b04641d5030018199003031030210028a220001180c80300100000808034640882050600c0001e0110b40c01c05c60721180c0300d1030840001d50003000c1820b220750030841e9031040702205070311141540005843e840a1900c0c10f024000194111540030381d90030b0000d0081d2a034070482805074094400f601d00151001581e00b00000c01210560307105900006000f800620000d0780e4481607806032908000d0f41025a669232001070b1410885420080d0403450100b40800362034bc00002400079000e004a0b51700b800f10000441078440300e0544204a440e050b0786448890b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 580676789 1250 580675539 580675561
    0x9050d12020712120f06081506060f19170109062303190201020106030b0408071704120311192006030f060603040318031b0803070c211703060a060f020303 68
    0xc90303e00c0001d020174659a101030340011a1001d40c0400c10f01e4002d00e6400061140000c1d016a000508480082c01c0c040301407103500c40c5016803120b040c070030900101f0078000c0038020031b07100ea0340324500c3c0c5800c82c0c1c035030b10784000601070042440380a01031212a1580d07500c0085114000121250140091104072080c40009000110340101641555a109c0020001c505121082c0d813213640183c1009540703030030380e252020900d14840c005030b502e148284024002100c411001858083d0589003c0d440621012802c50400088407020420503140c0c214000400900b00b82e07401000012313034000785e110414802440510b03c021200501c4441030000018003d290030b2020b55040f03406480c3c0340c4d0440704040c9044c01c900c0b00c680c00035180d9410200d1000310507040b00070034101401c6198003a60920146994a030361004042c01001070704c240817120380e01c8000c401c46500b510240c00c440b8600d90103840c401948003d40c02683d003240151490390010420b0743c0500b83c419400d9500c5d41c010340c550703501d0420302e41d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 580678039 1250 580676789 580676807
    0x7020d0b1306230c03040f33050703180203060f090c1806040605010f0c060509281703010b1801020a06020d020d0c020606130f0b030109050d12020712 66
    0x8088a8034800c10740032a45920494603a0044640d100d54401c1c1c1c03155181c08805002400c2a038050010801c000015012881c43e00340306500c400744200d00410411040c3e51200c1610150000b4181c42c0103040e881040368000602440b1030b614100240e031412242c403c0030313501340800a50968002404107881440300f5110544c008000d0080c2c0d00142003000000300040c041c80c8090f41c9500401003800340510381403043c0401444c0900705850348106840000d420303402001c401401590359080001c2034101c0a04c00c0d419401080c802d000200400000081264544440141e400200300d2035020a545282e00882c0d050751003554000d03040c481546800b15080c150801054110301031801040b0001d101c90001d4041400300520141e258884070903c0307804c03150070500001c00c5600110034081251100d02c1000300c00c2601920110b0002e801861543c050101d0302c106540562070f100d140d60600001180ca001d0341c90442d80c50030202404254044207900900a010b02045481440900340500401d410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 580679289 1250 580678039 580678051
    0x1505060d0f1e060b03040b061c0203061e0a0e0624090408030a0c09050f040c1e02011508070609180b0a0f18090507030f0206190216060507020d0b 64
    0x1140c0e00701030a1071a0705036a0351a02900650b800c0118401c40c4021500422024001202c00030341189065121454000300c01f4202c5402111207400ca04418580da00f61b5084494000c0c003200d840b8180303e0494a10391058104c0350840403100c02c003003001a0039038060102c2800803140240f4a988032031000c0303a14590382d420300001c01440d2098012083c0c40300d102040c8540d00540c041e9032070b8030f41820a40309941050a0b42020011800001d001c5665480380c4e103155076500b44c0c0d00040b40b03140c070041a10841c039907039107001e035864035031103445441581500f1203007000002000100c8516a00d9038060382d034a60a0282c080840e90707110013840150035039601e01d510095040030108101c5080e40101b207103890584c100f014075125040042c0f0117200707905000d10070b90301c1e1340108021440c078076210a5154090b0f030000078078a0403213a818000b95501c0b003045d944481c0680036400c40102511401a542e0502018080c0303001041c16400100075005a094640054000d404070189500f683e4606840d80001454 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 580680539 1250 580679289 580679291
    0x8150631090c050a030b0306091005090106031502070c171002030406110307020a02010e012a0602040513020c1b030a0320010603080904060b0301030f141005040308070905041505060d 80
    0x6042070700d8010308030b641e4990348840c3d640f400001402425585000d1a29010350f110009201c0f41080c0050011200c1103809000541602c0301c01c0f00c103003d060950301c060b000e15807485543c0d0700ba071801c0c2c2c01095124440c15041e203c00c1ea44070a9a2200741100d0344400706500310300413220310304425400655002d88148030010300001c1c5c840f4060840d0308145c4803140140d101128070001c5581100d01800c00384030900700840d021800c60382c81804000307002d0a40900c80364038001e0404004054058a000d06401041d00c0800c3c40c0060014000390804901c0740242e208240c4881c20600504c18460755201000d005050300002c0c3c0d131405e44d0103c1140c515250040007401410728011001e1190a0145106a0680b0381d034141ca001044166440b85c0c01080040d80708000400000b03094004010703103203a002d040c02c852901e460140350b050056400d03d1201d820b050600f04403c050340100c55034402c0185440302020103490300c0038801204d0ba014421035031444561030601c0350f850720001500d6039000e00c03d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 580681789 1250 580680539 580680637
    0xc0c0209010308030a1103100303050c0109050102031e060d030c0b0601141614030325050403060501030b040b07020606031e03040f151d0d031b020907081506 69
    0x202040c12168240c0c415650148003100f8000d0948540c0130300c40c0010124905242076007869400a04040010b05c0001c050010000325009a5002034120350b103001d8105000315140c0c80c0ca111070b0161200c00d00044041c08228000041c02450200d521000341c1e500744d514251400001c3e600c060030349201624050602c43e080c20840040c030b003503100414002c0d035440645400d112280c82d00b8010580c0b0401807243d940c0081c01013200014107088950700301896140d202c5404481d10304165020320590304080c1c05181043c0012040c0200760030100d004900c43e0308030321156555403004070f855003829500f030303035140d000b1640800c03001900d117a4550304131300131000b500e250590341ca2691014117070341d6000d24a50b02d0002c136002c80b215004038420100d040b00c1042200b0760000d110005111150080b0000d0500c2822103c6080c281c800b1409120540d0b405000744000d403c101c1c4002e4032043d4122891440c0949822010010b420032100359103620400d03100325900e0503d10711080c14082003148151040480d061 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 580683039 1250 580681789 580681793
    0x40b060f0a06021609060e131502070c060905030a17210f0603010b0d08030109050c1b0616050c070e0a0e0a0c0602070e0403020c130b0a1d0609190c0c 66
    0x80c070714001003580340c0082c0039206800d880e00d05107005039800340c402e89241401c2044440319103840d20780d100303007100300c02c886039051813800c402c18035101102a840c092002c80c240782045114144070042e00c540d6182c6001c131990329410075039201c0f0340b103500a140c1100b10740b4003010b0705451800b8180d00e4201800d041b079081c040394102d28034100c04840e015002c559074801d205483c1000e1190180c80c00041d80c00c0501c1c4286510340340d210b48010710400300c860340d403040016030046403101a10904803000c0c840b40000964002c3c142c0d07580b2070a9a08104003400c03100407207089401201240e451507a8035024141c0c1c0c6280c0355107400794510080c06100b045403510740c0640d12600c18894000b0f90352040740705085642c11710500038a00350700c40d00315802e05080e170014000800e40000d40440036000440b108460340c101542942c010b0514142074603004040450003042c4024445030940111440354004803140d40ca010030402d0340e900070b95185103c0500700c603d29101c007406402c402d1155440b424410300c030188039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 580684289 1250 580683039 580683049
    0x111070803221706040f03020a0f050307110901051809070b042909013c030b040f36020310021b06010501020c37080f060f040b060f 58
    0x71800e0041001c01d42c2c00807140c800040581c0a07000c80e4128206a01c400101c865036164003900c0945641d05074096101014803c10a61048640c800c0b1a2041254540303000c907544c2d00280f0044441261020300410f80303041c90100749048500080011021601c0c0b0001d204e44058044c25048890040c1c1c0b0022841c00341441c000c00003858081004d8850f140d8101e00007984403010b480c50002540100084405603a1025403044801c10000c0c1039006006502d400381581410a2002511483c5480742e056a86406601c0707107e00000546050045180e01700d684403c40b4821426401480f07441d0a4006924004803180c25188480ca5003540a240c51500068a0980941080124240c0000e1788040d00803404115615511440c401081154103040010b91500c407124202401150054604410340900c1020424a101d15480640c0e048000c1611707840358600702d00030b503005407142450000b520340000815a02c9801c0000181d945615569542142c0a0010b480103600c89403010b1550010358030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 580685539 1250 580684289 580684297
    0x60c060e030301060e0306161d06120a020a1b0503030705090109121b05041a040203060402092e0804120318050303101403030a0509040207030302130308040501120501140111070803 79
    0x86034035403610924a20080500d441f0008249a01400040d903000b100c1642041000541c003121411596407210190081512401565081300360030000c0e02c10f00c01050803a5005201d00d110360b40c1d4510b01103e50744240c4161620455004205a1080000440349803107070b030260025550501d403c0780e2556440c0f1041030858180c140c1501c203010500340101040905c480b0480c001c120950b014800004001c00e8500851615081107000c0d58001000807050340d40d6504552a141e0018080000300590443d0015040214101e845030445501e1000c04101d0148224511480e07020002c210f00700503c040840103072404443c00c108a618048282001450610146204d402c0d80c40b427005596141003c5041c1c60f0f0101c502280c001d400c10040c3d20940d07507202003221101d1000f070b40c0c056079640312450214001e109168071003a03e2104c808010007084003a00040084803002d0341c1d10020f031301030100e4500c100c501c01c3c85aa100028203501e000000e50141d505050300da6520780603182e071250b4415450307040d940 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 580686789 1250 580685539 580685549
    0xe12030c060709080c040507020c040e15060d080301090b030309060d0b01180605070201200a0312050a020a0e220c030f06090c051e04180e1e07060c060e030301 70
    0x300c0c0ca1140304104101c42580030140c0d141400d4058501034080f03445e0035108002502460310b0f0000101e446000b048074102c1018094003c01c5020f030280d2072241c0b0340405084070351601c0c04000200380f641c900312020480c5030303401203211455a468072426400600050100ca40c15010900c41c66815a0b190300103041714074035002020480d800c8440c0014503201c0c0d072003000668003600710420300c0400e0b0703c601547d500701d90a0030314060020781c031a004420600f5400d0401d405100d01c0b441a8101071f401241502003181c181c038148941d440d03100c85041039001e1039117070000040d02c0309020b040c240780000100300d0190b01c181c44081384d04485a0020182c410306801040882c0d100d1070380c01c3c0203e11074412070008000c909800c0207a044607040007041d0744500c040250100d91204502e0380b031610f02c84101c6008219400c101c8240c5c508040700140a40300d003010b25400303809050010761140190f02e00001d0f55003d12006419600d00740501070715407041c4c840e41502c80e1b65680c0c11711401054108000d5010340 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 580688039 1250 580686789 580686793
    0x611160209070903150c0302070501062909090609191416020f0d11030c10150518040602181801030c0816050f0d051006030b0c04080318010e12 63
    0x2049006020798440054011820441c0121081010481c00304014001c4e40070482e01103100054800c0480c00f034020b031940a041c44d440e03c200000c46d41410a004c030212400c416441c0d040700c4031111107802c180508491590000820760019215203445154664442c92910940e10710801144118045502c00c0c3c82c3d0f02c10413416003042c04a200241c18040030076491341d20080c01d161500a04c40c40d01d50081240c20030502c100c565958800070b8041c0f00350790011881c8000c45007020055a901c501910b8142c01c64a140c080e5103c0110701410071448407550a00607031400e0100e502c55986002c001d51185d0f54503070340c0d03200c140c0305aaa25581d9130813581840b50441c103044015410741c01c041c00e280840d9480005c070303603000020800b0340c01c02c0000982d040366004c40c5d03402c5d40301e081100810346060b100100140580a5074440c1000c5241039403103182540e01a118020060780c811b020450244194054103240343e0003800706030026160b2100c4036003c2c1e00103242a00c040c05c901c00110301c0700c03025408013840f15 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 580689289 1250 580688039 580688077
    0x613020c0c1309111e0d051606050703020318010e0303070b2706040f0606090c03020d060f0609050d0c0815070e030105010b0a0c1703070e090a0902090c070611 70
    0x1600c2d06503404403011110325801c0107103841581e03901d03940d501c03246140c60160019003611126425500590001c03c04040c2103006401803900e4a1602d54044407904212040030b0071003c40c0d41482642034800d065499001140740007040c0400869000078004030340e04000b40c2d41d07498125034900780040d0401d18410001d201c59030500011189012100005441d0f2003603000c000d4450001001500030b40040d0010b8200d2010b500f00d05002c006002142c001140d01c5060155200d0b03415031541c000d000300410041c0130414180c0b14804081008900c0c85403e0000d660040180210300c0c2440c009441c1c640700e000c064a105030380364481410503101d0b8103010050320008041102450300b200b18041d0005003180202711540c11301d0140b17030550041711007160411903000b40c2c2c4020005418081c0002c51a49401c003070302e83c5001000180041c410306d0040e801144403401003070b4800e80901a40403115401008080c2942e2503420a43e69070700041000d44280da29a881029080da07510b000b441c14421f83c449040d40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 580690539 1250 580689289 580689313
    0x21f05060d051b1516170f070b010314150109021b0706030c080c0304120806030f010603050c040c110a1209030b0a1a180c13030b0f01030605071b0206030613020c 71
    0x80000314090900110820001c0d800c3c40003a645ca001c800030342c0914000e484945a030010081400380c150007034541003001442c801403204820400d4100e17445465100c4071fa0394aaa0846d07118086034500c1300b580c0c0c1401d0018070030496030381c002d0504100c101007152a06078540145c0c5103400c85a44c41800400d54601c05131084c140e02c40c80140e4040060b000061646c10a40e42e280454080d0400d1b5404000b1000e0109005aa040c08084031084c0054002c0c0141d0351a8280b15456403000088a4402c5161210343d001c81c9000f05107161010403010050181000d43c1d80341d070304000c1c0b000302c030603c01c000541402000041c800c5468600a120450000424005041164003080114100144a4a049280e680441000440c86548490300041c1e40c2d440e41c0d05003c4c1ca049038105500b00801102082d4200040280c5011266041724000c20062180c0d4407402030903295102c8001c0d6520742c40d020b00c40c0c52005420810001c0da08440054940d51303481000034443e5081760005450046950401b40c80c0c084 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 580691789 1250 580690539 580690549
    0x40b0414030304030510181a061905150a0507080a11150f06120c06070302060405011416031109040204081c02010b0d110a170a0c06021f05060d051b 65
    0x511100e055005529103070442d210a5683c0765541144080142c0b1204102c86550314019038100007640050101da01101c164404000b044049416074024071180a070030914080c40c40c108000c9580c06400f50b4610000d0400310100c99228482020510130300304260800140884000c0a92034880e42d40c0c8020107403020801030402a6510131400d882c64010306120740c0407011a403050308140211070004805840c0036050f81840481180300f94007000120b168405c2c19008078006211301c0c0700c2d2000b008030440008000703100c440300b074a1042a500d05580d007850040d001c0e42c8083ca40d04043c4480b1350400c0301ca107001030160f0b406074120000c81e400c10944800c40003491107411110f814a80001c1c491204035102156444002150180040d00e002d140030356141c41d901c088502404541d100e0780c20212404c01d50999070200c195040b100b0540303086000505500c0401d040320040320600501c2115800c04922502528010304000d9108528107440340c0040d0040000d244810001000b090615400b203007001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 580693039 1250 580691789 580691819
    0x1110a02070e1b04090209010903050d0c150e07030f2a0e0f090303070e040204030203060a060f0b031509091c081e060f09040f0f050c1c030905040e0307020303040b04 73
    0x1809044441588000c0f0b400c0c11016030f0141d9648200040c3ca80c0e041e00012907480d040390f840a8024010941e0107148168019810401c013405846240c1c8951003880401d811101400c829041d6504442d03002d00009403000c00b600701e400c1c099280d007a5035450103c185d140941090425041039500c940e0204490109915855813280610340d42d0f040c0d52500500294403884000c0030306040100c41d0000f180182e0712581650040c5030041c0032101c451501104910092103c2d0140f0a49542e001c840010403181e071804480c40f8001c0302201110001c0d00a00340301c4008030213051a200d6026500132a02a543c200a41c00b042401035519140ea60401a451301031402c582011607514240c072000300841030f1914480700a06402c02c0d0b584a03083c0c0d840f801c0142c140d584002e0008c0c481d1854900400900000160803800b040c411a2030252211000e5150484458400c10050110391854420041482c040d40425115084501070307900d001190750010742180d010390001d11a4260200e8203100481140b8080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 580694289 1250 580693039 580693051
    0x5030412110118050603093c0715080a140702010b0406150e060d11040b0c0105060406050d0209360708060c030f0601121b02060a02042601110a02070e 66
    0x210228050070f040c0030702000d425000c0d65005803400804100008010480890701042502e0700383d241000c0c2c00c0c2d030080402074444c240d24249030200311981c4034106c04140c94044030302c0e42e00309101c00c00040301c069030401c0c0014500f54215030b80324261341000c980c00c0460385c810030861380001641048002003004840f070310b403c408100003010b41e400ca04940c0008a804483c10115030084e1102c8150012002130845a079110017152030120307001405400940113030001c1c0c0c0041c4002c1c00300b0343d030314020b0104035070380d078403440c5c1d40f0a000300704200150400d000016040035007041544070b080c48a01040410000502610170700c442210710400e0002c10512511002c1d090100240025050101400b12760f400094242e50f60b0314188804182180e0068040000b0035218600c2880f801c031200d40f503021003407500c0d54a10054010b040000304170102c81e1080381c0944001c1400c849161508100691501d40d44080c44201c543d079074424840c00102c1369004e020741c24a60303401048020b043c2480a03090510203012 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 580695539 1250 580694289 580694297
    0xa0801020f0a030e160303021e06060f22062606160f0306030210030507080f0405030a030b01030207141c03090206040e150405071e02030f25050304121101 68
    0x11490700403910340e0840310414034034034010541c10103080807075081a000e505082d240d904105c100200301900419014206d00700c00c031416102448402050781c43e0a0b04851103640001c0058621400e840c00d4065900c0c05401d20300008a1207400b20080422240c158000704801d41001c2a00d807054007040d480000c022107201c1c041c00490428900c00c201500d940000c00c82880002d5180c2019035100b60720000046400074074030909042d4440000d40104000d44a0740300241c1140000703548402c4c0b100195000d0b030f9110b00214507040d49094100c0003405051919030416408009090200d01405010b050109a2074060070b540b0810041d006a0701c80d40241c45000d02d0b042846c240090313071f565419a41100c90389110090300e69150b11140d4610340c034040e600c070b602038944402d21440b682d011405000144803500e0700541201100d00c1030741c0d64002c03000e96032011802048250031410aa405485107611514210050b0300c4841ea00c040c10b58025410003807044840c009280d050081d103400006a0500a0070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 580696789 1250 580695539 580695547
    0x1a060f0d020901030305031f090f05180c040c0504170f1612060c0905031f05010506090310020d1d0609011401030f110f0a0608190204180507140406030b0a080102 71
    0x1000c114503482c14440a41801404000144e4544c400c410325021448510011090031351209404d50090803141824510b080c541000503207402d20149009400e50040001802503083c2881004090511071100d03004011090200141f815101d0ba001e4080319880c81c054a403485c5007a861500c0c00955420180e158008620200aa42c00408650b6400d40d000b02c008140326641e450b003521142c40d0360b403201e601407285092030f800c500d412903982e0510508500050040380d984004000403400b4034a01c1d140c2c076400403441207108002c25030003004480050100032804250030034104140308541c001c5940240c1001e010059132444c00e03c02c5404030b40360104610315035411519800040d403101040100078840c00302d4072040035912180b10f0003400b00024044080c05403100302c001c00e2154140d414414982a042410b0312981690080d81d0503074038280700c1d5080c07524156171303110064040034042c07030103011503150000200c80c1000c00420150139030791004200c0310031410500848481a5100c0c00761a44140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 580698039 1250 580696789 580696793
    0x314210304060b06160f02040c0f020c0118030b0408030405010609050103120f140d0207030813020d200d030503091c05030c070303020904230a0606170c071a060f0d 72
    0x4010380e40c01c5508668000307244055200880c0c800d201d42041175114880d407964402c20440c5000340881c02c0752003a5028800b030b00c08a0b20a07103441440c0c20080e00940c119480081555115904a00040d00c601c840b580d01142e0740c0d00c07580c00c909010744065681003030000820091040034010303c00280411003040085600d0350301d6032581d00041c00c075102c04201d01c0c500100300807485000040310003604920242c2d80c40c080c02e54080c000b0340c03100004a010070074502c001003011100c0c244121426802401c402c0c1e2020b00f80d035401d14003540ca548250340c0725642000700100307030b00c9410060b4982d0307119490b251340c0c905010303100b1032804502a0b44c042807001c4284607004240d51200959400c01507810f07a03151a800985825800f034000e940426030003500d40b0a1014000e100321030105001c1080d0030124170151140a50201622081e00030f030004140542c01004e200708111101b5507010707640d03682e464101a11541c0e141c0b689460b040600c1030b61203020050000c1c6d80381030700300202c40c190111041c081c002119 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 580699289 1250 580698039 580698103
    0x60c050a1d0d0f230706020c0315010902030415020f0a080c16030809030412060b0a1d132d0309060302121302040905060403020604150b0310090204150314 68
    0x1454004142540345030800042280c0c0c00544d0154044e01da41c13100090038802441355403050035100d03444c014418030080400b107041c045070540781c0703c0c01c03d40c0b05d0310300380c0c20400660080c1d4000303401224030b0104200d000e2403c40d018400b80c00a4441014450703921840b0090040c01b056000e401c419121404002e0510503101501c40c40130b6040d814100b61009540d07008541d4198000c3d64050350046455480000c1000340170307809406607640c2214040383c65a01c800c8030307501c441c1149a222680301003110100c1c0500c2d051200e041c4000d40304188510444a42c0112458000091403450700380c0000042c441d0109034201403420050040341c6421418a011a80041c00142029081030544c1d80052090360a6465541280c4211600041100d019042c18900255079900842e011b40e803040544c500c0403d0006580244403424400034000c0020111000d40b0a0041c000c2c040d08a9009594820039001d205180034110001d5009800d8120720000d241c291508180c0c03000c9000740c241403d552450840445 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 580700539 1250 580699289 580699309
    0x15020a030c051c030509010f0b221112061e0a062303070801061209081c1b031a0a03050a0b04050f070e160f08070c0f060c050a1d 57
    0x146040011000c10381042c40c10070405451484000c800d0000403080707a90150455070066803800000c020b4190301d4104001141d110311801540968040c00750800322050504c0c465404289590002e00075100061021050f44404130788842c1d0000c030400c10411340b5007079524040e00c403105540e404500d40c110300082c080d11a140541c0c3c0a00011101266082d4004103600b150560300c103a02d039551341041800030708011030902c036003000202220903030380d80000240118100c480d4404c0c038240c140481141c0782d042600c00c0380a0701e150643c4d12107180c501c011640207001086051a100020450100c2281860391114454100d00403200189d00300009400001c9501032981c01c280148001e031a2031411a082c4039403025a80b4941c07092090210303030340c6900b11109003d104181581046131010030800d490146608100c0404240642d0000b1754032402070302e50007904c520445501940c0622a900c83c01100c0b60031200100140c00410620b5801d41c110303007124866841403012003480c0e06950005019520 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 580701789 1250 580700539 580700543
    0x12021501150905060307050717040503070b0a0527010e0d0b0402060c0a0c03110f091006050d0b03070b0306120f0a12030e0109052505090105060f0f0f03040c15020a 72
    0x8034280720500440c400d61441c00a09030040c400f0740c1e2401d110740020a035410103c0c0544103291020701400072582450120b40c01c1303a40240c090b2226515102d071107001c98121004400c1800380400a0035281001414224100780000070000700012081000410920240c003489000f14060b004040c00300d840390200301c0d0300c10b030704482ca0ba60b940141a20982032a205800007050301400080c040704022045007000d000e0001542c08105d410f690200300b00c241102590b10501c07568840da824801907120740000c0c0404c03401d900002c00c3c400c0ea0751002c68500103e9610100c80c10501009006003803800d0358050342000e0441005040702200003003140e4555002110042c0352942d07158040c1c11250107a000f65004c01e40ca90001c001e18111030515584403580000d2407500d8420840d450908002000782c02c10a4420141c4502001c2e828002801140c0d84082900c4000c074105000d1610000e00355002846240c100d4810a0f48a04180c40c00c00ca241d082a041401c00004200707c9038046130780000ca20040310b07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 580703039 1250 580701789 580701809
    0xe07030b0a1806051b0304020603062107090501050a12020109060f18030503090301151a0915041e21030507060603050106080102070b060a1d071103130312021501 71
    0x6100ca0303070140000e22032801c20990341d150b1030300d0b518140704856210394810203c500019008988004004031640b0048400940c000b07410710100d202410070006170008440c18a02651946010044562400005074003868220341c84000601403402d103080000d00804005d00103108001031340d40081e10500c058000c0c2400c01043c0501c1c410014481d406500d1600f140c40f400c0c0003020b48906140c0c2d1a940074190680c003d41c02c1030780c0050204598210641140d00a86030070030b42d0049400c0d80c0070b56034803140100c0d901c1803240072001c5140810710000d01c0240f600c0d079120311100350032030034400e24404143d101c0800da00803100207200e01040032061800c0c8a074903140c26991903205140100003010383e03800207400d6600c1c102d8042400001540180300b5103010303c2a02e400307681e86901308407140807903014810742c00d0421588100400203003080207400002a04000c8a0b070000050005e00d5500001d248000d071411a140070020300820610401c3c0b80c2010b88060480c5c1c0d40003000b40c44200760b0600c034401c426 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 580704289 1250 580703039 580703041
    0x2070f0605043b09060601080c0405120f06070206010302121b043206042702060c071a070c060f0801171006090504020306060d0b0402061b0d020601090c030e07030b 72
    0x20300f00103d044a07a808107544210811181e5076207001c100310046441d03441c68070441c0040751203503018140c0140300b400101c1100303145c42c1c00c05060080e020030842c00046540709036190510740d500c092150500c03402c8181e005000c15072440c01000380b5182024607010150300000444d41100034520310318084100241c40100c1c0014078000749840c014415404100d07145c41d03101c45010f121003451071240c020007040341d0038462020f140c0d000c41c190f400c640501e0041c1c071003070300d01550040c1001c20107049000c0460040e241c25075500d0161410300300070b0a146841d031030400070700801048214400d0750081c0c2182e10b0014410202401d01901c400f5041c0030f0f410301441c4220b6240041c000810030017036504801d8909000c543e540e150050b000d80010b031403c81c481e0182e070700015081d040c100b01640c0101d40000002c02c1540315a024002180c0c04800215142708180b0b0b28a80c248400308149481100c5a6004085642c5044188000ca420768006602014100300d500248054006a2801544d40281101c425 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 580705539 1250 580704289 580704329
    0x140f100e13060c090f050a050d020f010c080a0f02010c030c02060f04050f10060306110910080606070209070e0102010e0706120f1b170705030103020d06051305030c07050102070f060504 81
    0xd503000201e8020b00682c00c081d21506000e6220002004855140292505072030300ca504000c150841400f84607005112940410051724007150740e020100c8060404c46241540e54503001c09030b40c05540f0304c0c1e003c1541c0040201c02c4550911884030b104803103160400070741c080c90300025100c00002e00141d0640007100e0106003881000d0000e480c00c003070110220340e12218240d0604025046520003660518500b0041c03c24440c114402c441c811400100701c1c90803951702c680d00395113012002d80140d4200d0014441400107840d1074110a024424076181c0058140b28000020709440e1107150266041d0410b45c41003298542100032102c4042c0302c554085401d42815030001e00902d40f102101c1c181d04102e40f46d134110590840d039101443e0100c054040101e98481c0003c1ea850312081c88002e410900e49c5014002050180d48120f40100c0074040154446140e43c41d41403568000c012180c055030000d020810003581c0400042c00244001c0c244102198a882d601420500403440b40c9100f04910324200c101d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 580706789 1250 580705539 580705561
    0x7020d03140d06061101111b0c03060403080402040e010b0108160302090405010f0305070b0405101115240306010503031b0a050609010504060621080d02120a140f100e 73
    0x9660030101001d9030712000030a014101800441c803032000481d216021403083e060041c001d03000b110b907003000030501c0c0110450140c0703c506645840200d46e0b005611400156940a00c0700c28040ca010f0340d1a0304860410b4010041103e1480040b4002c42e81360031a100e0283c1d8010b4502035110016909250302030b9511030040d0042e102c0d8005450340186001e00101e001d4160a03546011f80b40198202c83e041c84d220485d901c540d2090340541a4040e03d079411042100b071107081c400852140310405e545049485c0c81c001c203008a0103862204490295510003a58515150603401c00745004800510803545860702203602d034800d00c030128004021040c0f019a43c2101040000307059540300c0120f0301035282002030103009040541c3c0071510641000000940781e1030700d24009110354100e500039042d03021141d540a5003030f03203d51400740c5100d400b481844020300440b0107451140b0078920011600d441490b40c0d03000c0d0301500074150701100b000b107801e0043e45021640490150350f51020307500286d80f24841042 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 580708039 1250 580706789 580706807
    0x703020a110a050f0c03030a080c030a06091a0102011503031b1a07050a02010b2205190c0e0306010b0403031d13050a0e0c1212031005040c180e0c07020d03 68
    0x410358071902d2081800c0160000f08143d80c010b000081d1509000c03880708040d26841408c0d1000002041107011070102d4214100542d0050b52249000880540d42e200c1c007401d5602e08111a070385009040210b0031296028000c1c1030068500070b143c001d01a00f9036030f0240c00d001c101072040507448680722040f400c00171842440c625521045050341c1312450b14010040031a070002118034010750910800c518a0300f07142501c0262107103c260b440740c4031f0640c08920b200a1000800810544040010031b40780728105200c0c0f10b4955103240ea07540014000c4105051918806030b000d07030800d11081104101080c1e004d11418602d140100e00400c25043c0000026640030150703051f000d502d807400c070520580d45800d0703010391070300070309101902d411002c101d04200c40c0c41c05000c01100f164008000c1c444003804007a00455010321035001c3c0390000354544003c5000c603030f5903260341408a06402e00d404442e8200c802c021000300030070f080d0b041c200c0c41c1c2110003054500501d28001d0081241102ca0410540111b00708 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 580709289 1250 580708039 580708067
    0x51c02040924050d031b1115040512031303120c29090705301c020601080a020f0d03020102160b0109140c0a0f140a091412060703020a 59
    0x52140c40ca28510352003030110080180040c290300c03030000080c1c3d4101824950b220035010307168180300c000802d080005081c5c0540341258401c2c10301d0703103480c0155958106103c030310621440081d1100d082030b040c09006621409607000710b5009100f0310818401049000003078aa010420302a20045c21006603058518024001c0c102900003612a200c0d02050007a000c203001c41c081c0b039a07120744900c003103140c0b200d940e4001e40d13030019654403d810220b9160880181180001c05c10401c800c0c1421644600302640e006455914002550031021002c6d8100011405003070660003900030301c00903500140d0300605285c20b844c0150007183e546005e0500030740c142c3d0040c044152600405c0701c914a0014680042406415180c500d8008640e210701a115403245c8900700150055240a011290030b1b41c204040341c50810800900c88550502d024040000e001d4440341750300d4511080742490100300ba1440c1d4074130704501408082c0b9250500d0305002a43c9504400756003030040e595400900112101c115034400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 580710539 1250 580709289 580709291
    0x31220010c0e0f09061e06042301081e0103150e030307020d030c0c030c0204110702100206061e090a050a020c03040303050408060a050c0a05030a0902041a090a0c051c020409 76
    0x2848440941044142d0301003501102c0041d0715245076401c00600580c20384110b0341000803142c0c9085241144114a00c80a50080c0300b2400c0564030340488001900e18281d1540031034200011506558100c05001e41011600e1b0310003c19038044402c0c94171400051101500b89207000b0b880e40c40c10000c07a84922110703542c68042c0daa80b0324000e003000c0d66600d11801c4800004e032410124400c038900c80c00705102e40d5645580c490000054503000c000140400401003881d40700300304501c0300140e1b80c2c0361044c504c0500680280100780780034001c00920703101c0002c80d034054001020000c01c0c20f90303404800a42c840e00803480001c0c1600d4401c0000300900818414508904c0005004000e03d81c000004c0e00c11125203401321a079a80c2c8060409050b514151508005104144940c0002ca801480955400070090400180c1e11035290000b4060720320b01203882081d05078462512010f800c0204000b680103883e40f105003c0c01c0b26180004095100d014031401005603425040d420b11009030301110024006880 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 580711789 1250 580710539 580710551
    0x160204110f070f0c1d2e0302010e0f040501030f0c0b0f070b070c0c1d09031e071a04060203010306290f0a050a08060609011502030a03050604020c100219020703122001 73
    0x280940440190b0b82c0401d801d80010091001741408400c0d1810846c05510f020500d40c40d6600544004c0068981a680500c0140690741c1a4480d481018029030241c0c499040c4820b040c2054614602c00d81c0060b1880401041034062110341e110481d181d050f4011000c40b55580c0f401e1080b02c00c071451101c01080c0c0d941019000440ca080700c04a010518021040800c081d2a55400356650303105101495998054440140780c0201c5190040d291890054030b4100038145001c1d100c000c101000c0700c042f945a5408030041c01031103454400c9440034130044101d502d540c524030311544141c840c410440c80c0b00c0c840700007c00d609503c0b4060280d0003072901500e0103000c1600c6900d810744510040b20403074042e20000c000061074001002d0391100c001d25540107145044c3c074111085016101c020b1441c0c3c2c2140d002c001080104108004903002c4920b1302d4801629a2020300148500454040c0076a00b15400b00c079080c00491260000d402510443e0306001c0a11944a41c076102c6540d4070040c200900d5107061 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 580713039 1250 580711789 580711829
    0x6050a02090a08010b030706052809140306100509070309021801060807020316120912050106090b010905031507031103070201060609150503070e0a0902160204110f070f0c 75
    0x500074140c48803040350301121083d280c00f0034508841644e5107095141d403060f0002c00001c3d000d2001400b9042a038124040c40034003441880c0e2a10209182e10030016001030800c00c04e001042c90500381c0d650040300034248078102048080c03c1c252083c00741c00e11580a900200e5040f07802035202c40440ca601030300300501e228100e51803120540c024890940400d03554000075241c244040101da010018168558103160701c680c640b00c5c088120446440f00b48865542c020a46c0710740a003030210181e204000210b07d071814200d0398016201492002070602c034141b40c080c0b001d5078020032000300780c103603034240c040c55941d420404901400809023007140c0303c40d00100303201034598190003960903107015813107000100341d4a09a000e05103000d0300314400010000e10204205500c140c1c0300c1d07c00c144000345044142a1180c3c1d002040b81c2c0004208840c08100d404240e0440c01c00d8003807400c240a2004520f4100a8020f10202707242c031502d03070018000030b099a140c03c20030000c4080ca2000d020244041e1716086150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 580714289 1250 580713039 580713041
    0xe0609040e1f1410050d11030c0901090207051c0c060b06070b0f16020a0b070f20250e060919060e06040e0601032409080a020601170706051e0706050a 66
    0x480007985100604800036688280c40c00d1284c00701c80d006045180070004684600c41503107135501d680c1e581070240061002c9030b03a640c9900c2c0d50190a1002c0c00580e1400e9914280b86070182d0422806030400c0028002c0e014148c0100b140d0100c25002240842c281050400081032132144d154002d2188100c0000c0c4264002e91101203071294824480010302031205650a03030f40c0c3d072100d41c80200800c80d07040000d441da910a4078407400c00e0026051502074040680e429480f1036140c0e0000320001d601c549030050b110803500d40310710a4840c1e40702d03c180c1c4950038107a001d0031404004003124040d000c5800850507034513007071004400d400e082c42c00800c00152110215401e080050361901e10490510854580700000491424100ca610900200c01801841e6100300003202ca0909048420396030340c0d19001050b01c250090084241660291840f5810000444120b0410071404041940640320030b118807900a011613101e50401440c002030440d071100c0c4d05070544038018008020300c1c1000d007441001807003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 580715539 1250 580714289 580714301
    0x803030403030c0801060905131d01090b0a18050604030f021c02030306090f160e0d0606080609060718060503040804050d0f03030b1005030a02090604170a0308070e0609040e1f 77
    0x100d9941c4c841c82d41d030b0314030085851050601845a001d01ea01d07001603280f100d140c0c0000c103100c3d424038a0b000d1510100080ca0308507400107000307039400d00c006002c0102a1119108030340f81628840c400900010780c41d1241561a00e00410040500541104c034080b458000c105403540442290030300f401d4110440c0009480c1d400c20b4982038010240140414100d500341e0700c45038482c003040c1c41c1c0a1056008003408850111150f004036422611000c19074020501a000340400b420f070b0031004140b2030601d104001c2c500780005110a0401455002084048001044040c1220303c64130308141c80341c4440c10a5802031146512856000e900c100700f000400a9085081181e10f00940301080005400f00c00d0199607801c459100b00091010000500070b4412503000d00b4141101a25480c00c140d101c40c0f4507540d5005041d629401c0d0343c400ea0f520b00405600207031041d072001c101d1034441608100f80d030100e503050048420f42da1290b07868280200102100700446452207040d0010a0014490148010010300b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 580716789 1250 580715539 580715561
    0x1020070503030a0207031502031504090809300c090114130c121b0905012a0308190204030c030209091c050903070509010501021f090804090e1c1e09080303040303 71
    0x1a038a000d280e2060347c01c1c401d6a10404414501d4001030300300a00b040020902010219290783c802c0c03041400c139803036600180400345d0514010752103000d404a042d60380400701101d4000e45034401030240313074180c80c2c5034151411245800b103101c98a80b01c1d01c0004800301b40b90381180e01c00c01e14010b00c8401c481e80c041415012302c11a0b800802030b0780400100e541228800c80701c06008107294150400c40c6503c110303010880c0075200c3d000c00001c1750100d030381d54000384a81c81042c1d000880316010f1110070035001800d44070858401e18110300c0e2625554035104890380612010f0320600968000403401d44080c001a0100d03003605100058030001940c4c0a0019040044810f01900c01c00c070313010420b0309000d509281038881c141c0040600400760394100c0c0c60000070542c00c8040944518503440011840005000074000300f07c808642141614642450b0080e0103040c18004952402d031480569006629500c8034066400c5112907080740441c1500c10781c145600c00c0c001032000008003c241640f6610040c6000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 580718039 1250 580716789 580716803
    0x70303020a0e030c21030f040f0e0f06090f1e0708010f06050c28140606010809011b08061801081011030106091214010c030b040b1020070503030a020703 67
    0x450490905949401a14841303410016010540314002003017403401401c03145103c01c0364540f164000c1e0b049031541259200c42090705280d0028000000c1c000ca5842d40400350002c2c0c0b0b06035192410010f0003596002d4882401c103248000403900c03640e0030340880c2100d2100c0c60544101d500348120300524400b03003441807031605260342e840403ca16212b50201d9600b080e401c0001c002c11800d8850000021510700307110b41000e141c5120700d00014034806100c0c01020340d00b4000e05064540301001504259005124500c540d142405090901c40001e0228004805a02c0c00c0e00150399124046200e01e24801c2c12101c0d14482c2c08000241040d0000700559007099040090082e02e0000c0083c5c0c91600080c01510041074007205c0034040003800780d161102c0c407805513200500301036a680b5034900b10b4802d01281000207440b501c41350818182401000d02584d0180c0d4940d8080024800003030192881d240c1d40e1030b60b81409107400e088104e0800100c005060b000f4103495846012280c0a5500c40300391008880300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 580719289 1250 580718039 580718057
    0xe0f0402031b0a03060b010207080607030e011a1e01090b16050d020a02010801142d010e10050f0c0a0204061d011a03010e04150f09030809061e0a0f02070303020a 71
    0x5860251030002c240d000946042c580a0441e0348040103480d14401c500d04600c140100000e91010400840340242da50b508c000070b004c59021010b1342900c40c002c040c0030300c002030702d9805241030700c0d15801c402030190402c80c0c51112121020040341d5483e8190f00030400070708080b918603846441400801040b511035811a404665026030036602c60700544e4002e804191840c004201008201e003403244d149800404481c400e420051a0500c00c142d40e684030000b407680890181daa0b543c10200d54100404122030411484010301401480c40c49680105492004e02090102070441c00300480b0141590007081404041e45400f520500300f6590321038007040342411800007030070620300c94000b043d4440c800c419034a1682010002d4200010103402221140c00610b2110341c0640e40b4814003a15121040c4003013031814040c103004140d8940944040860340054090110f10301130441220f0003540030054000580c0e41d4002420f000788501e01c0d41980040c00044d01004241c2d1590060904030000d445001300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 580720539 1250 580719289 580719313
    0xe190c0201150e06060a050304050115030b0105010e01021c05250b0423070b1606050106090f09020913090f060c030f0c020609060609150312070605010819080703090e0f040203 77
    0x20f44003a20256000b1030204544c809082c868001517a025000d00001300e44065003c1d41a903100380f00d503100707940d00b51280e0010310841da4418503e540c4420244000e00d164403030010282c2d20240715020513010b001d00040e51081c0311003040c58050340c0e10b01c010704141e011005030038400941c1c013085030126a401c1d01504210803654503021284001c01e8202c00501e1000d080c00c0c40c065090307001d01090a08403100350a04000200e850003540c1c0a89415611034003d246069a09000e1075119085220081d005101c20709e0345454540d0340791041c1c03016000c003244d488541d080155240c00b40c0038019103110700308030b003c185a82c0c142d00485240d00041d64104007001030034034200d840b2001a80d6001e0307903400c10710100d90549442024071303030003c8203c01405508081140000e2030004158014401c0c0d09010561900f4010070340b0800d4014681440907059030a041001900c404c400d051000f049003002061940926100e040b0f850050001621200d1140c01c0c120b2030603491280c00c0b0b904a11a01ca0300e650481 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 580721789 1250 580720539 580720559
    0x80318060f0a080a0603080a03060608060d051b04060e01060302030108071205030313020a05060706050f160c03080703020d05091f0b150c120712030507090e010e190c020115 76
    0x62500040501c40c1814621881141d43c818007510800b1156142c91010000c540800024a096015502e000840ca441c2c0071010b000c5910003442c6501c41e96140340f01d180030403800701e240e00704000215141c0588911030700000303005090740d4224000e090031031400032441d00c0c1c040d130007107040c0c0708540204c2d821b4581e50100e01804094901c0000e00c0760b04140003240c134030551180111032143c0b0003040c643c00c03141c1700c3c4041407880c0c00102d81070ba210340e00c0310184042c1c60b075260086600b100421480130f2011020300e1000c0c000c015089001010488040001440107129a040d64800500b99100f48218100312400c00da83e02c181152081541d0070140c01201c00140c144110350721600040c200c00c01c6c1001c00701e011100ca400102c000e200c140125001595014070341c4000303140041c415034038210b0240d040d00005003200c100421580610586100078081c0c42e98130100b4a04550000118840d0ba64861200401402c112030001205a003060f091524668040d0005905c04020400d1903040e1603540020395 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 580723039 1250 580721789 580721797
    0x100f03151410360504021206090c1206061507050c0414191505060a050405040c050c060114150a03140a0e0c03010204030f030c0512040f030204140906150f0a08031806 73
    0x70740828000405030f41100300d82c10585d0310030700052034801d4440510b030302c40d8100f01003150916101d0f0015624900189440003000c40003500b034600410062401401045c022aa050314a0001400115464042007030401c101d02e03c40d54080c1081c4413031000403040606048044d210140c0484225102001900c068494980844d4a814110140318540703024050540d1101c190074040180402c408079a646036030049034040d070080c0d51065507441c04224524280481a08030721a01404080a00035956581c1d10650400d0f40c0208034955030714407000700340d004000030f0824007a0110540200075210320f0992001c2d40301101102a24041901c03038041500301d115a01000385168031080300030307001c02c1c4151060743d00c0a100300100d40302440040680704494000c0e40c0310403810b03841c0210a10842c00c05000d044080c070140d4968140f1030602c4404142c80e101700611400a04d6a00c0401c1e205a59407400b00c00909100503040d2034000da200c00659403a035201000d0030190008961060000b41000c034101c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 580724289 1250 580723039 580723109
    0x102010b0904021917030c120c060604020f04080a0b090105060f09040b0403050f2209060302011b020310110d060f060203070b1021030305100f03151410 67
    0x340d6481e030300c0380e0030444480c1c8036800c2c1c01300d0710001c1c1001292101603040005e001c042007100440d2610500c94159240005141c10101c07484400d200e8508102d40c0061669048801140c01603101d00310300d41c010240703028641c03009034039100d507202072814032010f45846805199208000e0280d90b80340307400e001100341540e00e80307600001c480b00010086032800e02c4d841d401034464a07001d890540c3c1034846019903003016294003a00c00094604a152101d1030100c2d200078031542c00306000003481c64002a0030104442580d2a0302d00306200464210341d000d00c021140c0c00402d5000308490b940b450390b0b5601c9a003120000c0c640c2c0b6403a240022420a40fa25844001c5540590065180407015a03d100f040c1c00094010b6a141c1010036001c00c1c1d410301e090400c988482d82c517900780010211402d005003035035800340180c000d20301d03070b20014040d45541241c0142503a8000c4880c09111418a54110003000000380c02511005d44030f00340614800c02140360350449061514030180303580100c1d4820709490540c261 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 580725539 1250 580724289 580724299
    0x140309030702011b02040c08190606050a0e0a1a0405130207170c120307050c1e030406050f0d051003170f0403031b0f0302030406030c170606031801290102010b 70
    0x1800056200d010310312000340e10b0384c0901003000500d170301140544500d01c0d5900d0100c0c2c404420852400060b50320144400090603043c0301c0c1c00e141c00380180080c41140800410003c242d5100121921004404070080c40d4034844a54240e540002c0f508168101c4d028030703841448181e02e00190013210b402500c2c01e0036005031681001c114840c00c2035841c0d030f201030b642001900803611a11900d901c8d000c00b4501c80c0409480d4540e644032100c107181e051080081c442981000c003d0881c84011100009403000e640580c14650f40d03030ce00c81400303008680108000d00136660300304020401840aa055240c044900c1800684e13044840c070318502141d406040320012004000348000c001103440b820003080c501c48a0b9034a07201c401c000351074085074108684001d034003513440000d0400c01d4542c5880b82140c441d42619000c4030103a00150b0703900c803209002c2d280314807032403022011481070a0074102403190004504000c01118403002d201144a061604100300800314613002c1403825401806100504040109 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 580726789 1250 580725539 580725547
    0x6100f1d0601030902120307080711190e090c121c0c0305030f0c0c060703060503060702031e0c03041509031703040b070c0503090d0302070f050d08160f1205030714030903 75
    0x40110018180d445060781c6c0021100c1440c0111181440140440c900900d0003035607800881c00d000410020141800b03004801e0f00a00e4002c0a44114280084d1040680020355070703101d4120f103a01d414108030525511000340401c3c503400110010f5100b0f03403c46038645c00c400c560b41a00043d141c01d9045000580405c00c100000b032080540aa455540960b44c0c4510740e062000140e0006d00d0004101d90700404640e40344002d003c90700e0304100b225444104c0b803009500d000c01680c0101d014070b406c401c0b490f03032014004c1841d024500060003950080c16100d141c0790395445d49031500070003c15262006450031038039002c4404110740d0303200849119981041801e6115211144102d40003e0501070540b4140810310241503141c2d81c001283d405507000e036004000450415982048003116640301b40e201c2d120704050440081c0000c01901c0385e20810301c10031000e00e003c60500118249580000615500058018080e0703581c008010b103000300b0190355032650b010319100364242c141c40103032908c200c5d90340300344 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 580728039 1250 580726789 580726801
    0xc02030309100b031b0109091d0c040618020d0e0307150b09042a09050c090109050603130f0f0203070b030f06040c0e100509040501080d120c0c0f031106100f1d 70
    0x17100f2010011818944104d4036a981c1412800b181c0c03019590106070b46183c45a04081842004000c6d50344000f100c0804c40240740c814140d000d4900f5644d604407464001c0381c01a402c1d40d440e804212080422002e40c2c0d502d44e02860000f90710105080c0b5035022a1420541543c03d080aa001d07901c83e40e400a160002003010007483c80b90842c110181c5114900354144c0490000c1d424010107024460440c00750b9221114040054021083c6400440c018501032080110400f090000411590b07005000c0007044040c07030600248004140300c01035010320130040c002941c03042400045200c1c00d03c4107003140c0c03251241001c01050320b03084c40442c00090030400d1849058584504460f0030060b4508105240c004580d000c42d003034070f809038042c9045400071640f001e482c2d074001c641c0c9944400700740010001a01c03841005070a1208004c0068854011a4018020107001d0720b8030441101c00744c0d0460300700b46050405880b46214034001d5402c141c45c001e40c002901009500d03112040784482d080310340c0d00d560b90 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 580729289 1250 580728039 580728073
    0x2030a0b190308070b090c1e010e1503040209060307080a030806040c0c02030a081602180604150e0f071115070f0c0506151f08151816030f0c02030309100b03 69
    0xb0b000c1c0005801060300d14134032541c80130265502c44c0d23900300200401182100c0050010102036200500503207580d500c0c41c0b07a42031817408880d030095041700d00c0040d40c2c850001181c5800e14030340203003075070f481045400012306401098062003420222400d000048442c8000c0710800c0c000d0100941541c001d0010030000740701603000d00300300c08000c401444150941c0d00002d003c000c0ca1807a00b07080040002c107200082c10301d0301071503095507000301003944258503180081440c804010542d5a0448200012410007885507500c4034101c00394008449054080d00c9100c0c07482a403c4e1441c00100301c28600d0842d955004001072288140c02c0409400c00f6079501c003c0f90310701e0481005047d40036140500c08005080c40d122302954401e02aa9213485a141400340d041e100c94546c06024866071080d100300c1c106c164401d44442e0b219004200d1454000400b80040e405400c0107441e03150700c0741c01d00c4110a907040d800400355203d20b00d903008840c1e44c881450440004c8840c1a51510303099000070300c030041d000800c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 580730539 1250 580729289 580729291
    0x61510082203080a0b030601030f0b060102030702040218090a0c0903060b030309031f050c07202b030314010807121b0b030103031d1014070602030a0b190308070b 71
    0x103080c040300800051200400740641c6400100c000c00c3c810001e01000d401c0b54400c45600000c02d0b0010b05441d415074a4040b02000b0051004108132040000960a030b4030900540340f4680c3d001e8130541d102d0300342e0301800385407060540119014080501c006403103110f00d400381181c00d10054480405840c00d544401d40684841c540c6c0540503c4200516016510f040184c2440007000841d0101c500c4502000002954009040403203101000c0c019440811030341d011140e41d071107404c0c0d400b071019619440469009254046480344102403118400d40d011481840940e00900c02d60742040182d810004c511040300c400c1c029a899640404000d1000c418001003280040c0e00441494400c0c000c0c1c40c108010719019a00490f840348000300c0104105a005981301800c440c0c004207184c003420105010a44000040103044104a000c90400c1d10417501201110f29680e000380b425136032071a044280c54040d01e414202180100e25032001c0b00706890321442c082054035400b1444030319244040d220b000c00d0b858 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 580731789 1250 580730539 580730551
    0x8010506091f0809060117152d1e09070b0a110f07060905040c0f03200c030a14030f06090a180506010f0803040509130302030717030906151008 63
    0x550b50188070703000e900c0c414a888020000360340c0e010680c54200740031410000180e200d0000c200301d0000c907081c007500100344014081e5622006480b141c0c0c0d42c140324100580300c941041c0310002c03c103000c85e8020220744001403084002c0914041703089681d405119901c0d2045601120075005418107111000242c00200300c1a406454048581d96400c40854108010400a070007698440c2c6020001550488444401440c0860b0208804d9034400c401404243c1507085400030540d4402d4a0781c041030001500c22600041c40c85107a4444451040040c1d599014219550105074400e4070b0402070244081200c1c803800c0004a00001e50300d50409108841101501895900e038480008030f8102c0c941d00c0c89001d50500038030052005500d00b810f030a8040c50b141d000305940d40c10402c0244240d444d100f140e143c000440031503416034103946043c102d0660084280c014080941d0401d41c00100001002540c0504030800c140c50154aa900395100a54441c0c0107594204c8225008055100d0003580780b04c0d4049 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 580733039 1250 580731789 580731799
    0x14030a15171207020429040b100e1002030f0d05010810021309150e040303020706050c160209041506060c052b050903100f0c1b050703120212030c180a060801050609 72
    0x65248044511286000120710920074a02d0400c2546d07140034060064100e038251020102c4108941008004950803890b0360b005136041168002d04500c20001c075038090341d0703d0b49025100c041003841c1c0800b0300820301c541d20f118800c03a01c801517a84814402c44417092441081e4056851900c1c0300f1a01500044001550541c1207401c00268420a000441d10030703442507600503555001d42c90110b080b07807009400301400384801d104d441e00607822690b61142281d01201c031680603a54600d007007110845002d40101c0d01c2d80c1041c80c0040c103242c014955184051007079082e079004644050030306801c00700103601d80006c0980800054480e134007a90051109000c050305444201c6800d030051025a1100d8005a20f91035070340c0040d84d000d60340944840440c13409049001102205521181e6840081d8003024040307101c2d8900c0b00003014003c0158109500910844a03280d14181e20910013581203204440e01900c9000602c000500d82500d0b0384e8180c48050f00c41c4100c990900091100350b0308040d00300781d042 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 580734289 1250 580733039 580733051
    0x90326041b0807060824060405010c111f0f1121090301060312031a0904062301080c2b030f0c0204020d02071a010b0901030c14030a151712070204 64
    0x2c81d1041c44018054190b50301d89130352509195004200441031a01910202039420540c000e141c0d648404440031940c00f40303841c01d40b480e4039040c042c00c2080e050401d15484507144450021042800790b120301a5081d98941035403e0312415000d440c1c442c40c0ea14240e415400405140c2002e140c2c00c043e01c17050142d00001e00b810201041c1c0400e0031605582c009403841407010700c42c03100320b660502454042c100001c904000300c07121100440c1c2c840030302600c0101650f07103555840ca00f0072562182e004224200c4002103999580da00c0000b0380714001449424001c0700d25100e0100010300d243c00091907001c1d0f00c403c500101a4a45045a129840d1070649042040102064000d60380d140050110741816020040c0c0c0e0380500d00e0f182c1e10140b00c0000310081c815910004000b07401c001003e9422511080c200810314079001681203401c011015803180d2701e400044180900058150b203c07242906510341240704194480d010040c400040d080c0340c49065109141c16001104500c02810030303240302810110305 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 580735539 1250 580734289 580734299
    0xd0e0d0f020d120c09030206070b0105040b01030b0a26100f140105030d0f090f06350103080d090c030b040203160b040b070c0b03092b052218090326041b 67
    0x2356010840c1914108980b070f00500040c5490b01c00d1104031002424204502d000c0000880d0081e0064843d0040c1900350300c041545107401d0b01c01c0030103040d003a0002d5994240c505200100200180380030401c2c42d074070b4140382c80a801d00203100d080c1070340c02c024010108969200b004954894950010340f040003001c90000503401040301c0ca1201403c0700e0f0700c0e041851203280c103820000110001081c800300c2107525040c4040030500002c01d06403074205035100d660f40342c20789810024000c40c19001b49a0038840300e00006004203600490b0095100720b09070766444070206041c4912290a01503200079610400082000404010040c81c116100e440d00c902442e80d200b03050407154004844e1803a842d0807400400c0c840034189542e00c541039404200fa240a9148a1002032050052400840b0b41e040705c1c0c55050a500c00414100b4010f100201d14018000e1154a81401030048114114041009aa4110071000c41301895425908c02c80c0c180f0004ad5072103407280c03141445a61032800d4480149180428 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 580736789 1250 580735539 580735549
    0xa0e060f0603100503060903031b0f0909040b071701030803070e01110d020a14070803090d03020c0301090606091401030807060207210903030906030c02070e0c0d0e0d0f020d120c090302 81
    0x4410064580d0f20308141d8642030505092610051164072107400170020440d00701d01c0c1d4804801002d0070540300684403001d00c5100740c0c281c41541d4500c2c1d40700d80800108000c01040c0d1017101d1142c2c006660b441e40350140320b40b01c1d402a40c82808024030048091000405c0d07148031b10202d0400c4e000504d065452031010340700060a040c510032400e401078101511040034492031703c09002604a2030001400c8140c07501c01c10b60348a0040b014014803841900c1d503004c0516100300301c1c419103504028001c0140702100d00d4030701c1c0140200c6c03150328282400e200b110301901c10b54031003030340c1241d07040450f0614040c443e030b490f80300952050208a44e04030440c11501240c0340300c6001c0780b0140302d00d516040051811401c01910644050380104201400c004c40280c02c5540030075440100d03144004c0c0c0c0742064490442d0441d035030007a190b16500b0203152a11b86584088001405020364069440b02844084621401c9032240070740082440804c0520710721843c00c0c08030b644030700354500031454840015622580011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 580738039 1250 580736789 580736791
    0x150d020d020406031107050d0f05070605070801180c0903230d120605040b0303120a0b031b0f0103140c09030102120f060a08032b090f03120605040b0a0e060f0603 71
    0x159015404075043c080d03242c043c071410b1640d032904202d5900b04000359940581e200a0780d402c513410407010205856000c1e0242050341c002e0359200106000d9442e209000410b2490240b003041e0342c120324094241d0090003940b00740d11010b031040da40e010351030781103860b2048001d10101c1d94009081c1011074245c0410800e100c06a01d404840d96a5420150001c0c40003082e50311a40282e482180b91110003c2a5500081111503851540d020103c05070b4401c08464001c002d5040d8150301800b40020100d58101ea404540741c42c40022142409164071080044044411500740901e4140000c0c0c081000d00400750081d01c150b0780001c0015182564580c004400d1150503140012542001300074403202c1c0c945a05c0d0000a412090000c3d070502204001039142450807464956010a4206011100c12156008a400581c124401e5085c214462a004110980381520640514078000000c519882c150082c8074500788001d0540700f00342d05101e00c0000661002d40074641c4506542014140c036100c080240d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 580739289 1250 580738039 580738057
    0x6200304080a0c0f1a04061d091003291308040b0a0915020a0803060f031908030f091209130f0911120328050d020f0405010e1e150d02 59
    0xe08001480c1980b5480407480c00d40040d807061211080c50034410058605441c1190954034001c0050b19404d0b0b10b821000a4001d070030380d00800000200600d001818ad0100222441408142d00f041d1150040c01d642d10400880190f061140c10b000c20082c0707440c0d800d09001c0c540603020132403809030394140d91012070380300350128404103a4400c0b0820050680710001c5042c4e0718940045d101c00d2246a48a11071403000a008510606c0e034141c02c00301a48040003061180c08040b414203020014908080003176130001c548a1035548010030004901d5400414950513403160058450f0400d00c1300000c011603908440e02203460a6902e0544442e410490301079071071700324003444003c0f004191040500805061400b04180d4541c402c02a9094481c4040c1d0410f00c184031802040c0485802040304840f18841c1c0310b02c20b016503001260100982901c20700800c102c0c2c50980768007840041c580305212000303000700340c60b20540710602d075491410305107580000040c182c1c84007101c0c03030100c210710580d0403030b080030f042 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 580740539 1250 580739289 580739303
    0x90603030306060c020d0212010b0301020304050a211205180d1107120309090b06070512120f0403080a0506010e04060602060f130510090501090b04111906200304080a 73
    0x10410516805100755409006240340c081c10f240d849801045039402a07810080c0a5151464070403185003080d4480008e001004000399564109070900302d50342e9002a038266030b8003100d2040c085020890f00032000c1c0703190f159202c0c90180280b561014005000c000d20348210071100303000301c480d90402800400706600d1141c4030b07061170210b03c0401a1500280303801504c0d501d00c065090704007298000280744102c030345880c0c01080c1514075201040c041d014001000309980300300101181ca98007164041e00c1920070922034030010b50380711028001e141c00280c8002d004610032202081c440b0406822450b446801030500d103500b0008400440c045600c0f42d804200160804024800d800e0034550b049508905204c0101004034075644401d9150060504e0071103d141e41c5070a5581009000c0d00505944e03604000c4641c101d00c0c05062031032180303c8484215100c0e504603040200c0c5106042c12000595030385544081c510814a0b1101d03502811041d001003a600c000d00000aa5400401c80340c801d481c8140d02d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 580741789 1250 580740539 580740551
    0xe0c071a0417030705090607080405221a0f010507030e060d060608061509010c0c1a030a14090c01110705030106092019120207020901060e0f0102160b1b0709 69
    0x2881c0b02070541d9001a0b151801e0308009000500b036000046d12803026080b124955911140c4c503041015104950180f03800c013030000361f000700c442580d00c500001ca581d00e010520403004002440ca10301d2800441c0c07254001f414003c040f089e54819800303002c000748071f410413001000c072a0001401030b40203980c800380001e884040038842d0541c0400c0e007580000068444018070b03400e200403101ca601425882c3c40c104141100c2000a107e41440311000424200400c400700d200301d18900045944100e907111350090a1801e06542010f642c80e002d40b2401295010349030520303640b001180c080a80b030340448882e1203100d401044658007032007108002d021003400003990380d89c00b140000b070312000c0c015207040d009828402e4540502003048003180100380362030101e04c40084022110003d000b080f80c0030b900100c0e1b0343d0000c030b409074009a4001101000311092440b461300e86004aa4030072042165014415000008010305a0410058125030480c10b210840c5901011600341c42c050b0240c2c01800030350b403a05 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 580743039 1250 580741789 580741793
    0xc0a08011508010b0907081009050114100e0a0e07090302040e01020702090c040b03070f050c010c2102070c0e0421030b01080c03010b181c080d0605060301030b010e0c071a04 76
    0x302407100030182103001340840020303a00020042c00000302464180444800014403c002c0c145a84c0060860341d0f2040045584440440714080c0910710748602841c0000c040207102805081d00c1d4215000040240300407030300f8280406107141019060f10706106031f8010210040c0c3c0d4034018400c0c070040d104001038841844cc01089480c0101510114082e00104001e11101c2c603482c00b182d601082030b0074101c800c6020f070203040340c15103c1c2c00401000c5500e403030088404c0c160b002ca4420110310320103048010610740606000c0c01c910a0f82c0c1c1c014030312104410204003008a00101c6503002d401405c4041103480d00303401d1075150108000c10200001d40d580d054015035a0465182504401d0605401382150b040480440d07251184a40c00c65940d00448042011650380701c0322101040841051440382c4d01c010310300512f254110b0052098000d0034024041001d00306901628100c07030300f00080c20b40603480c20380d0150360890080c01000c42e181c42002104003045404c607801000010142d400c0100303103032034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 580744289 1250 580743039 580743071
    0x1060b0d0f0b0411070605070c02060708120601081306051f0806010f1e050918030d02090901090c1b060207052b110d110a0b0c0a020f030301060903140c0a0801 70
    0x201c2e08080c42689001d80d0a8a1061540280c81e07400ea485040000c036621507000c00d80d4440b4050a0080d0302c0300c00002c0c0c0c0000c00080101411004401008540d07158482100543c1c442c0d00071108615039109444058000c9041500800d4020000105400704004842c00210f016009038001e0b504540c13040c40104032548002d02c0700802482004070610f0385421031503102c107940e180d620481e0710071489440030580048800c5810141e014009044907520a000d0a00300043e400c4841550310071a6070307900000341100380e4040e04100c540c40d50340d40b505107440d8844401c080c0348400c0094856503404d004480020b0303c200141d407619854564094404040b485000b10030b030034598509000c000d80411020240300c0001010300c10b0301080e040c18240311220385421490840b0220000e02050681428004445050802024008200d0b420345245101420700c195692100380b06500014084940405c04901004000400c0484c2c3c80180c82c221500480040d003c449160020a5240d5440742041d10b08164 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 580745539 1250 580744289 580744301
    0x70807090204030812191b110601081005070221040311010c0c030206090103020903013201032f100206011707080c0d05010b030601060507050105010e090a120201060b0d0f 75
    0x20440041d0300d090705541e1000007501950f0160012950ba0a001c2005036070701e5500000c0f02e5815803410402d4408200700d4042011071f41000130045421540c4031416003401040c03450688442e00e005015140b2041c40308001070500402400450080290700e401840c246041240c0030782c5c0c102c09203902c0724294101350b05549007451000381400501e00074100080c0b00a1003003421250101d40064448541a0058020703102d00b40c01c0580c95440c0030328204035010030111041c10300000c0c080305540c0710400d4090000401003800060910024052000000000ca0362902808404000390b01000215070011514051200c4c403100096080f1100512580300d000da130010060900500400c0c110345401c2880740c5412810071001e010b000401d8101042c81800d42000f0607001010b000c4030900c0d27944410043c00c642109400711502d500709000001c0b154020301d2591701482d800006084480e40303d58854121080f102d815105654071100d0026400b105c0030060100e0700d241980200b8618050f4600b4811150 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 580746789 1250 580745539 580745549
    0x100903021002031501031e110403050c0d0b010e0709030f1101020607090506040902071103030703110d0905010905010809070b0c0d120606020d0804050a0f0f1a060102062406040602070807 82
    0x202c10300422458014080d00208108002c0c28000340009030401641101460010b96254450400d10942100308490009000300d1307020b1030941e04014200e4007000703880032020102411103000300c00188140804140d83d20b8000249003401c076061541c07545c95210729103074103000380c981c02401d1803c0d06081d41c051201e0390740422123242c0100080d05003c006800d50156006101035950702045500800910105005070710100908503502c0c0e199600c0c00030700c851800040d1110318000c0326220340100e400345c61840c003a102c3c1611081e000e1800c100044840380c0000b0a002a9440b601c3c50000b4507885000c0200515029080902400301c200c60014120702c40d401d101841c2146403007410405a9401b0464440c1c031452860440301e0368540b41091031a0001000001c0e100360458044401002810000380301c03040d1055144401a4903265450300c1352120880300310780541c2200d07001030b6804d40440405004203407640e43c801104130f01070001c205140c01c15003148000da4070207881404125400c004000c0200303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 580748039 1250 580746789 580746791
    0x1906140711100b0a0b040e010f091e0c02010902040c0e01140304050d030c020f0303010f0603051e0406320109050912040303050f04080d0306030b0928141009030210 72
    0x25802001d0302c0e92010701071201c44489544280300c1c44159203003035031040288183c01025848907280c0d8650340d94040c081c41000e07a0078080c1500080d902c1c034280920000c070100804804407581c9400d03010700142c81c000464504555031107038290700590700c501c18154140107903566001042d030000005040b0800b00443c80f03210715018002c020000c1c0002506250044e034901d4081060b9201e00e0007a4034200801181a00600000c400890090f000c00080310840c3d07041e9405001a4403203039101d0f6042e5000c11041e00b8400c84040024002c01c809400000307107a4041d5801d10903c201c44081c50100030343c1340301b100404020344801002a442980542d030381000302d5070090010312614a140c030880d4445ca00c0b006003800004504c2116448502050724018186031098505849003003000400405503400222812039686010499100340040c40143d4141c60100ca4900102d500c44039036120f032240042103d4404850540c48070342c07141440b101244d0700984e072011580507020702c4d02070b0511100d066414440d03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 580749289 1250 580748039 580748057
    0x8130b15120c1e0604030206030403120f090515040305041205150f091e0a080c1f1505190312110c030a020d1b081e01061d06090919061407 61
    0xc0c3e0345824421402c03414034283c0d04260300c070410204a03540915440070358085400300c200030505401180b07902806241000803c414401d603d0106d04680803c00c0c050b01e240c0c42450802102803082610b1900315020742801c90600e036030354005c10301c405d5450300708403102e030403400b200035017400d00b101001e400c8645402260380074a0480112651452045505219650138901000304844144080162203410407401c0f5942c901603a0040d90726008030801da03460a101c0088000106413500c2035038050801a80c0c5880c0c2e041c0381404000100302d0148042c0803101c070104000000544404010603e5a11911003080440d01c01d80c40e5070808006e0040303540260401c0c600c0d5001a501d0007e503003840e5500450121784010300364095000325205804c6042c90388105000e03c007540d02d00d034400f280c4403202d40009210094640e42c92008c0a2170380c54841e0342c00d00312080800c80d01c3ca0301049142e440307500b00d401c42c0c8043c02c592051078102510524143c5140d40d03030b003504400481c0720002c9140d200181d400c08145c9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 580750539 1250 580749289 580749313
    0x2041508010b150a0813060f0c0f03090b0711010f020c0a1b05010e090a0207050109050309130b09060d080705060f1905061807031d03030703060e1608130b1512 70
    0x154416803a161303042012000c0040c1c00068544c11002035a5005042002001c0344010204010883d02003208040b480a0b9454610544079002d200c0c006944042c0d10203403515000d0b0103807846a0341a00e124015501c411108850f40007601c09400c1c2100080020820b1800c1820288401104007000a902c2000320f4018406660405420222100103643c1101c05681d030f402c0c0c20f8001c3c02890f600420039420144e14805024001001e0034020740d0444900e000242c0140442c41116100c0d94166046100c1074001042d40c50081c00800c29103004003156850f142140d6509401e0410440d103920900c0080424000c0380e14403000b01d4485d070302c6150010003181c10080c1c001600080103601c2041411844000100558031980081c1c11040d40c21420200d0341c00d00c100260b4032a04100d0300c101c002441c0440000e40048103445c030354041d000700c1840c84e44a410b401c80481d0800c00040404c008008031115640c009600c0c0a881031007601d01e82c0408409814000803c05004814800c020143e0300c06030709221 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 580751789 1250 580750539 580750579
    0xb0a0b0309071a041d1314010c1101062304020f0d05011d0919020307050d03030203060906030106150c05190f02010f0503060f130f0513030201060803071205031302041508010b 77
    0x142c60700d0200841c5c41680d46205d070461480082c40c00a0010440d81824001300f841500644102e0081e901d80502d103003c07455440d0708a428500c43c02d401600c0604a91914440906498403074070005040580381c14000d460321002580400d450081a13552a00100204c543c0885d400c0c02c46030880004041600f0f003500c00560f2440c1440000392503d0304200d240c0c04540c0c0030801900101005482c0885400d05801e026000b90012038079680038004c12400a005440d040c4900c405031580c40750030144c140700040c004c0715031080f180812661841400152481c2d08038028075070610506c10100c5c00c0f00c48030148001021064450324680501000703006000e40d507540d500c1c10303646ca940281c807004107540da030151903800f810748141300e07134038141c41c0005128282d2108041500024001e030007e1080682c3d030140f4550703034440c09401601408000103185a894403c1d40110f40100c108110450212aa60005421039071540015003500c1c02e850010800e40c0303000c0c09581c1090004450480991102030581c074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 580753039 1250 580751789 580751819
    0xf0e030a082e2d0b16060c0221340605010e06130e060a150b0307080412050717090111070e0117010510051909020c010906050a1e0b0a0b0309071a04 65
    0x260013041c0421124a216008a504840690050341c144041c0325010000394440288100c2d450f5071407007240c0481c0090003550112141010507d075480c0705105403440b60712864948500c2d128900e0761000940c404a42e10f409094040d10f41c014403100141000010001055441c120858915041c041c0464008102103401a4440281d0034040f6a080c2045c151210640154105001d4503a02005002c045640251241e110714804d04007980000f002c840c090f01d40e4000c0d02d20060010149152614007800c0110103016201410304060f03004849400720340d418052150031943c03820010000402003118600440620101954020072003800c118945d0b42001c0002c0c05440d000310510580801c02100c94600b840007800f9285045440c2d2240302001130103400841d030140c03907440c2008045220b0428906c90104182c1000c071101c81c403014107400c039002400b1902c0a05500061060300024003040c0000114401c10341c0c1d0003e40703421801c0100d40f480e0850301c3c42c07001610746002c1c031050201c842c2c04071fa00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 580754289 1250 580753039 580753049
    0x203060111011b11160b04050f030a080f16060c020f10110714031603090603050c0405180709080a030504030b09060c040b090a030c180f0e030a082e2d 66
    0x1c1964004c0a02840d450250307802000e11805c1e071460300020300085404003600a95104550000c0380c100050101aa82d072403a150242c940301040007100c0b5041d608900401c0b00384036980484059030455141c05c0c0071604d41030400300158000891446a415040c040995080e9160f0410007914440307912035605406803000c0100000c50143c200f111000080051f00c8902c0110111800400000d19008143c800c8500c105c4021904010100c1d580351140010755040d1840580b80c041c203510f02450b2078480c00405840d0100f030100c003410100321000240101e130080c80c0641c44165440c0d1851501c0302290030000d00a9500d80c01210512480c84041030840b4111460002026140c2c01c8800018144071002d6000910340f85040780000f030200d0441480d0380d90450003120070400c4c0768043c0480815030740c1d076501c034007000d8104004a11004d40203150030307a0410700000b9210400b0180c500c019070755440f03603500c54108040803581000744e109030085160003042e9141401800c20810100d12821901034012 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 580755395 1106 580754289 580754297
    0x9040c0303021522111905131b050c1f050a05310804120f021c050309040c0203160b1b07050c0904030507060e010203060111011b 57
    0x10b03803072080d001e103112a0784c540c1004000c901c491610200840f14540740c2003c44486450f14140119501070f0440f12804550400c0c080001800043d000340e03000c54144030400d00c0c0307041d505902c6003c0c203d0509045880700441481541003030f440c18525903101c1501071807900382081c1a00170b68003c0e51002010810ba4603920500c0140150140710366243d5006111824603072a5400354481d051402003203460b0409444403170362004401d5000e8151560350140e100401585044c00c4c0259038698161151610300e16203903a2291a40a072080081c41a950342621105a0b4020300464143c0d81c080e5000035810b099a00d8404400c1e001a1a030482c030b40040d24010251501000483c1c1b103054004000313010400c1c0f040204000b03450001c004504120702440844005505405202e402444290000da100c0c40d0410005042250128420610b0303810302910509131907a5200403820368180340b80c = true := by decide +kernel

theorem cover : BRFrame.Cov 580575539 580755395 := by
  have h0 := BRFrame.cov_init 580575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 580575539 ≤ n) (h2 : n < 580755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
