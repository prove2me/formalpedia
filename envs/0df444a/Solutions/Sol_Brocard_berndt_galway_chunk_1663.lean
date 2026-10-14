-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1663
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:06:52.539851+00:00
-- url     : https://prove2.me/submissions/397c21fe-9522-421e-b32d-a4c984b2a0c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 298920863 ≤ n < 299100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 298922113 1250 298920863 298920889
    0x6050a03030503041103031908010e060102070f09050912160506011a0706020f0f030103030246061b030b1503060f0d151b020f0c03100e12040b070c0f05 67
    0x17210303461078021055a014022a1001e10300d4851640001c080e01000510008090080000012805001c102698000140350b41100c030011001d20b8407609110610020b001c000e01038581c18030810003810031501c010805405c2d1020840e65810101405007032440c9000c1043e40502810341f41b0b003c1060b1500c1c0814100c9249a40005003d64ac030705511013820203601c100c080071641d0030703030210010042582c04244800c21030455030034440c044032807212882400c0c940c3c001780d1002d90983d001806403000d110002030301b1640269000074400b00d0081c03e400003580340800850010b40e95151000381c6240080361800b12003841b51525080d032a0034004102621500c030800f6209030132400380c102c1044650504540110740c01c44052110180d003c404189402440d0444030240c0141c94480c41062000601035203175941c0200107210000380e00c03000c10b0040c112b12041d03c00303d0003402540304506190500a200134500d00500503a030740403608008903441ba503070308050030403944014100819a41d406c1c4030680d03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 298923363 1250 298922113 298922123
    0x6102a053a17130c060302030601020d0e1807081b09060f03101a070317071e090305010518010b0a0b040506030a0603060c0c03021e12030a110313030306050a0303050304 74
    0x8850500142d90180005812400070740c0d88500300302c100c0e0b80f4505030b10000751251450000c060b4482c80194141d000860380980180e100c8440341154902c14044610079090240c40301e042c812401004841d502001c0300c40001207425001407101c4849500441d1800c1d500350249181800305a00028266100d0490003509a16011010406d40400106000001c040304003900e503018018510406883e0007111082d404240b50b1400312050f40301c0000e1091180000b43e6942011861088188460302d40584e11801002240100880014000d215640c02802d40c5c611080e41c0c11100300c030940c252000c00305800c4c01100c03010f40400000740e54400b600c0984001300d1b0519140d40d83e0702c00c04e8008100c02e500151450f410000d41004c1540c1040f2880306030b80c001d81c287c41c01c502000300c0f40e1500014200700200280e000c4088a03001c208210080c541165010358046000c04018070807020582080d950381c004a000c03904540304054040c440d00001b85429070b41001c0f503038a552006801404002e10280c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 298924613 1250 298923363 298923463
    0x6040b040b0a0e0d060501080d09050f010804050f0d0c02091003200607060603060b010908010c09061b0b100801050f010e0402010507020a05060a0908190b06102a05 72
    0x2c6201d000b260184140070000c0d00c0d0a56860050138044043c000a102e2034940c0d008072180300b03010904c01d0200b40b081c2c85014120655903001600119003112000b4015220b90140c41d0803500f003010184041084240704d41e4806d00c1d411803900411030200d40c013078102e80f80145074680030000100d200c4041d006000144e83e4142c041101d20002c240d41d88203011000305800e10300741c0040b003045a290f100c4e1800b48400e80e00c0415070f0340c49440d101d00300c81c814625580403d20240d002c001551040004481c0c21940703600300500543e60b580c54221000d0b003500c42c00c1000c0c05200042c403003c002440348540c80070410300080b890f540740c0b400070040c5100203040641080400a0401c09548800c900366004010242059595600040004051664900035048680641c040d1446e210381c4414940c80350719004107404046403034001c10810110120a0a1403c0c04036001c01004240660701d50b011241d072411412000070f1b5618980603003418210040740001b00b00c1a24030400c074100c0304c01940d002407200e5480b21 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 298925863 1250 298924613 298924627
    0x10c030c060203010f1403160b0a050f040b0304150209011b2105031909080901081f08010902010908010c020d030c020106170a060c0203070317070912030c0b0606040b040b 75
    0x2146590400c501602070390000000154007070215002c003044407403070541e58a10319150390415403112011120f400c4c40911880c010320020342524002c000d00c1415080c0301d40350840c2254000c0664025910a40307500d28040301b00000d012407058070384da068030303c03500c114984140e0700c002130020b10304104a41c202c0300507501e800c001c015020b810316207042021407606c18400c0c1060001869503100300c1d012441c000c0319040007030300810140106100380e0303440710020341085a14801199041801801c1d1000d4200302d200030290007180683d00f00141003280000f10340b1140900000d0010689a0b100700303e1685413010001c2200d41c08220000c0f6545140f50103d2920030030141203001d4002604003640c03031400c031141c02d0714015000a20645640c4292400e0102d00c606d400140d03140d02400c00080e01041d80b0109e5581c0580c502401c080d070010280c00c00000050700c910703c0841c090381022084000c00c450349103d40910210700310460740207600b140c4103441d003801c0c02d00401c0103029910904460440120f214 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 298927113 1250 298925863 298925867
    0x190c031101030906020309010b100f08060f03010b090109060311060307021b0f04060602071d06090c09041b180f0503031218030f1b060601090e090a062d0203060f010c03 74
    0x401c031100d13040381d030542d22410203c80e0076000300210165a445a82e10717401c0320f4103582c080c00c200514400030752600760440d5075070380138014240251485c1507819542c4500002203603507030010480c060038010307000081517400c501d40655000c5007400d00b14820b1500f8000c02c40b9496000802000c0300e240f21140702c0505800001107240c0c0c502260100c3c1c0c0c0703e82411804200c031a400032f41c08080303440d00b40c1c01d1000741c41603080d034001c0110150b9104e5040000c0b00300060030b010b100070080c0940b076409400011040722440c2c000350b40d0401d031000800000e07414001665402810341280740034180c00b0300d400702c00c145410300007aa03c0c0b00d244d21106c01385c91a0702c0040c80c2e95011208002105200c5d03820381365140c15001421446500009103d2240014209010f031480c2000500e40e1203400103854213800d150504010103180d45d40101200c410b40f26407002800091414000c0045c100c00c00004209910040f15440a0b00e0800784074030791a440c414800c1103c0b6580d81000c060b0000e100382000d407007040d4a4201 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 298928363 1250 298927113 298927121
    0x8070c03050303072f0705090403120c030c1808060a0908250b0121020607050309030f010e0c0427020315160e0603270a2003190c03110103 61
    0x1034120702000c010400782641040002c02d131010301d80f85e0380c1c8030209001d501941550440c00130a000c0c1e4072000d0240624181381c900687c210703020707040644058000750446029a00c03c40442c400198940130b1102110741c100c09545c5503040400740105090341405011661040001c0110010b6620340d0940010b001c0080d080315000690700403602c1c15151140c0501d0fa5540c2e07078040072140403c0403000020000911151100d030124580e901d00086205074080102c103400114060761607000030000f940341a0303010041c1c1c42140040c0c8001090540c1d41401050401803005005800f4909003141d030811269081034081c0301103c80d5401064010711070002c240b8000400c4548103840d14000306110b01c1c450301001e110300258041d030f100b00000d200c202c103001c01804180d0b07000781449042d840714114140e8200d40321101c00d9014086401118071905c07107200039849664000c1a800703055076025130604083c44095000d1700101110b0700d2a084541e0b44480042c4107100240c50840d03021312181c070680c8030b500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 298929613 1250 298928363 298928369
    0x3030b0a08060921092805030703150b06121006080c1c1d060f09010c14030a09021210022a071701091403090406060e10080603070e0403082202090408070c 68
    0x2d210480406684925014403c261640c0e41d00ba1b1800c1e00091600c0c0016280c01682d5004241e983c0343d0b40012101c0014114185030103174088800d1098850381c86814040c984200e030001820803d0030301d404000341c54090050200061003004100c10059050a0038915016841d404800910800c9000072980305000c1c0001c24900c41c095401403100050030480c07400d0052030154020080516115015500c200e054800e0f0003099005000055200303040c4d074054084240040c01c548000750140006504042e0312050610f99680c1c04240365007000f101c200240e00b0b114404c803401c0610580000c1059441c032083c070171807902020404924107064000e40100540c55800540a00c0980c50b000303034191207420400740345e0300030381c038140740001d40358416000740c1414500a4031440d14000c00c1c8800f05c2d83c0f65001461030380c05104140000690910b800201c034407641c001d558000d8941442c1200d44034040c012501400c5004900b803400c00903a5075810f040d0740040d4070071842da0355501645048030b42240158 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 298930863 1250 298929613 298929619
    0x402040902040611121201050f041103090d09330905040f2708040b090102030403050a050c030706020d1d0d0f060203090c190504022503030b0a0806092109 68
    0x1c180040c0c816003180c0100130310505401982d11181d00064584124003e0300d40140a001c2500010002d9040c418000e030300054010708045070390018482d01100070791007598042c4113503001c4410040410b600c101050007910785d10010034490340409900c218001c156044000000c42803502140701d2034001c8000ca001001e02070024031064815003a220002c00950307828699020306285017000041d03244002004035a1700415a0382800d042014840241e00103111160540c0301c1000040007103101042a003e481e031041d07001301501c0600340145420b000542e032000d0705550201030030b40c80564110040304040040441304003c00b800341d00004025181809010300240c030501504424400c90f500190320904040c0220388a02c0096410310089120160580c2664400c0074400c0c4150b02c0c050300140070481c1204150200031824040b90fa503450800d10045010075030341c002402d00c5050410a05000300203200c0030308810312300303442c14a858407681041e1869480e0b000003070402e8003c101050702c65000300a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 298932113 1250 298930863 298930867
    0xb0a061413030c030b0c0a230c06010e04170c10020703031d1605010c020d080306240307080109020a05121012030302040e0105042f12190b06030114010c020402040902 73
    0x82e0400310f444042600081e500140e002000030204005a0f0880d1182c0041c0c0e510070b014000850507400304003a00340d009081c1c2c0740c3c0030071002c0c0c0c0c07801c1c08004444c0a0500f0651214580c10306140544828080250426181909000106522002140b0382e40d40c0b81e1044805651503402d460b0480003040d030f2840500302407001c203e030f0301a07203900003035410105240e90141c0580c0d9629140195030615055200030740c8240001d10078400503e400024640150b8098035025103100785403142d1405d00c1c40c0c024482000f0b0008030411210320361048605005140c000001c42c40c0c8684040001d0082c4501c12140c4503403035a820128405040608400e402404518000c020600c018940140a0b51141c030a440c440109000003003524545445203050303030300b186c040303483c001d4400c0d030b40c1c540901ca01d084642c0d0070390f030040c0145400c0c0418040e6151041884404810545040380300b544115802a5921809190240010701c00300c42d107a020600030b51024200107007241d00c2480003c010780300e140c01c180860384c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 298933363 1250 298932113 298932119
    0x101a0a030b0a0606180b0d060b0a050706060b03070512070e0301020c01020403061506051918121505040b1302041d060601110102070507090b06130b09040e010b0a061413 74
    0x1500014001c42e502da4050164030f40e01d50048a144d20700c9401044900141001080009070030b000a100040c1c000c0800b00f1b29a40e100030f031500942100703003408041540000d40b0b0007080741500c540301c0a0401c4000043c01d40c1802c1400a1240c060325501e12040000340010070401d900485045414450041c0295603c030910410305000c2e40161000b182d0442c10314005614150b00f403c0c6c1c80054130556a80c00341000d00b00aa011910f05d00c203070004007446403011305d04603680882c05549029141c000085403045c051031822241c08805448401403082c5084203000028480c9040c440d0001012801600032868074000103009000001c04002080f42c42e0028407041d1101103056072160009132115003000d4020314000d4240c0c82043c80c0100190000f4509012420803a4441002400040e1940d0b042c082d0590300b01c03c00301156004103c0f101008540955541303400d01854161251960080c070503210014040740090b1760a000c0c11082c4101010041c02c4042d185043c0d845e40070f0f40860507858140c1d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 298934613 1250 298933363 298933373
    0xa050607030f0b03060c03040803040c030f05060403080c090114030a060f0e15030609150c09040207110306010915030b070e090a020c011b08161e030510120302101a0a03 74
    0xc00c0348541050f080c0242402589408102207110342d41c030b1640d40340380d0303501d03a07a94080d0369000420842c1e00c5080703e540440814105a0100400d0748600c0042c0802d017001c0c103014140c5030b030040c80059035000400c800c90059a011080380140c00c03c0b00703546070b01ca80b1110f134071101030700d1a82c101000c00c2380e12500c0000d00c0c100074001a070203110381c107291040d440601410b0545420007144ea61003a07a10925890410300081014035520404400c100c600307001060380050281d82c0419400c4c0c1d03c40c070003400d8a03242c43c5070030704c0700f103004102c02c1c50704011280d40c1c224070400c07089451002420408038800002d40341400b400d607101400c8001000340f001da1410600c40740c025004000d89000c00d41c42d141013805101207402181e2072004c459101c0400755690307111071480117015850034008000d000c8905c44880801e82d20081401402d42d140481e42c0e14150038a480700c483ea81e8030181c0c5c40c90310140090080b075004911043d29244903080820403581d402005a00080c4401226800040940000040c40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 298935863 1250 298934613 298934621
    0x1401051f080a120516060902090702070b18210a06061401170c0712180b041a0c01140702011a030304060f12090b07081801050403080c0a2303010e07020f190201020a05060703 76
    0x144212503100880e03d0300035003240d8410b0b5034002e1420013a003c000d4103580c008073b10318028007800014201d031440d100c1d00940c0c00402c5102d80c0d80b480164449000d030020081240142009015103030308a01c220300c144030008115021804540039000c4819000c0b807010421202110b4243d50868007030404546007401c004d0820042c4c1245070b50043c2e0031440822a5054202101c00310358401044020b0315110300c001c9800756001d010081000c0d0340c1d0f0702804420382c0301e0050180c402d25058000091220440342c8500101c0c0c0e00e0a0690f201e50030801040c041c00e0b400111151b100042458900a90810152103000402001101520800d8104208002140d10050003440385280c440c0c030080020035041810709072507040d42d00401140f815400074001c04000c0d4054410350a141c9001c550300c5150020980a0402e58999412071000c000014481d02c5070030310700190071102900c000c00103100d460b0030240e1990a2100501000c168005a1406582c800c10a50b07000d507800005943c1c0d1424110320290041c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 298937113 1250 298935863 298935881
    0x1603060503030c0f06010608040302030421060905070f120816080408070828020d06240e01140604030308070c0f0501020a200a02180901091401051f080a12051606 71
    0x10305c209400491164410003200d03010301c0c0d15800841c100b40c1048038149034500d005482c558100e29039080440420014058007042c05d0060011b422410700307180b040794280405e82c21400c142c00c4084482800070358601c04441c003481001407060f007c0307051071070403600921a0360721100d0580305100000c96000e0f400b02e8450320007540a82c02c07100d000c00c4100410b03183c82074400040d40c001460803583e00826015003119199000d651221790210f0811420307007680020701c1c1c101007114611f201c018040c011507100040c090b03490444c0d4042c2000d146550080c001e40c0000e005204000d0381030051800c228400c6041c03110254003000a54607041c610b00c0c01000766500e545840c02c8903519103080440903001250030300610360003802d0102510f010001d16003c4403000703482e1020940da200c860502040340305204696041c0180004903007820086040010b03142922010b407006104014108082e500c000303044884035901180d54801106000c0c02514113000780d00380c280981c0c5000c00c9280420400d03034098410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 298938363 1250 298937113 298937143
    0x60d0f12030f0b10050a08361905030f09040902060c010c0f0f0905060c15040f031e0c06090212061008120c070614041d06030d030b06031603060503030c 67
    0x8a0700f00c10080041540c4072641c4800030610400032000c00301d2003400e05550284035580c040c2d14a0413207025843c003415000070310520340000304030075036681c50043c4445c2280e16400180032030300c5030b080e40340c80d500d07417080040c0201c807a01d002408041644940d040400281d40041001c0d441c1c3c00381c44241400307881c0c81032240001078540101401c00a024801d01c2610000f035658614a283c1818280545584040408081d6114006141d50f409203482e185911980c070860300c43d003031042546005440401480c0d000c01c9400d004192041c503c41c0d02107107008000d40c00903000b00c0c107440d00b80007280e442d8a440051500500401c42046400e00505120030100c60215046800205e000714100e5424002e82c0d108135050340214100300301c19071045078400614507008804500d090b43e43c500e40d840c1e2155198019040040c01010480d1604d424000344080d038003203003001d1107811450780000300c581c80010989104c584d0781d00c00100481e4403a038840009000d01a04407642c03a0700c4560b0490b40c51040c2141c03408 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 298939613 1250 298938363 298938371
    0x10f1107030201050a090b061009030b0c09151213080c1b10020328052503030f090c0501050f0c06180c030f06010603020d0b1009030201030b06040509060d0f12030f 72
    0x3005c02c0b66221707000c25150881c20400840e1150420448410710603081d50040111510000c00800c0416850034000c14074031600560b03941801d030502c404201611a9030140380745c103011050105100b012020380c050304410460b040d4044500d07003036a00d030250040d0007030b00c0d100b0b1903e20b00b0b440303d0480e1078401d80c900c01c54500c0e1000c2d2064008076a00c1c0705070b030288500c00000c0082c1421080107807080313a0f540300eaa4103180d030500580030544800b001c144d041000104015025070404d158140c414042129a100700070302c0b440f0300039124203600039414407c96042040000c3d848281712441400c2e07900c0c2c0c40166050b07407110300b803007014151020040b54947c02c4600420400d441c1030700e00000c1c0940c40503c490003800d80c40c1c0c81c0c690150025080502e044460340d440d60410740301c942c1c0f070002d9030b85000555261001914158000182102c004042490007004100420300c102d1741e641690a0340030f282100c4243c0c0302e41d443d2400c5841e81307800450041040c90181286407005825030485c006020150400704 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 298940863 1250 298939613 298939621
    0x60501090902091c020103091a1b0301060e090c04090929070219230a050706022e0b0303031317070807030c060617030a0e030102040803090111010f110703020105 71
    0x1400c0303200321220301e940130b48035801c07891182e10b030035030203100050050500113003440c100e4448004240b001a00381c6502903c40b820803030014141d2019100c2c0300c030680540e41c2158140b507000f40200345501c1d88580700311000000196450740307074405c0b14054503a000080c884903155182c002e00c1c0b2080c0d016201c0380302030007181c5c0707444045035030070304078410078035940240746640d03441040d1100000d507100c06603140343d500d600c0003a50210b055a00403541110200416005645051179401d26950780c00c0441150030148450103140c4480c9200c0c14101d5141c99020420891041c0000042007041c5849803d80004410000b041d803501c42100b40c0c42e8001c602c0006070340103100482d45240709058000b00301a1041c09008042071227881020100d40c030580780050140e8a902610a13103100303110000e0358030b0748000b03480c82280c0d034808401e2007000000d40c000d60030242080c00c100d49900544420504100c461901c020380303628250400c00503903803c040100302e902c0300850910307031a0b42f2540b0158013542c01d1101003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 298942113 1250 298940863 298940879
    0x151706190807210f2003070e0a0b1e1012110403050d020312072f16090902060d0e100504060b1002160b030604020f0d0609140c0d150b0d06050109 64
    0x1804030300354000742d4020180300c5681c590400d8050b20588640c10810f420040c0c041d61010003450300505200c0788680d40c10f19080c9c20245c182c0d11581980d600882e10800518240e845100180036038800c119021220201c0041d0105c0d004a401c203400c0d400d2601b4004440b0400600e40c00a100340c2c0e00442c00c0e2400303214003110603603403442001c283d810965100c10002c2d181904c1010801c0001c4840c0100920440031300c2d03a0112040b0b0059881c80c89a041014081000b001040503440140b140d01400d100428070380e00014568007544030f40200040d1034044292854805012030a07950680a004200d60308150403e03000600300c00c140e0703e010304118000400040e00010300018282404083c0350003440c105001d400f400c0c0c101504840c1c000d5000d02c0018950081080604203c40701c407000080c40c2c80c81c1422080549809201501c1e002910005101071100c10204451040c2100040400c04c10104140c010360950309a01c0421000004a4048115016034000c802140d00c2641d03091070381600d420075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 298943363 1250 298942113 298942169
    0x150e0f360916140108130f030305010519080c040c020712050a03020d30180b1015120507140301030b04030e01050f0d0b04180b0a06151706190807 64
    0xf10300c64060001c8036441d556104034019603028020300070810302103120350390780080c071680c2102c1100130a0b01e4800600c01401c0501e00c1c1060104070003000000e1038580000a81c80700b000e5203016000315102d83d0305e144201d0007001441c0062035010040c11080586052003512001821001c90041c0107040043c0403d80c421110505842c0c580c034410020041e1807a90607210003144100c01c804503444180300d02c02801c1c04403c51a0700350060300780b9116854808848180f07401250006140880d00303401111106034040c0b804002006482c1001a258803600c4e0240c5000d088043d2000d0a0701d0000004800c2050712400b080c0114400d456882031000c910006407a41d00035800348456580e01800042c20302031380341d081001d8012024200040c03003d008580300f107100440c3c4205866100941f0144000030415100b030718002d1014402c0c002856800000007007a81081200818003d0518001704d5807a99401c00080c5018880c12091344032103070fa801d6496210311080c41403003002860240705996a03104030203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 298944613 1250 298943363 298943369
    0x30a050a02190e0d0804080d090b031021050d030f2003191104060207061b02090a090305091206070f0908030d0507050706020c07150e0f360916 63
    0x10354403065410b9001110352050705407203a64090240c200f40d0001c1900200100044c0802c0f00c041c0201450058002e0450380d41e0b0343c0a070079007003820030401ca0320540549414007560f440d084050007016428241810784c008810f0b0142450003000c1c00d8001081e0941d02c50001480342c2c3d4014002c50382c025411000301c01046450b2145d070746040001500b82c100c0f440800c4190303a21600c00082042c40e500b9421100e4000342c0000303001d030344945070600c81e103504020f4420340844064044002d0480d80da0202e00d040001504442605448130300b04010107004105a5004017009007000042003d00e1507440d558000958101c008100c043c40303042d6003184500c2000040e510010021740c607021940c049a001070000038100010040e080c042c1000003030490004042000c1c0c044000d00e0500d003030140c44101cbc14401c1450390240580c40b0002e2150b42c681380003800c09100209c2e007242080007040c2d1214221403400003440c103406001264a1f42410744000070601a0103c0d0040740d01e58034542008218011140c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 298945863 1250 298944613 298944637
    0xd05090108180a08090303070501090f02040509030f0706020906070f0606030b0c0f19110a0818101b0204060f030c090c03020903031902070e0406021209010b0112090f17030a050a02 79
    0x1c200f01011840b410028003002c1c0300a4201d9207040c041362969800c4500381082243d1110150212100b90324060280319004604400610f03e030118041180b9003511a400c1c00400d00707034002c9203c6200d5a1030030107403052640c02c500d0075085010035242441c01020680421600b821150021170382d4030701201c0a80e5442e890341000e942c81c1900d200d110058190300038080508000e030724601555443c0b018094550341502c40c034040750715020152030a842043c0b00303540407800392192032112003140340d0208114008645068220710a2403e0f4004180a030100740c01000310412695400420004034000304030842e16000410400c01d41c50f06400c506074070485075100e600d0383c000d000402c0220945009040c600e030950040781d030020381d102da150b400414100c03029606144c0c04030740c034122410041c07400743e400b802c410002c00c0000100000078081900c09905440b4941c2c0d51540502000400441c04120303a0300300380c040440d0000b5a0f4051903990040300d4100c003c60410001c0b40868009000703a58005800c6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 298947113 1250 298945863 298945873
    0x80601151101150608160c0b0f0a0e0609030a09050604050d080a030e100615080f01062a0506100b0304080406030509030720100801080304050906060c0d0509010818 72
    0x30082110003a012404101c140d5683e421a0314900603208941c100901407a2030301d80f040c0c07401c0d03c88800303a2040001280240202220300c80f0000c0d14036900c460b1f000000c00c1c0303c0f00041e11002c140030010423140c4420702c82842103100f8000d04510000181c00f910105554458245441d02c00384100e6014610450f9000030600320424005020a1702074865001145000104811130034415490300441d50300c0c0484060b900c842c240001c0e0070360440c05800482e075003803842031804c0602c140d507d10344052055078204071441c0400c42d22108204026031081c2405041150010a142061901c81400380e5414100c1030100034005617031110201070307070310858009800c1420203180c0780341a40a440e006054501c90300003004040c1c00504025422901440e40e40d00e001e01407099074040c009454802d5518105205200004000c8161700104840a6031400e80d81034156848840c007103a15809400c01480060140000d401031301d541c0b00d0f014160700c4100342c1c0c603d01c1d03584600c040348007d1a22410203441e55040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 298948363 1250 298947113 298947149
    0x30f06082a1020070f0e06010503060d060f180b1806040f0f0f140c0f0409080d0b210309040c090b0d05071806050301030b07170f0415110310080601 65
    0x600b581c19030761181645220b040141d0f0102060918189403c100404407040c4414030051220401d002d81c461820701300301d8611706107040011f5074a40d5400009020399218142060010242d0700310300030246030b805100e01c6030703016803070881c2a03921300322038100e400c0f40041503c90800c040040c909009a03007182c0500695000c85c5ca508101c1c54444205031507d206501e5100d0016288580c2c0001903540ca102600707841001c50100042440304902c1d280c0f060303003840022001304030b01078101c4800020005000507c4250b000210343c0002d0500304080c0510450130a0480c5480003000814950500721001c21101076084c03004c0d01c07005e05601409104140a2004903c102c66551050b82c01440c42c0c142082d0f0140065040300341070074550444000a600071004100f0083e00034040c0b034105000c0d0034007d0301c0f00516103a01c58840c000078822a4105000300100b81401152076290403034030103105e814840e001f855600c04e005507006403012003200030200d000040300400442c40318181c2e42d07088007410303407410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 298949613 1250 298948363 298948367
    0x4150501050a09020f0f0304030c03020c0f130207020315090609011112010e0a0b060d063003051c050f010312020a0308010b091306060e120a030804060c030f06082a10 73
    0x5c60449081000420040681c9800162016500c511311a0b520000300c8119450002d00300604800a21b0049041d034584084940d00c2c0d00348180c2c014807900c2d0043e1122040c0c0002460800c0140c0d1401c40b02c6265001c1c00f180030404035046114032180b400a10200c1440309a40105101311035800001541160040c45181125610640c101d11030080100e05205520009041030340030045140c0309070b9031288200003201f05403c80b103d001141c0e00d021540241d00c4601c00600690f0b040e00101048000201c814000491610b110349051150f50204218503103a82604070050081c00195401c51585c1d1030840524800a0120324441e4150344a120070b900c1c10f01c1c255880c0c0c000c0c0030041ea0015861210008131003041c80b0340002450556184503408164000b4040c042030f114a140c112500b00640c501e0110b80c2100659800c554024400500100440021002082c0c680f190410f00c1d810f24000007020032001801c580c608500c903000014120380b00320800460285803500680000e00041c07650041e40c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 298950863 1250 298949613 298949617
    0x3030e060304020d020310051506090a0911071a0a06140f010e03070314010506010f0c05030f1308160510030204050a0312030207081b100c02061306020c1504150501050a0902 76
    0x6440130300484400d43c92980020704101960b0012808030382e40c1c008000140c5039907080c800300340c03c080e00e03418230305a0f038034010840980b194081c0b03a140c42d440c2c00c0101000c901000c100d80c80b00780c201c65030b01c2c201401518a00b020107015128059030906001010a0f140c02420748420207140041c1000c030300c030840000565a48007107a800d141e040c0a06c14001000c2504a248981c200407074400025003494440005001c003059a01804100101e00845a0010700004100d5200000342d03111240c03a504120722148807494103420400c21030081040e80048400c0e070901040030f541044400a206800c4498100c04a0255104045d4001c0c1d8015081011130442d4041414030207180c075001d481e0007841e403191405580080d05007074001c0d58842c0014516001808490304881d005541440303120090350703000390b5a01d0068a5071078594a00c4410310200f12a07941210b0986074150141e84200c040c0b8004036081c00002c0313605850070b214685400c0a0084c051041a058070401000328011504000400b0300039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 298952113 1250 298950863 298950871
    0xf0d1203020c030c0c1e0a0b03090a0c060201050a2412020f040203011e080a1a06030a0b1603200724110c010e0105070f11190b061903030e0603 63
    0x31503800c108030401103000303000600c080d10340b0b0380007081040c001c08107200c0b200e0807040d4005030340312400c452a640c5607079016018085500c1c0084440e1240c8070a0142d03070603d02280001444004c0c408000174100c3e8041d0040b5105100391401084031501c0b42c8408400802c400d15080c0e41c1101e00c203410f010a21510201c01c0c4c005001611401c504411000410201d0784280c006406440c070b100301100000e801d12414001070840300c401f404941215588000b080311080c10300100003081c410014225440810038280c82c141c101c14090020306066100100400071004600c0c0044c0c10700752030900740e140706003400740c0c0002100103891402d070240d00c2c2d040640c0d006040c000f001202e40030650300740c01d540e4011901e181041104441c0d0341c0c908500d0203401c40b004214bc4100c50b90414041040c8a90414041c81d21400c441c202495022103801c0f2050500403022a41c1c2c07181c0c900c51004030180a141c490f402d11440c815124150180030f502500305207000c051000500003004a180d1040d1070605401450300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 298953363 1250 298952113 298952117
    0x6090c01020c04090c05041a03100c0504060c031e090819050c0103020a110307120e0301150501050903010e1905010b06070b0103020118320409020a05060c0c0d080703030b0f0d12 78
    0x5001c2e15800064180d5402d000880412031158003108c485260600c03041100d102c410745c00300960901d22034098514092442032005000c403040c4ac200c20f0500440c40500080000350b40382c1c0b842c0d9141c44000d0684540340c000e8908a105580c6031141c110a84d130382040a084d0840700403e8451052401140654000c188410401074105d00032413014004002501c0b0003441800355800003400404024090100401c00a100360304006403040c50800c45c4842c002a507400386001d41c1d40b0745001020034094425001c1102c518030a82003141c592080340711041610a2140e00240110310b2820100701c0240140003025100c5003000004000641c0244460401d0104c05d5103120070403a82c3d910140703084c0511800846280b41c0d0002451380c03940c2c2809820307075118001c40f820000e0321038940120390b60394240c2c0500c1e40641000a9402c0052008100b18a003405008000c003041c0c498074944050139030001c0d5012000720341408402c21003458181401030051502605442c214216a2107840d00d100c120042002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 298954613 1250 298953363 298953383
    0x6180a08040b04060e04020f0909040215070f110a06050f0d09060c02031308030f090904020607060e0d0201050f060f0d061103070302070510020c060f100e041406090c01020c0409 78
    0x500311001410041140000c4607449601e0660060034080503489550b100d288108401003d511030390060310740f815025624090305a440d0b10200d60082c0c0030005100c20048003041c000100700c820440090b45510031a20144405c5c280f40c1444845c400c3d9000c0d1b0008204240500107050300c000003e4044810403180105200b4900c0d00c8402c120703020041c40400503007001070202c1c05c01c042d00003100c004100406c02149050301c00c0305c02018134041c2e50441d134810750103440428199544c100c1a52101341d00100b0800900498001d60b0703640d0b00c5544c1c62003000d9402c110004038a0b043d015400303845040d000d0083d1901310481c10412900041039181141d180780c0c0c4054a60303540007401c02031445505107440050740c030b1080c0d007410340c070f00800002e5581c00e45004000032296460003107001904103803c43c00341405a210048442200071080d000b032508030710940d0400c01440243c0e009044c0340c4240109681460f12481406610740b950340c2a00c6025034400d41c078000f61810a40d01c0000361074040d034a849 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 298955863 1250 298954613 298954633
    0xd02030604020910030210080901150f050402160c08030301030b070908060f0405030706060603050603010b090c04031b1203030510080a020f0909120301032d03170a020d020d0903021c020618 83
    0x11f0310301003040c142030001607510f004000e1051001d1240105403005080c01d00d25951401c00350031000c80181c007520340541c0c0c012030540c0301240c003400392800007a0f201a00d0240c3c246c44056040e501e4000f4401030300c41c4035560001c20400b5015402500035558208023030a0b83c0d603a1303041d101542250140003114103110801c040c80c041781c0340344645000740810f582c000c1400e003418003c141c03e50b1090202c9620814250051280301c20b038500071202100d9000b4000b021403151a1000050300c0e005078044052602c4003035400082580c5903004900c03c101c0315210304801e6490b2041281c1d18400c090f40290481c02e41081401d0514101d0aa26480358031a0221503038a04980e0b44040c0e1a042a8411501800d1030500c56241c0c003401040c602c62500d40c00402d4040701f107940c0f0002c040e80421201c070640481c3e110003260142c16940c0480f582c03007020382e5080d59140032074401000144008601580140112040b0b41c207283d0140b1034003043e2010340c0d801080107886645095480040101c2107008c80d108401c009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 298957113 1250 298955863 298955869
    0x11407051c05042f0111011103060f010203130b0702040f020a021005060303040503070806061008160309062702130516030b0a1a0406020d0201061503090f1b0302040b0d020306040209100302 83
    0x1010004508040710460100d04e000007400100ca0f071850040240d042c8100101d581503250152544208c080f02d5012201c13441c030340143d040d441825a030500320f44440c10b02040b00703a0a41c00a01d074180c0f0a680030410f07050795900a10880c06420301990050304641650b0a40840303903007040b03800c4680107054074030703140e5643c001030301d0700c1e00c0d035031000c0752036003103081040b038a0318044c94003050414550030000058900001e03500d024058404520040c035568082c035400303201d1913601584c01802c013a56240c2c1c50003291420300c10b51042d100d004901c681a0300e20b201044103428041d15028090101c41007094041d040c0055000e412078450040c1c002804800004030f00300d240c48840b07039840d03000054503076840c00c2c100c0c02401c151105420100396070400104000c0404100c18070701c4a02d160f03281c002425031403450a00c40502d03945c3d40c00780030044c403400b16200600020803000c007100d00c02c91381000500907280a00c02e000d24014030207545908244001000b40c101201c030554046404c03000303800c3c8540c51b9400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 298958363 1250 298957113 298957163
    0x9090b060405040903110615030c040603030f051308070608220809040b030c03010218010f08010f03080a050c010c050a020f060408070615091107030314090a060f0e0a05011407051c0504 81
    0x8c40c070918030590100000e40d003000e1207503074640002a00d0078000281191400750103000080d500c0400c10100041d0300600081d403e0742c58000d002010b007903d4800c0c4c0c0e28103000740601020b68807003c0c90165000c518140e0411250b411446551000201d410f1964002c1000003d0407108189501401391001c003010940d001e1008000000c400026141c1c421040000140400307200b020100c140308101c4014004a5046e00d400030880f0351000e00c3c01c0c0d842c00c0c079285c12140b600401507904141c1d0f00700200c07a00c54035040701c054012220350742d00715413400d02d000c1d95240e07540c0c0c0c0503034018112010400281020641541020804121501d0310104c1296038600c800115008000d07071100e080750125441c810183d02d40100c0083c106410a400c1032414090043c580720350980100401e01581d40c441074201082541180d40b11a41c420b094a07850303200d034208113019040000d144048040e00c040019021405042542d000580540c04134039592003a0702003000070b00f006041950113040043ea0301a0703170701141c03907 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 298959613 1250 298958363 298958371
    0xf1512060910150e06191509080616051e0f0301060e0f010306060e120705120f0111030103030203070305071109042102030306060702190509041209090b0604050409031106 75
    0x8014a007003204942e42c041140c001041001c290340d500f480c1004969a10140b0640100d0111941c43e1840c60000c440c4907041e001c0c1d40050100d100c1c5200040283d131b0003080741c2c0115040c690641d10036a8840c050108400700041c5c207400828010b02100000361480c0d0003105002d0322140c1c84601c0c018011205491540090b8403820000349041103441c4181048410b01003480000e00b014485a0b052041c09040e521f401007100340200c10001c48400ca030b4000304000f000800000e051500c898190400c1651100030a00940c0050341c01c19544c00070384940e40303044034100e9805a001e54103019031a6003c55481e88165015601002220b100d44c03495625006c441d40141d21810f1441040701110321510b421806408241e0250b4100388100501c686600c011204815070407614214404101c40b04000c0001c419046243c00c40c03020740400041015042c07110211800940755400110707968400c100c107481034213401c40c0d0416001c1c0400c004a041c0354004181041c42030404091640302d58130403d1070000116 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 298960863 1250 298959613 298959631
    0x926031209030d1505150c0106180c1d010f050307110d0f020f07050a1202061b03040e010b03010305480f040203040c0b0a110d0e0f06030f151206 64
    0x460030211542803080b84c0c1380410a00340729003100d1500d000140c64039440300821003100400900380d200700f0740a5211401030511100d2501c019200301e03600100610180560001003503a00000c02a102445180307405501380507503c0316a4084104022103841e04090040c1090000f480d040d2001050144102c82c0510940c0e502d0003220900090002e04d05500c3c18000d980b56042002c0070b101c183c41d250081810707035150720607400841c0c6691001c150700d40704c0d001000500341424281d803c103951000c00200200da0301c06008060503601d49844002610086c8001015540010142c0031028032103d98098070700b80384028640c2001e02e410040d0b40a0410070701318152400c0d801b58030300084c40c264041562010064400314254035165403101081801400f0301842400c2c0030440c80f62151140c403489c06580298819156140340101024010740651010580328070302c8020300b824241418419a0700c14503414130401e21a441d41d0003083c06030703403040040981060303000d80d00c01004101080071a00400000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 298962113 1250 298960863 298960867
    0xe0319030203130905130809010504181a0108070e100c05061303030606091d06060f070b06040b0904020f010f12230106020a081c0603020915040c092603120903 70
    0x3d200c840003006650704092481481c04050051341c0c17502c064410f0041c1d6006000d00c0d610600705d001a11305000319881004071140707030148100c000510781c02c4407441041400b244000c00310b9040054038016401c03622140090000529028907140290f0141181f20450504950250842d1500c60a00904881500d1200013650703004c01099032510402c1c005013140d29041d04510700300112000041442c0d035020098403541c2000c55001c1d42e540c422500c0e60754581c41c0700c0b0b5841200d1310f8440f82e9101d080b078038280300301e1234080e0400c1c03039041089082e482541c1c02000b40400c160341c48015654081240d041c04108002d109030311845001600c20356210520a07100e0080034413601400013040e2a05230002e800710b404c442e0362180021800c900b60307083d405405440e07180c41c251a07a00c80340180815807000c1d600070440740030312413484001e80e00441603070425103003031200c6820303800155610b00030340c86984d2808429407444215490402702c03d1241824074170a0301d01e821101e45201035408000e43d9a00c0b02a000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 298963363 1250 298962113 298962127
    0x5130f060902070f0510060b07030c080d050702070e0a060b09040509070e1e090a0321090503070c06021905060c0f0c0a030801330e0f030f07050103060e01050a060e0319030203 77
    0x4010814071b059245000307200060070014031401a0140304402000c0c0700840300c0203001c0241240540d5244081100c0400240c03500420081d030390b6240307100e1910072440c0400890300030a510702418081d02c3c10040c10f18034000007441400010600103291103014001c040000c105880c214080d18002c01c24160048400003203c0505c090980c0003130b00080003940308074070080c0042c2c1c00100310300440000003a01c91441c48030080010180c014580c4c001c005020004000040001a00301a0305554030781e4210b0761944c000760070810184516102c0945140d104d80c000600b509c03000b400030091101441502424004000340c42482d10801c64802c50206075100014041e0440002c484540b2070603c1001d0501d605030041102c0c040081d1140480801090040e95a4151582012000e0808015003110347d600300e038402c0d0303540318034280c0113035070001e03041090001d2005903440003241603800092140700c2c140e261807026141100b0907180e00d90180240e11104403400c50821400079041d009801075a41c6d80c0d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 298964613 1250 298963363 298963373
    0x602030a2a1709040623040903020a05070306060f09020306011409040216060c03050c0703050301030b0606070503030a05160302040b040509040c0b07030903021801230112020d230105130f060902070f 87
    0x40f5500403c0a211108000d048070704440c3c010400349600075100023654074070a060803401d084e4a140e02401074400ea9400008110540c0d00c042d00b10741c03192007680a05900c410505c0141c1c8401c0e02c006000030391007a4030415114020300202a2440002c200502e05034000151800d0f050400e0b9042c0e0f0069a94503100144079054007400358440f10f008181403500b1103e40d8050920b000c10702014000152040000b085600e414080351000d0713401200726904d91804c5d048250290408817141810950044028594a8000d000342c4041e01c00c00f0881c8c1c0e04040c06c0809004001c00010000c4e02c0880846400080c4030071980d0003000098082d950310308000e411401404503040008050b400e0908041004200c0b040c1c41e90045c0c2124a05d00594003a88a80d0500484064424418081c4a18400200108044550352000d102d00440034035414035508030340548000801c4c01d100e1560040307602490011403080c158800c01201c484024001501d0392109070794400c98118040403241e40e091801c080c81844 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 298965863 1250 298964613 298964621
    0x191809060906080a1a06030109150b040b0a1a09060706020a0504030519020901180b1e09090a050619020f07080d0e061009020a020f06100f0602030a2a170904 69
    0x10012000b000c1015813036480c0040c20341c17901c0900c2c866051402c00310b5401c0e074080d000a010b454002c25203902d0000703509440e1009295048105110305d00e440002c00080c14400203401c00c0b1130b404051041072281458000200c0d030300c283c0119078040010001507000031440d00c054100c00c429641d6042c0c032541589040c0b4600180d01c00d1942c001148948242c00590300c0c0103401f070642c0c84568404170405200d91480300030749100b686080d4480c030000c50302d0710070240000400003505011200200c181d00c2d0203882a44518807844080c0003034201c0300004036140c150f40005a0b0281402c3c600500d8100242e4403a4142e0700030240032141484c00050148912360b641c010142101c0728180604040d0800c000c5407100e00d6514840d0107002d035004074803000110700a008540140c0c0f429400d460861900c8030360300e05201d04a00820244c2c40180b440401c1240c400420385400d940d440d203d001c04d00031005884c640b84d0010549000241850480440000d41d0b1549500003520010302c040d034031450b0010800003a9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 298967113 1250 298965863 298965869
    0xc020a030503070c0801020f09220603060c020c330c010c03060911120105011d04020408010b270103030516060e0c0f040e030706090c0b0c0a060606030e03191809060906 74
    0x2ea0040c01001d52018425080f1010004104d84010940d40c00d410658ac1102c00711030000c0a19180220001c14015a504401400b1916034295001042107008000403614103460030040d03c012010f82c0d04c14028039072032860001b0888003c01d420800d14201d1142034913501c0003c84000394131500108206950303400742a245440f8080d01d1303800c0c200d11034003441c280b100500c6624100803802d003085010810300b9041d0104028040c01c00d642d103940792141c480c041c103404a007090040580465103c2000c1540610860703030200d13041c1d0760619900c1d684040b20315800410340054400266108280060102e104048503054070b80e001d491807114a004000407a058858250f020b5814450030390b04000c030100031a02190f5000c0740004030009582000c2030084902e420000b02a41d0024a0100c010b60005120701140c0c46404203101d9140c90b501c0407025100d020000d801243d005201c0b00c40c04204007400e207000c0341402d28010b800c0f0900c020264250811642c45222307031a613100c0d014020b400840c05042e0107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 298968363 1250 298967113 298967129
    0x30c16030b13030c0b180a0804030c0605031006031a04022208032b2711040b0d06091104060b090901080d0509010c0c05130e0d021506010f0c020a030503070c 69
    0x400c8548024084d540d01c00c5005210301400700014480d110010755541c00c0e0803054003200c20004a03850150200d0f809400f081e00c10f04c0c02c603080015030364480c104481c8204100c2c190708842074601902074014145031810300c140030104000506040d200e0340b0141c540c020010407200210308181e4030302a4544180c0e00215000e030420081314180511004080c06500689003900b0b40001c8103050b448001c2040713200151988041e041d25101054800c000711003454010002c1d1080c1e0750b2400100001c5802a1102c1030304400c00002400118078240d0003004d11501990400d50031181200004040b183c20b5000b88a4002d0081512851030030031075421809040c4041c010b10100c80c803e0306c060704500840d110f4034100035508546038200094440c1890040c6809001c10541070b100c8400e8130090603a003001030240303219212410403214400559086520102c0703103180d42c5074651400440d0710342407450701001130103400c4002c00b0042c2c84084101d40294007a01c00303551a03042a10b0000e5040c0c80303503404044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 298969613 1250 298968363 298968391
    0x40b070602031e060306011a0d02070b0601120b1e040b12010203091e1507090e09060601030e0307020f09090703050a11091006050a03051024090602012c030c16030b 72
    0x2991701e0014030141076035071004c1c0c4181161140c0c140d0b0141c0f48035143d42c040f02c0c54000f080c10f00420044100c064000c9400b600c0e000070403240d00c00d4010488042c090000d0b84091025403c40c0c880159001c0102800306c068000324181c03041f480850303c10b21320030301c0c0d865a9a43c00000c121b1404824440c02010142442840708110388600b0420358407402030b50150b402c1c00900b03010804142c001d80200c0700501412903001c0040c44d2050320291100e0b400c6030041d0109042003411044800c0c0071040b201c0301c607401001d0b0f00e085590304080c80100000104020b0381449621404800b0810030000c0e100701c03e118041000b111100b150500c89159005000c84030f08215000049c441d00d03070014183c40785071403149030000f62552044110810003800c2e0340310140a020700801c640c1071701401541441c1d01400e0b07807079030900c91303035180c40c203d0880e43e020b11a85018840d44240002d1120310200b80104100700301c0489003814040680c643c10302251621200203020041030400401c10039a2000764400001e00d0440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 298970863 1250 298969613 298969621
    0x90b01091e080c191701021b0d140316080a110706021308030a09030809030a02091302151303081321050607020304030209150a031205040e060f0a0e040602040b070602031e 75
    0xc4501541d03030144119468100d817900700f40420950546905082c1071080c1c0d103030b03140c000358900d485000d4246007000042c0c46203403000764051842c0c100c034010f880d1140c00d84020311410310115002503015107009804c1e602c030828200034540800242c09481d02441c40180c1c0e50b4510807500715014000e9000c1406a04140001c010081e04092104200d0303400440700c2c0e989542a0000078203000300c104000b54001c450380107200f907044001e4030504a0031700c240d4000c0401030250001212501689044000039005440305000040d4290b0240000c8140078800307820885c0c5481c002e200e041400b8904100c07401c03082a094003400340400a2a4108420780061841d1a0650300461075940c4010140d01ca40306e003d041d0107074a510f4400c401e031300850300240307659100344c11401c00508650080c030464810f02c9107600401d8580c03900d1101d91040b8a0002d000703003225403411040d8441010020400d640c80c45d03082c803000400c50020401441400e110300c0005940e4500400c0605800e4580c07001150900d980710104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 298972113 1250 298970863 298970899
    0xe0d09090902013203070906030c020f071505070506090c181b03130c061206050406050306040f0c27060b03070801030b191104080c010f0207090b01091e080c 69
    0x40d00710000c10b02e0316041d41039a840348107840c811045004904c0110004208403a01c0c1e400402c1100386c81440c3d8080c030180d40285c0040307903194100ca080398810b401012080129030b0070403030310110042e500d051490800029840d46400c16004444500300c0350400c2c40811528a4903203c1c0d448508030910400b401401c00d03402c8204544070024003800905000004501031403c010048454103038040402d0b0482e13a26520000c0400c81a441050016402c00c0e8010030641b0b028018001902c1d80500141101e658684803111a00c1514005450586d40307004041000b1b00d800310304400004298000790204014071070280d00321600c81d0300a5041000a0050000c3c00360b00c004031504488d0022003a913020746841049201a21801500b52801c510b00742500002c00310a4000e802103c50450035208401002401950700f502c0b0b050200f00180c201a105025800860384140c00c3303680b041c9040c13096151150740c3c01030640420b1408140882c000a02005910010056541044000e0300d4100c0910058088 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 298973363 1250 298972113 298972127
    0x507180311030c2407060209040213050a0b07030c02090406060e0106180905010803270d0b0a060503030702032a1804050c030c01050d0917160c15050a110a060e0d0909090201 76
    0x20150a80e200010b17080d050000c03d406031520410010300456030786440ca0070700d4001c00785521425000d00c80611001407116624025660481d405840360700d00441150708101e61440300410840d100c5a54000104895400c848003601a051688031521070119205443c50000c10703507880382e5840c1f41407800602c940f84004c0b0a1fa0704601080302c0d01d50f245448201c400200d04661031200303411200c8696841d0a1149035902240a9801c0b86001c100b810b465409258581c07086280203501988420100e080c248019440604091014039074031201c2c42031800010242181c10300c04049109104044c003040c48018449891a071030120020440b9490400000c0c0c2280a10358000d03290603035942000043c04800b240786000c02c0214580710b540c1d11100a031041c280300c2d04e120b0130340f8074031500000030a056172041d104610182540c0c8402d400c0410034082218440307020b200d41c420b5405031a8035080015894000c07a40741310f0010000d07140d503808151000304406540c1d40703e160326900f0031849201603600007007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 298974613 1250 298973363 298973419
    0x708070e03030a140703030e030c01090201030605030303010518090c03011107110406030b0c13090e070f08010203250507050d02010b0f09130b1f0b0405010e220507180311030c 77
    0x200c4140c550250382000e600500640b202c49238107000c00621540c810700c042d03000044283c400d80f401c0000d541c41744241552030009000d0342d500060b04480403170008010720b02c09030b440a801400c0b1441d40701c0038404603086d5024140c0c2c420202c000800c1c09410003425a550880d01c55050303404000c910720319120b541c210130002c1c1101c0c01c609000a2603058884c4048d00d600301600d1700b400d00740210112100403d550308a80d00c100f1155011080011030300381011300072603000d00a0700780d00009030301e150401400d0340c101c49036885050242c200440702c0004d0040c400907103812103603000000c85440d2041403120b001c06201c0c24520076001c0754100207030000f0000310091520f03000070000c081a45c8401609044041020107902d8101360001c0001e00308029038010019200280d0300c21207510503a0003804918541301c001951452401d030854000301855900480d80321078186410b441d031509400400560f101150001d4445030340c40d04d134080141c10200a00000480709841c1a9081d54850100c0020045114 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 298975863 1250 298974613 298974647
    0x32a0615060c240106030c021504172b0510080a06090515090304080c09090d081f03060609050105010e130506030307020a15020d05090109060c15050708070e03030a 72
    0xb007140b2004820401a003038000b491402140c12034481071140700c040c1c1c0404d105070000031f1704211944503218808140a903a441c844200740c081c1d80c56544e00c900403142c0804c0c0c0b440121a082c0064208900c0ca413061403030032006c00300402d10340c03042103401c1400c1d503600410003800112000d004000c000c0d000240f00c5c084e150024030010381d4400034a4001d081c0b02907442c402d44001b120703105001680c2404401081150309250450b610750141c03200384001c040c021580d90586811070340f081203405004444055006803c40c141c00003400d85a502e45000d10100d40050760399607668401031056901c00c0c03250b00c0c0541024201070318110364410001d510200c040358024031090f100c401281d05c0761001c00a17502c41c0c0c0d030300038528001039445885407038032060380b00c1e4800d0040c0b0444854550680c010340881d04541011303524400301b1402c000081c1c8980792100f0007120181810118003045130b11030321650780a44025640c002c11406c050b04001c1200304d1903410140310360000c00c01c0c1c104040d002501c0744054203c00b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 298977113 1250 298975863 298975867
    0x506040c0f022e06062705180703150f030b06060702091929101806050a020c0315090d05090d02090423010e0d080135032a061506 57
    0x1014201ca0f00403002160019828206072000c5507143c2c20810004146000c3d00030014140070007003141c140a1380070b200c1d881d000110101c81016408413902c1e0280d00003000c1c2008512190560350b41030080c0000d0744001c01c140c82206052041107d15220181c02180485015080c00b42a4001416140e8003600102004002111b40740c40c407141d03600880700044421103410910b602c43c0000f1503a41116414481c03017002414a42242c0c24080c00d01040401c524a10810741c0c0c80c10181d040c0d4981d44080042e00561040410501d465501000300003200b00380c68034620741ca402c1008007d4131300004403254905001050061407240d0b20303140f0070410041e8048584542c1d81d2945d0074000d02a00c2404e00b1034820000d04c000520510300d05400c04503010154030704856100803440c200700c441c94028047c00078240c4100c40d07550045800d03100d0079801525411550b0403030240042040b850b551040c80c40085a0301d100c61182d4400c0074642041c440e044260001d090285801c07038400215010710b80040d4400c01c40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 298978363 1250 298977113 298977163
    0x360209030a060f090209160e0609011b0807050118030210050a09150b030c0402070c0e10050a03030906021207080706091104060603050105090c2704020d0f0506040c0f02 74
    0x300481c0070401d0300304204000c1040303a883c481001d0720b1414020fa0061a4541c00f041203803e103128035010321821581c481c00d0020300d44042041c2c5030301a00800d41003280055030010700d20b4028020071142c91043d04082d6035241c00f45000342c2590324022418218001080145001c42e0700440d88403000b80000200007116504c1004c00d400810740058081c203002c485003011008034000d540480070500c4101c048a04041d00102044140d00c20b810300100340d080c100c0303020050030320149019600952046c00005078240c03140040368502c000b07030f80168000341500d002000326a40603c103a032404020006010307e072000325101c0440b03a2045010090005640d075000000f48801e0b4811000c11040c0180309000d00c650303820008025213000e000f024400c200d5072010420003687c04045800d8400c4800c1d030610303c6001c016440c00c100c0304031042c194102c0c2e0200500c2e1000c4045206014002d01407600c0000d40d81030100130b0204030303000882c0e0802844980ba030408012034000a402e82c0b03c10220040341f1035095 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 298979613 1250 298978363 298978369
    0x90c040e091204060203070302160b090f040605040e0616180b18040e0f070e01030f2003010c08150a0b03010b070f0f0804061d06041403030c070f360209 67
    0x400c080c102d807401c8074081400700f01c8036408001400814000c1d0300325861190b03803600340022140c8500c2400c0c400c4804201605140c140000071680e00e0b60001c200080440d40d03080800c050301d544500360602138100104100d00c10480c1e20030402920030600e00102240300c0100c0600c1c1910150081800107503000c80c40300c2c4010032040711034061020240c42409584942e00007207035030740c69210414880380a600c0740803030b010391064462412641c2100701100c6001658075a082142440484080c01d90030f6590141c09c00d860900402d01d50703401c2590340c4c00c201d02d400524045e40600886203548a40309183c410840711841000340c9040d25103e1000c0b5030703211658034080141084e13003400113100e50054140d0000340502c41c00507000700c800c3d54440247d507241d5070026602c1c882c4413052190740030b90248002e001004400203038a0340200081e0480c2d00d030070320b00c0100710714081d115441030b00042d050308420f01440c0d40401c50105042c402250510040b0000042c10340350200541a46030031a40c0400d604465075 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 298980863 1250 298979613 298979623
    0x5100e0a0c0803042d1707030c080c09060108060109090e0c0405040506060f24180301020d0e1209010e091f060f03060605040803070f080405060a02010207060605090c040e09 76
    0x19510003003070101c081d82c82c1111526508644107034000b0403420300702c002e030390b0280ea4482009113502c81d505048450078440b281c000c0b440300c1951695107101e12040403000400000d041006000880010660052003004100c0d80800040c84641009100d00034481280d8110a03081c0c266003000101140e0760b40317007102c00d900c5c04154101d0250300909040a001c04d00501050183c0241400d640201090712211305001c50098080c0000c0c0c1c1c008400102c02100c1044600500082c041140088003d2260103000a00ba6000300042d45078041e40c0310014140d03c00100401c0320303010001203605080c000c00500281115140303401c0b06026078200400680100140c210070410403502180d020003a1762a01002031001450442d0900803034a08a0081106401041a6000c541114000310729160091b03441040301e00301040103c0306036005104c0810183d940c0c401030b00c0800c049a00043e12681641080310598503140e1066015450800500003840c2c1000304440c20b41e250300c0009091903d44180c0b651500c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 298982113 1250 298980863 298980883
    0xe040b0405030c0a150e030906041806180c09090b0307050f1f0804031404151b0203010c120614152503050a031b0206012112031b050705100e 62
    0xf8000c0800c40400c0024880c60303522250840f0604006c4580081065556071184001311603100b10b051108001100518a80300031800c0d003041d01150903561031000c07000c000303100ba1030140f03829107400d5480c08165001c0e0040d0014502c08900344a248440700c0420386071581c0d40189801805900d5840901d038aa0740030811054075400a0504030740200c0400408140060324210b00003505403d90404506000d000e40701a25800b400820241e00070100559040310300e0300c91600d0342d5600080500240e034007882009614010303900c980811070445440c00007281d1958015000c0d18480c22042055901ca01d072001c051081c54401950b92400d610740c001480f03e4403140241d016403450a100c40c109548840900004100c648080c0145a065030281031100f12241500d8010b0f442640108217607000039410850f00d503100c60a800140042d500e42100a05802481d00086034036401090b004143d110139403d0480c0741458858101401d555400d40c461105035101c1d216540c81d0381880c044950180201650 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 298983363 1250 298982113 298982137
    0x40902090a02040312020114240907020f010b0103020c120a09171f091218030b0109020a170705090103051509041202160503031204050c060703050c06010f0e040b040503 74
    0x65407810700344510196200380030403216000720461100007280140250912040303a984008082c0c1d403120702028461111030078500c1801c0714089100e40316115445901c2c0105190f90281c00f8844106075614252811114028101441081490b5001802180040c03188644107039680d565121502c0840d20b40c10180c01c140a0304800c00155800440005030f41409071108001e02c1b03107103041c8903c4d0f5000300e505806c409810036a8030708281c040203205a0090100c001d005510198094072900e548841d10002d03040b0314041c9900082100440d80c0208482001541081c00e22030300f4074010704000c1003401241080e5040c1030701d842c081102018480c0282007808406080c0d9a92440c0c0340c2080e00f042200341031640050f000d13040551903000010703800754054490103801149420b0484000c40000c840060003a10140194280c50078107a40b00002043c5860090f56000d842e003001110b898200717601a4003e141d070010f401000c2110244d50510951700c103811050012050343c4d203040c828254400c00300c141103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 298984613 1250 298983363 298983379
    0x18210912030702090a1116050115080606130608030a030216080316120b0a030f0812070816050301050d060f090203120c060c07051f090b0f0f0a0c120209040902 70
    0x80c849a0000c098000c803402100c200a0f00d45480c0020801c131003c0280b040101d440404c00900d92055640c0c00b1809148128000500c00300000c2d56000f8200031a003003481103812620900c41c5502d0010850781d1684402d80d000c00c03c03145042c5111741c2d00e104840318041416000b08210002003e469144440396801c0711109070340c2d1501340c8244040c1e03550600100b021074100c548040c42c282c030701d10512500348009800b00d80c03454155268450107030200541280c040d01d0030840072603154a00d6101d00c0c01181a9110101d5508000c8200c1854000d100e508404110f0103000403c46036650880051150b0780000e00000e403a5020141c132400340c0104040650907206141014541c4000500202030040000040c2c8034503444610300b8040e64070420344050050750214170300391100116142c0a031242c402c021f10000301046550b030b81c000c1140d42119041d40004110042010750b030011006268803a544d0300b410007841d446480301502d80c03816941d01d80d42403a40400c60b949180c840d58060108190002d005031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 298985863 1250 298984613 298984639
    0x3091d2a18041b0f0c061107030c0212011404030c2603071803112205010e061c0507180e191a010b0313031b060c020105182109 56
    0x301c10314040ca120a4042c62034120030040f40e030842101050003100d02d6440040002141c0404c5036810b802c044191255681d4048442d40740c00e06130000c0442611940b41e411107000c45004000ea480ca0001c0c0c0b101c580d904040b100c0d60140902c1020950040d030505148104284508118680b2604a80e01010b0f94901e031280701c0da24061107028512980740c40e510342c41300b8042c2c51b00313900081e103807484000c2110820100382c0100c1d01d000e460105404a031340c02400480083c0c500d405003514030a0340042401c0c80d45e081400101e0810004030345210f0844941070461002e00d079100307944c44400d403040019078172016a0804488890380c10800c0b0449400d411a0480728410380b0704204541400021200411403840c0501e07100100808541220881c1c0c180360705594800925010f000301c542d0381101082022a1800405000d03e4038402045001c0c00d40056010203c1d14040d0860304060030781c10700340520319075403d0180d00008401c203034284400b0314817045030361800000d9414043c0380420390b8131071f01e00350481c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 298987113 1250 298985863 298985887
    0xf0801080d080a1103041103060702030a120b010e06030403030b210303060d0c0510081e0609160302040306060b0d1104150e03010e15040605060901030804090519020c0a03091d2a 78
    0xb0102c880e000308c094032566200e591060741c0c1e0744542581000030503030f0b03d0001302592019500a5003040010304101d400140c0d1000003c009601c11201140072070380d11010305e41c1900700000c019825200040304160700304800300302c070707560303800010000b80c4990360301710b0720904200a82c607442c802004003602c2c0190310220800080c2181c9001c6400040d41034800c0c80c0c03030480084401e8400d009140c06007001c1c805407a580040310700a6000e10a0300b06041c0c00700400000506240b2480000f0165284000e0325480103070034620a550641c00d40070b40c03c81e020721091010900100400c86800305030b040134082c0d000520f0100780980011b0b1080025800b403c1c4401840035404141c59108074400c96040010341d8800e420451142003e01001d0002c2009100510a441280d40480e4200c4558410460540c051501e0340c0c0991b0700004101c079903a000303001440d04140d0040c4103c805840d414410340200c00f403086102540703000040c02c2680810842ca041c62081c03003058002e00d0041d0109500c41c0c0d036440b5000f21 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 298988363 1250 298987113 298987133
    0x140a050415140a1a03090a050607120f050402060405130f0606030209091f0e090124080c03010b13020f070b0705030f0112150e160e070f0801080d080a110304 69
    0x2e01c0750780407200c02c030400300391800b5002c240545001c41d030040382c1c801c6490030103d407540004200400078460200943c011a00c2003005511401903507980b01003042d038460700101074405e5020300454042c00d040c18000180e42d020f080d00c003980c505646030112621800f840c00c02925071000e001801130f00e03000000c16215419002040d1007441998030f00041d40702d103c00511a4415059440359280180e441841a03038403e24010380c0240d40f140000c103204c41e00300a1251741d01191554028950080c031020000001709015a00c0c001200320004c000d880810800718000c0107151102501180d40045c1807400c580107181914002c5401c01c8402e0454039141c03c0141c165402030704c1303031540c040e030480c0001007000c16401c2eaa01140d5020140800316107640c0021406410b00143c40031007401220b0810030000240325200000342082e0001c0991800c0c4040050300449021780100208101c07040140319106000a00f00c01103a480e1921801e0342d0b450103144001440d001049140402000042c0301c02e1081d1900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 298989613 1250 298988363 298988369
    0xb070c0e37140c0301060c140d0f11120301090903030e03030403030b0f0409110d032307061a0d080a05090604080a02040c0e0102070527190501050409080301140a050415 74
    0x442000400d1000b01a031655460464088072003100400c0107100e668403604000c081e140c481d00540300d011042e195805e0404401007610320024801c0160701042a0b0b2000206010041044c050240f04144007020021131005005000d1482e48610404040510036480f1480d074080820075241c8034103041c90000c0141c200781420714032401c1c00305241445440e2074402d00b00b01039031049240c034440180714184580500502802d030140661006404240b000c60540030440b185124400b5544070761601d4846c0841c1ca00d000040d00f8540322428446154440310180100140c100e009030340c9901c1d14550845080c8500c080c040d42020011400080007100041c18102061081381c051058060210b421500042140181c41c0183d00010081020381802c1914109040d03240d080340c0380c05080683c84a0154409450100194041d0102118080980d116150140008031024048c4110729280c690081c00107000d48099420400a086403035580e01c6148001058044c7c001c2c440d00728140802c50192130144 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 298990863 1250 298989613 298989721
    0x108060a0e060f04020108060409080a020f0f071d2e1712160f08031e0f040201050a050a0c050109080405011214010b300106090b070c0e 60
    0x480d030701d00c003076800700740644150842c4083c0c086550351070f0011900a00c0241400340c019903903085140124035030b88000d01e41d00080e078008007010844c801e00c0c0ca140841200341c0b070b0910f401c12275051028440e29842d1001700480e802940030140ca070803140c043c0f1036920346503803480001c8604100c2c8003210f94202d0502210001300c0842c2892822410054541140d049200d240c000204002400707134682c0b203609944d190159100c070325071040945c1c480c4500c1e40142d8481104500085101c0d10f04404402a980c1c403030005819944a030600d640060000d00640701c0060030300c4404070b800c50003588554a85108244c000c1300a0000180509001800d940240980b50014810b520820810340701401200c011070047c0200303250580c40c00455120a4100340d458403102011450007070300d912103041001000300c0307004840c034102354902a00a41054099840400300f0300d0184500c102140e20a81c1c4c0c10101d45400d0620702032a07566059180d103010001c04c0388601c4556503030070100502e48614030007090950350703 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 298992113 1250 298990863 298990871
    0xa02040e03190f0908012f0c2b050403110405180a0b04030206060d02370e010602010606030c020a14030f0c07080601060311070f060612050604020405070f0c0803090a08030108060a 79
    0x120178060980348002c5a403010750f06403405070051502c03100e13000034a613107560003818202540d41c0340b40f41c2410621401511095070030703002c0340b2080c50502000c1c3c940082504002d45020b155540301c24407403a03000c180500c1103a68900040b4081d440a1a110100712814190f0700c100382940f520188080d810307038054005100355000207a03a420a0007540342d0694005180102c40c04c841c0c07215502c0c40300e0310700300001c0307160407401d11070b445041d8079070080c0141c20b03410148842981403480080c215402c5500c80c82c101800c115018000d81d401251503107905c4e801005545e100d0f840300010b9451803040e140e01e10f8076000001041c41115001143c840140d541010643d14940d9880c4400c5042c0d56540000c1030084030100903902c0000c1c250909900e003d4801c1601044040d034406c0703001041440b00c00c0903640c6410071400c000c11071429108080c7d0000590604031019110345500411f401010307400181020400008600c50741e00030030984000c140d028082644d03030b68440e40f440c0d4840c8002e5070720300889810 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 298993363 1250 298992113 298992119
    0x1090308010e0105034b0c030c091302010e12010228050a0516081b06060d0b060105090402090d1b0b030412030207020112060306051807080a02040e03190f09 69
    0x44400c410703041380c03001001044089400790000340c25055040841c1200c0714a92000c4416003480d000d8000e03c06601c1119042031910080c280e07003044400400b0b14401d411644e1040a03503030b291030040e0703080166001140503180d40c0e031006a56000041003e603074005941100e4000414054006202081c0c07034898a4100050300e1140041e4503184030040e2010a0060001c4d003d170501c070381d0281c030521101911442c60f980040d2952f41c46070f448000004600f40c0407400b0100320351000c1017095008041554420510903854582484404d005400a81005000034510119a031a034056511000c002046400c1581152501c9203580b000b080c1e91016040a074107001444a4400082c0c92045030055004804901800e00850003035100744801c0741071240c4200c140e4198010703886035001840c032030000000c0d5400e084521041e655007040700000b007075100030414440084003107a0040001e605079004101c103d402c481c42070441c0a08032805240345c0d4000c85c2c52030950b9205185074001e18180e103a410103561 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 298994613 1250 298993363 298993379
    0x20901050d0f0509010c0c020303030f040f0b040605101401091526100506070503040302091e090f1b010e061b0d0807030b010e1c0201030f02160204060806040209010b091807020109030801 82
    0x702947c0283d49174006000181c00711458444aa9003c1c1c415a01007010b441c0d00d5031a5464110182c80a46e24240d40c1d8082100204100f92400050801c120507425091000c030002003070041240100c01c6000c00f0754101155140c0905800968910140c07141c140d01036040d603030008071120494031090b4040300705000007451309042c411a11110740001c0a14035060460b0244000000064050241002d40142601103203000002d8540190700d848080c00340840e0300702c1231a103031007140d0310100074031030180a03092070980c0c0040c0c900c40001000d1780c0c60354036003004442c2c1400700c4c462515580144e01030310f105a10748540c40398416100d00e400c3d840810076140d105004480e006445100e507030b00312003910b14007001d2507000030107000601d205240c085144103c800314076040c0d81082700048509641a503201d0b0852400b0300072400175040d0000240340b94602900012403010043c410030a0a200004142034603445060f4440f0510101c1c0c08103446034240b9010090083c00802c03000c0d00054811070020903000c2d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 298995863 1250 298994613 298994627
    0x1104020408150c0301052b08030405060906010e0c1b0304030212060732030603280201020c09090c0909010207020a1d060d08040504150807030302060f09060105090109020901050d0f0509010c 83
    0x354041c000441841040120540b0820308480d044034500e002190307d0b00260701600214412440340e406089242400c5501c6032810700107030024219100040200503284e144942a2425100700c058449108510f9285072400c6200d00d03000650000b051003034014007244d000410b98000c2125903940200000d4a92a081001e0200e80048100b82c070040b594070b44160650010b1500700c84001c0c265030034203004551096001c60b0100d0b4023200641c9109801d4155070b01170003000920074041d00c02c1201458848038003a00c4107911070303290340326061240108508000940c180e5400743d9000d0a00c1827007940b03030b024400016030039045480200220100040e9a4200722540f11543e5900c44030084c1800d00344010800501494030743c280301074111100000f03402400f04032441c011400b0380c028200710b00b814100c221410b80014003208140e40035500400441d110700043c1c07411108043c000503110515035004a40314400c02000c000c1d41801d108180c0305551035035004078001c1200000030800300c52039042c00d80c0e0340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 298997113 1250 298995863 298995869
    0x8070815010e060607030f0e090f01150203071101031806050906011809110f01031509020c010c02190807020607081810110c0f033405040e0a020103091104020408150c0301 75
    0x40d01c217008000c00240107001040900901e0b046c8590b0011102c1c0111301000421561194002c00c0c000042003600440804512541040d1004d1481e1070015240c0991040b40b030210581010b030707240740c0d141042d03259940d90960143d20010500c09414000c5100341d540e4401c3c004c040c0f006081c840342000c1d243d000d1007201400c0d42d0100f0895280f0140408000741c420b111002c4074145511621a80d20b15801e1041c000050020108c0040c1c846950310032103821907018a0780070317003558012a050803400c0241c140303510206038042450f070b82d220002d1011404a014801005065000c081517022188a5500c3c000d65a5002074492981440c40740700e0032240b000c02950300c1078090708060304c0c03030f20541017030314180c070aa00000d421210751882d5400b943c0e050319000071b4600200703080030841d12039005031180700d18004d00d0112414800803190400705c54862104400090616688090034003c10411503180703c2c0c45a4010411500c65a1b070305081500d41d441c07003110400b140e40e12800106c0307445607070081c3d90603 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 298998363 1250 298997113 298997119
    0x31005010906080406200706021201060503270a0c0303020f061b1b011b020d0e1e0409020a050405130606080304151110020403150f0b030c0607030908070815010e06 72
    0x1035103a54540400401c2e20000c0341e401202203801b025203c4001400a00840c0d100e00001039445000a074444818541170b0004420084200280038000c01c04c0c100c020b01040741d1100c101000781006002610741049500020041d09070208000f09060b00031558051284040d41640da25990b000d4030842c5a03c06450740381d01882083c0125130340300506c180801e070300c0c14848000103541c00741c00c8182c01200c00305a440c100140d00400340c0c040601c2c1c4c02165215082c00c181c840c1c84243c0340c5805c0045180000f00402c50103650b80c1d402c01c0c415543c0300c0d5421002032101500400003410092083c08050b5880d40c001d40d801c0d41001000503404100000b10340844070910306a0914100b074400c04c403041e8148620402d4a441081c00041066425100a00c000e600c6a414290101600b4030720909135980ea4405100081c901484810030b9100450401761001013180c0150382d8020529040c0c6080400f5000514584145400410b01000001d03650b500141e81c01d4550150360b90321045088154000c561b82a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 298999613 1250 298998363 298998377
    0x5040f050412030e030405060c0c010f0207080a02010c060212010b1806040e0105090403090312020a140a0f02060c2406041b090504090809060a02100c0c0c0302061e070503031005010906 81
    0x1428440d5000d81d00c1ea00c00b900c140ca286c90b55980005125030810b00704c010f1a0341000c171860b03d1668100400320381c485d405002802c00d051800046503240c0b807107884013a05105a410200c0c00704900e69044450300240c1007000525940c4469105e8204d4100380110a0000712005400300c4510300901510116840d01001c10071a0382403406120503174001030012070621049850200000b5800d03942640d001c44c080d40103216000321814441c0b18540d100c0c58004642d000258000d0200e20699041e50110ba01505e10b25a200a03941c0424030300114000c4421040ca2081c00554010300241c07495805424101d40510441c100151840403800890410700c001c220b121204000c00c1c20203402c9010306500845a5900740207021004c248079030b010280c030344c005801070441c064007043d0a2181450307282d40b5241103090224955071b221105009400060300c18500441d544411508609880803108805d50000e6107845261070416503a40098500100c841003080c030200780c551184405e04212a082e548140c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 299000863 1250 298999613 298999643
    0x604020609060705060a0b0a0b0c06130c090c021605030d0801060e0a031208040b0c0324030a0519061a130506030c030601060207091b02070b030c070c03060605040f0504 74
    0x2200c0c5520469505402036001e12050000c941c081c86030034481c240d0b020011441c0030b00c2c1410040c0002c1903800640c07819078184298510b06800040944e8410f0484454114041440c100510280d84a500c44a09517007890300c3c0c070900d1540414018540d0607200c80c646862520741d030130984ca507203c404a041c0028000780041009511512034503090312400360817281c00903213a8032101c608200c1d00c0c0c0860003180b040002d1104021401040c0c030360001e0348240c41802c6082081e40e5195003100d845054090610012040b44250707404e02001120b0b81d030140484100b180ca01d10700a40004040c1001d51b50a8504241442002191540d216107050000c0c0090b2842c40c5004240c001020054412900342c41090140700c0152401c0140a018000507001441041e00c0c26090a080d50a00401d20a02c00d01c5050b000d9422500003624800350350802111356160307a5034070741c583c2a6005544025241e00740a10f0004240b00103540100151030007500c003446600e8000600c001520001d460084c4110381110b00d403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 299002113 1250 299000863 299000869
    0x105060d0308040b180105010b0306030c030703240204080f0c180403080c0d2d15051507031404030620180f01051c020a0908150a021b01021201030b07090503060402 72
    0xc0380c1d025800401d008606981ea51045e400c4500982003000240380000c1405003078a41000001800070b81207000703106050540e90b0703027100b010344c1e8400822100d4140c104031040e051240c05a6000d070008504540724240c050701a507569a01c0c012800b4090039070b408564410807000340d8964441c5815845850780c130748400c2c41c2411294059800102d00c82e64814528109844c41954803074660301080030190841c201700008421182e94020f0312200d0508940c0410840d102d4144c91644039002e107810039112075060400361002c03814071034580c20750100094080100301590703020078000d9120060760700044050114140c098440c14501408030258486088110307e004081121003610602d01030b818203046070550b0310001d02e01c0300c401d208240c0100d495400d81e64004032040c01070100d00024240c18801c6818000304440141090000701c6c0c00080340c02080d00b55101150b078814030310000315617030307000f034140441545421b00085801b01120004100c04a10070100750303090b100010098840c0352103d90030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 299003363 1250 299002113 299002133
    0x7050f030c161b0b04060903111903030504152f010f020a030b0f0303070f060b010315060c1a010807060507110a150e180703050907031202010e0105060d030804 70
    0x6115048402003169400c98000304850b12021403060120b14038402098078215a01e42c0c9a4000c50030ba02002d0004200c050791144104044907041301e040121940484081803010702c80307103110104008241e00002c2010b43c00001401198040400041d0300070b014141295840710002e29010240031405150381c5500d240081100814030b408000162080b003009248140c0e0420140e40d00826a203c40380b0302541061054035001081c214051850700304180d40d0601c1c40e4016040c00340000b42d469483d19003990007588044c482246441000303110035034139040100f500320500003c031004c0b103510b6404d0400104101503541078510f804003500c105814071004851079080103100341c40f030400440144045031507164420002e03081c5081035442403004c4071310282c601802224098003880c007d8940460512400e12040d420003036624003c9142d44400340c0c410725181194002420008201941d80c41c07154055100480503103860000340415500e0900700801d24001c0740c005030201d001c42000400181d10081 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 299004613 1250 299003363 299003371
    0x5011415040209090f0a0609180309090605150d020705030711100e01050904090501020d150f060c080712051b011a0108010308041e0803040305070e0a05060d031409060d0501030308090607050f03 85
    0x140004d64a907842c0188d20540d0403204020002c005400800d1003455031002144e0b0180c08030100c02d0100c2441c00700030500c582d4000c001845900e0300400d8065a0324070725012240200e07084812651210141d0826960700000044d1741f9100780504080d9087c2540207059003091314805031941d070b0400d1984400d000c054000000d0442e441d540c00c1200481303c00b000c2c801c11004891140043d5115410041c102a00c68030581101043c0241004c041001507280401c440c0348903401211080480040541610744c1d005600402d104e50324080000c50b0b58000545c422100d100f61160110321030b03080600107441030f520a000140002100300030500c00d1440361600e00c010016034860244000759035403c00c80c19034001e0b0708211000d400910042012010b00710380d260700249a0041008541084400038150210640c40141070000c28071001d00c02003c0b1605803100b40c04054070403a5038686806041008041c2400700b200800d0014003c41c50340f54001424500c104400e0b1612841c10320215041825500010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 299005863 1250 299004613 299004631
    0x30907030f05060108010510080c0f010c08070f0b18060f06150403030c060506040204050f12030412051501060206060d3f020f0f1f0905011415040209090f 68
    0x480000015428886090300280540007600840d41000c800030309491003c0c0088807400c05840d0240055200480c000654a500300e4005001328003d00058401d00500040a0000d44c2c1c00301e270035000d0200d204180d00b00d0902c140044d091640e520310f61440890f081c1c400000b03566001400150140e50396890868120900030071192440e40c0c0141e488109500c95003040380050031201e00e010802c0b80502803a600a03034122012b60500d410500450300340001c00340d21a104070070300c07040450380140601c22a000f5210b203190702c8080700428108659582000b0140328000d1021800004029102065140c000c80004100d684c86180c6900c030320380700210003162100603c1c17064000c540c4e140da40110748108811544500c3e0f56120900d00041e0801c1e90580c00007055401409555447c3c9101191041b560400c601145ca510312241100c00e0042a801c00002d28079860280410602104107150364807420603582c10003041000c103001d00c8240c2c042c040151780c0004030f20010070220420282c0da240c2c03004d409 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 299007113 1250 299005863 299005873
    0x3070f0c050a06021005060108060609090a0e03031305210f070302071e060f0e1f0e1503010503160e04020d02120a030e0310020316030c091d2401090b0309 68
    0x91070020701500480c1d4000d030090380c0300740041c0820201a00030160301030340900303100c41c4a01c0c000c40450000d10458500034400c0074601d00103441c020050b40212004d48100342165201d14082c07481d0309280c204160155090310401c00c2061031041040c10030481409003c520b01e0801404442100103a00040c8040b170a5000d450310101e00c1c0950300744035603c504c4803034445c175000390b00e48040540b05030100c80002c020400c01440b02c0c0c0c0c49480b400030f070049803040b00c811850f80e01c40b10b0b02c044031450b603001d0216500043c0100c045d001e004c506006076068800840640e4207406800030004020511882061541490040041d02500c0d0100d4481c01c598005088030403c0741d40700000c2400c046c401e85049004c180c05000000040c2010026904d640150680442c03441c10310f0a03500350070042101c079100070152a94020846030f48903c03031500c003c1540d07a00c40e4619541c040200c1041c403408807100209a002c03404c050120004910710041c1a98041e15042e048600f0459846500d82c00180942e2240c498 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 299008363 1250 299007113 299007119
    0x100e030c16140d24021314030d12090b100603062103030906020d090c060e040902030304170c03030309010c020d0c12031508030a090305010b010207050907050a20010207020f0102060903070f0c 84
    0x3034404c000d070385003144400045c1e9913a450000c445c1e2066041d00805e00c507524800020901e0f40300021054002603003410b120604902044e9440b014021800c0010020003c0205004003500381c15100400d50350142c4081c00081e0310783c40b030b400c21000446070030400701d1600c40b40c00d004a03001741e014089041c000c1d100035240000101c0d0300070584803a0001128240003040040018036402107010003c110115014860041250006a564010790258241100c2403102180e9004820000c6908019000d400d80e43c4910700041d00a008011019407c40580600301228104c1c80c4100e039010145540000480074880c2384840c1140240b0011180c1400d850322400b010940c1c010400c0507219110850380ca450b41c10b415840d107070342541c281001150541d40100300500030782e918044556032244681c6400c9480e0a8444011030b4004041854030722a442000d0030030300c003d6810340090408500030b807010304805403840c1c012655075808690800031500709205400001c0d1a41948d14003040c060b0444d4400951 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 299009613 1250 299008363 299008403
    0x414070f0f17010311040c030507090e09031605030403030809030f030c0901030f0216030e090f06060304081603270b090d020103090209090d081f17100e030c16140d 72
    0xd000c0c0c1045e1003010848200e10658a01402125200c0505180c00d208908000c13601a04002d50f6002d081c0791440d800380014000d42c020070030740e280d050b29801000f605070700070b050a603100c1e4807074003044d0005546a4000f9a80140c00000c03214503468500b4102d16540d60b071154074403244c1104901e14101500d91414561490701030003d041d09403151840c1d40f030039a01c245005058a9000d258841c01440c03604204540c0021001002d80e1080d0143ca41503500e0390790f0720f03040200707101d40c00d80225003a60700c01400d401d05038001c2150300414141d0102c807004a00881002c0704161301842044685c002c10080c42009081450348144098818100032072201110780c0054002102243e039013009620002060b0030f01c5510003035842d0000341c9420f0704107043d40780310000400400c85005003d440019072003038010140b0308008181002001c540208500160013610301e0f100d83c8440d15801c501d2050005c40b4040000281094003180c2aa280841010003a0b100348044140c44102c10b80c1c007505d01c1404070200d04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 299010863 1250 299009613 299009657
    0x30b180a0b0604090219090b01031e09020307180501090b010c0203070306110403050703080d0b0105040b0d02130e151009050a03170c062e050d11060c03040806060414070f0f 76
    0x2d0760510301b1700e26080641d084121a00034006a041504011740044039000d102220b0303130702041822001c6460030080c00070914260a9901506964140782a0441003403091b9100d281a00e05580c407c1c0100c44c3d500004407040152800040d5064106000800000f0300950015641414804900d030a150b601c1d01c0f018188203039139006850302c0303e0008a8201e880c002d0f01c5480c200801c2400c1043c1014101560705219009222203420410b9001038089006d462200b02c550042a43c0300c0115038a00c2c01000c650b4031741c100000103c0c041c0d50200300c2c0c500454004c860b014242e90001e460403012525541300d510503005003071745848824104100c07910551006101d001c0c4603950403c0d030441002c0e503060044603004c0d4021009000451010b01c02e00041d5680b0080b014680e4000418a00c41807070400040e026126000d2140054840058002982000070592074480c0c1400c907010803415003411240d80e50340c0f20480d0030000054042010000780c0c0d004080550402c4c00714034220b14001000e0003041c0d454 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 299012113 1250 299010863 299010889
    0x106090207031115090318010e04110a12050c09060d0212160e03060f150a050301020423030109080f0c010902040c09080d030c02070510020c030d03020301030b180a0b06040902 77
    0x40c004650310f44014000c008181c007404956a40c07405514003407400f940c490045c5082c0710030296024080300c40e503070300c10410745410f010002e00811580900a07074114055000121000110701031054561038620b091148500c83c00000c1540c81c0303803100c0c1c0820880c885c0e101c3c2d8049441151700b4880c000700c00003019840c03440340411100a284500c0c03680400360801c2c0c40c1001c101e209900410404c00c15508540c0e880b80c114030500910115982c4550015100100d603422558040d8030100300014408150201000031324441e00040c1e4402d12003100349800e840c021341e0041c207274220800822080c0580c4800800704100c0c0c8000003d0f001125034000707029910415a81000100103507070501820303900380820fa00c80300707076824200080c82228030041d403510780903c1007a201d00080146480c01030b009001201380070500070300399409a012060003030000c3d00700b0300054400c1010100050042c3d072820355014940010f440080010181036503944481c0382004000c00d8005880e404080016201c0c800700d40340c0c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 299013363 1250 299012113 299012117
    0x706020f030f0a02072616030801140d0c0e0c0d020304030e041d0703030806040e060a0903090510080f0c0702100806100306060816050408070b0c07150e0909010609020703 75
    0x14908154a0b200004070700030b400410114410455140056000c840884224500000c1480448800000210580940315000c0c032255040344c07250080562003205207058501113040724074078503100d0041c480c111084460040400c054140140030950705140450707031100c0b400c085a4a40a8800b904a00380c3e001603900302c003c03e40c3e8034402e500ea450306024881106812116100e1034004464000383c0d220302912000c2d0501940e003000c1034807500c0d07540112901c06c5a140407501d03a4180070b04814000c0c007088400754001411000041610715041c0c0f400100140d5030340e540441d5854001c60801c14100c050031038040001d040103854016220040302c004566541d8641da06103107000000c0c0b15840115080303800403d40761800500200d0740040815400c40d5a8010494002136150019105440f4941102105116000001901c0c215200050402408800c00d0700c1c1415134808420741303940d03094000b00c0c01190001c81203e0f020309240080652040342c14002040541c1c2e259a568200d0f4009442940 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 299014613 1250 299013363 299013367
    0x1314040e0d020a031b020f0d0204181b08070602070608151f12020f0a030203040501060801060b041a030705040314010f0f0b030c030c030d080a11030703050a0e0a03140a050706020f 79
    0xf41a0800311421744c20020f04800091580d00360b00003850002000c1c0c1c080c0c0300d004004426025910342c0e44c003040b800c0d0305211004d500f4080301e042c010a000c2d9040401d0490982810300481c08240108108045400f01d0b0003c00c80c0a0603c0703821340c1d045074001c21240c400100344004503480e50b50000c60015400480b4940150b421141d50010b1500243c441c817400914010000c0910001f40801190544030a510b4016117a442c1c2c2d1511501410f056480f00125600b003000c0800e21804540042c0110f400500341199100807512106031240000c4030800c0201c1d10520041021414040b094427646101000014840c00c16050000c100c2e40310200c400051955184011818141004101c600c1e0780210000d0424501c03110000703903103080c5e20b1a400704100100002c151424580e40240100410b1031010984078a03000c074005000f0b05d0216005e12a150400c0100d003440f010101d4040d030915019a00c14000900c10b001407001da92101114a0030050704110f000041105480944100301000003155 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 299015863 1250 299014613 299014633
    0x7050a0606060f0c02060a18080607030b09090114151210020a020f15060d0f080720300c03120409050f010f03060b06070218040b0c1314040e0d02 64
    0x100140002e9401006000c544d04001d80560380340c0082e14407544252400d41288160007011040140b060307484140544109018044a1a05600b003043c9a01098070460b02656400100380e083c2d401030f682031a10070001a01149861584021141802802600401e40494100c144600c0c01e40081c02d06010540d0108003a0849541809800d040b606014014007900008000344038000d180584080d204005030510101000880180d210149400541c1c09854015030300b0710000030820781080d0100540d03840c1c030303103291890080348d80c080d61350000e000c0c00220801c0c1c0310710340398140303112500402d00d01c039651031442c6943d0304004c0e0b0503d600a00d40d00039160342c07420400304240e03078028010700100e018900060102104e009581c00850f5001940400c403c0702000201c3c8452164850180d00540e010003d08400904000303458003481c41007d8020503503541c1c0c0c580660354003c0d00342044050402940c104113005500c4803000001000500000307500c2034a8983c0b51030203c1e039000540150f08825001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 299017113 1250 299015863 299015867
    0x3070302010b0306090a0b0a020304140318040f110306090c0c070f08010507030e0d1202070f031806030b010e12151806060904080904050a060b0315031002090a0e040807050a060606 79
    0x750410369205c01844051126610605504e00041003031581541c0440044c09000c0c13003000300c400c613620f0321080d03943d0395484031080110610300d640b955005034241202c140400c102c91003500011040c5e960100d09548641c82040b00c088000703010004003500a02601102c07003c2807100100410019001c0d28405242540c074038251030005040c01c061500e05081406440d001143c0380504d02841d02e0300d03071205280c2520b00802402901005441d000b082e0100500300360700300500c1030700d00724503070701e520842a6681c00031070584040078800e500085c3e03c0503c03074500e801c20443d110280040541502c41080c806509802d550304121483c0f9504058074204003410503091200540018060b1602d0180781b030701f500e0790b01d5540714220204e40510f07a81c070005000d10305282e0150000c1d16080c0741c80740d501c1c02c2c40e00750301e08074080d4440594440e0142140030510030b5031500c00c0b512903507409801100268640b0100102c1035800038425030390032108100090009005110b502c0c7c0b02442482c0019140e4240100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 299018363 1250 299017113 299017123
    0x705010b0901060207030f060f050f0105040b04060308180604080604051e010e03072a09060906090b090f04020607050607080114060304200112060305030409051f03030302091203070302010b03 84
    0x44140692074a00051005580c04114401900e42110800039112071502d4504014500c204008500901d0b000510002121603040c4c0fa04841d0101e03800d001088404080108031600da1000604065040013a500c50071030b4641a40d03c5a00c0082081e170400b41d07640e142c10304051089604681d1500541840c070400c41e502500d5111096102008014294030140c809569100f081000b5112080300c802010390901c07081c038112849175510300314140440ea542101300140c00d0b2800750300e00b19410118040380140c0d46101d65410ba0350000d1509005803201c1200850b0740070701130410381e0403900400500000c0740c1c0c1008590b0003035440e552192003542c034262524000f90310840c00c0520801041081c4808a07101b00d820304401008900b03480d100d0400e500040c2c50900340e01e01c26400f801e04242d0000203005e40071020f402140c400d07403003e20156030b6041401ca80008454450910080340103003e201091003075010b01480b0501a0a00e000042480040d503e90382061754101d0050f911041c42e0592800c1c140700c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 299019613 1250 299018363 299018381
    0x60e010f0b03060105030c041508060307090b0f060a020a08030c0705010b090c030f07030b280504020a0906051809010e04060f1b110c041521210908030d02070501 71
    0x100e1240d2850801010301128407014007168104000440400e80410310f2104940060420440108842d080c81d00054100101200d0042c4240516000010000e6440c056008a00d8000780700301c00001c078580810806810884692342103100700311403100010206130040d0700039130b109a0100d88540c158a002400e58000d40c1405000c0e94000c400e001c4214680300c29070360400801102d40240b5a24004214018100700408030742c0114001c030601e401c0e00403800584034110409080c42211921007050005034407822480500080e9802d1040000511840181c8410000121307001d100350343e150b000410801c0e0a8010525a0ba4454144010003078548078070b403c008803040d014000d211580b00e0074004210001c503074100741b01088010220b94074051007000625840203008102c0024450038064001c03800f80141484660f0440e044001c9100c10016014170540c4040a8000350811484956000300c0300d40341c1d0821b00c0002a4081803800b0180301904c0c3c5221044d20040e01c60744142000c0307094500c229 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 299020863 1250 299019613 299019629
    0xc04090e0309010905010503060f040203190f060e1602011503110907020d05030604020702010903050d0201050402120705131107150c090f0f0e06060c01050709060f110726030409060e01 81
    0x1041d03600744d80141c941d404031042401d09030303143d42e21034020a03c460700c10f0040a40c0a48000704101c400802c8440d403034540c0ea42e11204116120310320300640e0840d009070041050803007407003002805803a01e00c44030b0b0380b91514902c004600715482400741002c0c03540396081140c0c14a9222000902400c0490311a5881015440100740c0d0501c03145002d090303480080e0425000743c0e0001004001c0d6409108172a00641d03010702203998040024000034000c00701076400320b124020302d80c0c91000c014070028860041d1800180401e19409100340c1c054010840ea180c00700c1c202d44d080c8095808140240004802d203035140c3c0d0007060b400c074054001005a005900040c000a42e200d0040c0f1031060740c1c0c440942907032001094000192542d00c000368090007201e04448196003803004200d1455031043c4403400700c5030715031034410208a000c2d6060300d4100292520b589554811802048104440e440c403040142c1c1c10f92241c6842d001000590f400c5521503080341c1d0000340c58032801c00820310003a1443d80101202 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 299022113 1250 299020863 299020867
    0x3050f07031205031306020a141303050105090a0503180109050d050d030507021902060304060b1f020607050f070b060120060f0c07200a0504020a110c040c020a080f0d050c04090e03 79
    0x39090a85401d411170a0280c02a540815401d03542400b070310107212010881c4100b02c0e2200341c0804000d40d0a4a5400200c0c0d40e54203041c0800d240745000100b03c880d0a51000207141041c000d0150541d4500d0803c122a0401040d60700004003901c8075145200480e01690150005552118015003510009010401103610540941c0ba0f01c0c82281600301e42c050b03046820302d9903500c0e2381c02e0820141011103402c651003882e100b0300d041d005440e030700b040700d122045170265000c0f03a54a03503040d9201e00810b40480501d079002c001d498005000280d602c4d030b0200c4141070a009d900c1c0000c0342100350b10010320780400c00e5071010041c818800c0c0f604d004103502c004071541403440c005031030780d610708219896201500907120010407402160740d501e003510003410014004644811800000804609403076007101454010303500c07500c03043e08141c000c0c01ca222015400421902c0075a0b0345030232161380304500f406004142403090400c2100c99009081c00f8000b0b5002c10740c0c90b075080805200442c1c1858141502a87c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 299023363 1250 299022113 299022121
    0xb030606011d0409151107051c1d030109050318030610150f0e0d1a06090c1e070f030c051618020c011d0303070e040612060b030703050f0703120503 65
    0x10303120324940001c3c0c070003046402c410724040b0020010075214801c607a080100c203101ca10421009004442c0c001c404590a000304242c014222907400c1d8001c90000d08024544860a08280c20b030180302a40540002442d0885485a0f0305581010204c08222101666101c0b05480d081181c01e410641071030008171040e01d0100c03a00301101c147c840313800078403032125004107400e401551855007000002d800e840ba4450b1500d0480c01c16541c0078401c180030104c11000ca101e41c189a800c00303201c0c000130103c1c01d2425400349003881c420700c1125041d1200800c02c1140e030002800483c50407226520944601c160000503107400350030300444800703464000218560070442c00c7c01e06000300540c040c50003001699200359102c8903015040d24420a01c601840b003800d01240e0000000451159045940f5252003040300c1c4204420f448844c07140301c0c20010414900800700340c3d154040740f00d03107200404075040e0a9903550349905104250b40c80380360a07042050200142300c0c010b07110a80f11485842c00c00d01e176140c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 299024613 1250 299023363 299023397
    0x80d020c060d05040507080a03020d0305012306090301110d02030405120307090e040c0302030a03020c09070c0b01090b0f150a0e040504022103041a0705010f060e011e03080301090b03060601 83
    0x14480d80200b4840d1100c3c00b1409002003031229001401c03000083c0e4820b803400e401d000c0d6640000d0805080080d1820000240602e20800c64402c400c80d004480b06003624a20b080241e543c00055031144e055503141c5605011407104401040c00340c90101000d604d9141c641441e03070901d60800300722901841d0410400c019641c0c408404015107840b401c940c1515111030424500800c040c0c4c00080d0540b10320061101450b8000420964400742120318040c103544011049500485030480207240603821401400307041d20b16007009250413005070440e00750104440001c0c03100000720703003011088440014040d40803984440603281140007550140141d0805501280e10007810782d0400001c01c40d15907000c014000300313004480080041c3c40d0041144c00c030315104089140e0068074103c640390f02e44000741560100743c0c01003104136018078488642036842c207a03e810261010002c1c1158010101c80c0c0800018070803805140a0120b107000003818010f00418540b40050260030305052000c0840d0107920a5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 299025863 1250 299024613 299024617
    0x150207090b0a030201080a110904020c1606050405032e0216172a0f01020c0c1305090c010f020309150702010e03010e07090f06031a04020a1403100b0d150204080d020c06 74
    0x281520707c00041400c06041c2030492030180d0341c01540e1003400004d0b0a03e1060700010048620054043c4504e1115910b0000340e46030b01c030710711980d9015003018000ba010f611020104050359031004201450798044110520100d030b01c0544200942c184a031340650500c1b803008000407406525198103441d0290ba02d845090800d1042c21401e848405054020104030040c0001c5160004c40c4000b95150005508070365281c004401d03c03a405035120151a82000d041c600a40d80142c1c0c03134501803d41c8076292001140d08007140341070130b8251b20042008405a481c0c40360404410f9800e522401d4540c1c0103403000408103d0f070b900c3da080c0300703030306080d500004000301042c400211210f139440041c66070f4901c8520005040750350310140000115002181d908480403604510071482110b0990165468903e2a41110000703444117406502614014401244540c800b003000c82e802040410b041c01140c0d10f01d03403c218010250300c003094001c2010807140804000b03290741c0d0001030000e85180d0101d035010070701078 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 299027113 1250 299025863 299025871
    0x4030206030c1c0614010c0c052b050c0418030207052101050115110609070303080a14071d030d02061306060312020d020c01030b0108060103050709150207090b0a03020108 75
    0x103003000070100b5064040c1004461102d0285405100d029503ca9021001495030b4401d41d411001c80b403141a50540c412228054419805142d5800050a200a01c1501e003091086000548c0c10390080c400959004c41007030003003138826001007074402112802d02c02940c200c84840300d1404420180800040d40124076074043e81c1c03090b01c008204407141c071001d4040448802da11450f0794a02400894001038a1039800d4094600745c5480020341104d101495541c82704031407184c43c0d070700700100900009108490040e003108804c10302081d005620f40800410301e00546000700820f02081d10080309010240481c02c400000714041d14100c0c1d01c041c0f000c1e44800c00204004000308850311000200080b6034007100180d46c020540c0190b030001c03000081c3d541c5046410b8500507110f51541d02e2020340c80f0b4010840c1070b443c1030f9115243c0351a0300005401610010700110f082c070500a00c00300305e00c04014460302600196600030b28089150039001c2c0125500100000d004920300313002400503036000b625603500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 299028363 1250 299027113 299027119
    0x180f050c22201305190302061b15010914090706021f0e0a05031b0d2001060302031c08090102040b251e02030607080720070e070225030503040302 64
    0x2034400b84484600d5030540c0156681c8400320003181d84100c400c0300480a02c1914016185900c10309015091a40c000545200095002c0810405000c106101100078070301002d600b01264640c6c26148180e010051098008040d80ca5992040300c45804e0300050854001e0101d50141010302e050141c02502c0304000300c0f480010103000b07284030321268551342c4000c1c0482001c00c251035102e400d030b2812725220f5100920354071000d10324610f0b011031603070301084030040c4140b103031959080b44030103081c3c00c01031041c2d28040e02150f55035090b0000c0980c506001640700c1c01000103020b115218034041c06464800080d01c1400203a10500c001e0010381c510204441c583e00520f020a860302002045a00008044260090032001c00880001500c51003000c40240c8a10880c01c1d17403019a03038107104542401c800c9550344001403e6185c042c000d2000300d4601c03850031b04080c068948164035115440200442554041c0040c2d0014144110150006100c14462a11001d1803140c6600d9a29800d580b40150301003e88 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 299029613 1250 299028363 299028371
    0x40f0e10090312020703050a0917030d1d010905031b010504020a141306080303010333050c041d0a140c030601030c030f0519051e0c070204180f050c22 66
    0x1c103040c01100768002000c5003a00541d551025458014210703048600004081080b43c48040740e1408034481140041c244c04000b5400c0841e50017003200608003020b4422029a4800b09a40c0844001e01034100d50a00800056983e40704000c003082e4504400310003070303405034588400d200059680780d80c0ca1080380c6801d0300e030154403034400000400380b00e48240704029162410b07000084602c1d0101c00b940c1264010700681030010340c00800c0c03010320482c00c0c0c002e2810701100703c038503185104103038030560300144020141c904260b120310f032054103a03c0100081d003520304c2100401034140c41c680201030030960380750b06205440c1451400d1110301c0c000907242c3c505141c3c035002200f9902d03100398400c0d059000c005d00300740440c3c144803c00901c40d03c0000c40d41a04581000009404608480781042980c0c400b040b80c104143c2c0c0c0e80c1c055090903001100b04a90240c2c5492206011820007030391070488600500b0000e64034945450702600c0c050200c0c54080c01658060300c407264500c4c41119001110f82400c101003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 299030863 1250 299029613 299029631
    0x110703020f1c0f05060601110c1302040b0403030216050a120f0203011407230a090b0715110c01060608010b0f0c01110c1e030301050f130603061a040f0e10 68
    0x4140580c0a0022510b0004070104801400034108840307028501030010748480f501ca100044a400300980d80d40052903100262185c02400e121152500d0644140d40c0141000c1e01c2703480c2c64020340e06c982e2058006034007210740052072800a0020200408080b2140e4000c0780c900441c1c140c009008010280c6885003010f215810364070701790412070f040b0014001c1440b00b40f8040c100030b070800801c0442c038050305d035210b4100610054602e04440785a0082c0e1255000903180000301c12941e80300880480d10900c01010078029a00c0c03038001c41c002c8040c01100552910710310f0a8090071184558070580c00c002c2d41100402003005414115041c42132800503a0365034042581c038441c09480b21000071801e0b008001a040003886000c98070000c0f40d0305d5203c100110400d100c00301944c0380001e000b1280c0c40103240c0140515481c0c074034003151074540c012101040156582d2611003c842c0e00802d0991048035003021101540b40a00c285461418248010403101b044416899074404907090b10288142d6a0a511 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 299032113 1250 299030863 299030869
    0x80d08040602070803070c060c0e010e0d03030f14010519050135010801020307090602070503072d090f050a05070c14011d03070203010b010f050f03060a05030a0308040b07110703020f 80
    0x968049401c04c00c2c0c1c2d5501d0514045c01840c411601030300f81d40c602c0c41c00400d07101103442a1107188221320140c0d100715084101004011041e018050110180360396803d02d811056941c0c0034085c0e250704103894151403585032500f4480c4190f02ca00c0082c40c2560028400d124580c4c000c0e03481d480754001000303100d070803440307110041c4403041d4023268107901c014011000280d0400150001c500c02d80c12940c440601c00da503804180ea4529040c024a84c0c035800c0410305201410021000955040507a140c4858410080100d400109002d8008202803a00c03180e20100c1c3c3c4d0300601074103030010b40c110b40420462806400c01400c0303075115540100710200440c08080c80200c25001203141d04640e903014580710076807080d034541e40c0d8041d5100301c2c00b079420a064651658019650407500c0340031616418a46002c5803040351056000511696200c46042004209a1020010301408611a03194110075040c0780c1001e802d0784c00c00130000f204001d03120350011511103011526008407581592140b0708541c1402c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 299033363 1250 299032113 299032117
    0x40e0411040905100e030a021e0106170606030105011401080a112506180302030d0906090b09060405010e03090a0e10030b0408121b04060c1704140f040204080d08040602 74
    0x48950060a120000c02801004648240148503901c810086076240307001058513401347d031000c140540c03c4040c171150b800039106c0315070482d4155040009455601e40c1058880c0710200300c500c8800d54010001c018150500b441268050304541342c0140c0c00c4901d9000007840720400410189903180c980d03041c941c4120382e00c0e0540e02e221080400c0d220f40c40c65606035076a20030b00341800994541d030403c6801400301c40081e12100070180c141c1e02039850440302c0b82d06031000d40481d0b0740848029a40327141d01c602080c0110101e6000c0c01400703015108609090801d1401d41d91440c0580800d40c10401000c00c1554480b14800c0440d8103900b075142450ba902c034038464500c0c0d81940050410215081080100f02c607183c010541d22051078071001c503503202d1240302500e0401c00840c0c842418001c01050200a00680c0241842d0748904080740010100714102c00036504554401d0200e40d481414041042c80c1c52000b50303403112001c1d941141807a103401d40290380d07580f1f040d8a020a105a00c4042070503c086501 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 299034613 1250 299033363 299033393
    0xb0102150c1b1c0e0a0311091506030a0e0c01030c091511060421030605061204290105040b0628090b130905010605092209150c081b040e04 61
    0x3d0b6001c40c2e0b00041c00c2e260342c0e0320005580700000c540185800702450102082000d80e6000010f4a4031504810f00b80144800b000e030071050f02501d440541080f070741c1c949004600c60060050049003107085080c0075850052443c3c00c4d80c1c141800c14a00000d15980b2144442c00ca0782c0c569040d00440b40e01c0c000685100c4000540c0c520a800341800f08014402c000f20610149a0100080c40c1043c14200c41101101c41078001c15a0217007081000c030b80d0380c643d42440d0941150090600200c05207861604c40005250032465003550364089004001c24940b0b4400c0424068050302c210340340005400700e034600c0300c00003418940c07030804803843c50001a00c10a0094041c06000044550f00d407211104401c80304000c0c46030580440c203240007c54810701c694140d0f03952480140101c0c0729420740c82c0c0c100c40107252683c094900141e80c1e4554502049000700c0049080c00c90020000d44040c2e00c2c940102268070040042c0703900b03a26144401d00494449040301c0803503007038464010803a00c07a45480f903c0c55002c42 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 299035863 1250 299034613 299034667
    0x203090a06051e040c05090108070b0a03110405030613020a090b061b0f060f010906060e030a030e06090d200d210509060403030302030a05100b0403030e060f0a0f030b0102150c 77
    0xc1c0130070041081311000306040e1102110024010380e41c607643d650b5242610301558604010a05c0b048001c1030280e007041a6040401c2d034014201526000400c0c501036040318601c410b512904841000c0d41412104100070307000e003160900c000d00c500c4012580d0361064511500d4030048203915182c5c2c2017414427001c41000f000300d0568480d820f21800c915180b900038055480a2880c04034002402400b5541e44c21000c403024000d40720040c0b040c2c0342594040810324100c0d42203442000382003501e65550740e49000302403080c2c1001c1c0c0320048a0048028036819111054025815407201d130700172555108609032030001c07021201802ea414080c003240c0034001d168040b9006000810080708054144c2c000d10b20450303070410104266038030340c0c10745e048072a100d100e0128400010802030000c40d210b610900180400a0310300b6260400e00b1138141c1c1594080410103000030005060818640d41c140600880c4100910003491002849101058100c20207000b65008060001700d11803080c2c0b80a080d0201c09040c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 299037113 1250 299035863 299035921
    0x2030c0d03050310230d0c0b03012601150b0703050724051005150919030605040210080402101b020a080d0906020105150f060f03070906080108010203090a0605 70
    0x78a80a0456081541d08000800500c1030216419400c020240c0c0101c030b80400240108005106021074180c2186065a07404070702480810f0046900009500070484000350a5400d0140086a10b40c030104015142070b0340d060446032140d0060450030b440550300b00076160740e80c401441c0b030159100e01c1100030050171220008180315050312056042501c0300240a0144120f540d40003220100381400e01030154015104c1c241481074200020261000c1c82014120f410450309143c441506000b440e81b0440340700d07407500d00700811414021a0411094040d040084503030030298001881c01003c103141d0800c00600480100f00c540c100c40c4100546500601072810298945c580342d504c80321002d16400100d2170703285001940c507105114491094400e1044005030300152400c1200303800044152680c0f00a052111105041c050402140920081e840722140c49203858005800d090b0305a002400a074414010010f1001c1c000c00e84550fa15441100011650b40e0410381500082d0210300c181404800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 299038363 1250 299037113 299037139
    0x20901051c1508010c1202030709030213051b04080d080a0f1a0102011802031c02030403140102030f10030b0a1d0a030c060b040516110a1a100f120f02030c 68
    0x5280e004076000c0d00050b510900e4580c0b51140c45007070b20b00f140710250003c0c0b0f00060b20450504a0b6020b581c004a262a003450000e0380d03500001c02c01180c083c0b109080f42c2d90b950522241e144000ea44441c406541414035003081d18101c010b5407505c0c140c54908007409481c00016140b040315a01c1480e00c540c4407142044140040342c1000c00550b552481c4034003540c60000411a100d2004c4604d1050680c010001c1514009100d01044d10b803204117040401c2d48030a010200000b02c58403514103080350130800044c0c881c640004891035401001d0107480041c80250001d0010032500102964059180e150220b01c0600050507052000e800f441d00071054000c0172103403420154051b2092140c50b026560900c85403403110100b10440300144c1e100055603030f507044a1302401e4041c131842550380020006440e03048155031034900c20451800c980b0781a0b8001001041900561022600c014100c184507a000c454141f03c4158540314540d400649104c032000c051008540d8100700c0b4020007040034010540e0965 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 299039613 1250 299038363 299038417
    0x11d030901020601060206012105030403120c0615150f090b0a020708120f0301050d03020309060d0618060303021b0609100206071b11040203040311061906080c1302090105 75
    0x11605049006000d0f810000030454800506c0301d0503681040621800421680b061010503101a4030031140d900080c40f00002041d48040c80700c41030b000d20380350103d14104510f058004c69524180c080b40030104c10f80e0170300007000e503c03107031440003a014104082102030080c0e06642c9100b03075620440c82c00200050b10b010f95a80410940100d0b201c001c21078000c601421125003982c0140c8144041d0b00b4070500042165142ca43d00441e0114000c2c0182c0b403410f10358a01091296100b590012061030f00c0b81410841c9200904c9900c1051624130420001d040c1140d900a4503400846584042d040d03440384966881d98505081f60161540101465984400e002c0003a48521044071140c0105204080c80f80000e6400710700710300780c2c9034046041c5004107c2d410412000303410180090b410800c21003020800c01d90f0030806503006022096030008800360b00c01200098075019004000b032a00310024048182d141c42450714084080f85401680714a803100048440c2c0c0106d8501e40010300389282d02c014140c07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 299040863 1250 299039613 299039617
    0x3090f030503181c1106010333050108010510090e060f07090906170d0504140405042916030207110f121f0605011d010e0f030709140601030504030207090e011d03 71
    0x100032503d407400d0413002e000b50305807210402d100c0a446c405149a4681c0503c0f1608105024013645282702d051019001c0001d80484900360000300090b9502c4042c4018804003016060051032883c40c01e00c1606450801280c0b00c490241042c9148d00140d0042045580a50040c0020b42000c600401610360340e01f00140b40b0044083c00b402c000d02900c004075100c24030400450b4152070588848100c0c04030030358140802410300074425280d414030380320b5101c45005000c241303030f00c0800c031010031140c281400000c40c103444848626600915104000400c00601203c20140d40440101c5a07240040501c5021518031040c09008100354010b60b002c10003016000e210b02010150041030400549840e800159800003031941d110340e0324100c9051020fa90341c440c1450281d200c1000d0182500501e100000c24035108098000c003003050f880f4003540400c190480042caa000c1002d113803d02060809880c041c0d00c1e4a07403401030318841034542d699240a1802500700b850502c441c01e80018440519620361500c0e030b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 299042113 1250 299040863 299040913
    0xc1002070509011d181903050d061710054303020703080a0f0b041b08090a0b1b04030b0408030915010b03010909060e06012403090f03050318 62
    0x40500308004203000d00150213003018400780d41d001c0e20003921540000c410896a80980d0710300ca104078203402155203a03140d520b0850902c41d44405480d940004039110641d0f189401400802d20824051600c1400c001003156600000c40300000380d90b00d4204220068081140810428180310600852046804d095266000d105844901c0c820501e01c1c2048050307105160f800b60005d25500301145008801d903001441ea264081c07800244031211202050a03101c2c420302d480b0364040c00c2181007100d42d405c054080d41c000c19030301c0504120400b0355581208040042c0c45218440842103010502d01c5180c01180e0286030080c05080040c0b4007890484081c1d84101c0d100d0901c0d002c1d035041e280f0741688680a07613043c6c0c0c28460800d821682402003640c014424028259041e645070b540c8010f102d4014040359020b0402c41d6400b4000b10019029038250b268100ba8120405146c40346480128500100d40c030341d04c0c0c0e814038100b6600c0d11480d00003000200c04e0040281d070703070003200c41102021a8417141c0001c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 299043363 1250 299042113 299042119
    0x60f0b0c0709090209160509040c03051801021303080306010c06020720010e03071a04030803011503110307050702010c0f02060a0f081b0405040c03140108010b040b0a180c020c10020705 81
    0x1d0707180d0403508151103c528000b50011a00b6011516400d00d0500740006003032a0701d0605d0030b2042c4940002e00f590030007406c06010079a43c0302407040c008007070000c80d135120007000000d600c2c0c100100d04042000e021880050880b10b80803000c25400e031711401c403480100d030b00284107540740c00a07820075003ca2420500101c80b10142e5440342d011550241d02000303e503941c003c0240490501e0700c1010170a003445e0142c032200b41502000080006003031f940145010300b100040040c0e014080800260444101e189803c1d980d04c002c0c8204121160300c40c04079a43c1650a2030400035000c00d40c03500c081c00d03034050300c0c0c0203501030000700300048041c0c0d03c1007030351741e94208603950f20680f6111200d00b001170b089242440503134100100014015810319400111400056190000300c64104100300d90b4005d00c00e8103c01800c0c3d44420700e80e0352034942030164000d07401c42194404410b43c40c00d03100f541c2c05d4008110040c4166210388510580900900c00d056088101805c60301c0000c015000081d15640c50b4010544 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 299044613 1250 299043363 299043373
    0x20a030c1e031a0613090b1f2706090e0c0a050f010e0906060405092815180f050c04050a0b0702090f090a08070605010303031a0609010f03060f0b0c 65
    0x2000024220080040b00e81041003107a4450954502e0404024010120341e001602e0008840b4258440d2003200d000c680500640303e02803e1030701d00304521015058004004e410417041c24000303030091040c43c10010540003c812201036214004c500039046a03031101c0501d40c40d054a2684c01000400c03000100402164000d4080707032038504200c8020900e62103e030007d0540b80c889141420f244000a40049005018608065503600040d0300c2403012203003060840911711604c48840740100c040c910501c640d40050090364034540c0390800d20b0425119402c0807190100610f01c04d13030400e43c40441c407110802c9051100e03181442100b545684a0310441c3c4c010504508002060340d020300a45d0704555000300b4105058a803050010025103003e0809141405000300d0200014110381c0244209032081d10701082030740c50b5080284c11602850b4107010319480e440c0300e0122689d1004225600741c002400c3c4044407152080c4e00b10001c0c030b0150050945111030300c42c0440d001e0700090107080741d003c0c11800c0310 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 299045863 1250 299044613 299044649
    0x5062514070b04090e070303120c11030c07080f07060815220b0310110703050309070f0603091a040302060a02210c09090105150f030a0207060c08070809070501081909020a030c 77
    0x180c2e1880030740700103000034801c4510301c009101281c215524180a5207042442403001199107801c550dc503c048050716841600100310b031800c18000684900e40da42e020303001c800c0c0760400241c088407005041c0082fa9602a03080d199030303a1125040c4401c104c4000c180c24041e40010210030040102007001482445402e203140d010340c44900442c140780c440b03c1c000d0307410490295016166078102078041a40780c000c09501240e03c2c40d08840e940d00801c1c0c3c503540410301c10403a00344030318440c05a0f1510062481420708010200c0e0f0001062900680410f000690781c00707030416070982c8042500d44c89000400c50000f4030049900c4038003d064a00c404030b4044030070ba642d540400503602c04840b00508040f20034072182e2803a4503804003442c0d2058401c50302600c2c1c840345035210412a07030050f88100c0404c40d0102400725459004000302d44c03204210000301191410701c0b0010342402401081c802c4102c02002070728940200b03070b0700001c1c4050340c098050260280c980c60034558020180c061940e200407007480f40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 299047113 1250 299045863 299045891
    0xd090504090305040b0c0a020303030901020d0b09271c12050c04081b03010f021b0705060412060e19050601030302010e010203070905010806360105062514070b0409 72
    0x80c154a68180c403804d01e014075012021043c1e401003502448180950045100980ca050000f18450410f000c001680c40e14080c62143c1141d441c0d460ba14040c2440508000c3c0308400003008002510680703014000b01c0d850420080d143c405680700120680e01c6450b2018010340d00001c883d49003e40d07075401884241c0e910b000c2c41035140203511580100e5489102e05509240030307001810301740c034401740c00883c2d400c55540c24401641c0c40911051072945c808400444000c1c0240102c0d405440c04903100e03440e2a2900304903409031140d2031005010256a41e1002c80524020071065508044482c03000140c52103074105143c84201c01d20080d4059420711540900840d810720842e841b5076404c1e00c40b0343d9043d040c80c0044410610080117982c10242d107006d24210404401c6441059002c100c620000184180e0710b0010f205d10f0603030116018003421301155252400090801f40310080006011440d6010350810589884003440700501a000302440862104d9006004100396284008103009010301e082813 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 299048363 1250 299047113 299047121
    0x71a040b010302010809070b03010e061804050c040b030a05100b010f0e03030a0c051603080d0e0102030609040f0f0f0b04170304120f020304051c020109121104020a120e0d090504 78
    0x4010039560305a401440150700400d4402d800c50501d80448001a4886140106a40c001c0c0c119141d1041c40c20308015161800c0b48611540b02274107040280c041c00d00c1d50b9410ba9500f0002c0c1c14511036615240310900360707201000343c408150b410000711000c0b1702c1c03100403038401031011070042030010300700313025290b01c4501820192240100280085190040c4441c0890388100907100440300740c0030303001426100344550342030903000e0740c0030b1803d0b541d45030900940001103c40c09500490310784d0061040122a5480d484032a90103030b0403640c5054075550501c2e01c6e41d040759100400030b080340340c0c1440039001c2c0b0404808091086102c2d0070b101d60740c8040000c0701441b50004440041c100a100001101010b00c6440000c00c0903035580100c0c0d052503200e1000030b01801c48100d9500e507140c1e8a040b80c106540c0d01c80350010091a1010000c0313602c3c0116150700a41d40013080c0030500880e00000c0b0740740101d07c075080f0320b0340d0107002c0c50040221010703e9640d15102c17101c42c0a0940051a490408038241c601882 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 299049613 1250 299048363 299048371
    0xf0504060b03010f03020f0a1d090d020f0a0618120c0515150d170a0c050705011412130c0305030306030114090706030506061b0d0206070201090201090b0d0603051002071a 75
    0x151202d0213614550070002090f404e24440c0c3d80121816000041d0820100c45082c1c142c0402010f4902526050f0360061071b2850764000d281c11503108002c481541840070500d0b0b2442c0c0e812620108a05c0303200b0003c0038051812580c021311701b00589090703480081e40b0515126009200b2001d58400006290503840d807084217507210754459031800324043c1c6900d0504881100c1074403500081c56042d0030540c011529402c41006000403507501d5080604000d02844518003900003400d0040c003101704100c01c0c41c55400350842040351a1070b00f03030200f907520120090100000c1d5002e0040070b0255101e00c0c20b644c60b40c02c181c5100d0f0180d828211500d203400ca01014461107004444000c1c01450324088084000d418080c3c2020b80dc031200f042406c441d80395140180c2080340074100104124480c20300b0003403401000074203480031a45009400c0c00182c0e801946607049441259045403034112440d060b07001420b032640004d0880c41440c1c4c2002c8400c10a030054083c0768000c0380d02503a800120381c40469401d008403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 299050863 1250 299049613 299049629
    0x503040c0e01180f0b03011802010e03010e0d050c070902030a0e06100303080a090c0504091217060a03080903010b030a150c08090a030c030203070b011d0106031401090f0e03040f0504060b0301 84
    0x10010300c5628607980a13008901d00100b000c0b0304000201c020a0848210914292800a040c84d00301d0a40d60860040c0e046444107030020400200304c1c040e401e031600365001a12040000006103032401140c1000584003900054104550b00d0600101c030000801c03400c0c02040b20384c05104001010a9409031000d0107c94042d100d0b0700c610795680b94414010840510100c5094800c1540850349031500d1050025440c400c4041c11100703448042e010349a601c4400c5610090004c220412070180c1307540124500f200d0344402015120480ea900007809014244403568051007011450420b0020103c8c41011102258134200018801c203841103d0004080341c1e42127040e80b119800d071001070302ca5003c1e04255070107841524200450745d941c801c042071003a8172005104640340c9075410301140189201d401040d01d402c08102c2c400c40904400345400d01446100300e110794840c500364204000380c00c00c2d070f412800b810980f90340f15100d0320203011540709409000d000754a001b00c00f16407619220100c9060391020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 299052113 1250 299050863 299050889
    0x8040911280903081309020414120601030312050a0e060901060f050a0501140a020a080301090209040c051204020904050f0f011509060803070809061e0711092806030507060503040c0e01 81
    0x55120354520382c5c42410704040304485032100003000355251000d80041c200d0b80d000030507101e4000e130400110344200c0f40d07100c504e80c02c84801003000030b402240c0d1503202902d091003c01c06645000f501d0000b402c4d6128004028000c1108000d031051040d0305c807005840180b020b9221076034940081c8000d051082c00303960301207604245003510810b00d000181c011114644111a0709401c0c590302d00d40713190000c0e48a01c100c9600442d000f0401d10b4540500c0c2800780181c601942490b8030303010b00340f441d0a800341000c1d0044078540301050600c41c06000c0005e2007841c0c4011a503100150300d0500d8024004002c07021001d01c070140012076684000c1c002c00d000c980c0c62200840c2050030700d4a41c0300c00f40d03100000296100078204032680f40028105400500180f66140072504e680d65800d100441c0e003500c00c90f940c403c0c043ea00c10020703041030380200c4040b95030042c42084c0318000c001c03182d1030003405160000752031032151140000f2815400001141701c0d41c0728003000e0500b20750300da10700f1034165000c0c0200c402020710 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 299053363 1250 299052113 299052119
    0xe240a05160504121104020f0a021005040c05060a0e042f1908190906020a03200a0f030b03010e0c030f1501050103090f020a090518070b0313080409112809 68
    0xc000c5151549405903a001005c0c211210001b012a448441d21492000d004200c1c0309025806004490503040200400d0045140c25a14003922100314004c0610500011610103840c1e40b040703241a0701403d010304100084010340c840d440d00d83c080080103c28a03a50000d0000c00b41e002d03174069602c1d13100d110341000f10205803104e040d00c4c91200249880710b1440000c90158982301d003402040c21880c0941c9006130b840040e1000102078804845460955081007010010b440061004403030b5a00100d1520b4004c0ca4415942100074001c002d441690540c00d1100a2103522004034a401c1c060100300c2c100d0300f410301c1620324592500b0307140781001c140c030f403180d0300401c140c0d4041e81003601c0d030074420001642d01c0010b40d0b00043c0c100c00540c00c41c031052382c1c1c1d0b0003c00c004503046068400020403990001d0486030301e0f01580c14064400240043c03035544075034510804007c4c100043d100503048148041c8105044100e0096094100740312451035005007032881300042ca00c4d0000018800c0095841d1150582 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 299054613 1250 299053363 299053379
    0x50405150304030c120914010c02010f0305090102090a0b21070801120f1505010f0f05031f0e0613021302070b04110307080318040b010e030a03030e240a05160504 71
    0x700420a0f400d01a4010340940007501d5020190305c1e080142d1102c0451b07a0400200802414401036228140300309000d52202503a0420b41c469000c0079030b45000700c1c8540d03800886074064041c0f8040c2c5a00f151010601249945807080a441c00d078807100d2071090496030065021540cc902503c818003c12140c2005025844000200419403130040d080482d890300b0783d44c2c1d1006180041c8200b8006196110f005219194071013074a0002001d035080101c103100e00b410300013921050800c0001c0380c5681e181810352020000e40d000440f40790960401c0c1c4403140b07000c008000b244448158200d10803504418100d81c1402d4a100340c070f0216800000c0005142d889507603415a500c842c40030319a00d44282800003400c03800400042c1410140c410105640d900d0450074001600d14121042d0b06020520200c080c0d50b440010b44003810300c0d01850b001c224507295080b42c0b82844440440e084945c800c80c06450520030300f0a4a050051550310004c0000d80d54000c5801e4107034881a44a00001d03d00300010021a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 299055863 1250 299054613 299054617
    0x170a0c09050a021e090f0f03030d0e1c11060112080a03020a020f0708150a050108031e120103060204051f021207020a230a09020a140a0512010f051005040515 69
    0x2a008082c01458001d510390603241c0b412940500380c00c4182e000070440c14030304151070912003210064410400c02800280029100d01801a1400b00070381d03910032903101c1140c1045010341940c410743c4c19803010944810003c11a441a0020b4601d03889117000015040e40c0e4034000f64551034001c400b01d070611085440c1200031754444134070340d82188250f01d05414840402d104800060800c0c03001442003895200c0c001a81c520300602e690804c51414004004141000c4111810146941d00400d02c0c0785c0b084c0d41702045c502903002003045d083d803080004401c0041c10750082043d108111280202d064041000c2175000d00703903030b01d40001070704000070042044803104041c0800b90f200401c80c003092600c409004050145241d0b86076040101801c07452203600b0b01c0c21201000d131480c02425854954401000b0b04001c5403e54412030900000403050380a52240c0150b5510400041a070403095a46640b0076000c0d01007401014880c0d460232402a000601400c211811900c003c0c0902280141200c403401c856 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 299057113 1250 299055863 299055871
    0x90f07060c2a05010906110303040201081306021c0513020d11012105010e0603030c0c010507020402070618060609180f0c050307091e06031a0c041e170a0c0905 70
    0x528030380d101038640009840a0b100030840008880110301c0d0100040c071500d000d0780140107022038002c0e030035071040000c021203900a0b02820100fa9a459120b001e6100307071841074001e0080c030710200d80b200002141c0c0200d9002d403081581c080c032058807000031036034180400b42d60003035100d001801e41400081c07580c8150f08820505041a84107164011481810108180d0617241425680c0006102d03101b805840503400001c22381c002c40c03d24072119282d40d5100546106141031100208241045558031780440b11040c2c0d01000a002d101500811314150303031007015080390384900344000442c0d0107400c0d2041c91001e038280c80b0000002c0301151141d00c03040c449003109440040c00d140c004152900d0407c05c090041009500000791843c101052041c004804221aa011401c00d402000480c103481c00c0c2c00d600f0340c1c180c0b0200c0000d48032042480700f0303407141c0c1d80b01c1c20000b06c4105079210301c542c8220142003251505a04420f01952082d03009440d45100130005244092128060041c070503568130041d1300c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 299058363 1250 299057113 299057123
    0xe07051e160606050312031b18060714151608090a0519030306082d0a0c0602071805130f030306050303030f060f0306041e031e030c08090f07060c 64
    0xd00700c414004001031031400c103026503070b05490f00010001400e00300042a025841101168154140720301c10446814040104404590021800c2e0500240080d070303820710b090340200080d589030300324a4050628000c901c81e010050240d0007100d94140b00782c83c07045100d83c1c40c080c544a41403011080994950b0700251021009200d00321141c07000600401070805440d60000007041c281000c0d19004007954216001400c03a608502c001101b420f40b028032010f00900c1e032550071580d09101e0742e2000e141042900000c0c284540001000403c60f4003c940e13001a20dc40e440130b06001414200000c080d242c00780da10341d003001217115000303011031359588a003031045109150118013941d50b040003924680040c2c40051400c01c1c810180b00a900d04141140081c007410360240409140607210b1004000034050354001c01c11210b00040d081500c600410380c8004840000080401095003005000b00b1f54070031030f40003180110011420718a80020403503040b007031402c010000305081000840301400c494504542c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 299059613 1250 299058363 299058367
    0x60b0a0e0f0a2f090d0c150905090103030305041109010906090b0102010e0c01050a0c060c1d032e1512020a050d320a05010b01081005010507080c0a0213050403020105010e07051e 78
    0x390755070308444014850003040c280044e182041f2051a0030348000030001f062048000301003220b80c8035040100c2c1101c0e01801c000032281d8032b034144104650b4031014519404000c440003c20041c005e98004400d0b6507500404118421298005a01300ca004118030221540310b414600ea6039881070000b42652200383c50040003200700b03a40c540c01924a96140000821503061340c1c1484007020304070f2052025400c500414a0b8044190040310400c2d622503410500c881102060b0400705058100c001c10300d401c124502030840d07803508450542d0f1a5254101d00c01c00c010640010f0368039000211042090708010038016010701c00101d00a660303420759030414043c04450400b41000d10501c800c0c0d82141c003650010070950b500e00c000520000000b45240d49010701d500c01805aa6404401d44204560149a0981d2484c844080a10305050b9103002544060000c0410401e40c680e9004240550b200780c00a02043c3d0302d030140d400300158115000000103d0504c04205900a52280b0b12204115440294 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 299060863 1250 299059613 299059627
    0x1506091f03090b0403020f0d030c1b032606090a0b06030712090b16180f03110f0405040c080d050406080c030a1122080a0201050a0c060b0a0e0f0a2f 65
    0x65821241181c041c5c4c0541c105002c0044021030078400011b0390040c0f40341c100100d0012000182901c1c00c45002a4030740300d1142004402c00d4056518404061001d203601d151050302c40805500a140403035140d0302410340640401c603411750070701035040325060040c10310b030460340c80300e408035007039048600c90461407038503021b28101040e030245095001b85515104844d0011801c100a042078203042110040d07814030f490104030700c03901d100030744042d698400c65201038a50424005800240b0204225902a10705820f1008000380c00d5010703004c646c0c060f801e403091022922000d0342e01d409584100700104d2031480c0001c149101e050001d5503c425855800a143c0c2002d00c04500760350401000c40c0000c203054045801e100040541d071100400078000185900d48641d80006c16902400d50b2803010b008650038000108403144d0000e807462440a00f04107580e5039100001c0c021007505550f48110107a000001c1491b001041c0200304451002000d9101014401c110541347d8460354524100380c00401e010701c0d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 299062113 1250 299060863 299060873
    0x80d051c0609020f07020102060708010f05060d0f0c0e030d020619020c0f010c020c04060f080c0907020f03071110171503030405030316030806090f0109110c030c061506091f0309 78
    0x150104e0010580d40c035444010380d01c00a0300d8044081c005030280b01042c001048080141010b44083d10700548446448585041c280e070064480c61004104041c06c001185201a600200070031000c40106c0484403107800c2004203a80f82c600544055042480014203403c03403442680041c000b200d190340c100c0e401c3e8803403d0705442c210780c1c01c01845401608000c4d0160001d207480d01510002c0d12118140c60140351800d44056591460061a240904549800902c1450003404500d5000c00c155080c1c0750ba07840d00e45060180040b4506442e84134450287c2c1c966001e9102d0030104e0703100591200410916260070b14442c56801010300056450303c010800031407182c4041c00076101125190201045022a030700c0c0207400407100402c50b81c0284000c60400c000003801c1040c2d01d0441d40074031400039200c100800040c600384038154492180d80700c002013032804840009a4144a02d0010403422202010003003001a203200341410650300c881e58103404e0303da0b2900c0502000d0011940d04000461191994030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 299063363 1250 299062113 299062117
    0xf13151d030c01060923040f0f0c0b0307021501120f082a060c0702031b01032c0d1b1707061805011109010c0b13050f0706020106080d051c060902 64
    0x8407016511081304100d400c08034010b0002840300b0540c04202011000302039070081200070805030400121641d014140081446c03000141d50f0403111001107213403542030120956005a07100740052007100b85041024030242d2140b416600441c41401d02039280e41c032074180e00a5801800d450800c0e003000303030041200038401c10307803000d06d180c04440c1c240d007150000c41d0741403900062900c88003000c1008864016500801c0c2c440e642d003442400a03003010b103003d00480c010115000b0000c010501c4c030a410280c00c0202084040c600b0a010891f0140007035140304449181211420140e41d103031091046000400c14108200844940d4024904001076030301e448007964410a01c19007034001600644007401400e018000d15480324074102032600c80d5560008104d500300c0e4001038841c50500b400310b11448440c83c034404d1155080012140300d0803040401039107a501ca8402c1d000503601c0d2000c0003480d4080841c00408080c81038580741d041008200c00c100c1d05141e06601e02e1081e0f80d0350400420404c00e9480 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 299064613 1250 299063363 299063377
    0x16150c14011a031002040806070513050901060c152a022a12150105090405010b0d060605010908070305031902030c030a030605040506090f0105120c060409050f13151d03 74
    0x72903880b81c4080c1000341420f03ca11100000280c9004010500a2400c00164660080c8880c82c006a135080300c1c0002680c08025500640da101d031481d0000540d071507024100160841c000c0c84465005080b00910b0b404039280961340c0c4040d0321500c0c880e6411039404407048588040d082c0142c40b08a42e041e00da4aa030300c09407003030401405900341d8501d22541405004015049000c2000b000b400b4003032000d4104654052090600c10342e07200c40041d08010081d041212441c02c044c0000d40300b15101d14085002c1d01c400c0c01001c3c0041d10018000030007400c0060341c1401c490308180030f98030b4151112510080d0450178016502988410030415000940c2000100f990071b0300380d580012428244000c1105980010b40181d01c12420102400ba0700042c690318181103500886403144140504200b86007002404042c103036100702d000c01c000a916082e500041e118140010a0150070340e650b8000c0038201d40e62500107000074007451400c0d9508c280590040121018441c26401d03d0849404480d02e540e0042c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 299065863 1250 299064613 299064641
    0x150d032109050f151003020d14011d0615011202031b03130c060c02030d030c02070b0705060108011803051803070e010b0d0c0e1e04020f040605070516150c1401 70
    0xe100081a480c09020904d59000c0100400145007070a488035225203055000207442840760010340c100300303d0050851802c040d848030081c01079140c4081110950801c80d0410a502d000d00d0300007440c408030b00c8280c286d009005031112840d01d51504004c0c07000703400050400102c119640518007412244901030f512603600100c0e0050700e02054501520300d20442ea019000307121100c94110010303540441ca02ca0040c50390300e000170700c500f003e69040b45040303d654048600c0e9000040c030f080600c4030100b56507040c4c91280c3c000340402001c0780c0c560310000324084009400180140900105c0c03108841080c502c206009045031241c0343c840c0d02d50807181c0001e9022a50701e00c00000c040c0a40c800340d02441c6406140d6041440c20400000f02007040d4010b4030000c11030340413410b11521015551a410344001400744010161a039803129000f038900d0b800b00c402656184262142c005c0620030f1080444140e44280303039020842d1104030703000c1c1d910144100c0c08444007095803980c280c608000344a00d0f84901211 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 299067113 1250 299065863 299065873
    0x1f03050a0606081207020603071418090609070e0915090a0f0b0a260109080406020106061419050d0e010c0f122c1504030801030605150d03210905 64
    0x40d282a2046440550080001d500144c0462040340c4203001a691310f642c0680e40141c2d2a82e40ea5422034080340300d06c02219a81e800030900d603c10003820f000141d541c00c01540d4124054442d1410406e140e10100e40b40c8000440d0681841d0719820010941c54228aa0807408151414201c001803900c403421588140c03000d43da03128216002c4442d00403560049010794480000030304140c01000c100a00340c2da020b0751041d13121103a49200400f540316201d040d03003050009403625250780c0024080c0116116802c009040e0014004550241c4800c580d40c1c0107000e2500009110b000c602a02c154004190581c0d00d90b84c0d4110460b001002805071010701001581d51001079a04000054107020200d008a03040310f203003905800404024580c45034000c110003007044062010404c04529043c1d440e0f03180300741d001140c024813007016004281c2e54180c80c400e110911845d9074103400441c00061140000740d1048120211102080c0520815010600800d01240c4501c0540f411070b000d80d009024112001e0b445 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 299068363 1250 299067113 299067133
    0xb011d010b0315010e01020c1f080f15040f020d090c0302090901110301140d02030703060b130c05030621030708031602010b1806030709050a0f141e1f0305 68
    0x14441889001d003000c01c4209055003042c0302441d40b40d6480c8a400d9040c00084004140168020040d180e070344d0030010034080f1202a0b00d0f071480020041c03111103030041010300c3c3c085900d211140d481035100340c8640c68480e281052400400024014201c8030b14a82c44d8200f0186000c80e42d1030003003901c140d0242c01d0903400b580ca03510600c159100020181c0005924010165010003100001c8a0444030580f01c02c3c1002c8182d80005006e406620400a50612450030000204032203900410786c5407100710b400e020500750500000c1e05540006403010005441040000c0140c9003c3d2038072100b0084100206102c3c0743d92681c90380c5564410b84087c0d03003843d0044104000301440340300002c0d10400340d1000b4004600194081090f46d07035078415078072400b00303900300154041e14104070910040c81c02e0601400b05090140c45c541c0240400e804404d102e509001209496801440ca02800307811115500344080141154010f03030004042d04d0b0b1500311042e0881c0207901942c0300030801c05140550301801c0f641036 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 299069613 1250 299068363 299068409
    0xd0f020c0601050603011d06030309031f060e040b0705220b090f0604050d0210030f09030305090f010c05030703180f082206080a1a0405040c0513060b040603180b01 72
    0xc0140c0c40709104030010001800002ea1f0320b180d04d150108440c143c030780c0c0c5440304070010f411b40c002d1300c84058242c8035041840002d00880d600c15903112800b00010080c0c1511005044410442240d02408100b1340e240400e400c544500002c0444c0d4031004614000442c40f2900401441c2c640c0d03100360043d4401094001c076924254a0380b04206800f151150f10b0246040b01040440c41803040180c814042c018950321154001d0f046110041c5880380104030240407494090002e0006440b160070500c11500c500410050511400c01e8a00240c3c80f01811652444030480107018036504540d200402e90004800064001c003101c00d0044c45030711070903100c0340d81d0450f50310030201540710440c41c012400c41c1040b210741c0041c0019040401c4079800b2502c1c251000c40c400c4c03400c0310f20b01825003040c82c140c00c010901c45603006030000d49034121084140c1d0044d108401c0295500740c0204079a1a1003007100f007040038060743c00003070300d410412040b80b0800116140c034880360001740d0100e103800741c0100c40c642c00c900c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 299070863 1250 299069613 299069623
    0x70503090c0918070b1e03040f0204020c0307060f060e0a050402090a05060109320d030f050a0507020d0308070e0109050306060f0a0b03100311011d01080a1d160501030504030c0f0303020d0f020c 85
    0x1b69a0031011030552500e0380b91402d110901060180c01182e0010711510620300c00d004640210743c0040c0300388100c0c0c4161420100030141403154000b40c03464080450752403c41800740c540030b44d800402042c0282c8401250a0050001400c02810301155620000390f0401c1c0a40c0048103007a1303802d0314000306c04400d001c1c008000c0c00002c00740c8149581c1c2d1407140029003000c0f510003810403621344030f600c0d8a200c030403d0340c0c2032087d0300c406035000c1d440800c1035042542c8801c5041c4200500e0780c54526400c0c0150056580403614050240d140d04050002002070500c0704803a14440001002007030281c0d43c403001a11a94025070b030082595001101c1442400f070030034115040c1e15003c0c60070441c0d1005082506544001c5c1c0b05a90381040915070100d005076680d80c01c20500c80390b86180740e00aa8030f82c10201c2e65642000840780714111400000001c0b298003e200721b0f8807660f055102c41c0000c0026583d6440f03401030b48241201490303402d00028031007002a00c14000c075010f030302c0001640c442d5000c016a280c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 299072113 1250 299070863 299070907
    0x180902090903090a090209032e140108460c050a18021e0a0903060b15041511061602010f0b0f040f09080304060212070503090c0918070b 60
    0x42c0c0c02001408000d0b25400034400840340c41d0100142c8480403440041d0900300d2400c84018480d081c015075030041103040c83e0715004000d90100c104100502c401c2503840d990024856425641c00c503e140fa011104001000841304008020000481002c0a400178000d1208010f080550348140d9040081001b80c00007000640000c80300c6059613498180005568521014010300b61074000c18401d0300901c02c070ba40c0070326400a0780059a00c40300a0000100344e80100c0c8002e4880700e040001e140420308000101d8901c03405400752591a2030b090088a844010b50003403580200702e40051903103480e4005100b501d01400e2000400d4140c2031301020002d00f9030b401d4a022403011858405800c030380d5964601c103444200e00648011690680d400001d400400c1e48103030107006103a00004003c204000e550080404007038845042180c0c2d00d036004211801d020840b4008a540d0103004552050b1510410040d4040551401c4084441070b4190003801c00c810343e40700c10348054000ca101400021002c028400c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 299073363 1250 299072113 299072131
    0x70803011403071202210a2004110c060408220308040e0a0e070e0a0608100e07060801080c150403020d120912050c0405040c12150f09020105030f0c0418090209 70
    0x202e400d403500006c002c007801c00d20841010a000564801c0440c0070301c1407402003504401d00c0e50480c42c0e0700c441485000c2d43c070400148210320b0902c0c404001d030080810f8904855003000104100d9440e035071076071060b0f4000c12120143d820821031064070b2102600800300614410079505403514580340001c042130601500ca144180e041411050130104001009412200000c1c0042c6280c0c580010f4103000b040e03c0e401401407409540414144070005802c00f1100c44101d008550a955540c10101ca4060082c010b592580e0440001442070b85441c1c1c44251154206900c44c0745400e030740ea80014002101401c0486101c1148000c00c6c15181d08440004014030312a218441300410950700c1a440b6807112041a12840c2d46202007014070142005410140c0204141c00f01c0005413410201380c1d10400d4100c101c20386d410b2042800c002c1506010341c0100c954107844260544d114005a81412000244008460801404009101c4109001925800041c00d2000400d140c00740188018007000030041e0701 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 299074613 1250 299073363 299073389
    0x213020405030c0904020112061211010207060206130203031201080606012703030c050f0d020a0b07030c090303030e0a0b0c09091602030702190518011403070510030209030307080301140307 83
    0x281d61004242c84643d007008444680103a0341d02d10069481c260560300800f1014a44900420b0101d403c011101c600340c011038644c4001c1d01600700480c1e4455a40c001e41e40103800c03400105442c2d0710290004500075100170f0a8906041c6000c1c10001034003400d9010b20303c0c533407001060182558008c5040103400048107820425a03031004a100000c4c10b103444010700b01308c030070381d030040a000040c400c00c1d030108d00c00400c0c0d42c840c01031400025039030008048160349212603900070641c0c0900902c10054070b9a100e445a150b01071941d01c0a50040860f80d00740c04503402418403c0c03000420042c00e4522400d14035002d1900c0e001c000092020080d001004488101c41c0120160122500002540c00340b41c0d04036540340e401000001d243d030302218035501061f000128501c2900c80001d094441c43d0580d03500e051405011030102c001c00d43d542100d4031907183c00c0100080d801e244180300e1740042440c0303c005012a442c02d25150303100c200641c0240c0c07040c540200e2603c1ca60748249130903c1100c000704141c150b019 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 299075863 1250 299074613 299074619
    0x14031308060709061d06033c0601121401080d0f030b0a061419091e0b090f0a090e030702040c02010504111509120a020321180f061c0506030a150209030a02030d0c02130204 75
    0xe4003481c8c003500c510b042c0304105181403131b100c1d400d411880040d0071030f07503502246580d54a0345941d109a140f8810011030005100300d905180700e8460b48126050061800100c58a8241e0a44000e20644804c1c54040c1c01004480080e2503110000254102c499554050030351801c2404100d000140300315550a01e250130341041540440c0f42680c001003402c0383c400c01d9501c3c051001500c90f0940d039001000b1982005c01d00d0034125004805030081c98002c0c4c5051141c0210031200306c0c01c0398000c40d801425860b19241c0c88109080034008000c00481980074189840ba01c000000c01c10041c0c000c00030300c40c0c0e020071500411810248040c002c8000c2d5900003016148504541100342d0080e01038400303040d41e00180f862a00e030354aa031501003500300a081555500c5000c041155614113a00c6c4c4200700508242c007007070380c03030400050701e03e01103401c41040d0720031400b0610880c001c0c1d408032000591510444000c18090786d03090003c08401405078681100ca4400d52040c401045c1c600021100c500744140020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 299077113 1250 299075863 299075971
    0xa2001090506010510090806010303020a110904080717090d08030402100516110102100609020d1d0c09091e030a09050a030c0e040f14031308060709061d0603 69
    0x82c0d030540b4011076115800703031043c144c21607090226a01401241c480c1c440008140341d0040b03420710740380b40500780c1614001008400d0217401c54003030300c00900e101c800f0001003002c03420412a11b076404080c12a5189804074260000e2144125010199003030f20000003480110b2904035880300200350103080407428168640000e5500c0101c3e504083c1c010f5004001200039a84217000d4101e034161004400c000c401e4892603d08003c0d001001c003070300c4840c0340001004a844018a41c1404c01405200905081d0b001c0b030700303000403050007a03c0c2080e184921450242d50192042440c22280c0c0c0c64001903403200703801079000300601016071006000700008801440030072501c0703100310241c0c1c50300481050780c0e48a0b4034003540a00c002c19000751881094401a858820f004002070841c00109210b0b9152143c0311103080d034030340b00156440e070b01064003224200043da0054a881e82c1340780c07000c4140e0595412400101d241c641c001c4500c51482d100d42054402c400d5032006103184103d202e1040e4416000c07001c604 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 299078363 1250 299077113 299077123
    0x507091d0f19050102040914070f1416020f030f010203100617010522060b0901020106050f240403050d020304091b080106030e0309040f02040e061210091104020a20010905 75
    0x12100c0e0850041c60a0b074140102501140c0040000703070000c0040b40a01c1016880b070203020745440b000110041e03510407199101d8400004003039040407a00d440c24007003035001e030b1b260740d44103404a801883d107850720212940c0501c1102000e5210b0000903035a803806051862480145030022804e002d40c0344208a03540e8208441241510f4065500307214103191018410386420003100c4003151682452000b19102002c5c1d8040c0c148441e0a8000340300e4583c80d80708120b509109280004e0f00204844480450f50034200c2003280e0601411200354541620b03501c0e542e04240c0d409844402503800014200010b980030301c204091340d03840340e01018240401c840c000b80950010320804003010f0b16003201010004083c000c03100c5c2c10354010420000302014481b40806034005200d9901800d203420300040180c1020b00a041140034000701a024800051b00642e00410b038480c0207907074003402a201c4400316200c902c02400d05082a854010817200080752100e240a0192510b10099041502580000b140010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 299079613 1250 299078363 299078383
    0x50f12030a030207030924082a0f0c032101060e0d02010c0501110d05180f03040341010501081b041d060412030f020901050d0207020a030507091d0f 65
    0x380240e610007245c101100c0074090354200a01300d440450006600c4410385000240d01c540036201c0b00403641d41c0303203541d14140030a4000340e10024a0402d1244241c14910020140500c00c2205d050811142030761003440c5801c00110010b00c0c0d0402c51802c4183c1503881c000500504003443c18140c1f000b8000b0100390300700c02d19400241400003030383e56641001307000e4105401900000c07100f10303112001d00004801801040c5c0301d9800300503908070704c056140d802240d600c100201d03e000645c9082e02d503030355a101c0818184000984100c41c1032003a450f1041c41001c1c40d5021003020011103044014030681401c556040c2d101c403005a200c05500c1e02c5080303002042690000045500241490103280d5007240c8050b900d501c50624003440042004002c544403401c0c1042d030181e6000c0100051200c00b91003240300b64074040c0c1c0801d03001c0c022500b40090540003000300ca03102a03c55208103540b6a1a2071402c01160030080c80540c540004c0b20720300c49402d0b18025083d402c1d10052440e04042051b060311902001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 299080863 1250 299079613 299079617
    0x3207090303210e0a0c0f030b0711071e05010f0216150c3c080403151503051c03060b0405010e2b020a0909030207150c0b0907050f12030a 60
    0x84074100541e0407040e420004168000401d2042403c51a45a511810413184c11580700b1104e5501107102036841c40f1507420780364003a00700100c40e128110261149200c50382000e449200340400468049007400407047c014901c43e40c1501003c1c24107001526054030907800008541c040640d484d900f005018a003800c5401d04c4e40c400020030200c4400301c40004560703101528543c41044c5c812412402072030310607090aa0317503480600c10301e4801d07018007041400c52005030807131005020078404540c00003090040701c03030740300e40001c1c0f02d1046081502d4411181e40c0103940d0342d00720400d00400c05500ca100010006110f03c3c041021504003000c01000e800303140185810803140580074641e5494003402c44114031004034200c0c040035541a0954540161000100d0185a608000250020450080c48e04c4603600d03401a00c800350500b1030a202e26070024500c0310030001a84089000300c2c054030b86071800b070100080980030b0241420b0501c40946041c8004a00402c101c0180c0d900d0a240030083c1c8401501c94 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 299082113 1250 299080863 299080877
    0xa03061e2409150803070b040c06050a050304020603071e1d0d08120702160b090f09090a020f01020c040c031a0d0b04120e060f0901030e030301060c080c103207090303 73
    0x408540f148150075500b01050030710000601c003040c4800c8001c014416071180050403015512408121854060400d10030040307481480030800500d0048042c40e801071503450180904000c0d000240042c202d5000000042546c4000510425695450240d90038100ba50000e40e81c20983c0d445000398801d1542505c0144901c401003691030f8402d015801c2003a0040301d800a0442c2c40e5102c0c40c40c20f0b40038103030036032290300c1401c614030180c1444000f00b8071600d405c8001d000118856028400c4064568407100d0441c0110098802941c0e60340c8120702d00125035075030010b2080c040300721032101c201d4681000d920681c000400100003800c0c0e0380b01181c0c8594440b13180d54401c0500071741070700c00028400741c1d1940f010010030410150b4001001a043c464026602031004d6241c000300705403030344000e010310800158205100c001240c01c04d0014603407800c219048514960030f101140c021601d03150002d082d111110b080404002e6085003aa040e0700881c03070314103802c90a182e000640000e5071407000030f00340404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 299083363 1250 299082113 299082131
    0x1051507080c0d0f1b0305032d100305071a0304080c1f1b0e0f010f020c0604090c12060e01060f0302070203120a090803030f0402040207020a03061e2409 67
    0x609003911400001c1000319529070301e00a0f00508810b41950310310b00001d04021451480d0340d400d0621080340da403d6185c491554650300b250720030400001002543c20f4094450026001101035903046c0f00708400c020351501281507240460038421954061b40414160420340c8081c5040ea034100c980041e800424140e840c03015421260030042189240c0c441c0c8a903c00c0501d4061180340c116034039034041100c003000910b0403e08296680f0341d081c0b25194100c6181d400078051540140c4d426803101c0f1340382c0100d8012080c580b00161044d44039800c00780c030b019200d07150000c83c0b941041400d080c4940d0b00c80240041810141028081001481401c0070484000b8107004903034025411100103640107425104604036a50203181c455014015103000100c00c10720000f4802808000d0f02c1c090740d603018503040c01d034030307240c003004041e401c070790001d0f40e101d165203900000107200d1384200d11400030403030305034041d040b15510200e04841020350106a0309195012170748203108000002000c1e254080000286245 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 299084613 1250 299083363 299083373
    0x51b15060a0801111b071a04060e030a170f1606020901020d0f05070201030c050408030a021605030c0114030402040b09011403060a020304051e01110a030519020901080c0d0912080601080a0501051507 87
    0x603158000e11071a07481c0c7c0f43c0500850748410061080d03a649450b00410440c108050603616030101360b0180034142010140c880070151000144004442d0301c0ba200e080004400b0850780c4041d40c10022140c1a1b40019104880c0d60141300104e041d420f03506004035014001c80000c0c04500c04c1c001700a0400d540c514103507040c14050010355003d440c071202201c0d118544000d0180d901e00c3c03908621481286000000641c81c600010406401d06040c0d45142541510f0100b8034525000030744200c0c1e11985400c0f0540303554884043c0321b4000d101d01041a001016130030241801e2901c0a42205061801001000b012900c00140e081c25524030303c1e101c2d6120760402543c180102034900b0f044404078000126001d00c0c40c1d01d40c00080c01070074580701c40314180185032280341c128131820360428041417040c00051000c00c2c03800c0c041c181e0107a00160108400505585e008900c0000600e076101240c044030500009507403052815502c8100e860040006504090010340c0c1e401c1c0381506003100708000207145007000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 299085863 1250 299084613 299084623
    0xc020916170408130b03100306020c0f030a080709050d0c030b09010e0106060c0b010e09190c1a120f040201090b0c010b0405070801060825051b15060a0801111b 70
    0x845144030051007424280360030a0307035a215918148100d030392010003060414800c1c5c2224080c0090040c04807a1903e1665404003035008142200d15900a00507a00d007101c1e000e000400800d030f40340d520101d491030703e00b0000d802514070740c102c24001d0104c034244000040102c1e00e01c130300380c0c1d030060001d0490f41c1d41c07121190f01514038109101901e508040000600c0c40d001548080950301c21401e92104d60b0b00c3d00d08942b030a01f4200c40300021039014540b03c2d050b9450700c1d0741040d0b000e400b54038951083c5813141c00421003910302e00800509010b0016040260010082c100d5800c0302c91708042c440306003020740000344070300b602e4000c1010000001900c0c00c0380c1c0009500c00281000d014100b8030051401910140c140e80c0c0c00d101d03110106442c0e6001403029031914034003042c60402507008615480c1001c2c81283d080d00285051004100c0d105101c4480100400c01c141100c9001e030700e40a8075252010501c40c50035219804407500740e0420301040c51070105801a18554515642c00000c4101c00c078880b40e20749 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 299087113 1250 299085863 299085887
    0x308070b0405010914030a0f0809150402011205040305130501050a02070b03130606031103010c0207080615180a0f0617190501021b0d020c010e010807030e0c131a010c020916 76
    0x2240080c1c9843c121704d000440070309254861519913411605501e04203540f0b18500326091440341d0044485e986519a8580e038140e0443e0061620401342d000b405c030708400312031058406401191003c144481c004020800180c041c100a10740706003800c4c07140c0e201035561111130113000a407400c003100054815208008110016411420901200c0da59003081007900d400d000c00c19020b9404e158103005254000658441200c150000800042d80c54400342000080c514a40903440041004072000052a0f584d080b40510303a01000003411000c25040307d0201c41b400c0d4070060f0502e00500c1900e502400c040707030081c00001e000000348441c0620386042e8ac024450505d8110a146074280b15454810f8002a000428040c40c0c00300d61601829000542d40343c4240440140090303034260010380c8040c42034100e0070051400d030301180c0384070785070500044103458501c0b012aa2255201760144001000c8003400311050420300740700240f842d850300441c06004000700140d0216480c0041003021a1240b0600210 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 299088363 1250 299087113 299087123
    0x3051f060804060605180109110706090308090f070b0406210e150603010908031503010f05011d0a0b03030f070c030b0109052409070e01090503060924010308070b04050109 75
    0x14544448001d0807036071041e14103866103440c0c1500400e0506007035500ca411611444500708071a8a03000d4004050300f500c010000403c0014405080041c40f00e0041c08032451081e25002210728240c00040d04e4035110307481c100f40b5a402104200485204a8216000d94840303240507101602049002000e59258903140c0c8203241c50060880204800414440d100700300d00800a241904e48030300f094207807803500c00050451503081020607086055454091807005029001250b03281241e40240d003100c20903809400ca180301e9480070340c170702c08044031100d50120000300304108620090b0080390b50b80c003030204e50388404240050888c0a01c032440c5541001140d12040154407513031103c00310001f8100030b860540c5050440104600d900c00f15424911010720f01800e443c1d03041d610440201c2e41c4540e107200307540c1804175660340850540c505000e410700c204080002040810505140b540750940d035070305000c050b081500e00500c00588030004450340d258003c0003028036a00c46003451401030402d241c000344 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 299089613 1250 299088363 299088421
    0x1c24090b0102120c010212091f050a0e060703020405011205010806220c060e011409010c02010302180d060209030712110105180301020a1205100e01030b090f030c0303250f0305 77
    0x2c10f0007415002001f42d81020418400d180e01c9002e481d039a6504480b400c030204442c2500c881d41c04250302c0d07104a83c4107030050303c04a0041e0290164500b810307026655440002c1e00098244025600844041409108035204110b550724005119407101c9014103050400070b90306440281103411804100c1d0250380105100325503941c1c880c0c01800f6047c40c4030703445020030780300a200d0f0407680c4080162042c070070f4183c407020319006070380d80110300a50050003400608132003100c2c0742c60785e034580886002c4039510400300140d40b04e0350102054035113015a1b1012520035103c1007014000307100d0244c1c90380520802c1c200350340c842c408640074120b80c0d510312054640544c8045103810710039501c0300c031202151004200c10007003901c0342c0300101010f85040c046d403904841c42c1c1c401040061264202c00340e20003550700c103640ca070064030a10b0314195072102c58000d41030b52020040c06032424595100207044000322140d011070140c400809040c2030b00b41c40020b8245a0b403000000c0c0c0c0c3c40003000751140360501c2918070750 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 299090863 1250 299089613 299089627
    0x1203070507080601051804081c0609090501090b060603060a0e040305041203020618030a0203090d0606030804030308160306050d020405060102010b060c0703060b0913021309081c24090b010212 84
    0x243d6220401d10172180b0a03101d84041030594482028024000c03a04100b016150035032558003071000d203800e513401c040280d07501c1c040000c12030841e101300c039000c5101d0b00020030f4003106c07810000f010782d00207070034148150010401d110040c0e44004001045803c9420451059079481c03c0558040c0541c0d0b101110324916583c40d0340c1059804034050344a18602010714440100180790b1554a002d08030300b0001580c01081012460301d001482005440d03c0bc00012a806881e541c40303864940042e030044010910040900001c0512004000101d0f4403e01d030030032070a0303e45000900340200490010740100da440001c9001d0fa4400c2d045820043c00261207036558407044440d00c0d9985e01684410f40f407044c64403000088500d0003082e040d0040e02d00400395280107825400304844400c0c103170000d1081c656502040c0001800354406000c0d00341841c40140c4215494030306000c29140e8520b01565084591003000c180c441c0e0025203581a01d0b540c0000165614080300180d14100c00300d0000250040b0103e404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 299092113 1250 299090863 299090879
    0x3011e05091c0f050705030313031806140d0e0d0207081510030605060d020d031d010905060403080c070e010602010209011202160b07170a0b010228061a12070503010b0d0506061203070507 82
    0x12040c0d10300ca40e45004003854150340055598a450040348001031200c4500680a8012006030512195000d3b00144401c01a1001844e242a190051015810048007004160414041d43d42c07603c00044034241a480d00d604e542d1044002408018076441d40c4038049003807500c541a0102c82540e0117010310642c142982805001d0080e40d403000d024590360428100c02035441016444111007000d00301500342411a5200c029a8101c041c01c00108e100d81c450006995015011007802440340c0d8000580d11510600010200c1603880d030342000c001d0040000b08142c2c00e00c00803601c80c0b6600b1008424998445e410115480c480d90403006407c030b0b2612007072000c00f8440782c2c02910148000d0702100c084207190300e88040c03d407450184040685031100680804078032035402c451800d140310003a414141c0c07036900008030280d00c019400013150f40103100034007550800344034011200341e0480e00c4101000c40d0b44d503080c1d0f481400138003140c0255400140e5150184040054503401c903070103420f44400f59110001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 299093363 1250 299092113 299092141
    0x608010c030f0605030d080435030601140f0304110102070513060f15020a0605100f0909061a0d0201050c0705091602060a0b101d03011e05091c0f0507050303 69
    0xc0b50544500e40200020340745000a055815030b4200e4994114503601da4481d121b032000100441504031a00741c02005c10012036410000c0030b01c6e1038103200303a100e0801d00001030070ba403483c880e5480035001c02c0103060b60600515060300c0c0c0c030a5203c08040c0804240e100101e0070031246a000e6070304447d0480500c0c503003000c0d0742c1180701a60b15844012000e00e541d201c00d0030740c3d00c070004050b00140e004900500080790550b000140d02c00c4503001070008403540c1d543c0310752901020764442608186d42c6c0082a00b089081d002d500c0e523001a004c01115040c515100055202d002184000c0c103103d40002c1c2c15007100020301c02000203150003041004a49440700c00b1007139150300c140448005018a0001882c2d4a035148140e2140d0b420141c00300c011161141c4040c0e5200102d94148528503460028407044c0d680e090081002d44010740040d801c007841146051020345a0103041303541180c0090010460880280c5544541c402c2a8940068094030f42441501c0610504c407014149000c00410070207a410515a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 299094613 1250 299093363 299093381
    0x908100b030c0f06071509020303030106110f15011e0801020301060c1a070801090f0b1509040c0c120503070c120207050f01030e060609070324150f140d0608010c03 72
    0x582c0c681c42542402c02522000382004154041c009201e054080760003101000c103a54841240045c0c0350704130f0740019141d038100764810000030340140d19101c0250001d01a11080304074002c000d0885600503004640707008014000c0890000c444c4401410716040703068800000c20300c50000315030b25612014020304001d9031813815100c0307142d02e148010b03d84441c5400c95204258542c2c030141c4c1c1e40d08040703080015151449201c101b507030312101e125010343d840c0300c1c8810700030900f24071840d41c03094000c05000030f0b00c0200b070104080c0f000344036810022840c0e0307180b1b40c508081c5e00d00d806580c0e941d8120701603610700752200010700740110b1100c0403c0d265030000341580546100305c2e542c0319603504a200440a42c0e140d201c13014010380107400031440600300f5056142d040501414003142c00c1d0b2046042100c044084a081d82c00203800c018100450700d0070540c1c000f403140319441e1041d901003a141000d0040118134078001c00902e40050141000b190592110015107070b942c00038004510f80800080103490000707 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 299095863 1250 299094613 299094619
    0x603080705071707031203020c1b09100e04080c1207060608100908070b0705041e031a0408030f040807200405090304060e0603180118051b0a03120908100b 68
    0x2110210b400e031003c0000c80c1d2500c46020040a0f0982190799072070b0700400e950050000d00d44c0034030141580c000144224a18032080c11013100c0110340346020019500405085031610187d0080d05200354000b40c4e0750306500c5608045600d07a600240e90125281444106a100d588030b000714100c0304005694000300100c8905000311014140c283c0322040c00c07600784920041c1860820410200010640d0682d507600c5951b0341411400c01d5904c0c0030785255410701e90b0203000328000d107035028804c001214844048001c00a112944685401e9441c3c850f9440b0141059480c6c007442c00024040100303040885003080d42c82900d0540c0f000e03003c2c000300c02c00107101d80b40d944a281060001410b13560008241e8007251015920003601001602c24491142e00c0540791391000b1030648041d202c03052090007100f66000d40d0003106400305209007009410004950f1084101c2c0017582c00550865035480100401c0da6084400c81e807200ca100102964448001da02c0b0b01554010014221211600e550000540000076 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 299097113 1250 299095863 299095873
    0x80c03031005030c01050301060f090e0907031713030f080d14010602210d0e0f011b0906032a031404060e07060206040c060e0102030c061003150510090e0c040603080705 74
    0x482c101034562102c100118005541480100034191043d010349107841072905140029a4482c2081c50300f05504542030411648070f00380800c00c20545002c0c40300030004135014103040021b010014409030041e444080c040d90110010141400740b0b69040350f0100505120401c000e031110300040c901e000091040c1c80240c02015008070090007401c24412000f104003646524120302d40076124000c0080d4008030680d44501864030621000c01d00c10030b00105101c0c820b056502003d944000c0c105943d54010400b0581400c03407582001e400101300280702089805000403d010183c03086005243e006041400e80d1241024802400070a901030300c0b804011100340d41607991a07403030590352110180c600402d4501e130b0031401c0001901c03034845951510300501c1540d14021104d41194a031034410b44410f132090050302c1040080090100f502d180b0308003075040170b00c0b80b86010b51402002c0b0710b540c0710300d0385140d8070307503001c0600420140840080320000820070450141c4a00301110b0301d40102c482110b42e8422 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 299098363 1250 299097113 299097119
    0x30c0d0314010e06030a0201050309070302060c0604060b1207050609042d1d1b012d02070501031a040506150f0418060806071103190806011805100503060d080c030310 73
    0x4200c03600d600c140c13005001441521016130045072164002800100280103444000c80140d80c1e003030007003030060b01b608000e18070303420725003001c000315589840954404c0c80d4415468002800c08140700d030494004581c1d444c0c58560060100e805004400413400200507042810484001488250a40e0030075440c410440303c0c11440300382200c000703c160f075034031181e011203203420b840c800080341c880c009081894044c98100c54802030f031180b541001600c010f0000b02140711070341d00703a0401c002d00080509107024400d41c001d840c550110903504100d224001e40d00d0f40c1c00103840c1d03150300c0a4004501040d000c026681c40c0300b5608020717a50080d0296003802070b29240134a00c14802e41c02548291900f0314046e0881d13403103010098580c2c41001d00c103659207003c14402c00702c9441c900c0200c1d000b00c01e02c50b02c039500d03a4600f1500042000c0b2412a000603444019441402180c0701e08801d0f1072910700034100f9a0f580e88a280000700d001301c4058008000110002d0301070100b4070080003550203211004005441d15031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 299099613 1250 299098363 299098379
    0x6060503061003020d0c05030d080f0906100e1314070608011a0a0804050a06090303061503060e060111030c07030f0b0a02090303070201080a02190f11070503060a0c02030c0d031401 79
    0x7060780c107580402d107010000d1001d803802441c031506041c49800c102c50f09075075032800709040000e1032030040040307180030003004001c100d18070070541c0c00840c0700f002c0d012b07034030780380c8001c900c0d6a0844c0101d6000d0b03014500090106107403014006426034120114600c024403011450703540e03251134014100000c00f120000101a481101c00034101c524090400f82801c2d0224001c40d82900014003d5400e40f24200210000c1440b81c8140c1803524042d1340c02050290400c9065001c152080c0d80100c201450508200a2004a50760b0309800c10707400d2912628034680c041c2094914061000384500c0e9008101001080100c0c414825400b03a00c2032154025030354076108528100d0003103c0030307950550402c212510041d881402250340c4818a540014108050b950309600149004159070b00411002907040d226a0380280d009a08109414000c004a608180c082919074038003403d550055034440648009a0f0300a0040c1d50303035820700380100e50501d10000001009046600389503043e44068500102e0584d0b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 299100719 1106 299099613 299099623
    0x90a0f03150501081902040b1504081608030406050405010305130515090118170a02010603050f03041a0a08071215080f010c020d090909081303080706060503 69
    0xc042070700d66504070355060f002101d40398807103403444102280900f507850200368142c0713010412081c01404124240e6200e141c1c15a030401c0810b000c42e00600014160f4400c072924010040d503e980c07000e96940ba4030641c0280000180100028009035019400031508207009600b2070300048400d03140c05003084100b64408000ca04c20340d09001442c00240201007a0708103c10211980004a50302c2d0b0098094500704038814030804608194494000e50040c03008581080a481003428194015034495016001c2c5d40c4c0d0190140c10201d200d0080035081e200c81080d44c1c1c1710401030303031650300003501c51000e0300400c0d030a000e03280e4183e400780d220700c0c1041c0002008000018100041c86155103801c0d69940d03400c680455010001c00c0640c80d80c41030341c0100f2030395400b5002071019918144041c4901c501d00c640042030300c41d44000020051402e009041e007174040c0c7c200308030203611281056110 = true := by decide +kernel

theorem cover : BRFrame.Cov 298920863 299100719 := by
  have h0 := BRFrame.cov_init 298920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 298920863 ≤ n) (h2 : n < 299100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
