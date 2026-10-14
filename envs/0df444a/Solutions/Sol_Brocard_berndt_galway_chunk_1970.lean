-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1970
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:20:32.785168+00:00
-- url     : https://prove2.me/submissions/f4ca4a8b-184d-4006-bbe6-08d6b9583b06

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 354136690 ≤ n < 354316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 354137940 1250 354136690 354136733
    0x70309090b06030403051c09020a0806150423340813020a03020d15020a0f11010b01050f0a1b1406060901031101050d1407080405120c0c0f0607 63
    0x30300000c0d096206000c4205070681d100342c198542070350040c2c982d11980512074658143c2000d04401039011750881b00802ea4082c122070402d55842890316a9030600756411076881c3c590503903226160405100d03541014400c5481d403205a10451031480c46280003521f0340c08001962080c0000c190014000c003181a040303428030401003044550000c2940b9030180001d038980099940303000c050b986035907210066a404a411811100c00b80c03610020711005010b21184035800425040301240d04205542c56a00c0c19840d86022513000020741404c80300810441404070300140314024048100d00301030b1141200c2820320001d0824820761011030300c002803000301e80411070a16201e90540c002d10480390800020703103240610b03504594501d0354064082603203504000011035266070141c0d2940200150041c028448001810886402050110111000e440d54404c08281c5441403600c841101c0310503161502926480a00004100400c22250035842d8024002c0c021440819a011500c160440c4940d8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 354139190 1250 354137940 354137957
    0x1104030302070f060507230f0303060a17060103030807050d0e0a1502031603020a0215010f03050f0a0c05150403021c030908010207020d06020304021807050306031608100b150703 78
    0x10340245010540d401240460190750030800035a60010213031210984d200722035034041c4017400d40018014886108401345d030303c61344007440b8440c10084000c6014410a0312106031031030701e802001d040c40d0407156901c032031a406180100086841506041e4001049140c40d0b450a0580c90242e4207403211000103440541150444a04200c400342007008490103409041d820f43c904009109548100405601d09042d0000b40241203a8400d00c4194801b500f140850f400c5075849401c0c100c110307602400112414440c000b40c4901041000603080071310342d408206003040c00e04000501c500c0080000103460442000d10020006a0304c0030616040310602c1e40b03036809106003c2c14010003900203a4801c01e40c42c1d00c100324000242e02c60700d046e403060b260440c2d005a0350303466504c080340c41c0e65089480c10861600300001d00411550101c010b500030b84080702100c040144207a1212100c403d5807180c00001d50041100414070a06508105040e1800030080f04860300898074050b400d90022200700c00055600 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 354140440 1250 354139190 354139193
    0x80d05030928060c02070b07140114130f0f06021b0c010e03150c07080c0f1b090f04030909061e12030f1b05010204031101030e010e1002070c09110403 66
    0x10400c0d20141a0a142034003600220b015458060440319140038009035120224855654001c218841c02440c6c16244280c0e03501260401140d95468a0308194042d42402400e00b007502d080090140225040600d501e4030b40c2c050b41e20504001032100301110401d00c004070120110344284090022180240407c0114180d01c00a09083c00b0181001505125100308040b074261000550030060414589450b0282d84610340844001d00440e1002440c01c0b2002a4100c0c580701c02050a1054904190880d8502d0351515030b01200701c1310002d100b50704a00386900140a01c50081109908107001e4202008401d845403441420382d5040e80000b810101c52503401da0400042d50407002c000d00200800340b04101c0e007aa802401084881c0005081080718060b240c080c808040b03507080179070f501000031599165680785c1200300d103d5529140b80400c4c80d2a071008058501800f5910540f50000041c1c90407444140850f00250030401040da42e1600036072001c54224054490106c400343d01c00f0885480382d145 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 354141690 1250 354140440 354140443
    0x13140f0402040518071a0715020a0912020f09040305071b0f080a050606040b01120c020105060f04020a080105060f070c120c0b0c030711060d0207112b0b060307080d050309 75
    0x549048003a0011598840c0759060102c0c1800946c0e03003204650a410502440300b41c01c50203100e00207070856045910140c080c40083c1d00400d090b511540780c1034800342e070310142603400c0c0031048406904426403078100009842c3c840303030169005101e070130054185480d90700c404d02c20b1780b00242c4a524644d03144a080c00420b0368030700d070b550007010700800a10b1614090780e921911040080c0140d401251203001d465100c1e03004024455030b050524004210800b00707814000d000c1c02c02503c1e0340f03029664109070070f0f0f80f50816000f01e940c0443c0603110054140d01e0700062080e998000d8400c040344090501c109400605000803140003040402060382a4882a090244ca480415030207041554000c00c65041c800c1004002c1e034003100d0b080311a91102e40044800324000744141c1f01ca02c040944001000810403400e800c1c2000c002c503040e910034200300c1036444202150b4100220940c804150307010b540c0005840b00340321590003900075060703c0a0036501c0c8a418584003000b10341e0b0703001c01c0700802004a0b5800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 354142940 1250 354141690 354141701
    0xf070e03010c0203090f010e060d0c08070c020607020d06060902070c0504180210050a090e0910060501080123030115080d17100e09010b0310060e0609011413140f040204 74
    0x40403002000412081e920195880c030071040801d00540802c8450311541c3c1c080c030500400310102619203944c030034403240300500600718070f0040800700f0b80d2100442e44d8540b085402040302039001c0d00c810301d819441e408014941c03404000c00c640c40c0b91a20004a001001c60000d000c6140c810b01003c0307809400c05080209585419046130700d060504140c800c056910b0030001c84041e034042c107200355030300442c4078120b41807001500b003482c61410060500505601c00503586545144402041000589540045036244070a1150b0200604050000203191000c61200400c3c031500900010300100141600507015996502010b00c64105000420300140c0040b0900089643d481d4181600d140040480b120b001c05400742c4004080c1080024050200c00d500c1004212801011604001c81420714040640b6060013200380c4001c900001c00d007107060841c0154143d0394600d202840821001d0f00740140404044036040c0070640b1840c080c201407180d140c410380a00e0151844a005240c180148804c1d00d8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 354144190 1250 354142940 354142967
    0x2070501390510020a2a0803060f01030905070602060f010f030f0b19060b0903071d0c130e0c07110906132c030d110301030503070f08120f07 62
    0x28420801d542160303092000e84080007451660844a582035424400c1c540340b110521040e1141c80040d050b02e684d03402101c0a50740708929164085100344010040c4400c0000240080a1100500105d4010714115a1440400f0030601d00000c0b0070006860b20342c40c1c02c0d1254046030241e00b000d820301280041e40740c6054094585440323140407080c611759034030304401c151000c040c1c450941003002c101084060341035080c030806100c106100c4a80c4890020713080b40c0c091909a0f01c20f2155400001d5036141c492034004101e26113500805241e600c0090a1006a104900c400c01e071010030741000c15521380d5409102e005401d0008070382e4641e40c543c034007418020b5038488000d01c42c440c0c010401c9040c0d5200c010f10f036803031200c0440c003081c04604021350003050401c00e80440b0001c2ca08143c805030701d880000c0582032045546a0620400725440760032180d9200030300001cbd0003a0001c00a81010030180607140b812a440340324001e240402090222508100944610808964020611204507403111807a0f800c0e8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 354145440 1250 354144190 354144227
    0x105090304030c06080c040b18031c020a14250828020f030106090905010e010b0d120f120e0f0c03010c0c1e080f07030f14030f0a150602070501 63
    0x750554a40e0b4071189041e1190400f0400414001201c0907024402d5a0003421440b890b151101d100303520380e404081b281c103074040c000c0c443c071a05000d0380300b6002010031801c421900a0090010349845250301402d005d99461014441c0c4119245441c0701680d0781c00a110f41920401181741c100345915041c0f0714416020b580e802404121106102c1640208540d903a47c1100d400b02c1d101031000104e40500082d0340038001c4540382c10801000e001d410740081e616520f13060020411011a234080000c0081003041c040e124204551446110750700511545201c02d4650034064104480c400c0c030b43d029103981c0300d504210340e0040704145090b01e604010300d0000540840091103d0001128024118984844007401014100030315606100c5492407200500d131b040801c0e159182c0c060351003a5443c0c2d0090348101e0024070540e00103401d0920500c00c105416601d19a110f2840e140c0c0701c496a40802c010b002000010350f03400b51504c486034113a806000604590700a088503614040000d484018480780384000f5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 354146690 1250 354145440 354145447
    0x4080d0f030606080613060305031303030306080f03040b070302010e0d171e13030507021e0307060806060904020c160f1e1d1b21060102010c0905121f050105010201050903 75
    0x200c13030308081200d9110301c068914041c030900024114020b80542d91019044d4040041c205607489000185081a00d0203910140700055582d1080ca5940d00740c0701d5201d000760005e00003032042a08100080807010300a20011440700003804060341026a29100030010400580900d20110507200c13115911100f40c0034416100c0070015092002ca02c1c009054601c504c1036a8410700415010b078068070310310354004e481340e20f00e03142d10701d145194080c00c030b41c41714401d2061a1001520600ca070041d107200b59000341580d0704003601c600c01d00c4065042401c40302001c0c06444070720017180941120b0346e4002c00944d000311404038a0100c0c115102c0c245400001c1501c0001e00b001d002542d10881d51541c0c8540241048a0650f01d0080d4041c40d0350551854007910b0300b0000d052200490700e50500580000e42280c5042d80e61601001a801c9407102000740c00429180c3d103040040303207840c4603038905030700025042e140e4100090500c04514400b49100410282e903510041c03242d940d091007510744c04403400004528 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 354147940 1250 354146690 354146699
    0xf010e070f020d23121512070e100312030b13060302030c06030c0c0303010314010606030b180411040f0203040c0819060f1d0a030e04021914070804080d0f0306 70
    0x100c4100d102101c4051181c07080d02d4050501326041e00290781a251040e0a031540616900410200800d50710907004002106212843d4640660820000380e0003a009010b400e181c68800d0381a00300041500c12a03000c817460003c0403501880c1c41c1d071100c80d032503980010140248004c020800100410780d12030585003040c2480140c900040c2c0707444020040f10301d0740e120740e1114071078503c9100b100704507912804048000001c1103003100c4800f0310081e0650080c0904c41d160142181141c0541e0880c80c0e0002940c052125440380c00041c42d60090700501c12609a01100301c0410180c404540c20304040a82c000100801e00441901500240c01510040e19907a00c2520700381100c29516000500629070702e4046601c170200d070f6804000c00204d1091000454180f0200d01c035110340040c5810b601041042c80092901c2c42c00d4800c0350a4055411441540703200035210443d08030400052000c1940e2041110300c000c54540e002074001041080010080c140380c130f06004217000c40324172403a018182407420a01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 354149190 1250 354147940 354147943
    0x6040204140c0f0705030d06060804030801061404060c05011103270c1f18153002070804050406031b06020a030c0b1f09060512070503060406051b030f010e070f02 71
    0x41c0c03c0d11000c02c0407500c8107030b6400d1860844c850440b000c3c484601d840c034005009030f00300c00c42d00d200354060f803548809681c1c4c1e15003d8491404c0d884810306400e00401c814009540a400100e0401d4010000001c043c14181d40c05800c552065481446003607406d442d02d5024a900d5840201041c50070015200014422000c107a0610003e85004018180005441c00c041d215980c145000c1a0307038849058040da4a01070300300000c441c4002800050707028a220710807030340314525068803219844040ca4012a0809581c00290081c04d001c58002c0f404202c0014603540e24000c01028500030b07034040e10a44904260303c07040e512207900900a54102c014100042500490407056446d00000005580e60700e184009503481c1c0803840380902c440030400c02160012a55010505a0740180c802400c01c8880f92409503440c840c5110b445e40c076500140c0054005031440d0002500300c01c02200841400320f540108074500d4008035081c2545100c00c000421440324141d50994000340e15046c0300180449448000703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 354150440 1250 354149190 354149197
    0x10605150708040603110705010504110901050102010c080a0c090807090b101d040b0d061506030e0c0a170c180601080109020c0c0d030e060406020f1002040f060e012006040204140c 79
    0x38801d05d9607580011884022410883e4145d90340440200641c0c0f17080c2c07420350190308500348907030b028445810010480d5401486110404840c60b21480b83d203a54241440c000707890360024000400c40ca0680000e449081040500c000d041c482c8000306018000c4424000c0754800d4010039000c000d4a01c8900c250380c0c51303421030a0a4114107440c0070490085202c0400c1e0341000e00e00006000a03e00784040c01c90302900c105441c1618407a590510002980d24441c0d0f42d01c1500c0300d4080d07800018074104001c1d8540d402404140220b80405a41401c0551000905002001128111301042040401c2025a40038101a000d0000e103101181040404444070f83d444040021850044407a80e03144002d00d401601d0560081e01c000b4940340c1d90b280c480304020340701c0c4c040000d910380501c683c80c440f024281443c0280e40560712644100e80041d0b250482c21078510030000a081d048c02681400c0c82d02220704000031a6145801c01c000300000d0401d44140401c41e984440303840d8465000030180411b0300091800c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 354151690 1250 354150440 354150449
    0x15020f030a0905010603020a0308091003060501020d2616020610060c0602070203070f09200309060403141c050f13020109120201110a030806010f020a020d0206030c120901060515070804 81
    0x50703030300c42403030f046005008a0f0406540800e80600c00003c1083d0100189444002507800701644130b400c040680941e03035980103217405a084001c80308440c2e40f04d070701c00703000040402e160004002c01100031401403ca003074941600c90384401d00003000300c03501041000d801c80341c443c5174491726600e07002d0020021040c0d424001d25250b000920350055590800090018080700c0c0d003000c90305035640000c013005250401640c5075a184c001009480c0084250a980c8510040f00140006941d19501140c1c1205011150450380b003003400b49103040300c0420010304a22098507800121407d202c0c400c0c03040d0780360090094000d01c3c45040302c000142d03030240c41c80048540344a10301d40740040c0c074801a90055403000d000a620300c603000010040c03550108480b40198000e803580c07000100644170890300c1e80c8983c1d0000c0d4001e03994865070f40050614400a56111300d81e11102400e14228821030601d080c0700f61111000ca03911184240500c0c9001d101c0441504e1140c0c441520b030065a0790348500c540558800e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 354152940 1250 354151690 354151711
    0x1d120f070615090b2d04020f0403060c09090b0d020a0e090709020c010c0306050604120f021c0302010507020c0303041a1303020d030f12020301030b1501051306020a15020f03 76
    0x314034041009541110b0350300d50051420300034490b255200724005203201581c441c410000070440c040d40f10281545503944c60303900103144501201400c00e01000e580b00400c15140d140e820080040490414810311400b52100c2e0395501c2010f18014003c0180d54000801e148120300c0e01c0c40d60001a59110302e0306084404c10b0034a4106a503401a419013007050652048481c24000645110001e206500c40980b203400e54804010003500c40d41448061302450064000105100c07203080d0100e10036802c4181c0c9248000d15615140d8038a1340c0390f100344944410103c000d80c3d160801e00180c2901449030f4404400d00394020360410f40341200b004031049403140209452a00082d43c0702c0030441d907800750406190080c01c607034140011458024201c0311640034210003c0c00c410458101c00d070490086a04a90300003414820540b6a0246180c00048011480f4140035040029201c4454030745040c01c0209080d402810f406402400c04450304600b196403201418410000c0c0480b0190190035650844c40704803 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 354154190 1250 354152940 354152947
    0x806040f0608070303050c1c090918080705031209190311210d05070c02060415030912090e0604050907030b0705040305011a01020d08010806060d080d0507031d120f 72
    0x203411000300056040305502c0d00030220084181034000c1c0080c180a440403040719a650342c05c1903103203c407145040340540000c803980410810f030782aa800580321458000e00c0241a030840e6501d104503a0f1001c030044038203800100d08201000c0c03800e94010b520030250342c0a400680e24026680d221040c10381e00007014010780c03020b003040c1c25000300058140d4241c890203c41c004a1825001201600903014110b0321604010000d9003140c8121340148001e540504001d083c941021005010300000c05083c50406d9520031064012803900800c845001c002c50711860b401714280010780c0823100e0300a10725801542040d0611000c40300006501c01203a0304014100345948a03100100c40714030a550000d4280c0d07080888100d17a60143c90601c06408200360219404050901410344071000c00b485240410381005001413181d06102010b910140d205502c924505428202e01c88106c59003501d188000036600e4411000020001c07000c282101c0c1c5110081800c10101c080d00b1380035104001c4540311000011 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 354155440 1250 354154190 354154211
    0x1e0e211309051512030f030a18020406140102190803060111030d020a0306060906180612060504020f0706050c030f0712060815070207330e03241501080604 68
    0x5860050501c801e01401141865146191801e2185003094070408050000012860000084a0040ba20f00d4841401d40d80c85180700c000800c607580503102c4451840144c000165118401d040281020b0410704d041030b40210002441d0a55006641c1e6040a6005500001c82c1440d0b0550368000024605a2031114900390041d00314000d000044003894004183c1d60010390300350300304106840e2030350748402445545d014203d920344840041c4800b0000200010b0080510803424100c0c4001903d4001c20708070b03960404a404ca83c03100e0a00701d6054404039040c8200503403030199641018400c20020b083d030825000100340408060101014444074107540300c0400b074160030110080c078418082c1c80f0000c00c4106c0108000c2d0048035020018007510201296041102d12801a14000503050312031482d04000c2109224031070b400341e141400401c801da00c405507000c110301c2444442d509400c84100c18004024240110f001d0002030380c1303140f0600c1c001c031266848110700d41e12805c115000b181910a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 354156690 1250 354155440 354155467
    0x20a0315060f0906090f0b09040f02061603020f070803070503190e0907030b0f040e0a0f060e16060905090601210933110906030a0f1e0e21 61
    0x56600074140e0088400b4005070030103855100c0300440325072100503c82c01007080d40c41e004940d803d40039180d0040b00c0d40b0100c2c0201d2103068101514a201400c00f80c41c080e022801c041c003502100c4d600320016880068070750740e014024042403004100e244011070420055542d080c1e100d0003899507141428015a040084191055007050450303903008d041c42c4110304140d0b90007409030014581150007501500009140d0307080c02c2c0b14640d1016001000380c011036200b40e03a5100c130280344050036102d0589038460036071386078001c1c03001290903c40840c2030b001183c90400c01800100059100d40e12803146601001907503600000840070807081e000d00100c0c00b2003904821001002a00409013100720303e644007076222802100c041651200030640c2813054482210300c0000e44080411404010b0410301060f074031403d0075030186420590822010890f0f9400c20728a004443c030071100e403041404880030b0342d40745410520881c210924080050b107019102000c2000c00e401070046010418800001c44a004201 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 354157940 1250 354156690 354156701
    0x71b05060f07020913080315010e03010204080115080f0c010311131509050d0503070b040f1b0e07020105060915041116060b0303071e11030a03020f070f03020a0315 72
    0x1001800140c0701c0004091207203490704028012401121558049130f007080c0104a241442540288907a1640da1240c0703001c00b4480e8080d400505010325a9503100762558280040e1001d04401c00000540740b91828050245600a600a0170396401801009600c0c20010600c0c2d001000c0038280403400568902800e0b409118144004454424003400480c804213080600c40045d01c03a9640c0fa081707141c5450400045158204004005078820000c010010f10302d890041d50160151f8030804041c4010307150040e4030210808445a0865048410300070f41450034101500401d5074402000705142c1500481d81200002c0c0078507a1190120700b541e001d03941d1340c1c0c102141001104c0585d98031000301240822524580f90012500f040c1401151b40260900005440031107402007903081c01c0c1002801078044814030010280c1d05094244030080d05901c0412880c005944264010503103e0004140075082040307a4000d00d804060b003403403c02c0036941d07082b04101a2504400c3d900140d1605c12441001400d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 354159190 1250 354157940 354157949
    0x201110708041e15030b040b03070e0a0c05040f03050303060310050601170a02190903020424031509081614010e070b030a020910110706050f0304080a02010e011505030f0c06071b 78
    0x20781300d0340310420450b4550050000c4074020388040c419204034604264079548280650302c4c120880130005540c05c0e40b140c000300030003240da0030800e240503110701f501d500e01d05c0320303030415203241c2d100005118081c1000c100d0764440d040700c8541086241400000208048514469205014100c2010800c900404c1d030440b4504480390f1034507080d14055120142500303c4611050784507614022030f05606081c1384400101441d00c242a400c0c0141c110758902d90501120301c0f1007581980d441d0700f48400245464020569410b140044014802544c64001d50005041105c0e4800d84d050140150f000700001038a60183c03108200710945030b07a1003844045c02401200d003400d44c01000030800503590f0b0740081c54209003105950a0b680d03c1c5840c0d03038050342e15100705401201d280400300b0010700847e00ca400508000328079840045210b02c1c41030806425a0304006204402980038001040b891500708020059401000d0182c180c0884074400100e0300c0c000c01030050111125140b0007202c401d0060200800340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 354160440 1250 354159190 354159209
    0xf0f13020c070e010e090705060c0f0a0c17150117010e0a0b010302150a0e010509060c0706080610030b0d0b091e011b0804020307170a06090803070201110708041e 71
    0x20005880001ea0302d80b00c5114400e00c4142c1070001042c9960514401c9100b081c040000380909450101400215800789500300c049002c2c00202114054092104006141c00359091f03180c11414070b00b0403004400303440f00741340f429030201000c03407600c04900c06a81d0441d00090701420050320680d10660151140d0410000c0901032404407008003c00104085c0c16a802130f40c1f01c180c0c2c00c41d000306440c0f50348900d980c150017144000010010540c42038008004440c40540f040b4104844140341c02d191044030b41102000c00c000104000203801e054030b140c02a0319552074148140d480120100d500780200071800b034903541844000035080d203020454101c4e0071400b003410310004080c44400d03500821042840710394002c1e5500d0094083c03403103464414001c50300140500101e178030b021076a0648040c20712a8121030b01038280503102007145442881d11a50041d008980e8074580400000d007110804403c0c400c50103824859803000c16040c5050700c0642d000310804114085038002e902c8410803480d402103840 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 354161690 1250 354160440 354160447
    0xb0f0a030320030c0d170403090308031e090f0f0309060306040528020a020d0801030b0a05040309050a080f0706030501031e06090807060209040501270213091401030b0f04020f0f1302 80
    0x582c40c0009943da840700c411b94071440188207030300640b030700030b0010f440180000d8441d003c03d10106134620000d42d00500c903c000d0400c2c0e45044100b4101c81031341180c080b010798022070300302c1400c4d640070312100a0036090390001e981b40000d4000007d100e40405841c80e40201d5a030400100b50380d42103269507542080c40601c0f071030484440c034600c1000c2c0d84140700f038030014090120000000d50188080c43c0c182c960020312900e41d566200e00030b800a2070000d1080d02005003c039030015003611003144020191106a01508c103010018294910703001c400d600800815180c080100046082c49445200e100318014092101403154148030011b81840d0101520700c150004041040200ea03a0080c02200e034140ca090249a036103050b4600444001c1c0b1400a254500c4030000f1825401c0764018600240c0340c0c081108040c0c1c9984100c0c080710304c0b2440ea03c1003042510010320510104002040d800004000032401c90714080d4046518214440180d9000ea0080d0a01303111a540b5400780da1840100c0b00d004544 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 354162940 1250 354161690 354161707
    0x22020915070804092306130b120a06110c030403020607110a090203040b070e100513180c0207091a10020109141b010e0d0215040915090b0f0a03032003 66
    0x100c60380240b0442c4e4402d842c044801c607480a102c2031801450001d146410a5669020709200c015080416015080d540ea030070015000e40d07498604610350428800142003103201842d00c101102c542c401c10040300c034800d00220089040010458042d207606a81d410344804081c64081925288031201d643d000c1d110710b5000c80c2d804060340c0a18415801800e548555444480056071040800c880040d0040400326004a07521301580c0109074090044024900f0302d07a50b00101558004918900c031200d50702c440d561f800c0c8a0f030400503a409842c8001003004020201c255403070501d0b0b034800c107a901504c2c540b034600d6060760003940500362898019103038002014241070100d4985000700b601c44001e120090070000d040d40325124501500350040d001818034044c5808002d4450f0007070081c080420410400803c035070440307011324030510f514004014001344c200b0301d40c0c4003034a0100c4046409500b0b02800703e03400703030b5447c618001265014142850980c05e040c0b2559214210340300300080c20301c00001c03c0d68 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 354164190 1250 354162940 354162953
    0x3011203030b010503131e140114060a21080c0d020a02120102040e01030803040203030c161a030702100b04020409020a090305070e1e07021504030206152202091507 72
    0x285100e209540c10859103031400010b41d07081c00261202e0500d9540c54840500140c401440f40c0c001552005600442100310354034104040c6103198036038501c0e5180c8030740ca0140c4101c0c11b001508104115000c400e05818400c00403c007141400104603420000801102407100d0942142c849440f81400d80d038200041d85c5010350f0702c00054400728000c03601c1c1c2c860180b00781c0d01031090b10706072103050040c1d4901e6440c4da120349500e80c0016106a0303142c08201b15074176074041d00300700b00c110310b0076047e881e038404524182400d1054031300c0304030305040800c04004010240e503000c41c00c0c40c04046500700004144001c1004030340280100d4103c0240036100081a41000d0703017090000782144d01c40c00840d0b4880f502d560003080c1c0da82c02907c2e50b05d0b4083d4610390310800228800c9100382e101e00d86104403001c3c04c00014414140040695055015801101c03d020a158025080102185041d144202c450131480c02c80c0d1810201c50800301641580410504c0c0603540348143c0905903120603440580b559020b04108 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 354165440 1250 354164190 354164219
    0x312030406060e04050f070609080c04020706060e1816050108040f03170c0c0616051642090503042d0609170106050303071203020d050907091401080604080f0f0301 72
    0x30710315441601c4001480d00e20a200c0271094801650180c0750b100740c524107010203900050804c407a03003a26480c000c245a00642e84040c03241d4003941c1c0c8000e87c40114605070f800c2c030300c00c909c49000c2c00e1480700042c130036640c02c0410650420f070b0012810240b0341590404551540c0c0c1d240c245801001e440c010b001164a99201a000c5501150240e4449454014425100754407104081d004a0000c0c881a030003006600110740342180250200381c0f515400e403c1c0c880b0b09889038042e070014030510130442034050440c0710540c254548104004c00ca59980341c0c4810340c0e02d01552191940b0340d044a1004103d00d441808407000710b444004500014948845000d80350040c0d5004125482c0400d4809861020050103048102d4501501452600340c3c0340d2999a0784c210205100c605150f002c00c21040f041850b03219143c801e1603040041c0030030700c0c01c00c0e010341c1c00c1d0380d000800b0864a500350001071100b208007094407a00a644500400d03a11140710a100e40d0358010840c080001b003601000000f01e80703001600c0c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 354166690 1250 354165440 354165463
    0xf1305010e090708070e04060c1808030d0506040b0f1219111c1203020a110d02071401090305060a1a062113030f0f021c030b09060904020312030406060e0405 69
    0x183d820844d2900101c40d52001d00d07104d9015034100700b40c00f24020a086a001102e441c440d46424640380340000c03542141c02c2e0f00d030ba0104503075900c0050303d1040c1500503c196600941c04840600c6443c0e07000c00001c0a00003500d0086101d2080c284d8189440ca400700300c00c402011400d0780c01c0c50a0005030501c5600d007a80120340c10700408600b200c803000c00c1500e04403100e240340e121411554800c0c0e40c0c4e2045009401c1a031441d424003507258107191342e4400811a96045a101d50300801c4400c0c2448400c4444a1202e00c110b0305000042c04140001540802c9059004102a000044000311611044480210005103030380010b070020710712944810718204130006105a45d12806261106940401519043c00f13010740000e4208041d1094548508400248507000348110395500718800801c1c8404450f6240c00008a41e44500c009110300306820103c2e8455030031175500c0458941a0007094845d2600054201c1c00380000001800704415944550060308101d2141401440d0524003555a48583e844 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 354167940 1250 354166690 354166693
    0x219080310050103020304080d020a03110f0a02010b03030a170c04120b07020601122112060609090609020c030406140f030a06030506060d170702180c0319090807020f1305010e09 78
    0x50100c0d82d54044e008480c0220b910905240c50080d10141036002508240b1405c8205901d510f256801200b0340e4010b040411446d150041da40c1001c4603029003102c0c0c005040324040e0b042400f4840049401070002c44030859000c0e440c0900755038100780c1002c44d11440c2c12424144031762072010020321070303000b8840d4400c030381c00e808030341d601e989800304a100e4608418000700300117107100b000341600244014006032240d041c10400c400074404000b480c1614001c2d003283c07000039008441006103200c5405034400410140c982180f801c504400c0c6147c0b02d101344d002e410113004115090300c03074142a60382100d05a4108640349500c038100076454101400c554402610f540c40780c0000304e200d9240c82e10440c0711499101003240c50400110549000c141c21400c42a41c0c0000c460303034550084000a01c5445c0314510303401f0f040d0303901d1030120540200704c031000706408800ba103000055000500300c002102c1342c0d00e80403100d03006203080d4034002a010003c2c0e07180c034208050408000092035091000e036240250003140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 354169190 1250 354167940 354167971
    0xa020910020a08090607020319051b09010317090307121b14030a02091506120f13030504090504060b040c0801170a02220b030a0c05130b130c02190803 66
    0xc0100da0301c106018010380303d480300300995104c610380f4100034604103101800f1b9406c1c9070340300fa8a8a00c5080d554005036401c1e004103d403890544524440c00f140c00c0001c4400094950641d00c0380d10b0485a0140642000840021002e2460754100002c9008000f07a0320789121002148ca403084d21901040c02e450344c4e2180320440451004a9008a02e401c01e40240040264007210303000c00601180241c02c084051803102210351481e120103000b130013000d40e500e6411060341041c5030070000d0840c0040984801d00c51019030740000991210491b401c40d035030720001141d075032500e04000e8000d056115409500500d042401100e80b5001407450b8100c60340384418000d114802070820b07440d080b850000a40c4001211001141c4c105004550780700008204d000103500064070000c6440c2192030303039003506d6008051608015030b292485030104c00010b040014032000440e080410160300c013008822200715111000e448155208200c4003086030901110b50448170398900380102c40e540152507010b1003202300b8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 354170440 1250 354169190 354169219
    0x70609080c15040f03050a0209090312011203121b0e03010c05090405040f021203040e0a06060c030e010c050610030611030106051c090b04080a0806040b0307090c030e060a0209 77
    0x24806042225518006007011004500c1041a92008080d000020610512011581402d44181ca0003d035203d20010511140c15004104554800a242c105668010030250411103d000344080c11200441201c1110f0304140c901030310051038082003903140a2415000414125140400e03491088190f21090f4071001c51005060984401c03040600110b2020444680d140c202030b4445030380140510614203051038a940000e02d115400c0110000325407000c1414060044201c450701e17003101c41648104111032400c54054000d001511018051088030300062040380d0003801e080404503130007002c1e983d1501e0002c00c3c500c030a400901041d80c105181c910001603000100c411281611801c1d12078504005003004036091140c150f9554582c2d540d1100c1c0744e9000684200c0b061790059100316103684d20382040000092007080000d00b01441039080c049036484549003c503525090350b40d0080c0218a03030f040100250068903160704c0c4e44c4030501c6103008210708003459501030030380360701e08446501d01c00048 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 354171690 1250 354170440 354170447
    0x20901051605011415120d050f0d0902190f0b041a07060209300718051308120a0e061605090103021e040302120d0f05091f080402040507050a08040b090a0f06020c0706 73
    0x7c4204180810410000c0e0030f1130041040280c64002c0040e40041081c5100364040394144c50222880c400e0201018802d02106100c00900405071084039517003402c140c54044003604050302040d80500c1400c00044003002e02c1002d8044074455507016150701e285440c2d414407440d06c01104000c00e0202000708006009001c404104041101c2c0400811000c14801c000c00400801d00035081c0c081258521a032800000c130b005010f45403e1441d80080340705881c000e01c00318180c03034800c007101d149a04440704114020710150620714412845240182d124100f00b40180c00a200e407068002c04e030b0309034080d40100280d80100030019031f44241c1d101c2c09085000c2c800740359928682c94450010883c4188030000e40d80c0719401030000c06c00c1c0200008100c010310740c111a6606200c20866000921400820055007000d000301600940c40345003540c82c16400360340c0100104000340004041800c01004149402e07401c00a49146981207950364030503034640c0c54540000e6000301c0f5410728a0094080005810b0300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 354172940 1250 354171690 354171703
    0x50102060a0e1e16062a120e0103020c1009020418051b0d1719050f0a05070f020a060c1a010e041b150906030f02090105160501141512 59
    0x301c1c002040302d040c03072903012482d41200480c0c1040511601c4e480c8402a945205100020200b9031a02c0b40b07960301020011a0300c144400001d0509104c0311801400a101850341c156403038524507112601d2007460004a0181c810035242c030032203210307107801103401030200c0d4800c2d030006200f103a08000460305401100307521640250081c0082d04440000010440340401e034071902c0200400390090389030b241e42c0e46004c01a60024032008a040441d07041010080d60002c003a02561609007182807038103121032000c8920548400c0d0741045008180f00c0104160180030007843da50003000c502c80242c841e4801400c490000340b01303641c990039524480480301040d030005816a42207641c5201c00d07030313526150312908000182c50742242e4802d0711400605080b6424440b064000203a4564a01c03d180907401002d6522104403085a9441045070620581e005011641544810080382401c031507070703045c15801040c82501880710034a4000802ca400340d20880f022480c210100c50005044140c4003401d540c548 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 354174190 1250 354172940 354172961
    0x30a09090c30051f0501050c1920010816030f0e01020c0d080c04050f120c0301111308030f0a0c080c03040902040906061b02041503020a090c0206070f0c02040b040f1401050102060a 79
    0x5540c40070f0089501c24401841038081d10301c12940127854183c114044c500c54100e01f40d40c01228507820f580000e01c045506220a1000d00c2c0c00402402c05e0505000304004008806060550362040e40e90142003d4210300d2011402100071504c860b40400d12544480d845c2d080c01e00001c607100d000401c4820000305071000d44201520501c400c403031820038000001c012407400403041c4248001c022880d5024004c030b07002d21800345035098845504035810580289584c0243c84660024081f5071426040e01c0160b4100e09454036020004c503102e400d200d1001c5c403400c60030b8040c80c00f0009004c61110b406030005e04c11030303100d40c2c0304000c51503640d0812241d81409028038800701c01e801c101d01000d85800e403c61420003132200030740d100300b42e034a81c00101e205039143e02c800c28841c0c8030214081c16940520a41c1da101d4500e003003c070b0040c0e0741400000c00f105079041000744541e548060b0301c01591a00e034003045005040e500100081c03415880c186003010350901c6094018401c0b04000b8ac0505828041c5141b0030703 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 354175440 1250 354174190 354174241
    0x10306051e100c02031905010509031608130e01140f04090b07030f1d01050f0601020a050601090f06180f05070203040f14030a0803160e03030a09090c3005 68
    0xa029200c104103080101d002c1d610704010943c4410405a6414031459048051000030741c420301c1c03201c0ca0040c0c29200018400382c1103800602c0b488043e01c26070b801d92003c00764410543c0740da417003a4181c802c8103c2480c0c0c20107401d965659001190074210856600c0d11007404803821440562200700f04000d441d06900c00a1405100e070002c2407406001c0c2d0414082040c03048400b0481c040104d401d120501404c004050003070703450b00140a5084002ca140315008007080c0301400880021344c640954410042c402d4a00300307070340c1d5452540381070501d038020340280c4610004d20440141e40b29200000d03003003e00ba40c00c1181d1a000200d641c250000003110f08480004a4201c085450010403904024030204c00a0701401440444000280640011031040495560141c0341d80f4451000030328140720910001e00070307072081295003816904008203000b11a41c0010100741d12a40e02c8044548214140740d6501c0d02d217507488907151841e102041c1068043c40503000b08516a05c4a21043c4203140000d03981d0308c1c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 354176690 1250 354175440 354175489
    0x414060417090a0302040509011409120a080c0d060b0a022b030906020409050403210e0c06070221030a0311040b0712020a080f0310120201021506010c06060f0501030605 74
    0x5181068020b40400740b0700400060401d6030b0780d00842c00b07031801100e803a001c0365940c09104811b65204581e03180c0000e081c400411403a41c000c02e94141c68841c5114000c18004032100050a40398680100c1c0c08070200410241b06c499a030310503468264106d40c4005000d8020b40507540110724881e004415001c1c11005410480049580300f50001c00000c041510b02e1902040007250a007510300940d40640d203c0d07038424030100e402d26804e4017882d420321140355006041c402c80f940e61000000b1900884041154020f035a0101d07403001400c46020462041462a00507040882105010015184814080d18107001c2c805010040c1c2c0203d120b24081c04132849418800d40307000c140d5850a10303070200303c2801102e5000c5404d40750700700c060700304900101141400008000059921800c0140100245408c10f0900000303580080e4030341c10f81c00b9008903103c03140e1700017448aa1181c140046800e401071020440d99448510500c03c2c440316014290100c0e09001c0c00041d44c0c00e00c0740c1c5c2c0c43c01d4580341143c0042c0b07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 354177940 1250 354176690 354176723
    0x114060402031314011103100303090602031c0b18130b0105010e0d0f0303111308070b070b190b043306080f0903091e10111902210604140604 62
    0x91107100c4c11a00540d82c5840c841a5110281e00840c054020b600ca4600440e1451030000c0100350075070030500071504180041d8031101918006040414140348000c1610381040d0041658101c800c1d1000030f45030303416010301c12808003030b20b00040181d009041000d040da0b03e4030015211402210a1160031001d0b20740080041600c26402070b1079580320785404141c4044074070319425203400034485100300c0d90301104100700f810380070803070320004041e00c104103070a259554a0340d11110400601d8461443d50103010365660920b6035005200340300340108100051a1403000c210aa4101500081605010700341088948125100f2241c12520140d45000450b510381c511b60700701c0d0300040c00404251009220445003550f03400e5441d040700b4066504a071954901c1c00420224165040100003400804095858917406c041010b41c80080c0c0712a01e40c0e4491031a101044812500300c4140510b0050201c041a400c900071074050701650299a04402c0c0039407071400e00d0744600e01a40e000f0207140300d4200001307 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 354179190 1250 354177940 354177953
    0x20123070b06060409061e0801060b040b070c0504020a0504050901051e240409090b0a05040302030421020603090303010f060215180309031b030d05180d080d06060201140604020313 79
    0x250b1015000d050b25041c00e995807894000d441040d00b2601c0c0c192240000081000c64002c070341c000400504000340034082c58044900c05503c103c5c0103031070002600051250038071512614000081802a008564a00c1c03100c800070306d140c0250180764880c00007480005002e21f4107980b0046c03100c1092440c00080c17100c91301040004d21032410030400001561420a44c20259100500014195054042000300c020709d494206080004c6c400f0f440d19292600340000f095000044e501644c007440007482e40d0718600c01c10aa0714003100c00f4002e500c40d5000080081035500440038604a940302d5a01d01c604a80b0381c50141e0300e0f0300c5245469405035144100003454455006103036001d0802c5101642c0c6010410310200b0b040280e08016290030400416a60f00542001c200504144005103411b5040c40301a0b00c7c0700807003440c0842502c0c860b1003443c04001c207101c480d1084442e8840800010440d035030361510003a018241c041d9610742e5001304003001600e6400c290007102e10503040c0704800e04200e04207660f5071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 354180440 1250 354179190 354179213
    0x2025260d0e030a05010e030703030e0d090b18040213050102160e06040203060a03050105040b10050f0603010e0901111b071205031b0f0109062004150e03010906051302012307 76
    0x242d81c1446140e9421010810038420341441000312030107965a94190304001d0140d03107202804c0803550b8442c2c82d003c07840a91005084060380c5114443c03a13941c0c0c41000340c403034840c007075440e005502910001785c0100202d410310003030045840a80907203042c089003103c02d241307005207841144541029503000031b4092405030300031980014024030b1086010780342d8640300d085400403941118019128410b10160103a070005020042008440d80700c0d0084025010a1042c0018401c0c000200841d60105072504020b4114014521f00311002c644c590103034032880c0d265600c01c100b030400c0701d000e2000041b6070081310715040c0c59a560030038001c6240140022060000506541d41306505021b001042c0400034020300502da800c0303008004c040741000c482109245101d0413200e1040100717404000400860301e090400140040460505070203001000000c0b9001d4204400007c085516000800041642d651081d05640b070003a42d5909062900b01104c81c514020348044100865040c030483c0000351081d10301 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 354181690 1250 354180440 354180467
    0x304060c0234090507202503030e19050603092b120c020c0904110a06080a0b03160b070f08030405010b150702012025260d 54
    0x4590b6403010900d80c0d10b0744140103560140c0aa9182c4549040303000140d29680081e02d44a0400c000d00c0c10314000c0906154884118000d40c00020606020704034414018841c01c000084c884640c1c5840c0010b600c20303500c00e140000c40c003141301205400e1460a0955000072610782d00901e07007100604040c01c0100c6900700400031300c41751066869220740f681ca008400f081c0b001da4195116010881c555018011210000031514030525040060312a19400295400f040c0c0b03040d11040c24680341ca0a0006000225056903504805541c00009426922040092154000359010491039090008140c0c640d40a0070103400002c8021809000d001c007880001c0103030505c40c44548072107145a07540c00301e580d0400c5070300b030314903941d16400c246a6043c215864140034030014045443c055050b40013074645661503102001032005e00032403000c500c108000c03004014842280a0002030381c1d51820b46a58243c9001c0c00e400c4903151f2560349151421409000100d100c01c2028007610150741400302c0d20861044003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 354182940 1250 354181690 354181693
    0x18020607051e0d1b020d0803040213240b210c07061404030305060607050316020402160f020a0f030c2c0115080f070e211e010c0e03030304060c02 64
    0x42c60034084114488030041a1515005005030350281c010281444080f40c0740911022080041c020042e030300d060065042039440b121954070f0761258000f1414884200c402c6541440c90440d040400340b0020f42c1c00245a0b84654101c0c58075600c80301100c0880c0591390103542c410180070301500e4030001800070705a1004140c1d0350706041050035250003041d51824400f8200741c003503450901c0107042e03060085603801103060741c90038505031450f83c4051b0341c0c4c45030312281c02081c010200c4000c01c40d510758040b601420381e007100316500145103043c00349079104038020882c491500b4040000b1600d4000040e001201d03001007040c40c007240707405000000703040da01c61340e05c02500400035510702880f12001c441c2c0c068440207000d80c141d16043c180c003406202001c0c0592054404040801030382d41d500102054240c182a01c0248c54003400943c00c5482c80070a6440109502545600c000c0f2200d2000d10440904d030280e00034425080000030546456400403903c1340c16400070000240455042d8001030416003041c030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 354184190 1250 354182940 354182953
    0x120c0f03131103120c0c0a060207090207050a02041a0102060601030e0a02010e03100c050408010e0a0b0a1805010606021b090103020114070311070609052806030e0307080307020115091802060705 85
    0x1c000034100300f01c0c1c000e2080311020100e107145040c00b0401021100c0310003030340d507e400705041c9400a51740301e49502c2040ea4180c0c000403c0d20402c2010711080c807845034042c2c001d000340521050f0a080702084900450300502c940030010b2141c2d88207024140d03103614040c002c1e01c401c01c4140c004581707861204002c1500340c480e01c0c000100d0015580b051020700741031a90369a440e03504140710582910700320b81522211f54001c00c100e4000c40c5c0b40c152000d07042030440e0700000da45501c403850100c00407525800134005510703241c0c2c005813040e00810b4014800c2c234155540035000503e5402c00091401c2804040e0020302d9100b0403824421254000340031150082c02c00c1c0c00721200307000d44240791a0741074121070700140e0020800c1009050150400e018401a008400011a154040c00b003a50140d44030703000400d500c40c003051040000038411100b40c0e5400c600030590b28540000080c2c0a01400c0c0f1804004108100000403103c80c18400c580c61305808c001c45450030fa86a4003002229003111000780c0f90b9024a4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 354185440 1250 354184190 354184223
    0xa031b090e0a0c171509100e0703020a020c041b09171002030c0f0301140f0d0b0712020403050a0606050a21060b04060e070807110d0c02041a0d08120c0f0313 69
    0x1c8950a20401061720105041d400d51800c0c049480c2000e0716101c10860084402c0c05164550201c0c00e5102e0581e02c1c006854050701e01040b45809100713070f000340d0080e107401041c0c0452200701084c40340041d4a500c5100303505549150488200b28504039003131854110b800d260aa441040d0015034115808510300e604000e0b003060103034071031751081c1d20540491720410304516041c00c00210000c08060100c6401c004908035480b080c203028402811301c000c008580c0518040f204c60382d410356000e140c00c0401c0350030100c001e18011009190901607a4400d6507501000600c1000d544421703a0704a100040c4070701540410390f01c20018041303807a01d050b8055103594010450604098403a80300c0c151035600c0c030f091402e100d02d0240160008a5814506070010504403051681104100700542d505880000304410480f07041800090400c4940303a01103402c110280074460504050000c440c0010100c2c0525100c18600c81b24600c144580c0b000000d10a00000e07020313081d60040b001c081401501070f41e800003100d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 354186690 1250 354185440 354185477
    0x302090c030604060e24150f120a09020a0902070804211101081612090c241d0108060d06020309010c030612030c0f050c060a031b090e0a0c 61
    0x45036140000000402000658079013030041c4002420341c0000400541028842451812000d80703601801002c0601c0c0c48030a03844401042c0700200c04e0701600c80d1200c1520100440f00c1d4040039000e0b007507405e00d00c08152400d44500c14250031582c0181080c8400b40b0f081060006504400400c0c0c1d8820b0741800001440049585a41c90380081800a21507a03407a070314004000d00340f249921070400440c10204514104064020880b02c841c2d0300745190002c042c4141180500780c41c24004202000c0701e180062074842000740c0c0d60b90f0440e08501c402c2440d0b1040011510705031800012104c05049501d05401ca50254010035000000a0075480780c840e065121030042e644240d40b0308403169592400d0300c50b0b45030305105240140c000003180641c0c3d0546514020a1141c0120018108400240203101000000c11100b414003038050141d5480b1040380c03001400419444680445824010f4a44224213218404250079520201041000e50303c8044d0990010401c411002080c0043c911700d4035004000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 354187940 1250 354186690 354186709
    0x1f0f02240601021b1309020415030f0201080c0f04050d020118030506071b150221010b030a0c020f120a170f01030c0503070614090f0d0c09060b0a050910090302 70
    0x315001809103400c00034002403400c00c0400820342441040d61315071650750b54503c805040c10700314550201d0024401e00000e0024039058248648949810303d0002c1046010000024480c0c000d8070380400742e594480503007420f44100d91082c4150344080005000718544041c08400003401854168031070307100c1207051a003283d550340040e5916480102084a615805840c1d189135019174880340907809115500e101c105080c6182c9105420b80210b60760001c6040890100c50102c116490701c85656034448062005500c01ea821a08960418991007800c500024410040200303410040c00144907a0302c0320341450700418540c1040010300b060202c00c404403d0304840c001c081603010590305524500c0e0020002305a50301590181d0080b0904104541d00401a0804400d40c40040340ea603148034400103103001510200c4d240e1011940400806200003042844156910881d080145540700e410003405402209550000540100002041d0b800c004101c0c0d200807d050402807596900e0b54002000c000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 354189190 1250 354187940 354187993
    0xc150d021b07050d030206060409110d030c05010506010926100606050408150c0a080a09080301060e0102100b0f550609050d0201020f010c0507111f0f02 67
    0x10100a101080741c8144402401080c04440d600b5400440d90740180d102c041c02407140d803050366201070701c3d0144211800f0010f2005001440156030307246500e030181c1421030f2402c1c1942c042d864000001c00c194041c0d0b10240c103036140140b036a0f61001e00038050400c03641c8220fa00ca0018080d16060b00c0c2403001c1800b07104094843d5031142c07034a40d402c0031241c1d460400c0810549120383c00c9101480480103180c1c00700c0c0c1d0f1002d1185410801a680c40740360001816400a00400c04034000000107100c0354024485401140700340c1c00d6600b12114002488242d6160300200d55004c0b2001a03031041914007000c3e486600c40d001505c002d044400910300c02e9403011003603110800039440d00001c001c2c00c00c0c1100700060b52402c0c011010341e00b50504070f00070101865401598016011141d40a095a0003040510300d40345100c0c00074407020043c0780c4000c103e600300400849551042d50001d00461902c0403c10300c0040d4101180c0c5131203084d860b0204c13062485845903000b580604040190f18078584c0c1c14601002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 354190440 1250 354189190 354189217
    0x51c02120c090604090b0c0304051f020904050a060b04060e040b09010b0c062211120604080c0c030102090315180303010609030b0105041b110111120601030b120c150d02 74
    0x2181d42028444107500041032a40b06070318201041002404044609401100c09004682c482d40c4030320b0a240b614906003142480950300307084c1c03610080050340040070941010350701800300d85c64021208003914414014a506041d0521007400351520070315541c101414003c01c00b00741180a030b804241080800e0f00b12010140001031003614107a82000019001280c03144007000414500c012099100c4501d0300060280f0688046001c2c169100202c480e40012048140d03009410f2902d000c0081e030780203102104070b40c0030f8050701e104245018401e50b08400400740150a074441454042e000009004107005041255091011000001040554082d008548400810030f081d402d00424041050f441130344114141800781c52140d143c0d464010b501080b40c100085162032030035200c0e01401403c400740d403001c00007040313891a400007244e076540510350a803020000c00c48440d05000d503854090040402547c02907044224904003030045444000c0c03004c0320b49041c002c0f0a02d405003660b20207090002e41 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 354191690 1250 354190440 354190453
    0x627060d060f060e031912030e0f1b04091e061107060c02010f05090a0605190f1d03070b01170316080901020c0609032e0903050403120905060301051c0212 68
    0x810780c2148500c400c005048008211b001c3c0250003013118003031018001080441e82621070b4076003030300a40101c174a03102c440044e50b1403500303100040c0d6038540d1020191591081c0c1c4428412042c1002d00c204503d0540013501c040d0031468101300c1c080f030304800080480380c580d9103200074107658a0060203080712610030305e004a81d5140e0400004c0c00d4450016442c541030340380c6070a10801c000002107040c001684410080351565401d0030384112404840e007100300d12030500740201e0a250140e4071841ca42410640c0c4800900701001c181592801440b900030500a00350300140103080341c01134008000070800741120f20304100e00c0480c030560310000200300c4841070f010035003204940e0140001148005c050700c0841c2482000070020340c0d11a030b101d40d18646098074003000211f04020846a003d10440d04000b4094a01d8903e002400e0790300500c41510382e03d13400e110b44c0c3c003290311601f1101e040301d40051541e07040d40d08000410007014120480804900c1d012030405006840306500c50540c010b6030805030070b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 354192940 1250 354191690 354191699
    0x31506130e01050a0f0612090b070c0507140607020114070515040524070509030f0304030503070b071e0e0d0b16020c01080c0703030c0c0f1b050627060d060f 69
    0x40c00303007040e00b10903c10704140f40c06201c8602844214003c8035001e02d0092005050b91800e007000306001c4ca03000e0321903000d41e0200028a80c004620510052168040300c81c119a15694412804e505140c0700760710110800c0804055071107004001410f8480080c000d2070141c5e1950307020b2a04042281c01460f91500e4420041800b40c03e10035071446591800c0365003070f2200c1038040b00700202c4d00140a0020310501013405450380e00c041207199010000e6004481c1d6503a1607050560380d039040800c1c106d4010207041c0002d2406803140e040b0041d02c2c1041c04031840925421142a80c1176611080e00a801007202e8048401207500001280d001c0c00a4940240905410500080c140aa400310050600040e0030034012222011801ca4020720f42503c0d00180225001c501156541d10800000d000c019074089000180440c141c1c00c02007200810582c0346909903140d00303014003402505c01c010a180c00d030007071640c0114491021205218002041503141c400c070400f840003150055008005c450440040a20 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 354194190 1250 354192940 354192959
    0x112060801270209010302041503170c06010f0f030602030a110d0b010201050703020f07020907140a12050f07022517010203041101030b0907030903052709070801060e0603150613 78
    0xc154a0380c0158510329481070790003007603101d130040c4002070003942d4030b042c01d13030b69000c0d920525006554809600360485207004040d9826810202c40076074140560390001035101c550340c502d0710407946050b030003401301860b40c4c5411000f0b4000401c5078041c152203000c070403a540101c0c40180b80300d5011030000201c2c01100d01c002030850320024100c0c0c0a0610400c4108170790800c05055480310b40c1e04680c064807540d03840030121240c0011058002e143c4001150b403007945508181d2f43c448050203d4030401c010b6988410241c40c0750801d543c54000760f0081e0300340a100e8004a000210040065030f8207ca28540d20b00c4100d648400c2440f40d00200e950200c140320800000103800401c542c001d20341070025aa03040000307420b00310060305e0481810b54440c100c004060142040e40c1d8102040a0f43c06070550f4000e0760759150301a12041240f0031603007040042d60717090007640000d0581e1880d540710ba507400805001e11159510152109095540c520031146082c0d4403000113156120080410305100741c03420b02c110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 354195440 1250 354194190 354194231
    0x3170409060e0f070509010e0d1e0f1a040218091501090903030b030102090f010f0207050d08030103060f050408160c03060e150c041202090a0216060c020d090503070b090112060801 79
    0x81c420405d041082d020241e03882850b1070303c0c06204640d100300a2081e441c18080210001d07103204a003140e102c0740303601402404101c1d0204113020300315000040a40c1d1815407001d074000c55000350302203103405c0c503071085140e00c010117540041d8980c01c1315449501109008800300c400d9105820454030341818400301a03240c02001000c801c150025410280c0c48400a46c2a0600101e0941045000c1100703003d0207100300804401085d014000404045403400c100400d513100340400d46680d8100600598003500034441c1511443e00844454102081d41105241c50b142111701039400c207101801c0800455031911851845c1401240207004000350900c1c02d0801070401000003040002c18003040100e03519110b041c0207850382c121509002030752400240700081c0030390101c0b400310010308a1340504000f065408407402090036022155400a141000c4500d030b15a40245900b58000381820811140103030047d00c1d03e90014100403010f4404000c00c0d6049800fa42e0140d101c980d1140c07500d1003080032050381d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 354196690 1250 354195440 354195451
    0x3050f0f06011503152c161e0905031009110604080a06050c0706020c0f21090d031b03020a0308010b0f1e0f1c06080a030903170409060e0f 61
    0x6012550b00d4003020100c415107030346101081c10b4560100008040320112000d0146c14080b4000c0c1445a044a90f05612410006000c40386014035001c01c2c1c00d1040240c0c074084299603961441d287c0750100000c1c0a0142c200407403a070510440c42d00102d4180d0741400107603ca88400da400180143c91814440261410301d4121405640304000610242402080160000e40c0002c0041039580716030807141d941c1d00c100c450283c80c09101280c1441248070103c1e60003940c80030781c021202c506807001310303604028a003000c0008040e5400c100c840c000741842c000310140140203042180419108d4400e100003103501c600c0880040e0420a880f804041e0050130003405809003804050420400c055868020305ca210002006c029080c14421800a040c0013240c2c190076580b41010340300d54041c6140300680c40704c1c04241480d541018408154000e0008489030750380d0305541d412001920303540310040d4080c0c01e010302c44450803007000081805840d034010500100808540c0726a2443c2c414004005600094a07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 354197940 1250 354196690 354196693
    0x5040207140c01050f0d0b1f02010c020d18030b04060f050c1c050f01060804110a0b090901080307020d15060510050706050702010c020c13020403140a031206061b110a03050f0f 77
    0x507002040d05c4e00c0080e0781413280c1c54000058020b0000c0001214266000700c054203e4442d14540981654190010000104103400b25040440c0740070066400c41100210001107607124081000071404051a254016001d11400507800304912542c3c2e0944104440b90011030340c00050141c085211070800981204030250f0400041c2002c0c84041e070b0030360061007403034100b00081c4013003000d01103000444403071010010f182c507468540e24003001441e82c00002d0101d1243c010340c0e00018103403202000b16140c0c154000c03c1c0c6040c0201654503a00c15605440c8101c58044d642d9030b01107245d4440300c4088001c0f11080c0c413115200d88951910605071070b0002d0107031045904080768550415000641c0241c020801c03201083e6a04c07070f015010000740141d81c00500605004045044000804102c80e02c0d0140244e84a0142c0f0240340c01d0b000c241e0740e80d40306400018040c0006150b2a859900741c1591940c492102d034070001980700c0009040038029081030341c40740c01ca21006140500100604500c1000701070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 354199190 1250 354197940 354197947
    0xe1005070209130206090409060f1404150213090903030b040b0d171804061d0906070801060c0303090503120106030b0411040510050c0a150c1409120705040207140c0105 74
    0x1804180c21160190003601c0c2503c40044890456484409503024818054000c101e204c03041e04080003c0c0c507070011400741c1e0502e81030700e1241d50340580f0f035080e100c0c82d00040740c0c0002c107807000003820080d4082c0003503608070003240c8004a1001c559008a1051768003030fa6000c1303030022a51301080120b030f40c3c040c2035521a103240d800300320002e4041c06100300445803144038a07840c3d80c185810788860554143d48190302038509000821002141d43c0014a914500361044086a40c1c401c0c1003690381e00243d4050000c07814001c010890b691207412001c031514400d2402040c1566144e4406145030000d588030003030301d004200140451307541841410303480c010454040c05591549a6400300030b00c200e00440b4020301c2350306005561240194121a0b42030003400031034180e003001c0c2c24180714061f4030704204106907092229051690f4411120071003000702c0d0103040e52400004400b08554402c03a03c021050718080c20200140540d107500c05004164040c84a141142c09080c800900700000c0d0a0290b06101003070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 354200440 1250 354199190 354199193
    0x818041e1104062c030f010515041e0507051e03090c0f0112050603120d0b10020304050f04091406070801091112070c032d1709070e040f0204020d1b0806031903110d0e100507 76
    0xa000280c0e92004cbc494000a440c3c5408404403011310403256607000e0381038026040a80c04801d000158400c0c50400c06031440791220000b00b00044080002240c000350030907201200c1207c00d5408142c125200900725424083c0d0200c08001980040d081c140b5a00c0d59070407407264a0804d0f00b01074241003500c0c07010310701c1c0c2801c01d000100b040d0040300c000d41c01786a075a1903884c01c0100310540200c1134203e0710704031051440d1a07800184002824001c9480c9039081020302d810a940340c80580782000113102c2c0d454038950302c20078101c444003084842501001840350303e9000c203000d96030781034050341100d122910b05009100006881e40919039401588020709a04008900301e01050341825288948800142600e43e030400b1108003284036006588140300092415861880342e1006141c00c801008008105070019000d86020070216110307070301900881c401380220703989a40020250b510a060160318501c80b101010f00d400d00400c00d0130041a2a1038480010780f801e44211000600300303240c01881c14206 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 354201690 1250 354200440 354200471
    0xb0a1a220b03010221010f06030207020d0605070203070f030201230f0a0b0a0e09060103150b030a03120f060f0e0c0f070818041e1104062c030f01051504 67
    0x103080080e440c50399070060058203580a40450fa9011240f0319000b1003e81040e9104940d24000c0c806c4818070303084883c0004c0c0007402070007910002900104107004103412600e4841c003511000b00360f1303000c6010821800000484603203017040e00c0d80c0a0fa00008003d100ca0f4528034503c0034075048e00c244501507404110008424038006940b05248240100300003050402240f49038940b0340203042d0701200138081201004c400220981228000c4400070b001d00240c20ba150211506078031400c0d01764001c4581701010a0040030b103400700710b01e00c031800030b400341c803c0c3c0c218000c0300c1ca55004410350400055041214908030700c0400d400c07c1949051500e0071145140c48079403417207401001030080d4008590700d40c5800040206c80920103000d8010b001400c402210801084900840e41100926008101c07030301140541c2650140d6203541c440701400910f120f00e090300640700c287c001c02c00422054034440c042c0c8081c0710702da1140d0038800020429040c07201c9180e08240d4016002806546404d901040304500b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 354202940 1250 354201690 354201739
    0xa0b040206250c0504180f05120304030305070305150105070303090321020c0f06100e071224080715030203191d0f01200a0905150403050c060708250b0a1a 68
    0x907c180b03800c0f07000200c1d10b13149080525108002160320f0002c02040149a0103420180c4a0300461307170308020540c1c641c6400078081c901000c0707950003c0d100344505030000b0b0082d03000c2ca1156019007001d120414070801511740110700c210b076820030260041000c1d0025401007003010314030004c02001d44a980b400020301b0012800b94481c082c4c1360702c20030300440c9071603001324041e20b410f24501c3e0b030902c101aa1800e8420700204801760102080e010100009010302020070b000c0e06446155000c80860b00341600114042d4102a001c45404803e80b2404043c0c0a054030072444142d680385c810158440289000c942019000c0404502903414621464058601e00011003040fa00039081c180c0c0321365060308110b80704912600f05940000b02001130040904140002e4001c50784079804940c103000003801444094001c80c0001484030500f40111625880e000d03203201401440e039141440e80003019120405461401d40b07291044e144d40c0c10040c10030900750307004a54200026200041c01d1201d01c50014072405 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 354204190 1250 354202940 354202943
    0x10f060e060d0b150d03030509100c05030711011107030c1a0103030c020904050a060e060118020f160203030c100204090c0e090414010b090a05070810080a0b040206250c050418 77
    0x40f00c04000901401d20748003400030001010700b500841a4440c42e000d0300802c4107490407440c0384101d03580012041041e02030044024181c1d50350710704503141d40710309032080308000751600380355521103160b40110308512003d851800d0080c2e641d408000001d0401041c150140c5084140300c40307902c001440802e4001c4100303110a0f0341505e843e00555906d06105040404588006108906111420003c0303000000c1c0981030711060308500f030f001040c40310810124418bc41c40100c8204090004004486440039a841d03003c2c00601070720b140c2a070b1140d0203400c06800d246110255980070900f40009401e6204811004441c0c3c03c01c41441c0d00c44000081081c40001c00050900c00c980c080d01501071029005001001009805101d88bc200080e0450141404031039000015261500041004850b01150301c11900d840016210b00c00c0c4e03584139080c1c0d0744c034010001c4e604214100280031070080000e611440450180100090124040c509042c004800d54007041c803460410641c42002900c1400e5168110b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 354205440 1250 354204190 354204203
    0x10501050711120604030e03070f030206090409081605010b040b1e04270203060a11030106050c030f030c0d1b091806030609050706020d050f070b07090512010f060e060d 74
    0x204850b141041d2a1441e6035003a54100725009250054184001080b502031403281d1649045a03600707000389540c0705050f110303101c03a503058550100302602700000208038a07500a80082000c00290b190700c0c02ca0381c807410380c040c010300704154050240302081c0704550b1000c4007164140402c6069000184039408244401b07519406d2668402e20742c0d99950703001d807402411054030f82c485484840b50f035180d003c00c0300c90309034000d000303082c0040d4000303034540308024500fa0789a0b440d0742140d0801d071040b2695000100c1041d02440b042120248130245400610f100314441c00625030f6400d01c4442c818203441c00c54601035aa03026000e070172800140c0040101c0306036280c005c2e414000303084031010f02019100b035600c0500003e25251100d018428082a600141c9400350225801815451401c0312036102d640c01c00c4491600621a21300011070301002d1075086030040c6003002206864000090221050960140e1280e40d1110000090b800d00c3c00340900030015002d40c04030718500034002c01e80f01d000149008208 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 354206690 1250 354205440 354205447
    0x3031005060d0603020307090902120706080c0a030204051f030e12091c0b01030b040506010e0601122c0303070207050102071a070f06060306090b061903110609030f060601030507020d0801050105 85
    0x500030b00754070050041d600203040310032190765502030710018036043c101680101008040403010420016102c0d0031506150740d818102e907139041030030746070380c01c6a8590000c26800b080000750540e103900040304126620004041d104a07062000303411640e00195034005074011002120302c0059440c20707682c001c0c2e801d4035400340d10709992685141419507d080140300310420300c00401404290009180310364031407821540c083c1d8856488049d107070000c4070350b5070020381201384884041c03d841c1c00c45509607482d500314a44840c0c5440c0c0700d503a840c221000c545015407001c0104240c0703944c100481c400070802030016000c020305240848400541d02c4031101a840c00000d458000c10103c0c2c4520008681c000e0000c206007a200d00d880400303042c1c5607409440400c0c056021803211700d008d0755025013003103060f503010448903d550f1725000b0000154940541c403030428032005600d61400c5c040000c0c14011000074001318588003001500f243c10140c0b40c001194030001c1c2801c046904800d941e81540d01c242405500d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 354207940 1250 354206690 354206707
    0x80411010309060f2403050712060906090b06010e1002030306060c03160c050f0907080a0b01030b0409060f0c05070b18071503020c010f1a010c2a0303110303100506 72
    0x5800c84050043c80907182c990ba620358100c155005205070140b24075140c0c8900101e0802c890102c28074000685660800d400401040d1030344051596914880c1310003080c03010f45500c2e03c1c800c541c1500070503944040740700b080003000d40e8400100044044d003240c00a6082242480003503490200400290041c40c00040b61a02e40c141001a5143d03209040d4400341110480d20b00950144100c0c4501c9024070450550701e101c518141c00075512544171581d841c040d5075103d426181c09010384070071190601d6581c2c0803140741364035103004512456020b200007058180542d81d060045803114001082003020600c038072000100c000c55400e411030310400c80b051020340e185040c3c6082907400d41c4900c0c25002000300c64050560580c014128014a0310004c000303c041c100008400d55405107500d040040c40048601b403250700441504201601481500640c0400c16034184c10300600c5000d0f40c8074580e0052800c104060f40040040b01201c5254050b5040d41407052131426017180fa809070601c030b484082030303843c2c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 354209190 1250 354207940 354207947
    0xb0703050d0e0d050a11120d09020d060c0c170403050c0d0c180f050604200a030f05100510020a05031602010507151b0507020f0114070c060306051002010b0108041101 73
    0x10744000d80181c0f011010301c01d00140050741301c440e4032400b280802c80580513807107001c00c2d102d032080603495030ba078039000350002010010501c20500300c2c0d0100e41c0c161071402103440782c810721920780441d07103c05a5507012030504038240007082a030004e2081b0200001d1001400c08122020303848400e90b000c5955101520b09512000c01075084a0f1000459542851105030550440c2414000e072440400441d2038000134081503031b141410f003100c103a21684040b01780324184802004408100e250000b0810403c14022058400130b42d440c11b081c1103c07100c18001c62408401d03101420186000821100b15650f0310345842e4006d014500b03841c8488018250b066900a500b01e40d0810351102e5810007040880b43d0150080280d60402a412102c9048440180d030203102145c40070390700105402180e500da0801140c56824800741c00340c01c01c100340100000035842c01010030103403d00e81c50104402c0e0071304050042d000c0d450000b22085a0402425100990304201101e810a4010400400002541e401603 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 354210440 1250 354209190 354209201
    0x30221030d02030406090c08210307030b0a0306020c060c0a080406020a050f0a090f14090414010621021005180904050c030f06040b0c041d07021908030406150b0703050d 74
    0x400703031074000001c01c0100000e99211103107140c4107803a614410b54880c0300c0d8607598030340503404c181240c2040c20481e41c4e100b22070010756400b00a078030380070507100480d2011580c41c0e18154011a0341a401042c10105031005104540d8030101c0164814144080c03d140100100005403014044650000b007003400d031841402158000c45140d00c2e025034501986030000e240291f640306814041444a9000c68044c100d81145000c00b900280b041500740c50f40c1d1074080382c0b036480889032480756603588400a0154240c80100080240e44105d00c00c050104d030044c801c070110403400100c03c01c5010008640c43c4000f144811184140603104055955282e28106180c500b109603000d0381480b9500611021401c002440b503c2544039600200c00ba498180e9215580e0085020704d00040c044507251034442c00101c1030040e0b110400344115840443c0710400002d00340100c04050f540c003100007040006000c001c4c003c1c5803800903019900c85245242041020150094a0006081200001c1d00b0ac00002d400d4026 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 354211690 1250 354210440 354210457
    0x201050409140a05160c1b0f030302061b07022b080f04060306090b011e0215070905030c030d0f1409030114180102030f011401030e06090d170103022103 67
    0x8105224484450410341c42e41190989109414a0005090601180c00808003102d0540710541003103003a60b112800c0c5046640b1401014a03440c2c400038180c940d4900d00c1c0000e5001e0f8000e0708a40c140301e0b00d1040e0300e03e0000c9005040040400c501001030315031540d140380300c050032a21080c802c0c0341052051081d21504402400800c404211081141050b42c014811240c180e10100049a07460349440180d4100740a000d02003030301c4c0c0140c1110700c214051060310381007080c410382e540060300c52914942c1001c0ad8a0883c001140c0760001c1c010390400b00b1013048044400c40082c09040814240240041503d4903c00d08000c0b01682e01b51050314207006407401100300500a205c00e611034000303900b401004030703401c01d4100c40e41c061406a00106100f264001c405d20400742d0601d82c20b10141c8580c4120f81b8062034101640c4444142d500d101c288502d42c0540c07050f801810a956000c3ca0050903002c00c20182d16603800e128004000580e140c540c180469001706803c0c05070404c10344602030850042e400c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 354212940 1250 354211690 354211709
    0x90a12081e0901020c070504110f0c0703050a0605150105190e210f01050f090a061109090703091209060801051003090c030503031e0609040201030f0e0f0604170c031602010504 77
    0x14000c4442c0190050201194150210798115640340100401c2c2c492503c03403162240010004990203908180041208d2030780c100403035442540d81c0d83c940d403400800032000da54003a50b400070300c00300c04004901069055000d1030094101f0102410b000440308108040a091000740c50381c0c074445403100e02c600c5d403101c541c40d404a40e44d56911015503442e03075640c00031401c255292400041d12050340c00b400ca4003c881510040c62848500d5640c0802082e08081e280350b030103024030181c4c003d41e84a01c009446072081341c4e03002c5400242c5107000020220100307041d006024040200b4080300b030348014101d045400c1240c01c05c0b40040301c103000358020040784201811a401003100403003404000001503001d4407901c04c6450720710741207801e201c15440090f100030368081030380000b14000d0341c03080c0c1000c80c40441d0104005604011078014516080c1c074800b0315000c139000142000103002400701c01003401e1882004192600c200c040708940ca0741315494462a040104050000a5910410580340646407010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 354214190 1250 354212940 354213001
    0x30c04090f0603020f040f2d05090d0f08060a091d060c030606070605130f0c0806060402190818030a020d1403070903030503040f0c0905010305100603110d0611040914090a1208 77
    0x1541080c0007100f110088c40c403034140000b04038014030001d5440c00c600c2c426a20ba100c01800107000306e0b41042e01510b4150721090f15000411407108074824072001440c4034010207a002040031405092500087c010010030405008110a986070401182d46213903000300000380540d81c19502c200d442d505d007500640703100304424128080001c070000d0501a100d0700c8044810a50b1203d04000691080c00040302c0070b1000705403000b0040d070250181302e802c42c002c01c1d0011096910443c0039407079500030403a1480141d004011078183da40e046844640602d0141c2002d0b850b625060002510b4410f142c44010304000d00040010248029011796000e65a801003445803141c0c0e4a51940c00640300070300069a040c0150740c092008017a0901c00c900c11241d02c44842c868520805e0708200b0500381e8090180e48068583c44410603542c50b60000f0b0011788805200040c0480e945a06240b003503d000f08440415803098607100c001c6800c1680340e48186505140030846592078011103018550000c00c50700020312040c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 354215440 1250 354214190 354214241
    0x17030417030301050316030507030809062215080103020a0608040f06051302090916180e070803041a0f041809050f07060f020c0105030406110f030c04090f0603020f040f 74
    0x4070045048410490448818500d806940a8148418400107082c0d902002040000981407009000381860041900342011600c11402c00d48103011000291840003120003408032079400031003007828540c2441c00c011550705590116101c0302c001e0140e181400344004c0003c0c00c220554a5a07803c80741d110000340600d0402032a440c444e2590b55004030312550808002851001c000507034219041d2080d6070b94030317000303107040002811049400d00e82c455a6448148411144e102006214010400600115511450401140d840c030060300251400c0e240c0810801c20000c0004043d5010750f070001004c138110405180000000b40401600113006004039980b42240c0311000c200841120000d49600c0740807541c580e0126103414a0850711800b0800c280042808100d081c1d0021100d8480c2441d110715200d6080c1181e6040d42084078401120180001d0601c82220f8074010000d40c41840003041c440142540c1c00592000c0c050381401d0300444d580c00700b8000a603159000907004070f400c2c5505c00341c9030041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 354216690 1250 354215440 354215443
    0xf03050a02031504052e0c020f0f010605090a0c12110711010503091207020d231c0807120b1507020307050f010c081b0105012c0c0417030417 62
    0x4000c141d20a005030300816602040b8040090300c102e40c4807000e80040301042d481c4040a81881d400f40400390024144141128200d21801950014a8000380328820110540f41d1820303a0141c11a20a80d042090400040e00c40ca2841508140300400200b8892207600044074581d02544025900e107042411504008031150020503019004116407110b4a50000040d190b510050b40c56002c0c1e64020031040944104a0740981101803004003116040300c2140c581080c0482c00740091920400d40f11800c803003455080042c0444540d49400a01c2d8a0b40ea24001500c0d0140003468502442615000b030103550000c1e9001ca112007000400c4510000b28184c411130403038000341c40490007071150b803002160600d002c2e580c2c0d04071071205a49481e4520003d035180b40c565041880c450351a5910210000082c52003805010b01820100c607062802a0700c40031517084030500d4680e880c0c0c04002d10130034044040d0b5100c0440e000c0d1000043c248001c0d8260080c090318505c2241e01a003a141e240800c01e5001c5c1d1070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 354217940 1250 354216690 354216703
    0x130512030105190510030e1213080f0708030904050604090b0403050a030608030301030209041b0f1d01090209090703020c0313090506041b0509040b18040605010f090e070e040c0f0305 80
    0x3015190b100c038000c0d9141a10480d0b0303c65019203540011100012821148217412040314600d040080d90860040d060728079043e80c0003405089110201c030101070180c200c0800c05254a5514907008103110b6250102e829140e100302031030a80941e0712000004d0742e80c1c84940141601c3c41d03000c40b444581c0c0c40d050a0081c50380e00904801c400080c202100090780307207000000c0c1e87c1030747e4009256419640b40d41d5a8141c6960400008105240e000e03000003681a031200940001440d2485441c3e17005054103100000140c01604102e50701d0b8030600800300191640c000c40c03640400141401a5102d40c048005480c5008030010354560705121800420a800150441070044506480c144424034040c0074116240c504061060001941800300850500d0580c010002c41d100140000f10200c5260407580c036407500460f400e40d0703d2601d59004004c90024410b40340e005000d09c1408011810003c2c40c080c0d1503000c7e61203041c00b00280d020205092052075a014401020030341d2a00d1842035480c0341c92500c0c3d40c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 354219190 1250 354217940 354217949
    0x80c160317060d051015030807061a09040b1602011104060e03071a030c160b04060203040308072a0809091303030e010207030e04050702011b0c06110a171305120301 72
    0xc1c064001c99118240144080401a40180a4031021402006000081c114803c50f100500311502c00040410b08540090000f5809024040b03501e440360b41659201c8010590b05030f0058031004200000329040b042c14513002a0b2072404140b11900c191000c0b409000100340c0605ea00c4000140050401c0d0130000d07011080d03e00350305480740315542c4c403404030b510b8145128000d20001c081000030380c440e001030020428112000c50483c0031089135141d10034070036002c0350126100c550010a020030325130000d41d0380c0c0d40402c03246056151030945443c51a421410881209800060300041e0f10030005d80c40709444078400d0260402030a881d01078a40004034588110950110b0300d01a900396041c0e030b040c02126000c45e01510341c4441004030406000c000c0c40c00070039180841d540c8a001c4481c00307614040c0e0206076a8180d590032243c5640341042000c641c1c046171001f00101041100103501034122500000d2400300700c440d00d51568405540c5042908404001401c41c0100c400e0340c24290349003800746050300c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 354220440 1250 354219190 354219227
    0xa0c02060316170103051903030204080709052e05010c0305090306041101110303010509070f270f050103090b0601030203090f0f1c020c010c06020906040306021801111903080c1603 79
    0x1e50007040f0441c240c030400c0c00b000e482a0000c12180c80c0d006141109403d4480c8280307001840c00c4d6950b00990b0404059401c40401d554507401406552210804400f141841e0985041c84100c0301d01003410319400740e07100b802e043c880d100751020103140c000c2058405d01107014081c1d49007490189466048904c2558034140401d040200c1c1440c0d881c0004103403410380e00081c200144030f4803040381c15646281844081c03001c000c003000d82401c40843c03012044d920803030031b50f00c2d072000c045c06c101c41c40040e00000c2d00b00604241c6440102c2002c981c91905007a00410b00382401a43c0e43c45030038015050647c1503503081024810359008a0901a00003000035107022840080b01907601412012038803241000c1e0360a0000e140e41c2851400304002c0d40c020700c0785000081200d4601a0350b41e1707544003660081034401400a07108000d0030141d580004484410b04548400307082c0f96481040311180a00c2100809820040d40f180011030388005c0c0070449584419020103154041038071b14004141602d28282840c01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 354221690 1250 354220440 354220457
    0x230d081915080705150309060f040215122508040615080304080307060b01030504051e0c10020309120a020d0605060102030409050405100606080c0f161217010e04020a05060a0c02060316 81
    0x45e103d4007547d000c0d80f80e030310141c50903480709400025003541c00b80c41030303912a04600c2c0b20129510224010600d03056402c040118a142039000e02c400940009405101c20300c420b016003a005a01091240c0c0c400e85c408000151041041d041c01501d500301c1c0c0103003885100c005004562041d00001521001d0301c1818180601728806004405890702620000c090341e104110580310200d014504c45002d01341c550455001c0d0312004002002c80c17400416180158100144804250400100c200e15410505000303100990031940442c40014030202d010340520355407004107040768800d10483d801480004414002420607081c0240c13501045200e8003241ca1400384006081070113045014401c1400e00b03161410145039102001d911361185610040041c2c0c0e0015800004200058085a010701560b03180c0b82d0346641c04100710b0400c410307001550300b110f5a004010069070394511210a0390029210f4030348442d9045000e895000980600a41c8050088108102d00c0403440b40510800020b5446201 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 354222940 1250 354221690 354221719
    0x6020a02070918020906041d070f0609150207031e0209010314010c032a090e011d09030c0c010e010e0d211418060412230d081915080705 60
    0xf81d046041d80c1c000d401001c0c980001d201c038900b950050000344507024403d00c4100e0410162414404260000d240c02034a05000b803103481d520030303200c80150407036008030041c1c9010140084c3d0368401c640b20007003406010050301c1c0c1b00080c4080215400640c00350510415584910b401c5442c01d40407101c8209540c40d0080301c00303407a032003405072001005441c3c1094407150160034541400051020344081880b0056100140d01c03d9034080041c020490a07811052204004800c0811000003a10100b02544184041580d44101003000c645030311090a0030511030780b805d001642c0c814010320300e0b20b80c008606503025062140030207403800044c00c084880c180c424444402a2200142021568041d500a02951054050440c031001c02d1603801800d05003420740d5445c07480fa42b80c04500080f15080c0806240300c2203a440b17586020603161000c0d01030000c4028401000704504002020010145032094001032005400c4d4040d001c070368a81c00131124101e441d01941c641c0c584c274900c41e0314000c80102817043c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 354224190 1250 354222940 354222971
    0x6020d030e0d0801050112090807080901030e07060f1d09160305010f0e0604020c0f0307150605090601083601050105090703140106050a0e04091202100507050406140706020a020709 79
    0x2400e449a503194200300b0317400c000046400c64074003841181410303a5120f510000c901c00f4806032010074800c2d904140e80300e068200050640303100c4400216103901030f15003400031581041555124044a181403c52440c101c090000306284d030703106880d0000710307540502002e403004491404c50595917840511035030740d86500d0901c01e090b9900c2144040300221000c034a0910f0aa00181120b084080c11110482d0286d2400307400c5600c0030400b20385201e0801d840d46003031865401844000c15044038800741a1034618000f030b041c0680203141840c0c201e030080000050306006040c600714080b4040c0d040c5a00e004402c1418002c0c682070280780e02c151007240000e18a544a4010600c01854244480d08143d203001e02c02d66035600b050340c1d10b1007030241940161241d51120301c00c14414a004203891856071040d0312010b41407090034188400b4050a01c0300700940190443c08440c02c4528a2500004c07200b80d410310301c041070041d81401050180002511201103131f00044860035181c400c2010400405000000c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 354225440 1250 354224190 354224203
    0x117090d0f0815060d02040b0406080405120708030a02070317100303030506030d1407060b091303080601020111180109080d02150106021f11070c03202e0507050706020d030e 76
    0x621101140c0c10b0f4150300c0d4101000900403502c3e61141c050700b01b548469502d0441e80058010034002000310082009002041104200051060007010b00d00469910b501c03005100013003850401c540c002507181d042604c20850240b02100c042c841054600304403210041c8003c0611007030300041d040601244092130042140d07040305180d0f407140214070b000d020303600b01181c00180040e112941da0b0690f5805546407100302c01d2054000030a4050300700ba05140c0a044410050300081c1160702d0300599070084040c2d8402c0701d50701400c283c00117003541c3e01c400040307843d81cac07407904100041e0044520710114241c0000305405003915013070030020142c0c0ca41034100d0b40ca10b08045007010700c0e164000e1400200e040b6a115045001068812620f4200b0b16111203580c01e41c15070084500c50548010200d44030403e030201562090121809004410004200301c000010740003818201d40540c1c048201c0309008008440c40c455100307064410280c0d0391040a9101c00c8086400d4010070308100e86c1c000403030b9000c500b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 354226690 1250 354225440 354225451
    0x270f040b0303030703091a0a0f0c0215010b0d0204081504050d0f02030406050d06172104030f060c0309050d02010608070923220615120201021b0117090d0f08 69
    0x46086643d101821009030000440a4411304418544000341101c0e50147c0c0c0d118141010001c60b040180080003401c6840a41d0b29004540000e1003013a4070000c00c14402e03045030342401d02d8a4540049036001c200034840c41e8840b840c10301c940c112042d01c0340400c010040c4120b01a0050351000b5500140641304203210b078142c900181c2080005004c000c0c041d0010f0700d08062220380014003140c031580144403d010400c3d894040f940485c0d880e68041d1080304012034001520201c41d03041910755a03542e205100031042c001c1c956078907029000d00f030901c00c0d8440980d103a0031400300e8a6864420304068001c2c03905001350581c501401320080b0340e21004e40a26061000b4001513140b500c1954405141480d0002d88049064560100d005410201450013208007a0089100003402c0c0180c44d0801d06948503540b160118078440e0a8000c0580c0e00880c002e1400c15906840e0325141036040d004866a01402d0280b211005000e010b00c07109643c0065000c043c1303810750b1201407200c031f900c580944411204403003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 354227940 1250 354226690 354226693
    0x90503011d070b040e130c0b0c010510090b0d020108040215071a0f0408040306050712060902041707030f08030714031501080609040209180709020a0206100b0a0906050906270f040b03 80
    0x4246c21907446490760b005640196601d5000329150540494150310080c6d0400c4169140d4083c0304030560000c0081e0000e00d41d8130000c10515003007402050a20388407010181c18010320800240c255251228039008401c2200d294640d034035490700d0a41003030000f10300c035003101c1e61000001901c0040802c5075540107a40094905061619642c1c3d840041c01d401044042081181c82000701c95070000e015260280a5000c130140c0c0b1a814012114074455445a1179102c80d0b00085042012800070004e072160aa004500f081e969036604506a82c0f050102e24041c0c00600004204a18038800d0301500d4a508401d0742c80c00525101c00c4200324000000340c4010b544452a18042030041c00c24039914503a0804179010381c2d524030b135103072a02002c0b078004816910241e00305e4810050b101192000c140060078166038203600304803491000070400092800f034070092040003c1c64a15554034a030988412980e1040100d88407a20506035811070b030444102a4029548200c45280b18a014041c441000d20b0150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 354229190 1250 354227940 354227969
    0x70302070807021c140609010b180c0c190b0402010f032009010e040203040c1505072604050303030a0606120b0108060418050d08011a0f09040903090503011d070b04 72
    0xc080001600c104c082c242e40442000d800180003d48a007100180c0c082d080340540350070700d80b24814a080d076803006c030b03014800c0c031591090545034160028007030b811446462501d034550541d610007a1078128034214425100c1c095082900c2080010305026102d103200b1398454681d428000c0c4181d0540d5841004c03c0b81203920319419900900140020f00201d20051512100c410341c9000418101d80c002da03026590484120024000283ca4a0110500c00000d280080c135200d15610b49134001101103081204800e0348444800c451503000040d02e016020060950707a40c0e00381400020024100c0740704800100b00d0000100031020414401c404000106131601c08040e0f4440c0304010090075102c11709003180704e59001c00404240d040241c88c0c08807599454641103541000402c4001c145240c0464112410801090040c01c14000c1640d400c42000c1d140800d0204080c034058400c614a0f4002c0303501586000d1001c00c58111400c0d0098607120490155031490751940701130003031486280100e4640c0003412 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 354230440 1250 354229190 354229193
    0x2030408070f1b0803040e060f060417030702040e0102031f12080d02040b070b010602060f151c080a2105010302010917030f030726040209070f14040803070b070302070807 75
    0x900702e903416100f200c000c2c031484071a00d02261200d5aa030001009a071011400740405122a00425000202180d90307000002c025400180141304d5401031040c80e1400040c0100040000c200f51b0300d0709039009009000b0520740140d254000c4d08101c50b0000b111440c0e80001c0c1402c44c2005100302079584071207250345054030760385a40900e80c1c40f400000000d164204400101151180060803001c0c0c4281002030301942b400000a1400d500075044040140e86a018000031103818444150f2540041c3e07000c07002004045008465186400c8000c0c2040c0300009802d60781c160f0101d0784400302c00c2c040340c4d0203100701c1c1d1070150641141e030240002400b1440349113007032003400c084c543c05120484100c1e04891400780904100300031600141c603042d0101346141042e40c07040b1000c1c540040c03911100741200e041c5213095000510000006028041403020f41c43c0100074045c030640102e0b103200c058210144d80c0300d0350b440c00c1c10b940f980300002c182c07844514080407903020bd1207030088903903441d005440c1e64248000b9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 354231690 1250 354230440 354230453
    0x50304060e060d1a031b0d0f06090c0915171513050d031e02030709090b01120504080c0609070f03170d0903080a050105030d0503130311070b0703030f0203040807 71
    0x240300050364880d10a21242044003c9030280700c2031901400581d0340385800c1302d000c0c14a407030709502d020140c160903100e141c0595250f5554054007a80c003c482c0401d43d20450410200509180c600500309012585002c9412102c54000210842000d440d40a0301c035074400050454108411041590390082c2e840319421803841100181c000244c0090040c00800a80e2000d240000102c0c468010a40750498409404e141031002c55101c1e102010a625610b40314200030803452050140400301661484034007010707481615518466201d6020800bc10304090034680269048601c00d54854404c000c0000c813211004200c010807120010010b43c112801d5640e9150056070344500000c00c44001e01c424585c0c0c0303070700b80255540e0f075010380c41c4c24000b070903d1a041d03c252841600300d18000c1d4031280350705505980c04000c6960040800f861110100d00d1403504840752229516240303007a10a910300400d074a00054010458503109803401c210b6107010140c0d00c42607000407200a041100140319030000301381c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 354232940 1250 354231690 354231707
    0x509070c110d1109190f09030c0f140318030118030f08070507061d0d09050102100504060e0f1605090606190212030109020c010e151f1a0c010b0108010305030406 71
    0x8141002040f200e88100030441a55045130300b14243c9072a040e0f9402000c001e8030803a100e01d407100c1414403c601d6980c4029103a91880c0000404001e80451140c8c180321000400c8141d03807103002c0a4030356951101220140442d02003402522035460904020b600c2003002c840c00c01c0080c1c0c0341d15950740c524078100041c1c4050030014107c10a0100800c96500094002e109405d5401d21901000c00818040c0c0107040c6000501103502c400c0c0300310030b0702c00d202c60b13a00016950031060000501041c0e03030350b99240c00005019029071101d5144940c03200040c0015001c01c04040c042c0009810f0001540c2e00c3c0100700c3c1002c0195501d6410140411101f84800c441c00c10f841118003032030044803442000d13a800989140e10981c40a60300ca80e0201d81002010400c1c006c1c0c3c0a2004144001d1551500101182ea00018003901800380c9e643c00c200043c00011408410b00d004100300b07030407800c508880b01a21012a80320722500049035107410740040c02c540c001d1034082d05a907000002181090709002007511081c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 354234190 1250 354232940 354232943
    0x210702010905010603060e0c09010605040b0a0c14011d030a120b03031303080a0f030b0f040b1207060804142b09050a0f14120309060d020d05100509070c110d 69
    0x540700e401803400700d10b0034095000150301c240c0300000c0300000c040850f4149407000120307520650800d00100000d651203403e42d400c2c0c6000400e21640c4045040c400e9542d0002c054004100100030300b440810f00d54194807003c00d800404600080044074880322640700c0c0314662102000c210080201c2541d0000340d80002c0032203001808803403420300149884610080b16500031112038100107182c20480d03a1011619280103124102400603441c80c0d00014410490390f0500c0e0b0080c5c1d55008100043d943e40c00d421409075015005451085031615801408140100c82c183c9415003c4a2900c00481001842040e051161241684075110000c3d69a05071250031611408000f00800302041c15a038078071000004188000100c8107041c50020b002050341c000c401040c3c810380c0103000c1c2c0006810040100e07128020211a05030350f0301c00c0b8100800c000e0003500b5240941e6840d148c100482d42d85041c091009440048866011a80d6441004c813440c440e000030051400717100d000c100805090054100503080e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 354235440 1250 354234190 354234193
    0xa080312070e030a0501061401111b040615030b01020d080f0f0405032109011404030f03020a120c200d0507081308010e060115020c0915040b060c0d03060b210702 71
    0xe4407020001e86042e904500c150741d06d9550310701c1040880500d0b02c1100243c40c3c00e0038205001e48010948540b50010405445050794080715001c4190740d89502440241000c0d00200080001101c00100140103040c04980903104404060300858061020144103904100c142c40180c1e4030200c2440240c0384c0a04101c1d150710050190a41c00701900c0c03d158041c3c0d1071240c1d01d030042d1414030060741c29119000c004074005403000040c040030a40c40440092403a16505016a80c1c000380d110481ea200404643c990300e1601d0000445807141e4444224007542100380c0d1507950a507582c042c456100c00001150001042c4100030384000244110081d02e0060007603182c40074dc0030b03929141c0d01d0940320020141500d54220400511034000d11071000124081c0600c0113040300540c08e00820191000503088800c0d05205e80344601c4030381d44680000a5088019014079141e00826400d82e81d115444196400801d041c800c1c0482c020741100203940002165101d8158401c0052a0b48801c1a030041c1040046 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 354236690 1250 354235440 354235457
    0x1514030c0402030a0b0a09020405150a02070e0411010f02010510050f04090507030b0103050f060c1b0109230f010e030702060a140c030403020117040309031704090608030c010b0a08031207 82
    0x840c1c0c0d40744080d6201e48918080401c0c8040039104102e1114400d4000d034060034410b000901898468074108a6009004120305980e03141e49c00040c1d29226450b0700c4128803031084d20030072080144044141515a90070388039400c8038000c900307050b030a130f5a0842d0000300a80000c076003040300d4680285c00154803a0f024100090102c016119581824002c0d0400d40d0180300040c01002000020401c0001d000e82202c050f0180c0d0800c1720000c0c4080c842c9040e043c09144107505800c003916800c2d405035001592141c48146400b0341d404555880c2c144022002e0520b012340048441d50b5003040c014288243c03044130185113000c00070360801c41c8035000030b6110000c20006001c00c03940e601a4400078031009007880e00440d00d8038510300c0014498040f00f000c0c003404d11000c805200010b908019901c0a40e80c1c0251080d040000b645180301c03c034022540b00e65141400c10500081403c8044014144011124001d224441040c0240080107003640f04841040e03008200304520380b0300e005c401e00d030003084510340040e0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 354237940 1250 354236690 354236713
    0x9150f060c060c070507080601030c030b0421030b010e010306030317070e090c070b060607020d0b04081903050103060b24030712020a030c0f0e060d02030c070204140108070504151403 80
    0x20700001143d881c02d201400091003000d1100401c0014001c1081100401541d811a6500001704e0381510000f068074520f00003050420140000c207403458806606e440042006c00c11300100035000140e0514040341400ca0380c54425480303409410152901500c5142e820300c085107010341e44040007002601002402041c074222555448034490260290794502510354805090852000310040c00c00740c8a00350400c02540103850300e0287c01d000303980040b8904169907a508000600d80300d04050391441c82da007400b0b0303d5070300740d0517030710040c162405008100080d02198061080c007800079148801001d84d20740b1149201800d120043d9071100003860030b0448102e00c42c1c4028140e800100b840340119403101e50180d001e1f40c2c00054100100d00510b408006055480c010a00c3e0740315403040d00c5501c076000030001e07580581f00030480d1b006543c090700c100301d039003034001d41e0440b41c40c07081c00384007100d01880d90b000440b45094007401c8400d109001d0740c100044d2801500c3c0c1c4284d03690040e015018018108243d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 354239190 1250 354237940 354237943
    0xa03030c0f1b0e010e0f010311010c05101415030a120e0307060f0e090c0406050f04051215070e2d0301050a0213170d030207020a0801060602030d050609150f060c 71
    0x41004280d04007034502c5800e0600c40421050141c03c01d19840841d803042041c6081c01106280c11290012055a4a56041d9004880c07044584501400a12416100c2050390580b41e0085c5080e170b1402c0c00060103500c5400314400401500d608966050380415440e41c00f2610100540380444170609010040006120100381000b5644e0322a0000c40d44501e207001125400044050000750110350a4805151440c00384165002c0c1d07009440401001080408604400e80119000b8250052002928185460700690380e0b800c0c40120f83c0c042c25800c804180382c90300900c051013481100505410300c00c1c02609070304218545003204010005030000d81c0c0b502d81c3d102072140700c3c0071f60301605016a403000000201103008055034425420b1703024040030f2103011503001c0b81a0400c03018514000da520061400010b90300d02107a0040c40c51035103012030000b1060713000801031100ea03070018024085a03803500300f0007400c80c104442c4000d0400011040c2ca00500d485607956521040c014649420099281e001c2c6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 354240440 1250 354239190 354239213
    0x1104180c03150c0c05150a020f031f06050307090b03060a03020603090105061f05070b0a0605030d0908010f05150d15060807140301050c27040212060109140a03030c0f 73
    0x20344808580100360b00040c2202d01440f1803260081c20620794006131555880d03603800280c415030b0b006540d01c0c000308000a20680403100007941d03410303c90f61641003840092820030149c5850844034214544009182801071003600e12a0000d45c541c82d44103032070014000d16982c4010011540405c0442e004001680d4031405103010340a80f000000d29850400140807100304020b080311941e4a5407040a48955400310445452070340c80941c0407082d44441d40c0c00409490310307402460303250041c003025141d403c0d80103481030211070000b002403201d000c0c4201e410302254416910380c4080361000e81d1050041c01c00c08a1a00c60911861b10009414202181c100c111100d07034000c0041e0350415007041040c0e0340700300c0d009605800200c0c020042420305080440c4a4820071450815038040581403002010560001c0021800081d200355620050400f0024003c18100c1301540805e460140118000d0791483d40e42d110000e001c0c00d0a841142036840644101a90310300c210f52a0004214940000d04401c0b40e4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 354241690 1250 354240440 354240443
    0xd1103121302040e0f1f0b0307030506220c0b0a140c0a0b0a0e07030314040302190503010f09020f011407020d0308311211010c110c0406031104180c03 66
    0x72161010910400c01a40d0220546040f1a448008050203c0401064295006855440c40000c0b440c418106501820360090301030b44c9401800030000c2800310210368070f031142e440329043c54070104504510306543c28001101074081c9811210600032071982383c00603d001c01107410460440d0406404d03400e00350340401482090740e0040041003081007044100700703400c5043c0c00010300056400310b00c807507982c050301c0c8000303810011550180c060349071100703045402464001d40101e008010301000c104541b1014401c2038081e610341094100e1000b0fa80c441c0e02c24269008000c0d04e85900703040300440d1121101110f03221250010850305005aa4000651540381d2107615215218071740000304001103018418001810011050310500c81d240200107c1815a80441c0d1085000080c89007150641007500c42541c2c15880c0088080307003990000c910a13804015482100d0942503401c092006484452200504e48c508400f4944058a4590420051080d2006c2d503100f08044a4507081440301c0f05910 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 354242940 1250 354241690 354241711
    0x50426040b03152e1d130b0111011a010206252303101422091b0e070806150a0c0c0f030305030610110d110312 49
    0x8142091250100601908200095a050406281c84410322241c40000e00c590364086507849a0100c0341c0e81d103884148a4201455402c04d1075029021642c46100c2103201d41c004100155208400ba100e0b80135059600d00000d4610041c40010000e114090b0090b419098144620701d0a0706580020901c1021180e0300c0044080c1d62080284001a0800c130010384940c281e0449001e024940580850800c00520a02e241210840e5803074400302003604946099003407540000000d000c880c1c1e107038908880640310403821a0b0201c04801d820090380340c120786501c003000402900340c40010a200d61003014054010914000141040300c4100030a0050740c0211480404d010f00b4410403c0d8024043c986c0000103907107081142e004004a404280200300d20841049403200f00f68040161055040c070040130100140b14a1684919002d030150304101c0d00c0c640901981024503c81d5440380b0700c4000c20028060180c813003800d18100440303c03c402c00b060300711148800c014605820901801080c407960001c0c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 354244190 1250 354242940 354242963
    0x604180b03010e1212060a030206040b0d060b0c010911011803030809070302060705161203080c1317030a02010b090f0c030408071704050f0a0515160501020a17010801090f060903050d0504 82
    0x4420140203d001b80145005010202d82800181c880300100c8080d10380e03140c000e0341c030f680c003200f2020050074541e0005400345401080300a0013803015003090044501c9007122504503a0928011141e1004004116030035141c4c00c081040032134003802c2000e80102000f010340d56542e4894003c10070a070710440d400c0f41c0039803180c03403a500c68159241c40e0b00e01420066911011000341c94600412030742d00030300392a4400c400010810013450f03a64198900810044c07841c01d98010103030808a40341d800030ba003200095420121240d130207107043d1541038400c0401094070820f5032a117504c490542c2e08002c00451306110108803240c00310b003040c045c1c1e481001d1103e4000756100e0903c0117029001e45d461408a0107400c1c407040c18001a41e47d20804038880080c40075581d21511002c2c1e000b08003548241010b8255440007070140d19856000d009a180007201c0d540b044082c0e640c0343e03007650884202c1c1a02603d820210414000082d0080d00421800c40c081d140c01c030304000c03c0d902004d0441d00244da044684840c1d61 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 354245440 1250 354244190 354244207
    0x15060f0d0501050f0f010f05030706050d1b090f0506030108061b0d050f01141f030c050d020403060b010305130b060108040218131209060c060f090c03150b0604180b03010e12 76
    0xc2c045d15025000c0c041041d0b05c000e150202107039594170079001c3c1c0301c144240803840050380c1c0c415500248240e42092911000e07032419550203004030200d80034002440c41c0381d090205036810aa402c03070303041f916103a005020550760038460640010030080071030081d4a0400005415a0f500e0191a005070f502e123056040075450078100c00400c601180c0250701680020750792041401500007132040240240c03c01281000d10603100325098850030100c030300164030106010090144961001134100400c0e24100b10a4480e81c00a4040e804405001802d40c600c000016400b5440b408525800c03603c080c0c8170203990000d95003c4445110100c903008402c0102502c0301c818801400e550301c08000250a2401046040c90303c02801c440c0010740c058082074440b4000c800c00201540650781654000c1c000305c02803902d901e080740b01e8400240f0000d5002c3d04141195445c0e140c60300881c1c00322084a00e0141c0c14100c005001c002905035440d0303040d415543d80c01e01882442081c040301c00e01107083c40c83c07103a1301c4091 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 354246690 1250 354245440 354245461
    0x16050607030606140a140904060f2c01150302250b150a060c0503120f16021207020d15020c010b01170903070b04210306030b060315060f0d0501050f 65
    0x4503032040c000c00c90030340004c4901e01684412180a10014034005c054040d210250400e0380c0704005009801c14a84880060142d43c429042c5040d5030094070000b0004d415400c07034550648444546070840c1450500412485c01c00c00380301400c91801e810b02509210703407051400f038406d04820002003509141614882001a15200242d0000c00501c4a250400342400841e07a0120702e40108024408003008001c24010b04000f03858041c001540050440c1c98400c200c0c1402100039118000c40360328494250365158004190f4014244078000251f041503242c1d003c104803c802580159602100d0b00d513042c0305050702d0300080c503c107031103200003007005004800010a03051070494461144142c20040c440840e4020044454894028441002680326030074007201c031410105000c1c814110030a0158542a01030300080c003180d0081845d0740081d5070b031100349919030010101400900c51804002130b80e41c6808000c80001c5c0c01e019008020007081c541e030709821540241c500034982c55180c420040c00d03241 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 354247940 1250 354246690 354246701
    0x21201020c0c030a03092918013e2503020310061d0402120f0c130b030a0f05030415020d030e0d020a0210030b0a0e040605010f030302060a180b04060906060b070510111605060703 78
    0x140030b8100c1c0000200040c0798081e8001d0b0381d0340346c56140c1c000c01124401010003c5070b8140b6031003607200c003105621034400800d0040300c1c8800ca00034003e0345d0301e40324402c000d0c0c403400c002c44c0d02c4a1000018041d65100d41c0c0301d130030801401268006100c0c107010080c0403007080403000300c140d00401007040c400b0303803410002c83c1a2034511492540d401c001840c0c8098401003848400141e000c040c4403006a85440c1a5080d80600d030000086d031140c1c4109902456400544601044c07401d0310204041070300507091316281d40b0003065003405039112004580040c14190188800ea00d824540000c5e80044680064170190b5581c0c84090403002407428401805441e102c0c9500400c40461035845032817855401a48070315008112500180e0307241190a9405c0c50070080f040e1096010b0b41c072104601c1c1518150004282030301c0c0030f8800c02e203801004601c49861000311400690440002c01810074124003c2d4080e00700a03414100e101c40510480f0050302074002401ea2162080e40a40070526020304c00804690 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 354249190 1250 354247940 354247967
    0xf0a20030415240b0a05190f0f09120308040503040b0406030506210a140114130b100b09120715020a050c04020a0c0206030601020a021201020c0c030a0309291801 71
    0xc0110950f90011101618020704503a0a1501e1a403225074800e401d407030700d0040c1d4030140c0c6085244001020a194092484036420720b07980c07607140031070380c0440301211300302c4150050302801010b000c008004030f8010600c155210348101e00b181d00c0c01c0e0b03c40034059195000b0358085c00100b5241d1007449400e180000c02c1f007007103459240c040c00702600404060f664541c01840e005c0c2101b200e407030088050010a401c410081e1500303d103a40c000f400d180318810b6071846c1c0310b0301c10384001d82d04a0109100d1903e242c0c580e01203800d600420fa0a140b00c2c00200203102190080b00d4040b841000c00000703101950604200300241e060300900401d110310f060060506441681c282d218510411040c0800c682025071450704030380644d191900c82d645d20300142e00d03002c1c00c0b10010350702c13901c2d0b540c01202c07070179054000384500c100c40b200303032003020b13001a05140c0d48020540c001804207408000c14821880883c844041071203d0301b480c000300145d0180034140e180c0c00566a29a210403007000f49a0304e5070002c1481c40c0c460b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 354250440 1250 354249190 354249221
    0x1812020a0521270307030c05010806031b0f0301020d14071706150c010e011d0c040203010803070308060d0f060903030e030702030c091506210606030f0a20030415 71
    0x2d00e10715002d0541c07071007034042d050f00c0e03255007181020099003200440340441c0360103400c54007003075224105412015070500ca070f1400224035000040e0300341004141119a00040801c161000c600d9908020540182c00c10340e6425660074003019107448071074080c00111101e04013003140b4038206100700401c524203005042914020000074000b10344c6034209000045152000c41c580c035000c014010300e000d0410b182c4580029801c00513005003041924000440094910b0215040481008144020b030702003440390710180d80007805000082406600c1c40d0b0381c4190000c194402012150f03070740000800c02e1400a07034419a56064a404143d058840c01404601c0640294144155940029130328040d00c050039000380300304004109000c40000c0c24090000c4001e104603210703042850041603552004540d110310310000404111a410048210707030080b55448203074030740340c2d4170340c0614005000f134404c2c1c1c00c0740300f5000c0d4404048009560040d500a91140c528099943c4070b039900038007603038015041000340d03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 354251690 1250 354250440 354250483
    0x60d050a260315010c0c150807020106140604031401110f031f030b070f030f06240504030308010b0717030403230405101809111c050f0a1812020a05 65
    0x89003d80440c50b00350745800d02c3d08612082a518044c0300d054025403000e59601580795030450762907004540180302d034041d94020480c441d0780e294400c0703d000040c0f05003038101d0010401840807541030200081540c1b03000001050352818820b03000c0e5980d01c0051078a0425401006010304010607941c1d044140c80d80010b4641c00c203041d5140c117000b810015000d10142b0504100a8420724025003080c12031142c60311040100b503544000c48026414030a05168035003000c0700022818030702440c280c42c2035982655503a041e0f40e007491507200455100c6402513819541c10190074210300c1e01c40c002540704030b100c0d0790790040200c0384014202040702483c151120120060006100d2070b1250f2031040b440c0e1200f860008400c030f54030b07602000f20708a15004030240e1070501d9020380a001d02007000707011400280e4403400108610902d02000c07a2015100c00b040d103018480403a00303504461b04565036441001d651040144900c0d41e82c01c81a00c54071003910050b802849111050110070f005108201c1400180d4001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 354252940 1250 354251690 354251701
    0x100f050609070f020705190e0c0a0203070f050304030501020a030204051207080c210610060f0f121121011703090a030308070207090903020303060f10020c010305060d050a2603 77
    0x75107070002d00b03010801c145481c0460380d2620820400780205005000f0481025140000e0b00d01d240d03030342c0160040c100c2c0b510003088194007000126400c40003140d001d5414600c880c3e9401030300c6144000e05981038841444040003085003807004005071000e039103005a03038a1806040c0074607400b80110071b41c0181c2020358100032610008c51036038187d01c821204504002682041c00404d29480d03060710019120754401c000d10410750924000c00da46440c0c503400343c980384445c03007100c8048188101c800012420700780040d00300034540140d4030110b4698801403c0003040003c0740c114100c0d20800010581215004001402d030310100350342d0040f0f078200075510742100200440c10f042d1542c0b00c01410005000c00180d1500e1081c8031585c0507003440b0300240300200450600075a00d801c2954540d00c07440c4030280c400e40c1071070100d118000c1182c8035000362075101400c000541c02840000d01054101c8130000c04000040c030f042c082101c4041c415100c0d1070021446100e100c40400c10795420180c6001c04005105 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 354254190 1250 354252940 354252949
    0x50906160c05150a1401030803060103060e0705040608041403070c05090108010207020117060609030f07060f0e10030b01031d030d050a0b130e0a0b0f041502031e0411060c100f0506 79
    0x10242d03d05101103201903c4441403030b00100070440303801030f030140c0e010004020400800000c6000d035000740e8040c811035807a0042c8030341a00c1c098a195004c00e41c00c020402000780100d20740c96106000d41c0480c0808101820320364115407080600b11010440040244010f107800804075015141c0385000714107001307042c2e0006e0422250305185603408201c0348001501d42c1d0310b10044400501004d02524482017004594070703551825405004003041142c00442c00d4544a02007580240e030004040310940916510700340e0080c143e0f40b4405040684401520510b10540c9000d4040e1481820095640302c40807d14a4101c51001d094604003e040983e0340d42c4a99030501042c0c0801d03900a0000b50603089916554907200d0b502d036000302602007001c10007a050031000d4900344654000c20300002ca000081d10040304031b01c4200c42c1840302889082c003684980d01284019a0301603c10f9a80d40c290648030000070305075400c0f0b800b006000c1e50001c01c286c0b02c0001640a12811030050707a0091240b0b040010024 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 354255440 1250 354254190 354254203
    0x10f05010f090b12071d060105120601030e0703080a11070906080d0f0c1e03120903021b18100f060e01050403080a120501030602091005130e04050a06050906160c05 72
    0x818185454190b40e44440d69036100e80100d0704c40540880d0b0590707548400000c4180000300c04d1640300307280e841c00540b0b50f5000d04112000f0741e500c0c0c2e1070b404070b80d61246c00650007810100ca50101c03c2c4240140480043c1140005185400f0b040d103d8000340c0c004503151902d441000d80103010424140300c0c003084102000036860f1040407203401c003015501010303070040310401c4d01c014018207034050315600e5510720b8140007404281c2901035901c1446482c0c5280d139000030307500111b50080060b44030520002650303c07140000c99034494010b1588041406400c1c00b11030300030b07060300c115907440248001044040e5040010000410441c10101c802e10003081c0081d01c240242d220151242a0003c0e04a08c134500c81c2d11500e8071600407500402c001d58407414000c0003900092905405011650348041e078443c01402034a5024031702210906034542403001c914a0310320701800c110b0712881003900c60000a04503019003441528404010195031600d180c02064030440043c0001c1400702c0750b43d04101048011468 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 354256690 1250 354255440 354255449
    0xf0a0e0f0a0f080f03040305071103010b13050703090209180c010807121e09060507020115050d0f0503160303090302070605181e0d0305130b030c04120501091a0702010f05010f 77
    0xc1c0312140071076042c66506131041e8040040c02c10030020406c410190408050304000e0b001e840d204400e2107400061500300d9804031440c41e0301031802030510241c0e0000b070708010b40c820f51034500070400100f41e50220b1410f0006403684120840760000da51000141041104120b00342460005111308014101408020b11340400302c6440d519050310703500410448422600c820400300003080401d40d9418058014182561858015420304d041c0448004000644a09840c0c0081c8144001c48065583c0401d00760841411102404144005594600101504003115000380c4000c0b549807a50b1400a040980301e42285080c44810b1103440b03600d084286080c900140d007034075607503d1101c80741d990102e0709001d95865036000600c0746016042507400790150107c192007011108020791280d0801200d0b000858903054440014001000ba2914106c0c00110289c080c82c0000303000b080580341e02d00707095001d810301d520104144041c072072125424400d2030f42c08002d0b150100810750506400c2607151602c0d219 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 354257940 1250 354256690 354256703
    0x1b06040f0f06060308040303260903040e040c0504090c090e150a0914060705221217040b0d050105120a021509010212030a0903020f0a030c020d1a0f0a0e0f0a 69
    0x20341c4001c000260788607030041c60300a0b40d5140c40c0c46d52441c3c001d2088a841141907000b0301c0c0d00754062a0302d080c0c2103400f4000c005640c0074504290900c201120150300c028010744421102c1d6000141e503803914400e05c0b07844e900880f00b0f071140364200303000c03001078846191803204035a0003946411004100d544115802013070000300490680c1450400354804600c480d65081e050141800340942d00d03030024020301d40300703000c07a034241d6070540d0f18591020b8003011803150b07070301202c01d54071000c0008075409032228044007030390703186401c094031400741c80b2068203d19000b2041a03650001030005140038800861b410340c00e8002000b04640a501042000454441e8400b12180105000d900c0303a00a104000107480c80c4664a80c407854074a400001070000758406030007502a500400d40c080b8800b141c01c0140f01e41684910b40b041101c1c1e400d100c0200b40215064031820401004259000c482500d03a078000d41c448202d030700712803d000c00d40d002161407960040c021540400c415401d2a0804501d1044441c0c2010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 354259190 1250 354257940 354257963
    0xc0503120a080c0c2506020d020a0c09050c0706091109061c060b03010b060d1d030a02061f15080414150a022109060a050703111602040b0301060303051b06040f 70
    0x42140c9000d801c80000006005c119684c42c0000c00014001000c40313409a00310f9411101c81c0d48140c2c3c80d10400d04018100704801da501307020007117a903000365401182207881c3d54604a80f5894540460f540c030389046403540c00d001410001403411024040e003200089a4180e070040c0e040c030344a024080080c0d0001c10712602c2d00304820340c5035420f60000d4240000500300554400014088000918030780d0442d00213200c500420701d00d920400020f407080e03000c9640052016842e0b0080084030603080343c00300c040d41e14214401040304d0082c0c40700c00c0403411607501c4050307240c00c007450804c60709017601d11007000640c003215030030401c070070b21042c402e4001e610344a0050360784154891a41041d403810040d08090900c40050024500001940794811305130084100801c0c1c0710780000710143d85d010f407a1801c1c0007034140b200f8292038500e6141e4050142c4000d1000034501003240219082d14507583c01070780403400119000140e84010000e00001050540103010285050758440500d2000e000000e4008145103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 354260440 1250 354259190 354259207
    0x406120b01020c060c0105010e07020a020307171c021c11030f0306120f0708010e0d083702042105190c08030712030c080108060a0c0e0d0c0503120a080c 67
    0xd100c030f5020a18041c103c1aa140ca1101200b4081c3c0028441c0b004445030301c0d000a58400e1010075940300059006000d030080b540b400d402c608030000440b1120b220390041c1721520300a0301d030350261219054001d0700900428546003c0022140e030710702d0201c1e4280030800c080301e22400008402c0721030000322464201e803292030307503000300b10354604da801229082d10828260f040144000560301040b607040d013000340440e07821201c595480340348440f51040814449004661114150f110b90a204401c2803440a801c0311246076102e40c00d0220320206019541c0000d003072140d2185000004284003005204a0a400300b66880c00e60740c0030742184c4840441080740c60f0900708224242004010112201120388590182c10300c41d08491440d4480c602103483c28088181c264004c02d062030407a16000301800c1c45507a8503020320081c00a9650341e02c10402241d941c401c050b9900001810290700a8814108542c00c3c6010f1624100c3c0308940303961090b60a01c10350030065404840c81da1710180840f4102d8481c03414 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 354261690 1250 354260440 354260443
    0x1e0b04090e0307050a03050c101413060e10150b130b0a050f030c0d14060906090712050f04030809120d020a1209060b0a0501030c02030313021f02060109110406120b0102 74
    0x7070942c0182117002c0d1400010601d80d20602038502c1849000075580d4002c0803904010485420400c6030510403001310001d544039412000003001d081c0514070104000828484141c02c0907a031000501140e5502c4500c0360101a5008109014040030401c9519002d03001d2a040786500d410320901c500c00d00e0004146070058480c0301910390504148000640381e003000481c0d4902034120054892041d45404a0001c1c00d0842c9034409004020144c40181d1b141c4038081800300008000b0002d400b40f0901201910880b541442128411090312a601c0b6075401c3c03e141c010200724018002e40b21542c4074100100d400d214960440b0160822442e005958500c00681901c1064a85000202c00c0349403000140602102d50001208401c1c111f807500e4010381c8a03001582210341041c44200140d100384000b55104145450f100000d90008081d10b41552405c81d00116a0300c038950301c100107820074801006005680c1c069544140c0400903042c0c1040c2c00d0000c0105000300c11070220341160348a1490b5070a0b82d00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 354262940 1250 354261690 354261697
    0xf080d12050717040b01050f18130303020c0d02010b0f03030307020d084803090c01122705010b0307060e061b0f0a0b0603010b06090603040c0e0708011e0b04090e03 72
    0x403c00608086251509210030119001d10445000b0383d81022054183d00d0705d04209403014503d80019020340c0c880103205404885041e00450038103608112038006284200076a02da40c1806074008038098861009001d460761040c6540c40c000d40c0203000b1302452680215002c80b4000342131621000554615154203076a01c814103007800a07400780c0d400a00200080d4424001402075145001c800c1001140740f48120b00c0200c03144252508031506020056104040380300d103083c0348207404600194074a40c050901200540c41120756810703481d554007005820701411407000c80403800740982071300c0c1c01c1002d06252501500c0c00e108400015505200d4000304451441100c0c0c400c088400940c2c0c903a1200d41d0b030b80841141500c91401c5d403800114545414000e09080450142209040a1781c0d8018400141c10140084800550f40c58012030840c0c0e02060003849001c4960300d6600340c1d45056013a40320401c00c000c00e030710f44480d601c0003400394040c0c50741110100c45900c1c900160b259107402c10b5500310300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 354264190 1250 354262940 354262967
    0x2702030a0206180901260d0207060e060705030d05040c090b060d09051c320d020702030f06040f020f03190b1816060305091b010e011202130f080d120507 67
    0x184481c00440c020503958420400c05001340c9184580d1708001807640c7d69070041d15071050050b441540180b024501c02c0c0608020180060502c6052070200d039681411500041c401c201e0850340c8000f003200b84100514520700800d4050b00421058032407401040d150300c10f00d664035a80380d458004034410050100300f8054004c0c0e18010940d4405a110001801c201c2101c0c04080000e42c04c5404116000030241004480c451400c075a903d440042d140300c0c000f03900311440a80e498024966840c4e240d950901c01903104502c900f08005e0b50407283c0c4100038a1038a100e0070503000740e00c0089011a03400440402203400d40d0014040d2800d9600e0400d40c0240c800b882104844d90700500245018007408020100c3c00c0c2c4406403401d12a558400460079622007901da80f050001c94014150320307555024600190510006140641da02d503020403400059038008042003040f8900c0c0710003005030086100b03a28000e0240c0302c01800460003140b0b4000c0101c2d41020740f220b000761b914408600b03a14040c50700d00700c110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 354265440 1250 354264190 354264199
    0x12030504080c010216061d0a0b0a020403080a05031605090f120c0a180f090b0c071104060b0c010b04020a051b0c030a0b0907120f060506030f0304092702030a020618 72
    0xc00c0b06031148424070141280403103a46d41841000241281e00c07020710b0f0840c1002c100101038410700d80c0c13549620b10101926560300c540e804c000200115442100a00032001140c86059880c02e10058602c40134a482510300c0c10002c2c144030444443c1e68207807a41c0c40301d00c02280d50501c00800d0440d44c0c1d040103050740800791b0200104100040e24211038148840140c015a820018400c1340103210f4140c034800c500051003d60294001900c0b003a03802c0140c0030180c0241d40c00c2c0c0e014500178003c0f400700c40081c2c100d08090840401c0c50701942074240200081c04c41c1c20394044d401c00300740341c00141c01802010318040e14610001144484a0710403c4120100c240080456a07540054100031140b0201664500303450f008100c004545000021080d0707400d1a4803a0500720b18004903107400d4001c01c03001c1c00441d40350040d9079400c036070858200090009810341c4080080c080601e6000a0900b042c11700521b094482c03003d080d800980c0d0081091f9142c16011b55103555920042c00309000c668900741c41c00d9900 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 354266690 1250 354265440 354265447
    0x9050d1403031003110306060f010f0e0405040308060301050a0b0105030a0209030a0f0b100b0a050a0302070f020a030b0a0f051605030c040f030f031b050601090b0303070609080c0d0c12030504080c0102 88
    0x7000e4442d04007080b6030050108000100b28174060507183d810455111f6004010345109035403e511950500d96148403d162448039a00d220340010162030050780c0590009000c1403d100b41d034135080c4034454000c1305010040060030100d500103009400020f0106046a90104201960381c80a118406085034001424001d02d400d619044030155410f40d201d03441102403003004542400e42030200c54249000d501d545040030141c240407006903001e40d8003251000201100d106c016102d0b0020340002e50b1003000040c100b40b509150060031241d42c2414200d0050808007800b0144071507114014090b03029240180c1e0301da40d8460341091610a0ba845000c2054603c4c90000c00c1c80407000080447c1c1d0700c2992040c0346002c203801010440d16a00d1000344c45034120100400ad90441680401e6003c10050b09807401c3c1845520303a90102e8a098500340c880040c00508014a03032010700c01031b4042e0403030303060044c282001e6031115042e0142034007503a400e165680d808907091014040903130b02d490507180003e559 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 354267940 1250 354266690 354266701
    0x210f0d0c030e061302130905010513052401090c03180f060605040605090a090212030f0c0114191a06161a0c2a010617060109060609050d140303 63
    0xc0c202038240c00002481c04091401103400411028050300c0c0c80e0100d03480e1345146408000c0c0e41110311101e181015501c60300900090400e001d82881010505414025240e213401e100b030034450000200740c5a2841c03c020519410304941d2114117441c501754001428640c1484207800030032007480003084104540d42e0703000c01c0010285403514a07900c05c82c81400001d6444043c4000c2c0d40850103030581c0180000e000601a8485610011a1074002000480f019034805009400e40c1d100250102000400182700000048240902c40181414000400380c0d0300d0241402118100e4483c040c18009803540078005410481c1030031091a0b10000301841e0b65100c4840b044042001900c03812100c0703221310365803245507909450001d40719045800c0c019140940c1c01500346881402d01107280e841100c0c94000c81d4401409100d03140c0a022900c00036030000003000101840c0c81c0059101a07025030400c1000e005841c0d0080500741150f0007540d19002d00c0c41546000541145110b0102000b44404004c100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 354269190 1250 354267940 354267967
    0x3030a0f050f16230111070204020a030f060603060305070f080d12060f15021006031e0606030b0405010b0909010926160c05010e041b1404030507120611070203210f 72
    0x2180c210400411340c05403520202e00d0300381c0c0d01d4005000046c90080c00841d016040a400800d088181d03460005101040a05075008541d42c85d04480002a9150700034402c1290030000100070300402501d0003445460901c902c0c0d070f20303416a0025810015407011621250045400005c050b140010805203020b03110400c00e51040004c400030f02c01803107010b40401250203075105032800c1c3ca0708182c002c0300b03000c503281500003080d4000c0000c43e240c3d55149400004a030404205500551203000081140004c0404000100708041e11844041c0d1508000c14000345407414035042c0d204401030005800c10010701a619103000301c21110404c10a60720203401040180c80b590030595000741c8604017641c030807100348801c5a000c00071191810b50094004c0c00d13800d0043c1a0901514940340711341c0e180c80d07100e17541c4500301001988584908846882c12404010b8580101c1a8111040040c0c13802d00c3c0881e00041c0d80e0300c0d8014250121103445036500c140d0300e030034103044901d00361568421650b80e440f16007a90 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 354270440 1250 354269190 354269213
    0x524040308131d061011100c1101020f0702030c0102030a08011a21040201020105090703030c0605090a050a08030609010614031311041503110604062114010b0a0305010503030a0f050f16 81
    0x154882d8042000302c1101c1d41c040e41c03000013450030810080508221069020001302819a00380e414007144524040c08610240010006c044133395020546442040c03042c1442c104a0b204c02c641950030a01480420310707406041c590448e03945001404a505000707010300300320300c101c5490701c06401902c0c90000c03401c03102c208900c0c003c5100380d00811023642d60994958699103180001000a44401420000b252707407500324503080400d10064900121245d40d8a519051140e402203c0c6520080208829850091892401403100b41030920003101c4424400b105e5102c020726500c5904900d03a01c0d94140400c044100c0312880c4050810420607503205000c694494040c8411103900d007141000c8203c905010b4150740c22039401c0d454489291a0340d03072410010740442c4005900c155500c00b88600b120034600100384c0201002070810b60340340040d4038002d06842050b00980d0003540100709000c24103520400110840819180c00e0b6240c105600003c0014441e9080006120802d0440c1800317100300746025 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 354271690 1250 354270440 354270451
    0x1c0c0f080708090906010f0c0807020324160903020f0418061d010501080c030d0f050c01050a0c030e0a0b070e0a0302060a050c06150108010317130608010524040308131d 74
    0x4e042c541d41d505001101c00c2040c225561001803030803e0210001035140c00640182403000702560f0104610b80e401c040485002c60100d141440140e080c018044c0701406444041d90851403c0c3d5500c2e81180c000c01c1c000e001922000d402503a84040003601c80c4240b01c60007442c56032045050000309044020745414507210b4050906c20b51070800001100d1b000024104080d4070040c000c1c00004038011700680310766039002250418008104480c480034902071080c18840d429048000407842a64a070040c200c2c0c003c1c0003c0c42c099809200c0311400305500b11007903540b02e03995140c5120b40010a4000c03070078529580c0d01c0290000c8000c242c0c4110a90440043d1000030311003002c07111542c1d038001c4804125460300d50900d000c26003050052003c1105107541074188c1c030034803080c289030017200d4045000d03581c143e90001c00058040001441a8500b5896000da8400345200c0601048010386000c0024412840000c14807240011a101c80a0302018136100038040c0c1c40840180901c7c0794910060480111003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 354272940 1250 354271690 354271699
    0x414030d150603231812030c03042d0803060301090501060e1509010b04091107080c1e01140105090405160303021006150e10180b0c0106081c0c0f08070809 68
    0x5600004245150070900311654014081140e21103805034188200041c12840490103002200d02e01e1b01c2030380c3e0045000b5914840003da40b4580350034140300502403045407648943d0040c490002c04840e0302c85011000b0b8110003450340d683c80c3c00000900400e001003000749194241800000c007211200c1d6080d108070f041e0303008902e603600482d04006102e0703000d001d12501e0b00d84c00e003c00e01c100a16548504001e4000c54461458581c0741e4859000703e80001041030301c141d1080d051000d0f24407004070844003484899000380155500803003030008504e01405080d003c5c003501c10001e42030180402c02c02c0300c5030100e10300b454081a12420004d48950404c03011a4100c0d0910380e0020310b0340c946c0211505100348603910000080d0171034040020348034584c0d803424200071140a444220750700c61020340c001840d11b032100c503a440000d0540142501c9150340310a105400002105a108030a6130940b903422030305152241c0120414500000c04070404500035010610101c1e00301c00f081603400080c04644011507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 354274190 1250 354272940 354272951
    0x8070f0f050d02060f0705031608070302100b0d02090408040f0f080c01090608010303081902040b1b010605010c020913050d0504140a03030242070f03050c030414030d150603 76
    0x4148029101e84520094112130304100128400c00d10401604800d0301ca44180c070b00d8100c015540b140e07540e11088041c2d450074400203500c8205501004900500040101d06000502080001545d01218010003078090b41d440c0b0f00150070804404202c0b0094042e004462203426110b5500384940c488030300814246102d1214003550a44c02400864201d5405075101c40c41e0f80e085a030101e5285a01a20116a40320742c400007100d081e4190000c0c0001d0b0003500242c5450308444d0008004002c0b00d40e121400c1640b42800078407403641d011604084131601944d0711026621400b504600d95484a0000f82c5a4096000242c0322164004014800c07100310118910441c1c1030b69040050340300107807000502581c0074151343c00500030740c2061079000904031528070000c2210101c50f100152410800c80d403008050004110443d40c0040045819500380d2604000d03e103090240d542040c40050b001030001c0c0f030391003100c09214504004451800801d168148034114000c04010070030b0015000b5800400d0800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 354275440 1250 354274190 354274199
    0x12006010f08070305072706081006090b090a09140a06091401020c06160e0301020c0106061107061d0f040e070602070b160f030509060a0c02030114270708070f0f 71
    0x99aa0242c940103409446d80c245005500c034844500e5009581907100c90080d000d040c1310047c45410002c01074440a400c00300c0044940c68100d0303a96070130012940340351202c201101e1b00e41c1088141e1106010320001440c9817a030800c9021a00d160644203154840d40c1c1da41b1042103010f422100099120700d1103649006420100c0302e00341d018100a01450358003400010b549046031f8426840000c0c41c9051141400103420042426680310110a428aa458900810019900a1640758444500005469024200003004244d0404501d98070344d8407030f02d4950030000380d031803001a60031148000c00402c406044031113103c2d21000c8620804003d0300801200042d810100e8040b1003040040503e450007801450f0789400001585210940401000340401e4440e61a808001c01540c1001d8443c0704035800244101f43c25503801da0301c01e12104a501c028040e40c0c1e07485c11000321003101c02a502076151500c0c031444618042e4203622614039407180340c1c3d0024811201644200a070390014001103c11600ca = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 354276690 1250 354275440 354275443
    0x903080c03074a1306030201050f0307120501080109050c0f0a05061b010c09080c0a06080f1803030109022d0405011d040903170a090b0a0902012006010f08 68
    0x211207020100c0c0000d1012541c503503100d2905220907080340d18034650600603400007510603943c50000001d0b640801e0780303c0c10354070b03000da8002e84076480714406000701030440c1c0c0000c2c807034081d142040828180c08404902e455000700040f0001c11940602000a0b69450309880c1c040c11b007410301a585030080b8072918a00d41420f091484030008040d2814070481d103070609004460744040e90300328101d0081c8162000c03040b400c1c0a00440b007085581c40740305942c20103800a0410300419a500c0c0704a000c2c0304104030050700690b240c3d40c0f0404c0c04403007210a070f4031860355110444507002203903d03c0c04000000b00d5401507590191441c0d034061201903000f801844103d0260900048440d525140f0034841041150f00c501d0000004541a143c6005104240c2c1e012900751102100110b000c60441640300450101d41c08a095101c0e40c1d00c8018000030585403540c910210019204261480c2c6030904034041d640940c10311204c048a60300603103018010f02d113405403101c00a0088021000c0c403002c00080c107110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 354277940 1250 354276690 354276697
    0x20d060b040506180112080f1612030e0c1201020712090918020a0909031214010303030e0c0f01050f1e070c1a0a03020a03060305030a110c0a0b070605090a020909010903080c 76
    0x4540b1300324505a42015200c1240440d64842218140801c001094040d005e201c0504682c0d040c4c5200c042200e82d0a24255141c0c40d00801e17078208040c078207881440084070005a82d1007a910030345086110100382d60307000f406442400c40c060074a00030811103403503813940050344008070b40b4a02c0c4204000d0400d0682c1c03004000d01164040c3d031100300b07108180010700941d1300003001584641049894860648011001d0700c032004104240c18440780010001d05402d40a0040422010380c0500a41351401c00052100024840014100000442e140d02150030241c116203208000007460200000300301305111665205440c21101a000f034000003800c0e0031000c900c042c44404c04500c0c1030601c180d01500710020b400425181c0300705500c42c0400004124140010b180c40c9249545841e00c20320f28900803840c2038804583c650050310803050400201840300162441241c3c004004505d503100c0048940c6002402c0801a6009100034203000100e40d0562021450f40c0c8244c682e4000c50760341030540d0860b0f00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 354279190 1250 354277940 354277969
    0x8070801080a020a090f061511160608070804170408030d11071218090501081b15041802040b0309070f0f0303050d18080c1005010b04051f0c020d060b040506 69
    0x651001d014481c0445c070713400000d1a02c41005001980c65a0340c0600d0324108204269100800c2c0038000701203080d08d0030b001100e24032a501c00c10f085018902a4000c2986000030309140801c2800c0e008182005a40b42078891290034000d00c039900c40382c0b00d1902a80b41e61003080100c090030324004d01c0302c0b03805401c04142c826154001c0002c01e0942e10764402071740c0d4451450b220501c03d4904183c080b500d40380b030b889030394060032411004100c1c5021101606403032503251b0403518410f0841050701040ca06a5504a900b9608000c0607854482210f80c1c08c040a40941e0b080021501404002c00c109910005140000c80da0507120700c80146644884501c88080c02c0d00011700000d1081001c0c61001026821001c81404000b2207840401015100c034222500a143c5000e103076013100140321010740a502445014100a14080b8600346c40c15000034502e9007054428414101e400e0402800e282c0140325071007185030050000011583c180c60460000d00c0c1e050302c540c5c416460301d0003182d4142010f124010114 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 354280440 1250 354279190 354279199
    0x18050106200304031a1509090303010b090607020d0308070f110304032a0b03100501080c0d05060111060906040b0a0c0e01110a17091f090e060111030a08070801080a02 73
    0x7620401c0155981ea11a0340481281d00c010000080041d01d90740c8692006034840307140c0151814142210440d0000c081891846115910240440308202100b1241150490403c00b81d03a4039407080414400d00410348040e6114444401c01301c18560000c203500d224130300d90340d102d400090f1070700002c1d40c0c0e007081c001d5200800d62081c130041c0001200168035081c03106840c543c0d04d00c1c0f903c000c20540307004007151f04100c40e0004084140305d80105842042c00281209090420b03040c0350400070b00e0010302130303034040808054481010405d02d90040c134045003115038010a480341440c007422010b41d0b0b400c0544003100c104c409a4000384448050303114000f00b20802c7d541d1001231524007401100c2c06008501060501d000d05490ba5000400c5080c1d2040c1d0807070b0090966448000c0c3c274003042261418113034102c044034144000710502c84e5000580d00c05940c9044c0c200c5a40303072540305c0101c0c2c56090481840c000c5200c00510140742e96008055144650030556601107203a80b144e4005403260120b082c001e400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 354281690 1250 354280440 354280457
    0x3120c0c06062e09030312020c032a03040909031707020a0204150f140405100f0b130b0a030f0b0f031b2413090203100e0414010c02010618050106 64
    0x10310380302d0040302c0301c0560002070303503054038a581c3e182100c42c015103000c101244030700f00c0030020140c00201c5440b04000300305046091044042002d82c40e403285a040c54420000f03000d0304120041c89134030413141c584c40802103c2d2103039110402e520080090f000144c0104500c0486412000710700d400c1a4882c01c22540500381c0e0a0240d400d21002d400d013001e01100c2e070302c0e4a200120340703040c00030010b100420b035402c1d5400c1e64540c10000d120456401501c1c56000030141102070150041410f031540883e000c4ca000a5510b6020050495008201d034000c0d04201c400041c21a00407503064120300d105400c22181040b400075140c0c10400f284100c02001c43d010342000000d00b54903ca903281403054130340040c1000820310300c1c00c2d410000144610301c800c483e004020407441c41c644a0109240c02401280d4800c5141d410065244000c40e14503104901b0701c21000030014042200149035041c03c42040d4000b84200303000030001901a0180d8029081401c0782c280207504082c1c003a0090364101c40c1e03503440314000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 354282940 1250 354281690 354281701
    0x103020618030a21080f01050108010b0d0e060c0c190b06010c060e060c0a0f0819020c100e011e091110020718050f01050105090a0608100b03040503120c0c06 69
    0x300148a0200682c14010041007001054484900701c0d048144071811880003004040c000d40b204002600d5024601e003c0001401035903000444181911404103015444403c61007806020b131200d10450340e0180584c90600c28500410b40c041c12114070141c0685e040d80700d0fa414209040301c04001c014200032003607004503105501518911203d20300403680402c04500c0014420f2410200b80c4071880c40420003d020043c869000f403050f41c078105c00c1d01d00b248040c288060000022a03140d03d80b006466800686105181001c00066452841d003403010300c001103924000b0381c001d10910384880201c80810382003407410541ca01c10301150303a038084c00a616014821041c0965200321600d180d040d0303c62660041000000301c820a84000c1107103d0100d1103103003242c220f0719010010b90001c0e05115080c0461403166403061801001c1c0e65036898070035500d6445080b101c03803030801795101e103030340c0140002031106029011000340105005900e000c1040d032529100d0328a1440b0700d004254180c3c110300040750 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 354284190 1250 354282940 354282967
    0x1c0606082b14090f030a050f07051c02011d030105070909270807050a02220b0609010f0e031e030c070e09030f03090115080609100219030b0312040b030106080c0301030206 75
    0x580f400c0701a11001c18440d01002080c5800c07003000065400e94845510f408100008228a0014000c00d6030034182440c0c030000f41e411042c1c0d0032031b0028182b080ca210031403040001c411300c006080c074001703000380304030308210f20b02510600160160781e424504000d194482241840748101c4540016040c2001c2030180781ca50811030b0b001140215828000e0581c14005690740c801400c02d01c0d5102d054005c0041400010303141242c1d84e40410f580900c0c814002c541d040d80c3c0140e002003090076a803c0c58203450300b106002a0402c11100c03104400c080c8103005103000704d40004060040c00e8a03100484081c19103803015201d05520407640c0c0c031100d500411409404484c40c502650300050b030840045013014a603810044004019005000380da80f12070f0410802c0d141c1000703c00e030303511030000c41185004400c29802c0590341c100710690003856241c4111001c1a2000c201484c1c030b400704240d14a456640b681c2e82840c0584c020300c6018006480400400e1581114000f05c038100c0381c0c003d100c10715001040e20704c50b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 354285440 1250 354284190 354284197
    0x10806101a0702030111040e06010201050c12040c0e0a02040906080303011203260f0603010f09031d030c10030c02250303121b03020d2403021c0606082b14 68
    0x41c140244122801600c090007410349001d030381c15142c7d8603a410b140f5070358092500203120320304583c14001440304107002b070030890f4074440150b4103d0b0722655403030811203c96102540702c4801181c0c0081000031454050b4060802d981d0303052000d1110541c2c4649899a9000030f0048a1714010341d0368810700041d0150340801407504841c24241c4110640d00040c44000c0800c0f5080c1d03180c4440c9030101f020f80d160030300c5000c1a09240c0c00c010021032240382c8008240c0ca14400c0e05851254018001c9102d0360350800004000c0000100500040c600e10342005000c0d140303603000000540700b000003081581108401040c2030003038482501d459545507840464018401c000311260083e40c9000c1c000504159141c407030f04a000c0d079200580c5c0c6a400301046000c0703c18041010340498441035000e07007152050740440382101d40444651441d4164000d40841a018404000748014900b0100184100001c1b40582021205c40c1480512106500c00d041d2807100c0da440120000c0c05601c034401c41d100300180603 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 354286690 1250 354285440 354285479
    0xc0d120309031b0302031903290d150e060708090a11040906090c0501020d0914060f16051c030903170a060503030d020315060c03160602121e01080610 66
    0x510100c0d6a92009049151040001c4d4010303003002980d015504001002124440345a2504020112044015022030b0f107499000008440c0761840203920303035454098020603250480508458048440f4a00300140310b94525031726940100b0340014502c601440810303115031a5403004e007056040540d01c059000c203103490050341c49035660703448030003044841c03040130b1800348034281f07103841c2505000001e0302e08020b00c640541040300c0610b080c4120308100c0c030b44114804003030350000c1c1c032002251040041c81c0190100706210384200d185031020701c88005003e00800e00000200b803600400000220b081c0c030008034025000c216015448180241d0303070344010703500607241f60340001d42a407182d0000381194045131020f295980c01009011051803003070495004403c044031050300d4003180c1c0c8400750326030041b01201c200d0107410007030604c18002e60f501152039415140110180790710305803c50900c03003044100c0071707401051610300200c1c4485000030f840340100c04110202c0c808500c0d10050740702e4160803058 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 354287940 1250 354286690 354286697
    0x1080a060509011506050705072405091311030a0b09150f01020a060606021f09050601210c06110c19050f0105121005031005060a09091b0e090c0d12030903 68
    0x30140240135602020102418141c2d0b90746590704002d040c00c40c030340540c6400200419050350031002c40c5020010340101400e40900f0311031f850300c0c3d045001489010f1566000b0700c00f5400c203044514200794080c000c40c8035042e5008100803041401061142c010030844403184c0d1032000814140039490aa1818500400e0510480f10301c00d0480d610002618100e60149004d40d10606101d2110b48440070503502104812130304225104940c0c035100e94481061040c02101203500c9108407205030f840700a4403040e5000003648084554422004002191001e881c0109005400300701c00c80e4179280802e200c020300c62804222115080c48104420394028042250500400f007041207088000070360010320400ea4041e0196059251405240c00c001030b514080700702c00c0c40c2c1000c11440380e889000b1242a40c00c51040015850f01c5460004264000004e640704d0307000d2050b000107048803d1003152403044221000703079100308002c0410b00800d4448020000d01c2307021115414080b0f6072107540440361160013441c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 354289190 1250 354287940 354287951
    0x2061605010207021f030e03030405060f0702101a010e01030b360406060e1e010e070e06030a051503190b1003021c06050c090d03030e0c10031a01050301080a06050901 73
    0x50001e040c40076403821009030f0b159100e0760685d80303136010f1103905101c14204010714078524040d6503050316100b00400208020b9071210100d07100341d00c20032044a020030032034010000140e11190b8509400d02e02103c0e01e00186003006c18040d1544240100c0088040190480060180550581e19014245468100103100d0100700f42403020000c49128000d0b802040009074540c20012903078441d241c01090b07030340340e040c549155030340c1c0801083c0c58504440c0b8500c410191030f1201038046890242c1c1e107040c1e550028003c4240607180305180c1c00303d07000d540700e6a083ca813008806024580c4170071251000c0307114040003114100200b20a0035006034002d2400855007841030700c07580015034118160002005a124214001d420001c04e03115071070b0000030002c0349600300201c4000180342c21441d0fa10050815072200d4140b100103d0400000c40c44140090008161a103020301c010010007c0400d102c0b0181d00018503400035501580499059508140150100b2009500c58001502014082e05000d66a41c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 354290440 1250 354289190 354289193
    0x8090402121b030702101a0a0806060307090e071e0f15020f03090f10030603051b01090509010f1a0f0313051605060a11030d020412140105010302061605010207 70
    0x3880200810200c14031021490b080400e01c40c001c0c400c1c810084241068100140940b0540000b101600b6459014000c9226240003050300036004149070342a40000500304041062200410b0003441402c055003242c60592765414102c040c0d0f1000d410750310b5540c2282809100920704480c0c03030003020100b0486081c43c0307541d8030311122041c4240d6000246996085800c1c29943c0d84c1400b45911020240f80110306248103800019444545004101d1083c40e03401041c0c651640241c102c10000e40c1c01c03109803064040000c12280c4030007211060640011880c0c2008126132030621401c0f41070340d00a04902c12041d0500e01c94407851000310b542d41781c45040c20f001c142d601c4070041005511501c60300d88000034540b00340c68814034280c684034905501c555640d45c02c1c4440c0e1103c800317855141c0c00901d0481e41419140704150306520501442081c01400010003188552060340c0200e0f48510599100b83e03911260300301e0500301d5000f0b0000951011080104802203107240fa00d142160703000d03200043c9000c026 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 354291690 1250 354290440 354290449
    0x1a01140a031b02010212010605030907090504030c0507260703080409050405030f0a02010b0f030615040c050903070311100207060207060507020609040207030306050a0503070b0316022104031e120c0809 88
    0x1404004005030340004c1c051521078140b2001ba0700510340ea083c580c1c21400d01c2007907551100001c0c094406425503171000034040c0751048080b2020181c001c02501c0074980c4a044411203c416040304004601540026a008000010f0008100c940011605080c241051446006032601400c1070702c10740300600000e80c80c00c12000c020900d107486a000002d0801d21b4906100c0903401c0c501d9150720a401200070401264400c4000744a0107100f2240041c0d10201850241c80354014070110580500c40c01001000700920204910300d10702c822283c0c44101401083d00300d0351055940074a10058000080420045004070003800350076100810040c1800302600c0403804a8010034000d4001a0b10341c01c1c1003081e070401455040c00b8080c02d802520240b4200a2210051b110280229084204400704034409520901034440d0100b17200641d603a40228038409514a50024001511401c540b2001c10a45419001c01e80307010550000711000e0b80300084500f602c2a508112050701d00b01d400700403081e865942d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 354292940 1250 354291690 354291731
    0x5070903080f03070306152319090306111603080c040b031302211e0c09070f08060102010b1c060e030d06060e030615060c03070f0f02041a01140a03 65
    0x1d1151441e5101e00c1c1404009003036402d280d0000d00035400c03586950b0300c6281d000d00e6442180e50403285075a000074004850248c984600b003201416484000d51101e481944000c13032360100c0380500d03014840b1020080d4a0f1034039100b07000c16920a07030500f4861100190151035026440940740c00c00320304203695041d40856541c070440f401c110301d000d95440c0320b0171441d05a200407200201c407440041440114502d041d40d600740c1881c020b42801140c030900c0b0103032001308942600c50202804440c0d150030400e1001d03184815000c0b070700000c9080e02c000600a54030510481008020003820012050418040b22180b4545078005492854460815103d2040100028900901180380001c0c1080c5001d4008118040c1d032130200d4803039003140d41031100e00148410103c140d02d10840380c0070380d9195001080d030700c0d510030290002c20701e410582404080c4816404c1c4241d81500039201480400c039081660051442444403003408959007800c0030400505a20160050740741034180004c01c484a0103c4086024 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 354294190 1250 354292940 354292957
    0x120103240213062601060c11040905031309050705030406050c2a070e06090c21040f1202010c0804062c0a0615061205040309031406010807080c06030a0507090308 71
    0x89404402c00c54184d00031030202141c5805411a40504004c860071003100c1e10610440d01040303580c001d50070500880000803d440e01c8000c2080040d880036242c504d88a030003c00e03c0d04003607880d1003000541030300b2078003440d88030350a1a036070b951950b0b650740e0760300e0010314014144104c8030b82d0601032002001501012090f01e0b0b00c1504001c10740080041407245000026044140000c3e5050180001511459211504101d08401c0d080d2142480c0350005250340d421115048418507101c140800d01c800d4408644215001e5201d82c01907410014069003a511000d0b080b5001540420006010600603404000310602c030302100a01c402d02d01c009201c54600c03004591234990050302c2c0e03010802040d407017600c0c0320681d8071801c03800c850300d0110003400341c4420060400c03026031503000050405109102d640080d40e441741500c4a4403c3e405980d03591148240210304142c41059004900600000b900c00c44510340241401d16545d074001e000f902400c1c0141a0100703101a401000c000954110007500c3e500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 354295440 1250 354294190 354294217
    0x6300103020306100521121201050109121a090c06071a060306070c0b150406031203050109060f050409080c01050705190806060a0518060f0403020405010b1201032402 73
    0xa5046004260408a0142900d50f025185000401c25a1645248001c0a0181c494030780d98204410420b6420300c00252440b9281c40000540214460b1820000c90705950081e40c400e030581c0d4850b0ba9286942c01004809800b04900d0b5189006072641d80020b99848100141511440b1008002084041d0000801200d01c6c0d60068840d07040e02e10301c0c907021503100030f0031030050000c0e00b450030000e8440004078101400010413000080c410780400381081042c804094410004c803984c0c1c0c2070203442c603181442d5210000c0d0030000001038200c0b60303000e660103550001c1642c000390751802d01000000c0c03d51100c1168035500c00e01c8015801d4500703200f4988103100948400d50b9804023a400c0c4103019035580c07200d00c2809120401d009854481c201581c041900d07505045a80303500c058440301441c1103461110343d100c1c600040c1d940c0e8102415000d0001ca91003550240007076602d900c0442041c1c042c0c2410000d0000c802c10040004c9000b0cc1d4285034894410065130460360094681007080e030b0b000320008400d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 354296690 1250 354295440 354295537
    0x10602070302011404260304080a0b160801050105040504020d09020604060306150201090506220f08040603110910050304081209070312030b030601030b0702120304060509010c1b0206 80
    0x20b5507044070705114131080c4030325401d29150420480388580b650100000c803002c04080f0303118500300f10804c101d4018108900494015074031358940f0803d0b211080320001d1b9046403c28442200300d004140a90603200140c43d00e0303084c2800c000601000b50008951400c00907100c51610015840c0c220042c005040361356030200726035080003100f85240702d410b0f0700c1c941103a01d400000400700d00c0109c0d00941003d45400e0003000700340c01c008102d030111390003480503024080105550041014850082c000c13a001900d092004810400307600303426010354440c1d030760000395000885901c0c52040c0c2c025944644510803150518000b1384181215900448500c049580b0252040c024803240754a5090305c0645454140000041391001c130703440d804107203c000e10368034a0780e02007003d40c0e009004032401c48906000031602c80ca407504100300a00000e6811025070b501c0c22889218046c0300e091003d80388141811030442c079031042c0e03080c400c0f40e500407201c000100c0c4d0010300e00d61b01196500c0c2c000010103460540e0288 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 354297940 1250 354296690 354296693
    0xc250f09021815121e07030507080105010e0a0e04051504150b0d0201050904090519050606120c060a1b0f0303140f060d06020d0213060c050705030a1106070c05090106020703 76
    0x100d4040000d00e28071a241240e5044100d091080071200d405003403203d0078002d130300d40b8060791780c080e080c54612100280030715081120050745507010354414417266903452a10b90f80c039401580d0580d090a9100d03000802c40f0418084038182c030b15915001071042c41290310044c40701440301c41131503056600301c40340007130b00074071025100c018010007521450031241020307500810b40c0041d00b03d200d011a0301c0e02031a2603602c000d0510405104507100010080c441603440c2e20240b0b01152500d00c1101c51510420b40640202c8a4000000d070840807003402424591504080440555144480648109862107180c51000c0010303810004074841c0c070b11a803008035204000e9514241c081d5802071080f003c000001041110603961803002d01021a009180107948480b08852a0f0181c86901c00300c20b030764540d00d00005401c50b401803d0301d0165000b0030a440345030343c41d00c040548a19410502820001424114134040d1400d44010441c4034480c1d8801403c0a546002041d40741e14242c1c040c00158000c00c00410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 354299190 1250 354297940 354297967
    0x2030703031205280b03070902040603150906060c0803040c08030d0f14060109120302030f0315090a090308010e0c090d080301061404180c09080604050d030f020c250f0902 75
    0x190000c42d11220300e008040a103801310b54865420300020710003a164081068603072001e0000e00301a00e203c0340c0940d07035107403030300b401602811078006100310782d11504000003101c45991058005507590b03951100c5d00b000f85510364051541010304181c5064440030b00008019070100001c0105803c82400855610400b00383c80c006c41c2c6c01800c0c0000c000151004004141e03034000242d5042d102e030041140746681b82d0742400c074a14010800c51240300c1d90004144202c034413031084403468850086801a8441d6600c8500b0402d5412030322009010568080050200118034600c090780711991150340c5040c500d105000400d90a0f42c0f4a06072000000000148041a80300060602c0320188400d50313490945403026020b0710701c80e80c0b92034040c0da40e914022a50340c1072050003000300405020089400e9414142881c40d15071107018001c1c8042840c02884c3da000c9030311750081c0d541982d05d4001405c1d2104942511307200542c15100345160058a1010201d10300944052040180c84040c00068654110013040c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 354300440 1250 354299190 354299201
    0x305040c0e0403021e25051512131118180706051902030c0f060a2009210109030c0b01050a0807060c030507060603030c150510030b0c07020307030312 66
    0xc100a000000c0101180d000901401e101041344c82a001e0613000e540403e06140d12060312048002800d8204401102d405071000d003031714408c90b484281104898080718507841030031015040400c0440015810740c0144184540850041c8865545400400c000900d09800843c2c81c40c0502e01450500c14009440d804640100310b020008058040c10034001074218000c00d0b03043c9030f0111304900b14040e181e02c03c0c03081d2144102c82100311003090a03100440b58540a040700d0308842d07203150488107881001e1205040c45100303607850449c5d1500e00c01d08203000c107002050441614804020300c494412007000d00c503e44842c0e009580d0011500042d01d045554010107078080c902c11100722806200c000c1001c54104100c036028100f00106619601e010744440c0260742d80030341544d00c3e11130000309145e005054401d003a44104010880740e0b050815007411a54252222810b1200c900b4060001641780c064150304104402c65060404407280e0020740b40181c9038000314009200915060000911406103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 354301690 1250 354300440 354300449
    0x50c060603010e120306041b02030c0f2a1801091a040b0108061c05120405030c0118060507031701170d0309120503190e0309030c0603100302061e0a0305040c 69
    0x900900c0d40460f4250394601c4408260480400000003041c8985d41b6a4002200d0310055004021208564003019440750480c206042c032502805665815084000c20900f14900052410034201c44035200c80850f4203122401d0160005c90301c080143c010034071a814503000b0904505d0205109030700417040301910440b40b40e004e0140c1d040100040c0d05a0b0480e18032540994282d44071a0454801038188001c020401c2c0058075a009244e0a448013102110040041d10300903411180300004400045404c444c1005050f03000c6d84c01c40d0020b00140e071240c2c006021440c00f919000954925050351040059000e9116002144da0340c10428250701c2c00b8003075008224403506041002d500b0903140c041c01c503ca000c8021040000000008203041a404140304000144103810824420004801a40c0780c1c4111700c80c9229100f01036460301c3c1413070304500300d0340f00d088503e0400507094a95420303c0120b8200c2c4a0b07008900c0c0ca41d8038080116401c030b0000d002901c00d903980210f01424582068502050309411 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 354302940 1250 354301690 354301693
    0x6080105010e01030602030c12070201140105060a0c11040f110c010507051801050702060d05090721150b010509030f010510090b09151f0513092702030709050403050c060603 76
    0x40080c103074802c082d50b045079082540507a8941d20444220364500c52034411907151458401840440da50540c842c06000d0008080c850090742c9400402ca41e90180302c80d401d0002e03d4038814000040c0070000094028080074101051500300386442d01e041c0c54201c0035502c130608000c20340703003030040090095a41007100d5007407151030603482502a02d403000060980342d050102c009012421515807008941510700e4081040102e40ac4c0f05d40c0403078443c0c000e489280b008110030011302000004041c2102ca445910001d12801c0c6401110107002500d600d21a45051100501486034070752014400b010800100324000191361520500404817050580c100c10245440c085000b4200c0d00c560503c150007020000b05007010040d240001480040550340900c3e0803418a500703207003c1da8000e4044d150a08081d50240d80282d1107500850803211410001c04030004075271055056012441041030089001409442010380c88400d0001951400d070740440015100203060140607a091082c0d9400100860 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 354304190 1250 354302940 354302951
    0x60c0b0c041208030c04030605090d0f051812070801050408190e0f04020304020a0504020d020d0f0b0a15020312010e04050d0e011d0307050d1101110604050d051b10020a03060801 78
    0x31400308402c8030ba05004080590001c0403444c00d0008109507002107502410a1005190010504e6101c01e402d003c1c55001c142c5114148030001c0c010010340f12181800b001040486040c031081100f12512151900564000c400002c101d420080c010580701300d009402040c0d40e0085210a211002140c960070803c00002c9100c041040c0e88440d6040c074825400c44d000340e1240c46c0c0e400003c0e0001000e5010540c802e1000900451080264004d03101079003001c0c4003005120403540c00740341602c5c3c61290f440c0d4001c0300d049040c4091604c02b400aa440790041c4100e0f420103540502481304400b0a8020b2140305031846c08000410104021b0308080155614042d80344000700c00c0081e2900305a414090100304c40348d403010680ea10200020001050300070608d58904045050040e5106150301f81c841c0081c40c1b5804200d0038181c0014028000d90f03205d00200301c2d255000b002203440d500100b40c5240460307c06142c2d0039080c6001c01240b810300b21840740050b5100d142c0c0304050101c90130307039116080350b90600f0b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 354305440 1250 354304190 354304199
    0xd02031b0a0b15120a0606061803020603010909080f0307090f0603150603020906071505150a080a0b07050d15081608060103120302042607090b030307030f0e0604060c0b0c04 76
    0x51008a80003c0c441c50f904010782c20400009055200707100c2e0303000e4a4030840f45850b050050301c0d0481c500302e804a444010054511030b0b4400d20391006804043e4002d44104010444162264009080980242c0e0b2440c2000501c070700c02da00039401500c0c00760001c0c6d01001c007488a10000840d040c0100b00c2c40c282041b42c0800b54402d4010b081851040b40141540850300c00802c0d204d000444480561210024401100c41c02919004203000c0da142101030007040c0101c01503090118201040c3d8405600504a20099603500144441c00901e03c10070842c061040d81226103c1d0b00445000c0f9003001c840b245414107181410346000004240720002c0840140d040040440108100d8107680c5c0003914010107183c17015040d0041e10445d401002680c01080001c0c0001c12061088100b0080c03200035154880c2d43c4046100a41d101304282c1c40e4036410410007080020301500d1070074a441128284507991080132030010b401034100ba4007100104a03911042010030181c0c00d0860340c0504c0c54881e890602d03040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 354306690 1250 354305440 354305453
    0x4210b0f1302010e0a090204030303020c0c060a02060408031b0a1e022a0402040308040f03110a0b0a180509090c0102010e190f0302010b03060a0e19080f0f0c0d02031b0a 74
    0x181c002a0501140c41e0319100541c49080c5540050719440c0030640d51030b41d980c03600900a5010040f00c10322070050001d100b045152007000c0f02c05c4440140e00422040e200c64407070070600d038805010100e603280041a468006801e081c0901942481922007904920b40e20f088e26060b050300d100107100b150030819180105445881da90340a26500080212a40a080c1d02040089c0b0407238001a02029000c5000603014859802c11410b881c07040c0d4490701d1940e40344046c00b0480e102c40c0a01b00d42c000c402e015024810b8031840410080509000030540c0721540e440c04a0349682040d10340c458240c00082041c130b02540c09014106108200c8401007200344034414112101244540340184034008091002043c10710035081440c4842c0002c003a1140c60402c04500c0000300035110f0540c2c0f2a00a503040211050751a124032512590061045454850190303c10a21640000f20003c0b5510040c401c032843c488003048825035842980d00250382c1e8155400000c0003011008050501c903500220f140d1001828 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 354307940 1250 354306690 354306721
    0x3260c030c070f0503071b060201020a0203180f13020a03060f14010507080409050108060703111204150f140f01152705180412050c2104210b0f 63
    0x904140c0c548030390080c0303090404001c1152004d4028800800c49a0520255041440704000766040d440c4c0210781d80c0c1802d03801c3c0d028940400c00540c00c10701000104250030500b05200150041485002d009074400061808007245100c00c0c413942c0c00718422103a130b5090b104402c080c01c0d010f0f0010781c5c074502e000c0c2440c07140c0c40203005042c10060003285070010001100241d4002e0702200c00c05204942e1a803403a6561aa800c0310031100081c01c20404107a544030b82421030381c41c1d03911104030b1034440d601c5d511a490700c0011f840007004a690795481c9a4a65a020300c5501c4006140c0c40c214001401c0a02d50300c8032101040e0810041c1da00010070280c0d0007070b0418907464140d40318100d02c0d421b961540e203541c4e1068010390b01103508031005c4081c1d28812240440c07001d1165100d41ca0030182d04501841c1101c260040e949481130070b80c0904052000142026000c140c221810394a15241070780391ba5009050b40000640c02c20600202822102040524a811548808040207600c490321345501010750307110 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 354309190 1250 354307940 354307951
    0x1e1d040605280302030706020307020301050717070e0a15080412020d020a060905100c0203091201060b1e0f0f070b0708071d010215100e06060c0a031404030f03260c03 73
    0x20040340b82d49001000325005000315001410356002030340d6110042d45075400b5240807032083d4640000942000c1c043c410701c81c1d0b500d11801414045130340e26082603920744030403907003584d20800080e400681040300e95005400391a03a035940f4405400d1629283ca00b24641c5443d4000f50b4000014aa01d665070014410900b00c1d004540480c1c034503000d04042d400d02e084662251041e80c20000440346941d00000204502c08064548294400c00440700c0780c229440b500601540c000b0421085003104c010b050300c0404c0c500000441d0307180282c40d240703d40c801c2d0300c00e940d00344c0541808a1035006105a91031201d0740f00e03200341801c2c5500d1a060724010840c840142082c2c0e1160305003180c008459108106403940e100d40d0310200c1c40325090003000c50b03504240324450049810231803000035000d0706040c0f0586066281c3c410003040441c1103940c003522440540d944081c0840018440040860000b41080066602039110007880001c002440c10390070301d8184030030424001701010f0040d400c100d942181e9201 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 354310440 1250 354309190 354309229
    0x9140f0403051e0304031107030206040b09040b0307150212040e01062d11210a0f020f060a0213090b0109050609030106170309090105030f07060f1e1d040605 69
    0x40d6500c0c902030790103010300e407074020310302c0100b80440c0030707880c01180154011802a194250701c1201d0801503a03561003140030003034005400b0302c000c000a4036000040e045811006001066156040303001c42e01d0407403554400c4810120501d991102142c041c0109406d600c00c81c2403284c5498100480400001418401d80040207012160405c600703d525040b08100c0036410700211200800c9080204252462000c908090007042e80600c18134070910304412407281840ba0342401c0400c440c0c019500703402c00710090303400c3d80511007405004110502c0118840c00c0c0249005807120203040042c0035100c0d16812a4480ca458180082030581c0c00c58260b000300c0d00c00b00c0324199106152400729016000c5548014252010041010406040400034006411007690b8484581e030342d4031304044d60340b0312806841032140c0000000344200d501c5003281c42c15030f0b106414041d00c0042e03144e90700601c155103120140c0000c1c12014036448103103800341500041c500304540521403030b070070b142c0000c0c0e1081c1901440c82c00d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 354311690 1250 354310440 354310471
    0x402091309110616030e01120509010c032906030a060308040308270112050406060b0406050c0f0123041707110307060e03031b0c1c150203040b0c0a0e04060801060e010914 75
    0x6d580c420840490a00b04103201172005080c09401039000e060b1880340c9e03002003818081113482070b040f80441c203010f58038100f8410b4440d10142040c004a039001814210600e900e800000c004501c40000500080d48190b400d0b0b03544540e000d94036441d540198203101940080d900841e01c8a80e485050b001d24100c0b04d450025141c1c40394a000c000424640d8000200c992011900003a60354012000d030450148101c02e803070014000305003403800c03103d102504080102001f0303400035203200300d11603566105106090a580b00340004120050540041c001140c14100754180c00d9228101800034400400980c02d000418038507000003e40c0728042c2422000d081645540c1021003400308102e441060b42c0080c21044150081c00500703010380408060a450f403640420840c200c050107072003164402c41c1c02003003900742d07a00c44212f041d049511000151013000210300951071181d555201d508011300401000281c541d1a101d108482e1031016400840000d1801401440602140e000243d220015104104c003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 354312940 1250 354311690 354311717
    0x5011e0608091e0708060114060307050a032007050d0c0b061903320606030705040f1d06160203072109030506010603050f160210020306040209130911061603 69
    0x140402d101c010207103d010540c0c1d8500003040101d0040181c0c1e26074801d81d42c09a03255005180e400c0d041c1c16500e600880104005100944207002a2039400344a260101d0703204421408805031020b11110003403140300000d401d500b088400c001580c800c01039401d1004d5640007580f03505448010081080d80194039141c2d404501c81045403503030028640c04030300740e0741001040c01001041403200109480016000720300f0702114400007a0316218100040c010f00c00c580c02c0c04148805060f007010a401c1003602d52950b01022200490202c0f10084030038003e14061810040c024000052200d4100554204202c0b038008941d0b8040061224004800d20785240e104c2c1100c1181c55607250b500103011801100004100c9641c585c0101d4054101e0101c1c0107015203070041807222034442c62142102590000381100180d002070f0300a544d20030780c010070050500c03d0400c0415291040c0140c01c055a40d03131003c4000401a00c10f10110340e032401502d9a07400c190a0200103200001040006420700102002581 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 354314190 1250 354312940 354312943
    0x302040209030f1c0e19050118170109060b180103082505070501021501081e01020c0712020307090e07230a150f0302130608090c03030f040905011e060809 68
    0x14080402000302c807015030000035074004ea4051035000c0c000240040124460074540803440110001c0c10b015104181490240159000ba040301d04c480d50f001300c410000140c1c501c42e0103011450b2440c100010607088034a140031402c07a000307007811a1041210148070112415144803c50540b0b41c002c14840d0b94a06c20f486180381c08070f940080c16206921101c2d81010480701050050844038203808076004003070385a45100d501e003000d0280036825070000e020320025240d00c0c400c11159403501c0000510b0324548411081c104120b0f030700001c420b0300300c4214420860404010403801003210500801901009010482d2610207504c201d21102414804400785221060b02941481c50300600824600d0b41e04d100051008024071043c2d4080f8014242502c44c0b80d001c0e0084034044a40c203d12a60710300e0802c0303400c0c0c03020340c0301030900090342c8585110060551001c20040030300e45407000d40e0380d45407460007847c031040d0f0340705070030805070780700c0a282035400107148451003401d850785800c04031426a41d01c020340707 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 354315440 1250 354314190 354314203
    0x6050f1c0606120513170304060608030a02010e07080606030d0c030e180631150503070e061e010203030a1e05252a0c08060c0405041802010207030204020903 69
    0x80d8440d624000c00020b165400c50352000300598503050a000a59455074020a266003602c405822251420340c4000c0c0d201340c0304010f6a21500c248400600c440d203910940d0321303541000c9200d401503913640d5001a8011380030050a402849405c00030052840d040380070036103410003081c8800505c021041d424040600555101d4401080505007841c40803030044034071800c1c1c000703641305409455008103a00c0351007000000421070b60005039a003510501300d845400010310a401042959140040000c0313a60398043c081c40c0000e0810180a41c941d00b801c0e000c21500a403080c42400346461000d60b00031260342c01105482e486240c1700400905500c1d10344072421141e00090b600c0410900d800c0820200b000703081c80085410b00780c0c3d0700c1d1400c65951580709841c0c460441e40c002d648451012450202c1030508581c03000c0d4544200300745403080c2d6444040c285001d601b03403505402c150303010030240494102403264a00c200845070391031003001d40640003c0d48030075542c00060b0180b0340000d0000160740701003000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 354316546 1106 354315440 354315487
    0x30303140411061c05040b0105030f0d1707050d180b0c0c0304050904020d1e2108180c06181207081005071b08031f06050f 54
    0x200055900304040090b425000c0891300340e06000301d4024540200c1c803a059016140d4180810141403400c9040304040c03e92080030b502c400c00380d0180001042d101cbe1084400c1241d00c1d4510308880a100e10064203a115040a03141342c9101114610301540500030038411040e5240c48a14189510030326284000c0c5500c284414449440c1184045030420710050215000c40b1940c1e841c0f580e140344515035002d00c80e4200e12108140095049910121412104528090348070b25502401010000d000070711042103031010000e0f000c00420070007448001c0203140f207480f4456600d41a08007818107020b507001c0c3c540801e010900e020b0010f07000c030645201c0e00181c0068514100064010a002003408017044862094a50381400084210540c64007550540380d8a151003c008200e0981703540c4c400c20090340c11442001003687c03041c10317110444a15000c007980d500c101713405e0107505032078200c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 354136690 354316546 := by
  have h0 := BRFrame.cov_init 354136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 354136690 ≤ n) (h2 : n < 354316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
