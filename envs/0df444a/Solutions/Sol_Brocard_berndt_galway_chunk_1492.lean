-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1492
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:14:21.51208+00:00
-- url     : https://prove2.me/submissions/17ba492b-363b-4bf3-a5fc-74d8355ba197

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 268165467 ≤ n < 268345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 268166717 1250 268165467 268165477
    0x17060f0618130203090601030f060f020406021b0f031f0209030f030307020d08040c060507050f1b040b0f0114070305190f0809120a031109030307060203061309021003020c03 76
    0x240c441400034001c0c00d00000819940c100001c00c1c1c0d0300441d2007107190000c000320310095803c0603042d03001000400c0050121108650700740e2040c1707030100310000710022401c03e980180e0000c60140e0000031013121a0803d811100b840440101c4030400035443c864046030f240c50707188820000707400161020000c1c04800c3c0d011107074030b510050101c03050310754130003409030712a0015a800130043c0100000f0070030861103102d030203000f1030700201d050201528012064070309502c0604100c85c0d50280a00c1b004903030101740f0212102c0122200010071541160040008450f60301d400c0a2180b01c0c01038801000389d134004484204030300c000c07002c10390b11001802d064074180500480110301d001c041030b4224155501482820700b91100e0745039450a5124103828a0b2140ea4102491034452420300c010741180b482600001036001e2000805403a04c0c002802090459000c0300064841c00c1d000000e11510341003030018898034889480042207090000d900040404001e40c2c240001c0507000b0844c1000c1c210b00740100c0e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 268167967 1250 268166717 268166719
    0x10902091203070507060908070612020a1b0b06031501080604020f030a1b091817160f050a050c030a11040510050d050c011e021005090a080315090a02090117060f 71
    0x40c0e11100d4a10f050f994030510340c010311b000980c0e150000103058a00240100c10b40749a03485125080b40032600150080d049030500c84c0401044180614901c11000401c440041c0070b0441d00b8024600300303003417501d8200e5504882d010030a03204010011070030040781301c1c0d400c554100c81120001064900103460408807000180042c4900c0c0c01d074203180d214602c00342084468046091040320782c1d40350b0804805800c00404cc00c405031004c000151050b4050041068142002080f680c5400e5038661004d902c032004411502c0380c2c40491104180308041100300600e990440050815400076035a03040600200b03070000780116202e5010030180c0c0102c064010160402500d005659259420090f50b16400c000f07645010440074642c107521080062180042941d164004040a0302603420300e200034000106841c0c00c41c0502c03583c0d4400204240011806500110840c030321b24080c10302042502507024006002c1c603441003004007816600072242400702c0b001031003001e0305651000003181c3c0000720500c0b05 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 268169217 1250 268167967 268167973
    0xe0d020402120c090406051005090d080c0d030b0a0f03021c0611030a02220b071e020d0f03030b030d090b031f08030711040902032a1305090609150109020912 69
    0x10801400f480b0140c807650070308903800e12441d42d9036014880c0a041e004114000640300f0000c41540781880301c04084030900c1071300150b141001295065040040c40c0d02e2800010740c8864040641c5d02e0000f469201900040c03070300304841c5d031865000803c0701d60040301d0076403e5807001c985038003800443d0744000b03542040340c02503a5a07807411510090095204080d441c1d40e440034484001c00300b001d900290415507006106d15450603440c2d03110316444c2d201d10400c1c0b000c2c800e003e081000041e121482113a07076940c49610a038541020603c0d003d802c2d22803071500f40c0d0180e80b00c8103d8400d2241e01c904034100b19a001312034a592030326402c00101800f140c1d141040c1504001140010780314500000a00c9c8083c043c40d8048400440304e001c10007500c2c140c0e400a9403560001d07805c410740f4151200749032200c50040d04c0289040ca4000b020a25000c682541d04d84c1003681d420410440e400300b401120742c0b003811503024002001c06406621341c0c81c2810f0081088050380410598070079265280d803088800048812 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 268170467 1250 268169217 268169221
    0x181104050603071d09040c0305100b0102060a0f0207020d110a060c02090613140c03071202072102150a1a06120708060604031506080d02030a02030706050a0617070503010e0d0e0d02040212 82
    0x51f0044e8619880211040d11901c030103240d2800a5100f10109000140c0c054100c6031905101038014000800c00a207005a080140030300580d224102d003082d540c8242c3d542500034010707108004110000d0340c8504240103039041c140380183c1e102424181e200100f20350501e4403c50110b02c0d00010036000015110440c107080a104140107583c0146120315190703510380b401010f4001c0c90398240d01031282c00400921001881c2d049034680198100e00301032044c8112000b2120801005a6010341903ca00b10f4040d601c00c00d0040d00048080700c2031400c1d006881042c602142d00c90f214101d80c800901c2c24041005a401140061382d031601120000c6401a01c00e140c0311329041c0000c0002d105034420441a4454901c0080b0b01900100555552810076009541001003036100c100203020024076200e111a542d20707001c02c10000700340940d0580c5460a00502c101400c01c000d16084441d102c0000115034132128400e940c40da80b0007031142007840c042d102002071510901c0441d01078001c2113507200b620203012007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 268171717 1250 268170467 268170473
    0x3030f0b1206061f09090c03140a06050a05090c030402040c050f0c06010f12050703060b0d1202210903120d0f021b0706030203190c0c050601181104050603071d0904 72
    0x1a485004800c01c8a459103010181c05140c01c0b003424070980c190200305c0301e8004000e800c80c1c9a00401501c1c520b41408210210801d15000c51690101e90307082150366039000601203801c00045a001404c4161001090303400e204c44000901e0200500c024800d035101c10b484403806103c3c03c2600c039400082e20406072030b0303109000050340fa00400d0103150025000a0030010f211035090a00c1031804d5000000380185034155140c14018268940075503270000f401e2034207000003442d188031008240101c0d03400b400c615996800c40b00c2c0008c0b484a01c103070500b07505008908641e9030220f4624010860040100d80d80d5504801d900041c191403859156020310125403840e04a0304602000e2808030000d041d1151a034a505042c2e04134001a144003285040081411840510651200f43c000700281005131142c00d003982c5a52074050260072043c2414040c2d1248204045d13540105180c4905c15404507040c142414040791140c00300805a4041040408c80b030301014409484405491501410303402d0f43e841c0c241 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 268172967 1250 268171717 268171723
    0x30f030a0c0216143d0c050d0f080702060403122f070203060c0a0e010c14060405071403010b0d03030507050f070303231302060306061c060312020609030703030f0b12 73
    0x151254015079110f06100950701408502603640070a003c0c1101c1004400351700c2e840e50f2544100c201c000d000014040c4400725004210314000301c40641e5070801889108817004142d541c003c0c15860a6501250901c00040d40000e0142d04e03001c044500001c189503107000c3d101b90350368400101c040c031a0b0101101700d0034250904c024402d4a0080e030440c4c039180c5130308003000064070540c80c1a600003000205450000e40c80380c1c0f408003409010b60150340800c03010300841c0e8282801544e0484580d030003014100714404518010002d02c0108900030000f004414010078041c1c090f400008080560f60300002e120b0a00030f00544541c1500d0200302a00c81069240240041c401d030705007d03801d510030b015001000f046136089944031301001c03100d40d80e00c000c569083c0b110a03000546103a90205007404150380c039000ca60303011090601d98003c042135051440c1011030004500303608001c210741000e010002c2032007000040f030347d003280e0500d800505194100c03c0403004206005140394046101d40303425603c50400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 268174217 1250 268172967 268172999
    0x70e0406081e0a030e040f09020405090c01030b01050f030a0f180506240d020130060e0105010302070b2805070c02130513020906120703081308030f030a0c0216 70
    0x41890204000502480719503803d0300ca040280003914140740c008003402c0541100c482d04150803070220310b51199070b000030b0036628110f410b0394156110002030b0b21207603498054000d60003002c0c00e28034604010030820140901c070040410404e2510781558041c02400c60b4000074429514034070745001c00711145440b50b10b03180305454440a0310001c100c1801e01808680d100c04031864000c249a040a410f64010b44840c0c010000c40928086140307079007032842400d0300b104c0485c20007200c400a030407030408031448069241a0041d504140c03061000c100083c085030300311504824850070410351300310442403c2c0256034155203041c075903900341801d002031070f038004022003183e51080b10b0080c400c400c407000c02421503000326240d107880c5910024040250424800c400d40100d809804c1a0840340710208251401e0107036070007141d4003e0009028000c030040b11110502038901c0d04090361904100c22443e80c0c15002c058100d40402c1e40c2c0b08610003e00d4020008061030030510000921740503030304c48511a0b06194 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 268175467 1250 268174217 268174243
    0x70504030b10060903030c050a0602040803070c081207241104140f0306011809170c10020703020a0809030312090d020708060603030301060c0c0b0304061e090515070e040608 76
    0x81c18000c01d034080148030000095820715510f1441c09440c58038100d4618985440030b54060060b0a1000b01255060008101403d0404019035454400340741480307401002c1d903c03c4030f040e04071412041d0501c0c40c1c2001c8500041c1c2007140c2c01d0260b00100704104074a240141210811403403e100011141c40750006041102c03440c11103c003114103a071083c802d41c000041001d80d8140c00407801480b00040520142041c0f401520300080e85500366550200700750256600b15032082c50104e0000c15445040002114010142e2030544c18021141c1d0007030360b03a0b01c2c12a80100340308404243e185a03501c00b001170307990b4105904c21240b0103040110146403600c0c0c046d800980180580302c8082810ba0000495602070389002e00118074682c40c05d001250104501c50701103403108007082000400850f10340195001714090f00300081c0d040901841c800a50b12070003d4140c41c9400c2400103004103a000c0b400615030b03039108500c0a21907a400300d045030710904d0b401c42d00b80d20502d0300e10f011511810001d80720b0070b588a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 268176717 1250 268175467 268175483
    0xe0c0108070f0f03020a090308070f02090612030a080a0207050a200103090809040b010203090303041518060c020907030e0a0302100608031306050c16030b10051005090f0d020907050403 81
    0x2070722082221240500009580071888101000309214442e500408600c0b03070600d40815000d071203940b1680c0c16404280c0641c0c00c0d00c0c082d9101d10940ca014580c0075006003045545c00c40340800741501d103441c0e000320000c02e001d0000c80382c0082c0804d40c1e40e8040703c9541c1c1e071082c140d0302e4070180c51034040d00d85215240c1c0c181002030118040001075003c1d10440c013405e50070664082c140041c50041002500c50048041e0441c00240004c2069841c100050300242c6a1640313590b607010000c1e800200060085a000382002ca1107140822645400800030041260142c0e0300440039520040264060680100428000c1c800e02079107009056000c40c5070382c11002404401d20105607038030030255513030046202c4078031100d0b54400308000720303400b8000501904480304252040e0307001117021881410480d1707000342e070501c110508000e8451411403101f4044c02c0100c40d4480340602e0f0f003500400e14000c00140c00d0080d400012088034580d108210340c0307092039005141c407009252411000b00030350041d10080311284 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 268177967 1250 268176717 268176721
    0xa11070f030806010521040c0504051602010b010c020a060c0c0302030f0a200f190f0f0618030302061b0c010e032205130507050c0f07080c06040e0412050c010e0c0108 73
    0x36108401b142d0320006041c41110007440015220041700c64068411161652400b4000407591910b00078148030b110007045070151760701c0064000e429030303c082031450304000e60944035100507600c40000c50295030003441c1c0024a001640b0302035880b081d16400203580340c441c1d2270b0011000c02d400115100381c1c1e8414800801034510451a90168841d640c140680c0606049400c103e00d090488aa4024100705010031001d1582d46440d0002545180c0102581c01c8840a0a00c50140c01c00e401c92040c021810302c0000861542e04c00a48800f00076161107a079060310000400c801d50300105650300045490001c00082c103900c0400e50740e82e805042d9034030001884d968901a18044a401d0400701c1c0c40190403000c1e84a081c011440040600130000c0050020038804a03440110400500b141480c0b00c034000c0114904103607009103449004620140f10b07480c1000144641468200c50fa900710307601c14003444891500100988550141d41c140d610a5031030040b03222003c540000c5c12406e040400e8071504429 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 268179217 1250 268177967 268177969
    0x70506070803160c1a061f1202160b01140109050a030803010915090509070302030708010e030403080c01020c061005040b0906060901080601030b0a030b090105070905180a11070f030806 81
    0x50300400320058010301c8144005220320410110000d007820395132500100d580d1103a5661250b808030b60079903840811260080040c2c50806c1c0306000444070a0800130074000c0e6461800415207480984480d45076600825074112540c00c91150907101a8480c5a01e81c1c00d41c1c407030051400220401c1e2030030340000c40d107090005640c10f1201007001501e403c100358130f14680c01e0200709000b400b02d1654911800c0030004001a4240c8a4440c060141c4041006000c03003e05c0e50041502c0c22006d41c00002c4144d00d0b080000041aa0010071102103950007035101e40c6446115101500900a561544666020301010050326203c50240340c41520411a410001c203c0c0010a0205480080f6011038105008004070007840d8001c810540d40b0581c145408600d00180c040400e04442065104a4000d5401418003680202c203000e80f9070310010303500d41003103a40e24003c00070317612183e0031003522440460b8002282c1e000c6240d42064400c000403800b12a5111014540381d407000b0000042540054030f028003040305 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 268180467 1250 268179217 268179229
    0xf150c0c0d08030403050a0c0f0302010b150a021506060f03100801240302011b05010f0e0c150703051c06030c0503010b0306060a091802040c0302040503280308181e0705 74
    0x1007508001e02c01d00b0342d0354560b4166010b030b00c501d401e2001c2c00b440300e6190001529081558564620960000c11103c003624244114a10300321141140103600340305001c03003181d00281c0038030f50f081102078000350780e16428040b8090f0300c1110303001a9405000001c02c2000101c000181c2d0888290034020024241156840810891500461070040b0394407441000950b1051070f8407001c660303900307214801e410955035036a405c44110010300d0103081e0f140d060400c5c6842080c04001d1100300207403400a011010400900d0452003031800c01014484085100d802d035400e4110702020131a5103510800005442c0d02300424034540500c2928400e600700440708502c0d05001c144a4000d1401900c5090b210b81880c415202500c00c0d2010790032042d20a1100708090fa8440c002e0350720b03601c010b40300165201c4c10300c01490705010102c94100c004055400c12507100010042d554a0740d030350140303402d004c240c54080f00b090030320540040c014514030980e99050004a1400e40c1c00d00c510105070700b02c48140d9521824040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 268181717 1250 268180467 268180489
    0x90105040b01061d040504110f09100b071a04030e0a08030c0d030c0512010b030a1b0f0c141c030b0a08030412020a030c3f110f150c0c 59
    0x70303201c414001008210300a010265181e4181c2c0390b407540f440200e401040858100301c07019140040026140012418800341e0540c4142040e90003441074540b560003c0e140c90924484c07240d12601c00101003003442140300b2180904400c02180070807034101030800801400031031072002c1c0305694004000903c0307800041203a42c5920180050a980080703000240c0040c040c8003900c0c814000704008026214003030031070641c040c001c5442d03207644a040ac080180d04407040220344040520314000c28094240e0402c1008640074001e240c0300702040300034509407030034521100e2000e01038404d54214403a043e1a001d41c10f101c0b0314031a070f810402c04540c5800c0011140780d500c5501287e4108210078444a440c0304201e140060002c0c0405142d15a2a607401103840010740c8603551200341005d00121030400600c00c2404428019040c000554030f82030503031410b089214008100b8140c3c41d40008242e141c0c4082c0a0408400400b105244c09200e0034424007070303010440303040143c091900688858a000007100c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 268182967 1250 268181717 268181723
    0x91104030b0f07110106170d0206040b0406090f0f060218030c01050409090c0f06180b090f040b010c060216050f0a03092315091306030210030b12070e090609010504 72
    0x851600c0b00c0b4a4807284034005001c203002c00c1440c44003111070460034081c0e5070007400885280c0a03101500c040c400e051042d51441401150044000d0002003041c010116401580122000030716040c240307084504260200c5000b080c403500300820405001459000d8003420760038101030800805080105034481c00c04480c00e41c0418824402840036180075407005010510590500305999210f40d55198000c0c06544a0780000d0401c51400600c0c180341c0c4030420007403240c0d4021506000316000054010300304595801c1c0580c2d5a1003104020741e119100005c0d071160400411075907400030000d843c000d03015100c42a40c0ba8030914000013000340002030012800d0ba0140d941201007420f00700c041c85600c401100170111081cde040e00b070030000d5842d034844c02001c40710003260551f64401d00e820300071100301200060a1346440d00c00e081025032a8002800c45002d094a07000a80036502000200c0120044801910070720520901107a819040c0c00030383d0040c3c004c2c80845245903220901282614070442d802 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 268184217 1250 268182967 268182983
    0x12050612031b0109140c180f07111f0204140916111e0706030605010509100302091507060506030106150c0b1b1903060f0509061e1909110403 62
    0x305406860b000c03840c07035051200d240045240c680503200c83d800d18001c1d00c540d00e400e0b00640280300031403801010201307640b034659800c02c80c0d40c6048103040d58801001400f500070301203005651460950309100028502c0100440c05060708014a1440000c2d0890b0103010a150301c2941809010310f0310201280c80340f000d020401000036201e440494011509000030f88062080b0050350000009000d0003030032100d200c10017002124500540102076403025131049050000400c007020b61078898450080c500d003c1c0c0d007800f59503040b440c40450758101c1c17505402c0340805130200f08801045065005503010300800c8001344080d0f51584410904841804920001318104460780310005e002000030941c4443c89060410f80281200c00800f075551148144034011002c0340b0003441015094881d050242c00c0144008120b1814140402d90102002d41550b20500c480c81c0c1e00300030f0000414001714604405003c0350b41178003e41050150040031400340451842c1800e41c9881c05010b810140c0b41129000020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 268185467 1250 268184217 268184227
    0xa05040e07030e0d1701090b0a03050d11160506070201200304060201090614010506071e0210050703020f0627070f06090920090f0d060627020304210509040c1205061203 74
    0xf002e0048c800c42d00403d400000d04680000480e60511084070041d031192a1040fa8a050180c00e50500168081c10300450042000502c155102c0b402a10f10079a07080c00c1c1110028015550545003c0c091245554641700009001c01c8455064002e0783e070603840b8100c14054115040307035990101e0400d00510ba0007400510021010801c441903440341c245e021980f0312641460341c0c01003200142e104403042d012840004c0c0600c10146c0c104040e9060f8401500505034034105210303030140c141d4207850080308070440e000c0503181603001405900010508991542802c541c1d901d00074001c043c00380303e52550140b4119805e240c487c1c1c2c202d110039580456510281c42c000005003005402c2d01c604607015041108400a01c0019047d44616030141028192a01d481082001e60004400c400001d10418034014802c0c0000901400113800c0741d10030b513035280c1082d88028039040b0b030507000f10300e5040d0344903041104001000c0d8102200c820801e04801040c052944c0301014480e490440074030003c00c42d4400c201c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 268186717 1250 268185467 268185479
    0x10c0e04140708070c110406091406030d0518031e0708060a02072d0f23010b0915220f060501020307050d0e0a031a0601081e0601050a05040e07030e0d1701 68
    0x5d000134101d4403a4a200b11107a0615020804403440e6800040140d60345040e1843c07500a1120104c2d030020342200141041600c940004000b4000e00b17403035078820f00070b07040700140c15a8103018503d01140c004101e8150000d040b00d00386e64444040c85044940c0c011200440c40c081054001c0381c103020381142d003480c10b18a603a18a643d4242c6114010360503002e0303071048040003030804040824014010101c0c112100d040c2c2c1485404821019442d101a078075105603204c0355181c039181550301040440400c03900d0020b400116000186102c5c406503100b03001e80d1100c0c5004400e50211090fa01c0e200420400180c45900590b074a00c145c100c0517015500000a42c036071507216000348007481c0c002500c0c8401c1c459899540d11602c0012078410659542c000d01004800e503400382c0415404206400028420030000d8404400050081e10040c1045800641005020f0040003102d0041400d0107905c2940e151244005004000d0400d8000440c05829090401d503072082c41c0e030441c8140d18444060307899107801 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 268187967 1250 268186717 268186727
    0x609030201050a09091812050702010c06050601030e0604080c1203010b2a0a0f020f040212040f0812090c0108060121202113031b0311010c0e0414070807 67
    0x503c41c804101d80307040302150b207003c01e000300350020b26207080582d0760211500c4d154590401300c042c2501004401d101c0030026030707804103400c00c900b0307080a00001ca070b859000040707000c1c04407001180d40c54032444041c0030402c4038000c02420a80e41c1201502c0b0720301820008050b03288001c0c07254264545081c030002d0001340400c1d121010010101c040d582e624050102c00303500f00240c3c4c7c141910703400010094030701035080030801091200c20882c0c00f1481c24210050701c0380c40403c0503001501a0f501407903000d007001242c030203c03000c4648141c07242c9003500d85850a03642c3d0384a034214642c009400300c40821029401050781d8840303100c441403202c1c0d1142092415000408580401014001c401e20f1803e00404420b0014003174a0700d130100141e110341e241ea8a042c07201401500c441d075015035892121011a601c40e11075990754030045140c010140c0141812107c43e406814400c1ca0f951819500740c440700c0e048041d1518030380703080d5014400489440c0180c0009002211301034049007120000a005074810 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 268189217 1250 268187967 268187977
    0xb031501030e160e0c09010504380316020114071d040507020d020d0c0f0b0a0207060608031c05040c171006141815010503060310020d05071107060903020105 69
    0x185000149000382e411964036000c0c0c0640d00001551800f542071004088200550780d0186000c0b80300b518200024000030000c0c40340340b0079035401b16103010541005c1c2c416021001809001126086102c900414006c1c00c0740e80107680e514000e10300c0e035060710300440c010b001e44030491503d03080c0c80c2e109682e030540c180c1d83c000711010090302c0b0391003c51641e64107594907c03440e0301a081c154020410b007210404043d2815500365140c0003440b11100314200091820030000c0511644801810031503254036080002034040d85000600c0942061000b140500f4000054159001c0701c0700b5032000404607504110480304d040d200a0314040b2001ca040c00b9201e58030794441d041c1c0400e00300315a002040040e0000468059400c941c1030320450001103c014034107485001d04a584c0300c0038000301814503207101c081c5034030180e0b1254144100480002c01a582c24454807907000e01c2203200b55034138001001104000c0c0000c8880c0c4012505502650202c0c4900184020581d2815110380020604680042d10540c01c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 268190467 1250 268189217 268189219
    0x6080a0c1d0f031c0801120f0305160203150613060b090405060d151406010f020c010309050c1c02120d0503010b0d02070c0e07080a0e0717030d021b06100b0315 70
    0x2e541d40c2c01810f61801c10000320140e8600f2103030201c4640120b0300400c0600c040e0b0090803404002d8120101040c2c01311498123400b64503041c5a5658420710840c52400d00c4190320181d81800382c1c004244c0300c0b411014200e8401e65085403401604103201302400122030b00c43c003540c2c000d000140030000d00c82c00c0560110b41c02640c01015034101020b15a0781c12903001c0d2182004680741d4945460100c2200c400240c15000341c1d00742080d00b42c240480d00000c0d50390200d01c100340e0406407a9030700340c420b024040c401d2490f50b0201030076940c0c085030f4403948441561805035049018207060300701c00704a0707080031401610307040070703591032510316440c01100c0000c0750000e01140c20040e40c20050480040c581400090090021700302400341c1d0714200001500e480d000810403e007042c10809800e28014002c544802031340c1e0306441c01c1c240880c05406032480c60040f89541032880d8400104050a40d8a4810340c11074801c0d54801c50700d041e40c6000725000040d905208902202030240080f54201144400c50018100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 268191717 1250 268190467 268190479
    0x30803100509090a02190b030103050703060c020c130c140a050c06060409020604051009080a0c081506032805030a1e020106050a18020705070e091510030f03090f06030606080a0c1d 79
    0x107201c1f50000d425030300c02e9200b2200c90303116860810400509009040031000d03540060b140c01c248d1440420146484801400314203603940c64509401c0f0300440380082c006a46054480d01c030b201161000d01103602c8040ca0342c1c5030b4442c2b0030024855103000d02400d040d0315030141113282000d18100c02d1050a0061907500c3d014050513500110b4002400c000881c2418040d11204074064a44102c090070410880c2103404c041009401b003202544000422042d0000300b020300070302e001d0301240c21416000e09030704020300380e001c005030416a4030340c0b0005e41003102c0c2c0102810070523024684d6013603088889500c9a80d402001e42c000400c02402003003409141094404000352030400150b41d21420000d46030003180709075070031609110100300f007044065210100c1e02c05140150a24010010480d0b03280e10000b4a0182003003000340c101482a14944000c0c0340050708906c8254a4190241c080e0000380900c10000300e075030b8001080113901e07011707507001184652901c2e4a4283c8046260354044015010550444 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 268192967 1250 268191717 268191719
    0xb10030f05060115030e0a082109070305070f081015092c0d020a0f03172802311503090615030206032a0301030803100509090a0219 58
    0x9400d502040c1000c911500c0078100660401c0c50103641c15480006820030146421083c0d29000400504c0d00d0300d00d5009189151100c409a146551b001c82d40f01d400b400207441030b4144499130000080620960b44150282e866003030311066201114005842803000c1503002546100400005134009000042407401c50207019444210003000d45076034600340d000c90300041c138078081c80c207103155941e881da85c3d1100c0140000c0b03840524001d40d5209c3c0542e0151100c1c100354086400c15001d00c0c42e4144940c154540c1c0c41e041c5c6401c0355100e80d1b01d0b910b1044100840801c40c01d280b4400e08a100302e80200d048045c10080c803a42c2ca125840c0c003c41600050158000c1c494800b10300c09c1c005030300c03803401c40741c155070081020360041ca001015690f11182d90581c0e030246160510043e501d032010340c1d504c024842c1c43d05d4003400c01103000c500c000700582c4004c0f641d02c000000200138807841f00d005500c03403000c84084684161b526018401d41503030494403e02c2d10b0304403030300e1000180b80c054487c0e104110702404c0740c8101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 268194217 1250 268192967 268192973
    0xf080a0b0a05060f0c100204060203070b06040f09050604030e030c0a060503130606080109020f03060c0304020108130f0305090306070807020d050f04090f090210020a080304060509010f090302010b0109210b1003 92
    0x50350101000310901c0c84d01040d00e4180700700402000d0311003900700c01d0a60800d0310704007010351303203020b6224000c1121072000000b640c140c54079800007008149500050200322614100192500015202074000440c2030344144810b040010720405c100341d02402c245002458084201c415420160040c14941c01c01121480851014003d290140442800004891030340b0310400000c681d201c0e0b01640240c00000030040c0c1c03260320100341c0740d0003a02800c00f04090790b148503605840d41c02d41000100445222004141031551110180c82410b9040e030440300c1039250400241d034112411104000141d000c4540d480c0450b10890140141809145080741040e840d040c00b002a180350807140c9070965030b90b0392904254580071109503d02034240c00034002c1c201158071405013034480104081c3c640e5072918003040d1078142c00d6003ca601c2c2034074420108080e80755481c00902900e50110740600250480d08080f4403042e12903042a905940000001550b003d00d5440c06280407004003c902144e00001d400008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 268195467 1250 268194217 268194229
    0x180103050a18030f0e0a1511190503120108160b09040b0a0806070f080f0a11040b030f040605070e0607060c021204030305040810330f0915060f080a0b0a05 68
    0x6851184d21074080502c003004005211411020307201d88110f0800400b084a841c801000c400c1080207480c02c151a080c0500d80b00303181000301e0071800308551074013040800744800807001e4104103c11500590099984142e503e565001d07441011000f041204c10800c12003a40b540108002030010707101045c034100c0c807000030748012440d6100c40641d80140c0c0c00c10543c1c1e40e00c526001a01100d9060100c50345c20700a06010100800031b104000044d9203610000003a003803079059900400540d031840390f40f0301d0300c2900313141c280c0000d41c0e00300d4041d41480302084c1110301400503039640c8540501014200242c50315040d000d048042659815805102007240b8204812001000914080c0c3c480c503944600c0d21a10a203008850031005003158a002480b01c4010901110803109511882c01e03040684100501090b58000b164402c3d640380d800d80c2d00014440100ba088210071042c0540408841586c07560292000020f54003c0000030b001d039000504c007214540d11800e45ca04000c1c1c80d98a07a00c1d01c03a408940 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 268196717 1250 268195467 268195511
    0x60405062b020f03060f010306081507020715110705120a0b040f0b07171005060702040e010f15170105010302180703060801050c07050c01020a02130c2a0c0b180103050a 74
    0x40c0f84030003c108001070800804491100500b0b180402c0450315106c1d226480344071344640385107071481000220311028820800e21024004400d561034003e5a4070310080e00c94281c42d0440011801155000149480c018019000400f40030001e4880d42401756684010448000c00403601c599900034050085010400150302c41c403459180c1c403912011442850300302401c024100070003100350303180030311480d160501991400f5505603004102800c00488460242101c0044202c2052604a00c3c4440090800c6400100e880303480d050b4040c00c422001c490f098039402d0001a4110420f080c4000b0030405000d5115401421031400190450b01d500090303003556000d49101c1d002500104001043c00700901010342c1c1c0240074002012031203016400700301e060300880d80112841340d640103100c814034011b4100c01c540c2c2540c1d40f0a4980d400c1c48408802091001800c25034681b2070b206c1c40813a074000524129880d2015204c503038604003000d5001100074140c00bc01070070754139441c0e020001e8602d04c0220500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 268197967 1250 268196717 268196737
    0x2010908030109090b1803040b0a02010902040926030c040b07020307121b050d1104020903120c0a1407032607060f053102270f01060806060405062b02 66
    0x204001c2c110341005c414107003002e44240c10340c504480e0b04201440c0004219030450300316108964940d5020700c010f03070041c2000d200180d000350800626108200454080c40320500348000d17051003004d00078282c065140012141d240010104000510005070840040d111942c402030807240d00355103034010b10100d04501e4400300c608a81c003010039072142e0751207071501c4068079054460304140030b0b1580707820800350300c040b10341401181d0000d0410300740e4a090004a00c0742c00c040500a98400349035030720300c3d50307400c4900060f603554001c5040003d540f00081340078000c03641c000800200d903554010240d000100118654641031200f084004001002401503101141010800044c280380400c00c0d02c403980f02d4429514036000d4040c00e500b0304581d0500c0c0c000f8032680c068030b00388140c15283c8840d040c001001d50f90a805c0d507102c503040124401c10488054182d50b1603541c0e08072240c4400081c0b000f2030285004591f071082d0b081c4070950b081c0c50790312006688240001541d0071607184180503142242c0c003c1d40d9a03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 268199217 1250 268197967 268197971
    0x6110f040503071d060d0c08120d0e0a050d0503070e090a020706151a09060c011113050a033318020f0d050606130f0615020609120a0c020102010908030109 68
    0x4100303510b0140040002444014102e500188040e1510031002c18010943da1158990300807001c10320402031241d102516960b01100d00200c000e8494a1140d08000002c80c00b85060580007024600d01048020301c09a0000003444800c40900c400d40c0e040d040149071404002812807c2040c981c0c844028902441c0640401a80c80c2040d08104050340c10201d11130300d0b140d50384241003207482084a4900d001105603031074943c0780c003651000104c0754850411300a0166003480b40c001c919010301c2d4010071003e40310522206c2036035540c00030f2105540880c071000c2c007069412000c01c2d00024080ca850032400e540340a00240da40500c04c410003c8585010000c5603208110042104508042800c0404684102c442c0b604c0382c03106560f06596004000c04280c05225450407820320403c082d0040c00c808075145c003051110580780e030450384c400c0c40010844001449200e000c200d00040107d0144074040600c0b01092510740c0c1108140c84205040400324115965a22444080b496903005940608a803c3c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 268200467 1250 268199217 268199219
    0x309032b0e060f012c040303050f010602010b010f0e0d12110c040b060405010302070203070905090a17070b01030201031508010203010e06040c09060e0913020612071409030604080706110f04 83
    0x5100c212007601c4400c016990041050220325144565800d04544900c524140d08007080c64481c0e4075070f004803c1e084111040701c000d000405405030440b0f032103110045e00e40b4200b6070343e5040490a0360700d2066542d011411740c10210076500c2c850740c00302441c008040c0c40414226200e82d034142614040d042681c00040364134044052122082c0544440500216814031130401e003500010840d20807449038606055001580344c0440d1024421100145a00d0307508000528140304002c0e182c00c0c0f840003c50b16101446420250032014105660702c05404c2505200f1030380c25580190028640c1c4103000d249050508400654940700340021406011004091111402d140d018802510700b59013a40081c003010b90400d1040a0303000c400d1210112003140d043d00b40b61580c0070b1680d40980301500107900840f0000d07800d02c891020768030040c0210600d543d0304241078000050340407540a4036412980c50780243c0c0111b404034010902604850380035110002d444500800e604441e6031250f804024003500c0031034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 268201717 1250 268200467 268200547
    0x311190c020f01032d0e070f030b0705030f0a09050721110312180f0a0b0304031d18090c06070c081615030c0207050307060c290705030903 61
    0xd1420042c90782804c0900048500c0002d118441c4100780c8480600048401643c4600380c040c2c022013a031460f188159050284c99580e51401e07800180401d8550140c14004a0b00140c843c40c11071b88108030b8a45a0f44080d00d501424402400000340300791900e00c01d00a000c9240020189001096480c04408014441680ca082d102010765420003a00c00d800c650407020300a03003a0421169201c02c24400a1a440c0c0e40e2400200302c611000202074002c02e1880b40440c84100c010025030003640251544c001282186e08220110303058400a16000301024802c3d40000306044500c2c1d07084004442518106108840890115080101c060b10881441c030401c00c99400e0500c5070701790824118101c0d00c5000d003400d016003909440d0303281c6241099600c140b03030b0728090f2090102d10041c00d001015140c0d00c2ea07840e030300200000d000c2035023500c680c118070380941d8041201580b55091402452050042903032030b1701061b1400e41005100f400b00d404108a459020b0325820390010a8110313140300080c80d02005a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 268202967 1250 268201717 268201729
    0x1d0301060803180a0504020a17041707030c030e0a0b04062303130c0e0402061e0c3018010c1505010e04030f020a030e090c0d0f0209041107120311190c02 67
    0x16211740c1c0910720401146102c1707075002c07401104507a1406181d80340307519145803402e40295081038603048014085014020943c3c0b00000b4078a5500a03600e050215029004101444c22144076001091404000030001c0c0350141c0815a07100f06400d80c41541e112136014144000c1d07000300c0348540c031540400080e82c1040510103c40d4054074402d2500d60b92464030354081013480c451421440c0360502e148511040890b442c104461280d0340017000d5507c2d01104a5810302d842c40c0780700414950003190b171045948101c10f2425605580c1101d1884d0032851ba04100560300035902031015528816403800c0d00440c034039a401414000d28030b003141a00285400e0800a146049410007802150000c0c051000407076400014204034800c100e96004050f11194503101080c4144440d064032030b818428901c0d05146554007828070010180e03020b108068060309903240610076044000c126000401800c00310510a41c03190002d04d06180841c0e1504424500102c4413415141081b0001208400c02c081103003080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 268204217 1250 268202967 268202969
    0x31b010606050f0403021e100e090c120f100314060403020105060f060d0b130c0815190603020a020a0f05010b0a090c05070212101113060801061d0301060803180a 71
    0x10389406400c1402601083c0c40390f00c15440064401c82010691451a554195030040c40b10002028003403902c6081e08081c1206d1104401c0900c50011680040c00d903a0040d02140c44800d1402a010103070303078400ca041180f5031805400d00f0040442c072000800050303400004082929a0b000060905240501c0c00a0035140010003943c040d00e60443d01c0251604d030302d0150741d240c8000160100d140d11080c80070982c40d00356144c0d903030001800d2000040a454010f0340301c80c080c8030176068407486c4681620038400015006140005805134000301005010320a901900d404c0d40d051043c3c41201d401c5440c1c10007010525001694240d64904803d0760518040650074001c002031310043c03080814042c00a8603034041c5000190040c0800845403c09107014411804058410141001030031800082c04046401c0000b0001400d600d20001085060040d05464125050303603903900c149130301860001d130100702126007241d010340d00c030080401c0510b0705102a040c040c1581483d6030b61800540100603220000e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 268205467 1250 268204217 268204229
    0x1030f0902060a111b0a03020607020d06020d060302120115030b0c070b0a0b10030c0909020d06080d0804031710060f1e02010c020c1c0308060d0618060e0d0e010818031b0106 76
    0x41e907a20291141b1101e401140e4044903841d0701d0303910301d001080c001c4680041c000c0409100148c00c90950f070b07881d4040700543c1d000b40c440186404860070301508880608034011012140030070100009140c80f4041e5a001c000e102005060074929641e040f42070300c0a440006025440e441602d440341021501e003940d44a8504e07041c400340003954800303801044240140b05015400141e81d07195689660041c1c0c00403c80b00701151500003210300010720750141682c0c1140058500e24805041e80d403007403209405240c61861078151140707000300580d20800e007941441c003030000c10701c00d1038406420b2442e015008002600041400e01030f44000a0408503406841d074441c2d43c480100c0b1000307100208103540d00c1541801c086096455060018000c0c1510203c001c08160070315085102c0e424a4241070030190740706440070f0114244d080c1c803082d20b0300c40d401d627a80f0000c0d807103e0784040d003588a20000c541100c8081000b441d84817542c070880741194889401d41443d1110884144520f140c00d100382801001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 268206717 1250 268205467 268205503
    0x604030b0a02190c0f03050318192306010b1c0504050703020a050103110409020a11030703090306271104061a03160f0813030e0405180c1e01030f0902060a11 69
    0x4103a07180742002c0c1c2c0c0d822006e4104500800080e004c04800710702e000d40b84200b4030488601109040298100e80300d84c440403a1060301c40c50000b1b54114030740c84a0001c0d4001100500b085a091a054107001e411200d00c8504031501e0241c0f034582c5608510400b4000e5004101601d4802d06500501420a01690181e41007524201420200025a406441c2034034240900980e071480d84580446000c0b541250668841c0000101a030400d60405c05020440c3c1c42102e05000d90054003030700b40c004140c05481c0070010b04606000c1e000240d10481d160400c0c0d50300410004203203489940321086a20100c035140918500081400044404070241040407a15450038003030319465030074002c2030f95001506090301504249402c034105400396905041d1410058001c02c07107844c00c035812901a880850b020021400340182d11101d60400c49003240308038070f81c0301a245105a150004600910b400000d0702045d42d41c0c2c160341c0d40180d03180390081c02c1c00c102039601d6558041040c80c2060404040b00000c0e10112 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 268207967 1250 268206717 268206737
    0x7020a170609030f04170a0c0605030a06120b0a0504020d0c0b0c1b0d0209040501110f030411010f051e04080109080a1205090606040504060f0906020418090f060b0604030b0a0219 78
    0x10701c0100441d4140d561404d206c03a4580361040703402d03161440c050700080c4a0300d01e01c080401d02e07540c01005075114040c030783c6044c410035954000f00d20404a240c0405032000305081d00151501205030007851b04280b000c0c0000c0c8c01c006061f1254800e90000c4d4201c1c5080e8030300011403421150040206070b0003d500510051043c20441c00000d50b101000c40c0e0081c040d010060005040c00b50030f40c02412148880f0038900e6030707004e01035501c1d14154821282100d2400f1005080300940d441140f5590700c18420317864151a0003644c042c05464000003030164076140104210220f4546420700600d45020711520806481d00b000000182000038051008400b5a250030108130340c03420700084a44c1c10400940340001d050307c1c1c5050140160075a00c0c41081d02500300b91a90003000b49a60050080303802c451641601d50341d09240800c2520090140600245161031800020900580c807020048000501e40762601e6560358a50740c2c805e10072076103488110f07408600b4070404e40d03180c103520400e248545020001b003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 268209217 1250 268207967 268207987
    0x30f11120a091707060504020108010e0f06011101020702030a0c1a0f16030c1e030201060819020609010207050907050723030715111c0c08190509010207020a17060903 73
    0x40c0c180140403118640d1904245000d118152601d08241c001c921060f5940390014108000649802c1c0c17000c9000451600000610700015941c1c540104a40b05000b200d6888050044601c41c04d0b14001e580155820130210740166001c01450101e280318030b13810800d0f140740040131424900e091800d4149004200b05004040e0184011154681d40c00c81d010b20440e841030808640c101c0b003858000f040034124000c020b122045000081c0075140c8658001d01003691901e8a00381c0310000350650103281c04881e02e02c03400514020002d07025904041c8120f40001d981c0707600041a882050305c0d003002280c00000c1800a10482c000c14403c644841c02d414100a401904507642d04d10610502525241c01c072985a10b0a1403541c008070819641c1c001d510761162100c0141c890045c1c1101501d0703c03150326040301450094001d04501d0303c580210390080c0300915001e802d80001e854020980d904030f5600f0420500140c0c2c401c03c0d010050552012070045010442c05842d01d0004e018162103035980c403d0100101c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 268210467 1250 268209217 268209247
    0x50303041713090e10020c0a080306190b0a11060c2205030609010b0307080c01020309010c03090909080702030c01140f070611030f0f010608040c0605090609040c030f11 74
    0x810751161001c0300000c01d01580c04401d0255140281451800100018500b1600d800540c4421408815140d200b001015420100c0c4140f00e116800d541000300040c02040c4550007540d44070784080c06040da6142858080307501400550010000014081002e04845170b01241c003d041210b10070060005080042000d400d900810040c80320041e24500c0f203100b0b41c5104c8180b40000c0c10302038200d0b1440c0c01e19020f240c1c049d001c502141402441985000183c98000080a007000b00e4103801a5160000f032000444100f10600030507030600c94000400202a0501d100d86803203940540d2141d42c0300d4215104160410b0301c800182030411200d40303040321a4200c42811103912501718a1501e81c3c400143c0782c110050254203100200000001c0204a45a00058480340c81691444d0b80102d103aa03e0b4030003904da45605440140000703002400a01009000d80000c000007000106042c2c113100030a400541030b640103405c1080001e469010300780304101c040c001c48905904120130a810800c02041e1805 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 268211717 1250 268210467 268210471
    0x70605070507050913061401050f0a0b0a08061c0f030906031e0c120908030a0b0604140904020d080c0f06060d050a06050c040f0e010f090c0c1407080a06061809050303 73
    0x40b00700b4680020400c04905c0280d0844841d501c9a01072110300e03109030b101e030300c080b00c01d21440c0c2c003a5116600c480003d240000a070380582c2c03600400b42d41441d111104c1194951001010960410380c542640d2000e4841034043c21704403803242c022500c15042500d00200b407246103620060030f050400c24287c00517140390105a00348058080c1c005600c80b0518000c035110101d14004541c1c05240801600a0280840003544105200c40c0c0900118154100f0b204007449944200040e102018100b604546449042c01d42c1082c0000c06204001c2038a440e4150103034000c83c04150254840d0006030b40c482d13824491294082d00c129181e0410480e13940b215911982d85407001031000d80c1d01c1000404e0030814100f075070050492405904a41500c038402c07118048002e0142d030744014001030380009c0c503c9a50041c84a40c60702d80e686d6a80501c000d942e41d44804c4d1407000c100369540140c0d00b02140b000b204000051100b801400040755481c58a1409a0501c0d41105000c443d58145003c0c1d0300071880c000110303a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 268212967 1250 268211717 268211719
    0x40f0c1b03021e0703050c03060c03040f022d1207080c0909070902040303020709060f120b0a1e060f080f030a120f18062f07050c0405010608010807060507050705 71
    0x14040c4640d26040381440c00a40800c0c3c0480b12003002c0780e5409070002000f2050305d104200716a0120410400c142d51140101c400090540c404c100080000c1c4071800c2c14084144044e04110f590032601d0200b084d180d2241c04011460103401842c00c045141c070004403c0da840701c50340900991401c085600c0d894042c1104981c2c06034040401054085008001441c0101036100d011522030740c80e486e0080d1a0080d510400e120345051071008070340c101c5804201c9089440203180324401140ca55078203030514034010420a400c507030340c0c2c00f03103035180803864082940d80c40a15000549a4100030850711078401c160000913050f070241841c2c000c002c6000045034245a12400e045411060502c060006002043c0c03412540710704005035150a001d58406040b40c19210744020f020000003584a00f03803040d001070842003030007100c581a40703921070464000c0c000140039405440b0304050600104060b070704207911000000325040d004000110040c0105400307440c1c1450503c0c54408203413074540d81c94a4901a007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 268214217 1250 268212967 268213007
    0x105040603090305090a0305070302031005070c0201110f0a0b090d0c3903080a030b01080613050601030f11030417030906010608191514030106050105120411060c060402040f0c 77
    0x70b0905004e80159001940000c2040f02202d8603407500d65296074440c88100c1c003a103e9525002142c20140c0200c1d0710820180d600c405619102e41c0044854943c9a912084c00c1c1c01940c3d07c500410f8002e100084000e80281100c001e075041045805203800110000341c1c080021200118000413005400514066082e0940101c200c03a480e0044c428220706201140500010010000c100034569021740b80550450710b0802c5106103034030055403c1d03601200c0d134540c0400340c0e0a0a07030038014243c1c0196040310042c03500181c1a1100802175044076444220030301603100100030401005050811032001d0800c0c098485e0841c100511403035a02c000c10b000d50028484410300080000010104595515104e80b0f02800156420700158904035a40c0c050380a0130303405502101c0b0242014012a82200c5040e0b45017031a04002049003441c020300a0310440c0c0510951141d024195541009441e01d240f03031402408183c20184108804c0798111505442d900d81011880600d0036000a0303a002d00d807c41d0014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 268215467 1250 268214217 268214231
    0xc0305190b150c0c06031306051e04060917070305070204050c0a0c0f050a0609060b010e060307120203060a05030d1d09013b090a29010b0f12040605060108060f0105040603 75
    0x550a054504d042c1c0e642000c0c0100130000001502d140420015006080410490303d4003041202c1484404552003034600300600803800007a0386a100000d080e000d801007045c044180c06070300c40e955200d81d405900041c8042001e00640c03501d0300c91180c2113a01c000c0024500b00ca081000b8048401d500e00c00b60a0001c002c039810140042032182180d034a5000000f0444804145810030040004881181c006003149000c078180e030824504a07805007080b41c9030385000c10500c44445000e50300081600390040500c1000140740e44041045410900091b11640c0c0c3c0790000303c8414980d403141d080003610840c0c043d030040084c2e0b01824032001c011809440805160450104800810503a1380900c00310311615100708801100045201451a84141002c03021060740e140d0380c05880305103242c80340c40c501414004001c80138088000780200030920340200d04105444141c1101c080c02100c00b80c400d6511a030030094250b81c400c8078264001400c0b2018540c11003501d00003403050285002d003100b4180ea4600c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 268216717 1250 268215467 268215487
    0x1090b09031c03020c12030a0e0105070503180109021f020f03071109090c1908010b0108061305070c0506070306150302191803021c0b090307051906060305010c0305190b15 75
    0x11680c0c21040c01c42114084640b500c0b00d01d100303907c210350301108240740c074101c034500720418003816009414a50b2107c1c03c58485098081d04030241321803c480c650760320701c0000e0050315012000c0c03100c002d5810140210058240c3e0190400310440349608007500200f00d80c400042c0c0b5000400729511040e0341005c616a55414140d2500315204480da5104101540d4101e505400c200c0c0f030750075100d600c4c0c000d000300030902c00150342021082c2c894542c403410f0100c0e5442103c04030741c495540524103190500b1004071a031685400c04a090794408002900d42074140a0001e40c2c3e031041c0600c652a103021481c048498100030110340d0056401000c100c0411242e00d0742d03682c6d4160b07010185030000d05811107400110001040d003108034000b1101d40c0020300001d488640040b0654803c1a04180646101000e0760510b10b0070a40b411811944240c1d20a00800890003d1146c8195049561000615810f22140101401000c03994501c841c07810b20f80422956181c100880303d003103814031080d0341c4842803c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 268217967 1250 268216717 268216721
    0x6290d020f180307120c05040b0a03140109021926030c1002040e0703020403020603010b030a090c0305010c1101021309110c0f0706030e0a020603010618051002070501090b09031c03 79
    0x24081d1040e0100d0a10021080008101c0034114203c0c11500d50b01d43d241c0b8550005115400050650001000b00b04403a04240d0000520302c01d004294050443d01c036910007400559078084580242e544d41c00c00c00460070700c03071a1002e0301e203220040c0a48041c030705806007212100710009800c41280c49820000000b0b010010f5440c80f035108070641d038600e000d48074048004d420a100350203014841e9004507208a020340300b260252900039114501d0742c0c0c2031000d0a04282d01c00b904903040940e03600c1d251404210380c015414081e604c07440001c20001c50703002000f04410507042c034130740380307644101314100c4400c800c22400c3e0112480000086601d000045a00603c2c1c003591021180750f0080c014084044000440d0b000c0c240d0309151010410302d209120714503074524402c10025005182000140a0345003d4406640010110b004030856a6107480100752040c00d100b0f840009a8071030103052109680105070f00700a400700684080c20a400640003907a22107a100d51095560002d0052001141c880c1e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 268219217 1250 268217967 268217977
    0x60a0515060912030a0c0c0506040308070209100b0d05062805010c020f0d08041703071a04150e100e060f01060507020105042103140c070501032409020702030106290d02 74
    0x12000752502c03101c080001800c99420010100ca20031f40c034400124103480c1210640b4140e0b07800461190604003503a00f440f0321800050503000294030b1000d00050581c104e03200408440f507400708040f8450500c0400d01004109404da0040035400100076141110f28280380a421201d003482d2200c0d076000c090000c101c22141c90f104481c1c0000520001c001401035041c0100120b528085ca41041c000c4160401a03c80c01403000041040c0c5e5054001c06000040003c1c180e0858001e54400303540340110403052046035146082c9030a0342d0420300052440030418489d0080c0e802d28440900218070300400d0110441c041402860709000000c1410415644583d003a2009408900f414041c4c4021812402c1c2100708513030021800210050700100f80e02c0c0715201078903150054140104030b842c1c103003001980909220070100316490400c440045e07465407200c1c00c42c001829080801660750845005141c01e4074829000154045522012182e130602c2032103840780d00140003a646e540764000812580003a00c28 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 268220467 1250 268219217 268219249
    0x180a060b0c0705010f021c08060f03030d060509010902090a030210030b03060109060e0c0a08070f0311340c0b0a0309120f020d030c022a0918060a05150609 68
    0x4042400ca000c9000010400d040e207a09884030044842c2142080740c2c0d90030480101f049800307440d500407080501a008150f0444c000802610070703089801c0110b4903503005003011003030181d15014100110305020000c0f034050134041e0810343c54054080040790283c0a18400280141c10004000401c3ca229a01c4842400d100500399101540c2d6240d400000e484a40140f014032240c243c04155400070b000b049440002032916148455595a941500c80403902d2003c4828180c0387e50010010014103801040584100e0701c4698502ca00c0c01c07040c3c0a140c0d0000c0e4100d146000034090380c000b00f09202e5502c3d08903911513031219aa041101402c80c0a018100340c0140560198001c003aa800d4200001419032002e070340c2203a06d00000200205e080d640f54181c02c0d0301581064444050850011212810700c00c00950000d800040c0c8001203101d220084601260400794404500d0706c00505200e110f8102e250300500788040d09088542c40c40309c620540140d4400c1600140b510030903154a00c4c0d000000c0c40c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 268221717 1250 268220467 268220489
    0x240702040612060e0c0f09130c170c0a080a02060d0608011d1c091811030109051803030c0a111903030b040f05040f0b0403110303070905040c030902180a06 68
    0x9503441403000d0041c00301c8800c8420f00d0a20314245079040c07000030101c00e1844001c081c002d83d8002001400070204028121080c2d60f1421110f50020034802e2440100418980e0841c406d4030519010050400b45041c100341d1040c5c4001c442040002c0c40041e440060b20340480b0310b542d44800324019100181030701e50240c00306d035003000040e061061124950041020390981540c1d00c080c0180360003c9424411141303940482d003000021700c4500d642c01e40040d5220342968000400304004660140903030401d9103c0003205894004000d1201c4407070480da035140c3d4a400095081d401d000b040008203000d01c65100b0100324084070706a980140400c04c0460a01c0503c503c0f22018a1034100240500503007012135002ea801d010040c0c80740112032152500c6a0740281000604010f940d603201381d8000060300603010001c1100c50000c0822042c8000d60241c1c0ca0707921083c075500d10709030a2009592030340602406252420740741002503101d0280e00c0c0c0760640d15072009003c0d50f0344c40590310028011600b150304028 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 268222967 1250 268221717 268221719
    0x90604080f0c09180a0803070201020d1401030309151403041e03020d0809030703090b0906120c0705072103120e0a0309030c09050103081b0a02090f0412020106052407020406 76
    0x840220701c010038080c007514503842564604a103804c80300300300711010340140d02035601d02c8003040316003000d550001514030001d403030312401c074a441c0c0a0701c51525007030040c0d1804600420070582c100d0310140040200b1346c5459850011030070050810b005080144400b000000004ac04001254070042280300d0001103100c1c017118207040c0250342e1150b16103444046182d203404030311401d0001055030001d5a00d69140700e071003400c103540c40289802121129030000014810b8580c000f903100300d041c0c07051880c1c01c0c0703103615941c80341882d80c540143c0345c0c070284900c02c2006200203c10712032460081e80e1501414410034885c0300070200d4008240c185003101e140e0113100800010940c0c0054010100c900589546207201e484888c000308942c002c0c8001403260404200c441022000c1500340c50440700c008064484840f200d80100c0c1070401c0c12610b440503203508000308800c102d482c190b00364510065100030004030b0706110114044d45100c080501140010b5a00b154148a181c011206c529502800510240e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 268224217 1250 268222967 268222993
    0x220f110d0f05010b121f021809040b15010504030f0206090316090606091d13060207060f0c0f1103041211030d0c0b0c09060301030602030a0e0f0d1107081209060408 72
    0x1c11301070503600d02c6240b0341e50212610407000101100740344000c000c40a554071b4102c061200a5001da4080b4400d41d05000190916540b0318509501c00c9010f401d01803ca0701e481816001c038010404141414000300380014000f00d241e8501d048202d40d410b54400e0343d00c0700040300180c42c2410441e560030b585141e00c41c0c0400c1442e202d800241c1160866110031240c90744916140d020100c8100e481d49503100c404001640e44c5000031003542000d030042a00610345004c40e1a10015201499940503006403075425070300c1f1182e403265140c11200b050b450400c040d61048040f040d1240700701d2040f050301c1011002c512041c8203000c00988050507000b4115800389202500160980001100998843c0f00820024648050000c00c40389200d9005020750b185170b0030b542d110002908007074003030065259100c0381c02070102030810141c40c1d42e28248000307201c0c0b5011030380001c14078014150340c100541c000b04030801041c0720000300703085011380a40c007a80c0c8030074414010403201d01a95100f1009840f48503030f90180 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 268225467 1250 268224217 268224221
    0x1a040b0703051f060f020d08090d0804020a0f0b04180b0904170c0a0f1416050105130e100306050136110f0309010510050f0f0a0b0f03220f110d0f0501 66
    0x1130802503000d0355015100480144d0302d902c2c040750301060b9070304150940d1101601c564bc120b40d0062000f09011201510b503614110342010a03007080804080c000340070f00c858001c8580003000140b0194040c001c40d00308601041c0d0707a1002400084c800c11883c142444001c006070141c0b1520b1021078101c0d46001e0745400c10a800d503440c11303425100021140403012162001048d0744403408510b40c00c680c21680360200445541d030100144030101820a08045591a4400706041c003a00c041d002078a07441d401c5061220880d401030380400307a20540d955174031070381e84146440981580410003c3e650801042c008010103040711407181e4400c60381c00038049940b4120600614000d00041000304410360b2840d0100030b030350301d46000c0c00307500c80c1641528008134500700200702c0c02040090080302c000c07070f5140da60f8001e41c0c106600311401c41c1ea003c820002e40c00e029000134220004203074591780e0111601d45600f12070b030341e03141005040d505841c0d417566584d0315242c0c040003005c0d07401662040c0041040c01d0042c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 268226717 1250 268225467 268225487
    0xb0310090c0b0d0b13020415081312020607030b0301021305040e100203011508070e130207230304080105090303060a170c03060c0a1b0201050417010b04060308071a040b0703051f06 79
    0x2c425070b10b00d5541401144240701f0f9505698081000e0740303903041c0740785090700c8181005000750b2030302100250240004104109292081881b0740051078039042190f00542551586010f0b01d0007a88103001000d408a2403072400030840744203581c002458801002814202810000f0130203039240004000a005d980e00e40c508040c40301c1e41c1d42d42d60030949400c4012070344404501c407200d5000045580c03042050b0f82035402401418400c0980100404410f030002a102410303240c3d00c2c205400c0441c0401403c1c400307004041d400301001014500d1031400d20700141c41c0810a01403012030b040c1460342c850040c1d00402c89201000d5004044409a02d04480542c5159100481c000009486c042e82129091002e41d5034540c030310b034140c40d0742c2d0500e41800051181c0ca99500c40100b599900e8808100703180c0c90707600c140e4000d14042c0f0701ea41d03135036401400c21200c00074543e0300c4103800001600412010480311036003550040c07500d150100b02500c0e2403100003400b038001d16020084503030858000890b95000000e100c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 268227967 1250 268226717 268226719
    0x2a03011a09090a030c120c05070326030603060c1b150123010c0b100308030c0415050307050a03090f06050f01090b0f180c0403050f03040602100b0310090c0b0d0b 71
    0xe110380c0e69015449848454010004010400300900c05c0000341e84402e0b00e5040349182d2078031240820385510345c5071422500354001c0e2014004800c0301c103401c03d590000741000f1210f0040c90345c074505021010994610300100700a86c201004036181d20005406401c140c800d140c884219000d203490024114007a05080c807034080060a00c0000021200c103507040700400000585030030340c55102540721600c00b0180108540007000030f1010100000704500b01075405203a0b089121501d0314207080c0d10100d0114254082000d210341070081102440c2d0001c06c44039400100d15001c50488183d2038249640d01c0b18100080810303003081c04003c1d02c0700c0002013150481e0031540c820b000a10311501030041d06d16220101035007000c204818401e22026031a030143d00400c4180c0c1d15442c1075070700e0712075500300300e202c8011040039040002c0070410142d04118881d143c0390401c100708507451012001a23a2441c00040d1101d00c2c9403918411810f100740b1700040d200509101c20306c03a5560051052010042c00028146 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 268229217 1250 268227967 268227979
    0xc0c0a050a060516020303090a06081806040b2a0c03091e0a051507140708060610080708060a0b0f0c0111070b06090c0705030a0306170d022a03011a 65
    0x251858290554400c40b1001d450307942c542a070a0131100d200d09000304060b40c2510082041740c070030b82c0700c007401c5070700520040d564410281401c1180c0d1b0107014800094035180c0c1c1c407130002e22002c038540d070f0141034001c800701c0c0c0d03603040342c510614240c2400c1d803180d40d0010348140c0204980e00f502002000402d00c59000703c4500e03550380301105860325203081604446800c82442b00080c021418002c4045c0e0300344050000083c200803403603640498907444c1c842d01940d01c1d00081000c01c0450010480c203a003104080f100d40042c45900c0000400ca0b03100200f0400030032040c2c0e8007107402d03a1a041c0442d0064004642083e0b030342c04200d990310489901100f03036540d142d803900030340f19011020740302a105915888108020b13591500f00070405002c0c1c02914801d42e41804004a5000440402c002e0040700da468070049139a61400d550901208039203c841d030b1a541200c104514000c0c1d000c0740d050720139041c0342d081d190643d006454076841c103c8510803241e0150f18214005404480d141f0844010740012aa4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 268230467 1250 268229217 268229219
    0x1101020f07080d030c120203011202240711011106040605011503020310090c021213091b09060f0509040e010b030c060a090b070321060626061908030c0c0a 68
    0x10381c1d59a4244a001d000390010110700c80100c1c400d07003203000c1c00112440e001084038010001801264401e07440500365504200c244821070509040000c0c041c24a10401190180310030303c254034a01c80c140006050034140b54102040343c2c0640c9001d0f01303c16100e400c9514601c2d1901e03042004050a002e4480d2408813a888240120720a0080b64070610b10040c4c0c85800c40d00d0401c0360005820300103101d40545c003450701392000404d1400090410300000503911b02c201440d2041701e40848442d000c1c0581a020043c040c68040b6800404a008841042c9807604558800c840120f819024900d0116400790070080c200341d00c10015048074130b0314042142074132001c0c5428010800342d407080f01c4242c00407480b4240204482407541000d450041d001c0d0400000d003c40f500009048001c000c07031150242c0d561900705102140c0d12800001100c0c0c40048180c0030b002d00d82000c44400300c0c0041c002840780d48592440800d0040300c00c02e1500800900b0100d0b900d40403107240f00354a4a402041e25400741c6007000c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 268231717 1250 268230467 268230493
    0x20d030515060f0307021c030c03060b09010e0d060b03010f270c18060902070f0b0c0306060d0207060e03070b0f10030b011e0b0a0507060b03030f0412030c050a110102 73
    0x1496110100000c107410314200000c1c40010380c0707070401455032046d4041c0c002d600d529681c1000c42084c1d81d400039a0700180140c203040e405002c442442d0000c41c0703c0c08061104400c2641c008456050410084411385880f451a1501101900158611580550074076440c5103418201e0340020f001c0c901001145104544102280d00b820040c5200141200d03040d01400c0000805440d0b04005d591060800440c0d42500d81401906991000000700ca1465440c100310060140070100980c02034a4801803618509003140041c0c044d01410300c1c000b00065002070040c082181070307400032800320240c0c0d0130b40c2c1e00d5005038182000b000004440384c64480442000141d8042e00745450311090340d40c0704035415a82d034280b494010a80b00e030206e201442d590342c040003203007040148002d00708894040e40e5007941d03800381d0303c0c000701179456128415000c0c0d4414041020349030000400c0c0e070b080d640c00c049040c5005600e0304080f910704110000142072070086421a0042c070140007001c6600600a80884d108110008 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 268232967 1250 268231717 268231741
    0xf020a06030b0a05090f1303020109080a0507111e010e031e06070f020c060d0902030a021815010219080a170c071406040f02090c0c030313120804081c1b020d0305 71
    0x30303014640200c00c200010842c81907c3c440b01010341c024400007030010000d94944045902551004020507000700702c42c0708200085000b00e103207400586131205040480c1d00840b0700c6141c12070758036050120b0a0701070303511514100104089046400710510030041141e00c02600c1e00c0042d41c050000503210b0401c00c00c400d000041a039200b4401404032441c101c56000307014020900c201040780c0c1809081074140c0540d8400a80030700c040d003042c16050441c2480c5180f080301200e403284090554001d038106614aa810750004030314990444507a5944000504084400d2003505200d0002c1e00700704c40034410400904800f07804440d03c40c00303021041c203150740d8400b6944d0f40100da00030000c040d080c441c000142055520300c0d0704080300381071141c2043d242440d51411030700304486601c2d0101403145600184004502180c201002070300789184a030520341c179000700c98468000c0b0802d0707d001c10a00c1c001c800c2c3d190741c404032240c420706001283c64005100000e440f411a002c41e100042c1c10310000c40d06a6003a4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 268234217 1250 268232967 268232971
    0x117010b01181a07140c0901060e0d080c0316110102011109060d09030e1806030d0c03080c0f04090507180b0405060901080c0412050a0611030105010c0f0f020a06030b0a0509 76
    0x101c01206210340c9000d22001d500f20440003040c007101c4041c400940041c0b005000040310788420030181c040c14886209200c400001680071404001c0311450043c40d0351610740c0740c074a0340c9800c5006960360b0011100341e9403075032140d41403003000c054000e00010148041d90040c1500da000990090024030742c7c00d2150211805040900e41d07002d04204844200d4810340e034071400c4000d11900b0080f155075094000185490410002040c10b80c0700305040004c04c0c0350a2115100c060160709000103403030b07002e440007001701c0002010710f21203200c005002e070005041c03001620300402800c94144014170303040e10010311942c41c0610440044050327010100f03104d0300c482c06a03015a000601000d0030714446400440e00036070050840c54000004001c0400d54010a00d01703180140e00a000a1180642d64a054412240703491181d852000301030005002aa0f4032035224100543c005044c44020f000ba07007451003084000482c02503001d2340c26000040c100c1d4154104c0641d80c0800c072021040569200280001c2c2001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 268235467 1250 268234217 268234247
    0x3060b040c120513080c010f0f0c090e041e030509030d020c13020904110d0219030603020306010b03250809010606080603030304030c050a0c080115050f090402100201020c0102030117010b01 83
    0x240040901a0107060f4085030f40318481c50303406138a040240d280d0501c190720400000020343d441d174000c03002000990180500000002e0301c20042d0b040304510040204907240200100c0000b09000700e024051511741c4007103043c0b0104031346000045a8507000c1c219902c40c024950181c050800203154240c001704050041c448050003801c08500d4000e03010000b9440f4040140e482a0f950044400030344541d00940400d1078441c2d00180d070356410440114a90012011100815081c0700c014001a2000710b0b20b5411516159003813608ca80300d1401036883c1000d641441040004500742d500300c1d00740d1049080740180c2c40d180c02003000c02d48030301e021103620004a030745a0b0164420000f203000030340304000c0704c89a5070090046c1e40e004101c3eaa40c0e210509100d52003445960b464910000701750040c1c0980c00c0041c0400c450042c168414070020400e050001040a0305c00c1c1c1d245021010000e000790111001080040c000b156a5038507010070f00c42030500f80014840543c81d0082d050346550154400b0542d20b46 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 268236717 1250 268235467 268235477
    0x90608041110270515120a020f070c0e010608061c020103020915070302010c0912050c0907020c0a03030503010509101d060f1207090f150306020f0706060b07210c0b04020301060f08060103060b040c 86
    0x74940201f070010703500c96094100041010403541c00030803901600701c400390034100c020b210a94585440100b035100c01a1625116501c000044410310041c200c0d88040c156081c00c0168891515500203002c100111149140180c03001440c5c508056043d4090030082025403640107180d40c40d8500c0d40c18402080a004107954845040c000061a155403550781c050200e204072419404a500801e140c40c130668400c9001c21000710040c481c500e44154500c1d40514280250300d031407490020b00080030990924500c0008403542c0120705e0742c2e02c60008610447c42e0142c003000840ca4084006a0781d03140d284203900c02e49280614120b44c03601c05010f05800341d1810501c0004c2c090660b1140c03402503201c6650055111010017950000074454010400200300c0d100d49a503c4800c1420980301c000c1000300c882e850414040307840e10300300f038102d1082030704190410300c061030a643e44e1020074018840b83c1c018a2800e180c40c100000c41c0140042c1990580307102d26000d11440d40f2020620050321030301020000450 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 268237967 1250 268236717 268236721
    0xb030705071103070f0e0106030506010203072001031b020c030c0303070f080d0609111c14011a0702060c01090510050412030e01140a0c09060804111027051512 70
    0x10b00031050200c00075002003e80d813a250b5503100a40c8907003140d078040f9510a908400400580d034140c802d9941c040d1080c0040d41c501009a44d50410840491701080030b04540c00c1c0300e004441c0d1203030f8800d000b00c0818030190300b4011112500a580d074846040420720a00c41da0480740480e043c048150799806601c4103051454150b40e40d2b640c1d007250070004081e441d10390385200c0000c401c1a00c1c05080f8014012a1680d0f0f99a40c0b4802c101d0410000002c50340715143c00c0070154010800403441e0031341101d500ba4041c0e44100207012040450348150000a0340c0000003040100d40c440d410b51101c803581e0320410807655102484800701c001c0c0c560486000d000011801d0040301503e0080d0000c220b03443c02c203000002d05100aa80c020f1451505980f0502e40076900c0c4610807841d82c0180c00b1001a0409003020a02442d003a6540380ba40b225164845010310032176101d81d5107030740c01104004c0502c10003240e060070300040110352445030201e40c801c1a2203090500392801240c0c8025041b68074800c3c410119102c41c4d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 268239217 1250 268237967 268237973
    0xe210304091d070e0609063a051c181a07022b0203071d240901090b0315040b1f050a0f1502010c020d0806060f0c0a0c0b03070507 57
    0x6042c2c0c0090100218000320403003000000600103070024192502168402d030801800b400790604c40200b005008000320b42000e2403000140e030083c510502069130310054581030b15600902000035880091042c8141c5c954100d00d0402a005c146840140740c2d92030f002c4010b10022040c840c0101e12803450001d207411509212082ca403c0108451400503201201c1602002c1845902205188100403807030040d1840100310b1600340704180080c04101001401301540030108a031101740070b0008030740c9000000320003450b45101c8402c542c0a908c010410344641d07a503515410058449100d00750701c170340620440700900004070340549000b5900700079040c0c001d9841e011400640884009118107030380404d03500051030342c3e4607410b4030050701c0b21014400c207a926010341040140181e805840540e4100404682c03040e0380010720702ca015000d49024100d640703030f4a000c6207083c4a40c981a0b11140302c005041c02d5442c80c00244c240060348688408034482d61760f080c088909020a4400c603001400401000001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 268240467 1250 268239217 268239221
    0x14031f0f1407121506090605071403041701240501080a09061a010e241c050103030309050c030c13020c030d020c0604031805060304060e0a0f030e21030409 68
    0x19400d000030000881c0d0002a00c00041c04800b00d0300c0b00c00045821500b01c40483d454050b07445141d290602c9809503d0030002c024101c1c0c4c116014800810030040b6414051140c0100f00e00c000700c0301c003810f4981da40e03240c3e5286004454102101e44c510341c2044c0a400c100f020081408030103149a4003408000d9041000445c0c41c201d015241007406a00ea50010010861504c5051210080c141e110406904200b00140900003240d15061003080004220412241c07200140c105203c00c102210b079035465480d140c140021131550408030340600e03100005c4100b542640c1708010b4240a6030844d42c0314503041081541d034500140445070010007958403100f4401d1a03401800040d0805c00649080c08032109032102260002c0d820450300b98401d00500c0285030b0860204440701310341010f220402c6040c100810218840030380014403181d9a418005042c1e10240031000034964084c3c0d54524482f0182002042000c1580040e03124102c40c2184500d00000b0b101c420344071010000256081174640600310700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 268241717 1250 268240467 268240481
    0x1b02030307051c0e09041e02010504090c08190203060d14010209191406040b07020108060f09040302010c030605010315150e0a03050f060606030903090904020310060f14031f 76
    0x6014841803100d0000200280f00840d991080000f110000340c010100003400c1d000b0701c098160180104109000205900e420440098200b511945814000c1c0780b0040300c0310b00c502c2d4000400c01e0f1800011202071644000518014103403458254800030740102600100d20007903130b030207600540192a01c00090742070544003154003542400141880c1c415008181c0303001c1c05249840180036144010300280000740b01703004168105a45490a10742000c442140c28413a061001e418040800b00050095888246070340d90035601034200b0000b0300346403030080d02914944801c10042404d0850100340c6511030f1107030700b60300c07506805d01c0003d840c039103040e00d03148004240c903840c204241c1174079240b42510b8400c00b43c3d0007144908028030010140c03100440c203200303024104604c945010810b10480e0f0b14008142e0319029001c5402c0001c5d40c4a500c00245403105a0f100307056140d09000700012922040d01034901118400c00500c030b056540c5100305500c80d03140c0d00203402418a84405580049100e0340400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 268242967 1250 268241717 268241719
    0xc0306110a17071e0225030309090f180602030a0b04150e180604050706110604020604150207090e0a0512030403050f1e041710050907050d03020c060313170a1b02 71
    0x303070020800c2800308120130b207800c0907000960310808803443c4030040d11040f9118903a820002d090240c0c10350f0382c014680640d51081c0b4100c10344400c4911806600c1d54009800054640c051281152036450158060340007150b800c885207150104500701e40c1080d0040180a40720114003a141c14200310f419001100c01400c80300c0c42c0c0c041c0c4a1403100301d6804200303403030055010300004c05246141640c018124040e50000c0a2241c00507024400162120b4003582c00359107451070329401c00c2e02c030500200d03d00707074255102c480b6082c01d14000141d060070100315600c505004074251038010400c0c00e03101a6901c010b440003000030300308115140d005000d00001d4080801a00610729000000304102103158000d60004505c002084100c1c000545080007080d00c0b5032900325050200b442c0041d040c5455500030302c5114000e4110f0000007040510921031202d5154000f8021620380c1042e500c80c400d000f000180c1200c070346140c072980020703040704e080660f084003030a03640c1c0d9402e601c1000240d1400303000105c012 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 268244217 1250 268242967 268242977
    0x30f061801020705120418021603030f1506091502060405060f06120312010f0e060d150b06070606090e060c040303031503020907020c0112060311040203061801030c0306110a1707 78
    0x81c0014400d00a054086a410840e11b45541c01d1102100e0b00e1641c005101d45520b104001503071258618602c039101d425018100010038000c17114400001d021240708001d2011840080469401c0c0c10070540c4080e43d10240a00e811034140031002d036038070300082c0c0700904940d0003c0006021240b40d000603690007a0003402140230104041422840c46d04054131480c095000c4100500c02075040b880400d00614010000b030201b820200040741a607090f41c0c01c041e10310b04045504a00c800074640000e60788800c080d01c00c0baa06c54103402d0110080505001d00440f4a091045a1958040010b807560088500042451406256a40980050000e1802d00304000944400040503a44250f1128880c240700c1d0040d010340b903081400141140020200144000c0c41c201050021980d40340481b041c007a0151001a907944400b0000388005603800d0408080034003010000c420401c4c2c0e04240c2003268443c1c2c07801d0000c00f817601c0796800d150180c45030300800600200b49503008010705003031a503080409401c0c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 268245467 1250 268244217 268244227
    0x4020706060e040f0201081b090411090d1505010501030501181a1c0303060b04060c0b09190302030a02060703051504020901110601141f08071d09040303050601030b030f06180102 78
    0x1004a090200e40136241808080c42160555070070158803544590880d060328800400d0060195640c010b00c1e030100d004554804415050403001011684545c01c0101860181d100d01e150090b0082d0198540d1004039060400010b110f500034000c150507218017400c410501206405100010f100b44050421031040100d03446900d0349810034403802c40e00c01100b00f07108982d200d00b005000c4e65515406140340e404104070420186500510180d072071a0301441424807901c1d6444860300c0d1000030b5410018410b09201c440c0e040680000c0200121101070b02a180282c1e41c10300f0503411210100c03855442485962240321140c6443d034000d12400105040103403502000104280ca0303c0000d8004004410103001803081c1031511903a54003014003402686800d5138506c01000b04054005403551050000503100c144400c00002000701d00d00c000600700012519242c10014054503003595043e01291902c02076010390704000c980243c410781c6007402400c5a895440c3d03c00c88060001041041035542802 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 268246717 1250 268245467 268245479
    0x50709030822060305150a0b0d020c1501080610090902010203070311030d0914120c150606040b070b0f13051c09050a0b070b07050a0206010e06180f0702121201050402070606 76
    0x1801c00c02905996800003140d2038064901c1b0550390024504900c1120810070412202c51004102d403031501c0d142c840561908004502c503482d05496450340d1940402740c40000c1007800d0009034251160b544000c1400709242d0f103c0f600c8084a00d50710b001790040c3c0040282801090040399420102c524901c1100d00d043c0c5c0c000045011513209502c00c5500c8546801c04400080040049080d54043c20342d0442c80d0000c18241155a005d0858000ba88964160005000c50341c03024195801442450b0503507648466510344030866810844911202c0a0004c0c0482c82c409400c1d8100c0c050241d11070002c007150001e181c800d01e908416100c0c010200612000049103075207803240440011710407000348607101d0299150130780260344010300348000c0050904c0161604c03580025a2411149019480c0d2a161035400c0410842c03601400b007100b0121340d40092040094070524100d2080b51141d00b500e00701c100e608002107051040f2003e425000001c10018005454158020700702903100740f1000840701e42c0c801c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 268247967 1250 268246717 268246777
    0xb090f0109082a060a030e242712040305010c05030403050a0e0a080f030c011a180a0b0405070206090c090705090906061908041704062f0715030e010507090308 70
    0x3c40042c0001d440b10038503080400300700400480541d1500600c0300e0306241c02d0303c04030012801059460680100580c03200048505009c1c000401101000c0d01c400400c91991189642c1c410b100c02c4500750710704051040c800b442801900d010380d9041e81c8492411403034904c1100c010540230980c40c2c0c064080e1a00003602e103001c1000c206154040d9002e1511059000519821075003082e540048605400101440035611080c943c04160101c03994520980c540c281c1d940c0040030748404042d0498541010720400940000e90700b07105800040c1140c0f0760051400510610000964070580030a03803d0006284c14604840d1b09640100003034003a50a200d0210521a0109048841d0702c000c564440b09000600640c84000421407107900349403490f15281420091040c00c0800c0c400c00350700c86030020401528540040406085a03900444485d035848043d05103030112601c0364640801e107070013907010040c4018000d0502c0382c04651109007540f0f2131611010026404035a01c0462107aa5412002500c1400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 268249217 1250 268247967 268247977
    0x1e0303040906031b0305030a08040303111314010c0201020606210318010f09050319061b080a0e0c0306150303041a030402420705070b090f0109082a06 66
    0x1c03440800c0c154998144859a0003602d4aa0b0440c0d0601910600129000104440074a025450140400e0381c403030500b20000c0c880344290fa0150754000034413006042075800103070150f50b20001c011044201c0c2d80c00541c1c080e402c0ea10000d0250b04108001001841c009640289070301d0203c90540070111520000ca0543c0d001c039203104040528040a0100d6592201d85070b9600e001e1400c101c01d42e2800c2000003a5580c1401100c20011501220007004100c03158100e000404e82906031101108480800035004503421035024464a260044c012603029000958120708913014020302890746503202848030782c00118001a80601c03081100248000400780c01805040c0801c480c292a400c040c41080705040c00303c5464207038410040e08910f5826105190b0041301c20422002e2903040c400c1c401e40440354017401c84041c241e40200c1c1000140c154017074008020100c400c45401401403610b20054580050740c0c000c14286500c19981d03100100b4003140e0021309010520018501c100c03101d0002209a801 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 268250467 1250 268249217 268249229
    0x20a0e0301110304032a15060b18130b0f061b06010303030903080a06060509130e0703060207020a0f0b120702010921080f06011b0f0f140606030102090d021e030304 72
    0x20401c001e05030b10039884215041400d0b001c0d00c0c052200802251000d03902c007800f1f070180c5210901c40050104951041000f482c060012a03140d68001060b044164440c0c0b00c9107000f4400841104c124a540d1700c80c004c0c0002005090300302c1c1020410502c5130a42002980c2107800c1030644003050f2403c020015180218400d54010a00d0002e80ca001008658081d1a4044840c10305605201d51500541640e0040b42c0a0303403506002c801c1e0050810113070028204d039030350794001c0100200c02e004503a00244400c60080d0380c3c4246030f07070750344400c003050306400e01c42c000007014180a00c41c0c400f0707106c24046410055a00c004521000d59844281180d1000c42c0030800011000950003121074101e001103911022928441e2560725040c030010b0100c1c0f40301d00c0d8a00d5600900c00d0028200300b0352a1401c0641c0e034000c40684514082c07481d100000850b41c02c182c142c0c3d0711458001501904e414000c030785020b400035080d83d20800b8190309000c0d00e507007007122405080000300a54219901d040020300002c184e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 268251717 1250 268250467 268250501
    0x16080f04170d0e1507060b0d0b07020c0f060a02031c061a030405010c0f0f0f02010608190c0e041e02040b10051b151602030f04090906111c020a0e0301 66
    0x1140b00000340842c0780038010140942e0410714502070303180701c4406441c036190300403001054a24000c00010110400c805004140705c050302c09001004d0342c0010f400924117000d03079800d14000a910100100790242010040040c0d10402040507621054911800d80314036800c404130b842902e03400030b036484c030182a121180c0b000e0040104001d0000c00d016a501603026818004c491080080b001031020749007a5803c0705000005609055a61003540010300429528003955804a000f61520000440c1494283c6159441f0000881c05a0a8024182c01660301c042e94480f40c142c070000c0c075285682180f03000c1c2da105550350380c3c11030303507849244a141c0c106506649159440030004010050000c01c9002810340ba030000403440b904000c40c031800c5400c420700036035641403a42c02ca2412481c500c241c0b08000360794100071500080b0740c0c085e9000301b440d8134841c0100740981070001703603450a0360281c203039800249210b00c911480c00d0754240c1d00a0011071a103240c020b64112040c00802c1c2520350b40c58200550300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 268252967 1250 268251717 268251733
    0xa2a08010f06090504170f1b010c0f0206150904140609060a1a010e1507021c1217060d05120a1e03020301030f1209150c0302060c16080f0417 62
    0x20582c81150b0150080c03020400c0715041548600171000c0d46120100780c00c0c01c00041821000900006560380b140758104007100001c56860098007801c0b1100010001c5000d13400b058135401d00114a00344074100d15a000d00e41e01003d14100302203034102410980d070b500396810044444400c00e10917640700740b00c1d07100100080d08142d0502c6c021035a15030440380d1650001e00c0d0542c0c6a0384e1007440341e00b030602c044034507407500a46103603c0d81051261050003580f02c1c8440004407220b481103d000c5841074007500d20040302101c1d104040d107000707910394218012032400b2800203c15240020f201580180200100d85885440300184c0e90319910100014000c15100310300c1e0480d10800c40025600c60b007a42c6801c0d801d5515540e201c01d02900c0d00c2000074140a01d4034111444544200200d60090200b021004100010148083c0030f06900440903001030081100142e990801a011240f00c903030280c08440700c03030000f81c80d1248503400005841070307000000c000020740a03c10750181c8903c5c0361400041d000781 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 268254217 1250 268252967 268252991
    0x9160c0809150a020c010203190c020609100f081e040b090a0629040903170a1401091a0301050705041505130f0509010608011a0c0307060e0705010f08090a2a0801 71
    0x17601142817030440d80104801d240d03000d048441031115a01908000600301c4403440040c01d94003440156030381004490a104801c02d07071200900e07030322288940315160b0740c5d00c0b02c1c07010010f28500008490890460f030b40202c1c00196a198490303601c00c84000948555041e540e0b2072b036081e103c4001d0504012450340d2a4800c00039100308607640c00042c200c5007040103480c00e54020700030090703500300342c44c812a450380020500141078009880c40c04070005108038968403030002d54000d00600c241e80130000d100050080c418201403296a00642c2c46840b01c42c1494a803a4401b00c520540740006001c1180074040700d200b5007100c203854005400e05640f880a0f040c180000d100311000141c2c0403604001c14500100544100c0c03100c0b214014030030400059803507841030081440c61280c904010440341c60690384154850003c00c1e030000351142640c483c6102c10720024121001078054030400c2c2107030896041c0d080000c00d5900010200d0881203c00009241401c24064060310030340d2050805d81d444401c0c2c0048 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 268255467 1250 268254217 268254223
    0x6120a0b1f05040203150d150203090102040e0c03060904080306030102130e0f071b020402071106070b09070503010c0215040302070f0f0305010c1e0f200a05070509160c0809150a02 79
    0x1415043e80c0440c218030b01050100702c0d0440391081140a1280140280d061000c5424404610804070005540d28280550024001d62040c420301a13001c01c805d022410301e1404200300c07070141c0e0000308440d140b500c840e2034002041d80302401a40d415942085003501016210442e04005c207000001106035240650b2a1402010b0042a010400190004680d21100d0300c0c925240c40c26015900181c481101d46002c0c4040d4800b00c050983c0040046070400030804820042d0f4455500d07001554800c079a02e0301807600761004e600b070f00c0000d40c116019400d1503c09020800b0f41c898020310488101ca45d40c0c1e000420180055089415803d0030410284244a800d0080890345a010300c0c010200340720707084031051700038545c07440d150400c4142d0309078481c158400c1d51031541c20200d1107500f5800e01c0071a0b000540e9284900303004c40c0d041c000c0c040f0021302c510700103d0305440703080c0110140078070316400c110880d07140036a448100ca100c00c0900110310f2a8a420419215007414004642c0d034941d4030038001fa203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 268256717 1250 268255467 268255469
    0x617031207022b03200a020f06070c0605061c030203030406141b0a0320070611040b09060a0323010504051003030f0e01090b0c150c030f06120a0b1f 65
    0x1066601c1180e94800814560341c03541c070390b1040440702c82c0124814001c01c8000d01a00e1800c12004d1782214180c0290140c0302c0024218990a0b408682002d410070703004c036444110840e11200030032135901100c0049003464020381e911007001401c480107540c00081562025510510580c0164030100c104010010a48140c14030743d82143c400306c0151078048a109103409008000c040807030400f00e6000c08140c003030341051102c0311200c6003450a04801c40404440383e0000502900c00030708000c440740b008a0140202d60542c4e020702802481c11182c03609200c0c89622201e00d40c0c082681e1020300740c4100f00d400c042c141103000403001c4400954541820441503840180035030b845d0049142c0100002a000300600d01c0300041400c0102a4141c50001a030f81107100394400c003448140014800d80340303500441c01a80c0018840c0920f82603840742e101109403804101c2d01c003a202c0303041d040811400d240801c190303083d0981c000200e5580b041c0310354900c45821402d885281c01802c05d10310118110070482c400780 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 268257967 1250 268256717 268256731
    0x5040c0b070c031707051209040c05120601030b0d050105190b010f0c140c090903250c0306050604180c030b090f0a0609080f04081b01050a05031906170312 68
    0x2420400c50740c48410040009100091113425282c07041c3c1101400d05050711a1584c02c0802c1c0c48092001503100105984580e54461169291111500103030b070148043c0c6503880c5000100010036540d0307800541c001c10f50412890b600008481072000018400d00a583c42803c84130201c0081607151a10b8034181c8444a03026410f200b07802d12120640c0358816504000740d500111440e880e150001c0760a400e10040903160760300202c090081081c460341c00001030030700a0000d40003c4840d000380c481458841b11183c8000d0030390500910410218115800a5400c07400084c00050080918040000303881040c0504840b10b034040c2000700306100703586904651040d1b80e080501500324000c0e00483c2c59031250400200b02c5130f80e0383c4594060120480a441034028000002c41e51107486441c0c0c550741e40c46000c8196101c03108117040030159482802034800d202410307240c0074107644461110030a40422404a655507030743e514000a11007400040c82904400210080c65580540024900060000a003e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 268259217 1250 268257967 268257989
    0x207050402090102030d1e1802090a0603080301030f05010f060602150105061e13051809010b010c0c0b0a020c040c0c0c1202030309060703030e03030f010501022b1412040605040c 78
    0x216103244d03001300450788401c0d200100055420410355260110102c120342c00c02c4000d01e000c0d0b5640103007030180340503468240200e41a4407a540c90305540e00a5440324000240558000e100400c0007a00c42519101b0f0148150000304000c40c09448030300031501d840d0f1000005922290740f9041010b00410054054001a540d040c0380640740142c85103a020710705a0140b28840c0050050004001c840401e0302800c0000c110721844208551119600302c0c0c10340d8a90641e518260018150b50b0060340c4040c85264010003034800da03490011030076540d410010481c015402460070000883d41c0720311500d20b8043c2c0300d40b96510070b05840d04244190f0503458001c405c40c9808818841c01594001041c1c1e07106500c2144c070310b6600c504900e4214003519410315a0035a82c8800b00034840c105114a1029050b50b2003070382214445203003019210b1424a0014517007001c04c1c408079142103400d208101d045c0100640c6407115291100320910808800c2007282d080e41e0f0f059aa006010803c04a80c40c1c003c0206805440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 268260467 1250 268259217 268259227
    0x20040c03060b03070f020703080d140c03010608060609120d021c090f03060507090314010501051002060f0615160b01080106080a2a081b011218021212190207050402 72
    0x1c1000b81d44809001d107014442000f0100300924800c201c010080c5501c03c9005440d007403400da00c64080c0c1002e0860300021010800001c4100f0780e50010f59049660075580c404081e01e0715001d1003ca503100c0d17462981c02503207440403000100003c014041200c0081d6008002810300398809240050180000000308600517408208050407001c4c00c03400e07243c00000008981c0c43d02e41c0180c030b94040e507910003015400280451018030307030103505c064100e50094502040100102504030385441d000c0310161240c102440105210b801c01014640520000104c4a440c1c403080100c0c03030b44000c4a001003140c2507400030f001405215028052080245204002030007500000e41c1c45041402c0702680190b0500d02c4034004c1d030b4600d90190501d40003000e002042e203200f040b00302410b1001e18144100103020603920384100f00f060400d07101d0500d40038091112241c10b201c4070343c00c1080750100914082154801d07036842e44460112000245500301d03030754402c80700b0356114500c003130f040c0f0b102503004d0761089105000f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 268261717 1250 268260467 268260479
    0x11041508060105040507020c10020309030c0904030c0b07020f011a1219032f010b010e120d080402060d0213031205040f091d06150906090103020d030507060920040c0306 74
    0x24805042d42e00c01c484c04207056590400c01c0b8909010030080e25413100e894140144595000310040a144c035040c1c0a540c14500300e04240050500143e500400160001860501107030380e061015401c07a41e82e04c150358a4076803003c46a0b0a54035440010040701d90844050241c40c94a007541d903802c5075840b0064140084c1d61230011001c140ca02030081c1c1441071214180f00300e01818175901c040342954a54184c00c8144040c0300d0740c020701c0960803090200f59001c1c1e450349a0703d40000380d2101300390078030020200a2410081181d422101600c103d0704000c1c00c0c0500245109a0b00151112000103407801402600c0d5081c441e4540785901400e40610204010074082c0c9071010741010180e40c10408003150010380010349101c141c1440c5d000703c1c428000c0030148641107010410a200c001011203142105445071010007240c94000e02c0f00135807000000c51030340300013809400540a02d81c0160700c002844001510703010203101d010a101841c82084081d05032080c42d05200d020320011461500308a1241855 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 268262967 1250 268261717 268261723
    0xf14040905060c0c0a170408010c0c0c090f1e02130b0309100c020312010f09060902040506071115070302010606080c07030212090d06020d0b0a080a030e060d0e03030411041508 77
    0xc1d00350100b481001a1184032104104080c8840c1680429071600322541440741c10103580123400b417942c0c69400c10140c1c000e01c5110320a0840300e20b400c991860096480c2c081daa03801002d91240c04076000340c89108030100155100c4600f14000480013000d681c40000d1610402401c0352038000c0c0100401c107009010080000048c00c0420300d0701750b1000203980e01201800d82c950b0003119440e22890070144000b00d01514580400e40407654400c50501c610b03501d51840300d0580c0074070300a0640065090109001290340208000c406030409841640c182015074000700c101ea010784016000350b912070f0001c00a9650066102d6400b00d04004840d05003409650000d441e0780e48020011312100b03011840041980d16070006021196011404641c1c0312904181d203c00f520100d140ca5125105224000501ca03d000ca00c01c01e4003035140e540c1c1c1040c8100502004000d0700042007002803a41c2d90a05d0f2403501000700000c502843c02511102c100c48440030411007551894425800024090b04081190306000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 268264217 1250 268262967 268262971
    0x20a031403040305121503060624160804090c1403060607030809011b02011b0203130b0a1202160606080d1b0f0b041b0b03130311011103010f1404090506 67
    0x300303036041e980c0d44a070308007100c0313038010700c00a2503200320a0070a00c41074007410b0800c0d0007034140a40940301982da07450200440c044e010325404089111038510094105003100c0100702c1c1e0303041000d2120720240961110100e607006900401c10301561403d84288040e04445500f04818465071a01d2551a0500105145015109004060011000102c0d01d0070342e0a42043c0b00c0000c807502c0e0411180280301009000e01f2440e4400003160315105007070070314a4408011078002184000c4a40d80e120300c1c0c00b000d03041c20303804090001d007000448104036101d414a40018600c0003079140c41d4080354211800c0220840300aa40809035503403102800107016600400d210100c0131501c606010078154609200680f00c050309001000d8036049000c00c02041450000008182030344281204002d48a0298114a1000740d4640c420714041250b08070000748592404002c81c291440003251400c3c0c02c1421100c40e42081e0003040500c075280400303202101d400465030700049000c41d41032003c3c000548446841d0280 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 268265467 1250 268264217 268264247
    0x200a0f021002121303140c0a03030c1509030e0103050a06030c060c080d141605070c15170702010617071404020702031c17060f0114210114030c01020a03 67
    0x84a20003010080c02032020b0000c51801c00d4410340d0b0364040160200303114180d40012103460f1800303d01b0a601e0103000400c01e80b074000c0580001d0000b030440c2c80c1915a100c4801e4100c420b94032600c0c0c0d0620084850256a409034480e44030f030f40c0206004000502503030350007400e9090152500d202000820078060300310b17044a0390740c10400b0305140342d424810300600c03803607a03030181e030038100306d08201045810340b5450711030b10b142903a030103000c0420b800403142442483d80c0600002c2c030384a800d1285808110152101001c2d030b0512007c1540f1040791405982030482d04007025035942c2c441000142d4500f100c400c80c00f15400040e080340703410200e44504210b40589998041d5034081000c6086450030001444481c000c044003040300d03079214000414511090f81c01e001c240480388082813003401c2400201054403816107916500017810030780c0030b40c5a00907038006200b030001c5040c11001c10810640c1c3c00d010340340d03940300441000e6400050504e8050f80c2c41115046520510320750004c02e07408080d06c060051 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 268266717 1250 268265467 268265479
    0x910090515092d010605042301051c06020a0c020310051015120b01050c0f0309180405031801180321090513150b030f060a090b01020d0e03070312200a0f02 68
    0x21030180f00d900401c5590042a007241c030300f59041c01d550324007003100420160342c60040e461a80e00d0768244101015014001401032030305a440c4800221680c014010301503061510000b0a411600003a19241ca40000c0900313007a0703a40148050860051130640c090038010034031400c0280c10031401812001800740701c910f020b56440940056a104804491007841e40b441220022000011501d40301da00c4825a240316074044042d00000c80400d41c101d47c400d5400801075424152000740b0185002ca500d0507440c10070040d501030b100710b82a4141000040c502802051800e0000c003032074400c01d031310400c240c0307014014412410422540da5400d41c1207161881e981c0421110300090038840c1c010815004014030900100400c0304180b120486584202c1c4125200300d207084c1d5440c072901c01c0b0f5070300496450068100c07000c500555402a0b91180e04414050120384400e0f40d030751a0b840711180502540800100f40d2400440d800003c10944024400b0740c0c0d000d0494040242c1d5882c5d0070207880c04000b80200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 268267967 1250 268266717 268266793
    0x1020a02012a140606010207030210081b03010b04030516031e0302071a0a0315150e0307050414070207060807020a121b05070602010606050f0f03091009051509 70
    0x301e10b8440311802000d00700d264490b8003085103030400740d54600b030290a40d2407161038009070040d1300c006054002c4980291000c419010001d004580446004003d041601c4013552950700b04d4a0340d000441c001d0030390312900e6484a003145003040c14804050952038100c00200300500218103151030700d04200400c04600c490b40c007050b24044c0d00f487c0480d132060514500c2e1260742042440e20380e0040540840035034040100d0100c5040c0d24084402c540070703141158480d0100c84025501421522101032401401c940000c3c0c0e075100082c040e1580110b42e03031b900c800600144102030750104408000344c000350914103d07525010350b0081d035601610002510909031001d00741d94450003400c003070440d9203100c16815078260407030074515a01c425500c9000300640c600100010b005208205640140b803460421914000b0242c41101550700082c144000500031008144690207040c03241020303d5100d08040d000d240c1e901e840e182150b002c000c00150050f0400800783c1d0000c0c110f02110080d903c0d40c520860509 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 268269217 1250 268267967 268267997
    0x1d0604022101090c0807020d120c020309030f07091b0f0f0507023102090906150427061d060405072105040605060d030507080c0c0d080309010e0c01020a0201 69
    0x2261011201d0320610750301000440c0c04109a0800440402d054076100850b482e1200b080360b0395085259540001420300b805046200007030781000314034071010b20480c2d0410500354002802c1801c424502c20403035100c11001c01c100d54250050003139003200300d03208590380498400c0241c0715140c40d800350403c020244412111781ea001ea400c0d64135858016015030316019080da50024208a500c0903680d944040c041050641d40480c003ca0b1040180508812004d4842c02c0501c04040a0302070740c45400ca03001e0002040710910060070784501c48140b00c140c003034143c1400955003219400e8200c0c1c2c3d81c0780b42030725180c210740b151040702c10307080502a034001809640324030b01260114841c110360f4900d60380b20b00c1c8900d1910416003101d40100c3c0501810401c948449040000c0c44910030300007004940305001910200b415070015118100d0781c84107544503c180d45d07000503917a07100780700121500d04010040c4030000b5424801e120291b00454010808a0300080001c0e644101500c0001d0402c40b44142d08100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 268270467 1250 268269217 268269247
    0x206040603091505040f020102010509010203070f0c020312030c0d0c080609061306080d050c060f0f010e0405070503060c071e020604050607060b042a0906050301030605131a060a1d060402 82
    0x900c1040c1da801301302c2400e041ca010441d0303100c203150690066003880f0114045075010702c2100d00a421540315920300c005010b50070303a40c1065500e82030740e03d03004000480500070203100080d4416042031680030f0b680c1c040d080d0304804070f50b4802594000c0000d20070401007039440d4910610741040d001c90346803144112003540038003d0901504107001c5401080760b801c2c0180e4010000c0c001c0e8012260685101741c0d106060342a18a404a81c5502252508001004a00c0001c406140c00500840c15101d0300b42d103540120b49018001d8424004a0000094500502c142820a00e0040207503881300b0241c0b40c170580000d0070030300030760103002d210b107200003001b40401c500da80c03015149400140042c45a01448030070b04a41180c1e0f88510300c0c212140011030000c4a200d00801010b6405a0f1221401d507403e43d11a240102002454104030400c50042a0081a0f01c0308c032803da002c10445003c13142e450134209000080c036165211000700c41199a044100d0f0b610780217120790042c0c003501c0041c0c55298803c040305c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 268271717 1250 268270467 268270493
    0x70507090906150305031e07050303010303260c0a0909050601091412011805010501060c031425121409030703020907030b0604080c0406060c050a0f080c01020f0c100207020604060309 80
    0x190750801d0f2040002080f0001c0b001d0060810b40303242042d0303009240200785030184603050b40103050360420801480002d001d04000103c10000080c2c100200e0924109042000416601c0d02000003000c01d8808046510a1048c006082556002c2c00a801c00f00c0018200c2d11641c01401c40e440140040960700c0d4030346142c812010700b09c0300001c1c08a00030840a8007081c41000074180e03215400c01d400800e0503400381100054065164ad120b09400303c816041ca1034940001ea1032804000c0e129050260ba03030008500c009146000b401890310560103c07402800e055002812044812401d100040c0540c3d030204014040300c3e010388544827903642d09103048008002d0b80e91102d031b01c100301080104180100060003102c1c40d40680b0104946904da0f041500d5100140e00020403a5201039001c2001840400031142524070510400d030a0000c01c01c0c41ca800c0e0780007a26240384507200410461048402009942e4415980750001c52a100c4140c000c500395103c1d601a440506440b0f0000400704079078048002c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 268272967 1250 268271717 268271741
    0x907031b0c031e080109061505030103060203090304030b0a050a0c0306150809010b040501060216060e091602010f05070e0f090f01030b1906030303020903100515040b060d09060e12070507090906 85
    0x11918810f0040080c0041a00b8010149000d03e02007000c240074689202c254085002c1c6c0c0c48080c216880d44e59160060741c001041244240014840040040d402e4000240070359070900b0080b1780780c544120074a0031078005403100310406003490400c0101e84040704611032902842d00e00003440350f56401007030f0b016000e083c0000f07800c01d25050000400d00d50216251009000340701c1c252203559601c00301103410b01c0c02d844505a01c0140240411086040101030340341d040e0b190700010031003610580c5003508a8004407014008602c41002c1a021854400e03006151075008030380031201400c0101d1000500b25050100508260f004808a0b48c91002e06500301e44440600009020503922441d0080107034110f0b140c0c650282c450b008010460103003500030140305107801071154210b48040804c10010b0080c004203160004401c10400821010a0050360342040c040c3c0000309a158803910854036082e807003442034000410a008050000e4004140c040c01c0340d1301100081003040c6941049002807011038a08 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 268274217 1250 268272967 268273007
    0x1410051e060408070807030c09020a050313033c05040b07060902010c1502040e070c02130f0b040518120a082403100507091d190902120106050907031b0c03 68
    0x9009617000540b14107892080c4205619140d4070f8520500b64068503500c80081001880000d4410480d8802024200d01910709500d100b50170b032880c042d480c0503c00c4e081151240740c40c039040c45c0d0708049856031541e61452030300c00e00c0c103071500590089038010044000c1a0649a4005d001960712400180c0110b941110420b1a8a000344041c04002e6100e0f115580103160008006507542c1d01690194540d29005884c0507284c4248094a1008010b80528024a20b82d1905402c00c2e5032140e1140f24810303915100c0740c610641c030b0b00012602e0310140a81220309010104541052560300100303683e00003010200c007800499142013071400100415800310b416200300b480d0400c150b892a0032041c0031710b22589401110a8450900c0004d01080c403140075080b140c08030125202c54528100390080030381d0381c00d0005219105c0d600041d20101c10400060660f9101d107401c0c0001d1401914858126020b8141080b613800180949101e6103900c1d030004c824032400047c81004c0c180180d8004e400c0d94407040d60 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 268275467 1250 268274217 268274219
    0xa0c030b041a09010b0414060330070f020f0a06140313120203090a14220603020d0c0e010f141003090203030a170c030702070b0a0903080406031410051e06040807 71
    0x2540c001e01003064558826030038841e450170400110b001f8540100c2001c0c1c064400488041a03040c2002d6400c86000c0e041901b01e00c0d02003c1c001c1c05030203481114821008045502581d0040120420310140051b209000c40d400030000c00da006245041d00308900100517407207542e43c4421810407211841c02400c0503928048000d0702690220040c8401c94013140e1035542951280c0c41c101060340c2c5080070383e8006054882c40380b030300450314103483c6941030044c07000300c3c045441e80c1c0843c4180c0074000d1304949a0509900911010300381d80c04080c01342840c0c003083c0e14241d1615132151100412264034500440c1c4814104e803000c0c3c0300b9000750440b03907000760442e55654035202c4002c0244540000c0e030000d074401c55010030030041d180d4048074040d41455000382107007810042000e03940d6000f81411011b1040302d2100100041104000d400100415200011650b1903020040d01c8170314000c101c0381c00c4118940080c030141e9220300916a0f0b40c0c1d4150440c40e046181e0030045845071103550450901131040142c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 268276717 1250 268275467 268275481
    0xf12170301180509010b06180f0619020f0d0507020411090409080c0118080405270903030a0c050a090e190f0f0e1b1302040b12010f06020a0c030b041a 66
    0x5241400b4500d0000304024950340c041009080711a90060140e1103901000501085085080200a40304000340713605100c144c160002807869114000c8107404040342c401c0b40603d41d405000315110301303d0110141c10b01282c1620010054426208024404c66617814100c56106030003082e50400c00c4090420062a50705040c51402900300800700100e0b903092402510130000448000300c0e20b20b6000d00070703504290a2a040000c08130703034031006894100040d140c407402d10350303000c500c01d01803007441c4044c3d0f40e80c3c00c1111103413080c0c0e0240c1d581801800f1341041000440e80c1d01019603c00c480724100310044c240c860024070b0030300c041ca1a078644141790034600b80c2100c503c450780c42442540b00c1e0400810009a0400034070b6100c1c10030400402c102d05c4508205545400e2020030b00000e401e427444014035040e04d40454140130380103241e10303620b030706507190040c054680c15100540240c007a5000501c1089080d9499a034864894000145880e41d50404030f410001a40404818843d80b00b45010683c81c00c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 268277967 1250 268276717 268276739
    0x10216050615060403080a0e18060102010c0c0302150c0405041e06050109031e051204080a030f02010203010f27020a020a0b1e01060305041a100302090108070f12170301 74
    0x140040d2800c0c09844003040742d10050108003601c00c1c101400b00c5040c10310355101c049990b000801c8034000c1c01100302040101d0368440d88120540d006065280e0500e06020000900710380c42103485c0f03001c1c4100840c0c00004603070001100400b000806180f1240d07640c80e402039404c1c602541e488290010300781204242040c000e1605076822001440b81040310b19981d0004440461441c40040c00262080240304410300164100c0401c1c140a50116480000d80e407420880a502c0b0780e0214065400c000b0454081503071240b5209100f4400d44025410343d414031050340407014036071160744c68201500c1244005c1010314118081c8032200014115214100030390040d40301c4118170412618a288007001a1042242c04d030f0360b000200403000c1807002682440410f1300200805030003941e440f0350010390203102004400d51070313115002049211800500c2d610502250701ca0681002e40c0b5604188828171113800304090040803901183c115200c05045400c240d95001714210903228510300000002c22090610 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 268279217 1250 268277967 268278007
    0x408090d2102060f010b0f03040309030f080a1e020309041a0d1a22081b0601170c0301140f2701090c05040203070e0f0319060b0108070f0503060d0c080102 68
    0x40c0d02621140d5594070138021600c0c40c00d000d629080303c004d01003004245032038005035512a01c20300b0803441040d240d896032000c101e4802e8044590510000700c81c00e802da40600c058039180c0080b00c044d43c44602002c00070707440c0d008082199003d1a379030f00750705140f804045007a8102c1440900311034500210760420310489071001d09000001c50582d40460a5550520160300202c8a50380790070703811486035520b220540d402000050300c0c41400040040341001e060140a00030001c0f103414040c040100380c403d605005060074000d210342d1518000c680b445c0d01c400301c11640b098082c000030629139903004051500300d020314400c0d24981c41e2001540c42901e0158041c10702c803030280d11301d001d050795500200320a070b1008449074400107a81c20000c030071608244500c0159102c0080c2a590280d21001035095040d1889a003a44d145454a07100325079541c210f6005608080d0718908102d6016091001400034480036003501c1c081c49200d4800400d00c0541c000310740150018400a42d540e16081c03038070320341c0d003000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 268280467 1250 268279217 268279283
    0x330c050405150c0106050a080318060415030603050d050408120c0a0b0f01140607030e0f041112040b0a052203051201181109030d030b120a0f060f0b0105030408090d 72
    0x103051401b0444e480c024068104035200040118030700000b64412010805c0008400c0e50070160a200104019420340c15515400f00540c1c0c00040c11031035400c08078a400c080510741d2080c044200010700491034085160f459824102d03078031540e985003840d034043c9410080c1101a1240210703006102284604003200ca048444050110705110000402c025103072140d00002400310f2580180c00301242022015800b103030f030005000003602c00010240c901d0345e9100544080e03a00214000b00010440101d050751380103096280e08000394645000c820610b00c01c0b2613030600c004c1c610810307206d0402d0300c29070840706c071707005017844164495035079140015144800b0703101d1b043c01c98140002034440a2080090720301603080100100041c1a1480003a030007080781c80500c94220580c80f21800714200b041084120442c410034081c08035940318200740c0200c0d0783c041c11610074641420303102030046c0e0340407094903003180c0c2020180c0e1b40e40c01c402002034090540740c140102405440380381030000092102d00e1486c441a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 268281717 1250 268280467 268280471
    0x50a08040e011701230601020f060c0d06080703080306130b0d080406020d0c120c0812070f0212030402092707080d0306050a0302030d0309052503330c050405150c01 72
    0x42d107000078134203075400710281c0d4210402c1d8107500182e180e28042016040740040c01a541c4000382703030001c94109042121000e0216100041503400c648862240000074203440000e42181e5086030381e00070f424803020749411310925666079490030000083c0c0c095017100d81c005261007246552442e00804640241c480c04025000307041c0035150580c041e010b0035040c25442103801e690140c402c1c00035211103841c10300c19500b80308207006030011a019000580c0c021140380e25804441010040700a19188001520200164050060000584841403800d8014580303420345000760780b04140400c500354062005907410f11404800282414000c90020100c003d40e94052049545030030500046401611000b03415070b01400c10010114030a9110f095000c2c03081060b035040415413041c3c4520038030744008814003041c411400700301704400494000c01c2181054209030003551946100f40446104070036070b80b5016100c0342a001400d02c00c0c2d040b207014100003071018a010442d0034481c140c41d0056041160958 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 268282967 1250 268281717 268281749
    0x2060105040b04142e140a0506070512091c030305010e060301020c06041e02090103080919140f0102010e010212041202010516030216080406030e011508031204050a08040e01 76
    0xc03c0501651000041107040c038070058580b00204006003250100c400c1340c3d80300400907a8208500040702000400d80702501941e816240310420500490030342c0100e119802c01c201840000d0350100d50003c201d6107020116855011020102c0c003002c01150f03062581030210740c505030402d0b4041d4003407410307030307468000c650381a696a0041c107080f84034074011219aa0b0107000003e00044600c4400e01e034200220b0380038480b0303202c10b60101e00a80020b810031184150081240346043c18032540b54180440348036950388060345007040d00704901c54070b610070351f000e0500b0040344a420b9000350170034004184145d00071962a407084001c201000d23803d03181122070f0800399501c020329038414000c8074000c4031387d516014180b1901d00f00c141c0003540034a8816850311b0426207410003081c0540082d1000b8650f075180829440b11840045084851303c03000c0f218041c40000c0c0610103100000156142ea4905200c1040c1c6510789051091600d4030010b0b000300b640320300081c04110340d50300e03141060480e90380418203a800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 268284217 1250 268282967 268282969
    0x117070f14040803090d08040801140405060a0216120c050f100e0706020d0503090106030506160f0216060f030609050a0b1003180b041a07020f0c0a08150c0f040602060105040b 77
    0x252165203e414074030390041c0300d90322052130b004040c0c0d0350180c450400546819a143c8416003503501a03d01100b030444003c1c1008280300701881401da020303c06038000c40c50051004600c2e450030710541d002030700c05005100303511141760207503980351202c90b0008111140f80106540043e6940e4500b40b0351440c5a0a10182c20012074001603031400b41d40254001d0200300d100001e080b80d050b000140001706035902d07a00c0000c0455814080c1c035004009414821420200031031025001c0c1120030b00420841d8440c502c80140004000030000c06d560103450101d490941a05c41100584807a0300141d8901d4904028009203032907a80c060070046105035446e040c564188002902103a05903a0317810034140700b80240f40c0014103c0014258400c0c81b07180111f0300120b541a54058094044991401581c07052000d00148502041181070590045030b4004445090003207041e120b030f401003803814040c40f800d000300b85804407a40980f880d4402c402c041c19140c90f03403518000e41c0c42c002031150398000e0385040030010003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 268285467 1250 268284217 268284257
    0x90f06130204031a0403120606050901081e0708090703020a17011413020d0204090f030305010519081009060e0f100501090b0d0312110c0106172a0117070f 68
    0x21a60001035411804c1d00e0700d44d0307102454400401c21020003000c1000d503001411107218a070040c0c889030341d034180c6882c0014000f4090000181032501802c1081d94203d0030083e60312b2030194007100518080e101c1f42c4800032120310300001500020340c0441014004a04001200303040a0498010f000902c44403003014221382000c0c80a940c000440c8100d010f2450260510030f055803a6148040c1000908420700d032116241914005411000a40c55200412092a19941c5a5200c500311109201c03101d160007000340c1d80e07483e0a020745609588801011060001c194842d21a443c51001500c641c40a2800020384615480313125500e914136000000c035108840d4407503a1240100071301141803440d0151401d54045c0711034481a4000c4c2c1e200d280301d010040a8401810520324010004a1003d040c4290fa0f000f40780c0e81030802c09140d101801d00000d12142d24208062049021084810380440e00012200d42c02c0315802000b200400c08280b1246a40c8441002c0703c0810340c3c0d0303c40b01c82502c0c0c1460845 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 268286717 1250 268285467 268285469
    0xc05091503010e0c070203160605070c05220e0309060f0c06090109080a050c0f0d050a080a09020105120c040312050403120e100e0607060609050f10050a0b0c010209090f06130204 78
    0x4103c4040c10002426195640c00404107640000c089a5602881041c180401080d680003140000e05c0800d241003001104000303100034000807200a5500351000036400940d000d0002502c010507228003820841c03032002d00851740340a1000c2e08050b690030313264460b8410b6901001c1d0b554883c0c482c0100085682c0f0f018400e0525660b031051209191412408085903241c00401030468107014243d20034a001004104083d5111700d2910b446440d60f804e80f40c0a0450807006004041c9103060050900050782c0c04400c0780d401d003103900889071541d212140d2921403030003281c10041c0007a25110410440381d400c0006041120300c01c103049d4072600802102101c080c0da41605058101c0307a84209052200c0c002e03109207801e040041c0c05c05003017094540301c00058a03210740c056401c9958403410301001080f9280200da0006079403002c90245071510012a034617550305e1042248480703000c41d0900500d5800e404591510500502004050600060354010428151159441803000441c111400407490080d54 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 268287967 1250 268286717 268286729
    0x3040503030a1d120708160506030402190305030a1205090f0a080c0118080c010b19060e0406030819020d0309030806121507091a1c090c08010c0509150301 68
    0x1504080d4100010f40300304001024031581c65028425082ea40d40300c4401454021010900a141d52460300d80b1660a01c1e6074010003034a0410144000d20840c1c44000c00c07030340c000e40d050b62452809007090491001e07026568100415a0000250b42d480d03c5901207003070403154644480401c519101c402500e036039071081d0200c40c9040e821840c02c03e0041040d45000e0916840c1d000000300e241e80d0308800032418421a00c90485909401141c03180d45e201c400d1040001404090740d10101001005101c3c0c5010802d91003400e041050920038802c1546494014500466010354415100e4400d1065400030b00e07007a01101d030051040c6160107000c4d900c40c1c000c803031041e501600c0b070048585460040c8482880d041c8000302c118460013404000821070071200303a2003403e8a650310070080381080481c581c1608142d410f20f01200e0144510809100641141007151a8071500054044a10702e00010518001c0c1e1144000b9481c20408009058200e0b0007480344000c1207a0588004100822460a500081c0550 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 268289217 1250 268287967 268287973
    0x30c050109180f0b06041e0f080319120207051f0c2c150315010c1505130804140103061a031605070c03030e010f080114220f140903040503 61
    0x90140501c1c83d0740305440040007544049842044940030070600c0c0c1c0582d1000c11500020544280146e0a000107400501010005242d40a00c0d000316281e480c0603040d6212041e100710000d40f180c060140640c1c03004011100001e6450b00b40b10300b800c9488405402020700622402400c2c240d454095204040f040b0900b900d81440c0d180744002000c0c100c044c0b1030854806803034015200806903980c4900010006030601400c0d50324a0b048a10900b07125486901c541444101c079070038800150400024086101410400145a59501a00d000c4500801d00140c24000006004200341c00c01521900075503100ba2000c4c080d180c0d03203206040c9452a007040b840c041c0c0400f4808034075400e0317044440c3c13100300540b858110b0030440a40c07180f01070301c0451390040300412100350b03040e406035802c022800d0840c4407509002c000c641c90b2242e98000c0301184032101c0d200b1040c165400000703000140c2070b10520080c103a0304100c024950070306503006020200100b90140546030010710f80d044000701b282c0c1510f03405805 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 268290467 1250 268289217 268289249
    0x10c0e010504060e0a090f0603020a08060114060904140a060801060e19090f0c0905010501110102030403020a0210051b01020c1608030913090609030215070516020f0307150207030c050109 82
    0xb0031a500c20281140c941d00100b0071701c00188581d030b0b03030040050200d030016000074a40e2541c810000400312035442010300b41c0107174004000d101c0c007140d4079500e0b1500503665030b0786c0ca111400c00580201070000084550301d6041c0705118801540c2d500240c1a079403000020861940c03100003003400c0c10001c4409944060511500fa5a070307000c65040901782c81e00c80d100302c00030341100d5a54421304461540284000640e1f4030010042580e004540c0003890781c00c0c0008516600f4652002912074080c030402070301403200c06a0701c4401c188113404640340d0200a41400c440e192807400d00170b010303605c0050a1b8180d84640c2072000451030302c411401c012100000300451a11544005100580d108030219203c8981c0d1707131400d44e021445500401584a10980c040c00004118000300e60404a0240c800000c0090901030030b050000300e5064905074940403203861074400c1024000924001064025022a42c400000404019000075161080da0710552560315001d03210401160328510038458401c00003440c103030f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 268291717 1250 268290467 268290479
    0x90901060503101a1c11090105010e040b0102071a031006020309061b0709090f0c140f0f031c0c05060a0c05030a0b0102120406021b0907020a0227070908010c0e010504 73
    0x70060251104040d07200642540c400c0c002a004540c03010310f010605c100c912a007003003100002c8405480d001c2101e920000b5414080020240100c54814a020b980d8490700405c050380200030490062400302103409071146481022601da40042e14441e01c01800c904020507010300110590f60f60a40140245007800d164141c41d108140003800c046980313006611000c10f401d1030a00582c91403600030b980325001c503122440d01e86041080c0354420310309003a581248411541d103c203180171002c2002c40e030f914001e01d440d01c0000d04020044c2c0220b400100005850100a5004000700040c18060403d0b207000380e45000c001c0041e510561860400501c1c200001481c0191650000a0814040c4100c960030903100c51044940d134099040301015900803040c0c40c0129059000401d41d81d03d06441c004c160f4240f24901950354910305900038440d81c40c0585d41c144200310700c103d40c641c40c0503162059200e0b047c5041d0142451001e40281e100b50b5007040d0302800716a0048a1200c0001010b0b940c05180514000d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 268292967 1250 268291717 268291721
    0x190201020c1c05070e0f0f0903040b0708041d01330f020c0a0612150506030f04030c08040b03040b1f0302090703020f030a06080d0c241d060609090106050310 69
    0x1d161050a100b0200504000c20020059140940114a441000c0381001c0d00c0e1000c081c00700520400d25803503607104129882001009440442d080d4005440d250a01403800fa405070240d604440b00d0f109002c1081101c150006007060b040b15000c0340110641038030350901545100484c00040380500041c141000307242e00c1030b03090078044a1a0302c1a40c101c04040b13000922075094543c07100d030005d200d0720040e0810840390700c1a0404803841038500004130f45440c021945500000b08812402c0030180300140501d4020b00c07000000f10750041c8500d9403a41c4030340a00006400548051f1400713000940002c0c0d00341c940d610002d010141e0050340d195442d14540c208090148001c1c000d1042540a024001100d051100a103014070701c4401c0c00720710b46042a4019281c200002141310820051031303501d10101ea10160701c01284030b05003404440c40400010b4020190090440840035003600b00341072078200402240ca035000b0001164610301035154266010300740d803154043c1a50540004c58400c445408507 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 268294217 1250 268292967 268292989
    0x1b0e07050f0706020c03031905090a02130c052a010c0c05060a09081606140a020f0d050903071a07081b0906091306060c03020d0f0e011101060306050c04030203190201020c 75
    0x200f4025182540d0350030100d00b503410507101c08194a0107810380c405400740c40d0080940c4148080c0c01001480d445400090704540303030b01c4215007100e56422021380d1451054040b1081142e0003800400c81071120050700d10700f4072282000703012a510300594040441d1041085492898100c0010801611020205030081006800840d03103400104020341d46403280e0480a006140038010002e01500e40380b00c1c0240c0c42000804c28602c0c1c61040256010f0b001c014410b0301e61103940c036000090195560040b07186184500c1901901c88050648010f10740440203205500c598071136a40d482190303c9040d003c68015002c40c00d14500210184010011410058041e10104030000c01c81344000c0b800703107803180864409130002000245441080424183c04203c40102400c1c11700d820b861514100038000c14600b441303450716040000203402154440c2094102101071500310b070003080503080c015090b03862035100784000ca020780520399803d144035250a118511854041e0040c00c4120344c20340803c0390207004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 268295467 1250 268294217 268294223
    0xf0803030c04150c0c120c090203060306040b15060d020d180b06040f02282c0d05010e010f021b0307020f04050408040b030a0b1e010c0b221b0e07050f07 67
    0x4c409284000c5500c0002c800300810741d4815602d0808000c0c20914130202054000c002414010018071549480001c1c0d0503034019040600d456a9844040c0d8015448090075111070f40444c2c08540307200e21007030950043c4010845e80314200900707060243c0070b405850701c41c9000303032600c80074800081440c2081d802039403101b04104801803030400158985a04060b0ac0c401084003061920240041c541e040307402e18591881c10300d941d5a40303008031134010140d2040c907080203009490709542e030f0341000400d401901812045000070b110940407000a4002034001414540c1700d2480d041c0700d1f00000d48044200c0380550b401520210f29a1103170000e0002170080604100e41c0c50904100c0002e01300c407100050f5016800102000c50440340f00c00c1040751800f03a584882601400316100c5403043ea0700041c01c0d00072305620501c088004e5550380034050301c82c0884c02081030081140283c0740300b00945422004801e1100c000d1b001c881340e498500c1506081811142c61021850400034007600e0402c510207481c00a01c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 268296717 1250 268295467 268295477
    0xf090a14010c0e06120115111009020f01110c091f0b031009050c120402040f06030309090c05030106020307030e040605040216110303090f060306040e030403030206010f0803030c0415 80
    0x1035035980441015208490109941d501c1d03041c81d1966000201240c0644100c40460030542d014145200b00d0f0810311070095420b1741c0c0404540d03882d000b0441220107000381c409640301c4215141c4c034070018044103c022032048041d0040015198000c405412010348890300130b2120030385141c18401d029402524100f08080ca100000580c142003115090180c080810980e4980c02c2c0003801d400310015a4105904c5141080200807204403400280c90308440742d580100071a844600120380100150310744003580d5414850003005040e00007250b142111030300300c030421104000c228210394030301003070107000010b03002040f008000c00d02c10035011941100003840080c0e40c0b541c9400140890340a8901100e41c1070703041429000703004120f90400b40501e0140c0241d4a01610000051014140d0320800c510896020010800c40d0310b407640f140c3c0e8200c4007001200c1d40e42da100c0c200a99038620034455145031014204c000304540d5400300940e40035044170300c0703001e0400741800c074113100b1115070036142c9007004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 268297967 1250 268296717 268296733
    0x100903060b1804120906020114070804020f030105010b0a1409011e090801180201180323010f0204060c0c080d090620010f060f06080f0f07020a050d0206010617040302060f09 76
    0x307070402d40542c000c602c80c2c03103103800006503900040c2c03100792075a124105591414142c1e800750812464820707070003c41d83c50000c4075070f6517600c0040e60002507040e5141d055071800d0008140e112008000f03000010702d5841d001c0090026254501c042d10038980745038001140e403450000315002c05152901118602d017800d082c80b03a15042e038503084a02c80ca5220f02c1c09202d9210120555030808149085400300001d59282241152580405c40400c0341640c00740320600000c69031050b100394030a00d42130301b101c58103541ea43d82d00c41c4018440b040751603060702e01c90b000e0040001e442c8000a0100075404680c1c484120702450114255a500c986240d03081e100c4100c9042c4040c0e60700c0a2054100c000c403840000201541010040488008913421181c207000108091100e8238510282141c1d01c000c989088030041d6a071514203d0800e2403640000b0498810000c2c041c90150b00414080d0584d01c495541c0700f0301190030002e02d003007582c040d6000b81c0980c20103400308010f016540f100c00c1c0d1141220007190184 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 268299217 1250 268297967 268297999
    0x1002090d080c010501050a0510021f06031a061903030806060a0905180708160c06020d060b0a08091902100305041e05060406060e0c0a120609090f11100903060b 70
    0x190b00ca222948800d03551203005026070701c0e142961002810041c1ea8040b845070f0354030406944c5003511507000d1000c11410220700c0c105442500300401455108408158008105000200004007a20203910551000c00b1b800340071126049694200d940554540c52103031101c1c02801380740c1d40505c0040040040c19500401c42d41c0344e0b20711400c04200d20390021080f070b14020700e00a007100702c00741c4004440d4032407030391150131a0303132009002d555190040300c0169210308904101004041c65805510040c03408156580344c59044800c0034842e00342042030759001908400d0103016a10340c00030003544030380811070000d8550301c40c2d4090b0764400d114012144c1040e0346500303100d0080c00c20b01e0045500b5030001040004206160003400014149040c82c005030b414482500c8406000310391090042090040c500001d84072030b600000d0040403109001c12411300c41e030803c401a120852815940103850204100c543d041c000900101514a40d40b03c440460a40e0343d100040d24504044541c0803625052011034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 268300467 1250 268299217 268299233
    0x702060403060507020d031a0d0b2505030108010b0a0b04060e0a0e180f06040c062d0905090f040309051e09101d010f06051606090b06150306031002090d 67
    0x6010503001460030f800380c61310007010380740304108988c1600e00400905120703458006580044541c00680c40005580b181412a16214071200d560710303115458a0200015411000442c1600c89500003884912110802e0080c9141d40b0310a1028800080000300820b90cc5500c2c62100c109000301840748480c0d0b12085481408016124002c0d6000e0041095071440020800d64021180d0075002c0c010600c0c1c00c1c0c4030076014a04602c180000d104c001d100304001e0444050080c11055000c0d03503110740303100d100c00d40100500c51900820340920303104004a00c840250918441c41968140d443c112460f0808080c0160041e8400b007050b004081c400d0710a0042d07450302901840341c44a290107050403172404030181b503c91400ca401611801e800001030080c0c0707680d40b00e07413410784a01e8200b0300d03a689884503030101e94003041e00003d8040c40c51308440310b0801000c200d400d030042004983d802c0c2d080c2e08228003040396100c251041c40c2e05601101000380054441c0d0050412003000a010403000760725511b0f1102 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 268301717 1250 268300467 268300471
    0x30c05061b0a1b05040b091302030313081014060a0501050a030213030821010b0711120a050d0206010609120f0812040602030105090a0207081608090d03030501050f030f070b07020604030605 83
    0x10f00d10205034014040d9a08480e1030802850112018441c0c0c140303502c0400c1d40440e0142603c3c0312030501403820419500c2c100304840989080400341400a5560320b01c068035044005440c0c02d0f0607042030032a54040030b10401c1d03d4042d40000704188038281ca0440152845d501480745e45040c15028420031402101c40c6042000450007141120740d5444421014035420311882c040440d690384090050002c9140c0400340d03110a40c1c07004281a010b080b0702c00166500382d10040c0c5090030b1242c440c0c84010004085054401584c0607022101c1598850001f5140000180203840140e8607281030000841e01c1401803107000c0b03000300109840e1000035021521a4481200c050755540d400000400146c20101003166100d0051a8214101141c90344c03803070240c2c4200d105036282c21a5140e4500107100e42d890454003e088000e10281c034140c128680a03029003024410248100d0980c0d020803d141070102d0494040c0b072210b03000c1c1c0b0559007084406c00440d0818441a86c1001081c0b0000c80002c0051061078 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 268302967 1250 268301717 268301723
    0x507080f0609071e1d01030501120803190204090b040c021f23130506010801090228050306161805030a120203090301151809050606040c0509040c030e070602010204030c05061b0a 78
    0x790312500300e05d08880c031020b92048241050701d48001000443c1007221500d103a658418551540c035100e010110455034103140d2500300f21480003034002070390740d1107500ca548072000c00e6600307108141d21648103076100c081d40441c488450051400301006040d00ea80900281c0030300c108030300c82001d501825030594150484016202c40c110700c0010003440010040940100140d170024048652154041415107601c0c04044e4500d000c1c8010780d100d03a00c42280e0a40c0a010081c02701c1301c2e1072034030105406803d41054040c0010462450041d000f8003ca18054030903203501a006081101035a5500d50800d403001e241c03841103001c01e02c2a22410354003070185116484414108020981c01d114008510b8510205131250141c5000d8075200015004540580e04c0b100490300041c003a82241d00981c1c881c0b00e9040550792161401d010b904402d5010b07407203c1081410710046419403030311460103a080707202e240000743c0115003c1d83e0400242c40d0900050011105a04240345241c0c44c00110500d0326548032411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 268304217 1250 268302967 268302977
    0x30b03100e0a0201020f01020a0e0609060c0a0804051c051b03150405010603030e01020109050705040b04020717191403060f13021215011403011e05060c01020903010507080f0609071e 80
    0xb005542c0e0400c01c07200300b5012480210314011444a000e000d805226459902950002c204010150707124821fa4a80c0392205003a82c00301001e5140141496102d400b44910039044220b11200030300c5c080303a005ca00c96501c0300c001c0143c0a091424030f10b41481c010b08055042c45440b014403079041069215a015038802e070b002003030260840c9000344ca070707a0072603500c0f504580c900360440012410020f406001c850f01a81d00113100004003000c60003078850824060003044d0140c619841c40620032000340b00103e01184c000301d05614060f8105c400c0c040c2ca4801c1606100c09101082d04c61800001665408400030581001e0f941420f515500340c3c0c00c2114000706541001082081355480e01034143c031070740000d180691004400e140c01d10501d01060042c5540c9400f200080e403013070450030120710702030000181681c1c0c90310b100f181094041c1d0300010615000394200000b280119000b40900b030302501d0500d4420009540312401c2c4070041000030b18060401c24500120040403000c03090b408200030240d555 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 268305467 1250 268304217 268304233
    0x12030503070e1c120909060b1b0601051e040603021e0a060809030703030b03160e01030303060e1b1e03090a0c080304030b0708090a080409050f1510030b03100e 70
    0x2400c02e164501900d80640340064a240c52584031010030685554000340036072040000c0c01044401d00d000d034219450443c98a600071921600180103044080c1c80c0404906c41c4842e030031903043c0c0701e034000e11400ba00007402c490a0340041c2070700c1e95800e0710301f04080e0001070820b6032600020540380a032442800440c2602d000442c560414181e0b11025140c00d081c021141d04001c0c80380d036902d01c25035074044c0402d075803442011116581440300356080c94000c8410110b898036611b2006004200381b100314007091402000080303d03014024102d2240c02114043c201483d0052140b0070309034040c4c3c140300e100c002074510318084024024091400349250780024044c20b80945400804064a40c00c006441c1d0720500c010000a02d00a4015501a60b14070340b01e88150ce4070501c651400e0160400101480e40c040750102c3e1511090380322510414001c0d54400503901c40003860080c201d00300d415181c0040091039403801150190300319060b0b109000d8122041c030790010b020041158010f1a1800d44c03500060a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 268306717 1250 268305467 268305481
    0xc0301020711180609130512032701060b04090903180905060102010e0313090c050c060103080a0f03180b15090f0a050708010e040f06110c0d020f030408100b0a12030503 74
    0x88060f20b00d6603070b22440d01c0c6400c10344009258524010304001c4403010750b640090400409100c08201484124006512802c22a81d00c08401105940751059080c0d884a098001c0e001401040300706c448c1344419925050520081101400e4a200b0076030070711990303410b0310081c6403090404500400300c5d40c1c000250b40c14184e00080c00e64072528660f41241d44180400b03201012014000c000f12182c40300300081035403414009481c075011b0701e15802201d0003180000010f000c001801024000c4040d564402c044199001c245e00700c9450602c41d4030310242411042000990030311000d80c1011441c1002c0001c81d1101e40018010707130044400e910340c2c007140028014069018010180c00a01c1c90410030f0096052a40c040441000140054441d200c10211541844020761148407038440103141030b50b4a80c1c3e030710340361540c0b1202002c066005114a042d841815100482600c00717032124000a010340b000203108410241103603174101079001c4821800088d4844172030021400c0b0311b100c0e48a990312841c1c280 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 268307967 1250 268306717 268306729
    0x1e04050c03010b03070518070c080c0708010b0a08061602030405122d060403050f070c03050105040311120a030f18050a0c0f120f03030609110909100b090607050c0301020711 76
    0x500f03141c020362050f901400981c3c0e441d030501800b00e0350006244201e50b103204040b0340e1003c007084040c020305000a218580d0075400f085000c1600c1c5240c00034031120080c502884010091482040702030b40040010412954505200f0304500c5402c0c4112401c15845500041a2003080702c4000c43d0341d8002e00d00e6502e840c0b611950704182e040c201118004440e0369410003034031804010001010414002988805a603841c0240c401e01904000b172003444a480b860034600805060310300364040b600120f4000a840d400142e100c0c0134400240c038050920540c0c281c290080c0090282e401394082e15402002d2200c0342100303138240c9180c014001001f00540d1410410801d50310f0b50451240802e82d21000e015400c3e1a905600c0000d80c0065412014025414114020101900000c510604021516401c00c0c5a280580101c510440304d518554580e0400740c01c072034040784035082c2c9103070003404008030b68501040644040ca0080040e07811290884001070b0032a40b01d0b03842100c0c1c90403140742200d920700b891 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 268309217 1250 268307967 268307981
    0xe06060a0b0909100b0f12090a0203031b0a0210050406080a0b0109030b07030213140102010b030c09040201140403050102040905190915020319020301090c030507020607090303081e04050c0301 84
    0x40e10200200c0d800d04006650328400d0000385030089541c0c80114101e0342100483c1002000c03000c50094556075011340d09000e50b400001c1c80100000d5843c0030560000000c10001d80d9a40d00030015403404944503400304440e00c90003012203c0e40a040c80e4113001d43c1741c070054010320942c1030341e8060f070740c0e4240345005d008040040c0012540c0c84c1b8000c0340003001d9030400c02a80540b074104043c1c417021b030707a031541c00c0703000c1d104a010504845444003000151315203190319000903000c003600280080d0f220007040c03542c1c7d00c068032001540280c0e4a000b103000b43d40030713000d5020241c0300440494609900c4e03444440c2641d100350b0001107520340e0b4204005402a1040c00c000300d080c074011084c8150905501c5860030f00c50040906a602d0380d001000c24002c90f180d4003d00c0d020400f008056403130350394400c0020000c20300c4100303000100303050100285030301c0d101050300340c8520803645646072601d096403001c0b07a05003c01403002040c40303c4081302e80070a0066a0351580710318070032401800304041400506003942c2c28 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 268310467 1250 268309217 268309219
    0x207110411040608041709030a1406011e030f02151204020108070503090615040209030703030302030a06090504030503130c050406080d23090103091e0f0c081c03090606030503030a0e0606 82
    0x10902c01031000360f0740700d00c0041e0000e40068100d1b895002910a0160a1080e103000a51601c50303441d090302004140c072804501000241c0641c0c00a030703a6841c40801d07900488041159a10a1a038240000b921305041e081545001a04407241403864982e405c019900c02920101d1189440040104540e0b008694581c020741910f052415410a600080c2d0b80c0c80014050264034100b0103404201c5840d07a0381901c1c0151801801c903820300d03960b070078041c0003584281d42590750281456030100d0760000c2801070a01442c0d0585c0c510b0b2565031203000400d007125007079000b12804a0b088800207561303a031764003902000d010a0b001602100215842c007074140002d40001c070112071103c40d125000820391206441c0ea03920203007030200c0c441440f45021811854203000b41e81e07103140d40a10719010700220500e243c134664401c0054000b141c0d21201000d549200750030088828144070882024014466000760150900c65200072440603140d40d00c181c216007044995140036965040080447c240800c101a00080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 268311717 1250 268310467 268310501
    0x3060c180e0711121b0d0c02011808010c091403010c09120203150906010305100605060a05071a07110c010309020a0504050709090908130501030c0e210102071104 71
    0x40006680c0000a100d2185862180600001034080ea01440304014241405400c1d200216040021a1202d8111009420070759021205205a006000810b00079240d4980c596101c2d016642c0c0c01140e80208000000392886101c0000040c030300424050f01c0c90000e0a5140c0007150760900038801c00400c41c60345114401da04000100080380d4006002d50140c45010b503000513080f04900101e0b01d0302c80804074840041e4103840802202400106815043e03904c01d9003a182c880c40140075030020781c0d24500805034000801c000c40c1d4099405000240b102c0d52040100030b12200d42d108554002480456140020a03031614031240303501c40c14082c0f46220b80d000d003800c2200d024160007061000c9100e000d101d014a540b00c020501c440d00552000c0d0003401d00480034082c0032094030b4101c080d03810580f80e10b00c100541e020003081d1507000b0b01031a80000415a12010030758a001e04006a001d81d0318080859040b440b03141c4c54502c00d00380003d000e40c500510b250805d403400f490911040703e01a65140084103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 268312967 1250 268311717 268311737
    0x21011a0d0c151103030124050a090e040c080a11010305061203031504090c1502061005030d0309030e1306050310090f0803060301140a091202030301050f060f0d020705060103060c 78
    0x500c0805001d0554001d084040810804041c06440341d401d10003c94500348004400080c801018944140e52442d40d0400640781c04070050302a900790240c0030400003c140c41c0d8400f0b010f003c0300000002c0e40a8015044018211b0751201c41a04141c0381d010280c0380c94001c000041c9055806d4010b46030800425124152040104000a920781c007000d0300002078110590a450038682d00c41d00308000040d004402209000d42d2a18440d1034a103000d4a060098060580001d561003008036004080b904064050100d20396071401c00c0b0001c2c074590300e0880c02e11145492904998442c04c18804914a52441c0000c2090810042514140f0600c442e10742c86400c04059000003070500c2210304140740c0c0102c5180d1640c0300c400009006d054402d00d44588103110f101041903d01d00ca800080e40c5a01603e032920000c0d14030142280c80b07120074000e06421502c50800d080260800000412102d409020010308102000400b82d0903079120410590301580018014001d01c174052251952164560030020700300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 268314217 1250 268312967 268312973
    0xc09022205030a020411094b01080709090f0609060e15060c151315060e010510030b0307032103140c0c030903010e030a09080f03030a0b21011a0d 64
    0x743c0c1c020b04024069500d858070710000c0001390f0180c070184a00103010030701c0b140480d000c4c091000070040c00040840008a801c0d0150135500c00108030400820300c0020304a080000156600c0d880500b00b402009000100003680c002203118130b0341103118540340855040d181c200000d0958025400c91905110a0020310101900c203c4d40786010300e0060350950f071142c0e142c52403d400c142500d0a1408801c1484040000e0f1031004004032104a20034000901111b2210103002d0480303000d8040c010b403440c1c5050041c005072614241800516480d40350124000068a01080c2440645e40c0b0481300e001c443c0e416418408a591218805074400d440c040210039400c0701005030900e006001602030082c00035214820020600c11501130b108003034003d00c0a6102045002d41d03d502411003030000030000800407038503100c046904042e504a1500445c03c54a074078040c10000c00d90701310301503400300780b2200207032000304040b00d01c0ca101103000700001800500940803404080314815454801d401e1302c0307080400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 268315467 1250 268314217 268314223
    0x60203040b04170304180501031a07090303031a15040602071d16030e011505030706030212060913051501140a030203150606040b070605150d02010503010603180c0902220503 76
    0xb224034162901d0800385440c0c22840c29171013190441c2c0302003040311018640c2162247c22042c101d038440e040500c0040080c030f40c11025903000340c81900000740c9054040011a100740c01c06c0041c803a075010340344d51107600306000550814000b840341c29a00c4010900f00708541e010700402c8020004002ca40c0141c0c0f46400e4044500e0000034210141d45550320940c03052240700ea401024000e010350020054004900c2c004c1b049445140715051191081501c045804c1c1c0c440d001356030014241403030003036a946800c02040207441000b010324080040ca04201c60100d0700c00c20501d00a403c806503090115410714401c10010ae410640762802540089410030058800041d10301054039013540b0211680c50b80d06c009961486194021080301c070001c10f00300240115035000900440d240314011000784042002d1001c81c010400b00030307000c11428001005024060f0f000381c5400300380003140c0c15024603240d44251080350607400180c581540400e62102d0000c1500c1e2a0b40d403201000400801070b4946400640c4e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 268316717 1250 268315467 268315469
    0x1914010201060621090c0801020d1a030304170c0a0b03090d14090d230106050a080109080f07080d11070b070806222c12030609040b040f0b1f060203040b04 68
    0x32805200708000c80e00013503070f888640c101b903110358a14540d41d6900d1125000c0d400c540c080c1d41e5241e240c61107402d403070242c00a0394049964058080c5090520780394104102c100c1c1403d001c0d00034040d85010070810390351021008007600150303020315224142245140d107040081c817034040070b1201e101c10300d000180e00740013540c2ea0b03480100e42c01c1103070030312516040d200052815418207100c01d070311280140c01c0c101908481d0554a0541d1000d0b4600c0e40c0d00e0340d003402d271405a080079100603030400c100207505500f24000c0c8045400b440d00c03146043d2201d29903404039450f02131000191400400c00100b04846021035a40020891816454904200c40050840d1003250545145915040f41e001000480342d04407006d00000f040923100c4000241000202c50010030420100034003d0501c0c1111421030501528006c24002d804042555110b41c1e4410070f030740b40548141c031060385c0c0d4203000e00020809422144201038186c001e00d0014000c1102146c0400183c1040c000e5400501c8140080c60007a4182c0d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 268317967 1250 268316717 268316747
    0x4061b05120d021207020616140a0e0604030f0b0105090105060c100b01020c153f060109090e0d080106050f031f030f05030c0706030603050607030f020919140102010606 74
    0x542c0d01c0c0060400d6900070b200e14680b03415104824401c010403a030300498014030414034940008100e02000c0ca04403200001924500a0020700384500b041d0142f00b50660210390001810952501d61245c542c07411910800c00c00711213580e01800103004a040040d507807030040c00180c03500b03410b20f8140c00725035840e4058030344440d500b580d031008148d1203a8030811070240c911401030170b12410039080c000340210303c1c0e01c8602e031044040c4c0c15009115040e04101403504040041c5c403800d20720200081051503c500003e004141040014040410091454415000301c81c0c0e41d10000d0441c071020140c0600284c1d0140d1208060000c180302d043c21446141c41225400240882c241c1d01d121440c0400520801c459000905140c00502c0e444040000000080818103500012070385da180e42e1310021400c0e0394503804028040d4100001246869010307400c83c000c000e100b14030141c2000010f40104200b0b142c42001142c652208050812485070441084030070002c0030320003800314900301301d000381110300802e40903 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 268319217 1250 268317967 268318003
    0x5060a09230d0c050c1305060405150a121a0c090a0f050f1c24060824060d060c05180616140a06060e06030c100f050c070e0c04061b05 59
    0x2003240c280001740d64001d005044084513524110458010001101c800c0e014601c0d01b80418145042a249850346000081950401c5400e103078440482007507818084031040c3c4181010341511507903401842c800c404028005450341e00100c1080210b40c030325440310040000041c018032550b00c0310408038881a0094820344c640c10b4400c040c1d000c0783c00241401078206084050603a1007008130340d03070300c40e55042c0c00c160510410b602c1da08120303101c540641e01c001c000251000201c038400c05c2c0c8045942c0c049001002500e40c071071980c55a0b000c1d02d8040300c07450000f40d00001c00d060544070065904c90010429555142007448480e11105180207010700500010304c5801d1039907501d4410013482182c281c0c0140140003040c0d1f103940130484443c1c2a02e049120b80110810114181440c42076804941c0a84d503503002c007501c031410151040c0e440001da0320741d68004c0303040108600710070368034050050784a81800740c0c0d00c03458071000a0518a6080d031504a03600056044404120000b62048814040b1154 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 268320467 1250 268319217 268319237
    0x30601030f141f0b310b0703081e0406051b040f060c290411060a09051c020402070c15050705031e0c010504060903030b0109050d1202010905060a09230d 67
    0x24030021035080d074409060480c0020300541c695403448000014040c14200000b696101200c040170386a034580103552103040c003400f107400841e106613011500412000c40120020903440c0382c0b404180c4040f11309071449134a80b81407107114004481c01c034071288800006682440e08003080c0a6218000740301e940100000040c081040c40002025000c956400c03c1408450081141e20b0791403010084070180c80862245210b040c03d400d0079030071038010319610f6503588811410081040740391540c9000310749607014a10144e00c01602c0707c0c4001c10105000384200d0300340c1c0d4646070008242d0700545140b03030304120b000d10001000490000030381d2203190b000f80e1100c8418002126005045c000c0d50440c110b61740c204020b000500900d603000c049118002e80c2c051240e0100140155800b03040b62003200e8000d0200c9107040007141c00034840c00702038580c62001149190940d141c651a002c02500c040440550707541c40c04d401c0000c1d5100451422030140d140000554108054585541c540d90424040c0320000d04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 268321717 1250 268320467 268320511
    0x90609071d090c06030406060f1202130e010e01090f05160b0f0a051c090b01060305150402070501020f070c18050f1501110d0c1e020d0f0c03020306010b030601030f14 73
    0x404160a844013602d400e450345083e06004000d13195900c43c01d41288442c000c04221010383c186a85d42064014024003d4154a040d00c50b0041030710f41564850355503246c2100400301c00038060b03442198041e0f00d400140340c1890501c0e60418403801036120101285034402c03c98030001400395248a1079400505840700c008035000c7d5802d00c0759800c20a02c01c1034090005c0d403140380740d5128024450180c082d4000726038031440e041d0f040364030640780f4512206401d0b04107806032400e5001845564421030000d030400301018800c3ca40c40e00000c0c0102d4107441214400d00c02c1c9940300c2c4003188842c102d40700038880c6081c01188008110030141c401803c0208031409024240d0042d0590b540c0c407004a404c681c145080701e1001400c1d00000c1100311039804600f418510481c402200c40903a03190010070420001200d44d43c2c0e00541440b28008540d2001043c50000c00b69506000c45030080982403036480d940d15100000400716118911511800f40c94842a5000da04113030314980d5009400c0080b014511440d20 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 268322967 1250 268321717 268321723
    0x40f020f0706150e043c0311010902010e100203041e060f020102031003030e030c03060408090f01020304030b0a0504021201050a0b120a0c050105090a0f15030c08070c0f0f1a090609071d09 82
    0xf06c01e070004003107401229204d031101844c601c0c0200c2e01a81d1102860700c03040865500340c500c061800f0b4000381c100ca03d1502079241c006c1585805e81003d0041360310f009d6844628100c100360180551003e42c001c5030f42044015041050004002c1c0c103071001718a107203001c8500e9260000742d030101404100200030004401d4508200310a885403008007120102c0c40c0901e480c1420b580a5000107018541101c0d803c40e9550000050380c00356036004084c524146c0c2c41c000c145005040c020b100b0703030b4000610381e850740300c0d11401e2107854098000840046800c0c90450305000301140b034600c000c401342e0f011140141c0482c04030845541615000d181441d130b254800400600200e0041d04102c07822070400c00002080d810000d20483c1040140e1000c0c0f00201520701d094a00c200122480400701c2d55000d99840003c1e00e0a22016246101d203a80b81500005901e48008035071520001c400b400051074240417041d0b07410401c099020801c0001010468140340002c6110300100308008100038030000032035401d59040c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 268324217 1250 268322967 268323023
    0x606030b0405072402150903070206131a031512121218010e060a0c200102030f010b09030703060e07050d031e0318080702040f020f0706150e04 63
    0x21840da02418201401c200d516041030348102c2c0c50049001219002d89100c0c4654a030307400d00c2036000b503c121103140c42c0c01403030400000c040303da55000c03c0011500590301c1034040c1c8464017100402c501d04c03a0901d420503460f4681400e002000c801c0030700402528040c0f0952600039a04152064000c800d444a10700f403070a0010310b1300c981941e601107400380c80c482c818203005210320008610301100d4140c030101d0b03900300d8038050114001c035005600010022402e6805c04001c10360913140203c808248001004441100d11580c5004c1ea5000000d20070081910702e0a68050b202403021b941c6800805c2d40060303030321000b47c440201718035202c0f00e2100002c001840031000a10014190000c274511525004024086980b00303030300552100e0451154603482840f56051340040c441c4045000303c10350b190381c02c4540182c0c00881c0e00c2030322001403070181c48003030002c1e0001e02c41a000003616031b22945000d005a0350700e900c0500c480311340d110040220590203013007660041e4001410422841070061041156412 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 268325467 1250 268324217 268324223
    0xc020c0a0b07060b040b01050a0809030d02190e0102010e03030a150801050112030815010804141606021f0506030c091305060405030a1d0d1b180c030c080c0f0304060603 74
    0x848000080d48504980108030092243c2002c0108141d6a4100003c03504015010360004005000b0385410b03c0c040d2b040c4d42d030046103c4007100d081102d24124141a64022907040040c000c1701c15801485940052000040140900091202d9a6030b00301051380c9000c001c200130a403a84480104031884800e01d68040a820000c000340a40d41c0c6a05064410051801044000909541c0041d021010f4503820000031801650789507859140d0352951010020400c00d075a1550141c0c1c004039601c182c82e1000c0c44018440c64014042148001510703000b1041c6103078200c070040d800c02c0e0410130340d5039001c03c19600c84001215414529100c081c0c0c81260382c0a07031600100140f20352004d0100344040013004d822000d0981d034844640521041001040a010718803c6820811030048040050010340200064500c1302c1201e5454907694502300080043c01356440c03c4a40c0d44040d0700e020654107000d014401c1c412410214141d0800181c00f400c24840d212600a1406020001c90100012a08004c0007150 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 268326717 1250 268325467 268325479
    0x30402090a0b0135100e0c0304020f090411100c0506010918051501140604080309040b12010903090f0e09060411040207241a0d02060c0f0a05030d0b03070f090c020c 72
    0x52000501d040004041312102140c4048600240a041e8081000745c1a188103042c403640584400180c41142d80020740100d030311103000804801a61140600f683c4254010304110003020781d50414070003034418005d0120308201c00707040802c002c104d00040c00c504680310702c54001900d45044041c80100040080d000309240164501d2591140c40000c1c1c160507118603c514010881d01082000058803c42c412603140d40c100780f1081e095803400b03a000f0b00854801030080398a03840580b0350b46007140c40580e8102c000c11071051091010404c1c030780c417420103044c0c11800501203040c5240201d85d5910010710061114401c1480340040341c5464064815140d400061504482030182e07454401e0998802560012071030120910080100914003c03030600300a0081007020785e02c2d0302404100d074840e6010612900c9075920b0212001c1c0d04000083d0440e00520146844102d002030b500151f40c854840039229501c41c110a0003814070001108045030f41071500040c0500101e8030036400d111482240541c448 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 268327967 1250 268326717 268326767
    0x91207080706120c030207112202031303030b091b0f0c0d112116020d02030f0c011206050604090c0e150415030213030b1008010509070911030402090a0b01 68
    0x140e00101210081c09810f14180111031210313900b24100e0107907100c050b01045441172141c015040400c0700070071085103174200f6180140583d00100030384e441501d07144881c4902c0c181c070350b0074941c2c540304410000404640b038641504001d0020000050746003028094454000340e90030030341c800c0034200c8105804246c20303950003280014018042c001c41071f180c843c43d030141d40c88000b203c05941044082c9150030190300d6050241c0c400010406d68280da004903040b0a0b80220b070005640c00b00240829000848010800111104001040558002034408202e42030150a00056403101705480aa035030201000500015040007201e1002c50344034420f40151605035035180c482034480080081e2030070104010138500d03469004600300d1190500310380c142200520b0901c0060400604c0c1034110440e0600c0b8029151180002400c50700181e83c140d03203a85c0440307410002c1101324024050081c02ca980040e040d403405802145108130020034203001c40740d480642c00220303030290610900270090f510b02032500c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 268329217 1250 268327967 268327979
    0x204020a0c050a0501091217010902090a05130b0f09010305031213200901080c030307170708040e010305070603420b0c060a0c14090f060c011d010c02030912070807 72
    0x240b10701b200036505580c68213030f6141e5180c020214032900840d1060888807580c68610340c4c038002d4000d5404150b11040007800010300d607540201035882d0304001c0d040060741000e42c80401401003d1003000c03a0140e00c040d001000030840110507181d82c040750213a00e2803e540c03008100a400e500030a4010f02c448202100d20300c0c00c040c00701c2080c0d40200107a50343c60050343c0311031209650310038211900d0b52540c010408400020060114620140320341141603040c020280da0348a80e0380c104d81c11122074100101d00410034072108000010050010b810201700c0c0c0c2100c200705880c1c080700b49000240c0c0806035845041c2022a80d16103803003520042213018a0359880d01d405540700c1d400150101c401c0e00c50740700414810303a282c0c441d44401c0c00480d101c04010001c0c03007c08210326006412100e43c04032001a102d1420f407256002000c107060254000a01a1318690520210030907129101a10740c3c5003983d1808201d030000110b0341c6114044818401440f08445001d02c0c0407170507001038100703014007040003801d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 268330467 1250 268329217 268329221
    0xa031202120f07020c0916050903120316030b091006030911130c0806150a0807050904180303200906070203010605030a1202120903060c0306030307020a0324020906070204020a0c050a0501 82
    0x1030505038280c0f040700303c881d006c1000c114000c0d660f00c1c544407040402500c0c00c5006100500c0981405400e807804500c441030601c4064004403001c00703c48828809050007198984604c03202501c08548482103828651104050500703030f40107100c1450317078850251060207d112540044280000c045a10f1252040100e80140480901e078002040e01300010030380d54030300746034440d9009031f6035084642840064031045a0110015041030180201001004c6072a102c03402034000501d8581d01c40c0c0d1141010b45401411250215140880c1324145c01148286500420480e1014001110f0b00c913210748884c00000c0c01030420758029036052098604031820400703004051066113125800340c1d003050084c008403040c00d11030521003640c5034014100059224603e44051034020201070226414030020303901290701019950030545d0310407540118107103400c0c07407001c1400c164011401c0550034100740d030700818010302030020024070403a0045030040125200b07010784c100060704042100c036a03e05504103540 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 268331717 1250 268330467 268330471
    0xc06030e031926010b030705070309030b0403080f091f02180901030b0405010c0801060503070f0905030a031d0a14060c120f0406081509060415170f0616020a031202120f 74
    0x43d455695074219103101045025460483c3d24100c07640d440d5558142c002c94007035002e03040c2207050001e080310200204402401203842184661103000c174070305021002d00b880c4a40240141c120f540500c080d24884c207a40b1100c4049140b040a01684034007000080e4540a100102c0443d040700b150070002051003a00c00600c1d01031401400200100c0101c00403c444180c000d0085c1c8010990070404210201d00c181420426420340d460141080c640343c030300090506e00e1411080d8001004c02c00c8543c007658070000189102441200d004040601e4102c1700b6080424158031a44540c00c04036085900300c0341480381e002c08481e10303040c0315a109040c0181c0e24094201b40110b400190361074001620f4000c0c214254105000002d010488a07903a140c00c20010340381900040c46103652441c4000b030381c02100f615010141c074140020788030ba0050340c1d881c1450001c0080c0b500c0c2254401005070424103030040742013040560145060b950301c5920894181c040d200e104c24081402c20300e030081104084039210540c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 268332967 1250 268331717 268331747
    0xf0c0507061a0612060607020a060215060321030c1209071401020303010506091210050a020c0f070312050a020a15050403080f0114010e01030f0617070f030c06030e0319 74
    0x844555041202440b6429500c2d0503000041000307076040f64550115607039401000107241c18030b411440d9010a0750070030302d6030101026a00000400c0440020000850303842102600142150f009005085a14042c948800d551061000002c00d101408100490306181c464034031040705800e151210b00d54620007440380500242c00207520b20640e61010044a0486100030440d5050401c014100240c2c80300c41c800c2c40c1e86074411a40c141d59207a9060280900c80c0c20201c0006885110041c46141810704c00e2107170703408a40042405000151848509541807481d0385415515461050016882c1240c0340c4006000e0740382040d000e80c002612504158451807203503031423040a44031991400c508207421300451501e801802d05c659460351007000c41010140c4145008039201e0007214010003120129003080d50450400e000b0b0281483d003c0080030f00901031030040a82103461500c810030842c0c200d0044004140e2102c08622065004000781d41c15a43d038040400f0101445081c01742044c06030072484 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 268334217 1250 268332967 268332971
    0x607051309020f03060f030f010f0b1c020d060b011103070807060c020c130b0a030b01080606120d050d110409050a1a0a05010909020706020f160b0c0304120804060f0c050706 76
    0x108158807a402a10031203d46aa5043e0958443c0c10401c204a00210b080e2038052042480d000e10460090181d1083c845910138001140f1144d1014041070070840041d02d80300d0340d5001000c00c01a00d96102c03e400d11900007500140c07104003000122400b000d01f55a00f0102d00c404901441409518001807001901c91201000380e0314810000740c0c0c580074190320555004a0f140807004400d83c03650880480709a005240e510b00076100d80d42c41c1d86960007a0051a141d50110b0108121030030f25843c240d910002c000c006001c00c441c070b280c0c018100d10490000a0f0310503100c900b034110b8040910141c801034440140c041c800780c81e001ca00745005200340c80c90044024001040741d080e030f041c030001c080c00350340045c1d507405411420841e140000c0d40c8218021070350340ba420800d0b0319403503031500c021b0131482054039403810300c440440c00c121001940242030741d44001820000d00001421132250030403040f019040969596540e03080980061040028142c65a0300708580b5528003a480030007002018450041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 268335467 1250 268334217 268334219
    0x1a0d02031203041518110d030216080115140a031203140c0310060806030a17040b190f08060a090e010b0307260a0b070810030501022b0507080109090206040806070513 73
    0x54615842100c83e0701404c01d0f483c043c04070049052041f42c43c0e40f070900a004860b041130b800010510150040d0340000c069941d40c112140c503510072001d9002c0181084165892401d00581c0010300040c0140300007002c0d0700780c0c001e800890078000d4020003035104101002d0b41c2c144c43d282110103a207500407200d1401400090364081205405160000d002d40c41c00f400400748104555a6135581129000f04a00b4051050000140f01c079500c000402e16007a544c06181c1000901d10005403081481214000c01c0c81496001c028141e210340c05500102c8100402c0071031303403c103914041401001005009a0180030f0800e0201e42c10240e042606020a04640703c0c200e0011581d244903112102500e00a010700400004036000c00d20450a503a00094810103800c0d05c40e40c0c03907441c0c5007242c0c800d0b402d02c00c0583d2110100d403c01a1401c12440442d50b51036014084c0c0d103400840100611814005c8500803a51100710005640340c3c24103607000323446240212521070030f0006000c0c20580040c2d00302c280e05256030300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 268336717 1250 268335467 268335491
    0x304030c0b0f070e061b060703090c09091205072324130f1505090c090711120d090c0801050442020f031611011a0d020312030415 57
    0x40c094840d650544e20088020801010440c841e800f811440d01a54220120b40034038510a028841c0100d8040c0c80000d00e80680d4500443c54084a42c0700307a03951440c204881c40031680d03030048848012001d02d0825505c0407a89005d00c0f00c409802541d503420000301c01c40e054030300400190b503692240d540c02a00c0c003141c62012003909840c41103410262a841e1030000381c000a11440e00c0000c800d00c5400c1042043e848844a1800c58400701c8441c001540000e006003142d00744000284d801c60035511340744a04217aa10a229918081450354000c0003200080802240d140c5511400300280e1000b200c205859444440e54064481a00c05680b900c0c131015070804d0b103c40180441024100c0cac00c44c01d90070008011400d10b5000c0500e4949284c0503000c01c458248103048000441c07054411050004500364445001085503e040341009040d038944901d0b101071788c40400c214000c0311800c965a124160880c40400c0c02c2444056400c00300e000007109120030804030410780d00000c00365900402500c01d88135 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 268337967 1250 268336717 268336741
    0xc0106170313120c030203030309070303231b0c0d0b04061503050618030d18051c050d090507080303010e010315050c04034715010e0d0510020304030c0b 67
    0x20360245403070b00d00304010b94a06841e03105207444c000c540f010441640c3e41c0100b82558000c4500e0101500030040500400d40c001459070340c458100140d12408401c0920002a00c1c4586140c00032190440300382c400e80c12004101c1610000e0001d4403840410690745080301c05c1c084280c0d01181c1a9040403484103010725400762603000c49800600500c01500d40e90076044106c241d0002403441c0b40403c1000b48610500e50048083c0c8076a03075801005042458100141460080007664a550510300c030200074007a8828143d80c141d40b500354000400a14034170704030703103081004d600c8420385000210001a080001c400800c0c12a4041c0700c030b101111901b01144070881b00e0440e807003950000e00b8401400810765a1040f800c0d107a20401e101d1030300d02149440300d80354090300c0039103041101c0100e4100c2c91030204e060410350411800300301d8090b000440c0e00041c24030301c00c0e9003405000e14001e03540304091210401001e0319117401c40504554034141410010417080f884001030b940d8040340c1c0040b5040d94010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 268339217 1250 268337967 268337977
    0xd090816060f0e090f04120e030601060e0621060111150114010c060905100f092d062901020c1005031f0e0403030e070b0304080d060b0c01061703 64
    0x2100001529041001c261500c050402d844020007102c00c000b407400b03443d50486507003d2115071122030040e26082c5026064049108401410400e0702c2444d1005910f0014056040d9503660a1844801440d04040307009070242402d806900402c0c00141d80d0040000a0042d0040c02c013a600e41d1060300c3d0407042c42c0d944011010600e001149200c1c01000f903800a083c4511305024145004006e18410741c80385803e880c00303c082510540c22072000600b40012a11031660720100e1300e0414450000380d526214803800d0125040c28101210464104421540000b1405415130000040001e080c000d000d00c1e07400e001c1030b646810484695008644a0b6000160003600144010484512a1a2030800b2145504094010101805020282001610615851005403d240f84448110b24003802c00800782c41d4100708000e059000388009000c210401e4084907807040c0c001c403e059581070f40b905103500900c00c950103440070075008200c0ea40803800640108045030420302920000e034403030488043d1280300d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 268340467 1250 268339217 268339243
    0x304140f0304290c01020c010b2d040207030e190e010b030103081c060504060305240c04060809070e01080a050d090807050111030706050c040e0c07080901050306030f07080d0908 78
    0x1d5200c6452220043c030300d40002140c0e8540b2440e041c0400513108501313a0300301d0100c0903a0f59440d607040c2511818034146071440c08880e65041102007451011b800c619014001559018680005d041d405150207802c65070f44000c0e0103010781c50105011085005102100d0064441820300103000285100c801350540e8140c81c0c01083c03203440c1040100c200d4030745c880c1c8905100001c03500e807500041d10707541d00d200300d9009602901c0a48003180442c1d03e0070249111500701110001040d80a11016008800079039050741c2040c108401c41d0f4a6000380d892819000391300009441400000104440c03901240303080515100390100d940e0a51441020780303804c074590040c0303245940310340c2c0704020341d600c10b101c02c1100701164000d8070700d020031070340314103003590821101e5041300703100000c0c20460346d04c224440f190301c1444891514102802c503174545001d4416800c44904202000c8045000c6a806000f8541c032400140c04807800c0303a41d1440e100d501c405011410300f0118046c104005095480815403200100d2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 268341717 1250 268340467 268340489
    0x329070e04091401020f040f05100504210b0c12091c0e0409050d020705011701050f0103050a021c0c030c020105130605220606030b0a0b0906040e01110304140f0304 72
    0x103805001d00c00240346101007a50040f0b910340d0b10f401590000c1c0300804141000d9a29655117a080034001c04003007030564001c6000e01030300990762984a5010b4261000e64551030710031070600f4039292191a40c40401030001d400103000300d0a1100164010340104041d5100c0e6040e03042e190307290f41d145a02c509020504201d4070354074254401d0410310400c50300a036120018000641c0143d00e803116480c1050074810f801c09648043d00074801ca40c0c02011800c3c01e60f0103410038440325030420300883d04400e54100018181901d072030201c0c0685000c0d0f010b54100400c6500004001d017490000d2401400590300407402082ca40b0740041c8404e0310600442e48100f50400641a4440c040d5884500400005010142880200840d007004084442d5884ca9003802072001041480c20360500c05a007980161860728400c0c0392001c00482d03034071000e0340a641301c0da084070001000d860381e111240c0505143c5011054001c4000204410405160090480ca1f41d0103070440d01c050003505805540ca01c02e0317001312030440e8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 268342967 1250 268341717 268341737
    0x305011e0506030702010e03070b0f0612030409050402060409140105090105040c02070e0601020109050715030f0b1e13020418050105060702130f0605060301171219120213032907 78
    0x1c10000e00443c0c11413078910000900c03038110903040b4116040244104c41140080c0140191942ca084005400c07150440f225031040141c002466500d2040d417203100d403880d88910000e010743d522001520000e0408503c1071000c010302c8022001c14200900449118050210002c116400d083c8100340680c04550000d100c80c034241222402e400380c1c000c0036941199254442c29000440900000d1b00400e400c1c886000441d003960005000e80c3c844d46180c3c51902e242003074030209640d175070aa420314141c17241c050b280000c000b5008a55040c0c1c001100c02c1c903042c00010009404000c40e501c46801c010348480412450340c0f5101081010b2090b504040e5200346282c003030140600c4ca03907020b1010780f0010340000407200d0b41d030f0700480d819030000d07840329101100300500c541018a052104107041d0b804500c2152030310301c9407244a02001d5060082e40100840802c456016a125a040b99900b86040d000009440d41e03900c4c00c05280e115091040361000d050940c0c036501801b5100c1258025030481e15516242 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 268344217 1250 268342967 268342969
    0x40501080d020d08150d2001020102070f081308030a0509040e06071709010e10050601080a0b0109090e030412081905160f0201120504031211030c0315030a0618030305011e05 76
    0x484000d4890000c5d00c5421084424036590385403a10185803146c1034440900c42954203100c0300051310381c0c05e203045d039004204e071500080c140c000f0061415844800c03981c40f00c0701c0407010590890700390401003051000041d01081c0c2500312000d01409401107a003400703600014088542c07901425912074011404e010100003680e08001c441c1c40d8000c9402000044136040d140606160040109021580581c1d071402c0c801d143d60f20002c05a400b07a039440061207074482c0807000a00401d284d1284c031807a10395505221480c44004c0c8201d80007820030000324440c03003001d810400140e9201011b6101aa94a040a44d100a005000342d1b40c4160850035030f00703070388040c0e070303c508040d600150012410042d1781110309a6200c514071a190059010782d40b140019078544010004032111910b0781020600f0a004000340a080e881c1102da0110700b040049401042c04004641b504900c440000d080c1400c0c08101c007075007481c413441514400c0c0030741d50500040c3d07130f104881e0003400e242021440100c00542c01c01e0100d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 268345323 1106 268344217 268344227
    0x1b03050a0e0d17030606070203150105090f01060203040911040801051e0c1c0905010b1215071b0303092a03020a0503032109031201090b040501080d020d 67
    0x2800040d4948607440c07008007200110f000e0340080081e80315111503041d81c101d04d070b000c1c0442c3d02681000d81c4000c000c030000d008e540d0188225600042d010f201f002010750417030340e054010790b2415082080f002c01a00060304041a06a0704100c0022000000d100d89032144ca000302903003092012030b24000c1240c07035016214460084050168600d090380135502d245408241d83d0380008e00c10180e02c5c20131b000d131100740c21f103941c01008005403a441944c040760a500e03a043c00181c0f48046c0c0d075501c8040d01d0505446000411034401d665581000034040c0d81b054213528050000401e2000d80d086010003098030001240e0302c1c2d240c080f9403c008508141d02500082e00d011400745080c0b865a26185d00e201d8500019540040400008100000000d004a03460300d0010707146040c0035038440c0b10900c040c004840c8000c2c001c0d031520300009108d1801203507450030141154003a0445180040081711 = true := by decide +kernel

theorem cover : BRFrame.Cov 268165467 268345323 := by
  have h0 := BRFrame.cov_init 268165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 268165467 ≤ n) (h2 : n < 268345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
