-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2801
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:46:47.262849+00:00
-- url     : https://prove2.me/submissions/3da0caaf-a548-4def-8be7-320a9d6a47e5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 503597122 ≤ n < 503776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 503598372 1250 503597122 503597141
    0x21309150e04110414011e0515090a12031e0507050a0b1b0408070f050102071401030f060308070302060403110f0c0904020409050a0507030b0c040b090f0307081905060c04060210 78
    0x3140c1c1c1810850740f000030706a505021840a000020070300401000c40a1009044014041c3c6d03502c4101c07618100008120040c014040011014006401d880d0340c0d440700c0444000c1c100c49a00010110054100180400980303401002208048000c103c042e900a20590b4021a40038000b403a01c4511540e51401e0304002030425403401c2c0710842e85c0c2482001d000040e101601c400c1c401044c94a103840468844d910107540712070306640024a040c0710464000724490b100000a08010541c00348404035400144041e51018192920104042003019404204140118000d0781d6140e9040f10303241c48181c5800c03190502c0c03403269001c0c078080c8010b41401040b66501a000820014004015031221400c005a148044859400001040c0200041e001c0d0107034000005240650405080192000c1c1e688a41441d83d4400c1d00ca103041180f05039030401103680035285040a40e20350012640e00b00344040c840700421507072401742c9400a41f2402800080c0c17000c0750310f02d40c010049413846801360303801010641d2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 503599622 1250 503598372 503598383
    0xa0206240d0213140411060a0c03080c0d090813060f0e0409140f060403080a1505060c1e0a030201060503010e06010513020705011416020c0102030d0c020c090109021309150e04 77
    0x603140b860003c00e48111104000041d03011081d03483d191a0071807513160f80304e2803244110018428010165401400d001d041907040c107041303410340c403000d600d03094074080c40d100300c205203091004034020031615102800c10340b4040000c403c1d86546400c801da80c00300c2d8090504001407a4204810024a8aa0030228007107000f0400c00c4400c000c05217002e0300300301c1120000d1a065000800340304c00c05a01514103a40032014010400ca800320f00d4000b465288120311031680320f8400031030765610b4540c0034030500703014007001c41116600c2402d120080e0f807a0011b600013074001d94030300403000442d0f06040c05042c18455106001d004030341e007010704200f01c414400580c640c600e5400c0c000a0300240c424810701508251905880301c0e1391503d00000340702c0f148128608411034008540305603072660000240c59800412100109400103401c0c001c034030b041000020a94061416000094004d4180d401031aa0144401da842c1c0382d1502e520100b82501c0d2440f400f0441690102000c10142091600c020b80051050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 503600872 1250 503599622 503599639
    0x150904060f06031506030203010b030106080405152a070804052b0f0b09150106030c0507050604140f0631020613080d03230a0e060403050a0206240d02 66
    0x80298078003510036900900082a43c444903a58080c102030312a5001300300c0c603c1c0c158595030409003085800d00040c4034007403d02103040c0108040000074040044414610901c91003d031070250311100001d00080304540012080b03010803c46c4840c103904461150b0341111185103000e03d00001c0c400301030001d6000c40341344c0d12942c2c4101e8038003e800016085441c054840080c0e50127050a0845807900050454a455803115140004ca603103001d80103411500e10b4140001c0003902010309503001e00c200c02009005001d08006c00040108101150101050541c02c881c90750758035443d807507036591043e52080c0400e240f10040032a10501260440810704856800e5a42881c099012640581107031110742400b400d19403043c0080881048040800040340ca0305000e000b444501c4481d060301d40300c12440e40d40b842000010b0b52800c160304120701c124000c604070b40301440c1c0f0303040c010541e4000ca00032200501a0a021610343c0c0600c1d0a2403540800b1917401001e0541680700b048008445100f003241c0100d41c1e07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 503602122 1250 503600872 503600879
    0x3120702150910021005180c010f0315060201050f09070608012d090f110f16020f030d180509040b060409030210050705040303090509010e06060304240c0807080615090406 75
    0x1c080a03030f1909030b416001021142500b240030003d55400a06101c03810a40c4a0301d011024000200f07a001d00d0401c0c00e004120b00d01c07071a0704030b0182070201007255007507181c3c400010b480c583c150311084c4141c050504404040c0c40c0c4507081c50715543e41d0300c5408c001441410060014040c1c0c0b076458401010803d0030950391044072003221082481d1684002c16550703940d040071106036018010350b005e142c1d00e212102c1c500010b02ca80c051490150010040c122241140b14030b0841d02c0f80355222240a034020b0445032403a80d00303840244600e050303007010180c40031f5100c00040d0900345190594000c41d807000f010001a551070003800020300701d01000707504505c100018220b030050700303200d11401140b03980e9486030745504605029140e41d4250380514050019900100038003003c0703603a020b80120302240c04507942d0700c4509000f500700201c2e0120500352070030800304000d88189540300c520500c5050325171240c156145503080d1400d0100310744403500701030ba50041e501004803903c000c0a404100a20010317a10f030700d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 503603372 1250 503602122 503602129
    0x21921080703051803101d062406090a0915080307020a0b03040602070c0e060a0f150302070507090606030501031a0f0403030510030c0b0310050d0f080f04230a05031207021509 77
    0x11144002003c0e6280420447c404480c0143c0200d403640c0c2000380303040d0030003c0356000c1d45500a1050112403601c01c4149032987d0314141200c56000008104440c000c1d16116050001c1402e14612108908a6800024408030101c10348100a0b00200f680f2007192900b018203d250b8401042200c50540c2040803200090307a032120305000d0b2610000742d00072440d02c1c6040c07000c0e0003001d4000b40e0a61040e030b0003c009090f0048001681c800b418600561a001d041c503182e0316003045508040700c1c9504080c008120301d60b1680c0800d049034080c60641410b600140c101141005013550714504041101000401080c043d030081908650030078023a41c586956034407810100c0f031558124041c0d240c00001440194031607041a000680411a2000c19004150792580081521440010400d0001042c8114820249011346004100e60b0000f28000354040d510b10030b8102160040511450643d14041000d00700068802280d00740c4254a034036059080c0c0070804c0001c41041c011038201c03c108515074040c1ca = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 503604622 1250 503603372 503603383
    0xa0f080912010c03050a09110f15030f040c0b0a080402010c0809040c050318060105130c050d0504060c0305011418040c051804120e01080106030b01020109021921080703051803 77
    0x41c200000360703410b14604024181c0d94090002c0c4101c90034050300d14049403100c1c3c0000c1c04c41004880801c007401c0004007242c070b051020303403d000c850807003c8200080301d41d0041d2000d1180e8410f0b00c203032207465101c2d8080101c4d8002e080c0078800041410000a005502540540404901031009a41008442000101680c3c101500c4400003100842800200c0040d1501c42090390042805032425605040c04110b503070b036640d040b5004640c0c4070a0b011002c2c0340241c08a54071004614001d100f240303030500f03080018000c20428200068541400011908803200105000700f2000b012030003415020b004e00c0c6194800030700161042a0440c8000038142c2e40c0c9401010034030f20400d0f0b0a041c40c549810b240300401698814242840050302e2101450381c5d00a0f001c0f41500c03040c1c00c2c005085005000100c1c01481480c0c0020740000072124490151a00c044070401124400a81c520302c5042d01e039141e45e181c02400800a082800510555000038080c002505e400101b041500001c808200c0000b490078 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 503605872 1250 503604622 503604649
    0x3140a0201061a0a1e020c0910031704321207050603041a1503060c0d0e0a0302100e0a0c030b04290a0606020d0806091009060e07030b01110a0f0809 65
    0x1041d000813101c50031a00060172a82001220401684000076003034080d45401885061901c034015080002d040740480825500c0510781000d16040c0d11754200003a001c45a11034050f20b002d07a01e05a00e5943e010384000006011280c10390031500082c0c2001d402d0100d20300241221a0041c0503a07100402c2c25107502c8003543c1310354020303030040002d0a45200401025000509440e80182405c0020081c07a10009030003508400502c484c15601c038400314070390004140401c005152405010784e06024140c0c001071200d680301c1003400403c020103a00300c840ba910380b02260000c200703062113281000800c00d24001c4a80c414010002c2201e152031282c1c0400c0da00f02441c80b140b0b0309030980340c01c3c081074011b10700c42c003c00b80042d8001017007154001d40011f4515000106100d20a4100100288100e0700030b040d04802070400080a12055132102c030202d510b4901180c41900107840e001c466202503116606e02c032505540c1e2009040c2403040e130307114219403d59110742940c80550030000700005858034079400d20807 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 503607122 1250 503605872 503605919
    0x30d0f0806150316030605010206040f0b1506070f03020706020a0b0a0207170a030f23060f04020d020a0809060c040b04031202030723160b121b0a0c0b0c0703140a020106 74
    0x1c4c004d2203c4007404452240d0003403411540620100b10000b10300e41e190f0310240d5045103047d4110340d2440c15140603070040c10503507a04005d003c9001010070600d0581320a54a1183e001c1d50380305511608100c0e6140d0803004007900440b04100801c03c0c9200c194000e00826010389015140c0d00e2810421603025405401c046001a654070400f00d481c584c0c9204181c554262076800660304125154298100301c400b810b414403d2000c08644c8101d030f521036044600d288001c440941d101c8001e802d002d04110070450760108e02e400344ca03001882c40c1b15201c00700d505070740081030701c50705041c1140c980042e61410a440712095100030000c80020500141d440d20f4203400400d0f01e2000e40e103030f1107451410046800c0080030400c4a40d01d06101c1c16900c40b05861047c0e803025002c003071039030303900030000110541c0c4810840041c60008507c26403075446148100030714003410707202045848111103400740d0b21a8950107400113100e2895401070315208002001308052038400031582130303140c68100c040b203410800d85808 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 503608372 1250 503607122 503607151
    0xe12070c1518080d0804030302090f04110d0501080705150c150c46051209010905070b120106030b0f150a020d180b09120a050a020f030d0f08061503 65
    0x4032680b00c50800016207005806414070380300030403000d040914041e100405150f00890000d6040c2c9503040b42001c501d100500512a403070b52103500c0708550b07101588251019050100102d0b07000f03400a640c1e02151400340a00c15588100542400c083e00044085402809020015050300310031040702c5000b048244500390303032200c5084c1e1001e4000c031710308102d041c09045601d82103080440b007a009503510f5441912144202e00c000011100c2c0d00c0743c0e0002c05015074128051103004901588141c0c409072003681101c100e1a01d480000e03881d40900801000820124401801458407a03004071907010006413400d00c0760041540066500c070424259035017030003008188808410344c100098180c1c0f02c010304004440020b2241064508120350080f2a44400300082e882500e072101802b469034011400e0030f40394007109915000f611500310304e0b8142c0c490325a401d9408a81d14011944101940894842040c8000031000c1a9a800380041c881c03a0301071301e02284e0210011400004611a00c4000c0c0d2a0b038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 503609622 1250 503608372 503608397
    0x4080712080d060902090f0f0d0b100b13050a060c080f090612180c0d030203030a0c0e06040305030a09060801050d02010c150606081008030c03030c0f070204020a0e130e12070c15 78
    0x31200107c40d0300d90b200c0c001d207039407110058441a020909258102044641c070355901010f03117149090710390001ca10710b030000440806004d01e041074101a07403401c40303e10307079a01c0c0c0d50130302254844c8032804050440708042156105c00306411008110b03900016110906290126200b00d19603182121800041c4c40c050404046052050003d08103015080b15949001402502c0003036807800014690103180f070b650380b07140e0130840c0241c0d107405480c84010b00d03042c2d5454403481c0c002e84a800900c200e002041c0d10700c2011812a000b00005816548043c2419600d03e900e9001100d500d80014019a08035a02950015426040d80070780c40250505840b0703111503013807000700003c50180c2980a15403d400903c854522050040220707900010013010b0709854420003540c0300c409200780f0800031349c4548001038200c0300c0c94105080094210702125640fa514104401110556421840780700c41a0000840100205451000342542e00c3c00ba035040c00103162038a2500c1c8242c003405a040011946800141c1e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 503610872 1250 503609622 503609629
    0x15040b060a0603270f0804060906020105060102061909030e04060f061b0507051512010e010905370204090c020705090903070f02090414060c18010504080712080d06090209 75
    0x400038180c0346010040034803105010f411403c003400082c4c1d01c1e954030032042024808000c0056900700d41013000355944030b0362808040c05004280c45490003650800d0001500b0f98000304e0800e00c58071960304a100038035008031b140d500030000e80e01c0880901400008000c2c460300e8510a600c0548040c05440041e80e040600151120407000c0d081c0c604540d5108510002510118550302280d00c00e4036a4008400d060b090302a9030300500307074209054446500000380949001501a0403100e07072b403204004944030600062080c40000ca20107d101c003040c0c1c84090589240c89407080d120701e4201c0f00504058540758580c040c0c03482c50b1203c1e001030703101c941c042c402498602c1714a071308941e400004516129035030351004115528508081e1046074910b001409200075264000250b12514041e00c410b860484022421900710340c201c4c03000052070043c01d52555001d541110180c4040302c00074100c0602d80111052a4881d0b00000c0311a40c005004006088030342d0b00454004d400c80c0440940c0712600078090 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 503612122 1250 503610872 503610889
    0x421030b01090801050402280b03040b0105040608150c0a0201061a030f24010e01030b13060623121302031f0f020f0702040e03194b0215040b06 63
    0x200c210b59242409000040e6200d42304d0b03403500082030080002c07007201072100191094aaa000450108000040008000342c94048a0582e0f500315010005d03036884942c101c0e5507440e00300e1300c03010810010700800c440c6850803001c1e01c400442c2e07100104080780c07102520380c64022805283d07296900040b0600810303040081c100e40d030284240035141d90581902c6032a241551144401c0b03414004010050080c0764481d410460b0165070141001001007000448000184007600c14a40003640d04140482c1d0a012007106c6440171203403843c0c05052000c2008130000350a005007001c0e99042c50203044c200180c5043c40070850b10107990f103078221560401c8901c030050b11800281c900714548100800450403048a0030358882ca9010703130380090010344e2010301506d107102e04d03141c9246002d592943d4081943d80041400d042070711b09107407041c00d890301e2076030b20a40000304a5400d4020801c110039450104c500912103400102520407a808159000c500b50795050098030b080d940c42801d10100302050500c07618 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 503613372 1250 503612122 503612129
    0x10e0c12100203060303040e0108100c03290a030c030803100f050d0f110310020405150403050a03050304080d0203010e0a1a03072306040608040201120515090421030b0109 75
    0x1006414104000c62158a03444481c10301d1039036a80c0800412416101042920044c2c11450b0313180305107503140c1180765900c3c0030039100c042106040c56000f034200c80c8240107244841d44240b89130084141906054008055050f803615003143d014032000010803964600980114001c904041e66814488800f080100d1190041101768100107020015900c41c81e1545184a40066448500c40f502d403401680720f01005111903410b1255444241c1d1b072020030741c000c00c03c503401101c14689000120b02c1d544114056407001800c9a04190074403004030740154011980244a140c0c158906200065010102d1b04203801401c0c81007000401c10180c0c0e18075101d4501100f025014083c12031303000300c00003030f9a54150f01450b2403a500e500d011002d40c085c40f15242c0c10b0840010203a917184d54581000426400c0d0884060307000907454091500b00d040c0383c0c07003400c2c042da4a4120003100700030380d1014055600c030090710444200c1c2c030005810941c4160030122002410300341e40d000c01c0c4c80780307080c1c00100f48018942 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 503614622 1250 503613372 503613379
    0x1201020d0b100f3f0e0118080a0c02030f0102071110032d0b1c02090f010e0606030c1b070603061a190915053402010c050c12010e0c 58
    0x1015500d0740c1d900000c0300c00d240110072409045040360580d40c140040407044104601d10003010004d02d010701c058002001301030509000b001501201540919107031400070b070140c0070500401418010b2481410008a40303400581100d018000342c4803002c4c01c80c5d00c4120705a4001d0310180c2131900c11b103081c8910400c0340c0000e01d01070001da48800207412880c1d41d680000311503204406094251550b86822460144200078000440780f02c002c03e4100b070220015404074411080000010b081c041a0a0494162203e041d4941050f50301e110502c04241e0000d000c0d42d0300c800c000d0141400d00042100c82103680d0120101a03e130341d81c90708001506032501c98101c12600c0c9143e0380c0342600e501e044015110784900680040320a03500c03401d01501e00c942584c001080b03c5400d040c0c210364094101d401820307080d981d0100b204d020340900f400c900c2020410046c6810044264100b50055803050848203061030085003034030300703849095000071820100308049082994481c46016100103050003130725600d03401507 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 503615872 1250 503614622 503614637
    0x3070605071e021207061d49140d03021905090a0b040b1306051303111203040824010f06081b0a03090b0907050a090b1201020d0b10 58
    0xd035100321040108602c40014071076800c52400a643d41c4840c0c146940c5848010380d5a000d440301402011080000002000780c14400c1440240d4240a601e8107100c3c4504101c030310300e4009440100009441454414200d00b0f40700c000c900c4654401c080320b40c2080e105020a910103440303070400e00e0604228040c5801414410300a40101d2420200701c0d03500c002c280d107131031640c459581700004c0ac0d01e9815040f00155610104021407240a160b000341410003100a82da880ca0344d0758242112548541012401c10741c040340420070000e0329814612000c40342c0101700721912400040b11502e150480e0340090301581c00711480d00001806205030480340c814403c5184565030418607948903010700391180c02c0400209030000350b5540e0a6081c1e00750040c03444422642da0b1150408010040c20100d80c0036107015203440081020b2290001d4401d0072254042d06110130f40d850482d01c0c00c001d0880d000f485410151004d401e1440d15820305c002c00c0360308000240005d69044080c1400314403800b249102c024000360 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 503617122 1250 503615872 503615887
    0x901170108060c07030c051509120712031e050c03060f1c0b060102100c05040e011502060601030b030c030307060e0606120a06050717090706080a020a0c08220e0603070605 75
    0x1092640d801080d40100f55a5820185401c8405800c0d40314040c2050013005500ca0301c0c075212080a0340102c152004032102c0300d00b0ac0380001000e01c209035004042d00d000c0e04004a015000307412215071640c25403201c5001340240740d91142960811203044551080c0042000b02c1c0340b8010b0604480810283c4044a040303120480708110204004030103800119034800044403a0720801c00007000c084030040610100c074aa41010b407058001d03010310204400d0035070022541c0d01207801181010072090b80182900c2e1509801580201034802c05990980071303201025500f514200020040c0320310541002401d0602c80704501d041c4200544603620654240d08281d01d4500c001030005501500f0200009240d03d60003c2607600b4000490284500300d04041049903005011030400d0484940e506c42d59110f40d5801482c1040f4441c180021011420080100340415044006030420301c0910391941c080c0e0407040c802078600350072039022510010040c070800c11142410700600000304202d040003802c1024 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 503618372 1250 503617122 503617139
    0x230c0d03060f080712240605041a01020a0b071e0207080d0201020a0203040b031e2401020606010507060f060503031b160609050402090d14010b09060a050901271109011701 75
    0x14402c96101c3d17078045014a06010405001c0103080c0c0e416038000c0701e207140041200d0050540c501c42c0c2c2c0d00c154504502c01408808010f02c11066480503806090705c0d0540e41d50303407910000d01421100c01c02c88034454001d01404000d240051001c0c0301d40040c0302c030610f0040e801d454001250248011a4010300c50b031500242c000046c0d800799044000719640304c2d5103485540c0049261079000c82581001c0c00140301000c840001c10364030b00d00080d105141c030007040400580c0d8850040c4c1c0e24500080c01080444089103140d0f2008080459041011400560700c2001030b20715000000800c2c8002010000e40032503050801500c101c0080103030000e03860030b140074805422402c107032188602640d0009210b143c9036072900c60b0020355543c0315441d0002c1c5e2021559413802002003140c80360044d144400860401d1a21081010450700000c00c4140b482c0e0800d0300c26600700e90390b40001101d2940031541d101580086000d031649120355031294580307440380b00000600d6200d45441c03000050b01c148e00103000510 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 503619622 1250 503618372 503618383
    0x10e071e0f0e06100c020405041101170402010819090501050403020c12010e0c1003021201061e03060e0414070f1e060305040c05060a120e01050403032901230c0d03060f08 75
    0x24101d52090b40721a071160143e03a80b98480d1002580182341404210403c8920800d802c580242a601c0d203460503c805c40102c8041020340d0081d0119582a0000d190a50740508440e07800908410209845600380e407000c9c2982c000340c0c0c0c105d025811449a200c181e00f0620044941c008140c40203015031502003c1040e01c58107c01a481c1c040c0d411101300d40c40403030103901101c689482201d499000b540e075030203005002d140d84003001c1e0f400740d404404c1d003070030b41c0d10a0045006a40e00d0716080c035426140c0360b0303a0502c020510048c21146000e51040022a0020807180300014010040c00c2c40c0340e4a42d02e0f01641c01c101407034220fa030030b0504d40400e0001080100c200b00050f2401079610f5503035420018000c0d04d20307000303820300b41d4600c50034005455101036064000c240030b188240c40030301c1203001c20a903801c1c0c4015480c2d600b48030040d600c0d5810500d0340c1300e41c04e444001404288842d004804522480801c1e03444192038040301e5001a0105003510390601c5104018903072071150406071418000c06a417a02c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 503620872 1250 503619622 503619631
    0x90f010303080406111c0f02072a03050d020c1807051b0102091009080c03030a050f0906160503070507080c0a0e0c0405060c1b0d0b0a0905010e071e0f0e 67
    0x10b41c0d00068104076103a407201450100c11480641c0310240900c124560003525110201c40605045110340901064001d5401d45a8800c0e03101400807011540189029540b08006200018800c00000440d5051150b040749a01aa010300010303110f079428003074034004030185070b03e8020040c4204000790f0742c024107441c01403000e80d00a00b01423442e07004d0140039010342d00b10142d0090140f100308118a42020302c134012105440207843c0d44e20841010035881c0d001c1c0810442c046202040040110904a4010701c04607200030721603800d10f1011808551907220ba10000c5a85610000e8490244102040300c0d600402258000303045980d1040d020894051803403007051035600c10080414010b00340d203020f4602401001e005962552051003001c1d030344444141c03200340346600c001070005c00d80c1494055149019044124885c1d15181d265015000f408411000e68403550703102e8200c0c0c4048007d0000c10f00410031540f0b0110000e0b1125403040f07580000c0d500c9030301413900150042203032809100450752f22 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 503622122 1250 503620872 503620877
    0x90f0e0411040c09090c0c03030f050c030720011d160528030b16090902091c02010210050a05150f1e011803030503070908210a030906140a0506090f010303 68
    0x4150583c042900d03002400c0d04015412402c0211542549501103640030034140640c0d0140440c1907814180c100f1503c0544a07805481800c20000ea01503009045c1400418440015021405400b40c00b880c00c5a2180800f040448000a43d071803401c1c0c0708000c6072914102011100340384503d0000014149644041c1e0300101c90940b80401c0f00c00024654a4001141c10004440e0301d45421601c4400c03a01e00d0080c0c242c00f156102c07801082c4d8211074404d607a8480006400c0181481e030f80c6034011080703510340104078114800c003005c030b00401d095400f605014170600e14001c00d49040c0420307442e0a4810107140781e402001103958011150361940035103011000c2d07030701c002c00c4021f059400403104104c4120030015010403000d0004205035024001f0351040a40e070b45d480c0c1029031a010250f440f0881020b03078103000180d14031103115203007124001b0142000d0b10305000811034010382d5840e0580300910701c41003402400a0801030030b402207000380c030360024040303803016141d1408030900da1405a060002908 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 503623372 1250 503622122 503622131
    0x60111011503080918040b131e0609060c0f09050d06020c0f0a030e090f070f0521040b070c051e1204080a1106030c0a0e030304030c06090f0e041104 65
    0x150a0294084020845200c11001c1000d0322400c10385210741c031890050780140c0c0039a9107124243d10704075441b4000c1364844410040c0744c81e5000302c4110608111400c0e5008c4050038071010166440b4540140504d1040b140425440c80f181041d404441e4941101018013070720500c284502035014007100142c6204031641c50b2120b003c3e0802d0402405194610103041c8500d01451015801c0081c1400708513210f40e44400c4a40e960809001104006945603d03868207004013081030304d070046510749840841c6180090801240119880100300d07034111110300031030b80000380700600665441c125882020350505100d05c50056441c03660b2030200b41111a1000340d83c1034440060f000920042d0040c15004407030700d032601d4851070020f403a0300c0c20308021a0f1400e0310241000485c1041002d42c0d10802d00311062904100e4060301c02d89a20140c2d2560640c58081044003000059900c481d00700509010340d20f440380e19003400100d100485e00303900409102a0220200400100385018401d403401c0c0c01e450228 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 503624622 1250 503623372 503623397
    0xf060507080c0304030b010f0f030f0204091704090207050613030e19030c271b0c080f280c08040501140d05070201020903240115090b0c01320601 64
    0x91840c0201d91a090543c00002000010320140003003141c1a40d07402c14900c1143c0c2e544403e001040c1c0498400148180501207248000d07161590111076011b00400b0410707102000007008071559405608012002c2c0d60114585060050820605078003882070244011803505584011300700f5036100d41003c1c86054441c800110362103c0c010010005c41e88079a945003150b8031030514050040c01031070060450070300380c401e01410007110b003c0d44652600b458604440c4000d000000c44070321013021000d40d0508010400b82060703190880050810103515983c124030a82100f03100d020400e9540440310803c06404040008a4200c13400c980480e0f109091880a007a0240c1c00362060380101280450068641004c00c00515011740003003809002c00c8056400c041000e00804403c04545011404000c0704940140b02d04030411000c040c0c215800c2c01c00c3d6141d80e039210109142a0b01c09400800300d03945405c1d0000007102700c0d180c80052207c19001c101d0001403142d0441e40104030003089d00341004181041c20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 503625872 1250 503624622 503624633
    0x30506150d0c0306090311070f1706040f121103030f010801060506030f0c03190e0a0501050705040e010b0c0102070f050703020a0b070b0f0406020f21060d021003020702010e04180b100f060507 84
    0x1e0061f503020780c09541c11a03958203181240d0b03080500c1103060015001000707030100c0c0c501152180c031440e48100d442103591130540700c003240300018618920603c100050b544004502c1000558420380c0300744014045503051152032400d4501503840140950414002d009070320304000201c0340c0c4800b414040c81d441e5928120025510b002d0700305007504040c80c0481d1420000404545090711070300960080c8403079144c5400032201031180b44150700d5003491003c01401429103200007003000c030504500250030700500d0340311010708140340035044a56038820500bc00850034003144807001010480c01c0030f070402013561240125440000c107111800034200d00010100001641901d11821044210380d448007161424403801c00c09043c02010f40e0f0300140005801071400b8503004a10035030107009074600b081d0502c0213030007a40200100724180b0130040c0002046803a94424000c0c014410040c001d21490181092882400c020f03107000c1c40d60700880401c0c4011800c1214003411502d41c1d140c00d5030ba880311030405 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 503627122 1250 503625872 503625887
    0x3c0a03030504050a1218170a02060d2d0f020f04052808010b040b03010c1b170a030903030f2703020709051513090f061d07030506150d0c03060903 64
    0x6021000c62061031455940c00345280e48903030106982d46c0b014688890031088440b600791240c0d201e5601245192005051500203003400281c5244041b500600407a46240103804110340800c082c0384004150348000010b001c0e044601c4150074046141003a4240d070003805206901800340106000004a0b08030600300d007094118041d03080300040040d8440362035501030042c008005124030b0500c00c0245481c6410300c910300e4040000d0700c611402d01c1400641500c49101e09005450551388500e01c0450b00c030402009021001d443e0307030001580001e40c600641100c5680c60700441d824540060314003c000c0354500303507459440283d14000485600d260803840e060040d00074003400c600703041c240f058848009085050600c02202c4a000c40e000301041c080c111240814050084001241c1c5a008070714150b0107070000c07100030760105a4072849108400e203044c0c0d85071700865965001d03104010074064118070780b41441100f15626112540350b0380f44c0400004150102a00141c0c0d9010362008040c040d181 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 503628372 1250 503627122 503627143
    0xe0f031009050d090e091b010507050304030b010e010b03130605060f060714060106020a03120518190201140a080c1305091024081b04083c0a0303050405 67
    0x140a984601d1800e9500c82010250b83c20108022880c0070540e40d41e8482100e21030031b0f07100010181d110b10380004840b18010100b0480c10700908120641c0811024001040514090031006c1e299500d4210007903c0749605910446030f551051003406102d0101c0006c8402c0c0d550012000300311500c1ea1000506445c0c3c1400040703911103000a0704904208061000100e0b200e6840e09071500c980e42c034402a80c07140307581c1038010000342c0f03030000d512100c101640c00036401040c0101022038080d046c180881c0b0b09800d124455510810101c00726003150717400740e52110320321030400f41d96080540c0d048000e071034020040c0c04503c9004000c101030081110884142c0020807006041c19518101094820b41c105454018020203810145107c40207000c01c803074407122040141d940b800ca540d90003038030b0600e01a200e800c01c0d030180c104000c00610444c040200003000d480c11441031209407580741c5d6070607888034240c008103111080d100110050b100c0100c0e80c4145585c0504020860307950b50318215007080d05012 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 503629622 1250 503628372 503628403
    0xd1b030e06160b060a0b090102030301030f050a0206030717010603060602073b01060e19030f05070308040803040f050301050105011403090c10080a1409070b0f090a151407030e0f03 79
    0x1081c0800f40030914107058014042510130b000311170b0300c6000501d041e00ca0140a503016a000b00010400280003d10403110203000304151140096694001100c6034819500800080c1d581c5460b40b0244d605698281c1c010085401c0801000b80780c460040e455080320b00c02c10304c0c002a00ca202e01d14003144102c400a00240030201c0f4410b40b01140c4000c0385501080c06917100203000051600c1e0302d03060207101184124420180850b44503d10354070002ca1812140d8121a00d00034000004001307417801001d40080e0110b80301442d252802c3c4a11241c030542d565006910903818080100300d2079070050072501540502c610030b5a601e640714106203242c0003c2c444e500f03400504c49003030300070b00c2a13010405900842c0b50076818002507001c0c08482400041c207451049081d00140810804070940000400000f8a081e000701c2c1407664083c00070f40449107540c0680c0c140d00d03292070341c0d51007154014580c880c0c1c0150558060704080d59500c00410012902a50901609001c408841d071036808000d4125003000c80d6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 503630872 1250 503629622 503629657
    0x2060c0a0216030b04030216030515090102120702010618052703070b0c1e0c0c060901030f09081b0f070506130e070c1202071a0304060605090f01080d1b030e06 70
    0xd113480d00f4694011142680103004480765440703040c12624551040b680c002009101c54a0600325101d20b089001c0c0c02004259803c200282c0ca0103000c0b5941881100c0700c1d0000140c2d0703483c2031384240c4018081d0342000c80031072a10301041021294050703a000201c01c11a40f4811841000c07205626500c070310800038040314401c41c100842d040d800c0000304030764a04002400303111250500221450302074219405c10540152200069504210002d0410f1810500d4042640d41440c001c10007140d00035a0280e0301c2141c006088181c1501503450ba61121030004024045101c5011000782c41d101180034542c03090500095044d000243d200002002e0b02022504082a0a1241d4068802e140480c41221641d1031850340e02065400802ca540407240c00034801c0f27111a9103000454042d610040c01240d44503554000442d007074035500c2c4054400c04901005105a5042c005080d152540c80c1c0307070b407104015408001c2ea403111000303281900c002d545402d00b075106020040014a141c0030380ea10300301441912 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 503632122 1250 503630872 503630879
    0x501440a050106090911070308070302040b040902040806092e02120901051b0f09091306291512151009050f0402040e1b0708130509060d020102060c0a0216 68
    0x129407001e8101d800c283c83d400c01071540c500340c40c010384103070b00740040080e04140500f502083c0034004080e8070010710310b001490151114030600a641003900110304c010b41c0480d061201d6401000959000084540140f10407182280d940b04101c07004d061401004541c090425400c00b00c0c1d80645000155064001e0403a18114031158001e24084604102014108001c4002000a14102e84410300c14582140c40d1840f03600038860b0070080034100748885101c261100000c1043c902c94101d40e0002007030007002d180c0c601c05001e003003001501016846040d102041c0801291103008940001031140482c04840c1d440d81c500c000340394140b42000350805c01810f20380040c564031500050aa580c1103030f00e5103140041c00c0034801280602c0c02691f42c0d15000c040031035000c40d26141d111401c800d1416403603142030031680c5c800e4050303045910074404400c101c1c90180310720300d07100c0c4116510541c11303207886103019241c0c0c000075175594020b8405461103400040222609209110034201c1c05060042c010aa565 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 503633372 1250 503632122 503632141
    0x80c0f060c0c010f140a210507050a0e150304110a0806070903061107050111040906090e06040303090f0515010302040c02150a0209120f0a030e100221040e0a0e0106050144 75
    0x100c81010203014040a0003071f0000300c0389108050280c115681c940c2e05004020310140d441040400c4040e5110350040381c004124040c20340214030503442507a01004202d81e0303000b8842c0310445900b205000380c00202c20000e41d180d0108441044235007060700441c90800001c2d12030072910030000080c10079424444611803800303500004000b15401103408107c0140e0b581600400c9032300c00d00001485402c1000800c0100f44241c005094050080c800e812420316030703035516868054150342403c032140140c4010000c0d4a014071034a40c00c901c050010f050368108240440080724002041003880301d41c0410418100c1e00c81040d901102d0300540b046681c0d0070781142805a8400e81d922040f00020340c0800e50034000d051110902c011207245400a0a510741405980c5040600c40349101ea40720308244400505800b0304000305014034412a00040c012041d04031440c2074580f9a003041c0c4c10b01c4048421040b500705560a005480c000d01d05000c2c1421400d88142d41d8800d05c0004100189500e40080c06507110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 503634622 1250 503633372 503633387
    0xd350d200a030e060907081c02120d091b030f0f17070b0405060a0b0102101a041b110303010b0f0d11071a130b1f0f080c0f060c0c010f140a 61
    0x25441046a00c1c9039240303000a95602c030346d40540c24041d048030400307a04111009031445140c1c11140190360340700e448060500c00c01e801411242c01c00c1911001943e0034000060510b1207a00d0607961101015411602c840c10800c02c003a00c0108086603a804140a10001651240d940c000035641550b50301c61500301001d216406039803e98042c000c80c00441c0c1a40028801c40b0724416040c2c014040300c4160b010050020449203211080316405046181d906a42e544206c0c260300c3e5040d250b120035040a6a8010012a001c0c84680d10941c400c10043c040b140004040d5101189045203090b42c803110704680030064445c6600542050402103840c0017040303454044e200001cad40d00c981604450f6030310070250411548048002e4801081e040c041000110420741091a6001c040c0000403216035403400710400e160981d010f4810341d00a41d800726540d262222444200b088211091400d10f034402002a4403070a00c0d91245042c040c1c080c0b2101a194012085056010507001031291220007075038002d0b01c0355 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 503635872 1250 503634622 503634641
    0xf1115090d110f12070302010605090f160305061513090c0504170a0201120b0d0b0702070f050f0a14031002070b0403110f10050c04050d350d200a03 65
    0x98100340016265180041d151490540c01002004003d40102d1392040d260b00102040d0219500c0744808112900d03070000313007070242c840c000b03a0218a15146c200000041c0c402800481018104400d2185584da00b9040329a650307d1801e0860380c4480e2650040180401c6501460381641040200800030f0742082c0a441241d9a5003082172140d0355015021b503c407030344007400902083d50500c0e5002d00003c29404010b0b006406446d0701c40e6401e0540303d5081c044006c9500000603884010148911103c1990400040c041a5280da83c000f882030006501201a40146800101a14403802c030740c0c1d90800840841c2c1034a03550455850311030382440144e0341003c550070350100f4030014050050300800030307a4400a0318203001030b065201002031440301810011b044003c4014003400040307003d680c0c02c8507410045100f8001103180000320f003001c000144541c1c1d03002072030700300541241c1501c0e502c80b800c07101490009039001640d15007c840070110102a03001c480c1402030301240da11402078255000501e070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 503637122 1250 503635872 503635877
    0x5010905010804030206010902070606080102072406030f02040c14030109060e0115121a1306080c0306010b030406111e07061d030a0c020f030604031710060f1115090d 73
    0x91500c0318019205488140c1d00100142d0048004018003842a4085e0089a01c40c0c280860000e0307440c0c06207030070380c2c10001d0240c811002924000001d00907500300361211121201d4184102407564a82d0062170b07907213100c00707030250341c880c000d51040a11801e810140400d0410b207460312540c5811504009008a000742282841c2d484008a0401c4034000000c030500000d0b5500c3c0e5030b04030140b2244014001ca840e074203005031038040904070300c1e40d00c00482c6203190034500d41c002011460801064501a50300c50200e000c0d0300003500500071606010122588030f13421080114508440c00e920075814401c4000c8a043c00000d401c211044c007141c80300030318036140211001d028036240c95840204401ca054150015a4400c1203d041d4850144c0500307055640001c00c4c00c0000d0300100c0209040c080101d03800c030300160100102c0d0b12050002c0c0c10203500070400700001171140f414000c010306101e41071152102408613001c00c9039400030080090788844012296000d015080c14404c0c5a030390302c14903280102 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 503638372 1250 503637122 503637137
    0x510080901050702071406090d0204020f1e04080a0b091204030308010611070b19030204050d0501020c0d0806060304020d0f1b060f02030903030901180e0f07080a1a0910080f070501 79
    0x140c0f2403001030890305446100c1c0c021040c00c003807601007081036404285500d41041c810b8080002507520b030f101504c10094020dc60030b035980c651052040481c05c0500e40140014014801400040800105950705550003001314116440d814038840c50641c1c00b1340310076545513000070003208040e07008030107504903442510f60031000d1456056803038a809860007200d902120904c5a1a41c8850241607c0c100071181d0400510300707074603500495191005414140d82d01d039000910001c0041040040320303001e990345c0c6001442400c0078000658984005007010303104038218002c0300c041c800003080c0c1e00d1031540e101c14000d00d602c000340d1075044840d11740c2c419000403802040201022500100c01c070b41074040300402562810700075800554400080ca030889621641a083c0070038030f18101c010140c01406619012005864080c030000c20604000702001c10483c02c240290300c551200100c200d0058600301c6940c892541e42000d124084044d6501103002d6114115040469000c0410391400351142a070741d000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 503639622 1250 503638372 503638381
    0x170f010e0c041406090f1f08071502060c0d0f110a0c021c0206120c090a0b1201050a03050a02090a0209030d0e0f0604151b200901170a140304051008090105 68
    0x82c3c00450444003150441c000c48001180d050701c03c0c0311603500041e50b6240000c030324060b82d6112a0340004d9007000c10168007400c2c090080880c400307000802a60300303100800051804600c031008500500e02800c200ca521488150301c4100c868102c0d01d500c0c1680d207041511801c4256006005002c40300d17007a40101401b43c100c0e00d0201d00e8040040e66150042e0040e444d18806010850400c0c00c02024480070040034000912156280003c02000b031011390440740c0c0710072061111080d01030701a4030030703881100718003800c200040700402c104403004e4044405a19564800c070012002e071083c8181c2c00d80c540213011001e0322007600014841d1107130350169042405866010300788203041c03080740903003000b9881c0d201101c41c480f845210620350603202c0c103590011299142c0e844e01c1032a23001c00648400c0302c151003c490342c541007021002c0d004081000c003281543e8140071546454041c00500a009c9069a140c001220031040007210010600078010000d0314864280003000c500c819200791586500300008a03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 503640872 1250 503639622 503639651
    0x3170f06010e0d020d080a051c1506360807080a0b240d0c050103050601021c0c0c0b03130b1005400618110301170f010e0c04 55
    0x461003158103850380032600c40602d0802904000001003260b101040d0080440000c90010103445601615210940ca540005d41d864041010402c030389000b403840c0c800c600010301c80c0c038000d1000b03c41a81c180000304603255031200e00c2d5050303d030300519a0081982e01002015940d003500404558500082e1a80709844880480e200c0c1101c0c000500b0a0405e6808900d1065595583c04a440c4860101c503180c41025004288109810031095030740f020140c43c1084113581500403207910840c00d2000e0280080548000040320308c05080c81402c1002404184003044843c0c100f010140c668901da55480e46080c40d40001d81c0820810100c40948440f40400d070017030707031020286050b140000c290050b5105209101080022041d00904100035202c0d2601c003104980400c40c820f0300d070003510210729075003805074024081610700c1419150916180c4039001c0c03000c3da681030f40d0640b211a2810300000748100202031030b004e4110507081d46035280804400f140c003800a1111117100050350103009411803210309 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 503642122 1250 503640872 503640901
    0x52a0c040c051c0b011e02060402100c030903060213030f050109230d03020d020d0c02010516021f051b0f04030b010e06031902060c0d020c0a080102160f0c09090317 72
    0x2602000d0103c1d41d101440e6828507005039a40e041d040c98a2102d0f049100700e00d000b20600000580c005d6000305c014082542800d49501c0e1202c8082e04100003000d03c6903600034019070840c44060a26540030800010403220302c81c0c11030046402c0080f11411080303505099000b0325440c0c1c0300300c840d1510001e85480d042c10018951911651a1018250002c400c170740a4020350701c07228001c540036a0030083c0c03c60141c10f81c8203100c0c6845866000107000e15040041894400c050940b060a40d8405600d0b420b018441d525a80e140202480c0046129201c90040f0700a2032841c42005150440100d21840b0740e017081d0015000300d034001c800c04201c5036a9610829009a0140d0301543c040d00303e16100f82d40c1420310524010520310140182c0e160110708100d250a0400754a680b0005811986160b40380c0c1c03a14441c00f4001d0084c80d0300840c40d00404540910760003610580c0101900c1800c0200014480000e41c06002030180a20610815010303140081600406c148c5c0200d182589174081207049d00700801 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 503643372 1250 503642122 503642137
    0x10902060a140904061203090602010b1003110c03030108061504021e0a0e0a15020132040c1805060102010c0c0209060402091504150210110901052a0c040c05 69
    0x112071030080100402c0740c601e0315205003201a00c0c03040180c403010f6180c9104420040030700301140804480b280c50001c00401d500e41c0000c045a05040300c04456664031000e0060100c0c041c10001008600c4404403040c60240080001c2c1c0b030701001c0700004140c2000b01e8118460559541840414401c0f1744c04c1000320f006440041e4800e48140d0071101e4240002c0e402011410080d013002c180009107840096000081d60304050700c1000e40c0301c2910040c6409006407100d214070000c4040a45228151490034025a001104100002200850184012070761008040c00f01e420032000c0c0040340ca00e518000e0300050b140e2500640c070f0300039462503c0c1d101c1d000010381c007a402061054a51541c000b0000603401a030322407940300012080310341a0329070201c000d000919812071414100c880300074000e4109518130740b1007a00541091020b0340300d140c50a00b243d10103042401e05d03640300e18515281d1030140c2054590103c294419103000c018112001984190010003140c06001603001c80b0701c120b4050103002c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 503644622 1250 503643372 503643379
    0x140c010e010f02130e240111100b030c090606030a020a1407030c021309030f05031b1c061505030609070504030b150a08030a0e0d05010e0d11010f05160c0c0512010204080609010902 79
    0x186d066111a003101400b000d1141403602c1003405080105a6040054141d4404085d0340d540c403e400c03117801c0900440c000240b04446140c09032a040c000b113882c80c80010003424851350300090784010a409485039200150104003030a0f101c507214034000d42000720380542030f445a00c1c600080007a20b941c6004141c031560785a52808220964000d00343c56035040500350302c8100c010b055800c82240c03508009040d540c0701da031201080c0310404039518001c030f911030381000f803184c21021745c09400795406c0403c8a4001c07406a5141207a50f65086040310640600c0d00002d14640c401300c140004000322504080a140040302d00000c015540c1d21b210b6901c3c030421200c0d50110304a0b0480c00500e107854103007411101e014000204414100042e0142800c6400c004074012030b460a1003869096070034403a61045107841c00c01000360303080015169001c450040f6808041243d80c601d075808200c01c4004601c01810b0183c458480300f202640d210340030390401d001e50703503a0b40328203800101010014010001a1340c0c024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 503645872 1250 503644622 503644651
    0x806130f030f0210020705070f0f03030c03050f040312020307020103240e04210528050906090d0606080c18010b1b070b0a030b100f140c010e010f02130e 67
    0x1ea03402d42d400441d0a01540540c054030400107500070f19800140b91891040000e004e41d9405d00d104841101116040164002809441880000d4125607508100e07901740c142203840340341e51000d08103503120343e810003016256541e9045650907000809000e2441c03003600d09010b5525820480449120502840d600205130750380d0802104800d0044250040c0c001c40445138155555603003000daa0a00700054000618000303542c11140603131259066048000078039440c0d8218503001d0080c907030700808040d1171184800180c20109541c9001c2d07070080c40faa1200041c842d02d55111031480e2164040d60b000c0303015036402c2c080c0c842d61528054a00c1e041e6201191085d060440d155141034440400e01c1500710188200b4001040600c01c0b80302901c4a50200d80e40852010116000e0200c45405800c003c0b007480407241c418010f003500000080800503007800c906450718141c0d948107024003010f42c142c00595280400002000c00f40d82c0007408102556a5900c00070f6542d8003181c8000c0000311031820044212 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 503647122 1250 503645872 503645903
    0x50612070512030c030703080402101d060a030b030d02070f090e03030103030e030a05060108160e0f04350301030606051e09040212032703030a0c0b060103021303050106080613 77
    0x25000c4503442c1084404480c1840b9000a455245900070802600454a0402000214980b5001d4500203542038a031810b4406400f010b01074400841d8444184110008140440003d1090303111055128001381200c200c45403400b030103500c030b2040d8001c4000d107480021000c41e110f10785001ea2010401804011481e580c070b907803000c0f40e500c43e070b43c0b03425a4180540100e200100d502000302c01d028001c4880946400c94500f0359000203000a80d000400000045041186400740402d140764090342001c5030540c3c542128580c1981f4050402c3c1d00031350a01c0058900351000018006141030301e10601c4100304180d2140304020952203111420868030300c000301050450700380400510b800a1002c0c182c000818840c03d910350540d0010050f900c2c200c83c4000030b90003018500940c4040b2038005401443c903001000c0301c01004c05030b50b0a000f80c100c01404011a10356403184c0c0c1241c0d00d441c2d0300102c41c03255580320b1924138080c049a220b0242180316420108010104e22808040d07583d5110507083d051010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 503648372 1250 503647122 503647129
    0x606080c07020a080601030b160804050d2d0201050907120b0a02090a050603010806040c15090b18031e010501080102120630070515131e21060506120705 67
    0x122941c02c82c0c0101e5640030000b03440b90304001003406184160f10b002c01c90724020305580760181869208404004080c001d2001054000c100064100301d10700d01801031650000b10b81c03c50b2070141000c800c04011a0403044500c0d54103600203401030203100103641c100c42d9070f11885030700414042d10141c100300c112008107645102640c010320034003501409104ca0306680b00c000481c16002680000d2640d00124100410049404a824050441c1d15a03001f0a1038400c10b00400c607000b180100e5110310710008844000703501e25040c1d018002c0004088401150204182501d40c0c10b204880714515800c103000443c2000d010b0081d1070301c103007244940340042d5444204000300c522440c0e0700c00048014100c1c960420314840c484a14134158000700502c811813400d400e004900548200c0c0d95810042400412410045a9404d5045810072441c072158040303283e090102c0205203a00c2000c40306180d03042000c008409120800081d4000c8400b00001d9969909112000b0310400308403d0310b4104030740602240c40c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 503649622 1250 503648372 503648377
    0xb1003230915040f08030a06060e0405010e0c280507170f16030c0501051510020703021320040303080a0c05160b0c0d020d0504020306070f02031603050c0607030f0b040606080c 77
    0x18084d80740c4810186254a640c6900d61043d2005800d4940b154000d01460fa00300381c04400340701013a00c0420040d85050340f00305440c4400791100d041003800051024071a181c4010840c0285120010300046556803070b0050106d5000040803200c0d07134100030010451314101e8094949083e0303c10941450401c0d0008030b142d00f0402e01900314240000d241c400c50101c1c030240306a0b0321a44e0107421212102d4070788002c001030340044103040001c5520400e42840161070302e121a407170f00c1b070f07090b080803c00281208100c0c903407074480b0501301e0502c1404680001407550020a00d8000d2848401c1007242083c0044106c07010702c82c038820400300d07410b00344480303000948845845900c1410451100d040c042c4040d118400da920648860440645413002d02095280074080c1907008100e5041c0403503500e202e58000b86d00c1e0b000c1c00c4681400b00c40ca24070343c2000d060003801210b1019000c034040d036440d0b181c50503000e00100001c0e101c1105092901c5059200c5007498400e40083e540d036600d811945135aa1020094140d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 503650872 1250 503649622 503649631
    0x1092f0d03140c010614030c0f0d02030102040302030d0f080106260a060902040308130e0106140903010b0d0b1006050a17151804031202180103020901030b1003230915 73
    0x1e011904a048228070007504034107203d04008030302949040e090ba1841d520014240f8440e8018032030040745603550a903403201002c1c054811002e540505d00000713009000356031010390180140d00100c45400d6105652803690300c0c45441d2081d090b40c8034002201d680c4121040408514104010300b41201e0b51400d40325171004ca590b0020416030707141c002420a0343c100c0e40c412540036078045142ea280b0b1069140c458054000e0911b4298190f2420034000c1400d060000c0c01c0044005c0000d000905490a4012000a0f0000340c0a620668144d1400001c1c1b45000c0b01c801420800c041c20129000b84180c1c01c5034001079450780d80740840080ca0402020740d00014014a0120030003420800076521484080d0080d12000403030824145000d09024140e0300e0003246d80c0224510422180c00c0f1481948460700381c0c49020302c0c0c010385540024005130000c1501e4101154420164031000d4410341c3e25400010814008030304034141c20000c403c0f9012484800e8820303c60903040040f400880712054110690321 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 503652122 1250 503650872 503650877
    0x181b0103050a090c0b0706050f06060a0c03090b0403080c19081c0902030d0201050f010b0901050712030b1207050102070e0603060a0e0a0b0106051b190204050705090405010801092f0d03 81
    0x203240f040d81e21100e0100700d5621030060f00c0310105003003052084501c0f0f000d0380f1140c40c2c6503407001c80c034040c0d000508030f11408800c02e080c02501105881854440c222031000382921b80031103540e4588078284100d0300d4106541d0203105200390394001d4480700007105101806684100118200f44040340007011880070342102e421180d98600150016941c100901c907210195600001042d061105040c020010141c2100440d00e000700075050aa03680001120038240d0006414000c20124540c00c801403d510700305181d1120480350601d84092000c1041022120b090b000c8900c0395581c4d681401d11510f08454080c0d00d60012000103070250b440c2d401001086c00e1000036079101104a5072840350120003a0450800500301013150102060009045c0b000a085400107101646481030045088030800d01c009020350349803004106400c3c000e2007999a4440000c00c00e12156840302c107282e000746071100c415100340c810090800715941c2c1c00e078110200c0103500080403040300e0300350051114070404040106c08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 503653372 1250 503652122 503652131
    0xa09031403160623150307060804050607080a020d050412020c0a140d05031c02190908061602071203030218042016020a03060b030601080102040b1803010e010501060206181b0103050a 80
    0x1c134840c1480f51445401e8040900003114088030030f140c0390030525082103090190703150034400420000600294891040d05c0e0001d0103580b04a840d038040d00985071041011810201480100041c4008650184089601300c0368500820000c00c4450070b4144540410072000c2003440c000d038100341e00c605481501071030442e80340040c035810880304200076200300031000f5404100703502c2c10f4140d0042038080782c00c0c07460001c10103400c1440854894101808540a450380c203207a038040103000b840000020005079100d054407070905c0c00c0190103903122440e182c5444030007682c0d2004515140c4901d60350300c2c0c454680d6040b01885074183e03851551092906d20003103d1074000400060f81c8401c00398001d140305900100b04040d01c50241031404c401070b0001c0035030340d0040c070051295800c4141514078414406000c0d80041001902103070040c0768030846103005e542050004101340ba000119240074505164109414070074403042e5680700c68024248100341005014441155880f0740c0210340c010421900004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 503654622 1250 503653372 503653421
    0x23010f0306140607020d2f030d1b0507032301140709210615080c030109022d13140a0204080d08062e020d0503090c12120a090314031606 60
    0x400c203109221548004800e10fa04150610b03442201309010350b03401d4002744001800c50801510b800c0040c60500104508100b861041c8182009490700550b0030003840141d0400b5071600c00c846d8029800c580d0215030901150729680301a01c5581480b40c03c01c3c0ea01d003000707a410020700550a16044d01c640301c41d00580c08a500c081259031195420700d00c0b03510103100f030745407030031559504180000402d02d00c81e900d0140b8480c0507840b4606030500b480042e8040106602c0b9410070001141d02c000400303504214100100011034082e580824480c2c511448040368907502c0400302c0051b44100d0003030307040300d03004840c0036200d1038001c00f0002d0700210018076003044680924000544880200994881080c10750410600310b601401621403044492404a05e14035244002030740c0e81202041090094641c05c88000d208801804401c04d12048080c0b100d5840b002d002d4001d054030040d0200303440c1c441c0018840300c0d030080008202c801e80101d82c004c0403000312035915000000e2803640710348044260206400c9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 503655872 1250 503654622 503654633
    0x706020a090e0a060609080a020a0b0901050d09050f150408190c05010c0807080705070f0b06151813091a04060f02070804030c14010504170723010f0306140607020d 72
    0xe4800e4a0081c0005004c030728141000300000c220350302510842e08565000005610740c003035464103889a0505c40365549004d00012641c9216040b040007070107283c08440d404120000c0360320403030400e4a20031160381c10f8012810081266082d0b4000349111010070080b00e080303940c0d580c406c20402032401c100c041c158003500d4403800e4805081c0c0c500005403402c010000265001840302d500301002d0f1420606000712039445c0c1241380c81040c0c000e400c079007011000070242d42d5a0004800070120201c401ca0302d0300d00501c3d0300c28dc11684080b59910420ba0040b864045251620a00c90792542180d402c10000c5995607004152040241094911680b18110000c1c1002e150005200c21403007140d00da0b687d1807a6080510000c10581c0000c004010b101544195030b82e4080103441c25280304a14490810218201c010328001d43c0da403003888601120601100d10002551100305040000e8072285080c001e009802c9049400702c3c0145190703a505040d020381c076424030801420040b44041c040d038140000c13940700c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 503657122 1250 503655872 503655899
    0x140106050a0f080c0d09080f0f0d0b01020a030f030903020a05070612050105030703120503070c0c140301051e01120201050c1506031b01080a090819020102030a1503080706020a09 78
    0x204011800004250340c8040c0e01884000814481e4a020f40b29410100303e1384c1d81921800f07410790704441e21028003506210b1000111444e07603620ba0f82a0355286015181c1001a800030f40060941c18035100342c03813806500100740001034070307419135440b0703030740294110264010203100c20305030110700c510455000040c1e000c010a801402450701d40c11070000003820100c0c19030300141c01c49030003a008a101007000604c80c07251145450600d0400e5501d0b0343e10040102e821030b60140e00903100803540302c4006840042c0a618001450040e0024065030b80c0710004c0010a003511441c0158240d907400041110541144a058180f032051402030b20744480d100140d0b00d000b0220708100c00345040f01041c0992840c007045040081e1101010020191044600103000c0d2600241491f00c865140c8800d00c00304060318081b91403d280d03090350030302031100e4040d00038000c4d00304031351400c00d0780c0c0b80071403511543d03180301c50000031641d20058407407a2030a2592000c01030b4000c0002071007800442c1c640031078801c40d001807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 503658372 1250 503657122 503657129
    0xc02010b040c020f12191b0c030c1d04020a0320031501080d020a05060a0b0a030614040c08030424031d0a0201020d050301080a0f0302072102150c0d03050402041401 72
    0x1008010403d40342d090a10703003003951150a05e54200300c0f111401031003019060041c180c900300141b01403d400140e206442400380010001080c01102004018810070700809a4120003007010001520007410a640c240030344000e0751091941800302700184400300b04141500c110034002d01c006100401281c94a41074100000e020084440140001ca00800c0390020510721480240001009601d03029103982c0c000d8212144151205110841a00c40d4100e200085500160030010100c140c50200d51101c419030341110132240c00480050300240000949007541d07135801c0602c02c3e0141e08024408000c4480121409154441040521881c098002c004406440e04054191000c45100090038903210800e44c20612800f4070060040910001d980c4003c103910440d150100680d0b402c06920344000c0394400030000550903140c08000041ea81010785c0c061080e15507aa640030800101c0184c3e00071082060304c250b010440c0c2000b118481c4c0c00c40c1da00036002400c00145d29a82d0860b14004100980 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 503659622 1250 503658372 503658377
    0x91505150a0b07050120180312030a020a08070f020c010c0c09050106110d0302120f040213110406110c03030a1b080a031e0b03030f0d0f0509070524030a0c02010b040c 73
    0x3880014040b0a0051318001040d0006c071103501e010018200c0060b00400c0f007101c080310040c0c074503030103a0b03181041005c0c00c604240300c80c5d40d240c0c80c03d500810069480800c0381b43c0082e100002184403140a002c48044001a54001d440568a46001107484064280c402d44418910000018820782d2505c15a8064801e907560380308481c168510051401224003400000c00d8070421040c50f601c01c0c2e000503290810500c24100d0f29989841c0009101c200d810513155051920b00fa84040048025400402c11600c440c0c40321b650000080085070f45541c00c2c814804c0e0541c20400c90010603070701c1440d2000140342c0190441c13541c2d014944508031301340c01201c400c1001c00e44e100d040090072079034900c9a03114200305410511000f82d1680100341c481c00b61203a00c031151500841c0c001c81c114110f4011091441c1004400c01607450203c81c255079401c5a80f24803800b501c001f803a0403034058074000c101510b002c002c100c07152468071440c10716801003010003941c2045560390100d80034159124040e0b00546059036 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 503660872 1250 503659622 503659627
    0x1509100b0a12260c0c12011e050711030309120708040b03040f0314070309230405040b0f1f12030905060d05011e08060f2701061404091505150a0b 64
    0x120014a1803c611910a0002003814003d0148022000607403685a400a03240220310300c620f502c40f1805426a078103020542c81d04480b103094910301c1d0758010b5104042c1c81c2ea0f0504807940416203152280700c1a2210f0519400014059000b414003030002c100b158490880c8900e019510401c40c0001e400c00e540449030741071080f07508003c0c103174049002c214003640d21144524102065802905c0300b0054890700b54840f9228208114030800303200301142041000e00203001600c0c1ca0314102c0342c05c0d03d00300c42103d0908102c1000c5100740e411003942d00f10003200030780111115414002044013035240803100310100040c0c00000320711521100e0142109080141e8086210b5060007401c101e041510b11018118680f03840341007042a500065040c0c01000d14800d0117004e88402c4450024020000716015006d0a0810b82c056a20b00c1580504221480c21020740d030811005004c22040e50f20218015124500c8600314104c1e0041a50105800240300e4141100414518003c40c41000d229071003103d405102 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 503662122 1250 503660872 503660903
    0x209090c0f0109060f030c09050a0e04021516030e0d061b11031903022d07030f1d100e0907020307020103061d041202030708070c03051509100b0a12 65
    0x441c80446081000d0038240b400340c2c100500109116400b140200400d5110310400340700b1809001c00074050b00025201503441703911064401b07125074081d203040340603504000d51007640c1d031103030425506482841200901e5002143e242200c85101c404100c540c0b0030060010b0034001007103485104030762141489410710b0300764030640c003501d01c44218820b106150020416000d000c01c0c82203000526800609005840b0106a1080d403000303910120700d10407040140381ca00041e02c00003c05800c4203446035a81d43c0700300003004c0c0300300c3c0c01e50104141041902c00012000700c491800b866603284142e41403902e40c2a581c5a440040d18441c02503071300001580000414005650381405450060b101a88040c81e400310084480030190000410140161140c2c482c0080d516100b0701c1154055500401050b841d0317100741c10520148400c601c400ca415109070900c0b001c0c0c04413580710302481110380c4005092101480303440b01000d003000c07814041d03001c020f030800400d6082c03d410002c01d415000701080d0600307101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 503663372 1250 503662122 503662129
    0xe040b040320010515101d010309050a08030a09021c050d0806040207060603080405010f02010e0627060a151409070e040b031204063b0d060f050f060607030503040b0606070209090c 79
    0x1040c10b646c0007081555209050030401d101201307014a003080c07a00040419950078036905014032140c0062000700000184803844c0c0b110340058032940d008464040350521040c0030800d4480c4000c1d0000d100303401013810310015a00400c000ca510200151001d4a0250340c0c0d0343d104104c54103904100d4000201060504c11964002c2503041c24005a0008000c2d5603480c10b07241c0d41d2244020182e0756800e8207070507018103c0e8801111420258480001c8800700c2c20141ca104015048641d800c0d01c240c400c013400021404244190746c040440090140c21480d26002c004440b44609a01c1054000d83c6440352680281c40070480d03801001c019409040e142c90414600401d840c0e06028500800039583c1c211011a100b0080b036040e10380c061328515030500c417080c8003089100d01c0340000076042038a003040070f0424140540200e4407800c00c82e0305201140d03541000700b01c828000d401c00500019030620000c0c000804540c7c295403c41c2004000b80e04204070b580c0000c0900c0b1044680c031000d40c0045510220a05 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 503664622 1250 503663372 503663389
    0x307090603050c040501020714030a050d0c030210110d0f061d06040509160e0a110703020a050622060914011b08060f011d130f020901090e040b040320010515 69
    0x18140f03c03041c40e091602e80004e41c2e5030514080c429843c20391800c02c40e00d80d80c0030024061510303400001d5414032100b940b0702602401c4402001d03009805a111058440d040511910858034149030450303003041c03100f085480c01004000301d1503403190396410700450224454040c0d10315100c0c01040c40b850920f0300c1c0c001d20007920409000c10606034000c55001d142c0d41ca400110b070040c2c80a060701071b0040d03a1031034801d40180031015800711030034400103071440034540c0c0402c80e004030501600407076183e9141c41c02821031464a15480350140d0b4004022600058003e0b08001d080a00035841000100b400684141c2111450541003140500200d046003a05802001c45540548201c2e81083d81d0181100060f01c0d0716400c408a1910000700c60054607255100d40c1c0101034400e00b01d4003089050781c08034130f010080d40050895804581011800124044401d005174803580d03100b01c52100b00d40b1980c0c1c0554001003d0341c80390006150808013101281070900c1068404c0c6121035114401070058002d01c072900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 503665872 1250 503664622 503664631
    0xb030a0c0e0907270509010b0a030c0e030601051207050303030f1b0306010e0103020313050a0503030a141003020d17030c040303030b01050304051522080c07080304030f0b04060e0102030709060305 86
    0x10b0216004110300183c00100d4034044041d1400e01070500009072007110f164001d6504072030790081c007100022525001d0800078014481250314104007a0b0035040040e40e140c08030220842d45544404014001810405071000f545210310f01202c0106803644c1c002400c5820131260085400c00c407500300b2505c44400c007980b00c102d4000c0300340d030303480d41c140704c3c00017030252083c3d0030f50b00d05054001010403113806110b6040364105030032a00391802040c1074500070b6126030040c2c0303412106600385911640030a4104038841c0c09154208502041a071465080c04051485d00005680d10981d52200c1840885510015841030018000ca5940e0350704500e005011100e01d2b100d901e040180a0041100081c40000c0302c520b098400410020166030f0071783c005034a84020308482a030503030a1a044410040108040d000b004e52040907200660346889699513680550301c000b030312541388401c0d0341300424448441244c11501503039000c5a240340004440b42684c2c42540c16400040b1520f004019641d4148a4075400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 503667122 1250 503665872 503665879
    0xc03070302070e150904210f1101060e0a2408010608011a1e0a080d02010603120f0c12050409060e04050106051507110607020d0c1e0b04140a0b030a0c0e 67
    0x10742040d5505082c25030200522500030817112020405010281180c0200d401a580040c81c0320500002c004002c01c40c000c0c01d00c004034443c02c4103180812818002c6000340c6003012181804c1d580d4514251018000b01c0c1c40c00705001c1404114003941c0340f04210401c0103084800004243e16150540503421110040301c900741001104800c190b00390b4500c40c802c400d6070f1003209442292240b1600044031a00c441d030080c4017520510b1903241030729406401c00c0c0110307801904c0350b0f0f1003580200b806440401c0c82411080004a801c00088002181c203075428a0558040c41e2050070191141916012200983c000b0100744010380d081008001d001d024000140c03501f0383d0b0360a05030100807088241809640c0008094500580000516448980507100107a400800710100b90080f4100642076026500402d9841c20401c0c400181d00c0800d8201b00040380c1010a04600d080d05c3e1000e288000710719000403a90003456a0000100140c060000e0b60241800100020701d425182102801c070000c14030310b1031700 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 503668372 1250 503667122 503667149
    0x30c0f0304050622080105100306140c030415060b03071205090c010509010f14070b01060207061e08042301380616060e01090209060f0f061e0c0307030207 68
    0x42d40c59600a60700034520301c56881d20040d41150500b03ca0701000c1d00a0a501d6103410100482e1441442c1a141203e0040c601004405040007060450b408100c1e102040c2080c20000f1400041c9003c546c10201c0f075004400280303d03034540c0d8180e81e995005480020000d200b4100c0c400b443c000b24071a083d0070a1102e0020701d0100c2880e80007170003a01820007003030306224445003c00f81850080d1005007000d48070000b40c0740e480030145030184c034010b02030103071000600c24804003052260050580f10b650321b010000989a00340d0078003049130410310051085406440b0b904d070f0314806421100005440e514403000218841a00807041000d110060800b5440302400380c404035914828240140300062068591a0350703480c42c03147ca4210f40c10440c0004040d1403600c40c51001c400019402104603d100704d8000c0c1094442c802009064203140e070a60350b11201c0d11008082a10302000108281d11050300c038003d00e036840e019200c2943e0401c000c1c0a01d590400140c8404141d0b040c80618060003040c0031642 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 503669622 1250 503668372 503668379
    0x506160e0d02060c01060e040624060905100c0501050a0f0b0109030312020a1107030c0303090e06130504020f030a060506090c040303080a0207020103090611130801020a020a06150801050405030c0f0304 88
    0x407a015a00c0a01a0107840c00203403032015040d00307400401c0a41015030f1490f0140c2001e1804000421b00c441c01c03203c6640d00c0c03005080c280040640b09004031242e40d42d40100850a01c010005c071503009002c17880501c45508100b8000800c203000f614428108020001500c2d40c016540380f01381c80c002403059040024210b802d000098208500144241200000589913504a01d0554250940341c4204e4058440c40300000100b054041800c13040d68883d41d142644142d0f10f2584061b0540180e4503958406401521a80b115030b681d40442da00900044c10300c494424500d01107418442d4400080e5022901c80c0208101420310400e510f800c0364804d82c40a140525503180100034070401382400f084250001090001d5a1081d0003548109801150410103000341d6400742c000760f404088585180e03050280002a0150b061090341c800c4805900a403042c0a040d0307076200010301300c082c55200032407500d200114a09030f0910409100f14800d8004643d10b00407007a82515060320f41b1903c4419910030071003032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 503670872 1250 503669622 503669629
    0x2040f02070c14011b110307180f0911040b03070f380318070902040e071e21020d050c041701090c0302010f0309140106050f01050408031b15040506160e 67
    0x9190b02911351100d05c26400541c0b40051403043e0122426605101d041c0d004a0500452215826003111700881041a4505a11402d0a60749144000741207003103094040a40e82c01d0540080c0c030081c400400381e441507602c1c1c4410845a01881c4c0102c844800c46021440894241080580080b000c00c0f41e034541055584840600301e01c0b000b00640490020000c811810305e9041010030064034040310150344841c1c0711105d501d001e0030b040317494400040901941c8040500300c60800c03030798071007690f54942204520030b15501e80743d449085040d4a865080150340d080c0c0c0302e00d1040e0f0b40112104810726582c0c0c1d10b0b01407041c040c000e041003040c840b6454080100c002812103040102102d5082c2007044914141510035001031080c14801780c00c8540c3d5814840031450194019421354508488101500100000445590107070f8080c4d00080da10800c80b140d01c501440c104980700f2066841280c648945200d8401c0d40c0010540d41111554003200c14803680490f0032508801e10314852400e07408400040002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 503672122 1250 503670872 503670887
    0x513080c0901032301020c06060a17070e0903040801020708090a0b1926070e150a081b0c1209090a09050a031d03070b0d0c02030316030e0a02040f02070c1401 69
    0x14020081304a8041664031002c01000920072810000c64580d4103001c8595141c15084542d18440e01c0c02c44c001090081c450640329400c61110402042e100d0b00305448192000c0c0c0c0600501f1003031000388000030302a4402d00003071080700d02c681e03182500d81c0850414015160300070340045140300c4051240d0709450f8100750185401e080035190164003c4485150092201c4509010144002d21401042070198005010f5120031505940c154a01d07032442c0e000d242c2c180074070f006500015034088041854040643c41c0040c602804202c201d15240600d9086072420442e15624040e5210104005855181284a10780e02c0071a80710280319101381c0d0f64440342c032915030f000c000703050040761544080e241d909142c1814103144007a044424864851a10401642150028911007070808000c0740c0c01c00d1020080e24000c108841c200c00d2403101c1d07020300f940601000c0c00400c0d054414807502c44056556401002d0841d0020030700140d480c1400e04000703803801d8a540000d507944c2c20307285d0701503d0390340e01000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 503673372 1250 503672122 503672129
    0x5120a0c050f1513030807060209030d030506100e181e0a02070f0b040311070f050f060426010e01051005130b030d0c05030c15100e060303030c0d0b100513080c0901 72
    0x10303903510303200601d0184d4105290406404040081608010415603500420480301d0440458013004c1d00360400b1000c1d500c0072101150809017000284140741d014100004050300c0042510344041e86010180c0c1040100310342103595100600d031031856001c2010905c6800c0f00c86d8071825890308044d0f0300c1e004503040d28000014050300b40340002400303040c401c194215940c003c00003a1081c0b165108003503040d011407401030a00c10b0000c13406246203881e01d40105c2e41120981c961400380010308081d92150118140000282552942c0c0596034214080c0f043c41d1140c002d040c40382c0c0b107150501c02441364450100a100340c02d245010340524a65400241281030324240b40762281600c4041d161040c1580900d416070091407051800440110280e03c1031548180a88400c00c8083e83c0d85400517059080b05444013600341d0000c1011890f24680980107000561090704045090258007011a000c42842e00c00c140c002800455151411428a0194001040ca100041000600004c00103042150601c07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 503674622 1250 503673372 503673409
    0x6032307170102090a0608060f180705030403050d0c09030311010c0e090601090302030708061b160b0c070f0302070e0703020408032a030406030501030b0610020a0b06040605120a0c050f 81
    0x10318070000468250126030480e0005801405401d0743d03034001811089040e203203d40702d014000050041828282c1340c007a156400040b4404841d20344440c159065440a0025000c00804211402c1d0044940c0580061a03403140e0318a0241859400c00138440d0030046000012030b41010340d510380c0950322105526003040203c450307060350f813504001a200600c603648000e4060051400000f04010049442c5110b0800d03010141103080110441480b1403003045140e9880205800907080403800c200c207032940c0040110111840e015a5441d20b000724200c0340341c202c0050307206010912060340640340039134121401c0d0030158113180c00c0846081d241d001d9a004501d000d50142e0301d40020703110500907a45101018000d69941e90b031200c40c0180586400d00050341c0175400403004c508903007403003031010b401840907a01400144000390346150456078003a1039160720a4031220702060554456405400003428003008001c8018079140040158150fa4840c501c5001100903586551303e466540344214038144 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 503675872 1250 503674622 503674649
    0x207020d0303151715070c0804090b131d0d020303100501050c01020f0a1d150304030c2f0307090504020a0312030225060e0105061c06020c1006032307 66
    0x32021101c00d41855032000c80000032415130348407400c4020902c020014040080b41034203a580c860283c071614032401d0000d2000e0400c12041010180a43c807000c44581c0013812001c01042c0301e200c800c00d0300c91481c00b40981c410400a10341c80f600d400c110141c5000e41e6030010790700794945460111614176040c070549040c480c1c00a4048003941c800e43c12915000d001000c420f0b01c403200e0420080504499503541005155064035101c4e081c40c0180e040300100016044681c0f469841d580d04940010030518105c41c0c2440d1980d60160f0400c040700c130f15035030719101c00c01481c206000408040c6092110343c001300e0484d141a080c0405070f02d03130000c00d0040d02e411030481c02407114004030460082c411480d01c843e9903030060003d20740c3d4000c80e02010b0240d5005010501604650303507142822985c09554041c4d01010602079200103081c51101c1746510741c00b400300182868186c5a4580c00c11072150790840c1e2141e03641c0020300402c074000122440200e1032800501189036170407099680e482e42400340b0182c80c03221 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 503677122 1250 503675872 503675891
    0xe0a05010e0c0d0f150806010b070b06040b010e030d0201020a17040c03030f0216030b0709080c090a150302030a0c05030f0604080a0507060605120a03030507020d02210918060103050106030207020d0303 88
    0x1c0c4c1c000061a1165101c1040b140e031388211320000c2041c56010b114034138014440001040c480902c25201c0c40c5400c0000b561045c0c450804000003844400e2009051003205801001159010300081800001d17580001da43c3d480c1c00700c4001c110f204805041030500c0119014400072504003039441054030f9040c208000d4103000d0f140141d2900000d07180260524101440200811079441d09043c090b80740c0b42c85010030640c448a1039030700c4c0d46a19139002c3e0007050590010f5042d0303a20b5040354503460040c140c83c01c0e00f43d40341d0b000b1904240010405030303007200411b04100414142003040e0655411020090086814103a6034110030344140030300314080010200e03c2009024103948908014000100f00c1c18049185581c405c0d142e036070240065010030303e03040010302902e0001c60140290342c00c0380d01420000c3c5d00b0010003030103007000c1012044201d8080c407556610351038866503421b0184210041285501d0420001010349105070030000c00c250041c041c0d100103072220142e48002d25490309000c01e00614 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 503678372 1250 503677122 503677147
    0x3180204110f0a0c06110c0d210c091404051e06061605010504060b0907050f0f090301090c0e0c09090a0509120f0403021e09010e0a0608160e0a05010e0c 67
    0x301211200600030000340c0c01120fa40210380d4800d0284210814813500031500d60302c000c940200b00d1075008580108440d04602c900c90400545c00100c40b0b95103504200803c2070318030880c0e4140718000c001c15106602809066100f00091805c120116414041481d080c41d40650143c00b4403003040d0308112801c00714000b6500c000a448c200d41c1c255a60300380c6403c190038130b903020f00400e80381914036a141c0740c0000003c2c240b01e5001c07845100f858079403d25184500350840c0195001c4180141d280c1001d000e40c0900d60340a000b00c0c002c0034002c0700001d051030b051800340d2595038405444044820320400000e0525110a23802c0340e400822214001081d0340c85c2401c01d800c04210301ea010007850b0300069075007070803a500c50107041501c0c000d960003614850b100c110303000700340c298542c80c0368000070f413000410047e1102449140d12141c8500c012440907640e0444905d41180382d1002c1d10b00d507030824402c3c031208004a649692200c011101400294506483c00c2c00e0100090654500c00e40c001521160000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 503679622 1250 503678372 503678377
    0x10603050c06250b060f030a1e0516060504030302060a14060f060d111909030f0b061504030609060507020606010c060203070201020403080301030c090b01050c19020a05130b0a060318020411 83
    0x10f44080a00003018031458005140c1a045034214400c420101455109040002e0711035074070344e4842500f05001c840c0c846015251807078410702701c40c14826925011400311505046200400c643e440702519507041d460f0280c01c00d80010089442c80c1c3c5450b0b038200b40a0030600e00181c01c05016030f803e070fa20b1001d00d00800d0b40c601c80c145240f0b1a40342407000e401c111010303400c01040b0304144005086817002d01a01c044a5403c0c82d4400a05110f4004400c3d40104003031070041da4011030b0041c03c82594004180c1070812580003a032080e80c0c201d42d46c504200500440380a8203038880c081e4400391038103240103400a4180ca10290b0050175555003c800545094000d60440c3e01440e0001800c075203960b03483c0b0740304042c8504e9025007804181040103d44007075006000380c1c0e80d2901d83c0f5009e4251000e0407060f001120f03407004002e90380540281c0d00040c1d6a00d0b0a0280a0840c038441ca011640001c0c0e002440040c10280e88a2010186080b420201110700d4030410703004290b0440707020602c0000c54403801801d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 503680872 1250 503679622 503679667
    0x614120c09010c1208190b0d1403360f18100801090c240503130309051206070905090c0f03060a0f0602160e06090106200102041511010603050c06 64
    0x10312081080440c5d08a42214801c0901050381651400d903421800141c0340c016480c1a00305082c03501c580f0005181c008002e0403527038102c2c2142d081c1900112a20099540d01103603804004c1c440c80a9444800200d04045006a05548442c000003281004c00c0c04840801000d9480003042c0001c41c0380c0501312180100240600402030003020014140005e03418a0f07845801e400088481088004e039402801600380700b80c064540604550719003107004079500c8480d100310b0400c03110710004102540e031650344444015040000300b04034034145001500c141003e40285101c0e0504104010201001c0c40450310300c501061061511381c1c44403008a40a26a00d80000310944000040443c02c0d55000a07001c10488030385103c1c80794281e039208104960f14050350b038581c00c00c02410051003030382d00512840d440300c00c48004d001b035004504100d4508a8000740c1100402c40d906840e00d041d0141e01c49403480b88050a50f000300b04652850b52030560b15240e800034a0701444012424484030040602c50000c42e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 503682122 1250 503680872 503680883
    0x90c040509060d060c12060801061401050a021c030e0c2409040902030a060905160f05040e0a060f02030a1d030315030a0501230a0207030206010306051009060f0614120c09010c 77
    0x10049105c006080007034070b848440320780c0d4540300c0001a480b00c140524800c58810008060800111000448250303101d506070074194441c40d503201641c801c251103845034513907466400248103501806800d061403905c0700000c1c4211580b000128030500c1d80d0714107035038007511310342c4c025541e41205d40400c0c041c000c2000062751500500349820140316154004490391407041e0142c90741081c0651505071004420300400c080c83c0c0d07144c10144603c0c18540d102d40e010b00074281c02c94080b00421b41c0c036001520f4a20058201440d0044184640d1503c14010381c10301044001408058075080c01e14240d480c0030081c06000b141840620b80c0c84070341c50521003142d0140c1c0240081c0710b04045505100035541d40c02942c81d00304a000000075001c50392038070a64100a501d80e001e09080d92958031440702801003e0009041c0076114000000c100000d8401d403070042010522117000d0320701d03140c0040d28103000401d011005010402450012450307040c0c030305d41e00218005a075600d9502c1140103c8907140c240600405 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 503683372 1250 503682122 503682131
    0xc0c060403050303070e0907020a0303050a0204090519050c0909130602070206130e010e012612130302031002070f0b040813270c050d271b05090c040509060d06 70
    0x2c2c0700010008520a003140e8503619007010100c002c0c0141050111002c80058200089a0000074460b4110940164420300d016040a03155031a40045030001c0e564501c540b075145d6800d100341c984038080d40c0c2d480701100262508109003400890480d4000401210040d8038100c0c003a000c1101b680e05407642150043e040035111145814030446003280c1c3d00541c0c9242c0114400002d040e030301e00c0e40d000d05a620904882c80e00701301c1030f080c0d0761010b156000400481c0c05008050302107401c550005c0c02d10400c030b0003184029189107006040c141018190b12950310343c010041d481c0801e01c0c0c0440d04018960110740c0d0b150b10f5983d401c1c21482400317003000b5800111040300340000c00000c50103003113400307000386e030102e0780340820505614040341d0a0a184e480811400d010ba6460103d0386c1d40020820700200c10382c1e10741402c03a00d1291000c1c42030031388100c0b000c05080103009040d10420b24010064078003951100d540d814180340e600c110703004030b11a152140e030304000041c1481d11000445200158401400e11 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 503684622 1250 503683372 503683379
    0x20f15040b04031103010903050d05130512040e011e051201020f07140606010305071211040801020c01020a08090115121a0408091c0c12030c0c080d0f05090f060c0c0604 74
    0x40341d07a8414030040c0c498510040d0702c4201d5207010b205400e0b40300ea040d26454a400890070210003d814014214034540d40350650504c042441804601c2120802e40e48440ea52401c00b01e003000051010780200038504c5d40c0c0101c02401c00102c0b030050040e0b500481e403800d085e03c9500c2e03501d800780c41200081d0224203004602403081001d01030b480b04100e203007807046e154240d80b4040110100c1d0022241507002900c400c2814021400c80d40c45140400040c1d808149016100c0164909a07403051341d00c4c5160741c1d07000503020701e20380d0b10406007034000307900400a1055281149912241404034081d0044c880402680001003103042c0f02e0b038030742446070041d40d06454074090070000c82c0c2e50811280e0501400d6070200c0e511104416070340200d04180d00040c50081301d42020000c0c01c0543d06140200c0c1448881b103004c0011403203402d951300040c14400c0c010700b100100719400500c0c00c00810b0703408050040904c08220a42c0d02c41421000581041e11450f449601702140c1c01e1174070048000103504a0000076021 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 503685872 1250 503684622 503684639
    0x7260a050714100e04020c01200a0201060f06050703080612012a090e0f072f07090c080604050603030409021c06082d032b0c02010216020f1504 63
    0x224122451907110b0062407065200f0300014503101e0032880001403072280e4540c49490141e01801d00c9032036000002a5016030412001480c1c041d203d114a90b10300080740f0003120a6090244002034000c09820079030a525020002c1d10313034042d85100070280709041c00010400d07264441e00d0900480d81d90b0003030000039186503036284d0300c160004107000c1c02170b09007645040700e60003202170500319400900080915075609c1885201c0f120080c22a00c00c022045094030045602680380001c15000485980c502440501c415841e0140366800450414101a110041245c0080d11564040e82c00d0b0741c0895180d4034400007174214400c5401a114092010880d0705661225120042e41a049a50300704400703501c450149944540440ba071160740d800401581c1040d079a681c401900c06002c3e003045070305040014011001200803a46010f0403a500b643c81150414a54001c9100307554060000b10f140481c0d46120310000103002502a006075204100e401660b168038001d8401a180b4654007500c440d01d40480 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 503687122 1250 503685872 503685883
    0x1120b1c14010606090605090103180b100f050306060d0605040507080708010f0b0607050606132a020c010f08060d151505010207090227040f0509100608060907260a05 73
    0x1d041e455032821002052043c000c1d002501a1400d90310346a060002d26001100605206021503461014550904000030b40039011036010304540e0807030001103418140103081c800481c1d070205200c2c0d1701c0002880290745641540124490300310501051603502c81c2813691820b0381a912140c003510038500d00184407601984100000203202a0501100604c0020401f0303a00512401601c0c5402c000040b070481d01c3d000340300c040300103942040415086610441e801c0c0640361404480c4c03560103070045d400f0080f80c0c140413103191a02d0074200742d05031318070702d500081c03202034020301c1240100611070003d41400a0402074220b10020002d081c4840401b100d520500c46100d440381d0f90252180c030001056070a418004c3d0342000e0222071a44084000704007004150900c500c5000350042d0b501c4000700142ea5842c060b191084c5821002441c040300b04920a4003110440e9000e5121508a041071220001c00070070080b0880d0100b0a001c09160303041c1468002030480340b18420400c4c802e820040003040804034a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 503688372 1250 503687122 503687153
    0x3121104172b02010b06040e0a0e1e0105040308180607030507111014130503190c0b090a02090a060e0a050a020c1c1d010c030f0e0301020403060b1306030201120b1c 72
    0x7400050504800c1c000240a01d004007154552442300017000c81000754407810584580800310340c000d098607201441d01408011145010365129401c00c02071640101c44103401000c0800d07216104c0c2b0f1400041516540060704102c10503440d44085924203101d034a194038034001d8003041c1c8900c2010108050f0040015880c0160300c0e0f0f0f100d4001030090204024280d08840d040b10141d8504a42200300d803020201c020070420501100c00d40c6007011800109400d441001d60400410800e05940100710b05508002d081c0d1a601c1d084c10360a00c000d045051880350000349451f00881c240e151101c17410044e01a4000040c1a17105019001c81d01010902c5c01e1807030b080c10368a40d566518240320407040b41c010780c14403007400300d09903c0e104000280314940c41404200140340c007003a0840c4070b40011b402e907805644156030080d110001801c052509619030401708514000802c0254919400070309401d0603c03042d0b0a0040d079407801ea04070307030f11100510150400038440c413010410281c41c2440800c0782111 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 503689622 1250 503688372 503688377
    0x609030d030f061e140f01091e24030f111c0605032a0913142b1b0203070317090d0605070210050103020a12080d0906060303121104172b 60
    0x402805e458242445511001e56040c0d5895154608010814070030f04181c2da011040c2c030106050004240c1000c5036924a5030b00898103440741103141510040c140c551120380050124501900c40d0701803041c0100311850030203000c03c0c2c40140c070314103907202c40100700c558030080d014011a8001451140360b28445604a5105124030034240450b00070b01c00d1803502100e100d524210002c00400211ba040c520078442001da10007165180d80d48400340c4d513050802e41e074416114030214500c070004550071049080c402c900003052041700b0b1070130340c000903500c0d040c520028101c81c29411258028001c3c00044502c588005440f054900d56a0f1070074000a1001319503910043c0504840e4a2030500d80b4068141280d170000d1190780d071181850091000c0d14000b000480b402d01e410010307008084445e004050440d40074000001754107185040140403e0240034400b4001031900d071440c00b06901c440d0646042d03030042080c0c2d14189000d6042c0e9803074a15080110a50401c851420101c2441c04551041041c42c450b13 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 503690872 1250 503689622 503689649
    0x3090910050a0504021620030708011b081e07090306050f04052a0405040f1b0b18060702030316050139020a0f0b0a0b0609030d030f061e 60
    0x55800c5141280a4080c030355000c40800003c21207807a054001d89492052240b050b078480f445c9a868044481400030244000e0070a400e0401ca10b1405000c020000d10184000340560440000c28402c9918004951010702000d140411003d401c207400d40e40603004400b041110905152401070f00c101001d120403140d090810700000c1c0613140c120046401164840014200e003a0400b0b4110054010203d919074101c40d0329803141102e41e59802940c1c0114050b54014400103154140480c94071204d0180300c90062482204001d61200841120380a45000713141c181002c040c1d400107440e03803242c0c0d04040d515200104a0000c4a2200c0000d103021a2041d4020455034205007400c85030304240100881002035084540d01181c185081f100501000e1441960740b486501d0b036814903013898804007a500c0820b80000c1003040c958900c00e00000600444050b401c003040080042d036148c4488a0580406454044450448080c1e401210203081038403c10420a13200140100c40561188101940c10026 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 503692122 1250 503690872 503690881
    0x105060a0506070b0424090b0f0a15060e1815121b01080a0608010603050a11040b1309031701060512010f050901050603040c080313060f110303013302030909 69
    0xb0080764105688204603840960391030303d4455030604000e60048170182c0e40c1e41400421074141c824510190b12a02c20b502d001c1c1040300540400e050028030b460754203450503050680303940141464400301d450620f02001c4903001c1c80041004044c1005484102c0440c00c414080c080040380350b0b00c0c80e50388065549108c1402c40c80c00250369080c080c14460503148480315080c8055100390641648000d104002240036030355010003500311400d69100350f40395040328485c0820003803c4c0090318046103007214240300d4a1040000030381c01e00c0045d0b003459007495850540004040c0100d8035a0722000e5020514125036039941000351031a031000d00c1d00c81c2d00303124080010448401c02880002030700c0d8041e03d5028030341c1c00c110601c4041d50002e081921528103002001445410030401002041d1086100c28240340c500358018082e440c2140f00c11041c84004000c2c611814000000e80f0b044541c40c480201d02c0c8248050240946042e00303000390791220310001d202d507240e82c0000c0102000744003034510b0380301030750b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 503693372 1250 503692122 503692129
    0x40f052a0a0b03010b16050a060207150c020607050a0c140601380c1204030305090f030a050d1206050d0605010812190c0809060c011508161719050105060a05 69
    0x250303401403850b042e03030510043c8900360310900901a0002c080c0603640d10084031707496903403070101c0000d812140302d900003804000304109103808d05400032140701c040c0300c21102d2a001a4458100a103071104000000c140100c0041c421350440c400f180d003008a07500e0700200741d21042d440381d100340603c0316495104958030101000d003543d42e46141854504a00c00c40751030b80d551596603070041c11499054860307040b00300800c0d070020000b04001c41c840e440780c1e40d80750f000b2400c1c0610441c0c43c0d10382034030a0b04910880c1000ca500460401c0140b4482c3c94541c88148843e6081402410903070407554020404520031000c000e4145e1141e41079903590170441d00d4140c0f0b01c02d40641c19100d0703000c0e201c0102030480c0ba4007000d036000303114012845104021a41c1030540e010003041958011400d4104d980e03441e40340090020310406880c2010304020800b5200c0e44010019a03e030301051841f600e01c0128209113a150404c8090040c20b104603d034070103100400107141022406072109941039072180c601450005841c0c0b9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 503694622 1250 503693372 503693389
    0x31d010b270c030a0608060702010902031608060f0402240d0b0d05030a1107050907021e06060d141e0a12020d0801091508010204121b080c09040f052a 66
    0x1d00c040345200d1a0352007480161803a00054200d02180d80c0b07808002c6030722101401898801e07001580000340c4060303107004142c0742c10052404102c01c030404640601c40b004011481c554043e480710080381c90703500ca41c80814034034038103210865100054103800d10150301c0d01070300138020002518070034412905200c00b04270b00f0903d4040001c1c135a5004128004015000c0d9118000c1180e5180a4402c10340c0d8610104040d1341007251100300580203e003000c10700c564508102c010402c2c0c20f0700100a1480c3c2036001c80c4800c3e0070480081c100e00b0341c120f11201c442c4800c10104d00c0190500703e03885080e07009901034a03a20084520100ca501c2a11000c41caa5035100040408085107983d4460229034a80b500e100300034030b0421180d55400132610000304103450300740001c0000305410144402da00340c107401e06c0c240b1414510303e59400c0c0080e00000708540c2e14000b800c4480070604a407206460703126464808c9162000070001081030082000d11040b400c540b981045101c044141054025000c030741c204003500c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 503695872 1250 503694622 503694679
    0x606080312130302010204031b03050d1e1103070501090b0f0723180909032a0c0f060d06030f140a0b0403140c0a21090312050307031d010b 61
    0x403114000060303a03841003190000b030032034003134000141713095240e0312074925400d850151714032805aa41820010000108007502c9501400d1a0590b1080c014041e841980b03c8114110820091003208154000340e050084800003036010000f000b07800380614000280c42e90071202c03606a20003200c00200030501465510703c1c04811400740209241584100b020b640c2c00000c0c21f03412081e01c14011818644480648030300a2109000035a140c1c075110703100400b9015103002d88409141e8202210a1100d800504450ba410701104c0f622000500000411028050104102c0ca0035040000020500c8078103400501c0040c040c0c010000d06001d0342d90203c0c2d56400c204801840c8100c250005001720344100005030b01001203007462498030900c0c9211628001020343c041c1d61710701d00100c1e4404040030000305003c01602500300455000d2841d00d07046030b000b025141031000c0c890004000b4004500c682c0c4401200e090341c940590000c0310900056008082c10a00c46010350460203442c4003598014000381d001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 503697122 1250 503695872 503695897
    0x319170702060105090c070b040f0605090c03070510021c0e010e04230c041e0e0714040b090310020a052208071403010e01020a0f091509060c1103030d060306060803 72
    0x8613460301007030085c0b071800100b0040c11750909014910002c0d2980121a01aa0103800c41d41e5000100f401c001045802c0078207140e141d94004003000c3c08507100458510102d420403600b83c08099410b43c003c0c3d0806508d00b00050300b00707060049000c201a00000020708030351003a40d031246849903403400e100c122500e90100d0441c041c1c80f0014110340e9080102100d6100c0580d003403582c1060b0f6a0780302807040c400013003541d90411800d8881844104028110164080c000b460f02c030144604000b00d9220500c07450244520020f400a80c421068078204410488000002c004540d19000c1e50001081a0015501d104d100401d40204d6155401191040360564280700040c004c0640b0749070702c9070105015000e10300c0d010354881c0c4c0807815902c0c003840500313800021901c80414124042d0401030076002d541c1c0080302c15a42e40322041e88159803110b125000d4600900340030007521142d040225442c0f1100040c00e506100004540b0100c0c40640c00410880c3c0c0706030010302205071603c1002da103078018403224400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 503698372 1250 503697122 503697133
    0x801081c0507110a0504020d020912120f03070207030515040b07020601080c04021c0204080f120a0905090408070c0618050307050306040f0f06140103020f0102010c09260319170702 79
    0x4a981041040f4002100802d0040225503034800320782a60404154a40c01d40e034003084010190624400e01407040c00e03040054818070122205e428110f0291a890049242001c400100500d00800010b0b000c6c64214048899100d960919260800c008441c105c8603001004d01003242940001107030703416131780d80f4405002903502c40000c0c00000e41100e4940342d80c2e001e44001e055910342c094402000070f0034018016145c1c0071038106480b480c0c8514080c4804020030100302c49828143e00c2110710303054500841e0000c00c113403140e00b032010a9001b035407405060180b1880000031101d800c8074903030040312100320380f503034072a507544c0d04054403007005e440b510350035400c0600058005445d4040035a85e06100f85200840c2c0806912124201d8840c05208211803000130014000c2d45412142e0300c1554409100070721032085007107801008204180b01e0a42c54078440c0c6a5481c1244043c1c8042944007c01412aa01c400b49060511b54a440f08250540030846248012180c0303282101000d20600190300100b1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 503699622 1250 503698372 503698387
    0xf1a010806011d1c03081b04210510050403140a090915120302010f05102106020904090c050f0102010908031b1c02030415150e100503010c0801081c05 66
    0x11100080045406090b00c1c0080030f0740601d60b1078040301c1c0071150000c03544120080d024034024103044d4000d842c015680840c00484842c82c401c8504441c2980c0071031889513600c02c40104000c0e8071855880700105076005d00c02051000c0e14641d40001c0c0302e28000c3ea1454a40e140e94040e8000307170322890b40300c100000c0c03400d501408503c0541d048202000680d48030b080c0100c0d640c24104400000304002140140d45440641d4054045405805c1d00020b4140003071042519001c0b184c010020b00c2c8002c50072602100c0c1c00907042c440301c0d42c15104440d00142050000300c00d2440c0460340c50440e1700a8078803500d1240010030307141d44148035a4404680c01281c1ca80b554407009440410403030300c01076040e65040704000203004088510040400234412074000f42c0caa08191502c01c1c10755032003ca00c0341c0418601024502e0054030b0044410481e0000e54498990b07440700070351001d00302e804c0c1d04140d0300356003041244030300306078003c050038100c40c1e5150559803003800001e000903182d800440164000741d0144900d030f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 503700872 1250 503699622 503699627
    0x204031712010e071d0324090709180f05070504150810110723030a050405032b05070204180c05010f0f0e0f0402071205040503010f150e1017010f1a01080601 69
    0x5030380c12100241100c7d6000d04c45074001d04000c94441c3c6000b2081d212600740302e107045042003140041c0000b50030901011005c85884195a0400180641602c040b01c2d580c006100e410311406000d000c1c064003c0c09403190b048102200580140b04050031382c41102c5154401715142e04c2000b0018808060031840d004894176481c40071074030502c82d02c80400000310000041d41d8100020000300140d91140c030307115840d01c410941000f40300100700309814103140d49a0713030300348000c03140c0741c40076440e8107082e911460180045001801c00c102618852001c503c8080240f0030340c207032a08205c5200743d0b00e001002d28428002c603020548514508045a074041c03000442d40707020740450900c41401f0340b00600b030521a407034100c25041a411114049000040c0c14091400c003070042d80d0840d10302d41c00500c44034480e074107101d5035a4054802c02500f5501d40c800300340300d01d02d4a20303000001d0070b50180d158110380b00940a2030003445038042e020440351805400000e036a41c0721841d0340c02503105031034a03881a075820005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 503702122 1250 503700872 503700917
    0x609081612150f050105040b0d030f050d02160c1505070803071b050d18120b0c030604150303080109060e0f070c050717031c02040506070f0201030204031712010e07 72
    0xc4601280e400ca00000306842e40c8556160809480700104082d49003a003448100d81e00c0c0101c0d0341c0104840e80e20340e80405d40211344040c90440614243c2c0d40e171028006020000d001d1009030391100d941314140031081c0107098110009640702c00b80c901e8911f06c9d00c290f09a8152141c2c220044c0310800a0000a070030303c2c051541c40c4040e50200c0001a0341b4a160b987d22428140c0e885044808103219105055075007814003c068041c000c201d074850442e0f175064803003219404009020b00400031340080001c810343c4031a04042200030102039100380b00c58070703494064400e0380e0900520107001d00d000cbc030000b194100404018006c104201c00c0c080f0941b1070355411540c0b405042c1d8255600e2150b4a000689100312807c15550846108099500d40c10a880c01e003400c83c2103200c03014803c0e40144010312281c1d980108481040da485419051803d24510068020703010f00e920103800c581e0182004102a00044010410003041d80403544190781c0303030051041c06240540780c7c440002d42032032203280011210780ea03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 503703372 1250 503702122 503702159
    0x30105130207030210060e0717090c042003090d030b040908120a090203191b030c0b0307022a10030608030306011404260d020c10030f021204080406090816 68
    0x10b4900300030240c0105c806032122540031460306040c0408001d6016406135020810a8400c551101d150801c52840c9a42d0b488030701c1040d214a96a154042001a240a4164907410058141e5840f4948816980c0e21820800e0205003c00c0c00c0c40b030031050618092141c51415540100d1140c00d0140944403c208803000170070151002c1d80e1400094056a81085410244803900c40780c010b480c07540d454144080b90700a83d404e007150603c10020f10010b015841c1ca2416a010340708000c1e100c1c2d5446170100c0c50702d9521201148c0709a000c0d01c8940301d40030105480e00d200c1c1c0044d0b070724542c88190311908400700d900318400c18510340c00501c00304245600c580012106040c4002c2c0d42c0b420942c5a1541d034019681003009050540c4110418403550801807003401d031b2404583c0040e100c0c001c08400807840101043c21540c0c1095035500d540101002540e041d50900508180d901410780760519205a07254064000d04022500e1f51900080c40e950000b10f088081c50040c600044061902550b240704850707a00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 503704622 1250 503703372 503703377
    0xf0c03060f1807090b010905090f04110102120a09031403030f010504110909090606090609160f09170d02010f020c120a0201090206030a05040b0109020a17091606210203010513020703 80
    0x10b66001d40c0c0301c01c10642000c0c0030301c40f5001880b5000070001400d50f180716889a402031010004002105541c0e00784640e02c9034001210001022a0343c2c0102d003000d9005500040b138800102c2d44100c40d42d4421203170701c20340744210b48034860340000f0f001c016a6030108981d0003248840d140018042c50405030401080e940441c504142007640c200005210800100c40d9070034a079000f81c003003219510708206401e410400588040000341800600355a80641010046081c0107880e01a0f42506120349880c20003030a070f0b40c0320110480703006d800464488440610480c0150309040550901c041c1038801c40310300d200c0e548005e001050902c1c00c642c1c0380c4d400c461032090640d5628061403000d07803140d00080d071040e5003d42e8001168613152815a10602040e0080030070340d407040c0804241c041d0802d00e500081722400d640340160340d03642207425140c041038541349500c427940d0341d0707000803c1604051540100c644024a400402480080e8a0b00702d00092182a42c00395040184882541032135006007a9940a072 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 503705872 1250 503704622 503704651
    0xc0c040e10061409060a060207060f0c0602030408210106090e0a0f050f160207060c020d0c1a09030c0f010203030103080f040936030e040c02071203110f0c03060f 71
    0x1038908003228040d0f480101411030b00702d200020ba2a00c46003003507201200b11940100a410910025680d0803140202000d110003059070000c800c0c01140064611644108155520320f400d01d0806425042041041c00000180300e2418081568081450580b00c55580381c1518a20b0030f600120391a0002d4082d0742060340d980107007620070110f0b0060904c00c03018100300919505024071210b68041000000e8021504040c005201441d40484142c00803901294030b00c01402c0107050003507821a1680c80751404ca18440c80342c0040418a10140a892400301c042d650130558803402d0201101220440d81c0c0140c00c100700500005a00d60003410361021008801411b1a840b000c03c2801c0b40e40c900c15040e91414201901c40301605803801c030410646c40040398000007100c030340d00a003002e450018814440d644850390030b10000e2080054200508070034031510b01aa41d5800c0c05084c108191803054217500410200508a040000b461211640080d0050089940300d84e8091000350003e002500200c080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 503707122 1250 503705872 503705893
    0x31e0c01062903150d031101050901150f08070b030405030c0d350402010f0c0606230307060203220302190608090a0f1118041103120c0c040e 62
    0x1d21408010703020403080c1044001020000000d507801c9035014007010102002006000c1e08801914190103a0079202c10280890030701d41515010043c03a0209070940c40c027810420142015086140c25075900c1d520310020940700d108000614103c2d005614955000d02d0041019005d9807004507071007801141524104814011118280107044143c40b00142803042c1002c414140b01141514011043e40c18100c030444c1803801c1c0f10700d000010070290511080c10345404090f8000c04040001903400001001341944495000d40c000c00381480c045180130941804080f20b0034000b64010644000e60001c1d82011061076900e881d00311007036101d40b0441c45c018000001601e91200d00f0380c2101d144016800400d04200000700a4180145410b0030381e4030000b5500045820000e03021103554110700e00030500701024020070402c0d06070040d402481e40800c0c007000107100711500c42101c0b9800441c21f80e030040201c064800114020f800410200c1d070002d01e501403886c9865880342001015902c00e1300c003e5800e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 503708372 1250 503707122 503707147
    0x60602071e0506040b1c02121603020f0c0703060b01030e060103080d021911011505100c0c050306090a0605010807030c0b090a080609010e0c032d01020c1b01080a090203031e 76
    0x41395100d40ca0189000c20118140190613440f08040410b01c1d00071401c084180303182400010703024100c040c8501c9002030984005200350100e032100403211070907560301c80d5640c07201940c40081d0700c0190340703452526121092640c0300b40261420310b26640e0090030079900715110380c00d46522940303000780032036800c001d03a941c80c0d00f00f00a80c01e052405a160324100340031404400b0709440000003240014140da0106005540c3c8122820007040b245242480b08502c0301c0c9000d061085540d0480303940f604c10201002070b8881d0000e00d1a0010b80f1070101400242d0781c0b0513541e5a100320034000100300303007016401440a14590b1000e0214440010143c1307003140e589030f90003420807100703855403640c59440d01c031000e88103d001c05c04070541c05030650080112807a5001c001118041e03220000044211120034040c4004094060710400f0014400b070711407160142c5400744800200c2c10459010405c4000026620030040c81802d50664019010b1403609c0a80c10000641214403401815070300028001c0307074031041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 503709622 1250 503708372 503708377
    0x70f0809070e0103150e0c0625050a0c061d0109091a0409080409110306100305070908030c070e0a050714031f090f050c070f0b04150f06050a0504060602071e0506 71
    0x50140082c500c0804c54a152417003910807845c0039010a600c144070070105504d601d002c494080e240d0304c403544900b40b81080c001440a4401c0340c00740c0107101d00b020740d07018001c444407801e0441324142c41d1600040740c2008078038082c070601c1070850f010440b40349081080c01d00d030b40c0120140d0007405403041d91a801d407034000740484030b1410003a03e10303031004242884403800c140f283e400d000140c609071a00f50700d4000e00050709840f04003c000304050300e0b1804103000e00d0045003000040d240c0c0c2019640c440792140e540d11313a1001548a00c070343e102551300101e00d484d8014494240500c03410740da84688910b91400e50340e040d0740042e0403a88401d00100c9000c1c1d403050082c4041e801f900d0b48a0000c2419000c2080541c1a128060140314545108101440c000382401040500c0a40d01010680d843d035940d08002d05081141e500030003c50f03080c684240805003031a0312490035203004403040111035869106100880390a07005410140c0c0c00034206102c210224184034548100007003242c06501e07100c030081607868 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 503710872 1250 503709622 503709629
    0x80708070c0b04022718161a040506070b16030e15090715020c18060d0f030c1707021504061d0301061d04170f070209060d0506010f0608060405070f0809070e01 70
    0x15003440c42841000716002005d041140144001400101f81c040641072168100e481142847d00c0030101030683c603034134882900d0040c140100040e445a031241000b2015550460300728140070f09134070b08081c1031400b922400c01ca801c4028000c1a4142c0d042d10180b030020030150040545100d014800a1070a50390030713660303c1c60304056025050b00c55040342808001400c1d240c21a204035251400c0000580704d8206944e08290003600b0310310046907070300b415180b520980f107002d1700700c40805032801d220000045c0144034007442910701810b03d0011021200c5140640e01441001a080007940500c410003580c4c4034142c14401800004d0321a1f480e544102e1103c1e00641c82d940300138144007040180030140c056112143c010191961502d400c1142c06d024501c1292402031180031001e010501070b803a601700403e03000b80e025080b90318558440c0a81200c4488a20030440001e1030b4500083e030780e08103805081e004070055140c454607031940303e60030f039a28240100204072500c24054001168022050900c1c000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 503712122 1250 503710872 503710939
    0xa0509100503121207120f0c0503010305060702070b0d09060e07080109030909060b160305120f090d020102090d11010c0501020a03140a0b22060306110406080708070c0b0402 76
    0x12945071106140c2400d400d40c0044a90074400e218461340b1005001007294420080d1030004484001d25410f50010080140988500b0f4540000e0841890700400154140c900880803110b450340c1c0d0a00c101d0f46c07803580c2c0c05801c440300c10a00007c402e80e4581c0d00000b4a6a00c500c1c4046140c000324002680b40071116880742c00311340e44811804c400d1580050340304d8054003134030308148a1207050403165000c1d07110714005500014401e1a80d4000d05104109440d0700100810f626585400d02402580045000380e911111b903000c1c0f4011007202d44e00500c00c0b10f07084903028201e21500b00050321988607228004111905110900d0581d200040302840200f000c900b550300c00141d000070040c650410101c00400042d000c0b46031140d5100b15644115036028903d07079a00c040070910044a0203080030781440d501c0100b00030b04100c0c2e803403405840e41c4043d0059508a640e0b2103015910808121506001640c0050205208194160200c1c101003116544a40083c2903203402c1c14000c42c0042c081704003102404e40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 503713372 1250 503712122 503712151
    0x34204050303040317010e01030b220f11010903031d01091a0c0d0f020a0605060604180b03150f01060e01021615021c02031b0a0506090d030b100912020a0509 69
    0x2c00d900030094058175076102821004941c1040070102d80390a040c04043d210501450018a002c035658643c990148040c19000d5487c0a0500c0c0c5031101e510703a40c004603401265251300320b01b294410f0354071800710f98240c5d442c580c1e800c101c0881126103003101e03c16103040200009011615180340c00005d0402c0c60070360744456036554610026401c080c40320311403e08008000b040728640c3c6500180604060b0b4004c0000160b6403584030000b10300b4400c981c4012014000a804031160788400c0d40159260070003542610003614070198400b0a500089620000c9040110014050248200f03840b215854041c0116403c20968107260842d601c4168000c000c44800319440900099043c0558510040218803245006012450181d105d02546008003162501070341c0d00b1001d01e8041105401550300001564003038113184c44641e8481d0400200200481d00700340009032242828000c1d101a1146035840f4140c3c541021116040c22104042c2030f0780c0304240c42c0010941e43da8111106015019006a280 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 503714622 1250 503713372 503713381
    0x16020a17070b040e071107031b0608090c01050717071a010501030f0504122102040e060a0b09010c020405130203070905010603240b0912010c02010515034204050303 72
    0x514054039904104030300b40062104004540702e0880349170308148141031407040501c221080614041066002504854041d22881c0d5520a40000b1105446e031560320800340c0e40d07982411654500c50786100b540061001c10001c0041001c0800e02144111850078003490084582c41d21483c0102c00c8011005c07200c60350004001d150382500c11000c24240c1c0d21414003042c5042c0c0c490040900400b1260310510001d071808c5207427031004c81e4584c118801d903140c04646031915a81d01080007402205c485025100300c2c035010941d00303112000d9902812050b500e07a119210503500784006014058030000060703c0410f51080140c1d000e00c00c0704080c001c100400a555850540d000303050310395041142c3c0c80403139014242000d000040e207443c4142c03055101890750301c10580e80443e5121980104801c000d51808010a020581c19000a4020341502c00e1890f00025803104141d207072481015004180801d00c40c0d118084d010714240000301c10344240000002080040d18610588000c81d01154982c10000c00c22 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 503715872 1250 503714622 503714669
    0x3102412090317070e0603040b01050f0102150c0a0c050f060406050105010e060706052205010b0f0109060f180801112206020d110109020d0b0711030903030a030216020a 74
    0x144889008a009100307000594a0191025002620003c50180f0038030000328018044c650480314280081c0c10f4a503646000d080c1003501e2a828043e00d84902c0440c001303c41c080d8400541d107009004d40d4054951b15485514050089512a420410512041c015030101103034042c01882412004140500240c0c40e0a107000d9003101d03016080300e0305101d010809510145ca800041e6041c056110380009481d8075182c41c50305104003000c03001c403103101001ca81e40007040010342200319680350541e0b060011240e2440195081c0c3d2040c0140800203102c0041400f006101b921200580c040c144407a800b09611500702d5402e4452804000c01c0041e0300059001c200d4680c103062035201c0241d280071818150a0400003900da0201147c00005c2100110f0101d4180c4800e46c803a0f0040340d8000c0854544004a2812304034064013107078628049411030910788030300c1c040801214840480280550b00d0108441c80c207800941014022562014902900000584403c40383c4400f60640d10b01d598245040c46098 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 503717122 1250 503715872 503715887
    0xc0302060f0a02161805060d06051314030304150506150c0705030c0d03141e07030c05061f2601020a0201090c0902070c1205010e07090507020d0c05070b031024 70
    0x4d0004950280d882003113035620048081c80001c12810010513161585000647c04100b50f0902616262610b000e00200d2456960021921485038184100c0c2c040300c0548141c032030004450180100340010780051011015500c4158030000c01000303051440808011081c4981003480400c8060b0300130b207401d03c22480d0402c02500c0c662022607034a01300c0301c2540c0c1c000b1310074040001d00d001c046070046404003041001e8101d622520702010300b426211001c1d8100100030040004090b51346024403400702da442c1c2c0505590140e40418030458481081c60f00400350150840f4640d03a04009620f40c801e0100e9040031300040050180c198004150301d82c0c10304000c0414091540060400c0c0d02c104034240000c2c031508400411100547d4420003107d80030b060442c050609991807500c4c0d40030307618011481480a40c0007600815450342155443c03d50040162850155064045e2655002c0001001907501031030046030311403034000001c54910f6441c01c90031a21084070541c1071100f0240d140f071070b020b00c0d403003c038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 503718372 1250 503717122 503717143
    0x1020c15010308180d170702090703140c09010e0310050f010501050a0e010302031306090f110d0201020a120201021207080901050c0a08131e0c050a0515160c0302060f0a02 75
    0x6403401940b440d0754088052243c0c41d641c03200446000c2e0500e4007035071219900c419064001c180400c81d6442c071949a64564402001207100e0208580424045d522902c030700582c8461841400080b510342078a080002d81103a4041810000b040302c010115481c01e0000445010040d00045014109494110040700050700003504101c1c080c810406003e0f030242070803210360400c2c240181e51391103400300741c5060060300c0e401a28490a0000000c10002c1140c819500d1a00a441020b12090010208403102c5039545019005038440712072000402c4140b1011f9008000b00c1c000140361800701c2014103e4200d01b10780d01c40200f941c010070410021070a000d0182d00404c100c0c5d8940c40c2c81d40500b0041c1401c48050310000b9041404007140080100792100e44590200d10603041c1000ca003149004007007007400340103940c020b04c02000d00240505100402420050388240c40d603003082002d82c1d02032400615004152407450801d4000800b41e20b03031310020100c6039840b46400381e40c1d8280a1020349050164007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 503719622 1250 503718372 503718403
    0x14040609020c030a0e1908060901150f14060c01060303050403201c05010603060203150102211605011503080703030b030d1b03091a070b090105010b070b04060e010c0201020c 76
    0x21822107010b0010044441c0420941050364142800c0c0c1c0100d2401c0c08822180c40d0840d003000400f141b00f8500040d15171041d0715210082c080a0704d8001d810780e444109100d0384414020604081c07010501050170a1448140608140e06041c00d00c0c04040c01c0d9030090741709402080c0006821b205112405004030311888900100c0d14080c407058001ca80e002041100020005d00d0740518401005400e4016400a5401100a5440b03042414243c00d2100d41c1c480800e0141c13240015610800108201c440410301e0a0002581004a00100106060250716040f5035039540c0f00a0301900c6c02103060210050340c090000d0a4a0b00003c0c030b005001c649080d00c4240c4a58030401240900951101c2c0c0303d1203a80601d092905801e4962506aa007040359800801030300480c82c10541d110029030000c4c0c00858011b4600907142c1d11124051422114207000d4500250400c0251002090400e542107410500c41c910018070307212203201441c00c40c4c1403004030b0f00040c0d4000504444001301085104001c00a01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 503720872 1250 503719622 503719627
    0xc0c170a0810050f040e011b080106020c2709030c060a05191b0e13060803030601080115020d030b06040e07080f0105040b1806010c0b01080f01050a050103081c0b0a1404060902 77
    0x5001c1d0a20310401c4d0300c00d40e11040c21104064082d0400c9803120f290144004540043c40710203002c09109006680040c801c190450515180c9092a80c50f0350610040f96410750f03100c080c0c100d1134400002d1240788944020000408100020004039200e0a00801e0000d082d06052810342803022283c00c50824540c20700d0100410500340a90450404400b0308003118420802c0e004240d19030480301c40752060344c1c03803c100020369500c00310081d80f06845c00d9031220307596030700d9100d240400c0301d030010300c0c00040c4d220000305114603010717038030040c0040c50042013a401c050392803240603e5404215031800000d45040d09000d41540151441d03070140004440c01e0112907483d0010581c40720700c510074242c2100341c2300082816030b4020641c100300c0340d80000d2014943c2da1503480075943d40040807100170361507191000040d811006485001d040e40c0e803107405945800020b0300c1c1302c0114102551003540207599800415a55a01e0800301c0004001c01c1410542c0100104200011030350198450740026004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 503722122 1250 503720872 503720879
    0x41030a15050a140d23060a0b0307080a120507120e040f0605010212030c040e180c180414011b091e0609050607031103030f01140d0c06030c0c170a0810 66
    0x1a140814500101955044d124807484d04100780152000106959075a01d1107859603070800020501600c80c18003000f050080e10742120505559003038a100700c54050708040c01140011300c0403400451118500e29003241001d0340c0e40c4032400e140151111010200d0b41c01d03035610b02ca0b07003494081ea0b0800000c1c14020000b035440d000000c0c1d1101c5c24011886000b038800400201641c10640a54002d86010b021511300b078a00890000014103801d024007506110b140b90b9211507181c210381c81491b1002c8042000708680341c1d0340e036480308a150b000140c00c00b5500ea1035045d24541c544c803c0100541070720783d58602d41c1e40c50140254402c4d800c0c01780c0481c080784254810312810ba08500010100c903801e5030460364910103800c0444075100110704160281c000002071000d070301032010005040c0c40490788000a010075040c20080006001c04c1c0003811a404900f0070000c0718042d9000c00c10314000303418020501c0c60140d84510341d0500c5001000030600c0b01241c441c00040d44506038560007a1900f08a03a180ea05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 503723372 1250 503722122 503722139
    0xb0310052205010e0a0302070513050c0405062a0313090501140d14030d051504051501050c01141006020c01020a08190e060c0706080741030a15050a 65
    0x1034041c03079403014484191441c0100402540f0452100c8103940680306060384c6890000d480d245130b441600e200d42c1705c000b0080e45500380b910802d406102d5100d0107500d00f916200920a05410400c0600344203006258000f40c4007400f401110161190030000d15515000c000c001303812000c464001405a074030344401031080c00c4100c030380181c0c600b80c100c0340c0b4404003e003882d01c1a0f140b078200641c50154080821060f041000640025006461440140342c13003100030000e0000300e5070229003070f280c86840303207005641650027000100411050b4200115174805451448180c58200395000180b401c0040c600f0001c441c0e040c005088030820910141008510503101c0c480e160042074000b035580303d60070000080c41c0b8060001c145501c034000d003440da00c80119408803502d628151050b04080f030030315000280002e105900c85402d00e80080400c0880704002910320300d07680054445512084c410070002000d00c035654002d54481d83d00c005011880e007860304841013550025070302c10b0703000d0f03080c149091103440c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 503724622 1250 503723372 503723401
    0x705040f0911090d0c2c180a080406080103020102070b030609070e1306080318040c08160e040e0d0809010b0d0b040f060216121e120f060b0c06010f05030c01080c13090b031005 77
    0x8807451940704c1507042404a040c280030020b4801021500c000038002f4440343c00c0049241205c2c000d070207454826075968507540040c032044900320303403012540e4006a001e5000385654802c0c0c85c005090661001c03003a01c49801210703002c0e0003440c072a50004c1150300c906900c01da0f03000c0051340300361814405a0000c1070040c0040d2005000100c6078680d000740160203601c914003c25000f1802001408082c500b5421140c4600a80b05480001001d5900081d49440140108010204c0240c0038551104080d180d03001e910101820880d14090094100300201d1054006030054151440c804001c0d2802031409902c00c2c4241c0a1000031b110f43c0560f805012460510100078184030340c144141051004540700c0010b10306c140c03422200711329004010500c01090300242000b01414006c44a140e41c0310f088000c1d180505225080c0e040e880030803003030346a504c154140c98003c1c002c45d1405082c800342207584002203020b5002110710680d51a00c20381f440c07404000390168404101010802c40c20018003c0e140707036 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 503725872 1250 503724622 503724631
    0xd060f0f05060c0a020a1206150501050306010c020a050603071106010f0e0703050402221509110d09030207030f060c09060804050a1103030c011d01050705040f0911090d0c2c 76
    0x100e101080b10550002c1c24413542c441e066000b4190108961203801c001c42a81c481e010a0311554a08028902da80d040c00c1d81c2d0205030b4505845039402d60340c03001d004480b250000801241c1014407010009020344036240a10b00480c0540c440c0402d102e035203098240f8007001607108400802c2165400c2010020354a003c6800c4881031038042802e41e03950001c074448118540c0b88a0103841c003031101c00600e48a81c0d00c000041c1c0002e0343d019000340e94a084030002e55000303600c00c54040d6420810b40101842c140d1001080310f1103401981c640307541d01d843c4c0e02101e184054040c1c0c1c42070344804808500c90360041000c0094035150801c501c1038202034840590310000c500000b04a201031405040b070581d03041080e0b54801803084020f02071510542daa14100300800c940c1d205042d828500420205401031095a042e208060900e000d00c0c0d00e4041c0000140504011728454a43d0401c40c06185844000c40f10403024011030540c2c501c41e150032030480700700a40700b11111505080724115242c0120321500300d03410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 503727122 1250 503725872 503725879
    0x1d150403050403030e04060b0711100c050309091b0310051305010b032412030d0507020303060d080a140a27050f120114010e011a0a05031609090e01020d060f0f05 71
    0x408241d40b01050087c034281d0845210b2140c0842c41408014007070641e03400c1c02c071003901c00b02c4119035080020744c1c2d0405014401400c940091203000414281208007039884494501d103124202c1109102c0181940191000300b1030b01c003000001d02070350800b0310040c10b0f090086002041650b1400b10220014000034141c52035a03160718507494008070078a940c003100507000900c82c18000300d080c884241e0382e601040c00e040a00c2e0400d40040c0c4021300110507644540303805408600444001da5402c1a2070303003d00021024483c1400c914040c02130b001001e09020304c10b80e11403080c2c10034103050755035410b0000b0620308000b09035841e041c030140e242d0003c60700240e00d040e101140700308030340d040c1540503003401c22280442c0740c0074000001c0e502c4204a18141245d2080d540d4484803090107410780c1003841071a82d84000325100300040b540014110b0100882903000d460310400c2e2a88440400003a42c00b42c1c0462001a0740201d400f034045134251003000010840702c003203100610b01c0d00251130100441d43c03181c680b1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 503728372 1250 503727122 503727137
    0x10b070f1a0705070b01080703030206061002011b17091c03270b0103120c1a06012f0d0509090a05040f0f030f0806030a020a050909101d15040305040303 67
    0x10805549034640c118455122032003807074a05070340010001c0d04100c60a4440c00d49110000039171080c0030406074240c941550152000d42d40715024032482421140c603040442d940d800f403058440c050300440c6100d010076659000812031201002010494002d400140e03d0b03040012420b000300c0803c40d61041030000c0d0700303002c01c03010120950054018880403070743c41c0d80501b01c1c000c0c004105c50078000354181d07449aa41c05003030140d4804201c43c58088803100800100f18000160040c901b0031071096881081450482202031515052040f0301c4207003500b811001c441141203050b04641406188034010706440c11600b07150f40b02000070148030700580319a030019034800114040c0200150340e61002d6801201c000003907041d500c0d00409038200a842c00d00000c10920205803185804504901525002040d10708044d0070a810400120006041c0c1c043e14810001d40da01408018060804003416041102600c401d20558060038001110700700e801000c030031420040003d41110950f02640d03010b00e801c04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 503729622 1250 503728372 503728403
    0xe031912050418020409060b040e1909021201060611030a02032502030d090807050103060e0609071803050a0b0603070b0f07030207030218060f040506180a060302041107140303010b07 80
    0x159107106642001e01c18110412800c1d88030b03c00d0390024002c0300d0b130071482001001d030390b1881407145025a00865400e2442400401d10401203940410701c0d04551902c00102d140b603070350008860401c0001c0c1c410040e512640d0030002c698200482c242c05600c4140510700c0c00c401c8043c004c1d184c5c420112026079009816422000c3c2131200b00310a14525800741c12030f0900810f0707a0001d0403c481621600d407140c403950402240302d502c02e0096600311501544000e4041c2c548204010b00d4a400524404c1004210b4064405102c802c000c518002c5006202078200c400c0c850401c000101e500030080c5010381d11201c070400c50040050b01310b4044041c200f40319500d0300403d1900300e0900300e0640c4003961050a107810300e444c0d17401c4041e001c2d005407000c807800290443e010051109550701281d42a5100c0b1034071000c44005502c0310f102d2a88181280700000e51385407260300140131160000d0f040c0b00700600118080041100f815414030345500200000c500b590f14214440c1c403a413140d008000c0000c1c80021104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 503730872 1250 503729622 503729627
    0x6060203070201111e0318040c090312020a020a170c0904080909070504090606050d05070201200a0c0209180d11060412030e0d030b10050c0c01081f03120e031912 71
    0x1c80f4000171941a000356070329108002e0345c1d2508000c0da411400040783c90703e1520b0380382070711035081c914038141c880c0007000c1c1ca0f68840400b0910509007600560140310800f4006a480d2110303100a000c843e46104a503900008007076180440c3c402e100d0f405202d80900f400085504101a208000001c99520442c0d944071903084603503014580c022100103080c2500800c01c15005005014500051901042156201c80c3d0407400da0350342c0344216400ba41004d10300c0e440c0100c19001020b0500e49030400c00d014480903070100340103140480b08150003841c116400100300d4401d00074010031120034900f80c41003c208281c40ca0b201c0c03101510042c07400d101796012410090081d00000442c1400c00180c1d0f41017044d401000c0d024000c02d00845203c3c07403400011200082c01402594a42e0804a0080001500800056a203014007038042d41da103400303c243c08a8106142120f100255114210502c440b038048100544880c10182920b0f210b078115007088080036108028035001542c00c0b006443c0c216000d800706 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 503732122 1250 503730872 503730883
    0x70e04020a0b1309050a0221060117151206090706050c060c070611070f020111070605120604200901080a05040f061d0f0309030d030c02120904110a0e030d030606020307020111 77
    0x140082c1807500300449102c00c0da000c8c0c4000070301000c01c2c1d41c0c04454100e000d0003031a000c50310b16001c5501d20b420b04001e211142e8425601c082101561501e4070000c900041d61400803803201c1c40c90f64044010403959010a2014100800c0300d814600d042600c01a909500c401f070003405440c01d40310204600041c0483d9030400c2007484a45c4407000e0303460b0707a0740c01c103501c1d506190309c010381c00b14421842c00520200000f80c5002194000d5840c40e080c07088507000641c01c0c080190055920070784800315040b0ba0790204a080001080f0b0441c810780d01c01001d0009840254000d02e0441c0312881e006c10800881d288202042041d603105400080c540d94071100608d0310042582004554130540039181c8084038000f0090035015400c81c03ca507807030707400c20900f1802d07603500c1030110300107800481c1c518a00e81249005800310303901c02000403880b9881070403119155042105084000742801070707152000d08007800b20b22010105450140540c60602201940d284181d0b04020704009200d0f50014103413106000c0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 503733372 1250 503732122 503732129
    0x309080d11030405010606020c0d030e030a240b01030209010806061b01062606060f1302040914072012090f040c0c0201020f0105100e150a0602070602070e04020a0b13 73
    0x3000c2014481000c116001600102e41c212003641c03800704003064580c0001039200000b54002d1140795032820544c0c4c110307044401188142c1e01485414241d03000642c010111001e05c20280a1201c144071403064540150340000b1527081c145403040240e0b02c02644c1c8800350030381c1700c04151401569512924410b4802d52950903c180b044e52030118089804052250480c240702000a2440350070140074000a840d00000e071000c44e400640041d02a049007011071650300c117243c0c420300c01400d0a0741c800f4001d0541e819110203a281708078102c100207807150010a880717186100744802d1038200350b07910001c03940e8901104e4242c14407040440c0700102c80d99a08200a04058060028010795218080180401100f041c040380580190035031500034060502c10307a481500305d588010001c40c5040103049021001070000507200c209c90030f04042545407140c1690040480d1f50040292914050000707052241e160031140d000082441804050f940c1c2c0400c1d0400c1d9000c40b050316545c0d10204400718181000c991 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 503734622 1250 503733372 503733397
    0xd0618020a08061501050903420f0108241306060801050a06051203040e040c0e07090f0f061d0307030c090506040b0414190605031e010b0303030c0406030908 69
    0x1000400c00701408214180144004d4091499003984180103445134000e00284640552040c03080420044550745c04400e41a03d8200343c460b0405600b001d07042d410780591054a911582e031052103810a8900440703401001414042c0c8401c440c40d14400225420414010044007401d0010452145038400714803030280e444001003000c607035104030160107800b0481d95500700c1840c0c00c00024450800407520f080d0700410002640c03815007040d40c4c60740b901e01d01078000e0f41e02c00030009002c40e14080622149000355150784800210515001140502126541100100ca000c0050070407896030009914206842c001928507006c02c0341d10042841c007819684090185002d0410001f1448843d6000501a000948090244c420075005001c00e58050b5000d041c03e0080794070010b022124451101000384025440204031030342d03144000f07494202403082c0804070038014a4030540441c404d20842c610200103034059030440c07034180405075103405144241c030289a151003071ba00410000f2401c5845030750000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 503735872 1250 503734622 503734639
    0x50c030f0c1603020c0901080c0d0305160b1315272108070f0806010f0302030a0e010509030a180501050702090c041e090b0405101a07140303040b0c0301050d061802 72
    0xf414000d41d0743da0f0301c80c010341c0103404000001c224088041800700083c100a011400462201c0e038003110654840407502044c02c5200c1500c4001a01d8443c1d818000c1140840c00280c5a4035070600042440d140900f010b00d092822a0045113009102d080f00301c543d000340d4082d800001d20f130800100c000c001e4889001104070b401041d0309071030741002016015848075a25400321907071014044d51b121509035100c42c041040d645100403031501ca03400a681c84500803502040503c0e07079403410b90948200b52220f0009400c0861074590f8164003079030101d43c0c07100b02015a40c03001d160500181070351149aa0103030003506640300003000075a01104980003400c0205181440c00c9aa040e1560b0b19066809000207a42c24118503036000d1406001c3d15001700c065130741049080c1d14001019a482c80b0001030321046000600088000c102c6841c42620681d92100c065940d920381303440c102c0c551a4006009015001c001e00061241d51942882082141d82c454000242d5142c404820f060713031026058020760000c0c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 503737122 1250 503735872 503735917
    0x103110a02010608160f050d060f09030e191d0402010c050f060105090c0c0c010e0111010203010902031015020d0305070e030f0a0c080a020f04020d111303050d03050c030f0c 76
    0x55010908584c0b05409640e440540d0a03000380701800785104655800b10208024001d034236001c82c40b405031034030900700040c038500c0d1402c108090307c0c2ca0030b40550204008441d01c05450800c804050011003200c5005c1086504200c0140e550440d40143c203280300c483c8070005402c41e4081c8101d4040190030600b121080307018bd40c0b00725941d08007400703503901a210003c0400c0070881c401095407100003050f4060540d0000000044501001c440c2c842da040004503060504500310a01c0118060101c1e402c01590340c4c13a00c40b10364a0312458075031040c0749860160203810313020b590200700d56004140515000c07586d03484541c02190300000383e69026605000e600a0325804410000b0407900061203050744690182c0d444580d10307200d6001810280d084098124001c07002c0c1b605d07500800c50030125500003c0c030030840461300501030300b002c1c0e80c0c6080c0307540c49402031050103410080802d01841a160921151820942540c2c25000142500700d0740220b940120f0802001c0c002a110a001040035102c154100b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 503738372 1250 503737122 503737127
    0x19020a170c0102010b012f010f0f050405120a1d0a0f06050c06010501093503041d061903020f0a031205220506072307030809011d0307140103110a 64
    0x181407040034055860445030b41d001e54000c3d021007101600303026208840218200a4002c00d1002c8032031300c031255588501c026980380f0349200314501007540b04400219031030b0516013a440c144032900300c035074610010b200e24100980d02c0035003e0f95600c070f4012030089004890703010410b4203d00e500244000c04020002050700c41d441005401e98004200c111591640e0320740c01551030f5401c03400b40707525070322800500e4a6803070480224010041809403144108401a405041c103540142d003100c004541c0303101240020001c80c0d01803a810040440b61403a8600a1100441007442140f000038003402982000c06015507469100c0c1c001035800810014a4140081c00204140e101014203038130285621266640451000a82000d0f502c010f40300c04d25050054482d0320031410310701122206c0844400300c03802c0802d01032000c18000c500c60350b0345580f03400c2d41500140c2178050f05100181569050a2181519600081d2013021280c9810014040d2181c410049015005000c00d00c030720740a000400403802e03507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 503739622 1250 503738372 503738383
    0x130803030a090201031b1b020613030308041a130f050c0a0f1509031502220603090c05030c011e0315080c0406080303040804030201361701090519020a17 67
    0x1803003640d00b00642e05440c6c0180ca489070590006100091a81034036200400f65641d44071082c07400244614101404503100111305d82042d0811000144618144400c000148440e84487d400759000d0100f94682840c4400300c2c0204044064416170b03c070340c0400203119090104800d2600d0141c0510811501d402c5c0c10281035089208980135180c200c08800d090900ca240d052064039406826400d00c00401904d800194000328455640c4004202c001203c10020f00020001003426440100d020360740780c1040074505005500c0b150207a0002c1040c100543e80c081c0403050341c4401400e6805c1c0d00c8007904402c90042802c442000038207420041e021800540004000c0e00082003102c041c040e083c2c8030001c8903102e00090340d000b040020180700501c015801419803c004d286012401c4500341d02800400c02c4a1240c0d061290034a102c1d44c1007800741c0028442084000d0182100922500c0142d0751040d648611007010b449445140314003060131075984000540041c03903404003070303400140d240c001d25440c1d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 503740872 1250 503739622 503739641
    0x90406030812090709021c0906060803042c0f1b0c01060308070606060203040308030a4a0303070504060311090301020a261311011202130e10080d05130803030a 70
    0x1d2050510005117581c0c3c0c3e00813103402c0144001c00d016406554000c0c400500110030703003103420b1a1119404a5111010000b900060540c8503120712284880c0c80c3c1a11202300d4a4030300d40c80748540c1d0707040140b114101d03501280c01c0050840401000914008045154090103906030520750030300200205010000010307001060146600f041255601c80050740e40340700b00c0c4002441c0180c20300000301e07403001651114402104207101401c0106030095011020210544400045000f01c610100c00094940f41980080e0180d00210718504040c200034080e8001c6205220426854065020035208684140c0d54034140140c025525040c02e601d002d401020403843c240030019101c4013441d8803d58118140e8050600d41294001c08410f9466517001510014032017814404800382c05220020346c0d1005121220600303600352201801e2201d2041454405800c003407128042000904c003242012440c20b603100120704009650b00b20030800789038241084e41c00348903540008000c00541c00c8007604810400c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 503742122 1250 503740872 503740891
    0x1f09030302010e03030f041205070c180c02010920040902090708011a04050d080c011409010213050915120a12031505180106030b04090209041103012708090406030812 73
    0x10303e0054590fa640c0c0e0004441c002c0c030009009010901049481c910000070001c03900d4240e00d072001e5502d54648400c20703a400103520b400d1000300e400c041c950512441d41d00500c548000d1102c4c490b2074a4076040b25001420600100c48000001a4155501d41c00001d1550303010b45683d02903e4019030141c8000f800f4031500304540880381d98100c030380882c44212025903c00a104080744a15521807001c10340200c2c011a4280d9070700c0345001d500b1828200ca90307220f040140c0001d60b5483c1001380700c030408111a8000790058204c00b05005c0080c0c4031101803100402c080d12010a07081e1f4411402d8600340799410050003680091001000e81075240d00500000894440710700445966042031101c01e1209802c0c1c04201b08020005002c824425049034403000d50040000c9415403e1b5000200f60050a880c00c4440c0e00b400b847c10710781400c0a01800030411082c2000300303030141d000828840581c0c50b20b1001859503c001030503d42c02d035590b80c4940b0245410034041074951042d013502c040102025200c3c07005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 503743372 1250 503742122 503742131
    0x60403060518160b070605040c0806100312020c061c09150e0c150d0506011103040605030f06060403020a030303020a1404080a0b10140d05120313060b040603020906010e1f0903030201 80
    0x2000004003c030b4600f1242905141450000192940002441d0281c01281c003000c40240000c0d807003108100075405600c00c0c901c0482400d00e1450103800d250341303200200095400003036900e441580d0340c2081c2d6070481e0b0300c8018000300201280c3c82e40010018601c0c01048085030000425001016600403000f24003508216180200f440041002d612000100c800c50a40d00304100030b800f40c1282c01c480c1c2c00030810304002c180e08007010700e0329046400c260401d400141c004010030104110480707650388c000f80c051725903520b00b13825900812a036a940c2c0c08094185a000903002442700e10401001c5d00d0f804480795010303103071a1170300d044a440b403002d800d09a036075400d500003007440c83d081c0c8040c010454400041003d0128240c0301030182d002030b6030b44191468001e00700c5440c051166070700150310034600d0031400c00f00001c0501d044000c0303030744000c07103a07001d9840c01c00d080c40161928000c41d80c00c2102405c00c0c0311030501003400101000b50501c0848040004070200444494018402c1000c0d20b100760020f20 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 503744622 1250 503743372 503743393
    0x8010501080304050906060d0605150703080c0301032607020603040b0103032c011103120103081903020a14031906090c030f02030609013b01060f020114010e06060403060518 76
    0x160b030b902031401003980c0000520003007415403a20314000d00118074107020104a455440001030558110f004030f92031400c40004e40d500405a100c403281d50f102d051900e46c1070965041d600e550060b030130f13403014040158900740c00c141c0230410b0040c20780d480e19a004220a40d60f00c0c2500e0012100c00c000c0c802240880c80b069010b00c801328000e0702c0440030811040c0c18034a803981c17250044a02402445d0b00c00b8182c0010400c10142c1110054042e0185004800b56603403020140303072502608144540c01c00805106100701c0a00b59400302c0c100d4a1013124100071912900c1e000601d401240004850580c2180303001d84c0002d2050282d000080b040d5035a803410441494401d520000340d02c03044071420b07480027110700107009801251001ca00e800d00a1101c0d0150603544114421401c105220080c0c0132506210042128550108150b10241002e100030b1115440d24048a1003040040c040d00844100f0b880000300b068555070203440003560095420b0041d03041902010303600f40301c2842e8600070313030082c0e90330308 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 503745872 1250 503744622 503744639
    0x30c0d0f02090f1c1b050d0c150203041508071209050105090d0905060d020d0b4b040b0301180803042a090203090106030f110a140303040302120106120c08010501 71
    0x600b000306100b0156413008095030398898032a03109085100b00300344021021034652600c3e100c01405902c01c002d140103203807e0130f6200031b540d10350341002000c43d40304000030302c00b5102c008000980c0103950309140c3c0d0740d42c640c294280e45e40c1c00c2e1810450300c9945020b851780d040c064150001402403405c0c3c815101180741c626822a1713100c1050050f10b07000007042000003000c41e02c035801000e01c40410280010012402000640240c8200c01c0492034610110b10020120141c0c0503500b07803032440f401c00050614004010015224822051180310796502d200c4d070415500d0070b401c10300072280c0d100c41040c03880c61030340307001c124039001528140ca505c0c500900b204108048241913041d940749030080700d1710240c9030520030b034041d520062955881e95201c40300040056152440c3c01c84151203001d205074410291000c0c00000c850325803007100c50b00c1c030402c0300e60403c0e10044111419641c06480d40001d82c500340300382d1409014240c2c000d00066802810101c1030100030fa12200a0f00c00500003400303d40d0b41d50030741 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 503747122 1250 503745872 503745889
    0x105030303091e03040e10080f0a0b04061a150a081e010b0d060308120403111c0f090b03070309031101060302150702130f0b0f0102060f0606030c0d0f02090f 69
    0x181c1c03140c0f031800e80c1c19010140030821850303000b00703c0b0b00d496120000c10290210580b2010600d0700301c9030040c0542c240500c0721460b004210f8004004054158642c00200a4040c0000d40142c2c4c0d110300382d541807140b5130542c0d041c0d110003030440c211248854050490f0703a4858040c0b507001428207000715002c1110001d00220641c1d00d038809040d9030342018045030055120714200496656500d40000001c0c2d008005081030040e041154480fa00d840d04015000c03c4003651020642d801884900a804800300882003002c0005e1501c014400484503050301d81503600d40015078090808010002929031507048000d00c0761080c0e0707a00081c2c060003000c450991f0114000250300a00442c019219030303011001402885000034014811a4250b0034043c04030380c01403543c1003071552904c0042c0c0d26401c0410441400d80028802458945003090040c00c0c0144080d120500c29000000850144180441503d2008409400801001e6502c0c0b000c0c3e4003d40c031003042c1c5406014850440c13001460151030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 503748372 1250 503747122 503747131
    0x8010503030a1b05070b04060305150901062001290607030504140612040606030311070323010921020601060302040b090d0305040911031b3103020612040b0105030303 73
    0x1d60401641c0701098800c0f00180380c5007a00c400ca484495000b10310100a9100181110307940540d540d130801d28000c2c141c4900800b030042d4006a0340b101e140945a00e007000b0b0444015280401d414001e402824642d00d070034501d5120290300340760b15041342c4039114040d500c3c85044a542e5120481c264010302c0b410703000301d000c0a400300301c0034841008080501310480008820040001d4074141c0f0607445817481b00c80588007650901d5444c41c00340304142c0c00216a2000a601c81c004200c814615a181c410352a105020600000b488029200b6507600c00d40011941c5540103001140c515000d000001020b42c1e4001a003005104650000034086e009108407015038050200c2c071440d1034044803e01503521141203044080150403c00000c2e00803041c42003904611650440c41d43d43d090040d8032620b0300c0c00e40c1104117103840040001c02800c1c2c115801074511000f00ca404002c10550003040c0c09842840340c0e20180d0010300014200f103101480d12907079440340d441004a03200598030b17030f4140b694034082140c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 503749622 1250 503748372 503748379
    0x60f030a030c0b090a02060c03031b130b0904021603020a061112160c05010f0c030f020f1b0a060203070e01110a0c26010903090807080a0b06040203061f0504080d080105 74
    0x20b02d80011504000b9841e9000d20342008a4251001c0c550100c0d2155000300a00b8501da0404000e01c8500c04003c0034001060450094240c244004c2d000c1c82050ba440c01d100312a01d48000140c5502d05840326019a1054081c40c0134104101d4010b090103901c41c11a02805c5811500d400c800d22a0389115200303842051444001d48000c80e45c58142e1245c0b00e82054074540705010303110b550342d00098003d000c2d002003d2a04070010940c1e002880c030190603580c454160a100f180123010030205100081e0540e03c0160a0220140000d134000c80c0c454101844000b014000314000000c00c031801e500124000a402c0742a41c0c3d500302030302585100c0ba250101450011300c0000c91420802c0103e0300c54040015100804012400001c2c0507030b1480d085480c1044101d02090012104000291050000b04001c0410314041c143c4241e235903540124143c001044640f042d035000c0b012136440d868600f0510b104c00e0b03000b2030f06c242c42d5481d02009019500544a03c008510070503036103102e014401c06a8034125100075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 503750872 1250 503749622 503749637
    0x7030504110f03010b04151d400507050a05041506080703060f0807030b01080609061f0509070305010504050a09050309361b0309030703030c0302090d0506060f030a03 73
    0x1108201c2c580e11030401860741903480340b014601654941c070443c10010305031000010f0841c42d1400300c0c801c003134101026100a419a000700880410003000c11100c3c042c0c3c03844050600e16646001880c05003641044240c0102d0f40304002c0c00304040018044250f9404590709014182d688007040251900304060030080e40b8101c00c108a450300031000c2c2500300d0294100418116110300102060300401d0380180e2407980011810020300c03241403405805018032001500c500d1071b0000313001c2e683d417401503d20325600301105820740d40d06100d0034104000e0400288840b425003003501000300504070a001d940e200301c0c5482c000c511000b0103441101d40c65540480614284007141c410040c440f0120300c0c5d041040c20110007000b8240713285540d018202d80820000444505080d881d01d0000364074040c4a040303511080040c03080401c80003007580c0b0a26490f01d808a4008480b0404902078043d040c1c805070003441d00304410381040340101d051441424152089101c031502c2008141daa50b40440e00038002c507058 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 503752122 1250 503750872 503750903
    0xb0411011d030a0f0201051b03030a0b0609090f10090509060601110d02280209010e071211030a020a09080708030a0e0315061c0f0308060f0a05010f05090f06040801090b07030504 78
    0x800d80104441303030050410a0030320590082c4800050501e0009005640000041102c6104180f049190a0800741c90690a0042080200301c05090190850b0400054100012103c404440110000c0c02c5010814401e13401e103c4030181d40c07403100ba120030b80850307124003e03645265000140c03080401c03016802414000f41c61400d80e40c0500140c09899260074040c141c1c84b01580f030303404030903000b00541d00b10b81c080b51810035001000b241c010011000c450b4203080301c9880446027081a81d0304a01c40c8040141d0302c02d05a801900c400540b503000101c503004030000080d50a1000c070282c660380f885078540705c69000c007070420152190540c160740c82240313100d40702191241c10041d5159211402131154001001c02523100c554003c0c010200443c0021fa4440c02c00200b41041700390380d0404c00080d10042c806500348400a4605010301807004200f08010a8840c001d40c6c0d4036544a500280141a6541e01c03030721480040d010340358003c0309507120035142005c44e41d000d00c284a054400c07604410640c01c000351 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 503753372 1250 503752122 503752133
    0x60c1e0c05101d0a0c031a07140901020a1211120f030a0e03041d0109060b070314030621030a034223030705030d080103140a0b0411011d030a 62
    0x340110785031061821106454403c0f804004204007107010382c0c0144002440c619101c807507400c070034040c0d1041c5003248090040868000300c4000030f0f0403180340f0840d100c1004000403031804070314082c050a407040301000070809507003003800500b86540c8182a201e03078410300000c0e00080d1285a08500181400f000000e00c03070036490b4007040c81c104140c0b0030b90381f40c01d40e16a03030303403280c030300c1100520040051200c0100301d82e198501ca110018591300091034100415601d0103003070400b190300200700340a000400980c050380c809803655940c3c1d00e68401001200c101c0c407042d03540d9800102280340840c2c6030401c0301c038604201c0f1179210040c200392000c0406158401c0409840d80c1c500703519550441494200100341c441214440d03c803540d40d0580310102c0301410000f010300e01003203507000300c0c000c0e00300344904060144c0c407401c0c003815641c000150ba1542c05400007054548141c6c07600190400ca03010040c4801c000344006080500e40d0b00343e03158401c440d41c02107c3c1281448a0400b261b042e440180342c40000754 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 503754622 1250 503753372 503753381
    0x11040305060f280f0b01090506030a110c0709020d0b03011b030c02010204050d030f090504020412110f03060408040306050f1e0720070608151507050a060c1e0c0510 72
    0x1101c05103965002c00c0815643c1c154100d45644606142c60720300e8844640348a12541190000910b403291400b0701c0d04000c5000c0f440080e200701d054a0f180d6a609050705012411145181ca14104542a00d0b5aa03001a4020f4008051b100c42c40c7e0b0400112500707030b11381401b503c008102842c0d00040c14122800080e0000c0185850300e0b01595020322000135540e50b40c02200d400c9070b0180e00c40c04070307901c040c140091625660f9080319100320720500c814014000109011450355902c1611f0301d05c0d48440e1000075501c00c032030040307090341031160108100400036503001600449124000500c2151607503c01c40030625002c0700c0041040411201014817100310341e0850360070000d40e003450b640c100c5442c001b400c0510f01e042107040c0caa030b0040071f04000310b5a00142a40d4402c828400c518002001840000c410300c14803020350055050220f000d03020320805001802900303600c204100109030703190b0f802404524440d000214400e03203185694121500941c00020b45a0f84280900900a600580c00d070060 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 503755872 1250 503754622 503754631
    0xc0304061b053a0504090e010204051315060e090606030402180103210302040b0f13091a0a090207020109210c0f0503010c0504180903050903030304030801050411040305060f 76
    0x4038407101c0c0703240415803d015080c10500715855060342c00341c06082d206061400042412040015060044000d6611030161010b4807400c071804a40c0281944866019018941100d90301003140207403102c508040750b0141600301160020400c001d0341d10802075070790f4107240c01ca031500051014000344c068a8450021903101d0f100030000340035281500a04000703100c00740c0040326411805411402020110b0103043c03510b44080c46c0075803616003052602e0300d95019060b500f007296800480c0d41c1c80c0003400c1059a0014104c5076200b004515a000c0450310322102840071355009192000c40421095003a000300e918050b01030f190b10700700601d030200000b0990800014481c00702d4501200c0c0c400110562413440007415907843d0854040e041c4005c260849a140d4a400c081c4001044200803001e69010351092030562484002881c8c1d01d6400d060b1043e11408895540c140800402c110402d60002c08543c140c40040d141001141200010f06503c4c0c4240d01020b000303940305800207000800002ea54943c817 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 503757122 1250 503755872 503755907
    0x15030c0418090b0708040b010915260613030f17130302120708040e220308060a0f060c1109131e050a050d020c03010501031509020a05060a0f080a020c030406 69
    0x10103015840b10441e01d00c042d03e1a038001a041701c20310060002e07003185180075040028042207208103020600c3c010707a0552090f10b48601c03028201c0c030141201c0400449081c107004080e070301c603480c0201c5032080a8a40040880200d840c07000220081489081c4d40c2741a82162041661583c81e00141110301c100301000440841c81091b09901c41d505811010302103640c458440ca64845040449900700c2c0c840c02170007071881e50030000c15041d18026030011201c0700c64141c28641e5243d1035600c042050b4200d075400c294040c3c01408000186550301032940c800c200c1c06002118210180e5030104010382e601511310640100907195450085071511908582880c03000d01d0f03994101000c0d0382c0f02d504050407420190f4150308180342c445c20403501804405080324084000b0012981569603d0368422512141158055980c541400442d150300030000c001e040d00502e1680c0310788a8010050032592400c280320002800c104c0032a50342d125034001d440d11261444091410319080ca20102d81d5813608201c402c16 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 503758372 1250 503757122 503757131
    0x50c0c030313050406051203191b0c061101060b19170a06170a2001052701020c0a1505070201200a030e01020d0c0308130503041415030c0418 62
    0x929903007040101800c59501d6803140c0e81d0703454402000120b44081e400301c1e000d8403164203041041540441114031001d40000788150122603c001101d00f404200c0f100540a500d0140300b00170f0001b00c0414004840017565070b0b25444c0a80400c80b800e0b134031244100311403100f0520170600000306c004095440000f442c94140b00f64140400c0350390034200182e5400019550700d013001d200e2840751003480004040ea076002441c0c4108565215404210300000f031200c0d01c2c0c144d20010001740e1080701110082c5801c4280200d14890107e555040241e0580086000d0300c2052843d6000341014201c0c40c08407440c11100c44030000c10460244c8042c1c2c0040c100301e0400085a090040b8443c0305034094810000d140c00820408901c1d10f000b905026511200d035056600510f840030078640d00076440c450040e4189008107184d207e07041c2180320100d0002e0000d0560001080100324080030a4502c009160b0440d840500603088040c2107402d031000340c480f1a0404402c10080c0f180c585290030329049000a0b090008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 503759622 1250 503758372 503758393
    0x402091504090f0201020c220b06120f0601090807121203110406030911090c03180c040603111309030503070c02010c0f260a0e091305070305030301030317100501050c 73
    0x404903610b8a004503a11a2060b18260541d681080004019081501c08500c0a0340e1404800111854011440e400c5911602c4040280d240c5000790350710b1505030600040c040c104540b001c0c400c0141240e1131400510f598400042c141000201d820490b51541d04030b6109035050f844d043d0b2403100710f640301418103403503000e4180390072044001131000b00714964001401c000c041ca03101919a4201d201d5078421a040400d200c4038600c62412030385c100385042d00c5c44100c1c8282030001410040f07002800381d8020301d80307603000003442401080108464001c1f00d8000b001d0881048010445400480c0900001c00900c00107800c18041d0100010b01c5005051940302440c0c0b0ba659000780c4e070030000c030445000c1076400180158040708040125004c400451513410840744a0009000321495840d080c4070785e110001140d01e031184280c45100f059003100550760182d0300c1e03060140e07503984207202c11400100c446040005c41c0003050340c0c031801001c05c4200d440042c1e02c0d10004455a03048100c010985005a5070b028 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 503760872 1250 503759622 503759629
    0x51e36120c0f060603240406091709040e010e07050108040311010f0f052a0702010509040606020f060a02040e1308211b030c0d09080403060c020c1c02010804020915 72
    0x41c012031540d000140a40b56001e10500e003080d8020302030a010398080443c9a1030310081d0021410410f42242501c040d55a039800d03c3c1c00079000100014180c2028000100d401c0f030300201c0140308604d000c4c0e0f4280101021208564221106105001d8554100000c03d002540c40758000940040c064a8142d8500c031445081c103003114250204c0e4500141d03034894100745241540649940309c05030142e4049084110260b1086480741d800031440c82c1c2100103440402c40e03000390151102100d000d4020006142c50f4803020355580c804041c40c103180d12501c800030b40e49072654000c03503040cad030404d011180107601c500b003c09030001d03200c03101168180e00c1404014403120140c4104d00b8048800c01c402d0425043c000340f21055403229030700300c400100003041082600c00354a411035840075085400001c0c66031003410502418018ac4c0c0000701458102141d40842c1a1700142d4800c0b58a0111030030100102541101018601d4861009000c50100c50004c4c015161000500b64488441280500ba862501000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 503762122 1250 503760872 503760877
    0x402091f0503061810300804050a05150a0e040e010f0507110f07180e0706020102030a05160f0f030e0a030221090303030a0e0709051e3612 61
    0x2000041c002008015070303440c0c00f000d107800c0c00700503034134402180c2800c50b0b00040c0404c0d14090390501442c00f0442d00e510794400c29540c2d00c100c0308010a1070940e41c16142002c4c0f254880d200345813003a03450101c042150710f002407101d400c9800c0f140e10302e0715060010b0404d035032a120b02e00509a00c070b0360780c48904c0d1800a0038004c2c00203109002030001040c1c68028005001d0341d1012407446403541c050402c2c2c4c5181d000002c1c4400a450802c2100300e5501103041c0b508010741000d00c404207443c0120a0001090758054029500a00b404141840599a11a41000c5404441c3c04175000241045401c1618a014100c0c1d1000c140c8a031602007030103400400c00924013803580f20b04400691207030a50781403103d40c020000d2410804c0307002c180d103025181c1001903601c1c00040e101442d40303079a6031607009290104110100c01003030190805d100030700d00160701c0c1e028210381c080902d1101003194001085504a1058007082c1c4511b400071400d030300f80310110108501d442030b004680c01d100c0c0c01c1107840301d50800c0b1b01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 503763372 1250 503762122 503762179
    0x80d0e0307060c0503060609010c08070c0b1305010509010e0121051509100f03290c0304020f0901030302060a18021807020706091229150a081506040209 67
    0xa603640e00d220b140560032952500e407641d00b000703020b00078000c00c0d41d540800c4428081c0c007403034039200348115401d22408901c180600140ba50600c4d10303002075184541c0014040d40281c4401d030110b074076070f10390054074a407041d40b4825001480c448400c1c0981d600a44884203003505190201e054046141d4105040b41c400303030b41c4030002806005801d081841c0050a0652001004c5074520314140f4106410700c54085034000107201c000f44a00d801c407040480540c1c035000541e1045150414140103e0651a42e8001c0e80c00b030313018807141100207029003410b401c92412294107900810b52540e5207503824008115030803080360b07240100501140941e50b200715042e07007a400c0403007401341c50401c1d00c8043d02c3d0840a034041410301031406010452a18060426080d054001500c040f0386c0c07901d440a030b6030f441081c0304100041c4400c1d8041c03118143c0c070350081100e00c0300140d64007201d240c1c0705e50031a40c0d2243d840f06918101c0c4000f0000541900709600039284041c005091080444009034a0680300050b948 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 503764622 1250 503763372 503763401
    0x10216050705031006150e032803090501020a150e1f050a0b030f0703030e01120e07080f03130306090602131e0e070519090b040b030a05060103020a021504080d 70
    0x241c00d02080c6810b000100c164482c00204112036480e000f10b84104055100200f0240701c001da100e49071985040c89401208803d61100604100030201244000c40a102090f03000841b000c10108007940001002095070790800c21018408440b610098040d00c41c04c8400c2c0f1680c01018115109001880420101d02912150200c1c080c03814201c100304072149408490321a62045075203603244080801c584040d6038251600c0e6112840040c0140c1d5140d0348544207032035003460300c01c4408081c000494100242e84c007039000c0e0f880221258076099924020341104140a800302c050400006d403c55200301c140b83d01c5500c000d400c1015035078400d59404925880030107414048568805814a10f4008501400d1803d03071100c3e4034141244001c00034042e9030300c448a5803284030600042d113070042c0001c2c0001c04510f001e4650300c0b51602d40d10765083d0000d40380004014200008180d0940c064003d403501c04507035134002c002d00c0c00b13070070010311300706a0281042c0c907810810807030041d10300124001c02e6000640394 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 503765872 1250 503764622 503764633
    0x20f0c010e03040302010504091a1f12021801050313081303210e09041a0a0218040b0f0105070606050306070512070f09050d03021207050c01141303120201021605 71
    0x29525400d41e880c50441c1019a0010442440146e8000c01031b14250380f15030b000010510300140717054050540e80c0c0c03081a40031496100017001c0300011a4801c0c071415050352504203030b100840404044e0f014188a10356004140c030203488495111710f02440e031002c1c0c00901e412441c4600e0300c0782074059101d105c402e194071405907400d00c01d001c41c0f205c00310054a82140e60800030311070500000c15025004213214401d03d03613000450140070241c0d0840d06c540002c1d907111491401c01e010700b0350095018034407045080952181d8a001c1e40351034031402035081006880c1745030b62129200110f982d584460011288640c0d2a0002300340344c3c808101540c4925001d840b4039640c0d14a5031404114030f0801405201040994a0f20b414915800190501120001c4c1c880003501b140610b416030404848040790700040c0f402003050410302500040420311440203884404452010103049801445144010b240c01c1c0309112081000600010011600c203405100050808408500c401d064080902c3c007540c46a110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 503767122 1250 503765872 503765887
    0x90e010b0a0608041e0b0c0c1e1014010e0708090a0b090d030f1803051b0604061410150f0e030f0a2d080a050f041e0b030f04110f0301020f 61
    0x14002d900f81005c01d00f0010038040341d40e002804880104003906103003001c20f110302e00302d00812000c820710300107850303c40c000019800b0180d82d8284005040b1445410a03912030b0041c80c3c2c80c10000e0503290405072180d400d0350b030ba00086d511020090108001c901c2410000800f11360f60240d0180120f814070080c1c07200c442a1240101940e00812203412034902d00030000d58100581c04140030062f0b814144aa11018034401840400002e440340e103595002d51402c010421031076522a403610542d03a00c034007a02d030f00c8210641d5444a028000c0c0c540345000c500c0300320003550040003d050685503a280800c0781c00103905c080b81c200b0b0040c540200165000034500700030441e00c94200a000d105402c2c0003568003c880108158120743d621014240d01e0300010510a198801c5088072440407180e100140d8640c7d5502c05007150101c2d43e901070140580003900070078030502a5084902401424002c0022612030383c4170420100543d00c09261320802c0110b071030724940c4080c006041042044c800e43e03501c0b0060f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 503768372 1250 503767122 503767133
    0x204050f090d0f05040f0909140105060907110102090d03020105040218070c061a040615030c02030f120907051302120112031e1b0b04021c0b01090e010b0a060804 71
    0xa01030412991804000c0402007011400201030203040803a02c0e0030340700740180c403a00351414451900700d11b036507440804003c201906160020705645100ba11f072005080c2c1e07580d142d2400c071f410684000340c0c007898140110340000d01c0380d2400d1382c89200102c001031902d00d9080008002134041c0100324050b0351034404100961400c4100c144c41060081080190341c504440f00400008034000010503203a40c4401c000c1c465261070b100d42201c2c42001e070040103015161855804902800e41c84400040c0c2000e502c00c480910210940701e900780c69070640c0742094aa08461000c0e0302c0000c4c640185481064000a5941d60320380700e42843c4a000e801c010380d80c00c100c54005030030703080507000a170100c03449804100c006980711420300d48101141c0065004c2e4503950382c048503948a2509140c0c03a9608a284103814412407152050003684211504049007403809100501c1c4050343e10080d040404050041041c3d41260b01303d500c0b0807481d04000145600303c00001b030303070036031858015900041085007000304119 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 503769622 1250 503768372 503768381
    0x30a030f08160e130e0a1406070504050102030d09060e1605030f010b03061f030506040506160e0d110310020c03211003060b0a0302060c150709060e1011030706090204 73
    0x10110484595007600350b400740c02280780d5850345000711055207004407029116480300002c0d04211099510000c40f508000d1422003c03c840344196010701c0740450005401403084608480c41038010b1401c1004598a141c010145050140c4d0130545950801c00c1000090007140000d616116080441c1410401450b1900d490a1120602c036031400024104a03900052030700c3d8000c4005004078100c101594100c900f211482c0d000505030f114400c01d210401c800415428030406645148600c3c010129004032008070000078001e401c03c0402d401c2e0004290102212102491301408032150000402889000c0344e215a49039007994002156480e0744035440d09a81580113905070b41c5890504181007061100071003440001c1034255103c10f040780d0740d00e900072800000e540003003c0356194078489500079140c296071301074000b1007407481c8005041c981c050103803001541c64607902c43c410800d14500b03010a107040140244140300d20400d1183e1050010801410f82a12a88000c07980c0d1520348180320994 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 503770872 1250 503769622 503769631
    0xb09100f0213090906201c1404020415050a0306020c010c141c0920030115081222030305071101080c0927010f051311120702010b030a030f08 62
    0x28010014410848401e004800a4503590040001e5104e0f1900e0608003d000741085442202c5640040915031002c0703101802c000c0c0c150b81a070755106054a5030402c00c40d00d010006d400811580008240507042503840071a00ba4028500d0048454031040041e0115007158022212240c001442c05081d072401e0040b01500c203902e080ca486c242c0d1071f00c00d00b0310080c000c400760b070300c6280c503151107000e08180c0e190032054100703030440c0c04114141051540c1c11b501d507646468050103503080524000b42803006080100881e502e150107442c0500e40700005018036441090203400310115010202c0c40c041c80080c01c0401144607484859584a0340c0c600090119040d0443d2410b01c42244100b04d41d101080007215006481214081d200110040c480846018207411503c400d050304000410160a403419200030343d2000c541141a4011130484441501d400031030f1a000c0302030074426000b50b102c0c1980c42a0b000383d0a0300010030100d0603c00400d1924040d0201500081e07000c041400080d60032030000ca402 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 503772122 1250 503770872 503770901
    0x20a181406091b0d020d061403060c0f07020a0e070309140118060203091f1a040b1c020604030b0403170a0b151c06030c061808070308070f0b0910 64
    0x41d10740389000840758032008003541034962415403081c0e140c008000c1202d1042140b208110f490300140d400002c0180203c1c0a40303071000b030000c20450b0301442c001800d584a41031290060345041e9070107402181c107412141080344c0107070722a100130409594400a40344607469170fa07000160142e00341401c0c040100d0140d08014240d1511055000084590202d0f16100e03802000c0580e0341e403641000359250420181c10306285600559a0300b000604075009020003154442c0a50346640d40d000800084401d88070b03e4941c4203140041103d0440300185400b8100790006110f2420030382e0301d03102c3d803805880881c0c04500041011400862100c41c40103680e4000c06081020440818940040780c0030b03002e02c19400003c80d401040321803c0b1300b011038044c2031540d44103d003800341c140e07284ac21000c001c10301c0c0203010214440004142071005880490011900900010002a442e60305d40c0f1101e40c8c0100003d507900b0f1036004a49010514014000340103499440c010700302c214520310781c00100c1d095403000c01d04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 503773372 1250 503772122 503772161
    0x1a040e011a09040305032802130614090915041b0e100906020a06050c04090c020303040c050603101a0d020c0c0a08061603050c040503011b08010e100311010903020a18 73
    0x442d901609913940068040310487d00781c16036039182040c1940400042d000e043c00000c1180c42e900b8202c02101c1100c205803610310540c0c045a8010095000311049540c01c01440000903e101d8610303541c1161110016000042c26140130f450030741c1e020081499a404a0a840c013650211304200711071942844652038442101420841700075180c81110401a165a480c1c1c0701142101c0b211204580007440e1064040141090b03401c0c01a44135002100e041d5030070810030000143da820290212445038141c0c10f82d5840301400c000150058640180504401c084140081c0040402e2031006020661615000b80700301c000080400c15100044d400c600d1140e00b0501c2408a400345c540c10700a00b08149040c0801c0a80d54000847e00034022580560b070b0540c01c10100d60001e11004a0203504052155603044031360fa00d0b000c141d40e84c003a0998180c815010006170403c080f4442080e980400c1c0c605241c1f41ba0200ea0b40e80001d08008070f42d40040007564440700c4615940d50b071a10882c0d1448031219034800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 503774622 1250 503773372 503773381
    0xc1e080c1c020c06250e0f062209060e060a0317070312020d0204050306071d10020309090a0204080d0207140d06090b0c09031902031e12040602062205101a040e011a09 73
    0x811181140300b040d030049001042100b0380d441080320001154a0511144590340d41e0303600c60300007422f258468980301a9400002c45da890070402089000d07280c0002e1140503c000b40603100c0b40700d0b440b0907001d80400c03044512078080c520700380c001010070044440f005a110781c1450205810890040d280e00240003c428071181c240081c07441e081c81511046403865244280d40d0301c02da0844c45407000f2a0b1703000c04140100300c0a4205c69005d002550300c003038101ca070740c502010300683e500d40c003038005c0703842200b80d000c411180b5150080d141c4c04100d207d0340d0b0101ea101030950b0340c80d0759508283c41a00a2013004241003505050400503c080c240b0742c880403281031801500800e4550642c0d1548c6100740d05509111603122104001c05084040c0c1c0d8822140d03519a01c050007910f9003010f44081024840a5046001c0301459107001d0324400c2e00301c400740c05041e40d00f10b0079400130800020301024a002080e524041030391240b28883c0c03900400d000100e404034a0070038001c10210300003e1380b8071640f0503400740b2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 503775872 1250 503774622 503774629
    0x7030209060306060a210212160b270621041104110f030903130303020c09070f121a060a02071805040b0a0902030a02040c1e080c1c020c06250e 63
    0x5c04039103030345191801040e4002580f02c80c268601e900a50000b0b4501d0005544e200005039035960404040c3e0714411003510b86800c13003d18403034211215900035000700d085000240200200e18130713444c0101590700d800c0e0701c49103081c4802818500c914540e1150340800060144042c04001d044808032010001f0410045807980907004d02c1c1c4100110040210014050340020400c654040780410308480c1c0b00c2d6038901c0c1c000d5548800301c82c1e560003611a4004504e460703014060a2340070348625140e108000d00340041c000024185c1001f01a82000b04948a40040c1c44500c0204955803442d400f030b281c1d003824104841e5404002e40c6c0e16621580ca08000c2001280d222203499230054003840b404a0301e40e21900000746852035404d000795101c1e10b004040001c0302d80200d00800602d540b61000d102070140910240c0b1701c00012100601002d0040002820f041c210840c0380200e2060a0401824000040c080e213151000449462030040803100c4501c0d210318030350241c90240110f514003400d04201c2807010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 503776978 1106 503775872 503775889
    0x70914090d0302161b09020f0c01151202100905041d06060406060e0f01030f15060210050c0d09140d0f030e010504050307032303090703020906030606 66
    0xe1601c481c1c080d0003074915100c111000403160152030707202c00381000d1800600075a01d181003500070400b031266201405120072403413155501c4003e4440e901d4216401c0c04510004440c90440802420b0301821164404660640f000114040c1100c000c0e20141205d4008503481400c0043c0c1048250900106841d4203818804075034a5464007024007040302d0950040100150190115400604100700301c0020250185400103424100b140380700110341e5074a500e801043c1100070100020b03070341000124115140c0403020802400d1042186c801ea11441125a541c2511807800e60123204954022248a15024082d5a450321045038000d10b500301c0d40500700c0101e45404d1880061183c1403060a22175039109005500d00013054600707848450303080f101d081d1404041c034080b6600d407586401035802011904020701842c0e00714810010400402011300f40039038885000c210441e50342415 = true := by decide +kernel

theorem cover : BRFrame.Cov 503597122 503776978 := by
  have h0 := BRFrame.cov_init 503597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 503597122 ≤ n) (h2 : n < 503776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
