-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2573
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:06:39.964988+00:00
-- url     : https://prove2.me/submissions/f6716f38-313c-4b50-8475-e803d98b2c5a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 462589928 ≤ n < 462769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 462591178 1250 462589928 462589937
    0x100608010c0203132c040b010627060e150706060609050114030c0a0e09040308070e0d0309051903080d09030e060403080d0e21041d0105010801031e080406 68
    0x200114882400746020940560019528202510041c85107025843c0941c0d040007044030008041001c110807090118203180c0d800d034445040c5813800c0b640d64003080c49140b00044001c1c201002180e8101c03a8081c03483c400e4105069020f15121040e2110f5500c1121590f1100b04ca0b100c0d03e10807080140105001340c0f0400700003400c581030105c0500424800c0e000281046450001c0010204010b4200c90700506078101b4103465101c42241118100403c1c485141c0218180051000b0590040035042c014000c1d0740303d21005441ca1b00a102c334102d80c00c0805400141d0b91b60701040700b800c20340001648144000c8110070150b031079841d07440659101c1800951002c0e40c0e49031050030f041e4407540040003014116841890203103181c507804042d00a45904401150341e6504184d500784042082c000000c2031102d03d0b000041d55055581c0241d0428814a406445620310b00d804000c02c030000a4107850058584d03000316401d645070950300e00c0e04072003c0b04982008001810204955001502c002d0605556 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 462592428 1250 462591178 462591191
    0x81005010306200703031509021c1a03030702040504020607050a1a07090308040e07180801060509090105070c080a090e0f0601031802100315050a1d1501090512010e10 73
    0x3090700440303d0314040302c0720340280038401c01c004851420842d042c0c15050701e404188030b034007520401c5500c8003a610601325640300103442002c2d640b14062080c180e00511104120849100401c07000500010000c203506420030800e06006280550001d50000d00203010241004071613900d20f03160000c03200040d18450348030b04800604441c0200929400130641c5402e00c401465592408907d000398000c8901c05103286002030002c51040801c0a040041012070f8202c1560301c0c20483e00070b11041c040c150142d5041c2d0300060710070750140a058012803550355801c80f402c800d0389034804a50048503121042041406000840d19020340342c0320702888035400d10018a0512a0001d4110354099100c0d0358900c031075a070950003603644c200c0c511070208907a08022071255200a40d0346206041500282e0340034031001d1020a02220661411b20080300f40070460000703468103c03519a40c001203080c0280000c1c0100002c1c0081d003800f07c11048650404c40000c1030200c0b0b245222410568003540e8110199501c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 462593678 1250 462592428 462592433
    0x1d04150e09061f03020d030e0d05070f050f0a050f010c020d060504050607090e0417090301110c03030a15030c050411070204180203100605010206010b16080f07111203070b040302070810050103 84
    0xb40503100b0852455426800107107145e000c00d01202102e080507050045040350135099454030041a201a64460700f62210789480c0c11200840c507210b40142c3d4055150301c40c600005003010b40103a410350340006c007030303080e4211000011146200c0900c0300b243c01042a03e103240002d50207002e414040c0c0d2052015040318903080e04010030380806a80055a1007030035900b480041603d440081480521030b80840d82d07140e1015010034050328000031613510424000400c1800c80c2404009107000c0d2011650034408a00120401d003081d51301070001400c5c0c0d43c142e480c100302034540b0798003a042010903002001c0c100001500000d04031003240101c0c05910509170100710842c5424001d1403450348242c03400300406406c0130300003540d4183c140900850031030000303224080b202d00302c851640c3e115440b0456581e9001d55045180b00c9801021084440384403a03d14043c5a21740110300d40d4008140704000c508244080e1980030318200081c0c03041d000c0d40540c200208412000740044c52140e4840d500104140d491813 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 462594928 1250 462593678 462593701
    0x8070c0602060a0c0509010e030c0a08150c0c0d0c0f02040603110312030106210908130618030807110a0f090c11060c270405040609121d04150e0906 65
    0x821143d002c0340b4144000c0412900481078aa036804286000301407603807602c2c046840d15001440315235101180300c60000304c80c42c000a2220325090160300c00c1607940c0303a9402034007443c000e510600c8150b820030750491140740c0c46000c5802d01c0500950011104400603004201200e4180d041aa090b41d1088114040d90800700b02291810412440852642d890100c00508a1035240411015444444140304100e410340c3c2100400c2d07a00000c0395583c4205485000f01150064440c0b2404981110340d0004084000844001140e42201385140b60014072b03510905c000585020066001c0038110000c10030000621140d4050300340d00301b0000d0720150b07016014003103895040ea104800c0d8405420040c0c1400000d0a844040d40c1000c1d80da0440600c00468600400800c1d940a400501c3d1030304100502000c0c0e0041409030307004503403d07030141d0101602150501072032030301000f08540c1c110804040e42065070000d49540007404d42131804a8944054031a1440183c0e50441c26034000ca05208208084 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 462596178 1250 462594928 462594931
    0x170a1b030b0f091c11011401031203020c03091201200406030b040204050d02040b06070b040c170613031404090203010b07022b150608030703120e0d020a081608070c060206 75
    0x2d2054454a4600c1c0050f540b42e0800501e80e159210415103124100c3c01010001c0128010300d000f44a42c0e0340ca603502c1e05005000f44405d0380c00400f4080e58501c03045c0240708680d8540c1014010b907107004403e4041c091000304882c2c603009290b584079181107070800c125405200c10074004003840e981d50703d003070002002c2c1caa401c01c0691040e84100020003680d070301e42141c00441c80d41a500482d02c0303140b48001519034003035403a0291140c6119000c00080000038220b100a54420961f82ca1301340400088a5a5400d42103403004c5810517200b1900d404240a13198041c0e5111354030b040145003640321000b48d0140c0c0c10a83c0b0080808001040303400071403a0451807011760108020703184150131184080d0008118101402911b18103e8001480480c0e269400002c090105d14007165540c040c1307858001c1c404075085844562061400103004072070880401c0380174400c0740720b41c0180803400c001c0c0c540b00c07141c0d480400c107440304618a401010001d501c003405461042d00601400900341c0c503115000c0c1c1043d00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 462597428 1250 462596178 462596191
    0x90c030b0a05070e0307180b04020f07060615111e030c010e010b030c010f0c030503090705060c150708010b04061116080a1a070503012106020f0c0c06040b04170a1b030b 74
    0x4451014001001c00807030440352100540300121300608c501e00420300a1003244800f940490340020401c1c00d200080c0c20070000c6402d80b04031003402010b0104111420b05c1400071121081d0416014054030b01035070170104014030251320a41c1c3c9001e140c52581c908440030912814466515000c8022061405020fa400810070a08001c5000c0f03268250003440544503070340003014840b01201142111004211502c00340001820b0f00d80d96200448070155201070101c66010201a03600000c0c02942c0b18442301e504076200000c0c90340c1064141803050340d9010501070403031468480d441d0703820010f800400d448402414018044c00b80b541d190306000c1206034400424000d00e1a00b01c0601c09135a60003011241141e1703596480b00c05151000d80706c04144901c502014080a0010403030107041310444004026031030030141202e07018420300060050b40c3c000c0707100c0d00c040d8a0b41440200440502600815031241c00c1d6000e40b00a000960f982d04440c0d401c07904400c00307030100807406108000034042c03000e42121 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 462598678 1250 462597428 462597433
    0xf1903111005090907021903030f051f06030908130e040302120306010207050f04021603090512010603151d0d0804030e01051602060f1e03040204141009090c030b0a05070e03 76
    0x215001c0240452240c060218090644080021201031081c0040b0035244184c0400103d40011401d009001e070441c0b0769100c0c502407403c804034240c40b0b40c42460780c0c0306004540300b4030110783c50a1026401050302d544140d80c0f060080000d81340154600b0392000103006100c01081c16400c2c01d0038000d00d40b034280070791190304a0003001400000d07138000a00c84225081110305001003c41c400101e8060b0080d908aa120300d00c10001c081d08054001f441c4206032102580e4a4000040341c01103142a500684005807005007901d1200f03a484141da00103890400c0340e1a98071036060601000d8502d020314a1420000007003064013840200b41d40850b820346c0d1741c0000d203010360600150f188242403014014000900c201c02c00581c034a00f04a041c0c0990300320318022180d080c9140311485022003682e04c1124120b21075486c101078403441001c2c18800f24065a8000382c840c00460800c03a00d2401020041415140841841000800130754001c00040c03207240c00400100300fa081a16024042e407002c213101c41d1094 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 462599928 1250 462598678 462598699
    0xd0504030b0f04140d0e03120403030e0904060b0303040905101a03071107090204090228080112060204090f020a080603060c0703051606091208070e090703020304020f190311 76
    0x79034030340103030b034115400158140b601d0711035280c00f4042c800100d101d00c034140a03000f160513103203410200034446000d056050300c02d054094a0740c40013622450100a0100340300301130b0410b0030f0500c2c445541c0d00a125950004030384020342c0c000703460758020f94480d000080d100ea0411004017100c0700464010411147c400240c040f00c040a003009010040038001080302d030072040500f4200c10001f20006040141003195196240c0d071000020f503015401303e00e42e80391001100d00c10030300c2e01c2648001d01c2c084c80e655010303980d00307203c2c0c1e404611241d8030098a41c95000d101c04554451281309071144000780c5940140d4444058501811040c402061944a41c01c500100308040103076104a070f01e4a0f6051400540d100d50041c0b0260b24082035a402500c030303625004041d02000300c0441551740ca282261503c1f070b1143d842d5402256010b099020320303900901c10754040380da80c0d802500a180c026200034820309401980d8004101004001c05092482050902e420014000d425405584000060394900c518 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 462601178 1250 462599928 462599933
    0x619020708070305090d0204110403020a1e151103030f04020306060102010c0f050c01060803070303090b0c091012140c131d0103030e0312121909020102060402040b040905010905060103050d050403 86
    0x1d030b0260380d4000c0c044c4080001c5084c40382c1e07a030401074000309500074020402201039010410141c0c0040c001240961034214002c01c0d8000d0b405030300030500c0b0034000d80901143c2061015a00c03140950020028080a09580311401030240050b41c07095102c114a41e040e031509004240c0f405c5c101400a40c19a4503000001f6042680702c112010480c5031400c101c4d540e000c03000300d090300500c4130354030007000c9000c0400c12004040d89038000440041c01180c02c411103403a02c901d5100c20f1b11a84064941c04002c1ca001455914041c01c0c24001520080400145070120b00c6c1d42400c403020300703c0c4c554a010b41d0004501403004020003400020380860800500c4d449500010780c0c15489040c000503040c09012080252503540c1000f02416110a0701106500c600c01d046c41c01004a07000c0c3c2d50381591001c603014030594100d69105958669030168000c20441c3c5898003404001c012a418258000b030711110100c01007402401030710003043c420702c01400c2a602d107040c040c0c14642c1c28402039080002c200020000b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 462602428 1250 462601178 462601193
    0x1203040e1303030b0f0112020c03090604080d1106090705010c08040b03040c0302010305161b05011b0203030709060e1807030e0304030c08120f0a0e040225051c0530010806190207 78
    0x187c541013035401a07880e480005541e28500407640481d92160740010080b8a030040401d520741e10304026210141903103922030610303440352401c60303203c00150300c0200c0c01c111561060342500941c90003000090b25007a12000400c50681c0215015188041e20400400465901d031040f154420f001001c801c1442d200500010001e80c0c00480d1601240c90060082090080a5000d1015140b1401402900b00101d0780044c1d01c90304121840c6000c034003400c1c00010302c50300030354401c18080c00040c450141500803200310b048515015144008141c0e0310402515085020002400a14011181b0071411864410789501d05000c403400841e007440c1c02d00c80d141c8008001c0b810748410540c541420101e00780500c010800034080d120000070f103800f40100108a629448440c004010300500513201000c42d110700d08964040c601e807066000450401c280c4044c51240200000a030580c0003442d160f54240304c1034841c0c008400c1c0c0048420303400c00d00a2040f82d029000703c480c1d043c11544015401c0204540b2f4113503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 462603678 1250 462602428 462602447
    0x80606030a110f0a181a01050d2a020313092f0d050f040b390f0406030204081011090904030e120303061309050c1203040e1303030b0f01 60
    0x1888162540c0e02c40d80141c0e00d440419841000240440b180c0680e1082e4200305803d9002518854074034007a80e403824604143d141041e0100d06031905481e09a08948800040900085c14007407040c0c141c0c00080c4403880d014404030900d140d54021a12244080300051007a0640c0d4880e01c0340c94900184441d0b00c01241030b82141d1a43c078008001c01c5101116a41003440c4035044105001c0f500e04800c0041e1250b90a024074010f50217003141d1040d65580c0c14071904109001c42914490105910411404882854400502000c041c021600b040d10b0100c0703c0b54580c01c9608402e020a8011500f8040001c1c00c12440b2a00300103c402400603000e0710f04103d0052282101c03c6000c0c40400340080e09040c0541111882240c1c060032141c50718111000e400d840c4d07002503c2e1180b2510b10703005404e42c0340000b402001d54203500000508080200b05007040701c0d810048848189074001072000150b450110500c0d03074411707110b400c1c000d200e420702d610700103013182c0580c6081031045c5410b0f00c8045080c0d0380310900c078 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 462604928 1250 462603678 462603683
    0xe07180b3f01050a0c0807081b18090c0403050c0d0b0408030604090822170303010e0402030a05030a030e0c010c081902010f1e0609090b040f0f0204110c07080606030a 73
    0x14107030704034074644002001190001d40000390300b402c0034800885901d5110b4070080b2819a1512415129940700b251000001d6442ca01e01201184225500c40100d50007007500300d402144407100d41740340710082010b280089802c00500000840c081050004c1448601000b8030102c0e858188040c050751984190781d40a04043d040c0d12003c0000b0b00c05031281c0d1320244925402180749910fa0031a024030004c2071481113500d80f09100303480c0c00011456040c8035040c26040c00a005141142c0c04c1c0040045c00100091040c0d030f141c41151019404100103100503e054a101d940110340c0304e00a0004500c0c1c503141c0c02c5018104021501c2c80310100303840780182c13006404202041c07a40e0620316a0103e02600f406446d030704003249000302c00b6000c941c003084440a492030214060109a80d1080ca003000c0f98500b4502a204580704400130300011200750709a140940f0429141e10b8030b001a07000300307088518110030025204400070703072480a0b4004001c0d140080c54204002d1000c2d24140021945940c04840300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 462606178 1250 462604928 462604999
    0x60306060d08160b04080a0201060510200c120715050a0806120a0c0f06110a11150c060a050f161d031e0a03110a03050714010e07180b 59
    0x1000f0140340011410541c107801c0200d84e03104d81494200300d86c00b540030000000256103890380000b11420040e40100c81c0d0205034684903014100b000400e810704201c1c0e201042580160100d032072407940c2c4c0454601d802d2104400625100b030400c0c000c48070b00012a41407109000c018001c1114003a031140381030703600410540d04095024400e0019030300d0940414801003a040d040c2801252020612203d50300701c2c0c0c1c02c1d540341a280b1004500064881c10061006012051034504801d400e040c100c401508a100c61450300345850b1840228a080031130990340104200e866500b40038840d120004c02e21380205a40e1807101c081540f04801800c0c07190101007081a04000c07082004a41d6070500c4003502c0c9a0304072a94001107220410a161200041c58045002c10950001e89d000e0240008208410303540c0340d214185440e5445c5c98001240945d8100400d1664a07031a00d201e45040c00d010070340042412014030940c4c4d889100480e01901e12660b0514080c100d1642030f00c90881001341100c03541c182d041c06 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 462607428 1250 462606178 462606187
    0x709020927131410241208091309050307060b090f0a0c0c02030a0c0501080108120a180305150402040b0d11150c070e040b0f06010c1202071802040e060306060d08 71
    0x10219105140e0a012402c40e02504800142070072143e0440b1000c0030f610040031501c500350f080c40ca064100c990003401c84400078001c404000480c484020081c4000060400082c1c0700720341d4a40003a19442b88040784ca0750404a0700601b00300080c051500c20141c00ca03405107140c07a286400b922604030042a540d4582d845002c0241c1081c09101c280a80315005000d0710b02903031060801b40700c15021031084500084200000189442c0c001c5030f01d101c60986070025034036103080c000301141c46602c00d11584d6001011000300100007101048100c2c0003511b9801158042d140900400048540c440206800745a04070700000004c3c00303e01e005140d00300f041310050000a00280182c4d45805064000061807040030400700b0000c1c454207075984180d1181c01d814071596a8445c0070285000305840c40d07404550340301d04035000101c150034010010845d92045403420396031001202d08480703060340ca2000300c1d540010280421400a01e1956100006074020300c107605044003c90302c0385903480009003440c1c50215 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 462608678 1250 462607428 462607433
    0x20f07020405220b090f0a150905030d050a0b010e0303130b1c1503061b0e0f0111030a05090a080706052205062106010c03020705011808070902092713 66
    0x7400c3e01000c00701c460500301d40e0b5a16040c0390007076003a201c000b9188a0040806000880001c610908651010140c00e850501d014000043c003002c000441e214003090007207003a103004510925100740c80c1003402040400701603001602c50341139a82d00c41c1c007a801c1000121500c480c00820001100d884510705541c401ea00c3c0d903211001c44080c144c460615007006441d1450310303038005400094031f005010401c00c8202c0510769441d212450407a020101e00300e0300351070905143c600c000324018030040c10194603400342d00140e903065600000114001c1540400d80b000241042d0340740c1405810000020411141042c00c090803e010b009001c22000034011908e005441c401b45d581002004d02811860f00d681150440d442e0188079220100e400d2103814000520a42c800c100186903190503401800502d8200390046549640002405040c1c2151b103030005609441002000e0041c044214010f85031100c81c0c0170040c841100c0d450a480c5100c0301c0c3d504090b050005000c00750400c02e50b50292205400d1403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 462609928 1250 462608678 462608701
    0x20607081b0d020a0503070813020d08031807151211030a0c140309010f0e010b010c02040203070c020a1403010c110d050a09120f05010b0307080c100e1012050a020f07020405 76
    0x5180e0b1503860b0300100c0c280c146250054051030255855031244903099903484003164401d40c26100195008800d80a0040424260002150080d100c00d01d10142c10504090070f0b0b1500354207521401d0441d05040301c10420070392016007880780046600050205808140300340380170340401b9000d620301c03d54601c40c050881d40a20040e41001181300c1c0f450361a4640303c2180c600078a0080503012190f41080c010628040d010701c24035041072016142c0300b0203825181c080c4802904014801c206000360300d600000942d6420340031400800c1e50065215042c485a010701d42900c80c030301c80b00c0090102004c00c20018040110340b17150342215502d8801d8842c14a070a044038513100f00e903c800540080d15180034148600e12150707005071401000207111907940c15003890340d00d1030316204040880d000030421074243d10746401c1d81c803000c45a41c505000181500000120407503002c040100204201030702c0d120072031000d4020154081d0483d402141080c00008851540c0e11900c4002440b413555000043c0c400e02c0e02 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 462611178 1250 462609928 462609937
    0x180b060423130506010914010c0b040c0b0403080c1902011e031509020304020f03030a02030406050705150c03090609010b0d0f03270f0e06010c02060d0207060c0915020607081b 77
    0x412004a42e0910300d0320358010b080c103440b914000f07402c440004c00d00701003d550503c2d2005040e9a204107602d2240c0f10304444410207031085030521403410000620f1003090001e00040c6001300505603480428605030b41c078000c0b0f140d0a01001180d40906000943e03005241100c0200781030100e15070030300c2e10340c40444c0200f090840c0000c1c0700058482c045041c0c00582d01942c40b0740c0c400c1d690607044040200c10980d9038020400d6120041c0d004000c2841081e01c1003020300104c2e8821002c60700d8110840d2400c0c4007820003140c0f5000208070100c05c00c20165420003209820005e0b040c02007044900800c0800c000410425024000c5004800e2103400c0600c6071104011040d80e108840e03407681c04921110042c1c0d40c41d403003008500341c0d05540c04500341030a04086405024142c41c0d0200e100b41f02d5080c04065081020010452076080c48100082100b40c060100e51200c950f403039121584c02e014110821079880d0781c1d000d00710760084040055040d0850505500b05050040f0041c90100103e11312650703202c1d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 462612428 1250 462611178 462611249
    0x4080f090612090f06010e0a0209010309080a02010c080c0403030c11130c110f01060b0306150409020d0b12030901080402090a1503060606020618030703050a090b1201180b0604 77
    0xc0001c1d03103204000c04449400e0255060740c040d04c0004403030700d0b03c1c00d94132002802120300d511401008144020300f10f03802032005030018140800c8010306074450f041c0703a4000710280e0016035118500d924020303038030201c401d5001180044841c209400c3d62001070a2544100300180b118503034007810340c510b82d5901d0756140c00c98440c1200b880720700c1d038580c0c1c010804044204805198814210300790300a0303e06004440c2070b2400c030007645003196a00e0040103079405842c4940001104101f0000c21031490740e000400504003240c4020410304007a0051100c903070340e8014a41d010703400500004407a80e0380146144c0e00180c044030352a0f840d44410143c4001003680c0120200c189000040000c200f00542d0480704c00c49a098080c0d458517991085d81e900344040b10f90800c0b8054204025800c0000c1c000c40140203160458a4610f2006440d5851074403030307070b00c00081d107241406035900400c40039145040008000e1138140c400c0c40141c0701c01c0c0c00b00b1030078005c0e0b0069014032900c02812a1000c01a0b4450141340038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 462613678 1250 462612428 462612439
    0xf15090509070f0e01030b1e04060e09010506360a15060309021801061407210e030c01031505040b12060709030b09030a0f0509040e0d0908011d0604080f09 68
    0x2d00c580c1c041c28103911161080c012880a0302c402ca219070203480b580b4021080905001c0280d5500449407628059190035142e04c16625400840c0009110300c5980c07044075080000a11810140c0400a03000c808601c140c45103040d0b1a41042c0325013242c440000104081401445603880d0708000d88060440e400d9400d1071104024000120380b0b80c1604003e5a041c001d6070107001c00c2000c1d5030b80b186058401d00541c80403d21034030078640001c50401c001d04035140111031b840b251000340503030080b07119406a030900c0042c0840e5000c00c3c5602c0c0c2030244200c1c99000f4202040060383d1946076400c80701945c451710380f2841c1c1c1c0c5c0740c203900c81b0b4492020700503440011a003592014545000040c202a0301d80c0070a039000301e00d40000407001c0300700004881e00110141ca501310a5411802c088859601c4003107800e41244e03c80e070600913800c07020001001e502500361203100825041500c800d00f144c0303040c1e40c0740d0660a83c0c3d41c1740112072030000c9001c1c2d402540084e6040d9a03628402031000030741c45180100350301309 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 462614928 1250 462613678 462613681
    0x604090c09020304030309060c090f0e0c040302010c0323093a0213090f120e060d02180312190201020f12041e05030403020a09020c1506031e01050708100f15090509 72
    0x860384a000c010070b98903410211a00281c0740c0906060b453300c1118418a4401c003008188055030044490b441414407030318040c1000581d01c0c0c00e801da042400c0101421084020505211a2800d5640e01d2501082101442034440410100285a04014961503286038038900001c0564075403c941030700c0c580f03034800700340f21f48422403800d282903050000c03007518000c5c54107000c803640038071070103001d030030001c008041504101d40311000070002c0d0700ca04080c45284442c0c1c3c1c20341510f600d00740162221400da06400e561122900049480d0351a0b495143c130045920411205000d55081015122010b4411039012040e0355186016102c29203100b04010600c032300d81e480b403c20490000020000d591094507040d42e02d0399030f00c80d01e406078010158a005242c00c0b0781c2e10301d04040028902280e000c1d40082c1291511800c29544080380844014941560b07511401003008680e0003500c2d80340c00c0300303640c0000d041d0b007880d10b130340e2501000c2180501c4d011038507000481203c07544078080340005800001c3c44021603 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 462616178 1250 462614928 462614951
    0x3020613210c060c050d03050c0d0c0e040501080106030b0a0e0c0a1719200105040504090308181f051302100e09100f1a13060206010e0604090c0902030403030906 71
    0x30001e09500c1140c5101e080302010580e28410b107540034100381c1c000c1c010a107000c41c00600360042d01d0000c1801644071000d01c04420b646220b80200240b440c070030784800300034440d018203010035244140c0002c0300381da040150400014410382035031036000f00480c40002e69600e240c501c8504085244c2c12056214074881000310318112011920b2054a44100485440e901c9501c4a81148001050043d1198421000d442d07039120400d0324501007100145081e0f0303e03050300c07803000404035a03100350b0070b400140103070041110101c00104045c1003110060020510301c5d038000115038510003428010035420340c680012400043c0c00d04d98404402d58001e0075500e203203080d658014440c50110002e50310030b400c00400300310818000d8051205484082c425540000c2c1003050032b4110101000340c411f4202000c01c51540c02ca41c1c0b00140303501400c03890740a031006501d099400c96046002600c031620480c034195840c2e001a0401c9020f41c11983c80890140e22541c40e800d041e40140480003018025a052040c0f4011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 462617428 1250 462616178 462616229
    0xa0e01150e130207030c0804061107080303090c01120b09040609061503020f060901090b0310050907021203040b0402010e090f0907061e051608040902070201031a030703020613 77
    0x688880d2411603844403485401119041c41141d0807035080302c0c00c40c01a004403103840d0014810716010303040c141501d000c1c030340c1c0300300803540258003420001d40d29081958400c8030601811005141a600031421402d1450f11186c590100a80d80c90500003290407001c0c91810170707008a00c01e5040101001502d2400c2d0419201030071000f4400c03078402d0f00d08481030400410329184001031380d4000c2c2010b2000451002800003c1c1c0c060f14680b81402400f0900081040d020710086106019078000035101515010034451003030005440001550407032101450500c2a9800792a0f1182d004889110705451b10300068aa400c0750b200c0c0150000e000c1410420070401e6450040d000e43c85803812a82e0b0596281c408580307480030b81c0170040e0000ea0340100c80c100380340300750040c280040500940c5442030300e2596074404143e100e60b2040500e00d40101c0d48070250b40e09403242c440020048541e44003883c110100082d21007000d03020091045d00086850315980c000401c0d20b0b00030b40a0003444048a0000401b00700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 462618678 1250 462617428 462617431
    0x315040b0f060d0b010521010e0a1e030c11042405011b050327120f010c050c0c0d11030118120507080a0305090309090f0a060e1308090f0a0e 62
    0x904144403038002c40c0203820520507080e00190400343c051440d90811040103284922408101810150501d019503c0d110030712405500451041c01010f900034580b0340101c0390040507040180f8101d510074a680843c0d00103000c40700e42907200082c80790030040100014010300c4120380000d8894540040001520440d0034003001390b600c03d0325031020000000001d89600c0c4021400101075800a00006041c2c0300e081400481403000355003a4608078403940c0103c2c48000d000c402c0c603a11640612400c4070070100a218000c005441850303c0c5140c1256460101da81c0d405000010380600c09080005d0305000c06e500440000c003500500034849003078480407511189079141c8080e1085c407d0304041c03032161070040003290001541700825605190b00684260000c1030020160801800b0030000c40382d266941c0e144e0a071103940c00c014a0303222420000780c0242112515000000304280344014030070316080c454074903110780b644505040d940315610750101e080e01d10b000b42150b070404c3c0a01d00120318289800300d040d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 462619928 1250 462618678 462618691
    0x20301060e190b030f0312040c0b0f040e0708071b020103090818090903070c0323010606031a0a0305070909032309011704020109030312090b09010509120403110f0315040b 75
    0x50040d8040700e804c168860301c640d0301289031a0b0042203407188145900f0710855209000d50400d0b808660744640b11502c0741c0c013600d101641040005818000740407403408140d00451580f508290900d041840078019154000070b805020b014404002c04581c40780d0041121550300076129504d500c5560f040c4200200324210441c89a440300002980440000041d0740c0030701c0d00000910704540c81d540711a009428800c2107102002c1c1c194130508545075090013001e00030a40c83e54001010104181e000f50400652070344175120f101c2d00c990030000b08400140e08010f0384d805e0880090764901610703064070280003104c29040d0b80e080400888540c0c4603003070007030245601d00380c072455084618007640030341042046038000e0110f007a01c0814004640329039601102e82181c06000510300d0481c1d00e41250558085600000680d110300410514940a00c8032146c400001c0200605183c00c41e40c2e60318814030113460307950151901114000040d502001481d10f6223031115400c20080c1000d08004d0008801103840 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 462621178 1250 462619928 462619931
    0x10f06080318090f0402120a140c04050105010c0f06150f0e0a11070c06030b060904050a06060f14090d030c0c0306020403170307170709150c061b0906030207020301060e19 75
    0x2d6075080d080c414207082c4100c07020b801c480b0b03080d612075007000709048114041124503c64499003030f0014034171010210348440c065005050003008002000b003031300d80580185041152403100c00000569000300012810b5001501046100401c1c480301201801e40d400700300304290110b40002d01e01088140c080c01403400399824030205002242c82101480740410040ca106110031080101500c29444500d03082c4c00100300d00e142039041000602075501c290b43e01d400ca40c0d5a4802040740ca5040b00403a400341d804d5062016003242580c41c040001c0c0680103186005840182d10901018483c40b107455002d03600c1a1510840c0b6100d050440094000d80003c81e580e4905031350075180c00d1100d0342503d214801300c0c0d40d0026808003110380d0a070301401c094208404e00c120420041022034041e402140d11281e00d69413152100c0181c100007040d129402c07418544401d02e07203c010407003a070144640b0241d410909026030354a000b80302003401006640c3c07001d00c42d10400703010b001684403950008840c080802c1380 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 462622428 1250 462621178 462621217
    0x61c0f050c060a050d021c0f05061f0905010c1401090c092007030f120608030a170108070b0a09150804050f010b0a05041503080a020d090909051905010f060803 70
    0x10711142d07100708800e0401080080c0321404d614003140d0010554442602070680388044401c180b034058403400e10f5000b0355561107008200080c10084540c0c0216030600224550210b81c02ea4054204a12801400c0c1013001c02d000300d000b03003c058001d101015a140c002003205020a003010f604c0c890320b5000309007843e41080112986000d80da00c034030950320b10061285182c504656415950b500002c40e8801c24001c002200f015000b0640c441d0000034400348015540d20300282900030400703c03010000c880c03616101c0005001c15079000690704291002c0107442560745a94900540b0051641c0c0e0000b0080035521650340140303039010b52101e01035445101180c04040083c00500d00742c1d480142507507000000d8500811a5150942001d4a58a071480500c8601a01c0e0744500f180c80e8042c1d10b5500159000c41d59203000103a200c107155005190000c0e0402003041c0365601c540d192500341c030034035822494a04620003802030039481041c4804100d2020402160790704682a00c07500240c100a02d40c140c501c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 462623678 1250 462622428 462622453
    0x30810210f0f06060509010e0405060a0525050310090213030305030414070f050111060708150415120c050603040c030b06040615080a06080d020c040c05120c04030213020903060708061c0f05 83
    0x62389900540e400400b600c039507501d840da4000100401000c0d81c410302003003400324211440c0a180da0520300714541e01c0d41e5032450300b0980f00a01006941c4040c80c0320f48100903491128007151544029a9814507180396680ca60b401d0000c00340b54468021040350040041c002003282c0d81c40302e40e40803664282c8131210019a61403007551200c40031203a100c00304008034006001c1c010b500d103c442d58602d00403c001004c6004081d03030040b07612190410f9410f52110480310050003070411780040100400c45070366180d89002d903524541c4002d644801807242c107581005c44c030640c2c0c0301e802000250100070541c4041021a0100a0040505035520010760f0f1070010080356455010910900d5404260000d0449460301e00922000b030140e486007604001d81800440c6005406902050180c00e50b90129900c3d58214010000e07105c0a129444da800c51042203190915100481c41d181c1c0081c543c1008030465490401080d00c868145400c11032980c0c45a20341010089141c2c0c6814807140103034100d42c0c6945246 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 462624928 1250 462623678 462623699
    0x20901090608010c0c02280914010503010b040b01051206060d0e031b06010f0329130501140f040201120b0303030703150e040f0b1803040b07030810210f0f0606050901 73
    0x1d05c00b0390000300c10720a070602c503c0080345001c9501403d40014080d946c0d10400113048078031606032154400c019800410070317840d00340a5070400e203400b21420405854110000307084c038071506009052141c17501001520a03610f61058070214181c11405101e00100780080710f80701c1c1c0c440c035000100140000e20704d2034074080000304039059030890083e03003145500b9a142c42e140410a0112040e5107c10008619408032040c00094003e1440c942c1c0741d50035005504c0e009094605521000802c04841d07820408181c1d500151241c1098080c204001c0c0550017a02c0c1c400070f4080d405026405100010038801410380c19841080403010601c40044000e490b0f0b207041c0c80c098001e840c05403041c1300c0040340c140419000860160000c0c0046050302c8001b000010f003604641060348850040c1c0004982d02c001c0c5604410025808441404061070560400410a078408954090106030390074107564101003003c0c24440c0c00403030b0303044407447d80996010b20340f81c4084e200d14007510340610002c400000740301512 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 462626178 1250 462624928 462624947
    0x60a0e0601050f0d0c0303020a0506090109110907031d060114030105100b0a1e0504050a0e090601030602130e0f0604141b070c030b040b070915020715030603020901090608010c 77
    0x10050030450b4600303800c000c0301c1c0c0111810070383e011805500e04070004400c9020a4025031080c0c0150070640802c0c00e0150403e00010201c8815904060580000840c42000d9581000302112910010f807103c100480090045003005101c203403440022030700c64480090002d049034031001d66140440390410925083c0c80c4140c450319440082c400040c00101040b5002d48812007407440e1003079000446051a48169031240d042c1030105400082c00c0c051801c280004030040c00003140e6003003042c10030303070a860b645440511010b80507076404031351280540807000e028001405000804607042c108903440c2092240c040d07070410300c0f032881c1c92401c882110400041d144612802c803106249203216106401180d030101078111001a4001c00c04400288080712940c000c03809000404124a00420041d20207045034219401900620440c49005940040d900066501c01c0103c401c240c0000d190503005007100d508000c0d8031056540001c500440558060350441d29500002d1101006105054a003540c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 462627428 1250 462626178 462626201
    0x3140c0c06040f08090604030f0201080c1821030d02131205071e0504050705030a05100f050111030c03071a0c0702060301170703170a03050907060816020a0c0611060a 73
    0x715600042c040f49020300300f1202e8a0041e40c44500e0070028070002a52903010341c0041f074580301000c400c00d00703650780488940c0e80601d00041c0c0d41d242045800f80558000444059070384120b440703140000c1c150103a14074203140d082644040720340320301d25049008045d4000c1c85459050b03002e4280d0000d004022001049403151300540a0072000e0300380b03c0482c803164240c01700b05006104541c80000d40d5292440b41500c42d446a03a203c0d503c900300014541c06461000d01410503020501d01e06122801214210000b21002400e0918094600c400349070300f035004101d041801400003064042c24800b00211100081c800254080c68a030b40385520140680210354001c1e411200600042c820311106c2085c44080d2070b00700341110b513060343c0d954a0b0b089a1600c2c81e800146104003050724410f213509802610340046185004c0c102e2641440c200034480c0d9001403000c200c50801e03505000d8800d0090007c010711a4005031548881a245d01703014008146c3c52104001038070a0000062035282e0501c90380f0719482 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 462628678 1250 462627428 462627433
    0x90b060a030b0c070f020a030f140a050c010c0501240303021018020409020d06050a020d14010510032301060801060809030901170603120705010b01020106060519030c050c0d03140c0c 80
    0xc50740243c07909a0341001d001120a91242c01c0d102c0e01607511113402000451181216208115003450034035070000956015044c1e0358050300d126000194003246210180e0003c0c13070640c245038440d05101e07000d08405109500c806183d000030303101907510010003000740c85c081c1c0c084404030031a8610400885414100740c0c5810064001144010700d003d402c030b590028002404680783c030f480d58841000319030b0180e444890956000652013007401c0c40740252081e00210b00c6401c4040d42c94a808a450303641a40c3d2424209560307000b1044440180180c0540300300300d90611040190b8450a02901802c0300380508000b0030b01e0100090756080000040366800041a0b442100f0550201c0004003542c1004c1c022039070500a80c0c155400e00b03500f200180903414043e0001181c4969040c001908580d4250840010400104482c08045e001404090350525062400058480d110541100c580c05104180c03d068003c00500b044810380c150003e800960079100000710f07039250301d40d1030920b92165407000881074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 462629928 1250 462628678 462628681
    0x708010e010e040f060f0c1d010503011a19020c031e10050702010609020a210b06030c09010c0b0c07050c0a0f0e0a06031407080129060c100609090b060a030b 69
    0x18001c482005411520800400000030340070351700c01d01070303404014a03c0307400c42e42c1e4103180301819813001200c0c81011103002803040e00200741d000202207102c14000c81070f4480c00700c10001c40026a400407294203491a00700c214840c3e04c0c10400a40b6049d01e01e080303d22a204804450700440d607010740c034540d10401400103046081d21503901d8405800e000741000203655a4180000304100301e0b00003000700c05220780d0381c050f058008400b0081e8904103004000c1c4168038254400350942c90300c070300f142d81100707100f842d1940380c0a103d0012145141000c90041a01b40c0700b03014803951154000c007819106100d44180e5022014860a00c805107070540b152500c480d207103100c200b240300c81e0400c0300ba03001105a1404102036850342c90f04840600d0f048203800c41c03079000748010007140740c007840380c0704000c0181120380d0b4030341c0e100b900740c40d812200c2800780e54450780b40013460420b035450400081080301c01031310301030250a9880500d04002c2c5000c1c031041c0c03009912140011130382d01d00105004103030380e4080f01c00c0c00e49 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 462631178 1250 462629928 462629939
    0x5150904150617070e150d080d090c2414191112120a02042303030d1a01030b01020a021305070512090717010b24090604080f060708010e01 61
    0x3103401d406814041250382e2040480c0503640611000000001030004210407840e10b041c00820fa4002020070b18000c9003505260840d036074010b90482c42a42102c00301d621819402144c0b0024140408010522600140001850301c40030030700e0110903040c0310041103c240c1c40c1c0001d40d80540c171380309000e00c1308000b000b0b01c09040680c101c0c12040782c0c40c0c0b0306c0c000c1c11a545054141b4071b01403c68410020882c004901000c82c03a28000a99900081e00c4d4410760401d45480207521814851f100b000c4140e001d400c120741d8458078108280d071a000710220050103490a4030f01210b181241e50662180000d0030048007510b40d50000541011141c2c1c090311890804000440c00c02c0140740c00b40808081103810040c0f0003110100c008041d0045000c100605102072038005150001620705502d1602c0e40d050200c40d0750f40ba80c500c24000c55000c581110f2103109280c250050703c2d18030502004542c845004500400d800c1c8000407001c0812182303800321405078a0f81c18065401c22424411501c1a02800005004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 462632428 1250 462631178 462631193
    0x70f08090601290c010b0301060f080304030b04030e0306070f0f03021c0203180a050304050a060f02150709180b0907030203010e010311041103070f020706050415030e030405030f03040905150904 85
    0x6214200b40041e100320484040070f04150b4000070302650640e46500c42c0700114070b02072042c0c000400c0c1a4809101c080e00d400302c415200e0144e84006481070b40243c0c0010207240c0103400002c010440101a80c2c02460030060207450300c9282142c0710001005107003a5180346000f40700701c401d82103582c0140f150030100c40c4c089001940c40240328003a4105d4012750160030020800038030807007a12401c090750300d550600060009200c00c542c4900c00b08060070034503031241074003c600747d104501c0b80414a103003507450210079148101244e00c000c0c81014010300c0e00c4100c0c000f9500c1030220713110071100c4500c203448020003103041e40002e00415a10903032440040002990520018485450160012881c00000c3e5a0004d07960011a01d800119150003074003144554107101000c040c00490500d00d00303150402c1003c00810b15000311810615554440501d05201b0410607513004000090446104898100186860307822034821040d640d07007400040b40c426145480910030504020301084540e50b20358a0343c0d007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 462633678 1250 462632428 462632459
    0x90204121511041701051012020105070327090b0a050609090a090c0312080601110607300b21120f0d05040b01051309050606150c0d08070f08090601 65
    0xd00603070714040040c881d4142c601420080420080b104141c0e0011340c4035609460b002050070941505d03035481840340e00d0191040100b0240c080c80c000e5111400303460144e8502c02290102e00d03490f604c0c040c40c3c8035060043e010f00320175605170403801d2090072410f030184060b04000d4000d0503401082403040042c641420340316980c0c0081402c40204060703046071104e07004401c16800990f58070388a03c1d201511580c02c0701030306070460400e18011310035082c210001912010301808820410040b46c107205110b00903a4039902101c81c03840f01c411051080822508002c1040c800300e87c0c0a0412050307118480c03112601140200100748000c2c02c41010007212100407507014201c0c1030030807031041c8040c4441c814523124191040d48160307811241c3e5410070081103106200f0040c0c015400b030401041c14001078021803030540110040e10451441003500c510a1098042c1f4106003100c3c2c807070308104201640c2d024101d00d02828454607255007141d02d001c0700310b0b840c640454244106900c00c000401ca401120340411 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 462634928 1250 462633678 462633713
    0xa050a061e020a09060306080c0d020f240405030106051002070b16140606090a09020d0204020a140a0804021f0516052112013005010209041107030909020412 69
    0x1940300c2041c00700c580c4100e0304000c81c0e10001601001e070a010300d03600f610035080035201040081000b40300740000118594002c0f9002400f685080d01c502800d0346404c0318070070142e9440c00c0c20540003051210088403d400601c2030318429800c3c17103400217a80c01c0030144808480502da0240c41d0072410042d1548080e40b24034006c4d1008039007410080040703070442001004441e4030501030903050610004124558501800041d5000d00d0023904100590380c8105012510f94191005604c1c2c0b100004251108503c90040d410f14202c0007c03280c011640c403c4070103124500c03c841ca2003600c0f20500d102507002a828034104007040007001902d000f49907056038103e84622030021100c50205001800703148035180d44400321140c00100754103503034410140d01e01c1e014000422003d02d1410750b0b03062901042c11115691107605100201170000d00c1401c0d0112649928060010301111401e401c1c4105203038000d007420380c00210351100c00302e036285550007218120b64a083c88006541d845469011a1500b0304521 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 462636178 1250 462634928 462634961
    0x51206070c051903080f07050a0504050f0a090612050613030e09180106060e030705030a0302060c0f070503040f051c03080c090a1e0302120a1e0501140a050a0c020a050a06 75
    0x12074070801c014003001401610903a10311702203040c001040383c6e8513100030b0b108070b081c04014000b414071540c2c0242a141290401c941c100360911001c004541f0b14145900701ca540e06003040c030041968400c04030307400c0d0058820402c0303900e680d1f5a68004c00480c0313100200140014441e03a850b214a04d0195000d076001450030307414080740c0080c0358680b4215940eaa0000300030a940400000d110300c0c007484000000c11090f800340ca43c90701682c0e0025110000242b201300c9650700492407040e001c0310b403002c0e2400c80d988071040300d80da1074440740f010303810b001a4801e0314400d5103143e16030292452a0846401c950307038541c42d1661240c0314044541d2540c0c21606546030080b04c0240001141503801101d40c6c40b110712024210180c60460042c09914141c1c0f110075400c682c0034908100006003242c924001760f40d01e1180c00603015406180c164054000b4150b4030b01c410040e041802184002e41d0b11490003070400740300400103804000001d0343c903184080000b41158008a0075440400d110390481300c6c050a40001c0e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 462637428 1250 462636178 462636193
    0xd06020903010e1b150703030e0a120203030a0c05130303050901020c18060f01110c010509040209132403020114030a240f1d04060b06041505090307051206070c05 71
    0x700342103d040012840060b0321403d14901410000031156028110645031404840311000842c01d0b07030f102d902c00003010541c0d9803803684840b034000d00c52034445581c0219072058a03500003800030364940050310403007441b620301607846a105000380c044680702d5031104900c0c1e00b110321f152000d90316034211003d05030560040d400c3c4602c141e03a552001d04191450346a95080c2c1d418101c06004850071442d04460601449644105d0b0305c00000941172283c0d9424a80180e4400e40c03880800c0c060300030b00032640d420944002c0c1035003011440da00f1880f030042c940f0381e1702070102504000249140025120181c04292903080d4542c208403554002c680c446504c400204100500a0680d40d0b50001101c486074907103100d0f50148941c4807c116154024030042e00d0306882058901d210381040c000260008202031741d122200a696220070080d40c00403c845a403a4808031404170001d40160b03c031080c201d1080c0561032000c210383c500210a014851020f40007415a995243c10a494407100e6060540d020b00c180c95 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 462638678 1250 462637428 462637447
    0x150f0b100c0813180b0f06190504030605040302010e2a06031b03040305122a0c0f0706030b0a08061003020114161104140402030d0c0602040b0406090510080609060d0602 74
    0x85000008111594000d01c0204d80c102483c0308413441c441d0110710800c500b0f15140d8181d902d080568040f00000c0f61941001c20088800f40c92610031544001d14141c00c01040200741901980b0414488500c5030a0321541034000b400786281c4500317410388a8101d640121141760303c0c02c040000e180e0026030414180f0451200d80040b0000345c000321000c170009107000580360329a0004101054011202c0440c1c0c40420700700307000208100302910311904240e40003103503d0003201c104001c4035580001e40c0e0291401c05403038941c01009002220300040c01061101d00c001102000080c03800d104039000d290000c210340c110b90044840071515003402d11401000c0c01803901443d500d60300c003030303100c0d11034031100b498100040c050000790f501c4000301c1004540600200005610040b42c900603001c82842c4c01200c0c1001441c0c18402402560010001c81e2008500030420681028010080c0d4008071104940000c0c0d0311021036941c036003110103d81001810300071030544d00300041c5119590b0f1040d00302504000a01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 462639928 1250 462638678 462638707
    0x60f010503030a11480922020a0303030b030d02031801050309070e0f07031d0703121106041401060e01060f0f050903011a041109030a120309050703150f0b100c08 71
    0x12056400240d042c02175254061070510540b207403031401616281030480d9001e0000740d40100060030220a4055090204410018484030080c2140d00428400c001601c1e424020010041c1000050003481014140d03c04240004191001840119601003c0048100044409400240c030b881c40500c10b050020600d4006042018403441070308a8003003892800001c010140c0750140c0c0f01024440d60710f803807034000c013002048c000c0c01c1da6008000c1c103002150000044408854100c64101203005e044148010000040c08424031070900e440280b10301c649603640e40c10702810070b00c200404508580307560f0384e0305402194803908105950070202e00340318820010074255460100060750911016910700e800d072810303201e0380e400348820026050400c0d006401295aa841c04a005083d0903a071801c030040c0c80b0f10036000442c03100c0d40a002d403030309d283e500d140500c0b1030500100c108843c581425400c0000402034414032041d01c1e80180b00c840001810700060b52418094a0181c824810802005000b98000e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 462641178 1250 462639928 462639973
    0x3060106210c1e08330d02011202040603061409130b0703090804140102010c050c0712150c0519080402062215090314010c141b10050603060f010503030a11 68
    0x41c0d22030300013501c0c0138015064868200708010b5101d080c501e81c20540d01282c01d080c4159480103a8034030250840313500050302d21900c0096041d204170b00011b004900140e05400c5103040710813140c2072074440c0c0824020001ca48100f1504451408171000410300858844813003960006c0351400d0000b1614541d8131010201d5005030003401c410258400300c003941d964244251a55070009240040c10304240e0504d540d15802d0130701c01c4c0c00d44254100e0090040c0007440303500112001c607804080151418801020b00207401c216400c0d1403801e4a076206004481c01042d9151045034000e0004e1b00d01080381140d2032000b4043c21701c0c0409a1440300300801e071700c050f90344000106070054881c940d00724038600d0880c0c0300c1c140d10701c007120050341030031110000301d9040241000c031007180361541034851880c0c10441070101001c10814a05101d400200000c84940d5840a40101c106600b036420b25650140e401020080030300c00c2540545c8108840d074403c2d80305400250801c080302044e41e500081144221303009800703 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 462642428 1250 462641178 462641237
    0xf020d0605150103060f090e030d050a140f010f1a0d1a040c05120402012703060b0f09091c09171018050a060506040f020d050603060106210c 62
    0x9071442445080c01c200e81c6650318003142441c0034480e0509140b800c4034118120700c00d0781101a100c610a0900d024140b05440c504585640100064580344e0380107409000840d83d0091540d5584010840c801c0b000e00c1e4123416218903600b5442401c1c036014803050245412045146442411b01948c28500854020304d0a906d080e1320840b0014031541c410441110341c1c003a9200306100d0200700d050240d0100c038103595070003030b02428050608072442da13004401a84420300c0c40a03a0241c2d41002c420441d8550110885074016620791520b03120250520448000c2a550501140c1c09501c0394101c1c1d403511442c642c02c0c2160381c43d060340352aa48995001020700000c0450010b500107070a001c41542c041c0c1b0032502c100c40b0b0101008281445606c4103501d525094070054640d03600d03400043c007251aa03800900c0c07200b01c1460700310760700e030300003000c1c680140f00699201e84227000384400026424440c41d200d25810a01c0001c0300c43c0741020310074110007011070b9600d02052055004400701d40d2469180724540c00c04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 462643678 1250 462642428 462642431
    0xe0c071a09300a03110a0302040f060507030206180705061b100603031b05121b06010501051318060e0c0a11030301030b190e0f030706060f150c0f020d06 67
    0x700040854104a4902c0c1c50604808480c0001032011070040110358004000603081540c070380c4124012405051102001d00c524900041d000d41d20651507070007401200c412000d81201c09440740d008681a00c50b906016006900150105680755011000311520684110071506a503a42d50301042058000383c0d0408140c0070001d2042035070709814001e603102070114490802046066030780160440500a4400d18200d50b9080c1c180d04110082020300b24140541c0d0100e511200c450100d070720078070262140c02d6604d004000000401d94042c909480c2442c0d41811003138181c03800c00e5560b215040c40340e20b088030030340e80703601d000100718621a1f0868040c0034074110f282d60f0f41c44e1126002d0704c003402908078109141d03c104010008a0303c0440320381c0c0c1006c0d44000100005400d60301c440013415481c0031034400c41c000c203030303d216190744000001d00c3d106200300018030030303103643d03940184441c045403107041041245100071900030380c41040420000c82c03150920961854058000c40c2081910300c02c200e6885 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 462644928 1250 462643678 462643681
    0x8030106080907030623010801020a14030903040801061517010501090909030512040303090506100b030402092701020408120319090c03060509070608130f0b1b07050c0901051206010e0c071a 83
    0x40007480186d502512020000f54038002d0100401418000c0c50444e4816444010021035000c100c1802120001c0000100a12545498280c0b1142e54a5071305856000b1a00b1441e1741d0028103100c10440e03041f20816100d084040d481d040f4428041c00905004804000c010009180c4032003203414035a000b01d00a980010f11104c4a142c0241340900180c030800e001842c0b000704110081c040800c0744c0e44640e040e1581207403901c0d42d800306c100d40358503002d46481c0700d0314260320440200700c154040e008842e40c02c0111a01c103a8080b407020600c0c4002c0c0d608d00c3c0c80d14800d1032407800300070345500710603206071042c01c901070384a54940324902115802c0c1d46a04041e08480010028503a00860203500301e01e0724000f50180c000e003a550004404643c2e0f900902040c0d00400207221240c0d01c21103249400c045480c010f07541e030f810b841c0c510744403070040c40514420f4400d04008282801c06500c8642040302c4c0c0745c02808143d00700244d010038100001d24118a16108209a00000c4c1c2e29542c2040e40c6028440101500e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 462646178 1250 462644928 462644981
    0x6090e030c0d1707050d022701030605010e03030904240603240e160e10050309010606021507030e010603061d0c011b080c12030103050f06010b07080301060809070306 73
    0x40c04102c010301001c12001d00740860030100503000054202080f03040155070f600800707052402902078141074540c100c0036001c0810b00d43c84102c2240060391707000d81e0304201803515800103580e0303445103c0034590182d1041c8134049031410a644409111000c2891503042c044d801202d0f1010b0810300c1d08102e000a0321030030714070280080144082000441c2d409500c1d541400c0c00580703041c11200070074009000d04922000030034a40a0b20100c1440c18010305800c000a00b4564050704030361013980c03901482d40c07074240001141440810701952091480d01044142d8075442d60440181407404940c2d16107540c0c4000c0000000d19030702c214040a240d0003c0440042c2c141208541014514081541402104010404541c1d190b105020441e580450302507110b00c0f808203c0d0785094020034094020020010000c0180500000c82c0c0001c1114802103402983e282c2d07101e00828083e06100030440ba100b8401408031030302400f401c9034000c803034030b0446524035078945030001070380d4900d810208014040c1c100e1480c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 462647428 1250 462646178 462646183
    0xe06120304061d0d0c26121912060b07050f010606140a02150a0608211c0f020309010209030d0201020a080f04051005040b0610140405060912011e140402090f090106090e030c 76
    0xc4030070840d00900907061280d14030411500c6404480404c40342022620235403980100030808009602110070040c00d5240d8007502d8041c0e0140d034059030540f02da0943d1100c0c00070140510f20540d44940c2d1041134200d2810b22409076074024030300007802d5000d01001c0010241c0b41c010118802c0e055401d0109100b4604403030309007822402c0c10005410104c3c0ca5118100718139450480d00d61a580c5900c44c810129502d0340880200440c0d61049283c40c00081400744508054001d086c01036402c80a40d180b40b107410000b6403c0740720b001e2805c4e0104442900091188901d601c43c2588079020301c007038030fa107010b18580741c400312001283d0844060070020180a10fa08201c50040c103001001d00341a00d00c1603220010400c030740074a110b401d200f16000107414045440d1030f009410802c2d0701c0002401401440c032503034420150000585078140d03240c0f06800c84005464034802e8000e030f8014101490300d4881c0034403001205402000c1140a6480d00b81c0012161101c1c0304264944040c54003858544c10224201030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 462648678 1250 462647428 462647489
    0x30509010509061611031911030301031e08040902030a050709060905210a0f08040816030803070f050f160c050a0608010e130204060e06120304061d0d0c 67
    0x419a1614040000b25080000c481d0b0304030941c00e031031513880944543c0c100c1d400700103071900d8681c2e800302003401002900182c0d885203080314076495131715000310003c161b5a5640824030002d01b448115000542c0000c9540101e445014042e461031480d0549440304e00085e40d105568030705049640d0340401c51080ea1040d05400682100d1411008043c03800d0f001407084102071580b800a0b42441900c0220746508009100d8039991210039100001018100004a40c00c28400d000f0b19005440e051a031a40c1ca0020050070390f68490451030441d155043c04807032000c0c410840c10305010040140400da5600b4002070400e06a4004603118402c59505e070440070140b1a900990140164070300c2444201e030060b51103410364013040070040140c1c0c1d07900080c03d0b2882003928041e411902c2d00c8030209600f81c100424900c101025603c4c407412003102d140c031503078074400c40c40b8510000346000200200c0c1002512480484e0344007c004421075100c80e00d440030003100b81c1d44001091000440e01d00316400e001c18020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 462649928 1250 462648678 462648691
    0x30b01060c170a021f090b0106050403060509010519020309010902150a12020708031b0409060e0a0b0d020310090303140708070210060f050906190603151710020313050312070305 78
    0x2a42480030040000c3c0d55070050318038458017040c203d2080503a02038107038042c0011a40080c03252a8a5035900700252040d44240015507005007040300051418105000c1c8502481480c552040c070281100e034400001d400c0501580025500c41f070050015a862035682d1410841c0b038400a0f655034101d10300500100c9a03069005c1c4501d00500121010031080c0b401d030f940c01804980c180c43c504035002c0340d03174400703203c3e030b0b0000300c00da03468944040703165803001c00306a2140a17140b00403c80c506403a0308000035a261004001c1d4076522080c60012030401c0c0d508035540f014881c0c10003150781440f0100103078050f80110740c2d9800190002003002004c07941040b180c1d464000d034680804c2081d042480c900f42c00c220b2400303200d009020002c08a50161124500c0403088000c10414503992912480018040e005540c5d85004010f9848030115042000200c50b100400c00700700148001343d0409240c00c080c0d0801030040c0190344030000c0a102103142800208443c0f6402594001c45240081c07001c0c2c01c503a00a0240d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 462651178 1250 462649928 462649973
    0x80c0f0301090213090c1205070609051206041e1a040b100e01050607020114071a010b0f09090c07020a0b12100323010b0a0617151c020a030b01060c 65
    0x2550260b00c50003119070442034013440108080300d140c2404441c120881c0e2241004c204650171843c180000490124180d58043c1d466040340340d50f450400ca1409400c8198405541055001c5800242c003c006280c1c070070038030100394100d02140d88410240030100308181f4221440a4100000c2040f2042c91030b42c080e60158415203840e042c8404d9082e110014090b060003141c0010302d900644e802812030030754a0890b144199a0b90b4080d103804056040d139400408440d4480c0b030300114103051560250703945c5c4a80d58420a05045140040001002001d44425020502002a5005178450b4665074001d08588080141e0b1002940b4080349c488034000e0038003103541e6800a0600c0061510060282140789268000f001d15232410681c034014030b42c40d000300342e02c400c0500e40003072035681140c880512000f010540803583c5c1d8840c8600580261000300b0706a0008045580711080301c880001004601c1c00030701502965500d0b41da1703004483c070302a040440410310100c40c2038100300181c0e0030310032981e0101ca00c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 462652428 1250 462651178 462651191
    0x6060e0106090e060102030f2712190c050306040305180a0f0e0402041409070602060603071d1902120603010b030a170c030906040b09030f010c0210020a0513080c0f0301 74
    0x800600040340790044000410b80b050104084e60b00c200b0650f8205451301041c5541c2d4400003c0c0c0720030111841200000022442190711014549480104411081b00303000e4502e000000c0384244900751a40011100345003080380c045220345080020030f101d6846500d40954880814201100211890582d140b01d4074211405200440200100c281121648082140f45845500c00140a020540c0400d00d070111000300b007142800002610324100c139410740903200f507910740030103040e190605070007408082400084041d00d003007260078880d58042c6500790403440600c81c0f00380c0b1744142c0c2e000c041c1c0b11109008007024030080e03140a10030b0700c8281a00314000d140c80c2c1c0b0700740d03990081c0403205803c58140c1c1c01c2c041081e555442041c01201c020f104020700282d0384139200d141400c05a004045001d00070310981968241e070a205104010b41c101c002e800034040303200150f5200d07000e94004603940301080014000292000e02c480d01c2c40016204210180415544010074807299518400169209078181017 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 462653678 1250 462652428 462652439
    0x123c1c180501020307080d1d0105010f0f05100c0503190e1c0b0c030604020405040f020403031e081314010c12051b0415020307051014070509130506010e130906060e01 73
    0x1044403505c0c0d500040c240c4c2c40d200c40c0d5021800408070400c0c02c0d10005292000d4015450041d40424141c494002c00d080c1251344420064140031003a000ba036400c2101025841210380c0100c0008198070311032002c0b24540700717260105030400c014926020021541144502c09286003a0720481c1c040501e1000c80d40c81c1c20314644840140d003034003605080c982c84001001c030f401922150100e50162101800500c0500c0807004c00400035801132000368005a000f620f400081b81101c9090030070407682d96504000350b200d00c4000c1402403482e040845031541d5000d03500c00040003e00448190310f81c0c98075a04c1d8079a0381d0480100c10798400428031241c00600110a18a58150320140c500740d480480d0010610980d80b41e05030300d940304805002c0c01c207105e00648000032017170f5900120180442c0304003807610750321f42d450103590354013400d410144d004500045038043c954042d44601d5202e8014541403000981a002084500c6105841960a03580320343c503400c00d10455018420081c00e0783d0032050000d61605 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 462654928 1250 462653678 462653683
    0x60f19031b1808010c080f070306030201020303041502040918020f042313480b030402040f0f0209180402090c07150501090b123c1c18050102 62
    0x8481403400e01c02c044036001c0414844100b0034001d00069402000900030149001d0080c150888410004402c035400003103250344203000701000c480d03042c0c00850850b01c81d55500c083c0000d030350901204d415800e01000400c03035650700510481a181d101511058000c82c01840b00c241d8460148900031800d20108141d150342c244520307001c0d81020003020640e915040311070505030500b00c2c0094014505115000e0344144c802154231600e001c5006800328010210b03041080c3c00c28004220030744040b0b000340400c02c2c21610780082d13030700620003000007c0040c2d441d1100b04c110b460f0042440c400350790101340c5011078104a003012540000d4828031004524041d030014106040040c003884a8403400b0415030300f00804001d291110f43c54804080c0304645e12200d030680180303800e10702c0c14850700c1c9170301181488540200f58803080b10100c0d0141d0303d04080c0308003504001d54507049040e144210348036140c6003134042071004520700400403402110400c50030746c0080034610300700b401165880010804100680c1c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 462656178 1250 462654928 462654971
    0x9080a1d060d1a06030a060f0906150c0206070b040c060e0f090c0c241e070207050f010203120117060c030f04030309020f03060906010807090b0109031709060f1903 72
    0x4070040829012040356542e001c0103c124002030304000c0100920460045941000d0159201c0d449200000d95480819005030f80f00c4c0e00c549021071159010403152a88200c0c04803554074009001a80307040c0c96a40c2c2c4054055040300d051760b8804028109001c03c1c0d60207020308004031001c90f6608080e0100000140c420a07000c0c0001015680010b0302000100083c448560501d030140c403829000b2411103481030b82a24203c90380c5841891200982c6001d200b0003040c180a040e59600170100345003803c00340412001740d000e107030b41035100503c0020290340c040803045011b0107540144c0d9902d40c0c242c2c26102e1400201030051100a0014800c1140300014050600e1344140c1520340418903c00c9070011825030f80d041260340b50076000b40010402c2460000482074100c4038803800300c4404540c1d405000e021100e40c3c0050a000030700038981000414420701c00c040309100c0c100b04240c0303041e00990000342e4540c130044441c0201280402c440e1020500703080d10f0109030303010f810300b032000783c600181803c02c0007207 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 462657428 1250 462656178 462656197
    0x30403170304061d010225031707090b0f090319030503070c0c03020a0e0603150c0d0518061e070203090901050409050a08030c04030605061215150409080a1d06 70
    0x34040005801d0003400d800225000e00966050b0800c0c44801400c64082d600440c00d07030740703560400d0140b1090864400d918080c950380655900010207000209944041d40103081582045a026400f10310704841c1c0c0002c00401c9000d0300c0980d9616501d00c141818950785503440036861101c40950008240c00208695102e461481c1c031034880340844c50000700d10300d07180d0006504a0021f04002c91500381c880f00540c02803100b03c0440381040090040440040012615040251000d01040c1e50080040c0c2000750030410324001c1159410307801080f5071600034100ca0181200c503080510000d040550201150030110038805035207401c51440220384a06c1e018481d050195695401110a10006115034041c0c03c0c2e02c801d035240d03242042c00441380b6a4100c0d0105481281c501404a1a24075190550019040c90340300501200f44003820a03941c030090080000c001d013481c4c81c081c1d258aa469101c1d944000d48103030751164850891250061803440b5142c0032541c60000300345203015580c0d0300415140010b1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 462658678 1250 462657428 462657473
    0x9080a0507150212150406151404090e06060118060507030518100908070501030603050c04020915030a0c0f02011505100210020304080717030c0306150403082802030403 74
    0xd5052800c1c00c04400c1c400701d000c407080e00c04144c402190310302108640c090407003511420003c148040410085401d90312414900800105041500b280a4000b1b11141030b80211045d00300355032001c0800c282ca107205c40c10382d002e03000102000090340e041400c0a0000c2c2066150310b01c0c642c05d00350064004d1054803405024070101103441c0721500c0c0010303248119440007428003208144940e00180125840340509100d038054807201040d603501c81c0c407803178080700d070004028031091481c58144070007507209400464200e80620341078001c001551340114020b205260001030b11030042003000f040c1444011800045904052125004001d02b400c840103036242180d910401328680c40c4107a28001c0c1008000c1012800072040000303005a507030150200034001e815820489103480240c40491000b1102204401d00c06d10106459082c80e00c045004280018155407a198407a120040180c00529805a180c40440c00754004094992584925508940009c5051a04650b0b5460360610320788000314404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 462659928 1250 462658678 462658687
    0x1103010617040804080f0601060e120c090907080706021c09051008090313060c0605060102060717040f0611090a0e090a0809040f06180c17070e01200a021309080a05 72
    0x3c01d2034000c0f03c004281c85804c0303624030400388480c01c0e12141d0900c52540490380100d0841e04905201000c507207410070703660203009540164402c00200303050150008000d4071803540081940d903c1008820050070b45900246500710500060842c40d030034280e41c030780810001c806d0410a9440d2040d02c150034640c5810454816540c41107803610f0350045014050520300409400075029822006c4141954000c00b0280126030b20000103903625075080d43c00300002a49500b0002503020b60040345508244602100c150340d5a850f201c0030191a010500c1c0d8039842d000242044407882c2040140006140c038180e03c60807441c00c0c0039500d4540151150182110f18001444000c607920b0381e01100300d13a010f00200b002065110f64200d1407290340d0f4420000013a1074141e00200090044200d444915540d22400c1d00b1a602e64804580c00b00d11540c00a05111210b10800e134410302d05070030101020044030081003001024010040c0b00d0061018081040e480c100c400303800305180c20105c542c440c05a06007166503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 462661178 1250 462659928 462659933
    0x20071203090605010b22080a120306090903030b040c020d020309040f0e0f0703050f0703050c0409081612020c0105030606121008070f09060b0901021b010e1909110301061704 76
    0x2a10825500519052903c00042103841c183c0000c1c103d034410107070620940d07848880b4500d05d1580c040c003402c004d55001e4149080000c0d4411080354003440a4500802c03050f43e240320401c01d03560001e1045011036240c80048180d42007034415405250007910042c85040c0040340701079128401c2c0e81503680150380f079541d010350302101031300480c001c1c00100e41143d1780309403001d02071a242c502c18081295940035003011503010480008680080d0b0780c014014041c44604e8000f004000d01c0e9240d8215220b030028041122842008100490460f010722311070000340d05025402814031070040e048906210b010310601200b62200c000780c550102c0100c42e402c0742e075102c014411004620b00c0e0b1100b060791050840104400c1e9502000c003048039215241402500d80360740c003034200d0340a0340c46035500580c0700340f00b00c4109520340040240e042c5418104003494a9031040403c4020446039180c90214451510400000545102d10401c00c00b074200e01c0350031541010f600a0455111040e00d103613010445020bd0b05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 462662428 1250 462661178 462661181
    0xa1104050c2106010318150504030324050112020a0c06090c08060c09040c0e01020d080613111818010b2a060603060f011a1b190620071203 61
    0x152880401003030709903201d60b0080880c620480d2560300290900c1460b851071603115042011040c0d00c000580a0b03410107500410013020024002c0d010161201d0194800758080130b0400c1005246840350744002d410040090700e500804403100c2841d03481000920309281d84005c25407481c03030340b0450108000010f414900309114007500440d80c1802460280700811010f40000d03c0038401c03da034144600c81801d001682c05c51168414903002d0f8000b10340d0306800d07510a8114a07840b10b4010100c90b140382c06a0b14000848205a008240450000882c5440410001c00c00c808a0b001102d20f608401004124041c41c060b061213a102404400b01e04003181b568045900103402c0c02940d0110b10700c078400b1014a6440e50191142c0c3d0003402500046403220004116183c141c50400300c00c021001c0c030424004503a54045032844c28003240d8525034158100c030500c000010310070003201904803802241007440c2101c42898410700d1104c55070040075a015a54000d03100c903250811402d50309070019a80a80 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 462663678 1250 462662428 462662437
    0xe0f07090506090402161a0a0c0318020405090109150f050105040b0303040e04170d0204030209060306101202150307030b010f020109030e0d021c08030901150f0b0a090e09100e0a1104050c 82
    0x340b00c00c4c8041a07e021480d034030707070340c29214800d01351091018509210301179040700d4071b0071900311586010103460805800c09030042500080100000180c50190740c0703c40012410264030246031940310000e288400d25140680350241104440420000380c01200080d60ba03c101c1c458002c4001d1410001404c0c086e0072102805205070f5401074a580b080c000006100a60103404100e2044d150b0901083c3c0608001558510549186030040f111a04107002071503802c82440c0101e03070015880141c2030b4049007c002640c01201301e900d0214481003800c0000d4140703c03003c80c1c00c07400c5a01d050b5269000c40d80c0070a0401c0300f5003090301c1d40304040d400c50011030060070f00302000c0400c0350411300c9618204980000290b00c1342510340001c0100d054001c82511a0312035511442301b020310300110500c440030800c0f000342603004a500745603002c44e5640d8071070300c40408202c460000c5500442d0b03008195030098050241d4480769940609040c481541c0da0a054600d2048654092a918000109145a514101c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 462664928 1250 462663678 462663683
    0x20d051603050705040507050313060b060c0a06060504050915150a150216060c0c140d02030a0b0601170c03070f0908010905160506030103020d1e06060e0f0709050609040216 76
    0x98100d96100e040c025520607891080c3c034066454180000d0b40c20344142e041d01e0050ba03858007402c40d21a050303107403a809400b45841c0250f025204004001c444803040004000c03c6104420218170203140c002003100b00d030b030010002d03806504640c000410b0440e107441c803a6888078a00c294180345d8100c0d1004140940c803140c01c01c08450861552a01210783c0001c0c070602540ba105521034145030700c1703c0003183c5100321401c000f419190f5010b018412003458500485c1e406001804050800a003078002030310341302007050260f446050281c103001295034002844080c003034114542222605042500354030900c402021a0100710005038810940d520034000c2d90002c1034090024131070390101c1d0421607203c2c50140e4884420344010440001c0f1401c0c6041036a0489170014491415030031541c680f001000074240445111801c48221f510014107a0300c615000340c44161007511441c5450008850b11207406000d40c001d02c101c1020404c1030303960320720841d200000141c8016807070303600d02020b00307e29028070b0070300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 462666178 1250 462664928 462664963
    0x50103080d020c0c060d1401050f010f05030901020d1107030801050d030e041812050a0809150105010513050a030f122c040204030c060816030b0f010e0d141617060103020d05 76
    0x1c0e800710a840c0d0085402c41010300702000070745e6030ba801001010410707001b1041c042032000000ccd02226016a01035a44281100005460000a2006801105c04601d050000c800e00403079030f9001d00d0340c0a100503014040c1541c001d100c4c41d80a4a0140044a01403480740c420754885040319100200401c488160030741c010354807405419002070182c030359040b42e038942c1e0000300228001000814002410a1145950840045941d08000045983c0d9218541843c40d1000382240000c0d01c1d2600018603000b18061b13281c1d42500c40b00d03407400780c91071344035400c0c0182004081d59217044c0701c0750312411004c2c410603101a044088005240401c0c0039002c0c3c1e6102074402c0004040008849402c807009505c04c3c0c00300c48120108103500a02a000c40f04034000361500458207400c1500c855010300c500321500c10004103407401c0703441e10b5640c090031480000244103542d000391b452212240c1e03c6580500141025a1000ba0342c01000202166503400c14480603100705090070124042c01018800307072024280354181e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 462667428 1250 462666178 462666187
    0x3110405131704090c0905060a11070b2704021305040c0314090f150906150f0405040c05090c0c03071506050d0b0105032b0e010210140402090109050103080d020c0c06 73
    0x4441c3d410900c600e412880c10720103007000d042d103d280440700303a400040800d401d0491111007200c00304c80340c54000390716105403e00407480c0b4004002401404100780d0401c500755100c2c00b0703184980e5a114210034002c50042c0800c6501780e0801c01c83c1c0b426910b0503600054440b4090104601a00a54021800680301c4030184403010201003840e460300c04046045841c5441450b00c1003440400469603841a0f13041903000c20b000c00e0580701c403e044034100912000020045074002801c49005440845102035490303410800ca0410404c5030750700000a06072a41440d883c0c8542944900c151040140640d0b510440588890310b6580240c019000c041c25040c503000c40e0745803c2c890041c0a0140c1ca04c2803290700c4000c580400c0010000d10440e440c14155036518138104400c1d208070103a10300300d5055002e50201484240800d00c504a00e402100c0c511341e6103401d241c010b10000100c103801040d14541000c0040c808151494101c40001c0b182500060351020f04102c0c0c00d00300209140169801100080d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 462668678 1250 462667428 462667463
    0x706150906030f050c1009030f02010203070212011b390c0b03011707050d080c0708101a0d031713051f0b030105070e060a02010b030a0c060909060311040513 69
    0x40c00c210406203e4130403181c808880504000d145030901e950480007c540070814800aa91403801c03422071441030045900b0031202d5400a00c07030030007000300d420300c51713640d40405410300c100d041202c09581c01f24180340b1412400c110b0040d80c0d61082d8040c016290200641c80d2070707003030540042c1168190b0001000d900070b80d180d841d50f0301c8551003840b03800c40b91609003000807501040443d0707a4045480060072a410500710755103940180e080b4980c0343c1c40e2401006000290700d2820301c41c00c00102d0030540000f850740d0110300724821515810f80c80c40c1c041c001315a050400070707401941c0c02c100040115080e07049541c0c1d50300b86c0200e548540b20300401c00c2c024007120416119569000800d5111071f00414404054118103042c221803044400030001080604980381c0303400d122005007407003003080c4004500e10850a0100f843c0010035002103403101d0322010108070280d440001c010207019001c42c280101840c5445900d40e00c0076030003c0a01c125640c0001c40d6225408130444416546e120060442503c50b04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 462669928 1250 462668678 462668693
    0x60a061b0c0b041a04180c0512090606100203070c0902030c0c0f03070b01080c0a060f05071a06100908100209011215030b090307081b070b030a060f1505070615090603 73
    0x61040100144441d0080120400c6131000e860a44000d07201040019420f59038441c040c0605040f00800d00c50200510480b0104007400e040c41007801c00300030700e014103111040c00745003000801c198045400038004400000d841c2030025080301c015000144e00ca846044502c1d04c540714500c4522100d204034040d1106810010000d489014001c0407222001c0ea40c40340701e2600c03070704000151941311415090a21140b4025460080100c0319464842e0820b1325640c0d500d021039000404c0410079540c26020003500b440c00b0054800e1180c0c0b24a003000c0c4032880c0038445545c9195004800081c0c540114040340107921510113800c4680d540070050022183c4000c1040781f921450105480040c50000028581200081282d19a5604c86089440d095004c1c0300070844440c0c2103d084514010b50400081c4c401640014500405043c400001c0c45413401380d1101114120b58045034a02e08503094281c00d0907088816288003503046070300400c0c01d101180e420010803043d03400450a0a03e00817001c001d12011 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 462671178 1250 462669928 462669937
    0x20f0303070f1d0105090114090301060905253f0906060801060b18030102070515070e0102070509160905040f090614060603040f0614070807080708060a061b0c0b 71
    0x5545860341072401c000c0e0b6089980c843e0240c1103000c40d40c1000640780301d511a018030101040c1c500c4401d030408004a001a0075920035501c428400c40d1240280170700741030030b01c1081541c42c0010b0820380e51003e42030b20240140f0f1004080304070564039006218980c5039048000030308000c00b03c502400c102e52180c0740c80020a5005000d039038085c80c007900456004014401c0300251a40f9a070303128100f0342c02010505080c010082d01c160155024020a40059405c010310780c0b00c15004182d43e070440c904002d0050070307104003150391411503001c1c44e4100311584840d40a1504032200c801d030300034030b0410030b0020340f10761180340c2c0a01e800130318292340452200704691000c100c1510441060104c2007120f10700410500d402c0e0303050350b400708040003c500000c1c3d00140138160148101c1c0e0104900084d002401c003451412030340800821000810460416846000240c2c0b0030700c075061910075810b1000c0880c0e40c101d1140908014040d0f0f248445600c884c603e900740640759417203910501c103182c90340c0c00250640c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 462672428 1250 462671178 462671207
    0x6051804082a0d0f0509040c02071205030901171e040f02031516050f031303110607120e0d080408090a050d05150f011805040309050612150301150e07020f030307 71
    0x740360302628003a44100451a09130310207549480c10b2443c503400300710007460b0128003441036101c0c1c218001641d48003420f03503040c10f50055015603168040c05001400c0e80ba401e174441c9000b0380c0120100040e0800030301220301c2c6600c0040c40d5225039619484c056101010700d0001035498407402c240c91100000350aa034030321500b24071246014900240702c3c10b944601443c0042e044c40501840029000c00c00e1203a40540180245800f542841000c41b80e40d0420b4804d03110381c800100c08006c1c100700c0100e18083c02800b408400e0090408440d42c039801440c0440280c0000e0402c140040d2040150b40d52290310005004005c00c4a400303101c140c13401c1541c0c0d0800710b07102034003510800e00040c02c4076888a28981200c04811429072540491203001c0001c1800410032418040005004601c40d21504094640c08100d0300010047d03041c4200d04c1007900002d071159502c030b80c0c14108411480c00e03c84041108a4840044078001034858003016424034030f007845400080e1102004200103107a000150340040b20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 462673678 1250 462672428 462672433
    0x503030f06010e060a0206040b040314120915010302030a0f0203010f020d090b010608190e12030a0f0b030d0e0d0501020f0703020601090b06070c031e0c08010b0f0406051804082a 78
    0x192400c0c490b56000c1d0300b0b0b0780c45c0035030004070008010904580c0b0f0198020302c6850614000000c80340d141a241e0030000e85000c1500e0300c40c0c00c2011610042203011040070902c020907440350b15560009940d00840203005140c500949100c1085403825000224400b02c1d500c015074035160050481402052154416588100401d000041290003240c945004008040c86900d4400300b04158070007421106d0a046503074810031814000a503071010255000b03440310100800d070b403510346040300c0540e424203c61074465000a406541c2c11a00404da00d6010842502c81940f042e48504203a4028002c0b069000c031083c2002031801d04140e40490658140c400d43d860410544c00300074140b0400b4000c1c84801030040f19501810b1010a4904d03641c16041e03181100302c0c0b0f08101c0319503a01800e40e480d980c05500182c0d15800e003040d203440c010405c07a00c43c80d0252400c110451400c4006800385d415140322100040c000b03c0800c061094520032141000f007a00d00e00202500010308a200350b68041400e0312150 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 462674928 1250 462673678 462673697
    0x714030a050a12050705030f151903020316210c080304030812070201060501050f0721050d0608011a010c02060f030c03011403031801030b1305010f0602010b1008041205070503030f0601 81
    0xc2c00c440c480c0c05d000d01e1103951010b045a4500c00c0c0c2500d8124040d00b240c0d0303048203e003107141c0c0a0303461040b40c0a0228454045081e0030380f451041c945416000c0c0585141466091000d00c0078104400340140c09440030b90303002c1d0303041e0070f40e0030032462b054055006044a4000090b02006202d080c00c000c100c00042642c00d080c0c0d82c1d8400750102d00300c0340c0c0c50040074009a0100301400c1102c440001520070784d40503032001450740d941d04501c101d240c801d0500e010041040132800d40201c002134460040145050790080c49500300c3d81031000640400d101405041c002200d00ca40159203503482034501003518000b282c2d41e45d040001c10030405410910402010305989070240f08182400700a40f24a14a02c1c58041c5251540c40d0041d80940303041800981c00072007042c0d0b02e048a00c2c003070050354002e004002400074440d0422340c00a0a58003a0039109016026407100320280e01d40c0034904542c41368000c12405486002010200c1d420f21510384041c20a120200900c20700c24400f42020780100c1003600c1da68180b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 462676178 1250 462674928 462674957
    0x603050c030304080703110a2c06011b1713030302070810060605030a0e10090b090706170103110d0c06050307170c040303110c10110c1806060714030a050a 68
    0x101c0c8a01d000b01c031565004030308208009880c1201f100c0f250307280240324003010fa4072a04540380798911100446140303086140092811402d03500342c150013000030700c0c04454102000700201040e5500e100000c05582004107602c480b24041d0040c4c03502c442c0e4280c4940815962070800940d40d0721140648482801502c05008658640c0d10484044034020340300d4070b0842c0c1d1084074a10003000101c207000e016000e0b10a01d42d400e01400e1044a9109215070484001402c000d81501c0c40d1035060b8101c8818416061a4064031440789103843d41103951080b143d20200900c00081038256591842c001c2080c0316654002c50850b4001015512a5510342d4558039009083d4080581d584019030340c0c1d042000b8200b1041c804684075003900d074480b81c0800200c4411520090210321040c09a03d48680028405048031443c2c1d9000d001000d8400c0f0115031410703401500316002c4200320b102400140c071514002a08000304034400c00c039600607501c410309a0707494842843d4080c0855001640710400545048110b000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 462677428 1250 462676178 462676183
    0xd020f160509011211060a090906050f0306040f06240602010c0201050411060d15092027010e040608010e01110f091c05010207060c14030f04030f050714010603050c03 73
    0x100d490040010816900e00030700104400c50988083d40e00c01104800c40c5c9942e101ca10042040070455074640c0350081c40c00d11440c0c11601c9c0f41e0401842004160010b038030aa800082d203d801c150003903210b0f0030015051810b08010100c100b80318000042e0780041d40000001c1d81507230300480780c0640003031214081c90032089089a40866004040714540321400c001390030000040c007901030346200001b170350f15a000303468001040c5680c48503200c00e856040c80600c000015000c40d00c25114018228200700b039440611030604030351850034002d41d004040c050341c2d5a1103500b003110790101c00b9004000050310b40d0002e90282120341c0c9072040c40e40c2400040b1800c414150110b8205103503071980d86041416403401c01c002d0000704401501c1c0072101c941000041307002880100031007442a0b000240110740c600c009458000d54507041c4521702c00074010825101c0343d407141c859219915152801c0071062030501030341c1501511802401841d801100000251015409603055900900849803103049041c10140e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 462678678 1250 462677428 462677473
    0x20f120a08120f1b0d021309020406020106080328030612030809070807051302130b0412020f09040803060d2d0b010b040602100c17130209010f080a021309050d020f 72
    0x110f104041d04c001d21380c0d81d0522400b61000100d2240702510701031801c41004111049508081020781d130000e0304221980d024880d0000825540000e1428184008105c0c21602c503107012a11b10302c0e240c1080903004a1081d030141340941258503151001801e10304000304081021600c2d003607079104484001c161003100003800f0046070700c0200500040c1d285034100d1006034000c0d00403080382d562100703408119540d450020340041d12821744e641000400b907004001c0c10203506200039029200490500012072020701c2181d80c00322050b01c00107420303151072900b6581d0000d0b9180914402035100800d0341a1060020641c0c2e0703c1d030007080d002441e40d0725050385940071702c954442c10b40564444000e040014000e0f030041c40514001c4d0801c1150100040c840c120380d4003040315009204004100300c6c00440c80c042414601528015090505090070140c119588214110001e88074684103d0300d201c2801c155004007954546c0f05043d40d409401c41c0401a50f00e0031241c000d500b031409903140040942c07000c0d185c1c02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 462679928 1250 462678678 462678691
    0x203060a05090d0c050708060f070e090712090f0813050f120601051005120106030c18030503041a0d0c08010302180412051c0501060504080118050703020f120a08120f 73
    0x10f190a00c000391055600802021040351030f409014030000c0c4040041c041c01d80300703641801d0f00080c2460921401411030107130180041c880c50604080c00711084c0e108004500c02e0610600005840c1c545051a0424000e41000102804800100903940340140ca20300002c40b50f094038400c0c190300c5418100070415801424801c1103500a60042215190444804103207003442d0402c140303040900d80c58544110400d070003500100351140581403400c2c0c0c7c000821501e030fa02c07900a00c651542142d0b0350680b41d208a01c10403522000305400311035140c0045080f03c1c01e035024103c0c02c004c0c1e05030b8040c020700b0101c02444213070321603145058114450b0944002540c1b045901104d6510900d18503401034443d6002104402280300e50383d299160602811f109450103403900381c444d0f03600e992800c034841c4d0944032032441100304209180c1080000420024121083e20350407900c0620354414000400c40ca440c094502d07a6403840341d45e007000c0901180710010203a20564a0b10108655606505240c1c1310748240d406 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 462681178 1250 462679928 462679933
    0x10c050d0e0106031e03090b070303021b060708010611030f0d060305210405011d1008010321020319020c060f0a03060e07020a1104150e01050406090b01050d0c020109080a03090203060a0509 83
    0x5106128505c1da540002c2d51082c02c0200c2280e80f141402d80c21031700a8502200030950020301721140c22036180940484040210092505290014000b00400c6c01072240c6000d100071a102c2d2402c2d030809006803542c01410405407a11003002c0d07815200a0207480c4400e99660184210400303070f41300b40580c955130b07130440d903144146424501001180d080081c030020707682580080e1121461540c95880216071404180c0d280c070059419802e0034002c014030601661449078041e0488050150044265242078500406451785140d48070b0080e801c0000800740300c3d5025400289810f4540822806840349001c6968100706207a240e03001600102c1c0260713080700c00340c0d114608500020700108043e155a61002d0720100340c418608450360002e034510307000164640265001070009082901c00d060042070651024401e0640711030000c1d02c83c0c0b041907980850f568444003ea080d1038001d4005281311076019641980e10650b400c8002e00408006c4000ca100c0d008403408035000c7d50981c06801d0184084101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 462682428 1250 462681178 462681203
    0x20190c090e01060f1205010f06030501050a060803030717150901060207080d05040506120a1410140a0510260c1c0603080a0c050c1201150e0c03040609050c03010c050d0e010603 77
    0x103c07048039175100110303459903d60303000d010400c0580c000d8030700840c480c000125803800c003031501c901a0f4102c0d42003820301d81d0003441041031140e80403052105045900d04008069159203204074110000300003090307042468000000788541d8000b44001c2166208000e880324600f005104454921452044645c0400107000071204100318500c900e400c029254800641c0c0c45c2600088003040108550101d013080d030036602008a46241031400c940c658084a80340c498a05000001e81c50700c400b003890104115980961444028080402c034003003032100500c000d0343c2e1800d81001d4aa941c40080c0c0c0c03008a60050044008002c03542c0528020360740e00c520320a05201200d00d003103540c00801c0390250f90700e00c2070301d0855810f91111102c503912800c0100003c40d507008140c000540420041d0f00980b5640940b408010a944000e815281c0190303011001280103c6142850303454403c044098551651a10501c07010068215006151703140070118203000302c5c012403e2450880301184005400b002d181603 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 462683678 1250 462682428 462682439
    0xf010e0906070503160e03010e100609050405060703020a020307060624230c030409050c0d06120506010504020d020417070302120d080a020904020c0703240c20190c090e01060f 77
    0x81748414088502d1030044041c601180c002400c2d0756601a00d0f40e019001001c00d030155403030701d001e0807019010f00801400103040990350990f03190380003085e0004040d404074110350140d01c244119142c207074100d4001d100c8281c451703050b44c440b41e9000e28400034481400d2045007001d07006200071070700c00c02105a498036082c000c03010a022a8408805001603020402c0082080c0c20b0311301c2a64080d000a001150700d40d138400308040111901900015201c6448090b030000040001440381d0546d0720582d4007503210444a03490750041e010f1600484212440010711880d6040c00040a01c100c0c1d000700c0e1504d20b50303101c00c8403540d140e15900906800003004036002a10810b0b094008101c5080003800061901e6801000d05042c850307207400c11100703210035002022a4002c1105102c58908002a042101004100780030703081c03d03c260098801c98213400000e00f1181c1051000c503840302e0040f03041848421403454261060002c50103801c00462070005080b2069805100700019036164079400e45c142030414 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 462684928 1250 462683678 462683701
    0xc020a02011119050f121e0a0309060515040c08070f0c140708100e0303160e040f060b1c05090309012a030c05060708100506090303120f010e0906070503 67
    0x3440c100b681d4410480c8840c600501800d5000025001d10302800314201e010b0071540c10101e0401c01064216024442d040200b03a0b215051903040c030b5070398802070791500b07485000c4c0c1c0500b5090102500b4686804204204069440402c83e802101201c04101d41501e1200035211030f8010740343c0e44002240400c445000038055000b2040c0c941c0200111190300580301080c40c03500500760030100c4103070003142d42031070424030b903000f00c83c0060744500141d03007180307042891142d21114400083c41000f200454140c0540c884c1d5001000741007507200103000701034403030b110800799509c0551a5203000000c0b10510b8101203047c41a14010101140914542a0b0076001128403080c00504280c0c032688403000f03103100400901c141080c1030700c81c1e2078074499000030f0300741141484001001c2d541480303625010040228401c030f04040030384200302c0350765032103501070004285180144d03510b600783c10500c031050040c0303c49500f0404c4c0c100c0b40b11f108100d00c1592904036640d1220000e548c4c2d0000b040082c008101c090f642c0303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 462686178 1250 462684928 462684947
    0x90d090f150516030201060501090602280614090c0a1e09091505010f030201030f05091e0c03060c0301080f03071505060409240609090f02040207030e0a081b01030c020a0201 76
    0x1c1c54030509020303c402d070050020452a4048001d41c0d03660b101000a5604025000c000384414000b4010502c0c0da00302d81c4040301014101d8800c0445840380d0780341000b8003603014402c0c003c4074100b13510380ca15290b00020b594040e41249a8402e11880b000010000045184045001d135a200c05103c007619010f401d1002d8052050111041201d41d441c4030050341280c401c460003411006480c3d81854503500001d0101c132717107a85a8891090514080200c0d584000461510103107800c081121543c0410200c5414545e41c4108640d050254034248050310b08803402541c141ca0100d001e07261450b0983d04000d40c1ea108410300101a60558122825101c45981c04a40d11542c05040401d641720190380b02600c4400740301200c2c0a8150300b58100c04510054031403200600f9113803c4c100900d0005444170442c45080d900001c2c800c1d41c0001b020010144115051400e144d405844a00300c1502d4090190300c82d4002c1030400d104440c0103110402c19803013409410004c443c0f540160103100301b41d40044076034260 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 462687428 1250 462686178 462686219
    0xa0f021c02060711010e0a031a060a170307050709020a0c03031a040e0102071112100510050406080703050127081608030a060311030a030822060c08090d090f 69
    0x11250101001d602c0c0e000081080500ca8100500d6141d00c1c0400076207a1100561404e0283c1031441c4240002010103a02c100701d0f0440003c0b0360300c2035580900003555815240c203c19550108002c070307121703034401c000050f01d203c174468000e4400035510344100108078011404003000158602c00507001180c069070005113a000a002d80320b1308060000c000c03e0079500f2112000603540e600042041c240044030502c62040c00007201c000441c031526402c070503500d00c5415070004400381d0f5580030500602c3c9010a42c0d00130038002d1b01c01d2000a5507501c4003510341440c0d01c4280c4141d400c2026500d03100140301e9007540803101804d0445540c606580707540b2250b42000140f0ba0550401a41e943e01050380d00c07001d50321526a901e40458076608628050040070703502d9442c41d029034890341c0a40006600704c09680e80c801a80c0400901c5081a980100b071625500e09001d01071a240010401c00c0e5507200340ba103441a140041243e01c80313500550100d03050031070340c0f0034452100d0030014103004105540b840440e07540c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 462688678 1250 462687428 462687469
    0xc02132909270123150409020a06030b01030b030a03080145021c0e1219030507140304050a0b010b090d08030a020d18060b0d0515061513060905030a0f02 67
    0x3d410040c0d603503d080c20420a00c44c088081d0303003048505055200c1d2640312000c1503400b0700240c103140c0e02040e159440c9000e5081855120700c00403410382d10944c0003039a2500c00030225403040195040c044c000301800c1c040e030140c10b1620b015a2603030540c2808550200b02001004885407200d0743ca1102e5110f0b210410801615003c1040412829081c0041d010145a0b08000507503903000c1002c091400c0c460790403410000f03106010410a04d01a50100c60145030141004110381d51035950465116502120220701c0b40e4020040c041409000208900c8032841a1110346290341c9031b0504000500030090714542c003560a02c400d03000611204003454016204003000b5003800d16140300c413030588481c0341a114a4040a41116050180c0ca00440440d0b5105890b0b4043d1180540c45094a8100b0000f95030714000303405000c162540c9506000c0c401c01e40b200c144403612988810224034280c01c00e03106040028103c0900880d1030b190105004400c0c1c1c0d80400c075407602d00c1a541c240a020100020a0000c91 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 462689928 1250 462688678 462688691
    0x1b0b06040e030a110d0c0b04020d05030702090c0306040f09020306190b0d050c0a0506030105060304081809090a020103061715252a0b070c021329092701 67
    0x8032082000d445407803c541c07112101c800881d58080d1401c0c3c003041e000030400ca51100c0d0240071481e0038800b640c1158055511000c50704182c02c0452441c4200e007002900103102d8000c02c50005100401356016510448041c0110071214403220143c5402840c003945c9a000100030460014944c20304d1640710103841030128041c88001d000942d0000551f0094480c0e8000e084009200c1c50302000101c044c1500300c6031182194100310201d520760100401c003d00d11f20300050040138042007039407142862072004000314000c1c58547c0d00151070740007000c812070200b410300308081034501960044601100550004200f2040306103252903511402500103094444c0341c00c421b9400030040e2141141c1d08461b40c481c200e031000403444a0304000c03a456804901103604644010000f5104441c883d0403140302d1030813281156180c000035281032181d4010040d4217140940801d8581d224820414010818012000da0742c1c406809000781d210044076a5000c0d0005009131896040c9072825521300c11415400025a4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 462691178 1250 462689928 462689951
    0x11205070909060b1b031312060b0301020403060902180c2505030c0109210c2d0c05120a1a04050a140114010504020901080606091302030a0b030606011b0b0604 70
    0x11100140c04c0301180c990002024002c81d00d00703480311503840706503200641c40c007480040c0306460315026014a1040400c05458482403000d10b801c14044046c005000315035a80c0e80c0c0c81e01e0381c003d01c0c00f164100d0044010300901860b000d46000311a11510071042d680d8503040312a41074041d1a004100c3e41d58454500300007180200d1410006000c0042064000180d07100702c60514460400c035145130104d010301c0c464030309441d45034030940810b87c1650007101c5e860102c910020000390382000300072180402c2c00d1007550b0b10900105140b204101c0c4d10a0b00c640c0c8042c9110b042c01500d0b80e001a5010b089240c070152000c50494880c0405e50344540a0801e0398130132456a6100c2c8682401c40c078064125070344031754003266980c113001c0c074050040c0401c40b011407030010301d400042c00f009002018544a601701103520b000c41c1e207a8080f4001e140072011011980d0740741240b081c2008000b0002114000d208500c00185d255002d0740c041144014002c0b5154058002c0366950800c807100104565005520342c402c0300300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 462692428 1250 462691178 462691181
    0xc01030e150c0a111227060a0309120e0105091c0f0f0c0509091b04020c0708070305060708090709020d090f1a1f06120212040b040c08030405011205070909 68
    0x707a8107516003c1d41c400002600800814040301402955005041d0110001c103400301156030421b032818048907002001c01d00952840c0e840c415440d0052400200403884582c143d020380d20040c400c480c07601060b140707400c0c110f031008034603190640400c0040101240c2440d00d00340c0741900d410007284080c0c2d8403085d951903441c440c2c070b400000c446011048007800308005080c1455006448243d803604000d18100344000c1e500c03560398070000c2032410300a4000510351506d8045130100300c07a032001c403130255540b4050a50b407420075100640b100e011b03803000f0075100b9200c4d21031507004040034401031405038104154103000307500810f05000c503190344004030340c002080036114086007030041c2507081d51040e00b000c040300d0900004041c040e503007582c2500b002840b102031000809481d02da14019035082ca0b6103000d48c0081c0724030b1101d5000d40c1e040d88208000c21403152038035440b45100310710162103299030300102a600c1c056402610b02048410003806490100d503880140d01011625210b0300b180e43e034400400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 462693678 1250 462692428 462692431
    0x7060603030513091103040212070509190b04050606190201091709011d01050322020a090c1206030c12020d060c020708010e0708330f011503020a020c01030e15 70
    0x601003000443c0c043d4000b5201c3c00b0a42c01032001007018803201c5410190301a5500c00240000e104100f4a095070002d4030f010800d0038081d100141c00301c849401c2c080090418166001c000e00c0056017403002c3c00140341403601503c0d00920010307010f1410002840381070008407441a0700001150b40c2c80050002082902190310a20768444e07501540c5c0e01c940d0800101070b01c1c207501d03046131040c074054608042640d20400306c03640f00440021754080c0540e4034a03142013020304044041d43c00240030f000407030103440c6070f0312003d102041610340e00080c0c5200c00200007921600e2201420010a0120800c071101800080141e0644002c2003c2048032440d514002251008441c05006901a1a060010700b20074400c880300300d00007000408681c1e242540c111794454084040c2c0e0b044c0000507058a0300c0e140140c0e141d1034803070b51303480e4007206a141c80c001143d104c80c0244140810030700325030450600d0700d0103442150a208080e070b0252981c91140b4006501900c103081800419108a81c07101c1c0101c0841c5480d41d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 462694928 1250 462693678 462693683
    0x2061902030f220b070c050405060a0e0405100c0809070303080c1606050403091a04170c13090201080601031e0903120f021803010b1309080d0e030901030609060f1a07060603 76
    0x440342c41d888040503d60700c0038140c0040015840400c113030400304041c4100c0f0400c580040b030300403c0740e55542d408142010026848512902c2a200c180010400c0103d10700c4041207487c041005422501081280c040c181903803e00c00e103800c00341050012910814409900000c001c196614002903c0595603696074004015074501b6038a206106c20140c1c80943d0400810388521180303401d05441c41510400c0c8130394460040035411403100e00000001c2400503001860f4000c081300c0e2140101d07030030310000e04642d040c00c900080c82000000d040e580070380b040c1080862142950b481c01c004c0e030000c0034020030002c0c4041d0140140405419003440840c01440110b03a0801000341e00c0d105800200000360b002c03604224820f03414644d07502e5064550301d49201d66402c2641c4049000e0106060140661054100d540d481c83c6c101107110b00c110760000010000300400f070764104030710f9684030403010441d543c6008800705409100d070300708031000f0380c2c00e03c0311000c0b44a20081c52030071040c2ea858404540340740c0d108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 462696178 1250 462694928 462694957
    0xc05060406050333120a0602070515060427020a0806090d020601151e210b09070c020906010c1505100617070f03020f070506010320030a02061902030f 66
    0x4002c44d41c002d014540020f0b044080400c2c1406565004034004107442c0703001e0320300800400d445044926401c00c40e0500303094010714115030300c1000d42000c54a605003640016100e040e82000700c0c04505040c440d92506001d421b002560814607821500140d21030423805991040c03603010041208032041c40b000d4050395007440144182542d0b04030290034860144c0c4a0190f40d1108400c0a403119000304000d403144140c400205520842e40c54260b803951007403a4040710001c1040e007210600b030b24503488802e52000c1203880c00300f9561407500c101c511b030808110081d0400d00e0f003404220070b035000d640c007405190300c00d00400c40604c02d040405001c03658102c5640c10f10742c40040c020041c40340c000058a0101030840d40c0f42a15107410300c805000140c0070b00045081544c002451040822300d1402d44811030303888402e640c00c95079a0b0402032250b121040006244a00c02041558146000211045100c0d030140c007103810410b10742401d0385d1981d48580c10005500082050380280000070b0010283c4400031802c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 462697428 1250 462696178 462696181
    0x1302090a02031005060c10111c020918040f030305070c15141b12100909051f020901090519080d020a05120319090c09060902031803041d040c050604060503 68
    0xc2c0a0f20301d552201340103041c1040561650000884c18008215480e8404a103451342c03100c02214034440c9d513a0342841744440b0f41c60812008425002050b10180403204a17400c280200d443e51003508007550300a0408210078034050009000b504041e91005281c10907154070020b5803101d40818000381441070b000b40c2da40241001c0e0640200c9890b03084481c91180090100030302d0161040d40c82445400d9100e00202c0c000103800c0765418941c54081c01d405001407040301e04515050380d5a51111003170440712250a4025130030f10b4000e01c02d440301d00030305940b001c1030607107041d00b07000c03e04911420000003d01c521401061058003000000130b01e0045a00400d4450709031b040ca40d0401085003810504803200304140200b10003041911103003c03901c0713000024401c3c45403400623240b43c0c8a81c003698810707003086000203800704150f02841c03141054056180c0c482d4610001c176a100d101e80c2c007849220701c3e0041d0340303070f0f0b101d01c0303105080342d4403c0c891502240c2858849000801941003944100700281e400070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 462698678 1250 462697428 462697441
    0x20190606050604030b2505040e090a0c03110a0801150504050c09150c0f0d0e010f0c0b010915050a0f031b08011a1009030b070f05390a08121302090a0203 67
    0x12440c51180360340324126100d4501b440109244200d1082c07104504140010400c503040a000da20040d40c4d102410201e1190b507441c00c200070b00c00448140f4850609000c00042e9803c1c10700410a80004070544629110309100070000246406405952851000e2054801c280c0340c0d110000500400c210300c09440c1c261140c0150314090140100283c60b40050f000385541c5074100106a016103024200051178995102084a08111648028040e6100a03000092000542d40007009180d201b5940300101620b80c03062102c0d0002d0b80c0300700c098141d00c1400420104107040d602e4009a650343c1d01ca400d0b041e40d91045079094030480d111100d40640a000b14039660701d80b45030724104900e01401e00e0201c1c0703481c5031030b0440300c244010441c20600600340403030946244100b0486071014240c0500c580d03501070100224805042c01440c00b0b10640f0304610380c03414840c1c005020351306c0c0b42d4486641441e00005401c1c540504001818030040e00700c28100560060f82c4084031180f09040049005032689402c0f03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 462699928 1250 462698678 462698701
    0x10050705070f1a030c0d091103150c0d0c090906030c05010815130c0c05070f0801050903131203260405011d120901020c0607030c0320190606050604030b 67
    0x2030340000e00c07070b090325801000f0310905205916008808400b009403641d9072405405802d1041c1d450542d00c03540b070500741d41e0402c44004590b0190003825812104400b040018403840c0040c144c405500099082c0405024003929400030143c0c0e0003140741c1956410b644414050545a00d50400c49a54406200c203000e1543e001b00040d902166812550008080100100725000c41e45c2100149c043d03128002009406d000c1d02d0000861940102149c0796035680e01c00c070305400720050288112030750800011a407550000019200704c480b4070f08614508a00d00300031a1704c070442c800c004400f446070702d01042c01c3e0301c40b0b114840305041c0d88000040140e0b1500e441c15a08580414403e041055041080050010800140ca003110486124801d03615901200180d10700342e40200c503e64481c41c0000c0c01c80c01c040d8004400c5500503c292112044c9078000b07010400182d404082580003984510224107800c40c8452901d4000703801410000790064036140820314684c8940c0059032400f00580c10310240c50300c5c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 462701178 1250 462699928 462699943
    0x2010606021615080a1107080306152106130507050318070b0a030209120a03020a0b060f013219020f060c0708031e07030e010c08060102031c06030210050705 69
    0x1c040600481c00e14076821002c83d2140600020401201c0010f040c1c019140c0c40803840c085205101038484280f8038001a0b9984211100d60183c16041c03234010101d41014150b03043d050403004e4010f10707120041240c2c24240d0004043c664060350043d16205403e00510400e40102e0480c3c1e00c940daa031400c52048511180342c484282c0c0c02d940166420041031101c03809032060902c05140c0543e45592940000b0310b56029400901307407500424103440100342c0c000868400461003602d44a02d980e9482e0200a1040012070304980812500c6120b4003054210206550700f14002580070b0160710154441200c56420000050400400041520b80640d4040016440b41c00c0c45200a0080e0f02d0403000080250069003001403800342c0c08404213a400da8840b041c1d481001c0010902400c81c034040381c0c0100907044c160215440c0f9480c01c1d4040000741d2003076812a100c4d44041c1c000314900f000e800c4024004005500c84014803e5a84030044010f0303581d81342c1e54441d9a1150390301354490446050041c00d0008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 462702428 1250 462701178 462701203
    0x3160c06020c0316260d030b01090b120a091a010e0912040f030809031f0f0c02030702030d08061915171006050a0c0f0b090609030c070e040c0302100201060602 70
    0x4022811300c03024450104290b40c5410054440d01844402058420000c40000c100d0b50040060112401d54568001003e8840c2603881c0300740d50780e603402d5000242c40b4208141c0b00304104140019038482c03c9030400141c0c2403048558010300754aa254842e0754a00a0f000b6820003214401805400042040001003000507071034680c4c07402d0300e0007012100d03641c45840002c0c40b404010625030724950b01800098188510174a080b121103034061404d0f4018403a29207101c200d140703040c0112018070701c000156a00c89a001e4010a05141e25040940781980014a00759015966880981017035081641c00700090a03000d4a00100000a000144c299076660410f4800b52103507004000203400c02e014802c04441090901e1565402d020000300e43c00c40800714082c0504000e8031203030080100c401860b601c40c42d803580c10350715141c545160300c9450f03100d281d880885541c490281444201d803c8604035810510504510344a283e4035800700d91441158240d6202607503540100b0000340d82c040c4800482010b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 462703678 1250 462702428 462702433
    0xc0504060804020f06041d070306060306290c03070f020f0f03060412090e090c0f03061302130204081204090e0c130b21010b130e030403030503040503160c06020c03 72
    0x1410940300405031040204060701c980488020100e01c0d03250305003141d01900304500d50400307580a46008208010058428200107880c0c0000091035a104e840f691050740c6a94115400300800c07010b081c0701c852041340490703450b040200108029510108014050540301d07083d00d1082810500410480001046516003e04852082c940141d90040307203266001d0f6221200c00709003480c2140440c3c410f0071a801413003d21302800d05004100700c1c00a0400c221503c00c1b9000980e000c9500e0916407201804c0d503007000c6983d0981001d5006181c01181c1c0f4a0300e0382c081c0001410300707641e00a010710300365440000c0d00000200003420f010b403140b5401418100f1403c40028800085182c0206042d5014140310035203450365140f040c0030a0703444500c003410350454ad800905044a0300380c4a42d0081c40b2418600e441084035000e0442480058041e480c040c3d02d101e400ba5042910f56202543c480d44000c100711128002003001c88800d0402421499089000f0a8444542424200301070314082c81c80c1c000e54440c0c6d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 462704928 1250 462703678 462703687
    0x62706030c120c03020307120204050a0b031e0c0405071e050702010f0806010c050f06010819020303041a070605101d0f0103140c0d140118031416060203090604060c05 73
    0x101c0e50400c00088556003210600d4000701070400c000300c0b90340c0d500001e41c1400742401c001b41b40880c0c4052404a24022a0104001e03100c40c20304a040382c030040155900b50304646004100000840c00481d4041c031120300783c034920182e90000034201d800403240d14010614030b511808440c1e103603002860210085043c1249000d100c0e0700041d2000020040740410450340000052099214842c10100c25600004951a8840398201151941d40c2406440c0a80c17055488204030300154448909250781c000d40a035107030604210b20580c2415007403070820f0b26004208140f400007807041c4a03c41c0701d00140450090082d05199102c40d414020f00d41120300c4020340800d100f1442481009a4112640311203501c50010f442d12565080900c4442203e42c01080f1074080002c0c0014211007002c034890f001d008100b0403100300882c5410340510b200260028440b05040c0d002c4403007a100800e00304003401c11001d840703246959024160380c8101c909920b02d8001d8818042000058050205490880d00340107003003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 462706178 1250 462704928 462704933
    0x1e0f021005130611120c180d030c020108070201060b0319060b1c060603090209061002210d050601180e0714070302100627090809030d0c050c04110a120f06270603 71
    0x34140040c211016440c00058221f02159103081e2045950b400608144452141818090140e00344035006a0100b140000040c07840380c03040c800c030703002d94283c0e443c01c5003141c4440741e190b1061810b03061301011107540c42d4008a803a103140c0b4040c11203030410041034800c1e8000002da42007617403500e0344a40f040c0341c10000c4100c01a500c0000c4a54007241c01c1d91900c40341d66103003008a151282016060040c100a0302c48548c1e601c00b000000c004180403c0c000740015100da000445910109200b152104206a0810f0008280c06145541c210f8120310b03281c0188424009c9a24a41d0b20125040707025030706c15410384003249040d00414008100440b1205002d100700c042c440030700701400840b03c15442e981e00c8000c0402c400503040d940d00c810054229000320040c0074019040e004400b409036424030406030100b2082c5028060142c034080c61380c0050342400c01016040d5a0001900310100f510303a00e0b4440018442d040e44550001412003024003440c2c1c0307520008043c410280c1c9022590140d0034600240f01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 462707428 1250 462706178 462706207
    0x6090203070905060717210c0304021804030c08030a0f0b03160506071713030320031e0c0f0d091a0703050901260103060b011e0f021005130611 63
    0x703d4000340c035031135914501443e10700a107050148a101030a100414461400d002004500d5802035541e17104070701703d8543c1601100700f400304607002540500d2040100000032000740f07441d0b400c2442411301030340a00f5070b640c034540c00e42c02c112800030b0754564031a00e2040c0d040312401006250f0001760041e0120b030401ea440306512580502400c0d000d294005044030400c400145807687c544100a14185c07145901a9000d82181040c4402c4d40061103882d00c0302c1c03404030030402c21703039034139100c0c00003940381040354070901403102d8000ca12540500d2043c88640c204910911400442c00f070490094120603030794082c050001d0155400001c0921014407035082e0b6410fa64080f14803440e054140f668950b488000121418115609101040105416400c5d190491120400d0699201e080240040140b041c0110b861141101243c07000d0000d103500004018020403014a14015a10545904109080c40301040d21000d4401c82105410701800d5020301002c1c2c41495465030360f0340c1e802403030040c80384401c88 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 462708678 1250 462707428 462707447
    0x6094d0403050622030c080a0e031b01032301030f02010c1a04060e03040b03180109080a0507050d140d0c020f010c180501081018020d050106050706050f01050d0807020f220609020307 80
    0x920f00c1400242320501103004880b0f198084100900302e0314a0403100d900030134100c0e06600f040340860300304ec044450b41012102d1f40070202e0100c0d115401941c3c61500d0f607120610081d142a4184003118220b1404115849640a060361100c001f1840b282070514080040315071020032060b5a030001d02003030010445010407a900510003000220301150011039480c010400e901c8010150320f400100d5141c2030b904003024050407030260040e641d40e251000e1060701c99102081403d000c500c030805c2211407009660f4403004580750240704440c0710000101d8135500b111103032400c01020801c4580c0146c3e441e50010b0070003014160070318200c491401d140705020301811450280340c40c403011480151200c901a603055412280c0018001d000c2540d5803d805001540900c90684a0ba030809000850340445428040d0480e4005000c00403100200d13111650710b03401030f2400700c0c0e000d4000d50040c80b1a5403010608810711220072002400b00c100c00c5000d000301d0b01e41ea8400603203e0300600c20080066040800729 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 462709928 1250 462708678 462708683
    0x7060f05090904020a0e10031101050f09011b020604091401080c01021e0f0709050702010e0f032502030304150215011401080a0212090106094d0403050622030c 70
    0x200b6958855100044000300340783c100000d000c00010030000d200741031588520849000d1860340e8400c14a09004460500c1203101c050281042000f05916952088441c0e0f4101e070008002c0148010342580019081d40c01680b003a040c058036204485100c1c0c0c0640c07a030a0051080c0320062001108090010b5100d4204511140200040452148048000740010402c50713000d10b0541d20204c0c2c0350340c1c10800500701907804400642c80c3c000e402d034105800081d81c0000014200003542410381c006210f6880e17681101b02040c0805030700e404200183c404002820140c0a820304d815140104100c001f8030b040c602031550780780b11a4030801081210003800549030480c50a18100c100c0b42d030762400c40f40c00383c0718040742404403000c0742041280304141980540b094420114060003c03120008030107400c0781032003a5080210300714100e80110a1420b40e00010f001f511130500e0303104003410004d5014143c000d580305480e1034114104000b0f071500001e015101090202d202d2501d0b968480d100100304d40c4406000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 462711178 1250 462709928 462709939
    0x10021c020313050f010c0306170601031112070803070b0705121506190908070f0b04090e01060806100608011719020105130b121e071d060f0c07060f0509 67
    0x12484032103140d80c0c02110709402004490900013012a0103000f028010500c0700024500725000c50715440c5020320018800e206c0c002002d2076400d603100c1e1303000d90b1048000c0d00e81c040784071000c04011010501c4020020980c01c1c001d140c880e181da041891302c00704000c207030303100300700d030401420785038401d0001031a401042e134100d40c4a03291000c00200718203105030035021703000c0716640040c000c41075030064200040d01c2c00c0000303860605a0361020011220960300072128081c1c000c2c0b00910035070741d15600200b88007109200100e4210358030800e060034103105079004c0d41480c40c5040240050358004a041d8010512282e102c4050611407031415103801ca0316810048041c1c224200c40c0c1568800c2d000e88030b281880c48168040180c2d988600c4800d9442604003140c038245010004040001000e05071800008811007201148c0e604001140d03508806140c20808443c2045449007079194200035201a26850107020350350140000722a01d0040503030311042c1003110311420403e0040e802001d0380d0b114071040e40d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 462712428 1250 462711178 462711181
    0x71b03030903020a0f0602031e070c02041a1503100503030a05030a050613150602100c02060402090c0d1103010918051209060c030d0c0906020606180c1c0b0310021c0203 74
    0x40480c03c00304c40910242c5440c02c403d9000050000310f900079402801700e031032859071480f040d0f0750540c801c44040710b241e00410b1b4040f110001506060300601116440802082c1c41c180031040020180039211010152461002c402c006c043c2804500401c054901140214101500420014218400108081d480700e44650100e0030544420603001720814a501d0103004e0700c00c04030222041c0c1c070350f2481900d00500c03da4240c0300080c415445110130a910f160b000d0150750b034494091001250014020a080303000410107410700c46031f070344030b4442c4580e261102590b880d45843c10b01019180c9090304003100e00c29044039103001400001d100c01305550760070710303550f2120300c0744d000035100d80101c160380102c81c000041d406407401e140341c0c00f02d40188230507160030029035280c0c801203075911405c0352440d4010302c0350a50340601c10181880e01d50b01100e0308904510701420301400001320003e00200b0081540c42e10b035103215902d03050023011040180c4040440c00c040c8603140c1549881a58002e803450243d0020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 462713678 1250 462712428 462712433
    0xb03190c020307052a01050301050f0405040812040c06090504140f06060f18190b0f0d060510020d030c02030a020601030f080c06040c0e0a0b0609092503050f071b030309 74
    0x1040d034903210f40184c142c409008100c00e0304c004101c00043d03900c1c004003c2c8511083c3c558000e030f040d64142c0718050812485c6c007806009002c024200070344161280403061204a44110343c4da48003521903482003412444c0c2030715003031011b00010101d404c85449207040040e504044220b84c2945584801e24502d100150345440b400b03c2c1003486901710307401c0d40060001e0607282c5501012100b040c030040940f015501196100a210a0040d05008030810380104001900c0e0000301b0402808100714025000900f5980c3d60000552440303020015001580101c07a60904041d0540f0a40f540d00ca05400a945060042c00c0020f4650701c05000080c0340c401d40d0035415050041040550b22900c08440849159060030b04054035600002c4c4108140101a40001203c03504a8011400d103104040c00040c00c050f200c104004107407400a0084418031005403400c4402c0c505800c0a04c000c1c28240c5000416007450a000002c1c800001c05800601c4800b1280c0d107a10400208420a19605490001001c428a2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 462714928 1250 462713678 462713683
    0x170a12050d02040305030423130911060c0d18050f010c050a05060f150d030503010b0702130c05180a1d040507091a01180308030a020d0905030f090a0b03190c02 70
    0x140c1d849111032021902104105000008100b41c49907007890b44880d045c4540740b9440c06c0b00e0100840e8000d01e810b8402850100720b038000100306031040707910324003881200000c04d070390b600605c002d9a080c2d842002c2d1003503490f0f007011940112801e810108201c00342800003003190b451141c40041d0400c0354169401b014450306000c40906140d024050f00c0241c2000202c0d22040181650b8440000e00b080c8d81580e00d525003401c10b84030250b8146c0f1038600310f0780b0b840c00c050f249030800382c026a003058281e8641031020b90240700309210200c223600e07126110000c92040c40b403210041e200084c020180c2d000c1c18072851005c0c85004020b01d1001d10f8200d00e03036442d8030300301d420a00c140c3d0110300c0302401c110340e1140300080e0451522511a0aa0792400030120f414070322400c480140c4070140c055501007010a0502059400400c5c0781c0490f04030200304500240da41c5031440d4440c01a81c0e4080c20041920b09480c07503e00051801841002e00450860502c01e0480c80d200e810607441d0319a0355954015010840c0c003e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 462716178 1250 462714928 462714937
    0x507080108300703020a0c0f0e06040b120a0c090b06040e0f090f0d02100c02030313021c1a0610020307200a030803040605070206010522020a0c080d1401170a1205 71
    0x444102d251901c1a03482c020b503640a0078141141c5a10520001059048841a5400864a080703904403c40d8803910140401001070004503038000c419102213645075a800c01c0f10035102e5110f00e4007000020320f40306c4e0742c40c1210441d41e05941f10b070004110400c00c3c5060010260f410031001c4400850301e0302c501d0000c5160190200650140b80200f01003441000c1e000302d803c4110b5a40e24500b0301c208101c0d484101d840b44001c881c00f01c1e98090f0030075150301609000007080e60825541001c020032040f02d44443c2006000c400c501040118800304211143c1400304c118800001180000e41c01c0c02c82a541b10b0380e06401c030340c840c000c0442c01181b0035040da94481391410011500801030f66035900302800d000c0080c000455541d400b40c0300300030000602e801c0c1500d4401c001d0400c014190b108110502030b00029520194020042060205d9501d01041c54140189020120b00ca00015007100c20300400f035030104164005642c0e503207048404201901d010504480f0301d40c0c0001c14000c1a4401031080c1c446010f03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 462717428 1250 462716178 462716263
    0x906100c140703021003050412210e0610091b0806030106050d0b0601030b030f0304030f0602090a18050a0b0114030601090b0a020a050f0a0503190302090418060507080108 75
    0x755240031001c1854041400750660740281c0d4026024095440141d00786e0303105450040400603449071401040c0d20070070182901c4079480000240c0285404c03829400e5030014000b0501e00e41066040c01510440b190020008002c2d0709420f001d03c004041000503810388000c0721000340300c0464001070309076400b0b40c880000f801e0300905011035200c2509142070201c000710f030001c0c0403030318203506040c0d136240004180c0d2004503035074001d602e0141950341d801d42c03005200004899958092104110036540c1c004a203020340400c2c40103104030546144031f182130380d40180800010311711b0401e0610441c5d91041400820f00b15111072260303203460740e9004071000b0303100d68064503c00c5e101044400c4007681c0450039090b0140a9821121040d141910503521020000e00c0202503074020440c4a0008010752559942640d5608005003400b085602040c240d13600001d0b00a00350070f0740890b48040006510865402c0461071411027040d41c104000c03944d407145030084403510000b007960380084105039203801c80511030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 462718678 1250 462717428 462717443
    0xd0506161413050108100e0703091524091104050609030a0b15040f0216020d0201180b0a09060e0f0f0a0513020c010c0206090c0904082107090605090906100c 69
    0x780224285440d800b481c05414001090140802c40111a030301e5043c1c1074070035018990000d034484410580042c414058101d440c540c0304026003144034103500c520514101403040c00303007007003260400d480e00810300d680000540501e0103042d030250f40514019103040d03401c1a03c110395900c0c900c0002914140314000000d06d801c0b40032081003034070045040c1a034951141660180650820320318030b101a4041d8001c0c4140421406d0480d102504c2d288541001c0c1c140103060110f00d4810061552410380395941114003486000100003206036030200c0d8040081c00d580c03034080c1e49120200d00003045503c500f00481c2c0301d8000c2c5c4000440d640c1e07524007040d000b084010b1a0450701e00d4100400e1000e900540301a407429460b0041852040703001250340c0e4842c0043d40060030380c0c64000d00412032040000340069031176140070700244486c074020105030011642a4142c1841c00d02d0715440c0180b4190340364000c0410040103102c140070f1612a0546180c000200b200e001d090603096000071110343c000c420000c3c0110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 462719928 1250 462718678 462718687
    0x16020607080f28060602070609031a042d110109050f130b1306080f031612210e06010b1c05060303160f110a0b0304020105070516080d0e0d05061614 65
    0xf1940b2103811150380d6000e4840040e039424043ea494a000c0c40b0203400052006103201103000c4007101160300a10807031000800307041d10703400310f41005a0042051301c1d60211400400521249000348021541d0900e4040d103102d042c40003181e2101580c83c405c9000740344a00b0b5002c2c851031207800c0380410050141040816240305c0c607110001d0b0685e44200c2c0c401d030240300c0c0d00b400001000320442e25160005220f00840381c8030b50781c07400c1c01c14a00094841c10402001140d83d011040525442041002003401055580711610364600300071040e03028084400003000503010010008403800c092a403460f20008040d0f5510300803d0552041500380076810440e8880e0804100722114100d460600a680e400d90030b0b400142880154131a90060b81031800c0c003800041c00541c0b0410017081240e1085054944160004c0c003103140321101500480115040340134441d40a9034041c003827800049084500300e04841041c3c548545407217016001c4d0b074812030304401816030203001c2d0b042404030503440c110791541c6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 462721178 1250 462719928 462720001
    0x5030c0f0d2622080604020d0302031303060204030204051608070e0301060317070c06050307020307062d0506100206060a050d170c07170f1510080708010516020607080f 74
    0x4561203091095034103000c10684401c222800b8440703800380d1304081c004142949842d007c0003070340c0f41151021000c52108100440100410003042d40041d48a840c0141c0c440c1c0c21441048203486d00107103103500020400b04002d0340c10f0340c00f48100b0740100340c078200b40d2614030380680401d0240829800c00fa01442c0003d12002484044d030006240c15400361620100301e9440f61400c42c0d140c401520184010380c8140206c101041d5540d01002d205c4402c0c8284407a070440040e407050f003041c601c49150040964503403c02c12a403c0004103825291180d20243c041d0380351040c0002c0115815002d0795004802c02c400c000100400801801170100c08070348a40d03262005032002d913540b2983c034000c0d02403039004409a41c0600c2000603c0c050510002000f8144c0c03280240880d44030400c1c001e114420090803288009910745090200748042c01c1c0002c008140c40c503082650381c0c1c1c1041104401e0085500490801a103180c2c0580c00d01d0b0000c85180340c84a064590b001170340820210015000348910061a24416 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 462722428 1250 462721178 462721253
    0xb0402070c12030201050709060f080a141609120803130503070215040807050603010305100b03160605040519030b0f04050c120a0c17030405090a091208040c05030c0f0d 74
    0x8000c3e10940c000c1c803440d56102400c0340c4100d20740c800e01010401042003011028000c19000c2c0d0301468000d80050941c440c0d41081001d00000c0c2ca0015480b04440d41c2e950311164001814400b034580320044900da0007803035641480e50711008208540003905034030f03250200101401110f244680042c1802c289120403017030051958410700c15070a0501c00c132400020141024800e41741226001009405a103034a017a00780041d0401e0710340ba43e0316025040740ca407400800e071400e100141c500340e40c0f0f00b81c41d41d0401c01030091840c0c1880e1030048007000d501c81080043d84503060580d0243d011481090b203501c4074580030b40351005401c42580e0051040801c01000394001600e08031030390040080d50040d954503904080030f0803d1045110407031b001000244420309050021942185000c2000281034901e07861780c13154404840800703400641e4810a000502203400001800340400b10003510046542c01c0000f0b81d5440765070f88450113600d003004c10805003c0c0b01d04811145008030903031201101e00c070300d030000c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 462723678 1250 462722428 462722459
    0x80a1b030b1e09280501060510051e090307151b1a06011707030b0105161a01081635011e05041e08070c06021f140403030b0402070c 58
    0x81580b8040002d14441d00000c403a030548500c4201e1300e840308802c881d2203040d50304911040d2030540d01d85600180940303900002004580301d079941c072074071351302103042040307190340c050b02042e440050a00c81515265404074411003120381c0c0810f0031107860440d0505a03100c413100c550071003044810120980030b00801d00041c19038000141100308a5a80e07040054800c40c034001602c3da840285040003d000c14081c0e80200303902d0805061280c00c1580c02203c01c40030b07000301c0070101e8094800d104e04004415009240d140500200030150849030448030020082180c94071440c603501d450911b81018040b51205081221416100c0006c01d00070781c8440342e030103080907a80c1c190b464202a8280307802c042962045d180a194000c0c3c007811500210106925855201ca1040d02c0180c41040140001120154072034002c18898001d0800c90440000340004c4404011100280134101184400c0c400c4024161690240d450f00300001c0740c2c0303180c40104000b4000c0000060141142110100340f415078840c00e02c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 462724928 1250 462723678 462723721
    0xe0109050301050f010b030c0405211e15191505090a09021c02040b032a061206040c03060512010207060b0301020f03040303091e11041401080a1b030b 66
    0x2010115030303038000d01d4202c500807034460101450000050201100110080d80c10088500d4a642000e0303c480001e003190749564075814000f08891070651503408141b006401486c071542d2214251081c14201c00c0c0c889040006008460340c414000507006030920801d580d15900140d020040581703001c54850449903c0e00425208500d44000030318654028001c1e524550350241c4003a00e12489511040889021600c04076442502c5000c0030305075441c1005400d500710704400d504281e1001380c1c03603a52075000c0ca40248500500c01002191113040306090300c1c0f40c0012007030790700044400d140c9000b20000d006a802640e0710640140030022142030540113000d009002e03550400034480c40b00f0170103080b88184040441ca0300c1007030000601003070090380203190441c040d146012101d4032a43c0c028003540e009030000c0310700d003904180d01c1c2e400307041612030761001640c01c0220100c1941080c03400c65595205003c01001700c85202100a1846440d82201d002541c0c0510a1107090034400009629050240d001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 462726178 1250 462724928 462724937
    0x1020a0e100c020d060212090a0b010b0a0e0f0d12020106060810030b01030b0c070f061a0a03021f090308030a0b10020c060708090f1003020310080105011404150906060e01 75
    0x2008036529040540e1100c404041e111040c0700d414681c00d018411141e40c8003520740704d50034070084000300c10840110b88030b2008080035058005641c03134540d19000060300b0010142d402844400340281d046420f21241030310403280942c5442c441e50004158600c00b00e0020700c06c1c01500001d130011380d01500800e0654840e619000072030b5440100421038250ba0b07200141c0ba103000007004201190410a080c0d402070480007205e860410310f500c480c542e40c4115001103441c9a980c050449a01d040c80d901418080800c45408696501d9900007800003064154031842c4200d0300049405440c0c000c8041d40000e40e844002c2e44d469151501c2c500e0014649000900d006840c041003500e9054030115055900100c000c0c016801c0640d0340c0c485030002e8100000c1c5903000060309443c4006a500c962100074a5141603030003581e240750021740942d01800d140d001c00381d240e05110041c803020014080d81c0c0420790041d5000205144518409081005150f100180080c5401804900070361300caa5801013050003a01d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 462727428 1250 462726178 462726197
    0xc0301210f120f1701211a10090510030b09030d0504060b010206010b0c071401090503030c0106030204110918040f0b0403090501020105151e030c040204180e010e030f07020d1401020a 80
    0x1029245902d80340811400105114014080390030320580002090030140c483c10307140d0005a64244480a000030b49140c992410001c0203230b80e000b054202030180960034018819403c00041c207016541e0513001c014a81000c980000e029a44104241d91900e50010401d00403070070030342002402041414106030041c02213000204040201e54212210042480c6c01450686e01d0314a5800c00d00340a100e100e4100801d2200000e4241e60070000f034803002207080000102075145204010480364030720314a02111406124000081e600c0c40c112401022072008808110350340e901c0c6c4460312401280c402003815085000340001d166000500100707030761082c4c008029646034144005041205083c9540d40201c221000600c440421103045044a101600302c4125582d0b14000409a0304190802e25004413000c1610a40d4085130180c0910022182c0c0200a56441c811010b602d0b03109402031141040f00028a0354115201c40c00001441600505d48820101004454502035840950b03071000244881c04c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 462728678 1250 462727428 462727457
    0x9150806040c1e090504240b0a060c0609080301170c0130060315150504020c0307080c070302040f0f0507030b06191205040302070602060f0c0301210f12 67
    0x1541030700854000044100d414644007048a01008030081c03403c1040740c404000658450364080c40380100d20400c0256042e00f2090780118541c201b004200c0801c07030030003800848903203441c4030400c15100ba5242040496100c0c0c1010b002138065030100410030307400000009048440c008010500d9643d040a80b0344086003040111220480403021a040202902090a421703205a40203130356800305860100f1101c0d500d1b22540c1039011624420030310346484401c054101400f6030f1036a0041e2400b140d0440c245030003001c40701e5482c01180002031020600059408400b0010011040250307070080080c00040b4158600304041c010303032050410b4190518000c036415034041e008407040c01001808140c10400460f60440c0400b0f2803041400038080c401040442901c800e0017014415030094000b003107040e1811200a24000000f07020038a107501b50030512641000000840f8110746c186070079206090000c1c06803000240e2802c80007050517680c0d0042c00c0811400701d0010b107801c401074465440800744003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 462729928 1250 462728678 462728683
    0x70603020705070b0408030f071406011517010806060909100204030f060f090f0611070b09030301030212071202060f120a0902040b100e0405090c0d050102030901181a04030216091508 80
    0xd0050300c1b00c0e9007040c04500c21000c1c00d0340c0503001c414002d100708010098180d4075641808001e03080400d40079941d6941c24286038220520381c40c002031401a50000750b01d01184603840302c0300985214440c51107800418818801004100010342003c0c808542d51566454140070b50130910f00200c0c2c000c1c4c18100c3c5d0758203a84c024401c1c05000303600080d400010303004960b14031004142e41415012280401d0050070045072540146034460048000150b90f2541180104500e100785262105610780c05203405018241544244009003941a68081d032510703060041d11505001e900300090b11030740d440f4200985503c16411102c102402a5801c02058403140240705008488450300f03008109070b0100c0e080c45090591110768804403075402e80b03182d15032000c00680c1402001d0710a4640c0d84d008002d20a042d01c0a110b1840800c054a01c1e040e8001e8103a600c168882101e0640690072030081d000040a01d40203100f01c44140c01d000e4141490a5110b000000003882e00150001007031441c00004035026500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 462731178 1250 462729928 462729937
    0x7090e03031302130218150c0703030c02060421121b08030406060306020f07060c09120303091a0c1e0a080f07030e06180606030d1d01050705070603020705070b 70
    0x29000e145182c2c0c0322030700d075101d0b124854000c9030452a000009a0144d00e03d00c040c01031000503030300b80810502a80c0c02c100c4c0c0c041205282c201c207800d042010301504500020b0714411207501d4100119482d00350b000240280c0160b0b0321000c0000340b41844845d54030191450305a60501c20903401000c94110f0700225240d100901000c51071180d0170482c0c0012404160103035611034402c0c00007282803520395407030f40280c4e005540c06c4e0035183c4010030174004105150080c3d8000340c08600d4030001c2035241c9107408102031070101010781850750f070302075000c184842c20079136800e1104240c600c5a1542444040070065038401c12245d458110b840300d540c201358901c10200c07100d2140036a250407594840000401034094050022001d01d661510014031801c07081c02818414010b00301640a428800a903445c10039100426480c8250003402070400c81540182c110314188a05001801145100740c4c010380e820310a8250107002c034031a41100160180e4160010314045114000382d0f15202e50b100c01c150101c0c0603 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 462732428 1250 462731178 462731201
    0x8240114040b1c2906060a0e1e010f03020c0705040c09030b0411090106082514030906100503070f152d03110c0a0618050d080105030709 60
    0x104010410114855060428800001c0c00040c19202100010700302d001e03e04402d452001042c0400802c0c490450b60a002071806800d49030700903510034040d03071201907000302a90700c200b00204d0880c3c5424400c4407020312010700039200407003041586000d0b000d00200300204600090207860301c00c000038403d00903107030b1403100c24004109103404d003800c1001a000c2d0747d00795004c10424401c000b020821041c0014010707800740e28030003031a245000503c0000041600040e06218140f001e0000121894480c00401a4060814260302c101c00301c084482c202031445c40071220a02006004204102003200d601074082c00042c40f00e0341da0768105058481450344a4000c0d001d08003401004046010010045240080d107802c4d1290741500c0700751828950b04540c040901964240d46600740c80d01031082620b500d80e04032841e810714140c400a19170303c03541904004c01c0d55031a40110700d42801496078400314a98090700b92446880c2d100c5004081107400d101c1d151103445407140c001407415161060020108 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 462733678 1250 462732428 462732493
    0x150909010509040602070804090203071206030305070303110c100509060f0621030d06060f121806022d0c0c091006050a021c050d06050603060607030f0314040c08 71
    0xe18103410011602c6000308291207554081209038001203401c1d000b08040c2c2404240143c40b82849840201422811001c1740301051414070240f010030341101c1503402c015458034002c1021000c01034259014000d000074003040d81314901030440c4455840d041144201d06d42c20803154241e6481c54040714803d0160f03105a0008522204550500410389070702000c42c51070300449260180d10107809044920991190002803001c501903000e07903030300404c03d41c00480d1500003803140308990b0b403182125079001c201c02803540d540001c0306e200900d40c100150540f50704001802401c0c0036011140300300c0341e1003c00c6a440b54014202d204055280514071240100c2604007080c41060401c00295080d41c4031032581011761080c0c001d40100d011074036030081c400e84c995a803481c0d217400700d81200c0e8054170000e41103103219250900030000b050302c55000307660000da0107241820f9811b9a440c41540100548a0441042d21404081000b40700180342d80c40220340400c0200c554101ca41d00c0f15000d84a000043c288101c2c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 462734928 1250 462733678 462733681
    0x3070303050a180e04080307020d0e0f060901030b0603040309240f050c0a02030a050708010c0c1208070504093612031a030703110a05120a06020708120a0605150909 72
    0x102d2040f186039001c202183c42842100362110a81c034455501105c0458490000001f00a0096414804100d0295050a280040d0180c540024584110f030007040c9000d0720002c20b4601480e8402d401107000d8500c058055507680c2010f0030002c00b803034694000c00f0f2035030000210202000d900401103203900f440668495020102c08582126264411200d021184c41030940e03203000351b80c0a0180c0c21040e0300c603400a001c40340c40c00c0310761070a54004101090600c0f4510040c030f0301180b0051b051b104030000711f11704680e02c0d40c0c0e410000d407898042c80d000502c030b42d403412300c01c45003508088440c0d03440230100c44054054980e41d449004000f038001032000380100c115000000d40c0701e000360402c00428004001390a061421400440c1c5860801d600c10382d21603141d1a04c0b9126070603e0305107000580790541c6c8103441c4201401c00d003507032030304c2030480200025030015108052140c414240d40705440300009101090900b00800310143c03096015007480b800b051030303c420401e5900c804844403c04082d0010509 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 462736178 1250 462734928 462734947
    0x403020307021c0204050f0601020d020d020a121e0e090c0a0c120908030c0601140105030c0f180604032405090c06090d08040e010e0a05010b03240a0f03060b0307030305 74
    0x5100c280c001c40852591006079003005075250b0051b00d105032410030078a005c40c60410002858444041d2424056410800c09041c3c0d4036804200e100c2070035003019400400c5180741070201e0303641202071032139a454400e2240e0b881d0515402860302c03100c40e8044485d001c0760380300d074408020b143c464641c3c12004110340c6c50740200001c41000303085c10352008900305640341c10f40d1500c1103807e40c2d1103280035000355040080188030500b5100c02c082e020100030300c1e00300e0952070000701114052283d03011246030800081030020b201b1340600d41c4100380e82005401140c130f881c4d8030b01c3c00d10794074040688a02c0c0d8103c0703030000f484c500c011280b18041c41001020700030000c51750000c0901c2000d038441480c20b5000000306c3d20080106048600510007000c2e900e610050b0f541c5000201542440003030010702c1d01030700300300c01086a04080000d40382c02040c8518401094030800080fa0144030304450f07015003040400b03000003610303145403460004503801007809101008141c0c04158a8401c1070000502145091141d880b5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 462737428 1250 462736178 462736189
    0x190504150c0f0206030c07140a020904030c0c0308040e010321050a0f0c1e1217012705010602060a060503010e10050601170a09120f0c03080901110f04090b09040302030702 75
    0x9950b0050141189031038850f008110141d00803070711a1410500083d900c400c000704a000d00c880095400c000d001310800d241d00143e01201d01500180030400004100c40074000b0000d840c00056030b005d82c1c2d444e620340d500d104c0b00c24030070001d00c002e5402ca82c092306c40c071541550011409500da0031541e40c0f079181c2940301105407500503035404818208410600342e000040d0181c03d040504035014107100540448a02c0d003224a5001000031608004401d02c110168000803403040f41135580300c00480c1040ca0700304510030f0102224502c8640201c3c11304000003101600803400601403e030b400f405000440d00d40d414103003a902101088030035584040c4024070110032030342c00385411843c14900107001d100041882d403181c50007034882031044d650701d00b1000300b007281559a401898100d82001303407001d40303c908050703c078561814000e4180b01c0c0150004460210a40c0509115401c03540b540d91a640a902c00c01c20b10b0b001070181d00c07006854038120300f01a240c200c0d0300c14401c540c150700440c580740e0035909111 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 462738678 1250 462737428 462737447
    0xa0911040b0d0608060112030801150e130c0e010e220b030f100b0114120604180b01031403120a090c0b0d0c1409211c0519050415 57
    0x11105400340300104991074003100506032038034034034000305100707060031002828000e042c0e0154420552188803600060340020400d81155652404944511104803064452160855a0590055620b0003500c0c4c2c0701c01039400180d0b146116655400ca4101400040d55940c2c041f61940364408550f4201c0b5081c1c10380b640290309001180240480d454400f0340c042450004006c02e20324040d0018414001da03001107103c0d12610640901e000e82082c21448540700d414420225843c2100010034001080d940b9250000c0351480e2045c820490611140e0400d0a0040801e000c100c0e2104d2441e0b9224189010000603280c01c44034034070b03000919032164a403170001010b8080341100e9031031040c01d00280400000020301030985040b00042420484c1490080010080c1c2c1c1080816280c240403110f02c80d15201c40183e030101011041d100181070300c0c01024580702d44100c5421980d59489021000b890740036000e401e81b01c00d41204022071103031906042e04c1c40c1c041d900860f907032410741c04007000a40d40f0508521 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 462739928 1250 462738678 462738701
    0x1e030b030a11030c1c150207031b020a0308180a0b0306090609070c2910060e060a0912060912050301150f0507060e1b03030405030615030f030408010504140c0a09 71
    0x590611003040040392050700b0401400d40d106100500700c500f0702150008400486d00b641c00d045290600035900544045018100880c00803005c8a10a0840d20f0300700b403a2003d190801c110f1078660600500481c1010360045013940100d85047c4001180701c408801d0b41c1c05100000c00040003035403142d00313224121000500030b4003000403a0f081503021800c586200300c2da80040480a17403103020301c8480c01d01800300161101c0a0b640c4613400400101c2d6001c2d00c008886042258815590803041301c040b1000405c035003003024200d001491030000c001c190750290207003501c14606100e540c1450700d400c0c0c4890009125001014071074080456a46218110541c4855154180740f0300b0000c20362110801c9840e0355401c0b040720ba11000c0004501d0b606074040001c071420803401549403a0404c0c0101b900e81c14081e004a606011b5003015030a107680c144040b0b241030444070226511a50b0b50810580a0001941c00352844a265003841c144906c010405801c401400f4181186061a28508800a0404d92482c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 462741178 1250 462739928 462739933
    0x503060411122404020907020c03060a021602060408030306041817070201030f0e07180204030c2102100c020117040201020a0b090118050a0506180a14030d0203071e030b030a1103 78
    0x40362081c1c01d0032070000c8000c2c001c0200d020591302d8684184002043c010b06030381c0555114110880e4241e500081060b406800c403040541c4811600790204102c0c00240002980848041000b088209002015500c1640e0890381400600700d0080c0031403809035000c9000e0807100c003020a04203620550f00c010314045206140c00104086c40140b10011582603404548440d00668820062255961805403080000e080308500e828519075a03003800920320f22400b0586110156095407200c60681480c0940d078001e000c02100c0704d080c0e400140720100700c04040b40854000d98120749100048026603124640c181c006000244e4a0b443d804054000142119040c2d0349607048050034a43d400d00403e003481c4544010040c0074513510705181800d03002030064198420040c6a1400c10b280000c2084070241c200b0700c510304d42d85d84001e44504600c81c0c400c242500c40e000000f802b400300e07445407076030400d07842d41200c04000f927885203011000e0b9a15081002c0d4140e1010014402249084000d0710310407000404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 462742428 1250 462741178 462741193
    0xd090305040e0a050403090b131208090a24020a030e09060a1a04031712190608030f090f01090f211a0609090105190f0213150306050306041112 63
    0x40c1c440400c207040f102d040c041070b01d50003484101030300500303000013509a0400e07050803c001d545403003202038410312813000302803041140340d0f0900802c0d0b03007203400d041009040b0030021611000020100c2c3e140d4070500416900300100f070004103201003842000c40c0d40c50b03034032100c01280d00da04100340540040c0609501c590010300c0000c8201402400d2640c1048200c80d0503121807450400384252413520308455450002040b200113000e040c120060303840144550800d1000030180101402003915400003104c81c0b00010b00310503441c1010020f0003132074400701c42c001a041e80041c011100c41c0304510070f1420100c1000010312640c0c030449400c034a0017010400e034071004605d0b41c6643c4040c0b102c0701e00e403141d0b00d40380c0000d102c464104a05115846030360384000740203604100030f0288040161440702c545a560351060086a030801741c04071038405610f542106003960702c4600021700303441d030b4401c86008280761200024442c00c010507450320440d004903541c2030740075042c400d0003140d40e003451062403680107085 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 462743678 1250 462742428 462742439
    0x906060e041103061608013c050f04060b12041e0c140409050c0f01030216121707021506012c0301050a1e0207030e06040b030a110304020619110703050a0b1005060d09030504 76
    0x81c12602320321780c241001654a45440e0030300040d092030301022402182082000d00c40d03400b100c070807a680701c01216a100d00d5980c450a0001003030540740e031111a80c041c44605803040c44501e5001c18180c0e002c1102c0a0260140c0e82e040000300e40d411400208141c20012452246190070b244809882c10706050151070100d611b003458841e1403199800722246008003208441040e070290050700c1c2c207070103084012a2030408900285d034500c0406501c2d03e18580190003c0c081e84d20070314400e0703400403001c00b04508a81401018983e11801c800100c3e00079803800b400600c0b14103060040001f200d000c58400d0030403040007807100d030203940204019010320a4004025505840307400c020001400300042c215228100316104000351401410348600b40c1c0ca00340240b10160340e58000300e86104c41083c846541c1030300a064240c0381d0080483c2d07601301c01d000d6a6800403e101c0041691a42c40b4412401180c02e030b51041b140c0905c0000f64041c0680200d414070881040c1805640011032550080c14042d05040e95807 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 462744928 1250 462743678 462743759
    0x1404030305190f0f0b0307031707170a020307050606060307090e0a020f03010609090e0a0c0b0c0a050f0a0506010e04110907050c061005040c03110d0906060e04110306160801 76
    0x14408142c641d90350713070140c250050f0b4510404a80204c01c4000c0c1543d1803560301c40c0800341e04540811a48035800041100422800380781164031402d1070001c0c40e84a24012001945a8201075421344050045000040700783c50a8011071344600110f407200c4e04103d05183d4074a20030307a0001e01a181503a420400e10f0211184800554020a148c0d5282c086880c03e09100700240c1d81003420201d043da114242c07010010340d941302040b0607122400f26541d1904650142c5d14030340902650050054001e00701400060100800c40340d811601079411194a45da035030342600e120842c2120042d02c0d001c1c10000454091500c0c054641e001401482e00601b042d4282c107800c0d041200c161006000107018200400c02030401d40110101e561450400b0400000c52481209092081c00e020558466a03441848200406503228401030014144000c8407864035141840000c00c048447c940300f031140c080090004600f403032101030201d2095aa50159910300b00c000e0701500000098808085100a0303420700f0207104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 462746178 1250 462744928 462744941
    0x1a031c0e0307140a090203010e06090613052d011202010e12012a0509090a0e100f02090a0e151306080a05010c03060f2723040c09140403030519 63
    0x710055816001034000811218542c164170415905005100400c401d40540714402d900410584030240e00d5a910b41c0000e0402d010740b4150342c102c515000074411700700381c1c0c07495001c1c40f0100c5209040541d206125400c080c1c15091058812a110300c00d440001940303e10000d8464040280203884004911a809420355080224441d0070951482e0714081500700712050030151401c030f007403c07494021000d000c915500340080c0140314064481440100b807400800982040c841400070401c5206c0f444a0000d01942c02006207622444401c000807801018000d0744a00687c030990002c0c105500c01c10a102d04a00d6802d85040d03200d80c1c034440055101d03000e00c1000a1940b00700d00005100074100e030003800301d8046420020b0004042101400034059000c50711240412003400f50808100103400d10b009050151b030070f00c9400e5035100c1c501440c05040700407203003c2c51140e00c4d20020552240011000c543c00700f605443c0d00702480e004517000c00c1c000d81c0320540004c254500110341c16584000c1e801911079 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 462747428 1250 462746178 462746189
    0x6040806160507260f040605070c0f0e1308071203050402031b030307030c080c0f0706110102090a0b0d090209090a020312090312030c22091a031c0e0307 67
    0x20000400159454141e1440c52400d580d0814500342101c58840e50340d00350000b8804085120143c0180c18161030000a031159040c00303402680d6226203d290040140d042044226040402c1800c04181207101000e503101740d485072400025260b4490042c09441d40c1c82c0e403016a40c3c103c00304088800308400300410040104192801b0070141860f1052606d031403c0c00d07440034141143c19a1480311541e0100803a0304981c0c06241c074034180c00c0d82c4e080100c603922400a94405078825441c126402e10008641c1008a40080d10b8480500103c010318030b081c1c3c4503041342c460b8407400c405000d00c08166a0009040d86603c030040000d41c0314000d40c0421040720041d50310320b529500841c1c001e011803600300700b2030304403036482010142018851000700b036946008150310040e5260110000703022007481300070b42e00da40080e9150150310b102c0f917400c01031101280740030b0f605150b801c00c0f048506440c4d070300900402695018004045008000c48032001c3c01071100c0e440360810507062040011540e04000700c40103001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 462748678 1250 462747428 462747433
    0x9180e21092d03010908090f0102010209030a0b040317071e021015140303070b0c0703021203040c180b010c14010b180601030b091302090c2107080604060f18060302060408 75
    0x410400e91030020000400600c640c0c1841d02075800503907848141d601406044d48c404403a000403c0040c1e0190050114041e00b603c140aa56024082800e420134081c5010340c40c1e00304c4500c0307008100d005c4506c0842e000c00c0444d1656008035005150304628210403002031060f2280c84000185440941c3d41c018048544003105803001d002c03851019680d81603151003140250b2601d40e5603034411940c548010210405214041401c80a05009001001100b1480c8141daaa40d1509241080400285004603d440880d50b6044001010240714880b81d5950584502e9448084c9655034064842c1407003c0c0b4a165480d0200c1001340c0d142d00c2000c08014041054120705407518030001000c03070305030b24615442140301c1001e01c80030349041551019030740d03010b40300402290360302d50f8501d59038424000b4041811a01d0a1040d03030011560103464041d14040d40c0d50300e501d48600341040152080790054054401001c1304c02c000e1100300d002080d08034003410001054030740d502e4001943d103070031640c00b18100c3d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 462749928 1250 462748678 462748729
    0x409050a0b0a05122808040b0a09060905030c0d0303020d0216110406030c03080d11030702010f060e1611070519030b010e01181a090709180e2109 64
    0x2881e041c41d4181c00b4100136108000354410680d40a81c0d514000803440c12113120000d040f042da0907000d554016200d410554550703a403551941041155030080d00c01c000040c0c280a00410410310800311941100e038020010301da41034401040148084503214100e0a1560802c46000c07400c1c80c50016141c507410011804440052030f00703146c034405210710b00e400d02c29407034001c00740f000503000000b01c02940d030000d22140d15060004800c20081242000007103800c0f502004120b03a90354150000e10080000c42c20030b210722561184807910301c0000b0396401c0c0d54040404130840c5403070300c00c00c072950001d80c4020484403a1540c98001c40d512100b400c03da4114000000340600c24440200e030f00300c0c01004100c40450556140c0015000d9a01110500a0300d05850303d0a800c980c0c01d01e03081030700c0c44440c000e00504450a00d0840542070420302c3c45036000054011400305d25403c01c62168411800e606405010a000554002211000182d13420b00c0b0790f100c140004992ba480b244a40d02d100c81985408800c41c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 462751178 1250 462749928 462749951
    0x2031e100e0a030c1703010f170d02061801060e07020304030b1807030b0411040e010608010f0b1807020a05012d09020f0108061201050a05160206070c170409050a 71
    0xc041110005055041c24010104525640040c4107810180c141c80c1100010300180762110103c0b81d80803400c0091a4080000300c0c48180b60000341e000c90307444d0300004140f100017040710b07900c40c0c1c0030b2001103015802c42d4000854107400700c0044034407141040700005aa540707944c1e0034400c8107000c0d6400c00c01640041028020041074aa0703141e04241412a21858031101c0480d46a0701d040b68000244910111008501000225000c030f000704c0300000c100b13022215914680e50f00034050b034850315516600303100043c02c142e060f0b48140140840d0150604812181ca00b04590481a003d0164811885140b5003440450070070303c244003900d030805000413120802d01604541c0c1200507292a0021407400c000140141d654501f52a0451001e00f8480c102c1d40e80c00c80051a00c0c5a00c440c8803c07154280001c00c0407008640d44046d1182c5240607080030482c001080c204d940b40000c031000400700d048107040402180c585e041c1e1100c0c20074040c0d1414541a241c180071740c00c1d1003061b684981466114401100c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 462752428 1250 462751178 462751183
    0x503010912030b01021f020a030e0316031d0f0d050304030210110705010503090d0e0307080d020f16050a06030902030313170616090b0c010b061201090e0316060c020a02031e 76
    0x4003210901c0105180c50520051490000890302c1c50050a44c0c00201c0c034038109c1c0039402c801c54a01c800001c5e203489071404500700101900c401400c90004a80380000c000c8003054041c0f141030b0480c0944075100250400040c041c000b00c6003542035803180b0051100000583d00c0d60022040c15249a446002c00d00342c01900d9458480c65400c010b0500105008019176007000094000e441030051a00c0d04105444401181c145040d0380c22a0399180a00c0c108510050780002e8146c003080c00810443d120902c0940380340054149900a15510558448007007200d248650003510f42030380024190b03854801e13100b6000c3c007031649035071140707595158140076614880c406000860b4000301e003103000301d10320b0500782c4010040c2102c2c4c0030b410442507020403500d42000c0700354003041d070300036001e00001c0d51420440011900300341309100310340155082c00c0e00e151440e07001100f40c600201042c41d01a80d039121584d00d200c06402c8034940c6208511030346d150741015035020402210007000050b214034061200200c1ca03070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 462753678 1250 462752428 462752441
    0xa05090103030c11011b0b06040e10061a030103080f0c011410050405090f03091009080f150717040f0201030912030501090b01020109230a0813090b09040c031b050301091203 76
    0xb4180904450255036007046911880d0780c6940c0071507035087d90383c0d8141c00900140141102000c540c0304a0224450141255000c0b2081c1c4071003000082907200c400e4040c41070b620003400300900d003000078000ca00d82c04500001520010400c1400803828072012021760811110845066040a0040c1000c00550809101d003a801c40080740161081015442a5542d24454000f040c0d002d00d061600c100380f8148034001c1d9101038140c0b071040c1c2d03a100c5c40050b089035943c0d289200480d43c3d0600d08000c2426203000d0360382c16007400080c1a40744c603259100e44030300200d107042c070b0703021380c14191034150100000d080e4428002140318941c40006855042c408040220b900300e40c001d50540e0324110b041c030085544400404400c81c40840d80f0303407a40903645019402d101c40e81d038005004413808104102640c0d000845807041e10f01610041165655000405c01c24000640d00070b0060303c41044288042a00c1302801e240640c0380310080d450041e640c90100c2d00310b8484910541ea0510003005d000001a0f1600405 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 462754928 1250 462753678 462753713
    0x2040b0315060f01051606270c030303022a0105040c090b060f031315050906070c031b1e030e1e0a09050402010903020904230f0c0d020a05090103030c 66
    0x1000508510420440c4084000d0012031050030752100b1084113a204400b00c0356902200c010400200d0800c0c0b44c144084c051101440c043c8200343c1003110040b1600c3d25664445540208810711154990b807000c1c0c0c0258840075090824010440010400c040b4410b41c901d059940c40c400055549094200089940c0c540c3c0c03c600501820314080204503030b115429110b94000c040d06413985d03616128806218420f415100402e01c2d65104640c0e440c1e08081c1c0d03c41c51142210f03500b1344031666a100c01c115441f1b103072201c008010070b080e0203500c1100c0c0c07000c46544125910401c50548039280c82c5502440b10450400110001020380080c81500e09142c00341c80300e00302407450045245040c450004015482074000c0f4003401d56a640041c003560303c00d00d8010011500a018108181000d04002401c28121200040701c0096210303090b404110010304403407828038101c090a040314002003000740303490b44420240e0b8022001540440d07542e5a01030003d00031440b17034540c0881d65159140050746503002c110b14 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 462756178 1250 462754928 462754933
    0x16031803050307090e10231c111012051b1b19080901080a111201050102010e070f050d0311010c0806010f0203030603060103020126180106082803110102070f02040b03 73
    0x140a024000d01d2207002c251254a1283c2d03030341501f80d9001c0e5503810300c0680713400c0d0300207604022506507403506d510031031340381d805000802901c0c140742050004200d800704e4030a00003a04801c1092800d440e030ba201980146030f442403620403000480402020360031503804104c1c2560034104003104003404000c02c0500c880e642c40b10340c02d0722525031100c02450048541c001d040c421100d00140103007445910182d12206810f10042e1141c1025007640350000090058601544c6001292402000c0000380c03c003c581105a0310000c1504100600101c0300c2c90501c02c80038800300c03140c031526000082c0100048040c041da10450207240072400100315690384418101550000c0085c00f150340c4011403054192502070070721400f070084840400f00f034102c4103092808280d6540303061002000b1039210303210348594114024000141c031071002c50b445a0548500488000090110340c0d50500501080d00c80c0a001e0b0800301401035000f40c441d400da9214100c22141440c0c80d00a0b0307801c61909120780200310009500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 462757428 1250 462756178 462756181
    0x1202010216062f070308180304030501051005040e0a080a0e090a0504030215090607050f040308070309030c0819140106030b0c1903020a050d0e03220e15060316031803050307090e 78
    0x14a0722180706400c8045d082008880c00111801072118980d5852103080c0112aa00c0d075a900f030030350080c0400c0d28041c00040607030b60b0003d2149028001d0008034455000074060000740d41d5913000303644d404601c2d1300c0c1c188941c0a4150105548104446104806000000c11989014a00281424600c24201c10900540c600f0300046940004101e03500c03103958100300b41c0d02c20386c2c1034400c01d003030146074401081904001174040815a10481c0d10049a102e25000d6050940750112240c81d11f194180d1070207a5281c080100020034121000d5140400302034000080460720782d1074442c40310804441c03281035040002030b180e640010704200140f01c440180307070031402d101c035a141c01001d611501c040307214102d03120f400600c80094184200c4030004c001948900054480c800c912111851078840c1200c452000300000d1111500b5a19000c500ca600408452966981d0b007007560440103100c03100410155100101d00060b00c5150b444600e041c080c3d250181c40746488040140f42040c00e0700400c010031722050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 462758678 1250 462757428 462757511
    0x118080309070504140f1902070302030c010f06060f0e0613080d0210090209181c020c03160608040b090a050304030f0b06040c080105060f0903010f02091c02010804120201021606 78
    0x903029400c00100400400e283c3c44e4009050407d00013850314042080c4006a0389040607000001040c4441000000303000064007084a081265800d104007070124030101008280d00d031140e2100d8802e42e100030042030070800c480c0b94048005a080e0400b0b1619840b1a8001c10501d80408c0500e0590360000d9040c4900c0a407940407910414024042141b240380e20155904184010300245807840d01000c00c00e0070220440c2002036031100300140380c5000f40145850700b0045c483c02c522130b02c00e841d2251241d10458650703540d40c030002c000082c9016098094810441d00040052008000442c040d410543c002400343c1000c52503000c0282255110f83c0c074041c07801c21000c2c1c00c60501360446a0413220162580046120b10f1910300c12000c450394103510308840215000700f01e9003c0e0040c0340c0e050f599100882120610130f183c9505030940640802c075680d000600003003070012818903409640c03002500f0021600c0f0001d0440d0100e1404272080b945504010342404a80c140200002002c20841200a0f1860 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 462759928 1250 462758678 462758711
    0x6141603030c0e030f060613052505040e0c1317120c0703050f0708010c0206070212070c03020301051014041e020a09080706020304090b0d050c010e030118080309070504 74
    0x810020241078880e419401c4841c042c03004482d9410000d410380b022041841c0d20240c45510480d4000d224840b0194442144400c501c07905100308201115412041e0711060700c0710b920f07200d000c840c50400c0410400031034460108a4201d0290080f01045516401c00211025400105420a40c100c4081e000c011460120002e110780d08042c5040040380d0b6400c102800034200626a00013070035600c207036104501030b45000100c60741100d8000300200006100040200c0e100c0a041d0340080040e40140e00b00b24055071004000d00c8c540d071180300740c540368690303e81c003090035a01c044510040300c440d050070401c414034102030b40d00310241d000c440812a0010700c070803021441e6440003250b60748941c0411111202030103804104060100d02c0c08460100b555800000e65aa01c1401011029402e0440e003819504080e500c2f0034040303920002800368200c10500458030201058185503066480e03202e596104072030394240d514000e000d44100c82d901c0c54005c0180d1710b132090030303072216000701d1400f560500080c040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 462761178 1250 462759928 462759967
    0x301090b0f1c030908071403010f050601080f0702011d010e0c0604120b0c0d09050318030a030512100b180103150e13060207051501170c090114030f010609060614 71
    0x7214402d406440381822140c03401245c1141d40240300701000480c3c0a6030b00c203510b00b008801103000380521402c01e00c0b500d0540b42c00341c3d21140030826810204503c0c1895281140c0e100368035200018581c3e005001e21001140082a144940d035516603030350500c03003070034002d852941c502520407a2801d4588440034559440c104030107801c1c40c140c1d802103910002103804a52548070071030010b12a24000d41080780e2680d10034030b00030409000c008040d10305d41c10007040c3c0b1000d40b9010b03100c00c5d0406103000d51210256500400d01101c00080d00408a4075001d824050641030400c202401104550500003400315841181401031203614841d0401c00541c1f205840c55004100c200c1d0b01038035012a00e80403010f805000c40c002e00a024500000c481c3d410b482c002c8904035558031004c03007145a10103d1894a03003491100507078203c1924401480b9890b4a84c07003054030400050100c034400c07408807240c00c2c00c450440c1c11688405860b07400400c04182d202104406902c03100d1480c034680600030780c1c0c03031010221 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 462762428 1250 462761178 462761209
    0x1020f070602280507090c12060b0901050a120c050901090b040f12030203040905010303081e07080402040b03120c102430052a010203070b22030201020301090b0f 71
    0x14070207080c80000a01d43c100586983c094211241c05440740200c0019241d03501c4007000040040c096a00030002e00d00681040f0b54040131103520381f61a00d001196140d000720f008409200c00c080040400c01072030301c62014004c843e03070313955611440c652000400010a030782c8100010320052105100101e175100601040701c20540d502c03507001c1c100d03103026421400307503521018044c1c0c5051300010915401c5202284030701e100c420315200050b03405c1120490303140141d03006400502c41d040000d0042c100795000c05440b9100408903018080c550801030100d51100030218001c0c0c100c40c00720b87c01e032a15405403110b94000040202c0c07004640d45204409006980700b189030400098803601e00700100c20000ca0040212110720982005103030a10a81e200716400c0754000d0209840300d04a40103084e491141610101680030b5881c1c4802610b0307241101c94080c041a19001481c0d600300b114030790000d0f800c80018400d40000d6142c0d031501518104854107505602d0149540d20340011580c0d42e1001000034400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 462763678 1250 462762428 462762463
    0x405060f0c1e0705010e0706020d0f0305010e04060e0111220801091703040309050a0b071101081009050402061204051b0316060f0909020a05070203100207020a1a16060b01020f070602 80
    0x555130704240d40503007692511076000c2d002d00080801c01590125440049458540f00c011b0700c2c2500610440c21a4001d1184550110b446008940003600607008020b503648100d0011851221a0100b440b982d03000e074592424518001e120044180c419403990f800414038600200300500031070f2507007a00c441c03903106143d04c0088000000f604060059041030007401001e03020800d8591550303183d00d001c1e400b41c0000d0701c040c1220042035065610039021103108070782c13090102c850a4584000d140291038054412a4040342c103009400d4404a8030401e43d1003140034000a00046902c1c0c0854080d0740c420503200d42c040d8204040056041280c40c1c01802102c4c8940b905440c0074500300022194000f180c0c121240190002628452a9600102414039a03000b1015202c881c2c9034050018220312601c2c0f002900400d0071601003200c20520001d0728202d0700301340301007407034400c10a01e40b501400c0456000c486030f076501c0e0030303407607080d42c2c10005a0300743c01c1d054008101f4a41040c6010b0340d01c10346e5800b0f161070413 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 462764928 1250 462763678 462763687
    0x50607180f2103121d010f2d0b13060f060c0809010e01020c030703140c0405010305100b0a0306020f040f05030313170c0d11031612081806030405060f0c1e 68
    0x54030030040e00300c06810004c002c00a02481071400201400e071034003451003035820110310407040f020340d225800c410804031640b020300c80c00300044209900601500214519542c8417101516100d0030054104014054400142d1034142090070b8910420758105100300044030b50b4107000a00c02e02c0807203140131800d080c00d440440c040d0004038500b08074040402d806015400700001084040302e10121801000c405441c0c0b04d400440601040b1f81003403101505941c00040400501b8081c0d0f4450854a10701404560740ca684945503081a40d014041c1c6503688400040c2c10000c2c40030006000d00030700007c0b07001d50310b0b242d0005100388440c10700380500c910342100710340d9941161804004d02c4404803c060903080c1c003e4003d042c1118007480500b42d080c000e0140b101d0b070711550f0901c201010140d84050800340143d0f60f80d0740741c000c100c0c4c100500d10106055203200d000040c1d5655405144101d11803002809c0074903251410b19109076015000002c0e01c041442000a4000c01e03160f505030568031282c1050700c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 462766178 1250 462764928 462764933
    0x70602070b090406081c1d0d02091b04060f022107060506030715090302040605100503010e09031608270a090e190506181f18050607180f21 61
    0x74516a40442610701c1b4809400000301034810030140c80c1c100544904070501302245500100d400080d101a0384040074100d400018600150078541105214040700b2940d02510f44811283d8016007201c00801c8503d0130481c560765041240d4140c210350215412124101003000c81607c0c080d0020052019446500145180c0c80c1040800700604260722600703a9003040042c05014220580010781c0603d00b0850081128100900c04803159202965024510382c07070144010200507001e00904858041044804145d0904180b03195406000d003602d55621150b01004012000000260314403c01641d43c482d40d4070340d5100f0070f007070845e0005e1070003080001c51031403044d041c803203441059909070001104400c2485000241da9200300c818010000b0416104201560f480c5141e03029041112040c121401401c8180c0c0c02c003001040c0d030b0107e150000d00b083d981c0d643c1400400c54040c400204442c681c0007150780511404030040981c0f000003540e181c10191800b01070341e05009030307036013110302010800304 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 462767428 1250 462766178 462766181
    0x12150606081306110f0d0501090207050622051f0e0f10110d0f0c120b1c051005011e050f030303010b030606122d090a020f011727070602070b0904 64
    0x1300c040150b4040d69108030070140e80d0f04070303004091750300b0156207000d0010070805a60300c02c680b2646c1d00b180050400c0e40d50407008010340c0040c04900c00005504440c00400074608001c20b0005401d6040700412510f0750401103c100ca0305400b4000099208540000c0c0700300d4041764050401c05041d401046046490741e5000041c41401c90307400210780390a41c410030070b82052384251480011035440e00c0311b5688408800c01a511000e0740e00f58054520405500c10340816a00440c2031440b5205a034128820003604204a800981c0102070007182c482071000040c111200c801c01030f003003c4484c889011010300c00b10750340e8041400340b0b0491104c004041145c45c0c3d80c4030700b501c1404403052a0f404e164540280c5020040d465100444003086501c9820400c807030100d900d55105480e410000c1110591a40130414107940c0080d40e10705220030b45403245280c0e0490303240c0600c502134401c400001c49003859011113041c0003060b182552600661400c0c400154003180d00f504507041d010080ba22010a03800080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 462768678 1250 462767428 462767441
    0x10225030e060c0115090b030d08100509060a0503010c02010501150906050f400f2321010e0d0f090e070e060d05150f060d0509010204080712150606081306 68
    0x820081c8045000035002c021074011901f901c20640680f0f031000861801520002401d85412600d1107000005012a04040c00030070781c07004000b0880c07008e080c0cde203030003007421501c03005031080050351200c00500c010b401101513001526002d15000580b1072804030010480d01990202ca00b8030340000413080c024090281a02409840b03030854040e0f1182030760604050020030402080c4c0d6140b080c1800164405195040ba0440d100d181c6481803008482d229801070b01541b81242d0b6101281d011000382890a0b16085000209504000911a0041c8180c140740100030048441000104000020800e82c02800f410480d480e040b138800b16512201000c0d6104070341c0412007500850049008182103000e030f00035500400881c0c105035061903941042c00700120341c0c000d071282c000008100a640302d4425610107540855003800040c100b6403907105482c2880299482546603441110a2406100e1701c20407030745013aa050300301005091b141c14000780c00120010140041c8640c582e1a9400b441085e40050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 462769784 1106 462768678 462768701
    0xc120a0c02010c0512040b0a090e042d050a11040b150306010c17040e0103050607020304120b180f0105090d032c120309010225030e060c01 61
    0x1514100015881141c4c103214040103e101e101649000e440031b08100c0d80401c0e519210300400600c6024142c0088004404140502c40020841521300e260010402040500b40d4640c5138480710168645d200504180580d050b06010000d058a0114075000111000c0004d500c4007801e0000351200d43d07910b1454440c040011400c550302034044000102e00c103205401e580305140c00c901d082c64109900040c807880d98140180200a000d01a19610040b02c0c40110709051074014903210401401d00c010381560074403000b2503410249446071703a1802911178102c540f103040d0b60a8a40c000c1c20106d0709030002d1f000b580c0344001480d2007801900f400c0140c0c190b001c00303603080c2d511001445206000444100d449a03411501904045101941c030034140d0760300060716a0300281410b045048030310800f8085a0f144062040001e8002108101c400c80a039411500e9841c8590300c80d00510304003544 = true := by decide +kernel

theorem cover : BRFrame.Cov 462589928 462769784 := by
  have h0 := BRFrame.cov_init 462589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 462589928 ≤ n) (h2 : n < 462769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
