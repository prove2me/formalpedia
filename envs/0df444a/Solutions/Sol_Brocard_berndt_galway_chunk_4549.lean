-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4549
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:58:59.375778+00:00
-- url     : https://prove2.me/submissions/97a53bcc-91b5-4630-a694-23bba2cd925b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 817985611 ≤ n < 818165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 817986861 1250 817985611 817985681
    0x60e010f051c051b10020f062d0f041106030123010504030b0a0614060901121a030f0f01180b130312061805070503090d050f1b0d1101 59
    0x5a80302d450721640c0c800356070b07103410001d0101d1454500c002104500c45145052101c01304e804030107100400703210113004035041d0fa54a0140c0140110040c2c8019086030b103810340010304800e40302e00001d41b16810312808256080e0b03011101501d041c0d0b0140100b490619103901264122001d03881014581d00c2005904000364060030400e5041c0f00c2c041200100003401c1c8034075a440b038240709200041492401c03201410040b950301201d44110b50400856403030381e80040b1500307070442c1c002a00042c02c0c041082c500c90750b0465540b003da81441405417200309803500056842821000100030712420006608103441c0480c0481c0c010b0082080100065060a10a03d5114268024035113171002070b108542c4001210040c1d0410380c4507820b99900b07010b803803186003c0e40d6085101e038a059441c40ca401440580c0f22000e9441d42002c100d00051000018801101528100c00345c40c0c0026240340c0000c1403c42da42d21403c00d108011a0068404001d501810302c6610003205e411000d40208048110041c86448 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 817988111 1250 817986861 817986889
    0x30050a0314150102010b060a0516110409080307110d0507060b0316140f0901030c1a1201150f0c03020c010f050c07030809120d0207030201080702210409060e010f05 72
    0x540e6030a000101c0d071000034100c80c010b805140c02e030140100c0b5007000900350b4162441a6014010030050120f440303a1183c1100e000e002170051501d0700701e650340760400344282c0008070702d94041e0900181101b0301c45002c0056000b0186a200d2001c5c0841e60a115925800000f9a031408244103008032804a20316800400d51144010152041d140b681d12120703580703240e140c000104007036090079120103a092a1168007001034040340d0054072076146585a84051106001c4ca009000445012048aa00c80020346106000f062002043c42d80c41e0420000d1401e5609892030001d4640d00c0080c0d4a039001c3e40e28080d410707030158081d10142d07901c00019501c03005050784420400400f00006844240d00380800c0018511031804607541d240d00200708030700c14482c40d41d00380c0035800c01c501d103084d000c0e00003407100116507080c02c0105603561009016030070201c454000c104c0e104011803064000311a240014400d44400000801800c3e84030000700c0100c3c1c10902030000e0022840005016511307140f4140d04080c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 817989361 1250 817988111 817988117
    0x20604020d0204090b1611060103050709150b12060a090e101109060d0b01030507181401050c060f062d06090301061e030302100506061623030730050a 66
    0x10005594502c070702c0e58002c6032411644006e41c0007038604140c0c0310113103040007060a00201030a50458854648840052081da143c4594a501002d400ca83c4009060010f0a842c46a40e032038011024040300c00c601d0495502344104205000421580502d10840c4280c1901c0001803005102483c40040100b01071100480408400c1c400850656503441c01003915211400c004100003405a001400b07456000c3c01c154280006015040490101c0d1406a01143d41501941c160b5481c0c5400594141c401c01c2c089000e28064801001300840e440b18542c0d0240030141ca0380b210030401e007040c9169070030600d150002400c3d0030302800c1c20907143c070340e02400008030010000107a05542c0d0384401048606821444c0721050907880c01c205042d010300c0207102440c1c050b40284413624020340056610310503013090314a034000000113202808001c0d100c04011412852402004514001c10155260003600c01251810b0804030700c0801c0300385590382c0d5401c5040c10b043d103022203a0156030595040e000421040c1c10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 817990611 1250 817989361 817989371
    0x803040f08040b0d090b0705070f11190e16030605060f1e1603020c03060106090b0703030e0303070201060f05060c0d0c06020706060308040303020d09080c041d060a14010f06020604020d0204 83
    0x10f40d080c050043c5128241403200190781e64240c60301c0002d00380000c08030828003000784180d8001c90002004111804e07413200b400b007016405800080c10114408066849440d100c09004c80e00c8054981410b0040d07803840c0440c42d018041400c02c40684100707000d0240c1206082c8080100408402c000d840c8a911190f0740c10041c902d001c6516001b60440103424060a50800b100340c1415010f1110147c120020303000307440c0c40c1d030500302c2c09080058140b0840a01e0803000403071380c00703040c480d038010440d61039400103403a52410182e1009001c3c0240d406200c0c103c0f03240100001d402d203402001c980504a60300050480d1440d03030042075a030390b81903140075502c46030200f000100080e00c41c07040502031842030420584903411070500901c2c01030075411040500040d5030b020720070b428000400010120045801040501841c8541400b00190006401d564031440043c001840096000603000d201d500c14020016070307844500c009980b1092107200d026800000103c0c0140c01c065420145075400030b88007180c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 817991861 1250 817990611 817990619
    0xa060f03060515032d070c050a150209030f300f0703020a0614090a022106010e070f020610120c0314010903080601020a050c090702120d0209090a090803040f0804 71
    0x400c1c440003443c0300d240c0d040000104480c8150351011000a183c805c0100c110b11030151610742c01d0498080e103600700b03110640c0c10b0b5108109003040381c0c01615900444904200c0355004d40c1c00e002e07400810446120340144075450031042000030340e001915506412940c60b250784004803040d0050340381000c5100b008100491001c0c01110002006558440d6000344031110f0207007003200856109903125130100309000148503440c003001605881040d01102e41c915510304c8207885118413151301c4111085130088000004403001112101445807116481e80c051411061101301d849a1085400b911b4020f5800010b003c040307a1062022501d5200c1c4940164040e20b135240d80c0c280c003503034035203c20307983e91a103807500101a0b00011042c0c11070000e0008003007000707403941e039240c403036500f010468010401d04001548440c800c00c503400c03d030310990207a40d941d40140006400a5400310182d2030048116a000c500310030a24422012080d8000c0b07840c40c01c5417150740e10200010000b000c15210040c0610007c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 817993111 1250 817991861 817991869
    0x906040b0310050a031101111f09110603040302070905060d020d05060a110c030706020702030705120d031a0927100608120a05070b090f12070b0a0b0a060f030605 71
    0x2001401030144103540740d14001058041403151500200d000718980031041000a07001c581d118800c91007420144d02c4443e01420140ca000a40c030182c0305941841c1c03140181c2d0340c00d550b1088050038080d002c1084410720b0041400500e100c10340d4020010b92143c1e0040181071640c0c0c0c0300d1600a88000c050a4a031445500083d000c180c45c544c003921a03801c0a4140450b900c0e06218407031b4000c8a1040b03190810401280d40e58490160800280ca01e5400281d40b40131558140440f4014050081c1a06819000d60790150741c2c5d030b00e000c0010380c04245401a1070010390344641140382d034140010f04442040d0f9404541c2c03007010740f400c442ea800444030391130038a1100c001480b0011142c20b04140005645103881c0350149000d80c140001d4401c000c0030000c1860382c43c0d00a040b50340c00ba03001000300600b5111480410b240c01c856880e807802c00d000d81301404941800307420040261a0240e2010741103a02c0d0303a004601282d81c21041c282e804410b268041064601034412810030780301d1400c001801c5640c4001103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 817994361 1250 817993111 817993117
    0x306110301170705241209010504020907030605090c1605010501060f140f1602030f01060905240a0302240d0c18061202030c0d0c080115141b030906 65
    0x11168200011005200d182c104a0140d01642268801000c1e02d030716050126034400c0030100f8202503078004411440340c1500e003204850148038144100c600c1403070710140c040c0c000c1c5001e0310708034418082400403400c4103105e409403d064900040c0059540d8498035541103959200109014a0b6202c4081c60030100d01c081c0b0685008000c03545030014041407101d40103107858006185010751842c01e000d0b03441c583c7d80c554180c4e07103c0d507005d4141c0301c80b51003035000091400a04101308880c960a044001c98410101d41040703000c1c8881348000712440010581c5d001034011541001500421922800c00161808140301c281c080f042e200d11014016040090f100c1951003c1c01803c0e81c02c1e00c1d1000110a40e42c05072010f82051500c451a20446080110041400d005a1264042c1170b4001c804165110250001c50781d090103600010450302c0102d800150000c5000d110b4010681a100d591489050040d2008055440d49000407880c10080c2c40f5441d0303c8291013a1420940d2006010b0070307030503840c0e00f802 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 817995611 1250 817994361 817994381
    0xc12050708060307080f031b031b0a03180311041109121e060106200309060a080f0c18120717030c0d02071202041a0910030228030b0702070306 63
    0x107004040c0c5041000d2524000103680702d883c0310392200e41c0c400350404022007502c0040240d10343d0569842400d14040c0c1c61400390381c030002c02080c04d0181079003c9641c00141080940e00c40d845078050f9503441040340240088610000e050580c51800244242c170705a40000b204120485005092001c0d207404550100c11402d13103446142d0026169184150300c885810900c05030380801801c20f0340c10500010f054441804241e0000902003410803145081030040c1c400000b000b6120302d440c2c8040b0980103041d031605407825800c0c661400080f441000c400b00440f00b60402d0110001c000c545500140800750025414000d1140241d20003ca42420202e50a1000b4ac10440003141c0310281d80500c2c0d4180102098924255840010100882030030351951341c1815404035030024510b2418070004090034148c0b110542c0c042e8000041101000c0340c508101e09030fa000769001d1500e4880c03031550703455201c0ba44501580b036040204040002844000d42c90354040150700c1070b1024190341c0d0b6502d506851401007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 817996861 1250 817995611 817995617
    0x60f090213031e050f01050103030f08071101050a051807050f010507060e03040b2a06040303091a16031a0901090c3b06120703020a0c140a0b070c11040c120507 70
    0x3c041d03000c1c800c082000740d196080c010300800071549145c0d4048c240340d284101800900c07a0f10400030b03c0c02d500842d80308940030726140080c0072a148c1800074900510702140c009200400107504109000c8000030b2030015140e01600000c0010075200041d10300b03400c42002160100d48800700711110300c02c00e00c0a0001042c038000011348a020104e0b9400044510200105000c0340107024490301c2c40000501c2ca07001601410000740955050a1010701c9480e09100d0040d03c901c07600603c980d289205003018000845a5001c010140070104043c8460711041002a0b00c42001c000501a0348001e0b4000c005036006424203024203204400342e903003d452020701003181180c201c02041d80704042d03500102c00314142115032500d400e11000404901074005007522041541c04604c5140c128040d05c100c0c03000503048612007007111a075111450f51044981012030311001c01c1000b09110f00d01507281a140b290b4060f100c1110400e004040c04014148500318008005074180c0c0070307e0070703481e07885414000c2403a56 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 817998111 1250 817996861 817996913
    0x9070323090a0f2010020309010e0a0305150108070f08030f090604030203100b04060b0301150f0306081005011d0103051c1b0b070e150403021e120f01060504060f09021303 75
    0x2031304040d5403a0b0080e0107110320303240100d4126400700440c0d4410f002400d0002c40d1400c403a011803000d8016400040141c41036910100070540401242d904848004046623166519010940c02081d12807103010010352041c0700c2c450002203110b02414810402420582c2010740c2c90300000d24215807200e01629040d6201c60499072810180540c8014000c00c1c04014615450903184400145802802c00c08100e43c1d00c0003501c0e0075200390004001402e821084540c5803404001c8100240000c3c8216010b404601c2001c0c541c0c41c403e007000714102c80d00a800b900001032900c4404d0100d11070b002c41c800806c5075548a445611001022000c801405501c070052913280401002d000218020000740c45195004110a101038094040f1001d80c1d60680304c600150904d14698040a15a2204075078041c8d50980088540c0a0000ea00390f035040051009000c2c59035501e0a000031102240a13000901307920302c1c8140050180f13078000b0030700c0c08224111480306540d00e1325592800c00402d95941c2480c085a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 817999361 1250 817998111 817998143
    0x12031e0709090b09040b010e1807230406050604030b040618080904050f060906130f11130e04170903032101091118010c0302030d0c0c0209070323090a0f 67
    0x42c8200f089100f000e50340024607041c281c44004c03c0ca46c051060f01085038001001640791172440d82581d19807101941128030440d01d031402c01c01701c0030400345c00018003072445003ea000c2e0700e040d00484084920282450b85424150b42b0f807500c43c050024401c0d6030310303904c4042884c240340d10008180c44c094040c641c0789460380f00b10b104220684402820407100300c0320b0305041c0205e9542c3c44280c983c0210b0b04842d981100541d0044600180410000d0108824a04180c0250300c0940100401841007d031610080d4140c50b4517075001d5900007601c000c0c142c00e0f0000c1c081083c0d1083d4100904034410002d0440303040c0490941c4002c510004d64107103141064502004020342c4200c1d01510f8101c402c44c2007528240314490f0a84d00115400610081c1040000c0a400301854000d1007110000c011000c800d104806200c20050700601d80007000728060740c0744c0800121003030710071311503012201101441d4400d11408207005400f00403016041e084180260043d50b000202201c03c804901882280c0b000c0e0b141c004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 818000611 1250 817999361 817999379
    0xb0406060b03160f090503031308010608030f19030608030c070e010603020922021c090506150603071808240903090a0e070c0204020705031b030a0212031e0709 70
    0x1041d44050180039040c41400320b81040a000100d8003030365440c00e80e114240d604021504030f0080d900054043c0400100b0401403081c0784140d4069a44070b000030b224480d0b48c0c030581550ba00c16855054504142031040c060003051030f60046c9030140c2e0900d0089400c039200c44205055030301140401d681c030b0348089410007580200d400424014509070808606145000012a9240c00da8515109081c85103907400c1000c114964152401301390940c4142c655020b442081d0030061090038010340d62440780c00c000411401d540e181c00c611042016003150305644400700180d4514446500d41001c003a5003c1e00410081c00811056000a031001640c074807100002000000c425030280c02065940c0007041482c9064403600d841804840e1501c3e1180c40300c0d40c03640000c444401e9030b03c0e0025400f9000184941c14803000002030302805100511045442901d00381c1e00750345e8400e0803c10710168005105140804140c0c03005103601190340106485514480b00107928812001c80c1c0310408505541020322101072 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 818001861 1250 818000611 818000621
    0xc0702030a1509140c01020a0609060216050a050c040c140904091209051905010906080c041509090b0904200102010f0f0e0d05130b1b010903030c120b130b1c0b0406 72
    0x14404010300824174504000030b4880240348005024aa1520529000c00055a0440702e0035110121544210540b51a00a40300c03550030105035000d1050450b116501d207480c0c0300c0c0e503110003015110816001c000101e0105580c0002e900154444e82d035840540100d80c28030f058210085942d81d884007498141020001c9140c00c1e46418642802e20400a11050340c11aa020007030340c1580c241408943d84524004215100325080000100300e4842075074011034100f03940d0340559007049001d00ca120210010f1103030640040307030040c100d1030358041e14501d0140b4812031508560f4042c800410029a01c0039103009071004d080401c40f840b50f60b4088501903038018001032007040704525000d803410014881350744041c43d540c000e030300c4806c2c0002540c100390080b8140c04202c070070702c00c40280401d2180f4200900105280c0e9507140100b180c420007407000300d406d8031440c0c40f41038000303021681103c80881c40100412010409541001d10301139280c0415070340d0186110814400c10003080a85414645002034031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 818003111 1250 818001861 818001893
    0xf022223010b0a27030609031416170d020414030106150c0b0c0409090302010b0102010b101403040222091506050f0f041b0905030f0f03030c0702030a1509 68
    0xa1003400500c14504440c0445128061a1a0000340f45041d0420000c44e80c0343c5100c4043c004d2518003000041080039040700b00880d0090f00c0b040c148800c000301180f0b80348184141c10b1034024a00c00408001410748070100d0741e1407032030075143c0e0816407a00b40a008036400380e0840340800c040040840034502d4240920009481003002e03662070407042c10350142c083e8034550001012813507c00300040c051501c0d0410f54004007009001070214556a0401038028070114051324015403c28031507070054104007914000080c215669102045511030b0b400980740c20150040740e024100f035042c01c00018070310301d604140d61081c58001580e06202d180c01070300d10300c160052410040c1130800400665030fa13140c8152401c0d105940400c200060500090b0080c0080c1080914014841e00200c08096014449509896041d021111000f80442c2c1031035403064150907034801039200f00000740305401c0d064040c0c91202d101504075424090341d0358510610080444a02a0f406c0d5070304825000c1c03003842c0c4003103a615 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 818004361 1250 818003111 818003171
    0x31915020d090b150904080d1e050403110d02030d02030a0b0d0506070e18070c020d060515270c0a02030c0607032a021b12010c020c100801120f0222 65
    0x451130440204d4048007000740054462100420185842d02080d00540042c242e4061488220340200003000028902660158001514038000c940f502000141042c40e06c20350f50000c0d420042003070b03c2c07440a540003d1040e01c0316074503240c240503181c9440e203c000019200f0400b6024a1600180c010105030301001014801c0c08554816080401c03955410364202480349003031700141c038890020651514802c2002080c0c20b162804210081c24020302150880c001141d44034542c0014000c900c18004654000c1c00740c0581c40d0700840c40004c0d540c0001c060728842401582d00705424682d240f4100a011101031021035110300c0607000c071603251500300060700081603005501d546050f80c021360315500404040901d0303803000b01c034490941d60906540c80c00105403000740701032014088000d440c3c00b0030390740090252181030076415203680a04d0030725041c2e9010700c1a28001c0c06858a800000e00c403201c40a03604500101d1160030207a004001040c04205500e00110707151405071980c121170705515040d1071032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 818005611 1250 818004361 818004391
    0xc060702121e180d0506060102010b0d0804061b06091506051e040f09230c0a361505101701090209120601080d080a0605031915020d090b 60
    0x90b0b40c040030200c41d038030080c0c040380b00d480b1103251240c824001010004a40d108200360380940400a000a9441c4200400e80c02880641103070814409040481003005210000505c000d00150344140340d5602480c1c41041031010581450300c41c1c01c202c5406a00603101c0b9000078030181d0b0703400c0060181d08004c4c4000c4da40c2204500010b011040e021502c050254859502c650703062010802581100704c0c1160803c0c00c0d54003100d036140902c00d00011880c1d01003164081c44107500745902d4841d0306074084035924200d1040c850040000228024a0080001c8041c04245d41c01f84c5010100d01c200000d003101400740c005450308150400c080c0c840141e10440803c01c8503014440c2000360868480c1c11107040d000056102c0c000040055600c4c0003110b034041c2a846208000955201c0000e29401c0440d080d480d011903d0711440c05c1b4030b094804074000e058040d03100c00c05171086890840c401c00f04090244d4144c000b40c040c454420b2059034807607101c400c0480c1c0c44030302c03040c14000c1c4441c01c250041210720070800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 818006861 1250 818005611 818005627
    0x703081005031c030e0d050409050708090a030c170712090b0a020304170c030102030c07060e0118080a1106092406090105010f020102091305010e0603061b09150c06070212 75
    0x19031071003c0d01070200030350303403126103510101d0181d0400c401c802517040070b071a503001d19048002d1040d00903104200c0401c1c1041e00ac9110540201e080e6809048460094240c41c205034405840140d041e20007126104503070006980101c0c44c80c1d0140440c14841e000e07221155010a6008003072840507080341e02550400c124007a0920b800004840444180032400d60a00d00c0c0722032000c0c00c2c0070071407002d035405500000402103011000402405050b01c41c120400c030082c0c102203030728200c030020703100130041058201500000c034040c1e01c094040744001e032400184400d40040031500b45441076919401c264070180c6941c01c1d0903400400602200a0306959103020710308200080c0c1c1c81c2c0010704c030381814060080c0104540510070340450301c14603009400ba440400150304c4a000611091042c008414200004130340c20b45000f04a10340158150031320080034554003c12100310368080e0b05210341c45201d200c080c940c0c00c541c0c1d03005415003141d184044c102c6458203681c00b90400d045002c03540d8500d101000301d12 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 818008111 1250 818006861 818006863
    0x3041b09450f060203010305010b0102161d06060910021b04050609070f05280e01050304030e0411040f080c040506100915050d181502070b060d0f0b0c070308100503 72
    0x81c2481c00110036146800035401d0681260251020262442e0300010004c020f00c401504040700c0104282d0840d010b265047d04116100101809400b0f402181402070202000300400c0c496044030008020780d1402d0301c0c40c0c0003d600c000c0480503441c0960490001e88000c0588140b6844a401c001e40f420300c00c5140c0840015000301d4020a0f210500c000c80d006040050b20036029190b001110340d15441600112129050088444440f82000900b002c1015107107544160b058030301407640350b113559408040071000c00c00a0864400521707481c200070f000008261304d00880d2100142100302c0906042d030600700034001616030040189008505d42c00a030a4220703130150b05c0e48105d49807204140e1489074044400c68081c841d120f600b000311424001c00106482c01040d0300b014942c460500810340e4050070251505900030700b20f0207846207040000140850030310745141c0714218071032100040380304605c1e590111602c07019544403030014408180030b000c05802c40c00c2147c10100a4204000c40c600d418002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 818009361 1250 818008111 818008211
    0x1104060504090809060309010216030903051e0c04050903090a030b0f0901060302010906111014190b01050d020c1002040f140301090210031a0306130c050609010507020603041b09 78
    0x80e6001700c5000000070090402903040d5200d02084508842c98000c0c5800d0090480d0b0140c001525240a00d45100244032960104600120300e40c501520002075a0400c00000700801491100d00380410814011a0358031030485d1005148101070b040302c00e08201c2142003400c50020400c40c0b04c0d80c90b0000c2400580c0e00210140d080301c0307140c500b010180e601042c0c114100020300c581d01500f2818102c15884450001e0102841520321700c3c00c1143e52009001c02a0690b81400d404501040042042d82c401c0692034004002c0070b5051000c0b2104c422045410324201d9010b41d100400d0315a958000f0300588510440c0d55040200840091014409680004108580702c5280e00f00703040e601c0c0740e40c2d143e984d00600d02c5602d0b800010181d401303d00d020b292669800ca281c080885a0846442c400718407032528200f96000188182e40e0f850424040c0d07400d000d2958400b80c41500c1d81da000000807485102101000703030282c100050003003024030280e950340c2c45400c880116220000000700414400800c86010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 818010611 1250 818009361 818009377
    0x15020c10020a0b0403030f0c030204051305040b16020a0c080307050f120409051510020c04140c07030c1406010906060e011b0210110105040f030e010908060a0518010911040605040908 80
    0x503403c15502c484c68160000c0c07021450324102e16040c0104010f80f81e4055000d0006c882c01501c00c20709900b8111000402c60b1402c40e0f005084c2001d40340407480d82c0a22400c2d003c103840346401180d251010585030ba4040c000e0a606c44801c80c4c3c00094000100305003804800c2075030708114000c0c80b03160309211192a060245008600d0195a1100000c29492819120419021014011038101c040050009480e2502025014052420b0545200080c91f41041c0c10b4032a440080d080d9041c540156012120300b029041c0a840e84580c490856044c0301c410720010f0700900403600e0003d4920302e03010b03010b00030100e1080114180f000143d01403003455888040d424055a0482c0c02c1d05030f9840001094509c40d08013a8005525803801f4104420003141c01401e00c80f103402521020003059103800115000c1c4070030b0203009426048000454001c2d80b260b000107800213030160202d40c0b901c00021010342198140755041e01c0c9412180302c1c079801c1d803c1c43d00c02e1101074501920184141d0302580c45000031440b603000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 818011861 1250 818010611 818010623
    0x19030e011b02040f1d03070c05060a09051503090607030e0a170d020a09090f060302032a0d03020d03050c090f090903040e040b190504150b130615020c10020a 69
    0x50341d0075124104068584500354020020032050149103806402450718245052180e500c00c90384c544810400401e485410f40d00c010001040c600703000901c010380d000034229800307108001601143c55500c21110070b403248110032010751a23241043c5000e00e0b0202c003614000a151622841e400404004030b18400000d410060710407030180d00c0c141c0e8183d50300c20442245441403002c51442c42d11b550040040007190058141407040b120100d4607c07040315054071000b5072542c882c0d000141640700840484032251b0500d11030001d820740140c082400080c4d0200220700503080724140c00020758051240035081412200304905007a0f00d00040380000e110000014072404890340010f040e61004c104640c040d00e03400724048200c0c1014a0460111042602e00d040040a8940c01d80884445413044034230468224810894034004101c1d450020600209411b030050040308842d40e080307072680500c01c0107100f852450000a1401d0388020704200c0294100c510545980d0520307070300983e002078140940b5805c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 818013111 1250 818011861 818011877
    0x20607050a06020c0f010621140703020d0b061f02060c18040f06030312020f04050f06090904030f0f26060a0f080a0b0f090a11061209010b0319030e01 66
    0x41860362a01c00c188030000e0400d400054890501400030500c201307030000340700090040c036403031312258902e0b20840494520320142e49010400400c961000011034041290700f9200f1090305c03500803800540250f18259034681601c2c0910040e400c00e00c0110000007549020302100c20b190040003504c400c0064180156080081456800c0c842d40440741c6ea0401402801040b04840802c00305000c0c081d40e10040d000b1130380021404141e243c90b40216502c103000c1c0081c042ca000c0c14101003020446115500d640c000d0001c6c4500c8103030752501c24800d4019030023503e5000759000c04480040005203495030140400608850519002800109200410f112041544020b85d2500c01240c0381041340c2e40004c001184c0c03160700082c51040803a00405490045091088990710b131540710384514401d5890200740c0c0e02500218000c900d041825250102d00205003c0c500540003d07622a00c041c00c1d01c8500e00c9965607600c150fa140380802c002c03158502d0801c841c61410181d5200901003894004040781440302c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 818014361 1250 818013111 818013113
    0x203040f1106131d0c03010b041802041203030f0b12100c0c050304090e0106050a050d1202120706150603110301060e0d06110d1a061c32070509010c020607 68
    0x203802500e90616024155080b02c503966602d0451113003404084100000b080f0b000315103107502e00801c89040e41c00c4400c3c2c031890103248c80d01074280141c0a07800101010390901011689030517207414266444e020781d50120729081c81c106e404044541524005200340710005501e80391080c04150060f120259900001311030f40c0d80241660800041c2c070001380710707000c001000300d1803e072958031510741c450314000200012a103400074460080d1142c025213038056444215071000400e59501c11703200010301d205031034101c0500c01c0307042a542c100003800c450903901c83d990580131100720404000108058a41400380d0152181d81145620044c028001003140c000c44061150302d070713900382089c41544110708010b03080301140c0700c104940109a11020040c18005509644541c0115450700000300034805c6103448520031640000200220340e9411150300c4883c5107201c400b90903102d680103000920801040b03056124074080a00b4020f040c0070074072806100f180c0c1c441e40d000030484075595040ea8240c6e81c031401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 818015611 1250 818014361 818014369
    0xc0a050a061112040617010f0b12040c0b040b220b2a0d4118030d0c020a060c0c060f050d0c0e120609030a210f0c0e040203040f11 57
    0x3500f03060700c504a2000500045150b400346a2035082038581105080e203076240d007948002580d0500c56240005018090110340c0c005091100d40c10602c2000c092200c02d65034010b078001908554400e6000100105840d41083c1c2000001245140b0b2060b40303442c0b05081521204180c050420785c0a40b489449903050a01d00b105041000402c003442e084403100f03001002c00401c4110542140038001c0450501c0c1c0715003068850340020b101c000d1190841800c01114412811030708120000005403c0810780080c040d1024030000c01071b045656103490b011a07850040c8401444241d000c04100268103002c2c0011030103402810041d50302a160041074071905603411075181c050080c40a00c0e90307282c07200940c03085130841010a045c01054440c030b5401121501c505032a0750701103455800c01d420810100352040c2c8203007001e0820005400340009814090310403070341182c0a583d1b162018560700c0d096401903640200e91060000d9003110709518606c0c0c6aa21584203000e078450040001704801344914203503513 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 818016861 1250 818015611 818015623
    0x90615030e0f0714040c080403120203070c170408010b03070f0303180513060305060108030a05250f06020306031603050a0f26221d060d06050c03090c0a050a0611 71
    0x40c440480e10b030a0748404c0e000da01e01244030b180707920807882d1401d843c5940303016402040c45a40c154507034441d078100074403610010354002011402004101c0501c1400035110031404074640b1003802c4140c1d25075051000e400c0c01c4842d018110391180c4c0c0500300130424140e01c44400000d4030343c91701d882c030407101c24240454084a0190410303a0322420b00003842c0303503186035584113808480c018005c44030b4a999800006851384600d05051740060810018445070f0420808a040c0c6c80701c403517954800c6c6600544401c3e0300440f9040342112040c0c1c001050101c586802c0114560595019080b01190f900e1650380035601c0d0100e160080071450004480c00c140a82c5000700996141c00310a608054141010002c00300e078888804101f00500d0f1818801035590212070320b0007510300804441103000c000244041d6a00c60090189500140c20354120000a03084d0088034025071003268125242c0c01c100700c189060070402d100751401810610000c001c2565548046000c0f200a82005030b0f0940d00d0300c4140c0d003000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 818018111 1250 818016861 818016883
    0x1b030f0209121507030225050307061410060906050403140c030d12140903030c030901242c130c0b16031b0206030a0f0905010c09050406090615030e 65
    0x81e08205800440800c0407a80c1030fa000340340c5030b4401c034594441d20250201e018090811040701d1011000b00c40340a5480300b603203d15030007402141c0c1042c18076941e880c19181340b081c4001c49046240180040520b1944500c03001d45400d0070070000301818082c00070300368091440043e01100401c0c50305e21402c607050084082c0d071440a400e540100c1d8075040003030443c0c818140040130441c508500ca480184406000f0350040d000341c40514a580c84801c80035800d0f8001034840440c9559900849070f090307000c0002c20004c2e8509170303601165180340408054141001d0341c000c800361001c4410134000000c400004c41c3d48810000c1001c1140655030618044408580c0c000341d640303030310000d0307402071510711201e010031028800d42e81c001c00f00c2100031003500880c0004030f0081d00410b0500c08940744446a0304950031104180301c2c001410b00c0c55450300c600391206091003902144100c0014061030610b0300030719014050600d41800101e191245510b005620740030b46008259944421005003c0c00788400c4400d8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 818019361 1250 818018111 818018119
    0x503030d02091c06020c19053d0506040b010305090d18081b04050c07170d0b030d031e0e0a020603060d12030e0d080708060111070503150f09011b030f0209 68
    0x10f0006850100000d500c05050101c5501c660340d1078851030b0503d009a4990680c1c07084c0980342c01c40500c41d00c0e6040000d10102042c2c0100890f05441c0700c001c8034032614030718840c10200490103041010511003255001e800d120304060808040121280001a03002841d110501d4400c562503030070350180d01d00b2100c540005003540a6040c000d41001074840c600400308104590410598440c1e001c040058820790100600c1550070303601810b03003106554050010180700b280041090722507040041e00b0000c00051810119035035242c0810215a03000340a034944070030f2101005000b020340006a5074a000803402807144200100140c3c030341c1c1715503010421141e8400031207603420210310805005406210000c04062140c800c2c4443d040b485854580d0060101c0d0b1200900780e12078000440d481040c01c0c000c0340980c4110000001d403500c0c1000701f5040030890780002031440c108200070700b00500024001c030195130f041642007101d040402502045000ca1420002003101e54450440083d0003414100c2c0d0340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 818020611 1250 818019361 818019409
    0x40206070b102105070503191103070f0b36060702060705010203040b01180207150515280f03030215040c12030537051c050406091202070503030d0209 66
    0x8211200300f0440c4083d40318105590380c580d241c10500d0b6440f98444200c60200010340021800f1440c202c0800e50306c44800307010740e208107443c1c40c07500714800c11aa100003040400018140302c0161441c0107a00080c095007426241481c0d1004070700004098095140d102c1c01000400340219a908411602c0780c580c004000d544910307207800c00040d00882445004200120301b080300c000d48241d0f1080701d51080e80162010900005c03070742010b0090030020808290b00e0100b10a2101c2030340c1e05801002900c410384d8071440300c20071410180528104030f5000d0b0b6940010241e0920000b074002c20390b00714000c0300d00c44000c8140d48a06000084401c6540704041c01c2000076008002d06900c200200035242000052800c02c40d502c480b000c01d001c0c0c2c0d290708081a00c0104008590151269005004d141d104541a2031310110740104c0c40202c2e08140d5007264030a5482d00c0d80010880c440710100c8983c1660300103440c1b0307240b9001c08070392284603884d0b961021690019801800d0350303410780e01c015034500380414505 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 818021861 1250 818020611 818020649
    0xb0a03170c010204053309060703110f010501180b010e0a150c0b07050d0b1804030f050f030c04030606270209060d1b0801171207080f0d090c0e040206070b10 69
    0x4600111b100321010300b1500c3c500511030080e40c0040780e22485002d0700c0b0502d007010740e840840e811021901d00d08094003515141c2d441191302402842e020b8075880e42c0d520505007003080318030300310381091110030305102e6003050396134803640c41450860842c0c0701d61280c61b5580495000454000c1c001031001802140702400b4030490035489005031200c007903414001c0000e011b24800f00a1030502d5a0314840090030100b0004000910501d940c84601c00941005404c05044980e240d071241c008030381c070309407400e00803500304140300c1c0300c2c05002c00800600900300b1903c03c0400f01351032000d010728540c05980c1d0300050441c005888147c01c403001c40a00c510204040409602e60514006d980903500000902c440e00102d0506018419601032107031190041070310b004011801251500045400c1c1d40c20f2509118110401c1f407100010f210003c071200002461400500e000c228100c040d4000c2842442c04100300700060700d030b98044800e0700b90080c80701c1120b55601c0300030078101313101d580010b107640301901a00c1c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 818023111 1250 818021861 818021899
    0x12061506190815010915030c0302130602010504050c1504060f0e060d02130906050d0b060a090e0f21030601180302100e04050903090d23060f0108010b0a03170c01020405 74
    0xa0058038410030f084144070341d840044441030710074000c040b098031070100a00781c01c0d8000e60106412008508016041c110810007030b010000040c0c0c02000541d445804100401006000600c0d140070103e842d40305031031400c03c1900c02c0b4003076070003601c00384042d04040e0000c0138014404051801c20041c450b542d81d019045802001e9045203070501b805010746007010503201414000c4c0010b03100060041410000036840e580103e00001d0007881d0000004000031402c48041d0291500442d00f501c0100803029008070803e10704040503c51520403043c24012501400d040000c480c0c0048091811243c8400e41c400600b812184a130b2009522181c0c19070380e941c006810014504032190120340805c42c994a000200d5103a03c584c840c001d41c0003884542c17000014030f14074114040d45684000d49000165900000d92801c4810ba8880f18212021401040799040c2405004508007054031501138461440d40ea00e058100000004010301e400071450441000c2d017541628001c10000b007000c03203c80c5c000300f148 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 818024361 1250 818023111 818023127
    0x191403040b0307200d050306010309081201091b022109040e010f0507020f03090a270501030803040204050108150f0705160f0309081501050405060d0203011d0c1206150619 75
    0x21078840502026030481140c0114014202c40c185d51540c0d07180d559004c00440080024103c202c41c0884140084620b404110f0061800b0381111100040c1c61003061204080501d4200c84040456101d040f03040750604c5851950660034a090b01180c2d19095904001f501074400040606155071802120000c9100c03150861400707150701c1e40980b400072804154907a128480c0046594000ea85070100300f00b000030611800d207441199618801d2240d812441070002d5503420ba0040d20210000700c244020751030140b0071031b0f00422084000300001e0f25201ca84d80901580182001800194040040c55190040d001c9031440c07800282481844143e510b400c040030080018154005505400e01041c0c800c0000380c00107c054070500321401683c03906c010403024090051000d90003e011407001401a03c003401030908000a000210020070140664103142050000070240324030300c4000990148180492469041042116504c044401c10340104003944544542600c0c001c0640c1c0a44058644c0f0041c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 818025611 1250 818024361 818024387
    0x504051b03010c050909071106130201030501140d0212010204080109050303040627081c0230061c17030c04060201050f01050a0918020a15020609191403040b0307 71
    0x10301031492005060608988081d0f204001180c41005205040c1c58440000ca9001c1e009180c401c01c10348481c881e040c10200242c4070760764a00d00341302004003190b03050300400e4050131800c280400346400d1400002c0c480d241400010740185400d02840c0340c411400e4044802400142d0f001b400a0442864070641c0c941c801c0302e05a500f02e2508424a81e072156514030101c4980382c46404074010007141d01e07031441940c00016107140d1046540031181403185c06001038103080001554410026256243e4020b4444c0d0610001c00f21344100d00c03c01c102c6a440710f41094007881c0890301d100b0385a14500d440c03103004040200048407401d0100807c810054440d001f00301f55000b56000340115140c00c4600300080c4400e000e83c2d42d001c0d605c04411301c1b42100c41e6114009201d41040141d000d600f243c0c0200c0c1e1070303520300c1d00b106054484035410041e90507010032042d508070700d40300001d200e1045019200307140c1020185000f440d0040d16021421062410801e031005000d40035a1a5600d060000002e8003144514503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 818026861 1250 818025611 818025643
    0x12200c0301050603010605150310030c06120b010c05122a06042603060909150109200301031110110d020d0314040201200a0f0f0308130c0306050613050405 68
    0x3c19070304043c000c0c28200c1d400580400c542d010b25000d42140c81d040100944609103441d02e00201140030708440500514494680340c01c02e00480e159130702514140c981c404e041c45034034003044000517030004031070b40a80c0d04001e00d13945032203410162507140e04201141520a0300040e884050a41d000700b41c440c002c4d171141d0722503004a9462104103070360200c400310349040c1e84401d000141140c100f4030401a132025130201914648200c00c2560281050b084c0c01c040002c5076141c00c81d450b196035814002c042264010340300c900315891a0b403090180840c1c588801d000d01041b0100c100b06030300a103011500c0011050076540b64030214a4002e5a61125030710010009091656400514038201007245c051a01a9945281c000010403e00d002c3c7d00d030501c20404902c1080e10200205101c6503aa0030064880d40788030752058118100105445030107020030507800d40071485040024100c03c00f010460340d204070082003c2c1e9403900011b45940464007024080d50602e402c0008111020030803c0c00d0001c465 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 818028111 1250 818026861 818026871
    0x4150509100602030304060b0103090f0c0f06031416020106050904060b030d0302030c07030c1e2a0f0e15090c070203070b0a0e010c14070b121b0712200c0301 69
    0x1207038501951050700c11240036800400101c1c0205000e03400800b4490810b04011414071481d55812014151402c029a0380b100040c0052000c007114079101c00040c072031031800740894040d55000110b8030b100500070802155050200c03175200d038000e400c6070700201b02c0145028620315141c148400940038a0b007880d88a40100046020418000d1082d2402a0502d14608d42810000c0e40c040d19044144841136a00c2d40c02c0d01e00f00300040c000c00c81d090b01994071400140200140c95505c140c0e0b414030101206100c800c0f1501c092100c10310030500d610440302910340600d881d407520103905940b134a46406064000d5411410004e00c003194500030464144241c04541080c0e51701c440ba00c4060141c0307150400003444004020100d51b2140c008444414007038070b40405000707a200740662812140b5071049031020000700d8881c15107030391040880c4d80308450601030054606101e45910442c82041d000819480106031000a51849850100c100706903400c4801884a48029403550f10074131182e140744258248 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 818029361 1250 818028111 818028121
    0x9060c14031909060804080906070c09020a020f0f12030c0703050f040f1805060f040b0102030d020d060501170f07051803151012020303031302060d180215072f04150509 74
    0xb410009102da03802c02610750030106e8400130409c0d186d004200545000b0080311011031004240c2c40101001000740d0002c12510900070407943c201490009440340c190424003007a80c40c0d182900132660701940190540760f41d0f1200d85015182401544014110724001040100d0803e80b03502e080700c207503000d03803580c1f0351464003a60000b07054800482d0300030b4110380790761820b50042c14503400402d1007040500690f4101191765034003e00300c1c1c103c3c210103d59982c982904201e50350f004803003d08450303403840d80c03c41c0c0c600e010361102d0400394000e4449002c101002521170a1260721641d6601c281c07a00406441e20000003130b8030418080c1b400d586070306441d4244003002461801000c20303910745c3c80e406806542546d41b450445484e09800c01401c0ea003055040142818070780c401e100e021091800034071b8444090000340140903242c0c0d840010342c002c40c1020491103011403841a00040031551010392060644503d200a0210a00d0201c40642060070291319103031188800308048299070302507411036a40c0e514 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 818030611 1250 818029361 818029367
    0x50c190f08160e12030d050a02041a0403050a1e08030708040507060f140901020102040e100e070e03061311040603210f051c02280f0f09060c1403190906 67
    0x100d4880c2c0307404502803050800c4181001c440b4450005600000c1c0c03401c1ca01d80340c59600640390200c961f04410f070381c002410b02411246951000d20380c401d04000b281040d08540e15203a8501001d280a410101d031002c041ca400081809114040c0da4040e4000791030341000b40000e418070300c06071005c50b054024030901050852203014080030041d43c950b01c901d24850000511b903220342c803d07000941155020031010480d50503000d4603c2c0038245d002c84d94101c0514100d0000c1d441c0e20064040310410440741d851310381540e00014520340080c900070515030a40c5941ca0082040018404503075042401d0100000c140319071300e1040d841139000b0780d410004015540c40d0407122048024000400f141e801c0c001c024245011403691800114500001850305940070000c20000c1c500d42a005849103101008081c4030368003d149118604180c00e1480e0304284070140601030781c1281c001d40003000340b04400344c82404510089101800b0000094070381d1900700504001912003180c0003e00841d1024100240c6144 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 818031861 1250 818030611 818030641
    0xe010b0609060d0b03010c1e0305100b0901030b12150f0402010203040303110708070f031b080c040902041103010f0f0f03120302031f0b030a06120b0406050c190f08 72
    0x402400306140c11a07040030401c20340c00c42500c0c00b9089903113400d51200d64409218401003081c1a480e004005640c80d2501c00d402108035046104150070881407180e26100e03034030ba101c1a01c0d0344418032038840c556100100c4c02840c2807402182e10012110303400c0c4000c83c2c00f103960042002821080d103a1075941750340662041d60240c0e0000c1c0182d10030401000487c0c825501820f0341c0300389030261081e00b503803004014a040b925410041c0000b8200400700b0030003080844050404140040c40300805142c401515114620032280a00403034543c24004215a03c5a101400d89403c500c291612561150101880c1203900d000d4661801d03035405000c034028550b158080126640304020400785190104100d0194101030094441500481c40d54442240c000b801d00c0094180c05004644903c3d040d40a04c0c10b4441a03444140001481004030b4040b64000821542c0103411020204075074903000070030700c03c501c40d101c548c51440c401220f80d0283e5645c000010307403100e20301c0e82d12010703141c49528032100402 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 818033111 1250 818031861 818031881
    0x30d03090b150d0f0b0f33240304030905030303040c1a0706090506090601090c080610050912010506011e0e0f0105390106081e030721030e01 62
    0x10390101c00289040300c1c0c200441030040001e04024103400d181d07904e4900c20703503c0711400c9500b10181e00401c440004501c004a50007215a605058441740e0700710740400250480710702c01c1d0007141e219210465500c60140900c10020040e0340d000c100c01c254102c0300500e400c00e407422000100d40000004551400000703690103907402400c9103505501d8142549d4451001201c03c00f44d02078144400c1d8080340151040c091900d0080024041e180350804000b41010b105070010001c00d1b25103c0c01401540d030190362254845400d59055003a00e4840c542a921342c090b010307403030b40e2000b003001d1480514032040d08410300404017030f203a071505c0107a28038403250400494032841d0002200d06054040b00c1c070742034100c581c0d45001030521034038154001080c04043c40e0400382d00c0403041100321006a102000000060b08401c4203c000c1146506014140e611a50030541c203150301c44c4004115000c90b0410300407551b9843d44030004c01040210390b0ba60800700b0b0b04410071000401d160003160484401c06000d42c0b80780c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 818034361 1250 818033111 818033123
    0x3030307080114010207090903030203090607091a13210312090b0f0406091203060e061e091902130311090906070302070302010612030e0a062307080c07060509030d0309 74
    0x582e0804a48000f200315010350b56046125109001a404413588103050100e40240d83c05a40e910f00964401c2c50110003901140c100b01c5c0e019402c10428100d459000140c00c001d000b4143d0f00c1190f04140c400301107068020b031800d101c0b02841140058105c00c088510603119031903100041d10b040e1000030840300071401c060082c000180004407036505084c000c680c080e129110014680400b1b480d84250030a00d040305e00080b958400c002c1c84150301c000205503010074101e801210590095828503149071604005d00c0c00f0703000d0400400d40d2400246000c55690075481e004540b5070720416168049098244002c0e51240001c01e00850702c0c0c1400181d0920902d2104020460741c1c40d0100114000d52002d4029801c6540e038450219502100f1940030840602079618004441040070811044603c40d41c020020b000c0000e80c400100c0e813801340c50b1415a42c02051654652909040076400d510030200684424081d10300c6c040b5000e60010f018000004041e03044424840d41e803401942101c1c3d02a50181117 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 818035611 1250 818034361 818034377
    0x120a051009030c03032706020301050114180405100803070c050f124c0b09160f14031018200c0708150702150402221d0c090603030307 59
    0x12038060f4100091000e902c020780c06c501200c2c0f05d20844c11411141c0212007481e00040104a20360348044244404c80d8009000c40c5004606000317489540b001c0314030781d8003d54440b0005030401c00d05001301001800b00f032080d2a6200e00da80b8251030300000c1c0c0d0041c0d51280036002c0701080302d8107048184204d001d6111001b031400128242c00041e6a0b0940b0b4851011404600d08070541205604a07042082021010161600010701c609100740c3d00e890101a028040c03171402c0102c3d0030740118075000001058103115801c1840d1b40780c201ca28204c480c500c1074a140002085c070039000540c07030b9000112050001e2400340351240490080036610800c19209060044118040000100c5001010307003044074001c131465940e032100141d0502c480340b4483e04140140d80104901560144243d00701c1d28401c005440c00c5240c241e00140a01d05001d49000041c00307080f02d100d00000180c0d11103800002038500b040807030010307004525540c106605226008824440210b0715504001080d02d00510f5241c4843c41d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 818036861 1250 818035611 818035613
    0x30f0f061509150402160602190c02033c0a0201090905070905151b03030417070c060c030c0b0c0405150a020a20060d02090405090703030806061305120a051009030c 72
    0x2e181c01040c1c902513031083c0d0800041c1001d84000800120051082101580b02c2001c0c1c41205900c40381000c089040c81080d40c1f05100513903022400d034100a021a8051081104440c40c49003405806103003403141c0301e0301d0031021a12690010324405298802d0b80c07003c04071138807003851005a0784c040d681240852000c1d2410701c0b45203000415420f17110b405907040d44c1091741c1c81e40f03181d80c2c5010a10021540fa080001031006001c07907a00b44595040d130401c0b42ca403400e2040d03503403c1c4107400c0c644141e40c104030307006402404041c80b8100003444103402800510481c18402c68034200c80d4454881c29103d0a80c0d98080d84045108034182c030030755441d540142240d1a120b46030060010a524841c50904403124a81c0f241551640c0c040d008820742210b0060303e030700001080c80210741d40074040203410783c800c406c2000002d50001d885540020b05841a945803000302c1107065624415030000ec0e031041e510040803101590004040344e42c18050400c0311403465500c2614004c0301c1c80c49002a000403950031880d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 818038111 1250 818036861 818036881
    0x207060b010e0f0f15040f180605010509091503010f060815010e0f100e010e0106030b120705010509030705061603020606010c03020d03020a111c02100605060301140a05030f0f061509 80
    0x5424810240450019103c9101c40600c5903009030400b1135046ca100c0008c1c080040510302c0b00348015590b4108001032414140083c1041c0100700d1080c0c8215400e20004840c00a24000302d0340540010300280000328806400743c016005501603005903104003c005450381105082c680d04031403000c1da10700119268120004a02d220091890f440341c1141000061201d40701664540280001d103156802541040c100030305035405408218843c8040e0100209010b502080b904c00b111424201155036000300004071f130400d4101c0e40300c2d5a004c14045811000740505440508003203119500340c403c0340e45e818005642c18044510080c005900501a02c80f40314081c0d402050102d1550030111200c2d00403811a5142c050361141074407204409002d40c00181d90100694144501c2102080c00087d06010108015001c140304480c2d11200c0d00c0f480701d4643d211425040050b000c045c007600c4500761040d049642c0c404401a0140c1d05d84111000566400710303407070310340c0381d07001c40200280ca082e124405c0003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 818039361 1250 818038111 818038129
    0xf13061d0604120807120314010504020703050a030c030f020a020705090105040e1e15010b0c0706023f0301060c29040204051b04091a03010501030f080c030d09060207060b010e0f 78
    0x465034136904002000100b1a8106200c2ca049400c0d50003143d00000c805a840b00c03443e041e40164040da005010076000241c024003035503420b21071480c00107101c0102403421005402030a035444055880090b201011550116400050303d900b0b9400c00b502da6614001e1008a54803410803220301d402140443c2c5203040d0000b1030a06000350f4a08695031a0082540c00007004420307481080c6000300010202104034080c0105c400500303803800640440c80c07504014840b40c2024101c494643c0c04d8800700401c07404100041000035103040110943c0b65031f11a0005440414803243c1a1031305003e800c480c40554082c1038040685604030310304940c1c1034a85a0038800540070180c10078441c0800440c3c0102003030700e044050001040a54004199a170040e02d40f80c06020100c00d040d40664100030050020581c42030302c0700c1400d5400907039590341d04104460a400e500a0075141c1c86000e003418110002c0c04450380150034124001e000070030584a2040064494601140b0050f402c144411000c44407441c015500b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 818040611 1250 818039361 818039363
    0x15080d1b0c0503030d060518040302071502030d020a230307020703030e040b040906270b0c0a090b0d09060c020102090a0b0c0304031e061425050f13061d060412 70
    0x141e21882d1250000307130650300280b12040700c00b07a0340c4800704103910f0030041142c1008200c00c10510182040c0e14020b4994205009100c204850a03205a010720b10801c201d401d20b41d2544021910341003400ca000b002030640d1862401d640c400307030b549042da212803070080342d01409854000700151842d56806032800d1610b519450b5100c1d9448401d03c03260b440728010a95182d110300c00002d14000c400818071f000da2004d04101c41c00d0100e901000c000680b5800c50320786c03c440703550005c0d926180f96000458400341c06070040c4084080c04689504c18040b940c10100600f48034803014085104152012402c074003803808039590194600c00c0400c1403604000091148404001c1a645090745a03115003010650003d00b50120300c64101e007100610190307100305003000c1c0002c071180010782080d418049590400b56000c0046103000d80d10851464020400c4551100da5290265102d505090a84c0303848480d52007820007086003106a03902101c07486030340c0284848002c0605080604100c1d0f1035011307a80070b0380 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 818041861 1250 818040611 818040623
    0x1c05040804051002150c0405010903080d0b0d0f0203011a100e2b02180c0f0307021501180c0e06041403121b07060302070210030b0109090c0315080d1b 66
    0x88007103407980f109407104102d15410b400a099503815055000d41e8074000800649802005110034011030380d10201ca9000c80360050055600d4240d02815080103208000d41e1941c0254191640420402c2803038114682a0007100200241c0c0c441c0c181300c02c01c80d000b01c500b05500c4000d201c000d040507030190b49141c00710319000d85280c00e0743c0311000f49039900e01603000d04403051a45010100b011480c004d040c000820300140103c08aa007010942d0310300b5030254911030300c4c0c0c281c3e01100081d00345208010031442c06840a14054007540c1d550a4010030b2014840104503803810461038801850144403559400503015080703d1070203150003007a00c030441e00b403620240d042c0507000c6480d55120a0501804400e034074814000600704012080b245000e490380d22401c2814014095071015030b27201e6100800c490020304010503c0d2483c10b00403a43c9510b240c000040362031030702c42c83c03000566040d407122209401c2003000520a0740c40c1d02c090f0f6603603050720005c04005262030300000c0c1841c40743c4440b04101803041b2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 818043111 1250 818041861 818041867
    0x50f04030c02011b140703060b0609060304150908030c0c010b0411090d1401021902100921031d010608070608250207180f1a0d0204051503060103261c050408 69
    0x56102c0800154806108206600611b010300600086102d003a20301c40d000c858441ca041d042c80089401400003c201814030b001da002d07010100b025980008a84952104000f079603172502c2004468a600300484611096180591080700350401d48155178146840403a241c0c103090f01c010401c115030300704580885d840b0741107020500605070240050141e80c00b4030f9100513116004a03400070b01d07010200c504081c2480c00d094410010032012400003030701c80e000c03c811840c104006c0d04c050303000d001010b400e000c1940c0745810031134580f4010b52014080e220540c080d105110394545045850400984403010084200710440d15502c1c0b650017540e02c0c865103801641ca0307959807440c4003541411683c011042a42c1c4401c003071000503d5a200b4010745140781081e072483d032a00c0c6401300d400a008008020f0003540d0301c2e40818684030400120151402c001811201c00b503841e4a8034484c1480c0326414010070f41070803a11846500e20300030a681c5034201c5102c0d40c10707610000090300d402a00c00078001341c41d407820070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 818044361 1250 818043111 818043113
    0xb0a051002030c01111222020f0d05191509051009020a03020312040911041512061206020d060e042a03020a080d1d03101d0102031306050f04030c02011b 67
    0x3c1c09170070002c0c07400441040d00c455140306108111b44d8000e00a081403020003030b00c18a042c80c5100003c1b425a01038884c90407503445800894240c006000d009003c0b4818814071041c418440041d003190580320f0314440e14940c1c024200e0500341c1d108164010001e800c1000350840805040e80542e44190005044408030781d5030fa004030381008020340580e064a0000241400000c003580200d070f1040c0d8200d0945441c0a107000003402640b0a5580d0b50070402c02161501305081d45590082c01c068407031040d03288101a03103860000d00030f40c040400b8144403410900009148040c0321455841150040c0c1c030700b41042e401d50750201d00c409800101420850b0164004800344e10340c40c40160261826200603e059250b00b0406480d04a01c041c0721300e00143c2900c81c11046803004907140c90070020040300483c01200048403440da608001500420941c17012041084106003182d60060441c06084d0410881e100d582e2510f214920444016012030600d044080042d40b0070021405803103940382d54a64240d4203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 818045611 1250 818044361 818044363
    0x706180305030709050f0607030305072a0b0c04050d15270201030e0d050415020f1b0a06050c120c0f0106060f020f0609100209030a060e0304090506040b0a051002030c 73
    0x4082064001a0022042214680d00b11040c440601011141119280340c224001400b921035414020101601d54001c03c1425020320414a40c201c030302000780411050300e11887c9221142c19509480c00100f84010490f8002404200c6041da07a019000c108005496200c4481040d589075181e841c0d141d03227480606204561000b04840700c6803908a500d503d400d1070000509035010184e83c851950441c151440107260042c04a42c21a800b90f1041445202040300a07800c06040107911400c034014103403441c038409514001c00c0c140b440200c2e4289006500c858040b52a8014204128100c1d03102454031382c0030000c250301a2103504484004c0720b00701101d4902460035604194804404120075007480300c1f85507014054030002c400c1200007801d05150204001e03503580c001c5400c0c1d00c01c00380d00045101c22341c0c409120720321003d50050030a1051104400403190303240d000340302c0c3c141c50a1404010400900e001e01514480c0740f4010240d104a6040004011501000050031400e40c84100100703d94110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 818046861 1250 818045611 818045651
    0x5090322030c0b030f01050405090c0405060111030c100e0a0807060209060904150f0801090807170f0328110d0c0e100914101b03140d050403170903040501050706 71
    0x10603e6100c64690a0407500c0e0f405011060308014480c41c206401c2002e1396100061600d05024200c4001c2050307205e200046e24582050840070155001c0003462400600300000e03680e1703030008030764820881040803902031a11220100320042060f00c2c204040350110f12690041c10304000000d042925140c0050005400c482c00c01c4001504805000e10800c0341e13072a070503411002002154002c0c040300b8941c2e656804d140c071a04100811070314100305030314020b507001e02c1611540140d08607050341d01d040210021088a049028042480440100790b04080c11070340198040c0b1242e903000e60741000c050708074180291006120840401041d003c91654940d24600e82400108440e180c1d40c100724140700400d10314001c2150b0300e0380640501031200500d27507400a000c2d40140031601c0f1000070a40f8038502205c02d0802d603080f914808001040d50300101d0015440540944d2003902c90b0504aa103041003600098811184d0034099001440100007550145005003a41c61080034001008010981040c84180c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 818048111 1250 818046861 818046869
    0x1b080906030a1d01110f0c120c06010807060906080c0c460b04030c030203160308061206070806060c101a09010e0112021e0409032105090322030c 64
    0x562943d030706520000c2030031440b141d1125100028008490b0244400ca550310980c202d09518140000b5500c0352048240203500d656401000f0480c3d440400b0640141e5812003070081101c0350050310000109140200c0f0142c00315022034030f4050b40355645241002c21a0480d00f00e282d0140074182411400c2a0102e01d10240011310300b00d4180d0402c0851195030b0001d40b84011803080820031048a001300c0d0907041d0030740c0e00c1540751400829988031840c00700d00b0b5018600000f458606600b80307010405401180c0d0522946047d50380301020801d85590b00c3c0d0307504042d00c100c0b0100c0e0141c40807a400d4100341004044102c4100700311180b18001010140894001c40b10100414a007031890865a107030600f007040c01000d81044010382175040c941d40003452245141c0091154140440810100a500d544410320001c01041081b10a0701c6050140044e8602000307200031074588140400101d98a102d42c3c0e0040703101c54010b5081c1100c0807a0000d80302e1142400e2043d0384900500040041c1520300e618002d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 818049361 1250 818048111 818048131
    0x4080a0c1a150d0c050d030c0b0f07030506091015140d0507030507050418200d060509060a0f0e0603070807090204060e06070f06110c0a050307150c1b08090603 70
    0x1454030321901002d24a00003512845030104104400200d19040034000590b030040f5041e0349044c042c1d01e015600c0300c0c0c5101e40107214401400800401c00500d080b0544540d845403001d20640c0c0d50b480c2000f00d0701404072603c102018129009002c248500001e6004881e5107007000300d519444102c42260a40004003207807940c6072500704003d5102d82c980a41d9411580da8241982450305049680e020f242c41c14184118260b0750f0740030b1140100d804194150001c000200303960b40c441c41c0030141c401a00a0340034490103003840c00c0c04101c02e400c040c2e030001d040322031a5510030101d030300b0458410311031903010300f00380d516101d461f2010032250411300c4040700611070401c005035a14038000b000303000d807404070755950b110f44e03402d12201c0082104000c0419540364040400915409178240400c40c42c02402d05103581c42c404c1c0d89a05003000743c000b004091083c02141001e103403c450780e0070042035580400d07000c000070702c5a00d4546048207510040380341c0d440c0300d60350702030030003500308049112500126282100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 818050611 1250 818049361 818049413
    0x18060c09170a1e0510020d0213080a0501054005030301120b07030501030305040521060106021506030a210905030111070308072a020307031509050d05040501020604080a0c 75
    0x1005245224444004080300c0c0040310405540c80d2241c5078110040d01051741500003400b4050304000c1da040f54000729140c0140b00005403210b400c10f1ba00d920b040d20440c0d5070740c60107000c600c3c80008a1401007045000441d1080d14514100c10400710982c507034800c1c04400e008240c2c0c040090400d2028601a010001c8131078545011410b224440c1c1101400d001c09245c5824014404070354080201d8098500c199880b10144c009400c02c02c0c1c040d5440e482c050103c0c041d4100216500d0741c08100a400740394490320a003034903203940e01019100c0500311b100400c1c40c403045010003855220a5000b0070075000ba414004003895540340460309440b40055040c030802c0000640008042c2c00040c41c0b07801a10b07130700c1e101300440d4456079007901051080c01036038103210614610700110b590402c440c10155600c14448110071590f03d2440c0c0103060569400c4505000391203080b6900e0303218900f66402c480c0140d006107a50348607a00d841c121944080344110400c10f0b1025080003151000066566a200303000e10340c07903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 818051861 1250 818050611 818050613
    0xd0506091207021804050a020a030302031b1906051003050106080d120e06010b0306060f1b010c08070c26120a1b08010512070f080d03060918060c09170a 67
    0x1041a124103216000c1e80024004080561102010040100c0030000540c1d003507100ea042082c17800740d0040000790b0007095004044201580400a0444049401140508040c2d489046510790440c3e901e000c032001d400003100d00114501e6000540c01141e144400b000243c8c9a031030309820b48040d41c000d21100d5205100a51413a54001c88920252003615070820a1054040c0003d485031010702c0341154115010002c10819070f5202c2c215642505003090580d074806140d86168100610086101c016502c1c0c005540300c9903005958103032259410b5607400b50906020b554180002d40c40d882e60b82080c0b0183c40c80e0301840e9032124000d05914025000b030b00d040d031070314120180a4075421445040c003400303003000d46a00a50007410541c1928000c840810781d20000e40302480c6400b00390b50280001c0200c0803000141004041013459a4400355a41404001d4071109803604ac0d5043e1004850805140074480380468920b9101034030034080c07494800b00450784c48a040700241c031008070790365041d003281304480 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 818053111 1250 818051861 818051863
    0x90503070605090d0f0813170c010c1a040c0b040b09130b0303120c0c011b0305010b030f040204330503010f05160c0f02060d0e0d02012a0504050d050609 67
    0x5802071001e4a04076151902e00d2020070160f40d0304400050104001c072070041e040040d0641920f5445016808112026944980d11400101c449100040f5405400f0300190030754070403406040c100d0f4202e0495a000745201c0410800c400000388207441c03850030f600000c90000540b4000b00000d00050098945403540d0b50200031090500a00304220342c0c2c941b40519881e03441c08002e131850a007000110351402e54844400c0e02140c806c42d40e943d00254030380808185078002d282a040c851500554003000103a8889102e641a40b10545240b030303551000000140040c607141d00020000c0b0704006101288810114074179018414050140305011002c030014001420240b00f0300c1581c0203401000d201604203980c840c0103104e141c2242000700403a600c499018000146080c82009502a111641e1001d4510302c8400502880700805030070f014202c3c5425803144140500454020444e070504000103061510400d1114000c102506020741807000241960344c0748140d600590041c4050030191030881c00c00c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 818054361 1250 818053111 818053123
    0xd1212022b060602120717070f050f01022b0e011a010f0201050606070327030f0c0e0709090e01060902040b0712050a09050d02040b1c05060618041e0c06090503 70
    0x6208072858541c08004690b0700040c4664842e01c1060b035540d40303980d541031200120781202032040c1c014900180001c00c101200c442d440d1024012400d9804405404a4103401e0344500c08200000b401844098542c80180800c44c40034900080d00c0080c00610740c654040c2500e10b2891000c913090b1081c8490f075402c2d60043d007010080b8010784001c01207854650000f03a020b0103003c83c0502049a1141d00c1104488c1c1c40007000c01100b082c0400002c030503030301d14086182c0e940d217240866001860042c00034041030402d00c040e00030780c62500c402031141e060020f500c008010300110f4907032964840b10300144090b1644005c01c09030080700e102954500160410565082a844504040140070821031b082143d10902a00036034000329810b8600d0400b17400000c01404648241d0b071341c01070706070034405181c0c40c461513a5540d5500c280152410703551075508121160300c00e418080c0d01002d2802c00600050007000e120340280d004081038070104512604e6a01500d03442d074000230003041001e1814000d92404000d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 818055611 1250 818054361 818054437
    0x30c01020706170c0403020a080a021801050108040303050603070906120b0709050d12120203070302090a0f1503180b10140a232202130909020d121202 66
    0x41c4002480d02c0d100414000c0b28a20420560900c070001c14020100d0204403002550000e05021626403078840158452608050032445051a1190207049190f81c10000c1e040702c070142c481200030380d6161400d5010f850000d00d000e515006040010905d58613620462000d040001050742c00c0800c04e2500703031407031580940105d0a0101d8440104800c0c0c1c3d4038200350a905034042c0321504000409441613410345040d00c5000f4007607002000b0417522030b41c10f6001c0e00106404440f1786002a40c0c03a00340454419542c0039010380e04014001c440b8403a4041d82200e54090f460344041604108981c866080c0316405807070050302040ca244041190504650503e41c0201d0200c3d001c030920380c980344030b5042680782420016003050410280700d101d5541c80041d101084036952a9011070025099548001e500400b481001440e032802d0119100c81c81d4420754805581c0988018042602e80d2140310007030303619003000c101b00001c4404089121086002514509190300394502050b5030a0f0b41d1600070012141c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 818056861 1250 818055611 818055613
    0x408060a0b030703080c030403051c0e09010803040b0f160b0405100b030d0f0201020c0607090504061a090906270604110310090b01030902030a050c0312070809061c0e0c030c0102 78
    0xc01c041d0300e41d40205404044030380c094541a50b03a0403500003903085000710741c00906240640d0003d030004005400c200d4080c19a15035408071000c00301030811074000d800b07008280c403980c003e0105005a0341c544004101d8449012001410240e5107001d0306d249400c842c00484140f90000188000c22000b0080545006509a400d000030300f22030011aa036041c007110500708024107100c401c030380c040c000e41c1281c8040d060380080d20303400d2030080e002402070526446418040c170700d04540001c0c2d1068818050344640305085020346030000f140200401d900021302180c1c0d0000304915540d0611145101c074848110861138041290b10706402004200d0b04071014604442030108100048080d244d06510141e03807102500051404618004a00a000109000b0340604c12540310509103d00001e011071614400c034215070054960200c00d200c4c0e80141d0b540100701c0b20060018402074584103028008811744c889101d41200300341540d40d4180c52915100303c0044d0010007400324103050520010762802c1e4280 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 818058111 1250 818056861 818056871
    0x31606240b0702091302100f080901060503060a020a140d06094205030307030518010201060b0d0903140706020d05060405060303091504030c0f090f14010311010903170408060a 77
    0x100d0301e201c0900c12400002e02c941d0884000841102501000c0b6002c55000f81c0307203640c0030341d4441001d0142c1e0100407200021401c200c0010b90050014000d000a50320b01601503d4651242499100607410a014060500801c2c0f5030051440c00c02401802c07250504900109600b854149564200c1c1c07114040300070040c3c1c2100440d00205004811030182d40b0b0041c100c50402c12810508580c1c01010742c10607603050000003003907001e0640c042d001c0c003501139400300310040c9203000da40103908031030b0741c1d200e4524510030506c190580011181c0c0000341c400e01034107050f05444d031401605000c543c020300b000c83d161507001c20700c403403505840c0c412a03a021005a41c204003a0034810f0000f942d1703000307020010b481a0900307041185040217003410b8a000716801001c40030002d4440b50b11000c0441c0038042e550b600c0e4a0400b160303054080d01d000e4142e0321020300024035800d03400c3d0b482395070000c01700460440c1804207110002000407605901890403490300000d0640322801c044c20349081c44805000000302a04003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 818059361 1250 818058111 818058119
    0x30103170f031314010c031505040603050d1d10120b030a1527050102040602160b1c1508060105010207140603070305070210020304050a1e050601140303160624 70
    0xe10403a60440d40b414012030340b6004518240244084ea40d8500419500b051041020140c054102011941e60b9180d0360b0000c0740c44038140070849440307110141599000c030031a15001c134000d01a0f8806402074165071040c0035090310105000d2001800201d00090070009100440d0f05244613410300c0d510220040c00405440c0d8480c003440d039100c903000d4010207540380c2e41a04112181600f00801480210001c4005200c50610500075002403040784007500558071030742004945070050106aa100c0c2c40b00b1410525140300a820040050ba42c6011155581c000da801c903582c7c58482900521a0038014040c940c100000241445a150300c80c548200503038034100415a900c10607a54080300b02d2600165a640c3c11784101d10302001e43d00c501980d80e10000500051140c0402c0210625020b01d821101c14248030390303841000451304001821039004800148081640840c12400304040101200e0030182c50341500800707600701903412136140303913a4400c0010080c1128100c413001b00c403464412305c226180c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 818060611 1250 818059361 818059387
    0xa0f12120f0c030f090504090f14060f0411010e030a0c03050f0d0504030605060a0b120103020123090108040309050415170309033d0f050c0a0903031407050f0303010317 74
    0x40090a01813804541e034402c503c141180e00041c080140144218941402c040d410615450415190342c0c0c20a1041003100c400000d5182c016143d00c43c0460060b500e91312112052540080f0207410454808c04c2ca80c050b0ba030130072440400c1c601403007040c1d00080c9180741440c03419051110404070f50300401c10041d03481da0084140e4084a030001c20202c0e056844400141c0d04a4541e00880000318010489100420503004120f058a20030380390f0200980c2d0b2950f620194040c0d81d1074500c0300400812410942e544680f51030754105100c0d00745000401c2d11a0700140c00d4442d0702d9010400c090340d064041001c40ca10000c060300c0300722088084e51130030380c94401181d00e900c1400300d407800110200c0c4190038050500c6817620042444134042014070300805060001a1201c14424040c0e0750410300030038540e00800048429800031368903012211850742d40c1c01c1e180c102010380c9540030600144400310100c0c40c2442010b5954550201841d5258118905044e540d1001072441c1c0720030304188030b50b0303c050003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 818061861 1250 818060611 818060627
    0x40c080c0904021b06010b190e0a14010309170d110f070b070c12030207060b040b060406110f01090c08060f1b0711131d030c1b0a0f12120f 61
    0x70305850140c0e071a60b0890303002c403d000d03281e01c8100b9903106500000444140c201c0107031602101d40203440c1240b080c1c0b0201100c7c40c40304584441c0d80002504010408038034040041c06500301c0604011811a48a840d248840400c14040785210b0340f000502e02e40800482c45074a80c0f07141426041030500c080e089045100b400b44c01c0c4014400c0c480d41020403403440c0111800415180d01420404045002100c001e000c0c0d0451070342181d00c64100240440702c0d2801e40100201d126003e00805e00306890074104a50401955111000c0c6004980c1c0d00b950f0b055080c0541141c8600504103480124a003001107490800010040030110f142c180c24030402e0b8804106032a102182001200d031603640c0350030410b0845041c0081194010708207034010b031241545030072080000364240d0304113a103291040751a81d224403513003801e03da10b50450861034600e04005801201c0c20342000d02030b609c0f100e07152045803046c003401d5046450901e10045010040182c111b0140c0504001890034640000e47d011011304807034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 818063111 1250 818061861 818061877
    0x7060509121006140a26151e01080613020411070813210f1101090806091f0c081f0308040803091c0b042411040f050102160e1b18040c080c 61
    0x104030215641070401080100c0400585e2041d20b00031a404c25503410115001108d0b18907007409072140001612150200d84544640c46480319600103803116804c01004050410b0b0f81b202012042c0454800704d0752002c0606620100e1080071048035082c04221895200044200060006861000301c0002c10200748403058540c898007041c28659030780016286002c1c29000040b151144004004000000081260100070101401c24103600c0000140702070301c507070300302c0100401d1040002c04c0292078030000401002c5c0c104038400d807801d03499903a0001d0603401580b0180031036101280414082c03800c50f00e00000813a644120300181d8020f503440301100580240083d14240d8005154038040c6106000c6000e01c1e41c0313241d810007840c41c0f400031241041d00940500c13003074079030104404a515400005c800c41c043e8591291581210714040186881d641c0062031030038150b40c0c10080340d030a603c000c40506003c0410340d44100ca151561000c0c01708803440c8484860403c0120720600036802162001c8484030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 818064361 1250 818063111 818063159
    0x501151a04091109040216061a0307030b06040605040c020d080f06090f07110709060303020f030c03030f090309030a03030b120c10030207020d020d0f1b05010207060509121006140a 79
    0x1199100c00082441c01813220864001d07000040b0402e0800d000e200c024459445840c0820100c44808844030030501200c0c1840d40650140f24244080346000c0e03086a4015001480415055292000f1070b040e40d4400d070704040564010011501034035040844a9402400000240d0071481d0200004d0030b082030180602d003e60b001038011a480a11900394008184001401c80d40029038801c2464010152444203400600800c000e03030b10080304c00301c221a0505a00c00c0114155211203404240c03120001e014444c00c1c4c0710400683c09903860500051040502903240007401644810500407000207042082000d508407003070640321640e6844104000074604d180c0181c4036000d6102041881c40b0f080e10285d80112499816404c20004003001c0c5000e40c401d01000848250070000d042a10740036006490258000d480c4c01c0c8400c40c85a03018010b0300400500d00b416103100c40c211749003850f20140031192000c0e1101d10074061500603c040c007411b817006854100741685003044010030010054041c0d140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 818065611 1250 818064361 818064371
    0x714040302060924031005010503060f010e030a0501050a0c0801060309022b0f0b0405190f02190915080106080a03021908040803121005040c051912090501151a0409 72
    0xc203444d0355822028030b0325003d035082100b040308808244190011207496103e40c0c070405020945510980c140e9004d4000a8101942001040d0055910015481c051030305441424041404640240075880c000c2d103c0310000650320032100c01c000e110a105030800b00615080103113800041c0c031003240003410440d10400380340740c160b0400c0c0b0001c90240c05160250001000d848800c0920003106c800078041c910070340c00c0b03c1d41c0044040d661036859040c0c40010780b48045c0120074001604080c0c9031042108400021500580d44441c90710044a64841c901c02c80602d03081420b0003452800d10441c00500691001881c046000340d800070341e01c01c0d6a103424129414102c03a00f1040000d000d06070740144c00031a0559032280ba90014044440100300d071110360b191410301c00001c0343c2c04c00b8401e8621212041e900c462401c56200140b15550f003002d45007508003d90f00c050901216220720500034450300c22000441d402d40722900c40c82040d0550f030010100107109242030452407030190212811190041c502240b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 818066861 1250 818065611 818065627
    0x70b0a02090607030e0f1903030806152209052a09061204060501150509010509010c051b090f09070303110111030a0501050301182a0f0803030906071404030206 70
    0x4064068a40754941080000c1120b104050300b01800b40481001610743c50500d003062020001c9400956101070701206184006001282c81540f07010343c8100b0281c1151104203058503644160740c0190180454001c1905640e40c4620000700c0d9440100b031182e0042c082400c002d0001d04e08101c0109030048030052402c01b0864841c9120140d400c45d0000510303d580324440100303d00c00100c3c0403602125400c3c600070000c280d50304684071202d08130210f07644050501e0140c4005517071a03406449040c0c1030201c80720441000540412803d0b0354401c5646400e036086142c1e80c2400807071000640b804001106034020800c0c10040000e050007101d07010300d08220003002965205004201000c040c0e98100d40001c10403240c5a0700e500000d0485400380c008004010b8a108400c1100b090040024400440c038a48094144e0141031114800e5200110700d910865451100d0303c0f00c4415035008084507007000c1b0030081d900000784030459000c070f01ca09080c0c004c141c0390140c4004d184036901000344911008281c0c81 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 818068111 1250 818066861 818066881
    0x2030d0e0d140619020f1813060f14061914070b0c0a12021204290108011a150a05130e04050703050118020915031f0c08010e010803070b 60
    0x40c00c10341c0241c2c0d00d00350501400c444a031a0001103030b4000c0c6000c03883c0c03402d00050440e07100320707040b41d540400c20604061460140c2000c4080c51a05194001844001000c0000441c4200d03801810241880b00303080d4642841143c1100720060090f2007182e0510400300308410403010a21004c22501c0d140c0c601e40c84040503200c3c6405030b400040c0803010014100001c0e00d00840c02041c0041654561f00001500440d09070140e20403062660a04241000071400082c24802403002e1a4000800680180200081041a107030b0990144103141c3d124003000203a1507128a00200381d0320306545004c4840d00240c1d42912030701c5103413140c40410000080500c9200086103040010340300c03082c8210001d00301414003075514130301400160b506c0d501e403154000c174410844c180c8803100703a405001411650340344800800c208150919071600760043c1070075032180c101008801305080c0300d4250001409402154002c05c40c1030142c101404d00c104040040c05181e00020582c0c0450b030f40040000510340e0b13840200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 818069361 1250 818068111 818068129
    0xf09061b0f03060509060f01170a06320f03030c0a03020304030c0b0a0801120620031f0807060c02040609020412060b0a1a131a0a030e06041e0813030f15050402030d0e 73
    0x7040d443c4442c902b4854101450b8204000b1200382c4007018004500022a074440e45008103d401c2191200c40b144511178100540704141e24503004050302c2c1060b440c1c0e2402414039413003820403030042e000001e062003004128911070f00640340c0d0311038450070a414400702512801042c0609480b103002503642c82c04000c0d1a4205d5070380380546c1020007a03011041115004203400c1990303044441600505200c4220858541d1801101c0b4298006d10031146446019903000300d8103402660041d80b16140800c010034240000c000401200600300c10b03031010360901d0002c4402c0300d51594864404220308115047e80d00f00c1c0501042c603101425550b40c0f9510140326040c82195002e03002e6200a010fa11000d0380e0064041c00c40d80040b80c40038000400c91002c42a02d880d0111001003005c1003405ca101d2806c60011712190300d840c483d00c4024a001c0054000e5101440b03150f108aa292503050507000800c900eaa42100101d03000003001e01c0302d810a07a0009840d21035103056141040340c2c4000e01c81c0309035103036010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 818070611 1250 818069361 818069387
    0x606070609060218040c03050727090614011701030b0103171b060a0e1912140c010b010e06071109100317120601090b030a0f09061b0f03060509060f01 66
    0x801c564440111502c1c0c0c14034800d0020304ea11031490021100034080c064001c0601c0341401d6521228101d41200464102000742400e0040360950380c140403d040c4080e109010160203c0c81c006801d10715041d00060402092074204659850000010000184014443d60659901001c0306030300c02c81043c40404039000e0345c03010607031540000c0d00112514101084150203800c201e14244a410052803119a540320500c01d54040c000c40d186249020480740702e080b038010a2a0701d0b142807004040d1000c85007540100c2410082d036503440d00d25944035070b00217050604a10055074030031b01f440410380b0340060300f100460f031681c05980700400280d1481420101c4501035075101f550300c00701036001108044182c200120001100c0b00200109040d5030042c1f00711000c49030b10709203107403a40c1d484038a508080d00c00c1c41825003100da1a1480c0343c0004026001d44d0711041c0802d0854580c0c02070602c00100f96441c500c04500074145015000d201c82e80ba245a000d9008000b524001981c4001c00c004031941144844 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 818071861 1250 818070611 818070623
    0xc030503010e04060e15010302120708030f0703020c090108030a030f06290d0f230402030303040f0f0213150911090108190e070f14010503070c030207180605090a090b0606070609 78
    0x701b40d50980f0030320f00155040c3ea0003916181c070940107041000d81c0e600131501031900e41d0b40c014804066008091402410030a10034816500030700303246800f06800c103a00f80c0180031701c0c0e04085402c0d446294144100c01c8014030144043c003000d45000703155500f600100840342a90750411501070303a51003070384085a054186600302000500906040e403402818003403160740c804903c10350780d603c2d0041d413040b01030b01a079001400785203542c41d1581e54040199410800f1a0302288901e010005603440c43c3c52030038021500f0202148000003180e25014070740c0b450300050451840d2110b10010684e511081d11850390080c20601190384800581b00001120540261011820a50b1040c5410070100b1840100c603c111818040c03162108000021007522000c5107001440a00024080500c6804151a22402401500c1c911034880b17200c819a107400c1c4100c4000c02e501c406e070402690400c1d220300f80e80305c4a0114100300500842c1c0c0c031640d1219002e041580302d650041688000d0000a922406125912503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 818073111 1250 818071861 818071873
    0x901091403041406040f0509190204031226070c080904090c0f0b030708040b25030b010207140907110f030c0a020414092a04050907050a060c030503010e04060e 70
    0x120840741c0e290b00c00d0007074050a0020340c4071528582050000e60302035412403c0f408003040c3c20b0005218218100070308050501c55034109000020007544020300180d40959640344040c40005009042290001aa02c2e0341d24030303c12180040b003200100151300800c032032074004000d1541b07040250490050407600750780f1600d003407032440c01c001403501940f048030303580501a1400303551001c01285a000131190078010403000c0300010001245591113540c0503a41c00800c02c08895104100e840d032890703458152010940e40c0750760703220560301000724074000c0c114030005106032000c0c81c0200b80301490107000c400034841c1c061209080c1d25014013040e030345800440c2c2140d8076024007402042d52078080080513170245192035240e01a100c00a507101e1300c5000288020000301500718a040b44244180740c104805903005041c00c40107550302d0042070301503609003000f044030030b08000401c5080540b561080741032103126143c20340001e40000a503811264003010106240e90346050a1014001864030000323240241 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 818074361 1250 818073111 818073143
    0x3c0b090910060e09030a0c06091211011a0f040c031b03200306030a030c060b0a0b0304050114060a0909050c060c011a060c12131502150a020a0f08090109 67
    0x1d224480c40440203040c81801d648107290040c0c0034060b254403030180c00c10000d160320039002e05011a5014822000010707000c103a82c5034820f10b0301c65080105c0c0043d0b400071000040502c02d0043c015010210f0841030f4500061000190303201d58418001400b454071141000c0809001e580009600203180d851002250740c3c004006000301a40c20f903405007000149192100754000d00103580c86160054010021080282c40589550045103000c0710465101d000580c1d094460502d684000c000f120760b981c0d00c1e4142860840d00f510300079190700c4404a809170401505d5079441c1c14010845203103030170006154900742402810328644442998000400064615100300c055206540ca1040d014422064141c46800c00c1401d1040c003811140c0c40e0301c0b0380443c0c1e0004592000500442880c0c14460b424250f440b51144484020039200d200960440740350920340240220110758010302000e021442e00320940000307820f5a144000380310801810310000340707440d07209501080c0804c1d00815011040d03081 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 818075611 1250 818074361 818074363
    0x4081204030f0908070f060804140712050f0c0105120a1416080714030a0c121104060f1e0c080702090f1501020a050706050309030f1306033c0b0909 65
    0x1042c508000000c40c0031400141c04100030a52406603003010001c40328447c03400d0404c81d8241800303001038401c0c4e4404180c00080c2081000488014140c01240ca070080d54603007400c41c01c4c00ba040b883ea010329000041901c00a0380c1c40b10440d950242c10f5200c540d91504d034540c1c002c0080203000341c0d00c0b081103c10014003a000c400c20180260f2900b00c0e036a10340e041d0351000400c4940500d489034501e0020414008525041569004490070540503d02481c405040810f01c1d02940d000320807001142d4000a0240120b96108606094807241802c00e01c61702c200b0140e542c40c099400203280001c01ca150780d02d0342c0400003000b044590040c0c00814030310032805c0c043d40074445141e094556100030f4000106a113420350011030410480f0350800054200340d8a0a1700540c1e256000601c000b05d980000c00660445103140300103444a4030300b8880c204200317810100060105c442160104060600d80540521901d8600e0702095426011950781c490303a180e41054440a42059649164480b4206040090502c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 818076861 1250 818075611 818075627
    0x40b03041e0507091406010e03060402310c03060b07030906050a0504031a01050f100c0f02150a03140601032a1103040b0c1204080703110a030c0b031008071d0408120403 74
    0x5d101c9466601a848a4005540030320300c10180d141c0507008200000d016181c60014890b090681000081d054840c160b003051140140920680045a59a85d100d03000703945441000064050703144140d14002180d140074129691034480c40003001800900c11840310311400641e001158000c0840405002105400140070001d010312805462a10100d500301d1a1001c8120341c03110745500c90910380c25854480f41521803984c5403d80e0130240304803260300c1b441d2a04008204200d03196400040c039032030034041010040710141445d81050b04060740001841c2c0c052680f03c5403451410079050002140e0300307081ea0351101c0c01c01d02c044640004600010b40d10381c1040203001e002016010381e030300840f82c0305800d201401a4000d200f89540310000c24400250003d40c10205c4030001460280e01d940d4030754600c50b85902075046a1403056020090002c8640f90304420005406440040d003c61401c02d08e00071141c403c0d08030a00718621101d004039040c03200103011651600c90310070300514203117454100a04014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 818078111 1250 818076861 818076881
    0x1e05010b120a050c010e36090f060f19050702010b03101a0d0c050d081224033d11030f0a020405010e04020a120e0f12040b03041e050709 60
    0x40940340f9800c41c0d940c42440884005000104400030505030300e10000074030032449000d240104800c0280c501100300142c65144621a800010600784882c110501c0c142b000292007855550801e4050141d202d0980b0300302001c5080c88440080c3e140c0d9901002c0b40940398089039241c01d8080c00a4917403000d085a08000b10242403224444546c1030719406000280107000300c06403130003003082401c0c03003a880c0c81000d100040d0300071b0f14070b2801c04660540c4a400900c080d20341e42078000d030440800403c1c420f110350242d06484110003500d9031110303001c1c0d08034407043c01c1000320301d01c01c900486410201601483c1c12290050701c07103041150f84045280c5074495802504c0340e04990200000181d440c4d6000c3c0201d034241c5806075260311154000b40284030194000520703050a1110b01c48880c411091144101046072003004010a2140c1c01c2810089c200348070401300b0747c400780040206010410b0554101d035045940070302c003001e0f4416580e59021314200c62107402003030f50048030000140e144041d0007004001d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 818079361 1250 818078111 818078113
    0xa02091f0b0306150306060f03010b0d0f2c19050303102108160b04050604021c0512091504060207080106060801180906110a080412020106031e05010b120a05 69
    0x16190701000d0341c9800101c51066004044070300162540f60010701940d044100580664101412407140040c00d80098114030f191a41c0822550508511809030021014010904104400e006000d07001c2c203501004481c0c20f80c041000010aa0030400c07c49002e008642c03100c0380c00114103514142c1d07141c2d80107481204c054020740c00f001c244200544503003101003102c0e041210705541160b0b140009ea0308a0074032289420720f5201408007040800005034456489440034100d5072501d48108281d5800030003c0c400e890925540c100006140001c6d19144400d415884946a1281030b00084440703c2e940411054140c000c240000e40c40c1d00040c00005886884000340130040e20b5071401c4409540034803036502000c0581082204107400e940c4048281c50040b00042a42d41c80081d00d4621a8006800c80001500e04401c0006212541560080c0c1030220320090000d285903842d14010495501e0744203001c01d42000c2004200642584034a0240340081d04520010074601c64007034950140c9002a611 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 818080611 1250 818079361 818079421
    0x150f120f0603070e042409030c020102060f0603100b03010f0e15010b130513141303080907080d140d090b0103120314010603180b010902130b0306010e0603090a0209 72
    0x1580ba000c103001c0141e9044c070700040181d5846485485106a9030800402c40c81400c03076a0a90710601c60180100041c0280c4840b903855203e84002807410b20010083d00d030703d5079100b00f4130095036400314002280b070180003004a00d000d49100024010041205401c3c01c85241601041d4110404964100c0d40310040200c1c158503030740c0305092003c41c45800b004242c0e90380183c00078001440d040320b144442d182c44000009400b8001405640d80550548034894050408140030040542c01484c4c1c5074031190000150a002d0318100e000d079039078803004903540107001c3e1420b682210040f0034005d40e01030078000076082c807194282c0d041030f04510100380004c0e204a10809400c0a0080c000c1c000d4118101003a110103000741e28152040300141421204c00350030a20f1011418041440400d11502802c20000010f07924440c4050074010601036600c88210b540041c001c21807241e0f001004100c4050701502e00540d01d6541d280d40e1070810042c10700095000e40f000d000d0054000b01c10f146124402210000a45 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 818081861 1250 818080611 818080621
    0x10623010306050d0f021002010b0901030308040503070203010c03020c120f25050703060f0e160b0a091d01050307210201030203041509050d020c121c05090d11010e0a1202150f120f 79
    0x2c241c9007421022b9402c000420300400000340f1491103a40e04c24002e5060700c0c20100e459002a09490aa041c03a0b00066004604269607040c28041803000e035103a02c091600c0c080302d100000f04d0900441e0400c0301d41c045801591680c601c04641c4040d4460340c040c0075100e9483d00c034034005004116600224110500d4000e40005031140046c84c0c5441c44a0300c100c1d600001c1c07801d40e54801c6d951041c501c1d0400c00401c01c2c800202c0302c0741c107002080e242c01d1400c0c46030030660400d8181407600c4050b5000341c0b030404c0311000021110346071000c60300c0e03e41d03028640503942e5620750500030a80010380300c3c0c440c40c1501c2c0820a10521602240182940f0055400d031155054080308110494027409968100d0303811800c41c03181900e5100000c0c413080201420040d040204020000300e45c10098001a6130380c0b1040c1042c80c40c9980d106001501c6030000703daa54020606003c2d041183e038411840c0280a08000d00018035064901d405440a81c000700070503c1e43c45000001b105240781d81034581c00c1c1c40422182c0401c1c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 818083111 1250 818081861 818081863
    0x6071a0a020c1504021c0302061614030c070314160201110c03030a051602030d080a0507090e0403050918010b070b060306090c0d0303060f09050f09010623010306050d0f021002 77
    0x390184011400601d60382401150b00d5070703091000f0340100e0303010b404a486d2281d6044041d00d81c110705402a00948a00c1c6481580b5510703041c02e000e0f10008020404115403e43d131049002e494111819211103900d4403000d180c00d4407910f1400f03a504000311f401152011444448413540b44804c0c0c400e99a900840031040b85640d941d1152282040c2e1507082230140070ba44034401c402500d00d041c00c07050101c01d076a10307540120303040002c024a0700700090035840c00c2180d4080d0074045c0e141c1042c05440c0550519107400c0420030300010148c801810040001a1100917035209060303081c0ca04990307180c01283d941c1d41c00180c1c255502c500703001c854031000800040c210381380201e851445040b64030040d100c040c04400403c0320580c10f26104030180740c0e50b101e001c10848031440f4100e0150554034000202418501040c02e00008020008522681840c0040c403c032580c0c040741000d0352500708200044012007800503800780c056604130795007008070b0700714113418400c10088442d1f201c1d00a031a5081c811640803012 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 818084361 1250 818083111 818083117
    0x160519030c05060901090f0b040e07050304170a1205070905101106010e090304030c0801021b1b060309011808130503060403050412060207050f1501060c0203070b0d02070206071a0a02 80
    0x241c200c050000041000303060403402071054400c149840280c942d181c0e202c40702c04840b560081c540790740c0003040600c070206003140802d400c02d1150410a0462900b542d0b9200c4425201241c0d1850300382c04590031104501940106501c0e0032204000e100d03034074003448000e000c80d50b10702c2191300c6480c415096070441805a4000c3c0138071010f0384041c0030681e0030640e80f015907000161444529100802c000400b0444c01303982c004c00760085900150717403020140b081c40e144041e40791040c805900400462902802c5903c140d01c8840c800303641882e2130759503070108140140110b449220079800303d4076a81c0d0030410140300030000c40e1490700c2c84035170550300c50040c1a55603100f01c50040c04554104804d1100300000b40c1d10203070040c81080f002d80350010719030301d080c03c0180013a0000001d9020403900c0004184042e652030142c9030510b0030b90001d560f2900020b070354907400d1184281d8100002545003010b40282c0488504540252a032a904c848500d81000300340400f2594901041c01003001c509400000e00031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 818085611 1250 818084361 818084363
    0xe0f07050d110f03030403080307090501031409030904090c1511071401020303070309061b080906070305060105071104090804300201120b012a050106050603100614090316051903 78
    0x2541c2d80000506050000280802802d03e90510082c000000080d03d0031000b544286010750710800d540c1d01d44030014098a0311104d506a070301c180c00302007000040300082503c40c641400c443c041a901c2c003505200510025540001c80501c1080c080171a40740c0c2c000343c1003200800c401040395180c903643c0300d40141c00074041c040240141c008001040d4141d21a41100140d90f0107514000b60340300c107a040748240390415401c4e0001003446201044074808003440425070000250130b0600c00c9141510000300f10740329103140200380203103035098101c0c192180d40c8a40c0c04190310180d02c40d0703526100c01032203103182060288120b600e0388450703050440407070b41466036250580c183c40e500100c0b401312003144d01605079403090504200040e480e0305009040c480024006142c00c2d5034800c00c0d0407613400c155094500359009240542c2d400c0060018181c40000e405040b01e41514152280030800ea8100186100d4403400702e600d441155007800d40745260b10620011160704541300c1c209030300d641956800354685440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 818086861 1250 818085611 818085623
    0xc0102072f010c21030f14010b0912010b090901090209010f08101e0920030615060f120403050d0525080601030216050c01080c0f04060e0607060e0f07050d 68
    0x211107803265000351881c80c40c0600c1950303005180103981d0303001c410021100c0308580000340c8410aa002c001268421200b4006a141c128440e80d814110140e816100b804d4416003d400300500d4900743c400f0070350094a0101d00107102d40c4450501c00400c9001c0d00840d00d069201c2d541030030000485605110303000c002c41c0e007514041d0030745031050481c510042ca01c90424484086031000407244507152403249a228030312500618480c41c1540c90030b060b80040b101d003440d02076031043e403c0c00180e2400c540621a5040202d82d8195034045003941c50000d03002da0300c490300d1801c41c240f092100301604000a0a0004440340e4108840e41d00c10024107a110900341c490641d004261130a8100729200e201c00c030381c1c03003541810007520781004010903121001c14000203446070341003c1c1100400790381c01440c0d0342e004016960500e00307103d0b20414071411403003a0b100300018814000648180360300d50000f510b02507900820304120451550000325119011040d0f4080d1038005d5080c0440d8030315020003007000c0c5070b40042d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 818088111 1250 818086861 818086943
    0x30a0905031f180506070206040302060c040506040b1e04030b1501030c05180a1220103603060c090b19031d030a210b060d0c12020c010207 61
    0x180400e0020b1003003c460000d800111800c1c003010902c01c2080703c0c01841964000d2106241c6828001d04001016022051300c0e001040304010700c3d070703030b03e0145c40c2030b0f074419104259200da03200b03407600110300040300c1c1c1c0e8414640450004144040500007600c28000c207030300500209043c03401141100c0c400310008000c6070341440a0707420f0b10095070f40d0b0300c01d800024050a030396586861199615044200c0c2c100d4410300030070120031860046280b403da00e100103540001000c205c5503005000040010610500569085d0400305410521a051000984408454020381d5180e08041d40a0210003034018081007401134006501c0c1440b00403210b51150032a00c3c401038450101c0100c0252540c42064032a001c00c424580400b00b00510050100c098692070751000c1030209581c9241b610b1700400c50f081520b00d0214503079200c0c3c0b912001c0b00c0c88040284400600e51070041400e4549a501c154114081440402c1e406000481580141301080c001d0603071341d16905030102c83d0280c002403640040d112004903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 818089361 1250 818088111 818088163
    0xa060609050d080d0e01020c0a030e040c02031603031407050a0e2e030603051b100206090a1205071203200304080a05071505070320130b0d0617030a090503 68
    0x740c3d0142a0070f4455680116019480c480349509980000319201a6034010820340070403d60000da00e203069070341c00d842c1400f0f691020300b0065100d00452160000f549485900142014420b50007021a8140c081420046040c104001090740c0c000c0c403122008180080310782c0c0d5092608203008540b80e1803400700030340e021315005049240d0140c061490001d064680e0400700009400784944048030f00c460b402040003414140c100050f8068126189081d504002d0034459959004240c44900c150050760303030f2100000d04c1c84202e89603c600c45000d0118091601c64000307071399064210b03180c01d103580c80078003090240740320303041c9028030058800400f100c90810034120140d01030700141c100c8038020000380c030540084401500c01c2da0400c8600c40300180d6603120b00741e0000c03104403a03c00400c002c4d80b20241040380d0406e03d0203104800e80a0940038540c0810300c50070b0180960426030291001503006160b241640c00103a580e60803000c1d076140415115400440e5509000460321002c0b802030300d410409140d5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 818090611 1250 818089361 818089373
    0x70b07170604020a02121602040506120d0302131806080f030a0c02090403090f0b0306100f170c1c0608010c030207030203030c180d0f140628061d0a060609050d 70
    0x40040346130154041c00c44030b00a209403100150081d0000349608a980c05414810042259130060010b44120102c00341503455000000d4601030a11090a00680c2c81d103c047c0d400080c800c01354000390340d10349203107070f031622812030398110300c045400505c1254006a000f50120b912406021480c8001868204403000036140580c4442d422038000e00f0100d07241900c50006c4c98850900c0d4003e032075103485c00030900c211810134240b8418507c0242c94a88a5812075020003030042901e04282c00002001d00c0114032400103002c100c800d0707005a18131200700b00750307a40c013444042c02f01840390440039443c080310034809034001d000700d41c01c0c00c6d4140c1c00ba41c60750342c580c10020003c0c2c02c080c4004181032416400ca445980b603078550102d8060090200800e002c40301c1c6800070f40d084001440140742e4008609002c0e802c01c54000b02d14400c0c0744069040806514a078028004007455400022643c5540700100c1307940c51004c1c00d0340d000b007081c910700748030f42500c450b01603c215032107104064115482000301004654 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 818091861 1250 818090611 818090617
    0x30512010f080d031509060b1810140a0e032a0906090412090807091a1f0309020d0c030606060210021336050613060b032712070b0717060402 62
    0x600b40d1000541e482d2140101e801f100c003142c00100300d0500009030f80c3c803a10f22103d124651858215860468819103480c01800c0840c1c2e003103021366031074000c07a00840342801024400480d100107030490781000c064985010060010000781d500d5000308a070716000e18100710644501c82c56020740382040b2600e82e0713901c1c01d0b5201818100300b01004408a00400c2c2c204007445210010013116030040713440590300e0203070042003407440200c500c18840340800f0482d00d00f90101580c101482414000383c01c2421b400403a0402c1103c10009181180c1088040100180d0384c1c003c0090b03030030079421030381c070a005603d02c0c0040f0b00c0b54040714003210401580401c021505150b00e0313800031a040340d501c2c12040310940451007600c080e904c0c060740c2c4d946a400b00320144c18540c840d0300350b030300c24007000f40004d5190041c844940c1c400a004000000e1a40c1c500c803980c040f10140c445400c5d00300004031603543c5d00400740200150442d01b0110f41c844000c0000c00e6541e44140040822111071811945080c0c88180410000f58 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 818093111 1250 818091861 818091881
    0x1b07050a0503130e01090e070b0d060b0d050a0621020d02182a071e030504030f0303020405041109031b2b02040b0d050706180b07030512010f080d03 65
    0x84609020303040060018005415030020003400071084509103140c42d0641c45050b0001658603140010085040c2e000081c40400c440c1c444c005247d1700e034030803240100030380b1290708005150078000601c2c010600185c1e01c040e11407001380310300f040a60780342c082401031909003c282002c03202c002c203a0580580381c4810038490032072006191121400581550314041c2030300701d4080d8450052408031280c0f904040b168520300119962040c0e140142d903a5908040340901c25130ad03600c0c0171102c011901058021740444d0061074010240000b6002d407850b00a0280d40302c1e018031809542444400340200e44507006444c000d8000a001d041c0e40c503007070248104080414081194027402d00c000883e1460303a020094240c80724114034164010001d40140007c1e84d251810650007800c000300c02c100031034030205880003a41d01c94a0510112017071018640340201c0a03800001c4002000505001090340101c01072803003100640c800a40350b0382e15025003109415038400c81400b500104c0c59421420700c42e41c4441644 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 818094361 1250 818093111 818093113
    0xf06030a05130f0506150a06020a0b060604050301090510150b0d0209030a23061006090501051c02030c070308130308011a1201081f060f050112291005031b0705 70
    0x3039085440d0002440c0b500d1400744d5580c2c01039014400c24520b07800102400440503210000c0302840c6c804001e540341202039016003c1030541011a40c2030382e07400c086a00405c40100280203030f20440c2803250b00c40c814102c02c4040546071201340d020030740004211804403900c15084030b06044c02070401d20f019500420b00075526000d49140c60000400e00b882c0202800c1c10701ca80a406845c524070107a00e0420f02604145031038110030010045194000c0c41784069410030310303009458080803002603400845c400c0241d07045a001008018480c1c1d40d007000782816074069030344c0c000780340c89190108112079166603000d0001903555005002207100140e0106a08485407440c0745090615010300702c10003401e030000c03401a000b026102c0440020f440101520022540040012500c1c00480036206200f500c07601d4140251480102d0306120b45a01050400c400d00302d9010924180c04045010a00c1209509202d880003104400d001da11803000c1d02d1151040c040c0603c44045051a160015080480d0494003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 818095611 1250 818094361 818094391
    0x27020a050d08131e0602120703180f0303030c1b05060c1605060a020a140a0f081306020d050601090b1606021303051902010f08040b070804051e0304080c0f06030a05 72
    0x3000180320200c00c0100708405620118030905800132000d42d080d9070141e02154070001c04030219045034400c8540c05603250415054104112440a100f42907a07403000044800d8004000245605904420192275281c2d1310141140c060701903141e901074040d107025040307921610000310079084440040182c503000b010400f0301c00a103540d0700c61414004840c0203000c503402003051003005070070802d0b402058441c0020340d0300f030810700d4a0081285811917907580401060402013064200c00c00c17460380d40c1980002065588011120b0050003030031060303504900042c100c0031300049034030900e01514400d10741400c1c00401d01c0019202c24000c2e4000001d601913010541c2d200000080b820440742030b0049e031104034410701ca4240d000141103070540003030800074804170400308400981c40c8511540d001040f07042c514803d46540c24518540b105100003801c1d401668005030700001d00c000040c10032075042404a46825001d4002e01c07000700c1910810641011042c0003107500106141c0106034002c0f5800c680c101c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 818096861 1250 818095611 818095627
    0x1e09080304031a13050a0b04020d02060415080106020f030f07110316060905030a110112140711240c1b030d020d0e1c030e01090206030a27020a050d08 66
    0x20840d4419402261901144a0f4004080300d465001c81c0d80314504200f4040781041d40d4459544641c1207080007400c4624450000e411540c0e407841d040b038135540103001c0e02d4a4984402001e907464044444030408103908074000a8810f20000b080e40c00031040902950030501400300400d865040f2540072180c50043c01ca80c80360300c0c1c074100078803a0021061801030f10032920701071010b0100185034000c2c6000e50030a20103034012410248451052400a10700301c0c420150040d145801021046821a114003210b001d0003400303a031204000725115020001d9800c102c0e14103000703918508001a0401c0ca1640c0036000800703c000c0d510292001c480c145040d8021007010850300741c25a0300500310303044042c1c1d0200c0e5801c8403941910550b01440550b200611028403450f04c1d078000064801c03080c00400d61181d01c2c0d40d01e0a607007900642d844a5028101a0704d034201100c022001d0300401498402001c01175081e41201011503600e188000d4001d00349245040c281014000311400015040ea0640b0b0708000f041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 818098111 1250 818096861 818096863
    0x105070516230d20060915091003060602070501080a020c01090605010816120201140f040b0711060a14030604060b04031110080c0304150b09090c0f04021810091d04020a06080103031e0908 82
    0x7c0544030942160300c0d82c800b211000c0002840d00b40040204251824030180945500082d0040948030f00b400c1010079655078100c030b000a4805e0b1207034095194208401074040004a8000c41d06aa9100341034404807104014424400a20b86c0302d00102001407000c3c603009540101c0360041466010120a49050080e4042203481d900990041d038100c6400501001400300d813244000e11a40d040b22202c1c9003040f13074103000b0118000d039004481108400404128107581b5588482c00030110310151035101c40da24245030380c40601c54807816000d1400c0404408001c0e1044500a1160700c4042006040d40c44689038404070340801440943c0701d6581e45a403121a603214803400348102c0c03044009000d403901690030701040502d2440ca41d4000c1e0300510100c98a540d4414580d1751414040c0c488600484068000322071003113603644040500b500c0400030440124034404080d10a070700988090204994560007150262001d200c0900020410700d80e6a01d000802c0020201d08130042c0f03044101151034100079 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 818099361 1250 818098111 818098129
    0x40e0d0c113003040f03080d0f0c05160809120a03031103010807170c0904080706050c0909150406030c0b07030305240105070516230d200609 62
    0xa94045500c103000c050801c11440d210200c40d500075141c68011200c482c1c41c0300324507200002650740102a40c0d504070000c2e04100203580c02004402c21555899549040c00c8400398800d0410301c0000b42041080305071000140906000b104083d601d540c604030181c034440c00c0a103081d56044403034180800907203074180d40c0e060840c03010a0030500a1b0402184514002d01101d1480201c040c0c4204184010486000041101c2c01200d60119079172000034000442107060081440f001d5900540d0441400103000c07800b00a030150030b1050300c0c204840c0d00c503c1e81d204000c2c024126000d42c07202820001039503c41300c000b4508400880a800480c07840c1d226503915600d490150054003d80e4800301d001424958540586608a101c1008401100d805450321008185981c01507034180a80000c0c09030420000308903c201089002c07a070104926150500340c020321809c40300c061060007a61403000590b01c0c111b0b070440c4c4181d40c48400306036080982030100009c1c140c441e910b203a01440070b005015460f200c00d011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 818100611 1250 818099361 818099383
    0x15040203010603050601020d0806030d05070c0f08061e0609040215160803060a09200715180c080615190e0f01031b0305031c020706290103021204060b040e 68
    0x4c140342c540b0400080c904080e00b07c1d480104003501c4240f004e25180800c10521180703161801c940d84450390b0512080000140d804660580408480003500250101d00540074034844501c10310041100748040000142c1034540c01d90207196a00498011b142400d00c0c1c0298a200624660401c5e000614841c82844800c400703540900303000081001524140d448480036010f004410002a41035000801001c43d1810000340c103c2c07000181c210500800d144100304407100c44e1820b01101c5154800d282544101c00821100c0307041c07005000c10150390108405103d0144a40140d490345840703000c00600019804030600403881002000c10310506030700d6054410050314088450302c3d4514a000b151a25080d83c160030010248041400021000300072074200d80380700c2203400d4400010b0910240244200f00b402000366142414650b24056104104030200e0414020a204103100e080150103030312038000021b04283c80440002c00150703445d8803104070b401010380001003028103641203030310f0b26129401d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 818101861 1250 818100611 818100617
    0xc05072303060709210c05040f0b0a060f020d0e032d0304060323010806150103112d030603030a1809050c0d0f0207110d020f100e0a120309030b150402030106 69
    0x81805441070601420320400c0920301d01740c0c0c1120450b121312100c0324040c041c080c07199440f0448801e809095030020400144020115030506654680c05021a108003034550f000d80075420240d14110300444030442d407903001074094282c9020122648041c00b24100076041e2544065515082d8981d00f0005440030b8005900c000840c0403c03182864a071003d412018400c500c3c00c04014071210300b000c955a9044071080760341c040c405500038016000303400a605001c02e903107404074001030010b48581c06650115121055011980c070303040f400410301c0c441160006d41581c004c006d1118030030f00c10a01c2d0b0b0f0f00c007048a890310301e000b52180030701c1094820a48040011030008115050581d86078403820407201242181149004503950320540b41c08144296244510181424003056482c0e400b0b01c1516080020101e610301c203200c8030081d1010300f0b03002400c0d00072154884007007000391500c00100b20541e0103446080201e40340d6501c10b442d1050080c8440d045021008400803c1e403518009103001e84000e072 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 818103111 1250 818101861 818101877
    0x90a14040f051f08120a08090102091e04050601030c02120d1b0509010f03060f0e060111060a0522050a060b0102120d020d0506091501080702010e03041e05010c050723030607 76
    0x1403400040541110599400154200304040d900b00200c0706c564040f82840042d540e180000c40d0b009000341c140d440e400c265030a03d04540040c0100b4140300d05041120b0400050711a50011021141d0740302e05180540c0c008880c042114035240c0140610000c03000020980000c1e840b9400c8803500d44103220404948089050f145035130700070941c02c0c102c903c50300d410000540b5040c18665010030038030030400c50006480c0810000d0348943e0850300c20003c02001c943d0b103402c1100564001704000c0b42c46044d016640140380300203138030b44254015403030b400c0802061135071400c2e1030751030080c01115a00d50541c407032280c074029064145405000303c081c40303c40050b15402030007031400a9880041403c1d204951505c1007040c41d42141c030090031241020b10f0204d0300c81d5541c00c0c0c1a4014841031041e86100c3c0300214002800faa051094001400da42e0801203500b240e80360300555102e542084001c04a8120035824000c0c81e444a080404541c1c0c1b032501c00a4039040380000c00d040040540e28900069030300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 818104361 1250 818103111 818103151
    0xa05060a050f091b0f030a0c03020a06030c05030c2203080a031104030201120b01020c0a0f0f171e07090509010509010e03090105040e0a0902100c0b0606090a14040f05 73
    0x511840754401c405820300500c070303e0184226600c51540349126800303207402810316004c0b512001c810702d05000c005000c40d010540c050601e41068003003440201d10505084501194035882406807030614481922641d096031105600115150400107948000001d048613048201303120a04c0e4000550144442a64600c810440101035840c495104100c941040200700700603640f1940141800705845c000003060107070000100d081a0b40380680690090300381c880452201c420342c82500856070f80007440242070303540340d20907100207141c09030203082500b0100d4031403000d01010700300301c544040700800d4a84a5031201e0560302154016211b12125a64500400807681c038244542101444500d00450a014408000803c00e103e5405000d00c003588230350101e4590555500312800c4240d000f0840710250383c0780c0358000c1070184520401e4480c0d102550100b040303400d0000488000c103401802000c8003500307103988102c41001c00e05103280c11a903034031001c4151070860f110300f0b4003a00102052246c00903036 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 818105611 1250 818104361 818104381
    0x712050a030b0a0608060108190f06090e061506030901061509140d080301141212210c03010909021c06051608090601120311060f1803030f041b0302030a0506 69
    0x1d46494240540034401d4113200d00713508114030715030000007482c20b14507640e20031103181442056040c0502d401c034208072110080d41d00f035400400139240d4403001081070010380911b02d66074501c143e41c01466580b152280050314103205c0c3c01154416680fa0010407007503642c61035403402c000c2c0d000c8060700041035514180100080320b01d03800e10400e0304569680003034010340c40b8890944011302c691802c0040e148101031303c907101c02405075504410349040d00d00102260060040c55802050003442d17254810405c11041107a4110350f5008080040005040d43e080024040080ca08071105030381c448807940c0610201c400008226200d603101d0040818103003008030601c4648912800b5070410300900d4010000b40b000001000c0b0304641c04515600c4049407581030968079444000e10340341d040e0040c01b080105110904504600894580e07442e02c0e0030107002ca00d596200d0006031010740111414030041008a5904030340b0014112082c0000e40303100b50b40e540028075144d000a0201c82da6001141000b280000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 818106861 1250 818105611 818105621
    0x150a050103110f031e120301080a14160b0a1716081608060904260c0705120a0f02060f0a0804060b0d05072d06030b0f0307060c0b0402060712050a03 65
    0xb0080d1940c9500c40072160001e038880d0b50b14100c4440340c0110800e915800042003100341c0c80c0041d0a9441c590341c1d43c5070181181c4030359107624141c400300200c0111320b0101000051191024039807041021040b800d0405a83c40c55010403101000c00c00000e41d404545c50b07041000600070010003a162060309100d04010749500001011a0078601c181158144080e403c6001e0701e034018030468184285179540c3c9014000100b40340c41e4420612816201e20b14140308960082025074414022200c0c6250b40d40100903400f030704c190801415400c82d1400780001007603c40b8600c0341c580b000301894181180c202c0b030781040b904850407800001f03110300c0a00060028034420700d00107800c1641c802c1d49004080d203905680d208180f11f080b4090b00c0e01d00c1485400c858482400c4c42c00070800040700d0720740340d9411008000d813030012138151040402040a0b4118600060040101c44050315012070003006d54543c40b241c000b00170030070307600709100308810800500080c00720324003400140c071282d4640809080c010f0440b4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 818108111 1250 818106861 818106893
    0x9150e010f050c0f090918190c080706051c0605040f2c070b03070c0f140f07030b0a0903050c01060b13090c020a02040f0906111b120912150a050103 65
    0x1601003040c040102d25000072030703c5c070500c20381d45504030b91582c664101400d06015104012406101c1310a001801c0c05440685014000c1a000070b015440b40b090300d864450600c074005c00715000b0018010a810f440345c40c00d032801d108000000d407841e1344001050503104803000d504882561002100c4050b00700781d41d60014101428100109042e1401c10300b40e03140d03a00c0c0100c00e83e206c0c1c003000045074a03108a124299003036014580408d410801c2ca40398072900c09460350a8071601861403000207200d0001805400c4030740203100a50107496114420b402408a1041036040000801c00c0c012500800d026080c020b1a1a401144c1c0d604600590550700602680200da0014105021140c0c0b05500203903001040380c040700c001130804896800c12008250700800240114101410340c003400e02c2d02c1019100702400804506946501c481c003041e150369a00190751002a0301780202d40290600c040c01041d50071082080301c50001c4014030401e042d44049901540301510790005104014001c22014101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 818109361 1250 818108111 818108131
    0xa0b090f161503090f0f050102040e0106050304051011120f010e0c130915090f0506010e010c05120c0a082205090105090a1a0630010b0a0309150e010f05 67
    0x242062102003010074021030702c80c101519040403806102070384019072200e99000d0f0344002aa42c1c180340060103034000d0701c00c40d10350000820000420703d01600840b440303547e12070042c141000d581a41d0000030a180420340401c050706000c04602d044400210fa0b005500c4581c065020798540185041a00d05c02012040c0180091101c2c18000580d080740c0c206450760540d02103589100302503a81000000b0345c1c80000781702d0801c4030031558010f40740d100e44d018650aa0320000c420100d0b20064514070b042c44002403030342d07010740e40c500311000c04c0001800210821006035071072403095450344201d40c0c08c005280f00001881120482c501e004c642c0000c0010f100941c1c511841e5131400c00040c5c4a504001c22040080d520380031f08016544108051000ca00d038002c10468a421030300001045050000c40303902c2c00303121b002551002e0300d101401003504a501c00b9460610308010a0703c12409021150b804484c0114070300c045000c1b0241d03034050711000d85440000052907409010b083c0c000e498000c0c01d5003940d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 818110611 1250 818109361 818109403
    0x11010509091503010b13020705010606030506030a06180204060305070f09060e0c090d080309010f060e1302010f03090c1512290307080105070816080105010f08090a0b090f 75
    0x41e4a4840744140c1c06904032035a20325401c4400082405001030014640d803200e1070003c030000301070f421b9000d03040084c0070307034020481399441d8081a0210b41c410340c0c82d1a4941c1c49018045c0018405070414901440010007081001c1b580e03502107420350b465030308102c0d5190080301d002e1100e400010351000c01003000c40c030140a00b510b003c030200850400944510b1000d040003a1411940c2c54950405403182d0b4000c155a90300d00c3e01c0030000e4000c0c0600789034881180c0c1000030004006084450b030324001c03010351001e1269050258010350b002042c5503800320606841300d201501182e040d204820040100030545910141403840c01014030071500b0f680c1d072101c0d241c582040507901800108050701004100f50380740d11301074030001074503040e410b60148481c0e600b040304021003c1d83c0000c0c100e008103054900f841c0724000d045800e840c001e509010b80340c00030b20a00c01c21140c55109469494101000c41300303584000c00b65440e03190200d00212440541507116501c6070000d0b40d01008114200c42810f011120 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 818111861 1250 818110611 818110627
    0x2030705071205070b1005040e010e2815020702040b04150302091008030f07050c030a08030604090f02062701090503060415141303030b0607031b03030e1207110105 72
    0x28000c2003405002c090141a200701d0050091045500382500122140c01e18034240118014241c0c96025090182d410658040001c4005000304041e00318004060110b50340340c12603161080780c030824401140a03803011a1404a5814460400b0440700310318056550030740c500601065811800402c2e029910340691f803540317145014001c40c00e070703030303040301c40d0451030b21030302002c2680c0c251a4000e00f00390f020008148131082c1600005000302d80c0b2030002d0b80e075520204020103441e40814031001c1c11182c4204009070a5103040c0d40700942c102d00c1481c03103005046050300410f40c42c1c0c00c490b081050070280030500420001e440c50f19502480d500b46850200c5604007008203860b60f20203440203144901c030100111940c3d07852b800c007242e128a010b18545a525001e42e04c0350b22951081020b8000c0313458804045028242a003c50b1490b80e0141c07a40c5065000009181060b40c00c591829410075a4032860507a09010a204803030901c0d20541c011b43c1c48124138100007002e070b241c031542641484401c100c208 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 818113111 1250 818111861 818111867
    0xa061710090203012306120a1a10032a0819080f09030a080301170303060a0b071a190510060f2006010f15030504170a05040504050c0715020307 63
    0x1803040c44451801049404040c800309001d00304042d00c030500c3d0f2070440d621422090f020b40c01948101e0b4101d50013881c00081c618803603110b8861003005405c150032201d4030b2a80321103e450700f82d044080506000046640c0c1d84500d00010310001c80605082c402a440342e0202200d05628400f500031f8001030103941540410f280d022015200c40105606404201d4001d001901d07000d591034802c020703080d24035000c01031400030300c968424040c0d42c0b01044400030b40b0894110000913039100301e03009008402c1cac06003000202c06642c1c00400080790000c5e07494000c003051514a0500601034500c17141c6c80400d008011604d441036801c003c000c0f14402d10446030402c190780d44915244900d8800d414814400050144500d003c104006101d07034280c400e80000007810760059404004580790061205082001c1701c500f2016900244c0f000350942e000c248003c80141c01d00310041c0300249680c01c02c240391940d1000805e041d1041111400310f90740c03000c5180381c00d1004d0200341200040090f2001c52651811003006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 818114361 1250 818113111 818113123
    0x9020315040c0f03090f06050702010504120203030f010608090f010c0509030c060708040302090903040806091c030e06010b03100f030c03030207050616060209040f0516020c03032b110a0201050a0617 87
    0x43c0030940c80d917480005000d1000d00811040750000f10503c0f8514044101a020744015542154101030035480810a144040180d80c0034441030f5130005010b0b440c0000489845101401c68403090240a400056480e000d2150817651005510380a48031030340901018142503a044c48035019180030004400041c1241084805036541244e1042c11038589511080c60741c09942c0101d061840394006020500400143c40e284421b1508481741c4582c0707401400310203a034680201c01d60154840780043c845800c0d10030107581d0169269404111441e9166145510556a40e00603101070728041800c0c802c0c1a818000d200c090241601d07a90f2400d00c1c40074029021800d03004001d050700b40e01096001540d503498219001d8070190071400d021605199001c40d810b1459881036201510510750b84c3e43c1d00c0d08011060303a080035403070740d081000030402904080ba0f03c03820003003440840b5030707410a140204600c00040c02440c0c0c40380d400002c081c90318220300030403203890790461030003c00350780306500b1002c40c00945 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 818115611 1250 818114361 818114387
    0x20708060109050903071e02090a060e04020f040f0614150c030406050c0c06031e1803071e0503040605070309050306040210120605150c07170604230709020315040c 72
    0x250f207a6403100b09500b1401942d5004241c1d8040310503281c070303610014032034500b07050084501004548980f8122002c50b000c91149403401e08040c3c0004016150481240c0200b64029101241021050b240c8904940a6030016600c030108030307060001500b4181080307003262000910152a100000400750b40c0c0e80128401c01007003140004075400c20490a01c02640c41c254081c102c0303900c900b46040c07110f052134045031203801d81112010010b480c074a035402401c0039076095240514a00f44942d12036202c1280d200703905144411084c410f050004000f04000c10080c0400e44e222074940f00d44e4a0010104026940000e110340c0c449014000983c0e100b00202c13000101d0360401030b4041c50a90444000b4211a0713024640c0300d03248900c50442c50b16000c00505441c107414096541080c0c8814a80729800c1303420862032040d600110004001650b41110320349000101030042e5007880e100d9410910b0095960884031000f5008828400011640d04100040000807502400100032410004140b0890081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 818116861 1250 818115611 818115629
    0x30e0405180313090f06050102150711100b1008071b061509090c0801060501080f04050f0708241009090819020d0305070503092808070503072d06020a050f13060f0207080601 76
    0x201140406006e0204d0107640c59511042c0c41e21000500d5180d0000c100507264ec0d80141410103c800c5241e00c550b048521842d1366444515061078041c0d5040100903520804070303030280d40c80842c0380c005031600740700340c0042040d400c000c6124035491522081140242e4400b08060f070610505000680e04800300340d0b4441e4403098000910768035400c08a180c400301c1c00014005014045d000301745400085030b4100b00d42480d0b000e10f07907a0905201c40e000c440d102203036120188480020140b0a9100e150400c040403401510300da400c0181781c59640c1403c41c17000c8080303005a0b00051600b2900c43c5c050091035881044c82c1841d5007903182103050980c4030301214410203044a082804030224001040b8600d05a98000c120309842d00c0342403611035600da10142c4151840d0031082c0702d4080c0460030340c1e000d82a03101c1d000150134602556649440194100d18005800c3c01000e0100400c0481e010f40600620040d084204e00000c1c58507c020701743c0300c4400f2100f01107400c001000e1080304000282036044404180c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 818118111 1250 818116861 818116903
    0x260d02030f0715051e0702161503140708010e16020a02040b0a080f0604060b0a150e060714010219080c25051f05070507030e0405180313090f06050102 66
    0x4940320066840c001411443e0303e180100b80102d80101c0801d00345241406000c0141d15183c80d04203a80d100300b180803003c500d810300c4030180302820f90302c890001c0081c80c44c1408510603240740040e51044d54101d0301074002401460040000030000ea0403641c101003d104400580710155000a44504440e03101a0280d44c490b080c00c2016118074080e400240f59580503108031480c2400c0d02512803100b5201640d40714100200d16659140c120302e40b2044941c8901060711000d81000d059406c40445004181e001b0760510139000400c4200720082c0a01e5002000181c2c1ca0800001307940d2400c1080500008010b584000c11403442025000c681000702c00c03215180869481d518001143c80d0031840c0181140030340c0b4554070f075042481c01e00409561401405000300e0380d501400f00e40c0b5001706100070300001c01281341444903082c20f030701190b00880014181d8850304a48c0ca56180b07140d102d1940c1480003640c00800b000703852682d2007840c065280781c1301e00340003180c03600000030b59810031240313a40c807040500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 818119361 1250 818118111 818118113
    0x10603020c0703080c0c0310051006231305130524031009120f02190b180d0e0102070b03010503070317070506090604121e030e01060f260d02030f07 65
    0x10400b07540155403009005607a04031582d041da8641140501d003a00034800c5c2607120100700c4450107814403e10106807885a814074054049489401c101c142c01011034104040d400c41005090003000c0700c001c20842204d80c075191500340b040e00c030b80202c1c0d8190701d145017209004c03421600d007060904025000041c800082c030818002800c140e07064801c80010b500d0090303d6400c120b502102507061803003c1e15950800600a0390503038484050f2683e541c04418024905c20004040700c1209400c602a44009080648540a403500c1c05580c4036040780490b1b440940340641d50707810002c0502821a184a89085500d0030000c6540c40e80c0601004203100c0204600552402452059440d0103810508880c80c40c101a805991204015070f016212002c0c6556022040d5028404160040d02c04ca09082090104244200c0040c4090390210007a55200c0c2000110000ca81e4481000b40241c2c002e03c8025801c148141040054031840202e4241c0226000703540320358011041e22969030380d6426256030303a0740c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 818120611 1250 818119361 818119363
    0x1120b060909040c080d05040303052703030c1515010e040e0336040b010512150a080102040e160801030b071b0602030906060f1c0507241b0b010603020c 67
    0x140e210071503009070100007000b0502c8680301000c000c0320070f140e00341c17900c0300c001c04c4080303520b445940400b60203c3c0042105000354070b00342c001c3c44030030019548000e0900440c0d100090540e840382402001640c000e20207013220070647c3c030285030491100017000522801c41c2002030000a100383c2003604c0b40b6035038601d0411510342401100e400e1040c84103842066003040340d641c40840410341c54040071012500d80407440f414184203984202c1d078147c407414180010b00c8843c500030480180310540360340c204615a0410780700c41600c032000e04030760030015842d20b00380101c100320803c004000d01980301000031010200b9411220b4181583d800c03244420550b82e2300700c1c1c00d6900140c4400386400f100c03940d000500511506601940c09582250b0543d0500c1d168041041010002c000000c0c2d84481414003111090007042c1424101074803400580f01e04990782d89402c24601401407081d1200b400c041c1d24600c43d20f030f001c003080d24210b0a02412900301d5504d61190700342024140503000505500040025403108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 818121861 1250 818120611 818120617
    0x120c0909010f06120506070806011e020a08031014060403020901180204180e010c0908032b14070f05070c05064905011802070c3b0601120b06 62
    0x95006007840481e135108100d080180811000751403500410b0080742c54580f00d800e0007402004169141548a4580c0158076003080164480c0010340c81000c213101c002840b504041e62164120010303540d581e92130410f081e41c41c5920b8955652180780100014401a03660300d42c0a07040d40c0d203881c82e0421103c59103690b80000c0c81682c010034075001d40a98000b074106080c4d0806000c01032031800a010700390752035106546003220750140600582062000b40c0c3c0080091143c007500ba5a00001c00d0700d01076034048248116070b13140c0715007011040c80508110b411a08181855001d1025180c82440c0c5111510b075007807241e10602406104d40c5000881c00f65040406281108684a460101c4400e903444088202c0c400e26071500729840c01401c032000f00d0761500500c50380e8129040c9003540020f440011102030000c0d80031081c101e0340c0301002c03070021070101032144110a80b040c01c0000a4580440f00d00710005a014095001c01040003403010031030140d03402490341c24880407040020440300568000130342240 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 818123111 1250 818121861 818121881
    0x30c07082b0603170c1e0a0c09020306090f0c09040c0e03100608070b04141c08120708310512121006052113020a080303040c05120c090901 61
    0x128007002400000c0001e075005100b00c0b4429421203122100e03903580e981c040c4c040d418030001c450b0803d01c841404107503001d2610742030305041c1d02038440b00300b41da50710003010708400d0304076050141d40401007191b9410580006908800781d144481d9151805019075401d503c610b502c1d603801541c40e000c2c409c42071b90281100c400c5c603030401003d85180082150001e0300400c4580300d4014184500e40e000200000381e881140c0c1514566214008481089024450311010300412941158608004000800d1900001e04091140c01485001a082c20034000b08000b2015013071211400c4111002c83c5000c10822004080ca2620380003c80313503d00c28280a230a040381055402e000d00c10000e107003481d0501030742c030140c440d044801d2500e603d2038031074400700c0e51030007000d0081001e6240c00300031880c40210300b44580c2d4041080c54070400f407800590f0200d41210a20380c0080040d510100500c41000740381840c0784003419066841c900011900501c20381d440c41c00c01240307800340b034451380440c0360300c242908031540b08 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 818124361 1250 818123111 818123167
    0xe0a1104170a0501060510090303050f040b07030804060606030b0f131103011707080727110706092a05010f031503030807110601060c060e0c0d0305090f0303030c0708 73
    0x210001c903a95600c030b11082c0c1d07080b0b80315483d22001048510b0603003070104140c9503680d980f4504031b0035541c0c203488541c0641d25000d43d200003408000b60404021005045c4544680c1e20410349040c03c7c6401829071b074aa0308403405050034214000015101e0202910548504440000302449111000801400a03100c9800014000030001c90540002905130612090403401c0342c4400780e0b20451603071134285500440e00c900800e000c110344484100e010944504500500000302c56582d421102c003d5030000804685403074841215005001d0012607824404084404002c4d24807030039986200940c0c80f40c040c10303040c0103200150500d443e2195128006000e01070404421958581c00c002d4400c00049078910000780d81c1c1840c040745103402003101c0e81243c2c10b030746500c0c500612a030756030405044c40006e90b10300b5100d5081c12890f0f942d142d101e01da404d54082d45920341e0319966001445452502c0480c0301d4003e034003c00511284030a071500301d414240d08820101d4940100050f081404180f07200e8031000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 818125611 1250 818124361 818124389
    0x21b0103090614070f0e10081e10050103110c0a031d06031003020f0604140f0414131209031509050106180f0606110604030f020f0316020405010f0e0a1104 68
    0x40f000e01001043c0aa8002d072290515040420400c840020019075180d400c4556421290394035802500029045020715020035820080d010443d9484a0119010100842c0c40d01c020000ca50305442160114540c0e0000f8134540541d00c6151680c52000c80307801410072000600b00207001c58410018408a040184240d0752420561051000e65016020591040c0c101101480680c900042120101d41c44207001f24405901c400800404058048007507400a40f10750310a4465000f5450242c400c440c49000600504602e040420000b9410400881403100c900014404540e0311003440c01c40b22920b9401150300080707490160f015002c541d0001c03000320114000c09011051a40141540e2a10b0340c5040215a581c3c9100b1a40705150002040f05c030b4001401050209104041000d100c0f0041c2c01120407100300c8007811495a400b14410805030182c0c0c3c0e8440c411480c1a000d61070042c811100100310860802088130000c450250903400c0c40c59603001040c0b46803100e001610002c00d211110020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 818126861 1250 818125611 818125631
    0x13060605040915030c0603020c01110307110f0718020d060803040b040e0919290106120609020a0509011d191d01031106090a170a1401020307021b01030906 68
    0x1540d0094010319282c00d051484500400480090110481ea0054044c107007180c98200103070b000751300071a8145c86079500c4418010b400e00d0404000d6005041340c1d5904401c0c82c928845041c140140040d1007242500310080401640340341c0e00c01e18801d0150241c0c0182d0710705580c3d1444005024540c48141c0c00e0001040010750402a04003420441c1c0d03d68030303203d80c00e80c2c0c2c803a03006483d00c0c1103580651140d202c0600a001140124210702040e10040c01c800404040d802800c40400d4400da00280004540100480c000c0c0803d0140340010702a40354194100340803000f014110f0b0140002c8503041214001d10340b2100c603007980d022410000050200031102c1c0200805e0441080f003030042c050040a64502350ad0700340c210b0075502d8101d036082003030410205400002c0001a030300210003a58007100004011400000000d1b1200701e501c801001894107041ca460700303000c400d860130111181a4814400c100284d50081041d0101c2480082a003800c04091001a030042c0086d103405484a490454030366 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 818128111 1250 818126861 818126867
    0x30705040f060e0a11030c071e06050702191a040f150203060a05010c150b0a0513270c0524030702010c0e030a080414040e030708070b0c0423130606 65
    0xc0b0079a503050880c0c890790307a911100c07a415039034245110460b00208100146541032120060540103200f4281c04a4171140e100e0b100e0701010029030160f4000703030303103400303100e04560100715006441c1080c81101026030b11580762401c00aa401018040c1035074500002004c0014081e50f0416841e441900301807201d061403082e500070f40040b078096000b881e80000c00b080d2580507001c02d90441d68030020606003d0f00680d01c05000c1d01d2080c62468100e0103600010406a44e49003561004038482c580c0003456443e0400070080d10702d0115070704d034850140d0315295030100700502e410f04103464088e80c0d91a00d00b107100b00300f00824102e07640c1d400b2503410080184884030380e06410007202070b5203d56400244030001803c16407103040700c500050040c0010041001041200300b459004508003e100090310b280070103d10f07046500103175040700c070124001035200130800c4103011103401c86031a10000382881e0610f505560401000c0e2200c07802d82080300c034408125524a050ba5019080700c607002d00040c0ea4031407003d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 818129361 1250 818128111 818128121
    0x7030c03140f03150a0801090503091504030c060c08040306090b0901050901051314030906070812010b1c020711030304062f21091f0219080306010e030705040f 70
    0x44000410015031003402a0404069494000035210503c1c5151904800c0b50011498000c0c100d4100030001000039540c2030a02c2254521806240a180d80e1501081001111004010b00c20640c440a20007880480c04440c513180c184c44176814203204080c128244110240030f140e00050681b41040c040d0130401496008032030150006500902a9845d100180340c2a110211041100c44412102e540081500c1e454808141c0c107411050702d10340500390000c944140d100ba10300b03886200c00040d211102149404000c0d0040070111700c1d10381010501c0c001d0000500004240182031600402d407017040c010008583d040000000b012070341d07580c0d034528000d080102100d41d018828202c4c240202c01541d200b03000c900c4a0082c65001c0c0940c1000700d015000c6003000c220503820015000d11115030181c655002d035980c0f40203c4c0c060910380c040240c400070300d09050744112a24203400031a000b00081c008a00790703a00500e0908215107140d03078990220f45864040d6000310b0b40941420144c4030091015444 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 818130611 1250 818129361 818129363
    0x180d0c050c011d0d0c08060106021c0806030c0402090f04140a20040e0c0c030703030204030c06031e0b04020c060a0501051c03020d08070c05150f130503030f0601110307030c 76
    0x41c1d82480e064100151680c00364881005010081c0c2c800d1480e661a1800c44c07152000e2140c0050f480307058075854003904d0101c098100c0000b6a004c4007aa0301009014030150411121902e07190b83d40b4a004000301740c03542d00d8000c4060040390046900c07006590303071142c0c2441c28070016108011105070704081c0c0302c40e80000c0d20b001c94114a0310a0a4042c0340c1d0100d41c01d0000440b0989040c0382a1403d1201c1d420354000038a040307079951080c0840601c07080e0030310051400300e0003a40c01607155421410100030500075640312905051030010358086a901c82c5480301043c40c5080000151110200302140192141501da42441c1c05503008000b03804050b980014103a601c15a85180249584c0c2c03540391215288110140159004a15403030030310380708901080d07001080c1e1901028119a95846900d8019881c0c2c44607a0181004104010b080c1da5110a9502104001002103108001c0d282c0c65100c0c03001410510f03032000300c070000609503401101c00c941e1294031a0101d07a80c501080c00c00030600240980 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 818131861 1250 818130611 818130613
    0xc080a050915010e0406150305030a031104150f030b130e0c010201290406030807030f11011a09040602090d0503040f0e16110a08040b0d05090a0f0b180d0c05 69
    0x1103010700c100041c001c1006080c0b100080c2c6140d082c0440e0040c8040b0040c8102c5035603072a08071809000e50782420410085100b080196142e1411680150a8441703590800381c51920902041144040061584c0c0d00c0c041d490a1440d240f1041e004220054081ca212027a00500b06030b81040c1c41341c0e843d80c0b20856140c0b0803400e58030001c1c1c250004a00742d5400ca02d02c520f03070504c0d00c40c980360390750440c038402c125414008100148199690303607140b00310f401000b802d03800f040741101d046070510b0300300070305204907040100208070103102480e4445001c01e0040820380144051000a81045420345c126507218100400071b500248031460f00f1682c95019016220b5050414a0300082c01a4544040c5014080f00d1072200c04a240c0d0301012600d003040001544030a1051100c3e800105100c04e0081c40680981482e603540d4101c1c4080c0744d802d0320b0001d0080580c80d8421810303103002c590106010055194400e5040c402c9071159070300061022228440c0c0001c6d800342c41c10040816070052400722542c0d00c240 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 818133111 1250 818131861 818131871
    0x10519091a01170705071e0605010b120601020705011b1506140a0b04291908070f050405060703050307020a06020c010b01080a0216240f0504050c030f0d0c020109090c080a 75
    0x6035a10b590b0f820103503030303040100c2d1003402940001007181c501104083c1c1482c0001300420001c2d2249400c0c1d910aa1029640700300010b1701d04581c0001c20411544450f003070008121180c0f0b0100000c1003007404001c241210160004400204681c8800c4100e10101d000750901096444140c9030021b050303034403a200e1281151180018050590809130340c2200c1c03490300040520200c0d10f00f1240011408841c0104e030302d42c20028000c1524020340c840200c200c071951106400d18101001034042c3c420b280fa0001071003c01d0000300250355403403044500d460340c0741c5821501ca0f1101c00e4180d00d0007104000080aaa0003ca803000150f00305500c5421808000d0341e4007401354940003812001c0340f18041c4038104140321000240c0c04611400d4030200010741c0390310502203c00b201501e06085588d050300d07204145032600c06000921070304000300d025028040b0040d2110002420302c159594044018020601c504400c3c5001968058144800103101604041c085208c200200034100181182c102d03605520309 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 818134361 1250 818133111 818133137
    0x1060f0626060103150914010806060307030f020d0f1a0a05060103060503100e0705040f06080d0e06071e0f1b0f0513020304020604050a0803031518010519091a01 71
    0xc5206404030074a0380040c4080e4680400440c0078144d1004803441c05031049000082c2c00c4428071400000450f85d991260165050103201400d091002c0d28062095001a81c180049070449254245580e0f0454200d05030000314541001290004c90020745a068a0200c81c48031080180b08244150000d001c20881343e40c07808015400c6500034042e00e070705503006000c2910840040d038081614103800c40c0444150947c0d0701c0000f01501c4000c2a49140ba1ba10b41c0c1080000700300420045d4440d0071242009814280340d080410860f0203a003801902145064400540c47c420f14030165004c0ea8103c5505540900340d810004009421100d008120034000c45001070313140c419400850170b441d00181110740d02d07595a02a0380203900060300590313101c90b08100025459940c02c115a0041580d000516101c1c50310468880a0002c0400c0071030240c81d1620030540d4043c64400c1007030540f003084074140c400d00100700d090721807500703640c0001ca83c00f40b42c0b2441c1c80003400c1d03014800c0030480090340c03240040301403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 818135611 1250 818134361 818134397
    0x100e0303071e120903090503100b01030608120f03040f05060c12160906030e0c12010c2d031d07030303051023040914070b04030303060b190f030e01060f06 68
    0x80064000850302103c2d41d25040b401d4100180450003403500c03220700c0f61214002420040c002c1e40d095030141c0da904a076122035130103001305801490300c04050039041c01e410503e000203101e000500b448801d400000201004403c81d900c0c00d06a4101c1e04540e810300d8403100001041e8000100c0c1c64100c0c107241d0009004880c00340c402954942c49680c2c8504d9203250002c160040d150380c041c0d1101070300901980200b1a01c4105d225440300440d2000402c1412400d08058890b900318910b8001c103c880da44080050442d240140c1e140f2081d52030700180e17055881c000120400c5c100719280240d4084d5081c00018940d154001074014100d01810341402c580d02c0c241c8140104243c1c00c000c00b02c90107061082005d10b0300350f01040c5268003d040c0c106c40003001141040c20960240c02c01c1000714004242842410f1b850310541c40600031101d4064500071070740300402d510031009480e000801c030185511700d040d20b10036000b40200b514080c00a0100b03a40361348250b4100b0f04140151800a140b425034442031202c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 818136861 1250 818135611 818135657
    0x80706050105090912031b071a01061806050d11030a0c031d0709090311070f06140a0819230402030607020606091506040b1204020111030a20100e030307 67
    0x1d030384e400030b00d5140c1c4c06420000440c5c0008004055111081c080c0820316541180182051803007000d28403150429000c032724041c88411f03044042044400e4251000e01a21b0642290a441e12410f1854590b010101c0030005069101369604140c0004402d0100b4180b4a4004152420080d101030101d0030003005481614007565402c0440c5610401041001c004d490f440b014a41d4000e290a40c8401e4400403828908406588225000c01d8005000c1058542c4603c10240d96480491110310301100c42400a04174400502406e0010f00c945000701e0706880c00344d1069440711001510000301c0c60015000008900040360180e000e80590400210124404a10300e4030413480181400300039140d1440014181c0060816a034212204100c040f5143c50f4000140c00c2258420495441c1c03403425100041c40003116080c036041c140d0040c450380e00c6807904007029a0f28241c0302403d00f00d50000003030398203240254192031180c1e464a440b040e00ca4110000c0011489020b00340c0350880c40c20312103015121100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 818138111 1250 818136861 818136871
    0x20d021603030f36110405040812010506031e06040e01060f18090819021f09050f0d051605030f03010303020723010e131d0706091a07061503050102030408070605010509 74
    0x304821031070102e40d04c0001c032082029405001046450001c00010404941080e07038190f4038401d005c2030039000d0840d9003800501514090f1245425070800c0e114103441a031070141c0c078010360101f07103000520303603200c0b0740c00000180d404070028040d05541d40300c02c40210b06c07280152a40c0c0c0e13501d01501d01c02c03950f1074001c080e441e5600034030103840d0180c000306c0600001115280c0e60110f02502080c01f43c40006143c6284c1240080c9030b000440d400185891450050f11001c8041d254100c0100031100c0340e000f04c00d5500c0b042d402c51841c143c002075840d01501718402c00b81c007400081c0000c00040709143e4001071245c280c2c0c01402e52145ca043d2442000c502c06456802000c0c00581c0300045480241403a011140f520840c2040c04600c02d120703020141d1000c503c1c0070009403a50b1086408014442d402802000200f4601c81c0c00070400990091f020350504c1060000782c00e00f40c03248041e03030a00208441c07a00045800000845d01c1781070901d00380c402d960018009942090820001142a00d8034400c80c1d4010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 818139361 1250 818138111 818138171
    0x207030e1816030515060c03041d01210b04060e100e01060509071407032109150c0f14070c180e01110c0a060b03010e03042c0c0706020d021603030f 65
    0x1484036001b000750a610910b50102a0701040c00700107030902018541c1a4021240f6050009541c10030003500020b000c0d28404100610405041c01c0200300d0348980aa0000e400c50ba020451981d00a0700070300e0b00300407003400913281e40303030203003030380035900103601074800d60f48101c0d450101900d81100454105102e244240c40d402d01c1048450006030152801458200703400e030444150f02044001902100c0a00d80c05448000078103104c6541c8006900c11541341c0320442c02c11541121103800700902815007058140001c0380c0000c0c03800b0901c40c11000d080000c11b42541c50b000c210030090003000251000c80e50080e0158240400394480c0b4080f1415078407980303000c400901201300c0c01e8940b4000b6103c5140c07041d0300755507603903041204484144001c00242190308007030900c54025001c12100c12101c4050544a20004400e201214611038215414160011000b40c0c031000741000140003031241c0c94080294500300707160f0804064064100c5210000312030003c000d00100204842d40030500000b0032000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 818140611 1250 818139361 818139391
    0x1b12140616080f06010c0c03080d141902031e010f290a0518040e0a030905060f091e0a1214010b01050d020a030609050c030103200102030307030207030e18160305 71
    0x35464003e00d000364405014906440c890003103469a8050911176002942c0740f0800180d45035021800340681803003404002c02e00c140c5860240c0c0501d094081c80c582c2d0845084c2c000002c100098805141031440044400344a40e49595401480c1850340252049410181094610713038200c0c20010107410b07007060610051072030a000d010088880d1380c440000c0401340880f401c0840da20342c480b4454184c5c8600f0000041440205a0401803c0188076900c00ea02c11340c420014100c10341c4508003a615080003d0319141c3e01e11910078400414080d2481400da008804048005446440908182e941d42e000d042d0301d48190810040f030500341d0300c0444403280414010031601e040508580c1c001d01c0440c4840c600010104e494015220a0b00c2043d952894145400300051050241c1c4401191580f2a140c122418842d84ca00000c0d4803070100030014400d05070701140102c00c2c94000c0500c1030180d50002e14103421030b0f45500e84008500400c1e502c008064a41000d0080c0c1c1c2c600030320403103000e10495030005031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 818141861 1250 818140611 818140621
    0x32306150f191b0507140f0d030305040f0f050105390309010f0e0607020114011a1c05070f02010f0b0306011712031911161b1214061608 60
    0x7030840b50750307228141045814a06440800010040003035070a00c608042e00c1c440f4a070003038211104050149151144c0b1010844012139507800c181c1202c105d5160401280350f0b42c0d80e0a10405110000e140a0003601000300c1c0201007090640c0800d101e88944405031400d100c00b009424182129014901c0c040e0380e4044410251000c0e900c055640904404000301d02044a194400180ca649540d0780540c0d81c042e10a1043d01d50b02030044990b13244403417a901d10f0544c50070706052500074440c400201ca500340000c0750409011440640d01c0c04030780a0f1810300440c2041c10300101a0003694000000551a103034100c2c803c0005030040e4004010000e00070452642440035030450404000451800c5105203405002d180203c0006076102d40144810401b104150400040694258030184022100100440c4072414000e01140c0310a03500315000c08103060440d8283c40d141d6800740c100f00c4240c2c40001b100710070400c44043c5003400b902c0da1300c20384c2c12544413003000b940c0b18510244800c0106d825400051 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 818143111 1250 818141861 818141887
    0x50708070902090d140f010f0902120109080313020d081c050c0405101101091b181103070c020a081006170f03120702070e0f15010807050415032306150f 67
    0x45c100c4407651090b02d10f4280d03030214040c215540d42c43c1003107545e91100072507415460030740102086540004024003810740d03980d82c6c4407494070004001e021407805860004c0305544401d80d84444065125107200d58406c40a00c000b860584030f0354007031005070b0401c00041d00f0b02090380252021900302828141000c001140d041e2200c0c034552940c40455940c6041d480c011a400c0c0340000204100c4203216902682401910703d04c0c0a4899110407015040a054a269182c0c9004482d80110b040c9810f4503808151320004041c0b56076075008450300d10448862802512280c1e02c003400300c480c0c003002642c5259035040d02ca03444506507040360410341c00070b112071a8800007800000c4e072301541c3da1040d1200e00d5100e0141f01d440d0b50b81070301d07208102e2a8440800000b4000c3c264000300401c02401c6c148010314140300020200e00c201e0154035058149400b00e0200780b40250007420b0151030400c0202101c1c081606120584401203c03541d128884040742c81e416044480c00700d802c5190401c100c58540076034104c1740 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 818144361 1250 818143111 818143133
    0x1503031e1701090c020f010504113309040b1f05090a03080a03021209060603070b0a110a120e06040b09100e0909010504060b03070b1209010902060403050708070902090d 74
    0x1030050002241e00700380400103080500e4080c00501c0c4000540c180501e100925000d0811040c42c01a231501003440003103860624505140401156103070413001d060340645503844a80c00080c0606090000d0501002580c0c2c00034045071030040c0e40801003942d8480400c1802c181c404881f070b030728518007000e0060851281009240b01c0074050001c1c034a080e600e503036540966200888040000340d000c207604900001011202d600719007000d006000070f04001c000a41c0f15041449410040c40c4009444003101e80601040c00700900c0e004191880e841690074900da08604599015000543c6061707810302c45c0c40c101007941c0645000b041d6190804107c5014041d124030900e40013018400c0713043c401201035440c0c0302d496208200107000405c0078241880d151044d01c51101e1300f50b02c26042034500740320034110041525612040c2c610a1300b030b541c079940d10550060003019000f07034100c500020007206021001410200301c80e01b039412600020340e01c03c010320890154a6565502003c0c040070000171418100075 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 818145611 1250 818144361 818144417
    0xd020304020a0509010b03070e06071101030504060f09050708120a1b17030a0b0a050901140103020d0615090807060c081b1f140f040b0708220602090301150303 70
    0x1036482443e8a0701c0000d959081d0990040c80c0b1544000704001c48540e0100d00c2d00c03031036102034900314107141d11070381c56060818480d00810b04040e61000003400380300080c0c04c48054850016401c1001101da424199100c03d240d00400409100e407500364884001a90106c40300024180d5900644a0061960030100c05490000391102055210703424000b505990045000781004000001c10009040c04d00c041c3c402e15600041c42010320100411800b00c0e40d4101c41c0b0554400d207801a03407a06189041d6000340074603000310106050340e41140e6903503900842c2c80c3c400d50b900041294000303a13132082c0031105900c40b06002081c2c03d50600450600f10b44130030307a80500c00550b50503503243c44044402c0e400d2000514447c4030076141c885a10350380920700400010b4001268110740803261030716854540103180050540000c0002580008070715060f1800c4409814031903013280301c0c3e0086030b030500328041d4000c0b00e10b1078403951a0086010342c00c454481d2807012a6491b0310350b202c91100c04074681c18500f03003100c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 818146861 1250 818145611 818145619
    0x220f150201020f2803050601120e0102071a07111b0103022d0406030b09060904020d0510020f1b06090d0e0f120f060601260c0c1617120d02030402 64
    0x3c201c04603090b405000e0030b41010300700b9190301c025106007a41d0142400310100f42050510385070a00c400c69030f2144800040600f0303070300c010034020741d003551041c0280f2400201401011600705401d40104180013030501031107480d07881000e00030007002403c0c2c444070400003403400d4025980011066500a801038442d90347c040a2941d00314075100755000003281c06050b811018007000405201840c0c1501c108585000d080d54090309500e404008180007130800b07440a4465088001e0190800c030041050780342c0303804003040070b40d00c6810b203d18000c000d0b00a20700c95072400900c030300c03003981041c0c000800c1481104504014024030441040c10398140000035965600517083e2409000141c482e682612880d080700d400070100350341c01d611544d040500180006041021080307100417a01c1c00b00701404034045943e41c0c2c420340e0b511040501c403e1031040d40d0310184180180004d80481143e00c000380b0003102c030020b4106078134000340b01d2500d48460b020080120103050500c40c90088070407560141d50303c144094 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 818148111 1250 818146861 818146867
    0x305031e0412021512040302060403110f030403260708030f011203120504060b0a120b0c0c030a08060d200406060f0f0e0a0815160311090d0c03020a060302220f15020102 74
    0x141500c1c5c24008403825409a40403800b2b01c420554486180c400803c00e2001802c40c2c05d052800300360301c1e0322035413201623b5203501c10b091449400e0f00d89020035190160800d103e1b6101101d283c520182d800840742450000380c0c107400040c101c0c0c00d01d070b621813a095050740c1c0d611200d00212022030040c40042c005540c05a0f03a154945c0c09901d404285c4000f4090207142d8078400d5000d49881030301444010b1401000100610042625460004c1500d00c5140e441c140a17407203a840501082141000e180047c0c50043c1c01208806038409001c2d00d00414001074505000035a04c070342c1309540034140d08105100284600b403110912038850088514900c500406070300020303035506051071074216159101000c00403c68140960508a454920264880c504060007009420000c00c00d0b03a0103100940e0307029145080624080046140c8034038041c5074010542ca0348251506001402500503000032810081d0000d4940010344065031400c0484e0140d00040c030070541842c175490b014965034040d01e02559000c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 818149361 1250 818148111 818148127
    0x190c091a130506040603151d13151509150513090c09020f090306090705010c0b06030a020d080414090f070f0c08070f0215070b010b031f0305031e04120215 68
    0xa44014002040a546c0102d01a070340e2554003001001c00e03500c101c030300710411036a03a42e84a103003c103070b00d038481c20190601400011504140c5003e500c80300308903182a1401040c1c040c4104011498425940d001008114503400441c0d01500c1c3c1402e0300400d580240c103840400303006000c6401c07844219114103550b041c030720303540c200000903a00f00b030450b40e2221a000c903075000142410050640d0128440e0700800040c2d01c0c080001e01424440c000140820742c1c204001461900c0c02c000e0b81c3d9101303502501c046010071f03544c24065003503005030290511007001138070f0401c0380e8034110860b54051503403643c2c50106a04c0340181901c592180d42228424400c0c90f4201d100402c041e9030280c401e25025080c04a4004410300c1013001009512164072220402440002c001c90f07140c809007415103100000b020f5498a80c4452080082075004400c10108603d207004800c0000c0070003e0504140d4820707000b502c401c116642c090a90040b40204100380c044450f050300586810782c891042141c01c04402407070000c3c1c07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 818150611 1250 818149361 818149369
    0x1308030a2a0206030103061a090c193b030a1104020d150e01060e09090319020f030c16090b2409180411060301051e04020408010203190c091a1305 64
    0x903801503c7c07032070752244450710580810a0b5101101710403540c030311107480c10190541090040c1c4e1202d000f8000304524100c84c090081c0c19494084040a05d50301c42d01040603840307440c400300b104000107220f841c16100310043c200011407217092941f001082242c13030050410300c002504000c00c14090341d42ca90034800e40c990520b1120741d001e0103c4000f84061076041200c041c13350340020100c50701900c50340c1e04114003840048141c4500101a01e102691009039140407860b014100d080c10989010005251341502d40006805020b4542404c00803a443d965181c0b010841d40c0c10361103980c02030301020700c0a88008031110380400500d00340c43e40d1410541b144001c10700c20540128444e24410802007480140b1103010f0502c0480c0c242103604518540c101000b2900703840000581092074148015104010398680c1c05403005445030703c0013107440c0e10303000c00d40456464035405050601850030310800101881035003850252200107801810383e580c80801001c103940000070700c0c0c1013284d0348400480c556403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 818151861 1250 818150611 818150617
    0x306030c19121b03140d0906050f07151506090b07082208150f1f122a0f06050705030405010c150f0204050a0b070b0105121c051308030a2a0206 63
    0x10141d0150082c4002c902c0f0342c5d5142031320078103c00041c00100d240802410b0b50180865000c3d00080300899140e01551402c0f10b2908248042c2c1c8102d01c7c240088401c00c041e10040714012610596031741020b1a40e14142c604840c81840f80152004008102000d25032a41c1508585006a44246003000355941c101140c2011419042e1034502c0e05040f040c0616440d40d07400154106a0360350006001c801c81c0c6e9409400b003a078501c10048000e04202d80d02c81885010200341c00710850b4284010307c2a15004400b0341e0100300b07406003c0c040c00511201060151159044d20090755100d001549014100001940e80904280044034150103140d03c10020311168050504143e12001d00540c845082000b0018400c90a4104101000b8184003141c04550035600703040c115401a29402c80e00c0708220001c60412000c2c440a000ca00010a40d0360032050f0b000000300780c980440d0a5000040c2c1e25003094586034400c100801d000220f081c03040100c410064026041d5960226148503800540c5a0206c3c01c250 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 818153111 1250 818151861 818151863
    0x31002090a0324060603050618070207030c0f0e010608100909241a01020109020112020d290108061c030e060c0f0c0f0a061b08040f0801020306030c19121b03 69
    0x100010b203d80306580f00c0e014900c003505403410140481d02c0d085010030980080344a5460170450000c01240303d0794001e0100c0f201840d00b049507500750548502c0c0010440e0a144105e05443e88017000004e1000d02c0f03a5101c0740640c16200c903540d803c030b241ca0003a80103000514010795910950041a0345a038103108845241c0240454020a410361005035039405090255552815a410a070f40d840040c2e0b40700142c2c04c1281c1c11014010b03107031080c5160310402000e07030101c07080c2280d4940350800c0a56803940c5103044014001d030b071450b50030fa441000340085070301e07003a100c60300300d030700c20031140e40004d000301c1106445200103800c0d1400d01d0600c0d20305c9131400b01c21500d50003c43e000300e6110152400c00b601c03078101816080d01c04001480c035203400104103920485802690000803c0b100303041081035070458008140d0903103038400858482142c035000750700c2503807414424803a43d0002000d508021b40c4401542c0440d0665184251a008491060525182d000c440000010b117035261010940c41c0450055 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 818154361 1250 818153111 818153153
    0x7090c0806010305060102070821210a20090d03030b0301051503060115171e15180906010504090204020c0d080708011403030a121e1a04020306031002090a03 69
    0x5041c00000503045900c05400641150054801030004032400a4224101d80e07140c20701004c00a81e108406001d8011001d1102c109004030b807240003010a5081d110f03002e0400c04078104800310141d103400c2d0142011301e90030024544248100425131600a071801c001e140241070100c2e07107080351b00010342110340071507101500c0782c00b840c41c80c03840d030034200521405400a82c0060084c00700d1000040c04a6102ca410258032075441030015825001400305000743d2880581c0454460400201d90703c00d40b24030201540c001c0300003100c0302c0c580e03540e8070710000d0184207d1000f614943c2d00348812710000c0c080010b4181e81081d002c000950780c00b04200710000d5a04842d60f185081ca08104000610349081a40080304c0a003424011205e00e96010003102c13050380c0e050400c816600c2070070b05000301904001d0040812480c0d00381001402c0000b03500205000b245880e0080400c1d030000c070421080340020b5070400d0301540034040a1000d92a2540184900c1c03d0042088881640e2980c960020002c00400c0cbc85030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 818155611 1250 818154361 818154377
    0x18060f05100909051902060417010c12020909061309080f090f0619120603060513020f03070308040909020d0803090114010e070c030c08040b0f09120a0f0f0507090c 72
    0xc100350703410349000340031028014401c407209901c88a684112084060900c1ca031304282103411580c60b94201c2c1c0090055440c2c0308083d00b4040740076402810722600700c0c404076840a80102d41240680301f221202c0c1d00040100702c0503101c1400b8006802410003ca44500380da640720342001c00c4108021b00701c0300308170401e8180d6480412040c4181c140420b600c041c02203406101c4000c440341640c10f4079812003281c1c80d05c080e040b01019812005020b0f81d50000d02090301c1c0078140521684143c0c0742c20769903402600c0c503550103550f08042c9540d035070b264072018000100901051004003610740158407401d0000349480d05200e10364942d2086580261481c04c00f9a54844555082221403101e140c0100160055040545003a02c4082d21030303884548010100842c1c610740b241084a000155800b4100400020703480f42c1d008542008161b005421143c400c05001c0d4400d5465400001c0584402d80c1c01001c0101e009601c0c5e440b001e0720303042d449040360385001e60500403c01981c42d20a00c000c5400c0f540d64888 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 818156861 1250 818155611 818155621
    0x7060510080f0a0c0f0503060103080a1206060e0307080d0215060604030c120b0a09030914010c0501060609030204050c19230a03061d09121b0d0810080304030c030618060f05 76
    0x321038644da4003003a03503203a840302d0400040d500032441a0440340c00245065582c0e029000485075240300a8040104070b14005000c1040c9520200d801da9091041c0d0460f00c0f01e5443d034145680c3d42c520500040300580c4205914009c2811001140d50825000307403003141441d45070369403203d0550b200c0e080b048070884554540000c0c4100d2054280d0480a80c100411100c03055172001030160409014511000560b0760740c0701c00780d034400d6081c9505190804020881262180001030011002c1e120687c0f1540c10580404c6014000c10f00710340107034012000030700803050320300c0c01039a82d0b010307d070140740c5011200d00c150f60f000303c41e603401042c0030b10880c3d0b4006603440c2001c000d80101a1124201e8030300c2400c050400100c0000040c401443c070381c0240003580c9510b02903404141038000e07048001090300030511405030154008000501620000c80480100398480c0a0695a40503e2001501450031500f0410109480d07030700c010501401003c160500b62040e44501d81a03d1685403092400b40d51002040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 818158111 1250 818156861 818156873
    0x3080d0b090a06060806010f170c030603101527020d1b0509100813060e0607080f04080306010804063b0d05180f030d022107030507060510080f0a 64
    0x15031001100c841080018209400182104001086c1605002c0f180007070000301030048208200c0c1001e0440406c6152030a01c030007d001d504255a03050180c0314650858840005c1401204589021031181e880902c1c6016a051141c91141c02a500360540c0b0710300e201c4004050340014011920040c0000c1511104280b10100346441408041c08100c024440600146d84898542c98528503900e880981038503125131340d0400b0324407904028030b01441c04a40c0d40404502040c420312075215516004259994114252510b520490340100014030810004180d90f01a5084c207812502480000030005411207000513107500102041080c0240c416410103032204500745100b0319040d90016003100075001101800703038000c0480398444e00e1010400040c0035200e1005404455200500f21581d40704528000303512000110f4450a00400c00c490803141c81103600e04039606580d151b43c2e1945011250f884043c01020003411248015404070700001d520001005243c014211560180c0090b031050718200c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 818159361 1250 818158111 818158129
    0xb01050409030e01200a050106031a07020d140d050103050c032b0c0f1a010e10150807020a0b0108070e010e010312050703030f05010902030613112203080d0b 69
    0x21038425401e0806031400207900201c0072141c030100303003030050b00100c0303a24899181c425480f2042e0305a1143c60107010503c42d054201c60100c1e40603900300741040c64010082d0a4052044070444007580c85002c0c496401481064141e4400c00704040903801c1444180c481026035400381d20503250b0754444400c1c40024030b4207004000074024440b010860301da40481c0c040031076042000b44a802d0020442c08041400051203506d0204d03640410800325140120155070303220b10b400c0c000c4651040c0e0741d2001034020b101500b600c0041e43d00c0d050004991a44581c400c0b02c280800409400441c0180003102c070000341203080c0c0c0303800b920a5070003600601d410310040c0d01460340142d00c0381c40007540f140e0040002c15441500025142c0e10740ca040c954503903041c1425406402c599100380043c510b010000142c5030840c1d80514040c0303004590a800d08280441c1d46415101c4c0c410746541421070400229032a04d83c030364940e052800154260300110380d565140d5104540149003c070075502d403911f08010725032910004c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 818160611 1250 818159361 818159369
    0xf12110303040f061d0307050f1f050c12090303030c0313050a1202101104030303090c0e010303030b1c020112020a0e180105090f10090506042403120c021503070e0310090b01 76
    0x620031441444002a40c1f14564842d55002d24486443c2c0c00f0b003031301c1d03c08a510032151001d40840780c0c00c1d020032000f001c41c4d2000301441c0c2d05014a01c480c00d054041201180d00709a4001c0c015030440d260b49200710301a52015181124003000e8150707000014005200c1152898010420390f8808080036001a0411800b0491858020700e0030a0307030640355545000b680c0c103598143c54005000600b038070b0800724030038403504240d03285c03401030b000003081581c50740100091309400e94012034421030310f070201b51f4a66100301000740455003038503c100c102003556001c0d000e0b024040c50015002001d00700032441181280701c07032a00003d034410040c040740c14010038040d0030906007034600d420f503d003200030f0441012085c0103044806440d40041076460399203811074079040d0009a801c0c0d0321001182e5000031000c100780310490728000d594050059860140c0c0407884d4140e009410709603460b80004040d00298002807002023800021402c14680d070b1410010a41509440c40c1c0000e888006402e00703002111050340 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 818161861 1250 818160611 818160647
    0x905040f1a120319050c0a141c020606100e0604180b010206010509040f06062d09050702101509090b09010f09150e0703060e0304090b04060f12110303040f06 69
    0x1a40b00381c07010000045440c200110440700c3c41c5000381c0c1c0d800315502e100e40011001103108103500c540c24030100c0c0540c1c185450005040342e20f01c8212604034802c805940000502603000f241c001105418420081c42c15002c1074542640c88020316000601e01e44c01680000e40c080e110b16041080d0040140301c0c54244c90800d0009103455850800020075820300100b00500b6140328502c1201004450f40101015105180d4070403e4449405803d03810905d85aa503110540c0544000082044c203910565020312190341c0540b40041c1c00310402c038081d10103800c80350a80051040c00260500e1540324801d441881000c070340e076540c107000241c01d094480248070540d5aa01c0c0c103000c07000040c840c09220700e45450303a020101c0c811000352003480c04d0110b030b60b0018200c0760408182001d00c05000c0014800d44a06c40b20400000091109010885240740034800c100e503500c02d0700307010384a0800c40040c0c08a02c0b44e80b0660502c2030010120b811a005a406054031480d071490a108154100d4940000a41400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 818163111 1250 818161861 818161879
    0x30b09060601260714030c041a18120f060118050f060a12030e060703030c09090515040515090c0c12130306021e0c0115120b0c16060e06060a05010f0509060a0905040f1a 74
    0x48a402d2120b603e140d80e09108500d17030480f0050304200cd221000d510780c100c04c1a0365580d03039101e2000d0b010452030368289400e00d1a0030005207080c07404c0502d4a0050b0380141041d00c61034145075442d00c41343c0c0c8406099080c000d4940000c1c02c00e41c0d03000b005000729842542c002c110070000c44c0e0081c10028103500b05106040c140400c00c04542e06504140e40c4014003103c1c003195940f00c800000d419201c040c00340f241c110b000c910030004281c042000410240c1c10180444032001800c80250b4000c1c0120800488102c11480341040415169006450f5403184050041d080828415403000700c1c1c0d0050500c102183d448000009406c801a5075000040045400402244407265544542c01d4401800c04c5e89103000418000800035050100c50b11141d400300703080005040490b195070340c400b0210fa11610030100514040740390351043c40d564055500d5511450306180c1e0340403c002d0640c0040000034208035051800007042d90b1140140070f20340e02c1c5114000f46234a402090440d8444d034072550707107025000718 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 818164361 1250 818163111 818163127
    0x213151701180b150331031b0c0816060801140d20120a05012004060f020c061b0c0303130e04020a0807030b09060601260714030c041a 59
    0x400b02103500d2040c41034002800d00c100100103100345110b284010090320000c0708101d800c901504180c0006000000020030100403a08600324014080d0001000640522110f405941000c0b01c505005482150130100701030b01d4050301417602801c850307544404100d8480401c090740c0c004603c42d001d041714055a0a4594020020402c00301c4010001840140d400d04032047d1a0001c2c065039215903001022610901ba2104425903560702c100d600359915440c01c0ba280c1c2c00702020420028140c0c01c8884022305003454018162814004404550198024041c4180081d5180001482a0128410070714010f115050841e442e1294003000c2c0c80c000c0c0c1c41000301c0100104c0380404001210444540d850142c1c1e240d1000c51002c0f2542e03400f005880c4100c030804000c200d480c2000c14880c50201e400c451056440000441c1c080844070804040c0542c03c5044440b040d0314034240d03036032201107403d2105405d020f041d1600199801201c41d002c01c2840464240084c610083c400c410f0260780c600c1e854200405 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 818165467 1106 818164361 818164379
    0xf0918061801051e0402060711030105040b1f0f0b090406090e0a0201080f1302060d1d1c020a05030d020a02120c070f0b030420040213151701 62
    0x2401c1c0000e868030440d65880304011044c641c0c0080c0f50f2215001d011040c0d21580703041d02c2010380e070320f15001e09850901a090042c2d100c2d82d1080c04170301c1c1080d5404903c00010051000f45820148100030075400401401e0580726000d9005a0310750f15100024010030180e0300848034203040003084040200f01041d0100d6484c000c1c0c131045003940d40c00112034152401100d482d0310014500c00481e0160610401510a250b903005000858078a0b054034200074103059026446664826409404d07001e4030703c00d01e101e100304a03000400c0c00700c1540d030b41c0c141c80b0b01400060038040355010590b42d020510810002442440b08500c00d60740310340c141511510f420003400303500103a403140702e0005100d028420880348140d41204c0042520040d80d00784803481e03900500724071b501940a00c07201c3c002d25400c2c11440c0041c044a10f6050707051a5141c0081e120300349181091561021500c01000f21602c = true := by decide +kernel

theorem cover : BRFrame.Cov 817985611 818165467 := by
  have h0 := BRFrame.cov_init 817985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 817985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 817985611 ≤ n) (h2 : n < 818165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
