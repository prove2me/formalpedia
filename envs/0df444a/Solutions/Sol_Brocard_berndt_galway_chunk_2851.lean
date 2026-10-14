-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2851
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:55:39.607782+00:00
-- url     : https://prove2.me/submissions/d395126f-7ed5-4b95-9b7a-8fbb579f7ebd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 512589928 ≤ n < 512769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 512591178 1250 512589928 512589953
    0x1060806010f1112040515040f030803181c08070807170703060314160605040e010e07030905030a11060117060c070303090203150703110a080a111b0303010305010e0f0316 75
    0x40c07001d551308100c011104180541c030a03c03a00340300d000100d1010a280c02c40344202d408681e569441082400c0c0345a42d00b10550b00300030141c00f45c010f082c1000c440c10f40070501c071f50322042c041a10a03010300000d0b880054001c1d00e01a000c801005500010403644031b8200010000705408000500081e41c1c5840c001c0303018115940004120503080402410312103000112040380c190a80d00700c880080d00c60008a400b0302642c0f00d9075800003003140040010b0b044d034408042e0005054500428403458584510381f031640651000c000203000c0f40d03410b41c0c1800d401d0000f603001d1700d25645400030780785500c00d0407656032402501117404248002000c10405010f0352100750150b60180641d90441485218006500c0d03040347c03200042401c2025040c22003540104907903000d41d003074841e4000794030740c954000000c00c1d00000c4040d094030100241041c01c014441303c400c5480340310300215500c0d8198039100c0e0030760f228442c00d2112540702e030880804020b00402034404180360580f4000c4171240908104940010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 512592428 1250 512591178 512591207
    0x20103200a03050f09011b030b04200c060106020f0d030b180403020319020106030804270e030403050c030703030e0111012a020f0d0e04090503070b01170d0801060806010f 75
    0x203450203041d0301500f04510035607003026591a0b81c0d640050117803d0b204841e40c80e103494402d100e080c0000754080d5000c00401c51010304000341410a204401c3c40e085c0e20348010f5a6640c4010480c0c80f000c072001c110841c05800c441c4080c00440e02c0300740a066403a4504d000030400d1644504c2980304a854507a02c4092201c514483c103152818681806922503205c4003c0c41244034480e40308402c1680140241011250f0041b0b441d0321307040c500400d004402203210f07000c0d24203006042d04110841c540b030050500f024010005940e99520318a041d0b8a00b078040021507010340c00c00b800030004242c06c030b241403422480a0030440d80c59030180703003004c0c0100310840030f54001c0000c0c0c09815900080400b5005080c0803035800305d400e480c401d400c80c26540c1e407003031110708000340085c0c05140f01814980c0020042c0e610900442c1c0c01d00066590301c003681042608074038a0500c849118601110701041119404d03901c50070003d2495040500c000c02041c4010040780c14400c7d507200b200181485908803d16044 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 512593678 1250 512592428 512592491
    0x2042405040b0d1e0912080603030319022106030c0406080d0804081603174002030a050607090e1b1305030d0e03071401051b1609050609010605030112020103 69
    0x10341013803020040c0168601511411161220b0980b001d00840031b44e03000d280000c0046085035a8095001c40031070300302c0c140b104010b80a01c00244a156060f10400041d428500f1240c86464001d05142c0350204a11480d481182411000c100a5002180b61030303034144a4940000c5540c1c490a20550311300c220114046800c0c00764580c4420b1580c00b0701242c107071500035420301c2e0b483e4a13400c03030442c2e5580c4a1803014040508107060307a8042c0c000604082c1c950748100516565100c207030b40001b070800e8110712081e1540c1e0421402c020005600c8802a1302500c030b0020440e502d401e03c50100c1d1880c0810220105e80550002408880031100c0c002d0b2200401005040756070902c08280005c22094051014a000344100f82001c5650200c45058029504041e964982080035040300b416004a2002d420b00a5000b1144803443c00f290880064001d46081007000ca40e5052020502100c020141e001c41c1c208001840103002003110908060b00d900c0d024a0301061500d0603201031184030360215502d44120 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 512594928 1250 512593678 512593721
    0x180605063004080c0705010c0b06101b15110c0316030c08270402031e0606040e10030c06030b13390e090108061810090602042405040b0d 60
    0x103903c00083c85800740c4181607881c040d40d20f81c01585e00b40b42890000302041001030000b141403d004246000c0e030030082c94504002084803400c8001507030200001d40d26040c00d281108913011070f03405640c00070350300440440d181034054550340d0b0300c0b801814030b0340c455081e02c514a1000c1c14450040c8080180d040741e21680d41c3e0391150101003950030540d1850113140503810081003107141502c241c910400000c05040074031305d58400e1401e8122401020168024001d000100d020350420703038414829011000074440517410340c1800c0502d03c2d21503225004050400e5242000d41e10764070740640c1060348507500403e4500540140d034414207528501c442c40b217208101140307611140d1403071481084850b921080d031801d842800340600007102740200c0c040b40c0c1c890400314261031100300c0c0d0b8440c3e1070502c1040d95803c13001c001810040c0d42c985403068402a401040030300134017a0044a50038003c0380301581011140e4480805084c070b0085108024001070089003080c01081250894003a50a440d0f5441121 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 512596178 1250 512594928 512594933
    0x81803010f020d1404020f0418060905010b0109120309060507020102102408030414090c1303050601060f03140109020f12250c050c190b0c07180605063004 68
    0x350007200f443d001d494206501c04514032020061540119006089000782c07030622001d01c4007821140c44013440c0c0da02d22495040100b03070b01d032107400e850707512030400070038000c03682c200040509416070400b20200c50241c01c8040007030b03000744002046401d141043d50321803101d400140d0400d00c13010000f141c6a070900c2800ca0b01c01000200100c4040080c8680804050f19120501e40d03d00603400f400074140c03031160200d000c1d8500300c55403035484203511078030901c2c1c500100d03100703c800201c550041740c81d580010300601c60300d40c101d40030b0790030800d452508004841000c1c05136060000d043c841ca4420a50026802284500c201d045554800a64140020170300708202e20144010300c003980c00d1200c848444030b0740100762003400ca24071850b81000003004280009800c0150116003d0700d0204040e454960000f45822484041d106802c0300c1d00107000414540b07803600980820f0408407080c803a00e0514203000c15600c1c1c0c002da8951190a600c150401c8800c96050308001030b5500e5a203c8000102042104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 512597428 1250 512596178 512596181
    0x3030507090503161502010903091e1502010203090d08070c0f08190903140705090103061a040c0e0a0501020d0507030305041406011811090d12030917040603050919081803010f 77
    0x319010014083c011685d400000c034200c0310071040013000602440c908100d8201d06007240010001d014400c400229038540802d8112030350100b60a0250b500401005aa04014001e1910201040c1080c924620744000010480090f000000781000043d900c00f800b441540000c1e5a50661011000740709100d600340081c040c2615488206d0301c20301169042152410049407800854a001e40b510f502c2c0c2e406c69071100050401200800d1850788683c1c0d80c04c1542c2e40364028916100d91070348840706c01c100c1e50010700902042c150013003819580070350181c41070183c0c01821a0b01840e01480c000505403100c1c9000500014490410036462242c00004140d2138210086200a006001e00c2004003107001c0002059a0044182955201c003803058284d000c036450b5400f40b40128014600002c42c031795140d0b1092802c04840e070000301000c4000c00c05000c4a0342610070180c00a0b02c50707000709103d000420b60051248035451006103090b402040b10911291010510909410014028008005482004030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 512598678 1250 512597428 512597473
    0xd05070216060c0b0105042a0210020d060e061905011b1a0106021005070906110c03010501140a090504171e070f060606030b0307051905040e0d17090a03030507090503 73
    0x2242003251348000034080c90300384142613260f0b050011040da520091280c4900100c04944d9510944c051031034070031381e00c40881c0300170f00034ac0d004554000f50035410716000703d1840c64000c0069008030446984840da04803131003007071011030784240f9141c400c1020a505140031802171210042913088890780441440091503603043c1621419404c48241d02d41980801d82594070a8400c10702180d01e180c414402c40384511503181c803c0700c4090844020052180101e400c4802c240d1280020741650101c030005850141d42290040c4080b250500003410241c840da220303c2c0380000450424100042d08002411400d40780c201003940b2401c1d480d46801003170030100c0c1b5001c809041255114540380011402030b01030303c0f0b417114079080a00104442400c180c1442620801d1084400f0521150840010141c1e0313140140e00342c00c2820b0780640002c00d00e001c0080c00c1c580402070b1040709800340004110000c0340018a60103a540c05140201d000c1e12194000d5605080a401c1548c05009030303030142481c1c0c000c402140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 512599928 1250 512598678 512598683
    0x204031703090c032e140a090501060501051c0b120303040614060a060e011103131e0515030408090609040903030207111009060806030705040c0f020c0a0b0d05070216060c 75
    0x251074003220302042540b00c1248018641401405540030300505c1031030050400c03480ca8252001905943e00300e259820105c1c1118580481d6840e0f1002604000080c040c6034010f00342030800030b0818180304504008403000300c50400146980d480410125680c00401d501288018030a80f5642d0278a030030108050080117858920f80f8001300081403190504080c4001181c1c2c41785e0f00e403580e82c0c42c1c407001103903526480d40c04040c00f40b005119070304810510084650003442181030485031028421480b4030003040360340c0014425941071310040d0880e0210021a54030590109801d517840c0f1340000040c0541c01910308690b000703031400d40300b0b03030415826500420000c0c1c02040c6415290a80004124910070026000e50000f04242010041e05024013040e9410190050542d090a9143d07004603044404030005070000403d0783c2c000c031001d03d4043c4640c250402e02030b220203001a080151848041c80b88412580e0050755a80002d0300c054402d00180c0c0444484824907621207603a440300405488410005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 512601178 1250 512599928 512599933
    0x9051f080a0201051215091f09022b09150207060b1f1101090506040308010e09160e090a020d050c01020f06090a0b060a150f0f020a0b0a0b04020403170309 68
    0x8160100c0c00180850a560305940e0b00340740404580c40c0d106401c80181521034000a54040e120960356029940ca202d600442552002c60120004284500480c4d900880d00b003441000301c00421031440402c40005013011069001190b40c040c1001c006000b0080082c4c03501d20361400b40c109000b100c1d002440301e64054031041c04044094810030060b604e41041c42c40400d49140c00000405000e40c58501d860b11035000009408840c03034680c14200242150200d00041c48000144020705501d40080e800c0b83d0988021720500701e501400b0128403002d8003030a11890705800000e43c2c1d0043c1004403401c600e50141c507140d111800ca24101d903962140040180c09805100c080c00c0c041c100018003035101d11203060003003680140a4490511042c07000e0f00b00d41d048031013041c0105440b04205100b482180030756840241828414200070003500c0040341d12811900000004008261058200f50300050740a05c0095503104120005000b4461035000500b0121541140d108100701003000c1c5108003011000d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 512602428 1250 512601178 512601241
    0x1403070b0a021b1c03030e07030503070605042114070c150c06180f080a021507081e0402061c06050406080a0210090806010902030703090b09012a140c070905 69
    0x4100f120852006601c0c4c808648980c100041391280d0041c0c980200e001c01078404254a0f51119401e5a201840641d915501d84003880100b01c0d40740d40d61a07040103e05100b6001c151544001441048012000c40e480d95000c5500410300c04041ea94030f000b86840c401031900201c104502500e07090040105440c410b280c1842000406008442c01c000158032810580d94856142d48000300e640128090608500c18001c00e103142071341c00604070303004120343d840d90801443c0404078031746d01100512205072401d00d9001032100580b01c03201038800d5034401c50880060203050179800b100404680e03015640c41400d05d40001000180070032940b0b00c85000b03607050002030b0800c1509882c01042c5e4031402e2180d62120004004502d00d6601558100c0e10a150204a01201e1388820500345016560814030f03940d1101542240180c90341007010140c800c0b4580440b8014480d03020b400c0e45603d04021510300340014501c1071240c414099a4050181e1050030482404c1c2041c00c04003008005010b04480a00d440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 512603678 1250 512602428 512602483
    0x3030c041203021e0f1b0a062007060801090c030204030807020402031e10031a01081903030b0d0c14032802010e040903080601020712050604081b12030601021608071403070b0a02 78
    0x281c0700b06d001070001d040000c81d10300d024011502005a2003080007580d82481e00454a18400d00c0356500400003656800c4040d41040c00000c02c41d50741d0b500d660306040c030421007040002c8808058175460783d01154016100c0e0399114005c598098500c4065000c00c900f101040198003030024140180c3e8090004480c4031b8818035092043c2d00e4003070103402d08542c450b010610a5140d40849a200380d44039240109540d590000858416982e0b500304881c10210010244085d590600382c43c080d00b10101c004001c481180d20000c0e42c40030340d9940e8064100490030084056900481c1c0c054000440130f00104401c203107030704004180060580d891401401441d03c002140212100200d00054104004c0c01c001e8a9039031351f030000c640c4200308000c100300c0717178903881040c000c400c7c05941c41c030a90005d07540c0d0341c17440e00c9000203051000d982c912000c0000e40440030302c02c0c0c044c0090541c0640d0702d001c0121070404030801c0028a4180a644a404646030004a4540c010b030f004c40c5c0050f16820700c0c0d030138090007038102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 512604928 1250 512603678 512603713
    0x7050102060c160515070504030204050702060f0a0b0402120a090c06020a030801090216081b010c050708030f070201111810090305030d09060204171e03030c041203021e0f 75
    0x7591800c00120042c000510f250707007500e4407896803d10034012205003204007201001131303007802c44004000c500d02140070000d600301030143da544011144042c0c4024604011841120407001c0c1003600000c1d41d504a00b035160721b80364111800090040700134203461404410f21b17405800003000889130206c22503000038002e400004c2d800f5160742e02da201c10b4000d80c20b1141c064025084911042c424414070281c54002c510b440006240110f030f8090003052200c00d0030075807401d42c0c020480d464100082040760401041d03020080d41d40200d0508100e19898841082c2203001d03141d01c400441c8003000000754807285100e80c41e40003000b1402074031031004502e084081525008a6440090055041004005640b1400b81d01c0b00e150503100e43c40050a05880d680c0c1404415421880b500c0c040c0d000d146941d0101c2d080d000703d0007400d40d190740150700d58a41420070411501030740c45a81240d4898583c0c51040500a100f03c50600740901000480740c840c0800c45580c62250240c0b455803806141c6450303030000c245 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 512606178 1250 512604928 512604931
    0xf030210020102070f030309051501031208010f0f05130204330c120e011e02071815030305030703090b15041a01020717150c1308010b0d02090a0e010e06090705010206 73
    0x3020401c4c5c020002e03034600340e02a2008480441f2940203412403402034800b4006003501030750041020b160052034011000e81241c0b41a0080c034500392a6280c1001803468030072032079050b5902a540d0b4500700e0001c1c100080a40550f4001d10000d0045030f000f2100c2c890740c00c00006021000c0001d82402d418030601c15a442c844031403010346495442c1c4c2500d90030354020b00c0c02c14840003061600070100c90140082c00d119400441203240160171004040081130030200c400c15020220800c10040d10300703025038200101d0391070305c00103041c81404400550a03074040d42c402c0049640141c0744261502d004000c401002c1241e0038001e1240e0324200700460030940030420f4041450041c1c0040441c00c0c2088818400250203e8885400c0e1242c10050907880040400860051303500e00551501c40d0261540061143c4903500322a026a26107081c128081e0b0302c89518010075038058481c20a5500c900c03402d40083d01e64101820102d6081440c01c88941100003005841241c80d04203941c000754a800c012600d4240 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 512607428 1250 512606178 512606183
    0xf06060c02093603070209090115050619030b061e03040201140309152229070906051b01050411040b0a05011d04150b04081c0807140c070f03021002010207 68
    0x350000c0c00110541e10482e083d88048500003100c1c240085680003491030b500441d290103940e51512243c4000c440804801e0014020481c0c0007402c02001110a8041c7c0c00ca0506903070030140c0314440c64085841e03000480c0c0c0c0810000c2d0001d48004d0a48054902c50b5000390341c1240040d0503100c15440148495086e0703030080590001800658610b030308100d07001c450107030528900e01c660220b04520500e0154810812511503240e185c40042c564888000c80c8030780e1240c0c0e4296981c07807000c00401c994080f005106442803804c0c07503a1074140e086108021402103014281c0c166182c8002e000074010b010104040c0d02c13408860a02044007080c040c003040740c101d8482c85001c201c0454114500352811400c0c04454200034000040c8205007054001450b401c0d50711021510b60000f4051108001c10300500380018000003246008040400700140210002001d8204101a050000803403410600844400c103181e0320403640403a450f00b903007400110f41444120320620280c44078421a03801070003038030541e54 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 512608678 1250 512607428 512607481
    0xe0606061c050604022b1407050a03090503090d1b05150d0f0e01050f04060b010903030f260702030c0708070f030b090c060f030a0c02010b0604180f06060c0209 70
    0x84005034079030081c050141c80c0d16800f0740c0910410003980c10408803522200354210010406242c084500011030341850a16a00508031204001916030000102e4100da9140d140008143e0318504015007580181c41540b07500000310801d403010303c2003580003465a41003a801e442c00e240c0c5c0d10010854085420701040c81c0c0343c0701c01d00c405541144142e0202840c0700b943c00d0041200140304000301d00711751045070f41c8011000208c0611003401528403407035400c031800b030130040d03041411a00c000c1c144601422420042044c01080c903801c03d5200000103000d844040f02c980007030b00b42014065240d40040a40d4031543c8a48540020b0300c45001520300100c0384005020030a050450711100d0310790078002e100880c14030940000b205540c8820004040801c3c4860b51faa0312070404a1280041d1030503a0000811681081102d00280e070b10300044404948004680e80c080521401404000c3e003507030050f001c3d44914081d0700083d8190800300300d5003154401c95400d04190340e0001c1d0000385400d102d440780c2d4000b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 512609928 1250 512608678 512608717
    0x6020d140f010f06051b12030f0c071511090d0308061c081207050720010801080c090106110109060501170706091a090a080607031514010507020609150408010e060606 73
    0x95020717400412007070030704504d080d1501000c41c0c0041d182014840c031608074442c0000801c00a4880840041c1d040819446030342c2c5403855545810292011074100c4450482e80e905d4206488801002105d6140501500d13a07442c1b14030301d00b00540b88500c125181e0303020300030f4444003424810a841140c01c4280e8407907217150038614904010384002500902d50018400d080010002003907c5406101200d04540e00ba01d0345012650300042030311038180c0c000c0000b0b40c4200200d0410f662202c8150b815901d052909500221070741c80028003401c0307519005880c591400001007410300350426100e4480e03a80c10100c5107029917406044035030300201e101c4d48030000d51840c05612042c080800502d015034008103841851138554500500b461000c0d110407010940c0c03029546003d502d07075202080240031014400040ca40450b0001e800ca10400e00000d101c1c0d1030000301703046a9540c000d000000700c80460311254a607500c0340c4445000f002040007108561140e82c3c00a50180303411011144060107201414291 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 512611178 1250 512609928 512609939
    0x6010e0a092409020a02100608030d0b040605060a02010e1207020102070312050d0c1805060a090302061c09050d020106080c0109061112030a0b0a0506040506032206020d140f010f 78
    0x41020418920180b540c209542c0800d040149050003d48000303800180d0f65140e05034040d190008201000c215a402c00703004100c80340e8040305840400c030050f200030540065080004d4001e0241b0f8008a81c0a03c0c04908215019815400301e104000181c003100c0540645141422981c01002c03802030045e44894014000038078441445400d12640b81001c0741088000c4100c1419690400d40850028810b101514024007a004140e002420142c5183d8900f40d00d00c40000d0803800309000103030140b40d001801184406e48044a5105c1c008c051900300851030313051a1098807481c102030203a0040d07003040800b155180c4045411040c014058590b8040030f407400e00103603042c90180d840c0700814007941010114411550005611030f80542c10000b880341204420420011020f400040c0106000d0000340041c1d1101401c50790484603001c022030400040b4181c50156044403680200b4090000c13070341d0f24042c540c940141c8818101c820781a100f96a4030095000810300900c01d40c410402401c204224 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 512612428 1250 512611178 512611181
    0x905040b070507050c0901032406030b0604020f0408030307090f1d070c060902090708071214040f050a0f110a050f01020a12032403170315040f06090f0e010506010e0a09 74
    0x40b214404c03000d0b58040781c81c4000152940c64268410740341d00c0c0c0c549030700094030344241c58021911036401108000039400d42d02c0300d4101c08802026a40516400280c030f02c21200b68000707440080c01c0703440441c0da803841e0480f4014003140003889440f10500b01484045030b81c460300600310307100d5855880303044110742d06c0d81000c495400c0e1201083d0342d036030303900c10b420005a258000800e200f000c0a0311811414100100c0040820840020240d0400d151000c803446904001007401e401035007020743e481040340c840c2001402d00034800002000c10440c1c00300b5404101c0e103084282c031664022a44d640800f0341c0c0e0414003100090140801f80140c029111001c001351060314442d204114500d40010780035481051201d170440c003191444039569140a081040040c10014002600315400404d8190305103003803002035082300880700340d1281ea01c0d8100b0114080445d841600104001d0f807080c00805400701d810801040048004001e0b0b500785000541203500030042c041403180e0140010105514048a150 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 512613678 1250 512612428 512612437
    0x160210030204090207030806151206060a051201091e1109010c0503040f120b0a110304060e010f18020f04110f030402040b0303070c08010c1b0b061f0504050108010905040b0705 77
    0x20185542800302080801492000e03003281032180e16601c8450402e501044100c4c0110004980c0100f000c0200d40600860703d400250403210558134140c0380c49072181e06580c02c1c026415507078000c006100001800320f41a40000c04440a0310755450413030b89645000c201503e500c1c40c6407460780d0008102d04039403544550b60711304100d406402a80d043c03503200d0401d00240303110340c1d00c020300010704000442d084c050300180a58100407a003e0401520810714042c507014000140050047c2c1d54480ea240402d52080d00043c004001c540001c01c00c20410703000b8400e0b0030703600c8034007039000d2440c4c0c0101ca50941410703c5110700e06141103203002e0801003080210022584002c2089030010f480384800445c54500304003070100144500700501041382481056421981d03010440020801c0f4401d0312000100d0100c00c0440c41d0303402c8400305181d680c400d400305252080c03980464891101d04003042e402c0c03590100141c02503030001d0381c4810441e642c5000b03103020b5035001e0f140034200c4115800070403c1c1501890040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 512614928 1250 512613678 512613709
    0x1505160f0306031403040501080c031b070303020706091406151e010c0510051e040f020904241505010e10050913110414061305100212030a020417031602 67
    0x126581d43c40707580d0210801c9002203100740b13542c03000c40d00340180e60300048072a038006078070280681507151641150880001d50b616055040400040400c14544240c040700c40c00b0b0b400c0345052112124910b0058008500f8121076180c5014903008280e00c0491860a8000b215000f00301440100360700c800e9442030511841c181d4184212a408100000c1060081d640c002d0322a00300010240f83c0600c2100c111000883e02102521110007007000040b80c6151149825070141c5010a9983d01c51511842603407510011001744461285142c0b890300c4950809003840c601c40c5c101011582c3d4402c0195481ea0030300b65400e40c4440b042c01c0d0031711154400e00107080d42c107000920004e42c1000c48004001141c0c940404144c081000040900410a0398029207900d240140d80543ca026101010000c1c1c1c8407075030103107900c500100e86c81d82c00340901c01c01c2440030700c0e50503100c0b181c2c0c0c0e42400d0b604880254001c2c400c50221340b03861180850068008015a401d25030319507043c958001096007000780d03a48112820 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 512616178 1250 512614928 512614931
    0xa02090c0d06080c0a0e0c0708070f0f0f020102010b030a08040515040e13020312030c12070504080d0801030b1008060406021e071b05060408030901030902030f15041505160f03 77
    0x2503011101d103805840010504540600b8003035064030244403007941039402c090810480b000c144000d680c600c00445100503008281562034051a150084500c0f0000d03002400ca841c10001050610545005607100f5034400d0300208102c0c130a800505071070b105124005041641d0a01003000305007008806c80c05084008a8418540b03615414140701021040d01c03100c00070202640020210705003000600000c68981d04c10b5822340c0344c07621500c4c05520500504840300710000d00403520300740c043c200f41c2c0e0241c4007060584002148001004120031400d22050321101180c6002c2000b084080403540c05980c440c001400c00c03a039403900c07508003941c0400d42505400381c0440c403586011002402030980c0600c03e4101814500000140101e03080041d040180720b51001c00081002c160000b00b298050f5a0a090209000880d800040d0600406c100301141a0041541405100c408200d445101e2440b80b01003d4004035039007560300c00c80300102c81e4402c03400c01c2c40e0380410a403070040803411480d61452a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 512617428 1250 512616178 512616187
    0x15270f19050c0c1f060914010b1303290f07050f03040c1206140702010c020717010f15150e060406111e0c0a0603110a03052502070504050a0e0a02090c 66
    0xc2480c900b1074413002e403142d00c10912907010141d030480d000301401407210380320500815149a52049076104184104001c2d48400a060b44040744c01c1004c2c40015900025407034082c09a05a001010b90307071058103462400003110001d601c09400780800781c002d4038180c0e100b900300000d50700744541682c8003400964002d080b158000034203241200b85502031600c601c00200381003c811700c0380c00e0710703400191800e419a418440c90b04c40701a0b0000d074078812100d1000c4442e02c0c0e0014122081e00401c58183d4a101c8942081d101400480d40309440d403085901c0e235440d10500ca019041d04503641e401030100182d0104040000300602d62055010703004140301d650603500554141c0c80464619405144107810a8200c1c61850b1090324125132020020a428141031002d0859420030070194402c00030610181a40ca40c0844c1e0000b58200c2d03d004041c54402203241d15400c00b20b000396a8220740d204840c400c506040005040c2d01090048040c604101e00081c4241500d590801000d4039004080d4401c0038410310 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 512618678 1250 512617428 512617447
    0x52b1b0b040602100f05060f0907050c030712090b04030b010308030406020904181b0f0b16080d0b040515030d1419031505040504030f050315270f19050c 67
    0x1c10003041150003c01a0450342e5100909031100d9048854206142108000041c0c481c00c1034111200340440c0c58010301d0741e03001020340310344c015030408982a210104e27000341081044040307840c580341d40d500c4595046a98480d02c0c2d02318421400002c200e00b404000400c001010b80c0055030f0810702c954005800c0070170810128017190180320380d01c2c848001c213494010610a01500418102030403000301c038009801e0100a15401e0b01d280709000c408400060744401000642c0d50b81c55015138010031055540184005000113402c480740300e0342c45a0b1510010443c8281c00100140d0b0694000d00034101403601d5500c00d84403586035001c0350000c610200242c031850342c1e200214888020341074400080849800c508000c00b444513400c400e018519000c18080032942000d9031000306e90f003d203408c030ba580c0e80d0f03015140360300040908040d4003e450810081c1103000e01402c0200042030010a10702160354080391207102d81b10507120000c2601c4002940d040000c0160012a03224902c015410b24101c1e001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 512619928 1250 512618678 512618699
    0x30209040308060f01050a020307111c230d0c120e04060909060b1002190305070206030a020c011b082a03010e06010f0f0f0f11060a0204052b1b 63
    0x311000c5002500c04410000076281c29800844100001c0c640705051003030084010b03590740310b0410060300c400f5130186550596507802c40d403d00188a5810a29074032480c1c2e14100d1440c0564501c01c2404040342d1061f914010f800084420303220301240c1c0e4071208018241c0b00e024210703524656480801c40211081d1080c1d07100c50250740001c02c1c4d070300000030301901036007045802c0300c500c80c521601c01c8c003204c213124881e940e0020b01824821050304c5500b020309440e10b4180c40c28800d4400c029000030009c810048241c0203603001e85a0018010000d02c5920071640e20b022082942c03044d4100031032088404941d40c0d5040d80c0e4400d400440c01841d0b29003030103141c0321301e4180d81c109a12425241580000700902545e00032224010b0703501034104040640d0201c2c002501d0020840106002c10041d0481c00400038418091146c51407106010b03101d01781021b13000c51002e507004c2c3c0641406040d450441c003803506d400040290368210007031000010326129642c1c0503260300743ca103588105005a64404035180c00c10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 512621178 1250 512619928 512619931
    0x1506040e091504050321040c0302061b0a060507090b09010c0b0a020403020a0b09010201150f090915050403090312090803030f040f080c060f0c120403111c0801170f0a06020d0204030209 81
    0x40c1c0c02546c40780180d41d4410400107a07010380358407900b402001e0000007a40f5081440561358101c80c0182c9942441e080481c2e1100141611105072091404410500031150b014078010006562010032994884400e00028400c0c009040d000440c0c45080c3c0340031a14440481d078022a103100050300c0c1030f07580d80010341914130541012811803030014400074190f809224407090f4850780b80c114100d0768a80030240789000114442c8030f84098403a000141001101c01d4031480c0d03400c01040c00c00041c106400c0052400d20607000459441200c110060a00381c0a66071500440d1100d4004500c2e43c4e883d104510412103010b001140d0f081c00d2401c00c00009020b1350042e00c0d00e40c1000c0d00601c213510b0b0000703003003111003405000004075090801500b0040c00d10941407591040c2c040c1401070344008900041d0b4030f000f086418403c20201100060907000754003139402c1d4101c41454250591a001c407645103170300c900d406482d00404d503214607a0880080c0b9207070054280020108001420305035250041000d91a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 512622428 1250 512621178 512621183
    0x912020f032416031506030c03020409061d0f221e080d11090f0d02011e09031502402c0606090618041b081506040e091504 54
    0x440c64100300704070748003607040818100d03e880c0c24460b90a2400030405d02c502103000310f008050b1034240c0a00035a010760120b078001e1141c070344100125680d6041c00103c0b045105501e0f030942e044500800da4100d1000551405411108080c45900c0c2090b80100710b580301c59001183c85401403080c608107d4a201420300040d40100300c0c241ea10821034102c40211800b810039000d4460003440303000c14a44038513038900600b0704180c134450050400760005036041108034070141c0c14000070741003c3c0034103030780407400100300d0b8410a011504030b90120306170000d0307001c1d030118490301360000c00c80b1100100284842055400000b0011661200c404015402410441d001548488507044250442280f0000703000e0320a8a00d941d101201e090160004230244610618544190402315105070198201c0021040c0e030400240f007008582d22208a905103803101c1004400410030031400641800c183c0032066011110040403149000d0400032070503074188000c0c00807a0584100740b100c440704440048218000d90 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 512623678 1250 512622428 512622493
    0x1606050f16110703031101020903161404110d1d06010303090f06050304050606131508160b16060504030e03161514031602030f070f02030d0912020f03 66
    0x180488145403240c0880d0710312401c000529210707607545400030415030107032940340ca0325005a040c04882c49029020341200c40d40d1500510285052604112040311704640a1403000e1201c0710030041003100303d5140414101100d01d0030084003000c1d4082c1e0380808402c15000701c03820400030b00d03510058603000c0d09070811400f04610842c1441803481c0c50f07103280300905042c0340c0b0925520302a59882d440310720280145000700f8031000d545040a540d500310303030548004400002c40c05640c60100079134508003801c04100c0714144c400b0100303c1044103000c07200d0031101d00c048a042c0f89038036541d079401064010029020040c2c2d00e1509003403990240500758610079120784401c101414030003285150f00040005005000c0e4016905a44019100a8961108520890303003c070801c1c903107099095101d41410005800030000d003040421013800c49000d0024000d80172180e1600c00781d030741a00e01101c00e000d03440803a03404100c03210045c60001d900212030580a02550030030094090500c0718090400541c40420 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 512624928 1250 512623678 512623681
    0x30a0203190b0105160c05040c0504050f0f01080f1b03010b03040312020301060f050c390301020403080313210c03080a05220c050d140c01030903141606050f 69
    0x10710a0038003007400c010840400c0044194041c0042d20a101c0c4408010600728080d080e082440700044030100107190150060295000c0381c00000d20a60090140c3d610440d1100300712005814016405040b1060686810700c4907100d00807500310598000303107162019007048501250b82845c2001031070007000f2030342015031a0705040c900a1b00500c16100403e8807035106000421255621064108941c000703800d001c2e42da89032841d002410b1410040d403000807400d207002044103003a8002200340309181d01c250104444030b1100105400d0f40325505c0301130210042030010035202804e4445142c546072143c40b6400c480c004422000c0f40099002642c030001c02d100380b50000c249a00140900c0d40315040440030000d03403034170341c00034031140180012402102040124060802020b00342d288081d0000404c83c20720300700d2030b142040350386118281c425620300a96541980650090061700300301d640c191500311840c1c4030b01000300c14039001002c0f50328804400c1138241c00855034504c680c5000c2c0064400d1090207 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 512626178 1250 512624928 512624941
    0x3060c11060a110f0705030c010e0a15050903030106050a182304021603180317130602061014010e0a0f03020a050307081b041e090c05030c0f10020a08030a0203 70
    0x20040010301c0000e49504009985008045410860344a010b00300e444c0358840710241021469402640aa14415881d12080602c160b03000a00906414410780318541d12500d018000000d450707060b02c0c03044040d8424001441502c6c06813001d054142d00b00e00e0280000c1420038018852900b8a900c81c2d80b0080316805c650003c049010340c5c0d4004014203407401d40c60400c10281d05d03a120005d18801508200064000944008410004000031500640c0030026100c560b4849010380e40448032072540300d00c0076000040d08070300100d4035610136480107010a07441d618105118503900c5a40e401c0d41d040103000d4004030025034070302c0e011002070300302e04c032101480a0851060110340035181c0c11161281e80300c0d4504000c01900002c0c9802210140a80d00300d044240320086009003010401c0c4219141c0c0c055852000c24501d175108c412201d01480c0200b12103560360040c151600740320032840390030000e007100104050500c85400b14410303440c0d104881c41c002c0c094603002da95810549000384002c0d00003042c080f5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 512627428 1250 512626178 512626183
    0xc0c1507020d060c080c071523010b121509190e0106080703060b0f0303040603020702030c04021207080106031b0513080307030519021204030210033b0d14030c0403060c11 75
    0x1840706d05d081c855881c10350b090b21030007413000101c14074500c115103506802c180004250282130355400b07050380034a05541c4500c0021001d4000c0e020001d14610000002200c0660003500d00d19041c0f0302406010194546654200340c40080100880007103848071170f1340450181c01d10401c8006c04200c0301400001d4158030341141030f1401d40194503c92130880009401c180d8001c0100d13401c40d0319a083c0165502418404203003482c020070305143e8403510108104c25203074082c84800c0e119100316601e44e41301eaa00c9030025000c8072035981403034420002807074002d18814050001030202c4441013000e030303416030356035105507281d5072060b101100011404141e400015010440c0039204805134009804101000413250b00349025030310000c0c2c4282125605818194083c2d8808290801a81a9030282030140b0600e00c50114112641c0c00c4804c580b0200c244108501298050704030b61180e0b51400071402c506030004682d000a030406c42c441600b04000030008403544191146440300b81c81d03c0b080003c0340c501d207a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 512628678 1250 512627428 512627431
    0x301141003210e0d030e03070303080f06030109030203040603020c1e0d0908190303091103010f020c240c070203070b0408100b1e06130515041502030c0c1507020d060c08 74
    0x3404400502c000201c219000000340e400600d06a603030040546040c2070850b182c410107142d41c0c0d014040c0c400302109055004c1c2156100d030310107003003c04140d2940d000b49401c903601e2040150040c2c200384030900100d40300381c0040200b80301c039004640e81d0076864440d50103090b01140c521000c43e0301180711032200c0c40c3c2003007272040100106005000901490704506100350a841c5000f01010780c0c8010403000c0000c02102d60b0361941001d4000c11125a000012900a51180c41083d14074410721820b01220078104004d00c01d50300c1500141d0040752100654400c1a8000020490703050060410200d65041d4802c0640300400081e8000e158601d01c10000c4022907030761400c907038010741500b10384500035141800e00003c1200141ca01d55540c2c114a6807000b4104010340220303511048482c140e4503196070000181054074544041c5400d028090300b816a40da1060b215070064540000000300000d1403c3c40243d0703046007881039228900515036000400300d142100381100c21607552100605207540c0005001e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 512629928 1250 512628678 512628713
    0x2a0d0212210307081b0f031003110f0f0d060207080c03250b0420041113060507021c030512040303020c12042603070503040602030a0806011701140301141003 69
    0x30740b540c18000740040c240640201410001c03070310003903840c1140e84000c08031008a102281c2160303da042800c800703c0002c0b0079204c00e4503888a2004901030500d020243c03a007564400a00040d03000c07098505000721400c001c841a54110303828001ca101090514005155010a48014580c0c515200000403c200e01d811807440030318102c844100b0005850011441c2c1064020744260303c0ca080c4522060f05001d80c2c251400e40250402100d1140c030f405a20203040410203503040d21015944940040321076014600020754030000380d4200c5031443c510034911010460081c50850b103840051142c482c0d22510995044001a9002071306141c103420520846c0c003c52240c90910b0329041c90881c08540c110070750740001204900c0c00c5c80000c40c00710104101e50000e94080d042e0317522541c0d20b950294a980112140303e01140d03440700010155807141c0c03001052020100c1d240d0307001c1c2c1d0a1100c11203a0251012909803d90741e5040781038001507441d550a80300c1d98000c9103a001ca00d0851a14582c0200280c060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 512631178 1250 512629928 512629993
    0xa1404050d06020d090c0f030201020f01020f04051309080304030e030d0903050d200706091a040303021216060e0105010f06030b2803060903031a032a0d0212 69
    0x1403000e552440000c989840d0081c0015841e02c4900305080000c281021000b4070450700c21000040102162400b901107a00076002d039048058034190300c6007070b0320031503000442d1503501300300601c940d1421100035402500340801c00203042c8003550b40c512290f4425501500429035000341e541c0c2e18074003002002c0d40310640e8540410704a00c0c541e01c0643d501e2000840c4000e102d00702c0708614a01800b0002031491050f080b00300c3d200713540e60700c2000c0c114075110700668040b2541c4035800c032134590b500012070b0100c99140e40200890345c8210f40300981d5800c00c83d5240034908050800c0b502190242c042d196004641200019941d45407500000c81400b8a500c81820b0509103100c01c4050f6980c07004450044500b9803020f01500c041c11b400440110480c1c000900300c516007c051414980c0c1a0300c81c0200e0100c405030b299141610000b0503540b9603800c3c80680040c00294038000c010f080c0302144400c0c2240140100d94080351503400100040148480002c4581c00701e01246414981c100800b000b0502d035000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 512632428 1250 512631178 512631187
    0x170108102301030b0c12040b0601020705010804110919020a0f0e01020a020105180f060a120b0d052a041a0301060e01150503070e0d0b070e032a03030403060e030a14 72
    0x281e81c4624014070000d028241c4960000d407540100303000720f903d820808268003056141c5413810900100c0d080c1c80050061040758008079041d4003c044560103207070011070302d01000c550002045006680105000c91003161207005140010280c0003070030103002c441e100d200c0c0c04284c1200007405103650101d0181107602c9030441d070001d40d030050111680c1d01c42600c0284043c441107000f280f140388034240b138180c000305c0002d0710060301680801c4003440e580744110b00307200c00c5030109d04006207801c0c0c0b888040c00035041510480d10310a40e50004003c3e40c1240004155200449000101122441c01d004c01c0b40203200c19000805280070b20880010740030001c03600e0600d5042c2003c40940b051040741c01c0701030007400004181c16500480b802207000e0401001c07403c100119143c0341c0300c1c0e20801d660f01c001140f1290400b1001e07103800b08901080e4440480100303180c081904500101854038524a501030200f044040042603940c0111414100088015543d90520020045c01d050006101c08000d080520 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 512633678 1250 512632428 512632481
    0x7050304051002160f02040902091f0902040b030a09050a17070501051b09060f04090f0c03200a03110409060803040807090204080604020d140607020d0f03060302091617010810 77
    0x22040501e15030070070451085c50380c00d0700c0480c004155408029601901100130400c081130408206c44805640d07443c2d004505036124040c9003a80560b01546080510904c005440809164000c400881c040d0040311788259480d1101d25800101c2c0e203a004401d01c0000d40c410902c0401d00640e82c11a5030007810140d0024008600c0080740290815544521300c00106019148240010f850107007484804c10404108054104002810340c5019400407904180302854062131300000401c0a000361198a80380c9050120b04400a00b080d903108004036005200c0482c0d40c0d1420301c02c0703401800300f442c001c4d9521170034144214a8100958001115240100800e12007210041171040d0016410740e050324590100e850301c002c000340744d103481a130720744509010480c00c0c07640050369049012007030310b50400600285400301c0548185001c0650070a0000c1d000c50b031206158501010a00e480d443c1850580c4000984000c0c030500070303408800c89520641034000103111900ca01d07440d0302c8071a1540d480c0c111194 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 512634928 1250 512633678 512633707
    0x412020f1f0e01080112080a17090a0201140307120f06170606120d020304090c0504180b010813020307030210021501090e060601080f0a0e1204030c0e0117061303120507050304051002 80
    0xb0070007000d140c40440c02042362130085112341c080001804110389c3d9071a194414a545011703402d4107078001150901521140a0b2460850b400b81c406551343c02c440b60b05101482d0050700c103403818080c2c0d46544500000c1c24141c5021541c02c0035480c80042c003580d050541c10484801d501070211086170708003080140a0580002c102d41c100e444000010410b403a05c0f403403d442902955200c14114101c003000101c80e2061030b803105038414001d0304c1d00c0c1d1352911841584208403502401c02501a48418420700143c03420071501c48108203d4411210310030100212407200e11002c0c0e200d403100a40b50316690a402000780301d200e40c000020310703208000340350405500c40d44c68000b500700c1030760f15920165016481414080c2d00180040c9082c125035590396460718000405241c441c0c00c4003103250400100b03441c0807620080c405107048000800c4c040d112126003800034190540d00b18280030015080c181e0500036401114070901103a140d080e103900c0d09003800c034102080c002e00c558642d481000400407a4100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 512636178 1250 512634928 512634959
    0xa050c0106061103220f0909060c110a031413030b07080a05040b04030c021f050c010e030903120307170712051501080721020d02041d0c0412020f1f0e010801 69
    0x5540e04d5412424070035180309017010042d0441e41000020342404a0410780c1a080f10b08013501c41d5808002203e240d20040398500d901030741c00e10304c0c0d070800385101011030320901c0111501592003d00d149080400071a01a62041c2940111404c0d1003c208000040707030400c6085a00c0280c5145c14080c910381a550b60541c2030000b07000030280003500200e070040d922031180102c01c0201c000d500410703140c10321034050041e400c4035200881641c201403058402520200c1541c1d81d0340806002402450440c5e24000f171590801041e441c07c014100000d100d5564110031041d000d42042d450340107062900716440c00a480c0c00030810400707012448840e00c100d0340e20401c0a40d00c0621403811450b0840b41201c08170244940d00001400b01e4004528200309481a40c010b00c2107071508c100c00005000c0b42900e40703040850880c0e900f42d138440c082c442000810401d40100d0141c600c0181200f548a4284000035040c180010041c2012180d2005207a1030303036002400c80410307039801d080019036585080240d4110460 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 512637428 1250 512636178 512636197
    0xc0206010e25030e0a14010c180b030c0c191e0c0509090a020901080601210b0f04060e03030907090b040605030c0d1a01080d080f060102100c02030405060a050c0106061103 75
    0x2100c81c80c2c8800c40d21036030100b00f84103101c00980e02652240c0c1400c1d00c920300701c040c00240f036518242070240c2850046800c41c0f01e0034008500124101d00c0c205c03008c940794000400c09900500100304074044800c040c0404458141d054018114040142c00d2810070251086042031500c602e6103070303000100c1d080c0c5000c603084410486c0d43e40400d42d280707540e0a003071040341c02c0020b40106101002042c0041e021444a0507200e145625041c00301030701c6420300740c2c4401c510b0007400100e0401e0109444aa04150b0240d026000f1800450101640f400b4280745500465a841540d000998240200c640c0c60003401100d502c00c840030311200e424000000d8451150300b100c1c0c0d01c14196101031070300f040340419540103907440c100c01030402580d64880141d103a143e0013000400107000040000d0000b00320726401ea0007082c0682c01400e10038a607075000d000903c1903a4030f90080d80b10500000171190f0701c5400911250300135980e07142c2c40d14184c1d1461820348035240c002405202c200c20043c0803506000090b500a001e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 512638678 1250 512637428 512637481
    0x1a0405070513030b0610021911030c0a03081902071505030a1407110105090114070e010908060c090a0f0308070219050d060506030c150d0c1101020d0c0206010e 70
    0x115a15019500ca120707801940110902d20301002041c043c400700800d214a000359203d400541140340100c0c3c0310b4444480a81030042d24214003404240b510490441d0154007804486250500900060000d00340343e1003103410312000a018074522a00c81d610b116211910300040c160030b82020303040d00e04240d99100060401a010000424140c0d0075046200c10800c1080041d50609003c44020041002454080c0d00f0b9820900492100b040c144078000800658800d2651035890380e03c02100c1440b41d100000341001185007001c1004003062040b103000303012403145d25641f14402d1061050a0782c06034010040340c0445082040403c0e1944112a40d850741229440322110300c0c4600b000620515801c2a03030448841ca52100c01c01805502c154001c06c0120b04448404e00c0880030860030b10201c00314210717110000d00c1111702a01064006401d444500d007800540048402e141d1400c9800200c02c0e80c40b860741715020a8403142c1c040c0115405022502c070106c8003480d04260210b9500c984115580e2600c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 512639928 1250 512638678 512638681
    0x60f0501290a0e060405060d15061d0607030c0b071d01050309100203060a15080103110d0f030f1b0b0709150f120f051015230c0a080a020714041a0405 66
    0x4d580321400c03103000e000001d2429444520a841e002c0080005203102100040e600502081071401821211940e041070b00c5003501c18040c1c101400440d4008100440510590f03a5080c000500144101c0b84181040d50320141d402024800079031028207003129440c1030041c1041441004640490702c003624401c86c032009a0b80761116000725607100030b640c0c0561b00b801e400340c211a180b16404480e4074103e9005d190b14150740d00b034180410104888a41c4001c1240010b201810002401340031044d22140d12810400c4800300d1205c80841c201d90a07142c103c95680010382040400c6404c0800ca0780a80b03001c00076044400309102e4040d1852001c2c140781003d0040407020703480d00440135004005200c0c0001014403007810410381b03d03020b01c51a0b0140310380020701c000c003641c0c0c064400d080c13070098004410400e00c000e0341d03140080d6506a000b18100d440c0c0f0300800750540c020418840c010030031a002c0d07034010184103240114403400018402c5000d4032890421a400c6958141c0c1c01000c2052803040b40d002465 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 512641178 1250 512639928 512639957
    0x105070e01120b06131415160f030e0301020c0619020c1203100f090b150c031c15060203030403030f062d08061006030509070e041707060f0501290a 65
    0x81d0083c510507030300c20b1a1760407001c1500401c0d2100510b030b1441c00d603180420243c140d02d0f0080039002e4600813941240c0a41648008203540e20448041c8a0203401c260043c18164408a400da9100c07156101e016404841880b00d040d0240701c03520480007080100b1801c0085a503465505c0d002d894510481c0a000030000c40c80d40c440448400008061504005690302c5d42d500001001d0040c0c103003590b1041c10a2290040040d45c03007c100c944071241080918a49032203803813001c1d1905c6c1141c81d800d011a40e503070007084805094840307500240900390010768032031400b441d00400345d419001e1407110150500e44100160007040810701100c0d2030b1003504800501d5040782901814074079074000c900c248078050911035547e0380c82a10b0419144136035024006c03541c44100c11690381d84a403084110b21880f290000740420b4601d5450320f80240b41c445e007145802041d840c1c0c039043d10f041e0b07020000d440d82d0701c000402091040e101d411b1085c103405081c4000074450f4030440c03c0d050080c21550b1060005c0c0c0c8401c1c480 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 512642428 1250 512641178 512641189
    0x10e0f04060b0402040608150409210207030507030606031518030c030c1a01091a06030711120f04170d02100216080d0203161407060c03090b0a0b030105070e01120b 72
    0x70040041c01c1151244e0341c0381b100505400381039401d00e111f0103803111120342e0b5050070301514401c2a040300e410a013401c01420038030601c0a10032102070450113880000700000c1d2061180c04015400b80b1030103d00603003181062290082c8007817800031301a00c0c04164983c0440f160007288806505030408480e2200075044c150355160300d01d1401441610f50007091121001c2c0c410700ca506890260504100c44c5d80c501822205040c05480b84507030182007030001421a03481a0054103800e41414281c4503001d02070305c010a0b968011042c01010440c000c0340c02d004a021107007800580182000040c0038810919101035140d00c00402091001c87c2c0015a112240c505800c80000705640007002d41da41b5800c2c42082802900143ca4a680c098484140d000c1c0c160310488110803040b212407403443c81c003c0e80703945540c02044a146500f0506494641c0d10001c01d07640002c803881410420300200f14042600109821108000d01110034050003100c072680991380581135019512441c0d000240200c0702000040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 512643678 1250 512642428 512642441
    0x70b07020a0b0319050a09050a1104020f0a0903020f3313030303091209050102030a05030a2c07060305070e04020702030a0503030c120f0c0a200708070f0e010e0f0406 73
    0x100b00c910000601c0482c2030540248100e04400400400603a01c0c3c040410741a01d02e00d41010305250300541d00d00b00820321940344001c0c0168000e00042c50403021103004a01900014030140c04103907610010001d5041c2612010030b00d00040390031890303850075804104062071420802c603a03429441c8003005003082c942411504c404118820603001c06070b503450014003030305840c8000c558441007407140d5031f041030103180c07030320b0175100c0c160051820715501e00c1084625030002041071200c207407075001186c000c910340344028032000310078254420a0f40c0c00c10b111518248450744154100341c0b6020030000041d51202d11914080b004540140c3d88038124000a4940314070760102800e01d00000041c0315807025401d00401410800b8011240782d60b640086003410034034206c83e18902501704200300344000d48078024904100b4606451a1141d0b103822001e030345001c8040d0400e4680f40d201c90014800d216511001e0310003001c40c1242c250017581404104d0051142c0507241624800320720020508000003074000c0c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 512644928 1250 512643678 512643689
    0x625050304261c050103240209091008011a09060d06090204230a02090d080a0c12080108070b03060f0613031707060516020a11030309040f02041511070b07020a 70
    0x34420b46200300c8005007158002d1401000c50b0f2090765280400448900a00b4122070700150100c0d41c3e030b4001e10800441407008140c8141866007008840025941ca0841500900400d07460701c000c54101214075003120800d901207520400c111040c80f006940320704140358450410b890340c500c0c0141619100002e06040e080096105003440807450040c40c010001c000c1d1400e8081001603d620b4a60680c401c034030803240403941000a810061010403078020080c21420f05030f1034001181c40d0541c4940903040c11410303521001600d80d200402100108000d680c0290a80a01461075400c0500002e480441c0312116a4003e0501050341100c0c0b4032210303140740085801444090314070345081281d0344203900032941100c0c17691604010401904440b1010100018a82c00a01d941c080300d48800301684591501a907040c8810091242d05884d24000c040c0510001403000da1280d042140444091441e40595002c00031701c10f01c444e02281c0300092038412280d00e681c042e944c850311400414100748a58018 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 512646178 1250 512644928 512644973
    0x3030109091101080907030305070f14060609010503072103021609021207031a04050414010f0f05070203090303030c030a180b0415110f0c0313080d020625050304 71
    0x1050100c0350000d414651280e2040310281d02d8031001074800f00d105031074050b0b00d64440d030382c2480000e001741c0041c280140901811100d00440b5503440f0aa403408209014085e00410b082c0b003024203000213070502418085000d0602941020303001010340e0740410000d55184600c00c50441498000e02c0013041402d100e021000c061501d4903003003406503000c0a4000456800a4001603485200e4400c41c220b01c15904c00c200e040188990800010f84406081034611403500105480200d80034070828032078030354080f0003191655284484804403036004007040c003550000c01c00c0f6941d903a004401c0340d50126150b070000740c49440c0c6805541c0104440b00107000002c0c004446081030000e8101d1452007140706850824003030601122001c1035402410000f00401400e1000c0c0410346526005003c100000c402281e060151000910200980503800300b14180c00590880c1200c680c180702c4954030580002c0964022841d460300d02c403955411300584400c12074088042010000c0070401c410038900080d52 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 512647428 1250 512646178 512646181
    0x1e0f030105160807030209010e010f030b060d0e1908071506081207050f010e1c031e02070203060c0906030a09210f0e010309110904020a0801230c131a04080303 70
    0x12940d00700404001c2c2000c182c4003000102207a101e802158450303001030750b8114000740f0b1400192186600c1038032030414140c40c1c0744140500d403a0840542603503007032141c000c1403c0841003007807414000480e81c60000416089a080080b030107200880380815881003900001c0c81d24814460001e0103140c11000040c085d81d0340003422800400081e08030725010740203a07014100843c3c404c5088844440c003005440d0400ca031400303154410503004d005c0440c51420040742c2013420560b100076045000b004912140d60200c3d144040d0b0500b080a103a200812140c610b1802450b2030002d4102d00006103c1a907007a110b501d01420040d0341c1040d00c04013644880300110035542044040c16004071b0030b5846c000900310160600c2d0035882409031160b12a041808245400b1040041c02041d0000602c1a0b03040408004d001031036000901c6442088456500b1003c10301403007800300b410740000502300704a1808248810900c4019142ea102c007100c85041a80c036019940c00709440d142e01603030380420b055000110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 512648678 1250 512647428 512647441
    0x306010e120d021c081e1801050415060519030204020d0e03070c0e070c0c030b060301110a020610060809100b040b060d090c08060f0c0a02030d0608031803010b1e0f030105 75
    0x1d030b036103001209500400c09041c003100081790308080840d0494402604084822211000040c4242e00041000903064800c09021609405c1d5074040d90700b10f03101059200ca843c00131007248540d0010b05401c03280c2d4002812918086000a500c90101900c01d9600091a0180390101c0d4042e020221000d0180c4ea21121142021442241d45104400c081400600001c48103845001e0490050341c2c4008548030960640d00c502600d02e0004250b9901590307190310074404443c4c82406415030691a45c0100001d1424000c0074041d108250310840c140b0003042c0c1800125a0086080c09900065910000c1d4400d40d6800081c05401c041a945800400014220345d18052541207144024044c070307840f0104079074482d0310950f5010111070381e50004c9141804100b80120810040c1201150b40c8101d904209181d840031040b1007240d400400d4580c00060990100a242200703881c98840c00c50082040e2018400460040294203a1503407217401182d80b4144117950b80c141803000920086e000700118139000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 512649928 1250 512648678 512648683
    0x20601061110090614010b1e0c07120c080d1b020f0121020406080c030c070b04050c04060e07020c0a03050304060c0c080f011d010c0c351b0309060306010e120d02 71
    0x2145c0c940030305041e200001c9030349036101e8112a01e140d410503034942e0142489241c400c3d1504005d61188480c058034500091a141110b40340f844140a02c142c5245c05140611581c940304648d00d10400340000b6603201090900c50680141100e40c040d41c45121000da0f140048030401000c1680c2d45141c455003111300701001d1180e014105403155030726540c50380d403a020b10911490008881505150104102c0e2000040302d8080f05500284a03a04403100c411302c80d80007030b003918170540002103895084410807a081c3c7d0f0401c201c9800c10030660750780790b0741030035030725025100c0c410390141c1014000d00c44045810000a40c1c051130040040c0030564600711030504855011302021008110403009200100c4540a010300c01c080c4201e117161a11142848607945a103030281f1242020030181c220501c90013084aa0984441c0c50420626842c954551075201c2c1810000903400380581e195100344442001c0c1e071114400c43e0b42042003420608000d10220380081c9000d0100c2c0b0010f0724a000e9580f0a1403443d400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 512651178 1250 512649928 512649941
    0x307030c0801060509130f081b01050a1b0206160e130905070e0f01120204181101081e180304030203030a03060501080610020a0b0604060f0611010c030c0206010611100906 75
    0x1801c000b4010950313a10200312840780143e07448882c90039440c50000c0001c01120035441d0051103200b0003400c0c42c2a03084103150804440a1401c480d0b5154410003454007518840e10007402e102131075070780080104000081d074558004020240c018681825060f0a6000e41c0305443d0b00c20000b050300060f9040d121f12500907007818072040740e051150090105201128100fa203104850000c1c00c0042030307180400d02841c4140c8000140c0c0c10036914006038101d030b407021118505180c021416a0310180c1e2040c0010003244000b404100d40d4400c2c440d20090341c800035524035421400132644d44505074501114141544100c1e40000d61501c00010b10010301034242d0000c40481d0340c240c0b100c225560705c00e020700c051320007180c07031707a80c0141c000d5a481000140c88031256504010043c00c00070380340f80c48541244440380c00c1c0e08180c01090424030034890040c000d002c5c000410040b031606220341995820042c0d035034101030050f40144040100b114000901c100181c00c490303420f000e0244683c02c1981460b40007404ca = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 512652428 1250 512651178 512651189
    0xe011805160f2405070b04050f060a1a0f030c040e06090601120b0703090314030114190e010303052b0203090114190f060b0301090e37030e0307030c 65
    0x64500040d215844104500444440c05401110b5104522841c081000b0f00b80c12002840000d1280c5400305030407200b050b119500c1100181244440044e0041c41c05400501d4600c6142c142101c1d52003124071400d90892902d01540c0c5100c0750040140028249001c1e112000d03081b41c41d201403007008140002e2260301a48485042d91601d90700c0f8162080c100b009442c1c0a0a0701c0c2c01040442d2080380310740d000107202c80c0249012402c4504080045441c3d034000c0c1c1c40001042c20310b0a2192081c07808400d03008940c011201182d0f101c616254a120680d001484003405011010410f007014044ca20048000c0358100c100507030340c0c044d1152100d00250400e54203020150f1801c5800c1403207000d0711229a01a802e41000344082800f44042c180c058030704001507001d0103854a400040b04440100558042c0018503030101e070750120701d002c035440c210701c540240344110001134022140c0120041c10b080030710038110340e9010b41d6045003025543c4400c42400395801d446000d1000050000340a030800c144c41 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 512653678 1250 512652428 512652463
    0xc10140a140c3f090409021e03010c030218010309030215090604141b090604020c07090f0e0303071704021c031808011104050f0a080a060204030b06061801030e011805 73
    0x80781c81051581449000743c2000c00e90030052202c10002004002070608000e000304041106010760f4040303461040da5440c42c0340c240c0d022411031310700d0389030a01a01c801810a0b181c2182020360021040c11114040035450b418555611455030600d40700340510b1114110341c41409219040140c102da40d24001241c05540d440f1035002c4ca440130610210b1210368195003909036100760000d900801c281c0702806826280d2041c3e080069003001032050101c5030041088000004900c2c83c180010307403d40c3c5c101c040581c00703500100100041d0f43c0c0c01613400400c503100030301210040d03030303583c40800d2410f21852628a00882c10840ca40209a407110510900304400310035070035800e5861404500761004c10000607131064061001b0700103800c004060044090005140000f41c3e50b03146005403c190211a00b5911740c0e0700081c0c2403050000b486034103604481c0030740303031035240030b802658022080c1001007000c0c1c1007544600603107110100035003020109900020b49640e80181900d840c03035845501055412605 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 512654928 1250 512653678 512653723
    0xf0d260a0e0402030f280c020709110a1704020117011211090907050f060f04080601080d05040302010f0e0f041d0c0a05060a0804030504080d0504080c10140a140c 71
    0x34203140c003d8038000e03030050090400d183c84070b1610361000104c085210103e400c6c01040814600b4560052001144160700a00103040c2400c00240a40b9110b40c103146820608111101c0441d901201d02d902c3c11906140764842a2074510040761800a00344c10740c40352124250000c20441d6041d04095011441406410800c007402421b012a403003003264102120380203d01c041009041c150526180b00c03a009010a10b8880c0b00c4901112940040c1c021080d1030b03000c4d81c01804589010010300190240d2400c02604103403656000800c3e0141035160f2400f0480700240000c400c0d1100c0740861780e400341c01002400002c1101030100c7c4442d00b898560000782c801da41465000e400d1001401c2c042e00e8000d0400c40c641440d480c41510550000342088003000400c00002035445800c1c003900c41c01001b82e40e40c150751a8500076455190401388102d05125410100c946211340f50007004800c0e400a200d140e00d901e03150314010584440804420403141000002600c8480031001302c0c0e498200180f903411038800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 512656178 1250 512654928 512654957
    0x20307030c0309020f120a0b0a0b0111013c090821010f0e06030a0b01080304180228050708070c15020307030e090402150a0c0b0106020c0f0d260a 64
    0x1c1d2250503c0180d0090840c0d80295203a091000128401412000c01c482140e803d50b5910000e006086500d401c507596240d03543e4400e5070744070002001d10407201000303000000c0b038618045640c415000e0100c21078100301c60b582d039245d1102881040c840d0030103041080005502d05101209601092200305076000294020781c0b03080c0c034480082d041e64514400c4041803410a0910024002c001d020281d15105042000000a2100030920301a102038005507486034035048543c0006051a03400e070300d00321f0050002507024206244421680450101641d18450089800791b0f418400ca54001d000020f0014210080c0041c6c1c854020841e4031510304c203c920b001859040740c5900482d03000400159200794546464034082c400190040d00040250140084030b884800244d440030074400c02003030010300042c0512281015036401859280003403d2072940c840d0002c1c5400300c480c0101c900c5025510364000034024007081e85074821000903c5002000d403600449440d64224a001800080e4009155000b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 512657428 1250 512656178 512656181
    0x20a03060608090f030d0203070507020d050c030606180f07030f0c0315050603070507060902060904020309060f070e0a030b04081b030409180803010504090f05030f090103050606030c0304080c0a0c0603020307030c03 94
    0x81d000f07044e1000c2e50030041c1d40c07041ea001a6001820400406c0420700c9218090307035888802041052081000b00180c0c130000701850b0400c42d000b02010300c0b41010311001070586910154455020084016001c01961000c0044e80240507045002c0903192030100d5002c01e4541582c4800d0b01e1944100021001695510800405220449240740000d2041c48120000703000790b002001c885100070500360600c4440030110307040384c03c1254005403590140f000c0c484605141011036800180d01d15283e25100c03018800700f496810303640720090a40800c0340004051110903030075100100660b404041044c0e00302402c0c1a40c0b41c00501500209a1500b090404481000f061810100764404c00c102d00310381ca480200030040803281004d032030181140b0310f40000a07400b80000c02d00e20400200c000e4075200745100060454400411580c010407003082804a10201c24043d01c0d40184e01480c410b0342c8025641c0d1250a022407100d00402c4103014050101707503107406402031485010141e500b000500781c0741c0c10480 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 512658678 1250 512657428 512657443
    0x1e030e0604030507120f120c02180108060117160b0405032b031e0f061509030b04080915030c1e19030c0314090a0506250e0f04020a0306060809 63
    0xc0980c4e00402c42001940b004000c810f8078a40101c4681c4518145526844990180540f40a0029640a40c03940c214549120342040d4020a400b903010316605001c10b06035034660601887c07a81d4204060032480307c0c001041400520b08180700c0040d8090380c1d030090556107411600034103200e405005654030b000740750076002210108200c19010914040242c0c19001041c1c4071031034001d280c0440d032030600003214038016011008501c220010313456141048444208454091080c104241c00b0410008a06800c82d06904250040b21490707031380038041d0000b4a01014000c2c581f108080c04030401c403800764a000503100302c0c0840381c2034299064900c1c20565251080c2054070820300c40601805003081d00c00d82c40040000c00c04e0900207990410891203103410042181c0c5e44460350f12241100040180c24845507070083d12340c184c20205202d001403410031245c44000703000d00f008180c009114050b40c402010b54002c010141085503a8a183c060060143c10180208408200c1c4880800c00703103800050b00a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 512659928 1250 512658678 512658683
    0xf0e060102061605361c0f140705120a050105010f03080a03110c101a04050f010306020a020106180509060f0601020a0b100807080d030c030204120f020d1e030e060403 73
    0x15518501c1542c140c425400c600c2080703d41003501171030454400b8900b800c0c201004d804008186802404000300710a0300e45420f2000340782c00c0c0c0c0742070801c0041e0001b00a001140c1d48807601103051034030303405000d1070074507160302007a40038180d6050700d00325805c0820840380da180030310000d0103039a0702c481811110040702d1000522400c01005240759041c403d07400000c040c0440c08026252099100c03005160021401d4084074031503840c05009080100e07045010103aa00a440c1030006140c031a60398907007000f0500c0050318503500010394210035031027980f000300a400020250f40f15003101a8500004110442c0d5031181c43c443d4401141d0300c40c040c54121031291034168010729213021a40d071307040c108450103001d4044211001e400800c42c031000740301c003c3c00307003141c03c00030311442406d040003d055a4a0101e0007050520400c02480100d44108201e11882c3e005603000310f2180f00381c8040b4804081c4524080c00c0d110910003001c00e4941c2d43e101d080b800324000d0b0b07592807000d10181d040103618403507407100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 512661178 1250 512659928 512659951
    0x24011a03060405070201061502030a080f06060f1308070e0f0702010b100e0a0f150206180703141006030c090e06130210020a240f090b0a050c0906040f0e06010206 71
    0x1a0240c5003541003a030b030249440c400491f625940d40d000000b20148041544056000440c03c540301c0c65004613895402482008221001e00700000400c110b84600300054558150004410306450610480480107110324000c4400156075038924076010030f419501540c0a030000d0002c42c0510703105020300000c007100101040c40000c482001501c0c921104c560361070700014180800a103004902d0800c400500500e00110400c2e1840c1200a05250006282012040703030010050b0707660500007405030640383d001d04078045500503683e50350b240c864007031907020042d41001c03004010400040018800c480300b0890900c629581d5507095910380c041203a03c03410340c12612200101501e0141d80b490100080340c01034851113036140d02c0701005c950000a09902012040d00142643c0c0d0086c8035808000c0400d160420a81a807640c9542200801806440e4040d480724003040401c00c5140071100401d030010851990b880e03a8812025030351000c0c3c8100b030b8000040f140040c4455001141c010f00c14a0358511 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 512662428 1250 512661178 512661181
    0xb090a0b0c25030c0b0a02070503070608040b0a0216140d090b1e0405030a0b070801120f1106040f030506040b01050402030615160606060c140102130e0a02090324011a03 74
    0xd400d02018400701c1c54082c214100308000003050380700144002902e0b4042c00c2507900c0300000e43c040c2c60000140d010f1070003540190303020011180c0c41082c3c030b50440c4e480340400320a43c4600d6501c402900410519186000002c0c80c1c00c4100303d076a22000c104820b100303060713460030160024161111201031007599407001d02006616545240340d407550118800500301030f82410b441d5404246080c0c02c030b60040f0f4080d07510806200805820a02060052003031143c02d04900b91070743c0e00d14160402201008240000134521030016943d8102601d01400340e00620840c040d58904006035520402e440c00d40300700708002c0020a003030401b03008881c850f903009840d8248005002c0c040004603407128031299a81e51410fa044000600c1600071480104070654481540551a0400c02900c521040821b5421381c0304000580160903d907003400200e80a0010004080d40d81d8484c1d04082d2040010302589030003805200020410041c00d500b116000c905803000c4940e88801400034603e60300c40001c000c0910a20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 512663678 1250 512662428 512662453
    0x2040b09010e12031b0610060c0303180219090509010605060406080c0946210501090c1806060c0b070e040c05041d04020901060f0203040f0b090a0b0c 66
    0xd42440b001c800140040841c0c00140d48050304640100c80d4400b4480600350007050320101c1080790301e801511180900c01040e01c0d00001401c0b5494458008041c03588412010110051141d10001010b80142c50301c540b52003112000d042c00401401920380345441d15010078000041441900155080a082a49001c0c20880b080c1c8000c0f000801c5ca03030791608200044d820545602c07445145511902002c081c0300006119005595030b0104046846c0b0f01404516140d0b82d0070010450044822203c0c405540030600300000d0b03195181a000640070390300b484240030402074104008011101540040d0381c0c120f10150b00d0300d0036a011031054800003102d0028860100b2000e94600d80c02484605040d41460040c20108003074680003400c40c4003152011604019400301d9450001c0b09491510f001912850070390300084000006008030f6042068149104191500030411180681410070504550580d034203c8030101394425001c0c41c2c020b51100c280002ca05086030b054658001c40345001c1c045501c00d10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 512664928 1250 512663678 512663687
    0x1f0306081603060510080109030207030308010803091503062e02010b0a08030406120e0a110411120408070611030f0610140a0e0105090a091d070302090c070203012003041502040b0901 80
    0x1d08141d600710f041200004600030240b12340c0030303141d200740c015089040c9142005080300c0030507400312107140c20421440e052031307440c60050108030480d2002142c40303032030303070000301e0b8612446100030781035402d07032412098440e516400d4286841c80590700a00c0075046030310501c21410154130070b600740c51740705001c01e003c52402042552003d40301c0c4940013441c580d1045c400f0346006a901800e40e02046800c0343c003492410940a090805038101030342900c2e18031810b00032a1800401000a00380c3d0001092003010000c041e00b00c3c2c284a070300303101150744900300180c9550791020155005803080344401150180700d0b000d8039100d001c01e00104600e0b800e16130403510640b01078010340c03042810007004006416640e030342c24034030b00050040c0120001c1c90008a090a01d280740c001c498540c0c00c1e41c0041810401a0358040e00560300180c000521510b40c0c546101180c003514180070200400b024000340561100500b00146200d1340c0299800400c070700c05040c088040748100d02403028000360402031500c265014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 512666178 1250 512664928 512664931
    0x503121321060b04090c15080f0702120c100519050a05061f090803180307051e191d0601020d030603120e030304030602030f0402010f020111040501120b1f03060816030605 75
    0xd44040394a4140746d40e25a0b500c075098111002c15801008801090360703001c000b290380001d0002c0300a106040020000e95140300d13650185012083c00a024900c4250030300210614801d1040180707c40d0900040361303030068490280c0c03103211524040c000b030340040c1580a098000e610141000c40d411005400012a88802407010024007006007400202c1d036000304000d00d43c45041294290308128494201070400e0b50581c0801e1041c00b400d500c22000d5003500410048604040701c0d140d403404201c08005c40400490342c4481400c41d006d690081c0d0304107440f040d062058a00f6426501d040c3c0d030f404c2050703007110407078080075080b1680700301062030a5001d285100f9100070003c003182d007004c1e6a80d403081c00703a034802c0340d804896030715001c103000440d41c0003145100020814002170041d0841c0382180009406184100f504001c03055903480c0048995600070340060101130900c43e0b440c010519050000000c151000c030000f0714207080051514404612002c4090707080411501701c0d0315580b00d20300036150 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 512667428 1250 512666178 512666201
    0x5070c17010920010e1914030a050f010c1b0b0406020f120a0c1107060206060103050a0b04050f04031e080406020904060807080607020d0e03060a09050106050312132106 74
    0x40e41c190301008242d408400c008091a04600742c0400c020003000100000d41d0442007074020306d2031804150b9a000382500c10020341d658010050748000c844d800081c40d1143c1c1110103000f500803420010354001c01034100e903401c480a6212028007102610034448c01000d0104060426000100880c00050040c4c004211185002d504103040400310313500c10718840c0b019180500c0c501c0c2d60707a0f00c108603550888925003a40820380044c241c2e82d440c0c80c0001c0c2d05c0d40d000038503480c100340e40c600004508003440e43c090741c1c001402810401c21031511381300da00d040e03070001d90b0117901140045541f2039242d05d400e40900d0304000c030b55071001c04a0721196a5070002c1e4109800d61a07020762500b4000c18418002c12207070008000a100401c014107144901905003600c2da40c02804000e06074400c0328a54900240854011036018030000c0c904031241401c3d401081203070171442e0b140c040d0740c141d8075580000401501c89030342e01d0504d2044140c1d450b0b54402e95803c01c0b00c0070751101c628013840c40000c41c0595100340007580 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 512668678 1250 512667428 512667431
    0x12110d0c05012403060e0c0102060708070507080307021f060f06080411060f04030303050627090a0c18060503010507020c06030c0d020d020a0f02162303071d0705070c1701 75
    0x41444080c001c21003c0400d540d030705104169810014032016000c0c1000d00c0e0306000240075550700e81d0000031f40f00d5900a10100a0245000110310317a58412411505815000f0b14503076141e003030104000b902c802041c828881840340d4801c1c14038200c5160310624040381c200c2c50719019654038205003a00d06500050051790300d904400e591a40c10340b1064014010122900320303041c2e44908500d030103422200003820050103010058044c134548489510864030380458424400349960b1455002c1d440c010061400034290552060b0006180200c00030100f03412001103000e0048544910900d03080b41c804480d96401a0b00400c1c3c00b54050030410300458009801032001460011406425010b90b030050004449050740000c404111a901080c00640840c10384054004407910f002c48020b0304134a030081007054900c44c0001c4440c04001d504a200c8900c000d81501c4609039503524803a8600781d8038010211810380f280c0020a040e10445c2250540307a40006503030740942c00c5c0382602c00f03030200c603a01c44061517 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 512669928 1250 512668678 512668691
    0x2d0c10020d1b0609050309091e0c07230c030f0105040b150a030602031504060b0c070302150408160614040e0c07060603020d1410090308040f1b08030712110d0c0501 72
    0x41c2190052144c4180224000c6036280e46120502c685601c008113240703060b0902000f4032050400039002c03d40c10095042a6944500803400c00c0c81c1d02450b51050314060300144405254405030208a1809a090803000d490150031441111403ea4000300e60007010f824110740010020610a0280c0394118400340540c030702c0b00d45903910075041b60b00954001c00040c9060401c00458603181c02101e0140c041030100c1418130b5424401c1658809180c08020700c00e040e030908110341d40ca941020789000f4000f0404803080c0285140c0003480c10003e600074980041d45544140f101504a20105c8044070303441500201192744000d0000b0103a00803800c1212401d0b00c070031000016070344180c44d201c241801a40c1c4c08185805075200e1500d07002d4040d01480e041c90070700c0c007400d020075007040e0229445604411007045211061070a40c180045c1c034020082211035400010504090010203400001e215105500324449504402c1c0d5401304002c40c29015580030071011040d40e44200f00d44070b00b0500c10400070070b00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 512671178 1250 512669928 512669933
    0x512030f0307021015080c010320040b07110a0e040f020103110c06160810060e0a03170c1510090213090204090209030c040207020f122d0c10020d1b 65
    0x2254000e80b035080c01a44006000c00f0316078135610504020810048034066000d10740141547c6a501e00001d25050640d0341e50841c405000c81003094824140140185a035551200031000d104d0300000f000341d881d8105040881d20307605201041506441c02d03190140e0440d030b00c1c2d41d41d5115485120100302d04041e224031118070ba074858200034003090b920480207041549010001c082100d02007841c2d60341081000c000303100d2a104801030b03400548400d450004400d241400c0403131056041c035803009007450995442e41404402210190a0b016040410b580c240c400f6500c02c00d01205040d10152200204002d0402894045500420301d00090b4240a929241d882980500301c4c0c100d0703403042900d079400040c418074515050100000444040760b045081584680108154a40c03a21301d40d801096000c0a00100700c004209411000c0448003c00030204001c4041070503030140145042124414240d90b00260702c4c10b0206003602022981c0104010039060404031041d203001c0340710480c1a076000320f05601 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 512672428 1250 512671178 512671207
    0x11a0306131403040f2d150e10030606110a0221010e120301090c0212090f13020a030f0f05091507090503101506050f0a030209010909020706050a05070315051203 71
    0x30803151141d03030001482c0603080c00c504020315200980c0910b031a103c540c188034802c100d05050f1f1f0001d100f13042c21000045c9040e210004480100d540c000d00203900c9817002649604400300ba03401640d10181400700b0010499030b64890084000d43c045100c1c8800031441c003003c04e81000882140c400810520704040c00207003401c000e03103a00d00c01200d0010061203a5210b6001c1e0340c0000c00d580c130013440d06481c5549100c07650700805012610800f19000e40310709a03650104c1e403140607a40d41c00110f6607600e4502d00038008000c0041081803050070050002c0c840e002c3d82c41010b1244d105080941032440c4550104601143d0090600041c00341c050004035550f2400c0001803902501c189000a101c103844040c810380d00c185a10410400c0000c110340c546140410080d00e006101034240035071501a0311006a40b1500707150041d0020500c0808c80d081401071941100340102c00b007150800040d112000b04034151008008061900c6444c2d01c010405401d001c40c0c094000310002e02070304d0500040041040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 512673678 1250 512672428 512672437
    0x102405040332061618050d020d1709040f0e0c090405120705010227030d0c060624031b1b080409110315060a090b0c0c0a06020d02011a0306131403 64
    0x3190f802801040010f0040d5000003a40321810b00300101e42d546040c0c5240d40100083c0500d500400f444000c071421034071031042440c00030b903002c859000340180d8aa40800160011050340d8170840c20154202c4456001c2c0c4600c20001c0c5610000c0c004000858003445540c45014100f203c2604c50140c2000d0030742656406800903611034000941e42e80c1010901e1180e00ca400b00001c00c41c003460b145944110380d000a04c142115140c2d08092010445d2404e1940c000d00959000243c01c00c40c20381e1415100da001c031034141b1a2180d03900e007040a80181041c4103445001200e095012910100390190b0f14004481900d820728420142c0f0b0b0f10f450740b03680325102543c1c1458055005c580e804410b0245003000181008a0700d4810360f01c45040250485000f083e00d42c140c41200b458480c001014a543c1c0024410815403400151425000b81e5650000075601d100d4210204015442e0413080c0e0b4480100e0340200c0e071a410010014505c0d40c0320300102e40d040003150388044a04031104000f0000981090001c1d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 512674928 1250 512673678 512673773
    0x605090a051c02041103010f150306080d08042010120216030c1707030c02060a031503051e010501030f171c140603150109231024050403 60
    0x551141c2d080c41403000317880800c11401ea0300710040c001407100f10740240c00001243d162076480e8030012440c0e801907000b025180c02c1800c843c00307981100c1c40c0d03070340c0c00c09005e90041d0305c203034000302e02c402da00c0510342d1801b01124070140d07001d000c10403981401482200868007244071000c005150500b0140015601d4030340d18401c4010440d00c03800001485011018034030068920000c080c503060349560014013403400d09400a118030000328160361403d00c69444002031900c06070346a903d0319180d040c580d44d0760601140728508100001d00c0d0824070101130003118100c035032089103072200030010341e01c914041903400c0691051041c20b00440c50703e10403a00a6400d03000003d400028034141d03080903000b0200004017450702030362044007540124138a142e00386044135606080044d84500070f4011081c200b00240403441040c41c080b003440301c81c1802c1d0945000f12020110b1085100700e220100048000008540e4000301e00300307000400c040760301300981c081c49452400200800001c0c040c024180e04244002c0c6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 512676178 1250 512674928 512674969
    0xc110d170c250302031204080c060d02123c04080708090603070c0c0504060b180301061502010204052407030503060a2402010b010e031009020d230601120305040605090a05 75
    0x81003541020b1000120500c02c821b1814681400e0108a0360355041d40c01243c0e010b00c0c000108111900b41560544107600e06100409000341885411408810445480c1400c01e07190a2807135918417400040b500000b90742ea48010410b40d60b59110456180c10801090b550f0240030000b0030483c1d6a440000c500c20800d580341c6001c00901801d005003c5011600040d008910b8560103201e40c4000c00c090b5035803105d40380120000c00f0b030010040307805804158000711022420000c20842e103034040d005072064030740540704044800081d41521440203001c917940b5540e01020021003010070b00c40c40043d54001c0b0042c2014242c280c0c2c1e16280103c000d440c4c4d58400000b0742c03000c1d4685202c0d60a0140c01040e4009281048242b203400000986a42c9144000c0c08000c5da94540402192900d0251401164000c0650b00c1c40d2500c05444d001d02c040d035074007020340c80d0003641c0020816a004200d0b803c0b00c1901603840c64242030600100740c805900c620f03400f03503201c1c4945030005031300d0340c4401c40c540744803104814 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 512677428 1250 512676178 512676253
    0xa06051b010c0906140409240b040b1b21090906030106060e0d03181d0a05010f0513060504061502060112050a0209061804110406080a0b062101020a0c110d170c 70
    0x68888e089031a503003040392004002c2108008000c0400195000001c40d100020202603c0a003003610344504218003120020303018001c404d404030348001800712241c058400300c15070b0383d4200c1010f003245c29600130f41000c12850409100c3c1c909109180d003207198442e0404404402d5005c5074009580e210303601441c98090b006001b00c920f10b6909800640010781c0782802e02c10340d410030320401010600781c090703030713001d40310181d00c00c1c0c505103098000c08024a030142c000c00019884000d442d141d810301300902800340c4964000020181041e20f0380003146a0000080d14041442d0350070040e1450007c0e20180d80014204915030102c164801c1d2603014910ae4036199102803558000d0100b5190740768800142c540100b01c0c100042111003894560020007120400d454842001c4100015a00150310140b80c0d840400d40c9002d5640020340a0b80d0b0f60b0040050030b4100714044200624044100d50040001112125a141c03e990304009020350806850560f4904a040c01000c050714141c0340020010001020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 512678678 1250 512677428 512677481
    0x6030609020c031617160c060e1008070210061d01050108071b060b1f0806030f060c0307050f190206060f060a030506030c040c02010504020910230f0a06051b010c0906140409 76
    0xe604010232041c1004801c604503500002d081d40e0025082c0401d11008400190405209204441507005000000c100907525070780040403125440300d2600c00040704000101d101e60041d1501e41c42001c00e03544440089069940c7d0043c3c2036540d0504850150b11a00c92000d50790703842c0501081c0405c01030000501000904000b8656100500340038041e810143c8051071040b0041005a4018046d240155580d103802108032054440c401030000d03400008101c030140d10080c00c520754084441942140d203951a00e00410010343e002c075000c15481b034000c110414601d07004c0d4008640c070a10040c240c0304154a10380204007511001c000349030060755200704020031842c2c0800e90355004031140c1541c4101c182800c000d032004002c04610802d09900072031417000140d03a0342000c3e540016000d085d00300030075070300c000180541e04140d00554090f100d0840d105804c00301486030444071542e60b038488845614042c2e0076268441c0070580200885404c1002140b2500c0d14080c00000300780704042024540c4018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 512679928 1250 512678678 512678693
    0x90109090c11100e030906210906010e060108010b09190302060c010b120604111203040f0603050a0c0309031209020604050303030c04030302190b060f03030d050901020406030609020c03161716 84
    0x1102c43d0045525080d110143d0388000019104a681c05807259503884680b074006544940034002c400050070000010040b628101040b842d04892440c0a0491643c940c4001900e080d1424064800c8800d4113100303241d039501e45000500b00c12010b141c2c842c0115500c0340c021520542c003500410301c05a44580205620b414a128103030103004208000d4035803400d265880160804140d500d95100b01070708520010b02c00c0043c400c403402023201031503207100c041c2d8989014002e043e080340c0d501c00241c609420301d13011902034000c034920603600d070b030795102c107501a16a140c00a2015803026030b00b1080600001c11a510100000c50007500032013a01d42d05d403031561a00918010001520202c46458612404c2c0003a6550501e02d0f0480710890300804e448095501013803440c00b41480c911051400c01091207140d80c0194003c00560306159028418261158002e000368896110b0742c0c40c59520070410508607280600d400800c0601c03680c130080118090f8021800319400c41d0a8004100c0050b524034000c11244 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 512681178 1250 512679928 512679943
    0x103030e1017010f051003091a0c210708150907050f070f050303160c050a020906121014180309090702010b0d030206060a0e0601021507090f0e04050f070e0408090109090c11 76
    0x244c1c90207002400d0940e4603642d0b03279042003002030341241c0100301003110000044140d80c0c400e8180c11611010090710403025003500c00981c1c41d1030202c0c2400d0301040300d4032105070130003c13115000340c220090f0303890b054012100c5501540e08061041001d200303110000f080d41100c40001400307140215264140b5a54840c8040410341101c01848143e512940000c0e0f00801c4403404107404440c100c8180d0346600104119031020801d542d2180900b403001800e1040030350007280811600806105256203004400712400d40443c00c681c0c285e031003840980310700e203452800103a00428030320010920b40000340200b40340c140440021000358100340e0070041d250034081640c3d40100343e480424801400c11600117501c6100303581c030403204c403445000052030341c0b4029803003d4008c0c04501c5680d0300031a502c4c841e0b114041d109903001c8032540540a42540d01c400f0000d240410382c3c010582038240327500c1e1a40e401c075040c0c0c09840c4040c107100da002e00000304280c05102d429540d000a07210004460300307194269045c00c01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 512682428 1250 512681178 512681209
    0x921120403061113030f06150305010c080a020c0c12031614010b030d05070803040201110f010b121c0c0512040905151e0607080904020a020c13050103030e1017010f05 73
    0x8113100c807040d814100410501202c0d00070100ea500d44000341001405021a07034004405003074142400410003c0540c40701d08035640654856030385880d46440c903800d911030191030b0031480e8021040014249007c04008480902c05000c076072030011486109240c0450f40c3c00705440c440c5210410001e100310a014031b0400040031005090718101c5044060030500801e0406440c1c0702001c0300040441e40541c460083c10803124080742c140e4001c01d5030766800f8104210815001c0d403440c3c03801c138402c0390000651080003200500380e0001d0740e500c1441106c8ad0005502c0035030341e500c80c948200d202681c4040060000c1c0480b80d80111f603610f0260300c40760900c034414004500901c2d9881c1c550059200c10345400e455548200c51a680c1d071070207801c01b003103940507180209501510000303041030507540025103240e1031031040e80c0394074441c2aa1019501150000d11024002c81c0c40035495103002d141200040001c800303203003000d1828003827404c1d1a43c0ca00301c098011002000c51808184410f01d1f24010044244c1c6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 512683678 1250 512682428 512682461
    0x303050907150c0b06011107080f12090a091e02030702060114060c151512060a11040b0405060d06081c110705010c060b0406050d0614070302040308092112040306 71
    0x780910b401004019100c0c0301400e070344421008203440340e100719008034800f004002150a05030300c0307000080d1140c400440c215113600c50300503101d03c000305450590344190030061440c0821441c20140380007030020018100403c03032400c0c551a8104000748040c1d8000c0005500910700c96043c1079082c6541c00741800c0751031155100b4411004216400a420741d8240720200c40e8200c540c0300d005154400b6050030028030f034007007090303402c9419000c40010401c1c4648070002701448012416808910071744106d004403101100c04000030300c00b83c1030041c0149681e407900e100c00107115549000d2075003001600f03080700c503549086035403250856a0001c0c91038075014810300a06511841d02001030b00100b028480108800c0d00c4044000030340da1260300100050101502c540e00c03514041c50003000401901c40034007481e4214902040b52917129209490540f50f01c00c08051800059004001c081ca4a4038184d001406040d8880c100000c810b00040c2d5000a184601945650441c50050b0907208450308424500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 512684928 1250 512683678 512683709
    0x14121e161d070c080417010b03190f0803061f02030901020d0e1012020f12010611060103020f041a060a030b031509060601080702010f1505010f0311031617040303050907 74
    0x240c01100755a41242440c2828a114003992610b00103502556201c112560205580070140314019049100032600440943c1c4665010040120301f42440010180080c455580a10001400c4100071a000b4000521141c0034041c0c202600c00040d0140040310016040030034402c2c041d580420001342820290b080241405041201243c1e8014401042508121614103010008122079040320242001140c81075502c010440750180000c1007840350340006100342442c1d40e0080c00c0400d2141c1647d5000700040b00d410040ca041102610442da8080d1300305010850000655964100501c6c4007841614046075900e0315800b050f08202c01c82c0028841c04400c00f04101c088100800c0895100f41d090908031074986500904034010400d28541000e00761a041e031694004000c2e006a90031504266600704624503070700c50031000d644250300d03000f60344041800071588015039540c800954003c5482c0110f02600c15854203103450300255419000310750f9540610084600134800d18004d881110381c0745070702 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 512686178 1250 512684928 512684969
    0x10e010c021f03020c07120209093c0a030f030b04020f0702010c03260a0606020d020d0e15030c0706060f0e04060b0d230c0a14121e16 59
    0x40540b10004045960340104118100314003e505580204255104990a00d51115110203174200003d0040e07110b280c00100150350b8090010f190160790300c0286483c1d00d4440c4080a000704140f1200c1c034880b821403031000340309246100b0006260040c0c06aa11801e503071040e9030f0082d040f00d207000929405a8010010703822820102400c4904055083c030700b15942660a05003203454106952020200c4030f441101030313101106a401d4540604004130b420040107650700d03400ea1b034820304101e480b030258105086c1040c64501413582c21910701006010084230f000d540743c056005034004c60300900b80c070b00013140040c2407090031f12480340038007148181c00c0515270400800c1c200450004000510164991048010640340c0041d8106450703031005da0302d041039014110780100390580f605030262521480b185007100d45402c04640b0216000040b0311604000f2150030700c1400541100100340ca4412804800c82c240b00400e00c2459620a54003c0c02c214441a400340071045043e81c451085510421141c490 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 512687428 1250 512686178 512686189
    0x60207050f091b1207020d0c0b06090703060b0c06040c080a1a040c330e0d06150b071203050a0c050d090f061b030501050603012411030711010e010c02 66
    0x103242108407242c22080da504182d5403070a1145261030010070401107080c1502450340203805025040c03680a0300d03845110b02c08120340e001a1008003800802c4010085401c905165840c10f030047c1c01741c40d0100c1c4946e10f0b03a103040a00d501113603143d9041d603c4030f0200003d000e0b81d10032000240892002070b00c00d0b10790684a80007083c01403081380107640b1404000c01c040103460b5031042c004080c0d40070400340011640c103148070280304407001a2110803c241e008112070307200e950000340b01d02c40105940200519512624010310842c042240349070303071501e008a641d400d01070150401e144100300d01c5451401802005003699406418052001d050210101c25a60401c0644071542e80413080014401820b041148030480c03005400b81c940c81c5014601d280e560100e9175510008000fa44050020b40d0343c503003e01046120034441c0c80d40302c0c0405050b0402d194400503070004070600074948117403071099802c174103400c6503c022002c50740c2826800c0701003e5940c010031440341c05a42420401c0000c2d41a03004942c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 512688678 1250 512687428 512687449
    0xe250608010618091e0f1e0b0f03070311130612062301061d011d09252c030a031b1a0f06060f180d05030a0306050a06020705 55
    0x744502038070807020048451943d8401440329030800c3c4000340c2c0c0c0d81e690f828807442c4e80d04041080f43c184800ca41d11032202d03006000103107804a549000001c89a08440003c01646d010340d43e129401001022569400304140d80180d40a400341400c43c0303e03400c04200000744040041c0c0c001a0508104100020440b40c5000016400c1000442d140844004d0320040049407808003c50503c00d00010403007075400800600c2c9800301380380400d025040c140c019501c1e14400c00c0241300c040101d40100c0300604004400603000060780c4050000e1423030b0702602d211680d8052900e8000641750001c115084002c05503241010310700500307001000408c06000c69110030020304040c05000e802e06415044d801804c40d21300c0700c107401121700300c9260903003444042100c1c019548207100c240d111f40444c036a0720b020340031102e01c6c90010100318a0500343c034403101348106016804a600c0030800c8002401304905000410036200c030341c2d0300041c0301402e010400c131206a203904240d00f19400510107020a4a40e010304d01d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 512689928 1250 512688678 512688689
    0x11b1701030c0312050f0c0109021203040506070f06180609021f0f0f05091e0411090a030f0507180b01180602030a0e030f011112010608060901030206070201020a05010e25060801 78
    0x80e4403044130041c4c0e0203214180030b4210101000581c003044035019840401c51910031a140c40403041015a49990303806140a001d900240800c51800000c04c8400618803c034820400030a44003030204800c51310304c0300094155111500c030100743c001c500d00102070303410b0b0b41e04046178490162070080000b0320505c5008604c1c2c083c00401c16505840a006905031000603400901c1c2c0c2d0a19039010103010301c41a5204001c0340110705105086413801ca00f40d040d5501e0f00c001400c0740c079003185143c98095a0084100d0700355918054400c0114080d8a00141507401d44105500407441c05120000101a0050076121095500940300c0c28060294003000701c8485a0f102d11303184005260800029040c5031010311500700c04c1d131a06003050000803c06001d000d10316441d210320b10090387c0c0c8242c20f41e41ea540071907046078001340c900c005100502c2e021014200080c0188112210103525030742d110f003100c0b1800d807407c1c0350f40e00180840d11002c031545000b01c00240f50842040c0c24a2a00c080640b40c054180100c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 512691178 1250 512689928 512689943
    0x50f07030306030230030c1f0632010e0f0f01091205070303230d05090a0f0c151106270106091407050c100b12011b1701030c03 56
    0x4010030300d48207800c01c0340590b8008080c80445001da00c1c003440d100403200c521211003484070000300003520b0701000b540d21004180c0064000d44405e041e0855551240079a4813400715a03880001c10b0340d0100304441d8582032580392590f01140c2c0d6000e0328400c1000c036111154100482250141c002d600c603040b10b402600c8040d515021054801001a14600c000f90084403416030031400040c2407010000e088002c903402034454807020034070f19990207810180c00c0c2e950811250104828160200254041e580c0a0801001d542c0f0341c491960700c0d61400418004e007507840c1640b001c0144540ba82285d044882100c0318100858080603114809498160041c84580000101030400344540940903d460703200c05080002c000030364681d102e03480149410008010f075000000c0020703272074900440865140a5071100144156038070103074003038090308002c2420f6400c00318080d0118003a010900821034040f801d485005032010800b0001085420350014140080a20100400200c0d058018000030303244c22404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 512692428 1250 512691178 512691187
    0x60317070210110f1207022815090810090b0717010504050421080a1d15060301060f12050606240901050715140709140f0a05040903260403050f 63
    0x39128141450f184140d41203005178602c0044594004008202c403902c212400c05a48081200f419140d05940410402400d00c040040c004a400c007984c54110115a2600400c40b40c3c0394940581800c0900840940d604e44894140003004902c1c030070300303512a2403131500310304122408107610080d50041c403e0300d0043d5601c0c40840d0501070860017a40c0300e40354001448100710100100104480c1c0c7c1160080000b0340b0b0980700d03459880010900c1c40340100450024000f952008410729003141015002a81c503644e07a45001030000520b01da01c200800c2c03000204a16440542029800d10a008095521603440006403100041007500c680c40f43c419003041caa0f8a8912080050360107219445024080b25000386640c20061075541000811a03040030a40d03403181c5518209403170b5403416010f418025940301000c004241088440d00390003000003044002c0541d41c80c000301c0d0441e44010016400608400746080384045290882079a01100e620405445d240c00e4800400c1c9000d04448038810f943d0008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 512693678 1250 512692428 512692457
    0xc0304030f060b150d110315041515170a051e0a09061104060e01020c0603130809090406050f09030a0801120602120a1a0303070c031b0b040801060317070210 69
    0x740603c11518028028442c1c50020390410140307500301d01e08a1003102d0a02951902d4100d008040d01d00503250015815a042c102c5010000502024081d0900044c0300d0324000810103400002031810f04030716101d001861400783c0050401010040c9401c03080c0341400244041c07200341e03000d241040c009083d26003c0300d4461740c0703108020340702100300079001909000070b442c3d151081070000c104403042074607011040ba0b1203000598403103050030381740c2d980150184001900c10002001d064040340c0b04027021885c3c03214140001d030404d2400e0340d060316500d41e61030402106118540040d904064080c00940c14185050380c02841ea400c1401392410900e00042c4550400c40c89405454030000d90200e4000340f864890f0510006210717600c0b04480744810550303004281d09010044519079038101c20341c04203240c21a1540309207100101a082526020f8980015a007039419014001403c80480082440c910b5810104981d0700240140008480c04203d1038005907034080482040b03403254101505518481b1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 512694928 1250 512693678 512693681
    0xb04060905031b010230040210020a05010f0509010612080316030908070f05010f02040308190c0c03120e040203071b06020c03130f271107020411030613020c0304030f06 74
    0x820f0024401c88880c10212059001900540790043d01807a005115400e0f03500303005182c5842a00803540300034424042800341c18100100f00c01082e950040b100882c41c242d4034035003100e04002d240001540e0320020301515040a024540003030085291b200a0000ca9459829041c4400340501c071a01c60308601503800d480c0203030010b826090704158240c2d200d01c800d00b403900c4040f01040c0210750321b52828400300ea80c5801442a1001c1d29081100541001100c000c0240c880f164841c1d5007051000000d035080005401502c003001442c0708100c5122100703100000500201203918006101b64018030400032041d89c0304010100b003894040b481280c00049041141c003e10513980d41300b1003800005409001994205500c500300c0d2041b100d0b00ca200ea03945c124000300e200561a000d8031050907420280b01c243d441d03422204d11407070081001e900d0801d01d41e000a04980c802c04004100320804010000146481d9040d2039983c81400030652600f0b081e8030009499100f6800002c180109481c5520b0510038a07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 512696178 1250 512694928 512694937
    0x1031703091207032313060c060b1c0b011203080406150b0d060e10080a02060f09180f132a0b0c07150201060602030703080a0e010c0513080a0b0406090503 68
    0x544072a10380d2030310f180c20020a4100c2c040c900502c031140b02100c400d810702119003120400000405048500c81c2001e40072503014850b0081a5070700c0d901c0e140c001e01c0b0b030343d02c89074844280c80a182c103d41d001c00702803403c00c42c003000580c002c84080d90448580000300e41c0102c103140d84036a00c0700001500e0012000c240751107134030035040500718131b0020880141407441c503403040c41500c001c420582010b64490f00c0580c0012254000d001285d04854200001820004003074170034800301644a03810407100d5400704961485a0200000300480c08003401019040e0102240d000360b2a1544428803c0c2151101c004954502c03000d5611180daa034101501d10b08009009000b40500a0081d0b540b1608810055995001c60241c1c0a00c01070109045220038014822041150b020303030041c48c1044003544066070020340080c01804a2512904100d4044c9802e1080c0009600207444a6441d0782d405502c111036401107030000c0610f0b1744000f108a011a810582607907109920000104446003240303001401d5015 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 512697428 1250 512696178 512696203
    0x6090e01120807330f15291b0304060801050d2f030f0105041a01180203150301051e18070b0306040212010303210218040e0309180f070302030103170309 67
    0x580f020000c81408864011810042d0800c4040c440c0b0091345901942c40d007001d00c11f826401480003421844c00c003072002925469010503c94034205040c2d40c0a0322504140034020710340c3c0b50800a03044c4a030680042e0454050241507a4120341c000c202c1d0717500d03005081040c2c0c80402140c01200d160050116480c0f140140d02c0d03001e0700755100254501507040c0030b407005480c1111000c0218001c00203042d8802d14070781c100d409a5071058581614400c2a00007075102030031034002601500c0c0381848a480034000c039402201c03101e85101d2800e11002010f00401e101030803d0800124030071514400d8000041c00300190390204284a50b651503201c0040c0080c41440e01c121481c00d0104000400d041e0270114414031000c449080341001c0c48207025031001c078400c0718604555083c114201401c107040583c403e4a01c20409403c40345440ca6207000141740c0524103100c0032140b1000800c00070032401800302c03160444640e0400790300310f5040d5960711a4407140b408a2041c81080400003c8403000108813001080c3c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 512698678 1250 512697428 512697503
    0x111070b0c0705130504020102030d050c12071707030e210c1c080709120f02130f0207020114070507230406030303050403020f0d02030f0a0905060406090e01120807 72
    0x481c0300c030751210b00c10b1180600c25100310011200c070403424021184600d605071301540c6400a2038907044020000a003410a0000060000300c400c0012100700a0040740f00740c95000200b080c54281030000400100341104041c203010311480c011500054668002114448000322100c16440840e41c40c01168000700091081c0c420500030012070703402d0408001ca480d503c0c00b05039514010140c84511040c0714010f445207256041c8404100c1c040c40308000d262008014104000c1504103040c2a522581311000c60240e00140d028119a00070150101141c41c07030b01110f0604c222500c1e40c6480e030f5104c0c4100f81c0707514403080329250045115000c00184000040040103569240d0074001c0003031008440c100c3c050300c0b56101500407008000740700d040c54000da500441c94a8032030130f4600751076008005414184050071102151640d03c850241c00506182d9607840403103890315818084080c0103901605e07803205079039170320400309620384222070902e50003969520032051040c0c1c141740c180036641d01850703654 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 512699928 1250 512698678 512698687
    0x19020c070f0815010810050702011b0e120f0c010c02030a08030a14010905040c050111070f0815071812030c02031509160602061f03080d09061a06090111070b 69
    0x140111040340702540c01c52400c4810b10ba91090b59200c402a0038080d10942e54031005041446150580060b81e00c00074030700c0080f445942d0704c5d012520449000760054040b4a040080080f281000c4118040e1031507408000c152000c6000c07a169100c24803000701070304120a803c26030040d074404000c0805001e038441459503503890071042c40c0e0b00078550244101030b004c070514000600e8007510f01519020315005405d0000180c0b401c001520800c06c0007004d0b10b10703030081010029150000d510904014214000500023652070b45082143e041c0c40140b0b00303828030050310151004d480300e142040041d24001c40700c060404106041c1985c101d420317418000d42c10b100d0f41d524500400319a02750b0b180956445422940e01444003050f0281d0b441e4070f0f01544c4010fa00141c002010180000344044100320301e003111102c09a120b171120009540300303551550f01183c40b64031078002c1080b18801c11080421000c0b8001001c418a0005170861055a5001e41001025110303017060b0076080c00070704020a402180c50740d45 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 512701178 1250 512699928 512699939
    0x31015090c11032101050609010f030f060f030f1209060815041b020a050d020d051e0910020f060106030911010f11010c0210110906041e0e15121519020c07 68
    0x9443c04c1901101d0803818282c00001e060400106071801c540c0c0c1615100c59031400b154080300200040355225210319260310740050840300c0c1c111141e01550107980d10b06240d0315241055018108124000fa0030402d10003c204580c81d4032030740c0c071904040d03805425a001d5103043d0000380a0081007240c040c24038103500129070300603000261582000d02c242d00ba54201d020201080e03880700802604007011400c00c108080d240b061003101c0c030800c2c00002180c24241175414010502a444d11009403015910a40101c418450200720003401000a0b10b820b101c590019561800403a025108540c10303c00000d12001d8658010b41c031025030800e500d030003045407c111203002560b9002c403250025600385004007040c05c007080c181c205d034070010016041d01d28042c9880101c000d640102c0d821064014051400032410100c0901301600880c5281d1414403180c000c04104031032800da01c0c0c903401456014170704900d110851908055403295000102da04208803140030300300070340b080381c94140c2a40031365100804d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 512702428 1250 512701178 512701207
    0x110a0e0909010e060a0e0f030406020c0a1e03061e11090a0e161b150f0f0b01021209120304080a03020106080303070507150605040905010b031015090c1103 68
    0xa0041121080559101c9070159400c0b5a0384802000507900320100103403903442660003000064200b0821a20180c0602480604580180c0c00c40801a082007420700f9044c60701040003405010800d611a90820140d80c003990307110801c2c07000410070350b282d0301003074142040050500e90401d4268420b100d0010704441d0210b00e6404011000d2203840701c0f4002246442885100911400312440315000b881c000034425a8265501982c24801003007012030100010821401c00c40141d540741c0b00801c046000b61215800c2d580d06c0c0e0700b5206800d01e0213000b061140e0b400204244c2c800f0080e4181541c8880c100f011078914407100d00c18002034030001900141000e800906503070310900a074001c0029a44601049844c0d00c416502d000c00181c0c05c0c006a0b01190454220007050b9003524400101141d032000072400750384208005443c1d6035550b045025003801e003804001c0364250940010080708a90008051070642e40f0f02660b6481c580e6484501050781c0203210038500d461300305003125100d9088226401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 512703678 1250 512702428 512702447
    0xd08030f06120f0a0b06030102040815041a070e0910080a030c05010c020c01080a0f150902070b0903090d06110f0c07030c15050409020c070510111b0d021201110a 71
    0x6000d101204140e204802021640e40c2c0d1894055028101441054948105d501c20207052240d2556081100080306041007005042c810318400290390145000e0800568410b8544e104c504070b80442020810705503031000f060500388808940300c2d211501c1e607444119080c4051b0f00003814078859104800141038006039450110792182c0003c1c050b0090400c0104e84920381c0c00b00c0d0300d0114240d40301040100f80d0a80210040384034450000034034446c40f69043c2070800065201d04081c0b64001003500a00c800f0899007a409201000110b07c0c0901d46c5006c1041c034202d65402034500355441c4200324401c00d01800321018050b11070740380e1352107903112110750381c591010b031208507040700c0ca104002441640420b01c40a1020300f5855103402c2601d07008401d80030b036000910524960003031100200f441c0e5603981300624041c01e50750f14040d00001d074504851501550706c6201000111050020038945c4e80c8038540015994107640044503003004540581c090040040036080b811000302d44206119071000060 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 512704928 1250 512703678 512703691
    0x20d140a02070c0906030c1a09091302090f07020606011107051e0907020f06040f02030a0c0b130905060d02040e030708120f0a05040f11030f010204080d0905031c08060d08030f 77
    0xf00000c0c0c0c2c0d0304003102c121140c61000a0403514005401c02100c40382da418407448900115600b440c0101340c60009000b144102e0f943d10780810b4410141c000c1d81804800c0950004055440107524208a6400b80d17496000604a41c100a504114904101400d1000c44010807014110a03060032014a250b0120200001000d001d2a0a80c00251800c3e00c0022008810800c05002c2c0620340c45e181c84e0004e01800318041660548114201c4130006034860002c0401450761319040c64984150141d0460052910ba00c03c00c0403a0900702405919a03900a15007506a81118000754944000ba03185055029070000940420404155190245450f2900a100b042152940c600701e0b507520250008075601601c0280c11004481c118200203900c050300d1480b5508024202c1c1c0328800300a68135800daa104d900b007000b9540004142107482c03600040300034060101100a080402e5030680c201c2620403070001680100300c1c41202042043c0c864045032104550042d06150b80c030710308a001607a9807138058410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 512706178 1250 512704928 512704943
    0xc010e07030f061109130516020d120e0f0609030a0e10080a0f060510031a06070f15020906040303050a18080a02010507050c030105090d02060604020f030a020d140a0207 74
    0x84048002010610809a0303a1001c00c1e0389507140c454480708010500010008540001008125526980c100d9444040140f4400124080c80c02e00440d95446000e01c0403c0250751008a240a001d600002d13400e03100400c2d0271000400308a407540c01f51a049141010318854051030090240000001c00200481410b0b03032507000f01d92044000340400701038491410701c0055a0071010840d030011a4000800300c10f05884041055503c0383c0014007458050201c0c400883d5980c40341041c207590301000094450000c492550030300030b2584400084944d50710006000490044a4140b07407241c1d603060740c5076480007400b455251512454098119485100032202044600c042c000d40ca040e0503105009581404014180c003500f25401075905070081c64013150b00340604070118042d81c4007446198480c00608004120554078104080c0c10900050301c12806607004200c0d218441d40010220b80d0801510140142e0f1100d18180c8030b4014403614030603071180c1d5240c2003032040710145a00074092290045c040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 512707428 1250 512706178 512706191
    0x13090c0807060509220b030d031a0d11010503040611031003140d1e0e1e01090e0709141c0606060e040603020f01081312080417030f040813090e030c01 66
    0xb400d942600665080039400740d0485440365842594088101d401c0910320001706e0003645040001b800c2100507124000000d680d2a900382108401d4551003a100e2400e82d00c96025010545840584400752507940e81401400008a4104004c0b40e200c501c4101d0602c42c03568490401c07641c0360070100030318441a60b890000201440d400a00840c800b540300910380c071145181074001c100c005d01c481c6c0d140704144c140040c40c03541c2c91240c1c44415861400601250780c01d008512540005440c10806801240b046240702d000c11041d15085000a01540c100940e40b80b03002150b9000038001b019a070030100e28040c00013020408110301d43d0041d10035241036403030304c5281881180a100c101c84441c40040c0d4131001d00107002e00d90b5401060240d4108400030503451011820741c4405000000c55842440080c0d120700c200014018005c100740320212080c024145103003840c410051040394042c0002e000301e080020400c81c070402c0054880018240c0c1c46040c000424a000010348076001030a00c20350950034000b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 512708678 1250 512707428 512707439
    0x150215010806130204110405030102070501020c0120120a0b1009030627060e070308270402120402210f01051e1e070201061d040c050603100608040213090c0807 70
    0x4006102d0110b0303902c1c00860f219142c007040060300c0380240601042008100100380c80c0c038280002e0050380e001d1000540c0d5031183c2001c2c1d50031140760300ca1200720541802c03115007008400b00100e5016190301036001125844403044000100048201d25900140b07684090110540241c001011280240d5041208000e641c485c200e2005811241c0b40311420b0904c0200c3c002002540103501d000803041c00c0716009520b0ba07a030207210350311221070781c0c8000c4100e010090024083c0140300100c0f40c41540d0540c03d00c00c204941c2010b6800207403000744a10742c2c440600d0f0400c411082941000d000d08000c980d40342c1d03140003500d0700811081d40c00c103920046003815003280050305800c490065001807000c403003040360b403000c0329980280a01080115502d0f40800243e14540000c001e0078048010048500d17810249000b10b0075040551200d4010b000500400c04034402d0a000300d42110014100408207546510008100800012590003070134603200e4002c0034402074900e00c100b0345a11030110340d01c198585 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 512709928 1250 512708678 512708683
    0x90c1b0f0c060206071202030907030209041a06190b090411031003030e0f1008101a0301060f300e0307060e10020c0c010c0311010c0f030c0302032e1502150108 70
    0x112085008107000d260f5046d150220f944c021a444020343d400e03105210703203a03400101e00010968007664141000498442000d2010411582114080710101410841200c03a60100a1248101588014041800c1c102600e840e00010001810703a40d41d41d590389805031002651503034030701041e8001070781d11564291074100a00003950501c40107003110480b1410000442d2083d500415808180d1450400025030b07020750b0408482450005e55072035100c0d07041540080036951410741040030424100c440c0840b0b010307915200340490218109040c0d000d8803000e180c10282140c400f50920611000600106000e15a03001c2d81c0c20008002c19a12812a070300c0f20402130b401000610303285904440c410320000d40c0140640d00010b8071a0802818000500b41440e00b103030700c00302c09200407403090f410081c2e0855243c403400d1000e90311801c04600b141080091180704444001d80510900c1c07035000b070f200000712804168801010303034038903041e0040d0f035190000b51181c1b03840400110210003039002180c060000b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 512711178 1250 512709928 512709931
    0xf0909010e010f0e0d140702090702030d0504210e0a030809030a0c09091a0c0306010323070c11041509050c0f04080304030615060c020405060f030703030806030f07050a090c1b0f0c060206 82
    0x82e1b400b00c1d420001c4c26000c000340d03600c000d0081800c0d4402041095142c1d4410b01900d442240501989205510101025405990200805000c002c000c40c035919042c1c0e81d1401010035207400001c03050b1241007800c00300e07261400012018100300c00b041c0000801d81055000500a030707205402c0006040c2c079095158411304020303180080909828000207440e035204c0e50060301c189508400c00c0205100725200034020303175000d840c180c3c000380c8a2401b007418880151441e0500304010341d4108296a551491700c1d01204142c06500e40c21071302d490105200c22440025941c805001c0e0301e01542d929901d0344281d1380d070341c000d1100321041c905000d100003021501002400840b0641d4469801c100125400c1000071320006010707039406080c20106480c42d4908000002c09903109449800303180c2401c2c1e040600d402c03860801a001c0b50700100050049494000d004002c2714813024000c03803c0588407806592800c00c603040e120f801281b40c000c1000348005030b029080750900800480001e15201c0108985a1a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 512712428 1250 512711178 512711207
    0x30a0507170c03191e06020d11033904061e0201060312030203070c12050403030216060e090c040b19121422080a031b020604020f0909010e010f0e0d 65
    0x4c0c2039010b400b02c02811845261440382c030010585c0313400015900d1140d901d10506070740d10781e8003050b07401c100040740c800c100c08107a026002c681140b41c4140319501070003078000c20010a019084000510704808518024071010459840340c4907a20b500c0d00909481803500019144007044098694450041c0300e00404c0d01d0700011200415105644207501961001d091101084010301c40307040458184000040c0d080d0381551121f40e61403443c10001d1030614407045a4200c0e9440107010406103401500d050300800050307a00854a58034800b11079000d0065178001d00340030100003268000d600c004643c07025000c5464480855030007929602d001181e5100e0400500d03001c452000c90b104026440b8030440c001301d40e200000d299003455460085a40128228201003600c0f0794443c0000b01499851244103032852004298030301d001d4000440b00e281f031640c014058460701003c41d400308020f4000281101da0403000b400900c084000820060200322490320003030007403054010607188568000d110015 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 512713678 1250 512712428 512712433
    0x1f0206061f120c0513060504080114091506131b0f020a0308010e1f09151a0d051905090d0f1403010b0c030c1608061008060a0504050c030a0507170c03 66
    0x410b400d110030020012940010305010301401031107200c150144002c0017501d0303142e075540d84482c60407400b03c1c01d4652007403101c82001c040c60f0800001c03090006003c18566282c074840404c0303464100102c1c401c04455041c03031645074100044a000d40701c038070752513002006082e45c40b81c40a04503000304076186e07144144014000761021004000d0000c2540040d40c0100980c0390040907201003c0881c003c805041e0f10012500d074440100d60206480007008070004c00060a08044054000d00902050321a5110803054580d40c0e82c0440e42c0e841c14012050031590b10180b0401c0741c2c0c10880d0040f50755403070f0503145100085200301c05443c1d192042150f1038110800701802401c0da402c0c020301c600c064110100000d0948018041840800c100704414402c0745100c00440c0c450504081c00503080c004004c1c41d036152520b0020042100c20800038415521640709180010103807100d103072090414001142c3d480d0f0501c100346040d400d026000c101801141d0203c00030b6034012104a52894807600a20b5007594141c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 512714928 1250 512713678 512713697
    0xa03081b03041b181b0201022110030209070203090306250c0f0519030906050909040209090703080a0509281e0e04110319021e1f0206061f 61
    0xa02000c0b00c000b0595211080026a141c807090440000c8101c0502c0009540d121403c3d000117451003011070700c00d42e40501c005d500d40754040586a5880c0c48050001800c4444040011040c40300740c2080c0d4040e544c014115581c0d802c00a038002d542c3e40000f1034046c424001c0c030010a4400c1c921060440c0354420007912004156042d4005a5038096040015140400282c0000740000d00a1004000d480c2031080602c0d01c544031410001e0a50480750050001d02004106070074607607451000003a13000360304440044083e82c4581c8161f00300703486c0c0c0d4030041200c0404560b10443d160082d019118290302a141d800848030400c0c1645e20380a442141080a005564400e010b92810807844110551140b040c0d805c50b80e0380e600f4240b980c48000c07101600c80c2c40e440120880d8614040c44240f03044403014614410fa00010f03000500140207091555240d0071040c2450701454803031004d41c1116806e00303010022241c030a000084d480b20011034117940f143c001c48030080e0075642c0410030245107401c95500d00404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 512716178 1250 512714928 512714933
    0x501050c010b03070e010e010f0f12021801090507111f2c0601030312050f011809020d0f02090108030f0a050a09081906270f170c0a03081b0304 63
    0x80d80c03140018590654a404881c031842d00d00f00241c0d0010050301c54880c011b036140c200510050a41030300f2103200040780c00307010841010303550215025245288090740d803919281c400140448000110640403a03400c0e03000240680345584058800e0314662a01003e80a40d0000603496506100440300103a0240c22000342c001c4041d4008001d04640d00c1050403814145001000401000c6000d4252544840c005000b01580a02c04402000102c2000d00c15424041110b900b160414001c00e00030030103011804030a24619040101c925070040c0c130700d114400b0a8201400d0b40920041d060340610710403000040d140c6030001c1155080c07481070b180c1c01d040c404007580480c4d095020b14904410000801e1021486c400240710300015440d030140c0300e882140062034040c058030300822500d2150101c405020081100802c80416299401124003280c0c030034030729000e440841111025896240b01107010300541c1c60000d07500352514080d842e407000e196a0030140e40c0007244142c2c45035126013000e1020600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 512717428 1250 512716178 512716187
    0x31a0d060f091e15020a0e01142109010b01050403200f0418020f100c030804170406050c0c0f010c080d06080303090703030e030c060a08070c0215030412090f0501 71
    0x800381d07204200418401c04540701d2068200d00002229030702003011000b44200102c404c1c1340c0b070ba85004008154200040740e50007405899007079512034144003905503401708101c2c40c5004c48442c41200904e20741400c04104c070703544001e1001ca5070040700350b181c039541c403200c1d60040c01a2811640d124800040701d190200d40c0c56905040d002119400241480072140785941c0c9000f1403030107040100000003060b0550042080400100074814003600540c101048030750351203200098519050308002499458500d00710f190000c0f002c0908036042c00100d80480c0b101c1d8004024040d41c02803808a481c030034081e2040241c0c2c2814a01d040707002c124000b100800241c440f901803d80c4a0218a0006020356244040c030b0459108480c84119070700902000d2081540256058407005005d030001d040882826011800324850000e1403424002030000040d00c40703106d004410041a405010103150f0035101c001c440c07041e00196070445e00258025007400c481882400c000044070141403821841c036280100564 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 512718678 1250 512717428 512717441
    0xb0414060703170c0d0b0f030d030c0c05120901022e0902010315260705091f03050d0c11040513060b0a0914040605060d030f0e180901060501031a0d06 66
    0x1000c3c002c40f83c022145031107510b4896441808060340303003a5140f10030082941140d151225092081203e019424000e45000599000044160900007a030700b60040c1c064909141102c4000c01600c08c491890f008110418041c007165502a0200ca182c08910b141624400c4004e900c01c031102440c500c4507402c1c00c1c0c0e0b150070013507245006041c00194500001d10100035403c540d0800c1110401c1c2006e006d10a4801d001014448185000945640303814440010720302e40c8007034070000300b01284810002c100100406520001d65200040f605130044503c0d01510348101400295003104003100096507034201801500c3c8039001140813000c5d145155900d540041503804c0860341c014003142d40c04030304c0309624480c1900109450002000b1441c00307180c080b0030341e08024440c40c000c820b102e10700e60010b504003103602c441000e107080440e008144140031403440b01d4210303070071240c1e001075a050003109407040d408407003a900203030780a100304611070001c1c06150301140d00c055044514080c1103c0468000e50101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 512719928 1250 512718678 512718683
    0x70914060927090d090e040b090c06120a050709030803040f060e100b03070b040303051c0b060d051803030720070f06090806010608060f01111e01060f0b04140607 71
    0x5074580002e1114151004402504001818110200780310902500708030b03150010081d80b900321032083c00c00d160124518000b40c80142a20020380110382c296400b44168441f2040140141e0307100c1100701070030758001005440c03101c1c0f900d28000226612a01c2201c242007500d0700500140d02e180c0f1503640381c40c4500741555040d110144d550900c2400200c0c1440450721414003210003240250101081508010950340500e0100104000c1040000d0b00481074540f01c1801b0400d070060703244460008000751070351119075a800440003464181d010b2701940034034000e80c0c880c0500b58051460038110b699078801903031403601089807a440d0f08000a80010000390804203001aa0300b11959440241d10444c0c042c1c2041004c280040c0c81480055820403540d1300408052074525010b080c0710303022611407845114030707030f0400c8101e42c0c500101d040c0c01c200014406c2071b00f01e1940803002004040751700a1015009280148661990015807441201e0545050320f039030183c19003109105508010701584405000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 512721178 1250 512719928 512719939
    0xa03080901030e011a03011a010905010f021513051009020f040e071802041505071101141b03040501030c03090b01050904170403030306141c030503070c0803040c0503060709140609 79
    0x400c3d0052500307000d0705866179901c80003459044041170415094443c0494280c4a000c26a101100507a03401502a0304071882824081c0741c0340c030b182804074105501d04e5120350050204000b40404420b0804102c5a91070160302030318601c1080341c11100507240d844401950207107a0001c949080d1409900009028a001044071101c1c1c1d0355010301c0c0b4209500000c0c1401c4160301040400000c02e0300c9020a204212516215141c41403ea0b00d000c0da4880230807256040140712100d81d00c0b07088000089500768005602240608a0380340720303095407584940503040c00a801c4c0b211389403001c0e0003400f49103503a540c0405000402da0804041c0140381900a1055a0000c0202001c0140e00121801400514000d5401050881c20300400e0a080d08059850034010072103400c031001c00380c0311100202c03c0e15a0624115659444040c81100ca8603050000035060337080c0041484101f006001c0201d00325030f410f0b42030301c0d42d5556055041d10005550700c600000300c224032a12000030f2528900420106400406 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 512722428 1250 512721178 512721191
    0xd0f290607060e0a1a040302030d090c05130f15030209040f030341040503270a08010b0a173004140109092d090b040c03140105060a0308090103 63
    0x151041510700000000c40c0640104c49482d05102404100701c841d440c0402c40e00e40f00d41000c1d1341c020b41c2c0340300300b2038413068541e6a07100c1001044000c4400a00520004110000c07840010b42184001d08419125000083c0340959803441c03003541764050030441e03800070280c5002d40e0b55602d88103580f1310140d00031010199608401c494600f08100d401009040e5070511040003d4200c40d00003540c00105642401580b0300c0d400c00c00003da0000c1141c64801450b02c64110140e4040b26800c80ca81c1e98010442d0300c0711102c06e002c148071005502032003082d80102e8202d4070030b941d10400400584100b100c16041504560911544188490401e845489000800c20203150000442c00e1032034025810150103003a0206c0403190540c0e0202382940640344e41c147c00c00040020241106032207949454030700e4020801d0804101c0f500c2c40358001c10300da5820010024032460a89000e03040c089481c00101c524856100061060050501c600e5205010241c280440d4504545880c5400d40020104070f040680f50304 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 512723678 1250 512722428 512722433
    0xb0607260a080405070e0f1f1a0c011103040206074205090d02030301050d020307050d03051e0703142d0a0212030f010b0703020709020307050d0f290607 67
    0x80041c001d07006580d0700d08003a400c0c1860300e6810034109600011042c003101052017954001007179519042507450034285000e50240007414607d6101c0d41c0500d04124284090300d140b6088500240b03252104500204242074918000d80200d0009a60180d0065000e01413003001600100d00040440b000a16030705810722a41c2400d000c80c0c2036038100c070180e800e20070906050240a40200b9400000003005040d104a00e400020b5076800140714081c410442c103800e94040d9102817104902402e000350243c80c0c2261142030180a41c4c0c000d10705407030000250706d000580c0b003140030265007089501d55a540c96914000c81f10410076040b0340e4140f0b84074100c00d07041c091001501d9a2200700c15800c00b07201503d41c5040c01c0042d041c5049c6007116006001c04200700000102448810f0b0b056508820701c4036140c2c000780c2422454642c5a40011507840d02c00010300c544a50070001074214030480c444244000a901c80110701a2030300c3d443c01c0841603142e00c0e02221031031a40b5400c1c4c074980c140903007040e0402c0c000d42c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 512724928 1250 512723678 512723753
    0x901180c0927081201060f140d021c0605010905090103050607140904020a020a05060a0b060304060f11070b0610090608060d030509030a0b18060c04060e060702040c020c0301050a0b0607 81
    0x2141c1102d01600c0004c0186510003400601401490603041c400119004500094414a1040e60305002d1050025403114500104e6040e00c0148641603403180b0b500401300c1d60b441c028100340c040c02d0b0104091141c002500c0c900304070000d041e60360050280c2140d4035050340640f081c040c081c0e40040c6032981800688190703103691025010880241d030041140f0400341c106076040000c080c260800f128100640c64003162103401c2100e8209030f21110001c3c000342d03128400030081035007410260301c0600001e10182800b00104840d0300030041100c0c0d404031b03010758480659042d4064411013021070304000019029140c8100c240345440e019050142c5005035120000382049200d500440e022401c020502c9540c11402140c034107401c04000041a40382085074000c4414080c6114420030055901c50310304054880d80159180c01e5030103007003031000ca44401c1c2d010b91102c40d141c1502e0b0096203040001256514030303000d412501c00d0b000c1c021a140013001d0b02c2d00805540c10b0f5403000c20409602445d002c000d440d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 512726178 1250 512724928 512725001
    0x4020a082103151f0908010506030c090615070c0e070305040c030f02010908010c0906110a020a031b0806040b09010c080f011a07050304080c1302130e18150901180c09 73
    0x4150f83c2d640c03421384145000d024000c3ca83c2015140c0c0e80f4045c02c001310354400060b6500a88002c0f81d09540c0352361803800040400c401c48070b00b030030792900200300c2000304080c0c1c00d10308095810458842d2860340c0c54400440446800312000f6080824030760b0100042044580c484449500616050540d29120360905003034800c2c07080460700207244050201308482d030040203a0b84d8210b83e0806402442c130160000781c2d0b000c9450002410000c4014101030300000c80f00003c00041201d10305a40380d40c0740a082044c0a0b05007110013060a500f00424052000c2c0320307071040c40c41803000d007000f00d407141d00740010041e112400e10701800c4032641c03c2180101040c8100041e000500f00100100311002c0101c05000d40d12540c00081c502c01c82c01070206146251002800310b0076900420301c2100d1543c0e031140522a120000044001c0f980144000305007101407603101d0034840e04840e00248250701e00032101c03402e541100703072000d0301c0140ca210041c040044540c0000031221000216007019076018070000340b41209 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 512727428 1250 512726178 512726209
    0x31204111315140109080a14071205070302130509070b0307030b030f07080c1504060305070302040504141b0f0f0a0c050f0309010f0e06090f011b030804020a08210315 73
    0x81c0c0d800c20081124801418a1411005e2900301c003810b1038084400d80e117060f4408010700c42221074501c61184c10701000410001c204040e1b50441c465201e0a0894448003103010076401049200c80e00380061403d40103050181520b0070003055030920b001c60a10440c1c0000d450b040800d40c5615068000796410480025507048060150241a02c0d2400d031600e40003200c10b44d5030040b0288034030494a442820300307403012641941404500f6690755402240284100e810883d405450f101100c840e100d0b0005049110307006101e03100e045a080301101d00c0c0369000c1c1d0b401c01d0500750340401ca0302816224105c090881091a81040e400380681540c4440c200805007104004039480400c00f5035a035a4090400754401880c1e04083c548440a000800c0c602e12070700010342d005194105010b50340c0e9105904402c1892303510114182c08101030b00d802090910151010f030311515000f00041103081000c1904127041c00c3d00b8480301c04044c000503280300903800052004802100b4441e101c8151f4444a110003800c04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 512728678 1250 512727428 512727461
    0xb0406111201050a050102011806090c0e1509100b04090902040b03010203040f1e11091305060a0b1e090105011b0230010504150905031306020c030f0312041113 70
    0x604002c00c0c481c4c0e90070386a0046045a04041449110380110b03680301c5e069541109000c10558490300340504d100310154001160a490f0404000655070700c400d24078400a0b003207844904503103c82060700346445c1075026032030170a8010841040070b10303c0c039405401260700c0170340081034040000001030308a03001141c082c0e8010361503607409000c001201c500302e0642d03112501d0305032810380c0e103868a50a04819118543c0110305a00115104219800781d0800c216804401c45280b07240007240d40b0080c02d80400c0d03140c017580b807008503c0030800140d6610b01500701c014040e09640d0703284c0401100c54140c03900d0714036240c1d140349000a0140c2c60764070104d1103256810103401d6164008102c03c2d03000c4800c0041991840e40741100b84070006900000701d20a4000c204008210a1030b103082590030362050b102c2c41074610700b489100140007500403c40c102d19510440070b503600c2c10f2040484a48904c00c040a01646070f00b9003002a000541c20306424021803009807601c0010314001a141c0c1c1250158121007142a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 512729928 1250 512728678 512728681
    0x908070605190908160822140d0510020a050f030a05010f090207030c030509361e0105010c17030a050a0501050f030c042d020a170606070b04061112 65
    0x300e5080000a80300ca40e030602000201942c0e150f0301d0743c502800d12040781c4846580117940a010349801602c5107034252043c200e5020380001c840305190891b0b44100310b20410340603642c403603a2070700003840031800381c00c8401780c100801d889420100940c010480c0c0401d010043c002a049003c140c0c0143d132050103034810000303265052015140040985500204002e4010030007000040d610903c3d101910703074942001c5403640e407103c000401079542140110401d440750010b43c001c00444100e8801141c2050b2841110b0303454001043d203c41201c1c5924050740803d19004018035485040d1412a0318043c2404010210b442104160f40340d205a40d1200398a4840f803e04c0703c01c03a002d100320b038018041100c540f15000310303d40229480314408103446101d079a8484900c0071000c0841c081040e403805245c40c200a803d030000c41207000350000804d2000080200c01d800d000b500c440071265010718002072019003441c4403943c40100c0c0d800010710445240307440b4110061805500000380c03201400202410520703 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 512731178 1250 512729928 512729941
    0x10612200a1502011a040b0f090604022b0b18010611100609020306010905030f0a020415082410030206040e090708010606020d170f13030309150b100804020102070b0901030908070605 80
    0x45031750b8644843c819403030032040f00fa9607960300726404803240303007940d40b060b041c1d0702c110004000b402441003694042d00c0d07105450500241420340e2031482026103008000c20180c0c0030902051008445200e400304011000504c0128020018101c1c11070300c40c0f040340d100321001d004c40d00c140c030080e511185020782c000c0217201c12903811074030b641c001c1c1000f540140654418464010764500d001800a1f015503943c00300c03002d0740c07050180010041c0c0314401c100c4010003102d00c03529841e1100f0030480e0030b406001300085103400c80420740040c104d980051186081c9410070300c10113500f650281c51160b4a20600d40c00090f810300c01c1c02034800401e001d40141c540103115a00c05400c0c0c1301c0310318640f914a020f03441001700c40383c034601083c2d40041e50780106105001c0c540ca0107400410082c04003601200034640000012251500281d0401c0f0003521030a2404421880036a480c000a03140240940c200341404d00503200071502510940d003051401040d541840c0d00c1c1e003905948822070039108a615034041200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 512732428 1250 512731178 512731211
    0xc061d030114010909050c0604141311070206180a0b0915090a03080a141c0c0c030f030c02160308120105030601031208060d080c0609010612200a150201 67
    0x158220160000e20454075070010302c9081000c14000c2ca0540d079560005401070000070429421041000f4201d566120f0301c0f14a801d11080c417901101c0d1050026484003c4070021a0049a40c2120380c002000d052440c55402c00036590001da00144801c100b0f0590039030a9516151340310000d10325612504d6032284004144000120161b01000520404218080c0c040d120702103020100d130b400103040740d118002d00c0b9003150a0b071001952101600f0b004901d041880c94a0520344aa426040504201496040605175074035466104080e002c10700c4020a621501c3c083c2c0c00441402806205580020b15400c94221040590360816039031120b01141d10a00051055030481c050141107004100e00e45c59035650901e00040103040d0001c2044a0000c911103494800c00b04071029802008180c82d4034076038003603550fa10300071284014107600303107140000e2509a04091091458025240c41d90714105500450700101c62400d2954000743e040d080080c4e94188003203044003040a5900101d064001180040c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 512733678 1250 512732428 512732477
    0x71b03080a11070c05131b020c0109090b0f1908010608030c010515030a061a060409021309060501121a030d020a0b01060f051207120c030903090e01050603130f0c06 72
    0x140c0700c0040000c3d2000c10100c9900d101225800c840185404401c060024080c144035403104002d100c1c0c0200b50b0551540210b00140110800e83c7c40241da90743d500c50420650710440300d10b6801c405019108001810941e03011442c80b141011044440d03580d07030320140d003142c4555200f24400d41000c68a0034650030300380981a0400401852000903044120010340c694480c9100140950f54441c03010311b103a0700c200c00300d00007210000c1507035440d140c0d10710240c0041c1d0f1104201c501050004540411180001c0c4030f04000e07030b1810303982ca5040d04825030310f207002459000f4040d12209039150700c03c0c6090790208091080a015a8080c054091032450100202c480682210091045251003001d2456005e42a24001d118101d00d250075a06e40110a42e0031039040c4440c003061508008210b58000c0d05501f1000300740e4401c4e0788100c5040c0e03490582180182080c040d59501c400d041021035252943d0b0010b500201d801480d00101851903030780d0700d20032088194052030224440c070119194807031a444101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 512734928 1250 512733678 512733701
    0xa0503031c0e120f0a110d0801051216050613030602030721020408281406090d02010921090b07050c210c01110703020402340c0e071b03080a 62
    0x60034400c2c0152802c20442c003402c003004d09180b0022888004a901c1440c100c80d001c030214007a521040d11660000704210702c24003c11b03001c0e10f0801e2030790701c024600244041040c03881413907410807070b81404200940350348030b51450702024003102d0740030011502500c0150b00820194403140008450180445090300c0c00400348071501d481404100080f840102e15000b0b0490007040080c50b1001000701c02c2d07214545010007800c440b821200380030b02110005409800740a418044680d1a8900a0102d00341c1e074508600170100801040720044052401e001801e8420860034801c4140b5220241040e444d0410300082e10254403200a015050a11200802511030203002e120380e503203050000740c1c1d070303400c0c820103403a0421035003101c0b600c203003901072010344003840d4000e00c10b641e03d4500c41c1411081041000070708143d94010ad01098540200310709403510298410100402145840321003500b040004080a040c000d0031101d01c85004480081c0041d19407094850700742906000c0ca11000b04c50aa000700d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 512736178 1250 512734928 512734933
    0x121503060b01080c0706150e0a0c0e03010e030708030c040b03160e1e0d032303090f030a0c030f1b0501020309070605130e060411030f01030b06030604030905010309020a0503031c0e 79
    0x788644a0345040c00c85901c56000080071405070404110114500f00356032108280132194418464848480d8211012b0100300385c2c0c07480c508280c140101400c03104c946608005540c820003000000501c100042c5500c0070040d04024242580c0c3d0354513000990089a03001c058204021004400c0c9800c0040c829900b502a6440c03482d601c004d00ca000b04901600b15420322940704444103404040c841c1c55410b45e200005e0085004035810041403402c16002510340130710500031000018942c9034000f003529403a02660b600c0c9819070025880c103a0b68101c021078040c0400a14440b46003441c0c000c0050001e03c24400c400041e601c3c50040085c2d41000f00e503400c03440401c40200a00c4141c032841103194005e49104640c3d2540d5501c42c0000100145440100400d1420010080010300d03480c02039480d048038040c0380d0602d6107680e8041019114101100c4c000e01203120301c0c9080c8034a510951080748a1440540000a074980328000680356400c562009419450380c8203a0710a800720074081e40b0302c001e011000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 512737428 1250 512736178 512736181
    0x3010c110d03151202040e10020702030f0f030f0d0b030616020f070602120a020106031403030f0106020307021e011808061008070510030207170316080c030708010302010e01121503060b0108 83
    0x401c0e40c20030640c4c03095030600020080a84195500d0340d12041d00d0180500c2254441d46015980002035000241c040c0d21030301484034104503034400821000b400c010018081c6103842c0b14501c074070b0342e10740000003080c01c05039980c03190000d20348042015a0003005c030b03c007842c0d03480c1440500082c60000790145810300394121890400009400207517800303102084d01c0f0740607100d8003900b10881c01000e80780d20140c1034451b40c440c0c41844042c04402140074049029182c4026030706d03050140d90324841d816001350000490800d034003400c0301c05060740c45442e00514025480d000c81103c01219078003560000d403000d401003010301505125040b03d007401070941001820a5514107800503140100ca128108281a000546181006111480300c2e4291000d42d81107610b9052a95149502e003400140400101780880b020450122100301138912401d45541c0c0c4142030781c2180d00454940b880d50107104e051091400765520307120a6030203005000c809884036420018a141444000d56000f901e0103418401400b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 512738678 1250 512737428 512737451
    0xa0804140c090402130b03030d1406190306050709080105160f0903081c060f0603050702010506061204020f130603030e100314070c0302070308040303020114010506030601230903010c110d03 83
    0x7000d6507103c0e0b01254031034012000c91038800e002c1c01410701c956a16000000e1202c03561115a0301c001404941300382c2c001c2c02c43c1d40d04804c3c07094000c90101889101001c41004100045081e0030142c1d000710246008403500796038680860a440d41034030060243d2000c3d4800c0c0070626840a0701c6141c40740c440c0703440308400d4910389030003000e44070b80701c00c2109124001c42800d040d16810b80086004141000c50981c40a84c1c42e20020000e000c00c0e91058010350030040490494a04079066800341c6903c540e61103003d0301d59030300304805020ad002e501c0e500203410100c640804021031142d07000860081e1152060041340ca010800c080110b03061440a041c5048601c0b003180001d00c40065101d0441c2c10300c02021046814241d1908070301e50f200602c000c40001313003c01013682c11340001054030303601c0c0140d80450b602e07102080a0741c001240e8003400070f5420150715851b24800d84805104000c0301180d28900320314200400c2c20340c0d0446500070003090007528001d100160801500c0c070038404038941000314440c0308 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 512739928 1250 512738678 512738689
    0x7051c0b18040501140c0a1209120e0d171309020309073317181c09030f030f11030a0c14030d0509010f0605060702090604200a0804140c 60
    0x80507200008101d610014042140951222910001c1c1c8511a1024a8880d28660701d552000300720f400040c0c00345010021019042c09201d0b242d65001428402a0300544802c58121640050003075211104003402004500003060b00e00312181034480240d0785141c80b080000c84281140e00070380c0c0b21841003003000040d4078049032210907140100c40840402151380c4810160348104000343d40d003011946101c05000d6040f900000350003070f80c841c04010b6951a110746903000f1511048040064004003000101d50708404401000401c036800c0004d44c1d00e89a40381d001e02c0c281502c10880100d400080b400181d00c0e0401c00034000140710000079813030600b211000600c0c090b0b50200c020030025400381503202d061020300585050300d00384030041006141014520b406401c1c0010340132141d900e4104040b03424100071084400094010f09030010030f48550301404014200341d0340d07401c81b04011005041c102c501311801086500390741da4030880c9900b4142400107081d90440c9280d00f07a0790117882814016100c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 512741178 1250 512739928 512739949
    0x1401030302030d141504020c03041d06011d010207141210090606050a0f05040c0c05010f060510050a050f07050319020a0b060901050102150720031207030b0a0909110907051c0b 77
    0x1a1b07005030319501071400c0305166000e550000c1d00c40c200f0261030720381a03500c4a090385115800036a140d460000302d0382d2280d680203401103211801a0413002c0c0501c8014001202102080406402c8005012445130001e061100d40540402c56036101c516005c10700c20300f401901d020706011036000f8041c0340380c4003036021500320a100f40b500442c2c441907d60210360103190340c00312440d0000020b211824024410ba0000e05246c01076520a810600085940d9840f400030350324419a5034072443d00d0034507030b9902d8200b2904110411211480308103c140b15080e00554100340c0c220058008080302d0750289480b02c40c1c0034000341013500400030f8800403c41350b80e000400003000c00e450b051801094898090440303165058254443c0d000000075101701c5101c2c0c1c000010852000d1041181206465814048090701c8841c0350b650780c40740c80e41109100c0b00718160301c403546d098401c4804808001401c00030450700001101c051011400100b08420440c50080441c00000d0f01c640007042030100d43c20008542061 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 512742428 1250 512741178 512741221
    0x160815091002031302030f122b09120e031c0804020d02100917010504051231031401140a022508070507080f0c10031401030302030d14 59
    0x1104804280c040c4018000c011481440400940d07891511144a104100951310708a000f442080755980c0756090124001d4414a41d08200c10315010b24801d209038020340d50040c3c8104010034801c81000d22555220301c040591060302521800a00c130880500301d101e1042274680640c1121200d00162500300e2000303450320301681030100c4141c94074004910b10341d000d0304000350482204000322a90303d400110100840d4502c0a00d00d0005200c130466500340d403025103008059a20620581a900300d10784054041d082103040101d8402142400010114017810000c04070b0034030030300052040c003103a0b000250f03021007400000d100d810399900344440b0fa00c0d00108050060382d0301045031f00d000403449159980d10000e101d205084142d590400030156441000116007038071403041c00003886000410106501d4140e080500b103c50380701803e02c41d0540005c800b580805907154100b10500c0b210898460180d4008d80c011520341c96904842402c546070303c42030341e0810000341c081003050102c0c040544406407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 512743678 1250 512742428 512742463
    0x6110604060c030207020a090204080709020c190317071e021c050d0f060f06110d020a1b05101205071404090213050a0618090513060902031e07081608 66
    0x30b003902c03007103000b8014410000d50103090740c800003c42d185140c001e41b096446000030745007011750341e42d0032034128400e40d0250003682d0002c0c1a00101d0381c41d40d2142d148403a019041100f0016040041d1424043c002c490001c04a0104204020618185400c40c0d0b010000c80c0000e000010003c240042060110358041d0100400003404542c1800f203a00a4138900c03c0b50307101844a1515030401000241c0c5900405001648106c0152408040082d18944060310b94000d41204002d03a10f0b05005030340da4580d031088044448100040b19160080c40c0e00d8480a00d50f2440d00f030306c00f001100c1c2305465004e0306100801050702c4060101e180b101040f28115242d550700141c0d02d5056054550420300d445d444194821180c3e600090002d8218002c1c05180d4074610403000c203d919411021b0403a6001e445000348002d410b910f00f00018026442000130300d00050458035240e500c42a42d1700d40c400324100500c0181c104071000c01004d5400c0040d9050b449642e20810344c15401d0800c0256a2004035481c2c0c803112 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 512744928 1250 512743678 512743691
    0x7050319030902060d0504051e060f0a060f12030509090103060e0d051e03091005010b070302010c020a031d0f0a2709050c33070b070206010b030a0e25030201090611060406 75
    0x400524080c2c2c0b070070642703080075803d9885000b0f840743c0c0202d0301a41c21156160000e0300c26541d61062506541c40111040c4501e030a04c08000d2101c402c9090403002d0120401c1920856607600d0b9509000794030602c03003c1000b00c080a4400c0c24600c4064a0500384402841700307035001c3c415100d0300021000350004a540700e50305c854030f5a1405c41d07180003078101d03940b42000114495608070001c01540f8000c1c0c0013480072495644007243c0c0c0b02280d00c030284c00a004072401e201650703813400207501d04c620000c00041e01108400002035000c04680e0201034151002c00c6580303490a0340d51440f00f0100001002084504450b403603031500d0b42e141102c001e104200c0c0716812440395011494000301081d1380d0062101d010044066807403154401801510030348040800214044e00c000b034114162041101d800742940c4590140201615140760b00c81c2c6640940049445290329485003074580080e01c10a41c1522451400094403040107900080c1c100100003541840b48500041e00ca604240c1c0141c001444 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 512746178 1250 512744928 512744933
    0x906090f04061403061e0f06041b03050a0f09081602030a0c1215022a0c041431030507020a03020d0f0302010510060e090901060b07050319030902060d0504 68
    0x2108091122594071601d00b880225036045543d0071225500000d404803491a00c0c1c3c00d01140315810044005022040301e08000b50f11504d0141d409a0000d00161000c1814100c56241c5071100803002211000030b5035a004002c0700080b80d0245158600c0402c4080108170f00c0c50310340c035181d8482c400c0201d83c0000000306020031500c041007507511041d0402858001c80f5105d1100d1981c41103021030a0754a19410000ca106020243c800c541514040081503500300e4510380705419402106801010f090045020107061610b460161100706a14400c10000502d440d409400e05905070303044007240f80c01480c400d809400f00c005510609240c060078030607155085480040c1c00c6041d2a00002d40040f40300000d40204110b80801541285c42070300284034555445801460f0721543d88140307000121000096042410803c50294010007202d0021800c141c07a00c9100c00135911044044650764000a100d00402c0c10b401c11985030003403545400d000410a0741c0000308a4041d00104203e41c1d0f5071032010408 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 512747428 1250 512746178 512746189
    0x503040f0c080f06060f0108011412120a2f0a0f21050c010e0609030906030405030d06030c090b04060b07110109171b0f22020f04240e06090609 63
    0x604240040714900901c2401c203581300e003030a5850750f000300440140e00e0f17280c0d8000d031801c40c162002011929410804001001040f2801c2520300301036000e000c031020001452200100300790f04203034485c0c0f4920460301c0b1450009140307404480c500d100c801e0840140154000c03e20103c0710340c100042c03804603091030178030140c40b01962681c003c5c05001020755504c4a50840042c0410607480302c0204483c1d8500e981283e1942021620310b612600100000c030100c2c6805c0c4060354026000700304503404d015411007020b0485015070030aa82c1640e01c103400300110700d6140640140ca480655061001510706040b50586004076074004148210381501896503910a507440780080c921042c20211200400c0919030b2512a8282c8421404000d410a4040790402d110305c1c0b204004040d040003000601380d2641007007196404000e4489513001c0100b07820403061240904090121444c1c0e07950441c0741014814407445059a444080c8002c0340d8485c485950b0b010140c480c201e04c00e9038201d41e101e210800256 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 512748678 1250 512747428 512747453
    0xf0301171005040c1415040b0f1b160f05010c1e0b040309050406140d0305070512120709120f061517070801060503062a09090403020f0601060504060503040f 69
    0xc1c8003500c0d0800700000e00001c0c0540c90704581200d5241400c83c0405001d21000349020407030048410380420040004a12000061809502144010b801d000782c0c242040040b105012a0044c0c0307900060900c1106001821000001d100c01d182c0440c20030719000010301002c0381201d024040201e40d605140d070f249401044000c000c1e07800307402c0010314a480c4c5000350203641ca03805424091843c00b00301241c0103904810882100800924100440c00183c1d021940e550003c50111940c0c02a0300303c042c40080760a018001d603014201d4080154608404020404c4400d07621803900903035401075833800b0414440081e03008070381044003c50081c1800340e07404000d8445611120380082e0500841444034408158041922140b0000f40860b0741c1c1e80e81016aa031130241c0d8030f171040f0105d050b0001c030070b00c80b80c55a0840300030361142c001d810949498001549041c04590070b40c0503802101291114440c14071109014006a081080c14682008030090081c08000d20003040700262030703128020301554451a5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 512749928 1250 512748678 512748703
    0x10810180507020c0d08041a040509092413060c020c10020f0c0303091507020f04020f0909070216031103070f0f08010b0406030218061f020a05060603030f030117 71
    0x2041985036800000000d0070111903400050058000c0c0c0c5074589807880050880c1d5070420b4075076081031b090410a03490301c3e882040c004800501000300160f50f482d8840e43c948204442c8026143d220140c0c2c0041415941c4403501c1142c5c8035401c81004844d41c1c1360310b2404c01d6141c00101c0000c0b8201811403e900c6c21010194031903204801c1500e83c1ea11680c00100039985101e844e0641e85104480001c1c50340e60302030002681c0e44200ca00c81d429088440f42405000315074001010b459500c0200c2001c0b038203e920400c44c1e400340d004000354454249c10300710100c5070450a81c0c401440c00100c4401c04210014031400014504501041e80200c00d942c03c2207210040c1504640c82c440499072104407910241440c03081c40030550070104007040e1031602d4841e00049035000f0b014808a004600c2180a03c50350040c51180e020020500140342110303144440091600356400625a04c1281e0804034644100100114825803013004071194401842c0c05490454204000031541d2505000c070050500c107900500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 512751178 1250 512749928 512749949
    0xc05030d050406031d0609100e01050601020a0305070303090204020d050f070c031e201f05151003090f0b01090f0e07050103090203100c050d050c0903070b030705090d0b070201050708090705010810 86
    0x3402410000448da1030035100071031800b040341c500f030740c20402c1c283d0380d0403201240540c2007105900007003402180100600c0d8803d180000d1800201c1c2c0c00074040342c010740303503003200340b03589038108046070380e04030a00c1c0c0e000185400c00300c400d540035070f9009042d12001d9503842c0740c0c2c4408003c4030410a00034070801c1c0450034201c5004417001d02042859030b0b2080c2c1c0001c403018040e40b039001d065a205452146500903205d840c1798118148082c8144a10030f26640110070405030354840750780c0420480192080241c4c46454654219450040d80b04245c403181002070b01e04a181c42620a4041c50006044044a10030708000c038005100e40002410b040b290100c0d81199800c0ca040c00d42141e44c00801051a954a9039003003115841e4250480460702609040f241c043d80100014800b5080d108060359000a4501d0020716000f130780800b10b80c3d41d0344102d004032804400e140a0000d19502801051385c4500c0518100300c9500c0d2068407965588190300c6203505001b4010081011403c1c121013200180014215 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 512752428 1250 512751178 512751181
    0x50d1b0807080702190311041d16050f0f01051b030c0d020c03060c03040f03030b030c0402132310050a020c0a03050d0206070801060212130f120c05030d050406031d06 73
    0x1403400702e5038000e5404921888441e6540310b00c0310100c1203020141d81e0001c2c0b803084207410220900000700100d014004010b02c0314003400c002c0b032004008010a0003054204441914034040c203015078070344ca1b0341100d0f00c207000c4c024000f00f841e40e001040e51488180d16800707031801c04062201d1811031050300d180040034010003c0e06e500d42d90700052403845070b0609404941c4955284003407648180070585000f841da070010718a85001c64400d070041d0003070310390040660f403420798200700040485c0e020b00181300038400018401c1020641c400c4844049a4803080304541180e058070018004d040100c0859060210200c0c200b0012842004100000c080241180702c5a03030f1641015030744c44900c0c0310304000510035540002e101600c1855118105c420342c2d001880c1d240b42c1c60fa6001e029403c2404254007112416400280c2c00000c111268010100c1000210040c3c00500f00001101072035044180264041c215045056521800303c0e8203e0b41103180010342000b01410102c10002c81c400b9190340e902c130710300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 512753678 1250 512752428 512752433
    0x70f20030d1d06130c080a1203020901140307031d01050402060405270103140f0c03071511060f0907090b01050307080403030905070e0a290108130c0801020901120504050d1b0807 78
    0x2031203c4556004042c604d1750a6900c4130380350b6a400008400a001260b16142c0c020300a02070303005004e82c10014100003240300010000301c1c0b582e030400c40d15540004d403280000814061584440c8011142080003440781e8503054021a400e88698032500c0e0099500c000f00310106180f01c0c0c490901814495420700b0556900e042103802030914000320074942c025803400c03240b01000011440801c0350042c000c2c00d00649032919501c0c6000ca030140304000d11000c0300600410303060611900d4401d8104142c025a18203103004d04603e000c4c06500500c01151404801440780d03070308942580c0d1300c0315552070003042d180e40b00e182c06c901500c1c6100000701544180580403c0c0c05c003002040798494048000c040050345080c03200b020701142000f500b4100d0a408230320401d140c0d40704a203201d6024140081140520000e40e0391510901c0340c1d89d2202445943c0490701100d035691007150a010381ea042d86040c80642880d499498440b84264101403d0203451f10190400000300d1340c54a140581044103207807070381d9050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 512754928 1250 512753678 512753701
    0x70201060314061009150306050c130b0c0a06020d0b0d0f060c03150b0c010e061f05011103090f0f100e040b180112050a0b070f20030d1d06 61
    0x1070004480001181140d0600c00c080002e8840c4104c602c906540794151801e452000200100800e80d034180f41720901c0400070412038040c150081d60307080200391b5035201c00c44074030a03c442d09800c0900812410040000e4034140094100c1da1650007010050362500e0210b00c031001815401c20321900080c104041200f031201448200d401180a550180501310102d2421070444510b10110040d50700e10b60418016080c4200250070204030340c41c000241203c50300c1d20146000e20848054aa0087c00070040f2403103508d00c081000100003c0c00c006078410149014152240502c010603400b40c03d1680e4600c84981d11409103075151540900705090404402c40020034031810280c50701e025605100d10510350381480c0e40d110411030843d800c500ca03a40d0030001d00d140d40e061203020135100d62080c61480b0020940042d1000e00038011500d46403002800040c016000c01701c0074200d580111001c11f01c1d5050b12002100319100509a2040041e41c405110540c401c03d007002e01c9024454840c22041000d02d0040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 512756178 1250 512754928 512754941
    0x10e0a12060b01020f0d0c0501090f0803100b070812071e03020c072301080c070c2c2403030c030c030c0f0105070f051602030a151a0901030206130b03070201 69
    0x107640034861420103000680c2e444400c10504206070740b004100c26941440750301e021899600c103600104140c445038440c40c2002200c014260740e10b000002c03c0c070007074200c0d180082c0001c0a82c400d070706081034242d49403803109011b00e14040285610300000141468801e030b012030408100d154814040180c0305400800940000100c00740a110700e003004500c00c801d01c05032180040d00b28a0702c140c84040200110b82d68840030381002c00640040c81400005090a4801d00180c0514003180c840b15039a001e461a03000300e06446030395400c85ca44284840111030151005000314400b6104400d85241000b003880c0d031040311181545c03030001043e0f50084450100040502018000465102c904101071040c2250000d4452902045081c25540e190314050743c06402c80d102d17080c0048080310426004070341404001d2008840c8174404400020343d07444588109040d4548403c4500181d58032400826811039060002034400e0102260b040360320f4a0510017107000c0c080710105541c503420f00b20b0029020342038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 512757428 1250 512756178 512756183
    0x93807030c0f020c100302130f060f0906030504200d0803160801061812020a0e040303090b090a02010e04111b031215090411120111070c06021203070806010e0a12 71
    0x248940b03001c2c880c6100040030780307165000800c020450940020142c0080d4800300402110410805002400218045203040108681e40300c003004110f081c18002c0400009800840a152038002840003081d07070b4034001d000c1050a806d0400b884060000000d501c40582c035030041103150b0010030402c034a904d0004001c14042035440b0068666203036030042c0c07a5801070b4807030038684502d01e49003002003043ea101080b40c040e0019282e44805074a03483c000221000803a02640400d84400340711b010003000101c00d0b0351284c0c8000160110403007550008042c002c100410703901c07417130310f034045035641280c500704440140c030000c030280071000309181c130403078483d081080d140f109221340400240c8005141c150320140c03240002e10306400c43da201d40d2005a0303030820307025464010000c008000b221213824824483d4208040b001c03a0f88610b604d1070142e064032881d030801030440d001230440102c0081c1789400d41343c1107201420078107050781d00e400c0100c4030800880d80c4c85920916000c0c0000b000c1c6648032022072a0390 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 512758678 1250 512757428 512757437
    0x60203091207180b1e03060a0507210b10051905030c0d14010303080907030201170403020106030813050a090c0207051201020708040e18070509161e02030a12093807030c 74
    0x901c517082042c2c0c4088424880c0c1681060000031800703005540b0450348081182072404021464200c420003940d105c030184035200b40c0e9400b1b0f0341d000e481c10180329410700002d450000d150080e03c00d84075490b12038405903c0244800800810140014034007614800540c400c1e0400145034110b04540e02080f0030310054012801580c040f0b10800700101d10354042d01e4040c1c484907900c5400141c00c2210500c028019811956a44800700011741f541c001040041d100e4041498003a0030700302048903030f2030f060748219a414074042205501d190045204c00840d41300702c4001071000401c807140c0740a48120030008102d030000103004682c0c0b24040c00e01a000702ea00d175000d0740c8a880000309565888199000c1d0383e41c80041200001c060250740312560301c0145007854459240f4a000c4600d8891080c001001d40260700003003424103501d644a40e500300c00340803028050210b401d0940701d04d4400303000720f20005500702182800030030442245c00446c4c01980140044c807003038038100310010018005500c00b40c0019 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 512759928 1250 512758678 512758699
    0x50c120310061107060503040f050f010b0f042715021606050c070f021207031b08060702070b1c1e05010801110406081f0503030406091a04060203091207180b 69
    0x6a10410700020841e007444000c0200c0750074040b042d06ca070b03040144122500b0300704680307983c00640103000301c21610481e5000403a003e9420420401e2045106840d03c0c0101d1808140c03804404100c409c04440728030140110b0304079215824000031101e400c60311000e07202d00005804110b2050b05030002c107a00d019503020080380d110110313505040e100320040501800b040c002004054908440400d9096030202c00311012207030b80c0d03540c1c00001d050704919004015080c0404000d034030424020b0343d5006490744098201141130260b000760710300508902000300010104840100502c50303105200c0491400c0102120418a0040101901003401040c13681d508200c00d00348180d082c2810364040d52441c0e00c1c1c205650750380704c0340f010340104079038480380740c06814142c00a9181c07014801080030340b8042d0740d1b000600d0b0601700031103034071100303002c4102c50910300308020443d03242d0100a07150f50b900300321000a1004500300d0910b1902e281508886101c011081910f41282065409515054019560344151 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 512761178 1250 512759928 512759939
    0x5030f07090312120e100204050909030405090c07020a180f0b060316080c21090705010e0d02060c0f010606020a020111070e130f0605040303020901080f04170a050c120310 75
    0x2506641c4030040c5402000b0790041d040f0303030250580e044264484840000c0715442000a1450700e0780c5014076a04003903000405101504207003940d558091065001585082d16007404110b502200918a282ca540b022400d0b50841d9140041d083c01000e02505910b40c82040101c50301c004c200541c510018140741141380030301804d041d001d4134420401200703104041d9428940543c3c0001c0c0c01840768020190810550240b84c244001c09001c070b03000c0d41c1200c10741d8038040e400b60745400443e0708168140700622842c01041d03036401c241c035040254103940c020303260002c0000c410319108200083c4041542006400701c2d8066002900b07031100c0703000340d03a4a168110b000e4551030312502103008401052902e00700264050b0744584d8000b100d280704510720000020301e82c07211411540c0a95003280080d400058808682d82d0000f005070308200c84030f2050340341d82010f0356001d860865180108200400c0421500142c60003541507070012a121340644540b5000881040e40c654070031940c907402040780c0580402c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 512762428 1250 512761178 512761187
    0x260a0303230c09102312010801050603060c090d060614100504051003090503120103031e03020c1005071107090c18030c231215090a030801120c051005030f07 69
    0x15203510b40c03000e107801070b15428003140f41600c0004000380803c18034100305d01c1c00400400c05960040c1c15810b1344420150140c1c400b00318040e48403103600d80c10032003481640c1d603011440d81d4001040e41c1c006130361100ca4101044404000d0000a0311061500000080c5c400310828608070180b0200d410203041d4104502c1510140200c2c000c05030080300c1088504403150107a486a0b80700e40c09541107a0810b144140d0150444400340c00450000c0c1c880d4014811541409002644100d00313030806500b40b00040d0b000a58400309261000182c0707880c2c001280b001409604440490202c0c98152607401e070319504414090800d006420001480c40f2084110f08042509480180c941c01040384240e140340c10310308008607012034008003003c0ca0746110404550354031000b400c2041d200074080c0c01c20300c246001e9060100b4000700186150b03006006a000020b41c00110941541c1c52141c0c8402c0c00d4085040c140f18200c00754000300e0b00314500c0c5d100d000003290080c0141d88a00b81010603d1300d2580c640e0001c0b0f5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 512763678 1250 512762428 512762431
    0xc040f0c1407020307030c0f09060605030f0f0c0d0f02030618010501050f3402010e10090e0a380a0302010503010b030901090606090231260a030323 65
    0x621191145503054030340c000140021030001341212002c40e2280c0b62a4050000d9a116100440781950200002ea1441c0280401404203061250a525050103005c450140c01440040d82d18010f10018480f0091003066401740411210308100500c0350780da44100950050765103034400c0702d850030103100c1e499215060605803441a5104c500344014400c050305030f42c03c45400310403040c0c2d02d01440300419850351003030013140308050020a0010b5040c0009440c0151509040d8000d00c42081d2170180c0b542c01c0301142e004c5502c000c4649480f941d5082138080145240c000f65600b140b80048000c0b080d882540e04445001e480800400300710b80341d04c04000c0d002a0328480280410300500040180b010303114095a4015100000400c018029030351350021248035400440308640d010500a4107002e4841d010015000120080d0320101407032328041c0540c08403803041d141d41c25480044528118220800c15154450410481e000210070386009005850108100c54800c5441c001480440d410a40100d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 512764928 1250 512763678 512763701
    0x90f1b0516050106030203120912060c03070507080c070626061302030a0e0a1407141309081c0606080609060f0103110c03030c0307020118050c0d030c050303090c040f 73
    0x1924000c0048040711406181210564040d540da45000016031420701c030280d044651540c100e55900940410882d840585107082d00c0c95900c00410001540c0c05041103d401094608205071074040500e03110030380b840341d81b03184151400b81c5c00000820940114141c070740301141021403225003000403403100200c0c0302200c6042d8030904401c40220b84101d603600468000240c0074011454040440001e407030300c02003220480d0b81e0005515520134561702844400701401c1a0790500c0800312540c00054400c5411000001c10280d440b5a60810001e020040300d0766080006138480da04041840ea00380101460f204071401710340d100340000c115240c01c2d07201c3d0b881404000d110000610700300340110006e1885045421090204201d81d4a5a25082010350f03ca01c91490340d2595a18181c14024203490003a5180207000f0384c100f5131640002d001203520001100b05644004094440d424122030701c07900c0041c05400390000205010100c54081803000d0310b0f500c1a1400d0003c0b007100c00c14081200c499030b00a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 512766178 1250 512764928 512764937
    0x20c100b0603100317040b07031205010f0302220605091302011d010507060515120f1c080129070803060117091f02070501020c15071e0f02070f090f1b 66
    0x18400502c449045410300940017075018206912610044810383c4480c506034003140384400507201800b814043c1c3ea0240200605070846240303103030702103203803c031403107041032000030320003103c103503850350660001c002490001d00f002483d04104194403610582d4403800d03800502c4a80e14002d03220384842c0d240c1e03170345201a56224606807030354440c0302c01000c000e0219503102d0130b285050a040d55a0084070505201c4c15805000640e03805030240d40b4114079869a204055904c50f001800560880119811900c4a51100007000641c0482040d1451a4123100307003410300100f104014030034464041c41c402c1c0b500f030702c0b4003551203d0b0030080900d0010803103404e142540480680114000e001c80fa0604540d150711000d4204412070786c0c0c1c10309903045010280000e5001d018400e4841010031602c0790030103650304240c6081c4641e40c0c0228000f5101440c0e51040c440c1c0020217180c2144204940f000400702c2002c1042850385641080c6c0144c1403a1004d034a12a040132170003410582000a445000303000d41d00c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 512767428 1250 512766178 512766211
    0x9170304061d1206070504090e01050c071b0807150e090103120f020309040908030702060f0906040308040f1202030a0e19140a0b03070201060e0f060109050609040f020c100b0603 78
    0x3824500c142c40400340c6800032010701045150040c01c20401d401350500c0d4070b800c0c1e02c59040c0101c80048a40d10448903d09a0600c02401701500c07080c0c0441e0811508184550820a0154240492019140d01c9405507100300c010010b81034943c012620280c00341d554810b4000c060910030020005000c0c0006010508901d01400c5d08501851107602441d0041c010b590904440e0070000301141c044a10030b4485101c000100300443d6414440542e005010000300055810600c10103581c881008200070140400d01002c50301f0312a07a8585000999031040b001d80a4400610000f512900442500c00100310741d07440601292074800350303203a080d10907a00210320551030044800500c04416021a070404003484001c00c404005800451140c410303900003050291426021000384071000340500c2031200d4203024022070360790100243c401c549088408139280c42005000a004055914034030510301d100181c0e04643c1400840e01202c00750038214100702c0d01c865030f014010b10b44812114440042514013 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 512768678 1250 512767428 512767457
    0x10602011505130b09011217031302040f0905010207120e0a1d0612030705070501170910091110020c090108160e0a1118040501050f130f0b0d030917030406 68
    0x1c038081202d401d240081613039004800450700d011310a030030245859615107015010f008840000300314030b1101d401e200349949411f100c004458030441e00000d202d26141d8204902c00d82080d00004c82c0e2a4201d0021035846200e072a14841c0540c140d0550700c007056020121314100c3c50560108800c6a50b803541001040703207403220000d0302c41d000620269010381c03400980510100204060403906210ba001400c05c0c034100000500524002d004800300082c03003400b044044c5030042400d441070400408003003000d83c010b107040c1c2e156010b0810032541102c40340070050425640012003a024071b80a0306c140f170903640c030b4042e05915a80d8440082540c007400074810484000001842e41e4001d2461300d001640c4620310322100000e6112204130b448045880076003203003518081c480d503401010115800807a80d0004404942480b030301030400e1070200d50300e000440303413a5200e070001c00c40c1100003043e9049110307151402400c460700324000d1118034032218411b01414000002150103072101d6803111814102da04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 512769784 1106 512768678 512768689
    0x1b0d0b041a011215020901210c120e030910120606030c02010c0c0b1506070b0a051602010507090e0c0c061611030405130914060c030f010602011505 65
    0x1800580000e440210501d0480070b484c1c00961144969001600d5046c400c507402c240c40c042480000704664416403001c4190516070310703900b0040300049500400c540700040d03540082d41c020408100a4900340000180303004440c80d000d54150502c2040d002038038070540c01000880e403034001c0c015403d5020f00803c840700d0007924240f42500c910361601b0000c1a4040d091440d0f10040c100c51014a4903494111707903078143c000c0b22038a00d41c200038032074200401e811140300d503004400100f0350300c2651041c040c0500820003965069005800d0401086040e00b0103001502504400c0000c0030303040c00280191803040c0d1010001d800441d0944001070030301d0199004cac20040b90801c0006010b540d641081960170614130210029400300c0c10301d0803045158400c00707075540303c0c45000104810030f10440c00a600c04c0100490f18421642c0c0c482d01a820b840a0007000d91144a8a100034422030810 = true := by decide +kernel

theorem cover : BRFrame.Cov 512589928 512769784 := by
  have h0 := BRFrame.cov_init 512589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 512589928 ≤ n) (h2 : n < 512769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
