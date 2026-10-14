-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2636
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:17:46.222664+00:00
-- url     : https://prove2.me/submissions/e9868a9b-87d5-4c74-905e-de99630c44be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 473920863 ≤ n < 474100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 473922113 1250 473920863 473920879
    0x105010e0411090c0a0c050f0d02061e01152609030a1215140d0602030103031d01030e060a05070309050604050304030b0f01030f0b06060c0303131101030b1c0609020d050309 76
    0xa000c0041c40f01c8107940300401d1403010042c051005000340144452039000e42c00303a50010480c41c001c6801c7c8501c0c640c41c103006800000c00c1282446000e801600c080c0c003100794118440d03041c651840c1d035002c4018040420b006005208a4130a0350240c400f006610078806032150508145910aa17a50411190040803500e01d2007420802d4829103d024121854003e1040e492803915405001c40c6e00035a00494105404802500200d038160000394001c40c0309540f109031020100b0012b241c0c8061001c1414105800d021050720028000100503400449041b80092161100107043d00204404800144140182c10400c42030190220151040721302910f000130032036480340a81d0100708001d000042c8402e8030540c11b5000314075580d000c0c5902810291840340780c940d01d844c0d01c9146800031500368480401010581b01082003022030070368680c5081c2001c1c030908a400c800101450015441e1008408640c3c8030741050200513080035100540107030003003050740c62901340303192690f0002103128055a01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 473923363 1250 473922113 473922143
    0xc030c090803120a0f020f0f03010501090501050405030a1209090f022101081f140906180d09090f06030813030b0108060c0702060705011413020901080d02070501110f0105010e04 78
    0x40802101c903680c1401500800341d82c1c03110013900007402a4139a042c1001d070300340f00502010f010000107000da01c1d10000f519403250f00d03240004102442503000f036070401005120811041d1800901300c22195840110700c0301104035100b0440301d1314541c1d80165241820640402d0b0010320560007007407020b0300a400ca1418404181d08011081028804e601c5950301c420080011020100a40c400c00242c0c40c1c00400c1080c46000c0700040c0b22010740704190103821403003c0c01040200c81010100d0ba40b10040501b99140200c007000d0920441c901c5400c500c2ea0701c1d6040303011010400d501030f0010f541e10440040d1220348044540600010742e0008864860304d000c008114280d001901c540300c1d603c0500b11901d4039800e81d0900c030382c07600000021621592200030040d41c4100d503542e043e00c102d00c0d0303401d80641101c190040011300c42042c0e00450103030700088480b1090302d5002c210041a0307507084c01c1c00d44a03c0030301d510842c0342025242c2250140d500c0c140021074008404d03040140201e0086865411680da = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 473924613 1250 473923363 473923379
    0x1509050114040302070b03100302090f0106120504051b010c0602030702031e0702031c0c0210020102090f011e051c020a0806130b0d0b060307030602040b030a05090604080301030f080d0c030c09 84
    0x70603100034025a1214034104010500c810086a020461240c444019662a80402c40191051758000010103182005002032a44042c0e801c5448030a0601485207003007548441d0b803694050022808400304104003080c07164010005e02070896440340d8119620700d494a0001c1d200e03042401100010080308100140340c403a09001e0358a282e80040290400301c00510700c4680c1650f80031082d0050010100c5c4e0074026a866a03803075038100c070b140e800150b40c540801040020300100318605505011440d00741d4910309100344140c9087e4a0f040c10640e945010140103031031805010060011602d00001c2d881035030544c40005c1600400c4251451841000b90f1405082038640d640b00d02030300701b005180b00c040450400680c094001402a00b07a8050544a40340c0c41c059a10540002c0c1c82000000709000070307a99244115948460300d08040e100700d0401d95211090781c4130610001c3c081030740140d03462381403248401c12101c0d03a01c3da4a008124500c12404080c01034101c0480f4440031480724040012184 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 473925863 1250 473924613 473924651
    0x303010807090519021306020c0a0e061014040306060e010605030405060708040c0f03080304110303040f14060d0c0f080a0b13020c0111271507080309010915090501 72
    0xa15a038058280303941401080ba006001c000d2802402c1030300003501c542c014155100074002d010800281501e66810140040c2c41c0c5400c9521b441c0c00b54021000400c1003800078601c140c1c10110844404d52600702c031175401c0f40c100624400292010900090010401c10550301010446140301007031440c0e070ba03850a06803410b020484020701543c110000141c0842d20030813046134860301c0f452121007115119006d10f0700108292b00b04407900b80d8008107000500c00032580203401d0340c1e01100107624045c203208281650103400c2c4504407800003801090381080da034500c1568400160300c0b070200304a494a143c0100b14048803075010010507510004580c613036030a8020441e10080152101e0380e106021009503000b540406c00c451100c0d5070300d1825050350203100006224111640071110070141c2a0f1440071561000c402e0010f01c1303181d16001103000850244151210b45401110140d100d60703881d4120b901404138060014242c1c2e040da8808220410b682d440108118001e000800c040a01c04840205078 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 473927113 1250 473925863 473925869
    0x102030f07240c210204141003020408100c1d091b04090501080109020a09060602070b0c030c0a0b1012082a0703110913020a1a0c101508030301 63
    0x30304080000c600400d55240c2141d54841c9503090a000080012150b10111800e103110f0310300280030070444000c036904216910014071104101103180c14a0203103540c0c0c9031074510140c24022078040d070203584a1030090741901c2c004c02d15407040d1520001b028510100400384100d6100104000c02d584501003806c0001c03000307004030701400202250f1240d20760f0161260303a60580c010414401c00c4040703140b010f43d018140c002c0440030000300c1d01c11614810081200c2d42500314855036481d01e182001b419900041c000103ca014001c43c6950341280d92200303003144241e52005001d44500b5207824108642400c005106054503023881030015107962000c190b2000504002d44070000c14400e034507070406e004100350342c0e0001c503107150200044c00454490a1500581c8150744c803418070580c041003800d00c3c4522a0780601c1e20241c80e00703490f40c26400182040c0243c080d054104c5104a003800c1c0801500f011640400d02040858130080890b5801070040c3c1b41e540d200032030044100800140082000081d03d040e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 473928363 1250 473927113 473927137
    0x60b0d050a0b1e0411090a0b04150e0610020613030c060e0d0909020901090302130e190312180f06180c031209050303030a05151008070906081306050606120c0406030506010203 77
    0xc85d0700e90000c010403040301400c941e004598a20095280b61345034440c03821442048400486082d12b04009122003800c010141400b0700b00c110001c0a4982e404511254001002c029406180751141802c4035400450940100f586180c140420400c034800034041d030052000707948000711030b034403074207040c00380d005400000b4045001824184014039103c40d0507050014890800a0244080060146800754081180302c900d0764850303803c82810350110900905820540c0c05100207241624901c0f402540c801c00642303e4415040484100a0203030020b40d00c031142d010a031a0316420909040c0c800358003620086501381900401c130b40c1701e00c0c054076004045510003406141103985041210f405044010710b640c40490540c0131054107981c0e10829000c0c0358209503102e01c42e515016101828040894200d1801d0106000800c0540304418420390180c030791203000450a5152040858218080e03130340c5035182c0140c1034080004000030500034000300c0e100b9940600c103030785070600160303181c0c0705110700081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 473929613 1250 473928363 473928383
    0xc031209010e13090b0a11040f0b0307021c050406090503070b0301030f0c0b04060305040b090f030a0c151802090f0403201e060a0c050412060b0d050a0b1e04 69
    0x224560091442c0411820003412220003484500c0f1881c04842c1a24800c507904080b2a062080d51201d80c440d620607240010483c40c40c181c148001440001c1c024800c00c0c4409500000103540706100340440d440740c000c215000240000301c5003002c1d007540c016004500008040640018580c600002d8540440d0300303049401c3d1441c2d0035a102c0c03c60a290704c010540712449202800159000c102c0005d00042c081c0366400210760030035151511580c030002e89034407040d07804140b01511640c40401120904e02180c148000510228078240d102a620500034075460b0b4900180341c19003047d030f188203081c01c600c00c4900c10001e82d01d400f43c010f480318081e031b000b500080d865001640243c0005000d0403a06500310304a450b11044480106000180080d0720352103a0440e10601a89260030b0003102080e0b040c0e420164101403c140954160b00f40b00350b00507090316114843d910381d40d100c240c1115211604078003a1102c0e2480780c1441500b406007900c41c04100024210410b00040000c1c01190050f43c1c4001060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 473930863 1250 473929613 473929627
    0x11703070b07030b01021e0109060612020906101101140106030c020708071203050f070606080d030b0f041d070305010c020d0e0d030f021218030c01030903360303030b030c0312 77
    0x4000341004c24885040d4840c0103144007200d0014030203916084100c030000f240d5a206450458259042e1354401134441e0b914440c6400140d54242c10320740c1c441c005650308010902040021138500b01c1e0400c0403603142d440e080c0c1500202c0c40102c4901e05960706510140800020050300302d030345550f40c1c8104403c64000500600c14600200325076400300380030303240c014100a01004c5400702e940c4000c9086070910394903442003048000511100c40540e1544c10200020504240803400292040c44000c1c0314030780c0c4100314043c1d1101c43d1240201004440211034900d61245070107070082140c0c3d5202c002512400305c061001a201d03280002a05c03601403c01507445015540544003201081c01c070509501908090410015841010745084c0a44440b0046a042d0702424142440c14200c640d42c105820001c0f5840440d40100c203130104840b50080617400e8101c02038002944410020000591030041d16001051541c150001c03c0c45c00130440903108404200b104166840c03e00c250b4810304c0d008203100b01d0f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 473932113 1250 473930863 473930867
    0x7050d12021209060411010801060f030b0409080f0c0c0f151b01020f04090510030809060a0903020301110a02250b130503030a0c05071a040e0702150f011703070b07 72
    0x2a0340d658820100507040c02ca00601d02c5039000012191031005034401e1081100340300154112170070311802070a0110303655050940040085503c10040d0060648032810140c1545883d03101da1100c1d0f810500c0701d81c0b61010442508143e03801102d41d8426880350b45058200c41c41c0111280a034003100070080f10a080c151102034620350440c12200410601092046050708020b000401310818600789aa65940c01c162050040b101d000d030601c3c0d070400c01c0345010b01c0000c01840031691000e100315a182e0b10707040c2040d41202c48801c03d40000b5015400d042c514908158030401805040480380c0a841301c285100808401c130000c4292102c844100c1d0b44010070054082c000105040f250a104081c030058440c0d011034603643c00903040c00005600540701405008040c4030720b074090403a417000f0042c51405c900101c0e8040c0180c1c003c242007401200003140d0f009000b0030055941a902c910845090b103010900a038000400740316841202204c2c06004003065000f004039904c0c00ea01084d4100703140c84103402 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 473933363 1250 473932113 473932127
    0x3150b2a0102120c2706040915180b090105090402150d0b06070b01080601081209060d060513051504090812070504030c030506011410080721110c1207050d 68
    0x20490300d55420462243d040900607045441080c3c6843c00b03075600c8450811141700000640c00281c0c0000c040b0400180703030b070369240813070b000c6846020002c2858904c0e251071200d04000b40e8010140c1e0364070708400002281700358000c20344510045482d04911782eaa0001d010711b080003214000e5029080301c02d40d000b2114507801408082c0c0740d014000644e0b07443d11011a015602960040e20300c2403a001c01084150001c00800d8003502c0f10314058144c0440a00d541c28460080c080780e10711618011881c04200d80c0e80358001801042c0080c101e17124031644900080c003c0c042070300e0152450b54040102441400c182c00f0700000f255011303d200d4903000d006e0749816007000b0040d140b0400c0000410000000c00d02d0b881020020703502600281130319515280d0f0420600a803210028010902c8445009805e60010b199590148883c1805440c00c0c1c1038000102c408403928202c3e588052604108954000314080548074100360b180423905a480d8400540349036000b0b000c001496a800506210551071103403003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 473934613 1250 473933363 473933437
    0x14061903050a110c031902150f07020102090607060f1a011b0c170303090d0c0c09150503010c0903020a091512060b0607030c050607030e07060f0c02030d03150b 70
    0x900094a480034881d00049038403822001150344d05c00b00d490a207440340e0044e040e84004150000709040740ca0362117605030055000384200c1d41c009044000074001750003034044584440c001091039954006500d03020000b0040901c401290a24000d09025a145001607001c0e6500c0c3c1611000d402d1049030145682000004504964416141e00001450482d1664411003c000d080c00b8546900c0c0071219249089030082d0094104241d00b10707010080b035004220342082d26030002c40820b908181005101055a02c1d6016503055840c5c590507981e070650065240c4140d0f4401c480c0060402e40d925140c0b800e070744d81140d1007001d03400100030800c5240c5401c08800c42c1d0510801c030111b441005200060410380099030140c011516500b44441004005d0154030781c0103c00741400c00c240107010510660300c040d41c1c002d0000b402888441030114074040d0800d511035541c001c040b40e0350ba1882200003405021f50300c1c011607203001c40c0340300403c82d100d0380000d841c0c840000c3c00d206258181c6182c8100c00b00c4001030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 473935863 1250 473934613 473934631
    0x1201060b030a020403290a0c1107060908070501020c0609121f381005090306041211030a0507030c020d05010203070c03120b090613060e0702071406190305 68
    0x8900051000e44100255101d40c04210b00161918503504101c002605404d0a5a81908003002800c81e000044c02c001d6401142411000403410f019000075200e510803ca812000351080d12000102c0c1c0703a0001d10a01038450301ea09031200107a0380c6005a80d907031041030701250703c00003d1000403102d09101c4040d1101c040c0e00000c40d4400300340c5080c040f82003035180041e81d003031580300c412400c0380d000c1d400c0180301c4c1d076400266104180c4401550544a40c145210101e102e80c140c4005809668030440a5a1640c5402001d5078a942054a0300390b9408103031040c0c0c90301040045115503007149012040d02d507100c4441d16068501400342e07900702e51083c10000c0c100c2c0e00100d0a1010700104000b4800707540f00b500386449980b00c00d05541006082604140e561000040c1000040000c60300c42d0525190804000d8444c41c60000e56100d20390b0280240344c02071404880403004004c84c2d01d60000798041240c1a000e00c56905c2c154100521030548622501c1c4614100d0031031810400314803a0b48425030180001c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 473937113 1250 473935863 473935871
    0x12030b09010801060e060d0206070f050124080d0801060f0e0102070b12090105060f0a05011b08030709032f010810030507060210110309070605031008060106211104051201 75
    0x220009000650280c00082c460781d03480d00180403568100200941202040b02d9148244440740e00082541c4580d01004040302402465502005001d410003070842600800400b4420040b80b2181107c43e036a12031030160744101c0815046d1103000e000320074140c1d199541c4007210104401e200b900e02102204c1c401d41103204106c1d002800500101c06001c41c3c420010a450490401042072800e40e180607110710b200e5501c08040c0b8006e560750f000c80004455081c03d0800103194820500c60442c0302c0180e002c0e02c4034a00108000105a001c0c050a0070341c0d106000340211050350011010368021084c1d4420241c21103000c2155466005000f0154401e4113802c900c41d0550b02d17035135a01e007058110751200026038811515103511407503a00030012918403100c540c40c01c500d8a40206a030b42c100510540052040c0000458101c0740c3c010016800350411204032001943c1d40c0d84020508030744804140c0008104441c3c544058046e4081d0b90f003489092004241011b091104203c01c0ea800c1240c443d03815913035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 473938363 1250 473937113 473937131
    0x1104081c090e040b0103030e03280f0f08091512150d0c080106060917070626100303030b09040b010302010f120e0c010311031e130819030b031204031203 67
    0x2c0b50880e00ca00d100f54a220345a524614024100d800c1a108051180e0410707071208008040c145100d1001c80040e0a00c80b1079015117051819544000040140c40389403119100710600c13000b0f200900804c901903030b6540c59132001d0425003d485c003032140c00d00e424480c103101141c05100d076a20f031190320b4a401040c9a2070141c80ba0ba0f50f00d01d9070b503658800c0b903e41c0d44520041008036002070740d003401030015101c0b075030625075004a200d88500850180078140b08204030001c0416142c40f0807058080031540c00b54605043c9665030000360583c9102c202c00181c103000c14800c2c24100301002d03501551303104802d122240d0071030380192060866114a08108252104c01d260405003030300a001100a034103000e000e580120b600014265482c08000c280d0b0a03408209100504504000c0910343c103404204580c40c0d901c8031071894050003c1e49402410401000c541a0090b04030341003000c5404400d030b1001c12410840c00e05058540701503c8841c0040b00b000c0c801000071071607000c00d4009803280f9107000201c03a50 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 473939613 1250 473938363 473938379
    0x60f05160b061f0f0f09050d0602030c070f05101a090a0e0115030b0612150f0c2b0609060810091401230703020906030c0702040b03070b0702041104081c09 68
    0x400f02c80d007000104d03a0100404280c0c0c00c200101c2c2c840307040740f40c400d5569052038042a01d183c0070311001804c00d41d000000a100072000d005480034141e10002021003244241400b40c3d807032000c9240140414070300001a640c1000c041070051061070040c0c00000319a44500c502d1004010f10324100d6161354071241d2041d2900584a25030000e9442807c801030b80e4188401808248070355001d450310035910500244101201c9007140030f03405001c0181070790043e59000c11f1002e50340511400c049190a940307101070200206004d14114000705d45108000d590b40d103580c00400d4840501c12402603400010b81c50081c200250002131100d8000d6102e0300c11440c0c980d0701542110b54540c19441c21400a40c004054030941d178441507004480e5203005c0d0306103400e100010380b40384400b8194025100c1c000890804545403500040450000202941c00ba03a580341103600c03c42d0b1005000328032132842e000b01034003940071000a80f0b007501e00c00700080400001300200021380502d400b5050b42400b90144000503121 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 473940863 1250 473939613 473939659
    0x50a021618050604270f05100506030d0e2202040308160209090a030e2701080115050109030507140312030108030a09050f0f100909020c0304060f05160b06 68
    0x1040e07801c01c20341c919070500c0c10842124000b030101449682099100400e031380d01003129001084413a41e0680c01e0084600d401032058241c40402000c03406502004a015805070707003c00e1041c00154280c0340e030401342000c2210055014a0503d0707100032104e009800120b070020b144003007460f8010005280540301d0b142d8050342d0f00444d6080c6100e44600c64000c1c11420500d00094022486070b000b800e48450b2664050841c0062148150284a50010400b02c26220010a52440c3c001144d08509940c4031200540a48244e6014080c0708010034000601ca510a00d261011a80c020f00a006500d00306101d249560344001e042545c18407a5138880c040c000c0a05000394000c200a0b0000c580da4100b0810141542c80b00d5440700d0b10508040c3c030400c1b0a525050001c038000e000c101d401010420380b5800c1550440c2580d04040030385840854020600c0000100030000d461003a00c4d40601c009010b5000c075000c0c45040702c035120006100090500050640d00d0054011400800105c0c118500300307540f940d10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 473942113 1250 473940863 473940869
    0x40f06080606101403040f060f05070305010f05120309120c100e0418050c36010515040602031902070509131205090d11031c050703090503010b10050a0216 68
    0x40d00007500748009490034211020400e01d4500340704101185032150343c034060000030b0004c1e20b00c00918441c2000c00007541c4c0316000078180480108650308160750010010a8240202d1204404d0f100e4049a14502406044000e98485004500e46606a0705000419103080b107031160314403070064141e074680e80f110b00b440d51558040da10841441c6000f801c100607a410324280c005014090018007010070b4001c25090000d2409031000c1e4000d5420380d43c82d207409600452039240122812601c200200f0712403c1540c1203ca04581807801c9a500c20704102c054841c612035000540d00070040ca00007a02e04c00e05007a40c14102d40140c406260341e51021401c062421541913010104051000080003901350302003c90000c1c1d482c205041844c07040100d8020303024201c0c0036058550b01643c003003403236500b003100d02e602d254504046900000d02241c0071306580c1017070303200b200841d03546000813960f41014403d43d115200000c00900074180c11309815200c50303000c10382c1a01103000d458131410300d103980b000070340c1c0007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 473943363 1250 473942113 473942129
    0xa03050a051b06070b010608041b230f030a1b09140106021c020606042703020f0f0c031c050d05040c29070210020a0614060909030a1d040f06 62
    0x105000c034000d98040202c401201511440c3c0a0000c3d1000c201c07041c545034199101c1d401c0180310382e1100d00701803111187c0c0c51002c0d4410220008041440c10042e40140b1602c540d2150b03121232805001c00300010356800307409140d003550288060301c008c5401d82c1041c0d12650741801c81908040c4d100c1800e00180c60ba040400c4041c0e614400040190b50307410440c2208040d921184100624210300009444560240c4494031843e22049a40001b04021801c1d6803202d000c0c8101340b464000350314020b9243c010303800c4200224050740200c0102c5100c0401c03200400e4400070054500403a1100c400401070390410943c004100c0c00f40a40b00c06070b0314900c5018002d6000e0307001484418034107000e0400c407900d07400c15100c8048101c0d10442e0403146c00d1007a503001c10b60440f00b011010320101000c924113040e451003c4c01e0b82c0d00381803040340002d000d0082c031400790340700703840e8020182d50304080c0c60741e207100b509001d0002076541c1000103840707009500100e11303400e00180041100c007180301105040e22a02c0c2c0040350 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 473944613 1250 473943363 473943373
    0x13090f0f020f070f21020c100305100501030b0f1c1a01080d03090c03050a0c08010c0f020a06020f070b0106031b030606021c1b0303150512070306091b0b03040311030f16020a03050a05 80
    0x7c292400e8600104040c00b0780ca81030249140071035070a080c4280911445040c55104c120b00c0b95203a030303011103958815501905041f42803009a405d0482c541c1c1400c0705559801c0c002240168848840c649075041e85c1c40e8000406803050901d03001c400421200c5001d076880c030840c01c00800062410310028001c140078071540300440d07003015080d07403c5801b001200818010280c00c071a0f003c079000314000c241d4507009000180c4a180402004006e4420361900401081000002080301d5400da440b000700e425514100c40c80240c104141901100c0d480e005600141e84500c032080c41603520351421102a0005182180700c8403070001d030004e401021801c04a02080d1103550b840d10758000e2030b00c198010841203404181c80c0381000f003500d8580368039000203402c43c2d41301d481280a101600036000040e0060310521303012280d5801811305160415030301180060602e001c030540091001050b80e070541c00684d2424a480400790200d0760030000128100d8001103600e0000010a00c1400401030550040010345 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 473945863 1250 473944613 473944633
    0x1502040602010509060703060f0b0c0703050f030a020c01020105060105030415090605010b09180402090714130b070506060108060f0d02040b090c070c1710020c0313090f0f020f070f2102 81
    0x1a0801c0d8008081c0e001f010328140e0200031a01440403ca0101c0354000816130b620320590110358100899900094481e2085621000080301d00100400310200242e007a0303241462614012802ea40302910841e00046052002c01c0106030b170307407030b104884040c20b02000452016076600c07002134070b100340d010204400002c9003100300c0d418070341a5420549800d6030180050300d8158006290900c010b403284042041c10f002150907108031400f25401c1400041601c1c0b1b1036595040480302070340c40044d0403200f43c003c94000c00e907503500540d841e50281030003e01e1496403980b1802440490000d10009a078000e0b12551035000035101c11201da401908000e00d16a0364a90906000f00c41c2c0c1d2165000c0c0b5810507080d025015070500120b440c40d68540c1d03442d00541c1d0f80ca80d10018900c0c42c041c0c1503014115840058000804c205207034001d240802100d28140b050852035550b00b4121701407428080448281001448002070a8012140026102c0c010b400000c0c9180015410303401c121286202c05070748082c101c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 473947113 1250 473945863 473945881
    0x1b01110d120e0114040605060613030c090617061816030b150306090c0609040914100e0a0f080a02031201030503090a2304052203081f030b1315020406020105 69
    0xc0c2a890031080013071041c00000c40919060000017040902065624130101d100d694a4104541c044010100c500c1c0401c0d459041002c043d8109220b060b00c004d1510800041403904085461188010720300038011a41da00011715020268171800407035a030285d207465030034100300400c0241c02b80d409100300703444a03c2c024901410001c0f0403105980301ba800b280411640d080001580340c070700c2c001aa2400d07250441403001c1000b0700b024100040c020001c0030000c100601f00001c01d00e0904214000a100800000c03541c140c40321469480508079500089081000c0360440000381744514503403040764031b401e00b10040305102010a8004035125040010303282501d140c0902d03140e0182c5080300d481ca52035007840381038000344a810400746002396140e20026020f09648007246051400e40003041e070650500b42380042c4079035001c58103a16504600e01d448440c0044800e407040c10b03a5804a030b078940039211100160b07140c030300c0680119120640c400100390100c602e4009800103051640010402e81000200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 473948363 1250 473947113 473947121
    0x101401030519050304060c02131103090c0109080705010302070c05120f0d141207020c1905011706010804080c0316141b06041203021204030b0106140304051b01110d12 73
    0x480500840d01800b0380000c24004400c44040310b1541c145088812254404916454040402c80010138545410342420710042801107120303c0181082d0b6090581030001920204054081c29a641e0b00c4014140540e5020b94000e0200c0c074020071070003e81569a0000500d420036a45d205102504400c1100c0d95202d820041c1e0071009c11513003400800701e40401c1501c1d0f10303805114540320100b08801c011440b03d034028081c070118450080d1280d40204502e0341c0c1c0b04480541445040d0010354103505110b01c070003200000300e000710307030507503481c0c9035a282c58035105400c0d002070744030114501041024a20801400142c0012941703c0c0880100303010394004c035a400c0040e0080f0f4620026001502c40705580d680034100c80c191102d0300c8014151440f103060407450040f0300038010a10b070130005004000d01060301130440c101c0302503680704e40110300d5040304002540020340c1d0003000c0d41c1c001200303503101d84041c6418002851062426960101c1402440d40c505903180361240b000c14100a00c8030b10802d55406 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 473949613 1250 473948363 473948383
    0x1109061605070330080411010507021819060510051b0307030807090602011e020307050d0203150a0510020c09251107080102070317130206031905151f021014010305 72
    0x44244c110640c404003901c4402d000740001e05c1d100103403083d100c0c280e004000b40c40d13907e600034141c00c8491800101c00c042c041015949000701903900011000820f5403170003044240c48001c0c0248450001030710064905420061955056030300c2810303082c3d044181000500032450181c0d035081858140040003609800f010f810150443e410032010b95410311642c4104400d41d282c01100581c0c0e5610040226200c1c0038080640d44410b0000040c000b03520b8401d07070810384400084902d611010f0340e034001c06c581513801d01410809038101104040e01072600d40c00d030b0366000c0441202d54813143c0180b82c100c0c02e840000f18110b00855540003400084000070031040f000b41c92680021807614100c0c0e100942002c8a500e84800398480403000140c030713882d656490303034503c590260985840c0e00f07103503c00d542c038441d188074001003481c5400001409025088100707600380c00090b1880303070f80000c0c65840c0c42a221140c2ca111055208050700c200000140b0320526041003540a92400c0550651802c2428030010368 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 473950863 1250 473949613 473949683
    0x30903030a0524010c030509030a03090918030801030f020d0f030201140702060907090203060f0d0b090c01090b04090207020315091e210309011b0e1311090616050703 73
    0x35070000202c0c40d003080b45200f2900908040614070300030b280445c1c0d540300c0c01d07540c29014018040503208142d0041540426074030700300e8043c03025408240d003154101c4a078100240009a00ca801040890680e07110300c03103e140042d02030b912004031500d0301152141d03000d1086006039512181d07009912920192550443c01d1403000c0d0029041ca2003856590b244640070360b5911a6002000c100a81c0d034503103240c0316608016000a02c43e05e098144041c41080880f007600c001d000e00301460036036602c500c500300280c415000b420380c189410050030400179084440201d8140c41040e844000d00d03040e0f08602803183c882c00c0f00030154042c00c003d80c9901c0140c107982c01850381e80281d818800c2540c1c0340154604010744405035507200c2c0d507906513603400b40c542c42800303100400034035140301d030f945901c5440442400c0c0241c0c3e02803010361030b10420700c003150b000e144000c102c241c3c1070181005601d000070081100090003150003c20001702c5c0c46441c20300360503600840319a014040d200015070702044542c81008410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 473952113 1250 473950863 473950891
    0x22a10140f03040b100e060f0a0503060106110d031104091e050a0e0d11060a0c2007050406051914010504081c0e1f050901170f06041a060f0309070b030903030a05 71
    0x152402c405020003901c080d00c070b0481005c0740c1d5803c4d01d271036441030000c040060445405507581d400c0034144040e0341c0b0405d2000d000c0d00c15031303924207802809031031a9540003150389442e00c1e281035411002407100c5800000039580d50319004400144a028040c002d4144101c000b4202c1e4105440c00e02d8141542c1d01101030000e4400011000500401c0c0c0c664071451218020034518943d1904541070070094011030315485c3c100d00042da1141d400180001031700c4094604005040d15441082081c0c08400001075030281110018007040c4c0c000c100100810f01c06040c40340c2001d44460510381400b0200f40f140c80f510380300d140b660714450b0b0f01250301301012805842411283d518010b020465140310035400d0103024000810f086603034810003202100401a032042865420019a0100c0a80b000c0c0c0d1568407a500707220141d19991000d01d80d1200d040c000a00745840c2c44580138042c1d802e6080181a13640c80c4c0144a00003610041742d0300203510481c80035002d540d591514143d00300480d4230140c0032007001020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 473953363 1250 473952113 473952119
    0x2703020d020411070b07030203010519050607060c20060a180221100906050405060108240a0f020f04030c09020f0d0e0724022a10140f03040b10 63
    0x200103050a086030181d8000c1104688036003803011510038050b00819440209040080c501e0b41a806941030f500700722a0080c0c1107030000074800c1c0c802e445020f80382d485001000888009400c5074040d01c605081820858440144000080c5150a256240c8051034102c42c0800c000c0002d203205428680e0003400000055000f2070300862912506203540c41c3d00e03184c2c280c21046589008020080c1404062042400701007000d1401c1c4010380010b882c02c6807640308480011445030808506894501881e109115080040311200780340707404017a00301c8030280e270380e29560000d014940c0010100380c900c071103030300350780d40d195103004031461135154000303070f611362050048100704800700085985407204078030003058080000d05901c0c18590268064000c41100070705034070741c482001ca05a040c20900c0d40a403000e041c025418214002102103103c9a101d01c005580c00d400c4c50500319504001526140c11444011040102d44075644030b005805d4503003e000c010403040148201030681d001c0341151922600b145 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 473954613 1250 473953363 473953369
    0x240806090303150d0c09050a060320030c0d030507020406092009010504060806120a060c030e03032703040f09021b03120103062301031a09070b0304060525270302 71
    0x15000d03020611136428100c0007400e0020381d14820000c1c2500c60000c212a080c90340300c2c400184002d100813070b890302c540c602400c28030040081c13506102001034043c0c07840700c00f07501c10032201c003c2c071480072401d112092207010b0140e1158412440036048040340040d02c10182d9502c01000b50f001400080415801c0055502c1c0341d900c20191400ca8400c1c0c20040125103e4500081c40b00151400310b0030b040c030498162a050040715000360f000060f87c4c0e101000062400c1c807140c2c1e280d100468220007445110070000c5640c0060701032918002d104081524241510382220300c9600386280d001024168010170702852089611801d1221942034034001c514100440000d807292400500c4090051036880d1905500c100c40b00c0c84c48100d140081a00310b84a42e1a403410b030180205400825145081410020780d405000003003d000b13561310031a0403400c590315542c0300c10190000500d5059100e586844500128030100a0300e26000c04580740d158501b0845520050700c541c0150500c0b01103042814100050f807 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 473955863 1250 473954613 473954641
    0x803030106050703080a1d0d0f030b0f0609011103040602160506040e0a0b01050d0f1d070e01031e02040c0f0201110412080f04031a09070503010902150d240806090303 73
    0x10384d041c1481607107a901c1501150040142402002003035003441100c5203032400101c0c0ca03001c2000380742c5a46006400301c0c6401c40032a60402030941e0003040780d011600951510700068031a54005140c40030052050700f040c81e056800a501c81c20150303022611880d42c010b0400d0104c40580020341d2071508280c50540c243c10403ca0141c242001d017a82ca8024643c80d0348a541155036811400e5010b0144108400352a00205035488040d480166094800e015818012800008986440080001d645d09507203c19410036601c2501c0d02c4403613942c075a0500180c41d14090b0024902054850b4240203814580103070075620906810703c07002100704800d0205100b6100941401e5070884103554981048485080803441290000303010030202c00341e804440034100e0105031048101e4021313035078126500c1e0145801d80f004807100035030001e0020382101121103000060800c00000810204a110b0045080700c40b1207071a030498011003105a0080c44440780400c4015044035100d0015031443c90017000c012449 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 473957113 1250 473955863 473955877
    0x609030711190e0c04060207081207021e18090d0309050d0e010909020c0606150301080a032601090f0b030610090c09080624030d08012c0903040f080303010605 70
    0x1641c42c1040c080452920040c90700003414a8030a4410b8500741040ca090003074005124420040c855100c0110b0300d081e000c07071990b400d0b038010044107050112039820404a44820b404d903081464034985400019600d000720141a492141c0c0d4800f02810200d4290f4206022101030505060614100f0000110002000e0304800001d28081603142c051100486060b07030349500800c40c0c1070011401940203d0007065882c05040c0468001e02c0600a0f80542c00e01404240308844040d0030254205001c02d010310030400f281106405034002c1c030340e0515800301c050f00c02a0084084141ea850390314041011074894420380303070401c40050206192088881148400e1405684802ca4a03034412000041c080d50540028045450681e8030900d0b0440b2000001e001485140c6c030f14400c214451042800d002c1402c2104d407259982d0b00007141e00341410849165070140050307201030310704250070001030207502d101400345988102440c1c0e0f8518246030304a81101e5900141400e820402c01040100c2d040780131540b103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 473958363 1250 473957113 473957119
    0x501060e0f01030e2b02210a03090c081f11040f03060c1806020a150b09060f030705040f020c0c01020f03031501020a02090c1903200c071a0304050609030711 69
    0x49481c05524242c181700c62820310f03808050341508007900b59150950102d4507000254200c684d1001811260000300040405c4001d2621082000642d410f1080d0041202d980c01000082125a56034040d58a05509400c3c4005c02c0d81301d041d102c04250703031503008104080341450710407401d29040095210003881e051000400c280e60b60128402018064442c1c40d0004694001010703409a980001a4039a10f00580c01c03202e0185014140c0300504c0c0f248650358400e440904860903903680c42c4107000e45551444141030b45807013429000035590391103000b07441710310610750405a00d502107a00030f0380c5411460021541513400040e08144010390001c2a02d0b0f1040e070501010301e03030030644001030342001280a4041e4000d0000c40800101003065401000b006401081800c10044800e00031811034440700c05075030045201001d0000c0f0800d0301801343c000c901d946800da0707200956549484101206a154100e0146c0c004401c002c107102061200a50081585003e5807400c40e07280da58850208104d692244 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 473959613 1250 473958363 473958371
    0x11040b0a060e300604060c0302031b0901143015060d1b050315010903080a1d041a0a23060f0c0d02030c010e03120c220303030c030501060e0f0103 64
    0x180241200001251420304201c030f200d500c1c2c11005698440344c007150203031504c60a1000415800d84203100301d903c46d1043c03d1030038807151823199429903c1d81c840894641040040c00901088660741c400400c4801c13000600540090b041600c1c03260031608482210310b02e034080500300501d003070b000080c0308480322045480603611242d401d01c4800424142605c8138484240e9412040c0c1603030050001c0d80211060303621406111004801100c261884c0e001c000c082c0c80040c000354070075030301558030149021021110070901c44800741c045003c841003009608580c030b101811300101070608030100c0c000781c51040d00e031a03c42c101c20030031f00c6075842100003501e0184100003099901801d03e0400d4507200d080104c02d0f031f5201302400000a550f0f421101d540c803c603500c0c0c054401c01d09a0f00000700c1c0c400d00003000c1a00310756038a60b408030303d090300a0b140f4102d89080c50303818108038110941078070b006580b2a0300c0001b440b0b60030900040849105030404414061a43c4e0042215987c00c0d4003d103480da000d18000c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 473960863 1250 473959613 473959639
    0x3110114040f030501020d0e0109170a02010e0105090c090f13030f050903060a0e010c0309020102060c090d1208090d09050102250914090c010e13180f11040b0a060e 72
    0xc524840c079445290003109107032000c010428190010030b4a030b03803d66000e1024050b2800100c1c201c13000f0010007000d02c00111881c0c0e00e02100070000d0401440b041c000051a18450344440703013945e404417084600364014803060401b6240c0100050340001c401000c2c09994070b8a03040c1a40e510f8403601000d01446101081d00c42900d20840860307424040240545000f07092a003041c0c0003424000c0c140000325428a40c444c0e10706840381c03240d03541e0181c0503801060161600392409282e680044a002d402880f403004200103c5c1840c42034800d2041ca0b0365a02c016031030000c4a180c00c1100842c4140f0400201403010007040c1e0b400248980141c0c145030303030074880841044c04442e1000c50380c0d20004070f050401105510010740140114840c040c02030540703800c603910300011501c149941141641c080800c071101c501c55416648498007040d541d504622a0141030b448059003440302c08011100a4500202c0c400141458080c1c1d1019160a84a03c001941040400340251904e100c1190240070707050040c1d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 473962113 1250 473960863 473960897
    0x90b090702030c1e1c0c050f0c010f0c0503040e0103080a080907051302031008070f0947030a110111060106090915050d0c080d17010e090f06070305011d01031101 71
    0x160403032a1203400307520310143c1a501c0c046c01054400e0405d8940740514254074401c5000420f2013652554160f5603070172580000e00040c0c40d44403a60a054503244003d120110f40000f14950b118047d50040d10110f45410350280014881d80c0028891411038000d00d108100540b241c180f0000700780140c100150b2a6503e1030001340d0300031100d51001d2981c1c8145400001c14440c6890800142c410701c103070030301495039454a01e10300521110700540c0ca9100b0000700d104a1030036115201401600050080a5560580002441c00c414001d054440042c0e44101405c1503801040d40307512300d038041c40078180562500002400440040c40b8032052517495009820480e01682a4500136040041460f0040c00301410665803030071190181c080b0600c40c645000000c00e010794880000521142a01d903001e80c03c081d0348000c8590042c110030101d10400c04400d0344002c050003803601c903028035600000c181d8035040c503041c070907252115440b54000c5c401c401800410360000b20000900001c0c20400e2841c5804020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 473963363 1250 473962113 473962123
    0x4030c0507031101091d010b0a11010203010e0618061509150d02040e0606030c0a0302070c09020c010504050601120c0504090809030d020102092d04090615090b090702030c1e 76
    0x402405070103a80004010481404840710310400282c4c0c1d074800c1c1d10303152500740010031208084800303e44020001000807599540c0100000040c519180301c420048102c120300ba0b800c01c0e041201804158001c010690400e1062200901d801000c03100d508c1c102800810785480e00704070b844020b0580005d114038552900f82200e00a050a180300301da80b070022082440094225004040941c0d2021020400f28680340c410713a4060761720080c1162800007050320582c000d5108501c101e4a15090400c0002c41214500c00780036804d48030000420240740a1420500345041608581e0051840310300c2540882d4807901907809071507003640c002509a0103414a49118002da803651b6616202d0503c141d55500e5040d0094000800241c90f08403120201e211400b45a1a0710340038590305e40c44064520400f0710705900b280d6100350080c2400034554403480d1441c15210303010340048170036a450310040e030054103003420110781c80303000740c0302460900034103980003074984011401c44003030000348104a140c1c4c9801400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 473964613 1250 473963363 473963387
    0x5010c0302190c02031903030b03061008100f1512030206100f0504110c030c0d0207050a06080a150302030f070f09020c0604150b09040614130302060105010f2003030609010b040e0f0403 81
    0x58414046c0c0400e240003401f500310000700705e0180c012000810800a080d20384e46041e40d510502402d0380c00c40200c0000c00419003200080c3e80f1030b8440c58580705a102d07003424000a0840d0421060b8001000c0c1070291030124050041c07516204d070581c0401c51441c1409801c02903c804031390201d83c0d1481c4190070b80d020f002d003041c404d00c1400002030381d65082000040d44005000c0d01d400741c41e803a6558200308240d10425104da039000c130341c085000407942600365000840210304412090083c41c3c40750040392400c004100a400643d21602050010704101010310300185105942545441e0240440350346900b03001e040140004550b0740c24200041c01a0011075240d900640551f141d86001d04011016290891048410611590100e0807002e0003030902003078207406400600d200d92030040112150201c4802550070400d8401c3c0c015800c2c2c860441407900b500580009540320300300b0304104061000103a00550101c10208410400420301561160f03201d2960408180c607640e4908050760080c21002c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 473965863 1250 473964613 473964643
    0x10090e070b030c1306080603060c0309011b02101a03030a08040201021002120115030515150f070506160c0506060603060f1021060522020f0c030705010c0302190c0203 73
    0x1c420044103c54000103800c000c4944032100401c15522141511249416109103405400003400a03000c50504402560007840303180c00040d5034600d0b181e20740305141041d22000016085a5101c040d1a09140100703002c0c92000005000505d0030031002136a07a104101c5400b0a00c0b0803080020150ba00a0045000729011204155610700c410f140c00780319800240a43c6001c0a0494403d4070014842d21409102c3c1d0641752460300c1d0502440308008541814814210400d001000300750000482040502281c0748108000c00542c1411035403500d202c50042400340c10030814040358070100b800094116004038007980d0256482e1a0440418100c1d004a503005803c1110007800900b481e90125048054444c04c0032005503203595410000c098501038420b25510031210513035500c4904264501c010301d401d0340c510040c40c06141c202003068942001c0011181508081004000e204080c000c000b80303141b0710315085260420118080000c0401c0b61803880400041441503011910104415411020341c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 473967113 1250 473965863 473965867
    0x415060e1306060605030705071106041505070c05030a020918070f060c110103050c090f040213030b070f090e0106030c0c02090c040f05030f0c09040f020d210810090e070b 75
    0x16107048800d40980c081c0c1151160702d81100043d051344a0301c1a02e0045010343d840700e203401100c1c0c407800005030003d00e56940c010300070000042c49619080b140d9418a45a481d49612981c0e6414982c811070303600c0e400207019803c06040800180d0710100f010368880342040b00b02140c860070345481460208a500b000b04007100b0710b0790200b0b030705400103006400075104000e510101001400114280ca4042c3c40400324510240020050341c82d00b40f059180d0810058030050608400203c25031491055600036a2110002024007c16aa1001142074070110728148a0902d9181c00c442c0301d1074071414030818042650707c0d80b070001e40c24803c410b08a03030b550300105a04070030704040180001a0340b051040b0344110380c0c0d1840c0001c82e4200415804240c1d40780c0742c0036095a48480c0700341301d03003104002d104640ca200814003d00043c2d490509200c443c500408540d66218020110208040c19098203e07041c816003c04020144458114101c2511007a0001080d0100030460365864080207812440080c100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 473968363 1250 473967113 473967121
    0x2060a181716060905010c050c090a0603050613121103090405100501031a090105040b120d02150f13031103040b0c0f0d0c030903020607020a091a03010e0d080415060e 73
    0x1081c245480751000c0c0c14265144850702071284082e03803640e44526400310301079034010019980106040011280038800340c0d00d00141b200300040c81d28400b1650403031510350b510014402d00108100240d402006010795504807200e50b200c400c842010740d203140040200104038010b0a034800d000303841108070054001d00036420020300a441100c080c1c056a4002450300d605141c0244007840d9070002001c1c007800d0444c19074200700c14007029009401d031440c0c108903d0541c154800104201c242c03141d68095000d81240602da50394461000c0d00178000510340e100c0c00060108184210b0502c07650594036090243c003180c4041c602c507007103004a03030000080110102d8000220f51000c0303440704d40b5030741400944d05048080c02040e00c2a482d000c1340580001c82000c01840103080c880000d00c4028002000040d00641d45c0e070700a8156000c50554540986031100c0000060509020341c0c00000d4044010702000e0b214004001d0606a0050000e0034001808040d8049074006902220190102c84100402490 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 473969613 1250 473968363 473968379
    0x80c010b090903091305070e0307120c0603112d0d09020a0e0c03010603020a030f020f0a030b1002101505040e0304030302060f0f0c0702120d0e09090303040f02060a18 73
    0x84035001070142210800040e41860040121442824003d007040d003610205180e00000301401000716040c0003511603c450307150303000c000b844018015440400348484803031800310107400490f03004000781418100103000701c110500c15110010f90400141d9410704190740162110311241c030400f41d10038400903030752401710101d81012504500070388500142d030340d4070a0305403031142c41286e00d80707441e180c103000520840f40f003a0028070250101e07240224414074411602c004903800381e084104c00000016403102059018043c0720003082040781c8050b03403407004580213911860440d142064081c0d9078091107103031000205454015110292003006020058202c040d601d5001c0e02064015210300e9000a4120140c11480c80c8541d500c101c20031042e84480c48600d1850f0401d440480c3d000502e100c80a005110030480c0840c44aa6543c804180c01116800c0c005c03108406071000040703400401c10040410041300c0c01c22003e6905440c1c05642d0f404200040342d032180400b220720b007481035811001039100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 473970863 1250 473969613 473969621
    0x315010f061b02060304020d050c18060915131508010908041d01030c060507030201020706050c03180c0306061525020108011401080601050a050405030111070302070f030809040513080c01 82
    0x14a81e038840c1418991103000001289448100095102d03e007000010010f003404000607159611032000c46001c060391000065512210003005072a03070140341c04000940c502105411342110442004180d00303942d0201241c0c50000e81d05c090180b1a07264881d80c070410680e140303802d0041c4a4507000f040308140c030b0b1414008075070061085061074580d00c1c81226000c0d961041c414100c0303078000d8050341c4062130044150f4a9402414050f0700b555401d00a8501240140c0645445464074409680d0740746050720040c1074141c400c0071841d400d0f50140c015000343c0d4600003a80b40e0841c02c2103401c20300580744800031003294403a201940002c4030840103215108810043e0754501c8600c00d80303541150360b0302c810b2041000386c13054803044d0000301924007140b150350081008000c441c01070f14113540303800c2e00d90300440d0070359207640009824000002102c200380755050201074043d180351803010382c0380341c03030b545600d4a10b0160040c0e062003907076540d011030f8480102a02040c501984441c113251240503050040d0b000b4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 473972113 1250 473970863 473970869
    0x30106030f0c0506030c090906060c0a050618030a050f07050a0519030e090403050715150b09090a0b0a18090c03060209121c031805120d0b090105100804020315010f 72
    0x10407840d400c080f40300d00d08502070328030800d42000f2903810140b0400820a43c141c0181000ba001601001016401c4105021540105016400400700da09120300c00b080e104461060194042d08148583c0252682c403c00300c440d20780310903070f00b19111b54003403c0003402e0518610340204144140078050a0300f40310702d41d00d519000c0c007035240d035000d00030b50341c081c0801d9400c1154002e00080040003d4400664180c102300d442000400000844900440400b11914210f400040c910301e00880d80c07103840d280402a03580d0201c030440c001d021144a10002c1071060000c0d005150041d2518400c050a404c0f003584200020341c1c201b1094440704c0d90700c1c00c0070750081d40410041c0b030080c82640100115130340c00003000130300d103050705514190000942200310020060b54107044441038a003080c00000c00c3d410000003100c0a1500c0455907074000d0113625008448510302c859001c0c00d1060010030683e40e60044c654034900c0f480c1801c103003a507228030020341803102c0c81079800940b030f041c840049a94120bc280f02425 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 473973363 1250 473972113 473972123
    0xd20010e070f0b09011b170a09030b0a020421062c0c0a05130f06050603090f0706030c02030702061803011d190c05040b010924030c050307080103060209030309030106030f 75
    0x945444106903c5640301e2210104d012036541c0030801c5141e0b060340d151030820303030203a00740070850400703030200c080207603c041c0c02000001c2c2d0f03500041c82400340c0b640e012a040200d020085142ca4981040a02110380100c11082c021403030359241410f1010341d030840d21128008080f00c6403e80c079000c1c5c11090f50901107807440c0745403080c07030842c4403507081140c518010781c4c50040c4446281e041c960a100b001e001c04202414104d901c613200090561a490040c1d03000d0184c0d48060840301000684840c904036072a40308000301401c05804400098000c001c50340029019901155240d00c1c844400e9240d048000c1c00c25015072a121340c3d4030f1400750141d13001c262181c01c0b41c1903c0c00f4104074104943c1c0c0e002c0b000703406084140f802070f08100391b1405a00c41c103078038001030405031000c60b070b42c00c103c4c00300400c0703500214000340d40d50150030003080e810f102d86d07035415030719051075070444c200160014140441400b009001650008009000e55003c00940d013146100800900110380c803450801c011103084041224 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 473974613 1250 473973363 473973389
    0xe120d020a0b06061215040f0f0606270e04031b050c091609140f0d06020c011404080319181a090f0a03080a0212090d11030c0d20010e07 60
    0x3e145013110444a110b1a2142602c500391106104d441e014403d40410300d602560302c040c100c000b1780490103a0000d4030b03800c00001408620f48070002d460341d64030840610b41402d010841212285d41061044144c4100d1a40c18031640d41e50314007035401445004d906a5103d44a06c81241040b000290344034414405452030080341c0c65503910401043d01d50b840e8500421a0240288554107101240c40e03a030260080c0100f1401180e5004141360800c500d40c10b80322aa00001c80301c04504003406407003014500e511b2804054a0143c460000c0390101610340210780182c0b008000d42d81429811000700404104081d141c883c21914100c03c9070703c90940300f202042044000103c01d141c000c1a8068034000b0f001c050000c04442d5030f400c981c8082d00408070000964203000889450004030300003441410b40354002c04100e8101c0c50301030200f00c1103014580440c4c2c01000900c68805010800c0710810b0864181030315421101d04481110386581a0101d07000d40c41c0025081c4055030005802040728810b0b00b01700 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 473975863 1250 473974613 473974621
    0x120509010504030e0a050d0b04020d0602120106090f030209040308130c12050106081b060f130b0406020c09060a0504090602160b100b040b0316021c08010807120c03030e120d020a0b 79
    0x200701792041c4141a4491102d104010110300030444240e030091000b070150b5281c240c10343d160b200300c1e040700ca403501054541000600c0403a1b000a040c001a0400c542c0205041c0e1860340014020307000200002d040220304808180c1c190700140a400003242c0c012120501140c4580c07034035000591100043d6031940c2010030002d0b4006000c60404190b0300d0b072003c82c10840481e2000d0101e2940310880100c0c4903541046000d9404621100e00e034040e01c440314800e80e44628100c030007860300c2c240c951700610441c0c03103500340608c640d6030300d0020007181d505a03004180000a030521100901500c00400322001e054800380c000c012030250070b184910006a142e06146465040410380c1c0e008174011690312007000c00c0810303902c1050752007071503500b8594412501161848a01141007a811001043c007161101c001403100348400c1c031040c0d014002c0520503021700c1c03c29444030308029079688805001e01000c520f1504150b00c44804070400c52080c1c0084410401405000070340d01e44002c041035070b01c5440d602c042 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 473977113 1250 473975863 473975869
    0xb090a05040b0609150d0e0304030b0114030a02010e0d0b040602070c060206130b0a09051f0506151210031410141e060609030d03060e0705070503120601120509010504030e 75
    0x241c4031003501500003402d00440c0e00500048842203c824a0104ca01b4406012407002d40c0c0620410343c49950065601c903490f5203801c03410004107030031090741801c0109441196880c0010654000d41c0c09183c4080040b150002140403181e01c400b0161454138000200020300c950340d0020803115100b01d141000b5640c0e103130000c82c2c482c1b00981d184044110740480040110b0400440c00f03410a2880070006841160b554a203480d08c1025862909040f90f15416044144407a1262952046050b105400d0000c2c20401110340c91194000d1515000c5041002c42c07800030714421240d024650000e01005202101d06106030341d40c410b407549107180c82c100310400e140a508100e219004109160400721078005038040380c19801002800107030807143c14058900b8a41c0c04122a0b403000b642074900040042c03e0400120345420000c0480c41441010419040028400000c407105ca00d665082c8aa0035281d960048880c442103511002c650383c02c000600504290641c4814000c510903220700d04503003110303824 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 473978363 1250 473977113 473977121
    0x414060103020306010311060d090f0204050a060602030d05100e1f08030a05030118090818010215131b08070306020c151501030f0b0306070f120e030a030f0b09010b090a0504 76
    0x700075019045600104005001542049400030303000b441c01d400c1005a1040c0b4084410b0003030150b03102d03441c0c80210410b60030144203003034101051840600c44076060100c00380da070b0722594070400011a903a00005507800d11001c2c80300090a082c0349180f1490800360581100b0092041c1e490703000c103001c61070001d400c55000007140c0307003a6580d88696007940c0c42c00c141100c0b030a090b5070714105900e031605001d00008210b800140003021032194031400c420380e0303200021302d0148081c11b0703a16400c01c100280182208221410144c0e180c3c0465003e80000003102e56071604030007903025481c64404d0711404000c00105401a1000005c010129401c4408195001c0106c0c1015503290310f100c0166070b020030307640d44a500181c5a101030b60401040403204580485e1a020b002c5800d40d00040031300c0c894a1989501030b0140d00ca600c2440d0003072291121900660340c682c81450b03010b0051540c1c40040b20108517490300401403812004118a16941c2d5821309808550310400c4120b119400004001c1010f01c1c007440b03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 473979613 1250 473978363 473978369
    0x7060e01020c040b060c01050f091603320a0c06081f180209130b030106060203030408122203080a05090706020307200901030807030e120c0906011404090504140601 72
    0xc002c1400d103600c1c00600009011010301150014402c100140a481c42401110b000300c221004582c11480c1040b2010b01342907400d034154101007806141003002c55141c280d040441a40305902408405101903105040001c120b4800e0040c0030303010301c44003801600441035044031920345400e1803540c0e4401c211300024940300081c0120203082d50080c818222414280380d80070304264170042c0f601c1103c3c4009003044d0300c010045003901c0c1c0c851f551f02c0300038142806002c0003020365000a40c03d50074995034281791030140d41c5210030082d441c0300025160601c2082c5c00b00031b58540c50800607006a060030014038141040321001400d40c10078001c42d614040c0010000d00b2200b059006d10304281c0d05039034010740c129900120b07002d0a03101420b000e820b680c40d440d030a4000d61062200c19603642061030b000e8501d14800d4252403281c00c060f0a50504600081101303c1000310480307201045a544800603102a085074085c00d4852034045404a084840c0d6809203010724090760300c136040441c00c07945290751894240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 473980863 1250 473979613 473979617
    0x7050c180f040302070f0308070c0f060818030f030f0a15060c150902030f0f010b0603040803040609050109050d090303090e100b07030e1003090201032003010b132607060e01 76
    0x400550061050101282c10510a1054800241d40c6000e42082e1120341d41080e940390744001141710030840011404001070502528416882c0c0c41c1600103400c040e03001380800100810440b01070107034a0309004a07002d0a60111015031642070102d4255000c0900b280d100086e185446003105040200c5584082100d132a60345998805029070b80c1c80c109a00f9900160303801903198040400180c3d020300c9850007007001c00f0000c01501041d40350b41425105007941060141c8400c000f0b110104100b001100c0d40030f45c2160700401c0c41030381890080c0c010a503c24024016001e1844440111b80e07008800307100b1070380259a210741803a2140704044a82c001a0b90040107030054003010041c1800380e81c080c1509030302a003044600c02d240e81002c5443d030191406034000007540c410340c040447d030b014418884c6803e0341480c038038519040340d840031007180b006008241400d0008100c50314113030750111800d005003102007031810f5000081d001e25a03541050301c1c40420103010b0a6004030b001e80c41421500c000b08016 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 473982113 1250 473980863 473980909
    0x50c070204152304150902070c0f030221030d0f05061005090612060a0b031f0801090f03120b04090f03140a020c1309051902030d030b0f060c01061a07050c 68
    0x46078125400b10002c40031341c00c07035110700d80d003046801d54241040040a403804050b071b40b04a41d140c41d03402128950090120084020424409600c5e82000c1c80684a88819414460b40c0d66200c514035600a030241c0321902400c1c0702c004442110683c110745c1c0180415640c8140751a000842901c2c02d008088050317401980a02c108060091080c00c81c3c1e03002100075142c10a2030740c441c0140c0b04640d0041715040480c154101180315414140007413407004001e902c1c000c201d01d2101d03558600b0000390070000038003004114880256401916840030601e414024801c0105400c2850400e00c11000c0650584c00709a0342110204e50301c4c041d4040760689086580600921500c6004102c3ca441200c00161ba48039504c0300031030009141042540d56400c910368042c4190755403403041500e483c00c4035180703404050a180d0300030303881d40710200c0e4005468403c445a648035400b2410050040c82140c0c40b00308040400c0e2444024010b41e0001000c081e8061405e4410510085050241c1003030300400050901d911 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 473983363 1250 473982113 473982149
    0x7090506012105040c0305120309120c1518010606181d22020409050c1201061a07080d060b04031a070c080306121c02060a180212030d050c07020415 65
    0x82c03a0321581d4090710a400c580c608940b0781d140d5920300000c216210b07107000d4000091042414082003003854100c0c02e02c107510f16000928440c07c1d01c0300c012140903401d208601021505009005800044100380c81d00208071082c0d0390705000b001c0d56601082d002c4000d138000c102040348151002c840303030660444071500c2e0f202e40f90040c4d201099400c0c0881012102c40411008005a88a00440da1241e008000400c0d51028180030880c1c00d14955048100982c5000b804000c0c2122440503842c40018848100c3d440359401d09000a56100d18510400d0041c07604401140d420340d240041c10540e03020310905091101e5254168031000805d869080200b1240c0349001d002440c240b00843d4001c90181050034100c030380602251400820003040100e154808408480150f410003100e548000341c100c5c180144002d02001500c414030101c030103401a444a02c424542d14030400c1140c441c1c4140c83c000700664a44040c001e42c06410410301203201e00c0c00c00c4508204100000e40f10340650f425403d9040720082 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 473984613 1250 473983363 473983427
    0x31510050a1206030507150302070803010e060f040504050d1124011a040806060d020d1208160206010f0303080403170c0301061d130b0f030f03090117010f060c03030212090709050601 80
    0xf6007d8902001c06400304180710009007644041d50092140740328840160800c4420072800c5a0199142030242e8603040810020940008461201512505000800d1100071017880c0c00c000a5006c07001031100c042141d08040d81e003c100d100d04954103142646460b0000d45504c03400740c8540c0c80381b0580341c1c1c0a5800700d44603240000303000d15031038401000d01d0900c04842e07a807203049a012020381e00216140808008074140c410440c405019501d00c01b43c05107605010088200c20400e001c00b40421505800007070800d80611801d410303c5045c0d298000c428039040c502069554024000c10001034400403008807004032118544001100041448405414810781790004160220700319034846c001d211a92540d84081c020f04004c600d80c0d00265a371410118009040100b02581c0480c0d41d9102d10010040000e200009030292a85841c2400015034507003000c4000c2d0280068541d0b5141c031000500c03007034020010300c0070100c41c0b030102c0c180299a0b40e07000541d03100b2100000c06844103100720300103211170 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 473985863 1250 473984613 473984639
    0x90f0d050f15070822140601050108100b0717070818010e090c19120e010f0513032c1203120709050d15060801240807030215031510050a1206030507 65
    0x1c0907000b845e02c07594519203e510181d04158040301c00b0703410400041c0500e5078800c0c22264045460b03807240c0e18035443e2070001d03502c6202d400e8020303184038403141c85650044036070400c90b0070f05900490301f147c030344141506050000c400030003c80d01003a506900044076040003c07006118900391556982840d40014980c00000140c54640c01086400141c107000c0d0301e01403050000c511407940001174440010000d00044070f03000380c50000040d071201098000242d00101204074800400e500b10440021004400880810107024591202e80e42120352075003600000508041c200195460685854141d0107a130701c00c0c3c0d18003c2680058a540106000c24280b001c92070030010080f00000d05a540c1e54040e0b421039506642104400c0380002d29503000c090381208107000740c4150301c043d0012a01c0c681c001080c10400c0d80000c4003039240400000e1005810806404a100000c0c001d5800f04415007401000d5038880c1c0c61003800b04600e918495803d156500c80d440239280d106000b40060350900b00810091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 473987113 1250 473985863 473985901
    0x160311030703050601090c0219020a0b07030e1c060510141002120c0f1507020c090606120a150905040c0306090804170a02040b010302070309050402090f0d050f150708 73
    0x14801c00800000040080002a008000321303c0c0006006601101c006d081c440c3d0610207500980c83c00c0e06500240c1d489080c1101100c00b0780000c1c0d552841d2a240035144c50010303189550b841202c41e209402c441860001180019100d054100425070b2020103d09120f01790340100c02074219065261107150814031004020b44400340101c406080c1c014510170764a07032065040681a03008416200ea000100b00414031801a800303050b40c8141c540358070000c0d510440b03405094070618501000c00c019440b25011181110344ed154686510700c0c0070308100d406004c1c50b404c0060501040300000036460354503c00ca9004a41c0080c4040c141c62071a00c6110140c1152070b4107441004040100203032014030751190885890b199000380900d201c290040204462018041c207040c1401003100d000026400703403184083d00ca04841c010b0303c4503408408038101d44140c15609070440500e4021000f0b001c1d000a1044850402104661140007030242c00b0700240b01c00c2d21900702241c454004a40301c018082c800d5610 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 473988363 1250 473987113 473987119
    0x1009150504170f0f04080705030c1e0d080705010207051e0304030b040209060f0901240305010e0402040f110f071e080d09021503190b0a0803041a0d020715050108160311 74
    0x2004d10880741004141e000d03074890320f96a4030180040000381424081d840d17221408481d00820200c1c2825100494060b42850354030441040000104101c000002e54031402d4001008548030340661810325994080182410b401140941c02103180450000841d000c1d2580901840250744640c3e0134401d0001018003010f50000b40d42c080010140c940d2110140205581c00c1e8001c021b003013240c1000f400400008440c020103003030800600c03a41d4841d9500940007941a03078000303460f5444210610080c140014004d1080d000060720308103503030a10001d06510313801200301c50120303aa14000c5000c41481040018541d6405120006044000c2d6121000f1180050903e08400c840000c010000d5841180d261a902c80c0e040180c0103070880700d2080759400740007a58900c1c1001d0070103591984c0e900840c4503001c5030358241001105222052816a1202920b0080c159201c054503e4040e001ca0031000029000c1c074980000004c0400000071200141c02403079460300d444604584480c9903031044004e250760 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 473989613 1250 473988363 473988367
    0x140d020306130b070203270d12030207021c0c0501050f071e030f14041806050901060242070203070f0b06041805030a0807111009150504170f 62
    0x4096103060140d644a014100b90090305104145410300f184100540faa00441d4070601c0300d044640680d010000541702d40480c841036981d070f29400035160b81c01d0300740001c0100390b0b19440292141c2e05a005040c0303252003203d900ba840d0f8490707216107070a0b404402c009401d11030304007004c02855018000920b0a900c60311259131030400280c842440304205080360314040b81d9590b40400031b01d94800c00712080504a841d024200011440d40c51100b4040c6001e40036814042d40c19035698140300d503012070000c020141090001e580e40b88006074642840544291003001c003000c00300d80518104408a00041c100e1480030b4280742e0201504d111220010305171402d500c070070401080071591032824240854484d0841005a140610910040c0d544401d00010031024100071080000ea0110907a048103d051810618036070352000b0446e08000c030640c011405008040710b111407581d02c0d4020301c1400740144041e80c180b01c2d007180041c1c00c0755000c0b02c01030102c04000301411880003221006000882d144400700f4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 473990863 1250 473989613 473989639
    0x50f0c0604050c0a050315010603020a090e010816080607080411060903061017010e15070314010b0a0e010509030c04090809150705010e011e09021306060807020705100914 75
    0x1918005040c0c9042d1481d0f4090204040e06180c00a0b65501501e02070f8041d280e218084070180080280601a100502d81c000c14030240e1248034a185034000c194000607150340f540c0d03075003003542c4a8115181c6100e050718407030000710310010f000884030300070245035580800d035a80b19200c092003a1400f140d0150f01904c100014203056074200880b0f0301415158034a5a09645090003403180e102d0800103a00780c50741464410700c080e1101049140b1010159522142159100c01e411401803007083c00d0614041d01d520008601d0211060180403004903170f868000c6100c50754001540d550103006102503155000b551450503e0516401c064600c80c8654107650400e00e5060001d40031000d0805501510350000c103080c418040d00f4020000c41e20b518500800149140240040d400703803c441800300680e8841c8142021911100b0140e0303441c00034040100215078582d40001c0c040c0206490090061090b078801280c41d2402e0070313040c01341c3c103402d4455120f01450000344240003010440301562009044c83d400f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 473992113 1250 473990863 473990887
    0xc0c0305220b130807050102030403061a030105041425290c0d0e06030105010c140304091a01030c0806091501142113020307120f02130b0307050301110307050f 70
    0x354003030501c805140c0d444030804081c09168030f800354842d564560058100304030f02e03600403045038207590304800085a4074281c880c103445a806e411420a4156203800108403e021500191510190610041c0c5805900c017a0410315400042401421031190004041000351950300c101200482c0c003286221604801f2201e4552580007800c458005d600441d255180460f4803207584a03143c54211507a9045504200c0001c050007010b68000b0700110616090b000c12030402c105941c010003000205101440303d14002081d8800312511450120f070414070448139541c059240c4500c0341c14050300444090340c45003681030045501d02c007501d060105891103200305403000c0c002408154405407204030b0700810a184107255040c024840558400c040d0005001640c010074580100d9400f0f4844c1c11031603900d8203201d03a035a0400403000354801c1044002401c24440394001185102046040d90813869440c400d2500b40c58405043d01611181040044c403500d016402600d60707403e00e9450380307007032052000300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 473993363 1250 473992113 473992177
    0x90c06020607030f0513140703050a030309061406030d12090b091b01020a080702060d020d140103050c0d0c0e1e040323040308072a060908060702010c0c0305 69
    0x6001a0003500c104010550540900782c40c42a03c20400c00082c605000f0007007201c0303140500101604404e84100414a1003042440003542d00032068442c1d18800e80380180007800445000c031440c60418400d4441480307102145c43c4a000041c0c00b505031940c0307200c0100e40390b02580e24030040e4035545402500201d0171083d01c1502c607e0840005042d10342440301f1154104071a06074035411580100340035800100000180d51000760306441f01c0b0340750311810540c00084d0142000d40c2c04028607240d6980e01024600100c64100da01540640c4c0381500901c042c0b0a48180e0090080c0c0010840d000410029090080d0341d03900c1208121610030120030b801001e00100016541940040d0384280b407240301c51400c0040c0c000325100029568039092855442c5120b500600101501424810003090038a010300c4a80e24280324200028030301a0f03407a81c0d0007038000c0400e4041c80c000e9204090009400c03500502c2122010012502c0e0700d000c80030181d5045a85a1000c280d01d03529041c1800b0382c44000d071a03000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 473994613 1250 473993363 473993369
    0x110d02070b04060b03060408220506030903130801020f0f0c1e07080c0303270301061a0a0219020a0302060a030f06090b1207180906020c1002091804030801060e04090c 73
    0x54501e103500305428460309550058a41901c240c0000042c00005030010003150742c201140400e04620310840c44002004108550105800038400810001e2640001c801061034584000342d81404c41d0321400c00034201c0c029942040c030ba0708020840144d11640001c040d043c2c0080e1081282c803108813022a240640f084050981c2c0140e003c910244880242405100242c80b0154021030a051003880c591000c03451200c0b4258151203060a1041e00c2d480c207400c540050070080421017501c014020034030310301d54480408080140681c0c5c800080941d1050a9420a690003c00c07440d452402d41c1c0804c4410391040a01300181695902212005078043c06041c004200d9801d000811007048001e100c485500184c50140c141c100350380a00c100c204d03405103c0040106501c0004881d0454903020000307101c0d915480c6801d1103003501040c40d03401150010302408605560b90b511680105070145a240d000740c80040c0840c242100600100e48102c14816608000410201d070307500703558a03a9a1101d000b60 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 473995863 1250 473994613 473994623
    0x609060403210314070507020d17030a0f05090a061e05010e04030908161505090a0e070e010f020a0f02062101091d0a080a020a0512070c09020408060a110d0207 70
    0x20b482c01d00240109503a841e0401d1600302444024070010181c40100801001c0b01c2c01d0020102c0c040095450300c03185411802d50010842000309109500d5284503081201d030702e4501402c080041000c502580105030144801c6401480300d003c03c0d648010107070055048600c20802c1003940004652541e005450003044643d00387c804601307240c100200341c0181c03034200c07444a0380320300c0010a00e020200148070407500555904905407070030400440e224460079104542c04806480301081c41d444500320f00780030358000d0f1035503070810500e980190780700c102c032101100168005418440c0414004810806418401030120f490203030f4996100340c1c00601010802030200030b4034014010140123100c0c10f0304415407e150084001464440542e0307507490b009000300000390100b6154203140c003c00c8002041d0354000d0554055825900d28640c0c1078202c0754040d140f0b07013042030000800d04900c1c400c646c252079059000c2c01859031000c0603035015105405003580c40c24420007000141300018400340c400c50b4418 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 473997113 1250 473995863 473995883
    0x311070312030b061c090c0b0f030a0501060903170c03070609060c030f0e03090114090904031701090917030601110d0c111c03080406020c0a0812180706030b0609060403 74
    0x40e00040489400e00700b00c900444081020b01040c0300141c030030f0f0b29011320360341c4080340300c0d86c90b0700d40b80c01f2404c865030005400c1103010a4080820369071b00e0145100d4801c6041c1001036a98074481111000c200d88400b810003140c0c20f1401703c0106200b002004200e14000c100d9150034615900c40040351800001070f120941e40c2d5804020413075041c0915584103041503c1846a0b480482d041a02c0e1320599410a05101ea82d0710144040178107102a01c1550300010501100f514003401c0c050600c04e04c040e402030342183d02e00e0021501150354440e142d542a0000010b0804121103041c45c1c01c55032019001390305000c0754040c000403100303080081c1866100140d40382c10846590b4070b803070810351080c55089441040403040032914006800c90750030310b0b6a0140f9003104991070701d0078504001d104140d81542c441c05144500d0045c07168200c020403156078046801280c1d03a0340d070040300b00a0501c144440b00190420001040060300c0ba401c0302da9407801c000c04c090300d81101c110002e1030300d40c0a0350040342c00b4254 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 473998363 1250 473997113 473997143
    0x903020913060e0f1b0d0f0812010b070b07030e0a0501050103060c0e040b10030506010519020618010e06010501080603160f140d0f02090424090204050603160e0403110703 75
    0x260f00035414910454070062086030000008540c0b1000c01c180e090381c0c0e40b4890010807485950f08982d42116a40002548040d0301190500c403d89900c090004400c8442020001070950a0740080728080c80d000300e902103094071061022006480039100003510b51148400944c0466820710849000b10710807880059080b494000c0901a4803406c1c001c03510a92814020182c5c68540100c40720300404540380001f05a50360300016551402903c02d00c034200110240003600c02034000501500803058001003a00c2000c000e80c1d5103080e03a118000c45010b5800850040141c0d5006541c03442d0880402001d0307230041500d802c28600c0c90842c650008402e041c4402e42000b00500c051000180140c0c02c3c0c0d140191818281c903641c100f020f106e4030080c0629000c00000b0f0038814001c540f8a51021a8217844004800400b00140503080d40c40d010781c890752402d0081100352130000b03402104109004041030b02c03c2d10300304c05603e00f460700800a81c1030041d244107280c5100b805201030b001442c800c0c0326000404035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 473999613 1250 473998363 473998373
    0x906081308132c0112080315060f040e0a060f0b090904060f0f1d03040f1206021e0315030102131703090405090607080901020f070f03030b031902040b040203040201140a0903020913 79
    0x10040c1c1c005c46040d18034100e4140420005c3c1c0c00c4030f42c80607051140c0c0303104181020100704907105001c1c2c0740c04411004a408108154003811040c0070b00b800c0d5006200d80386d01c41c0c5020008490b10310a0b0600e00d0810400c80c000c030304100280662250080200140c400d21a45c00350040d501c00204140c40103a54100c41a1100c40380d401744010100400000c43c100341c20800400e5100c91b01c1d006104884509030a1401001a141c0403103030000403241500c00443c1c82100d100764290400e03215507224080c000304001c028101403094811803405031012114035483c100a800bd103006551100005000421000817503840d43d0103914098000c0000610b8540390032100100320f41c0700075000003826401001030f026100345c08801d4500141c0c00000307500f6054000d1030144d00819038113040941600a0380300c0344001105040180c9401c4c3d009503814025050083c0420089102c01c03503009002c104410031449002e1181000361038940094104852065120b0300040d12054045682c010f65090300801d07802006 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 474000863 1250 473999613 473999699
    0x7021509150f0403020a0f05100c200109030f140403020303070309081c170601180f1508010305030403140709020d0515010e0f150f03041101090608130813 68
    0xb03006080340c00c0c50ba400940314403411601400b043c0030003020b8002c0c0320062101c0e030f1600e005080f040111046003d005800444418030b0040240141ca10025504c1c0040c083c1e0405268907a0303c8020918281e101910418440c2409800301c039024000480103888c100001c00b5000d010342c030343e22078583c44c00e0000c3e841d1040040c8540d580407682074103800016004164801c044400c07010410032941c40c080100c40707000440c1d83d110302c1c8074070900002594541e03011116064070500010101c003007200d000c00369000c210a10004010398000c01c41000464000420400c24045080c10f5a24090b95803c05c0420b0780c01c4443e0090060783d40300180301c11a080b65a030800c40903000c0c00c2c140014a000f500090030802200c442502071a4002850b40d026284c040817290100c000d0804a9224101400c01c030755014400c21010340802c1c1c1d83d82d03010540e180102d083c6d900c509550360a0604d402040d130b4032400c0a821007030fa04880d1a4003502d0200d0b100b200a00894501d4050042020060b445c85100140d69 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 474002113 1250 474000863 474000871
    0x12010605040510150c03030e010c0f120603030512090712030203030601120e0c0d060b1e150306060d0b01020109080d05060a170a030c0f0b01031401111606050702150915 74
    0x1040303a26000c0002e081403103030802910026017042e003c8074070f00d4203042c0e01402059648a099502c0c28411014042d00b001120303450000355170320120070b503480384501c0341184c40902024000c99000e001e29001e941d081071017550300180000c10b641965940c1d01d6084420385581d40c3c1103001d60400b004009155a000e00c00407003003042c201b0107000c503003040703440d55440780506403c050240e0b0f01d0144140601000340c004d44192600030b8a00e500c484d044d030841c0c56414551080451007584a03800802e4190401010389000f0034000f4055840e05401079500303001000240001411365403034000820101e074086011380070b050140c0c840421a45020780c100a0346504640001000411010310030b00e00d11000181c1c04400c561500340310052904a007080e9102e040244801403040034014000700406c004010503520214010009115240c918818100b950103480000880500d00d4081c1202094040c3c0010360001d13075a00541d0500d10241c0f0307101e5a21079044680420036030110012207112440c0d40010b42d40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 474003363 1250 474002113 474002131
    0x60f08150a03080732060c0702100c241d1501140f091602071d161101050c041401030506060313031419030e0309090f090705120106050405 61
    0x4544902000102101c01a01016140440110f2900100710281460400d400040c81140000300a0141400c085030100c01c00500b15019041c0498403502200050315040740e0300401514082d0100c0104581d5a000340c1c030705440d4581c1070100c111030f00d12030b140c4202150401d210041500d4006018400301c05014294a410592003030b04004091503050006a0541d03480c1c4036080e58114043c80040c00304dc03110b00103141c7c00321000c01441608440d10804103e212003940030340398020355941c00c04100d0985102101d4944c0c120034002803808621119200605807941441d030360462814007404d00710f400c00c40e55113064043c00113041c0182c442b065800c00a070b5609190078019880c2c84070114141d030002030708101d501d9400c0464102054040c214036404904070515007901c03094000000c2c0c401d044c2415805000c01e02c0c11070074101c1c82d20044125880072001410700c59494030307511400d03508014000c103481340500031000c0200b40c03941c0c1c0500034150303000407000200f60315080c141000200c4d500078142800e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 474004613 1250 474003363 474003391
    0x90b09030703300e01090c0e1005060a120c0c1b050a2108070602030a060b040b1b0c0d05010504050c010906020d030203060307050d0f232113060f08 65
    0x1c0c0d4085a00d10341003d1031410340c9920251112400e42540c8110304582d420f50428210982c00308055002903e40c1d0701451a00710300c0f9960f01d10310110400190703544c0342c024003011814400b900303006004201e259020310707203840600c66070310301c5000700d0301041c2180000840000382c0f00d080c0552000200450f00700754414014035072400b40010a114100d1180100700000700942d4020007258003081c031155a001510903035905558505034002b98811507030701c0941da18211011a40480d4a01580d00340d40790084102d280001459404040800544180f0740358840c1e242035070940c1c2c6070213140101a92003000041180c0c01c051a0240c200321483c0303070841c1044254031082040c90fa00180c000f0110b801d50400594075120180807908081207508000e0300b100a4482103002c01010510940c1c4050040142c1c4450000203004214001d0f8041102c501c1071380040041002c0c1340c0241c0d4441c0c3c40710ba010f03010500d070200b003003c0100d11002c141c2c05000442e891039840040c1a401c8031165a0141401c90451 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 474005863 1250 474004613 474004627
    0x901020315090612070816080303040309050103020702040603120507060609050f0601081b07080711010206010302060405100e1306031a270a020a15030c1409060319020d090b0903 78
    0x203030901c0c4910381442000c142000c11010b844d043c1282600c50141026601d1003034075007558540d1006d064508240603c1e904100184041010083e280600d6042c0d903200440c0b840c1c500110085d4202c0c507010707680650380d01c0c400000600c02c511038421803800e0340c1b00d00d41c44164034103002045404c50340c002d91503503040c0000c00c200d000003080e40fa603000a003400e1411450711880c0d100c00106040c0544101108800907102040c44040030181458038401d03009a00e2080e80880120f03100c05017844025000340c41480207004620b402e401203a089413203443c00c1c0c61008003800c0020121091844083c4005903034403814004c2c0440c5803a85902c14568420000e018284800c540078070121030341c0b210490490380340011140260074408010107940084c8154009501d42e507844904280312000074001c6841c03d4402c15855000b420344030348001c245401c040c1081c0308081842076545c001070031080c40344900c001c1c2c21090119807000e0003541500340000526008945440100e00030042c2c80c2500340d0740140401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 474007113 1250 474005863 474005881
    0x1005040608100c0507051204051e01080a0b0f0901030804030501181212060513050a0c03090317061903050609061305101a060d1a1503130305070c180509010203 70
    0x54a12860102c10029100804840c102d4140c018070384020721600407180c25228402c001809401921300031a94100d9412030311103054065514122030034082109400016031020706a0710480c0c1c5102c1c042c0c40312203a0b000d41c1c1c0c0019202034090300211100a00403c00b4024400d0906c5031003260307075840039160402d070036580b19200c0040d121120802000b2007107000031204200f54000c44002c14020300107260605130300056a0140104940e2400510f28100118501c280300e4010070020642545401c039440305200f0120b0181e0b00c0082085400c24524078410180c5404080108021805031000e0141c17406d1012402d8113180300600b41c82d1403980c5407042c02000c52004504014079011140000852105140d20280760501c00d00081c0d5009402044101e0802d109411410050140b903103c0100000d6007410070100c0d1045407110040f80c41d0a00006040c0c2d0007000b00222068083d0408038107000ba02d41d20303100c0d04103050308614008040c820900001004d980102a000b0107214002c0d42545440f0000d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 474008363 1250 474007113 474007123
    0x31909090c02030a12200307030b010201270f060b0918070e06090c0904090203030d09020406050a060507240f02070201181a0703050706050708010608160e0409021c05061005040608 79
    0x2c217070015901d2040002c1d4501c6440c1c40c03003e8140b10b4217115124500100080c0041c60300188250265007403800d0304030001c04400003802d210b0500410021003422586034005000750511045501c40c1e95111030021550340d40709014072135802585402405002d1201c3c480c189080381c0d000d441c03200001000d000e06507940d0701c54039078440c0740003400e213448042d07a1000401800b0341c8540a9003500001941512103020398205010480c02981e05016295441d4203002d4040329921410b80061028403840000880e00300d680f20340c403240500608100d0350002e501208440c0c203642881995a40080c240b0115600031b0300700c484001e001120388a9103403030076858400340002d200100d80304010000f404006c141c014010b8543c060742000c410031152070030400252542900f03004020114082c0800541450103110098000d81c15aa03160080d16503c0018000680a0030384101e034011100f0031803501c0d48112040e00c403041806880103242904203030440007000d80c1c0301d801007406107007812070900507a040020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 474009613 1250 474008363 474008387
    0x8060708010b1c0c0504302310151401090603021614030309012004091d1f06170c091b041205100c08040b0405031909090c02030a 57
    0x80300d50741c036994021008500c40403d04804011454841d40c80040350303111010340284c03031540c0c0507441212121000c00c00641140c80d024440148801e1215000924000e01d840c400030854541d2078114140fa005039003007504118240201c203580b45d100441407401030180b140240300702410100c0c1c0c84400300008010288900410081c56000290040032401c0c1480442096400c80c0701c4c51040b08483d6202d5031a54070607142d4011035030814460801100e105071041203200001d01e00e1a03d41450320540307001800035031007044000f54542c011090620020700084000b00001e40c00c2800c1200b1041c0c1c9042103c0564005080840032412050100078001036001d20110048401130144c0c2c1e20081080c0035001c0004611410076004500010221032901e119a4030307504c5801513800d104015500403003165250131280001a42403004200810740025256412a0003a03043d6072034031025440004d140c3c40c02c6082500080d0b9040c000304240d80c15445040c40c503204034405145088050b010060070080311754 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 474010863 1250 474009613 474009629
    0x40f030204480804050a1403190930110a0e09061e07020304090f0e0106080f010609090c0603050901151e080f0705120f011103060424090b010504090510030c0806070801 74
    0x200d1f0741202243e0410649640c1484c140400e0190b60b08260020543e0005228030768002007401428400141e045002e101c00100c40700403044124095110440000c100740012504040c2c80314010030220b800700740a9200d8140c2074011316503030034a10b07041040403a401c45019505c84104060204080c1d0100455045400c26540812070012350300a62005008142c2c00074019031810b80005520100400d00c00c0041143d60001c0012a9458280c941900e0210034014510183d040003404124081d43c4207076003050300f2000024015020070301440c1a01e400c2d8101108440f9185d1a15450200c0030450901505101c40a80182c0110404040d0b42e50450300a1912604a13403800482014081104640032010750000781b203907020380144591654400e5860341c0c012420b10f5540d450701c8101ca489100d024481c04034501405113021000c00040c080c042105042100c100070004407a416401103030300501d6425040715000d46075103405a0095607540c8401c000360000d90811613425008100941114122 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 474012113 1250 474010863 474010883
    0xa05150702121c09080604030903030c1e08030603071e1401140d050609060d020a0302041d03030906071701030308270d02010501050f06040f030204480804050a 70
    0x5200040070030040d0742101980703201e000d0340f01901d06018048039000103001e844940c4015110441070b51940350866000c0d000c12540d440401c0042d115101c03a00b01c0034014510442440c01500480c01c802194540503190740c800070090102c1803a080c0020340007080e410030b400100c09c1c04402c0b03c80d0098002d2046140400703071788541c05110390007101c40180f002d007a518a50b550701c40b006640340003058281d400e18010a0f08000080c0d43d803c202d40404042da070001c100b07824080c036580c00c02010f4070070700c007402d80007401c3c03c0c000c0e201c401402c2001c1d40c080c08428001d80100d2500e2a00200301d4000318604003140382d1608010404280c00050341768212424018201c0410300d8405a185061440b81c4040a2489400d440d100010b42c10750150b81607400c01c07105500000c20343c504111444c01070340194440181c000000300014031380703640102081c070218103c00b5038030340300c88540f15410503000c19503c000403541041071802100031002c600801c0e07ca4108805242400c0d01d0b2565600490700c2c00400c00d40d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 474013363 1250 474012113 474012127
    0xa0201080a0906021e0d1103010303080a1a1002030904110f0304110103020702130c0e090720010b0a0609030c12080304020108060a0504050c1210081c0302070803010f0806060a0515 79
    0x203e130111003a4500542c00c8140700d0460103140f40b85a400f50580f00029844c0130980da00e450a410101e034100d0341c00d40e484503019200d03148850018111240111a00c0e0705810180c0610f440c0c80d154010f540003940c000d1500c402c4100144010784045016801c20b5400405c52040e41e0180c14040d01c3d00150800040084c0c1c00c000790058009102d51503001e50f02c82c0d40c205100003240d4181d040150006030700e41d600e04a402e2120140544485c0a546600c0420710b5600c0c0c1103804802880e8072189500e0a10000c81c520703030500040741c0c80c00c003203400c144000b40080750203000388600081e2000c028250003904424150312034071040624000a04005e0401c004603020034030503915130300400040c0130010410406424045070203034540d1f000c2c4e0500c2c00041c0b410800544c0484961184bc41140e07480030280ca010742c541000c82403150003e2401d03009040d400c1c08544041507545010354080c0c5442c2034803507007446c1408440c40c60240020482c610a02650b2000e01c03660726051320441c1a40741252540303841d418 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 474014613 1250 474013363 474013373
    0x130c09050a06140a090e040609020f01110325140c030d050c0706050a0c060617101a0910030c081b0405040c05010509030a02120114090d0f210903030f0b01020a0201080a09 75
    0x85c89500034400c0e41e620340140824002e0303031342c81581c5c00342c400c8032042c42000e8046d00665502c480f540f0041400c1c0c00030302c4451681566142c0c40321002484160190640d002984d600140c0c0c460f100d202101c5030311400820103281820031008500e8510750821703508180502e605182c1d01c04060044c0c07003c01c14040360000c2124040c21032809015031218052129540f40c3c0d031018a0088400d90100d954803441581c286121f00522402c6252203a40c01d094106881b1001404048000903226191040403200000301040c10703038001c1409468200e0103040b98124051050b03c0034010b0a18180c411807901b004d100c0054816035100049a10138201031f9100c048031000241031402c20303000650420b007405112005503c0661150b0101c44041d0000c0700c0e2525203006030340ea145000086080801c102052906025000e01103d0a0048254848401c3d00f426030314600b041d1080d104007100441d842e03513001007841c03c09006900d0712003002c0c401011641003075000203021100150030f0600c8240d171880c0c9041804 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 474015863 1250 474014613 474014627
    0x3070c061b2607080a0f02070b04082a18010302030c0103050f07030c140f0d050a0203060102030d020c070f06021e0309100c080d0203040c030c15050a0305090a02130c09050a06140a 79
    0x294100c135025445150040c4040d2440c11000640c0340180075850000c5101004c0e001610207443d0700c10014845081000d03503840f0060038840d00c01580001e901000e00d100e41d104202c01c000d44030080107400903545544141807525400138200d5042c10f05010030403468030070713848603281d2080052030081609603004000313440540d082c102802c0340c0200021240e90391984100141042c2801d002c080103140e4590a0a00803070105a481600503001040114000d410719000341240220040a135000700d41d075020302c102c828503282d02440140e00442c000d40260740484a002d0031804107400174600d003c0c103035800102d29040745903424042c000720182c00800d0043d05001c2d40c4034500c0340d42085540c3d003454203104000308584c0c403044400a1241c0c2021842041c0450040c0d085016900c9103820900145000e80103494020722901c0700e441095100005a51030000c41c40003494403990000701c00c2d001c034000522803001600680d01804100d2003c001207a40090b8059204042c184a26181c10350014125451 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 474017113 1250 474015863 474015877
    0x5071511073836030a020606030a020607020607081317010f061a0f120f0613021617070611090a0f030203120c030c030a0201140603060f1909020303070c061b26 70
    0x310f03001c0404204070000070051803404065003c94000e6580c1320109640c1d1030149600a400c55001d001d51001400e00f04081c0003c0b6120f07480305400c09e80540309001740104194440c90311034403844103c1e0341c0110207101d04034850450000500005040c020a520425008202c940610b0f100040c40a043d0010005480101014910050150034003034012540c2c00c009880750352241c036021804621550720b5108490b0039038200001180420495207614111410a0401c40d00752001001160000742d55482052001c1041c01400c6407180707a913006102d4420741300e070400a0703140c0329046c0600c00340c1c0c1d002a00781ca40103074030b400c002d40c6c401d19405a0b03803d600407498841c40c94480491002c2c030690b0103410044142448014440c02c6940b200c040581e0391f2020341c0c400c1100d290b8000401d5008541d90b10711100f0300314824001c204072803543d01003850765014440c10f4031121108039040c0700c2294040c408058000c02c409001c0c65000098440b01e0440c61180c1c2c4960400c0c0844038000d2a0510a0003a02c8507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 474018363 1250 474017113 474017191
    0x10b091806040906090f0c24030908070204050f0103061503050606190e09030309060a020a1d03070f0b0417010b01080a020306041407030e0c01050307050715110738 72
    0x40c1005450306c0342d00f080c2450300c1140e14442c840f1000c01d504112007810203103040141c580c4103503103802c04026001000301c07590070345042c4c40410200e009600d65025850040c0c0b4990071601096146040060407128424010040c0580c8a001003002c43c034009611500540100c903460070241032030040091603903141d40402842140c00b0200150301d180400514410002a000d644d0b9550b20005a1703030491240341d01c0329011914800018021840c0398050001c480f0015044411482d129a03840e03000e40c0703250740031101c045000034082c000503032481125405234140030003d0006441c004006002030340020060814903501200141a603615904060606035913040c549015080c1454010054040280301010b90720a0540017912540710300100c038420640c55460340c3c14401150f07604400d42c45c400c1d2a5074030107922481104845e0b2001002001050301c980c400050422040784e04408418001080c03207031524841c2c840454030a0380181059110540c032026502c0590002c80620400c51070072a800b05c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 474019613 1250 474018363 474018371
    0x19060b120a06120f03030b010527130513030224040f050c0604031406070c030207051302040f0b040602060108010204050d06020a02030c0f0714030601054c08010b091806040906 77
    0x18080b601010480713560003558180714944981e0010b40d070b1403050b1403480341108182c0c40000c078030074400040f4681400300104840c1114a40c050381c8400d0751010784020780107040294846040640400941034031031a41985111102e180d681e14440304103000b04054031a00c5000d10200400c0300038440c0300d418a100500898640342c5a08042c4880c4002ca50800c805100700000b01e0b68590003546e5500b0003a41c56801440d08034104414065941c104c10f5200e09143e07001d210200700c0751480200d9001416101c0c00f266296481c010300203140510603400300780396920400c000c0c007040d01ca40303480100c820380212000d40e42d009030000c1249944a0440500e4041c040e03982560140704c1c000c105c440840e0f4103044034256942212007016258002842215070200c460140381c8802403101861100a00c040745152019035042d01c8104107410706a40b01000411490028401068210714400d000d00300c410105030500b186d0704041500400000082503980e60703104005101c50380d4a03008502c580b03620080c144 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 474020863 1250 474019613 474019649
    0x408070605010b030109050f0f04120903060603080702041407020a020d020a030807420c020f0d12050f1303141e030a1b200c100819060b120a06 63
    0x40302913013003805140007050805001c14140310000c4a4680a441144000010307070300c85645852101c0010300e4150140400e1000001c086000c0348a10030065015190150380d0381d406204020032203021001840340040c1d402c0501c4001640040d00c0440103905952907214609680001040c01030f07c1d92006143e0100010504100101008002c01e940014103014006088643c41a00f8404404d01003841000100c50700c800304d680160042c051260349401624480c81e241425141402e01900d80600420011010586507038542c1c414290300030315503080da00082c01c10f19004030b12040b14a03005004c0020140070804180d00600403240503079001c03000c80306607050195111a00e50000c44007188440d142585c6500140d072000c2002c0c5054149996410005014440c2100716145009010b030241c4502c845c4100355440d014010648034110b0741700c5045603d01152003281180303503042c00199040c14030b0401c0003158034000548280984452409840345d40791940e240050030294000e411050b18400c0c19 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 474022113 1250 474020863 474020879
    0x30f050903130f140402090604030204141501020d0507201c02011101060506040b070c030609030507050c0307030804140d060216020a141c050a05060709080c0109030b0708040807060501 81
    0x1410540c100205030314070169907101843d001d07100c603c41d0013818a121030107082076141960050406c0c58004002c075042c01e442c0c4d0046000c07200481039040d607401245051001080a2000c001c4480708240b0003020306041c0e60f0b074018914012984010000c1c80c8103032405100c071103480b07100d803000701c40a401094002a01c04802900321066001a4046264003042111400341806240300f030b5400604450725080c580b8408008940c82980d0556420020740c030048002841030003000d20f6140250360781c645031070080c02d20343e0510103501c900c04c1c07180d80f18203420400101e015007910b0813600a20104c40b13444044602080da0604201e4000386202c0c0700040c58056203000d01c401040b001d0080e102e034004c10341c59018044400b14045012540a00000e2094084c001c4800307400c050507200d02c09540c2020400d0f594a40b40100588515020a03c103200501010b982000502c51003002440c0103504a0f10315100c1d02c00c02d98003e46180d04000e0341c4d00024003445082821103203c070360b101108000c1e6603581e00c45c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 474023363 1250 474022113 474022117
    0x611030a06061704020f1f03060f06110a12020a020a0f0e010803250305160501050105010210020a09050d080c03040905070905040209060a1d03070603020912030c07060f030f050903 79
    0x580040e1614224020034028440d00d441500c1034104200211561682d400700030320000c0701c0507150350200c910003e801d108003019511408800c0c25403030115503542021420549010507800c10020082110390032130b281100011902400d0750480c008180507a4424412410030700b00d5a00a50882c260400020300c200c0c540c8822800c45500401e455000d036260301302c2545078410280c01c2c08031022404506030031101c0b0401f41800c003d2080c20304600c1c110800301c96070541e01ca81e52040d50542d541c3c10041101c0d50b01444040150580c401e4110300c2e21400e6030028140c00e68038010341307000d0098006164200420a0101c03500302c03134aa800c0701e403100c0da507404210103003600706c4501001699800c0300140790306190003603030460340c80140754504040d00c84004903040385100d681450f1502c0503801d205200e4909000c2280a84140d42e80580d690044100b80301e00107400c03140300101a40104050200c00c030002c5486801d4644501e4030445161611108034054407100c9030080b903442c503200034415007440002c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 474024613 1250 474023363 474023371
    0x905030d020307171306051b160c210b0709090501080c030d0906140306131b03110702010512071404080a1a010803091c0203031b0c1e1201060e0f0609010f031e030507061103 76
    0x1201c40c0c101d500c4144042680d82f5682c141c0540f0302030004041d0004105440d5540c1c45038083c50600b584580c0c420041040d07c0c02a8001c10203074011071103e03e07080c01d050054107124046418400240c0c1d00c0d103070000300388485424002d2040d48011000c500140d64a00c81080e451107451014404e00004100861001c1000c0c0d10000c040303440c112a2141d0142c840d403e60300001d8050712180c2c200001410800101c5400030001400c100903280101c6032f02e1048d1014101070106040203002c85241858804c0d40c8106147c0300d8a00c54030800c004001042c1c000041390700c1880c050f0b49091b400c040c0940300c8070054244010095050001054180a680384100059006100d0b01c08803a00d4640400601482a00118080c03488c00c140d00004089030070b19660440d109a5054000540b1982d100144426810f065400d20722145004043c00f855103006404140500003001c44908820324582e6400020448880c4414080301302d04441c1c03091600030000e40d0b080301d0b0842c00074040a61035210b00121940112 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 474025863 1250 474024613 474024623
    0x212010b13081b04020705010917310302011b060905280309140315012d080c0d0606031a01090e0a050703150905030d020307171306051b16 61
    0x1c40005040b41d00000c150000c04030009015409541060600002e980041d101f03541c2c664841c0040c00001c0c019907000100000c0d06e1180e00c0e154440000e02101c3d4001e1801303440300e01181c002680da90152400502c0c001c80340d0900f4a007500040082c4000b018040004010301658a061502ca00f407040200301400d4000d0888001c0101c421240507445010400d80006000a61890000d0000a10750b903200c2000f0a001400c44984848001d03100702000c40036041000303c0400789690314002701e01c1e07808100c1403440c807510403401c043c1040b80203640c8103403809850703120314804420744091210550118014680124035020352520080c075000c041c401c03e06c161003080e441c08046140c10000441d000308140d5120024241051841d00e402c009400c51014000c0119600c07102c0710002141040200150005c40d100035031039162424001e40f242c4148048007680b0f41200c020091003100c001c02c810a1581e00a40010b09030b140c034141501d8045d07104030042031808000900d0f003420400703807074210320540c824 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 474027113 1250 474025863 474025897
    0xb070507050118180b0a1503090506060102073006020f0a0801140a050d050f010e1b04020a210b0306010807180e07050108041e1109070e0a0501120212010b 68
    0x98602440c80c20b074144641c4c0b451401007000514014840c2d001108402c0c2d0040c40f0385104c030380b608502c800413018281c80d500400e64072641c1804102040c0310f02640400c003400900340e45490000d010030300c0020f24041050103101214054084a5080341c21529590412021511900c1040b00c80754290302031a0900301048000000051025007203040980310720300908403000403440c040c2400080c246001044132640200240c000b41c89500b489a5203041301c40380f0003005080209440c003104a07200d140084d025600401041c91043d03000130b4482043c0300328020b41d1000484040c0c000b4000c000c5c1041050f8103006d840c0001404210006001080c0c070f6030604240001c4824902000c00c031944040d014440f40c1000b8810410b645c02098903661003401819400c00940040700c6c0810304110659046a480035161040062401d002424980c0004032303090514035009281c00003846e80c40c80c1d100f094100700d00f800e4480d03c007084075019101741303080c1c0c03a041440b50350311000240e8a070b0f007022800060101031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 474028363 1250 474027113 474027137
    0x120c05060a0e0606030c0604090e010906050901061d06030604030f050c01091515030f080310090207030201020d0f0515060a09031403040503011103040809010804080c0312091c1709070b0705070501 86
    0x105506c916000000e1503c2d14103407500703007007102402050f88580385556035810340c2c2020400c580900d903c07444100c40005011030508840c204c10ba43c061512042441c0c468040055035100010f40315005609070405900ca103201e0710742115648a0040345003050f50170012102c0810640800100d80c3d2a0211001e02036414810142d00704a4003521024160019000c40040030600a100039074000401010300c61180f522001454180e9002840850050790b0003c0c508000d84202d108028140030000014040c508022400413800b41d5540d207802d1055000064000d40503020f108501700842d0701c103411540b40382c3c045501c142c40380c001e845414025400d0020254144030101e0890713100d03541c44440d0604111000004491a8000410442e82003000704101500c0d1b01e030820180c00d100003a90b4103500985402c000460801005070100008081030030404904a034200c0450b5041181c122626009540c070301951074504192a4050780d0200c8000a40d10180f140c0465050b06a55082c1c90304180c501c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 474029613 1250 474028363 474028369
    0x30615070308010e0c070c0b030a021b0c0307050a0305150601210506150a0f050307020316060c031d0706110715080906100b0702040207110a0b0d0b030a0b04120c05060a0e0606 77
    0x6c00c4001c024150100010144a40843c290155421010045005080205101c11995518000c00b1042e14561104842042910301041600003800701a07616903d41e610390380d41d89a5403c10301241500d810007920000f440d60344107440240c0c01080704009808c45011500185004120981e5064000c5902c03240c0505080302480072101c2ea20495551410003018000303003100d0344e4202510840850208015551f80d061010a0244e042402600001000b208644010303003100c11000043c7c510b030314455000e8050000100340001100d4060501d001380040e0240b8240c142112504218004039554008000182c1c0c490351440c4205a04012074109031615120040a21407a100e480400001042440c0040c10075401070700c540780c032600d110001101c0a40004000000e960400c918028021440350006d0105002e2100c6588040c0c01401c10442242c440751114840140050700c0200420346411400e0f2180d075103035560783d400c01d003030b542d2604240000c40e024240c8002220524030414022880d140b03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 474030863 1250 474029613 474029617
    0x10f050601050316020309063606091012050906010303080a0b1e130e060604110f030703020f040e01090b010f02011e0c11071214060417030615070308010e0c 69
    0x1050b140d2600755034503040d100f00b900c08142030540860100744414452919540e020380006c0c590441c7d200c0c1488030344041150510301080c00c4025050b403030200401183c81d02c80441d4006801038402559110b00001d00340c403107400b40c1001d4202c4e5482c0c0810882c0072f00b03011911310f060345e1190ba5402115150041c5910554110f8401c03207074080892600300174480505156640210000f401140c4924160500c1d20100d5400440302e0140c0c2c3c0014042140e00d151074490a001e28001140e2103091205140c01c40429010042c213034000d1590000301041520900300680d0000c2001031201c58041d0313111103d40e0050410910458081a1031070b6070000307014018003482d405852f00d4010551014140c0c1854030217010800c0401c414000d281984c10b11900c070a101c02d80c00f800701c2502d8190090304501c0c080400e00308d0b840410450f6000542488005035400100d401e43c1c0c840031441701e480ea200c4500044c03600801c85400d000c442000200d01c1d0030150440080350407100c0d03241180c3e400340e0310005075481c18 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 474032113 1250 474030863 474030871
    0xa060e060702271f050918010905011a0d0305030f0702070b040b2805070f11040c051c0506030712060f020406081b0309100f0b0a03030810080109120503151c0203010f05 74
    0x40b1311210060005003031810038070f036200751480c19010301d9a0301a00701d5421540f16000541d20750351140d074030580713645902c16080600031055441111690040c0c50040c042d0102800c00c0c503044000a001c2009a031003008981c01600381c0031005a9542e81d0b488440000b0b610113424540140151090b4003041c4003210f0b1f040c100c0f0a001d845880c544185507440744452100341e003044a99413a44d01d0080c24580f103c0c440c046031310800b5150580e45280034611014403030100a0142c0c1414285402c0080300e131804942030049a4035643d0750120401c0c03034503105d00680f00f03900c03100414601c08140090301a9010030824001d07444d10380314030350f070781c400e0480d0035000e1200f00c030340c541c0d41d0b40000d032020807400b00d542c4141d1217410b480d98001001c10102c0700250040c0314540c0144c000800703020034062000081c1f14080f00400c0104002c1103c40e4080d510906040a041d08200c00e1180100006200607000c40c20341900c0070000b00310082056540d031841d41d0030000d481080e4042c3d80303810145034003540284600c0e802 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 474033363 1250 474032113 474032161
    0x703090803070e1305010906090e01090f02061e0a08010611061b0f1b06090f01050112350a0e0a03171b010e010204090b09060a060e06070227 62
    0x516030b80c80c1810350390040c1c0e06015940010030108014881302c5184256406000140f8011505501d40300903030050b5024907a5441090349072500f203000203910b03c0c0d454031070703070782e055070207603102d1143d1800c800c1c00c0030344003410000300440050785071884d980c00740c0c445040c0c1d8011b44070300380c0c03a00440c3c5503241d0300c450807201e0742c1225084044a11480d81024046c20a00008000f0b55140c80249100c4038081d0800c0d4000d05401c1d802001407046981080c0204241a02040000c00c03e641c90a84508600020590050140d501840401068070702c001040424041403800105800003010403282007581320b40440740000b603040d041c01005192008080040b079400001207252041c0714451002c86a00011144860403441400d41c0c0320b824082c0110101d0a980000050301d0380c0c50800c218040e150300b00c21580c4900c0b804402c006c28de59030a03254900b540c000380f8200d140c00c0b40603000300b61f0910407120040c0d8440741038042007042c603001d2504c02000e030038641c850380407903100c400f000043e80c8041200c0d964 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 474034613 1250 474033363 474033367
    0x1403040320030d060e06010806032b05041706040c090e0601050411090316090b04020a02061f17030d0e0304050a1505040509011202090105030f0706112b0807030908 72
    0x4411801095007407286807194080d28603140310941e10400b100c580da0b00601c3c2481c00641000307110341e00070400d5a8401800d5020f8191565405e001520081003405010541194210000251480f4000795005030104440a805a81d0030845090780c03680c0c01c6404840050310103401041a00f00350045a000c00f2070031004007002d03400c10741004050528030102c00480001031090403140d07941000b440341090011900da80c402400d0900d604c0640301b2101c40d56000d0b5004109403003049a000030559400300d0707040f0304040230340c080150503100d83d07076180d104001a4034406c1000303204900202c014000c2d00c16414080010090341009581c40303001c0e51040d658401c400b404108404081100b04070003041881ca4014941500c0d032001446118080e00004d2105825200300021401c050042c18050002200284a241c00c0c4600036a42c500d1a40a41010000044001da04000b0104898104ca0300d000c0c415060031002010881094a082403a00d80010a05408140300b80d01a21404410640200c6054 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 474035863 1250 474034613 474034637
    0x2a050d0e031203131b150906120509010608010c051812060c030403020f0303010b09240405060f0c0d03020909010b09090705090d05010606120f021215060708031614030403 75
    0x42d07940c01c02410300303022060101001d400a0300c030103024002c2c200090440f642c510305101c61244038244048850041c0846070405001d515000251000010843c020109599965103500e074090520f540c0184003540c00c0c007210460082d040005000c0032032441000c1c50503a5002c0c0c5c1000140725614221120b5500040f000c00c1400f1100c50045a0050090044036594400002420716661090b84580c000860100320074480c0d140144103441488428140c14030022012201e9800c00d101d0780c4111441100300081b0880c1804c0c0303034400c3d50800d00314030f070130740f04c02000300790029019601c070800716481003031a40000f203407201e50b1505586c4980c8001e030500d07680750f030740381000c2d60f0340e6105502d00d9a2040c080840301c0000341c424050b100150003240d0354036048410001c001c0d002c1d10042d000400c0018018443c6822900700c90301c89a5004560600340d8844c000c038280400c1c014030800b080504035000000401a00c0d1510f42d0306500f81d610f1542e075800c000c83e05060b0307001040c0405d8900900198041d820740c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 474037113 1250 474035863 474035893
    0x1050c1002211e0c041d040606082a12120403060c08040f030e040b09040c06020f1b0d0611070803060a0e460b0f03010c0804080a2a050d0e03 62
    0x10075070104844102c64900764451806c1c00705050200e00e8101c1c9540030108100400c0781e94000c910041c45203100030038030403202001180d80c036600c420218000e250540610011640d80d900c241c00341100102c2a075800f59006a2441e8070f0368040e000641e4100e0410340a000303c28400c0c1e800d240f10755000703200603298070481c0d0b030225460001114940e074441d4580710206a241c0c0d91440b600e005a111f8040090a50314103034010341002500301d24508160400032005010882800110340500c6040715840202081e42ca030280040c080c034480c0260312070010501e8400c0050302c000841c0030b0070003103405420f0740d90b031800c0721000c24038100c0300c110780003920a0b00200c41348140b8400600809481c40038000b1041c40800300d00c00801501c0140318880e80316401420300381001542a5005502039000b8081214001c6001d4070104003c0e00080510714002020080148101081e600c0d40c1c1d486200356494511002100d560a070390800d0a8815002c1c50403401141ea0044004008031703600030700509480d010300050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 474038363 1250 474037113 474037171
    0x5060f010c0c14270a060603060506040501030504150504080c1c2f0f1501140a21050327010801030c170307020402160b07050319090201050c100221 65
    0x10150704050300001c000010210090002c000075007541a6601354900311036440b041c1c80c1c150788088249442c00c4404d02054450701c003101e00362071007802c0110366922035140000b1007900c0907214101d401c0c603140c1400100b00f1410014042d40b103641080f250756220030f415103550403485100350008180d05044d202900306c6c0f032a10805840305022071909100c0c402003812424180c1e211072030280798002171130b0f40c0711241a000c0345501400b40c0724450780d10f44000c0e40c04981007941c18041d060484c5100800d4908807401040c40389041075015080e20b4483d0b040105412603000001040d0f8050410034261080c03951088100134100ca4024541e40a1203140555688840c0400008080d060104000f11009626203000401c0c0d40f101122040524043d141049080c0000141c00402000000c000384140d12400b07004009022100c19400200942a480107803403900c96818020814005c0c1c18000240403902c0d03011380b41454408000c4c01b00e100046031901d160070300032988035281c01d82d04103000001d00b000f008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 474039613 1250 474038363 474038399
    0x10501030c0c1203021903110307050c2401181e1806060311032503110a030b0f010810200306010504081209031504020f0d05120d05060f010c0c 63
    0x600044000b2140c541c2c8243e21600c4201c280400d80000b4010307030842102d203000214040c40c1c0303001c016203448100562058130016054104001c0302046000c5800f00a2107030140c0403807d0340f2a545144111000312000ca0000d01c07800715100c1500300c104007441058001c1c400c2e1004c01040100030904158120001400300c410f1282c4040b920814910010303045108131070186004001ca0140b8541034420540740420206c2c038285c0b0a0070301c1210300c4401908200413029254030040d030390805424407010500740310b100e51018110312501024481d1801401e4036150503603250000b501c0710f008540d445041581e80d06084200c0d401c1c070465002449103024800755800444c1494002c0c6056079441019250444454001d00051000141c0840910f020004211403550b90a018656481c0940015017020b01c500e00407070040084030207041c10000d0600000082142c8020002d80390014210307400001d0008998040c098840b04120b0201d0b5030150040b103640d940d00020340b0101c2410186400c4411104407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 474040863 1250 474039613 474039617
    0x50603060d15020f0c06010503070605070b09120304140d110318040608120301080c1906031a0a060c030e0d0b160315060f2303070c11192c010501030c 66
    0x706242c001508180014559510444e030082c2c1c680b030030042d00c0d130f05005041c0c0c0824401d9110140400805805c1b4058510540d000751091901d03544441080c0d00b000909840040c1c80d181c00030810042220b0f00708071100c0d80841e24220341014071060410b076248401620148296841400441464510b50304803218100010b4001300b510f036a00c44840d072038422a4a460009c41c00c1c040014040c4103000c00480092000c2140c507184948603000c1524041141d5008100c1059155481c010000d0242800550a900e0107000c24003181d03680d610040030804640021400181e8038507582c0010300d000d240100c880c580040303200d106900c480011443d50b070001c6903c4006e05484941312134503005000d100c01c1c0107120325215410480d01a4a004041c4100b800184c00d00e00b050041d841802d482080c1941d50100c90750418114440c21401c08001440001c0d82c1135511a840b0864800d03001c501042c0c4400322184505201e806000d10f81032644090300c0500d00010301702039000100500e6109400c5121014114 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 474042113 1250 474040863 474040883
    0x711060c0d0b0a030503121b0423090114030d02120a08220308060a1508070302180301110d180f170712020703030908010213301208010f050603060d 65
    0x304010950b0000f49130b009607400c0c0c1021545030380c4540c07940041a4000c01d6100e07003c168509003401c0000600031400703524001a9280c81c5c100380600d801c0075004030a080204a0102503030341d03194a6070341c08040070100e0301074010311688401c103600000e6a00c004888a03030a0a042800d00c40d0102c0c1c00d8900107105880000d540007140e03001c01c14a41604181900a540f244103070720344102400b00408280d804844020f562112254003554062425070f04000301e482e015035190b225080d87c0504264207225594194a04140125041c00070002403002c2038400d0810b005e2810300620400f40840c00803c09040e140e42464440000340d030004948041c5900040da66080c07000980700d981031042c19000c00741c00f6030302c10f41c0284103240e0040f010b1402411240b0003076203046d080032440b02c21200c00d07108107429061011101d0b1603042c6a0041100d003c070100c02d28001e41c0840741406110b200d4a9001000401c5041d400031982c1360021507010152400030b03000f0352454403401c09010505401c1842907445005d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 474043363 1250 474042113 474042131
    0x807020613170d02010b1210151a04050f0409020306070503040f0c1508010f081b030a08130f0f03020108070507020a23031002160312020d020d0509060711060c0d 71
    0x1403102290040101c4a008141e04a0b43d0600a4210348907070303090a02c00d14981d5181d011801c4000340007824444501c00100750000d070b03a1851413001d03045030050080f906034841808080d041c02006030048410860b03225012060400c140300031905280c00c003035019001000000d1001d80030382c00564200d8480c07002c2c401001e2040c2c4a100803101d450b009a0100300c20000703922040d99218030726902402d0801c40c49070601e40f511002c250340b4100403000001c000c03080d101140031030340d040c44203500c01d58024800907a1080d1500d01390709414028000d42d001500a0040403441c101021501000d581d411303160340c901a00c3c0c500059400d0340040c007040381d000c0011100420345011842c0d52600151107009961548540c003810141007000803028092510301c140800c1c0034040427030209020554250520340500d02b040301c0c00c138000e403003180010340c0d109000090760b40401c801d81d1300c014892020b41d4151000390b00c460208481c5084e801d00642032a52000d00858038000b195001460011481500003400583c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 474044613 1250 474043363 474043379
    0xc050702150d021b0c19051c05070920040f03030e040e0a120215042303130b041508060f040218090c0703030605011b0609111c110a030807020613 64
    0x40640d403e006074003960080200aa44d04100c007082840085960f01003c203200180007080303201c503104281c40380c040440140c186051000c4441c00c5240c000003690f0070561900c00c41c030f001e41448400d590308001d107a4005031201e900c04040c1c405440710403007040b08180c9140c600303e901d41102d0107129071090750b4117074a08041c1000c00840d0380040c8170365256840c8a21881d0060300f4000034140c0d8644240a4800304000106600e0322059400018403c4031004040c20703143e9451805444000101160381000226158100c2c0c4054011a00c0e050540800e06103200e41c122044401034528a0700581360403500a12450f103900034040e1005445254004d600c041710000e007c1c543d041d10f41c0e20040704006058011305a0500456018010a00f0a4151010403d0090b8a4804007540c0582099030f07a13408003041056800b502055248000d041a11015950000c403d04604120048418045003034003101740c0d00f0007000c0c400890b90003010381e600b0542140c0030b001441c6d22000b50300c414010700c0346000c00c2d40e03070b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 474045863 1250 474044613 474044617
    0x6121b020c040c090e012102060a0c0b0a02070503090d062d06050a0e0a11300109050c0d090804030512121015030207060608030307021506040c050702150d02 69
    0x1120a90003010003626040c18401210f45480d0300e50204254448207004010002e0180303411201c1840c40301140d584160026550f6801c6d090b00258000d10009d2540344095001d001d00c000030740a03208074002da441c0d14410008038800c40f4001047d5400502441e84c103450501813040c4564041c40c808103001104030500701841c840300e59000481c58440c140d144d284000d902c2210b000d49410303134410300c0d03c9041403491000010005c050488490300c82d410110140ca0041c26148255503880701c411031f008030704030303a8142000122141927040b01700390000a07048403a070050f00d01602403405400d143c542c041d4078000141040c0d03541612b240204000000009804210700e443d600440a00141c480f00b6407613000b43d080c00003800d50079042c0c402d80c82c00d10501c03d440203c2294407105040040e5240c41900d0311a0242c00c01c0d0307116446900000c020006040c1d0003060206041d0114010640540e0710130302048111001c0305090000213200740f10810050520400c0c00703541d04044449a820000c071041c40005030303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 474047113 1250 474045863 474045911
    0x4090f0219080c030304030308040f030507020a1701140f1f030b0702010b1908060114130e0309030d1805060a110601120209090625121401030c06090305070612 70
    0x684041c460070080e100003840f500c016004110099031a140c5142c80c0149080d038041c0024210b19408140481094001d604071060194003900c001082541c0c0c601d2008501804021034940394200102c018500010b10f0440340700340c1c502074811089803901e49400d011500ea07281000540d0107207003c040702082e880a05503104624a03400450348440d12810b11041d121040341c03110707110180e5030003840801d07004180305e8103491a50200202078030004c07000030501c90f410720440f19621710b00310021071001004001841a45802d80880b0070080c6180c0044036000e44c0d60303a51021003011280d0502091801100400880600b07180402c00e55100204240c1888402e034888034401401c03e040c0c1d01142045015039512071030100207000c81c1e1410a080c0f14000241c15106144414130b4108110301c540903006049802c0f0480c07600300318606500c608042100c000b03010a8a181304001000542d0a20031407041054a900001a00d5030610b004025105c601990300c46120503a01c9000010145c4401c440e62100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 474048363 1250 474047113 474047149
    0x20060721050f041101050304051b011e02010917040806160e100c03170c03070c020307080318241903091e0c0b03150909030f041503230604090f02 64
    0x10b03030416180840b03806290b016001c0c103001c001d1007008080388000c02d044001c0d0202074410480d005103840100c4400c62a403105c2d2020b29a90781980446650541c0300002062003515030079074000c044115401c15000d54440c07141030360301250001e10840302904c1c0780c0c030b003a0451b814060b40180e86200080c0401180242103400101518110401c0c1540606407072060441402c20074003e0400c6904034200c1d1000402680c14480c0f8207580d001192810001c00300100300080030780340c455980c101042e14401210f40711034420100f11100c1c84800136160b1900003000510300009280c5101c0200c071070f8188801d0744150044c1503035940c03820007180d001c0802602e85400d0741c8035120f0140e802d10300202105115040750701c01d4501030080004208101c406618071840880341080c2c0c591714034330900c1c598842c1d0f941032812000007150000780209221304142004820392002c0c014a607807040d44032064407030a08607800707080c1c06101240c00c03030a0640c401071401e802401481c481c6a410b402090300c1543c411030f1504 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 474049613 1250 474048363 474048391
    0x807080910021506090105090606132711040b072901030b18060103050606060d060f0f030510021804091a0f160903080a03020306030307150504032006072105 69
    0xc5002c981c0c1d0009500000440e417003117455050401091100350024405030007006c000540185100340000c01a0040c014085c00003001a0380c50711800040550014040c8203604080d002c1604848120071344040d1808041c0d002e0404805844824051044400c040c07040b5110560071250005440e03a100c0c080c40c041d820804d503600f0070060b081d41c0815038200d103081a0b003000f001400001d00214035113070030038000c54029407141d00c102d0041300105105d9100c0410b80d542c80c0c02c0020108a580341e0841120301171010b0320003600b03622195100740e100b0640d071a0040c4410045c100254941540440100d50007003a10280d50030032070988140e800070684c1d1300d80741110720004102c40e41160b00710308003004482d031034220000d5146995200c110301031444010241900800041c045440400644200c00d40001c503e081440d45204008024002504c1c1030300083d41ca034001f44803e0300d0708a85094000224030040070541c0d0782840440e521005c4e0700524200d5031110b134104420050030b004140c0102c0188003410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 474050863 1250 474049613 474049633
    0x4080c0f12061509090a02010c0b06012d081018020d0605100305040b1605070602030402120601090203010306050a0c1b02040204050a0305011b020a0b01170319020c101b080708091002 80
    0x5108000c104190b61350286e203061005076809052800701a61104c070001c582c0d02d0359801600d1142c0d00401038441e8a08508000a40340b0b0401980301c00c1041c6501c034100180c54402c2c194440d050240500c03030407036a0715074081d464944154003c203000104088005901c68030b6600180c4008107020034000001d441c0d20030700c001d00c04030030200ca800401c45901106007100500300a8441d0090890150841d07502000040c10341d2100c2e50307220707500320b248401d84195684806088000750401c1c0001c0c0c61403441e0200050104d06c0030b01c00d40c0714007140c5485141424104898080c071800880b6822a0495002d200006180e02d8409011000d58400e20012403801d84500c1c407840c010b140c0c40400c1d800c44d030100303001d078001c20f4204100c5130540304002c0c40301f00c00940400140346580700c0c22400c1c02c180400e01040d502e0296010551558442003200e0203c0c003200741c5101166032071000c41d42840108084408103000503c03041c020403605110325885403d22144500240c09001903070384440160300b01101c52 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 474052113 1250 474050863 474050869
    0xa021c0506100e0a030201140903010c0206090d0c0b04021908100e010f11120901091203020405030120220815040512030f0408030a0f06240504080c0f120615 69
    0x903046154003071410200c0f098421001071211242880f000c0c1c140f01e40e00b5241040318102100301d0300900c001800900c58020300711002982e45030110f90300600340c050310120108641c0300b04100d503155a0801d08000c11500d4907003c115003813921b9000c0340c926285100002400e038005015449a400e8030744c0d0002001d83c03c00303c0d2542501c910303043c9060007600d400c07020a9035060300c03801d640301c03044413021154540d55661003150061107151400707000340c00ca4007601180275515030000c04c1502e009500901840c44034004026001464640140214a05000210420400740020702441240c0310660342150b6840030450305081c8034000308015281003804010038400108888031107034400403016465850419181c151122025000030041c6d400080424008081e0f5081040071002c54401041034660f28030601c0ca1100d0304001d1a0741300700703805265140d042d0207942900c0464210001802d044138204040042000380010800c0d84524104104004800108100c6202e000b010307049200baa0500010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 474053363 1250 474052113 474052129
    0xd050106021f0b030a0f0201170a0501031106030415020a0c0b090f1509030403030806040f1409010f0b06070f02010c1205030124050901211509050a0c170a021c0506 72
    0x104550080c203003800301983e0b4400092070311400760020081c400212403840100d60003d002c01d103000c41c425003402402507401d810350286040300c0c03040401781840324554040c8045400704032400b80c20f03000e100880c4050301d242a001440c00300c0652901e46031840301591120300801059415038803540c84003c0303000c40c0c0481000040c0c1009000100d076403040c03902c00e120641d00d100310700000f0204100040440d4090f15190824025840000c02c01d0010b90b02007046080d00100072120140b84c1c2d82070602c1288141030300c0c0320708000f00d40090602841d1004644a44400c2e03030880404a041090790800c14003c41d050842c4442d000640741c3c1c88a82d603515000e43d1130314001d20195140110094942039080e855004800c0303c2ca40d04081c01c0c00181e03030540130341c03501c00341080700036807800c560400c1140c064110000e4102820345015440800c01ea464890300c080444161040d280080f070391f51900c028440194244040d03001140541c0940303000310b10b1710b01c1c10301e00885050b010030b000d4035031050148924154407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 474054613 1250 474053363 474053413
    0xe0c0411130f032301020f0403030c032a110d080a09060201050c0301060c060c02070305011b2c01050c0a0f11030607021204120c0504060e0711030915030a020d05010602 74
    0xd81500c1036811900c44d01c1c2d111442c00c160790107042d00b1210084070440290107442000500c06032860300c0c0c9a6038200500b1840e01d903401100001c2d210900d4842407140800c00b440c03803802c420345107409410f0b0b95850352181d070341d610f072019070002c1c7d07614081002564a6000304107a0005949d005216032400c003029094610140c0ad08055010600040c0b00041c0c0c80b0f4181641c0d030b500f14401040c5000c096200303a00381480394002402e55400c2c803026404100e818804013028101681c6c43d61020114080d10031040b0300404e40307480c0d41d0052240b514080358410b1000d80408240c40341580c000e80c100340c0e5000da075400c4015044540c032561a900302464074040c409642d001c24103002921142400003045071303c5d803081c1d00900700031004a81d6802d0910480840c50740140c140500100b05480d00d503084030742c0c1799208032103040c001104401104072410002c4242c405030000a00031080c000580403103411103400060001d400035034207012f616100101802424000c0c540b60f0064000c040c0c04640001095200c88 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 474055863 1250 474054613 474054629
    0x11120907050328020a08030414040203060d12090e09070312030e060402102f16180504020f0409120e0609090412030207080310061d06030a0e0c041113 66
    0x410021030301d0205801d0920303541d801002c140f500f401c40d50b00c0140f002c00341e40650840410940071400c03c100000820546e0090703110302c1070143d001010081644000c44945801030142d0800f40c001a603510181c1071119010700700b503240c098580c00403d0803064105c80304041c40c0e00c240070030000d00c155084401c0300700100f0324091003022191200c4076584c50303000d44028014044c0c40d521f004014418010b0105030000340b8518540b00700310350002400700b092241c3c04101e50150344002c00c1c1c2000c07100303105402c07035480c02d00600202040003922002481e00030000c0e138000c2c94140300071074540d03500d2040340303041d900c0b41103140303c100c802400060a03020140101e41c01114200018003282c0c0d90390940c0d5038450740c00b070440140c6040190040f006400b4400c40144209001310038803100030002d41d030b03002c2928203c1c0d40345200e940502d040441c08e68129402c203078001c401007020608400d0240c0040380b0988105044811036941c00740402c00310741c1002c80b098081c0d03c0100721001c2c4180080504001070203c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 474057113 1250 474055863 474055873
    0xb120309121c2d051b010e030d14070912060509011e15061409040b04090210090e07030c0e0112110c0114090102030c0415030f15090e12090d050102040504111209 71
    0x201d0050454417928820303840109400510401103402508034104541c0082c0640340c94003a030030401c0c070141c10103000c10300c00410090001171505100341071090442700b021209459055403074944800030f04001e441c045080d520344141503114283c107605107680b0182c075040040e080000704004a0b20340c102c2e40004003000202c4a681d071006801c10103650980404403000a80c1c500e884000400420322030a0003900000002d00100b001a044103c81d801c44a565030f00c2080c0740d441c500c048044030f403000c141e10301040460341001455403140301102c2240136541000150003000ca0b4081909802c813030154400d5a4590290303225200300c500003e508064580c0003503081d41425658500a4020b50060243d00ca82c140102400030b4400d400141401440000801204016480b140184c2d4945d000d000202400d0100c5154001c500092400140c96200040c80c14504150100203030302c03880420a40c3c007507409010100307850b9218841d0540f00c144a405141d034841e000001980030364401442d0118507044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 474058363 1250 474057113 474057197
    0x3200f030309010f030213031a010b070503040314030c150108010c1d1c060f02070209060f0a060e061b0d02210304030804020d0b070c03030b120309121c 67
    0x4103460303142a0900b85440354842141c0b0442c004e0069202403547c081ca0804000140000010f00800f22020800c910040381c1c0c8800310500144a1020000c0140e4410801000071448401c520521500c118055a20302001c3c070110a150000c03000c124200805094010080c2502c00d00c55075030611081c0c00d0801c4200b2030072000c0c2030392071012014030740540400c3e10000e0074841d103403d0502c009544604100005140200031000a400c1140d040b07005290707200200300e42d40b0b080103203111640d400900f00c09142c1d0409400b00e802c81c5002070000c0d0000320500ca0301481d545144480068000404010075400f0502c450080c40e01002011001c0f003003840804160310208030360b003103d034400d406041c00e000e0780c1c40743d2003c50070003500d030a0050040f844a4050054107a40074504880190003030341c0c20712003101c110042000f060030031201c03110503500030021204070341420503103038a44c10106015940c0221400e07a4035004081c44104071000038a80c1c150082c401c24240c40c0261002c00c0041c0e6520803404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 474059613 1250 474058363 474058369
    0x60f030d08163506010305040203030a030902040e015712020f031801020301060c0b0402060405030109081308070b0a11071509030c05240c07050a03200f 67
    0x4042c05000c590340c69041c075100c1c030502810802c04220480501c1d0320380a04030308900940040b1800c2000800d04448002ca4084d40c403d002c4c45d400340e50001d0180d440d20b900e54000b50010f0020a2041b070f00551103070880c00f030f9070f80288034002940750403c00b0004400c2091000c600d190090701c00c5040f80036182c0d00e03a54564000e0044043c848402c0a4101c1c02a0082141c10703114281c090304442001070001603145540d250800c00395010f0442081c46441e4000005a81800d030300090155000041107542c084001c5540301c910700f5001070010340f200385099107038000309003036800b4a94103541c09280000c0031004c0800510002c00200020000b40254030300f0008207050f10f00c1400004810031038081c0400c152040184882d100400d040e040000c080581150042d0a8011034882039880100105001800342800b400f10380d0180b400103840383d0310440005400b081604504100d04403881607900c003141e5901c5003c14400514000ca40141103c90618800c0c070030100110303003250180c0c0c82c81c1e98424803a2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 474060863 1250 474059613 474059627
    0x1090f02090408040306020f09120d05030c090a090f090203241303020f0d02070f0608090703141002030106022d06071d03010501120b010f06120203040201200105060f030d 75
    0x240d048410554640300c03810029400c0c000d030307003010300050b07c0064045055811704000703041c1c080003a19440006407100b8a62034403004d2038055407001c1a010070001d88900031150040030320010080405203810b403034444260485080880c1800d0b034907502c04409040d1301c0c04104030140c00341070440000e002d000514000030030820280003150210241500c141c02c2600900040008504039001c9a40508600400075602d074003510940c1c0b4118000c44011030454070640180e0311584c03000009040c070514641d00c43c20205000c03108030f9803c0c062190981130102080c0000d500074500b59006000d0314115040d03185d50703086281d100e0181030300c000c0c1c004044000041512580260a400c114241d050300d0122070083d03400b05000e00c2d0345546003500119030b05080a0810303c6150261344070071036236a298104407006001034000c03640882c4854910401490080d001580e02610600d4403d0385d00e10072091041c1051b042c02e443c660035035110020080c09042c075800003403201c0030850003081010140c00020b0103903 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 474062113 1250 474060863 474060893
    0x24030303020d021b060402090604021206060901090305070b03060f090601120b12070803040305071e031104020f07140609070b0a032708040905010602070f050d051f0902120109 77
    0x10540214510b0070700a02a4103503024000c4c0501c1002d50b042c0c880030719a4444004076000c0744900c0010000c621a804e00c1d20998002d803110f58100039013a1031700b604000c0b03640c000c000c408d8100804a02d0200c00602e051050b0f5000700750a00141e600ca040020800c0100140000c0043c0105000801c000103a0381c4081c1d00070420921100020300c40080201044003040c1c0d00303490a00c14440d200b00001c052000200070000c03a405a4140c074940c41d12041042c2da01541009c00c0c4686a01038007007880403403124120300012140003800140303060048500140b07250032040c003d60f40c1c8000441000d0303890030107100256106921030b000d000110305184080c0342e18022140021308140d0740306842102140f28444140c0200484c400c6140007174200c1c54403010f20707802030069103921340c106000040e43e140006480419100640041c01c540390401007407004c01d08201d0801d84030342c45042403003045181d00144032520385080c60001300d1203d5080c010304c041020b60004060083e03140090304804698a0810041300c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 474063363 1250 474062113 474062117
    0x2010522080904060807060c02180f1906031a01090e010606020d201c18030b0a020c0312090d031a0604090915050c04061106091203132103240303 64
    0x26810b5210105004100c2d0b50400340c65071058503008a940d41d008021150303124822110800d20f407000440d204000a02900c01105001c122004111102e15141907016030348108080000d4403641ca80702c907070003140c117003441213454561540144840500c3e4041c10141c04840720080c010a4900070000390b40340c52030000041000503600d0303d100203d80044261f40d0741981a401c440504104a002c102040035005100d408202e80754620140007120b00f48003030440ba0044202030b03150340d400c090300010f50b102c9098050907020400174007080e000380444007030041c0c40c648000c1c08801c40003000601268801c0400c0d1200c0516100101c155a84900440c3c007901c09201000c00c1f184881c4c9005004040703400181c151981c2440208605e804e00003029004850665039480e0b91701c8402c405054641c5402c2d10321741c41640040c2031002080f2448001103030414020002c00e01020340d2074940f4184001020404205040d005e00300d2103580c0c3e2b041c00f910302c10441c85c04a044505100c03030b03080d00d141c011a10004013 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 474064613 1250 474063363 474063367
    0x3050910020c0a06061401081e04081c0e060109050108011802100513170d0807020c0d260315010905060d090f02150a1d030a032a120201052208 63
    0xc0c00d002d081c401c041d2450751141c01800900c1c0c0742c5803c80f01c6d142100d000c0c940003640c40c80005210300e2010040d41c01c0031142586034032080c0c44544520240754424003061091010780000c21800d0326031480b542080c656090081c12040d41446001c2d010390364181c3c051070f202e80c109409881070044804188a00d50390481d0002850600160141c07042d0095401c0d24011040044000920306000084404003400c40000e50364110103505e02554a5401621030100503440106900a107082049a0070103241c008c0000010b1440d614040381c604800801d005e201c001ca011040c045c51115080000340e06c803000b420400b88050620000c5181e40c0202e83c80214000d484400700c6080c407141d481d41c6074501e600a46084052a0310025080d4035912203c0e038440010401100c01d06240703034504103200c0c2c14000501800c0c0e0100c490300c044506005440800906261280108500c810101d40d2500e00d507120304820100d8120100700642100c0b0010a0001d004a28061410101681040e030710042035101d41f0090b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 474065863 1250 474064613 474064627
    0x2916051801110115181113060e0d0b070f0219170d02042408090d121a030a0b06090c1306121b0503090c0609130c11010f06050f010305091002 62
    0x1809440b50000740c004c1c0382008038000ca180c5c509000c2e40401046030603010b00003185001780c846040d20858412207298503d032601449694443c1c1d60000c00410f00034140700e0020025103031403402440540316800422103100d819a80d550b0107202840300060700e52682070721003581c0d45401409031178902100b0f00100002556030403000030ba9040e00d002d0402c00045c1034100c210f12104171042e01103081d0035400310307104900180300c00b200001c521009a0702a99222072000b40c0344061305c080d00e080445240c120a000c2e403000b0094074100441c0094900951460065051041c14050f440d60701818510800804200044500240b030b1610b20484a541c580300c15000c2d407518007600180806064005803410403009800d40c5541300018600803100042074860300805c4004120003403051442d5580c1002d130f050305800c03114003141d03c14500070038107040c0203c02e25003599031103086448072121001070700c3e9285400e105d5400c0035800d036850303500203080800c82410452044c9545001410400c000c1a030009104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 474067113 1250 474065863 474065897
    0x20306060711120f031224242808070206071d0306040f03023009150d06031101030b01021c0e040f2702060706092916051801 55
    0x10100c0880c80c0f0050b10603000003040020b440354404040d852000c2d00010209007018074a10000005800743d024041c90704e014101808a282d080c120024a2070600b040312541500f0403c0050102d0040388000c850072180134501d00d40000342424100080000d05c008001016400080a60304a00030741002508541050210384c0411000090a50140a18002d00c000c200300580002103075440f940030b40300780d00302c004104610543c0d144454681860201645840c80e4501c00007040448000b4240402c60303d101080c2141c243e20902112010300d944074410001c0c02034903040d06440c0360091a040c0502100c0100003940c400d43c20f0035802032640d4400d1030000041c041c0c03402c000c00c101c01410034045011320044d440014030506c14031071030003941a00003951f4190780740d0a00c1c1c03603280e0041c00c03070341020740684485004100b00d01c811146001020189907c4018080c980104503680c1d03804011280b40c480303400c50348103000e00c900350184001405004210b1903400032011004c0307028a000721250f0301d0481c0c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 474068363 1250 474067113 474067129
    0x90e01060e011e0f0801020c01060503010c020309120313030507080609010227131b0207050a060507170408100e160e0a0b0f0607050a0b011205060703020901180b0406030f020306060711 81
    0x5074072004c001d400040d9000190040c000141c070410007042202e9464013407500703850030115198016041040600013510b81074000002e003105103421a42001500d20801c5409081d6400c00d0396140d02501c000c02183d01704008040d0300440310360084d400c105061040d64051141c1554660a502c030340d019604030b60f110b241fa03100c0311005159041c0304005000814010916281041c0ca005008205010609061a0171210100c846590315540380080c0f5441d2400516248191504008003c200000b0201000c0200340c00d0f41c41030400000304d0203c0402d840780340080c0804000343c0c01c03c007007a007006044034107280140d125044074004107400c1a00000690012405800c0c9a4800d40114503c0107101300041c1c1250701d244612014007803a600c500c07040c40101c1c8090b2000f040c9921140c0001e0240384290040d00282c2010b05000904d401d0072a2003c0010203180c1101c024040c0108080020a505018401c00d00307031150f000b103140d410003c010915510030414007416106004560018940f01d45c40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 474069613 1250 474068363 474068369
    0x40b0a030e030702090f06030d03060302180603120703030f050601030b18060402070f05010f050c1c1503021f02060a09020f240307050304021806092e0807090e01060e011e 75
    0x100e80c03481171506c540820b6440340c0554600340244100d84145601902174801c0c80196600101034110846c1500c07880401140c000384030680500846141d1021000a80040c0c0486807007600d012505a0702128444c0440b440240070504241c00c04103d103c907030300e0380c105c15510141604c0003800c16640c0e0b5004a0068421802e0090038400701a400005004040d03000b040e8911484078240701944070035803d0300c003038012120095222450746140b103207040c20907401b100208034210702d00681e040e07076900041c1c3e800361003e0902c021440b0401d200010380d0341c14800141e20650300c0c24100081d01452f00800c00b20782030344404038084d50054169048841803070014001c0c144048c42003036900d2400110090480e001650124062503810f10401d04038400c0520561203608041c00c03800842d5903403030a0380a40b102d80340d074444140c00804c280f848492582841c02014008000082c01d4082c5003954600849415000455090745000707c10b10080b1410000f0604503a800006203045101118002d44041c9141d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 474070863 1250 474069613 474069619
    0x1080403080a020c03310b19120504050c0f0a080a11190305030d14190203040f080a090315020a052a150703051005060405040f09140a120203040b0a030e030702 70
    0x110700c0c100742c0303400c002a0100900000d401c2500758506c92985000098550040c444c155009004140494070b006060203000445858500410700d00d04240c1021039805960607941078001d038071004000d044c80321480b81c1654003655130030f210510740001e154a900040e80018207421b04c108204003a82c0d116200e41d05038010035840100c0b410350342c0c51f14035629800281300292190400e02d0341d1030f2100340c4c204218422444c181084402d002c89020040094ac0300420884065104003038110114803d600542510490390b02c0f6962031a043d400c1c980b03080350421003600c1070640104022030310a03a004003501c580d088032a440d85a107050214200203030b03140d881c18560300c6200354400040e4484500307004600489a5880821558a071a404400c8008050281580100e0100410086403c2641c403d554182c0e21000010316868250384181104007118170305551607101c1d680070b4003480000c0b610307071501641c00e0000718682450081c1408160007003400900505694080301c1c40e0800b8184100d842c80c03075000b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 474072113 1250 474070863 474070867
    0xe0a1104021b160e0c030709050103020724020c070e0c070f020303070b04080405041a0922020409060501090b19060e060403050f0a0309081609020310121a1501080403080a020c03 78
    0x4203c0300a00b440c01ca20a8040b4000180d0201d145558600b0031a40114410340d50f41c10b2103400e00006601079407003c0c1086610b0012507983c200000d08110791b05000200b039400140c0e0f5500c400c15000e181c40c0f4150440c6d0070b00040202072100640b500c400311821260300040c1480c51004500009042d8014030f08007030420b0358404204020000c12000810a40d0000c0f1020030074030303003109044d1000d07904083e405504041034401080c0c0681c0d100017006c0c0501141c0400f06a410b185038081022f80c1d4021104882c0305446900601c2040d8042c003e82214900c280e400c0c40106002400440c8046810f1050f6414044410243c40068941c0300c203c501441d042011122400306540500360b440002601c01d90008002d540301080040b40070403910304820050744080c2c0d0b00b9007021a184004e61019050b1000c4c412403100c00500c841101079500b000d07600403140c241a200491040919501e00102a641161180a0003245070380e001242ca0f134209401d86001031460b5600c000c031000911400b07031002410700c40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 474073363 1250 474072113 474072133
    0x4020d050309060d020a020115050120031b061009110304060504051204030516080601230a081c170609130303090611040501140301060f0c0507090603060b040e0a1104021b 75
    0xd1707400034912400187e0080004401c841c18071142e2540a0040500007036006a840380344d0324400290380042c00024090740d20b0000c01000140c1110380440003606d103508980100b00a03c04421800c500405125600380a1012082c0c40040f2030705c401040105410796402c003003010300504012000010021050303a1b95601d4032424090755504d0b42c0d400d840440b04c0c0c480070100f00b0303081c0030411504072150920919003901c000141070004203018071445070001815030300007515400401c81540301c4113410009000744050358400810b04c00100242c0541c8020354030a0000503110050640e80c0801c030b0080c84504035005180840141c00700740e1028002038104945030340100b5501e0b004100f2514240c0b00d800c0403881c4460074280500023446103401042c0450849603100d8010303002c15003850f00c502c0c25a4030b1151100700740c408451158009a6400756903044120803410207200d0800403010000041c0121000c5640300d00765034040e0341d2030a0240390049940301007421140101c3da0700340591026603000c0c03c9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 474074613 1250 474073363 474073387
    0x1507050c18040501050a09020f042406050307110d0f050d0b040515010f090f0b0304020105040f080606010906170a1e23070c08031b040506070f03080a0c0804020d05030906 75
    0x40259002d0f5a103520381340205840300e00342d22500c80300d00d5000c0c000361781c1c0714440002c000060816503a615910761107003070011061100f2403908009042207460342d544038101414010241c0b12201d0a02d075441c5c0c4500300b0b0b813002680158507030403500700500c1c00c160307180b82c1781c91110050a003501d4081d8010381030078140004030368050404c0d1040e00080e6a55661405242d10480d0806003030b01c1001e000ca0721810b401d10200c035a100045038000d0042c103105103881d96072440d9409202c1d0a80c48086107801500034000e1a603800307400c00780107000500d0b02408840d4070300f610103d4540d0240011050690361030f101510b40c441150114446071460b20108003100310610055005030341c4c6d814054040342d40303c0c0003500c0c80e40280ca5540010350424141400c40e960b03801d00030040b0202e10090b5a12884c1800001844d507078040007400642c0c443d43c01d8044030b085529000d0a41c400c003030030201909040c43ca00c00021648650403561064048410504c03040983c2005401d502c01c0d00602030b00103c00140800e40d00d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 474075863 1250 474074613 474074659
    0x18060501030b06010903020901030803062206081204061e030e010e010b0f0a0803070b09070e04050d020f1b04020d0902040c1107051807050a14040914010806061507050c 74
    0x1c0e008016039001555000011158130090b0701000317500507040e400500202d09402c01950340030740082c0c440358000111000e030302c100351112451146069101c04040c80350960600c038a05a68204180c410709142c00d0035409445514000103070440e58141c54200403009119801000c00040030780001c01c003016008022074043c224072183d25014101c014116042030402444030411210345401840c1031808598a103440400013500303001c034510a4100c040341041c5101404c0d8000d81c4104000c0c510320b1410307107010b03017488000c01c071505090f00300c1544407081c0b446052050360f81c0f220407180165900d6220000341d00030b01c02c680c070294205151a0400030340a0308844c01c00d017203690002c00c4179602c55442042040d070402d00c17130064003c0c0040002090000303010b6000740c038810038541007040d00c1b84610400000703180c0140d4480c009550f114043c0320303000b4403e0b8a08902420550002d00401c9c907190000c1134440c0075210304004268400114482406802e00600b042c20720000d28100000c0c48600c1e11040300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 474077113 1250 474075863 474075869
    0x30c120203092b05041806080610060f0201091e050123092109011b060f02091002070e2a07050c0909010213030b070c0f060903022e0203070318060501 66
    0x1440e149024080040303c50092407440302036688051038642000b00407040715a44412403000103444140109001509000c118481c010301d405003e000ba01e880c00052518010390f00000c19a4075102c4880c01140045c0e91982e21480480d00b0361258000d03901c0c119004206d000303100885000000c22000e1078000080c4828062111141114840d18541c4d803000707140602181c06400c4500b00b040340c018954003031030b140c1565988042410701c40b00b1003904c3d0351055600c0101c07058507140c2d000440000525050314203a0328009184010502e450034104980302e0448090088000b154441128242d044100d4025141000d03291070415200c070500d190456075241101d1000c0c3c0314a0142c0009164a0014400e82e550002005d09201000f4610f441e0381480c6180980500d08000072040f6205c0862a440401180f85100d00000141d0a0b01420001e040030440c003841810f0700d280d0150041140d40c0c004048198182e5071600681d03980307843d10150024070265580410b40c91110b00d000c004d0000c6a40000e0407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 474078363 1250 474077113 474077143
    0x90209061002030a0804020604030204050702061f080a02091008070806090d1119051c0c0218041502210901020c07060504080706031104030813090609050402010c03030c12020309 78
    0x164a51400308010340a05905200050f0700a01c904151030b440741200304c0e001800a04114a016107907004a02901c0d0f04a40f0500560301c901d0521804200520442400e00c1b40d03a071301801c00741d007800c1c01903460b592040e9010b80f00d50403040128044000049081000700190b100300d8201035607a1142c80e1b1541c03000c44921310b441c016900d0402e601406071058555071500b10380034219001d01c1060b5864154008030040e54984145802c92107075550011207030052181c592070700142500244100a0803000554180141401600c148800140140c501e10035110394030a0140e112403c8008000a1258054a584803455580f042c031044c50700650041c8039018030b08013039412603911002c0594003880b03581b1a681203984645402c104540c403d6010150071620070041e0341c41d0680e00d458500780d80c0c000001030341003007405000801141503288204402050042c80c24441383c40d140c1c0001c0c1044180400160506850304004200284545040090380900329011910380c1080c5101c01da03100840600099 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 474079613 1250 474078363 474078379
    0x6121404030f0f0e310c02010f1104050a17120a1106100f1a16050f0d020d08010905071b0b07030b060306031002090a0b0d0203152d12060108010902 65
    0x102e0740b446002081d0741e103e000380c03060b10300f080810303d070300100303040e1121100244c9880540c009040c20301b805000d4580c080e0741c0c00490b6038010300302c4a100705d42c40b4050680d030840702008200b01d5600c0c1c0010303081c103c40c680c0c00402c0d030ba0b610541d116800d0601c0c90501003000c00c0001408070149410038040c402d10a01901254075540e5566069071042c0030768080e20360790001003c010051742154080d100e40c04c03000c0042c4d10b410320303800039241100884030317510480385a00003041690080c4030400103051106038a07c0180710b035030000c00c0043c051035018019094420b031170304006941540186031045072204280940480150b40d8145168400c0040c1c2c1c1c100c0010707040002c3d0401070b00d40b29007a41d0140c2001405051220078001d0070380001d6022540c007035000700900c5030005100c0c410074040d000480c45910302507034a240401088142c0800500ca280c40741c41c0020305082380c0380204c0b498442e60070301034038102e80c4507085070300045142194061204603842191b0012450344019000158814801d0720090 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 474080863 1250 474079613 474079637
    0x30503040314070b0a0209040b09010e04031707080601030b06043515130221010603060605330f0412210c0f021503041a0105030c030706121404030f 65
    0x32806100340d4034007800350304c07100c0003007908510320798024220351342c4c02400060011a10000304910810980c004025800c3c02003c0005143e0864100d040c10841000c801600b85020640134140b80d0b0043c1071141059510315400c03109855450031a4003401d92482423001000303142e0060301000500700030550b59007285640d102c0380c08034002910364518034280107050103555201e441030001001104103076031201042d101404410f02c03603000071294110041c004200030303040d410030b081070700c0c0f0560045024140d02d081d8441c410b80082200050313030400c030740902d1880d400c400010489019915945c041b900c00020001408400e4181c80030702140b0884608860b070007104c00064040b0300904414000c600b104d0b62000014650381d0000640c103200510070414100007034159a100e03007045500b124500141e04111b0a02c05000c1c0d407050040c40c04074003e1030310f00180000300e41c5a4a05100d00000d10500712009a0400c40301d8118468041215462040c0307498203050080c5220301fa00a4000413071041500b039 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 474082113 1250 474080863 474080897
    0x203010e160f09051201060306050c030403021b010509010507050c1e0a120f0209070309060c05090306100b0f09030a0807081207050403050c090c0c010c1817060109020c070803070305030403 83
    0x914440c04039885483e8000c2c54802848000c10991083c86500e550b40c12000c40000c80901c98140507524600e034035038480c60945001b9103080884014101984003244598000c1da91201c126141c4490138649070ba100c045614120346051000c2ea4125402100841641d248000303400220001d0314048820020702a9100c40682d10103180410260000346800541000750402440c426085000c174500010f40c007000ba00c550044900450205000840008100c04545005c00c4165040845c0740c2419400c186070a0341516548a1b100840c130140703201189080b495a0184030003141c1541000c142a520801490804410350060441058060400010903411807181c01a501a242d0040050101000750403c0104059004000c286640c00c20055110845000e00906000d00195100c0d01e951800700040031900c0c02054001e4007075110301e8400c0c07403981100007980a0440324014401643d5111101e0b44a0411916401042c0580f00c001848020181e0201c000e40c40b9070f000390748000b24003400701c0351 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 474083363 1250 474082113 474082127
    0x150301110f0403060e0a060c05091002010b2808030c0f12160605060f0402190909090309030b040203030714070501230d110d0608010f050601020303040308150a090203010e16 76
    0x3008845041c4403e1000521a900c044441c0d0105401c860100300c0035580c81098032030416800d03000a0000c21380d4202420608082c1140f00a28002400207940f40e0b0003154902c2295000748004040f14040d04100260000d42c0b0800341610348140d9503544034600780550f407020740c45003a14441c82044501c0c48141c0000301600d5040c00103000d104408034143d2034080103410050512030f40000180c41500e201c0e80c0720701c0101100340c5440f4008480c0046d0010181415406901500f025402c21803c00006580180b5030401e0725400910004641c0b100c0c00440c5c554050324100600d030042e160300383d00c00c807403000031400b0071580240e80340194001419070741d010b01c0d140c500c0e813070fa0b4800d02400041304000007a00310150300304100e0303007150074410f0321301c1c0d40015203802e984600b01c6a5950401188008080d020310f03036001ea000c0c0011840c60034540d41c014044040200754404004104203400442c0c2d950780807140c01030210910554995842c1d01c88001c031032400740c0710792030589610300100440e503010744e81d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 474084613 1250 474083363 474083377
    0x6030515040c021e070f1202040605030303070e1203040803030c1803032701020a0602040609091109030a021c0b071115011404020904090506040305040f08070f120f0b15030111 77
    0x10144c0120f8030015080481c0807441500141035024150011072402604102c000040000c28110205e03000c141c0103110844030b1542105010740c00820400a01a070402500640c00c503043d22402504d00c0c0079992503042d40242e811100b0349010000a01c4140032551010b400000611540c2d198600c640c03904241da20710030081c4840323501c0c054444460390191610815a40100180103580801c20540d4070001203038001e4025030013081c400801030061107102e00c2004031a0058200103481c100c05c000000e82d90b0351041100900c83c8601015800d070303400b40c9a01410f280f40d0b00c502004124104000080d1400140c0041e40000d40324a0448001c58519030910714103c0c3c1c02003051420710341d0f0590900010354001030400c3d401c280c84c0c000d41c400160003003140e94401c03802541c88a44850601034510000300c01a440003800368400e0409002e00071007910f45c1011100340742040041c1482c0f510b001c4e28039070812040545078001030300820204000090404407445411802040340c15000b100070540c0c3e002d040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 474085863 1250 474084613 474084617
    0x103051c0e040f0b18091002090d060c05040f030507171f200708090319110103180609050106060807030903080c030403031506020c010905041a040b0609060406030515040c 75
    0x80c1900d142c00e055111120200c00c0750780101c0e00501040105071440c03e0300c4801072035480307070108100044409003c1c1c00b5003170301140c501f07624040d100c5d400281043d0800401400d8181c0e01c045894802c0c0c080c104440007040318203981200c541d0341341826a04c902243c418000c42c480d40801403118102c003c80c160908034403200001c0d0011034040c2c0444004c1c0142c0082031100140c807014040601401009043d0151007503a00342c2d9a034410109050801009006980c511581c070000c8400148070510043d65025081c0b1f80001c44070f601000c94070003000c2d4280701519152501d21803409002041d0420740c240d034095100ca10041d182d074401201120100030000d00050310341000f141c0540c04000c011070300070f03000307103000704031204824806034030038140d41d2103d40580d000601d030440550f04915598001c01c0115810040da45803840101180b8403c1c26036544511b070b40303000b09241c0f9518401940c45207070f40170305040e8030b96488210103001484190350700005c52211a9152000e0300e05801400b891308225 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 474087113 1250 474085863 474085877
    0x40e01060c06150b0711042904060b030601090e060301060302040c0c0b010f0f06140f0301081b0907080601052206090e01051903030c15140403120c0f1d04050f0103051c 74
    0x1d44400606d9520500c0c01e960044e103400460641c680700c1141c802841c0c0c5010700560205800108100440300340d81d0107160000414001c200091b80c01411182c2210800c08100300d071552007800180c01000326400003580f00e0314100b0031030503040d842070080d0301180c45610090701590f214410354030316001a210b14030181c400d0400601c4414800d0f01e040400c00140c52807241401e105145490050300709804c4258268440c2241ca610100f00c3c03a11280c440e00e080c0d035022074506299000500d4a41c2c01010304c0d050100018120304180c002400c408241c00300d5606030300752103407030f07071401003102200b80701e000a010720280000c02c882c40d1170b0781c440990300c0c0007031800001d80340365540903a110010702d402980c0703c400c40c0200f603900e1100340c0602c5980b28a10b456a80c030030b01e024500903084070000c01c1d03514500c1d031500d013150100365006051491400280e007024407182c40c1c200c0404241c210003968664219052100b8420100007007040a03043e2441342d810380e94400080d41940f2a42c1c500500507100240035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 474088363 1250 474087113 474087127
    0x304110406081903030603020913021c48050f0111030d05040804080604080a0809030c280813080c0102030c07092a08040209060a0513020c0102040e01060c06150b 71
    0x5050303402003d80c07081c00c011606a40e81d800203500790500300e0703030110070705556840e160452a0800703404161543c604c4141582c040903072100c0c641c42e140c155000210303030344200c0c07003140c86d400303c5002c0a0043e251064070100c8031961b03040303811160150300c580c034001c49164035107220640c02070202020301c103001b000031800c14003458000005400090801e0b500200d0400001c10490002e00980384118002c0368501c0e50b810b8500401400b068000304004003e030410300006001c100003151070600300800c98041000070303004800414134500348201c010304290001036055000c860303501208040310a2501515007103070380f96005903124410b5800c1800141c07c992410f200c0480560b206000010f60700e0740380914415200b84581603400e85400400110b40c03804104001c600d403410001ea4004401c0d070720070440341c2c94040828810383d4130f02d141a01c0340f40c011489810b800e40940c1550003c094440766420700c1d580d02c0070050040c00bc0d00d030098482d80c2c140742e00060228a64050751040700c500e090a0340c0b030605 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 474089613 1250 474088363 474088393
    0xa03110111040e0411010e0d1103120913050a1104090b090703020f04090f02070f111207080a020103050a020c1509010c17011502010f0c0302040e010e1e0426030411040608 75
    0x7000d5542c6c14862821552422910b6103181c0b200c001e84100c10741c541001520040610301100f85d0110010030100704249000d5484600f80c940c0b03035034103001d00030031144c64500904c0050905059a14411200480c00240f461041d8000f5240c0007016144064070f80c8907540c0840c160b108100790884000c0c01088200040c81c0a035104030480c43c54244018102143d642c0ca11200541074402525440c0c10b0000704545840c007000003054010660004002e614589011141c031707140c421801a05040e0f42e04002510725800b03804032201d140e408400e031881504d944041c5501c4000c15500310719290b1130005400c05207406400c01c0820859030170020380c01a80b8050a625001c041c00003904215500c0307030100380d00035510380074040401580d0385001d0b807100e040415070740d00d441c4164407400b0b0728011941400800040c40000360304e406540c0c0089003403650b40b420f240d80c410701403580c610b240c100b060303100350364081d003007005103000b01d00c20281003020303404120030001070790364a00403c45140c110501c40c8024071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 474090863 1250 474089613 474089633
    0x6060a030201080702100207080415410d140c03060a050d05010e0601090b2d240a120e061006031d03030903220303140313050a03110111040e04 63
    0x103148102d400410070001d00805030f03009088e0444171402c0119043c403451105501c813484013015403402603003081800e0010212090305910340020903038030b0004804492160750a0420788104c0401d9581d807150040d552400912840c6003004111605002065400700c1050899000f40c1000b481d1107d440d04001c100400c0c03014134039044131550360f01d16079400c4080080c0603550080250190000780101c00d0403e1041c01ca0b40704c0108506030509030000319600b0301269000c0c0f00d500c0d00356001d642c1c000c04a582c0070000d5011050001ca90030000c40c025041641c0305821040c164287c80c014040a51240a4159202d00584601c6aa000345540901c5242d20a51120b10010008aa154260310320102414115403003611134013080d8200089400d080ca1045a140d004040c96800c201c0c140c900e562001041c400f09048120342d4610004007150f10b8103480c101b42031000380c100f41511620802450041d041e42d681c00e14140c031039400c0c4074135819990b030440180c43c101d81007407480300a69941c542d03034100e40c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 474092113 1250 474090863 474090871
    0xe090304030b070e1f120915020904140103052107020108520926150a0b100503010b0d0f0e0601150909060f0510021e0102090103050906060a03020108 66
    0x2c908481d28003c1d81d510894401450764046085405c0540040c0040003060407941c0c0703040e0b050030b2940060014881c000a1801402190f4005841d1484000043c01808504003e86041c00c000030001c0140702021615029144003401004039403030300100b01381098010024043d0104038036100151000f80460121403c0080004110580701d12100c070740d9545020840c505406030082101046003030200c140b01c1a044040c5003030055100b803a114003a8000034140c41034100e40300e4809946200d080040140c400c040700001c01c10515450070b0108540200b100010040c49000e205800081c014018400c4905a03a0241051494100300012400141c881c2030701d01040a40d07200c1d030512003000284402400ba02401641410341000c201d4018604c0d0120b801036403c1c586046010000d2105400c105000c039070041d80c4209111300b0008046c0d0411007a1341d40e92208070a0154480b079454810360013044100b40903282003229847d1144c01d00d0362504103d0f40540c02060b80081400598012041c460b44 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 474093363 1250 474092113 474092117
    0x102341a0411060c01020a08090106151121090f01031103060103020f04030807050a0209011a3a020901121e090503071205030402150c0a03120603020a08160e090304030b07 75
    0x8807605035004070f0b5182c1c0c0a9200741d44540d5001c620b040800d42e00200c02c0e6008a80c060082c80f00301d0400c4044110011040700d2101401130b4a00154880e680034080112005020240d240c1c80801140038482070303a0288960764440c00e90340224002c0c1d50300074840c818224440c41c0d0080e0655460b000150000d6000c0e54642139491800e020002c0022682001004080d01c500c0181010040c14418070030449810380100001480c0d05169080d90310f044030a440181810b6400b02202d400024140076040041840c40b0903040100d18150b010a140b940061100a100380d81c0c180c0016030001c5210100c0d8051913010038076090b522101ea4928510703800c5101e0241c064000c0e81c0c68000207a07106003c5100d0b00083c00d003c40c0000c020041946003400080102c54074050807070b8074000c5200e41094a41170201002814041580e000e091641c29585c00380000e141c2c060603101d000c0d52100021680d4a003401f680350909440d0401c0401c0640586040328010841b5000540c2458210340e2140c0d00c40304010311401c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 474094613 1250 474093363 474093383
    0x1c081e093313030305010b07050d0507030528020601171002070206160b04120804150e0c030a060207060b0111100903120501090e0f06061e030a050102341a04 69
    0x6803040c0c141c00e0039020b0406030910300182e00e124600501a0341050340710003e140303824000e035408220040f0b480c0100180c146801c81d0f94040c0c0345030545160107003204103044070556040e9072140034a200781121008070607400b2150607070b999071001000c28080803031407509500300300c00e0f03410906090740203418007500c0288080c2c20401c0760100203c002040038001e9455405003802d20051004c0158006010100d624002c1454907250716000c070400801584250810780d03880c0040d00d106024054800c10000003416245880d04034106440a5003101100395840d81c03512101c418598025650024071903010b03001781c450540c00100d003070002d04002e0320940c2404042801c2d140bc0d40200d00c5510b010b030000b0400090542800424185012809120203c542d403040051000ea6950346401000c82c02c80480d030800c007580740c1000b0a0401406460003421036001040094a0080701402d110404410400f250751400c00015801d02000308580c002d0594504a140e4203030610f49880c1d005e034050f0081c1c2c0949 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 474095863 1250 474094613 474094693
    0x40204030501051f060507030e090411040204080f0714010c0818060f0c010b10080606070f080a050910050f07140307021f031104150f021c081e09 64
    0x1400d54408982e03c0b01341d40204814400460011140c85010b08064581181001d129941c06000101c11031021482417411800007820044001244141204050420b64959a4541d882e81d5103410740003c0c1400b90103050800704031007491301000d00766004143d5841c03d4069542d281e207102d5500401550381140e0080e12074103140c1d210180201500d2911005071030359a51242d001d60300f1125041c80d103038402e0200480400c0f0b070f1540000e040f9001101100c9442c0d03600c0c1a0f2030a00d0100c1e00000004101da40c021038602d181a40140c09800140b070251940c2540d03036071100c1c00311740d90711400d03200d074070101d40520041000c40e0078121001010035a100803a86452055000502681102000e102403540245110410a50b241c012011204000e05401d420130381132400101000d40113405000400c01089a0302190f54030801884240440d00c0010040c442843d64000303114460450f440fa4448481501e2000c80c41740d0740402c1c40c411104003002e000d078041508181c428a4250303050340d11110300748904503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 474097113 1250 474095863 474095873
    0x4030215010e0601080c1309180f0b15030708030703030510240e0d020f040e0c0a0e010f0b0c1b060f04090e1902031020070302010902090c091c0204020403 68
    0x9010744088000012503180000c001004060006d202d04649036082c8401040203466000c03100c00d8400341e46012450506050300c0e03040c412005040035001c1442d503200f03417052140c0c10500a0186602c2201c1d015150341c00300500da52020b2a04c0740a145500400001021911175480240c0050080007e01e00039a0b075202924400041e0315180c1400d00f092511400000d900320070900c1049030300b81c41200e200d001c1500000c1c224240513540e24021601c849c00d11400d100103000807031381d80c000101070801640d02c1e00030380075445c0400d000d41c100302e00400e50081065074140703058403400800306005000308040c1e02640c109800320500c800d504600103010075010310446502034805025010030024003030b01481c0007a850304000e44988913070586042410313400350701c000c220b410179424081008103034070500e410310b034044000302944804e0620010640c00105541074004040340c600803181504a6140c00d41880c1c8207125090429610288005400f941c40d83c0c000d406c40d9165000400041c10550303030344c0754 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 474098363 1250 474097113 474097153
    0xf010914040b100809010605150a0c0606050d050d03050903040302130c2f061e070513030210030905010506090f0105010e0d020405070305190501150822060b011d090103030305040302 80
    0x200c00d000c07840c01c0041022100c5d091284000401080701c0c0c031049844903814040e201d1181400c1042005954070007201441010b4000d44010306000d040108007207180e04000c2d44480031180c480c5c000904240104600302000001d580039260000c040071400d0707440704640380007445e444000e1003e004c3d40c25125260190342115008881d001c40d100184000e050400303c43c10118006e00ca041e0f034400c103003c006980482c482505a0020003410030507a2505140d500880c5004150300c0254811589188485000da15030131504031280305000a104545418041026151040301d401c0110b0078404010031081d1710840e401d10b0761781c002502801c1402460340218050714021180000807940302d500b40302000c1c12140ea000b4043c0340d0740108200035410649a16190306015000070700308018440402d48000342400020803e110702d4138296003903000f03803400c1e4010308500081540404d068100f020b80324900044450300c03100c00140226440ea00719a4164000c28002d001a001c504c0b40034120200c008003c10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 474099613 1250 474098363 474098389
    0xc0e030d08011509151b0807150c031b080a090b09031b03390f010506031b01080a020304060b0d110916021b032103150f010914040b 58
    0x2840100960602500f8800709400c0d800300b004102d6481c604200030520f28200f49854901e80c40c203d8404008401030368409100c000020b06858030015a00f001c000304107000c00000364008005001c030030307803c040c250111900743c0c42e10700281c43c007101c00000440c400c42d0703155070044150740c0000d10038240e6151101000400c0350761540b140d10010700b8480000c1e001d9408000344402400652428000110444101c00316001c0000454440328020211001103c00e1102d101c1040040358006074039595218041e00080e1026030203030117240c500800007a800d2030010315404068441d020961280302e800002540010001c0c0d4205a81e42c0b04a0b015a440c510340b11006400390640c2c1b10a51250400c01544c102c02500400c908480c034250702401c15004a440071a0000c0d0314030444400c0640e10101342082c0f0007101c03044101c002e00324002c0015040030041e60280c00e4600340e015441d0f064600f404001d42c43d044035180400c1a8003000c1042c0406c0d40541000c10b6005003010034100704070004280c400305544 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 474100719 1106 474099613 474099617
    0x515031009021e030f0a06140d08090301110703170c130501080403110706020f0c030a17030c070b010905220b150301091407060f0e030304090c0e030d 66
    0x14981024a1400d43c29403a030720314104c0051081c94104503078140419147c40008a60810800c4c5060b23000000a0300d80b03403d540e115100e0901d0b54000c105455415901d9030001c0c094400e1800280c030306103111b9183d0480030340c404a00f040e021100280842c5410701d0512001079402c0c0311100c000b040f6042030074403d00d5500c8230b00741114041841c00002100d4462400005036107640010170100304240a400c4d00d05204040d400c251b00d9080561010b480a504c400d045a00700202030011038100100ca682e0500c0c02005940e4441030030000d80c0540c086076520401c100400707441c0344000c040780c60b01c0c040350454040a6914a90130700070180400158003082d00010703a17152001d6000c010342070742280d6800e004010a0100e29900c041600805001034000701418603040d01402865400c1ca400070007440c101414001840024100c4e206040208003102c0d400045070388041c03004481684440d = true := by decide +kernel

theorem cover : BRFrame.Cov 473920863 474100719 := by
  have h0 := BRFrame.cov_init 473920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 473920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 473920863 ≤ n) (h2 : n < 474100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
