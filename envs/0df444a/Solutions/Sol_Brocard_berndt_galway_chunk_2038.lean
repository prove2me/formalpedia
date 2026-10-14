-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2038
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:30:31.268668+00:00
-- url     : https://prove2.me/submissions/901f32f0-5fe7-4fde-ae73-8892cca68a4a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 366366906 ≤ n < 366546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 366368156 1250 366366906 366366919
    0x31f0602010e120403050a03081003080f0a120b130c0c05011d12041212050c0115050114070507050d14100902030106090b032a0310020d0e2811 63
    0x1150440207000303001d24840249036100307609001c2c0a0041140c241c03001c6a0f0700c50000e100c6400c2c140d40031241c180002e80895880b07502d454020001410400141c880b02502080e11502e4200c24100104201e0443c003a0303154461400000110644480c0404030204258440c081074160100c402141d0b0307540d099501421a52a080741c0b0002c0b08103100c240540040f42104640c030420340529800106c4c41a8441c0e0403400ca200203c1d8030004122182884400c541402c0c4a420070203034101c0242175908501030141500481c8005110a42e0060141003000d800c1c4156141043c0881c0c1d50296140588d0182d0751240384075a0104041080040068410103501402c0d07511226500d002c400103050b0300f0f44205d00c65400d000300801c0c201206e100c0e1031030030000100141042000380c000700300912414070b2018030244401381601e50f59101003207030780800400e2445c010b0380ea11350500c0d0071084964407182c101668001e03006001c502000c1c00e9039111501d03280041a1003202c0a07150103014040c80c0e802c2075421a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 366369406 1250 366368156 366368159
    0x1406090a0e19060b090601111005061f05030702010c0801080a0b0414010207050d0806060307170402040902090709060e0a051810050316030b0906070203041a040e04060522120302031f 80
    0x30f0382d0382000030721050950354405140c9071100150389200c0310b204800c2d5240e10403808104020001d0b00a1500240007810300580c1c403422a0b4060700741041c1400d6040403ca0010501042d40c1e030911821052505074a4030381455410103000607180d820b0700f00083c04110f03001d00440c2c188003011240f01e0000e007510000710355803000340c41d0194072270030160100d4001c100098000380d240d040030030880f0f21480240e03464200c580260900801107000240041c2c1e005aa10f84490005885401b0818042c800c1c0d0340340c8511341e500c0c2c0f003801444107440070355240c01582511801c205c1c98450446011540c1c511419a080d1035884611201240850b40d01c41903143c0f00c3d80e40003a05020745400e50310142c80c01981400c0b4280d070342181143d5294015078501d0010380c02000200300f0b081c000c40400070f42d903007440c2c0121301e0160b50f51900071330a20103540a49060740d9500a02c0401030301c0040e00e0310b6140b03201480b18824185130b1549603152481c040d2410503d0740000c0041c2d40b00480b140b035002c100c003041c1f041c4045035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 366370656 1250 366369406 366369413
    0x6010f050f0a21141219050d0c05040f0b1e07170f041503021314042a0e0d0f0209060607021002010906061211041a0303041502011406090a0e19 63
    0x100402e2081c0c604d5008140218410302011551007a450022013629280c4807198010510442d00044004100041400350f030403890074900070704003095240d60701c0548030740c28400b04941401d5254409030070383e035040180e4400a20350690354415580d00c25140c1c1d80300c541905242021007203103040800780076000500481c1e0a40060050010703144d03c400030003000c11140c07005400f05d2240403103089803c082910108080d00301d450070905081c4d40500040368240d4040003801c044402e9007110600b80502000503207080364802c8000540300d2003103e60702c40c100142d40b15000f80c4040000041d0148203d10300084041e00c40004641d081c550280c00b8055480718864020b00810400004440050400703800080802c405842d40301130b150000c030250f010005007420000240311081c1511b44080b401120300c5070b141e5092010704000c04002c5c04070420400811030083c211040e80182e030381d0840c000c000340007864984440c0381f50f01420751007002a45005004086d464103c14001c1c001c019102c090011080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 366371906 1250 366370656 366370709
    0x6070f060c020c0a0b16061503030e100504031505060a170105060a080c0a050108040203190c0f0b030106080a09051203070e210d12060312031d06010f050f0a 69
    0xc1d015401e66200400d03090801000300428440c0100380d900600501c0300e220420f001034200284510030000742c0d0000e051002c5040c29140c0e000b031b804100c10111241c802d0904211404040c4800d1805918240c110340c0c8044c0c03100180ca0071414415074a03000070b604c1c0d8407a0101c074405090b002a20800c03200200441c0c5000c1c0c0400c48095000d084c40200c005018440002e0941003804001d0080c10900d0920004407a0761400500590b498440c00c040050300e030448480e1006507500812810322030504080b18195800e00b03a84c04901c00351801c00040200961102500b50014003c0c000072481030000e003000c502c0e1032410341000c804444c0001c180070b05613400c403100640c60b50064030700e0507142e0821440041c00800c100407005050700701d1000202000d1180b1104001004071200000303201e0b4807612002e410328503680d109000b090740c40b09411a0310102814030303200c1c00000d400814156040011401e106406449002c2c095900111190b2040d81c4640c00c0e00083e0658a111030120680b03626820311 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 366373156 1250 366371906 366371921
    0x52a040f0f090c020c06030109090606030206042c1005060c0a061b020f120a050f0d091109010806090c040e030c060c09010305010b030705040e040c0b12010608090a03090e0606070f06 80
    0xb1140c42d100038010500e00209820400c1e00c3c000340260b042da8a868488009802c1030041143c13040e0b40c2d0700010006a480c00003a01c0a0050010300744207109508241c46a03040300900701c00c0d031b540d42c00c2040010314420b0f03850810603200155041a114100308200da031400e4000744000b000b09084c00944c4810501c80c40151002e040c10313500300c9040e1030103091015159103620b0071464400e00108010036400d07005000406003c842c800340c083c64105424071042c102d6400311000c035200044400704100c585054520140504204805030400b8240b40354201d941d013006010b20b43c00b854a8141690880009000b82c6007440c420100b95140c0e407802025800d00c1b0760002000d10b0110340341c4000490411003180c107403442b640c91601d0300352a05081141043d00c0120007041252b20407407041c0c000c1420100513000d4038047c4048401d08d00301d541400e0303002c0c1c1034402c008c0c41e8100030f40c018000100441e41c001c0d403003802c035441103a20f00320607292400492414440c124000c1c0c84000d02c02e154400f001190f90000740f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 366374406 1250 366373156 366373169
    0x10c0201140c06070f051206090709030b040605100905010510110708071202100503010b030c0d090c030b1014100e0406031403030a0c020d2a02130609050604052a040f0f 74
    0xb5510300500e20603540c5d4010b03854090300c7d84624000083c028100318101d55040340c90b42c141032400039179030343c0c0b004400c0c8400c65088034140d80350b0303091098803103c581808001c0d160400c4140442d6041c1740204dc913902c0705d2703034002003040101003007158200310520560b00500880d1060301e10181d01d50944c0c00111f1043e030381c05c80c041c4181030480206a0f104400341c0381681c1c80d1501507491600d0784108a4015006021403001c40c5070350b2001d44002030350014550f401944038064442c020b18240c00780c8988402190701001c5480c1d080380b98031440d540c44003e40b00e4803e40d81d041c4042c0c100b01c4580880c0042c80a50802403004d07406030700800f848440000614842d8502e048180400d02c1480812615561401080f00c081030608410080504808080039201170181403c2c43c85c00305503400045600f055040b92803080c9a03070395000d01c0150014010035510000a4405114505101d0f044020080c6028242054030b019411a961501c0b9004110340041081c10f1040a40e95250a03070510b600e00c481c460301 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 366375656 1250 366374406 366374417
    0xd09060c0c111c030c480f0b0c01020708030c0c16080312090f0a060c0908060408090607050715170f04020904080a030e070f060306170606010c0201140c0607 69
    0x2150718120f284248041e2484050b4054403250740d40a4030461444001101da00010741c44092150920200400c240c9180c0c941d16580060b41c030b08801c003803204c002d0f24049a1714400000384034007114540a070342150349000c1745507568450821f80600a00910000520410000050040198000c0c016200c0d0b203038148103441c2d03d07035070803103040440c0e0700c03d4030441205800c01e002050f11240c2c207503051030f84a101901569510702503001050f00b0301058200454070595982c6140c800c03039034010042c41c06041314130000c0c1030398141768403055460300962002510808002510034200f14050141d0380040001c4286c065401d0020540a04809600c1c0c904410500711180012055514a29103130300035500900500d02a803210b0b00d40030302a5000d080da980174541c6a80060410720010402c0034001d00711500317055062810420b00400b0340f441c07684440300c08800c1c010300304205c260108003150002c0342424501c2c511500c5100681d8040044803003107006001c00314880441e80f2012a05c64030449040d81c07072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 366376906 1250 366375656 366375683
    0x50d0e0606010818070e04020f2211040b071407050a09050613051302010c0507080313150201020316080a0b041a010201060806130308040503120117010524060d09060c0c 74
    0x4801084102134030821941d03c501d004010300500c6a00554000340003500070304c140043c1c40d0103d840b00d000032290342d00780c0c081c40205401c1030b40c5620580c4198240ba0302c010340380514014008040e030180d604090071070701d405a013040c1803410402c0b01c82c00800000d0003080f40340c0ea5a000241c01803c0c1200d0203402034080d404801e000c02e409200300c0748a0168841044241c0b943e6400468546003550000c44640c815000045100c0c101080901500100e4503900c4084604080811100d40c0308804080d0a5a0040c014408140204060101e03400c0711880c00d484980d4035880d0071406403604205654000340b8184052410b0b10300c0a803417400d00002031b00240166681d4442c60b0340d44807800c0790901400c000194540d80002d00c9110ac16401c54094422070f400c228420b038080d006030340700303a000740d0b01452010041640640207000d641e0380010300510001c1d0442d070a075410101c6610000e542031090170700003204142c0340c049a020480041e0000c104010303802648102804035012a1820759a900c0d00000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 366378156 1250 366376906 366376921
    0x903010e01060b031f0303211415040e07050906060706060f0603020d0b0d0201200309040212010303020f07050d0303020307021f0609061202150a0224010e060907020715050d0e06060108 81
    0xa5200450347c0c503945200f44400d4541002c0400701005281c0f6901c0340d2184003540a03040c80c24507940c00f0750440200040c4904649081104540c043c000c80c6000d60488003082003560f45050100b54010000d0710310907a07a096034a404002040207401080044101501c045070711941a03014003100380814000704943c1c1c1189041002500b65000d000780001d034051140c00e0410b0491008515003c508800c403403e0451480c0002e041e41c000e0549410303403000c1c00d4010418107a04001403059110240007414416080c1303070200e1201c5051150141c01c1c19000800b15400501c200b000b103101c1c020710303141c201c40c0c456942c0d501400b400b02c5100b080c0301181011070108442d18207241024120390b0040110315420f0f403004c0d5802240d00715150300401d501607400c40403510048211000142040c44448008941c10400300100b0f5030009030605014182c0c0808220845400181c1c42c0291030140280c80c0c1d0f415540d65040303c07544143c500d01001c260a00c50580640c410001c0c04c80e0083c1426207803018156901d08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 366379406 1250 366378156 366378211
    0x91b063506010302180d06021e040b030f040f14061506040501022107020a09060906170a170d02040605040e010504140a05060604050603010b03041b080c01050903010e01060b03 77
    0x15010801403004a012441c15030003030780103005c80b0310f5001d1074030114505000000c1c048580132005503082d0741c000589c0d451b40044810180c500340400c0c001c030381c100303403c000c01c1580300c3c00020081c492281d06140490184080102c4840c4103035400700c2400c404140d507420403a15410140c0b017000c0c003603841c40794054844c0390102c1914141c580683c02011200d030450b40702042e018000800340700c040c20412287d00503880e184103400152901c0079022513180c3c5045190421075081d80d0002c080c42e981008034010041c000f20782c00054603003010b0806010303039100c40300c14024400c2040100005200040000d0a90303000b0000c1d00031034044030900f420a80e683c600380025a82004c0c400e1f442d00f00c0c100000b0f0140f902c04e6110a420582c0603092908250701c810116406500c2078000080c00c130030100c1004104a0344514811030031901744c40d0585410b18141009079580d244500240c1800780c0426900c8954409500585813005400c000f80300c669a64040e40f10785034001d85200c070100c440c10001207003039550760 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 366380656 1250 366379406 366379487
    0xc0e010e010f031e0e0a0309080106030f110f030610050406080f0d050318070e16030905030d1805060a05011802180d03030209040c0305150d110103091b06 68
    0x42e121100408402c0030708070010200348103010260750b80190703018540d501a110340809011080c00401c1103024506018051002c01c0c1d02c602aa6810038005000103403036181c07000704a0b544108150740e03940740d440000740e180030440a219014800d400400004c0c100c4402c030320040b204107075810007588d40c851442a8442c058010940142d0340020511301038288580300035980890760100e07200c01c95580e80c5039207003414a181d00c114281e01d140c40501650307411003401d004c000703002414100301002003aa641c0740ca03070007030072096098990303624800501c4028591030031000305c0c0c2c00801d40780249030106400008200a00984280d048141e012000d4200184201d07440080082c096a0342d83d05064204486600b1a8078101c0801d03409000760401a105ca00510004801c03507100498035203070001400e039241800c082c00c2c0344030720101c04860012402006404907400d0080c40c0200d1041c0f19414118a08106444080100104e09400046807035020b071142da56a0480ca50f0a0f481a512507420300d84070308071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 366381906 1250 366380656 366380659
    0x1305150405090a02090711061f0e100b0a021002030414011112010504091106030403080105150708031902070c080601140609011704060f0204141513030312060302090106030c0e010e 79
    0x3d5140c4805071070080b0034964404001c0c45e020002444110800d07040c01c0095940d402c00080304401140c980c161454184080d00008200003010702c0c180e858058044024883e05124420001e14030311440e2080c000c4c107400048214055590717060a02d030449180315503856141c80e039460a6820041c055540040303070b07400301038201a401c660b420311007004014843c0600c201d400c5240541d103c0d1950701c808000e14801c83c026116400c1c0c540c900014041e44c0019001c96211810701000380c100050342a40035280c0101100000c41e03d402c08000d002d4000707100c1c0381d2003d414441100400588004001782e580d05031120201c0705408501064144820381c045d000c4414040740c1c3c6900f040010541401500c1d40c418011031004c02c080041210304401c030ba02940041c11f40d100d0b01c00000c1d045041081030640d072483e04183c0a0b1802402c1c0c10107903811101800010304001c94483e01d140b4020700343d000040035540040064045581d10040034005250846801d0040f4030050282140e80d8055400e62001010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 366383156 1250 366381906 366381913
    0x70f03110312070c0314100908090406080d09090510050a151b0b160c0212010905061b161502040b030f0a06060503010b091207060c150c020c041a130515040509 70
    0x2c0d81d0311402c01b0140c441100000b442220004c0088280c68010b412030b1600074000e042c5d075580c100040c40282c6010b0b8010758510350107200d80c549403550103a045403c030b0b8141740c03002030305455415040280300c1c002d9000e182c1c4460940008582000c0980d05549040b0191b1204c00400d100d88008030194161114003400d004404400554000c401c00c5080140e400c1c1c51a103001c0291807640041c0c00f000040b80005000da64404a81d01048420094580c0000c040c1c14941c8240308203c1025805214024010341b10040c909050000c02020304241003400c0310300d41d070654403a0740b40d00c0341c2091034000700d5034120203c030310f4008590900601e210b01d505650460b0340d800d00c3d40c2c1c24043c1c0409141c0c000681035811070803c440c20305d5885000d0106401400040d914850b0300840d0381404000c2c10b8841c18981c100625007041c4419041c0c0009442400d000290f60201c1c81c2c084d001e40c8050000c601c04003950300800020201001480181c0c400c6110381c005400aa40406031a02440126a0200c81c1c1014660 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 366384406 1250 366383156 366383159
    0x152115060a0f02031b100609090807030f1e0228020d06200d140c0c0d14070506090f0d050f0409090203030412081201120320070f03110312070c 63
    0x148141e80c40b40c615881c03801181d20700001401c0c102070179840c031442c3c490301d030308031703110544014502d40100c01c010007584100b4400f240494035000e082d846112002020701403591403d400740d0b409150402c144800403a480350500001213000307904e915071440c003050915001400d49003640c1249652540c031a0b0081c1c0403940d80f10044e980c0354010900c02c0d00484200b100b101078600320100100003001000c0b09030102081d0301580008000c02c40001810081c12001c041c0300e9400402c2c000103000c1c22002152030700b4803520f40c2c3d08030710040b40d10036120040c006e80101000c00000c1800061040308079003251040700c0704100100c0c1c04644078000c0030703014110958204020002441990011402540000e0903245465a40ea85240242c001d180341241c13481c001190001c901f0280b8545107004000c480c0e10815410841d540051007005c074044641c114010126100109000c20450300000e0240c08401005443e113a0030300740d80044404100900c01c1c403604070049500450711050f10340c1c2c2030344841c4200030f0320b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 366385656 1250 366384406 366384427
    0x60f011d070504090c03020903010b01030509030d02090409020909160905010f060c050f0105090d030b1009050405071107420f02010f0212011502060601140915211506 73
    0x1070030300c00c104242400003143c50f060500c42c2140e80c00598800503a202c400d0400e00d42580d105544813414140703017200700070f6118400f108440001410140041e034410303d41000a0042c40340b00400b80d0801d0096040203031a110004501e04d45040e00001c91500e07580e100c040c002510402d01032460032910010042000c1d9018288a0180070310403030070750b103990301c00603103250859004071072164140d4001101e807003013a1b42601c41c002810701d082d989140d15807003600000d460107050740314090141e6035440019090310710802e0409000c500440589100a03980d181f0ba0154026905441d18280040600c00c644038480701800c00325050703141865002c51500c41c070f068a180380400d51203000d5540b111442203000c202071004015030032580d0302c0c040455040816143c05585420b9044003558000340522890344c2c1c102c004c0114070040b159410b5950241c030808280602c204400340740b41c1140c0454851700301034882e039070200b821090000b211690b9640c00c0c1c000d034560b00d041583c00d80100742084500c044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 366386906 1250 366385656 366385709
    0x4060f0e2a1002060601110c090411041401080c01030b03010b09180a060606020a12020a0b2404050406090b0609010b0708130b030406090210050f09060307031d060405060f01 76
    0x452003200580762036030310088042102c80010001c8000181c102408004c1d4541c0c10071180c204c050340030401000300d0154039021039001d200241010300720790941c013042e9565035a160046020810311586000b0a541e42d2015655207450351551503001c02c0c00c100380c940c020f003014030401b50070040003060100d0360303200d00045000039455803a0001182c029041504081500c41c05400020305050740107268140550503e028460031180d030b10b40864020146040114503031400080d000582c2c1402c03442140c1141281104e414084c54a06811606003000c02050001944c0301c010705a01440442019555104c100176211400340140183c201c0107200e40c5012400c0080501303420400e52500801290700d4180c440301c13981088030304640e41511564200c0131800c250f80204c1c884501707410942d05014000b0803903402e90281840d00e40c000c3c80301100081006100703800c0000032082d025601711110f1350381c140040d00c50004840c25192032041c00082842000071750019030494a00000707002c99820004e000130342 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 366388156 1250 366386906 366386953
    0x110c0f01030b031b01090605040b0d0c0306090f141503031b07050d140106060305060f060c0709090c03051209090c0304020a0b04300203031204080f070b04060f0e 71
    0x1015940d408110b5103071020031542c00c0003034010b8501105858420001081e0344d0054101d902080801d01c001c2000fa00c05a09881070105002008900d00005040172802030256a000e000003508040031007002c0c400c00d611190f484003c0742c6400d1080c2d5903160920400082c02e00859406500c03c1160004d04058034803e42d180c2d00c000801c0d02d02c110f85d00c600003144141c1e00c00059400443c004070a03a0102001d10406000304154241030105d4030f420000a000d00c1100282c941c00750310300054604c0384810a10840002c2d240d402c508200c44c001c05e0501e14101c0085000c101c41038442c41d041c1c20740e840d000c4c0c81500c0c55034000800c402800e698102000d00c09400181040360000540c010119100c543c20004d40f01030440003910340c0d0401481051450a10310702c059045428500400c40030241c0c90210443d1074032484800c004081d42c442c2d14002c901413088046102009002080040403c02415a914041e90140d00e040c8204002000c040080b1a0040504c200982c40214802c0b111580c5080e00c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 366389406 1250 366388156 366388159
    0xa1202120103121101020f040501081e0112020a1a04080d031103191503050319080f04030c03090b030705091201141f080f030304020a0b030103030906031109061b010c110c0f 76
    0x409a0403401341e8609a81107061511b00160b030108050000c0c0d60322006084e48043d401d031026408100342e6896010905043c020b9000d605201c00e80b048c00e41d00c6142c404002800c0410540648540001088459800c1806904014014140c5800b0000c1c40307401083c541c06680c100e0107103142c9844008055512643c3c5500c204a511103030403507109c0040d00300c664019401140596038580c51840196007840300c00f003200007803040c041c062180d60310109401a500c1503241c20440403003400d0b8101690340010540c40444104400420030516a5004000d01400304042e07903902000301c5000c030303141d084e20b0b10300084101c500050b800050010003c018240c403105941241c0e01d40702e64654032000e007020121410600700364400003e1004508000c511403000300084030a041c25541565001040100288a0581010703281d441c65241a044030080307489806c00248641c1da15170500c046200b00a80544c0081e48551920b8400031041b8043c16100d1540088032005c0c1c11300101601c108400081d000d65410f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 366390656 1250 366389406 366389417
    0x60b010e0625020d1b03020916020a0605100e011d010b04080a030f050c0115031a0c1209010b2d0103020c03040501030e0307020d0f110105070b0f150a0b0a120212010312 74
    0x139022900d80c032240c904400e51011152035250071030051101401c405803e94a0f0b1040e01070030b10603900d6020694440c1a6846100450a621032044811b052022500406100e1a862000042d07001110754010040320504250301c2c030680e41c601d4021000d0003984102005d6400c01000000000d200700300050243e501400c0142c20b0045a2075030a084030b001c001404240581c20005000b0300c034200e4102105003a5120303426086240922200c100c80c042c04c6040440d220450700828400c4d032003901f001107135550281040c000010415030500070000c2c414216002c803c2007120541d43c551081c002c580b0f50075468801149000d1134140110014001040c0c0400c860005004840c01a50b44018014005010f20405640b083c810300300740c5000c042454040d41400400c20030040060714644072540c1c484c3c07010340c24588030b03036a402092060420100c00640c0c031800703810703010840035004006451101d82d86c0e960380070020150a024000c900c02c180c60010300010110040001540b40780400030020319a1422 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 366391906 1250 366390656 366390679
    0x3070e10020f0102181320071410020a180e07050a050903071e06030b0f04050901020d0903020d09120b0f060310090609060b01032d0209060304060b010e062502 70
    0x4440c00c9030410840c1c2803108007a60f001004a01e403c801b20b0100400c9504200452400091807113074406040980c451110b60105050090241404880801c0050ba20540324170000070b030000d800075130002c0030382d50204d40311090310403600500b1840c00c0c0175108008100da4240d100c02006941503040300150008100f001c0000f15032580301480300c2d00041c1094550f41c000d40704507103c0602c0051a0747c0008040500c0d10025034103513903584a02c090840d200340c800092a4848a02c1680603209041c4049030b40d6080036040c404141d400190464600303125a00c030050039460f03281e081c80c1800c1c09007002d0402c1081e01c001c901c000d0551541c2542002000b0100e13500b01796100c1c2c600054580f01a0f081d0b03030782981c4274000400e01500b805210140202442c04000c440d101401c01100000c0e0101c00c060500b080d030805101c07491155044800813100144155124a42460700c5009000042201782c0022004100c7c20a03c3c00d00030262058003032018010745c5402584400920329800c0d1640c2aa448002c4500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 366393156 1250 366391906 366391933
    0xd0201120f1d071d0c0a0507060212060901080a150f09021302030a050c190804020303090a03060f1b050403030c1e081905090f0409060207080301080604120503070e1002 74
    0x61aa50346032440c0c46400454003000702030b8149441030313105080e08441c03600501004407210540c2a400140c440a05456144011003240c0030700400d0001021144000b0b0000c040600d480e2042e44140d008031034424250b0f803509022620340300700180042070b170004006403041d0900e494000200c42500c80400007010201a0009503440c540c140030309542d0740d400400d200b40002c541c010780394450f0b408500c0520f041e03050404140c0e810a8586500200454040410304658081c0101d6500c603000a00c000d10b00d544030306086c802854000d64104082d40780001040c01c0f02c1100a20140040d030940b10242001d103180c40985280d0400b1500315607001c444d040c4a61060a5072164082903401401081d440c0c003481000e081a031102107841006001044c04204140e41e02c0e84a2100d45010030b03500481d5100c010715059002e0300900308000c2241e60040000b00301e40c43d00103021803283d800b40c02152080314040301c0560310781c0310a5590314001501c0645004443c28a070540304030f29001881241c130542001e09 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 366394406 1250 366393156 366393161
    0xa150512131218050301050f0105010503041a010f08070f030f080a2c01030b030703021e040e070b2205060405060309030714010c021204080c041d1f0f0b0d0201120f 72
    0x114282c081a00341907000f040c9a848103200c0c0183c042078008100ca070070315400781e050f0040140315039410890000009410014411a000c1c00020f81e00c041ca407940d42c450001c4915100030340540e01c8140324007640000d03a09030b81c4841038100c0b600f00102500110080d2560562944404900d10a01c07a41e2401810700c0700c1c607044904e4402d2241e5000340b1441c0c140e900014295690500094800e81c400c100610250703a0f2003a184581c130011001d4030150300402c1d00402c001c3e21550072415924010300d07600080d8004201c00508201c00c9512600784070088640084c8200344460017410381081c01400f040c03001d420301d5401583c0140d1254100c90910200e640c851160880c80301041c4060307512940822113154040050038100820700118505241c207085000365151070580025116070b48811b009094004030329035a640c0c4910301d1050b2803000c004014401d88841100e0a07024450303240c68202246501944180550b00300010400302c0c4201054004580003114070700c048481c10307680c036070101e003c42191 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 366395656 1250 366394406 366394433
    0x309311d060103061d0307030e0103020d151d0f07050a1b02040e0a0c05010201020f1815121f14091503160503010b03061e100b0a0e0a15051213 63
    0x135000070031590400503402001e07100290020ba00703a4414407100c0300094010520390f000500030702e8016141c901d00b0580d44042c0002c0600e4508081c0da102e00818170410001900e0f1840d07042d400c6441603605d85590b44000c034101280d0800000344e061000303800817031141c83c00071807001002119602a001a4002800311100c008030300f40641d02c61102c3e0410013844452030002040c0c00d0008606210240341000c034144140619070f511004880d900b4040c07035450b0540d0114045881b900941c0328050b20750600d0840350180c407500c20b0004030601800650301e9080034141929030003041e0061210400381031280984000c0c00c000e0b81e014510000445e280c070100840005451034445030302c10306152800340350031a14182c20741406508010f04100c4884001e00350b0700450000d20014503080d948426040c4030114998024500c1d41c4000103d00070003aa204c690610100780c01ca51020611b070b40d55411500b42c800e4288a100401d5040c4154005001c084101c0c503031040d81c41c054800906190369503800c580804 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 366396906 1250 366395656 366395663
    0x5071b0504060b18300102041d010e10051008062101060f2102120c06030112120309050d050a09050303030f190209010c140114090309311d060103 64
    0x45440c02902d2001c44c07141509000a407118942c034030141c042c082d51144605207582c52259042c0c1c1c83e01c4406401d504981c010074108007200300804100281b0b480d046030a00c1a9111800312502240342c02000c10302000469000902c1c0c594088614001034038086c030020003090b030040044800310400c01985c100705902003045d8000050381e5051107010740200000e82c01c115006200804960025020b40c1c49681040d50102c6820107030800e02000946018000c40039107400003804800000c1100105611186070b9114039240080305071402c030300310f0444800d00700151043c0d00c40d10280e0300c0c0e103004070000c1c0980d24940c43c2042c21542c030b410210303243d580161240030307406c00d41c0c0c001c00415640300f070785103054030714024401e41c40d0040c00c00009001c510801c1020704150000e40784c4901da40740950001d0b901c1c50108038001c469141080c2599140c0c0c1111200c28050000c00c4051050459421181616282c0c0d000001210001d1100315500610480c1165080f2820b20840000e102e002041010300840c80b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 366398156 1250 366396906 366396929
    0x6080919021c0521030c2d0705060106030c030506031c05042715081209060415080105010e0a2106090503030a0204061205061008040c090c050c0706020a0305071b050406 74
    0xa04002034020010340c0c4c10009650800e01c02c1c4008495842c08942250401502014040644162542800d503045810585c0300e440080e21358204800840c1090485500e40c50411440170042e5003a070540b8001c40d003840e4160014004100f90348000a0110285d050341c0c5083c908141e22905a586801c400c0000d0b05a0307501c0c140c00d0411104e406004e03070070690f02c0100711810240e24284045070742e00381075101d45413040c0300450f6040bc191903400c140e90081c1201c900c0f4643c6004d400001510480007800794500080c403031980061a814007643e5070b001c0f10105013001e00c0012440303868403100028004e045417599121030516010900170009075000d00e00c01040181e885103801405005001c0c210703d5609000d003800d0402c0070035618038014407202e1016003814001942c581c80d02824210258204400082c44d0200040006500201604c101c984200c21a2304842d01d4034026690307041c03001c81c0100000c0702003100313800140028000d0a94202c1c0c154404101c50388460000303040e80d4040d08000c07000c80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 366399406 1250 366398156 366398173
    0x20f130f1d0601050102070303021228111501050315090f07150e0907051b011e0207110604030f03050c030d0507050307020115060806040b010c0209070801030c06080919021c05 77
    0x9606020b05801004240020f0112928550300652100148214103800904c0426447c0707000c2d00c482c160707480c01d00072424a508020400d01015108511a9444031900d21a540c0500090103e4440d298185c80d07004005240c00c0d001d8190040740f9000040c0b20308420301804001c100514010001031020f8040031024104902c003000005166013416801c05200d41d07410344c02d000310980c2200444400300c140500c000100705020800c1400341c9125400c00c0340b01d600356180d0802d00901c0c2d5019125003071250101d00f0340c40000508001c01401540170152900320b03001130407000a8002c1005004203600e50007900c0c149501d107000c10046500444151021460000c100124180d081c400d0a880d900140d034005101070400d94000c0622a00070413960141e0366421691506078082c03250740d03040d1a402040c0081c4c0e4a45014000c044040c21300c400c0303480a00c2501c01050490143d21864403c480c0c1c80000d00c4903034074104080c0d8910500e0704003070760443c08680303081040300b103000207000c5880c0c001c07002040c100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 366400656 1250 366399406 366399461
    0x6090a03021807020f011104120305070213060816080706051c09030e0f040c141c05010807030318180b06042d05010c05150702010219021c030603020f130f 68
    0x1109517a0030a503c1d034580b025541a860100d8251426209100b208000041c00c038070b000d8400c0e10031301e54040e40c82003407111720b0740302e0703d206400400c2950b400340d003074030308509070001ca80150320064054908290001c0f2428400544035402504440740c2c180002c190020301d0550b61000c6a0482c8426030000e4015011543c3c41d0510030343c881508030055400f00700c1d042a0070001003150300004d00c00742052000050921410b801880c21480e03090070607800b0010795035210885640c881c1984170480220303110b4800e152006100c0381c04401203034448581c460100300ba490250000301101c25074107501c44400d00003c1060b801c2c0002594135070b28a1085d14040300c011500c0b024505440307500081c1000a2234050a0005030082a20504e202c54140101002c0c1c440100c140e0181c05038100c400c03241c042002401011641c0001d24031642c8003642c40106288842d004c0c00c600340ca4841c00301030340080d02180b43e45000e0512800350300140c2c04101000400e1b03040f802e60b10043e126500141400c4002440f1480c800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 366401906 1250 366400656 366400663
    0x90e070c0807030305150a0807170d02100e1507020604020f0f1e030a05010c0801031b0f06120609150e0f07020a080d0e1002041e0f0506090a0302180702 67
    0x10014508181034820220303629010140b00d038002c000c1c20152108046029503120510207954500e000b08564040d944407442c1030b6507a00548030b1220000400c07020620b40d6800880c503107182041c20b0780544501d19091101d48050201c6003d44c0801d841a140e40c80c04000300700b5445400340c209680039007040d003018010443c4e00d0443c040e5143c0b040c20075003294446580c0301a074881111929040d60a002c44804001908040074031801500b194205036464180c154003e9030f0034103880c415041440b0f000c0c0c205c454150210010300800703541c4180c102041c00000d010302c504e22100902ca44000c1007464a038135840c01912030301485840c3c942031081c020b0082140510341281d01c0a440700c42452546040070000b0355854031440701030211304002580d6805410190003041403080d101c0c045034107080001500100035072040c8038400c41c0300207a2036143c20100ca15004982165047d5500328401402e010070811640e119a840c103038442d0001500000585078061a40c24540500c04d03405082c0c500310030040d05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 366403156 1250 366401906 366401911
    0x20303031905091b130f05090a150c080c22080304230a05120a0602040b03040b090a0b060402030c0d0501080106090606022a06071e112710030f03090e 66
    0x4140c110340100b94500f071303500c100f188040c4c130f040b54001c11000d01c5902203c003c00d0303100d881b608058108004c0140d0150002840c02102d8407440001d80d445c002116550216203080600c2000200c11401113014019042c0150501b17004415005011000d4980600b41d06111540070b502250404203040003500e090000525802506090001000f414400094401001405400c0c400c0d0250029a510301c1001c101c0b010505601407030071591507494040d44074030b540046800315023606640b40000c0c04140013080780050640e01c000e07601c03064ac543c2810040a0741009052100d0410280b00d00c80f8076000502529009110f07080001a241d0704040200b429110607401c00800d40d4400c201e034401541d0304ca041c0c1041c0040303040c0100302c070402d600d00182c000c0c803a02c1d50150040b0101038001000c04200701419114501c1070310b00484100c012401d02c5000103101d804a040c032404807000c1028210030804040d8010759400303030003507010340b40d42d108403010326026411740010304515802d2102088002084c0e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 366404406 1250 366403156 366403171
    0x70f0c120b16090b0a050306040b041a01030b010e1503090f010c14070c03020607060203090c0307080c040b030a0f0506100602061005120c0a082406010e1c020303031905 74
    0xa88440d54456650a0354090300503502140003500035240740d48501c0c990405040c03c01e07000d070f40d00c0d84003813801040381d081512400e100f0b9240c928603200794601845404034145000407001c0a03403d400c5c0041d4010003003941c0c00d505010000b01e014019070384074242200c009120071300250310b071309203141c0c1a80380c4200c060400718241e141c094610505500025041c00c0c1400e520415a925540c0e40381034010300285a000a4208002103031070010080c0a801079849a135900d801c64001c411018101540d0b2901403250460940001c8041409820b16130001c154420b8007404070b40b8a607016549030100164101c03004d881c0c0b50040828042180c4044002c0c2004042c5480100010b003018000b5000064080c82812300c281c882c0c5110a00c980000c3c0b10300311600c24014003c0c07001a64540a00d500c6120030b545140310100c03080f54141034030b105070b51014010801031b9070b810a4038404005001e041c000121042c90b07800c4800c5484001079034104003c40c800c0218030b01d030200030341800c1e41c808199040600842e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 366405656 1250 366404406 366404429
    0x30c02060a0306080f0705090f0403140a03090201020115050604060c1a070302130e0c04060f030e07230105071a040201120f0b09060111100b15190e0105040e07030902011103070f0c 79
    0x1040245d40d0300c102230385c2003400c0070340c01d8505807a1803406070303400d07502200c04481102c0042201e1418540583c800541c4a000703030024800d46081c1500400e5a2240307005030b550000b0288001d04c550b5106900040c03082e889441181d01d4440a041d0321100383e001251400006500007a00d400703222145540e040041000210940a03030803c142504d50030301031170190400300140c034009000300b40c0c481d8100c5076072000d1900948036450744070001200420a0f0404440b954100426100c446512038011214001c1e0090314141c1c4055031640c001e10281c2002d80180c0c100106003c0450304902c0a02c584103031290303072000005400300d8140500c01035180c01069141030240c6640c5107201403102080c008410151441d000483c0d025040000e0505902110f000030090b102140c0d01c00054800e612001c0140b82c3c5031204429091490011580c0d8815405811240001d45c00490b00c080d0103608102c1d4100e00c141807034412080d02ca02e0051854122080603241200400c0703566040c07103948030036900a00030b411543c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 366406906 1250 366405656 366405659
    0x7050f090c070602161a0105040c050c070b0705160b09040f09021c020103060f03060203010815010602210702280504020906180616051011090a0b07030c02060a0306080f07 75
    0x4001e00c50040341005400d10307030001400e81c04030589001901c2d103d60300038040c83c1100050300e00383c0401303402401a1401145000504140540680d007a22014035001000b44846400e02c0d40f002c1664010040450340d034032800c08900e060800c000e6802018142c41154113403100e2120007040207942480c040c41005a00d843c0031000940c03241400d141c0a03100f5204c10340d60360000e03840102d008107155405540700494414001c001c00030581c0045041b03400b654111803101824007610000c90a080c4a02e4016a104072050f10800d4042d074140c2410641c2e540c2e03c40c1c10040c2c1900800e070600810290602c0c481080c0030203c003007800d500101e8020300790139241141064902008a8070910450300480c0307007803081c5079814a05580d51f408440d282c40e0640603020f42d10f0b641c3c0c0740c403607528640305004a180c1418603818204040001c000d507204814001c14041d0541e01d400038446242e80182800d07000c001e442c0c42c0000160311840000c1014490302d039000103100e840c003010705007810701c41813040a440d00071302d10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 366408156 1250 366406906 366406921
    0xc03020d0c0c06030b0f1c0201080a0b01050717090a090903030c170a0b12102f0d05130f03021f060509060913060c020d0f020a0b22020a0807050f09 65
    0x3444400d840c880d0034006100717101c2c0c10010700082c03e1000c55a9006d032003140d034290041420780f404c0e030001d0b2003a29070700c0941d02c8080b020700c00c1c0e40510048500143e01844490041038005400a00c40c11411003011715040110010408001d80341d0456805241c583d4103610416a1520030b0030340041e0b142c98800061a0301240c0c0100070703070004d06000c10594944c681e400e020b50f51000c0c414941c404890031034410000189814000c2c00500b40250227101c2a03418910410115061000d05940840c0364545091220b2070300b8001041c1c06056089030100d160200c1000410075010b8802d041d0003a0000d1540b100390003903031140d411200480f03103101800c00c1000c000035100c00c40550b8110b8001c89030b580050b540c21440403400490051701600d00c0d8108101d81d1603d5401140c0b03072039000704030f0380e0b003120320b900d044010381e902c0700303101e10003040c240fa140700044000162400c5124820078020b0100c0d0155130b1600040c2000002d0341202d20035401101c020810b51400d81004040090140c6020040b40b401c40d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 366409406 1250 366408156 366408173
    0xf06050c0d030b0406180501080d050304081903060b030f160207031a070203160c0617060d110102120409050f0105040e15070c0b130b090c0d0807020415060c03020d0c 73
    0x1a28400e054071420082029913580e045440a0061040c040015106404845010b0502840360382e081740911200700d07185a04c20000c03203105a4000041c1e42ca0711a0801680424001c0c540c440000c2698a00022601001c40001580140c40403494242d447c1410000d5944880900501c1c00556000c02c8007000003560031b01204095910900c82108507564002c1c0030707400d43c4a0008403588400c00c18101c4d408104c440c0b02e810707090b02c40075940c20100800349801c0045c4d041c4180c0d0025031025400404c0c50010703256800b103048640042c419150850f9802103440c0b915007054000c039821549a40802240300381403400180101021079051041407400040d0300d80b1030840c0000c0058410100001070710090149410380d03030250b0b10461850851404403001030b100c03054800111420801d08010410f88000010000c40020000f0442ea11003006503a90060950060b80201d801030f481d00b110000c080803161200380180303030580701e400b89113225140082c100320798500688107001207205000003041c22403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 366410656 1250 366409406 366409423
    0x15060d02010315050603191506050f07030201110a11010509070b03010b0a030605180f0a1505060a03090203010e0f0d11100c050c060c0d061703030601140c01050903040f06050c 77
    0x2800c001a9907040c5207624002c400b41901320350340000000040c0100209507001408074072191007401c00540c0e080d020701d92100d0100b4440c00c00011001e0003a01c3e200e0001c003004100c40703803003800005450028209481d005c0d4124031000c0010820540901c0340e540d80a000d00c55000d10140068902d950502039900e40380e0106005141c001130003c690180d01c14041d602403c00b80000600340328010160141601d0f502404440d4481c200f084040401d504000d5405201c060f452028000082d0b5814082404800c2d000079200004258440c00c0c4440581c900380f040722560207040340a0200b956105010b11302c3c01e03c2440320042042511404203e10302c0d40403880140310303141e0740400324502600e03400c102c0302c1e070040d00c05480d4180100070502c8644c0c60b0050003440d0601807100d05122103a55142e811140d102c0344044500190030410002e40c1c158400c070b80c64050410b8503843c03241400c901076112801c4410880d0950b50b15400010b0510110b4140549000100710030f14240346844d41041c6000d880702e804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 366411906 1250 366410656 366410659
    0x10e030c10021b0a0804090b011d060309100e0a030809060c0702010c11041b112107140a030c0219030f141e0303060f030106050102060106080a060e07020f15060d02 72
    0x881c00d07640d0b40b01d082840c0601d4403c41400c03a905840b050610480c0c070b500a22900400c0362902e0316500407540640c9901821011a4040031200c0720300c4020701c03075a60f1000381211000e015039841e08150107081d1194010584100008100104081ca00500300040180144503d0741c0003a040140007880c02c000c46415940c2880d24201440113482e141100c0350307014000c19030050401103082c0382d44217402411800d510301c07a40e5001150501c100c0d11a1a17106c080000308043d25200c00c1c2d80c2e07a131003500e00100f031154070984407a40c4401d141d191280c144000711390110300080c2d42c60450410b5103010b404120750360600a0030710546600d10781d80c50403810400e80c2d004010003603061031600d07429402e105021301203142d40c1d20109051940002903440394011103100748242c1d207900e1001420300f414428481641c20680040c02180d007800c0c0180d40d00307000203051170403003903c905021541c044070910707035401070700c0355001000207055107a0020709000a6100801040124004100b416a00d080b40789956130b40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 366413156 1250 366411906 366411911
    0x503040e10180c030f1103060f011803170f040611010605010302031302090711030d060501081f0b0c07050310060e091216020604050a030c170610060e04020c01050703020408010e030c10 81
    0x1103c503426805408204220900c15141c540001040d01034100254400c0e5004c945500701120200d005680090032a03030b00034400c0340f00341710501c0018112074031a5030585050700c0305414003600c040c09001c0c90303116801500c0012500d14900c00c840d1001d0103174002610302401c0640c2140b81010305040380d98003030200a40305940800c08210114041c0c81c40591154110042d00e40e202c401d901640c0140c810f900c03549002a011600140f0302e0524100c0445950802141801445d490143c5695881e04038085032802d0703019481c0c0000d003507502001240c20604078041d0214095140c40901428040010503060450b00141c41e201140204002104c41d0048803115150f4042044d0000c41d080703005d503030040c64100381c11000100078041034045250844d0300d034500c81d12580d00080f5403191240c0059a000700006038542d81070114600a0360345c0d84200001500043c00c04221508260948406603001404285d0025051041010030f00803051042d005100840c44c056000d000c090f135580030308040565181d0f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 366414406 1250 366413156 366413171
    0x20108071701080102040501020c0324100909050601051e0a090c0509090a0b040507020d09060c1401021b0d0c0209130c080a0302010c0f08090322120503040e1018 71
    0x80c01150080c000c44a6410810710a68440102a00030b5000c1e008883c0548910594510980340002d0003e001c03581c00b000d41294101e5a05003403201c0305001e0f00c4500f0b61b191804021a030941d0130701c9001455402880180403a501d4003050204510036170718585510074904418884c180c664105000031913090050008809100000480e064043c000d0000d91140f10101440410981500014081c100c216010800e54642400907680d80740780d1360203000410610030080204a0145005944490060401d0b8100711041070203107003240c2c8210155079031031044a220080381d19081028104251144c02c150702031089580000d42090300041c2040c1c0824100c040440422040c1203001c0000d00200048400c0084c1c00d180c064041c04201002c080040c1850120302d409034414141c40d8060f0a00901651a000d240190b40f440040b084408400303440e01050000762104010411641d0140980c014548450a00500c00c01c0514068221411035007070040901c200d030791164036160150b001c01000034404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 366415656 1250 366414406 366414421
    0x120317060a15050909010915061112031303020c030607020c06090d02030708030d0f0203010f0e0a0e1212010b0301060e06131a04081614010e03120a030c1803050a020108 74
    0x407515a000401544664152240300303940102c00f6141c0c0c42d4046030101c2c116070700c907074000c1c0c01c490401141c0c0b802c80603289801c20107140a0319450390a68480d03410b4800f48071065050500540c01640c00d020803680c1c41d07001c80f00b41a0305100712403c24800b1406480350b8100040025a1404400103c511510000503031140aa032500c0030480d160303a002e003c1e01c16041e0f44020380ca031039400040002540300e0501b1801d4182403103500c00c0345e051f030301407000c103095803424034448401c91203004200b10001903a1316101e00800301c00b0000500e4004561804968446101c00300c01d00186041e0300104000000307000511485070003120042042d4015140d0b00e440d9004180c0100929882d82d12203002404804001142240e005c4000d0084d0b030724000894101104141c6150040406882003040f40d41141d20002d40640c842c84007100c02c1030f002401c58070894059802c100140c0e00001c02800400e662303890000602d500080703581a0302c44c12018000050380b540c1c0f901a01c030462200c1c024100725426002803401d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 366416906 1250 366415656 366415669
    0xc010e010203310f0810140a020708120c041806030b0408090a0e0a020a03110901080403031d01051303081f030305030c0c01020a020c0301060812070803090a050a050705040612031706 80
    0x6441c040610a40300a95403907104d03181c0200c50080030305a002d00700c4500500040c0d40507240100c100e01e59101d4990f40d41101180094008407801c540143c2d0400c0600b000241d5a4042c900a0b610146c0b80703031381da41c50583d08a0404d80d00101141c294be0903c88200042002d40c0b1240b81d000d40c10a803401c0e511010000003610301c50b1940c211641c1c9441c00c4042c4030301c0600c1d03640941584089074504004100b0100030946190182c107201500003490340c8000350000c0c0c425040035106950001210b00e00c41d112070384071400d507242240c00710b422050007035440303042c5a0f0110f90180c0011184003135103c20001303103c41d181b40311501c0c0006414003100001240050701c44104480e0401c0d000c40003103440b580d00c000001c1d10741c40401c2e04a032280d03003407980100303415101064840c1c0241d04929002c0c40c1c0b14035030b42d0381c50203070300010400516401a9910403004c5401840302c41d02d407070711030780252202c0c60804041004860161f0440380307540c0d94042c480c200098014658460150907540302d2900340e542c1c000002c14 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 366418156 1250 366416906 366416977
    0x150308120a090c03031d0618130225151503030e0d0606031a1f052707080915010e060120190303140c1c020d1d0c010e010203 55
    0x500800c0302d500000703055004216100c05140c2c206c0c011282d07182d900800040c1d0045011410302c580c102c400d041d43d10314092054550550103650b01505043d070443d65140c802c44200400e1b40e80f18004800842084104c01d841d00d055440c0b100c0400c041c3c00c5900c10a81e440e02e29002c0101400300c445400b40726903075a610500c1c115a40308a0900126442c0d10b000b050022106580d081d00111794130100d880d030415010500020501d80c403018000394501001c00c04614140061224281104580890003140350030b9402c0c4200d00d1032300e89145904152419a18107451030428500c4604094014426500c4000b0b0242d0400d2003480d26200e115810150141307980110781c0f150050348540c4c51161107407400d1481c4551820b00a40341003154082540c008201c0240841d440740c0340d10010005031003007070301c007505001c00d1709a80c0700700504006c05291540704a03600513030440030240402590405901042101c14480102807034001d10007190080007035540e000c0c43c0715500c2203034401c0f000320340c0d8000120741440 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 366419406 1250 366418156 366418163
    0x218060a08010e071e0f0806010c05061306060b040906150c0807020909100f0f0608060402090606030711030d02040e0c18041802041103060a0e0702060714091206010801150308120a09 80
    0x720610f80c00300150942000306c0c0340c0404144c49500040c8a907010743d213070008150b041800b611807645ca070103e8624036000304404031107207561484003180c0419414040c20103800c04400004041c1c5c20a0b500c01200480c001031a0100500b801e59000020000000d031000b99074152495030f45074a585070881c0c01c0030030341c0358003100e8103127010520040d01c107840d04a0080318120781c1d4100b00d81919040d100c0e441c0c0c43c0448029401c2081080465a81d0074000015540201d0f245404c81c07100000600c50741c1554400410b01d40441d40103d400e02500901d002c8481e00705190b07048041c60416490403850310320441c00c15044c890356803400c50010841d5800f43c0400f8180c2e004004202908040348548040e41003a41c03014087e414013600400e19440a4040030b00502a0b600280115504d403001150200c1e400d0031005824642407055000680781c2c0c0314180c440c1c4c524800030b8042ca606040c0c0341800c6541014000c140889881c000b0404218020304035000c034594034846403050350b40e00030200c018200f51030f0000d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 366420656 1250 366419406 366419447
    0x60a05040203280b03030f18190e010b190309020303250b010501030908030408071b0801021e090d06050406110f03150d21020703020a08010218060a08010e07 69
    0xd09107040805100c03948400b030000d00f0960400440c1142250382c00e44c90640c16030710802404c0011094000075102e080300014024030043e82c0880070840450701010a040c58501075202440b4240c1e0b0552854050f11844c66554108007561416400d52076207042c22400f0325950b400c4141c1552401e1042b602200d4010f40d441400300014007014801020711801507072401c0b80c00002250303941c4240107404105800050041c21900d441e00c8401c010360042034200e034203010203141e64001c0280c1d040d00d10024100b0900042c1c0b5003010000356071042a8640003002e07042c90800903864507030341e2818861410764000c01c00146907aa2880c0440042a01d01420180400d020032100b0b8031207042070044d842003001071800e10380d082c038101c0be00c03101d82d500c3e0900401c91120300d920012921a1054414504000740c03045a0581e5034076008240c040c48590402d8400fa50005081c642004c2e545500e250031610542d001468113140d040001c00b03114060080f06c07101c04c4450003041310320340304440840072078400a401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 366421906 1250 366420656 366420661
    0xb160c031808300306010e01050c030403060518010b0d0b1b0f0409091208130f020112141501050403050a060c050f0a02160608040512161a07020f0307051203060a05040203 75
    0x21030100d4050b410000f03000c90b5a1000811091443d481134900540d0107844802c0d000c607241005403440c0c5c100041ca20340a1109110000c0498600e024940c000e90b1151100c81c041201c89890a01f50b0306040b440d58003450b004050302001400100e42103500c1a00e540b0085050082c5000d0080e583c403c01400c03900290001c60b0100310301c002d81c0e000c42c11203481444103c502c0a07000c40c06640c1a6002c44612000d04507036814900405c5003481c203038000034414508045051380042ca694111200030281100f1501d83d0703401c100c5070520ba00f0300041805024240035090600c0c5565195403220302010041146403a54120f85001c1d00620559001c10703005103500780c4407100040002d40e20b041c8a6425411000004400541c05008500503400b580e00107020f48162815520340020340c0d800b18014200ba541802c44200108a14400c0054000d8103d09a4140f5007082140213203842d40c031251002c0c1a4004202400006c0c1000850301d03407201061401648a80d1100000b800d0070303e4a90149400c107000004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 366423156 1250 366421906 366421933
    0x103021e0936060a0b0d0f030801050f030c130c0c0203030712030c031a0f010203250b281e020705030a080c130b090a0518040b160c031808 61
    0x86080c0e0521070314604214210b800c1452005003050030500c034a40e0000f40110ba110fa02c9074001140e03d034405417003601041c03000d03924090140000381c0c0c250000380a00b401440203140c980110a0070070400c40082040c8a8104002800700141c2d4202000b002d980d01e072401400c030700604441e0340140c3c0040c152030301c0302c101d070910142440c14095220700007480d1140704910f11b4064840c4005052900c1c01001c00c0d030050205000b081c10418480c2c5044d40300078051102034520581c40c41d01c044003480c1c18070b003816000c1d10305009801d801810740c00009008004585d80200301d005e040140809039200440c4101d410501c0c0f1152a1400c0c0b59085401d00004650701401400001091524025a02c3c0b4a00e95540e002c2100f0f103004100d00b6906080341044100608002030b0b0141005450041000184559403000035844445d0b044112903118205010403080c040880e01e000d51121044480c000000c1a6207002884402d490f01c008041c4060070030703032504260031440f642018050384811200403031020b41c0d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 366424406 1250 366423156 366423181
    0xc0c0305060f0405060919080d06090501060e0f04020f09060a0905150306011e0818011509050415020910050a0c230c010311030117190b01060909020c060103021e09 72
    0x44040d0794502c50000031540c101b40009143c4c206c1002408000d2007008156200407180c3c0c4040030041d441034664038007080c450b98a106260007800d0039159048012100c0041c00288150000882c0c400c0c0c0c41841000e94401c00d0000b00c401800c030803a44250b0303070038240005444e959010b80000703810840f415104460400140c00450003001f01341c84081d0f200140381c50f0b007000c9008880c441c1000810110100da542201c840b0182901c2040358000304035102210b514050000072079101c103070020748a07824001400014401400584083da0003035103000d450f10003040304820042c002d00c0400c100090303030700c2d80d1600c1859000c40b0b00b54803050b07600d0300481c83c014021800414034089070143c0240900c032483d641c02889502400b03140d49d101c49003940c0c40c3c20501c819071507409030741d03c4843c018900c2010503880100070031031403c4e100f0018468a941040700c010301c40340c090782218052600c1040801d01c0403000103146811640e0488242e0319100a4880c2440009560304d0f68a400c070004030103010400e003089 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 366425656 1250 366424406 366424411
    0x140112020607060c0c0c05120d03021303050a050d030c0f1416060e010905070909050c2e050406080610020309040f0f0c030b040c0e01090308070201020312010603020a111c0c0c0305060f 81
    0xa810580110340c6402c100003609451009008c47d0783c1c02220154a020f00035000b822000c00c8240600c0b108580e207884003405c148040f00d0850f00d94002285d540911505442094a2a9203a103001c000b132008500000d002c04120b002000440c1e18003040e0314003c90b40c0c503000b150035180d00203404c0c8501c00110040c98043c00c564801191503007e100e6002c9149052407140c03d4a050f00400100803008840302400b000c2008050400000d0f030304034103040300c0b40760301c0d501017003103075640d47c2c0d46a50311441c2040080c030520740a4041482a080004054086580081a03445800c400c03140022100455540c1200400c440d6040e018401c3c1020b0107496000d8056000a4083e1800d44060207c804404001c54903074142608803404074a10786070500125a6401c0030300101d500c180102ca03e0021100700250b082c80099000c440040e4000894032002640b1005440c03655803200300a04c0245035003200303601d201c04c00e10f00402c00c02454080311008e200c400303101c0000542d004400e507419400c003a0000043c000d001c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 366426906 1250 366425656 366425663
    0xc060c010207121b02150712020d02060903030105061b0109021f08060d0803070c0327051306030305090d050c151e07030207060305090309031c0210140112020607060c0c 74
    0x110240f14009402120b40c00403d00140b20b040d10510070315803c00c0110048034802590b480418010000010822444030010010a40050100310f0803c10002c1c0f030b001c40103042030815001807004108a45400c8165505141c1529802d82032402c01000d55006154954000c2d6010b0010f65042c000403401d082b11130801c09040e0744000042c0d5880041c011802943c8038005c19911041001640360b502c035020020f078580c460b14001c07a0703e031030792403880c12070b01064400b08030303015541c41d802c11441c54803c01130012120492424045140785171405491801581103160058600502607070800c4400c0c1f02841d1450001003005c0030f60310300e1038140340c1c0d1070300b040c1d07000e403462502140040e0130070444206982c02640c1c1580108072143814068220007030711380980000100c2c8030902a4a80d559810300c42051080c103038071907007514001d901000902c0e080d910995108400d01c1d28948001c100340c0d01c2c0419064401040c02d800b1031481a20100b41e091181100c05070001307280c00b248501e1700d43e1203011103220600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 366428156 1250 366426906 366426923
    0x2030c0f030c03100f0f11070b10030f0506060a090903020a0623010b0306040b030a050606130b03010c08090c3a05030c070302010e01030e0c0f0a05150d060e0402060301170c060c010207 81
    0x2a000390b143c04583d140300260035400014010640081d06034809154002800e80d408ac0d50350b560317942c40131030340129140b0484098008400b04801410600301f62401031a4420041c002852203880294641c8466140508440e481e020108010310b684000340c80e050180d9100404a90780d191103109282d04280c4a0900c55404c0141e07890041c81c000916041c0c0c1500080a006103441d03001c100f0260842c6000040c400903250007114101760b8085c442d42c60b500c07416403154a41483c01e200400c2c1402840d1040c28030415101c4900b4859045a070441c0121501e5405800e4000040c640c912012000c4404000c01c90301c00023a040d01880d40104c0d21504807807007a2206800b013681e10b40150306540c046000c440e42c81d40000d40700d941030315001d5051010440f02811400360b040d10b480119064158500c003018101400042d480d00c04031251041000070f000f04101c908031401c081c3c1c0000c6242c40180f1036603074000300541c2c841100e04d10500080e001d41070300a100550742e10000400501075000789105860700203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 366429406 1250 366428156 366428171
    0x90507080d08070f090b070f0c0911040303030e0f010606090e070807050d150504020a05040e0a06050108010e0a021303030801080d080907060f0908010f09021c02030c0f030c03100f 79
    0x10005462440c100468495000a58860720104c4a8542c503050302004c1082400c40000d00c07480d00c100400040303002c0c641810000e4028107100c146a4919442071101500d444040c40c180c2031200f0580e000d80740c0c54035000c01c1c1c1e4441c1900151a1880c4454050183e519000d00001e0042c1c000108004070f40c0c01080315603883d80c070000c0544a4000071902c0d400802c90030004000340c0481503101540c1c03c00c0c04080700b030740c113034680c0c0107c3c04030303000112100040781c400501030000895507956954003085e860001d1018500b450f00003025106c1c18400d01d5000500840815040c07081038050350f000c2e0407400c840b03200c019580c1c14002e00c046020300c80c040c00e5005840d01aa12907214188a600c541d000000400c40c00d4589030040b22140d660905490411500ca0401308030884203004a00c0d000581000114501d050f0b801081602841440c5d8600e00e42280c148940050b1804a212118200c040f00c2414000c144080400c0c10181d90101c49031340b500480c8001c4040032965400380e4440c1440310010818007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 366430656 1250 366429406 366429419
    0x70e01060e100c02060c010507050a030e07050d0f0c090504260a0c11040608030c0604050f030a020c0f040207050109061d0a030c26040602150609010324110706090507 73
    0x7402191441e5070412150080104818040e4410304541c0c0d201902c0c5c103180c2440c0c00e4140307003168000d494000c00035000007a212541030781400794286084a90f0090101d03240381c98001000c0c4145000c6c001d040101181c1da120901400c4420440203241c44030046c041c0f45094136010039009018102900b40004003032044418405c3e030401e46501c1c1c54036441c1d03001420b074207841c1c8410100b45029856401034544a0229243c1d405201516482c00c14034020304e9182082c0c82c06c1810468900111003042e40240300300c41c7c01c10307400951001204d0b400d440d00100c880c0c81c50f0102d400f912030608080c01c0c9600b003201150030810140d009a03080001040034285080320001c0d1240c480350340e604040d0008401807114170200c0c061a0300d50043c40762588600c071003d103150380550400e4102d90311450160708a82410401030541050b042c0d4403090443c0d0300070f0030358119602c01c2e1019061803001010310030b8400c4140b1101800c1d510000b01034040d942da0031740351b2166140c01c3d0042c00200c0f404889501a401000800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 366431906 1250 366430656 366430667
    0x3070e0402190503030a030b030c0604081609140708040615030b0609010f1d1f03030206090f060106210b0306010b090316080307031d06030109020403060c080402060d09080702090108070e0106 84
    0xa650000b005141b41c0704044004030050801103940030392500900300b240450760784860040000b080400c0140104031071140048555846c80e6026030012404c0c11010001070064200040d444913240c01d1070809615141050401803000c528a1510004401e0002c41400b03c1543e8090ac00d2608403803400c210307038982180f0340503058544114640c040f06604000b1150307284000e4150700c903010700b0808100029035100704810481da0b520139401b68100300c0a10035400401d206400d0507001100040c40d05500d4180018030500d04002c8000c501c1c06443e40265000d0155000040d000310001c0c211503040d42c603840030209550040091910070300c10b0143c0d00b913145030400340d41d0040b20354940166003042c035144c800750b80343c000301c04408400c0078040314140d0701c0c1c2d5181d1000c0c0d40038001e000d000503151819881c1003411100401000818401c41504200050351104102d0b072070f0519648001c200c4e10b5403454980e10a00929000035403101d000000070400b2080000c3c000c04450071003010101c2660382c1d10041d50b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 366433156 1250 366431906 366431909
    0xb090c010f08011401030207060606050705160303091502010207050d020303070306050102070305060a090c030b01090c200a1b0f0801090c1509140604170c1e06030406051503070e040219 81
    0x11800b044010005180d180c0c045003043c80041c1000344c644a482d40e941c60845106400c0840441d42c0400e2500030f0201c1080728000d0f40e040b07113941008090841d180500010a03612501d054108556952000c540c403c4d0151500304d9400700442c0c040760030800d8040d440c6e800c2183c4030400a032030301d00001152340c4001014011039810401804458031030948840c003910800d9020346201407084000000036080d102498001d0400100008044900b07000050014415010400c80800500020800e046001c02c0206105603c40c03d012404802e2030940d0311610203a5028042a100600380000c1c81a0107400c01208148a1b00341d01d0311580d1103060305840f40701c0b840ba01c1030010781846014000c0038410002449400d80081c031803400c25944603103100d500704020340b91603915089900200a58144407000007200d1800c58400da21400034240404c240780801070020300110340700c2000c80d4078603c118000b02c006c000301400380d50302d0340d41b02c00d61014081c0003568128000c02d0328510a80501040104007030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 366434406 1250 366433156 366433187
    0xc10050f16051903060308220f23121203040c0b040f0303140d0f0b04111e090a030f0f030206090a030c060e070b03010909060f0b0f0108040309050402070b090c01 71
    0x50030a8192249100300030f41c01410f04081c10341c1c03501e01101199170007018250010814600203000840c0400c0d0180c01040c65010004101c1c81d04024005c0b00003148081c820850721201c0c100b4549200c10003c2e640011b00c80c044499801703035041461003022003000542c4258041d080b0221608c2e52101031180034030442c8202c412901d4809400c0c00040c2c842d4900c0d00b401c42c14a4901810700f2014012002103c11428103190116903c101d40350b490304060044a00315115040c050742840d00461031161180b264000c02c408440e00010b440c1890b559041001015540100a803440311116240c41c0c228000981025805440703690001a901100000e04440d5241e055840942e034101568860004d0300c00107038a502c26009218000c2a801c00c0007010310300802a014000c070701c0c0d80c12400c1000403a100014030f0b2001302c0c10610300b110b940d00d40b07120403050400d0a00e001c1c80c0a84d80d0703060444074005c2c00e130011603026000040d84420310000c041c185008828900580c0c071480c0142005464083d07070b01c249030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 366435656 1250 366434406 366434417
    0x2162913110328030908060708090c010f091205070e0a0c02190f022b03031a03010501030c0302241c060b0705060a0f1808070512210c0c10050f16 64
    0x1c010f5124004840324515210b418202c48440e03c42c40d0320b908100d4101d03903000000301030404001d2060303420444804140700c2803c6c041045c10070020001c101c4a880e0040c108240502a9000b04109082020b03100501c1585000c05040c1003031004040945000701c49240144191070b080e1602e20014803401c03150f2640072801c04a034503425424095001003440101001940d030801cdc00e8041090070400c2c0d02c000740700703580005c0c00c1e20b43c000b184403018902800740350081e803603c00140300040e4445106400d070b0b0340490303e60701c220301c7c1d20414540c268000030103a41c402d140880c611051080382c04070040c1c45021114103200c40c07031311a03200070f40307901030000e0180980d4005004201024000e03070200700c9a001e170040104546d082c600c001010348800c1c200440760800d000900d0f0052003014040131441800c000d050320310b00f142c550200e0101c0c070b2044000d9608004030501040040c003101c000c8443c0740701c1c00303015030b0038483c21400c0d4040103000c01c4170300010b101d556000080c212205060000c07803600303003510350 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 366436906 1250 366435656 366435703
    0x11160b2a070302090402040209030a05071511060406090f080417060105090601050d05040c0f0f090609020307020a030518090c03071d0d0f020a090e1c03021629131103 73
    0xc0060310b01c4007510690700140c8c02c01a5454079101440030158540c0688000c28545103441d03840d03100c64202d903903054104001c0c000c074682000700c082081c5030000d40152010030403a51600700918622000c2038002c3c6003c80c006400a003c8031400441d400351045c000503943d00c4d13a42c80090040c102000c850303103800104100540340180300305500c81b98100c1d01a00d4419190342d103984001b55207400b1a003000d10180b00d1518100200c1c10503024103009404806001d6003142400f03d4040d50700c5480d40402428000b0110f0003115004940c0d21220000500801c45d401c0ca06101d001c0100691007902ca04002a5229120460b030041c03141ca00c0c0000d00000d060a0b28028043d19503060152040c20304990182260724009100d0103d8002d0103e07900c00c10f000703003035030840a103480092611800d1742041814014440a039501810710f220780a0650031100070001180d034901d100381e00691250068035a4035906003130100240081c3c0a202d82c4901c1418000e503c881d0000406135140035041c0411a0008803519 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 366438156 1250 366436906 366436909
    0x117100b4e010c1d010c0c0905150913020307171606032301030b0a090c03020d080a0f020a0203120a02010b1509031501080318030a050d0e0a09020a0f11160b2a070302 73
    0x840c29104d80034005040107e074403590003109441c0c0239a014030b5401000e42c0f40c2c00980c40d09080d03058004040f44503c0c00342025990200380c03208403a00c9160211460172007540382000060143e14031407400049101000f9840b030602500814803a182429106000c0c0a042088040c800166050700c4c0c004514081070355038042003a0140101030070032196a1070b207400c0040140c43d601c3c00000d200d4840e20340c0540b074106007a40100f01c1c02407222181d04540c04611006c0140c0c40110314002c40c0d0384000f1b110395413540b8048040c0d014092100d6034540050002810b510005400301c050218203000300c09803081d00c2e03105100c21120280a01544046400811007102d544240c20212240048086d0036510031804944549040c00010420000030820314140341c00286000c803c500b02078030300e02d50114100401d40300000c000811088964040c412004200581014100124014034000e0340010729040d855800c8404260010b4124030380100c104a81004070f01c4085441c1030742030300041c0007004414034580 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 366439406 1250 366438156 366438167
    0x4060e010b1e04150308030121080f031e040f06060603020a0504090e010b0d08130e0702064c08010b030613020406030b0117100b4e010c1d01 62
    0x14541c0f6031140e554110032004002d80e1040c40c0082d030141d06001c0e101c0d0724203210724211401a0fa0706044080007030305200c0000d282c2070191440d504842d040f00d603c0f95113040400d910003a000640c200e00300c2c904010401006418418451a0351040c50184490366407081e040d016405964100713008650309000030310a070052a07100c01c6c00900e0120000c40c51280240200b0300c5000e40074425a03804000040240e2850f07044916240102441c0f8040d43c4c817440c7c0800000d403500c001030031403d41c0c0122004440d41c2420241c0203800c03401c42c000700307160410784032034030b561403a23500420ba043d071250407004001003210041c800c0d403d1008000c2d02800d121b90703e64980c0e001d10301060301c0490303000d0b60356900400030903c010040d9001e01024045401c4001c1e0a040407803a1110070b8032503c09803800c11440c0c5a01ea26000c0000a440030040200308400b52072014004480340042d150101910211380c04200e203241070310b4420040c520010080001d4440c10f28100d406541000244500e0024824680a40d51060 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 366440656 1250 366439406 366439459
    0x20904080405100c06050c03011d06011103030a0f1505220e030403030822023102160b1003050309210115170312010504090206160302030304060e010b 66
    0x1500d02038075107a140c1c0000741c1440118007400f80020482030f410310410002d403241c0c0c0c0d0402c502c1304140e41036600d000b8106282e28082d21342c59040c03000b1400450603990041c41c0c1000d080b55401c1c152501c07860720780011802000344060b00c103003035814404c0560994500d02e07115416548054800f915111120b041c8000c40012004840104c96442c02c250726000d4040c8080e2001d98030079520f140c103d00789402c52613104168014881c242440b00000c08005035240000000034030354642025441c034030b894500131703400c40c60108465545400001d1840c0c0705c2d51142c8140305040e11440a2401c03940311600b0709942041305000081041e48200400652450b012020585004182c00e0700c0b14440c5100103024251056124501041c1110640c14401c110701d400100100300a100011420b00e000440106901c4806202e058050355032a03003900150345070101194034190802512500c040f81c58600250749074011581039a4081c90b0001d050a100810301035401a00c1d0000c10704498145419001042d80038003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 366441906 1250 366440656 366440663
    0x50414090907030b10030b060108061f1202030c030f0c0c030a0309141f0e2404020a0e04080304050d0e0f12101a1207060909090606030c080607091e03020904 69
    0x40070800000903201040b41840756108a21004451b0b145241c00c0900440c060405030500c50305008204458503980c5011003500490382c2408071168031044299011f90310803600d000c1072030002007084080d08030000114000d1002040340c940700d80d5030071018540da00813007144a0090b00b0411503102d0aa1013508994100c074041c030342c140144580403415070702d081841641030341d4010304214801d500b2082c521410303010541800c05000d0f604604082821003550400354060202c4241022505645500d080b510140038a00c8000005062a0420803034030b802c21501141c3c940308205144140f1842161aa0600719021b481c039110084071408002c0c0c8051219018078952007002201e02040a047c003c04051103034604040b44d048201d0014030640c0b0001841840443d88904800c010f2140e1080ba2601211110000000c00e02020710f003c8000c0e0007503030700184c4000d150a1001c211a00046040b0b4091213081d110400e103155160612152401d85080c42c980710030b58103a040015050000c860341c2d21922 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 366443156 1250 366441906 366441913
    0x80a110307031a061813020301060b090105120a020c0a0c0329190b060a17010b04030b070f0909020415110d050f07030905040c020a0201020d11062404050103150b010504140909 77
    0xc005240603640c1c01b281d12400500c415258001581020b10908025041051a0754902818900040c3c002c0c86074000f9040300f01c113088000740020070141d040e18460041d080070b54000e807801d410440d450030558081a01c2084d01c0d039060742000019080420141800070443d25000e0b60f42003c880c0c3c030720a0540c00848440e848032080f00701503036640000d18036548240c80d0f014900001c0711000140c200160040703540c00200300410b2020400d0340a507550300100324581318400c0161a401100c3c41301490b8010a901400441c010075102680d80780500c0d0035441c1d50311264445d20380b10b201ca0b900d1b00755480007000705004002ca803400070554001006058002e003081104642c3e200086012103c0c0c03071a0301c0c0c005804c500c140d40219a4140f110b1003039000c00e80b50080444200d0355038107486034009080d02c90302400b41c40309a40b08200d0007844001070000103200304819a5030b2308050412a06018142c0b82581c580f010b409140d44c0a00c0a40707007034801002e2101ca1a02d07075007080c41500036015104072500d12 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 366444406 1250 366443156 366443179
    0x150109061b0b0f09010f0203040507090b06040e07030b15070f12030608030c03030405250b0706110c010b040b060403080409112b0506010305010b0a03091b080a110307031a06 76
    0x1140c41107180e0054983c02c4180c29070b40341c06070443c0d003100d525001000c0c10074010024040412400520401a81c0a00758002030405148000507014892a84524000000101001074041d00b6610083c1d060506452000c580502c03490081282d00c0b03480402851030614003119801300d118108959130894044c1000544c1945410401c0c4c6903402c925110301295200004220420000744403048007500b402c0844c00c5030007101c840c98042c10901c0e00801105050118a040621026410040c4804588030400d95610311012039240038006072050240141c1c180140300b801420400100c9088941107601c2070b04081c10076a0320005000524062240c0c0c0400340039400d90030710310b0021203d24070a80c0340c5d0600481a1001b400c42a550001c00160503d864840108440b001200446030211110701e40018082d50b44d20300170b0502c0f20200c83d00703040c1c050101000706904030300040302c9400358001d004000e590720140302003641d01c0c0311502000b01030a2860000c0480b08908068882d04290000c11424410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 366445656 1250 366444406 366444413
    0x9010507050306030a061e090510060b04050312031f06080403020c090114060306030709050f070e180412030608011b03051803160819030204090c0305040b060d03020a0206030c040806150109061b 85
    0x94120722009e6480f6000200740e003080703c04038440da5006144050a107400d05240c100003907190b60700c2d60107100c51400000300051000c9074001183c200780740800500c1d090940c4800c030007010f8000440741100548510344580350a494007520041c1200d8140c154001d800e403603c01807001c1c681001e890107815206071503012565840c0e9018551103000000b203180d0141c9000c9400500f101d02c0314032001d004147c48040348000500f0787c807003142d0180d00905922913a14032010100c006000d554066442e80d4078110405404040080040300c0c880301d1640c007030000e5140c0c4e10310384c1074010503d00b0301581c0390b00c1001003034910b00240c2851200c09000d400240e060406540054000b100310509190001c2d500180900c200e0070325100b107030700d5031a0360b01c1c1c1080b00d032070180e640780d85a0002a1456200b84d280705840c00400d03200300f11000140d58003400d025100d00b4002c441540c1908940101d44180c000e20000403801150751480001800059503840c05603483c1071000c2d1429036025442030061001c981400010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 366446906 1250 366445656 366445661
    0x2120f0607081005030a0305180907030203010503100204080a020f0102030708040e04030f0c020d020906060708070b040b010608040302030405010503100b2109070627050d0b09010507050306030a061e 87
    0x21800640040c200a26001c0300040034018010521980761080200900203501c00003509044a031303060401c0340c3d40b850002c3ca1002120011001d999100c0c10324010004110761640185040303e106400302e41588200c2032103601680038034060000a0382c0942e1034003016250107020250500c0060050300c0c502213a42e02c3d582850751050300045980d111b000140420503902400e00c40055119140c0500004d0f540d500281c5840100000684250982c1c0041403482e81e40c6401c444081d42d01441e802e40c2e400c9c40b45001c0d080301c0811601a03e4485c42c0030000900f40d030007002407038130440d455400385241c9420300c0019241d58101610414141001c00400310303810b90801c0060104210f0003080d0080001415101d0061120003403c1105a40000078200f2007076421444d0500904000d00e0381815803c003101d8004102c0c070706607001c81e5010f031640264009220600d10558080d40280c0000d1101e640c0c2e0f550191418442030350900e0709503201840400220301d46030310007607480041c030075800c80c10a00b40801206 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 366448156 1250 366446906 366446923
    0x9053a060b060d0603020a09141306110c101109030303010306050702070e0c2805092e1205060a05010e0f0111030307050c16030317130204020f0706180c09090212 71
    0x41040c0d40780b5042c421b6286c5140c9650060050040501c51444038111201d40001c5c0a0800c040c00300c0d50315118402c104080d000603410190b018250380c0c5030a03013080583c0e40c810904c0780ca03160071450128802401d42d482c01c1101c0f100b51000e00214a903074a075941e020003c2c900203260200314000d4500101e000c204210041c0d00a44019503035545a001528034400440e600395141d000107220f008000407040d40080503a404082e040340d9462000280180340c1c9441c01c00529140001d007010002c1541c40f6030804168017449140b41d2042003169103010904c4007802c0f20780100c90100d1465413104210b450050fa0b194010b020616256407801000c483d01480c541042e900034020903404100c031380d5001400c101c042656009050420035041c510313203025028462542d14000c02c00112030000e095681c503075078152a0654081d20840d0359a00c030000980356070708140700c02c0303907040d0401e045140a0710260302c000c88000e410080300280c4618000c62407005140c4150100d0b000100300403030411660b030606c06c1d1207 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 366449406 1250 366448156 366448177
    0x7051c060b07150501050109050d0f14010603150203010e01050913050f06061201050103020f041d0a05010b0103060510200c1503071e05030f06060d020a09053a060b06 73
    0x40d00c0b044280382c8040d10f8440800c00d10000e07440c0000410140c1e921101e6501154000d5445a040e041181401190903540540180c00c0c040c102c490031004900550212007107074050000e2902c0f0130180014070b8240e200a20030130b00d42002080042c8030074540031540791b410102a21060723000c0e41030741d0380b540e04002c44a40c80d210550000ca041201604201411201480348440200902d6055600040710035242d520311078040e950310781140d46000102810752a00fa66854100ca01905507450118082c041002031940080e00344000024030303041440d000f036182003081d11941c810400c1041c01902603489403d41d0b103030505c02c800210226844881d03141007040c0300b0780718031036a0f4580703070070050904800c88010394100b580d4006864002a40142a00e400c4441140b541495880e0003001510600490201001c55840001d210001d1a000072000d001c5442c02d0328548804407402441030024131308845440341010703446034800307004600d001441e112544600000245a00c1c0b13600414025005151002e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 366450656 1250 366449406 366449429
    0x6080d0c0b0919060203060a0e0c0405030d0e100e040f09140705030d1e021c0305090c010201180b09152409060f0f0d12052d0307051c06 60
    0x501405190208164002c100300d0003012190200609001081005070003d04501ea001c008104a81d91b240725503001040248042803140c01d064400869540c820310038036109210340448c8040c2c46004820001514600803d01050002c41d036000f521a95030075034189030f0065498410030f401c004a8440c448580b0300070214882140c007040004c0c0c0c40c183c05500441d11a5001c24030030300059900280303080f0106480d1b041100e40303d8509000760700d03007140307808481d00d20369035442c041c1d01c1c035541503100d0b620800d082c0c402c83d4030300a00107006900301ca00e02c040c1d5100f644880d8000c0310200d400700b08410f420101190840b548001011101c0c01042029951400300c450181d001e0051140050701ea0400000308649076411030030018002168000044082d501030751508204265565030786814a054a8000c2406407a1440405004003540c1c00b1804100000240c4240d40c0800c0d2421403003a880c0c280014001840d6403100c00c1d080e41d168004840610b000031500e100c4000980250050400601c1e840840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 366451906 1250 366450656 366450677
    0x100501030f02030f0705070809060706090506060f01270509040f02030706050a1b0f12180806011505031807030303060905060f0f09060301020d0e0618030307080a0c0306080d 76
    0x40a0740c11203010741180794014014000180c2c0072a11043e003007021410a0356070fa01c0649000c01540c0601c07500541e200e1000f2501070180401c540200710a64403900c2034410540d03461041004c0f004664000b28005004c8040034101d22a64200603601c02c035000c90420b18090755140054051042160300322106460424440110304082101c0e034058045420b08500307200c400d803401405509152030501d02552072a5184041c0490305500710341d010340100c00780c00d03580440d44019104401d00c3c42044a24205050001100c1401040650689103034850030100d20358206012201a00080d0098044138150100c2d151401c41c1005180001c5200b0345020039882e241048400480d10014001c9001d44440554051541d071010000042d060040f01c00c20115100c03d80400e009009000d141c005440c504007007410303641070020b40030344285020001000d00c3c400c001d520340c0c0c40c1d0000f60781550200309a1400701e0301140c40c94020174810000c5260010310103568a200320301d418200f40080f0041108602d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 366453156 1250 366451906 366451909
    0xf01060e030a24150b160c0b0a0c0b070f05030402040213180e12070312050a11070804050907020c090f3c06120a0303020f0f03090d020606032e0e061005 67
    0x3044141e404d411083d04100749000c000c000c061040e21500110203401da4908010054a46948005020740e15400ca4541407507080c0079081240e0013205841d80b1502c100090303020b920074079120091411640e00c440c01c6495079401c2c04040d4125100700818071402d41030101d1110112124001003400103c80460384540e1031501c03a090100c0f48807100c400c00e00130416040440e410001610300d107040e0001c001000c0d540c560343d03080240a80e00760707544aa03900103245018024070310013810603144200d44401c010f448440c0306070f81e207521542c0807a4001060301c0001e259280c540c802d442c0e00079040502d0b5101601d108070071005800c0a81201c0441d00071641c0c440b82c0c9022204c0101c3c0c0e000c40152481051038042c043d02030365448403090014201500042c3c4101d11115080545010260807014583c980c01d02d00f401640b1100841c140744018450100094071915001466084070703160482580041c0103200181504070440100c0c100c0019268800900c0c04d48080194521805054401c02c100a00f081e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 366454406 1250 366453156 366453161
    0x303190909090807030f18090f0f020403031e0207030b04030903060b030a17250b0403140f031b0c060f090705010c0c0e070c05060f06040b0402030f01060e030a24 71
    0x104200c00741841c0c00010000a00c4800840300c140c4d030581094204452460301c01c0315040300300ea1180d200c000c08011300090218180e00143d40000c0100000c2c413a440c00d01d040102280158840078000a540f440e070488040124103000b41880498419a02d2a688903102c10901c0300081d038084000806140f001c200f807000900c1524440c00003140a0b06040c42a0b4894154801980410a0400100062706c81c40880085284050f5410645d4030f060004801c3c1010541c5e100d04850035408110034091030400800d0345000c1744d038000320b188010380c110303111504800070030544500c030680c0481c010000013001003410040ba510549075a41700e011685007030240c4c1410192540d201c00c2c10b000000a180000035070212002096460007091440d55039a4098200c1e00555118000b801d640a03284c2800b000b00700d5100510321a5005607810b101ca5a24201400100d2100300c2d01c0140320f10341035005202291080301542020340d8001c04503440c10400f41c03601d4541030300c914400c00b01172000782c13110070400c2d0072030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 366455656 1250 366454406 366454409
    0xb040f0f080d021f0e100e010b0118060518060c0a020f010f1b0206040522050c0a0c060f0b13140f06010906052a011505030f07060c020f03031909 64
    0x1000941840d40288101079130701d906040400c2d503040c44594402c1d61210a55021166005c009411100003044202d40c0034020190004552880d5090480900b90340d400740b62051407640d03400f101890214902001107407240c000602c2c0600f4480100d040365403d46d10003001e40010040707080608042c500d184108080350700c004030020306010360983c620940d81c1c1c2010443d49030b628904400c5040c00e1180c400242c491081d500700d0b035801290301c4030340c841850f001c0616110f4400361403c204102d403118030b075481d0203000b1200d084001403000040c3c0300000e800d030341222010070494039005c82c0c0303603903940d000032004007440c121104201d541d4401c3c0e0803c0550220100d0b049014405108810309007040000c22020072401081300748030b000112074182c0c00807a04104406000341c400808211a07036101e4134041c200d07150b5a9441d000d004007003c146882e000c03541a0000c0c0c500790042020381e141890aa4004107284800d9034000122018109070b070301c0c14030082a01c1141520321840e24840350202900101ca907 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 366456906 1250 366455656 366455669
    0x3090901050a27061505040f1e0314070b0d0c02060a180b0414030301030c1e0b0d0c050d02192307030c14010e03030a061d010902070c0b040f0f 63
    0x600811621000110302d0602e0f0600154140403016800000030241c0542d51084120070301d00c0140300c010580c004060000e44140b110000701c01656091004529100d41c3e9104501c0260010704000280d29450081010758200c0113031440c40d40e444141c10704507008540d0151142c0e4480d04030040300d66050103083d42c000312003001004190246042030125280c0b80130000c2c101c4155401140038441a902c060794080c82c50011242e50303686a1400703061103441885501501d110466802042c0c0600160340015110b8440d0310b50f041000b0a01c044014001034103502051003020461032088424a0000b0301ca0030502c28595115a4244400281802402c0d14100744481c80301d40c0002020600008036100b1540510b0800e03000740b098180400d2144594014012562030300345c24036200c03032001c8091403050407140000c1103911354500140c0036490801c6040943d2400040051040442542c042c046050242881c0704591f071b01e0359003091082e485500a0642421500c00030024003200c0c102381400742c0f10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 366458156 1250 366456906 366456919
    0xb091807050a030c140607081303020a080105360f0d1b0c0306021b0a030f020d0c02010801050603090102130b0304051c0503061201180602030f0a05010602030a0c0615080309090105 79
    0x15640b04c100c89040107002e408186648001503159565aa0040d903081a421100d41503854100c1520002c04e00c1c40c0344001c81c004d528100c0002031528040c07042911a01010880000c2601d0000210510b44041054840404c03a044c404120b2440f003044451000300f884c1004004150040c0d10150486201001e5991698200c0f11000006003481a0940440707500100243e00e9142000310440700076401c4162040c14480c440c0c6807414580c0c0403a01281d030b01641d40a464070010000e0042300c9100b0503038800b07408111038000400060414400071940080c61200040c2412404100781d50000d19a0703008912031000403040c0000e1017412701003601d20f83c5402041c010b0060107400003610794000144140d00c500710040081c044803a007034000c00241c0d00f81280e9007900140c64030f00380c4029003095801c0c000340390018000a100d00c000d841001d042c0d0310b5907001141000c02e042011151448601000c40320942c0b500054070400c01c0307070003e0a0150252002450315074020350284541044140c1c0300c1d0340f1814 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 366459406 1250 366458156 366458159
    0x20a0509011a09010509130c08010506160209061f020a110a15030504030e03010606020d1403090a08030705090a0e04050d170105060903010e12090a0608070e090a0b091807050a 77
    0x21455241e00d002c105801d030710795241e4000100607140c2d80601408030340c008031303984403d00040c2c80e594405c8451104940f1103080503603d410510000703004503010302840c82080040364001d85061020b0b598806001440e82e81141c80c50383c12842201c00d0b800041016a208001c0101042440354030481980c13000da51142c0c5980c42c090001d0700342c1d82081145014903a981020605052058180c40ba0904001c2d000f44442541c504009544880e00b000180000d6501001c3c61800c8000380101c034020341c0c002d0028643c0a99980380c1e245540d10180052080c8081042100e0080c0c4076801075034020700800350110400d00c0c00d820a141005200000c4904203c0c4541c1c0350181e0500050809040d240b095441a4a80e13100b01c1c0031a004016907600120b05220342c0b00356420701460400107154492041d900560241d1b07a40340103641280c41941c0c007501145444110315031600780140c1312070740040710f09804540d96402401183d000c490a80f0b0043e200c00e04485801d0140000b002800010082038840100d243e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 366460656 1250 366459406 366459419
    0xf0a0b0109050402060d1a030709140103030503062d01140327150115020f210d180b0702070f0302060301151103280e060306090403030e1207020a050901 67
    0x6000501400a4059540c0c01040640d1149000da0301c1b40d0701e040c007003009060308007107159010040250341c3e1846480345c840007140c00b21440c051801c0300c1e05c0c01100c0404590a5076810761f07003504010800c90304800342a8400351048152100c1a01c043c0a00b8411107000900c1c2000409802c1600300c600c165460800031302000c0b508001c400c01da178040441c25032454050361000c0768180009000e8018224428000101d0328168690341c2c0300703a034419602181e44980c110512191229003a801401018904004c00c140075100c0800912030040c60400026500c52088042d2882010b8800165040d003074200820a1503070f0100040c40181c803d40c4290030b0410f296030b0004840d4032050081c004102040055003070715602405e4500c00203502c12050f6900d8451140c4100001c480145111081401581442105c5802225400c04412002d00f1a92a640ea4401400008140900110304250b40c0300340c4090100c0c0203011140e82041005e080303a540308403d0040001100540c2c209511444801d401007028 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 366461906 1250 366460656 366460673
    0x5031501080a0201030b06210609070c050d030c030f020d05040c0b0f0403061a03070b2808061002070e07090e06090c09011b0f14010e010b062212140f0a 67
    0x62942468085a0111b0007400701759580110f01f150001180c003c12040c0821a01c000b03118411141a070304400f0326569100e086a40855188028085820590340c0d804014401d41040c1e5900d4081e00b4003080d115216a800c00807a03000c4a41c500c1c240303951703105010800c450241c10710028615405190300b4500805100c1c141846103200040c1026500d402c849509032a0403c10b001d8500010140c2c5c5060340d540200300116403100981500c0c0f03403145000340c2c0b124220f942080c280d000f0301d581d4809840c0d0f607a10038072004180c007484900540c490a00001008444085250311402c5140d0307862503003918116002d840303180042c0c1440d2041081d81c0800040610b55004c0e038180d24002d10300301c603000080a00c86100c00081c068042d002450900c03100c820b0140ca01c0950004c1c41c44d250007044420200b00400b800c8601d6000329075801102001680c00490b0f90004c1615080784401d008040030356155190101224401403ca40e44011b0f14030310003640005200003203000380e192024000203106941ea80300c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 366463156 1250 366461906 366461923
    0x240a090b06041d0f030a0f030e1902061306031d01020f09150c0a0f0b01060305100501030e16080708010501051c080a1b030306050a1505030411040e10060503150108 72
    0x85940e03e0180d03074100081d40d00da4a0500043d42980e02a25038001d09581300e60121000c480400c03152840140942d100e44161030701a081c0c10081c04105a6113113072800d030007424031010799110300c0610480d40302c580121a074000400c40382d1000954032442d84203000c2d9140b04030001000380c3c0d205001040035400c0c03038002c641036007030111080f01c042c14440303051011500810300c0c208441e00c1211007040c1000080d81085c0303031a50286224568580e42c6580072001d503842203070403e103852035030841049154065080008411202c10685010b010b4000d0100c0c1c01d40c0342c44d0301c01192603100074400c11103408280b10b8640980415200100d80002c1d01034011a100040d400003005a0400242411082d2141844000c3c8400e030602d810340030025410024040c0c411801200d100761011140050100716200c1101130070401a1101c605542c0c8a80718600720386407003107080303401030340b03464080c211041c091000c1280c10300005000205036080c00b05142c0741c901c80ca450191415180c8006000e030020010f42d004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 366464406 1250 366463156 366463159
    0x3080a0e070905060a150c0309050f0609041e0c050403020a0b03220f0f080919120201180308030103050303101203140a0903020a081e010b0105040608100503240a090b06 74
    0x541d0346800d0041740c804107481d4030412881484082da05080c03075104003801c48540c000e64620061640f1a410400ea00c0943d0400e9540aa010000c1c545241003079040708609000400b58440c8181c00003110713070706464483c00d01e100090030000d020b00c114501510058003034104810309a0442c0b07850509240c11215003071507030030b490b03030701190403001c104d0046001c08100784c4c0303d2403006082445182c20030940e0000b0425a00c10aa00030300c28400d04003003407101044400303130000218502e400c0d40041d1882201e2074a40070034551400c82c00b002241031540194001c608c1840150381c3c0340382c1800801e112042980044124020340303125440426408040260b80342c071122030003503581100500035911104035034802074000e4244400040c600c540418243c45699480c2c1110021094244002d400c07502802d00b2203002c42c2c0280000d0110600c1000c41d140e00080d6a0a52131105480c2c200003440d080c44203003103001000b000210740c98140c000800241d0046090401400700d00001d603250f05000c0c4000f00250b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 366465656 1250 366464406 366464411
    0xb04050a0e070e090304031203050405010c020f030f0711030a03200c0f0918010504050c01020c0603100909030221190224060f221d06011211061603080a0e0709 70
    0x5000c213030060085074015170307002030100c0020050240140c09050201c070280da29510b4000100c2c03600380041603041200b01c40300003840c41c00745102c1d11400b050300211426034403a43c803905099059101084504e080310300a85130f105000318011002c0504103080059980701d50020030464106441c0c0310f42d4032044030021504039590b542d4044000c0490540916104003a40c00d01c03080c04203200000c034113850012020b034240c96505502c00284240c510069480301c40780100d0050402c04218280e006000340e500c60703c161400318410074041401c24031a0340c600c98001d0380000380396008c00010f461012a0045030f0000d4200c04080d0b4455001940302142d070081c20700c680b4000030328a81e8942c8140b40e6010780c01440da405003130300c541d68020715400070084401124030340006483c14042c3c990450f5100300352600145001e03801c203444080158818882101c082d000004004550760310f40c00034140c2002d5441c00400c01000c80c2c100240100005081035002519010f0255030380a0f01150b054150307031042401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 366466906 1250 366465656 366465661
    0x6030504060f140601030606030e060a090302120d0506040b09061c17040602014d09060309010507080a02032707030501090318051504060e0a05090a0b04050a0e070e 72
    0x1001c082c180c2c009481074950302d0034091107a618841c0d850103000ea0801e9a0401135140c51b0001901203845000e003c0c50194003590020700740c0d1030a50002d9051622070300c180c031210b45242e0f032005e0090f003002046c6982e06844a04000c2c1c0d5007043d224440d1181c03c100d54030701090400b400414108101502c10b5a507060080380d4207410720522010540200070000381701a9074585d2548000c5c001d0164151410322114548080000401000c980200d5203400c0d000c2209818030440d6015020700c840744560700500d40a000d010700607030381c450107140300d174200200125a52500700c1d00248098030080200340224410b00078041120081021044203804451404501c205480400380c5420603070b85c0f0040443d03003801482c00400d5400503841048410341d2051b0340c02c66499400300700380c0c01c03800003e0a00c003034010700040007854800c806c0034600d9680034104009881c0c807140820400300c0c007141c40217003294a480c2e01142c941064402ca551013024903004000703e540b40c034100c946410051052102500e4098003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 366468156 1250 366466906 366466913
    0x304020904110f100c0506091204052b030309050607090b18030708011112070f080f060103020706241e0e0603100c0e0f01050703020705062104050a11060f0406030504 73
    0x8051000c03040100002205100280001c10300d0f118160121014012500848c010036030014400e404103110140b00c6040038240000e1100202245842440c14440030300c5611404100c1030b01012058040e0307070b020030020520b062151400401501010400014450402c0801146820f03652084000542411015034201c0020701d8034219030043c1065503e400c2c1d07040d4a014401c4010040c0072a0100c10b6080c2daa034a00d405c0e60b00d022140d0403c404500f0402c0001d81c0410342c082e2181d40200d05040045c104102c0e41c451300e089a000520101d62800e141c04031801c000700b18140792000b00240500d89880d4141a5000e044419046c85001c0c907516040300828566601400341c944505880601001003018043c001091945013020b1903016a04214179404194400c0048685080e0180c004120301842c11040c8111a0f000c900d40c04054800301c1036134064a84d40c401464051030154004042c3c03501c042c2000344843d0410101c407440340f2800c1080d0310b00d041e680c03c25182184d0792420001140e81d01d904 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 366469406 1250 366468156 366468169
    0x10e0f0a0b0109050306010e0402030f060f040320150a0b060405030a020405040c1703031015201e063103050307032304060c020d0c0f4103030402090411 67
    0x1c004c20740c540165800400c6013203044130490310980c002c404540b030400b50a0441500c0d928180c4020660411040008000c640181021a001200c042039065404000900f0904084045011004ca006510706001820310b09014000810703004a03001407810b460800042d035a0484180e00034001c41d240c00025040c000551850700050007106900e11800400c90b0510740c03294022a15204020f41d11500030810180d600703200103101c281900c03040c1690140e0b0008210a031002c40140d0030b280708807501001017000c064611824411800300400da5170400c40305003a05801c400c00130036407070b0309090b000d0807224007801000304e4125090306050342e80e42c0300c81408901801d400203800080f203c5420141e41d41040d07001e902c0748070b036000380030401164254400c102d8079022a40543c40000d0052017210b00481c001f000014070907031140002000f00b203020010640300111980094000c80b03070400741e1000030384000d0500240d02c50703d04041d601d0340c9480e90010304003890280020340480f102c044605055210307030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 366470656 1250 366469406 366469409
    0x40809090705130e04020616050c0301110a0e120d1215030b041a09030a05090d0203010608012007030f0f0e0301052802030c03010611071a040608010e0f0a0b0109 71
    0x20300100501d280407000a000c5502a1202920041d44050000382030070794442c01e1070059070300501a0349841c000d01c1108040003443c030800c2c2c40601801079440e1082e0f030240b01e90500442c6401c0c3d0a91160441c42002d0700308090300100a005001030300d51a02582408240c01d103408505041440220742c10362100001001061056050b00c0035010300482030240390b55007188a14800e020481000d042c000441500120603141c80e091a841880300c440c8950042e000f803c60360300c3c050300e2030800c4000750300001e0079960f4603408800c1c00d03552450000d00010111f0302100e20040300781c081070300c2c242161360014540750b540c81c90001002540c00382001001c1c8500711100da50000240244113038204800d01c1c211100c0c4d041e00e0341c85070104a4210700301d50f24490080c0c078400ca0200300c030340c2e0a680c600202541d1924025065006600601c0008520401e42c120810388180c0c0f00c451141d142d41c1810006484040103030050702807102c01a00304510300c0a20220540c0c40702e541800850840b581400694a03903545 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 366471906 1250 366470656 366470659
    0x9060f070c05150a0513050703063c0c0c030f0f0507200109050409020109050d02180a0905160e060f13020a020c1c032a080307080f090c030c09040809 66
    0x81c5140c0780c000c01403a01d00300d402036046101c05c0003291210520511440c0940358014826081140b0410100d5207503408954505001007140392040d1201640d00c0c3c00840d80b0162104032039170002600c40340aa24403a07059040403d040c030a4041503241c03005405851040d50130010400002e140030ba0040c0300c5c8094030601130b800001040754401d008841c02d100140c82c001c5600081e00300030300203000c1c50540951407025070184c444140480c140340601540d00b40300c540036a08400c0010080c1c0500081102440c8140901e800c001151049403a069044c103400309031f144004049a2024401074032031210a5412400488400c8042031012001c04c0d181128600903100181c400300c2c0078070407a03801242c2d4000895080355918504c0708040171b1070f0711140701410301400040034428400000d41600c0c0c8001a036030700c8071a40000c4c03030400f0354a0038000d40c422506600044e00400510580c80141000981c1041e20f010141c0101000c0c240400e079144c80c05200913109090300e80105041c840400e0454018080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 366473156 1250 366471906 366471913
    0xb01030609091a060a0f0308090402130312080703051b0c1f0b1503040c0e090705060703030f0b0f01232101030b090313050618100816030509060f070c05 67
    0xa07410701e500c0400110f0341811401c00c1c2d01c00000c1c07040c94515000d40544404001d0b203001c281c1181c60b4000313190056100f468010354204120703400149280090001588030f12140318042d0a5090010300000c005014001070504220900001803800b00488048800000b010b580740d1400d141e1952602040501d420385210b0350b4081c00850b514603422485001c082543c10f2481d40760700305c207100300520003180d0190848a0145042c8200660300c00305940020740c5c0e40442da0540d440f140094507592001c4411004290f40c0c1030b011140c2c5207103029281c0130740000c80d50010001070500010b05240318010f0710883c01c04c1c0d08003c600c0607090f440191400c0c3d030304252a50403400c0500680208164003800140c1d0032100400c0003070152040003045904126419a00ba00030304d14010a016040e00f012420481c4042849190740042c0c441203070a41c240d240ca07a85860385410100c002199031035803003101804060628080248146000402070b80202640e4241540390341c030b82e00112907101c12188006d18900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 366474406 1250 366473156 366473171
    0xf0608060603010b09040f0b0618010603020a031b171e0903180d1a0705040e090105010510020304050a050f120709020c060708040b040f06180503130b030c07060b01030609 75
    0x8400a09288100e000303a0082215074a1101040384500c0c00721001009407441070766820015039054601508040b0181031700d400400c500700f1803681e4072004d0700070f0000a6404225545032507454050b811145070034000108a00c401e00c40024403401e0047d8440612101007000300d841020144410700c091003080e00c9040d130b40e0500070b07071560b1213a11401c0ca5462800d1035981d400850b1500500750348000c2c0d40041c1204640c0720308584036202c0701c0d008000105004c401c0c08005180c0030034851107482042d0401c000569981420100b0420000b0030660b2001c6600c1448140101c1e1504407450050710b1048640100c4201d294001410301d050041d44800b407401030420002d1014445d40180c04c1e00d000c014141c2d2415034552408460707005c0100e80c007030040700003000410040b41111441004182c085c100200b48484060245250484002c0741140e440d030000076240340035149440c5c16005442070010b03441c518102441c4007a03030360280c2c401c0500f00340e540c0c082000d40c9a00a43c4404000c1480311070900070031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 366475656 1250 366474406 366474419
    0x110f030403050f0d05192106030b06120601061b051006150e03010c1d03070305061513060b07021302120a02030633071106070501020406020f060103080a0e040f06 71
    0x10000700400d0070340d40c45540c5600c6a694003170410384460341d80d813213401c01e250010913104865060344100142840103001c002d0343c0c5450007500800e000741d030180f90810701c242460010300440b49141d451190454018000600400380d10070038102c07010440b10481c41c070310019030803c0303401c101c0c004110700392a81c07400000013000c44081c80220342107001a1554810405a10309040c01d03540498040300015030102041084c8240080c01504c610078003400700c4958584a64030307545050000e4681101082050b81f007072000703203000900603002e858412010312241e4541403410388540103085c002440b46610b03440e850b00e01040350341600c040c2080802031045031f00348040c020000b0340c0180d83c454004d14800b44958044404140402003040308000e0f10050015011120708854009440c00c0b1149040c0c48036018159840d2006440f030507008e5000140d072140381c410040d262045160035210380350011001080850800000e841e04141c85003400707240510000d0025008140060020320590310780f000102d0403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 366476906 1250 366475656 366475663
    0x80105090705090703090203151f081f140c0c0a0c120c050102010903021005060303070c03080d0b090c0409150503010c110d0c0b01050f0d020603070c020102120910110f03040305 78
    0x210342e4250f44090003a2280a012001d8a50340440a50160310401d440c01c5804000081117601a00302039851941205003c1072450b881038a41c0400f440358051841c84042040000d001072030400400c0c010401514403200080d50200028200c91084c3c0c8003140c9e40c0d005003428040095900d42c0940d02240054403a20040310b810712005050354410a403e402007140d50051050142c0560503400801030200a0780984001d414020052505808140b0800001607044000f07400510321a515098136610300280b034401b110501818140f00b840b10704140604507222400302d50554401103008212207039500300752100000f10f0f81c8070316095840c1220215000781c0c04148034044003007100686181d04403d50040307031188200d040180007c906800100164a081c18240084810244c4880d9030b410845d00018019081291100d003c6101c44008100310340e0705211038115040c1d140a05800c0482c1080810046240307942c00b2002d1050700300381c41b00385540400441c0c80c801081c201f180e51b03480e160f141c080d44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 366478156 1250 366476906 366476909
    0x41e0605011d011d040201180305250f1406120103030804060c0905030c041508030f0301081203010e0f040611032e12080d200a080f070909090c0801050907 68
    0x15451a5440e50742c05401c0044058100c2d6208081c00040e000600118001d2000c0500700701e052010905e0810a0201c0c149032141c0210300540103040e518461040c075560403849000c1d0502c1e9561025405d0100e22010f0455206482c13080ca00c1d5643c42d11403801103100e500c5048140910058030000004c105640084482d11a42c407039031081c048508500d07c20f581841003401450346c550441c000780d20721030074986d10007006040c4d01050543c0035955013440d07a0869000b445040c14101c030000050003036100400030200079903485410030340b6540c940702c00d04641200150202c4210303540c04021406219194200d586001c001c3c2d9440c40e941c0c03c1c000310040c8085041c8803030101001e4504c610308449182d409502c0c3c115540b42110440c2005541ea59104982c8500700301c2e4450b5603200200301548480c900e00409418a200c1c00c0d56071020000000303440c3d86001044502214084000c06c54850303440301d5481c0c1214040c0201040514079464814240000364208000540c41c0c5001c200300c05200061100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 366479406 1250 366478156 366478169
    0x913030e0307031722090608070b0307020307080702030307120302091e030c0d171303140109030c081b03070b2208030f19020d0e0105060d02090a0203041e060501 71
    0x401400c10024541c40d5816840f003d03242480e83d00c1d282040000300e00051290b102c611690215103003d410941d0300e81d25080d00904400f0359140350501900e20200083c8024000b5140014114580004000d51b0b922030301038010001c00001c1407010840d10200140c2d4841580031940004071f0140e0b01c3c00600940064904c14494000a0341c50100c581404004030038641c00038000d400e121003000244514141c0f0100112129182c4070744c100c404030401d40162590a0f44a11485840e03851810321078100c000754400b03035107103900d0800f07403a0006e44c1102101c0c0120303500080c0700381c4031208414080002500f0410310446400700194940c204024419000d1040307a4140507a242107403924000d1038800b944090040062504001040e513402c0140101e0f64004c0b0710035400000500525881010b83e0003480c42400415114010310403411000e00425074451015210260b07403440d16000203000e400040d0421601e541c0c004046404d100030118182c21812503000618682003d500c0c1400080000748030f6078 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 366480656 1250 366479406 366479417
    0x503010c02280506010e0709230108070305060310090212030a090e15150c16030f0b160203090105070f1a07020d02011503061e110405010905240a030b091303 69
    0x4160204101d0060b50341a500030004040f5603080041e8480505400380c4240b007031291851001035100089400040c242185007296060104a580050302c07904025103003170305150030030f810044141c8001075802d180c1401c2c00d402207121001030003c10000704e003c40e200340c6540000102c90709000e40210140b012074603808580c0c286503582048685070b66885462803540801010350130b0b03210340a140b007e0807132107210340240c07484441d46511240380303411103520480d9460038885140050185070110250301c4850710719078400300740e140341009469101e490a03580c180080410303500d05002403515464180741d4007400c09000c810042ca203051001704102c0348040141700349912583c5d018410f000d1010a00728032a410b86000d4155504d402c090000000201d0350502d40041d91164480540641300460390034881566485090000041c074042d4184c01141c09020661909000107074150800010403440014842e114141c040c000c43c00303881c4c058030380c50344190b407031051012000d07801c460b600e031036031298481 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 366481906 1250 366480656 366480703
    0x2102070315020a02030405010815061b1603020306010513060503030d090b15010516020f030a080a030b0a180c09080a0305121e060105030a0f05100e010f0b031b040503010c02 76
    0x1c0d800760300c920043c200c01a081403004220075401859110b411551281101c1410040040030820a8220000c2c2101c11140e10b0407942d480101405603022050640c04446810307030458000c250348010600c1401d005108441440030260383c15403110b03010f0040281604c1d901d84031100380c140500301ca25000d491629180740400c0c04200198440d03a43d03c0410f031105810303c0160480400d40d0100d280040c2d0f00705a45907480d003560380c0c05101000078148100f4007151107901c4044000c0488002d17651030b6000e98401c0310140414941c4c28020000301080500115a00b082e00030304a0b9003510759030002c4490701c140f00101c1e04040d000005070038801d1006031030091a60799805681c0e00100244644103580329035a0102e95a9445000116480350110901040c0c420f080d1480300304860003200c0900e05c00c80c803440c06021860801c1d0046006250007040c03000f9550900c0c14900c82d521002d003080d200f42550002c0f02050010740782c10740c0c00608006008202c04101c5003006511340700c20041d00841009207082c5e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 366483156 1250 366481906 366481943
    0x1050f0403172a070803100305010509010605061c0e0708030301030b070f0522180906050a0908030a1a1003021b12180a090204080f061608060105030421020703 70
    0x2030310312901c280068075075100400059051480d118021540f0a144100840c1c1c0c0801d804000950083c090348000c5903480c0c2c03a5082060071200060b285000c6030b4140301c0104210b940d02c038281c8641c090300064a0101c0340a402c03150005158510802185004900c800104500701002850403079005040103151551100c9044550340003041401011440c18808454855000340c40d15810b64104110b084080303494084401194441103012052181c4481c0345d0030401105000b226045255030405100c3c451150b51b80c4a611b0000038803060091390b64840010215030701031400040c0c0d142c06060320006000e18880100030754040807111501000181e00c0c400c3c80c10700000c408207181c41c4403071024240402403102e020303140d0030914026800180d450000c10003a00d01d200610080583c0d000038110540d02020300c3d4144030b001030960942c0b04204607270742411600041d000c2d901080900e05590781380d88500e003403107150921104a0500b034410071b007002c075100e40001d442c030241c038098598540e02c500c0425 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 366484406 1250 366483156 366483197
    0x303040f03080a26010603090c0918050705030309010527040f0f0e0c060d020a030603080d02120c0c03040603050c0c1b0102070503211303050a0303050709140d0809060c01050f0403 79
    0x2d00081c2d06000400100100c6e8840e901503102d0030700c40c0403e00c95040c0d8500b214010345030105600c034600c503200c1040d0707070030848104058801003a040d80074505004000c0c0010b440d42c040c0441c40a100c000300030a000c82c00814400015540d10300400070024185454852802010800c0c0c1c124040d528088003803032141c6000a046500352001081c061a01d00310b0380c5a88041e4001d440b02500341a15050b000c0009008a4050320211900285c01038540518080c0601c284901516403000008108055030001d1000300c1140c094074210300700070a43d80c07074080d600407141c4200a140200d0b4010018420300341c5140c460303402d0361950260b084584031074aa0080503111882e80b11007040007008549150442c1c6051800f500e002c18000c14500901035603625900c3c14400c00010450029580e0802c0201190f000044200580b2000b0744860100700324034042a148040c844024151700c401150f0a143e50b554041142c030016007240007404582044040c410081000351011004035890b03521084a110608 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 366485656 1250 366484406 366484457
    0x130509071b080d0b0d050102121308090409030c15060503240103120903050d1101050a09050312040212030703200c01080c070f1a06120105130209060303040f03080a 72
    0xc0341d070304401030642e601c109140e480700c414a0b80307258031800355003229542c1060f122403960041c400580e44030010b00c0d6400800d04010103c521800c2003c40c0c000210381135106507403a9a200340c80c0005c107500d01d41802da0f03110301c0c0104000c200401c094904c40084517a40c1211080350016000c8503910260704000141690510f030220078040007860041000c00c0d401c03a602c0c00c0181960034030f6403100d41c0b01e0300d0f1681031140b40b24000d400700703207483c07085400290309105143c0d205246c0d080801611806a0382c0382c0d00c910402c2c0e444012000c0b504003040542da01c0c0c01401043c0303503055044a9603801d0501d00070b8041d84005800364075244050b0030003c0f27560000f043c4001c2846d4142d4074001e0b20380d59500c041000d03401103001030380c5941c00303003590100041c05040d0301010300c41c0c40e0000d4403480ca800004c00a05c0000c1a400d03a0340ea074142001c0c0650344001c50300700c0032059030403549a0883d50b901008a4554050703607104c80d804a0003140d0010600c540c80004240308000ca0b900d8484448030007016141c40c00c000d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 366486906 1250 366485656 366485687
    0x210b040f0f14071209020609060304050a12051c0c140409090605061804150b031614010f020c1203070f1a0f0403051c1401060816020708032505010213050907 69
    0x81030151302081072198005404603200415046c1482d152802003022600111002c94080e40011509814000030b10000d00c0c0c040c90a1400328074006100900d410090b500c020703101041a1100c2203c000c0d00d000d003240c08030041180e2909170f103450350390003840f010b4090440e09075403580c500700203d1420b0908142040201844108084494499540d1a10782c5046500c2191070b540d40c803842e141c0079941c18088071a0402c81e1410740740c541801c020341c10f003003402ca4055140c144584000c0c801c00183e000708100c982080200c40c1c40180c0f50090080c14214802c07103a0007081006800b08190420540a0700599503544030b1507900c80542e501040300c250b0701d905a81c054003043d014802c81580400341104150013101024004c0b407103d00e50100d0782d00c40303d07080e0080360210351400c04108510310310b40c0d0b081040441d82d01c0203080592030081011b0316407240c42d428240c41c101100c1170f0b01d8089400d00078000d255078090000c5584a12000040d0f189203210300460344100e1242c0042100302d1300c203048107111a100f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 366488156 1250 366486906 366486917
    0x1802090d02010507020a0f0f050a1202030706030b010e1801293013020301050730020403050607050c0106060302030105011b02030106120318060f210b040f0f1407 71
    0x49030707001551030340c1000504030717440103002c4004a0910151b01107030000b40880e0044005450403d02000f035108c4641c0c00c88207800c20088820300150fa40003800354111105424000340b429500300c012203451481c1c01d480364000e0505c44001c03001c0000420158101d504031654000c03a2100c61a402c452201214290040320609000207006821080822044200722580100201c0f03002d6940010f90007040b64405003030705860300c412056050a001380c43e0721410600d0b01018442020140c074811402514000303200c200c54801924482c038081d13046030040d5401004480c01881c0407100103180b94016000010194205140028424064000d582c180e0381b0503140d4800c0b08800c0d28403441c1018503140e00783d905640700c1d4000907620f0111140400c0d814040d51396220300e5103401310b040c8982000c0358800400c00402030761024450b584510105400c41c20f800d0050f0480c003e0780000c0018000d403540c1690300c5454006000e98010403540405581501075000b03011002d10488140d072460401c0b500040843c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 366489406 1250 366488156 366488179
    0x114060304030336030e010816050c0c040e0a11010c0c06050c012406110a020105092e05120f010f051003060e010e04020a080607050a0c030c0f0c180209 67
    0x34065040504c000b01a903d8488004100b000b0120441c0006000044920300b0820404241940600712070040e00c4203080503a01d0303092160040c50b00c54040c03200f44040100102c1e0f1176280075002d02201601c520018014001c4408a02030703180c481075040d0307086881c003034540008401d80d4054188000d866812100d41c0034064681103090b1040d5200410024865594512000001003443d400d00800c3c6402302400b0280e6080c2900640b80a481c10100c5a096102600810060380d0003421100c1c000740c15604011040c149000680742074100d241c5d0140030b0036a21600151184d4803001512407600c00078201c40b42612058504002c008082c00352100501131040107010038100322a0602d4520309074600090034130350311034000b84541d200381c0112480f40c54802c14841989844002c220150050784050006400c11000141440c42412040d6040c450039101c1803081c1070240d00648403040c0c000c417075121580c07118600000c08400358041c104018960243c030300c1070301c01c1c00d10a03100e51080152456540c030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 366490656 1250 366489406 366489413
    0xa0803090106150e18090a0c060305160c11010c0c0806071d010e0306060f030a06060b070c08070b0702011b0f05011d0a0c05121614030c010e0f120102040b0a12050114060304 76
    0x45c000380002c11500c104500900041c0d04420700c040104100d950004041c245074400e4500848802490800c10202d851042d02050302440c102080390400d00300807038081c0940ca09401c0202e520f6001a00902541c01081705441e0403074441c6e02400d101d6410091450090740042d0f581200c001d06c4a605035021000089583c20030919110720140002d04582041701e0726a02c020547d10550083d40710b104003c42e1400c20081c3e07561280d4050030200307010703000c000e05040140c40c550141e07681c00307410072640c03081d08540d03074058041e0400090703000758160310009040e0810798041c000c0c0b610307a004000385600d5200c0c41608007241c00180a6403041040035081d25050400400c0200765443c0b40c0540a01812034020140803c0c0d0780c0b0050601c0d08130303010180c00080c105803c20080c910b07541c2c14898005c51030760680e9507800c258084580d0454840c2e49045000081b11b00a01464012244000e030000d0100c9485030445044005042c030204103100720780e200c0c80761380c1d01e403e40144c000c2d03004501407000c00c000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 366491906 1250 366490656 366490699
    0x6070c03030209040c0c0b01060807050a0c0c030204060e15060c07090b04020417160b0306100f141b1b030a020603180303040f03021005090d0f020a0803090106150e 72
    0x900a20307001d8140381001000504076042c0c0c030204d0010909403441d640030020032207402c42c0100400d003858402e601d00a003000d0305520960110408100410882004000700c0d542803401554002c0c004200854440c015441d2001065070b550a410751103500300310107807510b1030444110300700f800c000d020034500d40b0880740e01501031206404d90080e000e00c400306100300810b060345205c449880003002c80000e040003000c80300c0202e4004035100b000070001c01c80c03281c03119002d81300280000c2c5444610518024800c440001000e102905410800507100514a075145a19040100004241c40c03070171090074220580050103d0981703825400c0a003010025203420170185600100d01f41c00c094520415221103070543c0c0c000c46045880c44100401c110515504108001549040510400c000e00b442840995207044c20200c00c410002000b50ba0584e80c0c0c130a01c4000c00a0f9802001d545c3c8900f0442c030498060412805500e08114540c02c2101d1050b01c5400001e1580320007401c2240301040590715000d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 366493156 1250 366491906 366491927
    0x804290114220f0906050901061503020a0e01080c131401020705030a0b01052b0305190e2112070606080105070f0801140d0b181606020303160e0307082107050607 71
    0x40c500d0350303142138101161250056500c1010980000540b00e07050401640c21803443c8417141c002c240c8180288001c25030882e4424080b000c09081151080d5500f400e901c0c220300c11340c2000d00d960ba50310b40c400103400d0001d803050708203510241c0a4500240d00d4506240d82c0d40034000010f003d041c0301200401042c02c00d061044190040c00107a1000503104004031003140c0219103003100052000034162051000e070700280444242c0b28603250488200b014002120004010400c12844c003d0318a5600c50314801c21405841036082d410f6184c40b4030031410f00b43c3c01444980700d241e286508040004442c18130032181e66142c0051501d078140c45c1d03404c04030030340d034011040c00d58950480721b8880c40101054001100c20322a240004e04000c3d100b59103514070381004640205403100041008007880410340100950390702c10180e8008a424a8601e0300485070b040d10621556050f0040304400f1603094004100402d06407401d08126070140107401100138144920b4101070420340000700030a001e644140c0c1d05a4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 366494406 1250 366493156 366493181
    0x1205031b06040201090509040302061b09041e0f270c09050103300c0803090a0206031003170301060e0105070501060306060807030b0c03090607080429011422 69
    0x9040200000500040d841202404012580000c040008540e40030641c40082d140a03105507070681000c0c0c0d0080e60310a409440c038080454420003026200036828192182c6031030050040c40105016054002040d241c41c060300c101c242405070958240f215030040d00c400d1081d4041440e020340740d92800380a100600c1001315529241c0c01c40c009445d1301c0a003d102d02035401030791141c9824000690349002030361801c4000d58008903032102d032100e02e42c00024008109400000082e030300d0391040007850a14801180007035210f10040240b10070f5444000080050301e10901c0c4013003245203c030b000030126010900c10200010100c1130390361a1544590301510f0014403c0c000810650f8884e5a030f5001d50358160800300381c540c40050100300340010700d100c80790441c00c0b07520012305d075090480e40c03c1d4407801c0043c0402c042c010403101007010001c424a240e03284a041c1401d074072182c914200380c0351a0030f07000e00c80d0b00000204d0403d80c1056107014480c2c0340680030342035004500344074194800d1015244000f60030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 366495656 1250 366494406 366494413
    0x60d0305040803030a0605010e12030d02070f0b150111070b090103022b0c120b0a03061d0607260601230706091101140408060604020d0b100c030206090111041205 71
    0x70b41c0640c1000a18025451140d002c40c0700303800c007400108010f00940c98184034001040c0c0e007a51003040882120f803000355200002d0ba903084682031503150741040050040501421200304039402002e040000100300d800da0310003403440c0c4c0c9914010b507665514001d0301e142c29000c10401b4615030090340100b1407020003074004003004100000d8900140d83d11007440c3d11180e03c40400203281548080c3c0d10b45140d068040804c14221170402081107510321b40001411959964904100220101f403ea86100a901c048a04510700848000d000e0321000080d281d42022042c42041000d0710948200e2280b4411b81d05d6400c50001e000e100c01c2c002c81c2c0c20341c0061400c0300400a200c04580345004544929014240302e883c40c2400c2000142070310740e12114070301540000d010a101c00352010030500c0d00b01ca001c44000d81c0b195403121078040289615848240d00003c000c2c6045021604a10000f540314007a4007503a0407030791868842800d03100804619403040300104014020041c44031050407075240240101c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 366496906 1250 366495656 366495659
    0x12070c0f0b0415200706030e01021e0708070c0b0d050105011e030c030e0709051609030c0603020304030504260601170a06090503090405310c06051c021602010305090703020108060d030504 82
    0x1013408006034021002641c1c00c049018019150103020b0141490080b80085240481ea140c035200e0300c4a114044c1e802e0243d0000b0282c09010700b030302c2074500d0240c0140340352000350340d02c2c0702001099110b9040c8c1aa501c1c1000c0000500358092040c0070a00c0c0881c4003020f11035103031004201c0007092650080014035950300c0d0703481da034240c013046a88040c0585c141c000a503810091400d20002d114a000c0004200711440700780300281c40840c5150032110b4a043c0540c5030f0300d5514003968180203030b070003844030140c0d00c2c0d07444040204500711580200a40e181500e01076600d42c480c0071007480b0f0300c440c030040035801510f0140005860360b02005450380102c0950341440009000242541c1c0f041c0c0f00c03031083d9a1162848900310744007101381d013504c8130b40c00d00600319008a61745444810781c0038490081440804500080f41000a4018018010005204550360b0058000b00d40140e030500d101a80024a010005207020800042e0350b0b05480d016102d03100c050307403418200704108500304412000c000c0140070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 366498156 1250 366496906 366496937
    0x323100606020c0f041b0809010b090a0609050906040c0b0d02120a0905060f07020a06050a1e020a02070e130803180607020105070e0301021c0c030e12070c0f0b0415 72
    0xc54000c1e20041c0d0241c02d1140000d070801241d00d80a6140b98400c511340a036100000f104400801c00f016941d00b44001c4594514010700d0040c010130700d03100e400400560401c9801041680319100b0340310391131000c0107075440e01c8400079030351002210300920034150010184800a00310024200c4d1019044c03000d13103010f080810740f89440409540c0b803459280c031018071600704001448078940c02000c42141c524140740c9154001d540e410b108d6005440c07103036244086030700c21080c0c1d0415000c1d00c8080e03001c20440c141d41d1140030000d5000881000c01405108408244d50b0005010a4081c010481c50340c024010b954541d0720544d44080c0136841c661644600c0c10035001d100744501c5d8130840d9240c00009091404400140c10141a440050310907481004001c00b820000e01a114001d9144c3c1c60005e86020040e10660040000100c0d603001846840240c4d84078030f45500007015054030070b084242d2007654a2a050804412601410800b1030044c04140410003030312100700840a014502581104000e10703 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 366499406 1250 366498156 366498161
    0x6011808071d0108060c030f04140313080709230a150b0706060605070b0a05061302040e1b090303030a021e0f03160806030a0b100801150311040501032310 68
    0x340a84981c0b5035010509a25100701d8000d00c0c01000c006014120a1410480c5852980b2000f40f01108440720100446c06006c070384070a00740e0b03003810340089030f546e0040d05070007060081c0140b040407618454104040b800544034007031400c0058044000216030790b503080c40b201200f04000c181640040c0d6602c10f0160422405210704c1c020b100d80120241d851a060900105a0719150802c50a1041c100140400100c041d4039060780440c00520004881e1140c00010711007580507510f4005442c00400e01242c184907060f40f071401100e903400340a2004031030b150840c555000e1156002d9064000307200185404100707400402141800c410b004003030307070359005481e15560032102c81500116000f10400c41010302480801a41c4085070502c0328075464560002644c66004c51001468034030120042407001c0070150000e00075210500c000e102c884074480314841e680040344411703a6040d1002d020a01c1a0402c1c0c800c0505982c0c00c60349050380500721141400c6440d01c0003050045910820407003a020b00d580d407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 366500656 1250 366499406 366499409
    0xb130f0e0d050d050708102610020c19030801031b0308070b0402210c0f1206040f03020706080c030a02030718060203093c01020703050f060a0606020f060601180807 72
    0x1e485142e201d0000d0f034141d108684004000c0c030180207040c3c040c40820117403e00c1030303001c8a12445804102440401140d44e080003217400e0000c1c581b0420104940320a41500a0012109075904994410039801c041c0200c07240028130240114070094014008100700b002c5800d5284019012030003501e590b555000c2d50303580300c008142c0d080160802440304515098914095402080d0301c060308045029401503250445510b201e03101d07a4040b20340c4010b54075580760104250038120f0a440b403d151a0a000e030a119117088120010301038400042140c0d40101009c0f40103d421540e01800c546d2175605040003540003a05200c04d00080c00b10501c03544d0152030004001e400c0e55070145480714084d00c184030b240d102003140140c0360161841c01d2482c00a22041030700c07060400148040500c02c66800507403c0042d2900007410ba0300034800810000b203c0000d8040c001c032160030b42080880d6a450741241c544901002c01415500018045507203580300310005004181800f0a807601103550f210041c1ca002c001d03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 366501906 1250 366500656 366500683
    0x120f020a1a041e051005130b01091a010f05070b070e121e21071a0c09011e1d0a1e1a0c0709110d0c020606040b03010b130f0e 55
    0x25102044204190604000c400715100e069201c650322069813120703112000c800350050310990301d0000030030002c1800302045196821000802d50f0f56140c0000c08081c0541c0c42141c3d406800b10910714089502c603c1e00403d1a240c9981d0f61401c0901a40c2d0720201e14401411120030410101c103060101d0742c9a035141c0c1c21a4035054000c0842680640406c0d02603400c045d40c0c00700c071303820030104862150710020144a0b01c20f2013002e1b0300c1d41d840e05032030140399208140f00305105e20a406000c018010301560001c000746102603c0368507078000301e0444241c40395000030304030000403281580752945416440c03d07200e5134080100280d8180e030700c40e8042000003040304a210341e88601032034100a0141c0440a26415500340d80c6003c0c0340c0b104180b0583c0c0d944e1841d10a0b48645a616007450b00035059030000c1d03e01c1064850b40511214038242d200940cbc4070401d94a4900c964503104001041e894144542034541c41c015100c2c2100e132086100b103400070248051103c004076203400c240c2402030424403860404064 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 366503156 1250 366501906 366501953
    0x604060509070305180d02071e080d110c1e0f0d0206191101090b070503040804031e030e0307032102010f111c0b090a0b0303070b2d04120f020a 63
    0xb0a500b0085c50310b5403004000c00e10760882500c0181c071a5020911406907010211701e065601d00f0301c003140c040c2c5c8a50f40d00c20040c1d4000d1240803010075038000c00c8284c0001c0808200c61003039508204000003440c80f004542c0c2c1044144201c00210300b000c428021205030000d03c00c84210003d81c021448a0348001926407075030100d12800f4462540045c5000300184000000700021100c96440c120340e100080c01c00000d000e0b0100014041244810840f400356510a21004c07040800180b41703c0450031800c401c0740899003040c64003801b4180020800100c1c3e81012410100c1e0000d20174450b071700800328030340008554846070507050800780c0d4040c81400218911041d50303108100070b00c05030a21410280111b94909265078121150340c1c0100c00f507002495610009200d001c4203001034954800c81200a0503020300104005000301807104070315199028510380325021030040c10043c0c1504003103500030108001c0c40008509a403080d49140d41b11002801100d01010303640d21102c400f052680403031000d005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 366504406 1250 366503156 366503161
    0xf07080c041e050a061703190c0f0501060906050111030711040c0509190303020c030a0b0402151b07170a03080114190801020c0715121e0e0f010b010509060d02030604060509070305 79
    0x11b01038440e0038011002200554240507070b0700100c841c2c0d40b2030301d02c00900300321a00c20740780140403000d00c0c64581399034880000c011b078035560028180604040d01c01e160100329100da017116166004400c881c2490791051000c002e4040e00c03401c02004001c0b41b500c43c0e04000e810700c612401d13500d03060f800d1865101202d0015640f40d2651400038034100b40c400885000350020102c0e9000070380c14046268200364104c4100c5a03030001e1646152150052081c0e201404e0000e241c40f00b1281c40201d12201685c000d2401d2103c07402c031211030580d03142d10500000300042c000e4001045181c2c5480094900d03d0001800a40140f006480b86881452603422200f40c603503000410482c004800c01000000b4840c841c85d41c0c4004a07001d4020344654020070884040d01e84a002c400340001810100c628201411202008040c041c440c1c620b550b441d207000320028941c685100344619600a5083e140c902c0c0c00140040d10f072540d00c080180103500b002d0502e581103919038034046400d43d82c2482c81c03480f03088180d4000030b152 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 366505656 1250 366504406 366504419
    0x30e0c04021c0b010302040b04030b04080d09060e070816050114130b0406030e1f02091816030f020c0d0c05240603010b1005180a170106080f07080c041e050a06 70
    0x10fa00d040d03030243c1414410003041007c100c100c0141c1d002c680d04120240c1c0e140e9210b040500c518130540802e01040d0b4a00341005081164a43c080c10b10140703500c0440b01c1d0562292041c0b5690b901d604060b603d418a10b036410000c66110b6161448220004014107040110003a01c0700442d150a8100c2d070803c0102140a0104a43c07600c0340f0700c1c42000810092808400000d12007900c9040c1100b0f03c4e04050f00001c01c1d01503a141d840250340da03506048810003c620740354940000e40c3c01240d001500107030a06100080081080c001c1d00c0030070884001504030000545003e03107001000050886070fa00981c040c0e101d0068901400254000340204c0070109032038084200f41c01c54a800c1caa05129812240c202c003052035001054a030003007400400e11200581c88400520140340740c1d4803005504400d01c0c07e81084042c10340000381100c000c6800c5690266422803a9a200c0c040c5005100300c1d86c4c840105001b591038650007100c1d1340040e480d00301314984a800d08c2c01003500d0044545130511501c51008000e40d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 366506906 1250 366505656 366505661
    0x717011a0903240a091a0a02070f060f11030402210f0609030702011202030f150607050609160e010605030f100e090f0c04181101090512061b0415030e0c04021c 70
    0x1503071420050003401b559501c2d81d88844492820242c4200c10001d02e08061541c12914090342150260900e07c0d034a01e0180301400c1c0024811240307a081a2141450301d24050039070740103071750041000c04901c200f416100c20420030482d1f40c1140b846010f805554081c005c0c1300c0e01c1c0c003a9180d44042d40d6110458000900000c07802c01c040c02c2201d10400c104074400f02d404813002e0b04038481e5141441040d480400141c500d00402c280940180a1401031241000d170008103940682c403881043c0250940d2849040104402441910017140007000015403481c0303044080c8ae40b02012000340750303070291504541108400c0071200c401e02d070f60140b0340c400041a001c202219184008540500c1a50000c030f40070000c1c0302c2800801007059a2403902c550303a0303a0140070310b8400f07400042c2040b240e070703040c1100840d0b90f14401c0d80c0000003138000011002c040010101120140c0310780c09040b040401c00c8103c210010031460254540b14042c90038224440d82c2d8600041685200b0b0340f801e10701000c00304250b4400c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 366508156 1250 366506906 366506911
    0x50601050a060219140d0801090b03030f0d09030306090c020c13052707091103040b06010302040303200114090d0806030c1f1701030602030f0717011a090324 69
    0x480d954241e400c10040d40d002035000445450720780b07900f0400e0203a1a003511292880102c21096019416200d060540d1190f0414101c9600306018484228407000741a124490540081000304c8100000d90341c8030626007000b101e003803180c03a0000d0b403e9a02d980081c1280d1418080100682003d41a040b640c5003449103c08418600d072000c100034100100d0303001c11a048a889500c3c0141c5c001e000000b20760042c00208000c00030548140b003194040c00407903060342c1c021901103418950304030219100c2c1d4070074404da030180e1740d0507240c00c0310a18090281c9840d903d03211040b03a10359901d07041880d090018501000d0302812261000340301c40364220401405420b80204014021343c071201048000c0d0ba900004480c2101c8000c6060301040f07070502c4101ca0100c0c18160480580e001c8000010030000182c0c01540b040c0e88066840304c40d602c80d1403040b900454a4191441d104038480018481c0d600b00d50300c0b0140044c6c1030701c050f500d016082c4011904010000c69200307140c1592441868003800009490355 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 366509406 1250 366508156 366508159
    0xf170318150112140f01051603061206050604090510050702010605011b0803040804090e0705040b09060d120c140c0a05010f020a030302030a0605040207210903080f0906120106080405060105 83
    0x303010a00720510700c8088030502c02c03991580290901c04003030040c60344c1d84584a80044040e105a10100e00302280a00020fa50080c40b084072a001c20103440e100307201e00c1059654034400410501c070b41e0b80b9100080c05000c2d10f96544590b90b9081c40c8002901000110a40c02407031101281c0303841c10b00c101900f164030030750050741404032451402c000303070f02081646076045a021206580726223703410b003040d403800340382c02016103a450060501c244140005e0034070b040720000c07202840714160110034441a00d4080e00c0e02c1d500041c049015100048401c4000d040c0c2224500e0001d000300400d48940245103903d143c509810340090950800d5402c040c44108050318003800c029427a030016000085da0b07007801000280400d0b03030200100300d51900640000c0003c0200130000d42d1a005641407003901e1080e0b0301500070b00d003900f134140200001d002c1c003400070072a5007110388031f410314504285007102588909841640900d04200c2d9628043e0070f0000703640a040f0643d1400310915061030654980719068000702d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 366510656 1250 366509406 366509413
    0x23100f0506070b040501021204110a090e0a02040902030f1006080708010b03151b0a030c020d020d05120a0603021c060606020111041e05060a1205060a030b130f170318 73
    0x52000ea1252400c40c0c0c149a4411a416420380da90b0803c82c0c020301a10403800d6003a0010740901080c00100340c40e102000724204c0f01100700766a03841580e4105c0e00e40042010301e64009407202c80251406d544841c200500190a075007462041c2401d02c3d040c00b0b140300403004055030b16001401604410007112001d040c00800800481e100040000d41e1031000d1031032a000840500000380262104841120008401210707440d181d00c403001d00603024091343c10412005119525403160041d1001a10b02060304003500c600e8a001512031002c0c503450002030008460f01d0b102c01d0000b006071104c0100b42c58103040301c107801c0c903500c103a481d0050903188603600000840e030402900846c01003460080750200c6121046042e050b0707019811740d04180c1100e41c0130030b61010000c01d0b0f480046412107040b40742039070022400c0140d50b481d941003100d0701c1030b2404060b0008522200145048240080072201a03000d801540050310301699021b000c0c0c03452030321000d1000c0001c01800101440d0308400c204542441015 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 366511906 1250 366510656 366510659
    0x30222060f14090c1c11040311030f0606090115050906070804030201111203010e06041e0506011403040f11030304120804030218040b0402011209020a0f0608060a08100f23100f 77
    0x55082a0003811729207165000900384e122102846680403e01c28081c4040c500d4850360f407801c04440f0610030464890190048465124049102107032103485030780018040c403150b9090a80180c0010000c2c0c0306141402010003030704a2a0317940001500b407548c03055082c55034a500318800144003c40c0300442c8001c1d0303440303c3c40300381850070710070b040d80d0654400c114508d510350394507000180a458030003408464640450140808262690030107842041c080c0c03680c0700a604406169107841c8812a40074204071268110b060019401c035183e071107081c000030112405c103910b42c0000507402050701d4040f281c00380d00040820860a180744141f20020546503200546c0c0340c01d840324208880c0043c0028100f24880001c920084010380c0f0200840e038000e0154800b5585a0054908001d001d000700c50100d4035060000e521440c0504c803034410b458403c80640240c000100d1400c2c0078021882907030001030344891052803080c0b01c20415180c40c1004c8101409141042d5810300b504840ca90000c01c0c4003905000c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 366513156 1250 366511906 366511921
    0x40c11060a09020f06070c03110f01120f11040f030501060e06010509040e01020417010209090603061003030f050706091104050601050c0a03180506040602100f090309030222060f1409 80
    0x1400c5a000d2000000800c11404510024039603031441600310340c0c0804041030f11014029120900025a0b1040380c40c410600f011000b00002000b01540c1180041d0086c102e10310070300c0554114a10f000d14040340421522415400300241c1e8015400850121116440030018000300340201c3c4000c1c1580c1001402e2814628002010341c4074107105c080c000e54030b03031b070408100c0c48003541220010501d000c0c6140306420866442c0f4083c0d4026803026104201020200e03249140c04940306004901c0d039041c1c135200078610360342541c503c6107002c4c1141c140200ac5c03104101281c3c01d13000b40215144500d11040c030f00c0240c80100400c4a1026141d039041000c00e010a00180b400026008011601802c2000e0040c0f29187e49040c0280b85802c030f66049100410002680358001030040c03041c8a81030b8080c4828503944070160125181d1100c042d001544562080001d410f01c040da150a07464404500341454045541a9007030340d0782c541c03010007408803a10b0204403c002c0058074003500e81c1e0480d02c0160500b0000c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 366514406 1250 366513156 366513163
    0x30804061814090106030507120e010b1206150907141303050115030309180221090d0e03030a050306030f0d0e01020c01020a08042d090203041112070618030b01080309040c11 76
    0x5c3c2c0051540d19404103034424042c0000c81080500c014041c00009103a802c0240600110405680100d858041c070541e582c0d000700740540f10b408800d0605a0500060040018806000e0081002d01020188050615540030b005000c01341c00002d200000c28074500e03001c0e0855244030b04c00480a00d800906000003580f04008400320b820f00f0b0b500074045070003424504002c3c8900c2c001c4103405407a00042c84205234085409074030406824081d01c4038051a0403050700c80c4101f00c108994184c104005620301d2a004101841d00000e0203022911410042445a85400e1640046001103143c551480b8000c2d0b0341042250145a0700388060300201200f039035210558000c0c0d014842520a52840800d405d00321402c00303042c4007145442902c403041d179030809171000354019241540c1194034944552281d0600074050800046140c00503e00d440c81e10404492080d800c00101d000303e00001000070108202e016070381c3c060400140507559400c410740404c02102d2a20030072006110034800045440b61011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 366515656 1250 366514406 366514409
    0x705060c0904060b0415090602030705120307120f0e25030b130c0f141503040b0408041208090f010201090b0f04150515040b15041e0308040618140901 66
    0x640555141c42559000402030f014542002059810108000640f080710003041e151441450b144e546540d5100c0004030303100c5c030400d40c015081d81e100c1107092030200694070041da40100c580c0383c9032410400e40c5210100f90b80303128080c0707200152912000650200148034100c0485070362018070280d14140391090052041a100c0500400c003210001420b411485441070b103000d0340000c40c2c0f20442e850320211260300c035090280c0da2a141001050180505190b0005869581180025800c69449541d07080c10100010803c4072550024000020b002d600d0110341c0703543c0c51140c0145034940d070048003400000e00300a800d0504680c1030454103001300b00810341c0035401c0106807543c074101b50f80700c0c01c0c071001d2004130552044519107050f0421100ca1082d05000b01032403800c440078412000b1880401c002c4201c04a11000d11040401c0204030003204003503c161103000c5150b071900496540e0700c5194898215038000400b00300c243d81130b440100070841d5240090b048450340c0111500c510404244040c005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 366516906 1250 366515656 366515671
    0xd03030b0a0f05010912060609020a02031801051c051314011a091015030e0d030c080601031103070f120218011b0b011406120c0a021b0d120507080304060902090a02070506 75
    0x1001a81d01480008d820070009402951000c0d503aa40000c07070000d640798018291780000f10038000203544a503200b2411100c1e1030089010004041c2c01d0000360341d00801011344042104440d00700794000050704685580500402e40700002a02200007012500c04050130140c94455803000b0304001b58241c120404000781e0303075034030b410000c034140480342503000700010070361018a4480c081ca551090f6a154000104d0340401e90f8406100d52203074001501640d8021642035442c400500c00180300610580c00c0403100c405e5840e101c20038441840c100c404991261022a040b55102800c041031540c000140790201000c038045034085820948030020b40d02410301034107402c0051000d800c03070156105000c0d1800b02c1205010380c2c000703041401d0350101d03030381c0316850200160141d010151640caa003070b42c03891a0301d41d015200e101018500da07108409420201c24003800e00a050040d0030200d510400a148a1413144000042045a41c0100020385030010023508206004004c0d010000c0e82c0840c000740c200e0f15 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 366518156 1250 366516906 366516929
    0xf060a0e0639030408030106090902070302211c0b09071e0305060105090613030213140f0603010e06010f0614070f20030109080304060b04110f030a0b0d03030b0a0f050109 75
    0xd4402c0e19080721882c9641e02c5500032808001c4c0418003640c880114121002611001e007901e0396a400700e0181c1c000c10030047c0240e04080c2025200c0180a0400000d02601612151405030302200d0030754150380c001e40d44840719507a50f0180300641000340708244c0204d114202150582962019044584a0441018101600c903004200300d64011415250301000013009a5100d030840c1024216040c118842070f807190800e0319140002207258421154840303410440c40c611030356600c000d6252a10050040c1e50590341c0e401e42e003040a007090100c02d0103400c040c4405601207250980003040fa140c5540846440da404104240008a21035108421107500c1042c7d40210084551811009800c42994903019400d010220b020803400740020b61286105141c01c001c0d0f000340400340b0048406140d503807400d09808010b40008991940b02555004841a9010500c40c4c00072001c80d4501c0b002030702c03c8000c0703a11082041b40502d85420f074030010302592100250107038a071400080c004c042912601e0000712 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 366519406 1250 366518156 366518221
    0x30f030a050a0219050c040f020f040303140705010c080907090c050a0e040b0603010b04060311070c0302010c110a0f170c1f0e06040b03010e07030911040e0a050f060a0e06 75
    0x40c004e201200c0c101c1842e40185003201c105043c660b45420090f403650788140e2800b078000f441c08145100b5507148808e504061b90030a401c44d641a10401c030054600e86d8588824070042c0001002400342040200051f5100c1000d82031500c0079603c0c0c01c21a420103a400750600100c1101250b100b1b09590062070385213880050501c00038040b41c000d0011502040c0c00950000002c18043c101000402c110340b403d0703908020503018200c11040300e02810100424003034081100b00f0140d0322031903e840400740910384d50411541d00c9000504030300f03c1913010340ba00a07502c03402006403900025030201041d001074064030b01110810001212824144451001c070443d01d41001c0781c1e14820398110720740b00710160460b0340d10350b11a0a15802c130340091050243d080740346000a8046440703801140142503004c0c000001c04000d88040001602e141c2c801d00c0454491424035030003050701000a20b40505a100142c0301ca41800200b550a4820464003d031081e408130003807005684103013003031442c1d251002c0319542c0c192 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 366520656 1250 366519406 366519427
    0x40516090e03121815100506040f060c1e0b04031706030607050c1501090204030204060b0403031407150f05190c021c111c0f0305280b0409140606030f030a05 69
    0x1000707072030800040c5100308480400c1400030721517440d002e41b460700ba01c000155629000c000752032140d4015501c0703015950004000f054002c821415030300d8461507800d6081c0c88001c1c200ba007203150100c9c0503a00c0001d100144424590000c0c803090f14070f109030307003481303050b1034084c02003591264060701403000c2007000101544130020506c5080d6154240404e01582940e5400401c0040d40044c0010703807045140805c00920001401c1c1200e04699158440300714905540c0c0070304005030429003007034804180e40700e00c19408240510034a0300564007075000058034184040c810168441071540e2018a03498205002205600024240340d10942240c08003940030282e1b504452032540486149a1881814941284c03900c001c6501c00c803402c181c0e44c03884507035242c102d4101c0030381e0b4003582c2e5015000402d01d41030008020131080c1d20030071b403944200420300415a0740800c0c100c6500000554021a141140542c482c4c000e000540d0000c00403401801190300717032031040340c6034403a0700c800b4001e201b800560382284 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 366521906 1250 366520656 366520681
    0x1030b06040312202d010507140c0a0b040b0a1505011709030c01090804061d010516060603020901090e010f0608190c0302090f010e0a050411060c01060905040516090e0312 75
    0x4000404c070075558903005070509100c11143c42483d1007200400380e0090780040c00148140362059245503078107020702ea095142c1800c0ca50292448a40e02d000b46010100440c02c4540711501491080e180035003685054500d140882e50b4103c000001c90722203d0041100d07a074007140c50040030896003e0b090458542c0400d003880e6100d0810061825401d1403801820b001494000d82b040310400d40b260001040c03410003290ba88614001c0690115406212504124191038000003416100b41c400017607041d22a00095010007090b440386c01c10a80b01c0450b9940b000c0c0a001d181d00c003048492043c402e1a0402c40300d0b075182c442d0040395882d0401210b409209005000c1c09a170b004507001780189881c1e0600c0003501008501c00d008440800307801401007181d60000380b0810f8450b03500701403c211200c000c0d40400415501025024405648038040820000ba00b440b960b03004611030001400103200c40b0400001e11a0a035205a03107031460400040034008010003101c0000042108100c2156107900742843c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 366523156 1250 366521906 366521957
    0xa120302131505040617060319140708010c02010b0d0506131505190621060c020f100b030d0216032907020a03030b0307180c0207031203090201030b06040312 69
    0x20b0201c45100d003100280d0004020b201782c0b40345944140708407540c11003541924030107843c0f854065000c4c00311001281c0c680d40e00f91501a00c00d204500351805054102450090140c00680a0765950301c0c08030303421902441044030000c810b42e0303034054510040d112582c540c030300100743c0c0b03801d9400c01250204000440c1081d00c0541150302c0100302c41d0a09404000004100c028500420761501c031010422803e43d0101d00100c4200800a11841405076201d4000d48900d180e440d06501c141c1e140009000070612046a10490110300011100030040c00c0514100702c0401440940d080f9505a4070b00344c0c1c3c20034801d401e8a402030b5660318a81d50100101140075440384080080500950074030901301d41c0490901c0300a0700071381e405d2220b0f4151070201600c0314260321a809040400c071012800d141c030590018503c019060042d2031189560b5190f440d004814504c5001c002a078503c0c04004643e054030614840050690340b8030b00b410708581d580052203110f0701011050011040389085a0075a4146125 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 366524406 1250 366523156 366523169
    0x18190c0e0103030f0314090307110a051e1305060619020309060301031a2206050a09021810090203100603150528150207060c05070e0f07020f0a12030213 67
    0x35419a900c2c01c0080015250b00b401400280c1482c090300c56043d083c0034068000c0003682d011314074181c203d585048400f202401d4464121701110000601d6076034410300b1450424200b103a48000c0c035807038030070080283d03c1d4244c1020340c07a00c1c0500b4044291181e40548001228030300909031555075802d4260301d94098030f000143d1000c4000008410080800066070600d4602d10322502e00d501d41c2401020f02c2c0943d25090858140021040c1e808a4501c2e0011600700c0d0300080c0000d00c0c1b980c1500801e15070300f0b904100b444010280c4080c0b00c2c00044404141c1300a111098003141142425906c0c000064010301c58001090340782e111102595014244d040000c0c44010320000648807042116500b90117100036085c14005d0700c42c07002518150481503042800102c1e409000c1d11414000c05031a07514010030140e0f240e216000003c02c42c855000c1c4045d016040544100803a8900484001d02d822044212180e241e00150f070380f580000c02440ca042000000c90401607280c10316040c6120409842d0b51184 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 366525656 1250 366524406 366524429
    0x15020115060c02030d0221090d050d1707080c04090e10050a06080d1d0402160807061406190b0c010207050109080d05010f08070306020304060b0402070b060918190c 72
    0x200700e80c02ca54601d40440c400e40985d9054a9420010307600c0c4d1120000c01e1341400c00c00700c04021800c000700e0007003000c680000c281c4003101c0100e440f11442c040d41c8580c0d90022440ea0410680450010400b4075400a007514007080c442c0b81c0000801c0d6140690700c204034900d5220745105408200c01e00c40c081c44800201e108101a10b00015020003411181c4202480c40c0941400c00d280c8610410110300341c01151750301003112506108c203002c000d41c40306c3c80c85330b240b200e80d400c2c150000e201c100c01032000d180204070124044c101030010160340c2201078481841784c3c0003e040a00802c0e010070322042190761400c03c0700c0c1c0760b00160700d00501910404000404a510b170040740d90400459001810700b090401e0740803c51aa00d842175000200c042d401800e8641d4010301041000a21980056034814030640020400c03440c5800070400fa60406001100d81407a400100000c81c108025119409841c0c101c42c94400c1d600d202d206a00c0d2204441c5011190901c00003503024800c800031414000d12003004030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 366526906 1250 366525656 366525659
    0x3260705010c09060809010212060f030c030304060c060b0a18090c0b0a030f0f181709130509011a0f0904081207050409110a1b030314090a0203010b040c0915020115 72
    0x2843c0c15154012000420510f40c0071030b035209014801d440301d40c4052001d14019864110421440820303404289500d4070a140e640010b40c0c40a001610040400d51076400c60b42210b4a000c90a84044441840c00303460b60b1801041501400320a081c580c8148104c0051324041c10709004511440305d42100c4071030a40010121510fa6041d84088041c03464480c0820542000917901e40545440501207840382121481160100f500b00b80030b508000e0051401515180d81c1d400880d44144440c0c813601c1103030f9a01c8040120383c038403c0c001c0390000c0d4500300c40240b20190400003e8030200c0e80100c800c2c002c119900004040040c41c0c1c1c1116408504807900e0701d12494040c0000302103a0190141c1c0e05047c0c140065441d0350a03800701510309110f400e403901800625148620400740003003041c140c041544030042c009070541c44030312150085401c5005000b40b100c444c010305d400d40c2d2610010072f0040c0d2601800000640d444502c450550704008a040107c81030a0300c100d02401c1e10350300d844000303000441c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 366528156 1250 366526906 366526931
    0x501051503010509011104030210170c07060f0c0516110d0c050a08070807090203190e0f1605060307140706060e0411030102070c051002070e09010204031406010326070501 75
    0x4090039120000c400900103582c0350001282624614880c4100703e440521052005251060808001149501e440310400201d81100100517a0a031100b0000200028400c0709001b0365010b0401c0c520041d403002d2103041c04102000b8071070b105101400f401801040343c01400c2103c2199243c042c1d82c0000c100700180845030510320f6000c1c0591084601c41d803a8440009521100407030580110f4038842e01408005152541c40800f0758002000f13810601c1e101240741c1406c0615100b8110147e039190001c10502c0d4074403000300d1408284256429000d109030504005c5590b901c811240d11000714074081d15400c0140b4600c4a0500620764010310517414080040f0300d540900d031405214a00581c070201c5551180c0040c5803c034480c040014215641034038080c011814440b240ca0f070700e002d2520450f091503685002c1c0300700a031010747c0c002c02d040c0d400260800621280c9000e10103c2c2c462540588619451541c2c2c07100c08005d45150001d02004040d2a01c041402e120300340c0c0c840c560464000e00810b1580701 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 366529406 1250 366528156 366528181
    0xb0a03140705180604090c030812090c0118031e0212030306150703050313080f1803060106090602060a050604060f0803090306101a03180d050408150609040b13050105 73
    0x140810319214103080021945000040300100d102c80d0010b0041d42c0d15658140005080801c80c2643e004425401c00000118400010034031500c0c003403043c10403400c2c07050155003000780780c0034007074104440c0303809051820350b4100550341102d5005440803420314620f040214844184080650320205041f8041c80788100440198803808084884031020394004040c820940a071030030203000a403090001a98800c5100c0700d42002030300440c1c00c141800d14138406031280382c0c0131070014444c40c0b14000000344107040800100d8050003841c1041a11700e41840e200a5440704001d2030307522060303240c1010542940300c65200780b0182070a1040b68951a4440304850f540768070a0000b94024031400c00010000d050044a141c1078501c198048050059100d50380d00342600050240411510300790007602c40310a0030015000b96454132380792a80c48074a4103160500340032421811a070b00210080400002c0c0d17581001c0c0a031311907400b039400314190301c1d01c041e03038a949011440006d00c658a04420b00c000018600e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 366530656 1250 366529406 366529433
    0xc031505300a03080714040905040f230c0f03030703270b09090f061014090a090e060f040507120f020a0605090f04060f0b0a0216030b0714270102010b0a03 68
    0x344c6981c43c1c1d545030202c04030b5800c0d900c0a80b00305881400c0c0028440459650041c07070b00180141e010082c81318180c1c5810000a4448100030000a10400c00741c1054401703101041e40301030103c405100c03c0c00041c001c44c0d03e80c0720700300c801410030414a03401441d80c240e1b030300d000381e0301e40170016000d07481074039007858142a2b07204101040c1b007141000000307408024055130b01340c480e070000b500b6071501c010720040a603480c05020700c0158002c841031168200c00d44031210070320028644032001103001c12050308a24103006002c5c0003002c840960000700000705100140400c205c82c03004000440d8400d460425214050003280025400681d1940c0000c0056010003c1c181441048031400881030f151402c1004a0301d5a1066601500c00f00d40304201d601060800340040388480d0040c0c604030007071614516854a410340080f102026070405001e07056038014810f105041032000305914010680885004410710705940c0341465160403800c80c8164401c0d000300c403624078081c020401c0c16440c0d2400798090f01c0d64 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 366531906 1250 366530656 366530663
    0x1083406050d0f18170706051f0806040507050d03110f25030b0a110403050601090509120306091303030204090c0903020f010203030f040f051f0b01030c031505300a 72
    0x1080210510fa5a9a202d180b80004001e0416113510226a845c0200b00c000d00c206605049030501c00140810301c46e0003021703c00c00b003902c40002403042504a0740c00c1045540c00c01c6019034860802c00c00060000200c035003d803902103c01403043d0045d450704549011085045151500440e40d00e201d03000c10000c0d2132900c084641043c440c07c440d025910849106a03807101401480d114404608002c1d5070360701c40105001c0712050103141a80741e031103d900c0d0140aa020460341c80d42c500400c14403070340a101d1402d481503040c01243c030710300341440042c614880180c940010b01840f0324282d000c0500070340c1101c00502410105018100e59580040c0c0b801d142440240d005980c603040401403584080102da21500f80e881c0d0b182000c0e116500d8204256000400880d05840b810849011099140d201150041c40341803002c0383c401400350004003900c0f248601d15040c1424201140660b282d40400c000648a06031200224101d22403016400301d5500b0103600313004d900100c190110310030b01083c040c400a01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 366533156 1250 366531906 366531911
    0xb0a020a0302010c1e050d0e0a0b0106021603020f011b060617060105060a0503130807020a0308090117090d0c051006030b100609050d1103030c010c03020309100501083406050d 77
    0x180707410140c1748440841c0c05841c00c00480c1c120881c46038060005880c00d26407071034000403041074501d07010b864403407805402d50310582d80340c00403c03245504001b843d44265150018035245440d50380803a25000709030004a06010400c098166030081040b480b1000580004082c03005c15520b02e40b0ba1003400ca001c4064007240104030010806003040070403508018056130354545960344000309803094107441242191503200800503140566584074560b0f001e076000302100e956403106040003500c03100c0062800c425103040d8000f08140143c0100f0340703a521445c50b040004d040382203881c1250805034035100d41e0959504d440c4012040c440b142505520134502c4101c4210440c1e214801500c41003418420168440c00d203540c1100010304001910201e02400790450b810606410f10550a640b103913044800040e60100400c525090100284055081c03075901c01c110b69410901e075503442d071042042e00b60999180b0520a100e01c982c141c424548a09941481198940c075003400804a50202414801030350 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 366534406 1250 366533156 366533171
    0x2032209061a1b0a0606080706080105010e0d021e04090506010305012315010507120216050a1a1803030703030902010e0909100e0705031e010e06011a0904060b0a020a030201 76
    0x50501d4a8070b0100c03a00400c070a814180b40d001070702403803d002040380e91039000300381501c0300154542c001c00d4050003104016040301c0d0309001c0d00038010031059110034100300755031310b180c2015161412010741158040c0c40340d40007800d16607080c2082000d032044c09a040380c03a02c04c2c04410b110300420114145ea01c1880240301c0d100c1c030703c04c009401d00c900f48004800c0d0328000b4081140030141a035150005103043c18891f041003032680390b5000c468085640c5601681182d401d0f101101c40d018103a4003e84000c2b00c680c41c48900700801c8140000d03026404094003000010b01895070109034154180c040d82c01000c60740d907200301d440c004000c0c2c29102800c0340800d0b003032055a40d0615118a865109441020040c2658055040000c0c00352100d10301c41c8165001d088004a1691814450000700e42070071072107401c180c0340c00310081d0700b102d0440e03807104455041100107000200c01041944a68003040c0d00305600d41901000007801820f00c6d0340508269800004e040140940116102c4d003034034000d8000f041902d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 366535656 1250 366534406 366534419
    0x501050907090e0a0e16290a0219020d120f030608060f0c03060409170a110d050304200409030e030c040c121d16030b1b09040c0203220906 61
    0x3100307507000e000f02c1c00440c42c00282560090394072003100e02100700110f40004c0e034004a030100b42d005980200d18951f2208101c44d800c10320490b06d468050003102c0743c940c981500604001e40b5030030484001d40140d65071015040c290b50360f00c10590301d006d40200c01640b882c81c00a4000e00041088801d0b2004241428000680c040012a4117031040341080c00c81142542c920b820581d607540014021584180c0e01c40d00780b80030401100030480c0307020803010b00c0380d5a22101e4a014048061403540e0840d594840000c0070001e035803200959401990004025510f1000c1380e100344610240304011a030410f1034207110b41c00f0316500c0702c031051403110140c0941c0d00310491401804165000000300c0c81c049010b00c007000d040c1003a164031051307040a90340c0340d542c0c112500c224558103100c02d0003503105d50116109003e1081c010320052803900310345400c00303841080180d0344460701d0034000c01624611455950280305041402407080319028100c4000c61040050380b4040c45101c5e202601546c10304078034260021880707 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 366536906 1250 366535656 366535667
    0x140106030b01020a23010504080405011709070b0306150d02030a0f09030c11030c0402040b0703180303020d03090305120a0c271206021204061406010c080304121b060501050907 77
    0x11881a03018013201d20031911007002c00f09030400317250074071101685514898074080c401e4a0240b441801082d541d1071400c000141801031802c070494252040c402813204054001800c80c0031603085158a0703803266515000100349848a03d800220f003800090707410b1145456500540c4581c180d13900c1004040b804411081c01c50f91420801002f041c040f0700d03006c0228031081a41c01c1ea0101c01401c440c070107201c0c2004101660080d40c024156490042003a20416030080c88014070103040e001900c1c001407454600941d1111030310100014141c1c0c2e4000710b4103161084044a0a01390400c25100341814000364a00050904007038401c0010918801c60b0f1041c54a04558483d41151000d25103800f401c20442d4019182c2c4154129200c3e642004250b00d0200d50700340b411b115031b0050b000050310610382d40800c80c0541000b80b0315810401c1010140d40054181c03016241c000307400500f50000141304400c20394054001106031520a000b1040c42002c00c16540c00090507940e056408030000d0721440d106651 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 366538156 1250 366536906 366536921
    0xe0f06070806090109110a112e110c0d0e01030b09010803070b070e010203090411071a1e01150305040203070b030108010e011d1c0302040506131508070806010c020f03060a14010603 79
    0x4901d0740c20044030495903c030784c049030759000e1080140c81c60780300d504da004203101c03103038991503e5190200d2018000d80401c074401c00f09203064094440cbd01e0a0401a400360b05c07000c100c41001d00b444520520080c00380d2299124921500f030282c1540015615450000d030b4030340200b030302101d490a210001514013072140740d00c4140408180c000b5414000e080d41080003402102c0b03048001140f0500110006c00c081c007008525003001520711030b6040c18038003112905815034030401c00c10840c61800400208101003c0880025654540044c00341c0301e42c4002130a20105501c81a04080c000c0004100d24034107502c4140004e02200003000703030b907007006000e40507030541c0302d026591600300c00c0c540e8022850203615099104440d02c0d00614090300e031000199250010818150349260340001402900a000c1c1e0000d20a1603a080c88205441c0000000f0440c2c280141030134100201e01c240c03501151036504c0207600d0107a00405440351480c1c2854030b500148500c440361000500c624000290440c040d104448 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 366539406 1250 366538156 366538181
    0x302031e0c060a0507060c0503100614040306020c0102120901021903051303030e03040b07060f06060c0f14010e0f03030a180507152c010e0a08060105040e0f06070806090109 76
    0x820010010108002c58001444090030f00c1000c003c4c0100083c0704d48a0311065426035150ba5803a41096821016020115002941404081d08602a0004d8110140c401701c81e07000b00d02603600c403034001416019002c2d00840d040c40103145010b2040000c03064029180010201c0c0301c980014413000000c070141c40c4282c43c5003010070503140f00c54012034441d40103540c046030483e080302d18113507a81c284038510358483c040a5600076601d400d4586d2194240c0250401015540b8108a5482c159299009244242c03800244524401c050244841c0e500303400030943d90080000381d484602c070800025441c0d0340211160702c039492038038000e1404440e200502080441c1c0040061440c6414090512650b40c0500500720900500008500e10104080418460080100c41128940500340300142007030b10040e40c80c07032007068062014400500d001039801d0443c3e904440100305070300020300c2c05040c0142d01c3c8029070280070b02803c001409800c8020103000d007000b640c1001050782d8809c030440460300c000b04560b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 366540656 1250 366539406 366539413
    0x18040b06010509030703080405031605130c0e0d0303020702031507021207030c0f05010c03110a141e07051501060512040b060a05093d061b06150302031e 67
    0x10046448162065806801810050f14200c00e9200091a128141d48101c500301000113050200d400e061018820f03c0100b446442540c0e03003060f0003e0b107461001c1007507408240d510070004c49030b02c0c491030303a81400703810140040e0102c15039410002d010354840d5206900900c6031403000c0d451f410a032922148030b112030303a0180c07420b02c1a41c02d0f2889140d0080c1000e8080248109130b050201300e9141c1c480b441c6510540001850140b1014003a056841010000c0010503003445030b2040140c014004035401c114900502d44c0d202e03407580d441c001065100780b8205084e4004101482080000241d07401d12010718041c12031103a903180000c4400340b0441111a170820b83c200b0200b00018880b0131079a03000701f0003c00c0c81a40c03584510115609082c00c490300b101011811204644c9500340410a4034041c0d421624890403080800402d5240013480c4101410001e8440120800010403020060030690080b424010800008004850761201d800260301ca4042c0c5080e00c0d450069100c4041040224036002c1c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 366541906 1250 366540656 366540661
    0x50a091103151801020d02160212120901180e0a090317061f1e0801150215010e09070306020a090609170c0918010509160501210f0e0f0a03080618 64
    0x10941c6035402a007504003299000c6c0b009a103144002d00107407180c1200c008910321042003500402c15040b000190440c0150007410009200d01c1014003160102402800d240000c42441810701203040340c070758409504143c05030184020f18545400c032880c440d0196590060710b40701c86079540c40d2044240c504a5104110302030f10115441c1c071001d0407941d0251804c02c2d030607504444680081d0005898054030016040c140188040c280c111880d40301d6400a10040018148020100a050006003e41c0c4200c24034100001c0ca0710300100109000780d90f1004040d034030f400d00350314007904140c0603003e0500841c240b40d002242c840b8580f18903061f401618030003801c22901e103000b8016402006030407811071039103403003001c0b000200900655000307103640002001d00c01071052081d0000045500b0150411541d4034041103181500c14503007580100b80d29000440014035202c002c014014114000000d010710301e60100992408650900c110b40a0741310a400c0c1d84c0e9100c108000c5a00206111180c4090f6501 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 366543156 1250 366541906 366541921
    0x120a0503070c0c0b0a08090d030204080604060e0a050313080705010c020303090409060b040e1b0402030402010f0305090c0d060f050c04080a1104090501060b0c0d0c020108041b09050a09110315 84
    0x1801c2280c2c003c00b24481020340300d04004c1400c2c0d1085a40001080c2c040e814003080c0602002030483c0c03070300c03145002c50409050107a82500c5c1c030b5028101810858642542c610255418003500401c241e1100489984640d4051038a0050503e8440c0c031800b03020351a800110365008003503154071150b0040186280c494114200f000401c05041c040d52050703035604218002d501d80744140350241440030002c1058200c513036440321905080c10380840c0624014000d000042c1d81103400881c60010310b080200e040e540f400c48140c42c1c0414603c0103580b10348540c40e841d0602100761710649500850f0380c0306015582e504424041c02c0c1c41980300704296030b4031070b00c9084013007007003586880c0c4441d40080020403480c00d252582420740d80903800c001030380980000c0d2001c64460400c0b03814102485414046107800c01500003030b11005004102070914030a5000d03020300003424005501c05030596500403c200d0600c0c1840200038049004129441142800c190035103285c00110101901018107185256550324030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 366544406 1250 366543156 366543167
    0x192a180b0307110313030b1e130809041505120c011d06190908070618030308061c0501060519030c050f151912140c0c07030b0c090102120a050307 64
    0x240064200001902c4080c0c10f01002d100900c441c03034030022100c0ca29400d6003007800a0201c00f805000081d044250036550014038528195403260a611801440c0708043c1040c3e802c1e48503191801d9401840c100c6c0031110f403c0da4070300f0300050314002d48107101032000c407000c41666010341d1491035021591009020500341e103407141da41c0d4032110283c14241802c0020503c081050380d0020f620b40403481c10742c000d20131801c080010400401c00c80c60f10003161421104040080b2400340006001c000c981c1001444070b40701d09501111403506038500341050b80f42810803034000d007090b00032076218880c102c1174265440904c0c1c22200c1943d8001c600c001c40540740c0010040d842c1d0031920843c0d0801c0c18080c0800407010f203030000d81048100c440c1e2002250f903a850b80100348071060f440044007549003503459080140b4442d007103540300c10025001c80d629045013461600d040e480364402003083c02503000704108222404080c00c49041c0a80844403640280188100709014405602000074400d0001948561140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 366545656 1250 366544406 366544411
    0x30207110f0d0b04050703060b151c0603021f030506010507111c080f03010f050604080303040f030e220b0d1a040201140f19020f1203192a180b03 64
    0xe100340b803080342ca60341e0085200e01c102c9050340c0c140c0051400300203206050181d0503c00004444983d2138060007010441a4020002d0300d421407841040c0e10030b120b40032130b800303403000d10307002403507000900031040000c46030030606008180080d050001040d21035003e441038038502d641c0703e5044020240c0100500c181204072001c58203034140d500c418180400c09550042030350f1048ad17803003180d5942c100040003507d03c406600c130601502007008204008000441901c1c0c000754001d41071141c80f0004e01303003102c0800440980c1a40302c6240c0442c48411130035003034051549030b035214041c08503040341c2042011080c00c511020f403404154588214004403803079000703603101d031050500c01d018ac00e802d021107089800200107148031300030000b1319540860300c9041c400c07080300d6184002c2513010440d001a503258058110031801013400030000c074450034241140f2240c86080c604003088145030004000d400c0b159007041c581c120503807100c0f15259051140143c4400900d21041e8400d805291041c84409070303000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 366546762 1106 366545656 366545659
    0xe0907030210030b042004030c1202060702101b1a0f0c0a03020904110307081e0c031315090b0601021e070506090d050a080712030207110f 61
    0x3940b1180c4418222464003065610841d00418080d041500200302680b40994003001842c04a00140080b03c1c020030354540800d90750003108140b202074940180d0458810040ca101504240101c00c0c032424140c41e14480203034040040900095004e01c0c21900c030b084072240e00d811003c490f02c03c6a0040c8448a090a103420010884501d82c811b04c0020000c1c15000f140c403e1141c0c3e160740c401481c00c201c41450703e58a01d002240280142c1d0304645103c0f0b0b021070049a182c200c0070300310002d4483c070040c0c0d0403289903403502100c03040d0207421010222035030900e610000c0426013a41c05001c6442d8401c45a00d0001d051a6001a080466580701c4c0f01181c411005c0340740080c4000142c401c1190804c0d14032543d0340345294041110302c0c812040c043d0a5124030031040c070401507504014111680540500900c40203020003c4084c0c0c8116a800342c4070085030604071015250929120b07170035040 = true := by decide +kernel

theorem cover : BRFrame.Cov 366366906 366546762 := by
  have h0 := BRFrame.cov_init 366366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 366366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 366366906 ≤ n) (h2 : n < 366546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
