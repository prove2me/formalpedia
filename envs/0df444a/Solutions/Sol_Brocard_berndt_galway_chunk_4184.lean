-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4184
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:48:43.286471+00:00
-- url     : https://prove2.me/submissions/66cd4b5c-e123-4dd3-93f9-416d3a1836c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 752338129 ≤ n < 752517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 752339379 1250 752338129 752338133
    0x70b070b010333200d091b03020607030c050109150510061404210c081b10020c060c03070b040c0303031b0c110d050a140c240304030309020a0308030a14060616 70
    0x4004c0403038841c2c008110026640b008000d290300300da20130b80d00c04d00703a105d41004209070704c46505002c1c1c00020740c4020100903800119100f1151400c00300e005030000030f25400c0d0340d602d0341200c0b83c0e0b011011003000d440d2402c000e6101d054959000040403642000c8164140d1070503074181611807401800c1e000302090041c0701760000c100006410060340300d400080318a45800b0183c0e542d603141d00f9444840810f20040e6105814014401d0040320420340003031400c034100304200800381d0003440c23071006288420300c202c00214444244642c05540a1070040843c03c3c114100241911341102c4291a2041800046c9ca0141c0d8400c81003400c81e5001802d44920500d54400914407070409030010b4851720580c1482c4c401d00040b8803030500681c1d00c9804842d00403000c0402e00261121b5054640003909000440b001004040340046030710910038500090100c0c01607000641087c0d003604161054180402000040040c0b40b003004422604041710b44680c0c50010002200ea1141407441b0b0300600c5040c0381c50341 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 752340629 1250 752339379 752339411
    0xf0d0c0503061e07050408030334030506030d0302190809030d05180c01020706021b030a050a030c050d0e0a0512010f0f02070c0b030c090d05070b070b010333 69
    0x405000014161003103420810102c01500c43c010310820340b2281480f01003a81c060040c82182e0440b00c00002540c103542c2c1d800e06c1da80380154030600e0000c038482c2914040b1546c0c115450b44081c2c0110586001800d401d00005041c5004551540201451300c104058200310103803007801000984c251400e0300480cbd9444480c58110300907040c04801882c141000c2c030041c144030900703000e11341315000111120441c160300126621200f912031360003d0b030850301400c1181d48000d05c1c6d52035801406011200d44003007a6540c2da1a023040080113a000455074421381c0c04010050100680510846c6015154a0b42240c0051a6030596100311445181c210300000d001180030741214002130158881040300d02c0e001c4004801940c441c3c14101c1d00480800f402180015100003a00d005903d001c42d03050a220071101400715010301d050090300c00c2e1180c500c00280703601560340203001203445071310b4004007540b4603d4040303010081340e40410300d0301030501101c400b80e12a01060246e80204107a0204104071040394000d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 752341879 1250 752340629 752340653
    0xc0a050c191109010b030604090f020303040617130309060c140607051905030c030a09020a4208060112060f030f050c0907020318041116020909010207020f0d 69
    0x100081c021950082011080e010600081d00d00889280d440c080302101040401e100c24020100704500901c0440c009050580c07107580801d10940c5c2501400c0b01070f4000030300c3d6400075889840010700006000034440190f07020590400c5020701501100081ca50b0301030200c200d2406900e04000c04801a0001c0c050105c00380c1480219500a07a082400c000c03000030311950215071500304408080d03442c1e078202c9200d4022a48620300f4120b40784e00395110781e039400d8040c06031180d017070340c0c4240d0302c3c1c80120302400c1f40e03e02040c4920261030044680da010309c100510f40c9094076401204440c0100c191280c0f0303a0420b260503070060091800b80d070b0751158142c9801c02401242c1015030381e208161004020481c001b2000c0f41c11901074001c441003502441d00704141080b080711101c0058205000d0b9207222240c5850720442248002d0022800284203000d09005811000307000412008403845041175081c1000c8154002c00080002e600c4d02034160041200e040b402d42e002c0380034800c48503002061101d00360081c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 752343129 1250 752341879 752341897
    0x20d090602191502270d050a080a020f030f07170414130609060303030506040525050a02030405101706010203030c07110310020a050d2d0c03090501180b1e0c0a05 71
    0x3c544036145c5507100c6440044c0903240041324140e1440405c420b14000050045807588000101140910343e6280ba0951704005048415071103500d49003200c0031400e00252241da130403140d1150302e8031590f0030107110b60301006180c6044213008101c20310540070740070803c2240900a441302081401403034003a400a080641c000c0140c5031600c1c0000c010154560007a60041070111000e001c1615400c00d8522041c65040c031203007401c50050f00784001180183c010b05078640c0c060065908141d81c4601050400d1a9040c0850004545816556810203030001458010b0b000384011402c500c2d18016024045c403803004060481981a40c52001c42d6800700081c410400900200395141c806107607010388181c00604020b0f1116091141411000d4080301c00700c3c8490030f031803500d01d10f61358070300d80320200078854007082600309030700c40c5103000200308240500b010245181c600c2030b011084a04024680300c40242003266140c59040e110401c903044a104290828400c40c41c8582c1c501d800316098510307200c1c248071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 752344379 1250 752343129 752343131
    0xb07051e1605240609010f170a1a070809010b01120e0102040911120a02090303030f09012d0c0302030c1207052203030f02060f071b06021306020d0906021915 69
    0x4420265040030b00101c2c07600000c1c3c004129a500e4040800420709000d0160300881440400b04000e85c0300308110445214200c0d0707040d01d1103200c49440d40000c007074140c000c5500c180b0f0400e00b4010701541c002001340e4000084802041451682000209100c5008807104052034444243c04000b41080d0304860040c01d54101c10440000e80d980d407004550052021500c0c41c0400038001a00420540211050303410000c001d90702d50b0365403032803109008901800c011800e41d61a03040d2011907250404d0a8066034030b5450240105d0755408810b0152071852113810101401403003407004200310101602c401ca0480400550345d41d4a86804980501840e0049842e40100380c210340b1001c4000003020041d02e000350743d40e024071418202d0aa0340c560303060703843c0403004080c04006170420344601520710f03420941a00c4407400340e1460311560f0683e0444030250300c1503002e85204104254042004030b100700d0312420040c54992814001079141c42c007007011001e00b000040105020411811816000c03486107140c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 752345629 1250 752344379 752344393
    0x30b090f0c3d0f0f020d1b050615130c08040803041b0b0406090b03060d020f0319060b030d0e0a0911040302060c0a0203100e100e010f09050a0b07051e1605 68
    0xb0301004a85480e15440011550901000c00403c4c452141c02c0d02c1800c0f140c0050031080c0e200d000031980740f0648110803c04074410311a04000a0081c022103000d01980c21403400300f8180d2b0001c1000100184468400709413070030000b40346850b00140403e0340a070704070340e44507141d680714209020b4001641d000254002c03a4150b01091420004d4080c1c82070fa030362a9a50031515403104000b58070362005913403c85c1d0042505506000510740010318000302440581659480074043c8075510200c980b40d807044500c140c80d04d400c100d10742800c0080001150700c5c1d20703010142c001c0600c08514000070398002e1821090300d400403048c03402d40760341c10bd9000310f9001c6c0c405983c504503181a07584410128004900c240036015004100005a02404040e4500d2101034103100e400c40302514001e003d101c01c0c6218954a4509224001440b8450120140d000318058403104815140a50348200010644c0042c82010f115000349440004040c108600b04025a0b035a5610805d6980b00301a10a503002426441410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 752346879 1250 752345629 752345719
    0x24100e130b0403090f060302090d0210030e1006030219050d0210030b1305040b1303090b090411070501020301030c0e0705070204050601110a1110030b0f0402030402210601030b090f0c 80
    0x90641c900301c61707800c45469001c50700c50030120300381c0c480d0a000d160700103420f1101c48003600d0114020b5071021410b04001450400410120341000075111a9003c5540da4140400c00e43c1130642c800b15230000d10f007038207410003801c000004910b420f4140d03001e8000c2e404070144094107806a42704100d0420014403000c0f40c913200740b82680c007405046400b1151000c100b03010500004441404100309541030302d485140b2400c255203940c880d0000d0b8041a88641c4070950640300c4e05400c1c000381030081c040d100260b6070350704500300311a03a51215880070000c0411101001300395a402416108103940c115004078164560200482d1a01030784090400240a8104c09100300b1594050042200209a864000b401101a0141c044800c0c400b81a03400002c418900500c43c50300b5802154414402049080f184010200000e14800c2400c8910880d81c8484010b009000004000f00c2e40042c0030002400480c64103070706541c480c0800c1081e1405072a0350b00d0785041c00401603010f01702401d040001c07031200011107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 752348129 1250 752346879 752346887
    0x6070b010b1c18110904020d02190f09022d090d03050f0a0210060b09031f02070f030201021c06050d0201030c03020d0e1b0909030f0d0209060c24100e130b0403 70
    0x840440781c00c08244c416244600380b008200b440340741c008100c2d11001c4082c1d000c2c401da02c07030b5600084601a913906000300302e444e296401c3d8000350410510041c2c85680c40030603810700e400011651225441d011049406106104c030849070070001c250340c00d2002d04c00b14a01a0344a010351560050300c2140403e00d14462503000880e42001c0d100803009204e51550f0b40c42100f807910560300c3c040d800d50081d00c200404c8030102981000b4030501481c005240603500d8843c641c607c1d4801a044006075000220a00250690b0001402c41e490001042003200c1ca403600150b4940d01e982c1c03000381070645520002003130728040c0d1b0545400721f01900c000c0c00030b62850652140c681d00783c0c103d6207101c04042050314119051816010344900140c0c1c0066140140c03200704e54040d0380000c000900c1321602003101f805281c44807005400c1c0741450f440100350321604010f40814011501c2407120182607070504202d040325010300c84108503620b00305040e1054441c442c0f000c0307440c664588041e0a100400c0c2c00d11040640c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 752349379 1250 752348129 752348171
    0xc12011e150f031416060c110a0e010602031b1605040c0e040e0f1005042a03050307030e03011b0509010f1119120207080c0f06130b030603010b06070b010b1c 69
    0x495069485c3d015503440b03445150620360080c1800608103441c0c0300009803020400c011140c0d001801000001d41d21074911040807801d030003100060300013184841c18012800c410b84100c074240707030141c25820350011050120362424401e46200c8d9449005202c800e0303000c1c0c040340e00180d00140040c44142803940000b0b43c3c1d004030501207034032803040c03180f0405183e41521906d030080e58884103840d60070030f076068104084a80081144c11070149044000300048041000342641c80c481d031552100d0800850801d4210303290901c0e211001a0410000c1c0310059200e01240c1c4210300c2400d107080c0c800c3c4512000c8600c4081c412444945206c1d2005400500d110320274018682c62180d2039545c554008400d00f245c03100b0903482410340fa41e104944030545450144041e0b4100d4070003400303250078280e182403082d10703044040d40482d41d583d40c00018080682400e0140d02c2c90501c09864040c40c0c0b0096580303a03401ca880511881c000f2400c0407948000c003204443d11404004a00e42041c010390960440300244881 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 752350629 1250 752349379 752349413
    0x1a060d031d0a2301020c0906040209032e0c180306050a020c190c24030b0d020d0609050606060711040b0307080a0b0703050a090302100902120a050c12011e150f03 71
    0x808454501031542c400906884462000360600e01c3c48d0720350405110103500100a01945400b030204e800598280314003880356500072810a026101842e061090b045a030600306074010401e041d00c21400b5404a0302ca504201ea50203400061150360f0495510300901521040ca812401210701d040402400d055007031284034003c103001c202455842c4c40030001007a400703003448801c6190680140c0d07103a0181d442004450760280130b1302c60a071450741c002169001800d208940c0d40c1d56850071082480810000b06d82d11030019070300503150001584446244054500e812032149803903d0a107100e0752401c0c40074000804072281281c00c100078600d071484205208450520000340b5001c0000c082c83c185002e0381040396050340152208107030b604004030103070003070390010b980000301d040d0145040d5104004e0741010364001c1c00a0280003541d0b80801030701c01030074040320700c0030307810540c44503602c040320504042c00c941e1400300044c0180100d151240c013504181e1012000403240c0c80e000080c004544d41840740c41c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 752351879 1250 752350629 752350679
    0x60e160906080607021908090603010b1b030c150405070314300412171306080603061509040c1e030302011410050120070306091a060d031d0a 62
    0x294940302c1e081d0b41c560f4122000360069100c0c001d800005190000c3c1e403203c0d80e0244007130501e0007040d94041545030f4001c0c0e2007c8807864000560791500052800c00041010300040650315240e003404507256200304074655494420803100200301005010071070f080003076500c41050711610340c01000b8aa100e840c890409810240b071034510107902080300000c1503444240641b043d050905210075480b0701c942046045440c9008491f9403450944108083d01d000103c5420007882103081034001801d04402603c0a80642d01202c10310200d60b10412030200d08030f50640300c2c0d20095840d41006c0b080c0c1090f0303602504210700741e0401c0c0c948150a456026060f02d020390000e0080302400d40385400d000d042100ca4070b0071104004424800d0b58422450b04080390600f11141c0b03401d00c1c03404400d504001300c41c0c1c4121007a60352000384c41d0410440d2803240e2542c803c03168101c145450034a010030b6190400040080412040240d040480920141d2289100201500e09101c09448081406441c0c030fa031503600c2811 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 752353129 1250 752351879 752351891
    0x60903010504440c010b1305010801180b0402060f07120201060e0f160e03010603080313021c050303010506090a09090302100e070f0b09150304030503190b010c020d060e1609 76
    0x2020800b100c0300f89003050004803e60507102c0b4450078070a500b241c50404a00d548880c1c00601070399030340500c0038104a12640c0090103500d480c0d40c09084911324294001141365162410020030750281c2c000d0381c02901075440f40e5440d50408030030001ea11600d10010119200d40d2a03801070b2560550003d001c1c0d804841103c0c0c0c00d03481d8000c0644201174100c4d00d4200900c03060000c840c030b051041c42d801030728000c00780011900945039a40c15541d90012a20340040096003170103402546000720140500c10f1010181040a1030a07864a5881e44414081d407802440000b40006003078543c15200c000400d038295040120030800d140003520307107004c02004280302e4100600d40560b04070114520003280c24848210001c0d5150246080d0702d501320100c144d900c01ca00c1c00005042c00c0004009501c103a11940d60035589141c82e1b1401903507840c226240c18402442d050541c1c4590340c000e0346070000107030100d8001d1341c40c21080c60b0850162078480400c400e24090514452101070b00071541c0019601822418490303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 752354379 1250 752353129 752353193
    0x3010914011d070e150d1e020901020604030e0a180903120e0a02190b0a08010305190209040b060f030d1101050f0708041407090c0c03030b010201060303120b060903010504 75
    0x107482d40c008201d40c094812070110b03a00320700445a0201a64001c0e00d081030007020381d18626503940102c90030300c00c82c64441c46448429409042c100c21345001c201d20450806c2c2040b00000d40d9140b0090009041c8446190111604da4030300300301d40d0043c41c50781c501c41d070348291061b0103001030400342d80101d0110388003014800b1168a0740c09880140c820f090020080d042d281e400300401070100b103038821a0000e1710348010a03000600d000501d81ba010710b48401075594510f00e4100d1030051380a00300b044080301e01c40201c0c0142e0700e11043c02e40164111104201607111500040e007198140308003171f80e26128004400d581aa00003016240c01710940c4002c100c50703901d00c4011a03130301608586030000a00380e01e00140005003920011507509600b0000c41300c403030b5282d192440c102c50810180c080468001c01800303040560502031500901c2080c4002d20801c1d10355580501071400d2802c0c00f00d003154640c1c14010142d241c00040d40c0c09544020700904c01c0307003040d003030000f0481c51140707800f51004420403100c40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 752355629 1250 752354379 752354399
    0x8012d0605121003172b0507022104050d0302010b0301140601030f0504082b0905030706110c0703030f020c040f060e011502030901030b04090209090721050714010c080301091401 78
    0x2040340d4011170781c08092660400003040550014006001c014000050000303850190308031019180080540012541081c0b0f5000e842d204050030f101e9400c2e0428420544045000c0c4107907002c0381c0d0103480c00f0a5050b07080c0f03000c0e409003c03801e107a640c156281010ba8500e4a60b4a52014003800b03003a20100282220404c00c501520801c6502901c2c3d4181040907000030708000382c200300100030030031481c03602e0700201c1a034000391200c4c50310541d501e40c1b0205041090001611488000500901e4203034500030005130180d0b19500c0c54400601808202814110b41e24000d001c81c4c3c448003c010001c020b80130030192810020300940c02007a4110610385c0000c600803c010081640c15509600114209280d050044010382889442d280e001919080c25000503261005c0d064002c1003070001401d02f841c10300d800c02c46a03d08616880401e40c101002d010b01040010034140241c40b05c640050180040301001601e1070340c0b0845c00100102c00000000400c0100e5501c203440303030340c46012295a41d036600e0203150 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 752356879 1250 752355629 752355661
    0x30501091103160c14030423090403080903220807060e06040b031009230a1503020103050919050307051212150f060d0b010908030a08012d060512 64
    0x803041c00108007140e000070008070b85044035195850400b4102d180340c1d4410311441e41c01c016071140d80c0c2c00031a042c4508942c520b60710711680c0d20b8850743c103603111f010000111401d40180014090040c1080032070201c51083c0704480707000c803d801005180201c0e0600e41444039085202d2840140030722070010850074425078101010110040c1264201820700450382c850b03a00c05410034820707821184e80002d1a110900901144481c1801c0c000102d04881800c0c808040000305440305e05442e001e240c03d201001c3c91031a10540340c0a29000910740d0701e2a040d2841c00d08594410b9180f1f4511a25050810500000078510390f0b20980949136401c0181d2400c00d450300880003030442d103840001c00209030071070030f4082c3e52210340e00600d00664664091701040b000c2d03100507503840c512a1140e030004c0155811800e040001c0c41e1714401185040544e81c3e00400d0002d041c0110100c0b1070790b44941103502d4014040000b04648801c00e0380c400c0c995190b0000d803a030351144404c0c52950203100002080d81420380c03110303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 752358129 1250 752356879 752356901
    0x120e0a1e0509090a0f121806050d0906020c0610151d0d05100606120c0c2001020715120c080405072705180c03121911011b03050109 58
    0xc0044541420104540b401c0d00500032480380c0302d031a208502017078000e8150714030b0314054407a80412401c4114003c242c400d54490110070320115600c20048594010300312880800d5008000502101514001019129064048502e84140020320041c5c48001054204403040c100340c80846030700480007036800c258100c480e004040c0552100c40d203076040c080b56411007288a0b6090f00c1c00e80c40700e41500c80844145400c8000000e40030359040c040c2c1c09492054206000c940c0c18500c90040d220f0744c0b6003268808040303940daa014800620400d04d80d0080120344040c00d8041049440501140b000401c41e1404c12480741109040542540400d07000b40368040c01541c000000d0441035091105001005031440342c2540801c55440441c00381c5041c500c600f90007a844910348200e1488000400743c589191812060b12031b130000600c40c96100a2034045400d1005039800f90b10089640140c1524100d200101621240d42403140454816512400c00c144000064804011590300d036070480e001c03602c404102d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 752359379 1250 752358129 752358179
    0x5181003080901140c010911040605030604110f06030112061404120815030a05070503010b0609060711010c080d0c0f1803080c01110c070f0e040c09090f120e0a 70
    0x400d20124420030010903402d5010704019150015240003111981e000d800d901c401a551001e40380308002850036601529a4102d8052180c0340c141000a5101d5501400003020440d6541071032015803a1081751b00c010f400003c00c080c1d286c2d0703580c07400280c13851286501214850726126650007400681c0d0140c038050340d08003a10008200c41060140c8003a08064110f8200d4455110801d1003aa000c002c096406807040015194441c80d0070245800d4a03006031070b0070710038001132016240980b034031070030b541000e8bc00501411f492040c1c000141d41042240c0000751101c1800a58450040c0440d0090107034a1001d41d9a0071100c603290341d08843d01c59002d0030300b04601c0c2102104101280c280005014034030a808000200440880034140c42035028241090b03a40d000301c00208404c80e80c480e01d035401411020f2041c041031425135201d0340d42c0c1026014030100c1940da80c101c982401954820700d024254000340036415075080040c050b012091080c0f07107a00c80c001c540c03000304000101440743ca0090a070580 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 752360629 1250 752359379 752359411
    0xd110a09051002071a0c060c19050f070c03060207120c031d0f0904050a030809010c0c0b1f0807140d0f060b01020f0601140907050703020c06030711030f040518 70
    0x1c00c0151240a00240c8011407140043c0494004140306141c44142000120f141e514803c07001c0392030401200034800030700403e061002004031110043c9100000f0606c1c079026540c4d020901090505000c2c1000103040c01c400500c0200420840707900800401d4001d0703803418402c0e082450216102d540c0c0440c024001040380341c00018800d940800344002c0e400050042e814160b18502081d4400c000b180e00791204d074400e0102005064001aa1a401c0000071000740700341140c04201402400c04a00300622900c501710005150181c40085c0c1c00840003210360403000240c1e81c220441d5180c02c1c078010284d540821030038007016880c0c000c44c2101c0044e8085908a050a81c07030b1101e500911614200300d042d0300034802c020303c4045c014031155000c2c0079095007914854440b2070900c906030000801034824030404001803001b01c4d07000942400050300455030140e907903990b00811548101c03000085c4040d48004580d0032103c0d0400c5000d0f0043c6c3c0c801b500d0711010056140115011810195111001549012 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 752361879 1250 752360629 752360639
    0x61401230325080102070b042607150f0221010b0909010306020d11190807111b0a050a030c1e0302150d14010e04120f020c0405041104050403050d110a09 67
    0x104809403050b500c0070b000c00d002d603034508036800d9130b0056604540810140042008100da40c404a010104400800c010350480c0d4140000c150b00c98020041e100d07090f01003030f482082e84030341c000e00103030394941d641517454544803048002c05008079402840140c00d401d00100d00d411540f020b5030740e003440c000c20441e280d900c0d5484040083d030002020315880d50302c0c0c0c4a01d01c1c0305503505c2c000f4122000c1c00c05c40d400c0200401d0754000c001010280808003040004940c8010075140000e8000175080c520a00c0042907440d00d002030100012580603e402c11411400001440368002c1c01604444440a14507403a448121000c045d20526010003540700703c0301e05e800c921842001020b0601c1c04101400021060040b03107001ca04240c0076400030602400c2d41041108020117007821840320b010908080814001c40d86029417100d42d01e4028501403656000001c0a002c0305175011f212114000d001000107081605001381107901c200341584165003040710f2203220010090480381b00340501d59803800094141 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 752363129 1250 752361879 752361913
    0xc030b01020d0c060204030206030f0a0e0a030503060f01170a0e010f0501060921061401051c1e0c05090709060207150203070308191506110303011a0c0a0614012303 72
    0x40f450503203003545e082c04080010384a680046018010b25a00b40f80c00b0300d0b015601005607904800008a1a080303800e000740080d422a0960f90030110848806d080d90000300e00480d5000551542806800b0340c6800f0b003d01e090352540b100846203c600700a102e5000360380c02c41d1042e00c03800e124103000a605000200840260511030040c1581c420100c81044500383d00c03038000b500c0c10388050f503204d0142d210040145151030130105000c0422000703411072656003621110a940385200b0700b611030790800e0407004100000b460071340c0b01600000b00406c0301350a01c241e005145805501416000d44142c02c80801c1c0c03010304288021100900380c0c02180713408103070b5078100c6000360007a20000f559501e00e030f0212665649401080d000404450041d40860b182c10001888210030030820b10301a0401c10041c48005109040705a403600b600c00034580c2c81c120314048914002c4480c0c00a420f25240c0201c2c98030382d0401c0b550650490b6242c20000484902018112038250100c10015615901c0000750a400700c4007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 752364379 1250 752363129 752363147
    0x312191503051c05120a020a030614090a05070306090e0109050f15010b09120d0e3c0607211e081b04170102091809060406050606090a060509040c030b01020d 69
    0x90349042c3c0e092003c0305c0030404c01000141c0e40c81a1807a008148030b88216410f20950005202c20162100317030380c14240101c0c4015001810308144640c0b1180000c6016000b5004003000f4030965404004220701c40070780f00d0003041c01800441d042d010300307607105039601c1000980128888078014014501e03480c1000d82d100561210000a8100083c040541820042803001a4155035541c8a40e00c80711651003c108080d03131105517a00c1c1906100d03007800c052f240054006614035032013003c560a0700c401880000d08501401c4002450445c60559400d07103007034445001e1107a0b4120741c07548016903141501902050000d8801034001542400c000b52041c00d851044061941d0301c940f02c0c9262a848400c40c04450422000b21280d81c0c1d000120100203041c04a062000c4804070ba11400f01c5060156407a0344070103010b00058800c0d606d40c00810010350310a422105c403410300030640c1c00c60541d00c4002404503080340910318441d6190000c174212542c02b034050070300020b80581c00780810810010043d20582c2c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 752365629 1250 752364379 752364433
    0x60612020d110a030e010608030301140409060f15080c01020307020607030813020a08010e0c0301270303020408070f03120c0b1308070507060503041203060311040509031219150305 79
    0x82c9540740da81000555800906440402e5500850091019070000d800c0d1806503200d8800c9034030820042003410b030b481c00707031070105c2a00301d5000c2150b000c02d05149026000a940e8410158900305110360810300c00105141120440c005642d410203039540160b03207a014504020750040310420032480006d1103595030380d50150394004411500c00d42e035000704900300d00d00d0700000400da40d2111a40c0d00e109040100010000c403c5000348050310312507139900c490b00720560030308800b011141000010035010760103440140800d0000c54040301c3c0d9800304008000c440344421743c0c405401d0002100114846d1222900c1c207500052a1451512134400c110165a80184161501c0c1d005101e0400083c4d0305025940c0144419501d0743d44905040c241089100c0780f036074180040c546004170800004201503004507103030008590004042c0c2d9919403043c154490070040e81039441c00303202040040c29441004d1b00701c50200c1c0c0e1b4200102907141d00f0384500025140005441030303010f00e40c0c40c4c1d04030b490755480e034807010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 752366879 1250 752365629 752365631
    0xa0305120a1e0b04060b040317032e060807030b0a061b080c0a0b0c2b0209040c27060e21060408070611040b1c02041e05090703060612020d 61
    0x80030034800b001039806600307800e60a0b1591001c1d003061030130780501c03006455485001860245140d0f03d071000c050040164020a10300440022100e5035019414491036010030b442a041c3d071202110404500300e1401004046105480401e804d07900c60710810350f8039800506850082e50400005864055040c1c502c822103d03164070794007001800210152031f0105012000b000c00c60701c03510b48210b01090040240c03140302c10900c40c0040c0c8044202014124a46214803d21100d44001070b1001034810242078076000703810001100b1006a01c807140714a1440f402d011050041b03803076820340e100710455200303013000244c50444901641c582040700c1d200c18a10742c1c0a80c0c14410142d8126401c0501c00c55058075604400b04960040c00554002c1086046910010354039043c03c21707480907900d000b6030004a46440e048091400911b0965048402034150f2a0964070320020204e400c008034505801042d014448003c04649410b00a018840c181d80d465140e601a0181d06403c8100942201151000d81 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 752368129 1250 752366879 752366891
    0x309030e22090804080715120e100908120c210c09030a08071a041a0405160b04030201020c040b06040302010503090a020a06110d1106191508011b020a0305120a 70
    0x40e030035124401d0203030722030749400f40c40e40d1400d05c4103401c01d00590300c0441e6034030030a00e50f080450350002604c04030400403080050000c0c4450b01642c509151225034210003458421840c05021085c0d0181465010000102c1026a5100c0c0081c0d07260060118411a20002d280017900d07030398647c44c0791030380702000042160a0051050000349814507040051707940c000000340620038403200140304208101c03000007400031b0307040c60b07910f000400d0400c819141a258184000c1740130000180044135803a156140f540c07001540355404048203a005100403030162084003842141c5080a018000c7c106000800382c5050034a190015180c5501c014103500032400303403143c10001a80c615240030003070041982c03a40ba038107a2180415213030144008000e010b00c4001040080800000258158080001440c1c0c024040f4001145d00c0580b0f203240c3c1c0d41c1484001164007140041055007c4030040c1c0c10b040c2002d807040d00c515000ea842d05a102405000100c080200c803003804940001c140d040700b0580302c00a00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 752369379 1250 752368129 752368189
    0x30b15060c010908091c0206030a09051509060711010527100504050604150506030607030c0306050901140411030712021e13080d020d020c0f01020106080601030f050d0309030e 77
    0x8480124030100c1d130f0640c0100f0340541a040801094850092070380306103031010401e0300001d849010080a91004540b1009107408128003840310910b94113112074080b00b10700f0803500c41600c41e4000c07a000d1002a0034404400c06115050060074000c00302c1c005940150031018400c0500e643c10965100614401d0b070b8441d0220043c24801ca500c502c4c002d8010f892603040901e4540c0114402100840c00641040140140c0d55400306616410020318100000d008041060a4001d0403040e4000b03130744040c00e1000002c641e090080c0c0503d9030081142d0401290702c0c9004d44181c6400103450340d0000400303d01800024929071740c0104070140e030310f0728181c04078001e100c40c040c220b901c50240b5100030800b5660802203407104100040c04081a40060068550030100c001d5403040e00c1c800706440307107030035040a84d0300c0e90003944a0380c05050000160b40c080e42e100d0400060600c400d1000b2102845034a84421800d4800c2c8105045154155904071001d102e00b810492002d90700c40000070800754503001c0c440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 752370629 1250 752369379 752369381
    0x209130b0126070e040615031a04110c0114010f0311040f0c030209150c0a0305031003081b06150a0306020a03111b160e0c030408070f031215030b15060c01 68
    0x2c0c6120203865284491500c51401040b81d250b2651aa004030300b040700a00250b40e21b131081c0207541d16140350005a907000c52401c80e2010303103219292078000b41b40118000c91341e10140c0081140580b90b000074401c0c007030122103903900c10000344110b04507608061400e200045441c80d07840d0703140c10b0041002c6040c00c0700036414022204110140c20101c0e03800901c00200d0708110041c1c440e00803038640c1a0342400030a00c095611802c0220000302045070000c00201c1d01d1600407055006503070489000c945400060405804850154121503480e00c21000041e48008094044011100002e00390180d4a1302d1540c40d6400394001c0982d0300300b45520f030100d00d68003001c500c001d00481030070880001055440e240e42103090410454246400d080f0b81801440707010760042a50f50040c040501c510b41d00d90300c40c10800500d000b510001040c80c440ba82151041c158401c07040d0f1741160b4400320400c42181c40c003113107100716542d42c070000f0851800d90b0002404004400c40302c001c0e560029200307610313001001420038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 752371879 1250 752370629 752370677
    0x3090c040204090614030115180e01020a02010b0a0e04150216051c0314060a05010507030212040605030414010905060f07170a0c030b030a05030f16060e060901050a0209130b01 77
    0x148009a69100400c9800c0303c00040c0e01a0170402c0e4020056403015100050b501c10340c03800b0707803101d15140344041202e420b100e80c041019500503000854135030042d800001e0181a4149110f449a41c5494003c240310461101032405580d0181d9542404201e07040b007940650000c0b800400346180600e65071010a1060041d031030001c9429080042000c04507038003a003101c080081c80c1e281100800d00b08040e5481d5104c100054a000f401c000d5110080b07407404a00c0c100040c64542008403000c94001000d64120b00918080c1344249442c488600e00803103060f00300e507645c000181ca40d50003840403ca0380c2d6414045181c101e2200e00d0410901d00e1054602a03d0b00c8003a01c002010a6454102450392a854450951400801c80140100300301c01d48416a880c06201140c91104c4800201320600c401e60205821503158090002d100310885004a01d803100021104901c0c15401e0400040c000c40c081d00c00c0b10316640c0f0017880c0b60400021500c803d0024040c150101d41403142031a11200541d40d200004c1d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 752373129 1250 752371879 752371889
    0x8010203190509030a0c140304080714130912030906110c03030f07090815090c090901020705160f120204141303030e0c010804030509040902060c01060501090519030803090c040204 79
    0x41d844902890740701204450005001203000d410a000110f1400d80c8000300c103000c0d603004200c2c14520101620b02038110720a030b501014052141c0d50300019105031014403010089411101c5450399030100040105480130400000c04078032044d070031000102d000e54070201202c0c0c000e680c000b0361102444034618042d1b10001e01e42050f54404001c01143c603608111803503102c1080e1500015241c9070a00d02d9544010710204488449e00c62400a694014100040040c0c8040140800054200440480c0c001e40c003040d010b58950280d000c007003030602809452030044990060300d00040c0e61030102d4001400d070710010101c0e0300c1600c41004242d40340c410700c8000c0c0a0b0500c00c01c440c21105151601804450b81c401104160b0780004d10380541c02d0303800c5021a64015054180f0a542d4004280024010000130364000e40c01007000c501041e84100c154070017019030b282a200c1584442d102c904201d10040c4080c0c010407405040e41041c4001340c03c01002e581c2092941003203945407170703515001a042e60030680003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 752374379 1250 752373129 752373151
    0xb040e0307170c030a1b05011107030f030b0108060d020307030b04140610050f0d02120a05031306020625200303060405070c21050c011d0706020321070908010203 71
    0x18090501c0304407004084580e0715102c50601d0701402515884d1a03020307445421040c010b082080d001b000140650200c03010394030100070407034030004000205190300403550030340008203601c01e0414580d00902c589424400f050311027841c40d584580401581a2210104980500444e18000005100030b0500c13070086124009c1c40504039038240d0201e1500100818980015840750350412650321642442030140005450b01c85d5a1001800450a01c00c12902d0f00803541c403078034002d5818401c010014140080302c1010090070117540c0c0380c04903a1444c0a03101210500c02c00e41c82901351000300381d210380b21140c40742408008140041c0c00c0c0052040d80c40c02400e4a43c20010403c070091400384140c1c1c3d0b202c505e81c10f01c092540050303140d90450300c0500c6492180c0a486035074041c00f49000308140ca0070341080d02c0080c0f101c0007050650300e096401c4452070310114402c4410109400d400401980c1d03442444043d407080e0440035070b86045c4a590050000824000a400c01086614003800194450817031806 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 752375629 1250 752374379 752374387
    0x20f030c0d030b0d120302030c210901060f270b090a06210323091207080609151504090602040303020303090d182303010c020d0f08010b0307120b040e03 67
    0x80c01505a800d0044084c1c42030100c0781c2c200700000e0a90181c01c4800ca414a40141c4a0b03a507035501101034811000134800b051301452115101141c1182d49a102c0c50407040203005142d03a500c01507210000c14040c2404403d5050965048040100680c000225006001040c2c0361030700004600d6002d02503030f50f41406a19280300b4443d000183c40907000d000c1c0c4540ca49c11001469841c01031041c07858000c46022a07490381c0a8110f43c1c440b840503100b0309a801044000101c000703941e07480d036030025441982054000d000000302e10b0100030444903030280c901140b04840d076aa001141c20310310709102e1020b80c480d5545951002040c20b510140000c1c512035001035949043c400f00c0603151641110304c04c01007100d5000c42c0400081081c00c450300b1580d02903040021400c1089540b20214840300e030300340c1c1544c60700e650042c10942c005034124000720b80380c440c044544101517085551040034026030a00e00020004600110300c500040007512003c02c00000d01c0030a00300c0004c081e02d40c941c5442e0b0f110f40c8081 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 752376879 1250 752375629 752375653
    0xd15020904060e0901060602150106180302030d05070204050a050606030610092c060406051f020a060e031b010c0c0b04050c0907030615031a0d021807170a151401020f030c 75
    0x4446e00340a003190340010b0492444101d2101c5900d03005000350400c0120380c81c880aa414100c039020006541d00800f660085c11140300c0050064200d0b003000d91286051502145215409100b03c60050f18003920007842e6540340028401e03000320510b903410801400110015580d0302a89140e103413030900002d03484603054100454003031034002920041c4a14030b0084104041da44080100762540c0007150288c0c8401c90808e000e80c1400b58941e0040e1100381049011085224040024240124000c00c03003d00114500301d03403400c036041a505200410400c88030240440c503034400082d0322034860812658410b5030107001c04e14020050705d4101c0881d845081c10f11110040381018044100d0b2071804005003942c80c03c017142180b010b044054058000341e040303c1d05540b903c2c0318128011440303641c000b043d402d040c04001c00b00c40a40e11001034401121001c980076400c40c2c050032249000c9031101d80d403102e0414810004900084144d907040d0b1050b10003900c002c3d0000d00c0038000340700f422070280040d41d01e00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 752378129 1250 752376879 752376881
    0x100e0f06010e1f0327060209012c090a18050604030f17010e0903040b0c0601140d1208070e13060f170601060518130c09090501050d15020904060e0901 66
    0x10103400380c482c41075000c1c6119041e403c5148190880d0342c03454003050101500c80300c041c90b0561113462218403001c18090406010300c0d41c0040c6410300003a680d24628110094000c0d210701c00400e60300c254105294044000783c0703007c02d0201d40140c1c10441c00501052a81d800d041d1584540d03008894682202d000c1009064110b01496250081410402c6070f220400c50184e0b03501c0014000c0151185080c00840c0c1324030f2042055801030500e00150030780d9111200031241c0c0c1c0d007009110302c4c0352014000100095904081e443c0e0140c1c9079200c405100751022240c0269070128000b0f01e80f40402c05805136032903165441100701044401243d00014115040801c10f6003051550307007101c80188540c046214181c000020300604440d02c03460101d03111071542420311015140704c01c5241d031051182d4120808107800340c1c4002c80480e0161600101c1750b82d40c0d00d00c00f0555101340714450b8800741c1e48000c00c000c542001c5500c5050183d242d40103282060150016080760f40c150004d210503020a01002805842 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 752379379 1250 752378129 752378147
    0xe0102162109150305090f060702070e01050f010f05180621010927050c0603191503030e0112110d0c11010204051012200d0b011403010b03100e0f0601 66
    0x110b442c000200c54141a9507040c003141c6403a40703804060341c810000307000704002d00c0034404513140351068a000d07040444c4000d40d43d000d81c2c0207600d103651808000007801d1402c0b03e40ca0170203a9041c3c407003100501806409032402d030001c9141d151103081c88100c240b042e586640c01085101c40ca446050101c200346216000e03c8030058101c81c448a1900382c1072007070900c41794074980141c02c3d5650502048081807070316606119520504a030001404018080c20481c48070350710141010320442000f1503941e03031400c0d6004000c41d100c0540400e4034821401d4155100f003c410043d04a5144042000d0009031940030742c42e80114950302019030b40766250282940e0184403a8a900c034024029810310341000000350700c421240c0300d110244998035810001004403500584800300401041d01c582c070003038003640d10b46540860300300101203240259071402903000b4038901b003098070440e41c1c0d1400e503820302011054603030025184041a5800500001c0d2920304000780724412404640d40c44194203002c0c002603c102c034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 752380629 1250 752379379 752379443
    0x50706140702010c0f0e1e0105040e0405031801210507020a140d03060e0c03070305060f0405160908070b04050609030307050f01022a0d0305060418080417010605030607030e010216 79
    0x150444925102d964003181d1303030266000314585c1013507541f200c00142c0e91803041c3d038002e42e000c001d4030003008207205012024151400252491007050ba038044011200309200e200800000d0804000280c4200ca07540d0049910000b24011140c0c2082142c942c0e90780c0c10900d456040c4668401c40e40781c0c001d95490301402004003802460009182018103032100c160200802c01ca0415684000280807659804660480054041d00401c120b0516440d420102ca440c80130010100d11104000141c8802c0094603004172501c0c80c040e1414903040008100c0c19500012156615200510600000c500300f030048040101400000681e1444400507100c10800c46d61080100d80b00c805821100408010421140c0c11080b031030002480c3d81c610000600903d92000304401c4840309a49000030040b02900800c10740c1e0300c5030baa80d4482d540c04806a0700f80d072094012290590040e8000c030b10024025005120003040c06000581407003a40c409682c041034261900f965091500300c500b5450101078003640208030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 752381879 1250 752380629 752380637
    0x3041104150308030408161104110c0a0f02150f04060f02160603021308010507050c0f0604021c0305041d010924170102090a030b070924050706140702010c0f 69
    0x1008101c0840e00305402480b000d03043d40000000102000508000c8407500840640d00b00034001550400a501d103103c83c43c0380340500c0c60304041c1e00711a025407054a84d800b8080c801010b490032079a40303002030700640c40000c0782c021094005082c0980c0050019000c4148240f42c2c0640b5145020300c001c06000c0e0b040f840500355084000807a1040d45803490b600c0981c3c00c14240981e4865544081e1035650280d6409035401c3d500e00700038050010fa000000b480946022011250003048034002c6503242c2c142a50700940c04416107400c89621509910281500c50003400c4c501c0c1016503800c0c05200c5e01c41d02080440d003c006c08401484030100354810401e88644c02811408101d0701c00b011030710103041d58012144210114022040282c40940464180001c064000703802a9601d00e80001c1e050020b0380c4810108004030804104040c50505d9416501c015004044c0e0705441498191a00e511190b02070f100c1c291207102100580140e404018050344041c0e0000880e4200007400608901d100b1406400300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 752383129 1250 752381879 752381891
    0x50d171509040b060d060c11010606030e0a1707140c15311e05012a0204090312150e09390a060e03120301120b15060d0203041104 57
    0x9880e41c246069210b548039094075000c1c2c507004e00240b041001364000034040341c2040d00c1d12142c158003051030301d40040c2c2c05000340111a192074060382992000d08240b80c15034851481d190125110346920f410301582906120314050640d100d00c051000c4800030072890b0b034032011a4512a04144403140c03082110700051701d0802429003400c80b8218140203140c084803001e9080e26825a40d0310007104004c04058452b07101000d031107048900810f105101c1c8030301140805880721410110301c2c1e95049101c401501440440e015642048000e02c00c480c8141c0800c04282041d092604141c401e500c0c2c061204004000007c1c0380a202c2d480942c030007480c4032500c0d00080c00c11a02511b400e07022070b01e4115041d9544c0c04200c4600b90151510040303400c840d5105d00b030381d44001101034201c03001010848040e41501c00070300001001c2c0b20301b480300b03205042422017507421f854081109030b10070a820030a0380c40d000300c0c0d203a02c00c0001385090700a490202240f135800028070082000d003005001d840501920b0520130 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 752384379 1250 752383129 752383171
    0x70603090b060d020f1002062401082e08010e0c060414060d02070512040303110a0308181203091e06010506040510030b150d0b0102070f091503050d17 66
    0x7100506028003442c103100e001c00455440482c0481e903100050700300c000720b40d42c601d0000c0d940c8509441c0f440035840f80c610f451080c0f00c0105d40c4234640d16410b03101d013210740e115103118011298034111036415001400e010342256114500000c00141030140001c2000c004d080900ca003000c1d40003038028445c0c1c0301080100408001c1c62580c4c00548800c03240e59403104503074400c410280c0b007001001003244c040e48040c40355421486001c2e0003502c2c040e5544008074403680400c0c0fa0703075006420b030180106150800003800c10143c900c20000e241502c9065516050041d201c0c52295007060310441e006800c0300c031888039070324480b90400001d1a0580c2c020042c6524220100d0101d03c145d0040c87e0103007031f02000b8269400c0c080d401c8425170038006080684d407048a100c01404642040c800391040c6801d040c8171410301e40c400210345080d107075400d01580941c0d141040d004001c141c412458019907112000000c042102070180c0c40e50041281c555030f00d200e00c0c40c1459044000010441e00d8104115440502 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 752385629 1250 752384379 752384393
    0xa0f110a02150f15030c03070306051b0301030308010b031f29031e04081603020717031206040f15141f0c030e011103030a0609061502100207030302120c0a0207060309 73
    0x7030411985401d08400813203140c04242400b105c6100d1540500c02d0250020070091190700803846480010b408111000507422203046610003844040e0001d165500148044000880210380010864521182c6895403c4c45130700b034102640e120981d140d0240a00b070a0840c0300085082030000c0d11500980786284c2207210301180e08507040145100d051040010307040107200e100321080c410035115104405555481e00a40d00c1c219405081003440110240350700c0280000b007592002c1111400508550707451005003c006e1240c1c9400500305600c030300001000d0070819036690040c140050100c603200b030b15030b02885078240300070900d03989902d507030382d0300304400c5900501e0040d2a55261401001c0001c0c0800121220030b01d00600705c049000000600c000010300d50701800868200b42c20600c00265100b0701c6810b80d0500032007890158115815420310200b09a00419150748241001401c01c90100f441c140e1440080741c201d03810640c005810303c3c8003501080304070000d0155103030078002c404555444003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 752386879 1250 752385629 752385631
    0x2160602071418040c14040209030d0e1f030b1203040501051b15091b0306070e01140d021909210609051e030706050f060d0b0a0f110a02150f 62
    0x3520849410422907407030b03076003c84081800800100030303040783c00d150811004446840c8610403e084001003a040c150415000f5901441d2000f00540000203000f00c00751020300e06802515849080e030701c0b00d110004442c503160520802c42e41c1c0c00044c00300001003404900c02c107150200c0043d61045c401001543c8c5e2100450301200e501812001014036203880152501c445410001d141280140c10002100307000525820484950401500c80185540a26450384400d8912000240c56004084c10550081010800768000f0a08151800201c2c00c045001c07a0801c0c50b240941c0001381d00c9090300541d10000c9640036003032a4480d2a00d418075204041d52812074291300070820744d03e5003010300c03d014051003281c81034056016491500401080741d00c2c1c4a038090303141291403a2900010507048200b00994601c501d1300a4400c0c00000f041da00c4442c4d00c0c4800800404400ba200d541c2c400c05100e207805002010301d52113048545031510044043d00300000702c0707039413002400101e041026840c546c0c4011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 752388129 1250 752386879 752386889
    0x110402131a13060503071b020f011116080312070504060918090203152a03060d0c0b0c1501080316060e03040b040b03010302090121021c02041b0216060207 68
    0x11011007466000e890045006201a05410703180c038a10018000780c000c002948100c005955421030000e001d281507070101c48419019400c081c2010401140394051844980642c28580c01c0b80e0100340820500000c601d86034000068036003011903140d114a000c1740c04c442d04003106042031401e150a00c40001c0c461072040c80750350031100c80c020060102914035400321507040d030060180c0f600114844070038134104006a03141120100e1035074051020803e00d03002d800ac0c0f40442800d003441c41e01d0b80c80811000b8403003542c0c00d07116100030b02c8001031030f100c05a00401860004e0f00c041c0208040200c0e09041c4150160320040450b00100861008074072404107840805500260000f14001d14160852650250741c110766691800014007084014a41002d141228821a00b0f5044d81c0c1e00e802840e42c1c0e11085116041e8005641a2402d00601d4035030148030350132500e10101e40300d5500f0340d00021b0660b1516041c070300100d007a82c1190461968140010f488151081004090407031919100035506c074074511038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 752389379 1250 752388129 752388149
    0x3060f04030f121a010e102c030708010f0609090f02040c020f01060f08190c0333050711121c02070c0f0602060604110a030f1b0c11040213 61
    0x2480d040107009404080000e00c0c0c00744100b1200c2c07544c494a224822000c80e055000ca1402d075500c0c1d1040c60800c0c90824021460354411924141c90300c200c03410300040200011881181c646243d003143c8040085500a001c3c007030000c1000840880765408881c0550000f000b10b2b410300d0340036800700348010490f03444564140d800048840300c1c81000c81c240b003c00700e21810194201500018006c51900c80c800c19900b284090f01c10001c04080401005990007200602c521800346040012543c0704183c800203180700350188040025181144902003546040303050080c0e81c400600481a500c64900507907030034110001e11400745504405a442d0003800c413040341e0f0380d204c4440d000030744005406980d0f1241d0710400a02c103403030b1560072036481c06d03d0600402005120781400180746e8039150041001120807400200d181100c42e4408501030100c1c20800300005840b072113280d4281c00d40b64040d4901d8000c0d81e4420000400514140441c00b6002284522450050240311861900c0d021700c10122911a68 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 752390629 1250 752389379 752389397
    0x18020a0501110c03010c020d021204270b090403030905060906240f0a080715050316030209040b09190b0910060c02010c05010504030f03050106030c0212030a020d0e10050603060f0403 80
    0x82181e252040c00c0f140c25403d542429203404201e0340014903550310502c65000da601d0881e0318800c01002d802036200310110900b10241d02d012140082189150480d0090000700c2ea0081e9000880d00d0344c942a43c4c22400650b65425a1091000601060b5044883d203009081c003800d10701c102e5448280050b0040e206602e445950080a9444c218200e0301800c0242c030381c0140f075940340082500c5210901c035018040c561841c40c451414402c0302246e218110703403203522081d02042d000840003500703d180851741003943c5000c6d004143c1d88052240e07200300e0105000080300380142016000746e42503040e1503406122164180030082e04d003c3c4220041e16614a03112004901c1c81c00100c880492200d4041d109510342401c5c44140f5500011308426028640c80500003a40e07500d404a00700d030046a1a0001a045543d551440c20700b050011a04074200701c7c80036040070412042ca400f01ca2a02c580c0101c154071024420f03c0100d0300340142c59004000b1805001d0520300002c3c1d102c5103040c004c000500304250a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 752391879 1250 752390629 752390657
    0x60e010b030a0501091e0b011a090d06060501030e070501051215100f02010b0a081510051002010b1306080d080903130806070e03030316050306120303130618020a0501 73
    0x1510104031810010210b4a910040b41000b034020046540141d544034a040002c0021240c10380003041015888260869260720300300303025007901400000c400c035015042000c0401691044494101c10f402141c00141d0307a4a002c001404442ea21022129130f07412040301040603a0b080ac040c0c0d810145040703080c050b143e8031501035042292000c840c8580c02044d03840704180085d03008414441c0c1260540003080174a40003000c100c00001103103da541c555020504541580c103049900c0d40e006070488410500c52512032002440d462091007074140140c1d9202011945480e144030390740c800340c903c50310070044141000e4081d030f290780340115a00148403100300420400703041002243e900d02090074640c0040c0b900c1c0c00215440b840c0555501d400503000528145003450003000b00d80c040e9400e40c00d0406c4200305280d007550b0541004148070341c03024076081010600841031004600c13410300c040f8410314810b81c40c5808070071101442c0f5005201d0f0800d51000d80142c4505403150190307502420b1150300f9070741071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 752393129 1250 752391879 752391881
    0x170d0206220215040609091109550902090105040608100b07080306090714160c05040e0601181509090f02100206061507020a14011202220e060904060e01 67
    0x12500342c0f400c00c000140010360151700103000c8060320031086042c42414014503c00b4a64015001d02ca0b038040300c4500940141c03132100c00e04a100541038007220008007500d42c00c00420740d000c0c41c8002000030405500303241901460702008083d080f40c200031410302c1d842d03000080c42c6004034003409003405500d03000701e10301000000094005000c1d800013159140c412785006030513500107070b83c1c19000300c0081021424a50245d0396030b003904d0248200031030605903c02d0781d90a540075810825a01c00c921240041340940300c5004548110b090b0000a000952600100c055100a40720041180c10700d07180740400804502c1e044141200c9110001160021842c01c00800748071030000002d6001240300e0100b1171554001c14018800d1604a4842c02d48003c0724803c0e03451881012002503008401d01030602c40c01014110780c0a4038101032505003600301501c8405000c80e4005d0110000c41c0c5881142501e6540000c0401005400d03460b40c1400702d81418004901403003005403000307045d252150040c006003202 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 752394379 1250 752393129 752393149
    0x7080307080331060c0509010e06090109030209090706090e09030a120605120d090902071106030903070c080a0c060504060815030f0304030b0a0b030105090709020706020d06170d02062202 82
    0xd141c4642c11070780d01c20701d01e0290b003610390200f11201d07400d19445084d486c2c0503809a41d0340d0300d0180c4890400d14061b10810200340c4c0304400c02030500001100100240c0c5443c1c0000f07100b00514030081c0900c80c244000500748009a6000625030641c55040242e04440801607400d8500141018013040103090030b103202a01c2c8075080560002141e240185002c11f000400345406a11f80d10354003103181e00c81c0c000130240e21600f800500142c9074404410085d061100003194000d207140c099070b0910710b5503522940d22052990000380350f584035110b0101800012280000185041e0515a00d401c0c031b010000b81c1152001000754442039900881040c41c0d403828044501011107840941c0da4540d01c03071800d281c03514003c0d5510811076182c0062458141014416203004404100042041d82c1c50607481c2c0010b0340c40030101301c175055000d00c841802c2114034002c41c0f014280d070188462882c100c050b5250f01d840c3c05010f00c1800c543c421300c00d02540f02d40d4141c0617501401c6030900da1480100078004110080a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 752395629 1250 752394379 752394421
    0x13020f1c0f0e1b0102120703020a030e01030501260705061b0d0806090403030c0e0303031f0f080c1e0612060f030105070905100903081303050715021e1504120f02070803070803 77
    0x6c1c0c00aaa03400305540031a260282d0340c800d450b0a404481c001004408903070b0b090080e514025020201003100b00054090804100c0550048800c0f241d10f80021413501d400151100003c04035900c0205080c45080c002c40341c2041640c588047c0030300e00900004c0130920042c2016080c980e5031441e107400d00f48a62001400d40b04064203d0350340341000c895010351081c8644103a0034124803a6408104c0d4001d140c0004208e07001d4000034030078a9125410007400c6401c4095425174240410790394071081c4c0326600901045000302c06c10700c800385083e03000d0261444504220f644281d241c081007251054000c092503040c3d420a859401481c0b00051080c1ca0030142504007408003400860380710200b56116449105591042081d00e01c0b65075141080c9500b082005005000750704070008040340400c043c3d8405040840340000c58240d4011440a290440015502a00d180d00540d210450315034004001c4000f801c69440280a802c1c0707071209240e22070141843c000c0c8451800804154150419920000c00e64 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 752396879 1250 752395629 752395663
    0x804060c02030d1104051206040210030209060d060303030c0f0503040b070f0c08030a0603030e030a2a170c0a051c02040b0d0203300a050913020f1c0f0e1b0102 70
    0x38480341300300780b580e005445040c1c801e40041020091805001c01c41c58042e40c8c1c048d002400300d11105001360041d40051451542103803080c0440444602c0c94001c0500071402524006490022144000c5c10b03401010f41c0030f801e100d010014000021207102d0507680c40009454100d51301101460300311004d4031182009060084d000c01400060328065000c401268860344800a0503071aa8003803540b103000d90756014054080313464190b00e14540204021401800030750505c0091501c50400c1c40c402d0840484134261917004503915001820244a404040c00d01140c02e1500701d0b062500c0c08070321103107400000f4000d43d01c2e403403c5000c5496414017210503542c020155140c0c008840309041c0c003240d0300c1d210f80702200007d0101142d002c142c03000310b404c0d4180703070303a0340600e09031440c401e0010f900004508504619030800101c90841000c402800f01600c40c04076001029031f01a096200f0740b042c2c042184002482d22012954040000074103074492200d01f080f41c1c8030f0800d5500142e01380704d021a1841c4480c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 752398129 1250 752396879 752396891
    0xf08062d0a1410022802012309010807180603090206070503040e091207020a120c0305030d0b030705030304120b04141905010c030618111308010b1f0804060c02030d 72
    0x6110000e002c82111041d2100e01825502c02422a42c078801540144d640c07100581d0440d5001d400d2031042c010190040c100510042c01703440c2c1882106c50340d58040040315001084003804c2c0d43c0c0c09044142c020a0724942b115050030007140c001c0054905214003c140743e030710786c8000119100d40003a985443d03001001c1d02e40380c95031001c090700002003c68545d03c407030140728070700f0410206c40401d8a44480d0054034282d103440c1040300c0b580d85201d00d9542641d0300d0480d2040000000e00c00c000070650003103203850110b40318080c1d0041c186080b0054102c288a5041803006005c2c420a4050011400f500107150305c1c40e5440701d041401c01c116103842c906082d40151541300340030341c000003050a0020300ca10002c000e02c0400714011000c80c0d4a502030300c100742104140c0a071002120344c002000c610f5500c40b20703a150602c4544000d40c0d0121a500003801a5115480000740c0d24040d04807201440e565044080110002000107001c5000200020400c980e200c41502c052442001552642d8040e00420001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 752399379 1250 752398129 752398139
    0x170a0b0c13150801030b0a09050a0303020a03020d0606110c0a181104170303040b0606070f120203090d051c091220040f050f070201090201170619060903030f08062d0a 73
    0x104420900066810040d090701042507101503201e0044e0708d60b0444c01030148901c035594124043c2d403100c5080b2040540070b000c0b00364241414410a40200301603105c51035201e02801c181824008401443c5118844d1000304020a0300d40c55004a000c140000000940200540280645005a03003003003124284402c4001c20803c0000015800b40d40120303481252032b80d9050030480948503021000701040e80d200315030301c0003800c10710b114030301f00c0701e03c2c010390f0704101140f40031581d45890101c094a07194000c10558080c085a10381817440b0000e1480c2507140741d414038100300c6940b0905007006001241010301ea13040c0708515080e821038240e00030000c8c042c5c441521815005003a05985402c510a0824080b03004d50340140b041100103681a150480814180250110030311001451a0380240e89044002d180b9402ca844a00103414552640e02485045081c01010894100d03011424040848207020301c907030310413503071660158449448080e501e65031000125443c04c0d80f00c0d542c1d00010907082c0403030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 752400629 1250 752399379 752399387
    0x4080d030606140a050d0510080114160504081b180106020606280302060306060c1203070801090b061c0b06130603050903070b16050c0604080301170a0b0c1315 70
    0x840c1c00d5652103858803c0c0c007901c61107035842102c00749400310307070b081041c2414203000d6000309070b1041c640e940c201c402c603940e039400a0a640103012141d6000b1407000070065a01e800321451a0800480c1c6401d5042a003040c482d2561464071010744500000c1c22000c90850341d4074072006000001d04650346901380e59607018060341e208000d45990744500c40c403901c101201081e4801c0e5243d94100500100c5a062845c2c080c04910782c0041c000d030b0380205042000340703403c000421900d82144981d030402560f9160400740240b65000603002400028101202c0402580c0c3d86020b84a8030703020700740c0d0303500c2a1349401c00500041110301c44941c0c00c1940860201805500c620f204011142a0744040c0050303603460078000d850f8420584018000d59556010071510031501000203045981d42c14042e05e0102200b28091804408903406c03140303528000014401071054822904401c0f504800602c1c07000f40360b68800c00d00070402440c119080c03001007001200322154a540c1c00084ca540c0f044030100c000d40d010020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 752401879 1250 752400629 752400641
    0xa3c150f0b1003141603090b04050a020109090207081903150308030106120209090a0903090b1c0b0409030c1b1e0f080307120f2703030809030a0c110604080d03 70
    0x98800d0952061861801d4080e01035052218842c42141c000c030360320050300c007031200717080f00c104010580d60f00840c500061814040b01c1c006d44c05603008000281d031a10005018071625007020308005d005101c1c25000910b076100f41c80d44500d40074007210310712000f04821002005450621001c0e40b141100c000280100800218142c2e0455130b01d4003034603102c50400a0030392203202d8866410044000028400d101594800705207141709207001a012644c4110017011904030aa2949855001c407060f100c180066106d40c3c114407000b07440c02c2c07001210700d403006441d0708040d2502a0080b8544280c602590880c0307034845010b02480320991402c80f983c1c90342c400e084005801003880c1030303446038404501d4003000400ea40c1000da003c04124841c2420380741c100c1d0320309000300b9100d040c001071018051442c0100c15121004160441843c180c0301e00c8c50034024440c5a0160401800b41c004224000d5110343c003190441d0426085640f5913802101c2c280032406612640e44102203074040c00740c480e42844da06400007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 752403129 1250 752401879 752401901
    0x150602010b010903020906060904020f03180c2d0301060807091a01020f03040b0a0e0d0614060f0d0b0915090601090c020c1008070c05030c0a3c150f 65
    0x30044103803507400644101456000c0a9401741c620340000f03049280040040040c1d00e00503202504020320440600369036042a43d00d40c000c0c80d005910812009410003039000442130495801c00c000e404034011103209510a510b12581101c150078000301030718250000720041c01034100302c4c1d01c545c2c1d0b60b4610700b004080d00341200d000418072000841e049d61001882c1e809410031000918941490015142c04035448100c1000a0221403140d6009a03620303000d010040900940f004a82908a00d0a44503040d00c01002140329036128030300c3d0200c80e00c0c0c140282c2c8030582e001210b900140c4801c95011b240640300e03903140702c0b90f003c41800c0101000c1c2c042480c034102c441d401010301071111a040181c1c2c4980003d0101c903000300225110002d9107215400c925040b41003400d04401480f01031702c42c241558010301c03406007140d005c2a5840104241c008118840c54101005038441c520207520507040d400c0c461003190034051200510809200401d61111070400303001d6000c1040b0481d6200e00f101130702c540b19403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 752404379 1250 752403129 752403131
    0x3150204061806090608040309050d0b07020114100603020f130f08120408030a0e040e0d020106080c0901050a05040902010210050a050f09030a120507020a050304090e06090708030301060e01110115060201 89
    0xc0c003030394210703202c5004058070603545440211908040c0200c840050007002901000080c4900141940302c88510340b510314000c480c0340202c0c3c582040003138290b90300740d21003030b0b695a098800c11032034101c00003020040d201c203880c1c0540d0b1a81c5c1e0f21032001441c000d084a0b021020340001c0c002030540e89002c102e1048a01a0003603aa032901c0112a10015000e1445030341d00a0704108920940b0a00c40c450442c8445002480014124200e510312480d01030024846000345c0e544010a201d034840c1041541d0b00c05000f100c40c00f07000d6040c8401b080c8561954400d55000705e883d214501b04580c001c0c00642064002c0b07000400041c40c00c442c150f0080e01c4243d9103083c54960350000309150f030300c02000325041118152104c030300040c00611803c0081000401d0001140903014006000541c140010b000034190b610011514240e441101c500f0000c0240009001d42e1054100308201c16002c401d503030440e44a81803030784800c41c80c20010380b074a40c4034468508055181c400009400131060300803000365203c070780c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 752405629 1250 752404379 752404397
    0x7050705060c03041e0801020a1d0307030c05041109100e011d0603040b0c09040e0a2a090b1512100506030c07110607050a0b0106350406060315020406 66
    0x40c028140701c0c1d1000720711242c10402c01030101d1101840e4407a000d200c550441050195210403247c01ca810074611800001c130440846030340034a280c020021000000c50203080322500c1d684e1411410f00341841042c0c00389480d070360a003203007094000070349031b003280007074a800401d040c0101700812102c040039110f0b01144041d851160b007032021010150009502621035842d5403180d4480105001c0c0040400d481003204110b80d0001c0e88440c02651403590865006000650007490084c0d00d46500c108800c05408100c1103644032401c440d0300c65401c0741c40c2c907000001c41482c0100480ca0000d465891010b5002c4002260945881c80d54120b034400c4801c0c1000500141d116400c02c00780d44029100303245102e40074070003038000c41d518091607060141c00800207032519503540e8401d070500074603003170035a0b100ba00180104200c41d00b00100001501c3c0380d064000c803d0410702c0c030311442144450001c0d81a038600200141c1004030070341c000e40107590001a40d445a6000012200282d0305c280200e0001440b818 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 752406879 1250 752405629 752405639
    0x8030a140705030c0c10060603020d1a060906210f0108060703110a050c030d050a0c0f020d0914120601090b040f0e0d210c050405090705070203150a1d03070507 70
    0x10051502a0364a942d03500d2460302c90042020180e0449040590781d4007901c001c6100780c2d0ba95100c2c0304005c1205450268236003016440d07000446514541101a2942c103003a895084c1c0e23210001c5400085007116400e07110800c6000c44001d01a1504001319000c07500824402203c0f51000e03010704a60a400444000b5912260224103545103090007244106040c0b00c8050102c1c02039015052000003034007100c0c00d142c0a500c00e40c080c0d6000faa4040f480c940d50301a5900c549034000b402c160002d602d80020503040000001c0240358140318450310035582000e000810740c50351002241342c0c1c00d40ca02011640c0c2075851310040c03c024451841c00c50300c15442d1040840c0c10850300d000704920b000071031010305201c1510030405e4030205c00705c05019011500ca10313141040010300384120011009140e9072951030740d08010130f00071031030340180240060050034003581005075400201d9141407407146442a4050b1a001115006000070f0080780301495101c0003584e540d008000b0151190350f000740f0403039660719510 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 752408129 1250 752406879 752406911
    0x7091107060e0a060c230d0b06031503070506030705041206061203110105012c090309060703030c0813050a120e03070e090d0c05280b0903130f0b0702010c0203100908030a 75
    0x422010586d600c000840380b508100810060180c5a0344550301041c07000062001800c65402158400c45203800c0550540b25410100a01c00140c113098854a00e076040ca8600034015004600c50100c4404080780340608100702c41d0403040082141c050340c0d8407941038a00d005017640e52507107000c450542c602400081c41401d0b904004c042e5041400f000e03101803100d6641070140c184002c0031007490744400c028008a075100c20b001010401c0c045e40d400541c0e4032510070001c0c40320502070500d00c840b504010004010a0b80032482e000780581c486030b4209042c514a1302a00c1c54100b8a4815030f2500900400069520a0410051040c5014416a888401481401d858518002002801a501c00d00c0c0000420415121004a401d0207080d104030440350b598403041d4441c01115466407030303000460052105400501514042c00002c24504883e030b0400d06001a98001c0850103410040d0645454055403400d0042015225004100340000c201504001600d40d009a8003180da8a2400c3c202400001e14 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 752409379 1250 752408129 752408147
    0xf0f09101d060d140c0d060b0307050d09020d080301080309010314040308070f0905030d050405030607030b0123120405010902011106010303090b072a0f090b0307091107060e0a060c 79
    0x2601804180d07690400c14419280c000035292440f05a4965004400000d0300755400d10402c240b01582d9031315084d2815240642d222070b4840a4003510a009028107560402d081d10941800000000307490f04590000580104880f40c01505511001002054a84c0d021000b00b0100320207032801d020a42a60703150204045003182e02400041c510800b0800c01e80c440c050f2012510f1040ca043c42080e0785480000382003004c001c05100100d6400241000350341003e1020a0b448600c9081c00c2011703040b00d00c0064904000d00d441a42e81003050882d88072050341020540c0c1d50522152100c04270b500d05403401e01c0c000c00d1450ba090b4089950a520f41548040000f8150305a0b40d140d6030700d00c02c051074030360711040a800807241140c68101095504820203890400044c1c0001d0040740c03100b80ba0314103500c0019020840d0041c07000c980c2024030400c40c58400040030401c8603c1c480c0700041680d121603d030441c3d4017948900a0402d4103040b140c858503100041c06110060103802c0801940c09603800940c0c000d15 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 752410629 1250 752409379 752409407
    0x50a0b040515040b2703030703090e06010918020c01140405100f11030f1006090602030301050616080d02030105091003150b030f0f06100e06030304090f020f0f0910 72
    0x1104110a1003a03060600402c1c0d0121208807081e400e1907155002c14000350000b0a4680040035502c0b900b00f00e00c1c0c0d0640328040500d07825009949041c1c00360314001c1a0041e18001c001c10340c514140410301e035903c2418640014036401d002201c00c0c40c000c03007144010f588078207000c141d6503007001a1140c0ca0304140c8020360107244d208005102480d00284030401808046041d00042945c403411b500324042018001e61050140256450b082d28107080f0b403290b5a449500517200b0411a00130620186400008403410754404440a9840b802c0c007e10780046c060450780000c0c001400070074140528030054001d141680c204a0b003001c1181e850b03c1d1312078001001d521019200307560640b41e18a2031505580200d160581c00307001daaaa070360104100501d010700f09003900419074420720402203022185800c040180462108103c0c03607041c05000039603a400b40e4080c1412407555100c01c00903040786a41240c418440342da04454560512020684143e0000d90419000e0309000340f00340e040a2080c070b01110148 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 752411879 1250 752410629 752410649
    0xc090601050a110a060504060c030609110702040b0d02030a120822080325120b0f030d12090c090c020d02060c220909110118060e0d1b060207050406050a 67
    0x3810b003000031110b400000c4640d5609004401c200c02c0860b0b00c80c09000e100350b0040101007140d0050950003000c490550303212006103803400846403e16050101151103071380e011240403510900280000e003906408450080d894030540b102d000402201c0140104000c4450300c1b001c1c1c043d40d4802c103500c08407809441d51402034550225200004103154080c40d00300c0d000304041303078181400c02c1503035842d40d070680803400110f14007440b084032942e81380c000c941882e4016996130b10390310020307008a6aa482ea9400d030a0501402018521060304030f50b0040c00900e80084054902d42ea80d070b903004004041c00130482c0014040d854039081e01e81c0c00010180d0240303019890f0030b86800d07003c6c00350300343c002400c51854a10804100002852020074001c042109014004071b07800221844005030903891004002001c8042008040002d40d40040301c4074246001a030f000c02d02d245452a00d0418860f24180010700c11031031343e10110700c0c2640000c551055034400c0d501007061948500422007030004500c00c441c144 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 752413129 1250 752411879 752411887
    0x1b030103030813050d080a110403050303060f0312072102010c020709020d291f02120703030204091a042003060d03030603050a0f02040b090f0a3b0c09060105 69
    0xb441503449951100542c00d003a640e151030b503a40c003410031803100c0399800081c003c0d0044c840944454403c00c0700d9811107200c5186040e06e1a0383c1e15885e40002881c6610800c00c042400001d9181840115240100481d880385d40391983d10b410092403200640000d04640f03001c210701d00180c0144540b0100c210103400408881d0b18050b181006036001020718a081c1c0e4a46140710715141c800d40116081a89428134080c440642806000854880007950b0001061031800a01959000709039044a90f160310b00540d43c40203681001e401038032030303a801501803518000d04c91540010349000704100f948215024051801180124480d10480d19040f044210781040801d4040c5000340381101d04038468240410300036500d480d81c80c00d00f0a06030b0141c1d403080c81c0d005401c04502d02407040780c014080849905605040c0545400c1c80504003e00300c1c02c1349596070010307a407033134034801260441401c4000b0710f91150780411007421000000c011001480e11460812040364a00180400c0c41810180e4596080c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 752414379 1250 752413129 752413133
    0xc09030604230d0203030a0e070302090103030804110616150515090618070206162102070f060507021b0409020619030f020a03020c060a1a040b060c0d11061b030103 72
    0xb140801405070441040340c00c9600c080c0081c46074441c01803042d00615142e240201102d000c3d9020280302064a4210000c20300c016945c1548290549426141401c02960740789404107018044098003a0b00031004a280880e00c1101a02c00502c180700b04041441d6448401603402980d07804c1d100c00fa044a0340940d90411400c01001c44e5500180003400410200c044100044c00464140c1d01c00006800c0341c801c0140700d00d800480c242c148c121500c1d00746104000c6c000c030b00c20400c1d1314440c0b22114540001c1c0680038442620790001c000c0d070300828200668100300c14047d580e1880b070a6064880d64082403510250310349881140394458010302098500314994001007030020340044038105050350b6a00029000e0300c1b034800b034160410282c9005a8900000c01a60728013140107050305400341c00e0a0b056040d4800c2e1403505004a04180c0c0e0125070042d00000062181c01090140c00740c61003008440b03040941d0081e80c44a00741d12000c16605162154240d4203008126034044041d012010801000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 752415629 1250 752414379 752414393
    0x21e101d150702100201090c0608040c050d0503070b0726010305060a181e02040e010b21190c0f080a080f0307030b030d091e0501120b010509060d050a050c09030604 72
    0x295100708805a0310704080c079030015001c600714003d06070050303548490303550030001001c240c0000b03021035052180fa80c0c540391344d60070014102400381e5402a4030a00400e1700700314040090303451443d0300c070b9445185450702c81c1c0e0040c4080000e016201801d103000100d400c004081e040340301e058070741100140020340d50300c007030070b1010340502c01400b12a043c2da0100440410a4001a000000501c0d5111b42c0a03520500401065500b013682e68103190f403500325003081a90f42c0d41c182a050700d0350b801c40d080710700100d03180260606a0800d02110b61020400e407113070401c00080c40c05001d90b26030580010160f030320b414015544660032a8010f00910b0108851148000014007559105041c0d01c1e001c0350001c90a0003103405c0a42d54959000812140002449079082200c10b900300c02c1051050585210f10b0720000038880306901400280301c641c0c40c0d1052200340d22800840e91700308409043c50743c0d18410240d1100040004a58039490f41d0314000c003180310002100121460710300000c00418168072a07480d03041c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 752416879 1250 752415629 752415649
    0x1050a03110f011407032c0102060402100306170c030d09050607260f030a0507020c01090b030a020408010c0f14040311130b0301151d0103080a05030a09021e101d 71
    0x10f060040f9a103410484016841c0244940e0348203584107100740e0917110030544400510340403d030030000c6001c241146640d0004410ba03204c0d0b01100c08038011400d80750107400808942d0400c0c003103000c1c045407201900c90001004d0845940560450b842544c0c1d019084590441c14000d003984448108000008107090002c14210600400f9032000c800c00140030141c0e4540c030a0700f420180301c0010041040c0003c4c5032240340d50044903400a88a02045031000901009050281031484000400410400362669055802400328600200401c0e4058003000d40620500c003800d01c0040ca618079140306091096003a1030840f03921003903200c402d030004010001803030f48503004c001000360b031202a0803082c0e038240100c8108111125511689904060440304449003601c0030421203140100100009024070045a510700190b1810030340f00e03110082c81340c0140c584038030040d50001541e626081070310000c10300140c20000440384d46e40d05502210301951101d40d00320012030b10f40712030f100c0004282407030f064030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 752418129 1250 752416879 752416909
    0x30304061815051b01060b181e0f0d0312090308040b0a0c0503073608010b090f13230607031a130e03160b070305060316150c0803090f0601050a0311 65
    0x12410076120464991650080c01044400f100c83c04681c01a60a03d0a40516554140c8198445038003127100030590001d009150749004601c040c0d0303202d061500c07818190b00071215002c02030124a6290400a00000042e01c0948006800b0342c00b0504040041c8102d908450007525414115510040d00380c0c0e00001000382c41c11024a4281070003810b00100f0041c4800c4043c1c484128801401c003194039084403003640c86680980107241c28440c00180044609a02a950f0030f0050800052880e0481888030702c00d0048903c44074200c00300c0c811040200d940762050b030303103940c040042400c3c0182100c815007070720102c00e41100700e0100e48034060b500c0e80c0214003000e5a650840c0d10303121780d0540584021000207801e41d04e82c1d5054050205066140c0142078102804030001c114030848062900740d1800c42e4071804030041ca202500c03007082800360400a0002d0303007140c602503d91a200140c640c5401254280c48230500410002041c10300d07041c164101601c0c0c0040c80002c2d415601000d00448030521600 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 752419379 1250 752418129 752418131
    0x60c090e1909080c0d030b03030c0c1207050a06120b042703090b0f070b01080102031015030f0c020c04050c030907060e0d020d03020f0c04110a0e0f030304061815051b01 74
    0x9014042000d01000b8194103101c58000e00c820140080010304a40c7c0c0011414440e8100b08601c2901810004851242c04003ca41c1400307100860a02245440b0442d4400e43e009042d909002034015044600907c00c0c0701c402c141484801207113800c1004444500282d070101c010614010350581884040c40341d881842030810480e115110000074609421103110f0740e200c42c1c000500c0c5020414102030003030061460340025400c42c1000c8a860140d2651030064101d110503072017083e61402d1294200c0001c0514a440030031003581d80000094541d4020035849001d58204404587e0034501d54088901c681490780290090505102c2c045500110202d00181d03c49040b05841000d80c1d94030fa8143c0f0200c0c420b0700245000030600c0001400d1641100c3c119210314505050a0111075696040b92179400280c40d01c00c5009819200007441c41d0128415140c05100115020400c035412070701c0540074884040224400596448a403451800c80034444800140240110001e201403194040814010400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 752420629 1250 752419379 752419391
    0x260309011202162a0806090d11150f090d090b09010513051810080a020f1215091b0d08041a07050105100501090504360f0807060c090e19 60
    0x8a03074421011135a04404854110501001c00d4040c40b0400d9000302200d60190000d46010901c040c0c90b40c0c2d10501e001c5c2403203105094600c140e94144812890000b250400c45458203001401d1400c02400b251240c4161040c401101c1c12240039a07144004c0301e44281d502860700c0041401142d90782c00040d21a40c61169000300480c40c0c0d550181068405000e0450807038291401100a0407201040d41c40104150004440c14016132982c03040301680840544d1500070ba00340d29982a1b28080900504410038100c4100340088280080b600040c5039503148884503510400c0e00c10842c500101e03440007042400108020002d040e00211551028002003605508001460321480d09486003216998403505000005100030b40c0c000c1e1299000c0c00d0107680c100300d20883c040c084501c440d070607074610700e24059480c03540b5211010341c03c0700c0201703603406000020ba08455203000407840e007040c8402c0f50924200680c203a0001c0c4a060100c0031261100c4c0041529161700e10364920a04c0004480c0b5801ca8640c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 752421879 1250 752420629 752420633
    0xb0a03081c050a0506030606010c08120712090c031110200309120105010509161d1f0e0f1503070503041b14030c0303042304060f26030901120216 64
    0x111032103225030208040480c107450003404047c02e204009111a05011114101d50701060100b825242160800480c540d00744d02da070300054900c030b024010280f0206091014660030821004080f6044a04c15076841100398080c2d020400354084060a0400044070503007a4282c940e1030007064400504041c040e24540030b402c4000c90004134414209200d980c0d1a0b00041250b81001c100c095031281100d8100d59180510000040c01e541441c101001ea00c084899401550340d548040301003091810b01c1d100491104200c0c01030807020b03012002c503224030070101c07000c012810041585440c1c00d560120b95451507403404400c0d1b500d17410103801554035680d10302a44201a160f0b101c46005040103405030b94030222a802010f2420b6180805030703000750401d02c003c119440441f840440500420705648104245420102d4001c02d515409004403100d4072800048540768502c81081049080400c491400103404026583e48070f002d6405001400d407460003071002403207501a002c0d04030070001030f0003800318503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 752423129 1250 752421879 752421881
    0x30f090506010608040b01050411070b090106170d030b060f04121b0e010e070c0c15020a050109060b03060907030503030703021b0706110c0a050907050705120c0a060f0b0a03081c 78
    0xf42c0040d000b1490450500080c0201c03c0911030041c68101c3e014041440d5036510701e8407038000c0c0c03040140003983d0500400d0b81c1d08802e40014000c1d01e4101030000707199001032086541c41000c07080540109203000003861003410040d04480da0038a890045910b040d141149807100c000c1c8880c41a98800c800721610700800001d40303040001000150f14500c41c0d5414a0042c0b00d903410b015100c1c000b071040194440d00010710144010040301d080c1240d0380303110b0b0104001a410300c0200d000041942d440c000f921030811a0a5000c24662242681104e03d6035031400c4066aa070300c00c9010140681c0d0040c40004c0e40e292094000306015034904104400344421440144d28051071508402e0100f9001c0700d124032410030402040b12440400c95090745c3c4075180a001c00c044210203004181003010002e412020f000080004000410b2003040c0e40350740d2010300d201542c85074103c41007212814100510002807003141d01071100d581b0001041d54200900c2e60b529040e19902c401d20304040404600d4103001c621190f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 752424379 1250 752423129 752423131
    0xf0c020f190e0c18030d0e131d330c0310030203030a0305010e1e04060207081b010b0306010e071b11041a0a0e01060207090908040302100f021006080d030f090506 71
    0x1181c040f035460b180d07040d00d4800740c4a0b6042c2414020b9000900107407440d0b50150300040c00324415640310307141c40320307000080002c0c1000d07503c0a10919140c10b0b094850950000e183c92040241200d84002060590f134aa6504011604140e04141c06e11001c91b5901031003100642d007041c40308000d084a117649601181c1550080b0b42c1e1500441d944000410000b2000c05115920448003d00206054007180c1510b603500e030043e0020304655404181c64040044400449080210081c084000800e40300b91075800380009081d242c0c042d00a5400010341585401021406010262610401d80749060040703c0303402170140c0e0503922a6102010b000135034a4902c10035240b248203001c8824024019030600c480c800e0143e0084100c50000c1004000c1180d01280f05401e407040050f000c03c04034072a04150650303000b2900083c0d072000c050f50f144000e2a400144000b4120b04513025280810005405e41080755420710541e08950081001035098610036448025030710780000c00069000d041d5240d05141c501c2c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 752425629 1250 752424379 752424391
    0xa0b0601180e070207090c1209020a1a04170303071b02010e0402031006030b0a030b011215021801021b01090b1c0f0915020c12180d050d0f0c020f190e 66
    0x401c0001d00c0b0b03e0759414031040002e0a403990051008141a1000900301c81c051690880150b9507070070460110741c3d400e4489001002d1701c04402182600ca03088512580c0d03c07510441c1ca080d49038040c031744444100032059074403403407141c0c0722080c00c101c0c0054180c0035141852000c83c1000400d4604111955076803000d94081c82034040710301c0080d401c0c090b01a0440d40103920080c80f4140c0b940b410800201507089403410f4484c1901c40d40d0b0f01c0e4289142c04483c0c5004c2c2c4400805860000ca51001400c00c41020058802800d1f402c58900085150b84100d0070075002080d0760000300f8081c7c040c01901e01444c02081d0000701c08102070308100030b5920720b00496110700b95080d1b0b69519820704105000002c15980851182004214901001c0000701591510320001300b0411130302c0403603001202c5402c122040b0b00980058034890b450451403600340d44800307211401380c0110301d415686410851160000103d01c2e1341c0a80045031030345084040000081c011030400445c60b19503c00440c0c0841c000003864042c0d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 752426879 1250 752425629 752425649
    0x15031d1506041e052a030417130b0703260411090c0903010e0c180c030114060f0d061e030201020601030f020f190f09110304060903030e011812030c020a0b060118 71
    0x240a154030341005c5550301003110084080c4203000201d100c140140080030030056550f50384e01c42480e003042c0e400ca12039000c000c02ea80c01107014001d25400c1055a1011180c800012090b40c00c0381000d40041a01550041d02c00303940260340004a0070719a80481d00006191000b030300b42010070380000e003540c0040b004030210b50020b0240c08000c0c02c0500100000d1240310b100320b1181d1030300c60b46141240c041440792040104480b00c400ca01612480304407490f402c06800a0399540700e10110141c090090307072003141c0c840e520030400c020448001a01c0802605c0d4141d016105030703443e40d11145400720443d03c0699102c0d5812415284555404c006410344500200415400c14605810404e0340145c81d440141c143b81020380148090300b000013125805035021100141d0f542071404d080300203101009251805600c0c0000000e0f4151001c02100c41040c03207056520302c4201d0141003203040d20400c00007440035a00a0180c40e0000c0c400300002903000340117140c8881022011203000c0c0000354a548504024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 752428129 1250 752426879 752426911
    0x31006140f030309010507030305270303070810060203040504020310090510080f06071709010e0d05070c1e0608041a0103060e10060302060a0c060615031d1506041e05 73
    0x10303041541540c003242070210081c1d4148003a03440080c2851040140017810181d4480014070010000a000150101c0d030390740015400c90010b4000e550b950040d200a40400c401c080012201c400004c101c070141d850350350285003024030b003500b84406504003415488201e101804081441d010500c03509105030b006448501c0032505c0e04407038034101100b0070000e4105412281c01c000900342c1108003000b80413002c0d17041000039528111024010040424a8100350140400b004000e9500c0009041d001c0d005240d148a6581e840740c0722603003814000716940d883c440345241000038a001e03c02c2194090b01070b01000c081c0010b942d020982e080c0c0d09070030498200c0c6d9507128000500c0004c00690072a1200c100080062604503000900d15026015080040048561104d0100200b9030040c000500100414800030b4451200c003038040c0c194a64070350f40d89814441443c0f80d0b05c3d00007580b541c0d4100c00301c0c8411055210581400060500c0c2006405000e00d141a0964915582e01c1082d01c03504020480083c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 752429379 1250 752428129 752428169
    0x304030f290f0f06010203090a0303030501080d020105190b03030f03100609080a020a180e010501080604140d121802031009020307090b090f06010e0a0f030638031006 73
    0x14035142414000d1080703894401c2000c0d94620b003400507000a481d003004030480d42c820004078034501c9284505a0448070501d0008101505904507034141e0b000701066602404603c0001c0742200c00c01c0b140107070225100b400c403200903e8158000c4c6aa21405016249441d110300307007c490903072060f910036081848405040081c15803102d80c1002a0a050001c1e082c19800c50300020700d000818041d5100c00301c0c1900c00340342c094481c2d5200c00075608180d00280300c0756a4803c0540c1d214641250700b5517020341c0000c00803120340000315002c03071a403015840c5c800402c4030310f0ba81c440082030700c0381400b08810300c1106c054026a4080003d4000c00c19600c0000c00c01d0002c900c1814106031031540300080307860600050071140d688400148d98004c04441d0340c016581e03152001214100c4017104100c0d0040b01840c00818002c005054503425240200024008480c400c40346094001300101c401a1b240b080c010940d032415100300c410800ca04000b41102c22030442c10134020103d070004d46c00506400070542c00004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 752430629 1250 752429379 752429423
    0x20703080732030d0506040617010506100f090b07060609020408030a0201060f151803170307090503060709090911060d0c020105010902070b040b070201110318011a130e0304030f 78
    0xc0d150441c02c18080c4104484142955030300800b4001c0c80c0b9540c450000075007075142d660002c4d000b44901d01400c4a04030700038a05600820b0141c44040c06070002210b036001050041c82c5a241d0251181d455840407483c01d8440c65a54014000807501c0319111100007807045040c4c0050409403680c000030b103580380120000642100c0e116400314030502c00006040200c003854110001c001c481c03e08000c10f00c4983c1a0903100446181d40000308954900c640104a014014001d90310412072600c40c0380070a03803618109980d0351822039845000170a0010203110018841d0401010544204240c00c030815801c800283c040d00320140444102d55544144848180d09008043c01089503a0085250000e15116600510b10007131001c0c007900d0504011911a500c01d5004e00e061103075081c0c5040e268203081ca00d100c1a00c0810700070341515030800d0207050350303001c07080351010401e10024810f202c09680070007180d001d4030b80021410010b02040c800000840c2603030500381d842c90320902402040845144440d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 752431879 1250 752430629 752430683
    0x12061113140405090c061c06080c0910080a0201110109060515010f03020c030f0c24040b060117270303010806010e010f1a031b1c0509030c0316030207030807 69
    0xd11075402e007404c0c41141e0b00086184d032800503082e9852a07a03012800e007150001c03445008a4000e0925143d00080d41010108414151920071a4100016103848010030000b61413801180f8007500001c1319100150b004950340c40c0da0b10100c17400842e05a0341901c80d442100c0c0c089600d4a4410a98441c00d040c0d5a4456464070300b0b0003481c103085080c1403c0750307c1749070b40c0d00400aa40d416076400041e9003e0b4260704102c4451083c21900a1510f40c90030030301b203001d501809650807100d20354000c0129007250f000b4403441c2d12a680001120656961305002c0888081c41c50400700100410044880c0403943e09100035400b80440340003d281079407400418001c6504140d0294000c018240740a100e13110401903018089001741e2606501c3c0d844852800100c50400031100c2d003800000945100354641102d80042d100e180c140701001159a0348551584a115402b40035029800802c0492091030401d0400b4140600a10441d002c0d5500e84c0d81c0e80c44030b50310800059400300b800d04003d00c0da4940e800051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 752433129 1250 752431879 752431919
    0x20d030f0e180c0304080f030907061e0507030c061d1b0108040201140a051215040608060717181608010b011e111f15050d0c12061113 59
    0x10015140551150242c99800341624010000000101d0280f056000980741d0b94500d2982c075581d42d040192180e03644010340c0c07041401107036a508031045040340b0041c110202020350744070107140149582e4200c0341144a0f441c00ca4806644440d6282c01d0745201e400c542184003000024045035030143d1504418280f000e40d25410410079808010050740e20648114011102d51005610748070007100c02d950a00410304042081c0e100c0e442005441280c04000548042099800b007203100e445102d00d03519440d0440d00c107400b013840b4114000c1e41551340610107511050305114055066544680182880010280351000e28010f110500000200b0721960740c61500c2400d003040c20048454001516140610042c03060011904442203448004c0c02007202c012490103004011000b10070b1901c00408007400d014071200d038000804112818032039441d2200765085800e1656084c0f42000c00d0840c0d01c1c031300174203c80f500c3c2c403424800c0c4a81c5c00003000c0e00ca80b072601d40c40310070900d040441c540c400195010300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 752434379 1250 752433129 752433139
    0x250e0f09190609020301110703201903090504050705040317040812070501091a0901180503070b090a0803011401141309200c01061401020706090501030c0903020d030f0e 74
    0x14400a038100280e030301c100e03000c0000e10000341074041c203011004082428000c1c0d019420200440c03000310122004069035880398507021225031a00c1801852800d0030784d0285015405079964880120020131443c072414801d00e4141940340d19003020909a030b0050f5400400300d00041824030420a0035186807241428694505081a1074064021399075070307a004004000e081c1c0014058103200c42134000c11180382e04002c42c00041002c1c40d440000c08041219410a1546803040c0345061414980301c0382da03400c0d040f200960500055231619025548090541d5005101d090b80000c0054002c00245000300a40b020f54440d0710703071180015100b0591084d860750701c49810001012030345082c5134910160390851100140c2030300051545150f042e9540740700c9078109004034901450751015003148042c0c410002e4180003c590813801681c0e907603d04e0180101150903135034140040e5110390b120411300aa00c4c83c1c094241131380c1ea00454030768469103001354002855090212030064000d00c030f004840d00c090366 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 752435629 1250 752434379 752434381
    0x12070b0a021504080403020906040b0d030c03030507020d02060109020c03160309030b07171b041802070501060f0308031602030d0204080a05060f221a0915010603110405040e250e0f 79
    0x395991945c840c5000003440707504501d0101e0a1070329264040c011f5410098442032400256081c05000c1049056007100041c3c10700300000c2c2c0c2c451010481c8103404103160001d00590742016078030740180d08001c811550a2005005142e0641228145a43c14500a4969840d443e096080c1503088080062511052100768080380000d5090782c410160302540c40980a41001105814440a80b00e540d11042c1d055240f000d00c8c1c0700e48c1e03016a000786600c42c440d41c000c00403590f550340601200c908905c00582021810f100040700c01410030180c0c40181454419a072901c12484030f0041260046e401002c16988018000390801904104194200040c29911072061030008250b42107440311003804803a45c2008800e40d01000010215400f55002c80c080070910744c5017101440d075075601d1034586400110744500000a8107402440350008682650169038030789814041400080c28101b60905964414844100c0d01421030b40da1001400010b15200c000700e40c54105050000f01000d041c0d09500000340e8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 752436879 1250 752435629 752435633
    0x5120c030c04033018050d0206121e040c030b070201060b0a050906070b04050a170a02060106030e0a12050310140a06180f0e0711030306150912070b0a021504 69
    0x81914100ca9002040d0031040c2d000c1190181c078018030318109500c0e444c041004480c07154200c4005180e12400b2411806071a41c0c41c42086164816200080d421034400c0083d041071525a0103801da12844922078040c41121180580105c82021102275039041d03041036041c01089046040140c0061039440248212410085400500d10480025070280000026404002c0c0c446009803140c480e08691403514030f14007801c00c42d4585407041003c54480003048951840101c04c5425115000e205500070034060703080c0315068001b000b400082c007030a88690425a00045c48010000c0101001540c174030703840781881d08103403000c00419080540d1001000c5000241c035181c04840004555003032404440b083c840703003000d8100070040c1e00700038040e07101180d022401d88240b030f2125014865940c0c890528110951146031039000680c0c0855001401c07101c8146400b2442c40504030031500102440b20808621030314034501140c580c400282035002150859038560144441906041d2201e844951880c1030303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 752438129 1250 752436879 752436901
    0x61802030c091806090c040c021204030b060112050406150b04061215120803040c060e0f09190c200a030233010e0f0108010c020a201005120c03 63
    0x40510700d0040c4500300005000c44140c20301c5446020360081a64000e040c460601c0740c9441114258500560406070004004c0d480007400c03405072010a22550b00746400c40c0d656026a91000e8a840c0c1000031008490030310f00c80794403450b0f01685c481c1000162000c0003c001d0303484c80c0d2a5600001e0603810a120404c001500000b01e120b11005001c0c0c0004c2800c0340309411065048150442904480300300050400c0003999001580245c0c090f860003801d495440c0000c81c1c0b8174100000d019080140500c0304003c5080048000350812560b1000400c05443d20a003041181c080083c41070006850396681e020b1a941c0c2240c4060200b1240e002d448401105d403406541e41c2c10701030b0482c0003000030903a00c2d074405486581c140001e1005460a00165944000300f50035000d06a404150301e50f0100000a8144c0d41489581c0c580001a0081c0c61403400940703c1701c2401c0198800c400c589c1210040c00601d0b695000d034141c2421865454560712000c600590708600030703000300301c484211010820b2007003007058 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 752439379 1250 752438129 752438143
    0x316030503040f1202061b030c070210120f090309080607080708070203040f0b0406020c041a1309080a02030304150c021e0a060e07080f06040206121b030106080406180203 75
    0x50030a03a6032522a0f00d4009800f1488507005012401c100f6000c1c0f1640d580460168060660200344000c3c0c0340100590050b544403d86200d811203504028160050801c0700c04401e0b07508079410501c00d010039010010341a02c240c91101300c8200d0342ea03256001019080040d4001601210707004224601d8040c0c030140c241311016000c2818450110001500e040c420401c4601400440c11080341d43e640c0c0d102000b8032600039005100c090300840003031201c642010310405054040d1500315207076040507041444040390741c048900c416a80c41e011f83c41c01080080000700500703041035000310b649140c20304008415024400038440303810304001241d000c6503400038542100c4c1521070030395543c00c0c151840151407c024900010141070910341c1c41480d903140400c0007021103500c64241d1b4250803803041c8a030b17101c0c81c0441e802948000e05006846c100c940d1200181e500c0250100d032800c166041801201c011340090344900c0c00130351076008000c100311203030085084071859100300340c075250b00603030000751203881c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 752440629 1250 752439379 752439383
    0x306080606060d020f0c010f14090c030a060c03020405030f1005101d360d090e0c03040c031b14221a1c021008010b070f24090b090316 59
    0x500405e81300340c5a00c5003421a4900640c05000300096180d00710f0400280100101050201480000041c01c544021501c3c03c1e04032001005042006895990030000345400740b00201050340c03d1002113190b403010820398012001c0e44000300106000717100e400d41a184010001c0c040d51a04940c1000a400d808910010804403401c2c07090305030741c5140364500c81c0c22011084a2600b2408210b05402a10000d403048100c0d82450548900710003070902994215004c0c441c00030b55031001d1002860129940005e160000d1182440010090356604d4030540d5080c001c2c180d81c41081c202d0410400801c5e00003041d07203581e0017a83d6059150320244c0305a01180440d449002030180c80e4040d02041c90040d25500044010060111800b400ca2410702b039880185d09104074001c001020240018900944030785040b59039410081d0f02d003030310303a69401d095091520400c03a00001410015201e401d11000000018900360000180c41d81c0310317050071304454001605d500c04a40007003207280e10300301e085120082c83c80d0f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 752441879 1250 752440629 752440631
    0x50d030302160f0b060a05011b0303090c092a090e010b1c0204180b0906151b03030c07030e0103110406142a060114060a0c140610060306080606060d 65
    0xb00c0800d5490001d08031200500c40a1a01d031001d00300700b0500d0443d8001d40c0300707841300d1002c1501ca500543d03000d800c00000c0303c002041004014000391080c1c000d41c2c0124816080c81100036959100352003502c100f400000140c09440c2d200000b540c1e58144a00501d258501c0c05095041c5420b01407808000f040c0502c160706030002402030340c00030b40b08110298503518094115510b40d55030000b0010290901d04003c42079050a6414005142010f04280511001000c0c00804071101c1142440c560150f8903c4120030788188001c80f9864060024510131280b4140b0243c0d01d81151038000c3c800030200041e02d060601e40312181240200801c00da4041d40c2c50742c1000310041010820303040042c051003040180316405080685103010007460a04820412141119490398a82514850802c1d62511464010351b052028041c010300c00d10415000d40e000300034a9944013070340c2000c5401d01c0310484540c0c1501e00601001c000d42ca40c544581001000707008050162400c118000500364814100514905 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 752443129 1250 752441879 752441887
    0x15031e15031e1b1e012a0b060d0b060603060607080708070b06030703050307030e0607021c0203060c040501090b0f1201031407050607051f1107060e16050d030302 71
    0x21401400c816810355001001c9a41c2d02c40b6400084034151610414a44103000341150b005401e60f60b4440b19102c2c00c4014000c08124500252829050700c0c140e038a6410001403a04c000384061300700c07500c2c2d480494030000200e29140c0ea0b09091101e80c0c0d020348614007540403220114003154010405a403c018103e902603502d88035100041d060340652100a4044040003c0503802c0114410040c24803510484207440e40e0740e60001090f0301e401880c071029080380c104019440c0001e00c20700c000a528040149034504046113900401c0317819a20050b440441103444048806610307040050550010070300c5401490a420300000811451f598400c1111841d0041086112107a4400907228040700d000c01c4444d403980c0d241040445000c4500001c070950041d041e000c07410341003c1007102c183c00e4201e001014030811031a0841100c0c40c0c610040c029a82c2c3d240d5443c8500303552000146005070090380c021650013843e8150030700300b50074100300b00c50030315001c14104a41d4560008401600350142001621 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 752444379 1250 752443129 752443141
    0x10b030403021b060f180a060306180f14010b03040308150f091e07051308030f070308040218011206060e0f070c050c1f030509010b0109150c12050915031e 68
    0x50240d98043c51000340080303203040701b120813074140060b1440101c88180210b9640d0500350100c900500a640d89101c0350080c844002600b030700071802d1114004030008480c8000c2e803181e212540d080c1c0268200034000401d202c10715078441140350304408020200300d100141100001d1030076540f121ba4600580cae070031001555141d0380b816601002303070229004c42507902c2c040000400d254040c80c011106105000700c0402c00300b400105960995401201c0c19250004644068501c0500240100d0b03201240203484010100f8141c180350081840b80e038000e03029012842c082d001d4440d80c0e08042104c0d0012000c01240c41000c01020f5002400b0b414481030040c00c0f42031560600200e0004260045401e407102d40000070117071450500c400041c0d400700101d4450845590130f8480240403e070000c1c0c42c0800c04c1c800c41d0007403414420510414101450100000d9170f039040d08860408219012600100c1d8402070b0b420904074001030800d045e9441d82c90752621540080a41d0001030406c80c82410001c00501 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 752445629 1250 752444379 752444389
    0x3050a110a0e18100f0801060b030606091315141c06050618070810320a030b1905010b0a080408131e090c0302071104050a0b061809010b030403021b 65
    0x100300d4040316490300440c83c0051900705065168817507071011048052000a140b101840740406440c09000c400d4610b0b1100d00402c003194003c0d42c0c00c20b60040c0c0c1018040d490322410702c9100484c1c204985e07003007419854980c3e85000205043c140a0052000e00c480c814021010140c14903080c6e445500050240c80340d070040f804074139280071503d0050040a051100711504504014410100707050003800c2d06895030700101d4000302175080d8502440c840b4002e20000c8003851041450688050504428643d9a84902d11a9441600c517880600564000d001d851885030007400e025000340d0f04ca9034502455010300030140310300200083d05419001c144271040c0c10081201600603d00c64891071083c42a0607040c9440c05d4640c403920720010310b400840b6200a00a00a882c20745410a00d0642421241010f020103404001c205501c242da640380e4000035951160003603c50421002144603400b60040d0900c82c00c0c250617000301c00300840a03c00c00000a900080d80260345040807480d40d030040710003003ca0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 752446879 1250 752445629 752445649
    0x106030b0117151305091006081b032805071202150913020c1f180f1e121407080301120201090503060c0d1d03123403050a110a0e 57
    0x15405400c4c001c04828240054004a008a20240694402c080c8000300c100441d1014415042e1640000c1940054000390f141c00c0c440551014007aa01c0135200c9108100040c104945070b510700044200e048400d02c01c007000903d015050300042c0042c4000140c0010b1032445d03c1c4441c8210610b800642c030015600c0b0080300076242c001b51003065451742d10b0180841e40f650940303c0d03084410041e2403404040e202d42c90050b0000c00d200220f22442034089034440d840151200030055410302880c04010000e403414080080201c1e01a90440043e038039076100080c03441c44090319400c07041c0024001000803400a2045a0448101e001e8803540f0040030702c0147ca041010364460760f03242c000c440810a601c1107442c010442860200701c2000310b03414503000703807007860703526501b82d24130341d105004041c6031040f011000e540003a8040341102c8030a12000050f0300310b203038050780280d02071800e240e000041c0f60180105030300911502010700030100c9a1031240502d01070300c00e486003000600c83d61340581d40c40300400701c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 752448129 1250 752446879 752446921
    0x70f020916030e1f18020306010e06130b030303011205150106031d0303190507171e06010e0f0103050709030813031a091515120706080106030b0117 65
    0x10002078944070100100007160140250040307400c004107440801c202141380380594a100c10100083c001c1071180c00010020f40c10b1089180c440724161001603a81000f030b0b0b80c003d1110003229080d5282c22001c0c8440074410100d120041810b002c0c0315502e980d4044280d82c1500c820001000c140340c09410203030302e00340d401280c418035441c5000c00840c0345035158120740051310b00600320913102a9100300483c0c0d20711080710215842641200c1010024086410294021074a40b5141c864407442e1980e04248440c10b546208800100c044825520403564403030070741c000400d0800400d0400302e08003041c0780c104051541810140c0e07070300c00540d005003d81c40c041c0196070041909078a403c1e00a9042009071400e000030780744102004104c4103e91415100c041c8100c44140140800d1074144000c90000900a4404444010807018030011900c41c40000750001c29a0760003461154640b180c003510b04081070300309408043c01c02c1c05002050740c202108600da01d410b21019000d41d0f031101941003008000c000c0c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 752449379 1250 752448129 752448139
    0xc0c0e06150c0606100504060c02040f020708040b07051e10050c0d0e0c040609060302011413120b160503100e1504020a12060608060a0b0d0f0612030e120303010506070f02 75
    0x303014140e000076001c4c0c0320701810f444810740c0310282d804c2580e090107140705100009454505e00c10046c28035800c038200c0f403440d408001d0f00b00707442c582d544a0305400940080180c860085258001d2050401200c10041440707901c80340c00e0f8000304025610f80c225010f102e0340e0103407224007180c1c103030321071308220340c400c600c1184100420300300441066200e071140070709a40308504180d0082200340c0548250740840e54161582c8030380d25041d030391098041d04000d10100d1010114900002c0003018a501c03c142a481340c40d104550b403a140d05094801443c820a0408010080c002c200c101e401850f0104d0540c1d83e000d01d61246503a4001a00000724400300030650414008104240400c3d00800b20582800c034803801842550346600c2c0850710344070110341040c1c2c802c0480b442041a403507030030000c00352428818404188440307060b0b0720409030366103640212080c000301210b0205055000c2a040441041128094410741d5801c10310340d5a4003040c018184070f0b03500000e49108000c00e50301d03224113965020308 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 752450629 1250 752449379 752449387
    0x4051003321024150c12090312090812180604080a030206010602161503020d060311030120040e060a080109050d03230f07050705011109040b010c0c0e0615 68
    0x120710b40b03412000d030780d6000d0a4200012074212101494080c0b42c40008510703240d0101d460480b525100684100e891014400000d00f000301003807500440300340024081d251000035614529140c0b45900c0d03800b2140e42000b040e400b09000460001c100001c1c8110b03289142500c4e01003001541e141d4262410625070701ca10700042c0000d0708200442e190030040d00a40076901030383e0786c52000703981702d01c8060051404440d03940f0003408a00704540920300c40760824030b001410b02100030500b10488035948c000750740801c03600d00c2003031041c5400d02542407800036219908469202560014140d8090f034019422510b0740880040d00c80e85800c81c0600041140704020700c2100040d013855510b400140c5052000a82044c46c41701242c040c0c034264154440060407490020b995685000707008a001411036401c1100403c41c410200f4803d0150514403c0c4800f8000d6a0302c0c4000100402c4070181e0400c1d42c10320804500e0140400e004d240b4072811660f089621021a68500002684e400440320001d0310f01c110200b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 752451879 1250 752450629 752450723
    0x1302131a1908060a091112030405010302030c1207020c0406080a020619050c100203040204060e01030b04030f090f06170f090303010e07030b1017061e0d051009080a090504051003 78
    0xf03041320340114000c41c079900c2c61b00720324000e11040e21208032811020f0741c81084104010b5209a00540e03208010407880b50074802c05040540031f8140c29100710340180e100d03680c5031b000c500c1c1c0b5110b640020601e5100511400e603e980c041401800b5070140301e4840b42c0100c0701c804615000d2030407165001d1010090301d98030302081214800075003040d58240d02852801d003012800074030a1002a06980d0855007004840d5507956044800243c0c540b1714908001c4440800203407001c00c050303d60302070940350301ca40c0c00e66106a0241c10080e08001c0104000706000d030140490450007004481c1920021280103a180c0d071850001c0e40a0011481990b8010a9120f23070500c007154050104403160300c45009000c030b00e407a503800300040e0100e500c0c600d505150160300184028509403640400c1c00340303d40d00380c600090491082c0800c0f03580036282543c1303000c00000c8180c443c42d80251400d020300b01c11275040045080c40245001307207400c075000003400d81c245840442e020f024510190901207001c11a1140d28a9880d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 752453129 1250 752451879 752451881
    0x510062d111207020117130213060e0c07080f1e030a020301060215060102071e1205010b090a11071e02130b0316030209060d14061302131a1908060a 65
    0x6001c0035007441c01070000e9904a00414800c07903607540d070140e44446c2005089038154000c8500038104154002d054003c200c0141c0364200100c10540050394001812440c11000c6040e03c803000b00007510059003046a900094204016181854400e03911152541500c0b204901d403112400020b000d0034101004210031075006e03400030740c160352195081e18020046104c04e201101c2064500f103001d41c00c004c10911100d00810b1a00501030b2080d12410b41040c0d96414240c51340c0e08104003601c059448041018940c00e003150313059008040e83d41e003000442000301000183d0b01420b98024840200d080e50100c1c0709030421040000981c0040a02d0900e5042290740002845c2c20070460303000e8080c81042083c03021003a000c01c0d007240c0c3c01405c0e03101580e60791030070060110901041100c40d013a080c050300c502e05c401041041e2140e900701c070b441c8c1103861890040207441490f43e0300c01d0311054145604089050411100750b04402020f494068483e8440030f1040608030140d0840e40c0a840350904012180400d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 752454379 1250 752453129 752453147
    0xe0d03052701290915030304030209160e0627011e120c09080a0206091f0801031e050c010f031b0815040b090417040f06020c03010501090510062d 64
    0x201c2c0500b2000440f421004150380003401199503885045a0001040c254103194881a0407100030280d918250316540000e1004500750b0302110500b64600a51a0b4a50072035115282c14400f1141d5034102615043c003207014403014414400348482149041c140c69025101c40c0c110008a141d072a914001418402004000c00999240071036060801c1d506105001c0e9000348241d40c16580500100181a000d0020325400300c0034040d0440325102c0c1c0d03030480b07400086984951a807155241106945581000b0b0640c03841280c4505908140300d03000d4000030000218284000402c1c01c020038454000d00c2c0a400520310030403080403d070034180001c500070b03500401c010b21616014511400140e0540d06210456048070301d0b980d00580448089008140f4a0046481c8018070080c080e103000d444009520207287d5582c00030700540e126044a04040c40d003802401d02428459100b00214504400342ea44041294171600e8180000c104c541c02840f4003224808075980340d0000c40d281c928030982402420918 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 752455629 1250 752454379 752454401
    0x170604140c061b0d09050f04091a040503030115020d0509040527150901060b07020105030c0f0409050f33030102071b0614070515060f03011d070501030e0d03052701 72
    0x1d41107551104600075445c10042c0c5201a006c2034881d0240010f0000400002c0400d641140d0600610755444110b810214800c0c1d204002558981d4540005403c021049449040035900041014100d1540c02001d640041000b260041400d0311001081750341c3c0c610000c419080651491400e1a25000008002100c46a840340001e082e94030524843c0c200c3d00580105002140200808c02c09503205501031358102417007101c150318044d0b811000091030f611903408602c1d902d495030100216141c1d8246510360250384003020400c000652019031203401c0a60f00140203c0c181100e2807203a944007541512012513100c2280020803d0b28049149540668410000007a8901e6504d8000c0c48602c015101c0d010380c408001c1143e0031490b09558020200141050741004610300b81810981e42409010130480b07111444000700100468075034142032294000d02d05050400285000b41403000952168110b810300d400216900d5415586e249130030183c03042800c82c0048950344043d2141980300ca05501 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 752456879 1250 752455629 752455633
    0x2120d0908031c15170c010e010e0f090a18060e0d05120708072106060e03070e06100201060e010e09010f110720060f03060307170604140c061b 63
    0xe0307660312045039203120b0300b00104681d158a002c1c48200d20b03280d421114481a00501c94000603441e1603044c289440c410a50030082c1e440840050300c6541c0003025194580c0d820b181a0020a8241012448510300c01c0c1c2c200b07008415402c001a8454460b50216000c1110f03250f016003c0950390405602400030601c81640a010344811074401c40d00650889805c0040441c1460317940e80c1350b503019150350344d000f0f000700d040c03140b8001d10b4010854507061010560003e2400003442d03c1c20000010030b4181501e1070b040c003e0380401c00601c425101d1001c229032061003210b600e801c02070f00f002e049024290503400743e440d12420350000300352031418086161140c0c2d0103200801c00155400344520564a603200000fa01510030080c6c00d0110700280e00ca000c141c045031060141d04402c810126400394014040d0164806011081c42810700d03080c8225030003860000c003185002032040c92103a44414010f44003c19250200c90400000c8005110104500ca0000d01c8951a444032441c10501c0f043d5190140c1524 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 752458129 1250 752456879 752456897
    0x130e0708041a04030207180f0f060f1206090209072102070c050d1a1317040503071838030d02060109020f0c010c170f04150207030c02120d 61
    0x503128549562160350000700182891251500054503440c014005030114000d0407404507400c54400101c5d0422190560300050401b1b03c02c1415040f10103c0500c040d00c40d00b07164040100000020b0581c05984100e840a8a1103d00c1e160405c010261040000c0d04843c01e003041100694128a080c04180034250b17281e020b0402c0782684104921030014001c08040300c02d1024001c80c00e21f040d8600c00c2510451219a00190550b003000c070480c82150b61082280700701c0d2500d010130003031007407441400807003a055600780b50400380041c0d1503101078003822491174480010181d4588035a0070103018040120741481541070a0301080d80c024820400003980600840782c1c50105080c0081c0b1011822030350f070b0140080742d00704030008000e50701c201c2c0d1207401124240140600400c00703124840c00c4441c2ca40b0f5954020320100f00b24801c0b000c2c0100302e010b21540040400000c59980d982c855010104000010b96400c40e502c0e068409646042010390081c48500464000c034600160403560f00e040c5480382045 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 752459379 1250 752458129 752458141
    0x150e1b0306090711010e060f1603050c031303170906010620060601030e1011090306010e010605091005070816060b060c100216050607020703060c0503041a0402060f130e 74
    0x1261109503240c9030410700c02800a00150322508100400991940001c41e80c84485100b0034908281501c1c003009142e072590501002200100d080260321004d030070117000c2c034607180c21030844030b000050402241d0a5250a02810103204d8152891400ba0300d10119000f030403c09101a6110001d00581d00030a0f01ca030100c10304545d111044421030f200d2a80241442d541c1c840045016040740c0c0101102072003584041d0082e124580210b490440d41076801540701c002c04000c2611380b65040e0712000c00601032600502005030305c0800c0304e844101c1941d113000d8a42110b00200d07210b00c035800c0301900c0300300d01180071500c81b4468090003e4150144505000801c41c403c20000c9034441c8400b01c440c0799012265805548016402030083c03008014060640000d8a85a1310b0828004403185001600180c03001d00400409115000c2c03503654907c0c14508515040d40c0f03060141d00c03140101500c0d0404d02001408640c1c5100c101e821240c0c5032840152036003400c0007074039407a242d07600444440349068070000d59 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 752460629 1250 752459379 752459431
    0x20a1221020c031207260903010f05190c0c08130e13030e030106050f0405040c0509010b0d050714040303051c360201210605271602030d0c0201150e 65
    0x1802c5406c120700b41105030074540c0a891060783c4220081e0510700511000045940a216100c4001c0d442c520103c0c0a1500e1892841554050251909100e26100104521540c020301c030304000c951102070513940f10309403a090054621503522090310300040804000411442c86410203c0e24841c2e1603010182c00c505e000c2500380d424a000b190b4000703d2341e8001202500d010b400c6203801034082c00032030190a807104040707800751000740c024120350003000910226410584c401c0760380c408210b00e0943e00154213541d81c0d241c24403031480701404000001c207400b00c82e850300d541c0604084a408a04001e0140c0944090030b00305e0705203140032200c10464012400c4851082210356000341d050b07503050030810800810107052a4404102c0704803580c3d4410104954607210050b41c440404120040244060303403c00b4800540010540a90006112944a07070740c2c1d0000140d401c0400a600e0206035414445c1c0100d005101c607111450030303114144400240039000e484803a01414800c01410229101e440f0114 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 752461879 1250 752460629 752460637
    0x706030c1707050306010c11060f040609090b0906040903020f070f0602150105090103060e0f16150318030f02010e0604140607080903040605090609181012020a1221020c0312 76
    0x11003c101c0c10800501c0540c42000d0008626105401c000007004a4601140c02c0e600402c1e83c400c10b03074100107014424160401c408000505a0380010f0015a84080110b0f09140020b44100c2c000d64850059404041c000c1c030502a8001a00301110380280ea104034130520524244111000340c0688001c01c2507054a94003c541a210044c007202240e910f16590700c00200408240341c116805880710780c00c0301c044248500b081004058040c1d19582d418048180100c07501c000c4500300303041c81d00c2c0484108030f290071301039044603400d030900b0300c044a0800d41c00e9000d0041a11031001c140200c004000401400d0b050b41c071031020301130045680c255070301c0c2410303680490142d60307401c1151300a000c10400355103c0d000402692030013034180740c02d003601c00c8041511140702d00708514480002d03a0400864041d840b108500030440408403106040715500451000200b5004480f0824007224428040c0b0144c182401710b000700000042c8070590090340003e441c0c04c04e104c4c43c50300c2805019000724001038288155 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 752463129 1250 752461879 752461891
    0x90a020c0a0210020a14010b100306030308340314060405040302190602040506070602070203010f060f090e0102090904030f0212041a0a020c130212131e140706030c17 73
    0x80c000070401d602040b60201081c68440d0851151a0007840001c54a1022665031007024002007442001e14081068410f02d2901220405181c540e003040804c0d404240c1d15000441810020100090f001c450750000310000d000c0030010844001c09010a60f00d1791004035858400c091160254582504210560740150760240059000c000c40410450b1400c0300c0c40304180c880c1800510300340e622404100303e03030420501503078844e60108106003981030a00900c044c1720503120081091038105400200c50000074003c66104035a10100b00e090000709604499a0260042c19110240380904d4010002114400d000700113009410b00044980000c005035010364074100744048a15082c0204800c1c1908a00942c408501c0783e054400a03549856400c1240e401e407100c00541c0d180946400446403101c00341800759042401c1c206040407804000220420580d42c00c0c071900c0d0f00f080b605100d80542c00c01b4203440304500400130f001510350307015440151200b1890700d450407002945010b05002400c12184 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 752464379 1250 752463129 752463133
    0x1e06040b0f150a120b100e0a09050705031504050d02060103031e17240603090c09100306050112030f05070c0e130503030c03150a08071a070203031206090a020c 70
    0xc01c505800c031007002036000044000000020340350358001042040c0d19808001102a800c00b00b00c00e0080070360180342c1c404011000074600618100204103841002001507090680c4c03010a5010000240118130007408000c0854400820007907442c4516002682d04403032511400404060007400461207a048980540302e5900d000003940c0c0c1aa014001e07070602408100b6012034002217100d0004e0310301e000d258140002441c0010032050075021901f014159486a4406c0c010454516400652a044040c0640c0d03203621603100c0c4000070808003031a800041000f130515001184a42c19035180c0c0e02c032140240d540040072031660105880c40e02ca614000f4082020450041c005109084420707a0440c1408050018101040d240c05080d6082034580039803408001080c00300144d80d03085817825006040715003900350351a101c0c809540c1c08030303445821300c0d0495854101c1081d41e89802600e00b441e4028007900c1d0b0310308524000b2001c00d00112031181c464140e43c00801c0c05140700d8401d540003031100c000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 752465629 1250 752464379 752464381
    0x80307051b06190506030f060112140f0d0f030204031e141e0105010807080303070315050a03260f04050d110613030c080d0905010f030f0c021e06040b 66
    0x1040396990300520318911089821180146980d2081001c1071044005400d4507400601245880068071000b41c01503101740d100c5206400800380c007060550440d40a809124070303100740c07072030800311610114030210f48600a89450b80c2e665a0301141c44946000f055035101410b408005040d0101e0095006c0a490041070100c00f00f41d112aa10f0704030105d40c000c40f020017201706034150b41481d10803220741d40e12a940f000c0c0784400901030240901380c090301038a00a400003c0c01c05044554030300005154104041c2c980340c810300b00040d21089400500300140590000c5500c0c3d007003024904036844501c000e002000c0201d00600c0c190130094507023030300706110500d140c64a040104581d603620316000f9100c4401054910200756a0700c0c004044005085009104c80e51950400c6c22600456601c8502d00d03401625030244c000d9408043c4030242c9100742000c100408110a00710f00506201d150f40e40818548807200c161207400003070009041d1140107440c030312940c042030300c1500e1b52000d503002000c20705684 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 752466879 1250 752465629 752465641
    0x17040315060e06120703060f23040b06060a0309020d060524010509011107050d390515070209040305180a1a1e030c0d1a0d020f04060801110a090608040803 68
    0x1c2c042007243c1038080c01c8a4025484e91144401c8469455001a03282c2d52410303281c02c1d10340e01d010701c4540245920544c444a28ac6610303074150041004002c1441444d00103446003590b0b000750300a07070086401802001242d000b0b442d10b44c00500041d50755038a510244074054400545156250b10290f506079102400c091802005450076900c2480c0d4400c14000c0c070f840440c0e035880d250385040005008406141c0382c1e840864551803249003104418010a65480605411036103c0310094101c038801d5900151101c212110132000e80290900207620447d00d90910082c5540f020203000d0010154684108031285201000360300b1089200c1c1403030115075031b1251502e40ca1080c002e040c10303031a071075861050303c8180c48a820155004841c03000150707001050008140f0040e10407102d0099a502d0100001d0300b43d0000076216541100c07000740710f01700d044000c11043d00c1d103800082c000d012050092207800c0c481c1205e41c0d850341210f0702450000b03400190015041e44210303202c500494025611a24544440b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 752468129 1250 752466879 752466889
    0x9050414010219080105040b4213061b020d020d12090611150411120d050a03050106080f060f06210609060108101a090d0303050604051b0909090a17040315060e06 71
    0x54402e00e0f41a080c10540d00780003a0b410905881280740d80b1080c555504030400d200918152b031600500108441c1080f40c0d8202d660a0808a141c80d0f01115581c0a40380c85200050310040c203100001d001404880e0b40d08100741d04015400c0c01d480ca940c580103019a00e001c03d45559440c00e80d484c9082140a60200d0049807a02103421403001018203000c1c000840c0101c0c15150940c8804128006800050240c03c03060b8144240d901500291620030303010704004111160041c1c010b418203100308045028a210b07555080c045a2821100c0205c8914002c100700c44c040f0340700c02c21140c5c02c1c003a05050000607041d61242c02c50314402e03010b1070300c8503440ca410050500c01c030703011406402c0c0b03a2803400c020b2002265941404500000d10a035004103540c80e064082c0000e4400c00350a044000c06840c10100c0303003800e4001610440407040e2618840c41d940e00861a2500e502e44101420380410048880648a00b000003442541c2c002c4480c020b07110b081040141c01c0350fa1a10506000740c0c0c400740821072a10f40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 752469379 1250 752468129 752468179
    0x31030804142a15040b12070e010c030f0909050c0d0605040b01050a0f0c0f061a0a0f12080409020a09060809210a111507030e0a080409050414010219080105040b 70
    0x10107041d011100f0044006400c0a030310039004151008000f02e20f94103101450101345500a44510301640e02031300c1d0b440082d0000c00070b61002800d01c0140c848500005100341003110052480d0312040c0058181507550803015030001800001c01414034001142904050142ea44d2244040e5a003d242900d0301c0c800300c2d4200318200002007000050243c945c04502607034403940b104cc1c000c80000804103100700d10103008600360f4810318000e00300203400300f0010711f00000701c1e4220781c00e000c2ca80c00c014125103404a814802c0d1740080b40294808228414203d601c07000540a07101c258580030313074a071101e03c130b00b0399103c009038103503400a8601018550300070f903c00058000c2002c0e5007000060003101880d0a800d10b8010340c480d000b04986141000001c40c0e15008105620342a00082c03d420003058540c030106d17110b02e00403900c40741d40320700c00b042c200a45000080d0002c52000e00071500c9412090300510311400c0c0c549a400001d508030000301e803910302885480d103015401043c078031045100485900c00310031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 752470629 1250 752469379 752469463
    0x70b060307080f0106050a12020a0303030c03090501140f1b030105040209010309020303190206010b0c070b0304050f1009030e04020301121101110a0f06110306093103080414 76
    0x81540000b5070000420190001e1a01c03c0c00224041d8104002c0c081300040d00c0d84209084202542620056151481c4da281030381d425140100d800c001664040d0040d20003094001e10b1507103001c616908182d5844102802140c00b9182047d542d22440ea40340c1d01d1008104482950a404100400203880d19500511400a040c100410840741580000e4256000804c3e0b02503900c14107806000131507414441d55000d000010f862a017400e00c0590102d9a0f02c0c014014030f010108004003040600c842000400710f0300c070f94041150100000c812661020344180041280855200750702070701c4c00c1c601070003504c2c1a104001e4002c40d43c40f010303442d000302e4130350740e0030509040c40081d651002c0140828058100d0f030a019410a40c0d02d400c0760b00e02481102c1407244084043c41d401d1051109940c1ca2200340c90300920380070001c20400d0296042c121804000c0080c00c2c030048840d0440104040d0086240c42c4207900422003040c007034010080b05502ea00300e40000010140002880d5170206181e05d20b4208100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 752471879 1250 752470629 752470633
    0xb040c090e1e0a050907170a030c0503090a081605010207060806012102190e0d0f0f061e0b1804050304061103040e0f091006030807080315220c0311070b0603 69
    0x514854840c0b03900400503115140c0154445041000b8140c0400c4a40d009108103410310742103214280005880740e07084e180060400c060011032205100c2c0c100103845010900070502c5050540c0c41d00415580c212a940c0c00300c003006040800640c03580080f076500100c0381180c5490095a41e180c00440380728801284850307503500c10745010740c0162841d1010304210b602c140c01d00f000d07034942440003602c0d205215881512448814802c640056500034108182c207900c000d40c0c04101a840c03034203d000e4030b014581d1089210703260b500c031045811103401001d0850701c1940c640300d94515908031504950300032100900785500030041004410300c28000d0310402182541640d040644031b070980d060450080c1c0c0d030f28041c071995a040c403030004810722241b406000701c814104110b92031540c40a0382ca0040c00e4000d040807502000045d40307002c0c0c1d4105100140310081080c4440b0311030b080810810300074010508000d0b0b1a140150152601030310500d44408000e0040c0d506000030382d902c1c649402d400400d9a6054 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 752473129 1250 752471879 752471911
    0xd0908150108120a020a2112050c180d200f120c01050c01150b0a17040c05010c0204060806100305010608070812090a050d0f02150a080f090f0a0609060b040c090e 71
    0x1141041f24403a499208285258559901c1071034004c143d14408260f020300036203842c05010500114004a60012b01c181040e001042c0741074000070012660164050030640302900c40c50913101c1880030301e601c1da44040b9902d5004182500a000e110103c01c1b06c50b035015480120a861035601610140c11000180c80020846213941070f08002c228100b0361110180005c04285d1001176138100c1040400240c02d41c84600c60340c5050b803505d1064022612407207043c030010601d40000d64a441c0c10100c0541010301c00c840d0541401046810b50030b1041c80207640039441c00c030010070b84d00c002042e10000c540c03e010082c0561001484010416444000c030164800340b2184006142c3d00c40c035454102c4280100786207138800503180103200082416111401c8541c0d0104051000c1503007210055412004940394903443e541c1c1c45030718500e4644803800060380d6111310103400c400c104180c2c01c200b1845118031401d1200001c0c14003444140d6070020842e030041000b404080c020035056044007031344141c041c140c411203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 752474379 1250 752473129 752473133
    0x20c1e04060611061302061219020a3606270f081216060e01113001140909070e160f020c0f060a0507050d0908150108120a020a 56
    0x45800301da200c580442c4504903607455950090144a500101c0c1703a00240c4024141d5000032258492101f59212a40603074002c03400d20440100c2504011000907011035503140a00b801130850440408c48441100c0718118440d12110790a4421019140c982d1a07101d00c00d040c10020b07034200480b4442800008071500c00e590b40c044d4040640001486d400403404600ea04181c18281088268100345096200401c040748030704017107081990841e82c100303400152180c6603c0d0028050507034030385c5000100002140c41d03080d080c032103017450b0141d440d0a0710480c00c5003044155898010000d210300d20081d940c0440883e424100400407560228a040a92f07010b01d84030f5041042c4008142c443c00e517074805054034040320540090340303c150082c2a0005100c0c0d07801040000d182280e400c000703180285000b003940d0b00d40c01c5c000c500f92400030b03034894180c68200904400040401181d440740e00001c1c07180101c100d40b141040d1540c0350585190f00b001e025001c81c0301b800103806030300c0b0001d40f0301140300700200000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 752475629 1250 752474379 752474381
    0x10612141006080a020f0a03050408210109180f0209070504080f0c2809020a0203090a090906060f031709010c120c05120408150903040e010b091e01020c1e04 69
    0xc856680d01d14220310050404100408200005028104d450300c10008005c943d2109010b8840e0f1003194a000304150342e0324507011400d40a07415141114020301c4000240e40aa4203401505035440107000700440f91070080745030503803a0260400350051400701811400b500b40455010741c400c03214184140b910f0b64550b00030b858a0040881c4000355040300040d10b4081ca420b000301c201050000c1140d480018020000840000080c4121b45841e640010b130b0032401d900a1007074074090880284032000596a4000c42c03001b900700d614040799028502a0040784000320b00880d5400c3d2a040040c0030f01e207066000600e4144e0340400e02c01e5040c0481e1500c5900040c80701044807800e025140d840d000b0b40c10292804920745003d60460b1003d01030144014000b039803001825a6200025074085090781d01c07400c0041d8294459034102c1d0608081d1100007040e07806550004041034102503d6150100705182c8059113860076159400d40107070403650360b0341003516101050002400c2e915032034000c03201840c000a4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 752476879 1250 752475629 752475631
    0xc01120c0c080c0601090b0d11120709020a120e0312040f020a0b1c06091109060d0e01022b381309050105090a080f03091c0509190e01061214 62
    0x42030f6a03200360014030400060b401411258142070b0b0b400b00da0341460740d0b501c11581c030384440054040c0c0111120303001d001030104203400040180d0711086540348802c40d0014040102551000e0b20203045c224450012034000003210f15600518200b030445441c3e9035901807a1010344c040c2640d22045106001c02c1090400006042000e03416024001251803d00d6000c1994681c2c1d100c0082e040c40e00041c0c0f812000010102e4a115100f210b9840d60340040d07400b1340e03004180d10318900310b182d8030105944000c42c84400120700b40c0e02d498180b40c01c10201040001086c0d410120300710000d2546001141c0d903a2100347c6103d0700141c204042d200001000c1e01c007252070286030404200c10182c42e02011410b01c00e080c45544e4010308100702414403841c0d00d4480400c20b04c1241c00e84094042c0c00000221801018440c2040c2c4072034120f980361002c405440002d1a90b040100841d110b0040000e280258042d10010b1904a910322038003050103030b1801000340c41c000001001c8400e1580c903410400311800d032031020b203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 752478129 1250 752476879 752476897
    0x10020a050d0f080f01180b030106240228110414040309050f01080c09091f061e08070e04110906040e0a1103040f0f030e06030f09010e0c01120c0c08 65
    0x40742c2e4520780384a0050200001401c80d2440b0030b180c40c0103005192240ea9030301d168030a802408220a420440443e0052400741d11050844000402100541541510000321b42101c3d600300d803410f00300303118ad440101e030251064030003010020b4007020004416550007401203800070400220b02e984946070124549080310f0840c005146840284010300c1c12104004c0e01c8a800c2c41c10f06002d14003085692040d124a00a0702d104203820030002d108003040e8809001401055280c0d2015266112800351151444080d904101c0700102d1144010710310440c1c1c0d261040503da9142303501844ca47c020720000b0030000442140300703001000720913402d44a2000a000130103096007000ca01d884c10382400307400c44103031452602c80603004100380b001003005859200c0c84240c00c1910f60b80300d1078031481d09541e40c0203450b890750341001d808002c01c40300710760106400307101e290082c0090083d88200d07990181c84882000c880c6001c9103900000c500801800c3d80b040d0300c3c0008a080c10741a181c0641c8409446801168103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 752479379 1250 752478129 752478137
    0x9100f0311280302280b0304060b0a120c14031e12040f050a060804021302091c0506060f01020610031713030503180604031203020903120a0c05061303050910020a050d 73
    0x3c01c21410192200302c685c00e500e08000e00002090b2401c108803098620644014407408004038092040562240d802404001c0018031040d903075000c105000a2919020394910072041400540340141403c400070f1148000c02410003011010f143e030900780e9540110f01d17a81d206550710180034003001c60040020782100045d40c07101c246080100603c81d0001d8001004000b004006c1c80700588640c2002c40600302c400e800542c9901c0410b000c0350840d00404941072454651403a544184500072a40c207008603400e075110480d01d1003040047e6941c0b6003c2d00c800903078801900040001c07441051240d1108401c58080703e2a2480111a00740c0c0582940c200b900d0350741000a40c40802494400c0500040106542150419145403902c2c49011420780840b0280760300011190566a0b0500c1091280038410345015103854450600400010304240d0895181c40b600d004228500d00c00c000014129502d683d80302d00c0d0035107100922007085001092241980b01e4245078000240c000d009a000e5600f240c0d403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 752480629 1250 752479379 752479459
    0x2a0207080f030912030c030702130e0102040e06040e0a0b0a020d0b090108281205090105130b090f0108040807060b03030403080408012c0a110607020301020f070209100f0311 76
    0x2c008904d6014401c2c0c440c1e540c0304024544803203401006941c0e000ea012500c16202c0000c0400f54070203080e40544225442d480007801052410031001813500404c0300713030303400c2280039205402203aa5031101c1c48094100c10560000940d5950f0540052651600c03811001c140781101d00301045480f0000c2e003020354503801c0000f8084c00440750a00c0380c00d5a48440e520740e402006191101285450804100c1c0c0410030300003041c07002a4021400c40711040c5490407201c91050356100300141c43d80188506600c42c4c440c4c88600080c07580f28a01581c02103030800d840a2030300317001c0c2c5e8441c00100104d044c20340d0140420f11000000c601800c000e00b004110080000c04c18007038424078201102121441400c0c03018070b800f000010f845c40010420402944140c0c0100c0b0303041c000c00010001e02800400951541c0005230490f440b101170700180145a01c2170702c02980b19150b04d1048165001e140c0074169009102d042d040010580300488685080705c090200612003100e81d442d62010071000c0c8081c415071740340b00c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 752481879 1250 752480629 752480647
    0x5031009020f031f050709151d061309090c0b07031713081804020d11040f14090c03040f0605130507061e0e0316272a0207080f03 57
    0x11010204040e4101c01800d640103400f003920a45a1100301c1d113040e22030b80c0300f00144407180149421006044049010030703074400c2d039802c0108041b100407003200e0240085803041c20141001303003e56080c00258500710310850300303008148006126221063342c100004110005030b05100a0040c10394601a035280f4a00c034007102d0440d550b8103030140c188421a0008501c100c04965200c0541b02c3c030414121111840c001c03080002001303400f5414081d00240d01c0c2c01501120540d4a000408c116210780b20b00c01100b0340e41e0441052860410952250000c80d800300142c140c01d6070b40c0c0110f521900c591100449190161034140c2241c400700c4050071903903c07000802c000d2207000c0140741c0060105140900c0c0340805c04542d1a0180721521202041c02111145100b02e41e40070b0020440ca1100d1845012000344c1d41c2d0a0040c00954048482054600c032089006440b24130780035400c901e4600341152041241ca1403240328030b440710200401c00714080c01c64041011030042c032125205103003c00003180c5800d0b01e2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 752483129 1250 752481879 752481889
    0x417190b0f07090308120a0603020319141c05070501090812090114071d0109150503180d090513021c0e010c0e09040b090a060213090e0d0e09100503100902 68
    0x74000d103043c000208401c100207500c40088458600c10800c0d14805131f02c420700e81c4006001c15403c0254035010f84490117005074904414444c150b13005034112130803e59802c4041d03480300815070307000281e0151020b0301c8105138050030060400e14820b034000514842e10380c8890710140c10034118206519900350138051158824019030715515a981c0c2c00180b24241000b01400c443e121441d1030ba41d01b4a8041c401c0e03510381c011000c7c2802000401040004000c41035002030150340100d800f0420800201c50080007081e0004c0c00307200d000080d44030b01411506020070820b41890714140d50ba0415001c014003c9800070207554695015018800440c2041820500b80e0079181100e62101c1000f44540030070140e59a05403d154016400002244254440303048035030030500b40c0f441c060709142c0002a0142010420044d8608454203614200811038124000316140c0d070071001e407a0001510140041000d180c03401201c0d8128008001c49541c3c2075540c00802d0034250b140f47c544c0381084d940c092407000d601744 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 752484379 1250 752483129 752483131
    0x1e062d19030212180703020409050105100b0423130e060a0606030b13110c060f0601080106090b0a030b040e071e050904031d010314010803030412090602030417190b0f 73
    0x1981029400c00f00b40c5800180c000070000c20b00e0804e40180030b41100a0360040c030820b00030f150040d100b486000c1e04c0c0e08000c1e01a250554808150302190440060010a01000d40d402d0312721481d181e076104003468815031959120050250f901283d00b0740351070016106486400c3c2c03d2442da80103010b5070b1170540c80080c2203a0140d80140145803c00d038041c039155484082d002500c410381e400006000c000c2e80403116181c01622081c5120744259000d01451102d8204d06602c560701c01d9888c0700090ba200c010440b1b08494038456960b440e881440070300076840c040d401401203400c0c0500002041c20044242d945860f01c2c9a1000c24003a00746858041603803010500b050107000203461036262801c0a55004040c0040c103a000f40d556070604c2c495402d660300c6a00890a0410f001c0350700e20725961180301050f201d03403007600c00b25a102c0c02d0008191f03085010b03810075000c44403d40c000d141018900703500220320780b119110780c4031a03000b50f0b03103010b03030b03c0504221000300140542080c0001c0e15150021680b1180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 752485629 1250 752484379 752484427
    0x12140c0d050d12050709050603130c1d070318140f100c0e04020a0f1404150504091b08150d060f05071205090309010c11040606050c0c1e062d 62
    0x1304184c1008000d0782c02c940c0341c60441d48140c0707107181e4030303540c0a086505840c20f544000b004020f20b0f002c0064030302c844d0b201d6000d003400c0300c0c00e40760959211060150200c8043c2c0d50750b0240c17601410818008101d201a00380300440007401a00c0b1010b402401da541405038294949800c80c1d42c0300c0000b00e60950142040c00c012209540452401c81004000b07065104500c00800800c8001c045000010655605076401450000100348001b169404098450741050140c0100180f4105c1607500502c1d5074241c800d40180c02d602c07800107a4981c0e84041030b5a00200b1242c0c1e8000e240c0030b1244002641500c945409030610300b40004041c1080c9a0007008100b44100c119a510b007024284900c0d62008800c490108400342405944031030285070603000c800d00b0211040d400b6280071030011300349420800034140381c6000016282000c0f074800070401c0804181002e002201c0c0341c420f25581e6800c1042c000e00103103540009130f030030701c2e9140d00c030148c3c1c88440824134156070440420060030218040515821801c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 752486879 1250 752485629 752485631
    0x1202010b1005220b3c09010e0402031015020309121c1404090b0f090411040b1512130203160305012d1e020f1308030412140c0d050d12 59
    0x3d441e0140103542e5004500a05400c010f407042d4296451206036507111034844841001e600e50301c0141255521a001300c05c0c060b01266009102d2002407500e4800c6900c902d49100c5031040190414200840483c075412950301035100c108145420391b80c440800d12100c803d140700402002c0b6016002e4084074402c048881c0034003400d04e008111119800041e02c0135202c50000002d240b8007608001030240708041d59130f54020132880148000c0c48680c240081d0680c0058600348640040082070103022000d0003049120300c2030900c44803d001003080b11035a08016800d40803159910325400182c1031a13010741002010702203c0c007017001088000e0041416001e000d021594100401141540940c8000400c0301645540c444140000d00c8800303071625219652a48210348034055000c000300d0a0b849000003038030742108420006002d200000840d415502c50250134501c100c015a00c9182e040c540d041d21380424003501441401a0316900d1001000c00e028000624100120030405000640032100100d110707 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 752488129 1250 752486879 752486947
    0x40f0501030e0d030c0504050901030803060405010b091c0204060e0106080403020c0303031b220f050f0f030705010c0f0f0b06010f0201050f06120c030a1b0e040f1202010b1005 77
    0x904800304004401c9450780c20003048034021920b00b203449211f2a0801d070303417118000002206010000c1c0c060340c400d002c107807820003999072a010000c18038028103e01e20762151170130254901061109024403001d1748090800f14a158942200194046003604148001142c0030100400d05a0400c083da40c0104154055481c0d0300703280c3d4100011201c0d0250001074490006071410301102070900c0c01e00103c00d6101058403898480c9a502d07e260501d21405114594210b50110036281c0103245001110001f002030920b580341a00541c0c2c0b80b103900c0f1065804132302859604001ca01c0049801c032200344100b0b840d054507d0a50000340040d102c0c0c150000c1107a24002c00c00110710303005014650040012a010503441040b1301c04185481658501550540901240e050810144080c07076030100403646040344842d61286218213051604907800341c0a120702c0d1075108003192908016124a83e2244008104124403c01141010004410000000d440051401804040f1000454201400c0ca02403c51 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 752489379 1250 752488129 752488151
    0x9110d02220605040815040327140303040e011e080a080918041703090c150d1b0f1404050915150c1005131203050708010909050a2006040b040f050103 66
    0x40c6c1c4440f00d00030f000c07108002c0041000c1c0750140503100d80700760340400c201c11120210305510340890300ca03208034034102c1c5e1103100f00b400b5450003000351019640140f07040348890307213010641c000c48000c402048420f00344c03100f0003048806040c003a4402d0703240a080d1507541c83c24540240310190a10300425514410004140f20002d6803c0b00e0b66110540c4c5110a651641c56000c40a41446400b408850f805100320b90f81d078000905a50103807413070803103904041105510020708010050f40360603594000a402c444030b0f9413443c0c0686078185001448030280d5050644072008500c0806041c1c80311a03123499a140020b855243c000025002c0703001c202600da00b046a000300c1b05649040b040882901315803244002460680c116544501198001800b241c040003c2e100250050006036109000103030700c040045210403850290310070040c1e00000408104e10b207030712800700110b9240c0498003480c40c8411f0b001030581c0d030704001e000a0103561041d5685e075890b2407250b0b2000103940e0303c0307181418105109515 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 752490629 1250 752489379 752489383
    0x1050a030b0402132c120702030706121b120f0e0a060b0f0901171612030804030e06030115030e240a0609110c0d08040c09110d022206050408 62
    0x50403c1c0e05607009640b107183d00b207401020b41002d811414001c640b080812545140d01022001d41780041e505440526002c2004d0800500c201c14010750550310600c42000344070710070750140f8104d00f002540010484100e00105040c50210b0101d000011400b040d40324440c5d8841c8222045035089601c01c1008001c5d865007d0b484185c1242c028080654603004545181c03a03440010802050040c03401c241503841c0d03501e40c04281c5041082484520550303c1c909600140207040005070740804800380420600d50f0f80454081c03c0c000c000310100031281001d0407107030701c0b0140633502030400c3d0002000d500e44840343c01002c903442240d003200d0395031092801c020010503480c4d00c50300311343c6002c000080580c2c41e0300c504805044c9580c8000c040c1c92510607101c40314415803000e402d843c1c15034025a01d030086002c00c201d51100c0241c0f4040d103440c10b005800c100003034141d400074107600307288941641440c0f000b20768401241c0010030000210700c909401d101c1c484250141d8000a0701e040d00f041420a17040c00c005035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 752491879 1250 752490629 752490631
    0xd0305090d09140409020105120406061d040507140f04050126160623031306050a230a0b0901090203011a0408071802040e130b070309030e0d0201050708041d01050a030b 74
    0x15000b6950342d8038174420742e4440c404840d034a148041060740c0505091406900a00c4580300d40b18824069281010b6490342500c4550301039900840201425030a015070b00a10031100e1090076444018603070030a01c681c4079030144a00811600c0c900d00403c0d2442c498006850725041c60021454101d02d9034804190104c0c0134003c29140e0320300d040020003603490b0990004401c03520342e002800c80b01108200311418201d042d481014441c240600054480040d06025034410010b12880390700200c00a20b03c80d60152500c5134040350700d034808112400d2009c0031903025082070b04051800b9070000018071101401c0d0200005101e425030f03500340b40a2421669548581880c054142c10040c141c01030310b1403012640644000e041c5548600c0c82c0ca0404c460201501e8080e40c0049074494062800a0311440c080d00c0b41042264241c0c41e0020890181401c019049002e035400300d05003c0c01b072050b42d02007890000a0b1020340903401490502c41c110703100d20841030005901041c42010207050510010388801c0c442 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 752493129 1250 752491879 752491919
    0x5060a05010c0b062710060c121d0a060305060f03070303080a09051c030b0907021f0209060c0d05121003020604060503090a150c0e040905060610020f0d0305090d09 72
    0x40c605a204c2e030300050303a500b0aa07100140200a85060000000d6840a8440c02040003040c000b01301d5a850000344d80302903803d500074041c424914105280e0314002c8045000500361400c4401003500302c800042d205a4032904070341c00080d0b45408101c0c1c5400d121940301c03c1a10100c004080007469a50011701d10309008000d0b01d005522425448100300042103202034410320803040e00802003100100038000c0c000141564498003074a00400d074200d00114207441c1110400d40442ca06c040c900c01000301950101c82e00f20303001002080f402c4090710381170000c0780b420700a640d00c45a40e1584c103a68030900041c050b0204640c1c000c0c600003000183c0d590380c01c48044880d2810119241c2c0d443c2481c16080441080002c0e0541e5880c0000d0030400c0b0a0703030302003540203805494907408007a42206000440781300003c006c0c40ca07409840031540900c8d2480710039102070450320494491504840b08076040080405581c00032948550a1000e00c00040c4100400400c1a19000071420301d09010420103c080101c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 752494379 1250 752493129 752493143
    0x209060901200a21030e0d030c0c291819060b030f16080705030709202106092406120f060103110c1005100302030a06060905060a05010c 60
    0x440d1840d03001142d02c8688105041610399498403401c0c400e1120701c06004500b41544040100c906485c040c0c42020310110606004001d071400252058008010800004060101c1200340300300107a585092060302094800141c1ca2100804c0700318241168003800384c4d450401c0c000c103942d180200018003030784050700c0354805402d43c004c81d0520400501c1c41c940700da03070580608141c2a00c0c3c4200010281d002050000021101990310007555843d0a0300780110b40c0e054210b01c0c0200308a8503030780c00217094101c126812904149840240448560059480314100c90320308000010049200e008a035000e00140d4005042d46045003d007509000b09551032101e2503402c00d003402c1e2a8403800f06581500e120380741c1600c05130405030f0020001c0541214214002030510030300701d01c82045441680d410064040c0101000d400600c104000f4100084c20700b40141c40c16500000966820001c45449500031030000a8240c20820b241d02511402800a8007480e8031800c1000507913408101811210f4120003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 752495629 1250 752494379 752494397
    0x6031008032a01090201091701020c0d02010f050705071509080405030f100c020f1b03160e040b10120b0415020301170f2409010608120405130209060901 67
    0x245110411a0300442068800498202d45a60340510342e40040b00b0103242486241c4007032400242a6021000028001f4102c01010041c0d4180ca421603d01b03440300b1320000d8100b030750007039001c1e10b40b14600000000603034681d00d4403480c0d100c4d01d10645401540c135152640c6400c1064540c440c0c2002d03c2d4201c02826071366003000b002440036020035540500f00c0142522400416900d686a845c2d2001c41c00c5843d075480c05410140f0240000b900c000441206c10143c010840f00c2404071600310000300200d6018001c80c40c0e0085922100200203015020750240d041c50707800c0504186e000d07600020300702743c00b0003800744040c09002e07c5070082d0905030b0340c03110f050f031a950f54078940305103003c245001d40c1c0f44542c008000824559a100c001042c1d901c0c050003224020f18425604c617958203085c420150804020441040034035400032140e55110200d0710001c18034a980d06110b0b0324003d4600044407031020041801e10981c501242d803681c0306c1490300419401c101d5207600090b4240b0915041700d040c0a0580c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 752496879 1250 752495629 752495641
    0x41a010b033105010606050d110307020c010f1b0f120e010212090105130905040b0a050c25050a0503090102190b0a15150507020909010207110f1909060609060f08060603 74
    0x10800041083d0f2010091008541d54140a0000d800a13002415524180190720f0b034040700900c00c0c1d03440b40403258024411501d44400548106c2c8074940b0381002c021780c03171414600b00310080740c00141172881146a50b032115813034105103031802040319003181005641d03401d4415603a40002c43c4030920814180c4139640e40c000c640181c4140c03241c212019070500312000300040c682c115070712091040340140346110b415a00d070344000c0110340045800314901d0b801400400c102100e004140c6c03140c0400081c040300400410303100d46240145018045810b5070000594a80c1941e040c0955210504d00407000c2035010508c1e07441116548000f400c3c0040c4654540f4402560010491000002c0094a004c40442120700100514036401250181d00900000c0041800e004051003212409500000c1041590020b0000c01c01045000754240da444174080c05064051101442c0c0e040c0240321b4144001603082c5072800150054840d035020000f440030952f03140c1d100d242c0111829038415822191a9502d80e150 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 752498129 1250 752496879 752496961
    0x102070b2203050715020706120216050a0f060b10021c0e1201060602010501050d080304060c030e0d0e090112150506150705010209090c04081e070e041a010b03 70
    0x180d103a5898200c0e07100e030010611a01180302c00c25507281038445150900c0e06034050741e4850040c0700e0b420000314105110200c000d002c5d406400d10b00c11006242c4e8600102d62219481e2007445001a900c4808942c8070754200946445110442c3c60242d904185004101d24081e4851103150048080e000070503440b501e0480c442c90b00203002c030030010904c40324281c4201415008180038028200590720f00030001c01d4511780080006c640e103600070755440c42c550707980d51020094600304607101d05041e120031a0414000090000c03401804e02c507500c0c1c82043c2d11080400814007810382c4030b4100102d5071481c0c00d012546c0c4080c081c840280720040031400d52a018003044021500301c0204caa05600400c0903010040190000c00e08203000b120540c01130740b01d1504002c254030581c803504102d503108048440c440503850304c010243c40141e9080c0c0300f020307a54001443c14a0000c440444091007185031480c29104400c0c040c0e030260400c140c2c414158079003a9182c04564440ba507000d900038a4215240fa0680c1003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 752499379 1250 752498129 752498167
    0x120604090c060903120e101101060f08030a0905090c040303082a0309060a0c0807030c05040e090c090901090c050f130e030c07080f0c0613030b0423010b0102070b 71
    0x3100e2201c196a55588400610140c8140821100301c0781c5112040d0010b4800ca5003503046550040c0b16640a290044090351b01416012280d01a5501d80000040d02d5003400d4958004004801c007035070b51069042002018041c0542149200f208510f082c04583d0122009490942c0e0303050038841c07019142c900310700e50611000d61800c1c5503500303190100e03821110301001a502500e0030300210355454842c0051481550064140c00e8002140c80e400240c405100f0703006844050328608040d40303056118200d040b500344c412280300d0501c4c1e210b440402141c0c1005408a54000003120080140011569425810169034410b10744100b14085610841d551014008a556040a9420081c04421806450300d1303404c040c0002d2450700400c071000800303003004100c80c125465584041c0003541151020003c0ca83c02060080c100c2c0b409150002c40060344806187d4059409204442048461860300000740c0100c4001c208050341086501186641c0005542083d00c480440107034a070301c400e501d08005031507 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 752500629 1250 752499379 752499383
    0xf0201050f130302180f0a02090402071b030506180703030507060221070206090d1403131202030702042a0c150c0908070b0f03070302071a0a0b030f06070512060409 72
    0x81c00140c01025081c0b41c040080882c0c3c13080da1203082c003403400601c0d03031503802c4119891001d94800c40d0000310071f0b040030f900a002c5090010f200505000041c1c503080d0280120107003030300403c24200c1090050003000c01850f40c3c889044001184041d0300d80c8003141d11103c5a1000405110020840c102002002c1e0190340c0e09015000302200784410300c031754022980724183c3d554005806041d0104105000109031200c640516460700d04010110300387c21907050744000c00340410041c0c030340103907000034034182c0c552030714146554000c540b00c40c9140100011a0307140710742c0040301e8840c0e02e020140700b1351003986540c85040d0b604050480c1b400b1410010140703070352403c050440c0d51501031580340e066009150b02c0d00b030b15240c07400c59a04585441c076941312441140105101d00d032043c00041e184030300c26002090554424070348000080c0b0758407402d9a54903002d86200d1400d90311038240c2c2499003401c000c070f4146241114004c2c80f882c00c00b03c901400c40e00c9903092402c0c40c0d0a00f140010b000c2c0e00d0740d400c8035510035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 752501879 1250 752500629 752500657
    0x302060c010b0f030c1008101a0301211a310b06060c07170715030f0c03061809050106180b03060709052d0406031b0503070e040f020105 60
    0xc000a40650080c4101e0b582184600c0c0e80004040040c24001240b011949004c0d00040c10069a5442625501d1000744200d48011150001040f8140d0001000022803420210643c0341e5041c07402d2048a00081401118810026015400480d0300c00305024035500c607154000015440e100c02c0d0910b40b076403002c04240401001b60a115030243c50203840a5800e0081403040d207203441d190b0800103284611144103600b80e1000c5c6090003410240341c102d00802802c142182e50496030341030200b00d5424003004042c0030030f0340c880e41002070301c0710350086140c0c2c411585010803416040c800741c041c00302804500100d02c00d540748900c00401509502410260072984c00c0798003480300c01c400e11805000506101ca010f070182c1c03404165242e0140200303109413000180081e030382000341401d142034656402d1104402540390b000a0307160707854030300c10400510700424805845c400c1110103919900150360040c4d0096204034000c000e540b501d20000f070341103030744a030307034810400c6043c0012502c03401824010a854 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 752503129 1250 752501879 752501887
    0x30512180a03080118020c030d02280305010e0115080a151d040201180605040b0711041410060e030705040b04060b0a0305091902061812070801020304050c0d080706050402010306030206 81
    0x415006a0f296040b600740701040344c0700c1c02940d1001c40c183d0155552400c1154818000740410758080c0c0c01800710034003800c40707508508022000c40c1044100104460001c0ba66440c010f0184803900c0d003503a40034040400b1042c00e458000d65000b000700c90010f050302c03020b039940c0e94651841582680a00010f000b008003101d00f082240000041070704040d10224049510311b104140b0154100d0303800d000710748a5032201828030b4a0038400d10000c0e07120120407650600004000056640e651007180c01010000480c1c40342c61516002200603a030700b980100041c4000200d100b0101e0394001000c2003520030a03540415410341d80c40104024182a400a468a50b404149107d410703602d0f81c005845014858100ca100c1c411807025002407075509400650414030401c04000c18507003207428041006c00c081c1030286104030f004c070514240f54a81e0000021a5000020321040c01810004444032010480b200b0902c4403550b690f070480342c441c1e80c0c4000c14158039a400201568081d505c828010b5030003900a0341e031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 752504379 1250 752503129 752503133
    0x4020609040207150606030b0d0b0c040f030f02040c0e10050702240d0b010509181e0114031c08040f0501020c06040303022107091a1612140304030512180a 68
    0x940b0104c07080100b42c14034244c0c0006034036100340102c0c80400405441c10301d42200700d0b01c81a080e058001c007005079a00040000060200700b0311104001540224482d07006e03455244104070a0b1402c0326441020011000584542da0f46c910400c03480d03420260034400e0b44c9202910100b02510104003114408131100d038880c1d609400880b0081c01d03002800101040b01c02c1a14006503014062482c0071a08074004503003c2c03043c03000c0000e6a0f030b0041685102c1c080b20414000410344494402d130485095280740448510311400e00308140e00010340d000c02e60380382c0040d01c40d02c01041041c00a20160001d1012191001404002c9d81100c021182c0300b0305503933140c5043e04001d00a980010703e03070b456104058500c520545145a03403140540d9040d6100900e042c50088505a1844102203281040e0010840310000c0c00f0104101031819200d08844501c500300c031040540442c01c58001d0311001c01c0e007041040002644007040b0f032021440506040e000c0c2d01c0780031000c0392030110070b00c54508503ca0810b00100b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 752505629 1250 752504379 752504393
    0x120f090f0201170106080a0c110a05100e070b09151e040608010e060907200703060b120307080d020703090824150a121707080301050a17030d0504020609040207 70
    0xe0680c001c0e03c40549800005460025119003407281200180b05900400c200c070103603800c4482081264a030a03413440f038076076a90500703000898000b2200d981c42500c2220407a41035000d1a0040d01d01180507050b03480c07400d01f100300b15200e04034004d8454000d40380e94000c00c0105405803000e01021302085030020f11000c42da000782c0d5109004202c0450001070000801d102c0284040307114800c080d26528040d00c030540251041d400c803022521030440d020407510291401042003500650041d000031441c2c01c0745500b0b01404448901c0c211071160803c001c80800306082e072044554070394060400580e40c10b883c0c2000c0765011181c0e080000320380600300d415045004003000e035201241c6806c281004903180d03ca2010492400203820070382090500c80704020a081021800e80210300074083d010721054904000d09240c2c0c418001201d00702e03070103c01408241010380440002d0304114914619011404e21655542d000300205104030640380d50000d01151100403c1d50140702020b0025900c607105441c0c108 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 752506879 1250 752505629 752505653
    0x506040509040f02040905100e15130b04030203270f01030204121e060203010b07050106050a05010c1b090c020a03110c09060607020d05011112100b040e090304031506081e030307120f09 81
    0x929104203132b801d011095050a4146c0a8501e032300b40551059881e0396000f0314280300030015000d600041c05004048104901d688204e81c400011800640c21890704004441002c501e4036030406105000500100c2003800c1d542140642051460031790801e108060401020361038002010640040000560940700c24060b0141520801c000d000c46a201d000740320b00346a280c4070301130010b2a028520300202d0140d1710110084a020305961501c951219610800e9428802904006900c411030752018990310000300c654544031240a40309620f04000054030204020b0669031086100140c603008555548030a02107d40d80603000384101203c1c60700e240341c0c07504500b1441c0c25070810324000400e0409201e4490050f1001220a14146414084802e10740b0700010500959032204100100101e07980b141306000300d04034013a000c1641c6003802422400c000b2540049160302030448030401507101d021083da540042c09244c041070020910206d0f0003d000030840391f05030395160007a0360060100408400c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 752508129 1250 752506879 752506901
    0x204090c0306200318010b10050a020d090f0603020a0e0918070617152206090c080423010b190e0906041a1b0d0c03060506040509040f0204090510 64
    0x200f1190100c140701ca603c071911680e108081000400000d0710b8401444d01402160110340000100c442924005c44d904c400c0908032007010132008645940e0a55041051300c0802b801c5150108640e40b5201d50030101106a00806084c1500480c0c400000b038031841d058103003040700030034408043c1054901687d80c010032583c0c0e10b000c1d008030000452840c0c080d1402807810082c0c0c0b0401140f5a03a20a4003051076080c0900c110390001203545122105c0055621441c4081919200080c41603e01506002114004e05c581360510504100300404a4090201e80390f40b442d404401180391080d45181d107005008600e2200d90142a400e004d056800c034a202ca14161a200d01400c800c07919001099552048100c40c0203110200e241c043d001c2e4800c041203929049000039905c2c00e0840301c400900e5010b60400c0c1191048280d0701c00002d602207a140c0035440c01060141e550510b0300d0b09010116580c0322000b8405014030800c90840811500c5640c0280050307600300341650202e011410105001c4d08941c00e00c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 752509379 1250 752508129 752508131
    0xf350105010306150905060d06030507060e180f0402040f11130512010501180207050705040c0c0b060f0102121806040b04090506010e0d121103031006020f010c08180a0204090c0306 79
    0x106032100100c4a10741e100e04661079288240c1c1c5007100300491f81d4010740d0f07203080990319079000200181c400c02c0b00b0000b0f0306003600c400b50110b190100f404520110007200459440321b032802d00050b41202c0d00d1054006030191804200800c20040000140003440c40c0c0900c20700002443d59990744809102c80d003502c1046608400010700170169900741c8034280601500150a403c40c0310419140b640140007481c450740a8890b01982e40e0001003c0700c4c20066008082030f607502e000402c100701d05004c00d1b442103045511700c0703d400094000035030b500080700b0082c201240018090071507140d07514840501980007050603035910f4444c09460296007061103003800e01e5052230b001c00e040e58001d869085c41d410b40988160422016501e401b200a11358466040c1403003041c1ca030308480c0050500085101c0c0002030f644514041c500a4024a084490012400164501060380c092030717078050010b603007252800c00310700c4502c041105030305d052640340c0300001e50191070020040d0410010f000040d0403a8041e0324 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 752510629 1250 752509379 752509391
    0x280c02131d070e0108070e06100e04060f090b01030903200a2111030a0e0621040c1a0c0c040b0112021201060906030c0e0910050904110f01050a0f3501050103 69
    0x10056546900e47e00a80313416092180020340a4200b4046e50b80b1048040e140015041b2504404203044a10039040452110008201800250454041c0301d101a0b0280707400c005e07500c0c0e103803801420802040426000d0f030412012010801d0420881e0030f026540082890b051142020041140039100035451000320708420070b10380801c0004800c3e03409201007910340100300c107000030170407419610502908500c101002c03400d6901c50840072040c0c1c882c510894a802149080089040c0310306c15018110300452000c1040c518441408a40052001401d0702e0104180c02800010b0715042d086882c1084451300c0400c11481840d00c2c0301c0a54100c42c05912400405a180e0f14110243c4030010308e03140c0860400f64a0341007601b80000801c0e407202c0c520202c00c00ca03030b4940000a0201d8000d50341542c05925003000c2d00c480e4500b140d5001c40103102401d245203010400140604041500380c4070106000300d800e003031140c101c442d14941000240103000165228681c0a143c0b06003402070081c103001a1a00c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 752511879 1250 752510629 752510639
    0x105071b0308010e0406020f0703020106140a120609020d1202240c18011e0c020a09090c0b031b193504050309030303010b280c02131d070e01 62
    0x6006204116010750703800340d2603824040c00303042c07844c0c01600468080e5800c016001881c0d62070030103000c0c0c07288240d00102c0d06a00d08008001042e084c6101c40b03103d0402d140040103d00441c0d030910190715404600491500800e000203540b00340700aa0103842400c011f10f40c0320400381d001c1480700403044c0e500c040750420071484aa0f401c10241c110390050180c68100013a040803201141c400c10704080c145002e40190410002c107604a0300800ca80c580840c00b0036200d2011850f01c03001e84000381c00410404c10080c0072644413405032440c64414030000e50310004c0841e00005030240d0b0b80c03c0071080603620f1992803810003c0301c0d203c4190750340410f00140e6480308404200ca02d15859520070144900240680004c3c1030f18002d20b2040644211294801080f00c240c03542c6003440034500800680c2905515680c090a81024012401044d440581a0044019091a04016501c028940554540ea024010009400d00402095040a0034010b1030402e40700c4450002a10000340d408641ea0150030f41d81e10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 752513129 1250 752511879 752511917
    0x50c01050c0a0c0807060905120d0e0a030215040515013b011a120a0c1e05030a020706020702031c140309060f060a0e0f07031a010914030a0212010507 66
    0x30481c2e000040c24840c03505000c40d03240c03000b030305005001d4030000a0841030380d40c880e4941000c1100010408030040b40c03c01c00c0403c11b10a020300d6803101405045c6c0300340180e4000392182445c0d24190100b00b9100042000c1c00f030104180810381ca8031480d10741155845030341c44100000d2210800c50900350050f031720618540030315184c4030700d0303242032040340305036401d06400501d106400d01006040c0c03441403284681100203d1510f13170090704107a000003442161103000615000310300d02000300b0055009402044103500004513903016010f4440140c6901c0c0070310f0648003034070802c080a5031500c02c59410b40d2148988a0600c44c140c01c09031942980030100c1c0700707410300c40d001c22141040507401c0700c0c1c0043c2084101d5440198004801003146074403c1c0c5844468070100c5051301c11094610001c82080441c941602c91075045e00550000c491000301c4d0140024a84050360040740025549420300040d162010040e400700310b07500422414200007200c00130350081c01d0846940d000a803400403c2e460135204 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 752514379 1250 752513129 752513137
    0x1120c0b07030c020405070c061d010b0a0e07030b010302070501020a020d0206130b180f070f180203010819020310020d05040b0112030507112b050d02060108100b1f050c01050c 77
    0x3060f00d503803055180300d4082000428009100006000031100d1200000c0d41c7e44c40703048070360aaa145090080c2c50000300d00381c03c441802c038495003d11820801030040008050b550781c0d22500034640420b6005d03083c03004030041d0254081c0100a90b00110707000d006640c0100e942c50b01c882c0c19500b02e500b1617440c608040000d14621a004d024140c0340000704544d20b128801d003040746c03a46201141e801300040b5001350320f881616480b689684ac0000d00620000c1424003044c04817140b20f030015800c550400c2d03102c940795002d008040c801380d28031001810031510144011400801101411902d0b03402410000340136107400c80301140c01607801e03000402c08010b90303105143d0564260f60307458100049581e07001d80e2500316213510b84c1d101820150780b0080c0c542e00b1540c41c025004280208058145514250703142c000c02c4030001c020f542103900107004681001a44080110103958045280781c00007005c00c4000c00b2b0008240903400501246140107a04080203045a10441008010640d09d8000d19456801 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 752515629 1250 752514379 752514383
    0xb03070f02070f14062206030c0302090a150e0301020307021e0a0c0b0a0324050306070201062714010807080d030908070f110a15031d0a03081b0301120c0b07 69
    0xa800341481004448410502030f200082c01481c50032040780c80002d469042c501c0d200e6001d01b00302a040c8043d6625011b4054a0201400d0940c24101240001260415207001e10134041c3c0b0314403880c50301d043c894618004c4807a4050002c6550742005140203488400d02040c0f10710100c0b1200407809480320014000c50b8854014081407906810440e0081081c0e10102e02c4038105500d42980f01011131a03079114991115110383c3d210380903881c05c4141810480700500600c2964945441045480c16103200c2540c4052200e000114040140d2040401089d05a007003181d1240402c0011501402c00101c41055640755000c54503415141d041c110b00390744120100604524080c40014002441c19003c0c018142c400e08016078000c0c040e0000c95500c40c00742d0f00040011981d02d00e030b4400300342c06118144000300c40188004c882403040c03010a50b501e100c407100a08001c1c200000030886034401c1c80314000380c0c8810802c80d5803560348032604504400e03801c0c1b0070f9078100030703004000900300340e02401c070703a5916 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 752516879 1250 752515629 752515649
    0xe0f1c060506190909021305060d0204020c12030103060509061b041517090a0606320604030f0803091002091f030e1e06070201060501080c0a0e09010b03070f0207 71
    0x140040d0340d404050325002d001e458100500001d0610108201c0c1000c1000e40282c40d4002201c05d071a004020404c109403818001c3c032845c290a01240780c6800507910704464050b40c0c05aa00ca845032004c610300002a04508a00310010001204100c1950042030090040900f00c074007945071b0135088103441806141d04401054200400c000c1050074a0f281000c001a9040841c2400c940340e030000c008000171195101180c0242c3c1c011010002e103441000d02a10305060441e5000881c951148400309840a80141034500d50402c1c00184da5000c044601540c0c0c040312070f910003002450322090b00d030425540c00c1954080c2031403903a5040c4181c8255203800c5c4005100001c1d148030310750450350081c0c25428103010141c8032590400210000c02482241201c40e80314040c01054824205080c075801922000459040007010802d0760f9020a100d50072904504041e59192006101650740800503110590045d00440000901c00741d0140503620030400d9495005140380c08080c101d84507050380c05000454 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 752517985 1106 752516879 752516929
    0x6080720150115021218040c0207140301050f0601050d0e030a020714090106020a1415010308030402040c0309170f0d06030c0503070b04030c0509090109060c0e0f 71
    0x1450701e089446491544040c0c000e407500400c522092500002040129036a0681360600704c6c510f00080003044480e0200302c019454400500c07801c0081034808820300d8117400c040c001d0a100380300000380b03d0a295078083c01542d0350340026404031483c5580302c41882000740108000c103d1000a030300242807007172504110130701020350a02820302071842000104580b603000200c0d110711544c0030a08100f00580300340c1191410054170100410200f42000000a2140800c01580903e009076004c1c0300982c2d20800a9080d5006072800403d840180d091001e0840401c5000c2c200c1d1841001c2c5461500c6580342c01e000540c3c015801c10348905041c05401c00c120300d001c1080100600309072030403d08088c42e68494580b511036900ca4a070082c03411a0004450b0380081d44210000740e40054100043c52036030341d005200c24007244525000d950140f04022941c5444150300000c40c42d043d0031300d088 = true := by decide +kernel

theorem cover : BRFrame.Cov 752338129 752517985 := by
  have h0 := BRFrame.cov_init 752338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 752338129 ≤ n) (h2 : n < 752517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
