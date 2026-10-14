-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2463
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:47:27.679882+00:00
-- url     : https://prove2.me/submissions/9ef50c90-759f-40a8-8208-b9eac0fb88d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 442805755 ≤ n < 442985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 442807005 1250 442805755 442805761
    0x31713080315041d010c0203041d0a060e181b01140f040b07060b18060604090e011103090109030908071a0a020f01060906050f0a0f03061515050706060e 67
    0x44500112205140c1000400780c03aa41d50624800030070505100710b60300700781448504ca95030001c60b44000c1200c071203140241314101508000303d980303018a1080c0d41040c0a820005800b03002001c1c2d2564001079030b10008294151646108048110207544040102c04401c07100c2007071090a05c44c1090b080981c8080d0a100e154410000300104820300382c100309450005103410241b40c5510465005101d840c507070300d40711589805c0000050ae0748000e01d901501891920f10fa8411711104160310074007004040c1c50900c0d0a001c8424000d08003400911100e641c0d034030f00742e0102c410103c091480740e81c020740042881c0c042454001c0548810b9408003140b9800840d084c400c01200703c40500c420310000c452180c940b48040310032880c012500001c945203510703016020070360f0704060f001041030311425161107881c00031000a000000c4284d12a03010307226803540701880055460740100d5058907040e01020f01040c0c4519421440702c92341914031021420000308002084400e0082c80002c10307a18030240d119207 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 442808255 1250 442807005 442807021
    0x201021608091518190e0403030c03050106020120031302120309180702070603110427180f1112030409050a0b040b09061002160e0a060b040b0418020d0c0c0317 70
    0x2004500c810f01c100c41745d410741c050b22040d00c8a04401440c00d46403501e030707600b440d040240082503000404400a0304040001c6070030b80c01405007103840c860304050309003c1205e05101e200d554001518060001c0402804070000d0b07603507040500203190000000d1030b0b035503269000300034001e07401030240e101c1040701008000c1c00b190086800c2e03046680320b00f00450326526100048460380318136004644016988180008000100c4080c6c0c0c1e8180d04040e801c0200102c0710440140b91100171030028056101c82419500082c040e400d14900054080d0810001000050b511030450f0410307006a4400f5580380308120004000b8043d8070030345003003a603003041684013070004210000d500610a43c01401c083c03040e02c04840c400c2103000e4080e8112030324028101c1c1c0b202c00c5140c05560542d802d03070080c0d0400c0c03408107840020038100c4003103440542003e4501441c2c1003540010740751b442e2628001646c2401715064101290160903214105607441d400035955515018100300c1d80030703502c0612220004200031900c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 442809505 1250 442808255 442808287
    0x10603031119031205060103180305120105091314100c0804110f0a03110f0901091401090e0c12010e0607030617160501140705070f081005090c0f0102010216080915 72
    0x804c1262011841d5542e0350700603409010190308110010401c0c4080800f410b910502820302c0070504498440581d0741d41041203880030041e030340700c485440b4000c04040080e14050a2942c10301130a0140c2d0f03025080c07441c403141120708a80b88600030941403400c0000b0060000141c1c686000d0460700724000e481341d40c3c003084100080e40001000e002100903211155a6007851280340764800030442c452641c0c41d00744d8040601140520901031141c12400400c80758510301403904004215401020031545010404c54403001c8401141415581c1d400c10f641000410300005105046580740482c40303500d89001203030305010301d83d420f2001e508a0030380051103404440d10b00b412a042403a01031181030031000120750910410000400c10301ca042d1000441c407840c607074140e080f214150241c0700e04a00901048060b564101c07000030858000b546e405074586081604088804411700c0010b0804600001702c000420f01e885c41500d60801c081035001c454076007803401c801d0070311007180c049081c054800004010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 442810755 1250 442809505 442809527
    0x609030c060c0718090c061b14010605040b060304050a0b0c040e0103060c0f03140c030a06050d21020d09030b07030f05070c232d03030711010501050a080c0d03050c01060303111903 79
    0x800908031410203441450362362050034170b60000d80601ca1750000c800f82c0ca0003000c1c00d20400f4080c500380f6559a91528060044e40e00c120b80000143c4180030f965036910031004001040001c1c1180b061101244880030300b0303a8280a14852000000d545d1a40d80000c0c10152596902e2000c05040404d00e006140400b401e40d40c002e00104800f030b840b6111280301c2c0c40a442d46030003082d0008000c04d82e032020b00c0280c468034203240c100c2c05108031f102051108103d031990340944403440803a485260030400514a140d035554008207510f40028248070109110703080e43d00c140c4500b4001074413001c154003840f04a41590320640755864846030011400908580c45401c0070f0b030f00144a0b03219a82202805580c0403802140c0001c0c0c0d0141ca82d645070042025000d00801e42694440358a4540045100d08100c1c8a40c41a103c001c0c006000002c507403400c102625010500031000c01030b0501040c1d05084007400b07034401840c840e44922002844403608246800078100399100f005444800e81e8010a0704180c1c3c0f601 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 442812005 1250 442810755 442810757
    0x60304030f08060102010b030115150e090c07051f1a0301020301080705041a04090804061403060a050d0f12020a031713030f02030705161d010501020303060609030c060c0718090c06 79
    0x1019510f00340180d00600710000890b4255082140c80e0483d541080d6401c8151512020110300d0910215800c54000401c20703070175074001c80c0c95404110180d0b22100602051403003401141c001044c408214800d03d01c0c0b0701c0c00e9105d03264035030341c1482e20298140100b00001d0402c1d030007182103600d00f000030395030b032580d80c40380030300842d951814020f402180c0c1c1c1a003092440040c00034400180d8038075046d00c55070300502c50040098820f01c2c40e04e1104102c441180c1c0202001440000d080d0300300400c2121741c89948000300c4079914003100c140c0c0010ba01d00c404d658112415000361240d11128200a440c90540c4a08400c1c03103c040c0003000007201d070060080c84017a03027610382101355000440c4140c0c80c0d44130b90380c1c01070100e00c140401000405081c203440303c152071241c0070010001c881d45003142c0505d0700070f005175400360f0400d00c0050b059040820242090f65002822205181ca10b08049181e56000c95520145900000700610030501e812224400f2000c11817402c002036035089d210703040700b5802401548 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 442813255 1250 442812005 442812017
    0xf0706030c0c06060f06020601081516120f020c010e06010f032a1202130b240906040e160c0b0708100b030907060e030d080c030c190206060f060304030f 67
    0x440450302c80c2c0c0101d81c04541c000780070454540c444561004c2c0348068451b00b8010700c50b550000c210394001045550b09075070034008407112174840412000003900d000000f18100003214030071b4050f214042c001d0309407a22031200b0069590844045031400e443c0c03561100f00895002000420421860100000460340c0111450500170b15219001010100b03d22206e4800e808282c00843d4204180d1590076a2901c2220540c407501c022142d14800d5030100304069501c10403146201982a01c01030aa030f100342101e55055140010240c002031450f0000d401404540f41020f042100200041c44005151103841c01c00d0740780050300d59513440c4280001401d000812071034a02203807015000d415208003800d01c50030b0f05038482c40c11000c00d07942d8407401d00c903040010705080040001400d02150307002c90030305166101248dd40d50030208640c9580050070700b01410b6020004003010200e9038031f1403403503078907030b0b501901680c02c1070002c01615031071105085105038800c00900c000680c0040b900e1032403008a003060 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 442814505 1250 442813255 442813271
    0x109060506040f180b1801081903050d0902010504120c1e03150905030405090405030d0606031107030302090a03020316080601060f080f1b0f0a0909050108120d0f110414030f070603 79
    0x82014004803001c0c15000700c904038030010002c1c0c504001ca4182c88e07844040701e40c030341104a1403468081d11b1200c0034001c180c0c104184d1540302c4598104205540c01070614030300c0d0a40e40c00d400c0b108920030f6242661403425102c0c0c1807142602d414100820245606002e1012238199120030b0b181c4072240c0203550049554140e407501308001070050390001c2100801c1140907240904042e40c03661300c4a02250025440c107900826024040c1c0314003d0306290141d403039800c0c081c040d0b80030750003580503c414550001d070003000000140d90410132550201350001d1903254070b030b01d4184810b26091040e046502800030a501c1d80030300316840301169500410001c594115602c030340d142c4a43c1c02c8030801c1582604000001d0300e4940c0349111004015507401f540d91525203650b40c181d05000c5400c00c0c0114005600001071b964850500e00300a030400385240100011009a40c03143c0c00704035106e03000c0e05540b000d000b1400708000c21270700e241c1001c503a8050b00900804011520441d0700c0307002c140251800d0655580c50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 442815755 1250 442814505 442814549
    0x40e01120c1214010603060902040b090708060f040e070902090a0801050912070f0203060f060f12030405091902042301031e11040b0c03030411030f03070818180109060506040f 77
    0xf5034490010030b4020004180c890030080c004c0c00d4905000ea000354104440314400342006544075100d01001da40f031503500c2d02ca1600304641507a02c1464658440d80380c03403501d0045041800440010000000010303592001c510a20046a000364400d00240e49084100305203d0303400309171083d0303003406100d08507500c22580c03501d043c00190760400650544600001c1040d00c400f8a221240286001c490300c0450070845c104005403415000945462a082440108028282070b903401c1c2c5c110061440c0b56400c46041c54400041ba00180d00c07200e10700704440c101d42103500c01d0703540305007585401b860705002800941c209480c58014160444100d0b13617407100c41484142d0440250360150500700c0000b682c4035030708a021562500262802c0e00c5010110744554400d24002a8082400d42e07504061820700c001501c0d03e0121703411601500c0720003400340003c0d980d55a25451280c1d000000310324401c045504103040308040b0713030341c030b411180c050f10382000140860f42c01011b011007120003140c141014040c6030b0311 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 442817005 1250 442815755 442815773
    0x6050f1207060e0a0b070f0314181e030d020c2d190f09050901060605162d0f0b0a0b03031806090a1d0703020f070b06010c0507080102040e01120c12 65
    0x842502401e00101b1400208043d079500400418003c0e0390340e186481300d04281031094860380245801d500b031f004840c44c0d8541464650419aa40d01d003031800b854000410110741402111168500182c2240d144d03280d1500e4002d803e25003013400680d603403600a00404032034102c0c500e12000540701d0b0040c22000d101d03c4218100c1e00e0301410520340711184076039403540040081d01d401d441115079035081c5030b00400d6a920440a46445d060710201c0c42c0e00d00c0c071560300c0f4003041c100c8421803092188017040300c0d0007000b808402c0200030b10340f00c0c2181c04031003140303401c100300c1401c0003426207000d0341d082122944242d82e00006950700e0641d004982020352840e0400200c00e4483c0f00e080c00e401070110800012240150001c40ca890f078085000402240c0c0d91000c101d08a1240400703100300c040c400e1042c40041644200a44c4e4000c4060504100d401803d07101d1074030300651544410308603900001c05014202000e40d2050040007154603030a5401c01541c0c403c00301448500070594900650b150307250078040060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 442818255 1250 442817005 442817009
    0x501140115080a110c03130506070507120f0215030420130c031d0102040305070605070f080a030f09080c010c081e07050f04090b040506060c0d080c070203070906050f1207060e0a 78
    0x16001d10745c0c441d821503005449402c0740c01300c8500c0c0d0b541904000351604101040301c81055018000c2c040890501e001c2151056072260107640300070f41c60114900584580140c0e80c4401d042c1c1d040c10b62240750518000c074001d00051030741c030f03910b1982c42d80b80c11948d01e43c010000301c0d4200c0c4090102d1400e1404000324001c00340140e0ba41d8442100c030303080d045a81c070190f0042c01a00d0243d02a502e0386070b00c03044103641034441c48500901c3c04914014803404a208500604103203d9546400308101c0b61514801d03095400c0c11030700352844007002813800380300b410034840c501401c070490500007180c1c60304028400300410140740c20403260000c080010f01c0b141c810310840e0a00112400c00c070ba1500e0300e56451800800f044800c8502491800c404101640b408406a5001504800c014500040301640c107c40d0000003801003007105006201100060b981808214060100f010700042c005290a00b04035081c0c4160040a0040d4200b50340c500d444140400c584007514007504001d00841c000c0008903402a07040d03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 442819505 1250 442818255 442818281
    0x50c090904020918060112030f170115030608060a0e161206090501150b0c06010e252303060a06031118010509060d1d030430080406020a0501140115080a 67
    0x1d40d00218980b01318495040b20603010360703650010071081890545802b128a0112424480081c1c010484040b0105030400b001209290102d4100d5a91050794a0b00d02e05030340850b00e10391200686d51081d00300f00640e06011044041020707089190000c204c4940144423000392015880c0c00b10782c0d061100940010b94a0521115500340941d9101d50000c8160040503884010f40500d40000521403100301c4421b001c0c108640c2c10b03c481250800d5201c400d191011028028490302c40c503000101c2e0f03451545c106105181ea04002c0c0e0702d01d04141007005688440c1c2018061500c0e05c4005214618131100b035a01464001903250421980a001a1000d000d507204495002c440000c40120145807600002130740f27000610a0350241400e01d014949034043ca024100e1000e01c2a407480c25402d25610101810700074940707140d000b4404545a80c0f2941d0301a4226001603882881c0d940d0400c07009124545400804a40301c0312903505180002c506010a07031030043c00c1010110129130100b00382c1e0701c001460307650 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 442820755 1250 442819505 442819513
    0x70203010216030804141c0c060e01150608010b070b130510020304080a02010506240912150403140f0307031d01050a0e0c0603100b220315050c090904020918 69
    0x240b5005101c40d208403011140200110180d21880100180c4401400242c0074121f12110b41403008560f2289016016614140c94111f00f0810074003e200703015002d000304100c0c24103903003026030160040c1c1040e070240301e03054010800400030800099074960085213003e54200311903114107045250588140c3c100c03d00c240300000f0b1104200c0400020b1216060741e8009110903030b2840d04215503102c1418508001802c0c2e401c0e58203803080e200c0000c0000f17043c01000302580c0c140c407261051800c050915601d0441c40e00809100c241074210381000700c6d1404862860340341800e0900032550900015000c2d80505487e41600c1e818540c520b03c03003840742c0c040e01c00200801c5ca00480507001500110500c0c0006010301e5040842504008045a10626034504884200c9107800031601d0709a10007003040c01d441c1100c4801103d901001c80c0e00000446c02507030301003901a2921040f83c11200043d14400c00080100940319068a5402d1415030060b01280d10032025a60040307a585914000d46810741140a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 442822005 1250 442820755 442820797
    0xa020f0d0806041b080a02031e040f03030510140402070204061d010e090c0603040212030c030a171302030c01030f060f0303170603060601020601030b270c181306020702030102 77
    0x10340128207074070502084038140b008882e840c0340c00d0700d00492042e5500c005040100080d11800181e0021a040410101c110702181036400c19025410800d45045641801c0c515001040c5030b85401102c2d041440c5c0e11040106905c2e02407400280351811012038021070b00410701c10300303541c1d8a9200c000100444101140c0c2d110310240c0b0103140180900072651404181008038985180c00543e0b45102040a400c0390714540b9a9005c0050107001491052114401044041c86e1460240098034180c80c45032144561040824451740700d6001c0100505070303070b4000c44480030151380c00043c0c03980b10890a0900188a41c040c0c0d900b1409404160440c0c4440e0744050400001c056000001c090304501041e08011144c41c0d0004064035100250303900c600583c4582c0040c400704010206c01038010b05034001036a0614020014401c451240030b00950b2280c11445495446060038039151f007210380381c1c04140180c3c0c50400300a0b043d060700800301030011580402c0c071804548095040703403024210161040300c911 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 442823255 1250 442822005 442822007
    0x91104050a032f180603010f0213060e0108070f0503131b08060a02070b192405100212042304060905060117010302011b03030209151b070503030d020a020f0d 69
    0x200d10b6080d0595185451005080c183c0460815412045001070000840301c22981c65040415030180446a055590300c0e8071501c440c0391480201a5104800c4500000c0c525150007c0d04890302001243c1c18001000e04003c0c2460303211001070b0b130b256001e051035500d9450300d24003070b200003101e9a0000d0030250503451480300b1840c039819000c1103c0c406011124070741d58407540402a801280d2000b81619200800f0501c903000040c1158031441c8060400030302ca41407034190120a0f00110407141206409107410301441c10402c4c0c1c21040c68059000600b201c5200e41e200302c250f4443d81c800d0954078601d8480000f010307000803043c40d10a0784028001c2c80120303101c0c3c1b0340c1401018240c8016000c11100e50030780c010240303405059412030743c05840c0e001070400054400d013040900e07240214101a03080040c0c10003540c94800b080300d1114103030001901c480743c14100c0703898030000a65880b0164403900d410086541c0000840f40040704003000503031100418141030740f600c000c20003400090701030040e012020b9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 442824505 1250 442823255 442823273
    0x140109050123030304060c03170109020306040b030a0c1a2115030d2f060709081006030c030f3f08040308040f15060b120907060801091104050a03 64
    0x103180d0100b486110559403440c042c290400054400f03030150011300c406c1042c03a019104042400f4040d04001d0303010307142c84c904556240f100740c000034240c43e404410f0104034142440b85081400099008100100080d00c0782e16148d00c0611505112941d5100820206032400e02a10115455011170b200c0220300c1d50015440c0038070031076600401705030b41c1802980300d2a0004004003485001e841c0c500304c00480305d015074852400c940803070803102e12444031074507104020400e1740d201d0b00d10382d0380d901102800d0040b41070500c2070f50189507881c0303828081c0902c00302e0794180d100c0003141e81c8101400d02503251460130f038240340d5503c440445440c1c102001200e0101c0180c034071010b6005450400c004082d90340800365400501944c001c6c0008285d0400100098030304a00310101d20300070508880c0603110141b400e002d50302c0030780042c030388a400401d241c0341d580f42070044140c00078036010103400568101100103000c01e9051050320203c0c0c0e196544041c54107099801c0380c01809001c1c0051b4062500c90405880c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 442825755 1250 442824505 442824509
    0x100b0a050c0c010806012003130608040c0b0414040b0d06021306090603060e06010315030204110a091410081008060708040b09010608070501030f060f090917030606030c0d1401090501 80
    0x80c01001441801503204e1580d041c07191038141c54403400c180e000415044145400d10349010700d44004c006290b0031481c24003030000101640c0d03642d03111501c0d00c0d20300a4514070495000e500200000e00091010120705004d4060030803054500084072072800d00011500d82840ca40034014510000340e200320840001600c00c141c4801d51100703e00345555020031401c079505845180d140007503074804510b0035032003904640000781060300201c1c10345480f0740000d003c40b5407189040802c20000140c0900f00c641042c140401040d031103a013680d0203800400414034401c803050b030100800c56290b0002c0c10840c0c050001c84c0c042c0802c001100c1ca20b10f0090700107490340c0d80c01c0e28240d0b0131009140c00151010814020001980c0144020b00122880c0400540103800c24031034128640307440300f80c00f00380c00c40c8200b2694000d146003040400e06030420b007004003800f081e80d038002d0b072011420020000b450322560202ea8100c102c0545050790313030f800400305000604c400c0c1d400096210640b00001007000c400d030081d40c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 442827005 1250 442825755 442825777
    0xe031b120721120e1305060d061d0706090e0c031e010e0411030c030c1009090513060c051201060507020f030f0d030c0903020a23060301030615050402040b03040b100b0a05 75
    0x1140443d4005032502180e4448569100220012075031100b0304a404c01034128001a0401003280d8903603440005483d202440ea081e4141420000d8800c00003c10402006001d0b40c1800d100840c20400515140900280003031400c400000109038803460700c2c0050325004c0341100d000070040d42c55452020b00031105031800d8410002c90106403651345008200c07c1000c041c001c0081000c1d04100060141240d504ca503544140315002c1000140c14086020307048c8203100007032495a9003407181c5049801c84100340c006104004040c004036aa00400c0f40205064603001d042082c0c0f14082d62002074921069120116014010a0740d03158a5140004021200c10404c2c1c4003403003400950780c0704503410240c0d0312001c1d41c001c2c42c03024200300d40a084070310410032081e1075044c3ca2803040b00b81d011841036803003a4011640d035030340c41c40000c440c5c00c00340798174401904048130103519192400c01403921901020f84082c0181d0480408610820600c29480f4000e00551580c82d40300e01142c0c00140039500807041c0c0d10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 442828255 1250 442827005 442827023
    0x120703080a02042619050a0b010602030f0f090f04020a0818030c1504080d050115022505040c02010f0f0902040b0303040308070f050a0c03060501060e031b120721 71
    0x228031030300e0750080c1c9041d03030104ca04040207403105940c030b42c2c800d8070342c000032241c0380c0240104030709848161101c260010740a50014183d01045103410b0359800300503031111003103410920070f0040d880350050032106a011200030141d00c2e0003e40b0005030807a00d444d1041035110740f00107500060300350010304c000d11900c41002d00c140a2014102c3e43c580f60300c20612030039a643c001202c00c01942c000d09000a400c540580300705c0d400c0407002c1c00d6072001c07644282c10803400704294080360308100e54108044000045000d011100140e02100c03586a83e14050060500c0f40d501c64030820030152003548401c03804581c1040520400e25468401c4008104440d0281d004504103c001e240394100081240d04403940280340500e40b400a40f90184103c039041c030210740d54080c1850f0b02000c00c14441044024501643c000541c65251150160110400c51100350281c0c002655121038900c1d0502e00f6220342c101074543c000038000c464585030074400c0d607030000507070004400c045042d103034a14602001494481c030503003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 442829505 1250 442828255 442828261
    0x6091905041203050a11041e08031b0f0c011416061104090b010203030c0a030e0a05010e0d0e0d030e01140f04120c050904260f0c0109030822080a1112070308 69
    0x2d0415a0004c1b08a2648504100300030488203061100490b082c900411054150303540301c600c154210342c41004007806d10440d202203494480e0081c00f0351061006020000d03c200200382002800900d4225045050110080382e11240c50051510050840f541722104014809070794480d81c0e100d8103e40501000586400c1d908501540004100e038001c198408803281020414003045020b080c034070711407031028010724081313500040c0e09008001710503100038050481014800790041400c0c1d50310021f1841401210020740c0425004038421904400c06c2c038100c2c424a101c22103244440c40b402c00241c070a02030024000030b548449a40524445208103043c0c82050364440c1001401007040d6000340058800070b649071540f0388507102202c45450a01c1c925801c0c40800d003643c0c07602c0d40200d03a0b40d4100743d44602c618401c160b400703114241e0000101c040c084241906000039010743c1e601020081c140000020060300d014080ca2100d0194170a00044489084030180d0b40240741c2c00c400c0084020800841c04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 442830755 1250 442829505 442829521
    0x8070504060602190201020a14010603060506060a0c03030f021306170702210d0603120503160906021203150607080403060f06120605040f0b0a02040807120305030609190504120305 79
    0x410003281c140da030041c0b107900d2600185600d00300b204d80c4120306501c60403406500280d044084005140040000002c80c50b1544c00c0080c00c0d107d0060455100d50720804c440344025800048200c14681c2511b00002c0ba1415114004028400e40450581c6200c5180001030f500b83e20400301d40382c054074a108248242c50301d01043e60368858181700c03040481e1002d43c807062a003082101415a00c4021a0089625580c9440301203184e4210b980030780002d403001040203008807405180c1500341c00035190a0040d00e103480f10003501d80c4136001208161140c00808981c4000e004042098000c00c0184a2541c2d40c841e4504101c50344c9c400d1104540c0785007080c00f010350503c0a4499041113481d80c0b034210003104802d66403a030041c00010011120709547d521614040b5001c48026031040c1315445c0300581e510b04080c0100d241078425404500c125007402da0703c40010340e00800307803030b002242601c4100c000c0e1240c01e14401d80b400401480c3d000d042c60102000184040e140700c03a00042101d4038104515210318070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 442832005 1250 442830755 442830761
    0x402240a0e0f0d020909030d18200120010b060406030c09060c0206030601030f02120106031523061308030d020706060b190e040b13020304050721030804110d03020708070504 76
    0x304483e07000240840c06005424a0000c20b80d20500355010f0f80d00e800212810030040303560a45900b00c00c4c0c1c160000600c00c0140d52284403800c60800100d81e006400baa100003440c020754205582080c01000000203c00301c2c00b50050a02c3d03560040c111900c5a8444c80c2c01002441641004c0c80000c084e1030002608a0143e0851620690064000c5140d69035050041d07016002c1281c0507135202d9800c1010503c1c5000c1860000d01801b1241da01043ca80c6c10300582003035100384c6822110415604c150041103002c46001080404072043e82d40c1034803036500c8110680c601a460707101081c0c9000c0090800d645114542c014820503100e47d20070002c041e00d60050851900410102c00c1d0b51600101108421a0152000d007150b0a4020400300e101d44055010854013440304102c06042c039008014001002428000c25014104106508001c1424001080115241c8620141c140303c03051010805111950a90040303920015007017026a4480d464025610300c804c0c403034008140620440400c99280ca80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 442833255 1250 442832005 442832029
    0x9080d0f1424011106040b0f1e0126061f0b030c030a410105040506010f03090204060e090a020405090d0f1b291e0f0402240a0e 56
    0x10b14640c4144100c80c111400d6003110110760b060010303d01c0300c0c010780c0e10100840c1c1d109078440c084000d010309244031750224091000d41a1850380c83d0030483e0039000c40583c41d100d0304540504094210914640d84020b03641014106038161034007a510411074610001700d05006c40e24990910b5041c000c0d529500400d00b40030549110a03150300820110300080280e03000440c0c1d030141e41001c0d0002070300404001c010450108085150b800d8440c40b1401d00c82039103180303140100010354041c400c5150900000700041240240c0c0300600d6034a007008002d544035039100c0d001400074001144080e0405d807400755560810404100d1045060100140e4202070224081c083c03505951103150208895500c10380306482c0712101480418081000d000120320b501061000130501d1040082c0c0341000130300c0d240d009801c020100014010440402c500c48005660026401500441844440d407964800a0910362411044001020020022a480424100040842020a0f100c84502441c90400d1145007083c007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 442834505 1250 442833255 442833271
    0x14160812070201110705060a02101d03030c0307050d05040804153b0d060501080d02070f090c03090f0303050118061203110a0501050f0114040218040c0309080d0f14 72
    0x41c49201d0055008071220410074002105460100b17445102040441d0013104648005920940e20710b100158584075121034250b8480c0ea02c071546030b10b400001d98a00c0064503078103032000d00200141031a4418410390340c0b08000001c00340018105814120020b42182c040c46501e1030001041076442402000c6084210070305a00b84000745908004400c1c100c41d26030410785494215070308407045552059104000b19104100c0002d0550500d540d040c54800060008025540040e00600184070064805011034055410201c1d09400304c0708103d02a10325241c008109414440310203081503010380215040e030301003107103281c05102008021002d980d1148907007810020349000b8640403a208071182004101080d04490584011381e951a08403542240c0941e008441000107014084694010300140c0b40700306d500307506003c04440c400c00c100491682051080341e0740c1c860403825901a4000d0000e15400a18150300d60045c5003c20740680070b0480303403c0e40d03903160404034079504c070105070b6050050b010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 442835755 1250 442834505 442834507
    0x30f01060f0801060e0f0316030515010803191b0c0e0601050906070602033304060603050402090a0b0f210115060516060612050109030809061501140714160812 70
    0x42c20400707980c5041002103a40d005070264807507241c0d5031000c001c0d9410f8030040b0b40d02108e095155041c0141003c001c504880404000c52004200107940041900c094034130040103c03041c68000c190591f0184440006001d41c0319480b21050284800080e6050403034404000c08031165868000443c2c03039208444000394820018010140403a146601542c2d110300d20713998101c40065212100303121400322060f400c0c03801c0050302e1021841c0c10540951b000415440c00e00b408182800d5000540f4000300404be8510705944005252281c1d5810f1404260760101400b0a20b60651226180441c1201054020015802c058211011031a401d120004480544d43e42d10b081012844400d018058400401d03200c003500e545011038030302900e85401c1809031244c000001c91140d5403030702030091007004045403140d4004800300300c400005440f004502c0d45003403920250b101c40d06d004900f80740c0203004018000183c0f503000e00700000d10000300740b0425203826400950040e03031800c071503a0b10b8404c2d10304050a000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 442837005 1250 442835755 442835759
    0x601050a05060d0509070f0f18020406080606130e19141003120302090303040b03330d05100e070302011101111b0a0204110a12090b010b130305070b030f01060f0801 72
    0x35044d0302c0745030092400010342d25969959416920f10311ba182d00300c42407005030550204140304000324985401c4868081c154181751600c07102070b00c515001020320340903400024411045588809802010705039041c010345243c04c061070558644040d508501e00c042e031800000b08014940003070264400c0402d06c00b070041003811540d47c03200490320040c201042c5a028001035809540500241000c0c02c05604515221300d0040200e0b94000020700c0b1000201e100c8004000510010244400d550b010640e46200c10342003a1030300f986408082495407514501d4041c540d99030503004541101100d000360b8a004c41c002c8850401401c9585400402401100c05c01190081184400c40541c0c420749100a9405031074264010a080c3d50b80c00b40602d440b41000035101103820f4000c00c20030000d400070241042030308031503034a0800d9000107026200701c28102240540558160381020406594458103981155075074200d040042d0b00291000c0e691038500c1000802d1251140d19500030080c611b650f25685c50b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 442838255 1250 442837005 442837027
    0x20011b060e0f030301082107030c11030a02060708090307080f060402220903110613020d110a1203050304020102060604092001140c16142d090f06030601050a0506 71
    0x90001c040303120310b010380060b150700c1a0301440554004c000c080040c10600b24170070510000c0080300808003040110500020b00403d500003036100301158880540d44050024000191810010f005d00a5011100103440c0d42000b503041e024100c2d802c42501100c2a01c0d498080464888210040742140c940c000000500540342048c1c000816200755500c95050307460120500301030f0390044500f0360100340601d6507070000f47c00030820541d00440d2204102e1540000380e00049a61b030340080c0103007220100740d9020310169242c1903280001c01560f00e030707407502801c42d140180030398108030b5090780035000d02d03800200c103401c09010b180456a03010f40082c03070201600441c00d10140d00e040000b410410b010703049140340300f800402046450140d0004084500c07940700030800820185e00300d00d1155080480c0c00c100394070f4100480c001d40c0c6070703900707000501080304040f402403188400c0e078154004040024404507008420144e40104400c0d000e9860341c1c0e0700e44040c040d000d0303483c0c403c1c141c015408111401c000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 442839505 1250 442838255 442838261
    0x601020a080d0c12051618050d0b150d05070e010e010e060d060e060a0b12070b16050c100f0e04050403090b0d09020312090a0603150911090d20011b06 66
    0x200d45070520140c04c20034200414100c0f0f608940075a4840310285141e04510b07007200344240e00d40d0460807254240c60034000480c030200d00c103050040007a070200d0041602254084541c2e02c2d240300c0580001c1c01041982001680d6503c14801d242c0402240d90001c80c0014240f2150707416958000c241000d151140e8050150641d8214003e685080d5200c8194140000501c04039020382051400485c11315540c1082090035081387c802401e40e0340c0210000c01c140f604050594240910b03218502e0940714107400c00381d0030080100c0101d6071005801402c251813503042518000c500102d0340c3c414a01c41512028041103ca003030b200600899090740d010040031101e900181152034a020740801c4002703543e0b02183c035000252402920480b00840c0240c0f03075042100401000344181d02e0140b0904807a01d04004401d00140605650681c40e811150120900c410484100000140400c1c221200c06d003004805e90580200c03030445c580c3e41c0c10040d141503105591105180c80e40c120100e01c141e186680e88401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 442840755 1250 442839505 442839521
    0x121b0f0503071e050d26010b090f090603070909030c06111b01020703020a020603060103180605070323130305070b0a0f0c0203040b04050409050f03030c03060f0a06020d03110408070308120601020a080d 88
    0x1241842550602106c4200c0f8220307802804c003503a400343c0764104801000b20f00009041118020030b04002009800d40d400210706d821940d01c845c0006803d52075090807100d50f4030b1a000a8202402e10111000801002c0000c2003090984c21032608100c54055460b4240c1c0319135800500180d01002c0000054940a0011500b1001c14140041d8400612110010020810100341e60b01d6595600b08541a60103021721403401d04840c1001c1007842c09200802d00505014007104001841c003008481014041e501300c55410b6000046640240744c05401c0501500080d10b403034000c68103000c0302e01c3c2118000000d5074203403200d0801c0340781060700380001d0000a0840307460903511440b543e03000c0c0340004810300007140140460281c1c540d807450182c0034000d44610000f491b0b0701514010f4010042e2030740c04541c12248001c503240104100b0039913089407019025580060f46036024000001080068030710040c015010f094654003a03a598100059072603d54210010381050800c1000c280c103034400d5800081c13 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 442842005 1250 442840755 442840787
    0xf080a1709120601050307051f0c020103180506060112110a05030903070606060522030c09020901020f0f0304090e0601050d020d0c0e18060a0603121b0f0503071e050d 73
    0x1040c0442080000c04602d401800c9030481d4014a005200e24241400300e40007410054480025112819444100940125002104002e6000b0f42c1c5c2c41160700c41d422400086074100460081441e0500b41140c81d070350241d51440c003080c0704800414203401075003d01c075041a204d0b0362181c02e140074410182d950360320040c0b0540d19404104036180008002e0b00c10310018054942d00c6649942d80600311076007501c0c680c0200d00c0c00213046481000010f01c160301d81390544003540409a00c55954100507403406000005183e503030700442618614031440000035008660721140184544240c0804040c0c0750502806860f400c048021100310244c01d00c406405803551150a00410743c0355030f10b035030354885070b0141c03101040940b032030402c420810401c0040580003034070100200001c078030b1541c5a98031140b010360032801344102c6045190908103511192016180c0111032480b030210381d45006502c1c3e500000c001c0742d510b00851181d008003041c4880281d90150300000a01d2007d58240003550000e01e5020242 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 442843255 1250 442842005 442842007
    0x601170c0a270b03060a06090f050d140d0201050a0b04090b06190b0a121409150a0902150910081303050f04080318040507030c0c1203090203030708070308010f080a17 73
    0x801030000100c51000300401003c241e200d013001420002c5003985540036a0403c140c9810a00c64a90215030410407580e04132131000b60b817030766458840700c9440d50f02c19000c0907004456404e0a880e4044d003015215407040d000401c00f03040742e401040102c3d52101005041600c01000181031410701d103180b107510010b4069049881c40c0d03214150741e00d5901054500000801d0710158195614082c0166001c940001d198500c46103850118160745621210402d9400350403a008294a00c406a0150f11031580107000f03c0455a07a00c0380c1247c030380c1c0c04290114058040301503000140f511480382540500744001d0030707071240e1043d1727142210380340c101d9104a2513400d4108400118a0010002443d0030002f07848500c010110460400c01141d20040c1068141420030000b000010307481072010b00940d40c01483c1003524030034880100d00400b40a88029054800050403c0074001d184001c1e1400f14440e6581c1055682c03181c82032803e10b0041c0c8034241c001e81c03001142d5000a000c8045003403600440000781 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 442844505 1250 442843255 442843307
    0xe010f0f020705120d090b1006020709140604110d02040902042306030109020906160b090d050a0e120a02030d051213020904060b2b140c0120010b0d0b0601170c0a 71
    0x802504003090301c4540704040c230800b08104607901803021a0007040d00103010403504c1c003c030004103d06900101901c0c419079803040003501c030b480c442082d83c0010141311402c41d111912521000001d501900580c0c03444040348410402114035090f5440403000083d00c21411070b441c2030710504c0a500300342034282d4016014014014501449451040100e00803940165181809802a801c001540345400f0030458100542d06165070840f000c282c031300805691920880034038582b09410489007603c000e501d4080c0910f603008255122002e468481900103015007103485011088420140100780250050044400a0080349c4a41d02c101c000c020003902c0707014400d0080355001003402055901105480c49851030390180058540c1c10400820318000510100014038000b83c07950f605040800d0944540b8207180c540e48201303401c038403ca444090301d49040c1c80c0309441c1040e9501d00880f549070000f5403181c1c03218001c4080754404c5015070410b0200a1403d03080440498400720b0224503402d42d00c0c811915 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 442845755 1250 442844505 442844513
    0x312040b070f050a030804061503030e010c05070e010b0304020109121e020301090203070e0a0e1527120a0e0607150b0303040509191b02071e090e010f0f020705120d09 73
    0x582c0d03031380d610070783d5421028a01841d04c0412141008030303200118407181e4007400041c0d08601d003d400d240c000d080c9261001014a4214548403182d00080e81080c1c4280001030448041409503014500c07d03200c1100940d200e84550094004180e0301520415200945021408801c0030f60640d443c005030011440743e110380c0200746000d41d5640078000e901d1a260410000074118800d0040400b030403806040001600c1d460850b03c2a00900300400728803000044908410320142264400f07210319003500e030b04140041c88152150441030004000c1214548031503640d190001c1103462b110b5221801c1030096000240600c020454580c000e03400d403004210214050ba225141d007803040307030050358ac0780c450441c9134403030000d49a17140200f040389450380156408254011640c4002c2e00c00700405034000c0c55100c1c1900b1402a801c0e07201e03510301c51038049051108801134004580408120030140b007600b030407a10600880c8181c00000c2e19680002c003a0350260f002200040030000070000d4041942081d94036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 442847005 1250 442845755 442845763
    0x3040804060807030207140a0311070302090c0c0717030307180806190f020f070c080706051909030f03120b190b07020a050603010f0303110309060313020a082a0312040b070f05 77
    0x290f0310f149900c0500312342d0415500100d10701c0207000541c0508440d0746541c1c0807c440c0100500504c0300c0c40400f0a6081100d1020409600101800c44481c280800c40000c1d55407240e10a503038240c00100f000b81c2d03020395480e80e800903400312080c040040c40207a071400720b01d040c101030711440030740015126000034214078600e001429941d01c4e81c0c21280c0d50f035480d901d031100c00760b4100d910441654100d540c2c04c10606812a0580d012030580740042261840800401c51b050000703904018100f070380d0282d40d001456130001030b25203071150300c12003048010351013010489040e48000c41003180c0c640c900400d00080390943e002c0e100340781c406403140440c16166400560290008d8020710000070024100f0014154408150b0007403140c0003000e14580101440416540d200003000385402412400c1c40b541151541911400108890b0342542c40d0b000000b03105240b030044000c1d002104403908d5100006a140c04604550f44060b105e201d2480c103450138074002c1c096000b00d201aa03490003158003540101b64144 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 442848255 1250 442847005 442847033
    0x4020d0c0f2315130f06051923070318030501270f32010c020111040503030304030e03101803120e06010e0c070525080303040804060807030207 63
    0x904901c801420005140d080c141601c1245801c011288600c0381035484808030300010046900000e9590821a260300710780e1422030380008540d0040c0c85001520b00e600a01a05000e07140384401d510034405898211181107210544020344030080c0007d031340c0240510014401c880c800c0c18509411000740c0411a41c00a050b403041d00ca59450308162944282d5196040c1c540d510811003800400740300da128191060882c5000070600524003040c000f0380c0d460034444845511711090107602100c4140d002901912419010f0005982040e030400c201e00c402d401550103170b0f0b0000d801141180c2d26520b08882407400d498402d078040c004c1401d95070308400280921460a9020840c20b070344a9081e15004114641c5440c00001c1e440c9070030440f00300c0030070200d000c40c11100410015211502c80c09051a103501c10301d4bc00411313a11585401140d5540c80540005480304008070035a4025680c041c0c03280c40380701c2101c005146510400c820b22049009414040d04800e00c0d140060038807030a03680d50301038501c03c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 442849505 1250 442848255 442848269
    0x11701080c0405011a0405130f0f06090608030c0a12030e1e070f030317040201200f0601080a120c0c0510110f01020c030405150904062408061804020d0c 67
    0x4901c240301a03040034040c036401405c0031940440d55420002040d8a140158000e661240d50090140884195960846072000c003288200700720030500ba0070724100621041c4a00c0107050300b048800190000040291480d40d6802c41c080c2a0b07101042d030750007a810404900c44004d041d1348209459120008101c0e4225501708504c0880107004010082d40c9014000d42c0310348848a50148140006a07214070a0031300b020307a5041000035034a5078801130b074666201001c042041c0d207105c220854204e00c00180881e2090035041600c0469032590f8840b9141c0e591080068040034216151216191259061b601301d0b034005d9500907122030315040046c0b20301003070152800004050080c0d401d01d641c1f080c400d607102041c1f40c80007180707041d501660f160f44a0142e44600d61150390742060a42d14030680c0411910510790007003003000420b84501c1007480b4450b2041c0b000b010041d601c0c40c149080340c050504240144002001d07402c80c00e42c070130700340203543c04010002c0707030014488800d2000091101030000044d200e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 442850755 1250 442849505 442849513
    0x2060706090f14010504120503041a131a01030f021c0602070b070f0801051003020a050c030a0305090d0e032d01090b01060e010203041508090a05060901060e0a0b01091401170108 78
    0x10f04000d461001078045001203a498203081c0400125040c404400c2400603050090b00c0365654208040052103000c0309507035030603c800402c0740714031600b2a05048144561130100300004404030058091000740001001c0040c9010408054a4002c40c00f9000d0030025500d407034072000d40d41c0c0e4034090340c000f1f680c100d8900034500d09004032650815074400f148246440c03c07680c9589031000081d0710721008070b81502170541c0022020384480c402d804450600c0d42481c1100d980b01f07036059000b4001c00e01101d06420724007601c034103212042c0c4035044034003240c1c00081c01000d00c0203203064801c0c0c02070032403141d00301c803841400000080c14800b0f000d201072840c0512000d1310300303602d401000380580d07000002040c11500100402e11000801ca19020800300759842c00140a40c1c41d240c4580c58000d25802c0074015104984c00c00998a605401a0054556400c406140f50725000d00d03001c03d03621449541804285c6c5000309000c1c15007040c00840e894031b01498400e6103000d8408044454400c2a00500398a400c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 442852005 1250 442850755 442850783
    0x3070f200402090d1104060e100e0705160809040621050c0d02090f0c0906040801050a0f14071202221e080616090b0c0c010207090c1202070206070609 66
    0x110986a80e10108196820740c580f8a01100040780c003801068010444084600740348510303100c941c0544003402d20350510880b60704100010811008592258695000302c0000003541c092062054522940100c42d4100702c07040b041d0303101000f031b412011845400503540c0303d002030904c00090303002d05030520200d1800309104080c00c015051001d00080c941c05404a44003200050300c1d0580859449000e500400c1407588401c4042d542e40c1c80b402c0c0004d68410004500401e10701019802980500880d100800085041180f1001130b6140c0f02c0d1008015134144c1c00248145000320300754003da190701000146802010b03080301032140c080e10181f18000300c4803241440307001406961700e081c00454a0f03185446a14103507040341d0f42c07103005200d403000f8401c1501d03040768a806020003001810750b80f606142c4616081c0d49065039084001e1255005100c0c03071b03000099910f2644102500010300361b031200c80d01002c0074141c0010b580101422a00903208000c2d040100e401d601c038549034036114680c024a002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 442853255 1250 442852005 442852043
    0x90a03060f0c0503100b03040203011410090605030a0c090e10020a030603050c0d11150f0301170606010c050c0409080c070605031b030f0402041d15010501090b1305040b0303070f 78
    0x902400362202c1444010024440c02d4407145190b041101c40501c51150342c4d940d98400709024016030380d82c20302c1d030101210500c05510300102000c410760b01c403210304029043d9520300700b56a07800c0c0b003d0007600c02400900240036140c040e41103142ca41b0f0b0f100381260040090180c2842c100d80c800c0e410030001076a650011f00411400380150a02004e0849500b83c8528040c0c40744078000a600c440d80348a031103c0750403041800791120556490001811045413650394400440318105081c005036040c5006000000c3c01170740c05040c0741d0200c40c0d0030400a00301e140324242884024a1001010f8818090901040040b02030030050740d8044c140340d40d1515220306103e804000d00c10411010145100340030310410a0b564146aa03066100c0d80484000c9000d07046070000c1d9546c00f8000045229a001e0a9109240450320101080c12100e00b07030b0360301c035440743c0d100703516503450090120700308141c548584108070034505134000d6814004002c098074501074150391400b801c0509040700b05c81220007041ca40d4850 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 442854505 1250 442853255 442853261
    0xa02030f10140402181b07060c030e060f16051317011b02030706110d0f0b1216030807020a17060702010b04050903030f18030705031818040f030203090a03060f 70
    0xa45140b00900e00c4504081c0d002078042440054581201c44100c00040c0c03411908900d0b42155440b144c050580d51100f9042c450040c2014102d8000441c0c00d000200452100010b640d80c0714122201100b4980d88801c0c91000c8042c0065203c14204101071080e14080d1020100510003000190581d111812449901c10b003903d115031003123201c1880d8410b116a80c039401104451110354024000500c01e0701c2044444194050a08521203051401480000c281e40f2507002509054003240c14480070815405100e9440b07030f110504681c48034101c0410000a00300e0005455824801401c03d2721703541c0c5a40565200d49070450340240309070304c01001d03c14140d4080c810a810820252130500951410b142410390340c0c400603000107954080d04001505018a05c080090b801d00d502069039560015420400c1c0d403034000000010740000318801e281d1061a09194400707144c0c19242d1066010303036881d1174004004d0741d440e00903801d50104021100003545d80c0040840070314801d200002e0800643e409500c11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 442855755 1250 442854505 442854521
    0x7210e031b1c05070303180c090c031415040b13020a090e060d11130e03040f0302090f1302091e100e15130c0212040e01241403090a02030f10 62
    0x703028215080ca0145600a04403134046405003804288240f0b66010b4074101544c1110150010f030341c60102141c1c1c2c4000341c0242030080710b03d640c12712080c0c407280d140c040041015900b002000038914246102410580c201d02c0510074010158015980002c90340b1069070f001c0750345d100004960030710512200540b040001c0d000306042c0d90440e6440c800c0e42c5e88002e403c000000071071140c50141803800781d9101030340181d5403103400c071811340791141c0c2e841c8240c4000d8103060204911a55101300024078182901c176406209510824000086d841c040e000c2c04a040c0703018024000340848602214503200001118034040c0c202080840006442d1480c0d01426800140c030006a002e000020020113075a600c10b16800301c00e03450307400502030215401c2649800b0360310308003141e40140828001000301c07981a2a0f41282e01003214010380720341c0d900d4203242444a0340940c801003880d407280c045c81959081c000d1070380110070742c04480000c01650000781c60442c411010010304c1e8070494080d00c03c001c040c010010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 442857005 1250 442855755 442855783
    0xb03040605180316060b0f03070f0501020f15043f17060a14450c0a051b0105090a031806021203041a0a0209090c0307210e031b 56
    0x824044032a0380a07861500708800501715644035281e404a541d101c01004000701002800c54802c07a50301c10300d071540f00700c15108150141c042c800900e0403107000441c4401c90003e030308840e08401e50b156503078001e541800c562448050950020b0100300e012005101040200707023003038000400e100c0351a00038810041d0025401041d080b00d010300c01c150321024411002e070740400710040140415440401c010820141e0700740404404401c22501c45c41c20514060034a81034100c03801122000c0d0146a108107c0941c0c100000303901c104200101e01d03219001800c3c014440110f80f00c0407086110000303007540c00030307030701c00d021a0003010002c0b0030035800a91182ca0450703028040000c15217004c20281d11108010708100904000100140410034041031807480c005003407101319945d0505425101c02504818451805940010081821080d10005480c4151590343d0b400014007500010300b800030040d04032000c08075485c1c80401c960038105101801d540b0414101e03810080000034000c40ca41a00d485030f0781 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 442858255 1250 442857005 442857007
    0xd05091b220f0914060705040f0b0307140d0c030e0708100f061205030301380c0a0b280b010c1e051006060e0306060f010c0303060b030406051803 64
    0x4007078480e00c41c80d640d1001403003002071801d600150784801400d00d5103822841c1c07618061110742009038020804068a04450807a150b954428100741c0d00d41c071407400781c0080e007a0b8a12003004490807410007154085003a1a00711302c04500f0040101803a00100c1051140c540c440108004440d0300d0301c1908000c50b00a00209101407610002e0781d1510201903004500507102c90540755018002d0700300301c0040c4038500c0d01034816901c50420640b203800a00440e0700310409000c12041f035409040347c0c4440c03107180c0c41d01d4034084901840c1000c0d0590107a103204400b8000d8a4100c0040340c401100d00c1e22804104075031007426006041c0400c4180050f0500b51603d502e003040c60410303039a010741c031115225880502c1c18082c0c400e510b0408540744800c00300500c41d20403c112041c440c149508074800b15642515a2041002070030201134032007604a0f6141d800034141003001e21a50310400045403c58000d040c00240c07285c40360850700244e441190180c50742030301c4000341314a4000c1c0c46401c1e2042d500708801f039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 442859505 1250 442858255 442858303
    0x90b0a050105180607020a03030c02010809010507081621020301180e030708031e07030906060501230a0909050c070b1032030a0303050609061c0605070c05030d0509 72
    0x2070514000c03024011003d4a240324181040d45a8408407022690014444040c1e10780d00d190040100c44c1c40e0008074000345029010903016441405428084c000540381c220169a583c0d80c115542001000301004200b0b403042c01000d100044003540300c100801e0b14015035a0b6040c0b0300c841e42c880031054000b40c234451506d64800f0003804040151203003603520601c0c50341e8030346844005010a0321411241000140e82d2000e02814580541c00745840d244031342130074401d4503603e500640b02102803c801e00e21484d100b0045800381845500144030038904c906100b60701c291200501003c44c0d0045444c021004400100181409583c0030306030340c0050340c2144d4031111070500005120307402d100c8410a90244100c0d81202451034010b001c900005406800c941412496042c010041c00d025204203004441010200c5d0090800f91a02e4a980111803030519541c1d1035a6500c800906004200104000c1d4103511040018800c0c4020540503000040c04940c908018007854100340f641840005180590280 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 442860755 1250 442859505 442859507
    0x40c0f0305061b12090c0406120b131b1701050907060c030c0501090209041a06041b08180a1203050109020307090312032027010c020d0f020d0c090b0a0501 68
    0x81c0b258041c1e0580c03180a41c5542c40380d8401d149000e03040c83c03d103064800c44104040c84c1c0000070005140c0c80215010321415555003628040940e402c40040c1c01c6000c00030015203102d00080341009814851084100c5205041140029990703d51300500d031080300400e03030650f162109000d5a41c00a40321006004454544600940700a030443e1009051107001e00c0c0c0e5400b440401e500c80070b091500500401241e146c2031a00700c52102a004441190302c1c03c2101259007800d0a120340281c10003041000c1900102902041d07807003110080c240d900202211440460f140410300140071160310450350050b016040c041e01174261441600b12411052051007000855540101901d013120781240e001c403041c000c1e100084020b00f2450010405203158072040710704c2071141800070011145818098240380310040f413060a811000300314140000c142d00760798030161800c1602e0241c100e100d680c0294044100e0b0340421200c0501c448180c1d40003421140400c052174590088408050b012140c0c00325203818130b40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 442862005 1250 442860755 442860763
    0xa0f031b08190f080307260609130c080a1a011502060a050c0c070611010e010203010b09150d09050606100c0515060f03010603061b0801030c030f030c1a040c0f0305 72
    0x140200da10202c1e0301080500c1941d9514400803600300d80f0701e9503645080840509045046810700c009100c030300c44060a8448415501401081c1c010028402c41d01c1e1519122420209080180c801d10040140020150001c00c100c0368642c1c4500d40003000c188508100c44080c00050744000d6940600002c03003904030780c1c0882e480b9800900305a00190355118041141918060401c6181c100e1060000c003150103a08940380003d041c02d40f1000703105818051071175909038007080c0310740c9503002030500281c03010349041e4050b038034994034824040c2c1c1000842d0250f90107507480200c0a4903141c00903400d1040343d003461241c801d44126641800004e1100340e0f030320581d44e8017845006e44404010540840c230240d4078107612441e0307000018000e2100c1600da0510400070205200980d8050081c40704042c5282d002c2c105240c1202e07002600b0a0000e869a21034209440c00500708504201ea14400400080c1e90700c152080c44101c482c103010040c1c58240b6220940e50095040300c940c00400d10f00810010704006 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 442863255 1250 442862005 442862023
    0x5010905130b06100309050a030804050127080f0c070e06101e0c020a05220f0e0d14040504020c150c090d03140403060204150e010309030e010c020a050a0f031b08 71
    0x81c40c04c40c816000f0090403401001aa080140540a4030401c1d00505034070803840c501031400792008102200b0540d12022500890300500c000b6079200015441c0401e0000000d0040500c2d94848145040c15442c0c2c1c45050245a800040b4500b204205111142c14108a030185d07103005410b1002140100405110300599000311400421004940020031511882800b07001030101030840c2c503100045007048400700b01d8051201615a240600141c00306d6103a004404d8410803080c00b41c918548110811114000c4160080c60f550300c0422000441c0d44032840200450301342440903003060000c0004440c000d42c00548000b85245081c4500703001580c0d44216440b4207949411708214180240c140906240603039400984404d01c00b24002480d4251036465101a00c05960b5002c0a134401100540480700e40d500701600103130030407059840c0d0394010036111403554001000d01052540e1900000c113513101c242c001c5540c0c0d054841040040000b0311540d002400c135401103164410341821000b03580c3da00d4207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 442864505 1250 442863255 442863259
    0x20906030103110f0616060515010504051201141503100b06180d120c14120a050a0318031107050d0503090904020607290105010c030f0e03010b0904050105010905130b06 74
    0x42c46001d0700b50b521803840c101880405017105441b03900a00c9900072845030004c06840c114240000200d840c00b82c0c517200d00e50382030140c540c14201401c24040c8100c000e00e02c641790340650340e103c2948061010403203410f449280000c1d2142c40468581041c5030510f00780011301026581000d4000034140d44220a07500d01441c012200005503410000140500b011281c02409280445034181d40d03040e07002c940608458001c0400202d100107484100e5034401601d2000500c100c4240880c641203480f40c0000c0c444664103140201e22001c440c104400800d80320407044002c20690101381a0080040c400b100050008403200f070920315054465540f07a215501005100300c07640030000342103588002c2078a0b800d64001c020040c1d001d403015102008949241d50550360341d0764000c00010b103580709080c1d070200755601d940c5080e01c0c03c00e01c5105588202c62043c41aa042d52524098416620b40030503051080d07014100204855150030800e030100d43e0003916580c640c1c01a03030915404603881418442d00b041c02 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 442865755 1250 442864505 442864523
    0x200d0509011202120a06050108090c040b040e06190e0a0c05060c070f08030c062d070e060a030209040c0201020c030a0807050d060b03040303110903120f1e04030303060603020906030103 81
    0x10340d001262003041980d10180418400304240140b200c0c40c1c03070340d2032184007840e42c108502a214030040d41e8548084a0815003544600c003629100d0406800045041c9409400460944800c0d2489400c0100c101c441420302003000c0400b40c5010414011440c0d4040007901512225020b038680c149244d62a0241d03500490000030415a80d080404c8800028501082c1c03600c240b0343c440405a80301e9002000d00401b52040344003040d6160400001c1c9166110342103440741d444002d4603105045460005c04240030f0007901440d0806a482e18002000c141038035690050b5610203100401049800341d030b10020841e0f02c10300203070b140000700004581040c10305081014099886c0782c02180d880c13103420241805617080090014040108070702442c0030f281300792001c0c46100342182d0840614050a541c865140d400b40c46a03502c1035a0310f60003401c0550424640b02e02d46801c0b180da078182088a0b0701640d03400000020104140365042c800c1c0000b0b000c85180651a201290000803c51702041c0030140000c48 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 442867005 1250 442865755 442865767
    0x10b180a150b040e150613170712060c020a08031503012304031407050a060605030c01080907170307050d090617090d0509190e01140307030c090c020708011407200d05 73
    0x440c81701d803c800341004001ca95107102050101c150955107101c0c5d070140d00d001c0c1061041304c00e0003080300c0c81a9860904980f5038401643c60301d4004d8000d4040c90000d5000342c255150115030303208011840307003040720704501c0202400741c281800c44160640320204842200d1060080803804000b80781c00c10f030113141908101c030f042d480c07100305032207a050010804c1c40740340801c01c2008403540091080b00c3d000c034141c5001d100140f00644481c003044621441d0750f00401824006800012984134081e11300c003048030f08000250f95110301d424044405200072a1020b242000880d500605910483c40f132018800b082d410f002c0b01c80766440c1a142181c000f44503000c0b030302020360303200c03061600030a039044540c03070b568181d07200d224201c2c0c4042030242404403000d0160034181c1c0d050014621048980c41a40c0d620018540785100380200001030740078085004600d00055103140c24040c1c541c4545178454100720034200350f4409020b441d01c40311001e8200d128150000841900800d9600d036006080c10f007a40c3c4c0b58 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 442868255 1250 442867005 442867021
    0x3b19150903090b0c1b033706050c070512070804090506011101230a060b1c06080601030c0608150d0b06010224061203030613020c010b180a150b040e 65
    0x100c2e050300a54a8800049003443c280c84000410301c0621aa2100001603403a400e030605450b0550400c120b80c040e1048240302c0c40c40ca140807200c0d510120446900341c0d40f0021030783c400c4140c41e0243c0d698917444c08082085028000107000c0707000c00b44c005900f09031600403140c0e80d0901ca4010f5124080c140e0390740b94002201c1c2d034002c0804801525002000700000c190300440071040c505513070015030030200180b000541642d6207100d00c0701a1703800302e5040c03030801c420102407581c025010414240450348940c0002042201000b14074042c611408042c00c01c035040c0034005003441e030001c2800154003030310105588682c0320080d40c103012039004400c00325203548140c0180c0c9000c3e4038149880001c61011201d001000302001e0b490f0060500b22101048081810006030340c0740000c0e0f6200340d1100b120b200c003101c07080003507000300050400310303002150313a0982d08001740306200c400710b4454950025004100c40000d02d4030581000d06001188510060f05124400e0300902890144444071401200420407039 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 442869505 1250 442868255 442868267
    0x30605091c050a020f070b040b0f0403121e031505100e090114010813051207050705030d1d0d0b060d0c0e090a0311011b033b19150903 59
    0x1411801c1038100c0041032070700200183c1c8800f107014014002c0e41c014258101c000f05d608811500c58050322401c043c109400800642e1010703a22591642c1d00300000030014680000c11005454161103041c2d40b96500c1c14032054101d003600c000d204045c9000c0e807584c518091103010001303840041c1c8040e415070369000350681c0e0841c1c1c2e9502180d80851184d00000300c1142101c2c441d138883c1000e90b24502c6603280e0013a03800c0940111800100f23303030459042e495080e00044042c200c1d00d0b00580440f0303480c40c2c0d62804a400c090786444905c00181d82c1580c0042c1c100b0000c0100c0900c1041601c9450804202e81c40c3c059200c0c0000d0916446046038410000c18000c40e0f040c803102030501c1c1401c6982d241043d409027a070354108641c0c11004117811501c3d40342d05840610403007000f00c505120032800a1140141240180050b880c034001807500b007083d040000109a41c001a2501c80002c10401c0040c1081c11500c1c3c0307030880500b030f200e082e0006500c5000507000d000110040d400c404000c24443e03014a415610 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 442870755 1250 442869505 442869523
    0x80906160f030c0512011701060e0c090111071e05040c0e0a0311040e030c0109060e060112020f01052104110d1121100f0b0108270106051512150a03060509 68
    0x500e1888400101ea8515400503985407100600000c0281590310044c10340c0cac00a040700d0707071440140300703100007401540030b0140480035064450a85146a40356808980005c000584070710f844030f601d80e410311003030405101d6181c43cad420078200201d80983c1a00080d640010a0000600b110140c24042904e40c540b0b0300840880c2400304192515098801c0c6c2d894001c014050003034601c1820000c46032101c905c04504a4140c41112a0004403190390345c00380100710840350012410840c04020b60603500061304043c41c00b034047e201d01d11042d03003041e04003d50611500604d081c45038004502000c00101007603c0c41c56075100644040980601302850755440c2d40004889008501624124404550181c0d010440180e0302c2034040101000f160700469110304111451034500300712003d80c000320044050b000b410400042c001041d416143c070041490003000c50746507014031002044241e945298149030503072001c405405280c4102c641c0d00001c00700ca0726484040e0400d503031900070580e807800602c100f0388 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 442872005 1250 442870755 442870777
    0x1a130c031d100c020118140706050918040222051503030c1e01020706020301180f020f031302041d0307060501090513080c070812040302040f110f0a0c020907080906160f030c05 77
    0xd14461b040c00c241c03a140b041c040c0c0b107048901078000041403190066041e50030303484003d0702001320300c0d1800c01070510b09900500284d17440304102c0c141091010480f40403911040031914081410f042c441421640146c0005500d0b100b90820321202010300c80004421010143c048c40d107035250004a09c0a0b0b00911a51070050090340c000000420703c9281e40c50000c1901140f00c80c1004150a00110407049000d41c05150716008002c10116900d904c00511900301b0f07600091002418127480c0c140c8681d044004043d002c02e5800104401091203c01c0c41020700402540505204d5842c00b1500100c1c03803000c60100078680140410140311030402080410042e0000204550451502004116058005101c100d120320b0804415400c03600d182e01079a40070142c201041424802c0a030b1701000640c001c2c103507810411100710b40c0800507949124026004a071151540c805904020700c4160a249001340250403214048003040b40155200110760030403d03644c9000259030412510490b098440c52980308 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 442873255 1250 442872005 442872041
    0x8240406080d08011202010e040c050d0f360b18060705042103020706050f0d0203041407060f05070b04060b03010507030c090f0b0301091a130c031d100c0201 69
    0x110341d807600080c24000100154039143c641c1e0b80c0e2000c40022809038640300a0004807403000d5080e1500702034000342c480f528a03040088c02c1c00c450000321130442d400c0540404070503464498254800111248203161a02c1030f42d02862110307011b000c100c10f03040c2140c0c0010042c00700c02000078207082a000d0119203481002081c0c5050742010040105550002c0c012828908c03070490380b550080d4883d4076009601d50f8560081c0c0206807900310b082d03420b82c0101c00301d00c4543c881001410b550000500c021846648542c190b10382e95030800c0c02c511f1800b21076401200920822004a0600d02d810105a43d9016404855912150341e1851715802410701820415010360a150a02249039015042281000310300e54030080c80c1940d070541c2c0c3d00303580c1d51441100c01c28041013005100c025002e4014031001351143c1c1100c6042d64450380800d5016007141401031485035101c408205855140c02010f0610700c0703c69140400411403103030251100301200d503e0f046950b039800c0c10b0361018001c1d001080088104d910071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 442874505 1250 442873255 442873259
    0x20c030d0815010f0f030f022b0f02040602030d0b03070905010b3c0711181015120504020406080f01090302011401060e010810030f12030c0206060108240406 69
    0x382610390241d602291602000102d00c90707551081d03020b01000561035a4800110110300010b5008012250f9040381584d0200403140c04120701d01c0079440e668250088102154034420390340401c80b0303180c15840c03001600400042210a60000c183c3e800e117000c035140080c10401820000b0700c3c003840381e170000c614242041c000103140908000640702c40038502c0c04050b40d542d4182041c0d800e40d007582280822100302c00c800111203010500140001510880c80c6900030f0031039800203400200240f0180020980660401c82c0001d6102c04401c000c0c00e207902d10a10000c2c0c4c0300310113000040041600c400280d91000014155652034020000800d002c9098403035010202e13070390744d029000301c1c1d40960256082104001c04001407000c010704990156a600006403203d100454003024041c004024141d1551004004950380e2107035092070078400d14407012040d84945014060b07a15101610003990040400c10546907002a0403584c4900ca0411050031107111210041d5400f400c0c1403000e800520307101c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 442875755 1250 442874505 442874507
    0x1b0607050306010e120d05070507082b050405030c120313090b12060f0109020f040e090304031a190c031d070503060f130303020a03020d0c0f080105010302040e16020c030d 75
    0x1140604420f91350080c01ca49a0018045003040c8011400c25076800b480b10314a00c103200380040c258140c801e40c01c4c1ca04075569039030451b152221180480c604a080b61345481c1d640c502c00d004003010205582022400c02e4030b80303000280c403601521321170b0340a0300b014103204070790306818030407038160034a01c26495941546803e5658010103603040010301a84a0b4038001283c854001040b82c426500725521100076070031310000101a401400ca8940301030380a02c004074031140b07000d40c12482581e4038402580c455196041020014915802d044140c051900c00d10002e00410030100014040e0110301094042100c03204400410014042d92411114003070441e03158180405d0560484100b2011140343c4c1e10b80b410307000013000e02a40d003401200382002208001034000e4000c2e200540281c02c0050420140c8100f640030b071204c0d10b0000703000500300039045008581281800740540000e04e0b0450501c0d00300703031480001c00405000706025007051405c0e5021144200b00414005c034002d0240c030210985050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 442877005 1250 442875755 442875757
    0x50f0601080612061f030218060a0f1203030b0127030506090c0112050601141b071e03020f06071403030117010b06040501180e010b0c01060801060608010302061b060705 74
    0x10600c0c00a00a00081101c0c0d02e00148a0444880c182016200c03e4642d805460301c501c015001004058011080c00005607444091296616544c0300400c43c561800004105502035184c2000316043c1010074103002d03003000103040c05034141c2d140c140000d200f084000160349003004140e80b90f03c901c84540c0c4d8030b60f50784200c92941c0116840b410440d46161180c0e0020783d200c2e00b0f483c4040e0b0004030340c4401030040008907040f10b50001d0b03041c1040800b034008040140d50b00e911010030040a8550508007404650040080100a080740c1d40c54903000d02189480c011030003a41e1002a109240828140c4640d940d41c00072074554603800f070410f8965800d1112015183c1e0424807442810960280d1184100807041c05000e1811b07000805031271a040c01c2800540d40040030710541c110b42c003c04100402c02c0045800024041e000901400d03841e40501b00e00942510b049401110059051150420146c2e40140640c0d054035070454005444011551700140c4002e0201680c900912500c02440915a000b00c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 442878255 1250 442877005 442877011
    0xf1806110313080f09090a0e0c09091e150a1b031104090504061b0306140a150e030a06090c060905240d090c030605010f0501170f0c0c01050f 62
    0x1105000c10499144290303000d0100316000180c07100c0c950007080c00600789000501100c488101094204024038000c21192842158820492a59088035800e4043c0420100710512002c403030400d035074580101d0a54641400d40c0305410a52800890182060018452042c2400b0240213000762403924540c04d4001d0b007020035103030745809100841d0b044501d10900803003400c0030041046510b845d203001c1c032002c010200200700b65102540d40d80b00004404585440a4049400750340201e00181000204030b5500708412416100d007222610800981a490943c0e00c03000c8801e00300700c4056282003000c03038209080500e00400241c034220404040080403907565069810954803110010b84600c00d018540c44001e9021180488580080000717009807402810051180d080104100c0c0f0903541c2c2074000d4a55800072075940e91507400601498030241c1d540c2d0010031003440c001d505440c480600c05050a4040c09100d9081c2c14180000c400c2c3d1759841c2103070308410344040200018a07107810003013a298810307 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 442879505 1250 442878255 442878263
    0xf080702010f02030a0827030d0b040b010e150a0311030103030504030b0c0c030702193303091e0f021f0207050114040e101509080c060711010e040f18 66
    0xb100c03500d04a10001c1501e00d00b4803030342c07103070070715612000e9002100040c0e800020200d14202264000c42041c2800504083c103c0800d000c1481086a41000b0a03164900281810400701190850031a6203080781403c1000c0c4826207141e5074800da45d411009083e880f1540c1d507800d98000700020030103600000500441e03000342101d138800c0c1c80745a00242c580c4102c0300f81c004240d109212050162600b64800f03d0b003052200e1661002a60311034516104282c036181030002074000d0b04012102012035000780c9884241440c0c200a54401595004616030842c4261760404016040315410800f1880c070f6060701e180c0090413101c440c1d072000101200005030410150050280e031000040341d502844103144a5510035404a007403a0610310030140050004044022074441d040b80054004066031000c84841c4169913090052070030030a426140030286d03e0580d00a5900b080100003180344210308401e0f419091802d940e001d000400018080d01a06409001080c50035603000140054484869441c1e445 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 442880755 1250 442879505 442879517
    0x3030507030809010504030806012f0102071509082506110304060e0a030f030b0303040b0d090201021908090904050307020a08011b08010b0409091a0720160e0a06030f08070201 77
    0x40c1c18943c500765401650000c3c04114030001160182d0700031032012071140b003c0001101c084558400c02d0407120740980e90301c1031701c0c4d50000f450028088112481748100303000000511114450399208800d074420750f11454a6165101840d0040010701c202c05c5009a42082c810700c002003e0300315441d090ba009072800c9031a10302e09907081e15985000f20349114000d81607211aa0601000d40007500070300381119015505000c04c01c00440e11032104409041c03410300c40d1000041170320261001903d004907240190710f10100d42c000c1c620000d4440c00840e01b1003c0f040d41c1102e165100e9184c0a0b245016500009503c0140000003152038601540441440400ca030821101c108071180e003511030690a00911036006000c000c107010904658000c405102d100b075060b42024425407109080c401710070780302d0354001165000d105c544076258018a0566095134001344c501d0011060560500d07035090320030421081040c0000580e011076640c055001503420042c003244030f00052030b000c841580281012400301d56 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 442882005 1250 442880755 442880761
    0x101104052b06051005011b0311011d010c0906020f0d1b020d0f02010e041a09040206070506010f0801050109020f090409060b102007121103010917070302010b09060d0602030603030d06030305070308 86
    0xc071820050610030480787c10385545a240b40c80482d5801502d0350f002c030341c9640703c401c6031204103214007800e4048100740000046100f1848001440307024130741e200008644c4800030399625100301250000100d101410611030798100d40100324114403102d040a54408492190700c824800388002500280d0320036602c58a91000075020001101e00c2005c803c03000ca11840c1e94240320341044000c0c550858002020300f42004407a5444501d004402d03088545c40e070310031010070004c601090040c9400350202407019420301c0510702205005002d8070402511898a0b107005500b40b0000e94400013207050302908402c01e5101814014020498101c00104030202d401201031b24200c020520384c003030310400c21241002d4183d540f02c211401c444421081c1d415560384040d540024110031000404000080078251600c5003420080d00b15905208221300940c41c0c0ea041100c5580c07251000c003041503100c03000507200c3c1c441d580460310798003680a169140c03901d0054040141500200544440d40c400c1d500e5901607030b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 442883255 1250 442882005 442882007
    0x50901050709030b04061b0c0b01050a030f120e12010608100b0603060d08090415140904030203090d06020c0105040f0b22080c10050711101104052b0605100501 70
    0x3920499030140060300407041800024404088250001e0084602107860116040c0d000001d1040480c4140441d0311a40e0003002c1240050f10309004100840e0415030342c80c03454941d0002101d480c1c20082c0380d61000743c0c07440202402050040c07070020002d0300844036400c00c101c070365000305024000c1403031030301c00d48507488031070400b6000e682030604014000c0303825a100d0380c05000222145520459000a052101c0000d544440c8142c440c0301348040d03c4414140d1802c100031240d0710010501600400144081001081c1c000003200c0c00100207031100d041d1200107040c420028003c100703840e000340d401c0400b07000c240151340c40000240b42c011048108161100d54000009941603000c40352a614140c2011000c00c041502404128040301d06403602e03400c20819600441e0f80c100c8204003c11940b100400c0e803441d08002c2a403800c101c0710343c01c0110341e070380120100792070207540f062910a01d0f200c500203481001580100911a00c03080400300c46c540c0754030f003a4000e450110350050001c1c2d00070b00c0001c0d01d5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 442884505 1250 442883255 442883261
    0x121516030e03130b2d03040606080303070c12090503060c120601020312130f02090f09010e2a030a140a020319020906190f030503070218060604181104140103050901 72
    0x521002d9903c0c980c1c0e450310b44200300382c1e0855511400444000700c003001c007207446030104015044200300c3d215984d1810b454a08101e4006030486840c039403090041217503440d004028520f8044d0010581c1940c8100701104481c020019000f064040c01250203000c505424000a0a8100d52005401c2e000c3d680e01c4004903502c0c040c46800c00c030100d107800b01041c00314010f03403090724000380919040c450a002c1c640110329031040684207108005050320400401d10300c20b106442090884034040c107400020b140009589545000b11701903c840c2c103d4280312240d40401600e483c160f44851005211101d0781c010320b4480e95501e900b40d01134080d044099605038800412206002d900614414590b1249418400010f48502e089041c4035446c0e040496180001d034a414000e5200b58011580d0f05540d105101c041c1e005100c04004011340c0c84140f0105a43d00d500f40c0302a5841c0101e4614080001c0803503001034486403100003000c10000401107254a01e4034002070600000f81c07001d100d651100c150b12422 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 442885755 1250 442884505 442884517
    0x30a0909110c1c0207031202060603010506040b0a090513050610080607090b180d080c1b19031502040504051008011a10030e15010906030b09030307080402121516030e03 74
    0x680d0001110f0350945032250b80c14800c440b58910460f502d05440f56140d200c82c2924031009030250384840100b040f10700d0240602948220700361004e10080d81c43c0c001141c01c0394040c0c003d07187c5940c0c42e000064003ca50750303444803149075000401c880c0d00e8241010b489110f20514007503c0000d0041000103070354030307010b410604101c03100c1002061038a031000e51255541c1c00d4205115038400351228240c408221864080c1031a01209009031104d81444c0d06074200200181e00290301403140340724040c50bc5040590398104903500804a860b14030420844840248511f0f006940e0161030001031114542e80e102c0c1000c1900c06110080000f400c1e0b607601c202c0300c034010011241e03000b0804459555001d120760030002c1c41c05c560104035030a800003002901000b85003608000e25950f40e41c0001c0060203808100107811622080295180d410900801031441d140204060702400303100d0525802c4000410046d0360040e2910400c9409050503ca00c055030044029941e00107414000b52048482c4c01004540d0307 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 442887005 1250 442885755 442885777
    0x10807170601120201021c2a0b070e18011412010212041104061d06040c0c151505060a0e030d0f1709030c03070507060305070804020d06110c030a090911 67
    0x1a040e8a40341da404107008502808174118021340c4080e8035483c0c44251010101c032681c0d264503038038508040f019042c0c0171140c000440780102400170b91700490001c0458581042032031034104003d101400c00300e03102405220200c025030031fa103000080d00701030100c0c80c19803040c012128150381d00d1054103450701340c0c0100c00343c0c02030a10940020800040702c081c03007601a08005040130130519590b04481100075005941d0075024555a82000154a041e21484110348242d00b0030520350f4101c1e465100740036600010b071208695480010400b5051071410f02001000b004000759910840040018441c90030b441d10240244203c00c1c2505182d80174805001310412907542c0d031107003006600e1003142070040281c65640540410001c103880d00c0f00c14401049041d0003400200450752800034000c0c2210702c014071010811281d1401e200061b43c0b0301c05a400c419030406008214007070300c2c240f003800c107120305024480c95100001d01021446e0b00b0221110032180b05490420555442001081d2a40b2400c54074207 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 442888255 1250 442887005 442887013
    0x90d0507050934020c0a030c03140706050412021c050a0209010824060a0915031203050601120e010b0a06120609020a0507122622050c01050c12070b01080717 69
    0x120f50078004564030840883c592044455141c050342c0072036004801d5400644ea10b8440600900601c00c41c0384c9181d1541007640b004184c6036140c05001405406a8040c03d0035003180014484103646d510401c184000740840100038150900c6c3c40c00e10713a40e07410210b0890250003000c2c000501c118000c41c01c20703a20181031010008902050401030081c61004054650142501c10045040c003843d02c542a4118206982e04558900b103080042070003d14181e10302c201030030801000f8050b42c0c000c48900310000c400901060403c040100503001d82140c200740e40c8c011051356400661554480c1e040d40c1c0d09107003078004000c640d40310705412041c2d202d031144a0011403010080130002598400020001c1c0d686840c21150b42030b4412052403078800c82c259010920710141c028041c030502403450011080501404503180d1500e02d5480b00d84410040c00c140341405004a566180d614041c0410800030150442030b541c0c5040354a49243e000100b8024604076214420300030609080e850409000c42040c03070000c1c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 442889505 1250 442888255 442888321
    0xc0909100b0d0f0f020f04031e02030a140a1401020d060803040515031008010903031d3009031c0206011208030c13180917131a090d05070509 62
    0x200252464980c00c0000781d0780d480c0c0b514144d081504c098442000c1c07040ea83c5960b21300c0c506101c4c010034030b001d40900c0b09580c4040c102005135800661043c1c4640d016800a10110300215180d003416414800504502910407503c0070026040d801002030b17032100390040061030703103604410313545c0e005a000b22074111860080ca860b0918210780907503803120703062035061405c47c5c0b500c82640c29611410b0080b00425210101741002c2d0314508403285800140710010000b0403e168580c1c1c002c6c5d403e4a401e495012405410315103052402e00c00c40d510000701400b00c5009070105444600126aa10803440041c0078207400417910b0610040b582d109036030405100790458942100d800b803d40d200f003080c0c5654005030000008c0c0d00351b8500130b602c131048107005c000030301225a044c1849075800c0c1180240e0580002c11032010388036121104007003600d0304512110300209000140c0c03030303e0303118109000e44e0050281ca0180d040010002d415002e0382d406130b488052035200d0103d00241d0090080810314041012014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 442890755 1250 442889505 442889527
    0x3070c0c17190c0f060201060504110307050915090d0b2403030f0d090c061d030309130203040f0209160e01080c0901030c0311030108100b18060909150c0909100b 71
    0x20b20240c28024600c205070030343c0c4c0e81000809030485a2100740940d4494900b0005413034540701e004403010450b5801461403804d6440249148591034074144a8200b0a048880c0f0541d81c0055480c102d101030000c5524200e9800e050b003400e07804403400742d0007824012240e60440e0394601d00c40c51158018009609005010300001040d81102e13100702200303a40d40b96060003081583d484400100f0164840c0c107802e064001024040584440c0d0030f90180c0c0c01003003c03c3d6075031600441030342500141c580041e240e440d02e207800c0070141c2c07a404029500c00c0e180360910a46031051002108900c83c940c860320300c500104001569080e03401c807003030000c0c000140074000c401e50094014107050283c901e000030300708075282980d0a05410a80000445501c0541c4840020181d44500303002481c04507500c144a04590700d40e031019840040409028000074008500c011104110414004520b014074121910b0f004000c920950801c080543c1b00e442c0080104480b581c2141612003540c41403c101450880c44c1d0315 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 442892005 1250 442890755 442890793
    0xf0c0905060307021f0207030e01090612020702120f0607020f0109080405060c190c0503160e161209050c09070807020a1e080c010c08220312090803070c0c17 69
    0x7064040d8000c51521700c100000101ca0300c508034029a50068541d81c003400e0040c1614610b0a1040c180000c1803000c1c0302c0d031608000b0344c2407580c082040242e650402031012030702c1d14a800da0721a101e8454031034001104000030608610074225a8200c4d41608420132210342030715002180541203141c1000203001d0390070800d00078200b94001d202101c1c6400d6108454a014140104042d90101400141800549000d010b0031941c0081c06498001e03282c14100c075030305040d00140c04500155505003410041078003400c164200f141604801b00254442030901a80703400c00316410a114450701800580950302450949020341d4250340100244c1e056903454691040e0008021150300c1c2e95000d181c2c000848000041601509500011a060a141070080d00903c0064660030000c40040c600c000102c052100751900c0640600d415040750b4501125000104176122014000d00000020030620681110102c0c0d031461040350322006090340c41c086100400d40c0c110b0312003055000b0081000081003001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 442893255 1250 442892005 442892011
    0xb03071a030a02160c0510030c1d0d05120c010b0108010308192001020408100e030a0309061d0312180304091d0601030311121204020103021e030a0b040f0c09050603 72
    0xb01c0700502c4e102c41640d041c0c2e94414042802c03199801c1300c040c1441281841e0248040915490900780f01c0300480c0030010701199252120040308401d1804079440039600d03440c0d00110a50001d0540707007407241001c0780c403540d0350180d10301e03000700c0d82045c0c40c58829500c05d9600a0407a50002e51590078801c1803031503220000c8080d408a010816018003440c41d0711040d141d402c1024210b08001a5100e00d000800c9040100d1514400001c0c1e1501034005040381002c030489404003a28940002e5240503071070000000d201802c0700052804031041b424030b100070000020050984208907414840e0350b07000c02401214542c48070325489400a000130400c2c0c158175088000b406941d034000183c81c03080990f007d403804c0004d0f842a800141d81c4101d00504c458244240007035031601f030301154900000003048540c4084041d00090400d0360018000075600440c2c03a4054508045004840c3e0f0303820700e013011001070301800110521070303450900c580303010300014400c03880207811315200c0400040c83e1104101881d0002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 442894505 1250 442893255 442893271
    0x50f0901113313080f13080102070c030615050105160501020702030604030512090610141f0201020904060b0301050a27052a030405070519080307080306040b03071a03 73
    0x604000c0041a030400c1204000c00b0b10301d42c0c203070740c00080d182e02c030301403102d0260940014051805800300440c920f00c0840e80c4500740f03022044d503101115014003088240c1c990007180c042d44003191100801c0314444040c03017164040ea4041c02094003400321000424610f2040e031307011442c00c00020b0b40b4410180c00c550b002c103003d540010b003020340c240c021074102082110110001040091016400b001ea0035000ea041020320b40100800d150081c0060121201401074014011101c402203400756280000001c0d40310000410003c41d040324400030b4040d410640503107128500305400890300e50194000d60b4100c40000385480c0c4407500d0100d11554040c251500c1c41250300c561b68502c1207a00c0e040c01003d0061020404041c41c0d200f4044004014400c00302c0c4071485144200701313110201d240018050306581040f5800c2c0000031840079861041c1207640c2c8144507c6c04081a80010301c580000514407448003a6003c0c00312400e0002010b40740c0401e070003001b982401c07604c10a05010914400b0316030180c0c030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 442895755 1250 442894505 442894513
    0x8070305280906050408030405060c0301120f0c170a05010e03071a090316050c0109150e01181d0f07050c030403030503070c021c02030c03060717041b0b04080c01050f090111 76
    0x603490760000d0f03e13422074090f0381c003c0c0c00005000c1000020444258800a038820490840d410b000f004008503014101c040c0510300291044414480400c0c800c40041c219600d1114030446420b44480e1103050743c89090390f49500c0c0c68110989408080111500c0e51707400018508810a00801104003950141c00d20201c2c0c802805032244500f140c0200301c078020301400003001c507900f520000401d07001c55900f1081290300c0e6928a21000341d08071a800c10003610909040703807809008031091400c451258082c04001c0c100c0b2556101000d4410107082c0104000d0b144082c280d070701c0500642d85407044840e814050743c410401000800d00c15800b550b00090946403101405e04540c0014003403100101080441440150119045180c1002807860301127054000e003090b4684901d01030508040c241d03d140a05c0320b0030700010100040d8a6800f096a40d00388103e8000310703110102c2c84003c1e0024000c8034000c2c03142072800d1006601078029a4145282600564a4110390b1001160280c0c1c0024115406201e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 442897005 1250 442895755 442895771
    0x1050a060e010f0b1819091b05030c0c0a150b010e0306071e0311040e0f060906060301140f090405010b01080a1103180c040509031c06050a090c091d04030807030528 72
    0x70700c01c001e02c5d0540d02404140c201d00c1f8100303001d550880310482009401070142494500b1402d400005503540440e400e100300383c940001103002c178148a01e0850081080c501103840f41d010300002da0040001117800c5e62501d025140d8130b000e243d5140021740304000800d10003034100e030701d04017807180c1e0001443c2d66140100f06100ba0000352242030300190000a0600c03004000c10042e03091085400ba4044000c65020303409041c4140803404510041c000c800d460600d066915480ea2103000c240360f4612006040150302e0316141c14118003c0c0810801c00e80000e03080380200d0308000c078900076900b51103c2c07015407031b141d9241c5108011524805414103511400703500d80b41c0710196503500c9554400c0e40b010b80a1030703603841c40c40942c0561204a40c62400d48501e8408288800e4440840c8403042d01c920b0040090ac00c1c4800ca81520307041d800c0d0703024010420300742d11004c4549003842c03481409030f8031948502069844820003502503480441d4a0805192158200d10304200004000c098501d03840300b0000c2c09403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 442898255 1250 442897005 442897009
    0x1703060a0b0c100f1a0111070b030a0c0e0909030a0309020a0302040e07091d070902030406062301031a100e130204060810050102010204030503070b060613060201050a060e010f0b18 79
    0x50001c100505140c0c101040311510415a0f011340b00d00c20503100800c0201c2d4030182000501080000241ca0400070700c1c080a0b100c1a5017007240c1400343c0203d400305511b0303180c0301c1d1104024001a403001000101306402c1140c060400910907401400004042d40c100701e40150100d00501c02c0c01e41c20703a409003404030000b0158645218490381d1510201c0644001c50400c3c410704160340901c8035603d0051068000981d80300d40100b000e0040d64141880035070b4075211810600b000d0110360300303d01c00c81c880c05800207944028a1950f4140b084003a00c09002c04049403422107100710002c40722079084031a9950550b03503076105040e50034500380000c1c003505020030000d01c0003003241c1180d0010340c0815440d0080c081160f80f682c40d0341004000c00d100039440e090941d075503645c481c044c0742c00007800c200e1b8940101d54555102419254021920241d200303a49a840c0c82c000e020309411b0b100d000101c0e10b8412701299665031110304c0c44c1a00c91035010b0030321042c58036902030302c1c5903c01c12040040c10181d10b81281c480d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 442899505 1250 442898255 442898257
    0x90301090f1103011103102702040b03070e0405130303230109060609290d140a0f0b0405040b130302070302040e030a02060a020a020601143c06071703060a0b 69
    0x500d0003810310703840c41c1c1d01ea6403e05007100c5004175100c941c18400e008114040c0c141240590036607080c0204400030b0800031007942d18410b0001c5e40400210f00100b4042060041e050185114452664884020101d01d109000888034217803550300702085c0301001080400d0290f00403003c0000c0880b40c40c1c08030a403150100e92105807c0e0032040d140c9440304000c2200c143c1c0301888101034482c8803000145150124041c1010790f0400c0e45512003d040130404425869080d071100c9a401414800070041d46070485410300140750341103890326020310304407147c034150034a0300c10607100796032042c0f564003182c486402d2201029004038003101184141c0602000603142d81c017994170516100b000864881c01c509602a051010040422500b548103100e1f1a2184c0d500282460444034034141c5600c16040160100e801c01e21058494164020710501c2c810442d10b1803090074401460000664480d070001c40100010b5101e42030000c0c1560090740c034203400880390700d0015900011700074000c0807c0f0382e44030040046 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 442900755 1250 442899505 442899533
    0x10c0b1e040b07120e0c0111070b0307020601050103050a020931020c010621050c060901270603230135010504020f150a0f02120403061a010e0901090209030109 70
    0xd200b00382007840059a00501d09a803002100401071080d0303482c051136141d8552402d60164100100090b52840503c3c05020510203000c0c280003a659903e40b22074081d580304020f12503540000e140c02c0010703103040400c1c0300361402d2034001040040024407115a00355103d000c1504043c280300c1880303408100340010300c01868107001900000c500f5510301002080c41405610040c0507000d4140344040c00180041940c00c500d0400b1500f1503140c200400040790810344d154004181504418402d12811009582040c121400b651301400042107071603500c40c5030000e9402401046940400500042810404000402246802003a42c44160b15003105900b26109282c40301655100706000541c207046c80c00c1100c0080a5804031070200401201c10f103140f20700110242000141d00ca52161944240200c145c0350b800801655100c0d0f4030b070f0804400511008001000504440054101d80d50003620140ca00b040010030f007003000da2a01110b1400b96024800d020341c155642c1d042500000c0d2020010700b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 442902005 1250 442900755 442900763
    0xd090801110712080405030d02040e0603070603020c1f420e010b0304030314073513110a0902120a05010515160507030602030f15010c0b1e04 62
    0x50114500142a821162160003a49a0510411600020811040a05042e82507603c1c14038425a100d041081c19401969800e98405000050010320081220422405850102e00b03a4100c80c0d540c0105404070310914260216681064031582541c04070080c0c0700034100740ca81000b2840440d0030441401c0420314551060340c010240014012407103000308119a5002441c980c01d5031f00303080c00001b000800051089950f1808000b00080826100e82c2020607141010f5900310b030203040c4110060b290814404410340c040c0011461040150001481d5208002d00040300342400d48a08070301c0c201d01320039210240c0316461840c4000203503446081c800c60061a00d03080c010303100c024062882207019400303081c05c04c1c2d4900b03050040c41166208500a208001214003441e640c400c3d00003150784690101710090042d0007042d0b4000b0038494260000c0d4402c0806101d21b108070364509961180c24a03101803181e0008901e40c0240e00016000c1c014140c20080d0400d040c500d58508c403102a00410044404031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 442903255 1250 442902005 442902017
    0x6060d1406070207060f1403040b04060212090d0f020303130803040305270f0409030e0112140f06030601080601080a0320030a0e040509030a0c1506033009030812090304080d 76
    0xc543c1e8400f0440c6e0b0030101c0d038903200c4080d1210495955450102400c084c03c1d0000078004207007040841d504440740b0048042d140c00c02840c1800030692982c0b01c02040601194581c003006600b00d10120032203228122545041c1c020800d141c840c0d42942e00020300840c1842010010f81c1c1d21800d501c05495020f1225019011522203034000f030200b05402ca18219001c1c81c180440040004d40080b00c00d42c0f808800c0c6040101000b0200341d81000c1c20b00248103d03c0d4102403c2030000c00c0d2110743c100e611406051f4219852070760b031401d0460399040309100c1c2280c0d9421142002c4d00103032040d003a414201d0010040001211f840c030050314195484138040c400880c042002d18142d07400d04d800380c150b000d1000310141d800c101c0164005810203105003001030079030382200810b101c13010166001001842d08410064080d0700bd50024540d0300102019107107000d581002c007078107541c1c80381ca16007040e00c1d40304000d5410240b03403a480d40d0443e040500004c0d014003041c0b02c0070074400400c2101c0340000440365110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 442904505 1250 442903255 442903259
    0xc1713200114030a15060f17061c06050627010e0405030409060b0307020601080c2103071e0b0c030103020d0318050310060311060310030f0c0306022a01050906060d1406070207 77
    0x5c140724a116600c42d000384110070f00320b15013140c1c101e021030180c2041416450070030740d51140080c0a41892034241d900e00c0c01400313108024011a41d102d5031040005941d0b9000a1221103000101c500d80d1a9020100c03d400100510100f0780d80c0d01115002880b41d802c50303050030f490b8a0a84240c070303070607004403041c07090110402148d9a0304200032030040050401034040c991444001c9010700f41400c0c1c884407100c0b001d44132140fa500d000c004880c4216080b001e45410704c06402410b60346840704031029103080b00f0820124080c0581039086030304030381d40141030f00e41d404c490313907010307581428200620002c891020b200080d00e078034180500c2c02c00c2058140005449402d500d0004624000c8941640c05408203004000c0c01d0f54041a210041d01e4100340786140980540c60b0106c90b944454100520a50000c540311620704405001c0700c0041a244d462800c4000004050900f240c9048450341441e40c0207402140203801c210a0039150300e80a0000c2400c85100c0c1c054651405c003081c0c50500044e81b00e0001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 442905755 1250 442904505 442904531
    0x1260304031202011b0f0c0f05061617070806011412040311012d05090f07030606060f17150a0902070f1109010602100510090c1713200114030a 63
    0x1541a0012458005e000c503603064650003003411040800b80c2061000c241010010b101d200e102e178094842d480402c0318040d00d0320a50103900c144100309400046040303030030300c941c0400a10080314407400d92582c07601c029031340785001199001c03100d610b0550030050420500d514440c1183c1114800c50203501c3e1405481c224280c0140ac6549101ca070600840c1d100b1003002441d2926170307030408a070140311340100c3d4907150421124145040c0e810829614403440c4030000c10081d0030f802400445460703407240d43d10244c0100003900c455401c2c400c0340750701f0f29034000001c640c2c0e5546866a04c8101c80900001045502c0312000400c991299005035840c0003c000350004004000c91403000840c0203441a0085524040d4040e40d41c401240c50286142c0d01c40c0d000401d4281540003000091241f00020b0140e002c1c0c401016200b01c05d440b8000303841700300c181c00042442400424032040355038040219803661400a07083c40380240c800d4042810800c040f00c003245100c81c000f0140d4050100b014000920410381c1c00c2c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 442907005 1250 442905755 442905761
    0xc05030307232d1c020a030201050f010e071101060530010c0512090a0b0c18010806010e09060303090a0f091802011b0f0204020a02030409050903120126030403120201 73
    0x30782d0003120b03400250340240800390841c05025503200911070300c1451004000751400d140303c110030348403800e144240b4141e035181d00140c0c2e40c0c5124041e0f00204040d8880769401110030009000703d010340142032002c1048079100320301901440404400025401d502c5200181e4500c40381c100d403113400190715804941d540f0707549800340b1041c042000204002421801e0142c210f01610102098142c440d00006020000c10300c00221029409134000c100d0f4905032020481e00d400000340d42c0005030301405c45540b1035026030f40c00c03400340b48142c440c0c51806441070100001558010300b42601030005001d0361115407280365000000e44107036200f182074242001d0070003007140c3c407002840810030340074103502c4050303600904801c00c60710200c4104003550419050a000001080780029003045c4001109060300e5401320160064508211091010351217800d2015601d002b501034045195401d0401000404800f0104d0798100c0602030035288030616440c0c0b5282107400540c001c0d104000f602c07541d004425820300c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 442908255 1250 442907005 442907063
    0x1051c020a020c0a0b0903120d0915050403021c140a030216081e070b13060e060702070f1409070522090209040605061303110d02040e1605030307031b0c05030307 71
    0x24507503411b01d004e080001c0c0d0f4502e1240d4115035030340d4001840d401c1009041e0444100300790032020900c00c60310100ea54900502d42210309a005000d201d6004000c1080d21103c0c418981ca60b50310341050040d041b04102c01a40040302c000c0c01d0503403c000d0035011402280074000120b0084203e01d48903072003904000f2440c0000411000c100b81d04102000020b1520041140c00444122030400f42d1005454420001c00c48480003582500c00c1d1002c000b001c1d980004c3c0001075503d07880903200d04940c0e40d0b01d8940e40b010703000080c3d03074040712110004107030510400240461a000070504a02c034042042103102c44c01d65600b051620b5a00000c14141170706260140c03d0040a068510a1904008010403a400c00c07550000800c9a5006a6521515540c0d606100340041c0c000f802004401049000c2e5581c136601451032045907001100c0000b868071f40402502c007280c0c1c05840c0d005120b1b200264200d030450106104032008020b150021400f81c8040020340041c6128040b110140103620708188000c9003d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 442909505 1250 442908255 442908269
    0x60d0b0f040b0c19120623033304050a020a03061b0914090405070f0909020a0504020901050316170a020a0914060f0d1410090c0c1101051c020a020c0a 66
    0x130010000b144181400d130b5030040d95546440d02c0e12804e8100301c80003400c031690101403104030018a4003401c0c00d6240f25402801811802c41b11030550b0b0110300e006042e41e01148140040d00001000d10111440c03022981c071910810070385001200b20750000d404170541c0e40007990001e0303441c0c402140c19000303072084003501e03030141c200313105101e25051070f0040a80c3c40c6941c0c3c9008021480204042000401004000d0301e403615003208410f40707644c1500002e101d1a1000e0380b0841c0211000107180c1003610898801101c10ba484900c4c66441d041c01808405514102d40f01b04404540c1090b000102c6c01708180c010001040c016964804641004141ca482904000507a6843c030003400819034a0b40121980c02c03000400c0e40d62650f5866010000400000079804007070151102007000f00407920415205507682401c00b0052107040d50000c4401604240c0003c1040307500e006468406e40c080d50240181c00604a1a1080a071800480c4d0f000d0781c2040c3c40807000359201c1d800e08413961408035203050107080a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 442910755 1250 442909505 442909507
    0x9062b05240609190c121b090e0103080304020d03050c01020f0910020c0307090b03031c060518040b22062405011409010302070512040803030103061d0c09060d0b0f040b0c 75
    0x1c1291401c00203040b9400c89a082030ba10210740500c24080d1b050f40404540b02d4608002c02000044181c8408081e0442240000d100c00303c04140d0a0314400413034143e83d0482411802c4da9601e07400c0c000d0b5410300c40b07401d90500109002101000600740000c101da201480d8043d5200c110320380a201d01e10445070f0380794055400c00d00080070140c134001000c2c0c044174000e080200d200b03200800440d0840c403600c00442600640d10412030600301c0303075400010860390152030010350b420303000307440c00c12020b010f0300c004051a1380340010902c010307418000f01034209158081100000b245075100802c4400020b485060300818004648090340e800450320010003003820081c201c3d01003101403021a2099a000701d060680c0418024140b060820004045882100003d547c55490380c4144e44e1b07075002480100c4259091110041c02c0c9071498400300c54015111005140c080c208004028040714010600c9411920040f90203001c28004c8610340c1c0118260030f20440c10b0308190401c581c0801d0020040081050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 442912005 1250 442910755 442910761
    0x20a05040c0e010807200105090f0316081c0f15060c0c050409080903120913090201020d031d010908030f07030b0d15090b0109020306040b09062b05240609 68
    0x203085501c2814440c0246030040351a40d0704e080a1b11031500c016004007140a80b401645640c1005501160058052a04643c0c00d0659040104d40e039100303520503058040d500300e0b00900001e000c0c07009045c59140c000c0b004019449020b1b90720b800c8480c01c1003a59605a21840c1a0b010034a035240003a01801070751030a03102c6000c15031103021407503040b4840c060103039a80340905c1c4140811042030790032050f001000d507011948090b082101c250450640d5a10032420301001840d07440c0ca03880b8003403807241d047c2c000e000b803260303101416001420003076500c20080100341c00c0020308407c20701c50410241c0c03017031100907100d0801058003000c040008061506051800b030169010341e803510b20041c00303075500c40d80490b2040040261100030341004c04008281950800003c201d0140c541c000e180308110680f410003015a0782e1041000b80c80301034401c9500540d04403110000780e04e026580000e521911000ca0312a490160f580e54036112242e10031405200d5001c0d9400010100c24130300b250000030498068045007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 442913255 1250 442912005 442912007
    0x8060105010c0b090307050a080a02070807030312020c01060b0a030204090f060e0f07020a05070303030506031c0e0402090619030603021e151b06041110080910020f0706020d020403020a05040c 84
    0x103403500002801d800e0f0044001070b02c4403010011a20200d40c48800c0c0d0707905005a1410294541000e00d01401502503014085158400094a0000c6941665074850340b03400b9859001e0095010310100c480954840802082d40c0e45954024200c0500642d0010790321844c4c0400c140864030448880d103006070402d00108403100036540555001008480701e454103880306c0c4c6040e4a82082d2140003440303030095030800018150158031452042c00f0503800d8801c020142448569455000c2c44032402042e40668642c0d0b040c103040d405071100c0c500c05460f0b03901c3c1009d01070007482440708010403000043e86824040c011070522880c1001e468120b0760300060300742040000078540003403100c0b0a046045c004103203410490345c1203984844640403c019907089007802e061030508400710800d094002c80d080c0c142040103030311880485102d9031500c2c0c05800c240104c4140300c006584094503500c1c80c03001c10701001c4042400d51000304011402c10600507604c43c59407041c07200720717503e03903114600c151314101200c043d003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 442914505 1250 442913255 442913267
    0x1802070f03050a09270606181a0c01020c0106050f011403070e060403080c07150e09010312031b0e0a051c020103051008010c08060a0504180627030c06060806010501 72
    0x10340d6250620036126580d4440455043c1590350100c40c0b214402c600702c02102c0c00c07802c0d11403449107117600c041c041c4a8480605a544600c03004d1088040b1240c1c040400c50100d035000311001280f500e81e0b4240c40c1c6108101035509a80080b0701c415600d940d1000100800c2c9400d959000b4840b03000c0c24108440401300ba2021068000100a00184030344c018008110b81c2c2d600d41242c0107107601c03012181c1c8500040e005240c3d1a580381c0503640c046144c42050f003c400340a02000362441c0b9000380798500680c01c2d5910140058504100201816103c01c07440503002020302c4007060180c40c0b03640d0650020a01d40c01c001c000905a807000b402680d860400c0280e00103082d40d45681d1940a0030040740d903403a084120108109540c0c0288245e500e088140b125550b030001106d4041c0310704444c00d401060300d400402c821106180344203215441499036450002d080b680004001d0b0010f030000315298a14090088000400500120300003000c042051041100358800d940180c040310005048031360400c0006040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 442915755 1250 442914505 442914533
    0x10303050d0b04090f0f0b011e050f0f0402030106020d080a05070905010c1a07050a0806060a0507020d0c150504031401150501050708071712010905060105070b04050a0b09030301180207 81
    0x386030340760b1800342001d0720345412034010b1360340c000202c0188949a041010300d080d00c040040714401d180c0c1c400042c80c5009040030349142c14842004c080c20522303040c1003200303000c11680d8150b0003055182c0e103802e585c1e07100d00c059802051180c01400c07840070452801402d90300010b18001e91146454207202925074011440c0054074000c1c2481d0541c80150f05140c59803c641e00344440700040403008001c40c03513600401820b14040f90b0348035180e00f91aa202005074074014800e9100000b0300c1440903030054500100c3d0a40540d00072906200750a88800121001e440380400a0010400010b820000c1020500c001c0e04000540d03030007000030a00c1c48004102d6040184612810072901180900c1070016000460302140e41c03014103050b40c00f1a82c1c0501007650001c12a13800d129040b0f00c00040e00206a008141c801c680595070a03241030354035070f0b600800040c050000e50b4103114054aa0300010000d8062038003e00840300215240d600d49120b0061051044103244000ca0040c41403400150703651550f958 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 442917005 1250 442915755 442915777
    0x203160b0402010e090703020c0c010203070b1317030103050105070e03150c0f0c030d0504060c1704031805130e0d0c030e1e0a09020703020d1412100801090506060306090601030305 79
    0x2503646960004950804000001c2030748042440140415660103600501d188480d51095810881c075440c010f9841e401482030192407000c02c080010001042d0191101c101480750341010320709602c05443c041550000d070401c41d69a075403803003400001c58204813400c9080400b24014058942d070f0325000520100098115408d001c008030301280d142c910441914045441d100031251240c6003104080302400007035900756078131407406e040040c080f4443c40c180c1d5200c50b500e02c580038141c1c0710360390f0403200c0035050b10240c540c1a40c0e00c80041078030307a1000c110080d1000401000b01d030b9080c112841070b0038450002c2548081c04440340e0f00000181d00040d1f02841c0c1c02d000c03200c13201e854640000fa01e408250700020203510110300c110120b09a16681c0c0505003890090b8200c0340515000d40050318888424541201c6441c0f00340850340164011004565004040004071500075070b0700c500c42425034010201c00c903600d410410802800741010411154888070b00d034007c041a51440d20040c4c40c920034245e03400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 442918255 1250 442917005 442917023
    0x7020f0f03010b030a0b040b070f0f0c050703060e030a09170d0e06311e180603050d0c17030606030c280c12030c09090e0c0a140907020316 61
    0x800ea075801c1d4840007040e2409001d585140c4103d2070302401620f001c42d803c407100c00c42c100c040b6500c2881090282d544540a80354160395403003e800c1a905403030507250481d190f105405000c400a040340c01100c5018540100454480c070035200d000d0114059500120040c403101020410500710014103040754880b5802c01308075a240704000b00d006031003850b0207030f0000b41e034403c4d4002c146016482c00c5174000011600c132862198407080a1608071034080310040801c80580300900c03520b140440000410040514006500c40c0e1340d9417044c1c03c0210586481012074a11002c100520549034001842009840e483c00d1440c0b400d200011480c0c00058020000440302043d128609094201c03030f5840c1545142607828200a070340d500a00090a404003100c0d045210401400703002c1c000c0c00f4865500c0056119030745180c1c140a8124000d1100024038007032889111742c03d2003da02d954144201804007144921511460501440500340e00902550308540c0708111009100c2c1c80101040801c5920203046 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 442919505 1250 442918255 442918279
    0x3080606090d0b011d070216031101053105040203040203070308070c030f06050610030b09010501081f090b10020703030c020402071112060108010605100519180b120a0207020f 77
    0x1090000c03094040003404a80d2000001c100c413000c445ca4450404441c0751840110360b91004100e80710505044c011020210748507050000860501415030329240c1854800c0c02c1198106450040603009158500006c502da0340f200030903440200100050302d810b807800e52440c140f07a4040b136a140400d01c805450074001280190402c8410002b41008607000741c00307031007010920304200e0700801c416110184a40141c140e41c40071140a4043d612400302c0c000d1a203045a8a445e0064400310740c010f1103040d074002003c031041210320004040c1005054100d400103461840c40081c018030100c01e0160505540c004401040065400a440b00302141e05030703005603c8582c5460a1040c0500c5941140d501906d121210040b80d08001800d03412508100000c0c02400d40e510300b4810607050302840c5400088007000f11852240708854801c003e0811490f2035038420a0034540500001125088021240c00c005040e4240402c6c40f010b031604031a50003011841d1861351390024400351b071a850142d0007250070351030f8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 442920755 1250 442919505 442919509
    0x90909051c050f070602030703050f07020d0f03020d14010306140f160311070b0a11042105070302060c06040b01080106180e10050c2104110909030f0a0f1101090308060609 75
    0x10382c3c5010720305000240d00c4078424a4120042d40080350460002440c2c10001b540c2c0d205120b04841c0540b01640240c80c0360b080102c02182c6a154000c4500d082c190200300040b06c1010a204111840d001990092200e505604d40345065805a0044010301004101400315000603140580e40121009c820744203500142c14091740a0005580d01c080300c0c05001c40c601080c840f000012510030fa42030042008038178454030800c5542c0c040c50160008a44040c82041f0701d00c1019503030710400d14095000c4070840740e0342e41d0000b65164002081c09a05407c80303c240320800c007103500907902600700c0784000d20003035003011541503501c02d903030640090142e00e80004000112003440100d44108030181d017072006283c503407802c500d0b07580800f850680141c0d800c24030b002c03920401025580516400040f0b000307038007500c60801c90904d5025110031401d0104011045226418400401d025a03068480c140c0700c0e0b060b0100508011400494004964140300c800c00003c5d502c00e860300e41c0648220303101900d80e042000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 442922005 1250 442920755 442920757
    0x60f040c03050303010e011502070e0a0b030705060d0236100e040f0e0c040908040311030f03030403020c0405010605090306012601062301110706120902031606090909051c05 76
    0x1c0058a42e00001002044104003c0006030603105200c10602024600b00400c80e600d0355984506990310804001182c80100284c10041a20200a0841c1c010988890004080f98003c08400b01d609a002a444080c070041e103480000840710481401c60004c20915a450020750072040c10344919440035000d015070703001d0b0071490700e4a20081c104020000324410a6401002840c05008a03441400710410301480c050241c1c43d0600e0740000f0b040d007030910315500e5074600c44560041c603901d0300485c02e80d65800740c2e00708042e61142d406903005108400740b19050000315101a0006810080d08005610054070001281ca04482203021644c2003070342c60300c50210301d2602d01c81950110f9400e100e0005000012402190f580c90f0313480000801c89d585440054031000d4284514125540082108000c05401040e9600f07070640d0100e004201203496600290504186c072044080341e02c840041402240e511444034005454400130401c03180c41c058403a0340d40c4a2100180c1032000c10844c40fa83c0341d1520840c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 442923255 1250 442922005 442922009
    0x3040e0f0a14040c06030501080c010507230a06061d0105030c010c0c170106181806020a0207030f050d03050f0c22080d170603010606050d0209010c0c060e01020c0d020102060f040c 79
    0x18503082d032a052901d80102d5070585807107010700181c1070800103d41d040000c109120000c1e0140c40f818940503141d660071110312600c140d448039418203000c41031300e425818000500c0310780c0305440c0000c281e4109581086880f464610a010b03252402005002544000441c299044000d0804082401c420b1924210000e21078119010350404030746409824801508110103881216962815581031100c00342c0880742d20801d01da502c82060303985480850302540c0101000c030800c3c4103848141d13480362500030f42e4880840c41116294010360a180c100c0307a15100e2160000810190070059040c10b1070091501d0003280f498000d04542403444201100c0d031040c421000381090f8040e03411403200d001029098140607900350840314440e00010f1544d260620400c0300b0303614261511818984200380020094202c0170181c0d0600c40340d4140e400110352141041c80081c4056a5141045124200024107010080717400900030782156001e440145c0c2c003c901c1030f80c020203581c0001400c0d503c50405131441c0765a6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 442924505 1250 442923255 442923281
    0x903010e07060e0a0503010b010e06030a060510050415180b0f0c01090606240207090b0f030109050606010e0402120105010e130606230a090608100807090606080903040e0f0a 76
    0x164400042960f000700152007030103011640d000300d407a03a80080c1400d0740d20780e9210500207000c10010750071614010b4051604100440c500140007511a004600f00215045070200420400300c1c04104662140d019003150b0001c44c64409a9a4402b04401092146501038601503850103c1d010312000700200541e020400054002c3c0804015030510350004d00950084c02c000c0400c2001d10000072440c401c074841550560b0307004100756450254032030000c048003000f140d1700410000c1c4d03c04550341c09018029208e4056070203481142070500c0090529031055402c2c902a40c014480c0a000c1616802c205045813802e003000000142503d001407040318285182a4089150160100d5070740e0344160502003041291002d800c240010140b00251340c050700114000045440c01c041c02514415a28503401018119010110b95180c030295802e0804581040110a94031003080000d42d5005000580000e2800c0c05586410306040c0c40110382000100300311281800c40f80412180d814503449081d95202e2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 442925755 1250 442924505 442924513
    0x30e070909050c0a06020c011805031606080a06080a1b030b190b0d020916140d0219050c060703050c04030b07170604020c1b12060106050703091e0b0903010e 69
    0x21030059200070a80840162102e101d0010400350904100c84541d007500c16075002000c0300e9174a03400440b2018610101101d80315400c00e400201500c0801840c082c001c0011003804400e82002d000424041c001054804840e040842c10421914080380b900485600260615a42c008010b10140e80142d280d10040c0140e0080c0300308003081c0700b00410501c01e0a2007007400e102e00c426060400c41840f84401000c0c0d480300c00c01c00132400d2801080301031070030380d0b03c00d081103101c00e501c00b81101c84981210354001450b0750006989040550385490060343c1c064541040da0030708110407041552044010800c40a1568034000314180b410700700140d500942c0d0200c0e61a0b61803074844401800c000b003100990a62440403004652246064026503c0701007400d00204403074943d52a904030b00c0c010900da5181c001214801d660141e07641406024081e001c02e889055a482151400500d01d030340b541e21070107040d0014414568000700008a4004644403010115198138085000a00400c020401489180310b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 442927005 1250 442925755 442925759
    0x10c081b030c0c2209020d0209090d110d1e02100f02040302030c01030608030a0c03030b0d11090a06030c1a091f03140c070f03110105040302160b090109090b01030e07 73
    0x30000010180d0a140c501590403603c40310050216070b030300c2c003c4800103030000c03410704080c464803e034440144540000c1c0388118200040c6c001c81c24207001070311000f03025008034520b1000707107030001c1c28500303450b480c21f0007004160080c000051080400c40b01d01050340100c040701552440c408c208140c4c1c10b6889050420810295511400095000d44800c0703000303014014165182e58024461601101c030541d015600e085802d81c01211400c05200c0b00300c0505a40da0050446525080c1880203803030702c104503d80c800d8071880304214250708000c00d2841c103035003400401d0000403400441003013200c2004c0200c11591f42858100141400b4103600e2a41100310485c0e001c2000c41601c0a050755400c441c0c03003c008405504a08804400c421142c0c2080300400700210000581080304801946000e450041000541400c0b01400e5038001c0c2c41c141c006900c94903964180500e2210028010f280017510103203850141e90018185044078441c420080342e8401c1800304a03402a001082034449071015182d4440e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 442928255 1250 442927005 442927057
    0x50c0c041d16090e03090d1202070b04030b0105030724140403060f050f0703060308190905061305210a030c02150c071403060606070b0901021c0207140714010c08 71
    0x80c2d284070b81c0707100d24101000c0c4001014080115081a00701414440aaa03402c0d00d0f120808a00300d20310b9803c500c5805400182c0d249003030084c00c040c5224114101d8254501820586402401c0e00089071200c48030180010101810b9801d40340d070303421400c10310703404141d03001c0c4076015002e150720240c5020304202d01d06940100e60342c010745c0308980c00328680da41910340718030850032641640801420203500704500c14003220f030300c81074104c800014a81000707400d0711703040410f40f280c01c0303040071890208070f25109103c41d18109040188240181481c01810079651154a80d0344002030340c043c2c1449292a18401592901c000111840c848070307071242d030384040300e08100f40da600ca1071290300c040800160585075180340c0405c4450003001d004007160704003021511070302d051400107005009599803c100d500e03542c40100203031442d000d08289005071101c49608100c0380d01030355610801020340186d0007d12195000005488000301c1c28603003c0d00300b044600c5c001040d441603074201c00c282491810002108 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 442929505 1250 442928255 442928293
    0x14011e020a05010c0918020f040b0703020307031704020619020f010204080c030f03030f24131d06010f061d09130309080c01021c1e030219050c0c041d 66
    0xe5102c1d00003002078807a42e460859068025005480c801840032200300d4602c003158018180034211841d00340d240680e030780c101d008241d00c0b10108402603000030444005054108115105c10075407a1070414035803400360700299032031043e4603c100780e496041c1204405c2903c2005244a080762100003159515125440c43d940c402c108248076109104458510014a0020050360300551000318a42040d494040e9015502d944500c22075070b41c010048551103903541c440600544411541b00006810400307120314900d014800c082011450b441840100050a241041d032000c40d5203510b005030111710200d0702d1005210701407078910b0f8055041710501180d1070400c480340e0070a5120380c481d407206a079500500da807a00e4055030424003503004544030042c810041042c542c4107072107524080300c0e100d2548107019800303083da1f030100c4c000a40c04546160000700b0442e002a0f24015414514109034290583c1aa00c62000c44003501a40e00c81c118480c1410010ba034500000c841c210680381c01c0d6220405440305 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 442930755 1250 442929505 442929523
    0x212030310080a080306092e0509071e0e060702040906052203270306050f04120c020d020d020d12020312060f0907180b130810050c0414011e02 63
    0x8031141d41002030700800000d4900c0821342d204480c2810342d07680c00e00b0049880401010308800084103c441600c21414625035902680103401200201c0d00708014007441d1100203140d03400703002407802c01c0c610209405c8003004041c0b01d40d04d05840f112840001082c1203000da082e009401504040101040002c80e80000e07110302c10041c0010100b14224080d1400699806c10140100d5008100c81001c5002400b9015082010f00c0701c00c002c46540740d4400c2c0032108102e40203d00000090144001c020348481d0403003240c2c001e454500510203d58001070001d00c24088000d2061008180745000c40d181d540c20080c20719001035014810103902da038042c1d1a5440021071b81014410040001d0302494a0425024903071000303841c2c00c0e001ea6480e04140c0e040d42031118442c40c1200200d80000d0307070180c50402001c80c0120a0700505180307103000741c011320300140c05403800402820074082011211401d4181c408a40c1d401600e01c4004481c0e000590b007840351600c01518204400c0640100765400040280d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 442932005 1250 442930755 442930771
    0x11071103060a02040506030c0309030702090403110709020a120e0109020d12110a030c02040213031b0501080a0c0c12140301060801171c0c0515010602010905060f010b0405090403050702120303 84
    0x70107688074104003040340b28a0060907030150341440415524140d01010355440300c40101180d03e0300c040343d0000341c0c250700100c81c01c5000910b19201101850000d118074401062030721400c0d82040d02204014140201001c181019541c4d208200d03010100250050592241c000d42500c4024010b41005003031103e1040c65035011036075121500c03040700000504c0b80d40b16601540d03011800011039081002035408141080440c002c2d8020100201d4001d0b1a4510035801b0142000a03181c035000c0050309840c001080910114034040f080c500441d0030000508095902c17140e0000d031031504510a030b58501c0c00030380c10004c0e03480110002c5a010b411107000e905940280281c2e089146c2c8032403c0965401c4412000006203000b10381034120345000c0c5403404040361040c029100c18001801810f000c21100344e1207040181c0d140c07401c003014080f051000503000141007518451640c14000103074018403ca200347c601900b1214002414144910207440c90760350b000f0150b1800c58203868420382e030394000b0344280c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 442933255 1250 442932005 442932013
    0x10b04050c041a131403070f08072102150d0b0a0515030c1306080a0e01021c020c100e1e06130807080c0f01090312090c0b07032001090308010605040308190311071103 73
    0x815900e804403200c1044500b12002041c00c0790a040711640e550810f44e8164007494140d9070719000594437020b0095094890703d02c610b880f0b0200c6000c9206840d24044818002c020301501400345032901540640c0a10044040c00c0e80c035112f41d01c20351080e00c200503820320498500740e000300c0e015a0240c400c41c0180b80f0203800740100210510014202c0c440d0b9030303001411340703070040c55442080415006490003160352010780c1c012143c80c0060344141c4000b05120281e13904155086c4100400501c0484441d10002c8024003003450300071103c2e15000c1d0601c10290420740b0100d011030400c500c250850f40c030382010070b0545140750ba2100741e03280039281d00c1c1412008519101140c0c2c205041c54456500a15001118018100d2904048020540c0071034016020802010010651400000425a078914850b4000100d12601d403c00900d082410b070400c0040020800041000c80e19032002e49140c01d01d56251083c1c1c2c0b60019500790003c0c200110011035656002c50801c0501044948065040d5805c0d0195 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 442934505 1250 442933255 442933259
    0xd0b1005040c050a110f0304080303010f09020f07200d0308090f0606060403031202040b1b1216020603060a03050f0a051018080a020a06110903010b04050c041a13140307 74
    0x84240c070420001000010340502080c504644913010280c080340c482c41c06d035010f25280140c800e0070760b8801c0e0050003207a40008010843c1050400e5944024580f03003204500708510322034164424410190040e200e42e0101110728603009030700040f01e90398100108500ca202c03c491a000c1d1001004072a00000d0f8002e1481c0c2400340c041c00300e801d610600e8020401407400781145d40a665400108009d061581e6080c08003013240c0e43c41714000d000641d079442c1c540c1d00d1001d1043c042031070100019604501c0301342c00e000c880c0825032500720100c2c1c1e156049404a40f20703501e034004a015180240e00c090610300c103d1010084000300442c1e1141000c0c05403003078038180040100d1801c00e80e42da403807c41341803695030300f0120302141941d0043c106481440c819540b900c0c010b500c51805903003501c5207004940304000b40070507a91501748039040061206580600c0180362410300c00701c00380900d108000045c041c9841110440c07404408035030b03031180c20a000f070940d43d0310346009100b8801012a0135020b44504000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 442935755 1250 442934505 442934509
    0xa0510120c1e030b090711010e011104080d03060b03040b09010f0903030f1d030d42140f040c02210a0806150d0218180f0709081009110d0b1005 63
    0x344e018980c00140880d815621101800c442e4a01c1c002c151480555881c40f440c00b20380e0080c06481000e00c2940b2802d41c86900381412217040c07299150318501410714020040105048010649030302c150800f40c00031142d605e1005003409000c0d031000c0c0708201c0749019405410181c2543c070105564041c9a0200174900ba000607240000c1c40340303450846140e03c107108181c1d5818064101125000c05e84ac3c048400c11450001c81c9980307440100d0142040182c0b102c1c1180e2440400618030090101591405060a05001140344c121a41c010749006540395102d22801d00d000704000e03107480b01403412500e040142805030001c16000f0862220004203c0400310710307580303404d141071404481d109010b20710704209801c20700001d40c030200218101610482001d402e541d10002d104030621003000e460780161810f4281260003a03002030814042c400d026006000d183e0700001c0310b101721054010002081156810100b260012002016901400c02c0e0340c07143c100080500e45902440420041884054448007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 442937005 1250 442935755 442935761
    0x3030d240501021f0207021005040503010f05220203070803180414010501051606060b040806180102130b070c0e01031b0b0f1602010c0c09020a0905040b0a0510120c1e03 74
    0x1c205401644201c024411030f0010792280f102c403101c0c4541c014908403503a808a049080e40c011084013089003c5003c000760704080c080c076560450811000c100074501750080b00d00c51044903000e40c2254203524508001c5417403c002810240c0802c004886d184d05031546680005422018464003803820b1244860340100c10408840c140c0d0b8050312900d042101049261002c440e241c0c005036140d0340c85400c002900000b950040014051300000780000e840c14040d5000c1c0e03e44a003e042c4902c0c3c4c030410591485c855003100600a07241c00c0300c4040e5403600c10381400e810704100c6401c10b0a0f40e290200c00041002501d072000904103800d0100c4103041c40c1e503507401050794011101120f0581c00304014240724020741451040815105040a40c140400303138440d0801440130f5080011040d034000388900c001a0000c61410041500321401d00c00c4d00180b0300422640c860700c1c13103940d00640c0001e0058070154001d40c0c0604404903400340821400c078800c4001403000207480050051180003e2140e003041c0d01c280 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 442938255 1250 442937005 442937009
    0xf02030a2915210a0504020103050603070308030126030c0109140307030e091e0412021605100503060d120503010e0105121507030906020c1e0f100506040b03030d24 72
    0xd1051a5041640c00704070615440040d211100083c2c514884124440790b101e62800388401c00d000040c1483c051001404441d0042c088512940c0002d50400c0022902011281951109800301c0c000100c000b001c2030040c840145140c000b80004200d40d1404801588240d084a009208800c1c2c1c041c9079000d025164419040080d00159078040311003501c0c00e0504042da003290108217030b100c0400c1020090b40d504101681c00311540d4241c1034a14002d558100704003400020241c012602551400c1c0000c0c42c001c41500c0004248840800082d03d07503901d00d40450303201034000340c4058020041082c0103005510034040d142810305004004a00b41c00d00e84401341004029600130901610400311500072488003d1050003010b84400e0760f440001c0080c0040c1807100c1244000f415a400d80301c2c0092000e4078002c03482007040c0e2082e500a440b641e40029401e0b0191441c0e40c0010785030f01c2c1c6401181c05002514080c540503c000100169100c00651110840b01190301410b4107940703030b01460041c990203c6c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 442939505 1250 442938255 442938259
    0x150301080307080721090e071d09060418030206010303120e1e0c0a080715020c0306040605150603180c102102190f030b040207030c0807060f02030a29 66
    0xb4058540080d10000007403070003902480107610803560462052030401364613400b4400040c410039040080e0420010030603002a100d007480202c101052149411100c1e01600080c4200040d00110704181c6070380d4407a111011903013030200c3c400c6546080181d42c030b180030301c01180040c001d011201c90820b5140b01d0740d400d50b0b42d840003402401525030420104035070701101141d803d00842000724a140c0e1011710100c0200b0001002e0540b151400c0340000c150702c1c0d155841d5003550002e070072590181e540421019886075100360002201c0e01c0300c2c0b21201113008098019500300d100002400344061002c44a020104a80c400300c1d80702490300001d010705981002d41c03500100d01b05c0c0e400140c104030340400c01601281c4e0184010704180e0405c0180c03000d10250904032001c10014814160041d515018040307850b0301c00e40d402e41c5000d0050742c0c01041c5155035280645040c00202d20350040000ca034010501c07144034418107544074204005090300608030020060200c050f121000d42c000d00040c4000b010203000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 442940755 1250 442939505 442939507
    0x2f010801060f11011503060501050d02150d1b030e010e0a080301062003040306140c0309060f07120e010501140118051005040f06080402040f0b09070e030a05010612021503010803 78
    0x1800c030701542c4403100000c5000c01d00a81900481e00104248507003001e003101e1088034a10f107803640c01c0c01000c840040c0c002c0790180400c0c80d1100e02603100c12100300c03903007a80c002c0304503a07038900c04000500400e2540041c0741480602852003202ea507040e08200b041031610b0000b005a00c0030a04100d80d134240000340146400c3c001e02c0100103c0e4068940c0a0b503007484d956581d0200340c0b451070f8460441e48160011501c0c2076031880b0701c2401032010001381e0f81c0008100780e0300d890b5042c41121141d44010040880c82280f2008001805040c0301d08180320155501c0340c0248a0a041488000c9c06040d01740621411642c01c100d40200542c402d031804030509001d10580000c5505100034400f05d041c4000c80e2506011040200107040c800b03071410707400101140d80d01e002113802c043c410072040d107041d00c032100f00322410040b46204559801c00040d8001a05090243d25a079880c03010906206100f0300113403055282640000e41d201e40d140142e41114400c4030700d850000481c41030410540820301810f6001e902c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 442942005 1250 442940755 442940759
    0x603030a0c0b0604111303030905060a020a0204020702010c060533060301033210061d161b0305030115050310031401021308030c28060b041103042f010801 68
    0x22100a25400c01800303032010403103d17103c030031240040d40029240003404400c4082003081c035901c04c0814002c0e24080b41d0f2039141949004009680c0e5800d990042e200b107500007180000c685c06040d03031581c0158000f41c14050b505e031580500200704070803408038100640416500a144020300040c008052000745403500316401c5441d40c2c0940a960180742c44050000002032084090036080da0820031080c0c4010850f51a00620480c2918a40da00c18208d90034803240c035910210411811980c0501520720100d00000521001c0362100000500d103010844500e0000003815803040056060740d02c40340051041800303442c2e08940b980300072503504081141e004410b00c001100015000c00b010746410016003002a1141d403208803242c9944801c1e00341d8400214110301040910000c0d01141c0c8540340701d8108907940d100b00840b0304207450020300c4540c1d601061103550b66039074071507104041c10407442c90f1285001d180c03031046501240404201c8080c80100c47c000704d10f04207070b03d0000480c182c1d00d40406074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 442943255 1250 442942005 442942013
    0x120706050603190503030a0b0d08040306020c0a08130806010e0c030f09010209090a050103022e14040b0a0e3a02040212190c021b2206090501030b0603030a0c 69
    0x11802504180c0e0502541c8002c0d900e002083e51652903d500a4010356500d040144442d801c0b9040c4604140c0103150b020f08040215481c1c0082d602183c1c1c01890259894850f000e50500b001701c1303c00028100c01001c2089a229450340074003400740c5108000304c404036600c81c10940350400b41201c400002e02d0080001034400f81c01011100c3c0c0040d03842c4000360a10282900046103517a084440300b17500d6564034010425072518070030700a8004141154006801d0f1160402082a2800200c94051200c00310300b0f442100764102c11107006000c0200303101e40b2895011401020501100c08039407003802c0c0f09071500b0304825403108003400130742c0d540480400000b0400c88404503102040c0c007603900c5a4203100008210303003c0d84200740308040a0315000c00110f1000c40384001c0310802041a400c645c0807075030b147c0e02c2080034030310100200300440b100880041004641c0c0283e45507103600c5001517062000008552149412250503a88105182c0015548402c185030b564040c1c80d02d04400620189510710200b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 442944505 1250 442943255 442943261
    0xe0c0607050d050f130801050601200604200406080f070f120201030504030e030105041a0c1206120717010507121a0d0c0b070305031e010b12091614030c0102120706 72
    0x4c030945051103040595074000b000380801c40354400c8040e44d444400300100340d03a002d641d0f408103111a040301807080080450032075032180003e1009100810100040a050511215480c0024002402884902c3c1c54041c1951611110104400c01d48110000810880f00c01d414890580c4c03803035260b01d075244c8400d400460103014080c1040e020b120840040c0f000c551405c0c0030f900e10490003231100e1109909140c0720001c3e5a140180169080340d41400307440c000307611400e120342e0010011150030300c0c10410b89016a040103a5030340022404560041c849032241010b4210764450f50480d03c5150300c041c0507a40640555001621401c082c0020002c50700152500c00c0e11a09082c1c09001080f40743c0351507160700100381e23004100a038082040841040341c0c24010344041c1c050341031392200da240254503050389200e81b8040c4600c4507424041e103000046c0081c50401c80c1c100c5281c0b41c015a410055038a011903413908503100390a0f800703070107031100b06c004c594000111813044002441e607062908409440ba5002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 442945755 1250 442944505 442944517
    0x10306270b1903050f0c1008071211090102150123041b1d060403110103051905070c0b09010b0604030803040303093002060106080105060f040914090f0a0807060203041e05010e0c0607050d05 83
    0x12b2000c80101d01c07440400510904160708400071a5994030a800e800291401021904126100c40c207003005120084001c05131007000d84014001029410050002802510041c0802a08455404007584625910051501450703401d030041560b000000b0060100500c2140006481004001c600881c60b51207179203c00d910050b0010b50303514142d0801000c034181c130416030309000003c084180200c140034240311030b00e4004031020001c01c0400c4001000c0b6034036018501c4058a00d54010000409060180d00202c00c0709500c801811b483c000580c484080790350380541c01004104400b902e001c0050b00025103a41603030301139182d00103281c0c0303400c4c00c2010355030020301d031039681e5442844000792034910741c060a20a00200d6150202c00e281c80a40107142490325005a80242c2c010800c800201d2040411030340000d802900260b625503544c241145074001c10310b0180140b100224075501800419840f18101911a070b040d40c100d80d0010082040c580545080902130360041e02541c18058003580c02084 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 442947005 1250 442945755 442945757
    0x1f09020936160210021206010c021302030f010e221214040803071103070e071b02030303180d09080717071203020a020f010306270b1903050f0c100807 66
    0x1089110340800034059150954484a00c1c41484140c0304850350140444c8440b02c1044e10304604080b9500789900c0400c2010b407a007814041d0b0185c00c1e80554403221110b007a50b04000405558a04080318486549482442491303001c0c1221408138101c1d04500d220030315034078201c00c09194040196159215003651000f008010300c40b40c07041256621003131902030310040c4451000b450311011141071200c0082000c0003601c6c801d400a440621080001004a40d0001c015191050305800e0074542302625000900c4081d501d1300c004001c02407003105040c9c0600090181c0d0080d90725124807100306907050202c601a400035600512018000003801e2000341d03a0b05d40031101103031101951944404480c07164500c0c1600143c01403030360841541085000307006410020302e400c1003054589240800a0719081803c80340c02d070070101d14400040c401c0d8101c00000400180011000100402014103140b0070384812501c502a40410a040c210041844103a007000500000c0244004000440307003c400144620 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 442948255 1250 442947005 442947079
    0x60b040f060609080609010213152610050411160f06141b09090a1a04020d15090207030c0b09010e101e0b0f130f02031f090209 56
    0x400c0d2015203014440c0145915140c0141041c20310950703500740ba400030076078203407a070042084504020003800310703604681054110142441e4010401c907100a590703005049800800303c43c8045525100d0301d01409038241d02240721660740e8500130710082c1c807981111911070403420720035030418070039408030188a90b11445900c40d0710307801550fa5a003264107803015881042894420050641c0c105200b08103603202141426051001210006020390402440c060038180c8400f102812035400059086265400900c150344455494010f14001c2c100341c0d04420401c030b00784100203661910307031080310303034040c0c16959903c20300c034a54132040d00f001400380510141d0b40d41e4990702e140000f0144040000990021400b2442030300100f070301c040309915a6088502e451504146080b1556120502c1e03030145426509042c0c10590070f1900002400e58480e071004090000003000716003141c43c0e8090708400035004014003540d865910100407401070351162604010019600b036881d00140d40050003140e0300070000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 442949505 1250 442948255 442948271
    0xc1f03060b0a0c0201020d170106050c0a05070b0c10060513150906060e1806090402090a02090310060302180c0d02130510030b0a1d150303160305030106030b0d050a060b04 75
    0x1a0880d5014588980004043c0c040140c2150790500108250f80300610308411541580460040c400e441840380348180032001412100c503800620050701c0d0076820209549107542c0c0d03030500544540c84401211905e02410b580044102801d1051600752a80540404101008503280c1c43c0104048900000f0034a05091300052000b040d000301300250020781d43d1780e08020440ca0601c003483d41c880134104180e010038001c1059075251049a90380c001d8044400280c6074503007075000c0b00203203d02006960540210005844125225044981100d2082c0c40074000d601452503201c51001c0d0a61740212060801c1250401d030f10490f070007901c04400190310754003040e0390307540001d40704151030415080802d443d884008010700d40302046c0c070b000b01441d81d0031613140d410503c4007402004c002008141c05404020020b104c0341c82c200b040d225011006940d096101d0307405e0501030900d8000340704580020341800d07001c1005080017180038002e00d034400018281c075441988c406c8041c108205406400603500c40d10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 442950755 1250 442949505 442949519
    0x60c031f060c0c0f030b070f0302090a03050304030b010b0c030a05070501180b0406060602120a031505090f22081801020c19030b011e0312020a050a030e040e0c1f0306 73
    0x600014003058440b94120101480c125145444692015854400c0100100041145911358582c070203010710b452002c0c25440a411340082c010116400e4010341400c80220400900100400a890095446d03841503a0794815468051040c411841001e401c240b02c2c144406000c1d80103807566a01c5030002103403501e101d00c00e8480c44d40044d030741a00c1a540740001c0c0030500029104643c00f40c00d1034800b82c06204861100852207100e0b110103003040564508004035031503071101c0354502400006003480d015081c40110f40c04925415100a03001c810100c100c91f0071059100056245990305c00f240504003030303500760000f041802d0200d0560560182c44c02e1240e0b40e540384800c0800b135856602007080041d065042010324040e058021042c01c0b048828400740d404407003448141106e52100c010701c0c0141103014200e04010510000411910400c0070040130035402c880a40348000007510300f000790500c140902540c1d5003070074804580100d4590407020103031400c1d03081071070030b01e010f8100821000c0d074900d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 442952005 1250 442950755 442950811
    0x70302070815190c020613020415060e010f03060302010e130f0603061a0411090402091216051e090a1107080c07050901061103040e070e030f0f0706050c060c03 70
    0x116501d0902c2c000010000c4490190f206041480d2481d1010031052401c1e0340301a54584020b040c49035904070b0708294900319a260340044020300c02034108960306640c0e845001d03141e016900d00f00313804500704501c2d24000c0c40c4a4418a000c40340c05940b90441d81e450081030040100081101014090f201d2491140c414014051100150b01c12240011036a42d50341a003103202100c213107001d20031410f10092150001080c020ba0320380d09005c4900607038402c0c0070f1000a02010652202007030714042c08000c03002e0100c001d41c00c4070072110309858040c4200742a00e0115040342c43d005c02542d2061115021401c4403005a02c220002f0b480c4c01109494001a51525021908402d801440640c0860018031aa04094a089006104038108203000780704045d0f0840c4c403805580100750341182e0070800192030030310a00d160620904044c080c0e03610607030132280d141c2d281c5040604004d0f092150400001c0c01610410440e95401c1c0008050800d503201e101c002606588042d09158261601c164404c01492083d8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 442953255 1250 442952005 442952023
    0xc0c0108180a110307140a0902090d05070906182901030b0a0b1902030c0d0c020102101803021e0a030c1401020f030106092403050a09060c0309020918120703020708 72
    0x18010301e84064050f04040c41c1c0343c81034101c115852200110054103480d00c84a010560304117400140e11204480049060140400d130083d00741d100f00840014500e10991000c0180c0d80301c180e00c0c200c1d1040d4507482000380c0320003c400701c0b407811052a0409060403103c1e200c000440f0145000715010000c100081c1000669070400a41100001140186d048800e000200306480c42d0018600300b00009030010341302c41c281d620404c103104044c2192000c5a1080c01402a6501044810842071014001031442112040b90440240c810041021044032001030002c1e410040f1074020040410b1a41c2d00315280351039110203d032001c90001904c09502001c1c0040c3c00036079002880c5945941c500680140707551481c2d44074080e034040c41c65900c428841814181c0540d40850708010449855000c20000202681040540002d1824180b1030b402581500304020450003100d5101594071480307441099960220307205909030b03100d41240541001060042d11030799010740190f502c000c2c0d842c800141015212 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 442954505 1250 442953255 442953263
    0x8090a060f0213050301050432120d0c021f0e12030f0720100b030a020d050d03060501090b040311030a080c06010f0602061618180b0a0b0c0c0108180a 66
    0x101da04a040c0e52110100e00040001718028015070505444200510032810401180e05d403004011004041010f0408501007443d101121002c011500c030200503034000d4250f0410703003414404001e04241c40005c40803865800c43c085c03143c0421166020307000030001241901d07007501683c0f02220032603001c032000d103105200500351b0007070317034a0444070042031600e5211a00c80b02c80c00d4014145541c1200180c020041440720034002864034580001030f141c5410080001e5103c3d90703e000c410104203000c10401202c105945090115549034401550b200240780200c0c50403801c240070400109001034008400070b18040c05850b21510242c5844809030710901c0150501e5004400400440140f030070716030018030071072002e05800e00300040c510700c0d920342061b40001088102d5280700c0341c0040d41d0703075036000600600b580c00144444000041001e0070f209072080d0b104000070080083d0b000405001ca844403119403001e00341d941c0c000300040d81e503030700d01601c80104040d102e0700000e07140320704204040c0c0d25401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 442955755 1250 442954505 442954507
    0x15010e0a030f0501050601020712020d020d0f03110607030606120209040902060310081911010e011101090b01141008011a04050607030507061d0a0f080d020a090f0603050c090108090a060f02 83
    0x2490510609450006c1c3c40c00d411540104410044c144203181802d0340503034101c51800414080f0300010320483d01c03020b00640a6641030250f00105038108030302041a515200503140c969070340c4a001d400310b44084c8190700204010f008010008101795000b40b1201c10001c2000485190640108400c0e420803503100410800c4a00140640e15041180d91103a11500517041000c1e0b40e6562810385000950000310306200c034410f40f00140d0b82c001c800d11050401c0d404000c0003e02c0e00c904042419080a00caa142401a0510400d100c1c0c14101a130940016003a1202a4141d19155103000308600340403860b6014803050102240d583d032a400100074443c081d682d1280c0b00c4090342040822100094025118110b68225901d1000d80200b065a41140c0000a0302d140c00d0642c14106280e2060b81c102c0e01e003840c400111528450f400c0040791056603078403481092000e0f01c1d00c406404a4806480703020404600340614a0507601c507002d22030b0f02400780815125040b110342c1c0c2c4c09040d5903c1c80842c44074290 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 442957005 1250 442955755 442955783
    0x1806122a1110091e0312051f0503070b12131b0e0f10090903030b090a0603030906020303100b0913110a03111305013b0405010b1215010e0a03 62
    0x64100011815101c101c442005a4030f40c0780d40e0381c80744000e02031440d00484031000e4072100741030240b0405251004a0b00c028082c52900030b00130745044c040c088500e9803180c2c2c9403601207158100000c007201a06c2c074101c00e8070302e400108050818034480040c081c608201c840442580002d000141d0400b40328903840c0307601109030400c40152000746004140f41c4071950044104550901d50840b0102100c04403400002d2040d81800e0072006010040c00c9260405c0348101841140c00d0283d11030001c4034001d40d204400036440d48002c903200d1209980c3c032074030341c20507880134092949101c0080c50324074001025824079404a20600c0c0543c1c489080f101000e08020030101c1c2019010300030b07842d001801c2d0030b60f28900a02e003409502031061310701901e0304000b0704540281541c048040c0c05404402200105c035882d401500300c00c00703041c3c21888400c0c000d0741000000903a44426130162140c1c0740301c0c2e00d6001415aa010b9070035041c0310010300e8490400c2045021000075440b00c59520010354003075541000b030350b8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 442958255 1250 442957005 442957037
    0xb0a29070f12180603020a210908040e0f0f0c0d0c1e02070f080c0a0e0a060f0e0615121302041d0309041802030a081309110a1806122a 59
    0x4000742d48030340c043c1801080340501c15603015a180902402c00091123442e004c9202105005108850008011660015001c1404000382c0e2003240300d200043c8003240e07035507a80d6181903c101c00a55000b01d036414180f003c07041010300c40d08181414100c528081da000b07503514500b1210500502412009a042060f05014034a101482d04d0013412205d0010300050901034046520600a417040d02c1080c04c3c0c8901180080070290884001080310300c0e01d40b00044d84035030b540c5d100c540080c1c0e055232092603040d056006405d0840140c03a16603040c030901a246540b010910401502200c004a0748182d8400394268a8000c0140c140001d40e000b00096803956803803818081103c40440b20220004a00f141400050b0380c001142400164407121142e150740381010b0100c0307407205942081901c10b0400b00c2d18950025140f002d0080f100c3c1c2595255443c60b265030080d01d56100d60b0091100150110386041c0c0d0208080d0842810310b843c0c0e604c540310804000405010400d800301d210b0002504843c0c0c0d2103050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 442959505 1250 442958255 442958297
    0x203131703012909030703080c07091503110d0203070f031412041206021e09040b12060c09031606020a02010f0f0203161a04060b0a29070f12 62
    0xa010241025450365040580701d42c010741540c00f840c0c5140d018103c1c0031020710398410136036580440c081c0071124410781380e00d40901035401c40259a002031150a20000d800034003405043da003c400c0c544a245084d0654540e0f007418080c00380f4481c1c01802680c206001602e00300500c00041454114001c4002d05616204805003c81031441910303522281d10045084411401c0341c1c11100c507200c114076042150f00d8020003074015000114034001e50525001c105182540c002c150010049404100740f1138100108280c41011400d0000c29900071000a03001600c0c0400500c1076110040458107100f04000940d202c09000c0d07001000181c22a049907411560010818141055103040032500c46c0403080c0002c0d52405a4104103140400d0002814140183d08a5144841421160401e02490f147c00c01c100030f40300314000c1c00d0007049503420000d084207068600503000000d413840c18004820075600d15003240c0000a054070300e00b038040002000541c45819011000d0500d0f00c0f0702988440c03d480f04420 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 442960755 1250 442959505 442959533
    0x204060908010e032d03150f04090f021e0d060b041103071e0512152103120612030412030207060e1f02011b030b04050105030a0f0f080d020313 63
    0x850b038182450700342c1002002c0165001d00101c800f030f42c3c0380498221084000c1480103040c03031041c2c2c1800000e0004402200c2d405807405002940e40181d50320b0001e0038042200c1e070003c80a42614100301808005203040341820380f00380c180700f4080c1104604200005d295030b55242d4225851507803001c00e4041400c1034003600031000300c60940a410351410364400350048000c4003100c1039044a9030140c0b61014010800c1d108111340040e115481441c140329055400c40081c14113602c030304040641000d41204a0210038003442d6078001950034800e002268003034901c0058415503001c11303100507190511034104060402002c5061118004008908002c0d0618600750030100030041d0102890419458110b001e10014910401d4080b40c0c45000c90207e00424074030108411030030112001710080342d4160002107400b0822601081183d0340d40b400c043c0c0e21640300c0001030500354208110000b09610059a101142c00342c14020715105284984504036401210341040f0844460894010b100202418041c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 442962005 1250 442960755 442960769
    0xb010804080a050309190b070908031809090a06020f0a09081506100e030111070203010f02030601090501050d0908030106090e0f091002070f0206040305010501180c0f3002040609 78
    0x5a2414241c03292899441036440210a001c000030200b40b05020810000014001c00c00482d9a031010620345252000c1083c0c4169000440160300460128408403c450f003801194a4012103c9004030900042d1080106203820b50b0251441100115820780002d05000c40010740641d62444d0000d0040e1901e681600a06540da2200101d880700840307000400c2d0f0000403c540440461000103021105051040815074055081c2443c01c81481d11000150111500c01c40081c0002580b140141c812800219041400501c089404110750b501500c000d244c148100100403c8004640c0c031035540301d030b1084e4807190025818a02c10000d4100080c03c20f90040c220502c0050a810f10841d1940d456618510540d0015400140c440c00c11200b031642c0351105501512039601c8540e41e003022030003040d091150f42010400303e140035010340f05911580c50f102c030494a03002d155906415003110003094024824100050410108152684040210090190311000940d0380c2d424458010040451540008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 442963255 1250 442962005 442962017
    0x51006090f18090807050d0503061e0a0506070c080d08060a05010503040c0605030903091203030601021603150504061d0a060b010c0308150102071d090d0903030c0b071101060609090b01 81
    0x4031288070720301052030300300d9031010b4003041c00c071024141307403050344034864000705280305140820305441e81150180d032290600f1503102c1e010840c10381e1383c4501e1048401c070755030340040c0d4103805014514000000d00703407250191071140402600c503102c2601c0c0800c00f0140380b020422103803c01c1106c6c942100c5000c0179040a103000750450801d503a0300e1200c42110300801040c000081b0000f0036071001001507c05013400101460340c10003901c01c038a84c50f03030b10503102c40c2e0060044d03c002402944030020820116a40305030003144450840c0d0304070004003006081281c0303668840440034684203803482d01c0110034240c01d010f441c8682041c60024119000d001c401414480440da8503400b003a00704001c1030344802070a121124400c04100102c1c144201d0750448201800d80340300001c14900079451541c4282c0000040718041c0011644c2a12241c00a100003000600d140c021a4002071040b20810703001421410010b90310300302d8214050a41d0b009030005030018581a108104243c11809004440c04080c00c0c18 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 442964505 1250 442963255 442963259
    0xd090b06121b040209031015050301050906190906050c030703051b0702040e030f040b0705010e0c150c010e100f05011406040303230d021c050601091a04050301051006090f 75
    0x1080e01d82188000b0364090140045040b903890f11035404540f9003400040c107581c182c40d810301e9504002c010045e4040045d00201002081d50f09052050703070b004024000003401d03a0340e03550117204820040c82c109204aa0340f1a21004005851801468001e80c94002e00c01d45902d49040001c0450303000402c00b1740140240ba40e1403c8a91800c401c0321130071b41c0c060b100403c901c8045000d9510f18032a000d906010904005000103c0e150414013402200e48100024070070021200c203a20381d039003110f0754450f0b8409034003111076101b03000e03030002003c0003107a00c0000b03d450700300344c1c000d24100034a0341001d8081e40e07100c9031084010301a5208407400346c0b8904442c8440d5030414408102c582c00303580001030520041c0d0010222803605048100071580b1080340c1a942d540025a11700c0107034201d44000c0b400310000003100a03446046004051240006940364480d040c50a0031101c3d03040c0c4049404c0071011700400000c58240c50038040c0c20700c41c0c41610f80f026581890110020080c0c1c00a030f101c4440f41b4000082 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 442965755 1250 442964505 442964539
    0xc010e10030e0d11061023040905030408010203010317031005090402030a060f0507091a0702060a021905030706050f04030c0b0601030f020f2505071505160b0118090b13050f030d090b06 81
    0x402058074412801f2480d200b103101040092071081409013140c07001040c0007a80c040e0540045040e60b10902c6050080c004180701034903039010903924042015041001840b0070300704012001da1040c001002c403540362485450300401c4600c00b480486c0315646a004020803943c00001180040c8102c21421580710603c000782c201034005c4c501c000b03115000c0003481d02b140600c2044280c601283c0e4001404140310a46011503a81d07100e00300849081e801c4c007000500880244078110300c1070360940c0351100001450355030080b25020080c4524103042c2d45034483c41a00040303201034030081d004900c01e1940c4031020310301c40345140315100c04110400036041d40600080c4001c00c404013200d0a444080307054000b8041c040c1c4041c01001181001807105a0030340b014480102c9580e4100c6604081d0382d544d03002c400f106c3d9825262101e1014241072105400714600340002540050510300850503140c620448000382c6065510680c0003402d4242c40b4914141400008030040d90040c4049a0f50807940008143c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 442967005 1250 442965755 442965779
    0x703050a110a0c08030a021306020304031a09190203010e01020a0504050a12080d0f06150c030f020d140c150103050703121b032d02011d0c010e10030e0d110610 70
    0x20004c1c08401c0c0880072620501d680c0c0c06070342c40c841d141184009115101c210003950390b080352205032009010070343c41000703555a841d2200c0c086c3c0c9450b00034200b046490b4007101249200c40c44200e130150750b502041c0e10600c00a101606a400b507640d10700755100d24060030450440c1458102c222100c04c120a8080000c107420100d8076903601c84d06003c24201e044205040c01040d00340e0010440001a079400600250710401600e1010b2007074986400d034a80040303049a407003035200b00300000700d007507981c42404c00c501500240c0101c500c0c0c0d07001c894080f0241e100c4c0d14003e0f072081c4d20031100d0358440d0f08144100701d100c2c000160410340381c0c0340c604038100c265800141240030f062009000d0141c0d4100030220b00035014070450207890000c540c20080d0900800c0240241102029001140210111014103104c013240d03141041405960384802c0751040e07400c0041ca800321200c49000d05036130714074850041c1400e101f050741a0000c3c1e1524114100c01c0c41d101c80c18480010910b6040d05500750090010041303141c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 442968255 1250 442967005 442967027
    0x210203010b15032205030708070201030e010b03030306061c060902071401151701091202210f030711070f08011a010e0a060516050610170f2a090703050a110a 69
    0x4d140d60054a41110207141024010700028125010002ea04014040c1c1d820040244074400e903400c011591034035460600b220a5840c605500d508200049401454048044d140f012049a0624440c407080801101110116803201c1c100b81d802250702024400e0490300300c03517121401c000030b01c003010107196070040d48042400741103854040d488844c00320440940c0314a00c2a54001c80564a03030840800195403000708007112a0864510240c0d18800c3c0003074029201070f001031400b00ba0a503121180c041c0c510380e00140300da8031503108220b0006101281404e8031001072118a00000307440003010c49000c450742c07803c90780906100b41c1d110091a282c40d400002c204483c42c500d0400d86403041c2c0d05194080c51500b1a0191183c400c4200780180307010744564200c1150010300c1c0c02a40d402d00340709945d8440307411a80703141e01c581003441c10210440701e00040340760004e00132070860042d00c135580001e003070102d05032212400a9174503020070055030000d01c1021400100402c88a08182e00601c0080400c8405 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 442969505 1250 442968255 442968271
    0xf080f160b1c0c03060e060a08061603330501050f09090411131d0d020604030f120203040605060906010546050c100507140a09210203010b1503 63
    0x2500038202c00d12034210110100c07400c4030a11502d8103070703103004024202c41d00805a100c10746902003005072030481c454400f06c076149000360449030b4031900c142003104004840320050540700c0840d01d41105040320901011030307181c10000c03000e4030b59039055a2081c1c0030f40c000e1030602408100302c41d00010a4025aa031404040311108850760321450882c44d50040c00103019044071620346174a03401c9030140c000f18036044007124441c0d842e5101200c1d2036925054502540050b800040100d0042440740502c4a210490340c00c020018100001550301280d004540a40c1d902d036403081400154a4800c01203604800c0918001c1e0070074116001c40300d0005440a880141002070841e210104c568200c03025040031a0920320700100700c01d91001a00d103a0000540818900580724481c074021035510809005160b01e50300c1044058a07003c001e81950300c400d04400500c48140e000044607200c00c02c02e20241c1101c5031840300200b040c1c2c814142542d04408000784504190860425000d041a0540ea400590 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 442970755 1250 442969505 442969507
    0x603060d030216090207051504021c03051e070b07020f06011403010e030409020903060a02040b070201030e030723300a18030305070b0f06030d08100f0f080f160b 71
    0x41450103903e0281c0d9151000010307402000c0001d09070a0603806000d40700e014000b0380d405040c2e15500c9802c20b1004560003035024440c0d1203103010f99025030b0040c0c2c10841c8241010740c42d0410307001c41c004c0c141d40c81e803000725401034000420340100180890b0180d00221103000900b07904600520780d13030305c8481c14014000e8640313160490801039903094002e49013010704a000d80355143e4540142d4400381d803140305c0c0d5030300038403500e4003051004000d4800c1721b04071014a01c4150814415600440203020052170345901ca1105100c0c0d02c002c01e80d040000501103501552041200501ca1041402c0070b1178940024503e500ba000700282c0311000400d0b40d50341501d00601345907521301c401c0c010745540d0501d00c3c034102d1800141c0404403c254110006084440c02001c583e0390030341e03a25800f481030300411540c29400d0b4000b550300c124400d014032100ca410089031015030300070b0f40c1c403580440000e070555030203800403680c3c0140410105600303100204c1516000f00103044404070407042c40f29905c405110741a91090 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 442972005 1250 442970755 442970779
    0x3070201150806010f0b0a0509043c1a090103060e0a0b01061728151e0306050c030603150622020a030b0604050a0608090f0a140705030a02060306 64
    0x8400e52003100c54008500341c190754a51200342c1c1c07039a00c1009000e0350140e01030142001c81c06c00b80394021751700c007903000c2e9030b030a45030900842c14403014085201c10425070140b201c08028015040360900c0c140719041d11001002155541e0341c0a094802d150b909500700d0110a407000e5283d140e0a43d00c505490308000041004203420740d0561408040440152036035000400104883d0303400b40d04140080700700180542c8035210366480b0030542c81c0e11a11000051200300c00003078800026004200e115581c1418141e034140d40d00c00302200f000c5c034074006001d101c0c0300e6802401041194402e843d0860350356110300b8114540600840c3e916104807402500800c0c12000042641c0c0d5100c0c0c40da204c090362251141041c5071a50a030f40c0c0690030200c00c0e400428103250425249080c210150303000c179800148003007159403520714240d89805001d05904554094803003094500802041190595486200307940390800c411710b04107040102d44e4028034480e8000e81146000b40e40c4640c1075030340080003201d00c004542 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 442973255 1250 442972005 442972007
    0x21050307080a0810050f01050d0e0133091406090a0207020402070b090c04140a02090112050906010f0f05090c0d0e070311040c11031905040806010902030a0c0c030f050307 75
    0x4090040000c2003001e0016410318940d520844080c01140140c0001c00c0c003540b101d0810019020709610715000440138801c4d503c51075143c0d0000302d01b20701c0d41800000c90b440f4144081510148a080346042210030740c0c40021882150102040104414002080004211003603000d00240141290740b240901c070340812404501c2ea81140e030340e40d80c010411542c400d41d614110f00421000c68200702d2034003c0340b10b000900e0420740604101d9071444a07070402d0340e645550401000b5046085803504014498006401c2d0018a110f1603015a04100040c0750541c0340c4460044012419040100b003020015020840c1d074440e010b030382d600030f0704440031a0303111010150300c0d03401400420000a958451100e0000500c071644078258003080b42941c050200300a409000d59005688607400100755104109100d40501005044000164030f0324080d4601943c49100514000003030f04180d130039503400070a10800746028860000441c030941400441c040321614003501c0c0850105102d024001d0020010b2042 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 442974505 1250 442973255 442973257
    0x15030203071403090a0303051e011a270306090307050304030b06181614040e04260f0301060215070c0209060a0f0308071203050907060309150e0a03020610210503 71
    0x32600b00002900c1c3e14024104540d81c40048a0660110b481e05000c034000e840d0808010f81045101070385882181d00e8206660f40c159082000449018810b0050444441c0e202c03e00e00901e003400501c81d10010542001c1606146010300591000d9004100e0180043d10100c00c1d50100d07504840e1120250f0f035030703102103141c0c2c046107401050640c914108002c10750505041040380c1912554842c889421940040451441603003c0c0c0141e00d1400c0c00000e0010b05091140400f200100ea1040208580301e200e65000360845a003842c5401800710040c03100310b074100710341903d0134042c002c8001103040c1020b015040340800701c030290103004894001007241c0c8499041e030000b040d0b0700002e507641e90fa0b6800c00c049140c118160072100142d0200100d0a064443e00885010742d00b1500030f82003c1d45400300a40007083c4c01c0c42d0484021480d0b010500f00e01c90103108040252400741d014003510206464000e08180c0000e03e0340303010110a1005000a5524480a135103c0d24140003642554402d801c12510b1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 442975755 1250 442974505 442974527
    0x5060c07090203060609180405070e19050901020702030105160806031507051b0f01020405040605031506120c1903060e0f032502060a110f060f060d2604060f03061503020307 76
    0xc405100440c5d18544108521f9100c1e0b40a0025196607039129080e00d42c4100c410b50b03071002050014250420300300060f611540e0403420342c100051030248281d000c00e003136a000300c59051180c0798881a48940c00e40199040742d02039811805400b1241b01c3d81140c01c0c0004000e8040d80801202203804201800384036440c2065a0b49030b0100c1c1ca800580c60300c2203020f98001c0c00703503d000b142001c000040d03d00700090120404074094502110b159518000d00c850241c1c0c24400c0707541e40c440c200001301c1c240c0315940c1c50007100f8804002e242708a070850a0000588610300d6000002d070788910b4045071081c40100c144c8140ea441c02c106900e0a04900840030181609d80ea40070b235000c2400100f2810450300051030080c1b81c030814041d1592001c0100c035140d20fa410480d00700c41555074600000f8541d280140ca4101000d01c81c0c251500441c100c240c4209174074000001c0c8004010000034140300f03040d0070001c012000b0050f45028084030f8104400030703821001e907418440074940c0100105444502171440301e14 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 442977005 1250 442975755 442975759
    0x807030e030301032d050c030c0307030c06031806090809040c020d1403071817070f06050a230307020a0b01050409080d0906140a1b090620010605030a0b04020a05060c07090203060609 80
    0x2814224604001f52a101441000c0c2c1c46481142c0d0314103018203000c1154403c43c0d0700820420326191800b102507001e80500f49240c00c1503400980b440c40007540a11404218900032134019842d8001c40c070500c002c59644a842c80c0c2954400d514400c1e5450b40248035580300e0b103056082a49a40320400c0a6a10b01a0100c00403981d803503444000c030360103184403511000c0d20350b010100c0b11240d542d45220341075810a40180d03000100f041100c803810300e0284003010601620083c2c60f080b51519805103200d035820070356880c4016000100c5c00014002c490000c0c50140200b16402c000f00725950351000c02c14071500500a05407601c60701c241080c80015030000f40f842c01204024045840e00104400040c08100340c0048418468507481941a101c0d01e02181560003030346400c81c00c0c2c0c91043c030341901c8a52503220030110b03640b160400300d400c0d1014401c141071144102c101c504681400d10400c418424503802c141d000d4007092001c160b18180002d00482140c0c0d03031074001640c80c0c0340c0c0310105080b8420050416 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 442978255 1250 442977005 442977083
    0xc010204062f030d02030603070321110d12050a02090a240e0f13060504060f03050f0d080f04060e06281b051321030807030e03030103 59
    0x1484076000a0540c015140c03420440748804002d107044000041c0740081e12105030300130301c8821320941d400d03030007150058002011107002c80c4d80d0340d84046829444412072168030f01d0320700c8440e50b000d8000c4450000b0350740c4c84001d0f098204800e4401840340c9144034550034055221400308039100358960440c0c413a2500a003440e21507e80703c081c01c140c00803105810304101c070100000f08440500c2216581c0000c20010010901c00c001d10040103800f01c841441c2030042c95844100040319a13541c03080704001c044152200a24524505100341840c903a480465441d4120399190860350b94491215079100541c2c00c44d0b80296102e82c1007400c000c10782d1240561003031140c0414802500c0c448120310025076101c0e091441102d00c800030076000c3c1e80d201c200240da2844c0340c800200b40d40e0302032000f03070988502d00c15807080381d00da0302d2030320740f03107055140e080c24204206201c01d8100703050348404040ea00c13101e6400c0601444c0e1040241a41d039110510001d44003440c55400b03591114003000e090b500c0343e6180c071510 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 442979505 1250 442978255 442978259
    0x1101031505010e0d0f08031503060a0b0934090501030c170121050604031713050606061e0310030303050702120301090b0f0306091005090c18091903020703030315080604170c010204 79
    0x7001d10000703503248146c403074401cac0700c000b0340740d107000e0b005502440201030011030702a203400e03c20030481030718180200028041c1c00d840b0304142d88d42c0c3c92030247d0700c0b0060303407080016454000051b084464590100040100c8040d400000500c4601401c3c1151200f90741c22030202c40a03040c0082c0044070b0000200a806010244018141d102840030380c03142c0038401c003500d2900c40501901c02d1414a000003809900440d00040c500c1c5009800b426500129400300010344072201d8849125500454070b00300008001c1c40c042c000c0c95030511a06038030100a00082100011819011850340014800c0303402894540d2510305041d181e000d00c0c140101009012608035091010106885800e40002e202440d03203030100007260f040c400628407110407130281443e900b2248103094200c150100a000c80707014440c03c10564059064400e5409016000e98094001503086281c014103991143c400100980724588080c8030701c0750b0100314103401541c0450202050320031002c0744002401019801da2940d4404900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 442980755 1250 442979505 442979521
    0x40f030807030810030b130c080118140f1f230906090c060702040506191e0f18020d0906110403020a090c09050d0c0509041101031505010e0d0f0803 65
    0x5001802d129031078001207580d031407aa00304400c000d880041c010065840c04600c04013981446403240c640140c2c404a401c84d162486130b405d6a640da203242c03c1030190400e00c030087c4280a1020318010301000c000e0a0011040f03c0c0c010342d41d0804100a0f1b181d20515030320350034010440da10001c103144400026003900000c00590b80f0b800b0b60308031084642d42c05000005843c8440100390f8903110100100603604040c0103800388001400300908650708854105020726017452081121002011301c01500841d8840c0500303003020700030881d030040e000002860010310100000d0010441c561200038401038940e0418080c080181c0102080980020304d482c01d491014440e0400810a49000b5545071141c1681c804007802207803440c6080740d001600e4061b0500861800003030700318509020344064440103440d03900003040c14506031000c480c000d4013046130404550705400b0f501089074840450308100ba00d0600041c000f008000440c9106a800a5180d010080f50205034520190464545500e034603005075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 442982005 1250 442980755 442980757
    0x22103071505011701090818060c100207030914090c0a1b4d01020a0b07091505191110060e01090605060423010c080d06050901050301200d02040f0308 66
    0x1024084d110034941d0719828a014060056540d41c00240707a441c013072940e0800c000c0c0524400040303500042c10004984054000c00ca0704105800325580107035914035616015101c0e030360b40c2c0d1101d40c0c101c0d8444844c80c2507903181c07401b0950110481d01016a0b41d040c6000031070340b01c903c20008024002d03041c4c18200510424010f8220156105070392200706001c1c070f070400841e0030140301c2c0c0b000d800303500c20500b41218a034040304448414418012210403100030303a10b03070300c0b14881290b207000010b440100c00c11111224100c0e03100c031540315003807003450185880424040d88007101102c070240724005200c03000111007049030030549111a08200320550f195041c01140031000e00c5580c041c5802d1850108192a080080b9000c032100b9005002000102500c41c1445c030041c10703405e83c107000c4098204d0020038150f1000300404228808009082c80c100401c104c100761042e0006070180e807400144140c143c0719000c403010080c10b003038181d5454507501e040090191146401281154007a0328000081140b0f0760 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 442983255 1250 442982005 442982009
    0x6030b15071b0e100e0c12090f0d0201110726040303052d091e030a051c020609030d0c030f020f1308060910050c041e0f080d1d0f06040602030c010b0d02210307150501 73
    0x41c9c03c2d1451140000700880c02d07210280301c0306081d610200003080006001101500c0038a41a002c982d41c22452201100200d0300030758001d80101c0e800151089144a0031046881c10f200c0800b41a075040780070100d1044c803400340b5030304039000743c420001036403130700c1641c412459a20400a0886a4a20f060319010340c440049031244601100c102c11400b401900200d25103204421301402503081100c81800b40c00035140c1c0701611000e00d40c4d910003040000401e40003e211400710b10521607624074410120089101150740130400540201d824400d62035404030b0a10a881e0310120302048a0f1074003584240c545c4202d0740704090039191121945026100149048110f0f44460383d0003403040e0b500c20728103880e0300401103580009040801e0b001d91a002c00301c2400d40c2c0c003c000d40100c20148480021502d642d02540005c400b5074004140d00b01074180901440c500081c043d036446100700095404182020180150351081c00008001101e001e0303000c005680301c09801c410103000c4180b401144400410080c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 442984505 1250 442983255 442983283
    0x50c03011a011205070c03121803170601170a0c2a0302150402151812030301090c03020c060604180515040b06041506030b15071b0e100e0c1209 63
    0x20070210060302d90f0501c9a58803c4a1540714060305030135a50f0100d441c00c143e01c506007101555003042100a904c1c0d58030f0040b100e40f094a80401441000b642c002c1c0218004203560304001003020060103507441101e01540242d85510301241c40000302c40d043d51241d200050b041c140c0300300d0200c185103e40707040c3d05003880a0b0180c0c0940c0c5484070f460764042606002214040c0d0813016054030380c15a4400b110040c9000c6465150b82001c81c4d2209002170f41c11130543d0074811182d07002100500410405201e00c40c0c9500b15401c0451800c0c02c180c000c20386807440200308612580d40c1d01d107450000e00c00c0c1c0110074401c0c0e510000743c0b440080104180d1910b01820342e0b00b51824030303602c0d00040f42420035108001c50600303100354030510103250100880182c1306000750660070081000c1006050214100500f0340300784a420320780d1150300c0840d203814150301941c0c0280740004c1e18100f48068561051a440140c400c00001341c3c84a60700d143c0360060b10f110300094044000c3c0580c081002034140412000120400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 442985611 1106 442984505 442984517
    0x4030f11011b030801031506050f040207020f27010504020f070605060a0f0608010812070309090f0b130e0f060601020d11122206020604150504050c03011a01 69
    0xb842d907084000c02e0110f0f0060040155119038610322030b02d10a030400c00c2e03501e4440000c000f0b079001038120340119400105030065403100c10700d0b941e01c1c0703c0150290042030024020302584884402c841100c0c0151a00040b5942c0341a0081300c500040d02030b00715060030381039102e8200034000078141c29032208002c0c000180070010720441c8002045103407a881140c0d890111003074109400c14102c150803802c00c0150500003500190040d05a401100f400501008548030400041805501007036101e141e01e00c04d074002d80d8080c2c00c03c00b11910350b40c0548120301031840c1d150b560b48200707880860160300b0255840704041d02c07c0e12040d118401901c21a5901010144401001d60000e4001c4074005146418038032003a2010107040028100f91005044601e06600c400320800102c0c910010507548900200e07052003c01c1110410b20003000b40200328404a02c4500c1d03d245e0079103400079000c10701d = true := by decide +kernel

theorem cover : BRFrame.Cov 442805755 442985611 := by
  have h0 := BRFrame.cov_init 442805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 442805755 ≤ n) (h2 : n < 442985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
