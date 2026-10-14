-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3717
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:28:10.542843+00:00
-- url     : https://prove2.me/submissions/26295e9e-dd45-48b2-8df1-00414a2197b1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 668345323 ≤ n < 668525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 668346573 1250 668345323 668345329
    0x30705100606090b16020906041b051803010605091302060721031109030c0103090c05060f07112b0302150a02070309080606061e1c05070f0c080301180e030a020609060a0b 75
    0x54405c00203226140180010700d090f00c450f0041c00003101484180061580d00d480c0c01f40a640007851007030b1036a000340c812804030740b0f81401000200c60010f044030a88e41c90340b1100700d2100074180800d80c0c000c0c904120100008034050707080805400c0380d5030102104510408003d0a5400c40300240ca840b00d0103000c81900d070394001c92544401442420002a044051300e003003002d103001d0b5400716a0042e130110b50b140d001d4440d03d00a0168504c00c038201402c0c10704640c00c0201c25034003c0803040052007074030000404603914074400c0312030f0350080c012141c000d26180840c001c1c840040300e00500c1c0640120f140c41c10543c00000c54405410000b000c0c08040c0760500103c0c1c0240100d100c11741030351201c4051060340303a04580841c2c04c401c1c40f0040f40715a440c40c101c40c1101500741658503c0000707804c00804d00d07085200d0401030740410741c03200c5514503591802d802403414032060440704d400d00e03903510312103200018200002d00000780c407074010705068980b00041c1800c000d8000d01e1540d8003400c04a03103980b20740e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 668347823 1250 668346573 668346607
    0x6180f0b070c031a0609010e090d0f0e0a17100506060304020d1e030507150903020d0e0a081e06060102280602040302040e010f060902070309030204050702030705100606090b 76
    0x20a2021034648960301400c180300b60000d50380c40500702c10010700d203100800900c1c02a180c481c540c155074042ca5a41c0e500c61102c0c80f00f0080301c00b100150042007a4100c901d100b15494010f40784c03180f901c044114900c100040a03006207510558051001c1072034848080400d02003a24041052403003084149080804500c1c00d1000400082c803550f1807604100c00c01c10303440600c803000151030300c0c041980909890050060b0740517072401d8507122015030001c0c2200315540903200d4020751581c00743c079400d85103000a07600303800718503c1103912444d40c03000481c1800301082001c5582554425281d2080380314948036040c110047e00c41411500644001240785015842c0d1180803c15025441d400c8000360910030001e01075074000a521074104841928000b005400000e81140d01840c1004101e940784032280892007aa4070003004034504075010809407410f0782c4140d030b2004041c0103880c80d1001039074079542400e0740651001a625a07072502030141c1a40500c201c0080c14041091900d0800540c00124900c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 668349073 1250 668347823 668347829
    0x3090f0c0118050f061902160b0702031005060328060e0c0a030f030e100c050c0906180c040902071a060d030c080c0111040906060806092a0c030a030606180f 69
    0x1036486240084085e01c500040740c2540300c4208580c0035a981404009440300f4000300b4100e4115881d1101061400906048450440d801401801d03800034031140c41d130203081c00400301a030500484000199410b80b00080740c1842081e04404102c0791042c0c0343c503a0484001655021807544901c06140e85070b12044003031416a90030040080710860f40c6e00d003c58071002040d014907048014507401b44200d54001c3c2e09020b03001c0c420400c0d0340040c0d00301414041c803c0400c50b035150380300c40e00d2920b50035025024590182c010307003100d00e114a00740c0c40d45594020f9070b00400c0c0489122040b0022904200c90500c00799410401c121a154001c2050f0b440c0148544038194000d000c1d813200161401003500701358040401c001d6010015a251a5070302580700003800948600320129001c40d00048007450031000c0b03103104010400d108104224100d1069600480b8079605114600040140c0001424208080d000f07807102503070040b0f052400c0030030080240070741c06e03022041001d61482c24840f03024040705600903 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 668350323 1250 668349073 668349079
    0xb01090902030d11101a12010b0616050c0d140f0604020306040605071106070801060207090603080f0c0307060212071209030804120c02220605010518060d0f0203090f0c011805 77
    0x14004c141d1180c28100040e860310b443c005031410030301d1540304005070000c002411048070910480d080e101201402d0711282428154440b404000384044030031030720280d0000c14050811203141c844160045802c001c051042910500100c07500031081c40400c000c452076000300e070390190030340d0704056020a80c1d0b018007400c002c0519849000091040703126043c0b016903000c07100c080b644c5505100e01c001d4480c480c20f0081030018007440324041140406400b130348084a9000304070702d25140701c01040d00350942241d640a00e460204014801c0071900c1400508488100c0784070700109801c00b22030107454480d01003c0920081d00b0501301c1004030390040441c542c01a0411300a252500c0307080022103403c0c00403000203500030b8814480318204000c50404411940003050f0800215031070300015606801741320b85280c407224421051440034100400070303181d100329641000c0b4030082c00e010002e00783d0700200c44c001d4007507000040c60311080c00d080115407400842030900d480d25002a1400710400c0c113050240c180 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 668351573 1250 668350323 668350337
    0xe0a171b010209041803121a04020d0b0f030a150c0908070b0c070603060e04020409050f121801090b0a0e03010b040603061a06180105031f060f08060411030f13120207030b01090902030d 81
    0x903d10707110802d0b0400352359008008540e2a149251f501d070060808020b068003071420042c43d007030a0705000410700d8000350052600c44041c1c0d120103181c0003920b02c00c000e8004201206000181404007000888090164000042d48894401c0030084c9800c51950114040505022003000030102415020b40c0280d016200403a4520981c10200e1505101ca0742006040c440c00480003059104180170342005c2c84000721031030610f4118401150b00c0b4a446c050a680034008000e0903032810702800805410040103000414284404000a0110780b8035510684541d40c4403400f100052100040d01d0a104504a4296040019150800411000404407141031010000c040740828980c0600102490149000d80144a44404009025100b00da1040d00428075a2004c0351541c0b0702402400d6010740c0c0248200e05550700c400780156603050103003000e440d4071911900301000c1a44076000416542d015001030031003915502c0d01d4000303404140d108902c05c0d454000144d0060750b002c150120322480900e8400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 668352823 1250 668351573 668351591
    0xd1a040f031812030e03070e01170f06071b030c0503070b0910051b090d08130510020c030a0b061c03020f07080c0306040318081914010e0a171b01020904180312 70
    0x6c0d00e04a090380100d1840382200000007100c0418814102c190f078403140c00d07159405c82034034080f9998101502c1c1000886e0001d0040d030340209444c0001d1500e07600030301d002104005243c03201030031540070380c405581d610603510800c242c0c20000c101c103005409141c0340400007494190f44a0071601c1d00a00300d00051200090300704a2503843c1c1905100302600f050709540d84041221030000e002c8042d2007414000c0c80038140c5900c6140c0049050044000060301078118902d0300d13034414181c01340040000750b101c907269a000c0c21407200401d01201c818403d0f0020604004190503551510b9032990000c0d40560040c2c007440000c1c0c6001c43c0042c2c000d0740c5800d00c000301c240f0084040d03114010703a0b0812034046c032804034401e1580f403044050011050180c8070068082c40483c0e003242c26925404404030382e650220032581d00103095040345250111101e000113003003d107111140d11011003c1000800705a4000c40c12001c0b038682403090409480368405405c00c80c0381c8654000e40314400800f44114565038682e000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 668354073 1250 668352823 668352829
    0x6021504061a092508010e0c0d110c0105010819081c091713050612042612010503070501020303040c150e0a150e0f01020c0d1a040f031812030e 63
    0x9400b0201c0024606061898100d903000c4690008950109144d00d803034440c0c1403100c1c000c180b003c1c1603511880704283c0c5556100704088071a03000000c1d00582c15583c461807201040841c000d402c0e0051100c2c00881d5951501c0d410518105038480e50388100590410b40750f00080c0d0780b40c1250015001100b001e2070700d4500d00c441e20700601c582840035041c40854140c4041810300301008042800d00c4800122059807580c05012241c06036201c0c0070080484240450040385503900c07032018500c03c004040e041c013284200b007050303150010710700809071010030001480344e8541404510064a400c0c4011415864103846034407105413a0b02c140703100045060091180076100e421070018254000c1c041c41412a694098030850720407039480ad1000900c4407000c401c80c3e140c511a9144441d005038018043c0c003900008200c103442ea41902151048000a1a1285904100039042c820b81c090040480a034141d420054000030142c048990710602ca04000c1c04603408800490034480e4040c54280d40e908104808 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 668355323 1250 668354073 668354111
    0x142503123606060806090f01050f04030c0209060d08130305010f0c09050108041e030e040507020106030804061407020310200307080f0a09170d0f020c060103171e12010602150406 78
    0x901354080e142c10054030500004030b1100031072660700204825036500c003410b6411642668003c1c0081d40d6000d0f464058a4024696a0072400040400100300810750700c8200e1030744003080d8100310071401e50040080c42380078410701c048400001010700000c9070380c500c0200016614058141444a0f00010900744940030b4804003000e0180740d124001d02d101070030090400344000120030300c120b04107000103459a2040c0200300403240d01002c82810242018001e44800c01002010b03102020184050741c0565010402d5800035a65a08006051b4900500030684848003003600c80610408001384401c45900c102826405504402c001d007068943d02d83c02c00180032102c030047d180c1e80c41d440d011f420320089200200302440380000100002c0e41c0c0980e03004141d00484040d5100b94201400400c0032810501c6824080900314403058a000f6052414400d564001000160783c41c00201e080c010b400c141608a0b80948a5400203001c14699840422081c0900170401000b40b038545410002c036020f61a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 668356573 1250 668355323 668355329
    0x11b1d090c07021002071d0411010c021f11010221100308091c0614101205071205030405031002070b150607060b1f12140714250312360606 61
    0x303000c88161140d1041c0c0005200151001c0c2c0d000c9070012710580d441c0d8000c6001041e0140e01805a40f280f014001c00c503112b40844000d0710081c0250031510400101d801e01c010880100811a2200880043c59142503102d1000341007018083d10500c0502c04612202c1c141c0d030202c00f003110001a049240b10003014a5860100c1c014103060412a41500d00104102102d00c03414070000d03060b00b41a039402c181e101302403c501014199400415041c060549d09026040901d405001142c7c501561080424a00511344a180910940c042000030030002c500d1145500501040c0010a089a5000016240d8416010020300c0b05543d139900c440c6a486034600003440d9402000c520400c0303246107a010300344000c0100e8444089140c06d44001304120815501805410030b565070b071030107101c494514019680004d00402022515185000f0116640c04a400c0454820307aa00504c804103681441c2c20b071030b031030301c00003a5000c0d41001e040706a820a500b900480078980c85d000550841c42d050400041c280b40d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 668357823 1250 668356573 668356589
    0xf1a1e031501080c0907021f05060307031a0907230f010c08040611060c04143c190501080a090206090406080105041b1a0a02011b1d090c0702100207 65
    0x41c0001816400c0401d04510b02502a41d48009691368a4412a114903074a80014141e808028150168811550201d0761040c00075003101c0455469441c1e82c0391504440840c0d052a0f05101d04014108405020400040100d0320084810038880301c25118000f002034020741c01a040c08600c081e181c0c2c17041c802d000c210b5070044d58050b6169190180100a65844c0140071395500c18840030070703d00c0307100f101190206d44901014451100a060800180c0b22022702c1d802e0054009012020b0004d02c4291400c3c030300d13030700e03401c0d043e0549070107005208100071030b02400c81240311035030403c0080340d07000030106038020307424a400188c101031413000034818011200c140e5007081c6070810100c0c00c1e080543c00b060041c1d01840c06000ba50384c00041c40000749456019428054040c0e502860340805d082010300380c00c006500005c20030a01c04018580080800307804c44000840c40035201c1c6001d0030f6100c83c40d00b08001621050300c1d51130050400700c054072800c04000d004c3c61644010200c154400c0c800a40606005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 668359073 1250 668357823 668357863
    0xa260d052a041e14010507210c020f0d0b061005071401020a091a0430030e040516052703060a06030b07030b0d0f061e0f1a1e03 56
    0x800700004154005005a501000c010314041150080c14401c14003110350480749010b00140150046900b9040780ea803c544d0080c2403004810300310b059071a506c3d10130020380d9450b903d4004900401c0b80d841c84048060b0f00507034081280c00f000c141540242c0e0790011050f034041c0030241d0f818404803500d00c24920050b1862900e640c4104d034404040d0014500b4009a0b5652518151035460011841d2100b050300ca0f4199400c000c100110040b039a072410807042020041c1d041c03000d5880700b482c407841c10381c0006c600207107101d00310302d50501e800d11486030011055854410309030074074075001c0c0913032242c0003c4185c800b00240458209d07000000c81000707002c0c4050259001410990301d4680505464001241d618101740000740340c03644244148240d105008015607179034041910307444141001e60078180c80701034031420183c40300d2048031401e080307001e2452400642c80c500c2da80e07840d041b507040744643c42d0300c0300d903000040c0070303d980341c0304c072281281e0054400581c1c501702c00d00017900e042203040d00140d043d512 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 668360323 1250 668359073 668359141
    0xd02240a1d0d02030c010b10080f070c0204090510110a020703021c0602040e07031407201519060807030c0303050a1e0c060b01030c050f1e0c0a260d05 66
    0x4080045c21964500c00006d0160000084c200124000e103e0034600000f0403c0b030009001c482460308054000000d0700784840f0b10180da80109055a400010940d820b5000b1000e005131254148210310407500c9a40c40d95081a00b026802503d540b1903110103480761402c1e20004c0e01da8000c03142c00000d40341e40150110341e40d0f9507071a11501e840d941100c40750013203440d0100d12400301d900c0c0c203c660b03c603031070310390750168080000c030600e081403105629420f1b094030070182c03d009001040100c00303000e84071088401d1600d56405590354291185904880703041e801041c0100000741c0c020110b48192036141c00c21a0719000c0714041151401880740500d15035980d1469500269500200c0b1381030010300a40c0c041c01620082e00066090360112250500000e07810042ea0403035040c3c20f4003a1005055181280c034022032200c022030040e0b009405000140c3d0041207010040210a0158880501009003540e114801c4125400024000c60005441d850380b40c90001d071889660f081001745012003410010040c9007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 668361573 1250 668360323 668360327
    0xf0a1e0e06060a231002150901020310050307030819020f0106060819020309060406020a0c020a030627051911030a05061b1c091a090d02240a1d0d 64
    0x806036182d50040fa014480403a20391850403090007680d940c0400490400c0c89041800034460341c0100c2201180900f1415110120281c0301740fa004101580c005622400d00d440c00b14010f45031548280d00c2a840701c1c0c41040080d44900548440318080302c4955404a0180c1003682088030304107075621554601400441c0c1075402480d1940165041469100c0303004106500c54224842519188110381c000c000040c0040e0b03040d0024000141189080c1e480d000c0c081d40422407140454000701c44994880146900301603100500c4146100003010341c2c528451140c945035124052440d4603204030440f0005601400110071641c4000c100140840b4501d10a504002d0344400f02624048040a05ea00540d00c210304050203483c003940c0740c508c0c1c0b448200c0c4807110380c0c001002180800c4960034080c0001c48a030340e61090741180b10f07115030409000c10160f03014009050041d4040e03108185016501c001d0038070348000509039806074400a00042c500006045a41c1c1a40d16000041c01c610454140d089426 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 668362823 1250 668361573 668361583
    0xc060106020109030806270406020c030a090317040b041208040b04031109062b05010e011e1803090504020c0c1201060303140301030f031b120309050607080f0a1e0e 72
    0x9020740d4170b4600c561129002c104a13440e2158941d20014092401c070804103a07000340294000e44540c0b4018072300064007010703500715005510144040791941604009120110b41c180c00101d0310412814a01030502425019030701950255451218007403070820f0801130048102c4024100041c07000361216030341d150102501c01c040980b44c1c0600c4822003c0380d214100150190600d0801c24081d40c81c1c00241c0c0101c140c5000b1149040d0340a640301d4103144440e2500b031007240d00002102d200b44149800b0f58603610180c80086880c0401c0404841ea80408039038072040c04425030708120740240e900c8035118030380d0b032908007035840c1d030b0741e0042c2c480c06041144041584980304483c031940316035001090252034046540402d100181c042d075845450703c03001034403590586001c2000c070b60a13480b8802403510744025003d084d036501000300b56140c5100090110412442c0e40c814120301e4207002524052800b0b18101201070700300e59010342c8861600740710303109241c540c9000652025040184580d034201282d501c1c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 668364073 1250 668362823 668362841
    0x1a0304060e16060e0a290403020a03030804020307080c06030a021c0f150506072003120a0302031503010531020d0b010509010b0f03061c0b180c03070e010e0703020c0601060201 77
    0x8698000503403113480c103010300464100d07421040b0354132160504010341908038040c0810701030b0b000c104102c080b005944011340c12000d9802640c94940d981350030b00c180342c50041d01d90040b180c280d00c846007540306565400c0440b9032060414001585610f01c0300300000d183d95a880443d1401403c01d07081c0782d01840954044110702c0140405141c0056440c41071006510841b24050102c0d00e51540b58211021480c0000e82c8544020782211004004400d0b804d1b8030b2741004401400098001003400000611545041c8204c00200c00821040c00c200a40148480803104240c00704240c0d000300407849031a09a240c2041500a00514039056452911a1800d2400d0090500c141521000030400c10030300340c1601c03950108001c10b00c1c5591607450412182c0207400000c8440402d102942200181c2414051030044115828001c000d1a40f003d0381418150041f403618001e40c05448108140c000c0d90300500e04549054108052a4075408403c4001e84500303400303210544204400050b0300340c0c3c154420144 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 668365323 1250 668364073 668364077
    0x50a09110a080a060e0a02120c091005031c090b0d23010b0304081c0e0f01140601020a060b030a05030703091d040807021c1416050a1a0304060e1606 65
    0x120400d100401994051601903031805038810311400340007070b180b13901818101d0310840850309080915030000c0d07000304410500007000e801903107400c2c9480c10000381c0d6035000440e002c40b058100d030624010030381e1410a44111410004140101b028546c01000303484049c16581c0d44803551681a001084080c143d130010b4415402042c00c3c2c10a072081100b026981030750364118000d40b035500c0d00c1d103402445802291085003001c0c920540c009518450348602110703032000d1070282c009044402800c038212a0001c0403c4034a540000070400503a80c003084c1803100d560300071800101c901800000c20318000100030001c100d0310002030040f080c19001507004040796420a80d100300c0c1c80707200340740350f003108003e4030024401d1400740311803030040c80c00c41d21404850400419680000000c1d4940c400050344410350400550449111940d0003482d000f4000050030059403904445864052030280512000d1498901018007201040c1082000d410106441c1c1807142204c00c030268040c0c00600801d882c1c414040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 668366573 1250 668365323 668365343
    0x1006080108010506030601031502040503031b0c010c030806043303120f090b0c03090d0b010807050f100f0212030f01060e041b050d02040302040e0f06060904050c0f13050a09 76
    0x281c0440140100c80c49032501030098840340e4655501c0d809880f0b0229000c40710746800344004103968500b04054504016070128851805685c1620755080c200414007c0d4108290700c0c0c84000403a42280e1800d400100540d000112828625080008402c409001c21940c081480100b0388180310b00169005603406505060003060141d181502c1203c101d600d20380114400d201d04020390a000b00181003008250000e0781c0c038021182d4005034200d020b40e40d0881d45001044018003070190100310840241900750b580c2d0000803021000201c0150b0001d078204200485e4101400c0298406e004c0c58411078418060541c8a080060142a525400740030303240000340610508202898035000d06544400344080c0b50403620818042120164030580c000290a42c08010010040c2c50758852002c000d480200907181180b002030f039443c02c052015141a20803c1c65209002c04643d0114030a04082401c882e00c21218000802068988100380c8403010724a01c3c0c8030070041104615003282100074801c46080c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 668367823 1250 668366573 668366579
    0x30415030506030d021914010e0a0501060b18060d18030207030209131a07180801020d0609270f060501170f030432150d140408030a0b01030603060510060801 69
    0x11390340c1e00c4d141d03200710059100c4000021010882e000c071480c11401a20f000302441d6a660440b0300b55402ca405100f080c0c0e0000242c1ca0901c03c0a10444014211000c4107500e003035164021004441c01107100d01e4032500f00002c844800055650001141403020709444400382100d090107034550b0282d200c1640034841c4040051881c000300d010b007544856011b019100c001a044c2d00314134040070020150b0040c04075441da0100320000964005004100300340c00983d4820703610102e40c0a40f43c260f0310110032141040d11b940c5030304001951442c9048003e454455a000301e034100610020540c0f10068880ca1801c0c0012800e002c0d01850016420302d42400c90340d07046000444a9a6880f880c415400c0c1c9481c42c800c030402c018420415200c4015603041210034514800b40020100c00c03101c800d10704001000a4400d103000d40c103000703248600f190b0314840150361409480d0340e2481c1c4001003020244aa0350340746201c01d030380680d000802039a0800310420143c80c0ca00809280c08400c1d01544010500c030b24000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 668369073 1250 668367823 668367829
    0xb031f1103070503040813050306131103030301060f12060b0d06050f010e10031508030a020303010e10060f0302030c21091501030c1a0415050a031a03060601080a0e030415030506 78
    0x40340200000e070b0f507480c40c41c1c2d51a01ca0004642200c0c500104000c10002c00040c0c40d40c08101003030140001c000d81c1384005460b803402c2c0d040d00000b00b0066000b03400c24030040202e150407180c51850038100c0c0c104500b0307003026185000c0003405107070480070825501184400b0140747d60ba002500b5110255041c9569010781d10054401c030242d941c4003a807106000e481391156501c41c1c1c00c80c041a0001002101c8a030340c0794605141103400030080c3c20010317440400108510b07860710a03ca5001020b100150700300710700744600105110020401032083c141c001000c5a0100940d80440d00c1d2800c0c6072010781e00c9507500c0d00c84a1242c240c269000740040c800e184007211042e441030402030413681e101c004007880903e8000340018040144280c150030200a000000c0c205801c6144100c2c0213000390b90f0150344107501c6070089c08456035615404008524050240c801340c5001841a4100b103007400c1422a80e03032030603000c0c0080d10b80c45103085560f002c0428005151038802003581c10707400058034244016a900c4040c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 668370323 1250 668369073 668369077
    0x150919050a12031514040e0307110103060f0b0a0315030f11130e150403020c090a09050613031209020604050d0c030c1203020d0c031211030603061b07060209040b031f11 74
    0x322070103500c030f003210401440208144019420501a1010403022807d4082c035046070060714080c3d4581c0d503801c81d43c14030ae69061080401070000904205072180c10302d0301c0e61080e4080d041182061603038410966490307103003042190300215448181c403942a50320303240000d004001039406a0013018032403002c0c01e4402c0c003030003039810301d0b68884003c061503002c4044a02d54000064810380550042511800a039203a004116100703c06600300841c10b0041850000e18107107008101070280200a2040000a039000e03181204060403440e0114400846000080240c480d03a440150301c400c036800540d081003c007190240440e40110410b00d00d807030351901ca8a0488600410042c0181c00511100c4817480c09001d004003028001c1c0b0b00491006804403081d070407520845501212600040100880d5203400c0060551004c0100da42043c00100d542d0b044026004808000349140c0e00490b0b20003030317921150700160030740400908441040640301c0401040700600ca044258413800c0070a801102002d03042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 668371573 1250 668370323 668370341
    0x230f0609031623030c100b13050403090e07181a0f0304030e03071202040b0a052103270a060801050d0f0203011b020615010908150919050a1203 63
    0x240d46060380c050840380b0920340c4a1402c56901d440501d506605258090000c110305500800030740d41c4250003880d40c0d1403d0386160307407510300c3c43c1408000700700760b16040700c900300c0b8000c030010108aa8841c2e1a0940d0100c12070b0300000f21427a00d000400610b135500c2000001c80318040c506020240381c544880e00e510041c42e8005000d09401002a03502080351500207561050080c0340c02440c01c900100000c1c00c0c030307459501044501004000c240e05515080c0711b0002e203002c08440c101d40703851410000c24051030601d5404080e0488440c059503514006004480504d10380012131100c0c03015983c440b04240e01113408603801030300c825101244c6c8134042c003400340c10b80b0b8004114448400495580311003044001900300c0e05552a607000e10041d80c007040078101b07200100d0f0054100c40c5014030b144010400000c1c0183c1c108031030f003271003001504008292040d26000324100400596103420a03d85080110040c80c100040d404003840d05003c008503e40700a14440c900320140941c09000440035140210 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 668372823 1250 668371573 668371591
    0x51606090e0610050f070804060f17100b03090f01150e16080c0304150c09090b030106030305120601021603050601080601090621150f05041b08060f090a230f06 70
    0x3400e40f02e0074a0181d0f010380b80212801d01403900e031844c41c0c0d50b441120740250b03001802140c104846c1030031a60300075a03443c980045402e445812413070501035006854295100f040c0f804200080411800c480074024084800c001c00000e00c2802d00320ba92070707a5044120b02c070b0010b41c510301300003041050b600030681c004c4014040d904c162064031401c140c00855440504215404030710400c5286209850b07006104044140303855408442d403411a01c2d42c107586000c80f049100345d140c80c4081c00040c0e04030b801e035014410f059402c407842d5550040141d240034034400750400304486450303000042100000e4400d0681c1d16001c02d6a03800d07640e4404000a594450048070f140145500701c041c10f200d620390074800014021841981c4600c0894174210440740c5055110205540314820082032101d0080b5000001034080c1807429518540100302c0e403a5031000c0c124241d12814000413840a40d0100300d140301183d0001510441040008216440200106000303129401040420440041c000c204144500b01c65 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 668374073 1250 668372823 668372839
    0x308010e0c040314030a230f07020d0204020c03070615051809011b03151a040608090a02040f020903010b041104090e1c02010c11070501090b07030309051606090e06 72
    0x32a552035021240101004100380c001e00002010520100c40042003509400c080d50340c1e00b0300254024400c49805001424032111003c2c04212407480d01e044403c0042c4812025031901250f100007100944040c001030b50141c00031817003071680d0300c0200050588030320400040000030050300c040c520510302c0380300303090317100404c0100400f02e40320000380190f002c0307117100000805042000d103240b41111140c4800e0002552028142d80c9070307d40b01800c1b80904210b202c240c0800090b2003203c0400d124900030003040040c440701042d0311031000c02c201d0600650040051050b5904410b8500080d081441518880d60030b01c856030400c3d040c60320400e003491403402002443c00d410814141c01a20300740308102500d1003002c0504100109090700494000203d43c0041509864250000d10351401c0a2070840d060f00499030800281e0f0300410301c90111203d401c441ea40f61f9030103080c00d40c01041030100140203030140b5418500380c040b01c01e02010940301603440c4d00c40100e440d18804211110101c4100d0b402c0624 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 668375323 1250 668374073 668374079
    0x5090a15030605040602090306040516060216060e0d050102030405060a1107170a0504030c030803040c0f0612110f070c181a1c0203070305030a080a0b0d02040b0613181107030801 78
    0x70f400c010343c07083c06120f01500d0402024040f900c1c240d4100d506441a4100001c0c07902c810b01502c103094001c080900c02480007002e43d040303103580508281704400501c0020a040030194403031450810640350090021500c9207001d0070310703680300c440445041c401540f400c81e00007040704014081e900555003103030041e99105080015500c041d07002e406490140301c018000080010129070100001c0e40c440c1365000e4032410f02d850403034220350860700004190080c642c010301032a940300040408044c14607101058103d150303000812244145002000c0c11310f00003c54005004001c0440300c103e518a40000f40141e07403a00d1040c080b910864820260040c0a2090301c5441c5003000790146101c0b6800c05905440d800d40d4002490b041461344103e40c10342000c280c28407815001000b641d40b0508004040c8030a4060500007954042545402482160348201d085202e880b0501a1200d4a00c034001065030503448000c0d1501036030000c1d0f400005142001c075a46d921065840554070070952540310036802340d00b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 668376573 1250 668375323 668375333
    0x504110a0c020915120102210402100c0f1a0402010f0203030903090609061902060f0a050105090601050304110a061206080a0b01170a151a0d031d01020102040b0c0705090a1503 77
    0x1c2c082c1054410000078030710340206540d17011a18620110200005a560480662440d15403011940c40c4462a85030000c00000d626840e21140d041c802c645084801c030281ca192003403c1c1050040301404c4c01d99140b1108206a060400307a86c0a58004d0b240c040b1901100c100c102e07540c0c40100ea4804c516003003030051480ca82805806420f0740e0900420640c20421040407100409090141d03400c016401141070001d44080041e103581c10900b4844148031310341c100408541c0031b2801400b100e040080004c000390074018054480c1e080d20500500380101141d030340b28010800c246103484407960501c2d04c9400207060070f0005032002c2c107561100300310741c1d941e10f01526014031241c145201201c3c0d0144402e690000f58441c448031b107400111000000f000c40c080c113060341403a4885411103000303c0d0348210800100350081c08a964036050244407030701400c4a000100d000e4061584001c80340a070214141015a0340800d00005851050b24109455591015030ac3c2c140c40a901c0c0601c00202001020301c0498 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 668377823 1250 668376573 668376589
    0x105030c12012c090d0513051c031209050d080c1b100e0102120115050c0712060501060807140315090414010e12090d02060708030414010c02161502070f0f0504110a0c02 74
    0x2504400401c0107e50b02c2340440c0c8041100c3c1c1421080f0b0054503004002c054100b203100700c80051440040168000999a05a90300c025210810900504034001560b440b240707400c98001a145054820b0003019600f0403aa031180e80c50444401241001d254102d06c03a014803d0340c003811590309400009900e0400103044c91703101c0000360410040100300340c080c103c00802001c0c000304038215000e04440124280401140c0301a0024001c11003800d0600c803001d03a01030b4821101e110901c801c25a280c8885000c1c5440d14404012240c11450000400080c03000c20810740b152210488001e01052081a1125880d2070040280c0103230900148078211080c14100280b411840c40030300028500411911250106d4000711411154072020107036809164000f030080d55803500d5140009e100000c0a1603118002c840c090007510380e03018500101a1340c2030301c00c0080000410f00c40c2c42c451003441c0c5413203051075010924003c2500950500181e081082070741d9040301c45100c00d9943c0c256804007a5800c000e120 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 668379073 1250 668377823 668377837
    0xd021e06060910081603050d090621021306050c0106151403090c04051f0504021806070c03022d060a200109051c03060f030f020105030c12012c090d05 66
    0x2000d0450000c9034043e003c022171440d0340e18840551320354503e03501d8610f00d00000c154041c000c100724944100716458100c0c0c0740c140440101c107401c00c0d45002100075100203000b0b0707803103034034000d080203070300085c001d802c08014440903501500a000d00b50b100d80401d001314007900005c000007690805451050300100003e550044400000d803580c8142540003d0161340c02a1071140f48600784603180d0300040d04002440000b004141c600750b06003944081d04901e4080c40d106001e015900005403001000001382042001c0d41c0d000301002c030300d00207507841c4e0342820001d923002c219140940c030a061654a80394080e55280c00721036407000201c1c04a00003d4580c4103000d507010650350748900300840050000d04c00d003004041810030f112a00b607018200141a19003035402521250003842c01800403c5102192000c40ca0f0203092095407070b1240e180890040c07050041c0c100000007408004540d00c2c0010314114800300c140b101a041c000b0402a0311211540c050340c503081c0310307405200040900c81c00390010388a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 668380323 1250 668379073 668379091
    0x30c0f0d0e010507050d0507020624011418270406020d15030b090c0105040b04120804031502030a0e03120414250812070b0a020d020f0a020d021e060609 67
    0x100e101a149007600303581007614800c001c9000441d40760b0700c5814920074164440135610080c48030381010700031300c0d452140403665003050322000c440680907a401805004143c41150112603a18a048080281041c01c4680a1442282c010b01042054800003142d400b0f444900d081c0040140c50f00d80da810000d6000d00503004240d80c43c0c29640e042000c1185240700214003070340002807d490b0110b030a0b0300704415090380c54107010003840144012a402c600340c4d411390b0650100700c81441381904101c201406070350b000420b04a00d4181490100440760003031401010487c205001c505101d500040c1c9901401183c0c0c1d02c01c4c00b070100005d01064a07034116040208021003560f80e40d411090589035480b10004038460541e061610030803e601c820001c019541000440150600c401a920420700306c9003d02403c240c0390300801c22400d54500b40d4111060004401e144544c6c50941d0b00c4080e4543c0321034000e10300540600c003502d40c4480030800d140000c0c545200c01520680d5101d404014590002a00a01c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 668381573 1250 668380323 668380331
    0x30a0908070f0209070306080307020d050f070f0f05010903020618011418150306030a030809100c020a03020c061912020f0301080703050d03110d0b0103141302090c030c0f0d 76
    0x1140a0034010300744140034a407506040307102401841040700d0003800d10420107151000c204107121022050b0b03011558100c0310b01e50500b1060510f149040d07031603841900b43c0c1c014041c00045007002c004011013200c00751340b20903e03000d0b41c600c01541c548949100280d00002c040050050b05c0701c00c807a0b4400304c004141841900c001d580d50194038107802a020101e100a403c4034442070703078900100300e041c01c6070704c100301c1c680b840c41c2401c0804c0c2c0703494030500c00030180100c1f8004140c052406104058481c0032001c3e0411213500c3c0643c0003176868110490582c054010188804160b0805000f11781356a44040d200060050107000d007220342100020520240c40d509110b480d40c207590a0005500800c1a040105160b605605181d0b092610713280550040c903250403140c03469401c100003034030581d0048040000c3e1081100c40160058111414086032016401d020009411421104803500301c0c02a1030f508515618116110b40038801038942480001040c0325481082c00d8810050052288640d0003203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 668382823 1250 668381573 668381591
    0xf01031817071b0311060a0e060304030c12080105030316060b060c01020405120a0b01051e0306010b13120506010515041701020a1205060906010f140c100c02060f0606030a 75
    0xe0710020303800c0403103804a0008260060080709002442403514100c010400300349580e642d20000805a55501e000b0040400c1c030110307090003110010f0740d0b0a400740c00c4640d00d02c1c051038000c4c01c0e410a00e104903500c0c4154403410039124803c0300c4260507200007600851a2a44400e440020324491a1084543da6114908040c2549400c00039001002d02d203000980c41c0d034200f00800c00f9441040c820711b400c0d5803201402e0f070046020a94158110303402524481003040c21850103041742900d000d48640c040c4180000001c0c60040c0f04001d22042c0100f52420b00d000340c03510540341d040402a4805005540070b40014041840c00101c540315034003281408903d404c0d82e0ba41c041320485180e0602d242580d6000c00c203101d501d6002502030000842c1508100854a4144001004450040d0001c0c0c1000383c03492600a80c1405005103002c0d10149007151921240942000c6070703a800100b900690603400c290200400b2800064030b9406003001a00c14000303a900c1805012242d0401032200d454140c59010324 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 668384073 1250 668382823 668382833
    0x10c15020409062c04150903090905040c0512150c2d0901020705041812031805070f0602060f0f07051216170702150c0706050c0a02060a06050f010318 66
    0x20000400d40c0f8040104569a225031000700d2129058003402130102c210100400100d9051142007000c00c82c3c0c5000801c1c1856040440340e690160f00041c02c594076160034041802410040c03181202e408444108d40401ca0542d001e4941c00c02c00c440c024080e4070480803030351902c48180a0300351703850005449128246903c4520050300c1440040e0004c4050000340100c042d603044c4013a6002e010240d405003c030304c10113078426265400200014041180c1a1222141c06209410002c1c110080d00140c59500c0a01d0038440d80300c4119210f1030703c80e19108480000c8440c00851240c0c03003841c094918001940c3c6511021508210081c0540104001041820007a404480b01a03000300094081c00b104103440c030301d018090829040d0403419840f0018200008294000b916058840306500c0c00c5e0a40d8966942d10a114040c00400600c11802c050401038a0340f001c1d005440040ba6a5084440742d442c2d03804510304581140c09015040f4890902c0c000f03855000350440004200c42005c0d074450070b881500c507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 668385323 1250 668384073 668384081
    0x7020f121509012712030209012106030b09011415030d2102120f1803041208040503060a02031f05211e01020a120608070905040203160e0708070e010c15020409 70
    0x503550055138041d110000307203e140300c80220300e44054101113207040442c0340080c020341034803214170801000c8245a07200e070f0000794200000943c0e00c10701d00d5441e41001da1505001c7c100c001d865002582114002591050400d28044600007015000e803056002101e0111040401c0e4494011050000791560b00c200f0369604c020442007500d00d952107400d040c1000414080c41018045c150030000d008034019045c1800700848007107486c00395840e1100c244e00e20f00382030a401103030b011950500550741007058030092900214490405102d040d89820120300c500c1021880c1030142d1500843e50320403911154061064500e010903103401250b82c060900c002001c40e155030a0030b103d0550350041020300340c00d031b0032201561003100403003418056281060101742d911b08581c49143c400135280d802040541d00d0034003034101c8090510300c140078010b4803014031941c2040709840201c00510800001440f2030310402a9510880e0141c0d192001860b803611124001c100d50080c113041550300f004001005441d92103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 668386573 1250 668385323 668385371
    0x40e011a0f180111030703080c0c0f010609061427060609040e07180606080a020a030b0d0b1f0305252c0a0501240c120507020f12150901 60
    0x1040e0b194400440c000104011505031314440b0355801444a0030000b074010381c0183e40301c1018200103440d000344c402014070380040d900c0700700001e520744200800c410045410203815580c0401100342c6403d59032003070020b400d02da003140c110010030341c1a442a4142c01d6003010758000b08000c1843c0d0400c0b2003140000c08a0b802074145d0006680308041c200958000e03040b80074014a10312208002d038620f0210060b10501004210744450f980c0051700300c0c1a24060307444050764003809844000100150320b4008a8100c0a40c1c4920407990890000084000441a44000e4039031103400380185041e00101723050b41495030484090010070000000c41c4500a520080702021184680d900072400410380140a02101401e402140c50a0400520800501a440300c020400c071404440744040880c10454400d8868000101817800e14000c48400c0c99000028042241c000c5500d510030040c0c00c020002d400400380c0311102c0c0fa4105000700844482c1c0413280591218a29002107004603180c1c0405c03400b01c40e640 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 668387823 1250 668386573 668386597
    0xe03090d08090105271203161106040306091412040b07020121020a020a030e120a08030a0e0712060e0a0308060105090d050307210c080d05180109061a010203040e011a0f 74
    0x401d2503039614009002c051b003501c0d09406507181c18540c075030604040f106106c025190303683c21541c3d6551a269441120f000b540c02207020030000074286011091024051809240d5104604165061800a8044400b140c22048842d450251141d005640e02200e503038074000700940d50400c2100a4109000418003041e16a01070301d0011103615005d8050710220621703c1c003401d40301503010307040600060414070711a0020011a00e0b5580d01644401134000822410024085d40c000013540b02c483c1c2c200402d08502c2040203004e01003040034081c0e40c95180007009000100050007007042940a007004000c8080094140e00440e80720b0385070a49590b21000b022603260384a0b1105290049144000c80844401481c0c01409420591078541c050700a0310140940c807a030b03a0000c40c0d00000d00410100c000030b0218003e11805059090040c0200542e84c000c08032250025500440d44d0301c0482103d0540703100e90b5603840745900b40074000300c25100c0c011180c58480f03000c0000701c2d1102c01c8000540f006810345 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 668389073 1250 668387823 668387887
    0x1606050105011d0603070804140106240f020d03110c010e0c040b100503071b0203060f040b0109060803030114120615040b0126100b07050708010e03090d08090105 71
    0x1c1c0c00186141d440b000b4146100d5012464006070782e03120300072260012098039103011a80c55509015072a2036410124104035031030000001164514008001406c5e6041030504011104910082d580c00000840e2a401a044800d10b1030006000f544a0f42a0020b00307054203041003a0400e0090031035285c4c41b0041501d50000441014621702401b1300140c20300e00f965118800c1c20310000150030b0f40030240c40803050011500c00308000c0c0075100c16021859400608a81306410445031003000100c0a5030161584008031001240f680c1890207100100c03212103000707614603881c0c0145100105401484607074050f101d8002001007078030800816014100c1e5108044c9249000c0d01000100c80c110072080f41804011602c180201c921007400f02880007a0201c4843e150f5100c101032042410b65030003a610150002c945c003014000005540c3c1e0640d40004000c0201c28846c903049562030145030a281ea0050749028260b00080d40d1001402e1001d2040c1009424154004c54080d0500c1d8154240000f000034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 668390323 1250 668389073 668389079
    0xd020c0f01020a0b0f040f02090f16030e121617040609050108011d18010e0a201f02030d020304060209090f071b0311011a0a062d0516060501 62
    0x840305564000803402d000a10f0300309200c0c0d5030084000c0b0001c0c00c803804039070804005001e111a4420600c202a0b0082c507a00003441c00c0140350012010a85641181081e16010400c84500a102d001c104617440c00046c4841c50100702d070300c903c9900141c09082148050700190b40042c680540c20030000b6410010191214141040145915072980c049410440c0c2c0000402c00ea212189039800007401440084071030350703600303007100c01583c0000701e00c1896503182c81c82104001001050450301c16121720070003800d982084600400301481414220b9000380c0c0380d0180e5080791180881100b008403940140c9007494584441c3c942240c008030760503640c0c9600001c0c00d81c09444d001549907401100110102d00a007040071004100c4103800303600303000111100c032001c4149800b550600e0030f0b210903035000b80b0020b18010500c01815640b500002d000e19941d03400481c0071401402120076001a604075001c2031400c031491079110808a007101e005122040041c40200b0841c0e0384d068a00701d02821012590703500d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 668391573 1250 668390323 668390329
    0x50a060333020a0e0d031d0303090a14010915050910030203070c03030209010e0913050c06041a07030e03100c120207080f0703030b12010504022d010c050705030d020c 73
    0x503000c09000410350310314510344811020515004071003581c00c00688524034514161110b120400030f255000c1e110314000001c15620505480c0860350701d05001600d41042c1052650703900032842080e900c80c103011000e00c207408002030103d6070a50149800d4565540d1140003400017024030005000051000519848904100c09008003e010307510b421461071510600c0100280c1d01c02c00010101600080d900100768815102c51407100b000500c1601e960419142c40719141e2040c400880340d5000c0c2000d507a503e0b140c82010b6504a62a10500e070001d40040300c440340030303940641001c8003480a0f03194a4038154034100001c000141200c900050912007107031010300600c0b01301041900701401004118001803541d02980c1144410f401002d440d005c080c501a0064200055070940225074044018000001500b2460080c2d001341c2e81c04404030402181481c159440c0c001d500034544020604900d1540b0440d41c500c0b12034002d00945903415110701c0040d050178040840000140d1021502983c585 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 668392823 1250 668391573 668391593
    0x4032a0b03070212031e040204020d0e011e020405090a20190206011403030904020318031c0c0c0b040f020409021f03050108070e04171c091a010f120201050d050a0603 73
    0x110182c07074135045180808100d501c07440d8000142d0600c02400c008141107480d0341d0150b8645001410084c040020580006d6000740703440303c0f40c542014000d01410090035520320898060712000380101042c0d5441c114600d015181f9a4028500e0301100c0c00d0f02060003501c20054001d03040b00310312090310070010b01402454510f06030400301c402c4004d000041c0c0c8581e400000c407800400305460144e00d90340c076044500e400303818142183d4810300001540c4c403448801c858100c1c01d11130b0689010015402142001c8440b070411f5140180ac042050020070b02194500c0c80305004e151000748045070961055001c2002c5002c45542d25145070110012942031a426004590150422500401040d81b034112071503c48117016002400c0e0240440342d880000d20700e0021100d481e1250042900c041c58080e60301340003402841c034160782c1481c980007003170011405804260304035940113101e01101800d140f03030b040501d030001380c0c103d0500c4410000e9030301d000610301481c0d00c5000d05070301c001034180c99410960f550b4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 668394073 1250 668392823 668392843
    0x1051c08070305032706160903020a0b03092b0c2909012a08060d2a1203020a02090c0d05100906060c03022104080a050601170a0804032a0b030702 64
    0x890031807800002c0040001605644601c07c04815010f401c0c004a0903034441440d070f00701a42103103442d030020410711420002180140001c404032100782805c03041240c0166104801750304544030103043d03044011321500d104580c3e1401400707480c00001441d80d848103045615441c11400920440c100402c910080c89400e070b105109225100d9007644255a85200303a805800785020300101e14042640c90b1075803e4034907030b200e9009400400c10091068a40c00d46808207484140c410010200411010006418402c109a060300280f21151303542c2d00300541c8074002080310204880070300c10400421110300500c0e0080380190283d0f00a43c1c1030041000548040c4d0700706805009843d039034000000c1d800030350600d502456400300d000244110344180e801c0c3c4621360040110b41714490914003806030221f1030f281214103003003083c80d03540000c009468442e03c0e2003a02070001007003488208081a4070520b01000d0940c4400b910860b0032414158001d6128030f034000042e0300c1408400c010350340f50100710030848 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 668395323 1250 668394073 668394121
    0x1101020711060d060f060e0316081504050c03070f09050c090a0905071b06020a08010e1b030a11070b040c050f2209061d100203070801051c0807030503 66
    0x5082141d8a882030102a0800c1450240200040c80340142c46158404005040b86280e4140c0c031607600e02004000d000700b001454441c0c0903000d4403c12100641e82c00d5011034114001500c0841c1c40c4100311800050001c20550710780c0501381000009680501403840540302030b0b0f003055420341c1090000411154020b029001c480b00c200241c0f03006a440055000071102e140c80003207415928041c00322000c2c1e03454003081034030070400c480c103508000d1690054500340003d5580c1d034045070383c1c030b07800c2c0c2c00c14100507a40034188802c045000d461419182004503030107440120080b4420315240601003060340100d1094451680360403d01c01040f01c000480002490100e602c0081644001d0029114107920b004844c2d11070000c03482d002c80c00409802095050342c003c0d07400c03c00114822001100c44030180408112030141c09011002c0c54000c0c4282c80c01806180e030344108907824003047c0310a61580c040050703110500d0101410020f4125001000e4840c803e81c1c0e429100d00f8041e1040396201804800c40e02c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 668396573 1250 668395323 668395327
    0x5031305060930030412030902040212040203010c03050601050f1612090303170103050309130f0615020d03140f07090905010b12010501020309090703110f16050f0d0206043807110102 80
    0x950842400c25245c0250700303e80c5688410741003601c150000c0440850080d0054004640010380e518140d080c140705500a038000e0014031070308441181160422260300e404120240013040c5506051805010659441480100203032010385034890b0034500040102d0002d03e2680d402c1c8109540040c864880b1002043c941c820395046580c1da0f6220f01607c0100340c01030f82c81a11403040c894198110150443d6010001c04c012611058100f410590b891406070140c401c54400c600c0443c03281c03003010b404069160050300983c407426189400d2410240042c010041c0b2001c010840000302d126840c001c003194164141d41e1a0301c120a40b128a00580c0720300e041d50001c0c407062215407110090241d11900601e40041c004012110007090f900540203074a0340c078030000c200745e40020030300a084000140502c0495403402e040d0804181e844031303080b11400c0141c11040104000681d01044032080f407200800e0822559440c41016003141c0011201c41e506100c1a8144030f0380c0d83c0c01c1540071054500e200000c0d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 668397823 1250 668396573 668396653
    0x60806040b0f07030209100c120c03120e0a0b0a09030813080334020705090c1c0f020f0703270f0608040c0806040503040918020d03050313050609 64
    0x180020000800118114042c4030004901520035411608100c800411100701c00c10203440043c04040d0003501124140555001441100e020700c25601807107030b1654070740c0352050548080d400a0000142030112078800c000050001441d103054052040e03081d03200018629080303003401000642c0142c60480743d02003050010000c110304130122544158142c440c40c50540301011100b540d0039001039aa00c04244203c2c501000944c04146841190790032030b150b0285858100d9681c2c1c15205200140c000d8595904101144640303031740290745018a0301800500708282c1c54550002c42e801800202c001606840494803da50189000400425a24480307001c031401d0001582c0070004c03502401041c08042030006041005210307507180038040d8201a1041c90030a490040d91380d412a00642050034240540c50314008050b81c02000d070940c00600d2101e0a0000b614141e5032940080e1240f6580c0d1010360000c0040b6000b00b00d9640188041d1b0b00030000c1e0350303000d03941402034826030540e00e20309440c8403096 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 668399073 1250 668397823 668397833
    0xc030402060304030f0e06031e01050303090a050d03020c091303172e0b07030e10230702060702030d0e040e0c0f12100c09140d02031509011118030106080604 69
    0x1495116a15080078000300e054040250b81c050761101d1b403103a01500c0041004001c0c1d0880520020400c548030b80ba0303040780d0300d980030140c503406513b030500c0d0814010607081085e89800350211040c0c601a00507034407034030b901e1004110815404c6500061100c00e103000d60b03040690064100c2010440c00542d10154101280740110440001c0d030014201c400114005040540d002c01c804010150001403550328045407901030408213000c00002d1280340405403c00065004811003071900c403842d5080b05001100803000c4440360491301c0c0580e00540144040f40050301d04200101d104280ca03191000203024503010407041d0342c03010b4140107c641004a40758065150044451501442210000c0c42103442da18100d00c1c00c07441d031b03801410072802c0040c104e40c01c640001c3c4640a540c00d40c1044004401040107000c01d801c16010b00075019403009864501c800d00d00c18003103421080303020000c284a205a03034081030306d8200ca080f020030001c000c240d41841c0d01d030900c508002131040402409a5242035212 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 668400323 1250 668399073 668399077
    0x501030203061e03010f0207050601080601060807021c0c02030a110306010603060503100c0c0804030b070e300c0301151805010e07030f06050a03050606040c031808070c05040606170c03040206 84
    0x207035103d43d5034034141c118400e41d42904124206080301c1400c648543c264204a0383c1c4c1c81702071044c0c0c46075024800000c03070082d200f50071a5220707070165001428030202d054688000440e000c10039004101440d000a03005030780501a9142e134502910800c1c2c03ca01c10b10003094200201a4051000e15282903000c01460700d0104014000000c114400900000c500340c5c1961403100036880103000304000240030041081d40d0142c9402884180c1e15040200a64020702c01a60700fa00079603101c5402d800c502c0350b0341002c0301802c68031104600c0156451f190340e00b4003082c2034801440c43c0004851022100f8000750900c0740030440f85980e010814031841d451700003254a0b07280090107210030151a201d400703403918903070342010008002c00b41425082c590b91f0f041c41e60b1102000e4400034030582c1402c132042c901d070f03200e4051410000301c940e107120380040710307942c58001d0356010f20401c8469121501d00041c40d5501d510a110050030240c444804c14403910b220305100c44001802204030040c00c3c02408003507220201 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 668401573 1250 668400323 668400349
    0x60614011403092401090609180b040516091a060f12100e01090902031506010e12070b040803030405190c09052a0a0905010e0f0d17030c13050103020306 67
    0x500302d82e0703902c48000302ca0400180081046148074182e400030000500061580e0495000101c00c101c3d2a4550801c60203072060040403559890001d24004081100b00344441e400901c41d030200e40c05181c0001c41c2c1109000c455201c0341050341d803035188000381411528608951041101c00615040030b22414110394022030b118403040c0e0800d4800150319040f16401c41c00980300036a110021980d50301d0030000540701100e01280240984819004407440b2100b050380074800c142c41d0520348401ca403041c0600c03207008001c0804580300c0d9610000d0ba82c44010f0061014000031000342d43c1c4da14040c24014130b030030441d0382440d5408621501050104c1c90032041c00301954800d440200d40c0352141e070620190340400900c1c039925030b1100481400b40a8084001342000315180e01c0f0543c55594503401034a02c60604e03540281c100c0c0700c201901c1110301c1c06000c1c0003c840d03c0380d807060441b010820355405580e0402c94103c00b81c084000741070f0003c001e455540c000140000d10b000e600e149054000300f4141c25500b1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 668402823 1250 668401573 668401607
    0x606010e220b010c0614070e0906090105090712091101080702030304050d08060f040203240301060e221b090f02090f040e010b10030207021c0807030c021f080406061401 74
    0x81c000b40c0450303200f02001d0381c20540015003403000c0001e210318009448803c2e901d034400300b0f6007440b44900c1400c208401a11900700240200116071801040c080f10400041c101401c011301c0c0a500c242180302889411942e034024200f44002640c2e000024104140c00380076541958420b00810000683c0050815018441460051010b40b610008501300c0084004401d03400740c000300400410b0440600c90003902d075600d209a40182088500b410b0817980340d402000140000000006c08560081d14a80d558412922a100c0008815160360300584200c1c1307101d001e0500303440410891502240201078410031020001c6181c0046200055054402c1d180c03914021916884a520403440030340c400781d0030301d8000e001040e054483d104010025800303014102c0c40b07a0b404040d12074100402e0000c0c010302c1548038000328038014007a2800d072041c0f010341000301d80c0300030314032400d0b004020300a04081c1e0047d00d03515a454070317040c1403500c0403d40e441c641201c0504068507034205411780c2c0c00314007074055a000d2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 668404073 1250 668402823 668402831
    0x6060301030f150c02060a06050a060c030c080d05010e09010c020d0f2118020406080a02063a020901030c030902030c13020405100903050709020a0c0803180f0606010e22 74
    0x2d403400c1a44a030301507020f28541803810040c0071540743c01090300342c030480c52807004010840e212010040004200d0198000044000b0b15810000703000300d00b8003440c070f80200b84c46403d2440e074010a005851090304821f031004001c0c4240803039401d090091007101e0840c4d0001c0c18043ca5020001096030b404140c1c034404101501017240b043d552890906058032030410014010314000e50803222442206480480c0682d14016000500000c042010340d90b0325030040a640c0307032003542c49403088001c40d0b42006207031401264030100e043c2440640103510750707950703031002580343e4030254009402c0f0750510032080240350400c1404e0005903004a0f0b10b04070700714100c40d50440c004004103817600034001c41d00442c0c1c20000f0382d0a403088054000c038102c01281d20803000c5644040d100c070f41540c03d90052522000215140e003003c900020f42001c059030b4000d40076501d0000140e0080b0324070703243c41c40e98076007205140c1000d0240184d5582c00115400c54082c00d80383d50410740b510b0072132802da02148140e02c0200980d5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 668405323 1250 668404073 668404103
    0x142e0503150d051e2a01140301090903111501050909010902030f0a06110c1c0e0d030306081b180402040908070b01060810051f02010617030702090f0606030103 70
    0xa52007204004401401c40c018045062038165528800922490701e042c0b0304080207018035800107a50307100d400010700821900b000c02c0310404105510400000c0c107001041d0030300865480358002a44c0200010500070480c5841403d001c1d01c1e032040302c86620b410740c10114000f070104000500c02411540261640320051b40d8803901d00d401000f0208009506d80038050035a103c02c80700003509100d49004080030041e4141e03411040c101740c450300c0c200d0107407a00130713030461203024207001280c00c4030b80b0b00d17800c0551400541c03400091017400c40c0b0104038046541d4220500c180042003080c070842002c80c081c0c03210110310140000b110814140044c1c1010314901c0005411921680c0049010b81d03400080a038032151245458052842c0900034803000802990029040b1351076881c04004640015141440c050f0b4460455009800d06900c9081590349941000400040140e0420032001c00c0401440c1c4030812481000001180135000d0190300f0100010b010156032484100c0781120b83c080c641c6030031244 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 668406573 1250 668405323 668405341
    0x18060c0b040312110c01090b07082202060708030c1309020315040b03100507081501021504030c140706020a060b060906040e09070503030a03050a050f190e030f04142e0503 75
    0x1009070304058900d0f0005c0b07041d650304c2005400a4034100c0c410103d030b0456954800003222079030422111440d444182c42e1944006000d100706107107240b40040c000700d140c2071603521222060340c0190345000401d6000a4400004031119009101805010609520798200440c003a0407845002c08620300c100d54070f11042c10a664104450803018071500b8040c0114506008041c041450031030302c0c41071050135043c007000030f0b43c40400d0b55907034041903101c00c82043e100d548003200c00102d980000c55070b000c2441005000340740104542d00c000e2046600074082c00d10b0710314000b400d0703808480d060b50103864240a1030b40c16582d21410780702502ca1410800d085a0b4540d00820f1414209a11107034043c00001640243c1940c50303086030b4815041e041040c081c988540d003050001c40c208131024000040c1c80c12070894140060340100c241d035018001104d080100f424865a615885503101011025080c8440d8020f41080002c1c190803ca01503801c1c080300841d0b144081c41d0003810140f16040007800000908000303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 668407823 1250 668406573 668406581
    0x3060620030c0d05090a1d0403030504020d0c0308130f0f05040c091203030204050a2102130b09010803030a050f090c040f060b190306080f2d06040318060c0b040312 72
    0x10b5086044030b009251040c0040d0003584030040d082e02a4043e01d01c00300783c00c60209215804204d09070081c00701d0350740d2510110014070010780100c0c0d002030b1b010202d00c0810441e010b43c102035400b81210b0b41e41d81040000d0700e01058419400380b00728501111040042c0068400520f003200d800740c0b404289541181021503421007160000c01c24111055140c1e014554541d0250094502c180e68503850705444080383c600b203003c0e007c0c0303d01843c13083d0b4048000600380b18000902c21565003001140b00000000082c41029003604840c00e1030340b0100422510075028014290407144550504040b4201181250b4507412020000e6002e161141c51400d040c0646510040082004c1805181c640c029058a8a1500082100030700041c0c1003010100d20050007198602c28412084001c090719400b03500c0441e4500403007002140320a01d40c6800108501003401418411403003aa2001c0b1503039056042003180d0b0006412000030800202c1c80040024007940705a0f8005403d800c00180160454003000054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 668409073 1250 668407823 668407837
    0xf0901091a1e01150e0a080a02130e03070303270203070b071e03030e01112b110a0c0b0c070804171c0e03100e06130609062a0306062003 60
    0x703082d40c800009081d4030024441140b00d140f0343c0c032000604508000c02041107682c0c00760706030681003164007200600d0400502400c0043d40c08011400b444202502804c54001d01019000b01c1c0c1c4a4411003081500c0c50f1043c1086075803040b80c00740031407040d0040f903900c0b811402200404240010080144180190b00c403031400b2034031a00205c00c4d0100d281c0140a086480d810504660a03c5c3e5640c41d50f40e071800644035104010100c104c2468044485410610740c0c1440d009801651000c200a211161000500107001c0c1740d103030340490200a00d480b0300c4880008081ea1100e11040c89104001460241180c080358818100524200511a0024100700d4040b6041d154610b1804003011000d400c200c00000d07183c4100d0640c2d40c2e0204c603040203001da5101300600001d540002c030009041c1c412130040c80c140c480c05200c000903004500d5454008842c0181e00703428104107000203201c03102c041d6000012840803103140030300000b1718013030010301450b00008032010841508019229403100400580d004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 668410323 1250 668409073 668409121
    0x809010c0c0e0c040e09070b03130204090b010b030f07170604021b0f0708010b03010506030c010c080f1602120c100e06090901090e0c2b08040b030901050f0901091a 72
    0x4141004980b10703101350320522910840c5912840001c0c0406000324940701140d214a11171403031a42ca94050450703018070100100ea0140e5948111004103c00c111200c0c0600034140641d5a00d08200c0c103400c02a0070018600c4c41001140307685217004c8101840c9241c6c10000907180542c90b081220707810700a000803c4000c4a0718403c0041d015110000000c00e03000720f4910400030841c8461020601d401d07203030101d6a480e05a44018a02c07101544a200300102c564080c05501d820704004d440c0c0b1408580c40072103c1340d221541c80c0714a1044d468108107a00c052200480201302c009190b20110faa02e000700b210381c2e420b020682180c5105510782000312014810000c00844640d1b0f15010318000030541403010078807a110718100030a85013484402052909141d55801714001900c0c5022909104054403c50780400180000212103000d08040c6000e4001e407000410540380585541050b000002c204150303c0e81800a43ca0210712189255150308500011480095035645464165041c114960500d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 668411573 1250 668410323 668410349
    0x60503131a040c050a1a0d021207020f1b091302011103070305040e070513170106121406100b090d020316060f08090a0b0606030a0b10030c1b0809010c0c 67
    0x1581c18021140984164814480c0484482e290000d0191a0146000304849485080c101c6c895000800d00501526010008050b28140c2e008072200442c040940300b81c00507a1103194001000c080500c071310980196903507078260303640014800055480c24081c0400da000d4211b1190700c1e0540e4803c00c140d211080c07a440849996040c0f619000b011580644141e0075180340450106113001d228400f10b40e000c0c80a00f2003070440303034140040300c030444117003000708283d80d03695501c0007031403c08011003041e2640c0108016104800c0c20281a030800f00c0081145607440036204003800301c003000d00141c1d00104030544800c01c0004103440441c0c90414016030b1a180d8260180c800140c8a501140e5034250f08810380d1800043e40b6000c4d43c0c540d684004400040440181d480040c4503400d000d4091075000c1005031001c142c0a0382400071444100c6511840e40c0040c0e00c030008a15282d4001e68880101d082c0c403d5103020030f10440d00c0d4601070780038000e1410704012900565006000b5200349982c050b240f05a0008 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 668412823 1250 668411573 668411603
    0xc0e150a091e0e150105030f280e0114071209020109090f05070f0519260925030f0204180512090f04020c060609100e181c0906050313 59
    0x1003082c1025115070310039030b44032400207111410b201d0070360001c1c070006841e268115111130b82c42054842d0020082c0075908802158818400d0700401c1780c002a13020340000003507211501c011582555416070200a00340002130901c0a034682c801d00d0f6044a00b0252030020f450340315440101e40458407540450640c60904107030301e0b031102c4e0070340c4814000e000c03603102c28000e400d844005541d280540841400c0c3d402c1000784040f00d060080da04001807081402290250455034203100265203020b407101c4041d9445044600103111007100d46030000040154000920391840da02c150811880c4103009006940f100741c0d10031303503400071007454108a40c80350035601e807004154501042c9070000086248200301c800c080303003d281494822516a640110701822881c2e9414082c0192445c01604000541c100b00320000341c140001038110b401102d24110b101a10100004410303d811500c00000c0c2c1492241d1800d804810740000d01d44048540301d040c816100d03030760140fa00305c3c1e41d8a030030350151407200380c20000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 668414073 1250 668412823 668412869
    0x9210f0c030a091d01050402130b0a0804020a060e090c090109030c0e0a180209131518050f06012102061b060a0f0b0a09050a0207020d050f010c0e150a09 67
    0x10b030038568016030701e400038280d440c131074040c20403c0307958a4819201140018000c4e4185038004003c0c0150304d07400946026030390884001242d00a941800000b003d81c0d06000c01c40c50444103842c000d00381b0b443c115040c6500c1d0000075401c0d5202070501d212184000a141034075900500040005580080038540e150f80d4944481e00c01c90400c44414022501e80740140300c422910110903a43c094001d070009201ea41e458a441c040381c0302d03945d001d9841d480c034490800c0c0c80f28100c0c0101003005107000c00f0000c071102246009481c1070094007012070039400c0000180888006403410011042c1c015114030750000c00b600100f0740600c034054411101c03145600034150181c00009a05000300c00a400802009001d44154001c940e034050040394001503100040090b80c402c0d40005c3e41200c4503040042c50b102196000039900d10241404844a4016070002100030000f80700c1d00401e0704039802c050034450b14050014001402d41c843d01010340b030b00132521404580c450100c0401400c6825a060502c038002925 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 668415323 1250 668414073 668414077
    0x3060c03090616141608031609080309061e040b070b01060f020106060807050f0903010609050f0a020406080103030f021c030509070909050c01081f030f06060e09210f0c03 75
    0x181030762442814040b40707000c4111540483c0345003059a440d401c0c0340b4204404800c540c0312400b5010040725804540c008281c019000394041d00240040400e0501e8814000c0c200c0005548001d080760414480d5500c242c80d09800c680d90010101110b4820315244200907420f4015030304241c44160b804074405003042004501d640c140c4419440d0800d5880725604100e082e164a401040300251520f0041480240500d007e000d03038075200c0c07451505003801003020030700b11403d582c0850382e02030b105e0060100c2401001d52068101c031101100350b02e041c0c140304003c0c04544040c07200a040042c00454602c030b1510a000c0c213404c0010303926211103c60b01c80d801c0100588400d4803020994002c0c10800a42b5100a02c0780545041e400b8010b0200085641c00541e417004005107082420310b83d0101c400840c0d004414000d025510440040c200014941461b0046070340e40d4000200283d4004144658040c00245a403040c008545072090070070450441541c283c060b0050f41a8440f0010a90902d05940400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 668416573 1250 668415323 668415331
    0x30a060c180e06011d120307061a1203030f0408120f04110109060e09090f120d0501170604060e0f01110c1204180c0903021507170301060f051803060c03 67
    0x40c803100d0140d201c0540324010b44080c0c41d014042000910310780ba50680c142c00071790409074001c0c5108904000034a4190465001c1da07000c13550301340da40040120207404001300c620721150071343d24064110400001203540f440003800d017005400700140001c080001040c05ca583e07554a8036039050084c2414140e2090304501a1012200c0d081e80c1008a100d035445050060121900d59a41d848800403000038000703100c1c3c000d041c1c142c01d40074040050000086c200b00d180c0b485d1100da0401540c811a9080307010844070103800c5034000402d2980904265070000071015001a08030400046001034100300701c4c80c04146841140c41e81d400c01402c1916007000070003404010302c004054071400707a00243d030940c0038807550007580150b0644011500400340c03154800c0c3c0ba9080c0303030300b4400a25912900000c036154544442245200070000b400000c000c079507484600c0d04411180316a0541d4100000074020000d42e404500400c4400700d0181c58111492114150441c405015100f0303d0401e205400b040340d100b11 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 668417823 1250 668416573 668416607
    0xe01060602010e1005060d021203040801150b0a0f091a180a0303171806010b07020f040912030b0d0b09011d1207061d120c07050105030112060902030a060c 68
    0x40080e0207070041c000d1990a80440003e8a04001440482e40c000c0402415060304031030080b6143c00140c6031307007442c491440000300055486c2c51404005509440c40e080075030252040c05072042190155100994000403e18100411060b1541204494921596110120451181000e10800304418004020a011000c2d900c0c62042e0700a05001801981d480f000b4005070300c0044036a0080b00d00c400c0183c2003c5150309140e010100c0d0030310703c1d10b441c0081e00019000000042c40c001186041d21802e00900307002d503010700111183e902c0342484150142041420315454900800d41d603070b54944260b40040d07210800c0d070700c2070400e019524000c03c0b00c2410400d014400c44a03c541c081400104075541d2200c0e000440d10b410681d680390780161241000080000c3c1d411001c00b442c210342484041070300d00c01d20300c00700e488600e203074151803070720155078821414450208010b001200c075000d201a00e0540041010a1020007480420b00c0c00c0800350000d45150702e48225660969400700c91039161410311 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 668419073 1250 668417823 668417831
    0x1413020a0306180c090b2701050907350702010e0d0302030a09060908030601090503150c0f070f0b06101803060e0a0803010902090a05063603030a17070309020a0308030406060b0705010e01 82
    0x25504c00d201f00d0007966078825041c01c030000410207490045011036101c00d86240001920400700346442c0800129001048170181103000368070705081c0e4045465000c407940c4003e000100384440c1c0705494903261a948000c05400100080c015800b541141e5400f9a001d00c0811104466003004e2040d5041691103a002420080300028540780000e070040701424110090005900c0309001e0074016402100001030181050003140c3c04203544044040030b0170700500035040d41c1c2c0381490130041307626091180c46003030200440200d400d1807025416401035030f070300160008025881e04240b034900300151400400c00d040c000b00105032007065402408509805a07881c0d024543c98208000d075600502c02c19005000d040c00020301d0b00d0f64030394035011541ba1007a950b100c0308080781002c01e082d41d1042c501c100c0440c0780d0f0300719031161200014078aa4004041e203820843d00308140d000170b058060b44d00c8042e0122a0100114003800003680c030440081070031031a059036032941450a90302800203c1e0808007194a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 668420323 1250 668419073 668419099
    0x1a010c031e021f0902100309061103090d0f0906091406040b0a020f011416030b0d02100c03023a140307090914070801051011010e011413020a0306180c090b 68
    0x205005160810707500510000032019001c004400032300002c03c081d43c003152200555035030040413400660045140402511164100d12030142009800040c280200f20380032008001d00303079001d400d00ac150380454000209080c100c00020381240074036000066281000100c14103110b40025446c0d4011141c030009102940710350740e0910303e01104403010180c0c0fa800943d0892007501c40e038000c50f0310800c01041210403107025008036894020424401d00441d619414a0040c1901000401d1600c81100541701e01e01c03020500d250040b0000444900408a00d800401b03007450058207000d07034200340c0015054517440c084070010640e941c6031051242c02c80c984420301007116900414284580420b072a0300b070040c3d28003014404401081d0303030100f00f08500d844048401001c28020342c601c8400102c0003142c00b40c10340144481b01d8401400400c4e01c82c440d80c1044006842d4248030108990300504e0000c1e49102075901b0340085c0340c5546004050038420710002c241c480312680704012010054442e4900940 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 668421573 1250 668420323 668420383
    0x609010501150801060e060304061b02030307110307080f130801050702030409060605090a0b0a090302030105100828020103050a2d061202030a0210090302090c19031a010c031e02 78
    0x542805190001080e541480d07506c5c0c10403d00540d04540f10b601e001074009034001003607400e80b10300f00c0d01d400143c00c00010320200591203a0b0100b080054800910310b0150a42e503440140c2c8284078201c500c8040c0851100c010142d4400c0840081824400034005403a05140c020b40b00d034414050042c0b0321385444804102d06206100f0b8450108010f4a1111100c1c03e00b102c40c102030700001d190170100300202c0404801600c003030007014061452400386081550a10001c542081c0010301529402c0344503e0301582c4d2800c3c0c950440c0901602820001442d4940a520700040e000340c9603181420250080c0102001d04c52203000c2e040c0c00740c245000c2000a44882015900b01550440a940341d07004d1084580540390a170a1410000718074101480055640d03800f26441500407101c009107000e000c41c14161112400710100c1505a40c3d01d010003003100740b07203141d5806110000001d0b0420403002a01000c150013040245a144100c2076400205003606d03200035520f421640030308624008450076034124107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 668422823 1250 668421573 668421587
    0x411090108070819120c060f0608010b040b060a0c0308090c0a0b0a020c030712140102090a0b120604060b071e1b05210d05030a1104090f1a03071511060901050115 71
    0x594054800300c501180890f0403194200300c502d081e07c609a4580e4014040b140c42d104000003030808800100300c2852410400c0221105131590074042c4008014401d0107070351101d0b100e801580d041c02c4c041c89c95122100a18a00b208290b0099048046440e01007010051080507007804013580d822900301681210030700d9203d000500c078001c0141215030b17442000584038440d2581c02c600c440001810320071800300160242805a0005854140004043d080d91514410071075100350151000e1024038a450004042ea100b0002c02800400121341c004000d2401005a6841c2a030041d40103001c1d448110303c80c444861152244e40d03c43d092a41c0c0105880c90401c07034000300f4054020181000341c212505c16aa0755100900008030f2543d111031a090911015014001511620358001060100600c511084030341a80d20310b442e01c00b40c4140c1d0140756500050000c25100c100d03440000e0004284001c1e9160703c80d510303039103000b030041c4000c2003600001544054102c1d6003e0248460000441700196906 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 668424073 1250 668422823 668422873
    0x150b0f0d3e090d0305190f020d020304051005090111010f0b04060504060e040f02030703050709140c181e210706051c09150f050906011e05040504110901080708 70
    0x880002e0000142c9440d100540c50403043c0030b400c049181c44032503021804110604104007012800e0a4042c0c0c1c4059410440e0039100300c101d0000f0351a190400c400a4401c00301036103c0c9080050016000390264425003200400742c000d800244910303946c40c4916000703091602641401103140c0b140010302490580560011220f003e45110040d80701c03911191802000e494069805208606c00000090402c102800040c500480d00007078600b080d480d0b4017150140034000040d915024841a401d4403513449200c500000101ca040000403c48040d428254903102842139106c1d0103114030800040e12400c194050025074019034218a85030301f025102e902460f60088500360303040b0501c100d604403d50041081d68000c0380100300e016190b40f001410f440c1e82165004c140d54480e0244081c02e68100851400350440314181e910b000c0350300c45166100507051040e1449503032510085001c1c000b440c5201c40d4003030405418014250303107850780c1950300e0005102e00c0d1480e1054241d03421080a8030b1282a01d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 668425323 1250 668424073 668424191
    0x911060724060b07050f1009032007082b080705070b06040605090405010218012613020402070308010311011d060c010b03010e15010504150b0f0d 64
    0x350040300400081c201500c0078240300d800c0c0c2d44150202e84503041401400b002c0384100020013801070041c0585050012800c0400c0c511420301801100080d000300d0302441e6024000c4a04402050700d0040e1864069598081c10f010701a080500c94000019184030880c2c80015101c041102e80c0800c04540c0040215540c400040050240c800010200345800d50041e60040c40401c1d016214030001c0c10030101a0390444290b0360010f141105808080110700444200b424181040c1d540500c4101e903024010600412004864000520303080039804000c030f4054000d00b0464885000340b8014044003004e0006035030520075050f000c80598070071201c80440d022009451a1010280390902c091034100c0401001103541760400c0f2011074400b44210702c180c2000030002c1c4546840741840348680c0302c040c3c100c28002c03410074840411140043d40d5140031921410011a9510000400d8510038003807100c00300062030a20908514075504503c8598040945a0815208503814181144219180e61a401e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 668426573 1250 668425323 668425343
    0xe01021513201c020f030a030509120f100e07080307030504060828020a1202030f0103020d0c1203180602010b0f0609061b01090b0708090a12030f020d09110607 70
    0x1a400c01d5140c0e1500d5198001140e04030784210010b11056404010f401c03c080300e40c0001c40c250324085100090081c8280c015210840c86030310f00511501c241d005450083d00d2003880b44014102c1003040b462070342544170640d0400e44110400c5009804e03905450b52a84c456140080748441d07003c0119454158581c4840e03241c180b0703100080c0c400c1030f0021306000200c001c0300d00c0d400010407004040402640c40d0003006a551560640180043c070040e6981c1095500c10b10070400d056542c2c82c0c59034152a0100d0382880c4400e070074a041803040100d9004000b040d04106401d108140c4c021060101c2140d124642d50702c0c5030b486020803422900c01d1a003150748680707100c0c140ca1031420325000070421801c01622140c40d10041d60700803041c06408041000890b9510400c0c20b00340f1889410403900f0106918101c00241030002e94169a00c02d003450207444d400410711100b50a50190b8003a628260390280295100e1082c1c40d22807000740001401612410a50711101040d0316203102160209544507100030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 668427823 1250 668426573 668426611
    0x25060b01030606110a0f0c26011802180402150c0307020103050114090703110d060303110607180605090121090201022518020403050102032a0a0509100306150e010215 73
    0x242004d640c170400e884521418501141d103070303141c8000e4404c01d40c81e08121841e88e40a00704481c00c40d038001c46140c00b103024500e08500141c0d190449c207003010040c03841c000302c6030312180001200000040c004801d0b12900040320001e00f04040003034414076000341c0f802c214a030390303c500700c054440c0221101a400120b000018441e18005e81c00710318100c0f45810039505044410040a0441c1e40903082900802c411004141c80700100b04025540010b081c6003090401d0a00c0016035100740f007a006650901c040031440c2200d40c2d200d0b81200003a640000c3c0111a004602d0f000320b801000034031801d0f80180641075800c040030b040c190442044486662050500c41e2402c0300d80203030008114140020b5070b800f000004040b420900195004402c400300c50f42c0c1d0402c1e10360007503030500b05002c405010064180102c8a1164101007a90304100054466000c107030401c41007140244101d40212030702c0c03d0600c84030300c50315900c07944032050540282c003240d52098080116190700078040385c04210761420f0709408 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 668429073 1250 668427823 668427833
    0x13120519020f1e060a02010f15060912030e27090a08030610090b030103050c010f0e010e0d030e03010905010605152a120a0f0f050c1225060b01030606110a 68
    0x4950419503541c00b840000780240054115440548078100503915823012500110840c030454181035010242d000c643c0303103030000262074240309100c1c001480b44c0c807002c280241070041e504008a007100030240b0304220640d19443e84ca500560b807161040c086503000160b900d01d40010350301403280d00840f80d1800c40d40c4010030400320124100811081000c003840000b003c003500c0303014601852140d0007500d1041e05600c0010072510104c4500700401c14a1004025166005110303401d0510b019545040c0859030342c1810b44041103113456064043d1f1a0402c8841800810741c031840954000b1208000f840b0407602420320140203202084490340b2038541d2281d10300141c20b4001c0040003020301039503a070444c0c43c014a50076801a209101c08921024115903c0e035034042a03c10103032a581c1001c2d810704603008613469070384211040c0e4011a58000030801c0c4070809500a0720179200101084001c0100700c3e203040d0b40581200703500240440c0c01c120300032440c140140101d80444807800700400c0d5000a94a413 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 668430323 1250 668429073 668429089
    0x170c010e091812070209130b0114011103070609291602010912020d080705040e07180513020909090a08070f020a050904030503060a08070b1e13120519020f 68
    0x60801800d402d100a032110800a000304010a00082001500c880850051180d0a80d00901c1c101650608414250000e071030030384404d0641d0b990980d004845a42400140d8038103074640144c0450b44400300b910010400e00c0c0c0c1080200038450007003170203200050300314074582e08445281c0c5a0f0b02207040001a1028411113440005405244004102d9464a4a4684450510201540050308050402130426030401c0c5da56410440510b0810f18040c6043c0c581038102001400800801c0408800110408900d180345000307001e009141d12942200058060020f43c001442103004a4084000900b101d5011602440c030a0300050400d1a00c2540c1e40c90350340704030300d0078400c0380d11000403100420ba507215014010b100360321035190300c0d80d01d0410504000c4c40710780e20f5210314000e0b032005409101c00e000c01c070203440d4013008041d00d40c02504030303103030312030f80d1078010a24603910362845c3c01d8000406517401700c5044c604d28017034015a00e89030640c0c16403440801d80c544029410080081d4123200500341170340c0b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 668431573 1250 668430323 668430331
    0x20309010203071e1a0f0606090a050f0a08030c01020a030e0a030e1003060b070606030318140d05100213061103120106080a0207020306040605161e0f0203160309170c010e09 76
    0x8090b01290b9080e641700c0c8060201d041c0d040c1c031035485020410044026451885400c224221070003030a2640f61000a9481000d501425000b50340038801d54295413100441c0c80b01401011060307a854100d0420000e0003900210804000a802e00c61480510b0402046200059825950f501c14002d031034000e0064a00320108040109a5202c00000310603800d18003905115105a00c0410298518100200044002e40c40c00b09040e00118041190050204004003140c80c240c0300c501e004032140c20f01a007030036640003059090600001d485060340c40008820800c0d503600da2900a0910320f03a0301942d0307690041ca2922a8511260300041c0180ba00800c1020340c44464108058502001030b800309040c030106071411119192185c041c0880501206040c03030b00da000519100c281c000502d07603680c0c220484029444c044c41101e12010401500c20f000710340040c405ca00400794480514980140307000c00c0341c801c54103c811400703442c0d564400049141c0d07801400c16560f00d0b440c01c1d0309408020183c60054 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 668432823 1250 668431573 668431613
    0x5160c020a06080603120703020d1706030606010f030e01020c01051f0b030c090a0312080604060b07050303060d06090c1206060603022d090a0303030509010b040902090c0d09230d02030901020307 85
    0x1102c86c0c014050303120b0090207094400c2d40503103c0b0300881c1c10060a800071490700e51417001e110b0030400125132030018103a64820f4007442c08501001440c075080d0018000c070081e04040394000074a00f0184501500010300a01b0807038040c004002c01414603005843d800c0c020400c4861301000840d2754424500e002c0d0042600091504081695035500e0181c81d080140b101c50201d84807108000d62450203115070402465004042403408200d0b643d01c41c0c41e1701c4000c05c0035210b61018644132051042c20703400a20b54507405102d2294a54403480c0c2d068003407001c18400c550150401318086401031003402580c006c0c0441100d0f0b0304002604009011501d02d60b003c44510000d804d000c81c500c00e940b12202c400046001c5d850016560804914003800d599000c050a4012824107540e04016200d040c1c90035071081b01481c205840d400100c49500113404404c901416600c41222550460105840301c4524580142c0c201c4112103600207003030ba1207010f0150b845026810601080d0082643da210480324110341c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 668434073 1250 668432823 668432833
    0x6060322080f0301031a0c0913020d14101403030702100c030c120e0a050301050c1209011506031a10080601051b0607110d0e0a0512190605160c020a06080603 69
    0x10400080b09504243c2c42510b9100e8101c10707a560301400da01c0302e160460441c44050b0f00d400e42010210b07440b80e0454210002069000510406a0001d9071181e100100d0300c280351170160a12000e107128002c517a01900c0b4440c0b15005565a49150000072078007031035070141103e5000c41c069401520790f00c410300404d9080c4001054014000f0385c0180400f548001c04e038840640d0444c85030140f010000d03403a081503020780c1c5030100703004114604c4c005039140954000d250701050b50b07994050300e000d4404007110780ca00c0c5510b12004a02141c042e00214003801040e04405004c1d234603402004004084004003001040c1c11101040655100b030000b0045411182684507075060001c1010f803803c1d01c2210600009409422400349030a02480300e204400261b2915000ca2030b410700010301140000e20a1511404400966000e5000280140245006400d600c920380001c04c0c10604040c110171150b002c04062000b41c50603816008400310b034040c40d006081d1920840c1000f60070350ba41e10010f0840340d80b500c14 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 668435323 1250 668434073 668434087
    0x61d1f030209190611030c1002250f020112020909360604032601060c020109030b0a0b0307120b040206030907170102130b0c19060618060e0606032208 66
    0x40d030f800c6030803040e00c1054140c0300078a0090b004202d50504010b095850704100040304041d4000200309800d0005440010b0f80c0e8650488020041542810305000000c8844210f009005980840c480000d000ba25100000000d07400c2c004124401c014001d41c2c09041c10000c20b00501001d42900c5400f4000f01c03543d800b6880c0484082c0c009024080d070028540d2082080004056011417185c11030840004114080c845062900d034040740d0500490303081109002406065a20520b03000c40295040001d540795800c1201d84034010704524220079000e882074600008103070303100903c1d03c0c00c0c66822008107401c0d034403154200451640701800c00302c5548684400400c00c00142480d110442c8460030005a0b6014980c103000b4142895070300c148691081800915148480031544021303440320300b03005810020580c03030510f0040015401c4148405502c42c00380640c4c00701d03540030038159886100c24692a039102003c201d680d2004441542c447c000e00180011441c144280840d8464030400f821820001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 668436573 1250 668435323 668435329
    0x6200d0309060b0406080604142d011112071d0a121703010602060f10050a0e18100605010201052202060304050c0607030302090120210403020a080106061d1f030209 72
    0x742e01d4200e4206c0307800c49010301c4100001d0085540c010702c7c8000241542d00c01307130316108146d16050307860100d581c20f425031241c12500003980401c00e07822a2086007510303101301000b088c401d84402c460100c0807030b070151104071444031100d20151255400030014005941054a5084220311080c000c0b103541c116020070590481c1484082d502a0095500602c21490b000c441d070414054040d000074a05007000d4401c0c081902c0c0d0141001c262051543c0041c560f849050381a60341c9090b0301e042200e18003841101da1800e003060381180c001c48030264000e10807900c41800c0c103000116002e100e030904080c01c600500041c14014051580907018200f48ca002041e580003082032036210800c01c6000030341c00100000b282d82c03c00046004081110704040e4a01c1c0e904440300c2c0d0b01d0005110304d1481220100120803110040300c2198055a070241281001941d86c140c1c2c68060032107030046001041748158004640402a50f4084110800610345003101c0401281d80e05c40382c101968013810990200141402e80d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 668437823 1250 668436573 668436581
    0x1d0f18030705100b0108010902030609060603060609102c10032003070509040e0d021f09050f03030a110f0703051602041503020f0d05060604231006200d0309060b04 72
    0x8034080c1c40400c0b6802c4d21000149400d01c1604910200c03481401445481d0700c0d5404066032000095852696079203960001410034025128140d9114818070b20046d9156800036a92820401300d42010740050301249c3c0d0ae41101c05001503c07034100300d9150b0180001c601c41c1e040b14103040e48e0740c12066107030b000c20303802140c055004492140210b4070000e80f99015003424842c02180c1084038000d0103c2010385080203464413500c80c056240400946882e1440c29120390007442c0c01507000d03048445043c04464015100d400c02c80d040c05640749051501030652603100101e81c43c00c440410300c5841c102c031030b640584854001e0490703030318401d140c403140e0001a00c8502c43d8805001281d50012050b924510411a901c0700301041d06000d005024403103c0060b5002825580014041ba0007080450f140e058000e070700b011750184059162240320501a039040300803410020344295607140c010f840510724200e070b69007020a0524510340e0001d21300703208807442036010400d100d101c0da0703022032011a4140000c05075 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 668439073 1250 668437823 668437843
    0xf030c220e03030f01061403041a04080405041a0907020a02060316030f2f0a050f0906090301111803030a0503011413020a0302040801050a0e0307030f0e13061d0f18030705 75
    0x404031345005000050304030a1070720ba86440550342d6899860603690b900603c207040c9c040c000c01d10b03410703001040070044c400e015100a0300c00030f4820400c0c900458103511f070489141e00c400340070b65201c00210b6111440407404038192500075104078611b45400580381090b44000501200b00340d41e40d40300010040c1c0c03600525030441030b00c00d81c0d01c6480d40b000b800c81101100d05610740321400e00030070104a65a4015003a190380708034203c041a107440c0c00c3c00101e2603c2c42000040d5074554a000800d401080440b0043c0c500b01d0141c281e8180c0017583d0006055170f900c604130541000c91420300040010305c403980d01c0500098030161a050244642144010580c0c00c1600c0010100c0d80101d0148107a51007441019404a48190148002c14000071580e40324820018084d0800010034603004072907028450803d0b1100303000e0080302c9003000b1505008000c003902d0041c0340d99110000c258541041020046602901181c480c400854444c8949030345142c4010115191a010510425000c182c0500c104056 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 668440323 1250 668439073 668439091
    0xa0b0a021507020c0439081801090606121509050c060a02010e0a0501060815060f10090b030411040501090c200703020a080d08010b07030c080a03110c0c0f030c220e0303 74
    0x10100700c010703419441d0061994035408140c0301d407129012456000c40c801e80c000301c4800845070305800d008c0005001d80900c1c3c002501c164145040003510403854a1090081d9015903541d8821687d01800c09007510780003074000e021036024140301480341c50002d000749006071050000289603100015841d0411501041c15500e070f035944d642c10401090140421701c01c4050300321348180c1301d10f480c0e80000c01c80e0001803030b0b85001e449609069208540624803080251401d0040d00f6160700c1d09140504500414100c402e010394180000083c8101203030054501180c8142c460a1010002c01d03080b00e6204010340209480c3d21404400001503101d407940540501034080140c009444404000740007804180d215008141c020442980841c0e881684685c40a601c0000b5a41d90314000d8030440252550300000c0c8410200000c4201030904001403400c4a164240c5020400900c60707c10942c8640080da6038030342100d440301ea0090021119481c4040c42d04241d42c00180d443c0841d0803103851030304201c03080c1403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 668441573 1250 668440323 668440361
    0x3050307061a2e14121f0f0515180f010e040207060203090f0c011d0a0f0801090308100f050603090a0c0609060215070504060c03120f0b0a0b0a021507020c04 69
    0x88000520319401c031100380c07a070078004882c0f40c81300c101c105944550403058400c111040c0101e400b00f695034100354401606800c140a0598941d2200c403168262441070500c103a5031240b10746044000542074070008003001400d1030030840403000b071054115945601ca81080300b1501c03100e80a540711300c0601441801030310010b8880c40d0452034645448001c50074140580c1c40400710056680e803020401d80421402d074500740c1448013482c04070310303040116040b8100c82c4514013404522003005601440c1c52500035501c49441e6112080e010000c02214040e259400c0c20315882440341f814514000d40d00500702c2021210346501c03e843c1c1460a003084e810050008104070342c1005400e5041018a182c41a04010b0042070305008074064039901c124031403501440503450014061500840c01c140200b02d24080a0000b880450002401040054101403240601ca1004a807800c5400242e590f070700346a800901c001c0b0011041c90700034000040040c030031842800b42903026911a80a4061300b0440111444 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 668442823 1250 668441573 668441629
    0x61f140f0d0608030702090c0703031503030503093711040e030c07060e1813060e012004140139060506030c010e10141b0c03060103050307061a 63
    0x1d0159030496100c1102c1e030b0301c02d02011000d41c4e10a11441d800c83c1c60070007002d07540c0f1900e03d400d078083d0184c0030500310740c100241400810705030004000c52050404100b65084010502c0552803916801d03050400e07410148840000c99074442c0e4401d07148180140c103107011101e4080c0001e0280e0301804101000d80c1c10100d041c186e017850401c52a405800507081551441075408003085000320058a00c494191240000c5490041020050560315810000a001c51989503020901a042034003042880420f07c1100f510300c1d0b250303007081e2010f5402000ca403a0101c0301510046414031328441c0c501c5800c020201c0c00d05485450b5100e1084d159120994000390303c6013a09020301215402000311f400398100c038403c200d150782d020900a100300412281c59480445456084035a000d03003412041e503007000011104001240000d01446001008044510013865039051644580007840020840d61040c09a180017521a41003501801c0940d548080d41038481c000042c038a0311301816020002101310210 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 668444073 1250 668442823 668442847
    0x9110306070f05162a0e060102030405150903031306031a01031107140f010204030c0e090703080d0e0c0d0809041409100b0f031e01050906061f140f 65
    0x12641c4069503041c41201940c0e1050003a089218103d62042c9140401c20801e0400c498005604105190080100d1000c0941a03980c8080748480c040d601d851400d490009034190720000894068a60280c002203620320055545400b5800c070940703007503040c0801e00c2210701d05100102080020407444d9000f10b0f0781c01880004c080d8018080380300714101400c083c0d8240c810720035a0308135000c0ad0743c0001131440f07000c5c250314030301d0604480580c02e02c095400005c0c0041809149000301042e5140007007112540e0300c4480b881550744940344401012071505000100c0b11200580c80350001c142440155803008102c0000182d81e00c589240032200f540300405d09400500307145c0f0650b00c0100c085880b03c01c15041c00c0c2e090680e1080029404821240c42c0e01d080d041603250307500544242d80010b42296494a42c040034040036681707403001c5044d290301e40800075000300400203210380180c5014104d140002400d9800c0705440d4a4540c0d503c060054942402c4410087c0700001c240f00000301040c00d445036162194 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 668445323 1250 668444073 668444083
    0x1e0b0702100b300a0212150105030f0a0308150d0b2215020711030a0303020c0d0503060f0d0302011401090f0c090e0a0b150304050d030f050f0601140d091103 69
    0xa28000c40d020f0910f450103514940c0d07901a0b149094142c4103003001801901864000300c5440290401081440010503000c005500410030700261034641d200d80c1c1300c100380341c1e503a80c480c01d420b00d00c0c1c0c2c0203501c4200400d009003403c5400451a40b424561101c1030781c0407a85601201c01e045842041c1442000808410104030208030b407010050b40c58101c116441e03951568042030b9443c094168001141800c20840003200c0c2d05e09500581950320a0701c55050240080d0401a000500c0740030780c40140400300c0c403460440b481654024a941d28408851007406490700444e2000c030203540d0383d250b04040c44100025818000d055402003c59800b0502c145003054036001540d00003800700b21142809480810343c0381540c40b4260740000201a1904800030f00742d2860b0060110b12406c001061105100c8003003060b00554145840030301c806881e54119504070b5400715000c040400454000c01c3d030300c2d8421110601c0e03400005410130706000c00302d44810100c441d00c1d1001c4900d480008810b440c98101802 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 668446573 1250 668445323 668445341
    0x9030306090f0f010b030601022a0a0608190f090204021603140403080306040504031e0c1a0702030703080411031204090609021201060f021609050a0608010b0d1e0b070210 75
    0x507194006003010f05034074820032810300401d000b000300880004c03100d920130004520b031100034900c035440300342c45c1c5c0103003013044400c0c41344088c029402900d001c50010300035002c81b40a0700444100500d070f050b0035240c101c01015290700c0c001000d6140e803c1d12015903510300142000101c0b2a006c403ca8010300e00c0c01a200095000000520050600003007010460a4040c0da504c00001e4030b0200e0a43d45500d0111194245030800340c0000c698409018600ba6024900c181058460482c04003440403005107020201021103d03440142c0c020040040064815410960414842c018101031035402d5000242482c3d42452810715504000c2070802941e1071500406004010b0031000b1440c002400c204410001014000c55050005442120480c18800c0240b460801100c000720740500741c0b114141400382006881180303800d42424804111541d061080e50030702c0e4001010700c4840ca106549250b6a0f0102c6c050034400909070290b020b02141403584520300c03411950f406007a441c1200903850f0b00303c0303101e91 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 668447823 1250 668446573 668446591
    0x5060f0a0c0c020f0604050409030f020d0c0c23030f010b01030f0509070303050c070f12021f020d0e0a120501090302060108010504050712110a0305010605100c15021b060903030609 79
    0x311074480e0941107240080465010343c3c058940c02c2e9608041100c030301c01c503808281c005141c80d0045060551003200c0c02403d1030950701740c441c003401a0104641481d850175000d008215030104c2080300d10f4060612802100d02c45101148070200000001d007000381c8200c0728030b000c2c1d4447da8010038640c1e052180040349400200c082284d4100100707041d66955450100a083c8080001c002d8413042080118400408450440c00000b9846420a80b0550f5046808074040c4458141c0030340d0884020948550348411a0300030910600141d104075009108401c0076074000740180700204040c008c03580c03064800c0f03020b10004980c502a84c80c00910b0034505901c07210a0781d01d040203100000d840824a24200d55070075281003148040c504000900c0891809040d60040c006400001044411341010044400c21200e07600b1010340c00b101038a03203181c510740007880c55591071032a94140d99507601030501c03862070300c0c40341703861240e29411186001e43c1a120000542d001208011052070034840040c0e002840d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 668449073 1250 668447823 668447831
    0xb2a07090c081e0c0c010c091809170f041a13080d0210020304020604120308010303031a03060c0a110a030c0501050a0207030f032004061e020c010212180a0305060f0a 73
    0x46880c07580c02c500821008000001401c011496113851031099800440c00a002080400319030500030b00107a07018802c0356941a00c007501c0000c030b26124441d14410302d0b0898076007140c41140319100d08040c0d10800300c9840003c401d0002107281c50510441c62500807412201c107a8030308598600001c041d20703560114499034080200480c4266010070540401d0b0803000d40035071070b0348840c070000780c2e24001c0e5042000004a16150302091540c00918241200e0003510100500546200e403003003d904282440c1d5010341c08180440d400b0440b1400a19280c2940d141010600c2e82c0c06400900b8080f01000a0300018113410500060140030700ca01e582080c200402140b90040700d4bd405041c0c2e40b4040d00c0d400500d6510004009030315a0600e008031851800111140c2d81d40e22034401030220252000d2481c50481141405e0844a00000d000890385070141c000741103d8446c640c00c03401c1d59010038554a6041e41020800c00580c6072101140e0103581b1400180146180c400c60189040390001d00580d0a01e0030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 668450323 1250 668449073 668449081
    0x121008030a05130308030a0f0e030903070e040f05071217160f0c080601090e0f06060319050102040b03150906030a020f0f0409021302072108010b2a07090c08 69
    0x800000c8856800740c0c0d0401e9a100c480da0030804107030802c1d507813010b82a003038008100125051142d0060b4009407144504000200a6510440c2d403030041104241c0c1581c4a940180580501e5580aa43c42403081180b2044442d89540c0d943c2030800a90101080f608a445040b00304098000e01c584441403582c1d000341044c0c0502e0b01405079210000300038101a2203c4c541500b40600404c0620192000d0b1040715080c5d42d661030114000e100848180300c1c24010740780003006159002c2a00e900403140100141403e5605c281a4003048042c094101c81e03d650800c00060020740c6103003c0d43c82005d60301030f441c0b6640c901506000395a4402480c3c58801c5c4c20403111800148c0d034000300102e990030301740c5040300020703014404076008110101c406507100500b404003070180c403002c3e00200700c024030a03c400051803075810045110035010504240100301c1c62401444800c1881010303201e080d580010340c26118038815615424030b100301c4101403164001103001d20a07005e042c09075090b03102141c0381055040c90 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 668451573 1250 668450323 668450339
    0x80106080412030e0307050d0504140603132a0303020601060917120a0c0c030c05040e0604080702010c0c0509100603050106210e03070c0b030402100e060702040c20031210 75
    0x18030300c19642d0515070703580385071160140e040054507145030b030003c1181c3c1c0c440c0c1c0819028000d90802c0c1716000151092450180c4141010f0082e0b03401410081e0100750400783c0c69481ca0103400d6924401244101e2505000340354001c030f1007034031000f140aa0003070090f95061480080c000c0c0d003550070554241d42c00030503080040100064165510b07004070102629100f0210b422209071146420291050421406c08010b018100740382004a4104550404c6950f414200464460508a5000c1c1400c1c00500c48000594081d1842d45183c07031040090030056074803140000e108003000e980e02110400c1100c410b1200300d405210303160242c82942004017801c0124800544581c81302c02c0e00760291030f202c030400940103608206542803280d001403101a450b44884e504004c40d002110160320a8038003580080409001e42c5802c1c030030020141c000b80c03078400c1940034003010b0304e65100b110341008110381000c040803030040c142001800d035480245030744180c2c200280882c4070b0b010f0700c80300f4200842c0c641049080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 668452823 1250 668451573 668451593
    0xb0f04061a100c02010311040f0906050a080607030e01060509090d1805030c040f11030c0a02120307090b0c0a120f0323011802072009180d03021c0603060b010801060804 74
    0x602c403450701032000109803004130080c002d41c104000d203548000c41d02084460741c08810f0010b6540b19a000c0152542d9102041510b000c01c3c880d810440c0c01080108440c00c4c0b02e030700941114941540003094040e52503002c0340c10319034200c1d4860000e401505001c09069401030640d4020581c400e2140281402c11780000c0e01c3c1d10780740403080d00c115070720440f00920f007109401420003032111480854032450100c5003942c9a5101d403010304018000c24155071071810402e01564044d1880340d4600c038246042089519203a8445200f058a0f4826880c400c40061180c800180e0203104d10350700e0301c1c1d58011003034004d410750700001801450b19503080180c2d42c4240800ea070060465102c0c500c140a18111100070000030f01c501c0f14080d080001310850800fa544201c044034420b041c0503100c2071500e9442d00da4641d4200700c3c3c8100304039550805060b407901e80c0c0c80b1740c001e01030b5410391108640c03032414a2080e603001c03500113038001c40d400c40e00d80d828154a50b801080b001e00400907030034010701a10341035480c40c041d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 668454073 1250 668452823 668452849
    0x10512330f071b1b1e0f0f12080910260f040f140f0123090c15040e0a060510080405030a1d030d1d0301061805070c0b0f04061a 56
    0x81c3c903154100c1c4060010082c0c0c4141040a00341e000c000854844e11803d22000004410303000c0303540d20540001d503051091034240211411f0304501090036081104158a00c4481d4005403021301090088031556511007030181c59814940e01c504004d004c0d010000064661402c00c09105800580104a10700003a150090b9020382e0003000c10307840d4405071821840b00500d2110402142c803c10a852804510550000c0c01080d10070308040c0f030b101c40515503a01100d40c1103640300b00076007240c074884000e81820982c02a5041e0f015245030308040e2502e401041e0580102d8120110548540e0104200d0130940c050400b41d8005240240081c901034845990364452010b00204011100061798401258002c05213810000201034035581c05280400401541c8000302600c44000d40c00b0303050500d03190510980b01124000b010760114121a110900d008110041a910a01182180b40070008a035031b0100f5125125078880c0c000d103400e0909169046814020140a9040d101d02640d82d0603500c1d08400c0d008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 668455323 1250 668454073 668454107
    0x1f0c11030c01021207051608010903090e040201020d080a0e03210a0c05040308090109230102161802090604090e0a0b1b1204050a06020d09150212010512330f07 70
    0x621659840c250f85000f40a0000d0740c100300400401044188c1d040d003140003002d0081d03580c00b00440d21082e20159041007958001c0c050780c070400c4c0021441d03000e54a515888424044001071300401455010300710781c4180b44420146401e650442200940f49900b40d41041849004200f04d400154014189108a00000d00250350204074002d040c1c7c4a56003003000707091009100404101c2c0e80e91071340d14200000500b03d0160107289408205d1007400200101100c10680c000307491141c03c034907500000e60104080c1600008104030100d1000c00900444c055612010010b103500e480c0b9003001c80001030043d0180642401c0310582940d0082e4401c142c500000d0a03030f80d549490f45980c0751444c50310202e080d008150038004102111007003c03c2d8041204107018903140c1c119a40d041c50500124400c40803600d107180413000040c48240ce048000804540641d001c480e072501d04800c0800140c20580034015000f4400c40e0140032082490b1809508004400418005800e2580019040084850341050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 668456573 1250 668455323 668455327
    0x6060607050c03010f0b0f01111002181005070c0e0103051b010314090f0c0f130903090306020d0614040e0d1b080d060e0708100b03061f0c11030c010212 67
    0x41409402d010050260100500800007040d0541d00c16028000d00003002c0c0c465040d041501129500640048c00340b84c0504020b06002c05080d1a200300a41200c1d05c000000c404080d18010f030380e02c40d003200010700c90f00e46c1c9510740c0f5104545080c41c480c42c4035401500300c0b841c1d84001000091000038018800c0d800385070000100100d0700004070000c0c04d0044150007001071f00070511400c800041010a40c2c150303c4002d482180c60341c60140542c0f01d507640020362300460702105184207410319034000440d9910a10340403541c117640713480b507405070f82060751f844035626540c47c1d08020310f0321003400034280d0f100191028030030042590714854541c0d0481129605101c40e0030307030034150300f925002c25a0301c0300c2d07024000f141c94034054480300c00189130902601c0482d800071000b040740719000d0090310f03101e01594000182a2402c0018607150354001419103034000c1000382c0b15600301401500d081c980d2820a540e006034990f11418002c0212480d01107d5019400002604126907030106021004200c1240c0d129 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 668457823 1250 668456573 668456587
    0x318070b030a0f0e06180706030603020a05060a03020417060105031c050304060b0402040b0a02010f05010608010e042a140918072105010203040f030324051201060e07051209030c060606 81
    0x4000740001c0416400a4000c941c101b00c0700c5a8120b105541200030402180d141343c2c0c07103000660490b1030500000e03500c450300c014104614a807c1001304041100752401504041d551004d20480302405420552582c002d074005002600f000c00840180b02da91440c0103400d05202e000c090010701c006400508003540741c00501c01c00780c0300c40c1c04990041590104140c0e9811503604c009000f05454049031103124108400040ea9a12643c03580b8184e03134030032201c013440780c5490b5075182c000c0d0001001c6800703110001c000707030152900da1503c001c000c000010400c07108851000402c004010001c02d02c803908400507101d84005103002698105480c0c0f00d030209141b0b0703d060800540032203d0f10b20020718035030002041000b00b200700c1740889c04280c4203031414003100400041c0c0e15084e0421000b01140400c2400d001c002c1d6280103000b5141250b0315200014140e9210700c03001040c440e0844190010034800a01c00144100008050f03a0042e03105003e1030030204015400f131389402d00a80030741d1103280045410703 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 668459073 1250 668457823 668457851
    0xa0804030903120c030206090a02010f080702011103010b0909091b0f01170a1401081209090703090c03080918130b0606040e090a1403130303080a020d110318070b030a 73
    0x6000550740001510094011103c4020f01c8044003540c00c50060062001181001c0c0c00000d03c0c151142d416118109003058100040703941d420700800020031592221084140344c420340c4015806041568101c44c0d4400301e00301032020400f0064050700c0180d01c448800007804524180300b03805018203e034001c0041c994540100ca140b40300411000e02e29070380c0000c0c03001d55182c1e40d022801e110340c0b0b2020304441d6a81c480c1d51070b40f03951034520a41d400740c408024940c041d182041d80c880c0d004c0e14604002440c030b0555151155400c800e80c20480300c0e410001051141403800200080c50f00b080f900f602d18251412181c0f0580503041d08500406a010110224074246d40d4002176034040d01140d03d03210101e00d08004569641c58044005454550340c4d05008041800d01004031000c807008111260203c42c03a6903412103d8442c020080e2504a03401c4c040d00c215800640100c3c05200d00d40c80c0190b1710b0b400c015001e12071642074021030344607d80c008401000003500c0081641c0d8401010100011005081580 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 668460323 1250 668459073 668459087
    0x30f1d0405100e09030901030c05041a0318030c07061d0d0f02060c2506082a0f0f070213051003030c0515010b070506010b250204020c030703080f0603010b060a080403 73
    0x1c02d040f103403094410880705603c00005000700100c2680e003403103000c0c2088400e540070321a80c012071401044903040b00c0f540003080d03c0210b03049601158605449030010107120300b103801842e46a081030700003400c1005200c1d8082c2d0b0002c0a00750b20305900d50700c40d00c3c0c0c4000442510070301000900512100c504a401c0d5542c0606030b8840c0c00d050b1082e00c5110784002914292580866420051103038510000b040d40c40c82400d280d44640300c0b0746a41c10325020840b008500500803180303800d601c1d2000308142c1c2c90318000d61016151001d11110350302d4031501c0701c1c410804890481a25184141e00c2d20042001003020759035074002300e94260900782e0051085003022810040c42c1e00000b03040e00610f000000b90841c00000400c4440d01820944400b40d0300d82d10320340c016100d00307039411680030a03114084001d9941d00d0300d044451440104010710b03240c40040080d0454002c0b880c10f0300032490071400c010446803840307001580100110000c220401c1801c001803003c2c0030300c01c0807134100b04040c00028100b43c041c02e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 668461573 1250 668460323 668460329
    0x50901090803010b0403030f030c0f0806131505130c0f1805090c0c0d03090c1806180b010210050105210c0916020d090305030d0c1403070201020403030f1d040510 71
    0x30042d900d607182c4091101a51007807108030001000d01107861486031091054010120b0b1350f84e10038a02c00c08a0f01300709c54140001e00700c4e87e4401d8100582609040061207030004180d00c4040100ca2280f030a400c0060741491400c480c0070041c208801412920341c0084242e426000b142440050b403110b80d8000540b214a6401650304201240203101140d080c0a010780300500047c800c50300c1803510000228140e991201000b041507804210a000003a411409540501e0007844001062556007150350407001110a0341603860355140c2c52441e4a5031b06109450502c2d02003041230029501d481f01107000343d031207104400c0d0010314a0300c4801001e0f50074041d01907080307401031586801d803c0804d41c0602648100c000b00b40135102d8072400f48803460003510010103d980000c06141413100c40c0380d2940150a580100404100c1901400140080f21002860150302c10b6400180c40d68210301d4098a211900c198001c103104161040b410700d5041d40c100c614007500295070101d91525402c2c06548803480b41c0e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 668462823 1250 668461573 668461583
    0x30708030c070f05150109021201090522060b0a0b030c041a04050301022a0a02010801092307050c1005251103040b030604050f01060c03111c08070f0207120605090109 73
    0x10f9007505003e0f0000720100c00302e031200032400c16641d1b50720000703080f417140c44d80a24500c0c6030040100020041503200d598480e09101c86c000b03040219002304a00c8080d00c440440300c0540d1104924598142803030418040c11341c030034000d882c609103140a500540214480d02014400001350680c07100e83d48825030b802058090001e43d01c6032100710b003403610ba6407250040c3c010b0241010100e01003101c0010800c014a4042c0c65440d41642002c0041e8040c0c940324041801d0700040d102038400405815600710311a000c3c070741e5041c0e110016444071030300b4030f003440b000d84640500b81001e0200c1000c049041c81800098601c0207004d600f101d80e4261150220702c0d030026000d0202003000100c5110b988019881030354115001c0041e6902c600c110004c0ba00e0a00a4a0015210681e144002030045120f1100d61894500311221541510085509131080c501210005941b000500030340c0754002c0c8040307044181c207001402c2c0190801302d95401c08001c0e500c0140250f600e500104000000079880280b2007a082 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 668464073 1250 668462823 668462843
    0x313150e03031503010209062a1609050709050f01050c0f0610050a0b0a020307030c0f0804420c0305040e1003030906080f0103170904050a0b0a0f08030708030c07 71
    0x90026a03459820480c1c01d00c20340380314103c074041c0e90325043c422109148001001d6a0034403900c11061403101c182c892280100070562110292114420070006640c946250b090210413820480210256207026000c04140001c0e0001885146da6049103401511801e20300280c80d01d1030910368500d0b003500c01502e4060350098809103c0240f00182031b07481900d60551f08030f00c0a6a54001105683c850b50a2100042c2c006028104c0000e1091995003451401554940d01945154551001c158000d5104070040c07040001226141030070641417140181c0e1918071041e240c0175400c000f160300515040b41500b0091014000801c1500031700640d00a0071105044060780c0c90566a50a54010140405c1e0045070304181c00160091007000580d11803170891304600340e540d1841d91401c0060503415a40002c0802c24082825143c03900d1241c0340c03044119800c04220700000300244013581d1310b41c0d00040c02c182c5040d401880441d00000031110807941c023401143c0d0340daa480d0140d1440c0c0c010018018001200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 668465323 1250 668464073 668464091
    0x15190207031e031d0609030405061606020d0603020406140a030b1807260f120904060b03101e05030c1c02060f0a3c0306090e010e06011703031315 64
    0x89a440070125400e04d04009891084070003000d5611a012201007095034000c0100303126a0034240e018000640c1c440c010440303038114a950301c50982e0011210158500e64900f81002175140c40d00405e802080c1d5001140300004003a40030a0400b945030101511a0103c90042a50000c5110f0000d8000070070b1402e840082c2e403628580d000c44601040740700c8510100910020440f0f0001c1500e01c20201000c000f0900003101c10843d48580e0054a904c41d481960f41c05c0004450461600443c4075000c1c64000302c0d03007142804403c03a1403006842c0420b2a6110412041c005600d0004207200340407011540f000a41d09540c001c04404405208002d4108101040403d0804042d40140041070019121898041540004615603512300c1d140c03401c0203a4030311400c80e407110354840c10010000e4949030125030141c07124520000c5c0c650f0001c0d04405a0364800400040d9201440154090507070f017401e002030102c8005110b0703500d010107170008015490b000100310800007100d18051032004184070034064110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 668466573 1250 668465323 668465327
    0x40311010c0c05010c050901082e29030c0909191805010b0316030f03170106020a0c0b040501090b0d09020d0f050f0724030204080f0d0215190207031e 66
    0x40004201c0c0c9130760800b1106518980540113588050380b06a582c0d10b415a200308002180018828411020408412061003030459440054004d80401d40c15551038038811105011464145814005540070500a0000d802100021207076007941c01c03220234040b5241d00c0401e9081003030b0503144d0210a03291180c0c1103550841141d8426050340904001c21a00380e0103814952203218000100700310812682c1c040c40011681041400f40c503000b03203403580303a28103c10405520700c402a0043c0700584d0103403144104100522070344501a1040c074841c070382803524020000e40140514060700498907000300301410031844a5010520080d00284044444001410003841c045034076801034072130f40504d01c50f046000100085c1a022120030762140c4c5514110701400c0e0f49080c6940010341c003015001c0000144e5014100858102010404060640000d0314100a072900d8503d070240c0203503096100070040303180c40c0003041121005214002503620611807a04982b02080d0444120742c0080364131103420710b95 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 668467823 1250 668466573 668466587
    0x30c0406080618010e060415021210150905030d050c16180f020c1b01200115151209030e0402030a06090e0307150b150708031b071208040311010c 64
    0x2040000301e140031121210601400e8501781c01c1d48064681c0301c4804503000440546c0358041e00d20f1100e0700181010b200030b482c2085d0040a40d85400c611441900901405070421705248103088035046c8110040c1ca000c020036100e0014010728801c0c80780200b01349650344000d04c25200d20020340c1120f041015181c2c1c00450300d805280000100b007524129414448111510880e03c0c1500110700810b41d1076411b03e11140341c2c100b807a0720301d810041e42d5510300c1100e0300c00510310b0002d11307420b80001c40c09980404e542d001034442c079407112a20011f210540d20606070030904004000d4080343c000320b850902c41c103050302d443d1440210719030400c0c400810482c100d0740c50780c04002524451103040c000d11020035001030b0340e030154410140c1a08001d540303076960059030303a00a04802202070044260784d00d4007182205c041d00102426903d09500004000d0000782c480c0c40d0140100b008001c40d030803c403142c3c980b407000384882c9215034188003985010506040c041e040b40841c40c1e10100007440b180c814004028180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 668469073 1250 668467823 668467831
    0x1e0c030c030f071506031a0603070f0602011e09021507060209060d090605060105040f05370f061407060f060305030d02070c050a0b0a0f14070b0106110d0203090609030c04060806 78
    0x1440c0c00150382c2e04c407800135025400840b60410204009284001288290a0310181c1816814414404e000600042400c1001c00400c01d64000041100e1800803038004440d40e0f000d200f1074607141500c0440181d840c1000d03d200a561042010b4560815244c444028407880224650044011510380b0b001075a81d080603083c20b201e8541440b89840300c03001940e89014034042d0345032a401c1d0440c2070041d4200340080381000c2001c14030340c0c00d5000d41c04501c14403041e115110200c00c1c1600d0802400804244000a8000e041c01c1c54001001d10b43c0744c41c1000280141640100069202e0400b00414120364100d00040d58002d002c0e2a5a01401701c041c60080d40004002c4030440201c540c0054a4035001410310200c0b04141d410702d00d0300e0003041c004c594040e410f50896040c0000a10711400d83c2204501030511580b0403052203003d5410000b0142680141c0c50010b1116170014000b82d014a501200740da05803c001c0e20f00d992907100840000341003c610124490b001803901d100000d101c03800040e180c1c06 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 668470323 1250 668469073 668469083
    0x10b18010519050901090b04021c09050f030901080f251211130504020304051f02031504052e05060d0501050a08070e0403051c0e0f010b03031e0c030c030f07 69
    0x1142c9150351055a5650a8401d250b0703c10710040042151010705d0300640c00e490700084c40140b401280d50388054010300a103401001580e0b030780a201040041c104141c40b90728406c0c0001354104038407000000d00303201d00200b040203440616404a5490000001d00c080142048405d05c0f80901c41800018400081d060f01010998100b5011001e4401c8131821034190301c83c02020701c00458103140c280400b0394000740044400307120305101091411084c200d04900e4440e0072101582d01e0070544a0710301001c8002611501c01c03882d0009001864610142c4007903206001c0c4990f0400c000c82040d010810384450b0300164000c000007802c1e42c0720f01e1580d48403a050302c03800c44041324030f581c031908440d40d034800314055601c4d1440c01001080100740590003900c898141c441490030300385010341404094804940c0740d00c0c0182d00103141c40d20044800e0068420f0100f0a85c0118280b0700418020b1414907185c4503400703800d100016082030101003d001315403945a01d0b5044a5642c445c072807101610394444036041d95 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 668471573 1250 668470323 668470339
    0x109030e040c03060b03270307030e01090518060d021c03020a02180702060f10091a03060a051308070203160815060114030610031d010c120603031e02010b180105 71
    0x2211500038442c141c180c0f403440b0045411030740c82800190138480d1fa564041d8201d0700014444100c40401c0000b040c400b8440d9844990341e19065001408400c02c9800403882403412010030880c3c20446001d5603888001141d411202240500128040100d00c202c403201103040b0401e04418580c0010300d1041091090380d24a860844012400400c9401912001c005800c200c2c00700325000c140c0c14420303802060078181103039020b59a0307512a007200e0040c0c09029404030b03101d4011140e481c061006507440700100c2020b104030300d4840c1ca071326401c00d4110b0000f040c415021030610b080d518104000d07d003070764921022008140e224040290340784d8051000710800103d03040001d4055118110a9425040004c001821511520100000e405a0818038010550756100c21038240000101e00c2c0c401420440000500e0158020010000300c8288135880d00203060038010070000364064454462282404203221507030101550403800342048c840e005a00030074600141d225400e01c02d010f98101c0340100e074111 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 668472823 1250 668471573 668471591
    0x10e030303240d120f1107030b010303110a051c021005010321020102090d0204054305120103031803050102030103111206100b0a02010905070f0906060801140609040e0109030e04 78
    0x40400d18000400804201404e101c85035003d0003444403440344209420711940d007602c601c20322031901900c0c0d07000740c40d4186200010020306422000250421050401030081d900460320b4080d5186507180c41e144004150343c815480c024400e100000b2502c00b551010700084d41e5a0a0002208209039450006075004c5440008503a00500c00c807140d1903006080481040d103103408102c000c0030020080c2d00c0d40b002980d103c1402e1064040c2c925031615142a50350307416280c1308204103540608100080610000704184080c1d20006500c00381100d40c0751401c862031070600c40c407545901c001e9500003000c80d03001000100c00c02c182c11b003403010b81240551b00d00300801000e4620b5959000f06445140d94954550b42c103100c0e08503c0c42c0100425101e600000c41e81c04242d43d02d080c0341000551112180002404050202c4880e5006e110010100391078129210350400005c00300703810310781c2c80280c4241c80000c3d42c10410344880c0c206981d180504002044402d04a06000c1c004000104021384924a006545 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 668474073 1250 668472823 668472829
    0x9040e030a1103130905040f06020307090e060a050d1b03050f0109120306120f0813080a020a060f050a03090c09050a051b0a05041a0408010c05071a07120b010e03030324 74
    0x134410404602945075039141c0f40480101c01054050401d907085101c1159440200380c2c10700085010f100e40d982c40c18041440c0004940c1a2400580b0b272030710850000c02c01b04065170326410490b02568000342d140c214031450343d0a0349034040c0ca941c8003d24a0044c0c1d0041008840198861075030107004403680311524040f40022800c8680ca402015005851b180001011070a40d01c2c0903202d4034030031603007039180c41d034100a040710030500340c0d01c00302490744039400f41011401c100c00c90400424050134242c0c00284054406487d90144003540c1c410180c1e1050000f060207043c0c1c24034801028070790010803260401101c05c0001d040110740e0845015101e4582500c0848070004031020f103400741e99a581011b082c036072510014140305074210a0035100f40070104100f542031040b2403400010303803141640d511252500300c0310000395000e03a010441a803001c201060340c00c01989883c0d40c203061000101d110382000165108140d004101e6054071010040185411007805800036003a9242d001c0e2950002000070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 668475323 1250 668474073 668474077
    0x10305100603020d20060f0c100b0f1c080406080703151a0a030b030106080102030103030f0201020a020d05031801060e1801020913090c0306050405010506090919140309040e030a1103 80
    0xb50000c140b9131a440114400612554800d641d042c45608001a9030f40080d1280e003082c61210180140081d2107a641001044000c0040080300d409101d40b0b8589400146e052541c5143c860187c07a050709004c4418107030803000001300e80d008141c6c0380c440e82c807040000c0c03000e0000c55014020078a0b00d091070300c2003103100141c00300300c603074081c80c100c0310030782c0c4040305002a0407c1c1d40040506450f9a51007246c3c2c0d6013030083c3c001805261000503100d6166003002496040c900402c5029a441000019141c540c042400e94400e5450301f0400c0d0340b038a80c0141c40c205500102030b9040254a48030740030031580010300390507000d40710014070407242280700e0b002c2c0c500b00d10500e0281d5511060020507079113007d45507080844011700407040003505070b58030f41790981a40c0e0b08a41c125101d0f551b54040202d113142404429812440304001002941c040800031100398501140c0600301c0740e403400e2000319486d020400c8801030b10000d80248060200c89061950325084241c0c00001f00c0e03030203070340c00e05142c80000c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 668476573 1250 668475323 668475329
    0xc0a0c03060b0d0b01090b01032a03140f0105040c20060f010f08061503030412120815131e0c0809120903071a071a090d0809030a081f0e0103051006 65
    0x42c0b04031340c0b07919100c4450002c1031415a11410316440e5018003406a40103101c4c034a080749003601c1c8d0f214609450038010200ca4000040074400031044043c080b03128168044541521000c0d980012055640c05e402c0e03032142e00207640208048910804d2540c440b0380455194002d808030109150341c1e9032501000c00e9400b22034000c52080e83e000100040300f00d800304071421f044404c0581603a10707060f11202101e2014504034026120300070310407680781140780e1200e14258000100540a155400254001120303112002000702d0741e607480d4981c00c040c548000840c41e1054002032400c000600310b610b006401400110b591031005d0040220ba2191102e54000300e6803500f81c02006842402d0a040d099a1081e40e401001004400306002c0703500007500c0100070200e201500c0c0304400891502c110f0041c686072180c00302e401001504418840e16900020070380702800aa03042c80010f039a04d845841d51418508901010701c44134010300080c441c03040c81280f5058038059015212400603640d201010384045e44 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 668477823 1250 668476573 668476583
    0x5010902090f011805120f0606010302090604050409150f0c081005090711120307110c15040b0c1f050430030203090c13270c0506030c0c0a0c03060b0d 66
    0x22002c44900e41c0300d503694400464802c2d5080a1132504c9401140100380c42d030254255075400b500e18000c0010381042032540c00f2409107419468094a0300214016008500c1040e001d541c031400d1b12020030000c22070713018107403014020400c000780c100010780e805050058400d80100701054007003040104440c180f101540c0c0050400d05d180d803503001c4100c881c40070b04002e404450060002c11b2001c90707019401107000300e86075901c20503603005004c110b1742000075855000b4801c0c0f140c030700801354410320070040e0780450f00c50150064a9840c004082824075500408a00c0720081411210780c10700d0700c6038041c078010360052000190002480d950004007000600c0d0b461140c2c00b01207043c0c503400e4469001558040850010340d01001e1100000c6204a56450341c11000162501c00c1e120b01601410484082000b50994100e400704081d01d580c2c60040e500d000d00d6018a1000000404054a84044450960b055011141810343c142004050356015010803505981000450031203071a0290380c00031815004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 668479073 1250 668477823 668477839
    0x60112140c09150a0c1e03080105010503060114072d0c050f010905040c020a14010b1c39050d02060d0e0106081212090604210c080412060501090209 65
    0x200c0c1c4240d11500400000c90307018140903510b11101d600c0e0006840b009060361680303c1250040d151040403520f102520128010b40f428210300402e500199150448000b0308140b80d807500c55400480d03603035613040007a100080f000205601000b0103042c0310741c0d0740c814684401c00b446034142c03603615841c80c50040241120086c00c10034446131501842621610805040070041c1c0340d90b030800301e4199841c0c51254009a004549018140214503d003400107030b244100801440205000003101010902c1c0c0c0d845005900741540b004221000001581022410700421400020311035030f10600d42040030100c841400d100800592030800d0307810401c00c03d9000700000c0c2040540c1019400821002e0011a121364070b2380341c0060203103c10b00480c140303540491816940d40c02c0c540c3c000221040f001c0c01e04070003503200d4000c010200741407003940c060044090000d00405d208003a01100c1d04502e02501130258800010700040341c885410200054078410303081400345a03a560744050403401080000e80e004003503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 668480323 1250 668479073 668479081
    0x90c051c140c071101090819081b0a030e040504080f0d15060327030e060708040515040e0708040b18191208011202030718020c0a0b06011214 62
    0xc40091601092059200000c20710681035009400c19400d5801c05104103000402d00240099184900c00685003030034555499803030300b04c030303d03075036207014052a50021407442a280410240d101256050310000c420200d94840319070286071a0b0703001800880102d5401f01820030a8241400350a104a40040340c017410041e0240d240c040d035500803081d8000560b6181c049001c0c10b0301059041c0082c3c4030301c1d640040d51084c40181e8590007107403405884040c06002c119031002a50000145d5058030098a04c1c54a80c5000d280810306070046400490707000040e450b124103000c1c0101c3c00b520440e02154081409502e54a006840398101030703501070701207900100060300c2c01c0c00403940040c0070320291003251900340d0b135070307c40f02400001282c04441840d818901c05d050554081e52407405020450035181c403507400b581c0001c1e44c51813540310304112070319898004499040d80e541911103001d071400554401d04190f14081001d40011030f00280400c20309210144d0f43c1c100c900c40c1d003600b050040d2078880e203911 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 668481573 1250 668480323 668480347
    0x80901060e07050a0c0c0905340c03170906041a07080711070306111801020f0c210d0c0308090c01021002031f091406090702031206030709090b0907090c05 68
    0x1c808049401484088140c0300001840c5200210040a41b40400208c506050032820b091803214001703026002c0013810380504003260700c1e020640700701107070a000618048a14041c0c1e444003030401070210000b803038010010b643c2404214140f15500c03800c00c21440e0000e14030380030070000302940ca0100080000d40000c00d860300811b00381c01c01070303160011500002c1d606c0d0746900c142c4001450141508001007a00c035244c2180301d404640340c40307090000c1c1c035190102c0010550b076150602900762084050a01c000c080700c1800480e041081c6200040c0e03502d607420410041c00342c40800c00100c00040f41c2c0300002c1d800e408041100548a00b05030b0107070034002400c4a0420207500702400848540588803081444220f00400c4c0314010420008045403c24030f880c51500c6500c0010440c42c0128042e10800c260a540071084a100400303000005880c4d0b1160404a40340001c56085034456510381101001440f51130302c0d15078460681f403012550700343e440d00507200c1501d0001c0e1400d00490002d204000c2041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 668482823 1250 668481573 668481577
    0x10c0c030806012007091b140a0804080702090f09060714040e1017070e09010c0801030b100b180f030a02062505120307030f050405030a03020c01020f0a0e01080901060e0705 76
    0x206003c04d1001d032502c02441110b0404c506548000003081ea610041181441020040716035000f09062000d15031700344500104d00e42c86022403d0301000b101c00009820407990f60151141c2640150002c0c0003840c00a11003e0bc5010940c4c0d11442d9128040001e0010f0f481026007030b801088031507806007014900140c04407803540142445503503070b114090100c2c407094554040140b455182005020b8a440c00c4041c062103103019004841590500b02220b0b24a07812880841c1100d034005928000c1e41d032a000000302203015070300300820500c4009142c41300e000d0b031480d80081d200e00884d030700054241500205030307581d10040070007508603806115042d8040c01550056425500340b1400c030258020580e25542410321040c0d0780700441e0404002d1090580d4144696200c130822602d0410071401c09844003a038900802c03503210101500011200301d00c220a4040e10840034410f200f00303454900701400900110350048034103001408580007d03050705414001c5000320b446c080c1c1c40900703d0302c9482c0111596 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 668484073 1250 668482823 668482847
    0x60604050f010507052e0b030a081b1002030109060b04080d0305071107121a070c081e040b03040204051e010303034a010e0606040510030b010603050702010c0c03080601 74
    0x4000f0611000c408110140032141c400000400318034000e030078504140c900406051040400c46241c41c1908805850000e07105400c80d03040b95856440d11007041e2181344240c1c00b0265003406000324401e091644d040c036000b4505035400050207100c800c0d2625800d081c00e001c0c078410880640d00140220040390b0103a801550490b00600e81892414489000b00e0f10701072643e48801c80c15051411090184810a000000303d8415040061001e040c00203005000814000020b08260070005054100789015007400040d03d4401d82000d440701e41d121003100c2c5a40080328207074080c0b400e010010b080c0e10490340c2550130032403050000030032990a540f030423002003055190303507000c0021400d00106101c80c5010882c11074444c0c11208014004507101008081800502d032405030387c140216281f050340b01043c1a0380c44041035a001626643c1c1601608004400e64809403105d4a1a00086202a41904000d2055036550024098010b50300401c0f60b4105040d04060009080c0300080395181d845070701c48040c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 668485323 1250 668484073 668484077
    0x609010c14251a0901060f0e06190f12020a09020304030903060c0507061b030c020607020d11100912021203011a0313050601060c11030609151003050a200405060604050f01 75
    0x81d85040c1c3d00d507039449440a80d031400711009041000030800003400340c20040d08032a0760000384c940c5400074600c40607030041c0100784a0382c0600c03081100d080807d01c00310020401d00080f001d603107648038850f105d8201d0308c8034264002d40c4040008101840075000f200d01031035045d03a41315010792031506c0381c6005004145044042020800011022528078020300440d02203006058144003007046014049070141004d030010341d0021010400701e6900810300840031041c500741620600c200c82c4c1b240707041961850000415610b0320307030f42c001800024280d240b0740b00301640071034201c083d03000790300030f5580030900c01c41c1c0c404207400b400c0e2a008a06800a9078002c40b40324003a081d020155556141048000d030040c0c80050309000f038210900003600300e5610441d506402502650410010341504c40212500813940f0110b50004a0a03040c2c041c0313023801c010742d04101907590308280e0b0318040113008090b403030341242046840c0d004d11003450309100c0c060003804001c1415141c680741c2401c0c0101a8080400c03541 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 668486573 1250 668485323 668485387
    0xc10020a08011a0d0501180506030d14210103031106100b040b07240b0f041503020906152101080c0f0126130506070203040e190906020a020609010c14 66
    0x8142da880c01703180d000e03201c940b660700030b81d00f0440501002c40e0001051745100b03074841c91700c041c0840d40002440f0000a860102d1603030f11400040c0101459145c10070004d00465100000000d0680c0f295090108a452009680c0780e0344425841180c102d5180c012000480c1d0304000400030320b00140300402405200300003850500c1d0340c40d1403640000e290344805071140f03a1200d968035043d2820703107103100351389100b1030b0104640c031482c0e81440884209400000d00913403000c00455840d507129400c1030307201b032408901d02d0b94400c54030f180a981040407021018210b040040041805000030a00c036000001c058201e40034280403200444064409040d240e151400902c8001828015100c0b0300744a4016411400d10b55880f0b0b140c0340c2e02d00311004011400f1500180000e10030710010030f80280c0c001c0105001c18920f1010403060400508504c0e0b401003a039480040c424040c160081070580c850b4a0034002001440440c1005550085c02e241500007140c00c100810800b0002000340f074400d1241d2065082 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 668487823 1250 668486573 668486587
    0x1020d090807090510170706020f0a0f0803070e060a0302070c0f1514160302010501080c060702030a200d0302010504030e10050a0302071104020708030f01080a03120b030a05060c0c10020a08011a 85
    0x1c584d40d4480c0d2900141f50424030b818010141c0411110074419250401400d942000340c44450a001080c00001c2c000000007003c206c016124190841d400080100000c1e5250801c110180096000b00001c964a0841e0b080018810a0103410001207a80009180100001c1003800b16007d45000d02d0403030251406000301c3c10400c940e803910b646050b100e03800000e49541800181c601c0c20880c0e5a01900c158030800c030200c01a180410074003121640204507030440f04083c602003503c2c6400c3c400140c0c02c100740e0b01458050690541050b4000d40c0aa119500606561410303c822a01c0300751901010600c2003080c0918240700e50700424009008140258003800301c9000981070b0707886500252500e003c003006025545406028550040030800028611800c6a40c3c0c090001e201290107210b0485d40d80c004124592024440b0915895100094031600c0c84c02d9013101100d90411040610340b44242004007400c050035100310b4001d0882511059000c2c0c2c40d24448400e800300300c2c6004500c0c1c0310301f40300320 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 668489073 1250 668487823 668487839
    0x306030803130c05030d05122211100206090d0e030304030b092812030c0c050d030e0c060903070e18031306030c0c020901090b0607081801020d090807090510 69
    0x55402402c1caa0080c101048650610f41c5220300380b5000107100390040e907100728680740c118044078081240070522400e40c0c2d4507941c2e40c80504551040b56210782e1100450a000c1161440d043d0790f0401c0100c030110f0388041c812204982d244801c0710b0360071803540329409080b00e25000c1c2c00f822020b104014100c0346005e0312130380c44d08082071064419480b135502080c0e41d40e605103110014600500e07070400003402d1654981d2580a4584031074401c55080c90307074401e00903151a1045041000c8550807000711a2a80400f03080207008006d10070701d40410f4020414000614030b002800c5036050203006004042d0241000f035258801000540300c001102e07021814031f060590f0500c041c001000c15100c1462646107031050207025214007081e1241000034007441880140d942c107142a05581c9091400600c1c07507c1000419014441e001001c1c01c0d814001c079146602144080c480445130f0b0003079082da002070204203000d41d02c0f50050302400060f40c1100005011000345a403041e40c2c418542000225095a10a08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 668490323 1250 668489073 668489077
    0xe030c12030106080903070f03080c041707050102060a020702300703060506090622050a230402040b0609060f090d0c15020706140f1e0423010c08090f0103060308 71
    0x9120a520000c0010000c00703811481350f560010001c0c004d14074000c0a9602d000c280c00024100a0034048814045001c004401c4107039005806903001d01600c080a4500c000c0c0e484800d840b450740140714900c00203040d40b1090080c4c8481a0780900159000e00e1085d5a0100c0001d1418001400c0d201d8221188258001003007242e0065019110001701d81c1801814403400400080038180503410401c2e0041c4003141409406004a500d100d0000385600c644903090060300300d152210748061040481152030301c949500c681d0059100b00c90070049441a00b06110741c07409042c507001e0f0b01c804d0600c00d840700221150000c1100302c0340100403108007030040e40c2d100c006a039240c0000144031355480087c04441d8042007441c01034101d50030034810300c1403090107048241c42110040b200b1014041740054907640d1070440d8100314080c86c40d030181c441b901d4411000384410304401c0e00d1404600e0700a11401d80d4000c070308650003940c0044901d0710b08104d90042c0800015000c8085040650350b0300b0010200305a040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 668491573 1250 668490323 668490343
    0xc0a030f03030507080601050a03090f0516140301090506062e08010503060a1a0d03030f02360f061803010504050607030e010b060d05041b080309040e0a0b0a0e030c 72
    0x4125065090303906005048a400410900c02d0040540500205a030030000b80c0c1d0034841d030380c500411152040d00d0200c0f210b80501303a0003440792241c00c20160b105400e454a1606440402c005206007030f00710070405080e0341441c0c01c05041c5d5040013020074414103000404090002c040c5a44022103680c603c107001c91881107109100015400c50014809440d0a000050b0405180a000c0c001001013510102d900302e400c4140520510400745620105030080e01302800004903100d04540321184e0251120011000e4201110030a1602043d20000701e400c2500b0149440082c040c460001402018040568008803001003e06039421000207150307000d00541b0710841c4204083d03c11810140d40203030690300c0c84a01e610003039041c071940701810f07100d00059a0000f1021403010070340c0d491703030300b0404507651241421001a801240d070104010314000300616803e80140c40402400c0c00f07012119886506085004042c0250140415411059508486030784464002941e1900b440d10800c00c0c03614800c01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 668492823 1250 668491573 668491583
    0x120a05280e0f01051201180f0203180f1b0103020d020d0c0c110f1309020f120303040b010e090a0f08210103060c03060612090c03170c07171e0c0a03 65
    0x1180d58841030400b1920018603000070300b08941450007621100072a00014021111441400b00c94003001e009240c1022482841c0c8140c215540d0521741408880803800c8404a80244210085060340342c82c0061007401284c0e548803030b82d0b480b5240c80011170103580004c0b2000780858080c03007011070b000364610501160303030541e0311504668603551500b440c5c4842c2c070182c4240305c0d90030002580340360b8443c0200600603502007180058000020720000e1840541d01240b01e800c40d400d0300c07800c0d801d0900080107501030b600903003068400c0d0380c2c1d42014044c0c8079021148510b00d40c02c460780c3c002c001016031a4100e076aa200c0c1e901181090700e01000c040711551801130310010b426060b00108107200d000d02c529140000c0c5460180141410f1904c042c02c0e5803c880c80c0204003682d1428020148003032032013000701460340324142041e131210300d00110170f030f031382000b5400861402410400034043d10403400c2c95410300301c954041c000412801e14041ca03400b8059020032240e0046040ca1503071a6030780d09a040c0070798812 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 668494073 1250 668492823 668492837
    0x151303081b0a02100c0201150303270602240105100c0c0312030c1404030206040b1b030d0207050d03050919030219031107090c090302060703030e0604060501090e120a0528 75
    0x24104c0607040e5021034a00c007095902d082d4400b5040310041210a0940ea01418846403080180143c900304030040000c251071002d81d0301001c01c043da40400c02b082500c0390088184050310a01103013041181080c42500d0340006d00070703840c90f100b03401208514902400ba450011501c2d0f03903a201c010030f0b01203061549001a66a030002400b05410022862107503420387c15440c1441c1c115400b0a0f91031040340600c040c1c005006c00c030100d0000a0300c0c030b5142568040800d40b40c9030340c1c0c056072040194028540032609409088040500710740b280c410180701e07041e0500180103000c60a01121080300203001c05804500440892240b0224170065015030725100e42d40e403c0440d56060941c42c20111243c103c000c5050400d507800c88000e03409031042007a04d40444035590758803440d10341540200382c006003007020390007a00d0400003400443da200720f0403940640800c2c01041c03480d030744041d2544461006540703441400c1c03042c2c249041c071940240c480050081d040420114800c1c040c001045030380c901c0d400003e00f503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 668495323 1250 668494073 668494093
    0x1005040e0f33121f090804260106091515081504020c0f0c0a1509061206030204091401050a02071502130815091606120b0303090a0e0108151303081b0a02 67
    0x350080701c4060766843c000170001c03001030769584d00c100d101d01e2180f85881103440451070780fa0011201501612010080204002035a408400780644015112500400080780c40001d02c01c00e40c071140b50340042c3da80e035481c00c5940c410f5500392441c404001e00e19000b030390900070701f032020301c0030024452610226401450880500000c012101400c0e821090212502c00e00340144241c101d40d0841c141c400d181062500c441d040c00030340000f80340719130001c0d50007420124010140080c1004410101000c0002840030707a0b501100c1d48181d10440c03100415004d060341c0040a07200703556000e0b0101d062243c05040c3d0103a03642c00020314184284c040c42c02104020b50174080006070030010300700a6409052000c4245141c8080506100900d8111541c1d09840303000300c0761240d4040c81200d14a038130043c413807000240c9900c1c10340d5111009003c1c410389032042c250f1024401102155031032203003400000002c0c00d61101d03601120f03032031805059628520140307402c0c5460080d5440250100402d958000c0240c115 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 668496573 1250 668495323 668495353
    0xd080f0d02030a110c070315140f040219060e091003021f23090108040c0b0a0c0201020606090c160501020702132405100f09051005040e0f3312 63
    0x19075813022100400b070802103031700b42c504040380300012a07401c00803844c25030940301e0750301c07014000c04400841c40d07074099001c0052103200b51080600a50080e150340c3c14130515410911150302080c006e41d03001c203101183e4100246012144180e203c0d4030b4240c0ac4180d50b40c0d03640841c003032400041c0c0807039001c0602e50820b09040d90110264039246404040c0c02851414021148140d100e4540042d0401032040005002d10800220701001400d400f00100e0303603200440380040012640403022401800703424007041d1a4542495501d010b07002020300645030420365032114102c20040c0a040707a803950280243c50240c8d036200d0900020070b1500c0408103106104100800300300d105880c4403404280340140502a41d113548a0b2070a604185081002d180d031507807941a209488280c0c403850744111150940601d2a5000010700212400109400c80d60348038010400e2228008480d08040020501da0124584200380e03c80a23402503404604c0d48603414170303001309503210070f0021003903030b1603009241d8100084 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 668497823 1250 668496573 668496581
    0x160308040e0c0406080708070c0212030a03061d012d0e010321020607030e01110304050d0201110a020a020906040603081615231008030c0601140109140d080f0d02030a 73
    0x702800071031903e401c0c00c1018040c50006010a4100403401d070004062a008a00041885400800d80c824040440c0206907899000904040000e402c000c000606074003440e40310403201420081d101240d0f82402080000310200962070000b44841c9251181ca41c08045490405070080c004222810360660501071035034054200400740c40702c00000a4006940d0118000d0b800565030704e80801c450400901e0140540b000c1884218607860001c1480300304900040c50154000c041c0d00203014602d07040c94145094081c5000c1e000160300010b003100014601244440c0d4002001040000e200b03450781c0348c0040d030b80c004c1a01082c004562095990600c511a446000010410001804001e4012421250310041c4208074400020100c001c603d190705042ea030038002d4201441280c0e02d42c0011200d00380c0e1164284122504492418142142540308400d96016508250280861050a041804a18264180103035070300c00d000e001e403094100c055001824104510380f00562a41001a03e0800711 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 668499073 1250 668497823 668497831
    0x30709060507030e0409020f03012c0c031203040302071208070212010b06040b030c04080a05100c1b0320070b0703020c0406050a030213020f041d060d11040e160308040e 74
    0x7120080c80000c00080c0d04c00c5101e52464410340d0003103048003903480458041c0c00d0704c2280a606500b413507003c12900c00c03000e02100c1d201004940c9401c0014010481c0b070303101c3c413840c0c0140c0c0e09038105040e55803180b401e0000558100f8881e20440c4c0c1c0c0c450361a090b070101d0210004e400c403000b030310029004056142055003404518581002040048450b80004a09124511400140880210010310400500000d030307030080c1440e40549417030a149103007aa0712400d0003884410264908490356030018840c038545040c19a00c0c8568880c0e12050707403011d8640c032002c40150401000004048040e414041c0052801440403089030303a15281241760280c14040640000340c000c500e040c104011965a0b0520b400407684c06841c40004081e4406141d0b0191041c0c0e0540d4001d00d10000740003500700700c0940c806021000c00c5494030321544809013009402e00255101808a900300b044990161529a115060b48002c50b000c80da18483e00703150805044850f80e00681d5441c03400700d020400c00c601881c0c61540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 668500323 1250 668499073 668499077
    0xf06161511210601050a0c0302070b122d180a0f0b0709060503040c050f011b2108161805041b030612150908120f1f0602061801021e03070906 62
    0x43d240c100d000030642d00501c0b40e54810414118140703800d2600034401e0300301405200c2226076036455410780076038046d041036031010b82004000c08100301c10108104074610074030120b48030300120303140c0c1559242e9113091540303154400c0c0503150040000602130b28114400038410741c90100c40346408080944450566403010042c014108100800101c00f0f0b2008800d4500403a82d12810084980040f22043d1100c070041c020bc4501c2c4202d8000d01c0011751403880140c000341c107641001c214040301200c0119042e41c409050001d108010151240510364040009440c0b1940c506850303921310004060700d00c58044080b4100c0762a0082c0c04841e41409546c0140c07450100310300c83c4981c6a5078140040d104203401c1c43ea120b40d13901402d01005201d00464400c1c41c5180440b80d940e00300076810311031080f019256040014550610904c0c28081c403b1540d00701c0d04140c01410b941d41c2e070b0349024079880200d80b50b041600d5508110040c2d08246074500c00480d40c1c0105a20394031ba2a02c04400f1f00441d13000d422400c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 668501573 1250 668500323 668500387
    0x50d0c0b0a0824130911060c01020913090305031b0d0f050103210f110a0c0b1809090a021201090c0e01080f150a021303060e0d0e0f06161511 62
    0x20f0244c45038040d01042c800820000290000f44d0300303101074004060f00c0c0503a4041d400180c1040f407410705401602440204840ca07041e000c20741c01005040320103c05000300850030a10004101d002800c14410560350703040d0382d5501c0c0c94529284001252040d0040d103080070358800061041c800006181802d0880440011402121504019009148680c0040204001e02c949118640b4040c0b0101400300c2e84044009405034859158070400e401c90b0b24240000000c034448000680741c0802d465000d082042e0240000700c01c00d800340044200091040d018942d220000301c0c002550a0507418000c11405210314100e505144100e07081040c90713656040d0980c09070422001c3c1003080d411030794100c0440000141d0b1a5400003203012400307600d500c081c0010345042a41490301d1000305072340c040d1f070382d10b69107000c01300c5411700800003880359200819400000a2100b42d01401034005210350303040c00341c5001c2c0d89414140c0e2844003540e06505004014404c042443c440100301070030030200c2044c150301040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 668502823 1250 668501573 668501641
    0x90e07080a0f0f0c0b0307030f0b0f1005120f0f070c12110f010603060204180e070303030506060f070f23060f0a020c010f02090a0509010f050d0c0b0a08 67
    0x1d0390340c115400c001d04400d00400515003004804002010520b5101000020030740d69100e40300031540085440002180c28412a0050780825100d0640880001401c984000000006110b01300550400304014041e041203048011f2180038410340c4030303a000038801202e625000d5802402234a014008030148030701d085000002503840c10a44200400a01d4000000b00f030b0040614900004040c80c14a01d504c2e144011080c400075400a10556a001d4907107680840701052040c204c6045a1490303d15811208052001030f01c40e4006c50f80000d0000d007610305044060003074801541c000c3c48121120010020081c08114445490203580b05060312413a46440202005c240c40b41c6008100a000100b4040081d4002015506440100c2e140e40000c01141c5e41b40c0c1c1100b4001e40c08036100724440c00f0a40c030001128034001c40714505a8048c8840442c2d42c038a040d0902410100140040b03c802c0b00800f0b01042c200000006010701500d00e81d2165101c6c20014000c03000812271442113101d000959001e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 668504073 1250 668502823 668502839
    0xf12090a0f0e0118020d0509070906050105092805130e010609090b060112320c03042d02040203040302061f050f120304051c03080c090907030f0e1204090e07 69
    0x2811180e80079002d80c1c098106001c184c2c001d219800d10f501d051441c01003842915040040c82e4015210201c0c41000055210001526280501c480385070344402240c00c5d2031441030344502c07406c42e0100c5080b241400c00b0380b510001401804030076a4648142d036600070404024000b40510030003405080070401410129803109643e0340001420681481240c0381010311301074556015180005070306103076210142007920b0300d08500c00c0100c0c1c030000c40e4043c3c0011a43d10102e0340300300e0f8009c0b079010441c0122000001c0304280000081c1a100c4c0c2d00040c04101e000c056195400154485d034440e5001d41564a00000048104503c030202c9000c011604003091001d512a10383c101050f00d4111020700c3c2d18000610068a1403185800c03150700007090300c2d540f0040740d00705800b2081c8540f00c5d8031420345036510150407628a02036a6242640140301c0000710300d40038020b078001c2030400041c00d00415410001c0c100280742806660a010510070006030030400d281d024801d4105520250740a030901038605004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 668505323 1250 668504073 668504099
    0xc040911010e13020310050103060e0f0402010c050307080708030a0510050a1e03050d0e12031207080405150702071509030c030201030b060d0c02031b1507110f12090a0f 74
    0x400c5040c03100309440440300e81c1d2a400902950103440c80159942d2410403048000b51a061003000e002c03d00b00040810b160100840e424414040c1034090007003555540c0044406525030842540c01c1d0008110010100d00d030040140549030064850075640d0401c0402c040842d1801800f0703d1440490620074020359890955010072520f009280040e00030301482c0303410408046500003001d62041d03c074440d01054101001c030013001002c4664048074160955901c3e140c2c400c018030714003041904400200624002d00c1c205411500900894078440d03201040303641d0580090315403201503407001900b0040701e104e0b03404c0034600f000075291803030089266603900c00c404580390100906054807a90145600c0e02c030078081d1240c0002079401401035a01800300651a50f00c0824070003004044194032100c507980014044091411010000c4a25079408000b101d1003803500340703031420b103014190001d2080042000480c0284103150401541c0d10740c00c90030042540720340ea00071f01400c40752500400c040030210203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 668506573 1250 668505323 668505353
    0x1c020102120306040b03100c0921031407140a0c060201091a0411030d0c020108010b0301140f03014d0f0c07051003140708061507050c150c0c0409 64
    0x7240e41e2680c440744000740262002101c130507011312440e4403114100d4190303048444801c066403101409243c6940001c2070840c0c42c042e220058151161300140001d1056000f0708081c2d08060809051800395500e00312039810340085102c03a54030804030304c0107021119801c1401005607000810810003183d8901303600480007a00303881a950002e00040c14004c0000407030310400070040039240e051000580c0a00242a81c0303038164004ad60346000031890454100803241603803045464000801c0f1200d0411428100401c6415095501c030076807004199460002c118106118130101c00402554078400c0503106441c404420901c2c00a000d15050400141d04550303200d130f841c1105903527820040100c140741c00d070355a0049410542c04201c101895602d40e000c07107413114440101c3c0801c0c0d154294211042d003c1504d04d1a8004031041c04c0e41d00c0c001405008080e4240704109031840f240c940400a591000b42d100117021030310002940e060380c00c800703101c5d1100403901200c0410490404d5100c00d04185c1e42c00c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 668507823 1250 668506573 668506603
    0x501060f0b0a021b2b08040b0415020a0201080109051b030711160609170a0b07030509100b3a030c0c0914060d080c010c020705030111041818060e0307021c020102 71
    0x245c5071449210303030407441046181c01c41c22040d41d0780c1d03880d10312181680c45803092040760452480e2a24446201289074451160160344440b490703406e2180000007040c0c0074202d0074900103a4076a500d40108050040c0d4030403601512094041142c6104d01307400c0511003201c500c10643e56030740600205401003108415a411920f240032807111020314a0301d4807000c1d140203484c0d000190200712806a15800a0340b00d80f81540030348501000301381c18242034a040d078104503800004803080e0b41c0000d081d5580140c4000048001e4507040b082042d14402030841510706a0001d2220003500040c130415245080080400c2d9400300b002180b5401480600180500324a100d4039800b00c001c024040080240e880c0342440d08000c0060102811001e9135074401c520600e4065400c02c0058004c081d40c00e8292001c0360200c2c122070706460702032040340c8010400c3e1700038850507029203800400440c031240f1450074043d100e807008582c1c030221401000200450113041c030601000d0240d0810060768046200f6a08a50750 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 668509073 1250 668507823 668507869
    0x1052209060b0c061501023423121203090a0b060604080601090518010507080906010b0a0804110103091505040521091915021506010c080a0503040501060f0b0a021b 72
    0x40310040341041d40c142c0b09010740e0201c41a94201212041c0c10b5001030b2356840c0c00c81d03110541c0c0ca101005c19803500c90303c2220503d4030324882403850305021000028030b04501c000c0c0c2d0b4015a02e00c401c0c003c1c075001074510f81901d41c442031500080203c1c0100240e00940200c503454102858484a95504c03441400760020301c1d41c964010500344d0854550607409850340c0f00081c803061400f044028941401246c01050714803810000161803444001260840c0d442e5aa40c401556a00c0d01c409201c2c000b140851410507036140b8101d80803076800d642180c0403a402a030045440d04180c2010b80c03602075280b140e80c1c3c0c5402800e49028181c5031103000c031441c1003416524128100403003511604111140e40c0034000c2c8841d010400d1320503990104503010031040c000800f90287d10ac10004440402110300000c0c0400c00804c42648414040c9001e10350252190001281c0c00352520401c000c18400c0307034000c0c4c1c800790002c0340c141038203078041c0180301c46c0300d038410b400d05800c1c100c50380052400e50001d021450f20040e2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 668510323 1250 668509073 668509111
    0x20d0b040615030906020415080403140c0a020918010219030e01050c0d0f0e0106090c0912021c0503090d0809030607081b09040b090711060711060406050601052209060b0c06 76
    0x56601a41d00030710f401c03580041c23554202c010203030040c1070072242140060500122002015213140c25030b0b0700458200024003e0503503a6085c8408a074000c2c01e07149890710b2040500042c0002400107001140340806503003019031068a0190944440c0a08c00c0e4180e4140340401840e4580c800c01d4546500c00c02c5808a0442444040f00008049841250f00c4c01c0d42083d5020464090301c3e001441401050340e900f0042c555560080942c40300071102c0294080c031401c1a070b140702d4401c1e01c80c03060020b0250007501c1c640b02e09100003610f60b41e130304503040300c4616001c1440b00140c038090018692203801410500068903102c80f13150ba031440c050140b450011004100034402c0d485031390000c0f00e82d54000c0c00d43d45480c00c00102c05045002c07070404038040c0303100e00400508442e2040440040103400a0020015603d5995030362028100c003d14150400100f0302c00200c40200781e45035034a0844402e03822564032811300009809803285d03034100c100c0c4180d041014008038400020256800700402c030210b00e003044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 668511573 1250 668510323 668510333
    0x14040207060f050403051b0c090a020306011106010311011d0f011107091d010b060720010c1209090c030e070e06010201111225020309100e0301090303020d0b0406150309 74
    0x44040b070755108a45050200000c041c0c0102c001c00c4881c030700c40b0107409001c5010b80500e40da052070403002da070016100e03004900945c1050700516000101414085608030700e400111345811801da000342d0351680c4504022125503080b0680c51007185071508501d010001c01c1c800310300452100d030100d60400845c42e1042d041c0d230506202c00c00285c01510000e024180c21090115501010314911030229483c0c011a900c140c0342160031518401c2e405014000794014290000314486808410181444040c100d00c600113420311282c3c40c80101c4503202c2d01c01403030501c4002d42c211001901070f1018103141c07038020001420b00040e50011200380380c1ca10350040d503401d00100d001d0005400f0740480c0718000702d01540440690002c0a00c2510344a12070014091010000800c616a4078035020143e00100450324144c144003514405d6103000b42002d02030120607101003400c4520302d050a80002e640400c5410100c00d0314007075819221000c89003402b609050140c41c42980100b400b0010038507640e80e40c500c2c1042 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 668512823 1250 668511573 668511581
    0x60f12060b12060f060306030709091b09050702010c080702070b07050304090c0210110301050a051c080a1205010e160f02101107030e191a07020415050117011404020706 74
    0x400c403003050035210300400002d590101401e407103c900c80c5204079000e07400f50030070405a0344900002001805220700d0405143c00078045a0b5040d62180202c0d601350000700c1052a403540107000c2160b00040c1480c001c0747c000c0c01c40d48119a43d004010b8100248003016900044040a45200d12200c83c1d5410651400514505c80d0b81e011a074524180042801c04580101d103503068a80340360403e20060402801044180c40f00b40201d0750320504070101440a030800807520501e09401d50301c0c00300c4078045522520106e42040c1c2105002525062451994000500829006044c008640d644074140300c40d110040000d482100000c001064200d244624030821001e04107501203d01004982d0080b0384860180c3e0003000f0039400f14110b503030003040e0760804040c0070450fa03031350385850745503582400b18000c0c0070031400703d0f0580d61030001c0c45a4405641c1d04d00c10985500c16445054510600d04000500100055140c2d50012a0b091004028903e0030007401100c82c00c01f12001a42c0c2c404a1501c54024 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 668514073 1250 668512823 668512829
    0x60a1a0f041212090e010602060106200a0b0a0e0604080a03020a180f03231b0303070206040803030a0506270705220e09122715180901060f1206 63
    0x1d100d46810240c01d00c80f5443c0721032401c04183d501d2407a01502e5440c11058404288248801a84a0b0004008052040700c56441c41045e9000801c2c0d0320a012929a04e0710003105030642d0080641030900017003482078842c100030749901001405840c6003c2e15840890b0150004810600d80c00042000d1054070441082440039161604000b400391540812140350510740412101240c1040145e04a03150410746c2e001285030b90390007031410042003985900310b518000c180c00d41521080c401d03003005030b6070040644050040340f40110f0301d0b881c003100c0c5a401c2d18006041d281c040c0a0143e0711b42c81090003200d41228004d14007801240360b407140c0d0001c58082c4a04180400045100080305410101048001c0d0440d40522421042e40d2902d00000d500e0f085802a13400d143c84d400c001d00c1c00f0400b480b0070502001c050b520b80c118601c1500310049002808086c0000e1400c00c030014071841d00103a0a52054801e500c191000e54a0758103103100a000152200614020300080c0704420306021050341110b806 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 668515323 1250 668514073 668514089
    0x19091523091207061106060411070201112a030c0d020d06181e330b060702060705061b120105040504060902120c1804120f0905030a030512060a1a0f04 66
    0x1501369503400041915000d4024001c0d07038020703440441e20a140500441c14440c40311910240341041e642e0055502104894800071140102c1b205440d44880407100c80110740900c420008040707000400f00360503e402c0b22105403060088211601c0035032110300024041d5940010000340d0311148003110040da15040000038908008100f4004010400141d82c03a07000c4d12401c0c410a542d0801c0c5e0380303440e54940345107803142d074019401c9409480e420f80750400000000058611480e20b40280c002c603034580c0c0041d206840700e03400481801400420034000b032034040a501101d40c2455024625000c1300b01041c8501807269840e200401c0034402c0301c2c0e000001043d802002c10106120303900c411500c2d4141403107040d100c0c004118040b640300c0c150881040c45680c3c4880c05401d03001030000165039208892030802d04201005c0c0303011801d6142009810a0b0714000e03215951038000c00c3c403d9034895240205014004c5045481c100301c4041c12840000b0500401500a03890f415400d501a025005662003104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 668516573 1250 668515323 668515333
    0x1d25050d030309050f07150f110708010c090b0a0c201905010905060705030d0507050412230c0901091a0310060501020c060711060f190915230912 64
    0x100740c1c150f44a03541c03042c403c1095441001804030b00c240c13207002c01e10484601c1c60403280c03e010030603c01ca110a41060981c02c04140a080030354040d841e0506e25000b07200c00ba99280c200e0400e41d5001000f41d40180f0004520783c0c909100340e0401001e0005848000b0035507551560300307103503109520354482e60510014203104403002c030300181d285100a8034030943e40030486411000c0350604000040300c0d20b86802c40000e62401d00c41410000042000401000400c84180000320703030449040c0800100900580c1c0701165080715041c0060400100401400350360b12000e0206607a0302c0c1c0c040402d04413031402c4c10001d0301c4400d18020082824990f2180365150082060701021044980d00442c280d540a07802c41e60410f50307403018044a4410341c0d102400401c60141a1131241c60028020405003a640048071f0820160f2404c1400c0100d40582c80c001240030644140aa0072410014407620406850030307040c05d03801284402c0c040100d01400c0d1100b1304000628084d151905440e103a131106040044030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 668517823 1250 668516573 668516599
    0xa110c10050c04030c051009080303040f02030c01050c1507020309060a02030301080c0a180e151513111c200417010b0f010f0309060515041d2505 64
    0x240e114880300003400d050074a4440480e40c030900140a880540c5e40c0010000280c60810342040402c0500503803800801003240310104130050309001860041e031090201003d001c043e03104050400c145052154101302e4240000b00038540d00007003020078003500440302015a102c200f4100d040d40b040702d500c0754025100003480190540d0000095040301c0c10313402910001390704401003012585191040305050300d070040c100f1034036400070ba1141100241720012220460440490210040030864481c03a00f81c0c8006000307a0301d41003680840c011174441e05001c1040181c0088403184a00440f48000041070880400041070391a507400382c00080b615400300c41104000001840040d4001d015070040042c074480048100c0c04140241b825202006004171010900b050045a03168070341c0400401b0580c8030703c0240d0129002d031081c140951420004410b44242440500050710081d6a1441504601c8a41c80384800000b1410211800102401602c0c40c2d81a08400300c4c445a01c2d00100d501101d04800c0d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 668519073 1250 668517823 668517847
    0x3030207140d051201090905250e0a020703030f0c270506030a020301081606080a0b010339020c0a03080f0408061f06030905070509060d06050406330e0a11 68
    0x2134200a500340b0f200e65030b03ea1b2200c1000e001c0c0c0f1003403407004101e540903c243c2400c48121143c030102e007183d06240100c0f040d0741d544903a0300280d42500c100c1c08003980040c440c4181a070600440e0082c0100000a0140c0721181c1401442d07550406199651b40d1601440081242452440d0710001d150003400940c407400c1c58074403100298002e1061964a102d0f60b0601824080794003c0b080417030b83d8640340c1c20303d99a64889900080c0c90f800504ca4101590b6199044d04213814100c0d038141060705031000b001204906019800c10728607104072600f598800103850030160b5800b688142030b07a83c070041c990385800800b0505948c0b402541c0140e10300e8041c00e02005020140f1274503500084100740c003c0c0e0000c0c1e03a2000c0070f4045072000c80000d00b150300080414052420410b1080343c101d40f002d481080d402030103445140841d002903404851107502d48001c1d950364070131544441004000c07403161000c000041ea0384196109040e106074850103504100085200c05213610040a070408681a113644400ca2211 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 668520323 1250 668519073 668519077
    0x140a0909061508120322020d0609060606171303030e0616022a0d02030735030a09060323070507120905010f0c0f02420703030207140d05 60
    0x807050028000007002468110003d0803082c100d40582c130040c82e64998080d420510140c82070600c1403c03000040c40801600c580160122182c000c240c00910260740d031400d141035a21942c4801d08019001c0c40100d0320303404007245990007140380c0c200d144140c00315190580140c004510b5040d068000d1004000c0c0f41c40c0041091a291010b66081c3e8102502000300071580360106282e40d440b01c0d621030141052403d0000b03120408500080459001c5691a01120542c945a0a038100c0c140e1008010b4201c000101104e9a2103041c8403028605003612104001d1517520b0034410301c810191114195011100c0450071440305042c0c4018001e540d1800c0a400703055540f0221045130380700151000e0304d010a210700c0c1810142c4005070b54021035100140c0c000c5503d8060448291102482d104002c0016920800c424001600000404200780d5411094010220300c80300340804070035201034075200c500703080302c12100c16680c103040060702ca40440c2418000c8811300c500b80744046c81880c00081c151900140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 668521573 1250 668520323 668520341
    0x304062019081003080f0a0f0512070806010c050708100609060506070b070516230a0b07050c030c061807090209030a061d0f061515040501211e06060206060109140a090906 75
    0xe0310100312305640e0084440e44207142d01810880c161030086440304e4450f05900d80c102005240540f041100c41c2c903414140b212a41c46940691f00080600403540311310f0094130001e102a90003049036600e0310f40422000d104100700246060441c0d03000038007040c00747d0103840000b1003031104100c49070940d1400000141c464030749091700110074601504040700002d49182d1583d401000503002d600c0e292000e80f81a000b41c80f8001d078a0009000410710b4045c200300d118400c0c002c50040c41108210110f806040119a821868455004018054940c1c0340054000002c9620000008005420150030076a4121901240700c0c2405000e4034400c0221001441034040c03840009450209801030f81080011605500d041e00060020b0000b0005507008469090f44401204502d00707520540400d04c02c101c490070044613800200007542d041d1440311610890025207072500041a5500300000003070041d41d01c0d449840601d031180300b21902191144584003004000340d0a05000c3d0f0300f06890008007170090700f4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 668522823 1250 668521573 668521577
    0x313080d2003060a0513020c010e0105010509010f03030f0c02220c0e03070501080c0702030a0c030311070605040605220807030f02091b0a030b01020a080304062019081003080f0a 78
    0x1808075188001000100c80c018100106005001c3e4582002d00c01d003013010702c500c005070550070b0001c2c4413012000e0045206c480301000c000921581800104107204a060f007041400d04030b489030a1001030341012411300504410300b000f8185400d18400115102a04580c4042c3c1c14a01010850740000c0c03508141031010898844841030150942419610700403441800d0000c0c0b0204045201049103200501015001800b5994060010349941413605010ba1084000402c802d58041c001c540510232a0041c040b1490302c240340c00e182480007800e0f4060700700c203600b0034560320890b16140c00e8080d200000a1201c101610f000343d03a0780c2001d4014040c00d00c0168000e00010300020003094030b2582020300c0543c084001820040c07080c204900a0400c011441d0642c8925042c54000c2034203900a988154800c071804610304284c800d02440070140700180074081a0217104907640400c4411405401c0609482c0c40d230000d980e500006c00d03416041c2e610140000c031000410b0780510705044014040101c5a0b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 668524073 1250 668522823 668522861
    0xd060501030b0604180e010e150708010e0414010f0e1e0c09010b0d0603020a1401200d0c0c2103110a031b020102010e0d0815030f070b0313080d 63
    0x5800650642e005030860b1548400200014401c00a88070366000303000c00d805000107100c4130407980d02800c6843e0200c1e0505560b1120080741e88018190150301e07400341451038010002d501d080440d042000029000030450200e00c078031032100078000d51105111401400e414441c002100c1c00c015140c602401c4d9a41c1030ba203150130b003207400c41c0707000440d90a00070002d042c0321140da03c0d02460421940240198055907503c445001015a4034140100c001d82104412408c000c40c40400242041040c035001d6805064a001103100503040415100ca00d8051800d03c2001007100c1e2070404c03840050741d04841c107500103100701004042610740c02221654401d4071880c0c0c90b900000c51280c0d03580440d40004000481c001030f007658000602c03010640346031042c0001f044514140280b10b0511408024502c00216080100120700b031542150780c0740800300341c1c00f91641002c40c4d5182074070750360503016094104000001242110b44000402200150480911911a020a000c180c05030040c3e01c0c0461241c811 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 668525179 1106 668524073 668524079
    0x90e161d0613060f061710050108071b0f05060127112a0c06121f08030f0705010605060f120417040f031415070e030715050d06 56
    0x1815071342c031079040004c003c0203038030000d4020640c9500d407024801032064100c201c000703441082ca001c8550b555809420744ac000f640103a881000c00d540300224050207200b83c1260356103445034043d0307a0140d07640d401005814681c2c20028103040a2848042c0d03040003e50700604400301800d051505041c00c00c60200119440e0f00c0041202600700c410401244800707020070280b103c4200d403d01e0402107002c2c0c40b0400c001c8000c0c034514201c00049010140b41704000c101c42c0c01850001c8c1140da444000c01001290b9400ca204203e842d5030030036034040b426107080c40a032001c0d90420b00f02c55041a2108184140f1104043d0081da4040784c405040750404909030700601c05000d454103910b200500e0351070000e807000b80204840721241c1258030b02d40d2001c0f12072a0001d4100e015842c01c0c01d0b0301c400c1e10f070000741070480c564400d04415200980c91040c46811070b001d00710b103443c1d00350100034080d6 = true := by decide +kernel

theorem cover : BRFrame.Cov 668345323 668525179 := by
  have h0 := BRFrame.cov_init 668345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 668345323 ≤ n) (h2 : n < 668525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
