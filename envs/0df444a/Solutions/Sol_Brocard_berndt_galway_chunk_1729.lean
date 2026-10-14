-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1729
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:27:34.609987+00:00
-- url     : https://prove2.me/submissions/ec3472fc-cffb-43ba-b260-3e1bd48f1992

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 310791366 ≤ n < 310971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 310792616 1250 310791366 310791389
    0x2d0504030302070f06120207050a140c0901150203070f030315091a101e26060913080331060f2f250501150801090b010506030604091704030c 62
    0x600850fa041044101d46c44500f410050f22a91941002480c081d1180005003a010f84842c3e507070070030400401e00313202c3d45e101956140021b0741e80710b80d40042c421800c2c9011780140c20500c00c60340010f074900030603a0118068500844c2018980100c4041c9400c01d500c5100ca00b56031300741c0e445c80c0d84400f041410b41a01c04840c0020b90500100d4003416610046400d2901d0118800030642418080d180d100341c448901c444400903841c2400745d5500a84041d610940301e41d01039000544520360106d45180c0d1254000942d509540314440e00c154400c419000c042d000e4410040d00e10004d580e03400400d90013030b01403c8041400034440d009101201c108a01910742c040b5214004000380303050a2500600000842425071307035000e80410400c80c40038030a0014040d82d00100c1810510405400c03c0c2c0c180855504261851707660b49915070b00300d415958004018403103540041020f803400c038001d0341d80000054400b140300038095803549600d0072440c1c406040808041014001d1040e15a0303004003401a1468071b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 310793866 1250 310792616 310792619
    0x170702040c17180102040e0a020414031902010503041e0605011505040605120a09140606100e0102060402190f0b12010f0305070e0c091002030304060f0c0e012d0504030302070f 77
    0x15a418031000910485103c040b540c0b01441600003541200d0040007803c07080182030510341d44141c042d500c5485200300c1181e0404400545144c08940d4400f040b01c0d89500c2c11080080386e00540e02604001d01c00e40b4510141800014842940d460320048103104070000100d640c140340000c65450300e241038030020400c0034001030001c190404210703181c0404015015500790342c1c1241d07050140410070303001407090384000c24542e110400065018081c510841da008543c1c074081008544c003401145425005a02001c081809030800110301c40c42c846103d0090921292640642550700c01558000d060840c8000b40301401c8030f42c40c2c04060301410b85c15860400203451034880540d52a540d01880e280c240007800410382e90b400fa1411110b01c9507018010040140240c2800b03901d07900304403001d030b850905050084000c071803140318181c800d8040f0780741c07942080082001140d524481b030701030100564110715003181c258042061840c054005a03201c5986909518009040080c1e81d0f20585450420000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 310795116 1250 310793866 310793897
    0x6030e07060c050f120d05010605070309030609060b03010c020a0b090d090b0d180807021306210203030c01020403050d1b050c01110a0c06081b070b0c0c030403170702040c 75
    0xd0340401c0707030600d2038220011106410b110b03040040f00580003a5a00c290402190394140c00b00c083c1c4140104140704004c140c1c2c0c0c0e0501584d1921425000030b00090703ca07003003800001d2790350740100711007800740c0720005451031030401082c2141e080c40070560250388128841300070401c2410030701e0341c440813600c040c10440c0081d0b04050700d0241c0901071040059004100d60b0402d4005a210b160002c142c41711441c85c00e011410002020f1340b01c4001640141d25010207143ea9035603501924003191410001a0078000713000d000303610300450f4964101e80c54041041004513602090002e070003c0c1d40524040c0c002e400150b600940004204100c89500a240c0301407140402d0300452600c28140082c06c1213800800044105030030f24422600c010030074409043e0101c1d81550102c40d5501c500303070495030100310403643e10040c1c84c58082d184006200d480c000340000c003024564000b828406102e4001c507030400e510f13561050303140080c6403829840d0300c6002c151441980303842c0c002c0b64540c2001e030a06122646c00c022 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 310796366 1250 310795116 310795123
    0x40227010e16210207032304090507030b010c030e0612010b0a09060c0510150302100815030f03270907050901030506090f060d0201050c030c0c18090303071d0a0305060f0106030e 78
    0x5161070f0443c0d01082010a26029400305c15030203081d0004800c1c41d03540030520360311a03081030203040342d031510388800511480d0183c4207210b031800c4161108105040f890b6821685000d684d42900e800c48410b202c68501c14110b03040e6140600014001503031103051940c00201508141d0b88039004001100400c0c4005c9800424400e0034040b010740003141e01041218803000030714040c0e00013074106130356a520001079580074220034040d415000c590f00303456052000f00b55a0315060403202805410400611020b40d015040e8203078000a0340044102d910303039040000d20400c1c005c070b4110004c10f000080c0c1030440d69040c41015404242299000c550f41002d4840f0b652424000707045501552541a0710025a03000e6000c0c2c1c1c0c001500c46089136076a001020b00252121881c100c5240549500e0030301c00840c207061140288100095001581181d0300d0003411036441010b0107400074524290103a0945a0701d03002d10101c05503020b00f008210905018204009020f4140c2c000402c052406481d11080c043c0403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 310797616 1250 310796366 310796417
    0x9061403060903130b1809070e03011a0312030a0f0e0d12090b0103020f1207120b100b030c0703180b040512060c030601050c280b10060206040227010e16 67
    0x17130403140c3e114080e031a901c8070361000c04402641e120075054200b211117607004103400c141c0d0005078000e200364285c0001200044001c1d134003403030b89a00114200c450f0b02042c800a154000050756010600001b9005a102242c9048414003020b0f005040000c00030340e004070282102141d000381c108001c0e20f031a1640503040d03906010013440340d04039011000703055698100c0b1110910100050720002555200301d60b14400c4068000c40b0b40703405900000300136400030300944080b5a8500003851466807215085c00540d0b1000070100d0a00c00b15111162040035110004005030081c07940055403541000104508011461044401c40d80140b04100d104034004040d42d801142c207080c01c686506000500604080780311420b51914031141c030304403201d205000d6044440c0790080c44814010745480c009410840b1103801250090791041c40441c1c01400e1800d502024a964510010b00f20300002821510a550a0744484000513050f4244520420a00c024070000e02540c20099601c66081044240300d40a5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 310798866 1250 310797616 310797629
    0xf050105041418011502120903030304030c050f0109031211070309050907031806051509090718140a06090f0603020a0909050a080d091e0b040f0c0906140306090313 72
    0x2000381e4400603100d012603c2c0c00c680e440308040140d9a1034112003061100b441003000c00511500b075010540301036007011280c0540010b409907145030340f076882c00c0c9c4070500c1a0310200d620b482039044c1504c000d1028401c3c07003030441c483d6803500ca95050300000c410540d4006008038810180401041002a402008000403a1001e0b204500740d5a5802004c1d0001d2550400381075402104c07481080400c4010781c00144200140c140714021035501c17505000f12080101d4061119601034001404119282403c10541d0b5070485008940a48006640e00c042d00081d074111b03a4880d1600310074004005140a10020600b100c001003140320301d19000900e5104980c410b0300602c541d03800a05041c44000d110b1014480d4121540765075a210748000140103160f01030742076078107140c40d180da020840c0c1c80402048050742c000ca5501200c2d141ca0b142c0f81d40c130340e288a0f000c48600b140b0082c0040d1000c424040e090040c1848021660b00407950303806d050230210014641c1480350000c02080300c000385140001819142c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 310800116 1250 310798866 310798889
    0x307080f0a020c010f06051e03030f1e12070e03011e09080c010207051005060f06180f040606050a180605041a09040f27081c060e0c130f05010504 64
    0x9540501c04000c3c429114040482d508121040d08000250380045d4102c1d9030640c0d080e880504501107070303014184403c000c1503140d081004a81d02c0c0203081d0029051000401300e5813000c045d030007141d040060b03120f403044150980950041056080d00441d0441c2c004600390000c2c0074180942ca4204105184505031080c1c90303684605071002c1c031012000345d81c1140038900085507148443e04245681f509200130403191b03035080c50002511824491b80c00502040040d061070b0505100e0b54203140c420f1804030a068002e044000490696a40da01965009085a448159441252950040070b51800c1650784540c28034417442003125950080c2120304481c2c03003541d0821440000c2401005502c00d400701558800c4c1040000c607c2c081c2c55a1010200218290b0070000c2d1240d01051495451003060015200041c2800702c882014810744060321110744c2c9030400070303070140c0f00e1a80d910058015030704085030308000702d0640c00c040503189040024084070069000014078081c0028410310807070103164007a40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 310801366 1250 310800116 310800121
    0x212061618050d050f0f01060e040b04021c0c091112040320010609050709090b090105010503150402030406020309010507080f04150615020d02060c090913030c02030f060f0601050307080f 82
    0x116400841400b421005101085424440c00c2c003603920404200700d60b4981c01403540c59001c44505101c1c40080310307807000b00c002d480e070303115100c90488507401803080e40c21500d80d070721040b9041160410700324407600c5182402c80c0142400031000441700400043c40304d03940c0c100403010b444d442c01c00946174400c0e0b041c54403500321071904122560f90400620401125070a0600124005000d40c11180c8034462030765464040ca90f45040000c242c500c001a86500405440014001544a08021540039051040c5595840300e0b203408202280d0003240c2c240c80f42c40d40030044c042e441c00217002d081d411264900c3d158a2500300740d00a4050a1303009400103100480402e01000340344c1e01504280c004251085c3c20000a519180019484c0c28102007100014094a40040c2c0440c40c101e055468120303018223403500c00c0d82c850701da54a500208441c241d0034404200440300059070104081c01d15000306002400c400c0c1000802030b0288500a40b00905000e001d04c10400000d5000c610313658030426140480d40c1030b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 310802616 1250 310801366 310801397
    0x6030402040506120a050109021906051602030102090d0308010914061302030717040b09010c0201050c0d0b03250f08070501082202060a09060207081b061309020d050402120616 77
    0x2100004c1e02c0c0c0c19502644c90301d082070050640c0030300d0005000360f40d003e4085040c4000600e4840d0740b03005410120f0014003928400980072604a000940f014000515010b040c6002032002e01c80a08202c0005030302c103006020300c0da0306020b105107d02a44088011a040c1000002c2c650703060000c07540e10786c0780d002c0000740c5254800c80d22604d00004190b110306080c01c0c5401d043d40601030840300c0441c4e642c01c0000140c111441481034502c5241d1200980d410810350501e104e01a011241407240c0c10300c039200e0307034880e070b0100e03000300410b401541c031a10241d082c03901e0150804c048582c0d000803aa42c2210000b0086643c02802d1643d00043d00001030241800d880c0450040e070b00c04043c042d402003404030303c4154860f0028104030698109401301d501c80f0340c2d503250142d9509401c06111480343c2c2d034029000741900704403024010202100991043d0349407200a80e5040fa00002c806168403a212014401036040c0700c0d04105500ea0968040c015511b0700f0086c00355074003d14100b140400c045010f680907034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 310803866 1250 310802616 310802629
    0x914031207170313050105060306041e0318091b0503150d08310e09120307140705010f1a01090506090a030212010e0105060904030c03081003050102270a0506030402040506 75
    0x500b4501c0c0c065441c2d051200703079040c04e02c072103890885141d864900421110328001a0180c030940c0c1c4602d610403500c550880710b030312091508600320144043c180451500c1d18a2001c400e0107400380c2c550001d0400d0381020480385408841051800b4000c0c10014000b071154001a201c56001c0192010054035041c2d2408a11a22401c44400e2030044140d000142e41d0740300c11078031b4036140f148540c00c1c03040e00d89800701030310252001d495420090340007030241501e030008403000d183e003d07403d4240041800140d100340c48886d8417400c1c1c1242c00340d40d6101c4812605031944540d004c90350403400b0504e455590f600000e0601300d46030141034860900800c4030b50031380d650311500501a50b03003e0700341000c540b00086114060850142c5805543d4240b400082c050700349200340520458242e40c81e0086a400c40d00c041d03424900180141c0035186900c2008400300e5400d00042c03080d81c10107802d00c209020b000c000310350070b0030f0b0400c03640b88601d48401e41084160b403010300703407a00039404480000307041d22524000b614 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 310805116 1250 310803866 310803893
    0xc070c0503010c020d1107083307050d0f02040e1f1206020d050109020712080709030b01030b0709090c020a0803060303070c0b0c0c0d03120902030c0303030c0405010914031207 77
    0x7030540c00c2070305001402c2e40c0030030902d00380e80d1903440c3c484424206032155500c4402c6406012940e9120480c00040b1405041110481c0601e9618092020000d003080c03d0300040222403040206000151800b400c2503a0312072100b22004017070046043c0360400c03e0145501502030542c02100c0507001c00c86500288802030a002810285560b040e548030310300d130030400ba4004207032407081c540c98880001007811990003110460b0360b01c10f0040e0703009200d000040c2e54410000c1c00881c02c1050b81c0074044001581c0c0c04003503002c0c0d4000c40c110b462074a00f07164003d003da41d40c2d82041c00c0303007420041c40b00f01054000036400c074030b02d0b48850215183da0314000401d1030343c0100c980c050100c0c0000e4400150b1810b000000303040e14016142503502c020300c02c009021000b8480a8010000b0b00d42c030940ba40400065404104003034401003d841848a0700d01c000303481c54005507026000f0b610002410052980c0041004004040503072400400c0250200025196100000b142400361000607120003002000d60035001c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 310806366 1250 310805116 310805119
    0x30b0402181005010e090105090712090f0624050a09020c031c060611060c03040b0a0f0c200601030c1514130f060c050d1d1c11180c070c05 61
    0x70014a000e518602200082c0d02c58a80810049a9214010b040510500d4140c88019010303240c0350322624801c0314030120b051811a156584c0e500140c7c00181e0106070451094040c94000c03d44040007205a0f4422000e02c2d4081c0c9a641410400c002ca5250212008200c590396040181c4940114540c642140b080401d0071003101c450560141120344541d204200340c550039595201780000c29194182d40301c03401e8400405000e001d000260000d101803410552184c4610800324240303c00b00441c2090b9251403c0780000315446030301408203071003e810210200d400050060001c4d5145885140324480d0f02d00401c5030b04240a1040e101d0a4050100780400d0051450040d50765004c2c002103d04110580c001c1c0d00d1100c4c0c0d00303400002e00c580310b07903031152940d034008001d461000d04c4000c0507104d00e030441d2141540c90307603078941310006075035825040ca98400039043c007004101540d160a03a000c10f405080a0f01c949105030158010340006c4003e2a800303181117940f42d0f62503038642010800401ca503808103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 310807616 1250 310806366 310806409
    0x40806040b07090b030c09060706090605040f021e0f060d0905060c1903020f0d09051006030f050111030c0a08090a150b01120c02030703050d0f06080a11010315030b0402 74
    0x108000701e00c1c1100e0301c00c2d481c65a0b6443c0881d1035880031412480165082810b03868140075603150b80c0380c0b02c0c0041c0790740e51182c00c00040b2480c0030342e15202526030888003644e0f2101601c44000c01d5081c5015000720807407000d044913060702c680340001130034080742c421001d004070000319070070200d03403496803009821a4128044982903d00003003401e0140c1e0044400c007a01c484d0ba1031200070707030f10300a00075240640c1c06004140c0c1030222409400e8002d0a540e9030688940c4502110840c4091185c8104006140101c204034003400d5207042c010700b9210b2400010840c2d003000c00422021484001c145c481d00f41051070003040e5900e075404100e2030306540c074001400e51403000e0601d540d0225582d1004040c0c0c0f60a8071044d103c420f088007804101d0746c070741c070740070b40581c00c100520310009214000a000040e12820700088420341c1804500031079095801c5060340341d00c07106252040c40032500c60b2007440082403a043c8079180380300070440e03c1e44000b444000c2209480030045006c650310b0b4080000210f9031a1340d031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 310808866 1250 310807616 310807621
    0xa05060f0711070b12071e030605090619170715050304031b1709032b2a03050901020109120801170703050d05090319030207140f0a050114040806 64
    0x111203940c032050710080c1c0810307100c80440c445107a01048800445102100581c241080c0d02c030f10200d08080200361a08000010781044000d5242d9009100c0740303585682c000801c03034240024412540d5000e001244901d001400210000b48000c00e104252900c0c0420030000790b00c0c0c58042840c2050070703000800500c0c0306000d0307504000d9205001c2c520580c065034a8050b03a031100c10150b2004202ea50005d4604a441c443d0900c134219140700404009001500700c9403905c0b01c4540c04505d161040c4039041901d4a49840009255480300041c80d0141469a07001501c03e9036084402050301c42203001414428045040354580c3c3c001c0d4000c0703080315044500ca24003c2c10101d40142082424010b51035001030f0040501030f107040010f407140549a00c84001d0400c842030301d409960b2900200c2e02580e15115a2000e0036a4141030204440034134400d80042002c0c9023070511030540c0280d4600564001e405100c0030b080c807541c2e001510812908203007401d003580ca01c2001401300324403654100c01e40e00c0c07280200703 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 310810116 1250 310808866 310808881
    0x501141c05150a1119030e0705031009050105061c030c021809150106110601031b080d02060609060d02031c09050a181b0903080a02161206060509090d030207050a0506 73
    0x50310401a042c41008060144001c40d131990007682040c03481c0f02d10541800140c640280e20151482d503850044034442503076640000d103090740540311550900d490345049400c002007409015003181c0c045400880c0d0342071014902c00385c00074032440501040f0002100400795114248064dd405803001c0c50000c0c9450b221500c1ca940741c0038441596040d0001100000b0054400c28100c59a100500080c102517480c644400c8940b40900421032490001c445001071580020840245103180503001340c102880c10b1420465104401407100d805040160344c0440140d03004651300d0110386c041d01c801000010f405a08950f00c0f83d4035080150488410032000c540004811951280d040b4404020700481c006c1d4140206036000445400d000304070307030036070500001c0d082c60040c0ca0810040d02c115484000c01c031a90b11741c002c0142c2c1c031003071900d44180c820209014075401040b010f84010707101e0003c0341c18458040359559004c14200300415a02080040c100002800520040e581000869007103041c030f0320 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 310811366 1250 310810116 310810153
    0x1080405330109150905010f030204050c0408150106020607050403032a020a060507060609090f12120501060806031911041112090312150306070e120610090f0501141c05 74
    0x4900004110013480024040540d004540c180c4110080c42d100143c070310b60900001e01409420800284410700020401000400102d02c00380a10030f41c05c8015490504d010b0308251020308080d0411a08000c28030100c0e400031055800d0089603410b034a01d41e04120180040c2c0040103000030741c0010760000020300c8952000150440d580070f2401007042542e0b5440030402c80f00e2b2100e0041c03181205528060120310700180c2e803070041c005804c0861843c0251284034084400980000300403580450070b20000381010000385034100440c084c2d00c2c1d001c9041d5100c0034802040c04084a1003070351101000660720704e054058624ac81c08541454080f424580c443c251690014069003460b1143d807400140c0f070300400421a140144003130054111a1205107044603500e0b03440344080c2e000351098051000c0ea800400c030b414418004c9040c0c1c480311904282146d020f840710301e80380108490804006200101866018061b140012181c00b0b03266402d2590402c410001c01c07802030b0007070281d1071050940c3c51041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 310812616 1250 310811366 310811381
    0x6010e090708100b070c0303030b010521011a07210203130801050a180b0c18030604030e12030901090b0c070b04061110090503030601031d01020a0309050c01080405330109 75
    0xca6020020743e11138030b2030111405200c201500180e1032080400120b4041e40c404161004180f510500c1c2100a070700880c012102d82c8a10780006900038010480591600b4040b0908010500144e1408440c0c0d1900c600c41004011408860035800e0088000d8600070411159941000f4218044c441c0d40c5d280d0340c900070700c0b088400403a60360918180c0301d4503224240c0b009000540c810b80443c0e0380d844501440110b60004051901201504106041c4a50301040014400c0780b20f80e441810000c885414880705000404103d04c5a0744140900e10490ba08820524143e0b0310304000d080d21801020022403800185921050380c84400180c0452003030350040401e414404504112101c0d4032070128000100c40c050540074026030024004034a0f250b108c0d03000641d00a801800c032a080340c8440b07103407600b20b902044403200400ea0b035800840c01c011082c0074400d0500001d00304103880b45001d032141c6d5259203c0f07080c0c00c0c000310742c400500444403400d8108141c030381d0482a6076403055a1070380101c0c401040403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 310813866 1250 310812616 310812631
    0x309120a02240f0a0311040b2d18060f160b06011e18090515090a0605060a081305150405011a06091302070210200f1506010e090708 58
    0x42c5400340d02c6500c04210003103481082001c29624101c24064400310303a030414540c490815444501c20304846204178060005400b2403070741c060741c4103d244145040e0720000c2c520854a0305207060f01000e01c081100079981008100070050074000b0100d000501d8503c1144044a045030303011500c040c800341032102803074006118895542c815140d9400641d40c0f250103160b600000700d6070f090303040344103845008102c041c10a00030440070340c82d8a40c603240041d1802180c0501c5c400320000c00d07241c02c2d0702e8890003160308806804010000103041c031021030a5480f0b00079900341808070030340115124143e0b10810303030b0351182c0050035a4514484c00c1c04000d484481070ba426502582007040900240c0d400e1040404010700c01040c15241c609160140100549810220003181c2e03400c0c064000540c85811013180346860390b59510f007404164164500d0b0000104240b10301d01c0d4404651102c2280001410200725004054120610341d518001201c40e040f85c140c1072504180000d05101e4400c0c0c100c09024000c005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 310815116 1250 310813866 310813879
    0x4080702091509070309020f1e0a0b12010b07150e0601050909010507020c0f040603060609230c0403060b1318150b010e04020a090f03120f030204180506030309120a02 73
    0x1030300001c00710340380e0b004540a80d00012940200d04081d00036400a20381d01d10242203040e502c40500d0004107001404001080342040c030541000052074402c4c07546c1d000d000c0d03420b0307080e0801e50707060982034000e4414081c1c860401c02c001100414440004002c501c00400c1002c1401071104220007030b40ca43e2028425130340210b0f895008504a11010300925100c2d40e06607000f0002d800702d001c00c01141803080348100b80c22699030300c00800403804901441000d8000e562011810a0340c8005212a000c1200c05010b14404035400380301111242c0421107040b290418004140b1407000310024110018008251060a142c000140103800040021640d4280103030f00000da40c0c901da4000c04240da02e45140603002440c1030b00141003038901039000c3c0c0b81c020764a00d000031015407150302602005156400995120445d01080040030343d04c410582e454154078035056041c5450800607020204000c82e800ea10b642d29440010389a071000c006440100cac100400301d486032400d004646440b139031007980580c002d08 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 310816366 1250 310815116 310815121
    0x3090106030c15080105040203091b1507140f0d0909090203120d0b0a0503061003080c281b0b1b330603010522061103010608071824170408070209 64
    0x30f408e10940b8418000d450143c4020340755800a0301d0100c2000d520140c1c00170140040c1c1080c010710002a20b1000d00c901d50301c960014103030903944c1c5850860703c8140081e50055200c904c01551140c4201c0444030541070209031400f0910000742010303078000c8052000304021601c002e010125403c0762900c21403c2d6848502c0369100c4090584400040701c0121010540c08402c000180c0d40d080103240079100d18080c0c500f0340204502003981304804481d006980490b150300002486880d1690104402035000324012480c41d04072009c009000b0100c8000c200d40000365100103400c03040c05007172007124050003034040e0142e00841041e121206900000001c44855000508074241482254060200140c1c0d41c5c0e032801444010165080a15004440e4070340c90751406410080340c1000346000c0c2c02c09031255540e520307001800406d020050300440f003148561003000c01200340e9200d03440003120744441c0320040314416a00166034480300c141140c100080050100800d200c50300c1d019100540c402c58103042d064 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 310817616 1250 310816366 310816369
    0xe0f150d05030f0d060b030a0b090f0103050d0e0102030c0d020106060e0a03020303030103060b030a06020c0a0b0601080f01062f010e010c170a0203100305060a06050a1a04030803090106030c15080105 87
    0x410040c45030b4001c00a940c1603441c0d2002502e20140000400304070b0b9038440b038a07400c0642040e80c050316540d480b2200c120320340c508501c6060348048000042441e641c55500da0700d83e02c05c20100c1070740c107000d103110418006900c00c1c0200c0d02d030007245000321983e800c00e43d8002402481903118a000040001c030107600702e0f20701031200c0381c21242c0082c01542180d0940d111040217006070010254184a003a03501c6000840d18006017409101d010050031030980c5909000c0c100c40c1d07004184504201d007800800a4140c0d043c61801e0540b2224900b8514400f20440360304040002110f80d000c2c0e610f566404074002d0541504004160289840284110510004190f81c0350b002900b080b5071b2001c000c00024850b00f156409580e04c080300340d07000b6030629500e403102d60804409644000d4144e40700c540030702c001d08080c04a80001c21920186042c602c1f20f000e051a8240110300000f8101d00000000c103403022400d40084001c2d5030802c840034501c2d59200e0240302c154202600d400045051030000050380d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 310818866 1250 310817616 310817629
    0x150c0c0705041a100e031603030518030304080607080106260f04050c0d0c030c1d01030f0614190c0504080a0201080405121b0d020303010f05061317070503010e0a2a0e0f15 75
    0x7125450382b074075400c0c110161802c00c407030080200010b03098070042c440002c19a1f8100b00316070041d02d6540710f089041d410044010322618020b840040780e4500030541390002c1c141c41442c00c1e0b1000480740304033a03540741d500d80300b030400480e000f4042d88aa0b80305079200a0119071501e000032640703e00d01410780c181e0b407072050341d40501c810b4407940968141c0398010804140b03c15101051103201e00300018940c140d6880340380b4024000d644101661a5214a00a04402c5880741700310307250050070080d042615103006540c0e00c0d0902c0e00001d040068000c00300f020021b0401980100e41c400401d003035118400607a90b810740300046010712031144142c4c20702800303043c00801140c1c165412002680400750900341805134950003940c0200fa290404100054000056014984030140d5079000e005601d2030201050f0079100106402501c03500103100c00800980021001c0c0540c2040c041c007403d550805e00341078503021420364419560074101a0400c0074082c080d042c02840b40d079900385041080c1500e101440030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 310820116 1250 310818866 310818869
    0x10c24180308040201110a060501090204080c01081009110906040303020a031b030207060507080c070603020405030c0f0f09040309030f0302030403120503040f060e07030f05150c0c0705041a100e0316 87
    0x81800d14000c03e01651085071941d5201013414202d40521209035510b0b0100c80d000d9009402007a0301040600c10904244800181041c00740380c190180d05058600c81e5010341c0c02d1007280741d0150f6401d0319800c0c0c5107104c02a00c021500080031691283e41e00d05000e03441d602420421400501c00e58050328110031280316110115800d41c0c0140b5a607420002c041c2d4869201000c02d80d003c9409120886010342c003080078001925050303402503103603454841850710300864038104900c501645035115032562910342105c03488150890703060045440f42c2c02c1c29189804103400180000007240210002d141c2c00100a0084901c5005001912424a40110b425000030b40303004020103221121746002c00c035a600024880082001901c20f41070750b968401c040200340313040032501038020004440b500705201900990001d4001395003458142c10b0201c041e1140c0c0d06001e828400c80d610b074440e028028080071250301c05d04018280e078500203090302020303160360035640c200c520a100d00405240c43c20034207003e010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 310821366 1250 310820116 310820123
    0x303040305120a2d021e060a0b15040f0311010503040809040e010615080a0e01020c15150409080306040b12071202030f010603031205062409010c2418 66
    0xc00c102d0040c40b660480da1000f26008100314103882ca095402060302000f0740c1a003000130010795120700e00803002e81020484031070300313451440320140100d04020118220340d1002c03031100009401402880000c0200c87c20010a2500d800045400314942840c0280001524001c01d54852860303070079001190f6901c41102d00802102050086070014181500100c46c035154150004c540315480d6200600307040c01c0c04106000040d010802e0001100c00f61189002d4640b001009515080700e29000d1546c80c006007244907811078802c0c0000d07002d1308041c0ca9035465090002c00c1800440640d0500d0303519a001a180b540c40b81d0b20309400a800c500e481c1c0017202400042d2000b0f007249030300e862444250440a4036040e030701405103540c40300b00701c0001c0c0720b2440030307501c25128000040040c42041f000c0703c1000380070a000c0d0300105032581444002c610306076055800e0030321440c0d40d544c01e1030040703400404105004017803126601c941d004017042401605e980703440400c002c20400d038485040c002200481140079 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 310822616 1250 310821366 310821373
    0xc05031506070213090f083106020303010e0712050c070317013812040c06080906010e060105071703010518060d0803070c0b0403030b0f030318060a120608010902040b0303040305 78
    0x400718481c45d800c12001c4a014400d074030040d002a40751964107510404081c10004141c282c405080780c028030100810160340707070407030415a08004003e5030328401806041e2040000c1c40005820b43c0c89610650100f003a008030601c118107040d980c80009800089040340030400c4c1c130102d40b9140c00102c034030030304030340703e5442d0354181b8210a0880407000b405400710010443c0140d140c2442c22404000510742ea09480b40360342403d24050920455600e5140c200c5020481000d05006440c9030008006054a0340c1d82e07503617242c64540718010b803080e00c13030f0180080072050a48080080030001e000514107d540983d82101c031302d004072a0004400c0740072600c2950224803218883c0203e8514000b859018145042c420407103119500d811a000b14111400c42c00030340c0303c000d0314140b070802c4410702200900650045051880e4640315030071442c2e07680c000ca0300a00e004910411143d101310084659541c041c0c0003040155150060540603100300304040c1d014a05180c000c100505000040310708913900840074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 310823866 1250 310822616 310822639
    0xc06040816051605030f0a030816030e06070c0501111e0307050418051017210f04090b0a0f180f02070210020604060f05010614090a090c050315060702 66
    0x400a99070481403001c1c141002008540e000203500b081071280300c0040096181200340b400042500d00a482d841d40740c01500859661030010360000d400d00d81203101038200c40100f41402000310f00034400c4a44464041c481c40e0207101c505034200d2650060503000c0e000038890742005140b01012845020b592400c000c0c455400f41810704403807405582c016801c0e15141c0d00c0c003641c908207000794102d200e9618000350794030414030200015810b82c803001040510b980c01c010212480c0e140e51200099802c558803d002e020481c00c0000c00c1208071040e09440003400c60304d843d10359110000508030824402c6c0501c0810740301080c581100c0c4500030407140103c1711411000c040318121405822152130b82c0c04099001c1c0710000042e40c03405602000130101d940244003628080c206501a2840f00300140c804130300e0940148042035101c207111400c41828429196210340140c082140905076503c003800311880c00c0c0404488544c80001140641400d0100e0140075076402d040111070f114810000358040c002018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 310825116 1250 310823866 310823873
    0xb0a0b030a06050405071d0906090a0c03060e090d02073c08030d020304020f091902090d30090621021608130f05030601050103020705280b0c0c0604 65
    0xd5078400424070002c10b9265035000032609070380003030340d02d01d0100305c801c005411320405038211400b021747e007129491020300b00040418442c0b9030280042c0c203226103414070721240ca4043d80003030307006014202c0d4a41e02031500b0a84140c48110070344425005000b0a82d0000780c1c0c1d2544095690b0081104661f040300c081c42a1800f5050415036031150f01d52501c84000090303201c400d00c01740c0351102d100c000c00350b5285420320402000100384042c441c42980f044081c40300b0501c600e40b01200098103c00300590300c4102d0030015142c03416412005003a000000d038805041c21801c2d814000014080300b013000c1408200703006850943c11030041c5000101c550303c001c0310f92403690500f905a013a15401c01860310f004e407a02541800c20161090b120f40c0760006511000c04885c9240800410400c0d406c507200c0f9081c000004d840d80300c1845846c0c10190049100e5043c40003d00c14070303545c25946541120382ca154140100700100302144160f54050640d000035440004140c1110951418a005410585d9a50341d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 310826366 1250 310825116 310825139
    0x13060201090b16020f0a0309030308070c26040f080a0c06050f0306011b050105090f06060409081903060f0609031a090a0b07050c011119030c0c0b1f031202010f0b0a 72
    0x1000c0f8085100f00c10b40682400d00a011400c0720702e00030307660040c0460440c01c01400c050406032480041021440c24000403a103860b039000f01c04011010458540403820500c600305000760b4000303051140c00070314001402600094405040340c86201050310701e40c2d46440503201c80c000c403140032941c0744042002854962041c21f40030149448100c01e450404665200c00d42120ba00301d501c2c00303035179002074400c00c81000c040103020381c4404200c034203000d0010035554001050140c410751420903103a0314864142c541c006d03041311001d00171030741d640c3d890345948000040c20f070181e41c40203031044402c0107242c2c5903001e480c48400b403045c03003203800401640c40c25580700d082e9070000030f286038200903090210f200361140a010f10320502c1c000801c0c0033389403214a80217514030182e03141c1803400d051400a010301c2458014824a96164010401c82c400d555882c03201c801550b40c226112a8500c1c11560200810155040c00c1151880550007044034a61000450702111429410140e0220030710038200031036079032217 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 310827616 1250 310826366 310826401
    0x1050301050c030a0228020109030206150307090b0402070f0b0a061e061d0405180708030c0712060213090f152403020702030607080f09030301050f01051b0d0513060201090b 76
    0x34164000c61b03800054001d40f0901a280c2001e00603512140106c082c5941001503c1d00009c5080c0855a420746000c0040d40c1d96034584100222543c95160352165583c4607416540880d0f0058406014a8682d10700324401c078404803040010f1078034003032010031000c030440a0400000c4045134a07151160901c01c0c166030b00c0d003400442880e03c1d8055140c0003202d403202e0281601a00d45044000d5a03803544440f61410010317190085011548184006e562140000600381c007158585c4081c414102d4640c1403540c041e1040300c01480407c1201c1c1800180d030f41403640504512a0b4284003001802c10300d84289014102e144a9641c1ca03041e449032200b81f021580400c501000c0705c0b4180145403046650200b41405401c8641201180c8050100318080c51040d19103070380720282d40e01940c0b442d0b0400d03000640301c506a490740e038100400401c9460440c102561440e001c01540412181880c039151002451075000d021700c4030180318404400944c050050080000342d9502c07140c1d2008540e00e1520701071046160 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 310828866 1250 310827616 310827637
    0xa0f08060109120609170c070506030c0706051801090b150d05060106080a020412080c011503170a031d010b040c0302090121060e07030c020610031e0503041e050901050301050c030a02 80
    0x303400040780021b4481183e1182500040c0005445c1d000d400c100a0601e4032952209000351700410406c028500740c1c90868a81503030029001445445a40f1013000700b003070b20007811441c0d602e0244900144280902d030031307104080c096240c10320184003005100c503902d84d0100041099008200501c00030b805000296030042130102c005041c82c0c0d980d9042c3c01c0721651000140c0e44582c00196443c00c40e082801418420400082c0c601545481c43e03507422400500b80d0a0000303003000220b8168050b41c42500b213038405104d080598105846e1183c0f40c02c1c001d24075005401c1c4280d1400000040c15030290080c0c0309445016102e080c0b03445075400790452003181904d40c1d4003203151341d20f001041c0e80207900c0e0081d0040500d554002040480210040c0c54128090f0803181c0381c002c00b102c10000902d5002100480080160b604c0c10f680001c1e20713240d031031402503030440751114a483c10001c6031828802c540c0c00481c2c0c03040f01c580e0710a13640d0b44181030807508181d900031400c82041001400d00f100540052484041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 310830116 1250 310828866 310828871
    0xf0903090d0804030501060611121602090702010c23090906031002040308070b06150910031401061809060501090b0a021603030e041d06070309020301090209010b0a0f080601091206 79
    0x12040e81140700d046a40c604041401c0c0b0a1120034400c04020b401641004100d0800b00301e841c65980907c81d50303d110701100010003a1281802030b6aa01d1155405041072009003051500a800380010f041c181d03001815a102e45c00b062000c0b9a504804d4822000d2514035010180c41400f08051000f003100e80c140c8144d181224450340c852008100030b41c06404003e46480c07203450100600c4001500052007607561134a440c01100403601100c107407500c100c0341c44e0480d6466038026005440c0c03510419013051480e1000081403034010600d01240054107014070781c0c06446070100c00c2203444600030540002d12010b0244842c0c0d00b01802030512078a40d0040b100d420241c204004548540d5030022000100401c00e218144e04041c094089990940c1003d205202c01d0540c0b515620400240b148c8101030311220890b003035403000c1d0b2209616a070040c100003070315a158085603405500c8426000f00251132a2060b40101c6c0c45803070118040d200503580c10350968038014035a180a000c01c3d0003607650384c4d03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 310831366 1250 310830116 310830127
    0x120216060506090609070c02120f060106023307030f1b030c26060105070b091606030212040b1b04030803040308010609180f0209060c01060503010c0203120610110a06090204110405090f0903 83
    0x201e0412002c4510b00b5100010035a94dc14a0402428445036104c020004418840c81c03215191014920426a500420000c0304607960640e048000c1c1000b2500c025000b80b41042c0c415200311202101d803408201a14107121105206000b1541001d21881503403264188800403840000c407004070369082041403402c10304004507603c85084031070082d641c1d10040da100381400c0f00c680c000700c000b4500030000c40c20210f060401c800e80e08001c05500400003081e0342024800500104102280c5030795054205c1080354843d6120726203d50143c2c015281980814008400006c0b081e104001200a4a0030660800740c0171038008209009001c49894544085409000004894407110f010340320900c90034002003506840d0005150031030f0340b407126941c00c6420420081ea0602c6050038400c0d0460001d84911141503203505040f00d09a4610708604003601640d4242c41c240000e980180644c83d00850301000000006c401c060507511580c81226008100000082c541040b460000c079031001400c01a01d184c803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 310832616 1250 310831366 310831399
    0xb0901020f15060306101d07090f141203030103051906090f03080709060206010819050a020d030804050f01050610030209010207170703061a03120a120216060506090609070c02 77
    0x81c046540031080100050100300300743c42e0802040d600b0a1b51250244801410501c00c0c2506031442c1d40e04135100301c031480104050501c150780034402086441c80084105854942994151400300f003024030809540c40d0f0603140c2003010007124102da5001d001481101c541200482c0092800001a03804139a21200800410200d07100c0004a81c070035a9451400d10300240c0141010b4400d811003805c40d40100014001940e0004212802120028519070040040e15045140250018009400410300c42c00e94040640003a20103000e00c0c8601d007900c4d0702118552a85080314412501c09500090000701d050840d4001e44c0144030081c410310541e00d65640b40d030840d034100c80c0316003284440c550214100300207000a900c540f21840184212014169210400113039641c0714140322800801c200103074030400c83d401425510034440c50380c0410b5481300720070950210f0554a02c0c40655007a410705000528034074004010300c6c1f04030401800e40b02251101c500031140c000d0f00d1300301260840040e50180b0541c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 310833866 1250 310832616 310832623
    0x160302120a0605011107060f140d06060c031101090503091507060c051c061415040f12060b0402090a03150204030f0c06020d08100303050a0507060905010504060b010908070b0901020f 80
    0x30010740a02103406490300300014007180040445c0d02c12030b005032100380081ea5100e80d01151400080c5401c1144d00c1c10710210b01c1c0188200c07202c442c216485c203d0005000e5030800803003031619000e51903140701030203000c0c1074900340c8000e810001c0240e0001c100800e843e280c40c5c600212400fa1410700c090800400d9175501e803c0703c40101080f400f0400204201e070075424072800680301044020310034004180340000b0540f400311040302c1a07220781c204c1d030411140401844c06582c0144080c0d145082401c0e82c5007010241c203801e0f0708059501500308848034840781400c0c0201d4201003400b908140c1da00340345032503034820b2401c8220319840203602080000081141c80305860844c0e80150142840c46141c000081d00c0c10703451002c0fa4051041540800c007000c0d5031140c8000459070181416030303803840081c80031211071060210043c030807490300142d18188401540b0141c4514860300d002c0105101120054841c280c251183d100c090344500d206200d210b10100c0681201881070040310342c80140290040e09 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 310835116 1250 310833866 310833871
    0x1716210510180902220902100e040f020906030a0902060d0204091a03060f0c09040b0d05010c030e01020c030a0c020d0b160f03020304030e01080709180b091e16030212 73
    0x6441030441848100411400d40c42c00903002c0c00c00300440c00080e400f0503104c1000d240c140c814100c4200c05a203100c500358011940056004025a12440e82c01d10b01070b004148140445024034940340c07400000b8613080c4215881203000410882c2140e4a004460000d40000c040c1240c02079002c1c0198943c40300a80060400351004500106501000050000d06503012800e910b200e640280d05000403c21082501500301c0e0030f0a441c10381d2071507000003107000340c0000b181e21600b101003c8185001c0c0003042d4061003200c2115035040c0501c0d002c1200b81800d034000c1c1c0001061f541c001f0010320340810f0054500005403440501007007076828440e1140c3c0e40c2640121130f28101d14071049402c0303014a51144c080741100d800741c1011820360030301e0b0302c000302031a5039524114180400340c00892016030241d211913005050f00c80456005080600a0902501f1041071260060781c24801003a0791b4014200e07550741c41402240ca000d51590380b0040c84090b50408110002030603420042c1c9000f4402280801d407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 310836366 1250 310835116 310835131
    0x403170406150602071d0f1b0910030203061008090606100e03101d070b070f08070605040501150b0c03030c0f0d0c0e0a06030902090f180601030f0317162105 69
    0x10145400101d0852051545480c514111701c1b804104c0014200707501540c000b41310f0010740000311300d20000720b80a8800d0754000c0c0c0e44002c48900080d14141d140e00110f01c80c1000f41c0361043c11307541d0940c0076142c4907016140c90450b1340090300000d0703031418003503104042d0403101d161001035031a044000c2428060303400000c0c0751442e100c0c2c40c600c84130200c105805c048210004000e2030320504c1c01090030200c2c000c02c9001003c42d8100c0b82e9100900420750160b48030303a40c001e1030030003044c10189009030081001103004e00a20741714075070020350000024141c90300c225100f03016615540d5101034200ba02c1c2d010351000c4000c1c800034080030403c4442c0f441420524101c3d6211480050500d40402c070030000c0a038080c0080506040c00000140c541c03596040c8c000310302c50444403042d210300d0540c00800107500f02003007a500c2100000005e200e9609624907a0038001c2d01c80074080c0c2c0c0150035041100c0307401c6948a4a00051480c11281903120780c400e00000c960306c91422030180e40042d814004d841040e1140d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 310837616 1250 310836366 310836373
    0x60112110703021509060112080702060a120b0303090d0b130503070b0a0b0904110904080418061a0703090608090a0206030f1006020d0f1b05010e060403020d080403170406150602 78
    0x5008054041003c030012041050f130b110716a150030001141d03940e105004e101c40d1040103980071820030444a00b034402e5140e00400c05030b116400900010030810f5004040d290440c1080072140803810b0210454403c450042c1080d01e8039030281d00da84820f020054640750315103103581d10403800f203a02400540b80701c6115882020340b90402920394425207107401c400b5882400303101c0502c4002a51114a6040305c0d0003030321001050358881c144804507000741d60108a071145512552181900c65901410603100d4a40042e05103001000d000d4459000b035182c01404a040b100c4180100d50140c08299403001c03180b0100c4070856050790115401c0d40054508072840d903910418050800103c05410000c0d10b0b540c4001c1100d0220791100a140505145103401400300345041d0009a4611a4803051800d400c01d0080c49810b1980720b1241e62428211030540c014010b4907a50b4031a580719014443c001c6030503654140c11b0206400b510183c401029008a58991356240c00000d403525100d1001c0042038181c028 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 310838866 1250 310837616 310837627
    0x181e030c01080c0721030e0c011e03060b0d0207032a1e17090f0f130b0301090203070602031e0301180c0201090c030b01170604052d0312040201030605040902030a02040506011211 78
    0x24042c0c3d405182503807220b41000d08c00f0340240c2da00c440000c284034000200301511034030f80f050540003045560008a044400050840c2c60130f80c40ea001409100c2c403a0b519810940c10340103400c80401d40c2c40b80b03056240025000c01c84007143c5106208907400701181c10210b010a5682d85002e41740c0d10342c1c0c41c03159a800300030504184074904001824464607040d10036210b025407240002c0c000034114403420100d43e59503400e451550301e0941c0b0405c1079039400750071510259280d10740a96a5001080e00030414940c030f8075841b00d820090f9041d00c2c100c03005001c0945c01400c448000001502a60014004540d80c03008101c010840d00a032280c019400342c95801115410100d2103602406060102c0b482c99200074244400684001504520202c810685035105c1c0045101d10145100c4034a106100e48000300d08025101e0042c40d44501607407007601c1c2000340c103507560244011741e54448030203507140d0004a50b860150800d5084158000d5051411440501c8280340000468422000203071704402e000c03c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 310840116 1250 310838866 310838933
    0x12030f1b101a090a05040b040201050310080303010f0915030c03170f030412271502121b060a141609080a061d06010509012108181e030c01080c07 64
    0x1082d50401d03084c103c10300052405d501c0f140c42c0c032640940000c0c10450000001800ca100e96400d0704050520356041c0c0350380f941e4442020f50125060301417074270014580340d02d030158644040c010380110b80c1d0280d1002c200c580b441e05c03407800003465480b1101e21284100002920110514010f6101d01d1291406000a40e04103100a001c0641e2104401e251120400c02055908101242001f140e45044420007403401030b020433403d100720914200095031021642060720701c0e403e01214032208070b05086a40660f14850010296290a540071030a4400c80c0c2c08509010300c05841800040c0181c00c110b4059039807855081d00e040c0342d011040e00c0b0940d27110038503405085680c9941c10603048000c020030a035410f10380004e00307111061044441400315000c00c115411255180c9400264004414a440b01101d000b81e0740c1854544181510440754481403440704c001404045c48000d1001d40104070b000f03900c03401510065005446c44034070364420b02c071400018501d103464003070310302800010300b80c0c02c0c2030040d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 310841366 1250 310840116 310840129
    0x17030a1a040216060b120f0708010b01020304120b071e03090605010b030c1902011506030b01020f060108030307030c020c090a240303020a020607080d150512030f1b101a 74
    0xc094422401040307a50031240251811506194000d1400507850f0b000c02c00007951001442061072843c012180310010104020400c40102c0740799000900c0b05610140c012a00d9100b94014a007100e0000c490b4840801c0411100c1541700c030040c203020700c090780642c03c0d0141021204540300006034403261184108515806014010031042070b0042c11802c0440880c101d80c00b840c20b105411010109031300817010700c00d41014a0762242040211082c40c1c85540003009000c4020580c0e015100e0303084256075565001442c1412030300c0500143d420b40d1583c83e0110050010f5214a60451240c0801610705603138200e0340c58000e803851000011040d400f0111409900d20704040107007000b02c54081007010a0b000b00b07845070403960444aa039036600d04d0b4070301052a40119060210310929100c40c8441407410342d25500c00f503400450b65400d01040390102c065403481001e54114103102d0900c02d21205902c640c0100072000403010540d86280048503e5808032000c174281c0c0504038070801c544075064100030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 310842616 1250 310841366 310841411
    0x32b093002061302040b061b070f0608090703110607020312030f010b07080a080a0905240606090307030b091c02010204050f09010b0a0c02030c100c020301050601110607050717030a 79
    0x5001902062401c40c4083e20740302c072039035406030181c0d07181d40d03105002d40d41e21001c50f110328180481c880040c0700440302040da204d40c6070040405908d14404081442170241019602c41c4280700024510141556159140401c9000c46c06401c24410700640c0d005035018082640d64600100d4815103d261950080303201c1c84041e03012070b0b0031a104110302d4020456600c2118402d120605111a20b038445610500080113080c001400b030b8042c0d002031031801d111a42c0250b40036802d4004000540e00d0719400c0240600c140c40d0f0441d45035126110800c009601c83c2d5156601001c50000e9880006411203030f00c0710658000103c000507580010107004501e0030300c1483c090940141c50002c410342c1000c111070258801c50798060180400241c45008541e810400049440c0000c0c3c580180038694100103040c0003d5070504900c25401c1c80002b43d015407040009510321140c2d40c004064940b9000c5054816600060090715102502e103158084003040d18001c50140c1d104000000714075401d90030350801c60440 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 310843866 1250 310842616 310842713
    0x10501051207050f070807110a0906080d030b190e0108070e0f0601120603060e150a020705030a0f020f0a0f03030c0215011a0702090a021308032b09 65
    0x501c120080360051596540c1e20196a062099440b114000016814003c41c04020710382440098140c0c01c0100d40f1480034144c1d20191a550340c40c5484405401c107070b9001d4000d10031a0f81c0981890700003070744203411a048a541c0a410308010000182c00400c24030300030f82210408441150041100c2c04c0700304207040c0200014580f800f034500300348203240e078140405000c090400c40e118000f929038030025440b24006550001e8104030400c1c654441540301c03030321010b032703085241c000306d00151341c02c041030003119010355014010b1071402000040540c2c1110b11060344100710300c103802d545490100300b080900c100c24025800e5485c920b030b00b0300e801800d40740440070300710031504101e2118155650051500703040d15000c0d80c040080d03e41c001000c074114002d40d040a0b50010303000b014480340c07041c1d5078020f22091164600110900d030301d0340180f6949200d1000a80d01079200b500034500d00c02e81805204400340324401d004540007100c3e854800201d0103500b0b00c59140a07800510b00352200d92044a1081c80d0342 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 310845116 1250 310843866 310843877
    0xb101d060105070b07051303030801230f01081b0f0403060c020c010c080d11191803030c0611071a1501090b0417031614060f150d02040221060405010501 67
    0x4041000818034000c080c00201540b441030003081885003d8000c7e222030100b01041d44000650301c0c14003c0a45000313100d948a002070126001840c003410b0b403138400c000c0801406080c1c144110800444043c03600800d00e407090090b182d400503650741204002d012050100c51410b4945045060034012203091841000955001d034030b4070030640e40c001c2d01883c025904680c8423920f5410030a8180040c0c20860161406040c0020308100d0404203400300018500d025a500c0c0301d440c5142c83d4003e841519400040e01140f003c014410000e45503030400c0c000354514440660030901250745258100030951038164a690740041001120070114080c965a043c2c01d01c0c01c10203a81c0f800d100341820b44960b0049004041c018554143d18500400407600d40d100c40000c603040401050820700741d00c480401d1140301d00e0040070041002d150741c00382564059540c0c2c90388100c1c0204140100180701400c00e04c100d03005030302849a103084c820081c2226407000103402403040c145c505101004107c5105030012410b011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 310846366 1250 310845116 310845121
    0x60e010306140f09041502041d0f010b12090a0c14120313050402070267050109080d1d07080303160c0b010303050c0d0e130c0504030b101d 61
    0x141c80c031503c0700340d00b8003d80b40410305840d6030800d08070140b80d2034050321b007072800003c000600f00c01306030342d2603504004254008500d03120b4031a40d01d1200803c0c4941035200c1c3c800d0010380c40b482c002c07003070094000085800722107003d406641c030180003a20303640c4444000026001d0090b400d050206401c01c00901100107941b600103a1190159100d0090058038092940841c10b8811034481002501d0640142040b9005413190340c41d0805c42c1c40000305456104c0e541d2100b120b03c13808104001000703490303845810704845903408440d04080c40318640301a0b030745640b14901003012800e00c400410740150307103c0011410809010380d4904144401200c005240d00046007044048000b105981d008501884c0800b10101500d0342111250302a44e0081c20b4461840000010950814014101b0214001c02d0f10001c160b001c5c1d0a4400450442050750020520592181d456101e50f000d0200442e03103060260506071a03481d20548500c0454504042000c0c01009100c0340c00c08095040628500003211400e61 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 310847616 1250 310846366 310846369
    0x301290f010210020f1605030405011407050c060d090c060e2704020402070f080d0203240a170f01090809011103040303050405060a0909452a060e01030614 68
    0x440708007003c00c1c000c681c0454101124040c480440b1041c408a24414070300e021117050898413a40a807141d140419800c44500b04038160722015181d0b040e801101520200401105101e0b80d944540389982c500d5580340d1410300001c0c1c40754043c030043c005607964024900d00030b04c10310507182c08503224100504408025070a004200d8503900307510a80c141d40c05a1129098607201180c82040440144810744c0030503a045007030401d5010703502c0be42c03050f641c0c4880e014002c4540d0001d00f034481c000c96045a0a8030041c803052800007030b640f0b1500b008130304450801c00b14103942030031190070345001c82d0b4010000030700c50020341c1d0200c0142d01120f000b102440c030306407031598050080c0c031480c440c80c0e010350000f2644102d5070f4003c00c1d9600092241d24002d00000e200585070b841340425a01c01c4854035400c504034184030035469010018400b4000d0280d01071040961074410500c017002c51013002c4846207640800340700b1903d09100c00244142c2d120907860521544c0050266440c54224420110300c0e0140314145 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 310848866 1250 310847616 310847623
    0x3140907080d02210901020c03060a0b01030609020f0d05181e2118040f11090307060e01140c0c0d14061609060c05070f17070909050d080709050301290f0102 69
    0x6a00c4840c4d0850341d281c640c200141e08003200501c846606002c0c0f075080204001c03040d000601042000d83c0d0030020703c0d84a04c0700030100c0c003401c40d814420380300502c010355560039554000c44d00301c03494000000c9c26013226004245801ca180b6014146650300c40e8500718030102c2044201c0b81c1c1000c0d842e40b02c809048490118549000340000d07682c810591000030314a0391038940c0100d641d030340082d005005100030700a5500555004543d0300c0c3c0070f842185000940030b8030803072480f0f02c410016510603400c81e01d11840e0311415080f8015482c294060029444065900d41d01c1c4122444d20031041c4601c601440e80d03840d030a10900402f15100e48154101c40030f0348552242e0103400f03469850428034040000d034205249041c0054001d40c000303000d04c01c00800c0840310204007840c2c0c404490215401c103501c078900300b020707138809900040c007981c09403d48840c0107001b010360944c00013092409004c1c2a580300002030035200000145000d0f180c10030f129a00342c1030602030800300080705407078681220b064400002e65 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 310850116 1250 310848866 310848913
    0x30303190b06090f0616120f020c0a0e1f0b03070822020306040f031b08040f060306030b0c0f0705060c0414030c030a1721010602010c18060e0103140907080d02 70
    0xc1010002854100703030700489101c03000e15400030b0f80c06019a8411304e008d44006d002181c8000544680e40c403c00140c908422414213440c4440503543c91070f100d000c031061501c0803a1141c0343d0a01c5d0000808616001800051031184441e5903aa00a0b0300740000545c80f1070f892540c10036502d20711010705001507103000800641055001c0d4900d091002d07075081c11512844c1d0603056064000c0c049840d030060001d104042c00680d00040e40c084c0146e5030303669040c3c08940f514880208441070000000f001115040c000c2c0c4401560180418a04115581d8140c1411011140d40000107008a4140924021900303150341881c010b80c010482c007803074140040e07902e42070800d00a0840d002c850f004200c4500280035201c50007000c100742e841c0100d41c0303210354618039824000c0303074010344c41d0880009000b8426444404c00004070072880180a0401c08221034100e002506d490526407281c554004282d04401d80620030804032014021150031f01652a090004d5240364004540c0078102041c030f50040c08000f40c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 310851366 1250 310850116 310850119
    0x907020703020609010908011404060e070609030f06020405180a110a02030d0506040e330c0a0c060b06070602071115040504150801020a020706020d020106032f030303190b06090f 78
    0x6880361213000c012a0340403519004104a94200031890507820301102c0d100b07005900c502d00c10701c4442c0040007034554441240c0f2804000481d4540e0801c0801e40b445542c4007030714041c04000d07150075180e00110750900c075482c280c00480b482c103a0410900e10007610604a400f122a02070501d00344115200035620b01070345103460440390f52003010071f08a80e16a44440bc5000046042d22849169030321000708081406800e840402c080460200807540002c1d030141c03040283c081050f05149094008903101095034008681480c0c0d41c801180081d51880082c0011034450500940d807801245030003024082400c2403140101c864a4501c1242c221034425902922411703140080d506052140c0c0d0f28150700141c0c82801d0b01e500c0010991021540845c2840c203560858085a2001d030482c0304c02c0b0700726241403001510040380c0751042c101c031b64040364201903c02580d0509601701d103801000a42107030700560340408142082c50994089091390301810040080c21a54541483c3c003540c08950b401d29628101d5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 310852616 1250 310851366 310851379
    0xa0906022b11100f0c09090506030a03050a031104260a08041224050603060124030f020d1109031e15130503070b0f0901020703120b0102100908030a0605090702070302 73
    0x142003581e02004035004481581c0c40078080d80722002403103001480d606040c170300060400000402c0701841c41c06540d01410002d4014504804140c60450310b5401400c1d4000415840f10300b901c044c0e481800190024094070300a55011941c0034040680d4507070240d00f41842a04207100c0f07900401c040e2001c0d01c00f1030340c40a803510030645043c5003d1300c980d04251091803c40b500c04c04c3c10b200705001d95000034401d1074180c0c2190010b0b600c1b408030707110100074071801b89180e0685110079070303015109420810507030003550000740c03e03c030001c0004170950b180f42c0340f11100c240007c9403200785854100082841041101508a484a1105d00c441e84070382c0c523500c1d03034000740049c01c0210f40900240c4030170f403c0182c2c10106a9407201d060f840d003030440c2c00069880d28014031207030000c100e0080042c401c0340c11955042d02d030100030442159805018100100c0e06906500a10361046034014445c00307810151440b480a10b607a070f00c1c11502040480f141c075080713240910b034a1010007a6150b00001c9200541c1d40481c0d05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 310853866 1250 310852616 310852637
    0x8060109050919020f0d0b0a021914090409170a0f1e09121e0b040506010509090a020f06130305011e11040605070c090c02030307020c1c0f0501020706020a0906022b 72
    0x308200b006c1400c07000341005006c0d010400201d03a980c1c09015501c812079590341c15240a80c400300c800000035810038080358030402500032146065400f01c000350f440b5141c4074001804400c9092056040400f60710017042441c03204821499000a00c0000340c182d240c1120f02050004d4030003020f50682c0d0141802980a001444081c01040c101814034034448200f0070490301d965140400b03100b1000d480403201031080c5400802c0324940000c40911444055000b03240f01507464082182d07500d01d03803151580194013040b400f425405078585100c05540658000320300318038500f900b0030a00300c2110b021880203180460400207200410112000c0742c5140c5841a151185801c041d0100b00c1280d208014180c034001d0100b1005070040040d42c814982c030740a8400140c520b80c2402940d0002c0e0040a4180d02000f1140c80050603882e0b446203a1400b0b0000141081c015a440108a03030002840c4004130b415088200400d550411031181b03c2c0c6040c40856815100d0b11550f02e000201090040f000d0100c01c801 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 310855116 1250 310853866 310853869
    0xa06060c060510051c030f03021c020304020a08011109120706090b0c0705060a0804020f0d02060d0f0f06060c051006080606010e04090b010608010519080d030c0c05060108060109050919020f 83
    0x4848040c01c130080403d03500f500c01c881e210a8080780380b1003c401007142c1d96060501c16000c1e10035034400c0a002466120b18520041106000390300041c4201d0340242c80d00c2000c60440d801b441480907840d225544030f41c4d03d103d1101005400c0901c840c25104640c03280200703004566101c0080350031144071120a5444000c03107084d560410300c1d50b4210742e80220740890078070ba459074403101082c01070f40241c61900c031841d035200500070740010209019420540c00c000ca461040b136194000440c2c80b00380d14001410035028107510f0b00384c8481c1e60140002600340c4000e0400d020090005025100c10000304018082c0f40104041d00c03100010001410f10801c42d01c51003942d1520707002040810784c00400c5000a6171030721400f800b048406e000d40ea010b0710110302080142010540c070001901c4070300c2c0052407948290300c000c80c0588000b81c80c8104101e100c82e280000100d0410659000c1c2004101034000d540c140341100e001c0f07480081c201041035110399000c0003076007100c14000304140d4068403c8002d07200c0000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 310856366 1250 310855116 310855141
    0xc100c05060c030a05070e0f060a030f0e15091f0c0903230606040b0a09021b030f0705010b0901060c030e190f05031903080a09060b0402040e06090a06060c0605 70
    0x100103051801100100199002c118009520444242c50100010b031501300080f16a01184c12001360480e000701c0c42542c2a180000183c0008142c038900810394400340018101501d0018580c01c07010381c05080c03103481c0384a0305481181d01803a01801402d0724100300f0780000c04042418010051701b5690040d44401c1440358103640080d6401001c001e20842c000c240300c000300b5805041d4610030b03020303890100d070707040c40c01d4002c024007080d00900c4440c03690300384140e080007503001d102d81c055001c0c11101841e1356001d05002921200c101c5041e01030b2a40d829051550950301038208041c072410000005020b80d40e000441c494031f030303074062800421200d01d8401007040003559003c007900c04460402c0c0011101c0c0944001025144158181c071030007880742c0394004011007440c800801007012940080d544860551100403058040ea00c00302d4910800030100b400c90f4844d030800b488102c41c010400219003004015160440d0040c801080103502d030100081004140701d8000b401c207515040401c94001100c3c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 310857616 1250 310856366 310856387
    0x1e070204050f0a050702060c04030b06270405070905060d11040b120a02120106060203040515070c030b01091404031209030e300c01020a03032a18050904050c10 70
    0x50010000341c2440ba00001c0c04a00489440010604060014100ca0310203e04c40e80114188030095041a05540d600c1c00e45250040c4240c5d00700302424846500012408112540001c0d620654440340c01d04c1d084c01b0f4204052600300030382050518080c0003081e03d070341400407203041d041642c00c9606641d1b0310025000e0700020f60620752088103141410f050110119000700c80500c2103075401034000c51001b089098031151b1240b075001d0b800c02e21042000341004148444140e2540004618020303183d81d03544218119504140d071007101000040c0301c3d11034244034410400024130309200143c40d081c1e038020300029660b410408900d031a0b04601040600070128540c01880c0108182c0d80100301000c1070400d4032903c80107440c6031008170190400b19001040c60340400c041a400344c40404000d0720260098100395079014904e01200c9c100081824a02c840d5036076403840c690b10001d6010441120640580340ca411191154240c00c043c0300010350002600b9441000c191805401d115100c1420b03650610350303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 310858866 1250 310857616 310857619
    0x1514030d081323010e06040b1501050712020c0f0d0b01031b091107030201110c06070819050a090606092c0f0709020a1d0d060e0727140402061e0702 65
    0x1905150381c90f420b100d070841ea0000d0031810082120240784945203940745015134014040c1c0044502180110f680600700b40b04060701810b03c0c030707c4c01d00e243c1d07144204010380d03034a59401a041904284101c0c03505100302a81c12000700c4501010321041d07141d2051060041c840180926041800c0307555050280c1604d03c024181c00c0000c1044a9220f00c441c8032603032240c50200d00551034160415003503640202900e8440640d04000c120558540720140c4507654042e00c010968007000140d4404c0e10000d001e082e00c42d03440600085000d041d1850402c0c25140141c104808084c00d041c1d4100034410054140b50100141000c20800e8030641d031402c0742088a45a0031050038018003101083c1c1a43d2500206800e006654648680d01d03190541c2c0d07100560309001c12507200e1010f112040c0420700075001289121031103002d031502e096541c8041c00302a00381e000c0032450034001880742c10491945100314001250f280c580d41185107020750016465210321b2070524000e03140700804541030b88100d420749100310360 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 310860116 1250 310858866 310858883
    0xc0201150602031801050c100903050f2809080d050702061204081206040204064b0207090e12180603040b06040e070b16021804061514030d0813 63
    0x1141d540003900c0c0d07400a64400c02400c5441c2800e0036551290086680d03600115010304417400c0075051882c06403408070801e4007040000e0110791101288a40181110340f00a0704507440c61401030a012201c10500708990140081818100107106000c00d40702c240310b66500d4200d03540c41c1d880c130000b04035000740121b203114a0380ea54100800c201c2c20000820300800d1121002180307039204000c00043c0d2085018000000394640c81c2c00003491103001d00d00385100e60306400500d5402e80c21000c00f03500c0e2407201814a0820320102c001100980502c9013501900d0740030307414048800128145540c0d0290703e510007048550018101141c0750000c2a5000741c0701e0018059a500e01340740c140400d03003180544003148640d103004042c1c4100f18000800b5000c8900c0f0002203428064505c5c1040302c0501429020783c2c00c80c00032000507201c10594042140700351710032840021503ca40704000c14207150309410003000c10711822640354255070005000040d045031440c1825095072002c00c0e001e194014150010605030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 310861366 1250 310860116 310860119
    0x5060108010e100b010e0906060702030604030305070f02061e060118080a0c0b0304030e0f0a050405010305010509071e09020d11131404060605120a1112010311090105130c020115 78
    0x25010b4212102054842d400c40f841c1c483c4200d242003c0b1511034140c2804100c0290701c840103400c00d203141c41d62200f40140201c1c10204590003003030810303500312070450019940300100462217812016003540d0000b07901c0104914a00a101440e83e64103001c807221500c0ca2100000d4202c0c1c1c0b04010480f0981103e83c61007002d16500d07818039688810101003242d02030040440440c210f0035940c1960b02c650b405a0710101c0440ba041c0c240900154458085c80d048518150003103a15155805202e00843c890000001c9034501181d8650605d03240342c10a0034100510307031100c4005030320082203d0681c3d4400000503912004102c00c200200710b059000e0002d081d020420703201c0050040e20030b40032500041d1107080100b0941c1c0c100700807101c070340c0602070100d00248400c00c000c0e03c200300c445a101c0c003100c00c0001c41e44100c6903400da00d6042032070050310100a84006100f0001404929501e180044d2002d2400b0f50501000821001c00602440117255031200703d103030014800d40042c00034404034014044101e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 310862616 1250 310861366 310861379
    0x5190609030e060a0f030906150305031806091e0102010b0406030b1608070207060c0503070f0825020904020409022b060b1e100c06050f043f050403050601 68
    0x40000c00c409401203854040c100d80b041c02c00b00112282d11a1542e0b0b010800d011446003a0300030494241d0a80d4480d40d20a816800c0d014204200005540102e00075a203484420800d010310301c846d2100180900350500c000e8072a620707405020194a07a904102024141c40440108d0052000803e1264042e003401000003d020148482a008810810007420b030001c1c4454281c440f10003d868400050344554000c01c5001e00c80e501e042000c0348504280c3e480d040061312a003c0c1c0c21a002820342e210800060a0b4420400b61903541c00ca4214503171000c8821348660300015800100200083d005903102d800400840da5500c024007036500c1000301c2880d003030045822801d1041d008500c00c9410354944407804215103001c1c100c0c1d900c1c0b0403850100d100e82443c039400384181e0b0b000449840c03060048400d0b00f5000103a003401031921850b500c10348603029103418200030020700403444164074076a0403469141644160040502c1941c49035000318a4604e5100303000300e070f1602c550751001e0310382d00482002283d034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 310863866 1250 310862616 310862621
    0x70213090b0a0605031c020a0501060b030106020f060705031305150405010c02010c02010b30010204090b01030f0209210705180403020705010f08010e060103062102040507180504020304051906 84
    0x41e01480381c1c000c0a070b0350106184110780c070600403594183d00079030915407011908000d01415031018415105680d0003aa116800d440c06504411032919000c4010300c40140c3c100121031099580c3c000501c030301e04002101410328030000c0c02211003280c0c0781180c001400b40c1000340742036119920380c1600c03103440e080c02d01074000e00a050402c8015401c05641c2c550191050145070143c000041c488441e011000d0564910144c43d02e0790701881a01241e02c100c0e0f811020f102420050101c54004201907070560001000c0f199891801c00c0100e00c14003051040c0d442e2078040502080020030f540c10383c80d00078260705180c1321007580200d80c40b0002c0d20040c82e0406908504034003543c803e40072600465101c000550f6021090600700c1d0018607200010080100e804002681148060500180381505d61600380070f0700d46070345c0e20f1040d87c04a0071410011805d02d0300c10160304c101949484009a0b440d602c3c041d5606049201c1d0038172841d000300c00300c0e00380030381400401d41c41d01c0b58241c100c1c0e02c8249032410001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 310865116 1250 310863866 310863881
    0x402160501050f0a06030503190903020904050313060f0807030902060d150503010c0f0c030503070311030c07110f0a0b030a060b070b100605030c09093d050409120c08070213 76
    0x710350010221340e2400b9a4000c1d84152070b400f90145080c021210101150742030a00c01c650208a000400000562140d2140601540c056800b4666a2429040c01c8561540c15480301041000300050000144e50002c10346400112515010400c1000350000546a010390604452440d103824142d1000c00741c0798559108a032000c3d00240002c01c0582003c1c0c0703204141280e00004203104062000000c0e22070f1000f1a80061035080010780f4807149107000c603c64000301c0b0b400c00140c0002034160180420360806107042c140454428145141580120f04000c0c03162040d4280c0440100108207104800d42104000d0400311501325256800c909001c280e0701003d561004160580510108070b9070b104d103084034403071a4804885c0703280c0802c03142480440a40140060005803003002481d0300060ba0f0511400007010b4111032030040c14070b0345d01400440390190700141c41640350901c0b51000401500c0004083c032554100521a40c030300c2d0404081c50300c43c0040083d8030040c0001d9540b403001d4554013005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 310866366 1250 310865116 310865131
    0x13061505070302011107050a03141303060504020f0d111e12070e0a05010f030803040203031902011a010206040b0f06031f0204030b070302070c05090604020d1505190320040216050105 80
    0x441560581440111b200b00700010301150000689200480d0181000010602e02c500c4040d1502040c02c2c40d4200088060300100c40b07158860041c80194544101341c2104200c08880c05036038450503665034620171040e030100780e02509803128040c0080e9040116501072901c003400c1101d0100c0d4402070300c0e0720b582c4a4092040e000b03045e50302041ca2902e052060134180e6081440310300c4440e056071501c1c2e50940000380103e0b0305120800540226250501000c0f81d22800d0303400205d06119601d11100d83c191040c04024115404501000045a80c00c2c13aa190405140c03a80c1990303680b288000701e4206000d564090f000004003210302c0144a40c5580104116030040c1e03500c1b5100e44814904600b40d1140c448003902c6030850500038840d40c5080c003201a00400020300052500300d000c10b200301524070350701e03070108d916000000411180c00d0050b01419481002100b849540d0b003165180003251002da6420074405410704400d540340c0d280c81e03048940b10440d007aa5500313034844038a4854060501200e169 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 310867616 1250 310866366 310866371
    0xd0f03050907031704030b160824030a0b100503010209010206150103110a08070807050f0a0f09170303060307120206030f070513170c06130905130c060914010513051306150507030201 80
    0x612320324040e11214440d1002d65454140f16140e180e15044841e2444401d10200407000c6030b41c14860f41c017041407001192040d0042c3c85c00d80742020282582480685c0840c0c003030703401003003826910b13a800b094259100241000e000303940c50081e40120000e00103c01180d2402c840090010210354000b0a080d104003241d42d100e0002d69900401120359000d11208056819028003020a1541c000c100c420a003c0c135500d04071036200c1d55a20b660700850781c410818001508000300f0310101c1d003414400c01c0c01500c2d1003490016141003da010543c44d102c0108444d041a404034085203d1620503011280d01e003146a0402d000c440e2a8042c3c1e40350a01001381c0c01c4014421100c255509041c004240e03107500008502030302c551441c2c102050013504c0003c0c03010f4440300842e244070001400c0321010348080c0400d961102142410700303141150255815100d14184003050000b20200f05490740120181c13601922906001e84821070075402401c078580001e02001c4050b40d040e0b9400342d018010340003141c003c0e4000d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 310868866 1250 310867616 310867621
    0x3080d0506010c08040303080910050a090218010b090d0c05041125020a0b0d200c100b0f100216080d0917100b060403050d030203180d0f03050907031704030b 69
    0x1516520340f01c070001440700d24184000c001082c0503401050f40705040c0000c2c1d50804000c080707100d04403501110030038581503882c20f500c001d500349a40549646800c4240084255042960f840000d0041d05140d620955842891004000a200c02d40004080141040c05801c084282c2081c0ca50403400400c0d41450b6140014a039820600a907103480903006440b10b0301040c105140c00d03280742d2019280e6160640c6441c410368854a00c0360a003110006c03400c01041d15a440076107440e0404546000c41c510803030030a40c0c440e5072980e800001021020f4102c0341c0031000c0c10305080603800c15015818100f4407040114000616107008168800f44404131380e1101004e6440b2480004180101c0041c0003d580c0404441c2031f44c18415404000141d00082c842e07404c01b0b03602d6440340d282000c040c18881c0003036004014841c54140d1000400c2102d4546000346c510140484001000c1021501a08042544035000300d50300707a409001080256410044c0d07450070800d82c259403203c5c1d90081c0310450308003948000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 310870116 1250 310868866 310868869
    0xf0a031a0607021008091519050c040b090907090e18010606110a021512010b090103110a0c02010c06020405030102070602071b081e1006090b01030e061b0310030c03080d0506 76
    0x8031010b40741d009080700320000b00c0c25412075500d0001843d0601500c241d0740030340d808041010ba07503446100107050721503908203130300e0f511001e550020340a0048200184424008000307050b0558149241c2075400b55451342e0b0f009c00032035140d08681c1c4810000e020620500c07082c040150903000103003c00c8402801503a40d142c401301c4007000c10030384290301e44e004400760300010315040b254110306400d00e180c0d20342800e080302d10315050180700381c0c003416a8800006081d011540c040c0140351a0781d041c1091641841c0c0d803040d0140400f040e60100034108030054504100300251035043c0c130098003000e0000c5440e01c0349403510310000d6208210a5410b41c0103060014010a1100c1801c02078030500c201400000600c2071090480c6049000c42d000103008402c000c4614410a1003139070010010800c021908040c15400901107a60082c0030720780c260400820884010558600c26204806c0070741d905503a41d942c40811901500180c0000b400300045200010510039044d01912079008a60420080c0c0d845420 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 310871366 1250 310870116 310870129
    0x302160f170306130f0f1d2b030203182a060c0304060f0309022e02120301050f03070509040602030f0903040f2304060303021f0203010e0a0903050f0a031a 68
    0xc039025403002d9001d51003c81c1304c183c0e4114141c5160074410100304c090304104403805a81d1703000468070098a2440c40101101c03c00c101e0001030000c24020940c917140d18250440c82980c25034000c1c1c081c9a000030118800c1448000c100803417400c00030079108001282600c0310101c0210120101d900f0007c902d90f40d00901d000d1044a0001d02d0800c01149001d141110983d160100c0390004010f1546d42d424910258841600056002500321130080248243c81c26080302040380412140466200e040e0008140300c0000459043d0390045031080c8101c40040700213440c01c08190407041d041030806040c48100703e040c2e00074600a0f02c4018240901e90f59030035080c2e41c3c0e07000c1c03803050900f00c5c11004010040e440c60070700343c20b08002c0b245103900d020007225008102505c095900880050b4070188009547c041d00580104106899000540c5194075181041c2c01184019042c01c9405580712080000c16018004407a400070303280308180e80766030324050050014100c0c600c080c002d42e8210b1007066428036002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 310872616 1250 310871366 310871371
    0xa050601062c0108060d0b040501090308220b060a08120c24060f040605030d091503090309170a170408160518060a08010e010207140105040302060103120302160f1703 73
    0x40c00c424490708461030044071151340250419401541c410210704c08912085441803103a4055030010440b1241803400070002c4900401081d00052843c0c98110f20318220b0b00d201c0304080d0026000f60302600e84100003140f503050b50307003d02001d2185150b10245e5440702805855850030f6503040d1355451000110703020504508544801d00b03a82850001081031501441d0340003504000760001031240e440c0c10120b0324240e0400200c40c08640014410061900050841c80e0307042410324061101035155a000782400099000c0c81d8200645600b4a00d6003400401c1101c2d00d680c4c100c0d0000ca1485000310028641d6071003070090310140c0c013030481c50200c03a81a0342d13841c01c11102c0141124003c032060714100300c46c1d404050001603000ac1e06190000c0e102c0c82c01d0080800c80c1c0703452000180e44a900e032500c00480000b48080e080c442e41010104004a60041100d0341100e800c810343c80d40301c0040da00110024414085250416000342d40c014007440061100c40c0d254a205100088140300e070440319000c1c90208 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 310873866 1250 310872616 310872677
    0x3031303260a050c010204150c0203010f0e0a03030b0d020d030c03020c040203012607152d0e011b061d010e010b0f0112020d09030503040b0c0c0a020405180a05060106 73
    0x1004007050b040d10441c0100355a006810005062036100c1c9244203100302c002c0080c500141e8a110340f4400c2d49406c2c0f050070400d0380d0742201040855180c1700c4454490300801401b138241903840200c0303a480e4542c41c03182c1081540c0141940c20003003640c1340281c0224100f85068005219080080c2058100b52007128141c500302010700781045882070f0541c01c0c2085445241805010708807001a4148c0c4d4441188000b96003611000c8010010042c03292410840c0801c40000c01c40030342c1b4103003550740c0041d50425145030a103040c1d46a1410140141e031607041202b07004040c1d501e0708240a450b03480714500342144401082c000d000f540c082001103403d89032060310080c0d000c1c1e007141c1d07440c0281d0b000e02000480440c3ca43d2025040c0380020342d82400302c40c0700e404264042000007003040104500481071030b0b4040000081c85003040c04816100e40c0c2c640207260700a020f503940e0000301d08803403240c40d000850480358a0441e11101494078005031901e5081c81004040382c4c40f0800c22904c03004661950510410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 310875116 1250 310873866 310873943
    0x206010e04020901210f060515060f0a05160c0305030d05090c0f0108070c080c06060109050303070507120c17010f1a1305070516080901090f14040e01020903031303 72
    0x2c050070001c0042c481c041030b100800c1780d8040980043d4500d00440300c46400b444c4c001400340703403011600084042100b16244280030801a0f4600e510f84003054030820140c9282650321100c4a4400b072442680c0070902800501c414040002008000802004036002602e4140b00d10f480c1c1d540c9042d92034811115443c0c1c4503550300c9440c540f0354400c451150788400540340160b500354480d25030488503400b8800b0011a03810100c01c000180d60000891700c01004243c3c0154074100035078942940350b2480c1d008068289480000b10300502c141264604041c0800c0c8030049441d14010020314000c0c12140c00d43d0840794101031000884e1003600c000141000e1020340700e45000c0c50380f0a1041c0040030004d151009100b02400340345503100514101458241c0304102d00c03070395000308900140c0042d0b42c5034002c2c2c44039000d00380144141d040c0068010404141524007060b840704101900740640a0012000c1d01b51202280d00700303d141d9501201421240107203515100c0d100d18110242c07841e480c40f95107288004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 310876366 1250 310875116 310875119
    0x61801032016030525050c2d15040e060406271d12032e0308130801020a0e1504061e02010605030304090204211e030318120206010e04020901 62
    0x100001000000c07070f0300ca49002890700b05011a541c0ea400c48100144420480381a01c3e6420800b0400c10304540e003004444003141506400a03014080c1c01480da045ca41c204005109605038032040c1c480302041c3c40480d46c0e191125165002e0034150a412241240b1480c00d18400149612042c61117580c042d4548294508030a000c4100710041c2c0403103080402505080030b040b900d0280c02f441500358445083c044c1c682d44c1e003414280342c03491560103024400d900e0703100d03030740040095400b000203412a58003030101034551440180f00720400126501503212540002540c05406502104110310582c04455807501c1891404034031b4220301883c0101c4011a10025000b00028003107980c034484203109100100d0a69250000b1a04580040c1d02c401e9a260300458144041420303110401801488810800c5418000f62200141c4e02e16180c005541c82c8100082041894400d070042914454046000312a4034818605034162962040c2c064005000365400841e050720310b28145805030f5002010441140d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 310877616 1250 310876366 310876387
    0x80a15140d031b030e011101050106020a111801060201050a14130206030603070b07030305150f0a0302060307020f0109120801150e0f210c041a0604090c020703020618010320 76
    0x460010000d03401c0c44003e0b0026004144071140100040d8032075510203a415070f9120014011210300b4090306041e0f41088010f204103503000a649580541140a00340d60500c2003010511250007000c1c0c0380200d00040d800814443c0c5c054200500440b5034220420018a08401038644060140d83d100c4070844817401e01340c05031070904003542d00b005c0d00030181d902c42c654032091240390f40d1100200714003003916241080302d2909281c0003082034040a69004044a0002000400340e446c5404001d205150110214400310300c20001c003c031801d480f5008000b040d0090402030440400040d1041c00901e40d00300100703401e80c0110300003025901544402241c039141004002070304e00c1c1044503903080029601c11070700346e42c0200c814034070302c800660180041c1e0280c0010b00c41510400290002c01c21500300c0c0340b9009450701d20407901200c0e10140002680800410700301e0800045500180d07000002181500c0b940340c050b90f4140340070109880810103141c2c41e08500300809000007580c580c0900c10703c502c1124 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 310878866 1250 310877616 310877629
    0x603020705060c0309071d07120614090a060f06020c030d0e060a121b0c050d02062202030a1b090e060606091311160c08010b0303030103030c0f060c080a1514 69
    0x402da00b0000d86d12200d440e0520070304034145c20881d11a0070554482807000b110340200e0102448420300d581440f4460415410140b95805090303040d0151500e8000075415606542c0840081c10003081340c10511556581d00079616515980058864020366980001403806100d0301c0310030745405080c0e5030419165000c141c5400805100d40c039003403034803280070030a2688071416007645d410307a0783c954001205140c01c00603d0409043d0401003036602c00010700c50044000d0b1002303501011000c24840060516101183c2006c0100b40001c0c00c20310700400c2c0388400c5214a10a0064074a541c00030007608400700c1c0300c940d440905541d500d4003c1c01c100481e98090400b05100203000840303650114580ca0768a884401c5544100c080d50842c043c010720444c20801440c4094004000d5440203101680102001030f84910045c4801000d00c203003070896000708815440b00400103500014104101c442d1000040e00101007140c5048070146032800d9198035a101c155520b0030b4a150b110b47c041c3e1400ca0740280b144 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 310880116 1250 310878866 310878871
    0x20624090a020c031308010e01062d051309030f030903080403030e1501080f010b0d0c090c020f0a050102090906100f03020f0c07091b090305030d050c0c0f0105010f0603020705060c03 80
    0x5058082200e00f209090800003012810550390045001790b180241032800c40b04030500071801e40c0d04092041010020710301080352443c03860040c101030180e20400481c40c00c44190301c101c3d04252481c4410a8100c0346034803c80042d0300a44a40e406030450303610440c221103a80b000207012851820110303012a11039400115100741840840b0411217640780020031180c0300341d201c0c0c00c00740c1c03095020720b0700700c0001c0c0206185100260741103c0c0b03042c0d559484075400e800f41e00429a245070b4079a040016207108100c3c3d4140c441d80c1000b5200500143c0c00c10a000c2d60000c481c0c03030b000724400408280d280c10031a01180c0100c5955407000014040000106c2c042d6020071540010404140140401c40c00240700400003800102da00040003c180c0d019030a0503e8810f1000c01484000401040428030110403103801d03007580d000c0021a44e5409080320300f50b0141012041c0349101e0708405040300941540494181c4200452106180b5590a022026403240c1d00340200b0783d4203c00041410f20388103001568 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 310881366 1250 310880116 310880131
    0xb070f02042310090e0a060c02011b03240605163306060f05040605090102070308190207050907050d1d0f0d090b04050904030c17040f0602062409 64
    0xc52600c40e0740b0141506449041030340d0104141c005200c2940c6029410340014501c480090001080c8100d43c540c03503100d0030401070b110a89071510401044c0c401e6001c140840d81040e9030500132404079400130024a0721040c1d0840c0030701c6202141940d81301c1d611006040f141e580e6034403844e104400c03d2645104000200885640164a80e40da0802e0f25145180181d40300700c4490752030160301c1e2aa40d0702a0745556114809000021310304c0402c86502804481c10b580c0c0d541841c50384c0b5240303100100d00c5c0c441254006441d04c4408a42510f0000480e0100b00b0510055070890342650303159000c11026242c142d0f0b11501081040024840351191900f0442100e01c140102d2a41c0c007032120001414440032003204034080c3c2100707800445c2d6640000b00c0c000a01031061140c1c0c00e00e42000042415140003034409402e103c0041285020030000c0340300004140040c0c2c0c065501c079942e84142c01140c0c000f5006820250051000080d442c4200e05031070720000900f081c00f00586440b80e020b212603d8000313440700 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 310882616 1250 310881366 310881371
    0x8040b07120617030c1e0a0b041b090b3111090913020a0b030108030d020c03070f0305031006050903060c1e0310050907021506010e060d180b100b070f0204 68
    0x80c3c08a0b00300c401d210111641c0002d160344100c07200856040c00d030641c0c48480080c41c118081c0007000e500050020075503a000e24020401d4880307052801c101c4a110840704124030760000c01243d02d0102d13400c01250403005403500d899044403200c5400000d0016911070055031041d002106072803410b9041041c000355908e1140c4e10b040413400c00302c1c40c3d040f000c869200c03844010508807411070415002c0d81c4002c10b0703088041415541080c000549078030888900b1002c036030f00810740c5442c0b10814400c07100c401da0f002d040151070101d40e203000350194204968800b00c5890b44440044d546004002f180d07003134000140900507035510300c00c4541132034202004003429090320010802603500c0305c8009600a21000a61b03910740c9180008200160750300a020000b150040060a060207004041c12078008009081010005200201080d0180540046540200e00304a031101c440d0142c06c02e2074901f2030159041c809c140e940c508520005032520310510300e5a44d801c00551000c552081920610244002d001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 310883866 1250 310882616 310882619
    0x20d0e1c050111090a0e07120510170a0303051012060e150901050906160e010305250306090e0a020102070306050c0d06081b100e133908040b071206 65
    0x2410300b10f075481c03500143c2c51803001892000074a45400d14000078291000e08011900c0e142c10014200c604800004200303e80f120301140780000340a0604014250f090060164903804100c1a81e8a880d10314055002c0780c40c0801003074100c807030104c4010980708001001190210305542d040018800301a1000041c000c10188581d00d511440702140140ba081c1d0011889091a8003024140302d0301070315410181180c08590200b003070300100310b50b5038000c090034002850ba440300c101548140e41c4400c8103030819802c2803019800754143c4c0c442c03815942d80050030800e421090620366038403100040302a0140c1e02481040000800c960022503020346116111800d000c0c10141160a552482e0842c0895800c00c0f50300300d00c100c0b8082500c41c0d00950440700041d240b1801c00000d46200c0105120901039002c03542c0110b82191260490362981c1c0048003000c82100001c100505036011407800f0480704080540509000c501c20061507029981146c0d50000d59228103030103542590310700e4140e00c1c580e0703142c050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 310885116 1250 310883866 310883873
    0xc030303090d030e0c01120b0301060305011503030311161410110c150c1602010e180609070807120b0102010e0d05040512030c0a021203130602030415020d0e1c 70
    0x61801060700a00a11140c0d2810744083c0c10380b40c4045031038201d940300084c071003440c1c1c0e44070708005065800c00000050218111020a001d0b02c01e40e00007030b0107507003001d042c4104070110115140803a4043d030f40401404c03224540c00c180c5481500343d0a0780289161018601141c810440c0154242c8007108803a40c1030305000c3d501e0141d591007030341c80c0000040400c804240d4001031001011030440310940801c0c914140c00e05100078004e651416207142480003011007164000d03400c201842e00000c0581070701201c68100120418000c076282c0c1c0c0100806404500d005016642060090304280c8507a8800090b03504600014110441c3e124119034903403805040c0d0744010301c1840800716503035030345643d40c42c28282030103c4182c800ca0004065841003004d41d04c02c0038041a070002a81c4e0440c1d0203d50380410340c900c91301d98010042d1101d900d8650310400500550004024011550108120203000f801d1400c2a030300c554a82c1c03c8200812128684082146001840303800307103804070300e4295503c014030384 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 310886366 1250 310885116 310885123
    0x90315010b040f060c03021f0b1305180604050309011b140606010315030503121005060a020708100621080409060830071b0b0d0209040e0706140c0c03 66
    0x340700c1c00c908100002c0038070281d903058074124064025403c0c06040e01125a400a594454259885500c0390940c28001ca880c0c00030303004074410a03001031041c030050304d1030b11400300106015904008180b940c019220700076040031442c1803240d40c01c10040d600308649280152a000c50324060102d0000b600f219000001d48155a00c5d8284c0b00c2101c0140150718000300098125582c18441c22403900c296130040001900001c11680d00b5829003800124076201c480c9030354100c0c201078004960040010032240325407a4000342000071507401600700d902c054500c2d0148422210716006003002c0f00d500b220b00b10340d00419000056503051107500703424a040d584200ca9001c40d40e481e00105210703040316050b41c100c0c03144030b601c0802040d00860780381d40850f42044114010702c074006006103082405120aa55014550015001010301550705980d680036000c05400039400600039a10661509018000e8044006005020386040d501d41c6c11160340403012400c015008029030780c08520031800818190340301030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 310887616 1250 310886366 310886369
    0x180f021302030702030703113915070605010e06060a050304140d020d0909050c032403120703031a01020c1302131409091c0509011205040c05180103050a03030209031501 74
    0x340e02a5807100d416190003080600c1d2081d0340e403081d5020101d27081c1001c0c1200030380407080400c008803002700c2c1d070400b00d200c20055031100310640c451480542c40b81d00b030161800503c04240715003400c02c0207030789800d0703030800080702a0390f0281c01c00000d0043d00c003410f000d400110f801c98012002e8030b401081d60616540341048020f001c1c0c005800c0b481d158080340707400c0040c01d8064094408184403500d403000d00390340c0034000107003200b5024586000c100c4409141001d21000b5400c041c3c107a40b0105c1042c0d01100d4254002401200040d20b400c0740702c0c00c198000e00303005061b800c051740a0100080e040b401c001040030001d0091590759030802915130000402a4480c0003007203034051800c02c28500300c0820101c1d500040c0300c031030316030071418a92201180c0c032080400d001c800c50a046840740b01c001e00403070b6985550604c3d2410745180205000600411041200450344100c0e0124010407107000403606e804403c1c880100241e211611030b0000074001c0c1c015202400d405012281442e00041e84144400001e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 310888866 1250 310887616 310887631
    0x60706060f0f06020a022404080601091d0f0705270a0e0c060415050a141c2301090513050a11040507081e091009060b0301060603180f02130203 63
    0x1009810480a2034a1051000410860001d0005c049460700842c0344041c10b44401d41740419210082007035910f0002c2946c000e0140c01084801941c1c613022041d00400b201b540f28450380801d00d51002c1902c1380010600c001b07645040c050203071140b800050204104501011b0440707030403083d1300b00340c4103902c90700118400d000b80a004584141c4a0400c80c2c00d020304002000d008200411081c40101c0d03a501c00010030541e00e00d0820780d195140c03c0101c07080c0c6840f107002070400200181e00c050300c485040c1c08d412240503000c03040000c80f036148640701a07103a2000d8217604c100442801008408016030225034050801018251100320303d5407070701d00345040310700c04498501c03800c00300880030300f000c2c8900d40e4000e0040c24002c0c0c231800d1801c8000b101c200c4041034808101c5074103001031507059043c84040030189418005022800f100e00e0700c0c00150540b803203218020342c1b82840001c1c0c05803013400b405803041c0040b8480c0401c0e40290701d488a02010242d07060341c1001e1150b04d18106c000c10361005601c41d140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 310890116 1250 310888866 310888889
    0x20c01140106080606070b130209071707031b050306040e07060f110703021f030b0a060e04050f0709030206210c0403051b03030f180604060206040b070201021905070206070606 77
    0x103503050340310344903040c1c21810030032820004010a0382c80b80001c440309260071590b03c4405a440030a00441e04c0030b40c0c000250050314600c1407140d21a00603c12210500d80d580150b407440d80c1345007044086071208140e82d802a9611100d030f42100303000c0e02c0116006040504013003000505401c84524003000d070b80c4032000040c010404012081e034821100f1500b00a080054642d440c80d503000a00390303c0c1c00c0315251004a018608001d03000e0700a9104031490f00e00503007001521680ca600c00350020170740450320343c000d1f0f05000c0041e48120302d0f45046403041100d0303100c00c04a5801c6070284045600103c0c0d182c510640c000c40200440d41040030700074815001a012182d0f210b00710b2415a0810782d51404144881020701c4400300b45560108c166420a000c4440150b01c17200311603c042da0724200001c40c1508540f002402244d030503030126250f4803035400b440320f8009941356a00c00728201d12030340c020050344642e11140a2511071090008040300d41c00101400d0038049240c50300c4045641c3d50380100d02002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 310891366 1250 310890116 310890131
    0x50408040e0705070203030703030b041e02031605090a0e0402061e0d0e031201090513060e0d020f060403051e09101106070201060b0304062d06080106120201021506060c01020c01 78
    0x904048640e0740014180f500604103442c56000c00d9490252040080030b154903822240c1950321561700100c48601c0100440c0306010120019078025402508c3d01c4601c00c04100070b420160340504120b40030300030042e011881e180d103000a04141c0b00c038050001c0340d001000b00040d900b5222040c2c0c0407800d80545941903076035405031004803001c680c0c002d00700e080240c01c00d000c80990408140c00d40c60460700900b10202d41c82c1e5400346c844c613001c4010030006002624111070710038010000034108040c0680c036001c85292003158005a070343c50704200c4000f400a001044040350352125600300c805602501c860781410300c488003000544582008084c3c00c0099031041008072120410480c5c190440c50341d00080100d9400c2030350003120340c800140301070101a00c5032866014017900095089003042c040c0b02414400c44001004009001c1c40d200c0c0003a02c0d0f090407004108a4281d030644903603168140c00410411020749090701d200c400040007264000703c00d07c00c2d009851000c2c0010010410900000100b10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 310892616 1250 310891366 310891379
    0x30c020604140a0f18090302010b1503040b010e06130e0319020f0601090501120219150504090f021204020d03020a0c1509090501050d0b04051204261b1e0405040804 72
    0x11034654843d414500710850200b10040701007071017001010f18018082040a254282640980003501039290400f6444130301540c00483c0b5005103010b40c2c0304d44038035007036640d075451500c03103024007503c04d03640c0480d4512400074041c003690300800101038000c041e05d0810405980a51301c036180e140c12900541c12507141c00341e03068400e010302405080c04820400065041c905410801c04146800a000d14540c201140701c08542c00a50f00060007040800c107007002110100030810340241c86400c040c9070910a0382e2044024a0007995a4609100080c0c4815515a000c008851920304800c0c0c040d80241480c03800414000c0b403100f07000d448010703d00c480107500703e10014001038556025000c40c83ca080018000e42d48e03124001034031690004409012900c55040c03082c00c0c600b038900071550740000010300082c6079040142ca03c0c51000c4034403820340c100b4101e5480c152540407061040000d134042c50503401451a001901c10750f5601d0120700c44007010350420100b4102d030020b440c10f581e100e0380802e040216 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 310893866 1250 310892616 310892629
    0xb03010306020417070e060f060d0609020918150402030402041407030e10050108120703050c030d0b090106031802090a0e0f100b030f030301140105070615060914030316030c02060414 80
    0x82c1c418400052000c030b071034a46c4d2455010000703848584a03840900314040e080d607501080d0746100d06500c4007000b19aa9581c2c49800075032017012242d000341b900c0910b03000003a07108000580716901615800010300c06400802009510082080380c0c01a80c41804401035115424024481d40054400054038500e04a01c6403904138020306285000d81454018443d035000030401d0740442801007102519180300d49800c0c1c6284c001c1c1624050648400716000000210b82c1e001094a0a0152030107812a600c03030f1400c8060701c0500e240304003101100208a00181002030202c1d50042c1507110029100c40700c0c84605050421040551045a00c80300c00700b4020300141c45000300e4100110000c102c2000140345640c0c903400148603200180700030740580c0d11a40d010300d040703030b080c07503400001000701c00c0842544c0c082d00b81e2903000d240d0000312440b5021690407040075415441d020010300840c00c00e40040c904452071aa0320008404115005000754010f031102c0c00904041d241210b20405210a51428840d8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 310895116 1250 310893866 310893899
    0xd0b01140706090201141e0702030312040c0e01090b1c0606050d0b04060608060f0406180f0503030f09030f040909060f020c1b18060d02030a020307060504180207020117040c0b030103060204 83
    0x11b40316041040c500940195034812000c500038560440e00d803d102c0c00040e013103000e00b83d181d5400300410707801c02c41007090841d03c40007910f112080c91a00380c0d8a858a0303030100d8070901030103600310300e0b0070000145142001d88500b2101c0d2050703c011a2464442012a440c10081ca02c1220210b1100d400c0c0000c2040c5802070320054440718004081d5072400ea45c10580315a00604054a0960b0342d0780c81910a4281c03002c807940143e00603288102d07604481c904030365290b008a6054410002c2c1402184d030181011080310203404c8451b1406040030f00f000700201c020b20844c201292515036560340780194800700d00103000b1040030a0094015400020300a25407a80c08102e210300c14041089031200000d0305801c06504000c00f0b6a1914003559107101280c5070951420b070180d8944030b154400210254000c0c000e00998000340782d40c280e03180303c4100503c11380c003407403100a0110f00200081285403056009699026002d034441250702580d0302080341207944213820907540241c00113814030100044c90240d00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 310896366 1250 310895116 310895147
    0x603020301060518180a0f03050a0e0f03060a1d010f0606090b120c2d0406020717030a0305250f09120c090c030209060d090c0501050f0d0b01140706090201 68
    0x101c880f200c4c50169000c001c205280e41c00f1008800c081440d810080c000c01507034003009001310110b0904015059400155076240054032608807030400b410056a100d98070758010f801404903460300c00e1b2042c00f40c07210714416010304803014039695920009014025000c424400001005401d2500040420505c0d8028503640d180030041840d581d14480d10042d4080d04060300303191210180301d042404e00460a00c091420181d00700703180c0402101000500443e50301b40c003180d41003a07540c2c22032400f065400005494a4005120621029010f904901d030b1090144010851000d0740201200d800700043c0380c540c0002d0403141442e1286a0407d40c220040c0c1008040495007141d507076138a0704805018000ca00740940c8501410845070302940594608410081c500c2d601d030212062554018190000150f401d0045c80b800055154000c0003250011500f0b00c440c0c038079080d00c0c3c1c8541c42c00740082c0d41c00c2c54108a41c40100c2c1210b10001c6c03025040e66440b0f0301004c01c1106450000411001404030f061 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 310897616 1250 310896366 310896379
    0x40314070b03070302090a05062a0f0c091f06030915090203030711010516050f06070e0901090c020a0602031e070908031206040609110d11120c0306150d06030203010605 74
    0xd01070780680c00d007030380c2c1e1220703080c58090fa41e9400c91001c1456580103501c096001403010801045d40000041c60545955000030000080080000b0440c0e403100101140c50141e00304551201071400e000c2d42d0680e2004403140100003420103181100c2c0c0c8450030380d010100181e0303541000c1041003031030703095418041c21088081c80710f08402d0f00040d49921840100074a40e800514071140541d008106030380070180d4500c48020004100e08010361900901164081e99016100000c1c00744c9004041c4040e0702c1c1c5015100054a84c00c159846006018803002c10084d84604c1000500282c2d4a0000f144918112545410045400e88011120410242c049001d02c10113034030a21550800206544651254404d00034103502c400d800f1030014000703034105454060500320318480302d0182d80001c0c00d40c07428442c0c0420480840500400e030703d01803c0003280b920202031001c914204c1c4200c4c00b55402440040005113038481001c1c03102c0d500d07446a0010311840780c80b11002c0056150a03c1050010707c0e054402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 310898866 1250 310897616 310897619
    0xb19110c010f110f071701180b0f0c0702090411010e330d09050f0d0908060106030e1608160504020f0910111b090105120c0906030f1204031407 63
    0x1070701c244840c8007181c040003860010f01e90088810000c22148105074000e43d40308a031140d006151540d41e5203804541036080c4144694010b09030f01083c05040d400c039101c000c080c2c4440303104400c1160050034030075200100b0b00c106009a50f540404d00c1c0118415140c001810245400160810301d840c0d5889108460f81100e4041007550800d001c0f00051881e8140c0310f0a1042c184010314034011502d032103800c2882e042c00101002400a011510011703030b50105e500070090300c82c044824010a0040e400d51343c200900410000340a9089202820b0342030064450191100c1c82004102159a00c40040b0340e10243c88045000307800841200540002c0d1025498514106620149803007150314142c0140c10102d000740e0514490016503003155030b540155440d80300340c1b01100101c02c0a001d038007071052080c04000a5a46040741c11030300f08014030030180807a01c00c02420030500d84c200410703850b0140610b080107810600107209110074100c211194544075030039400d1508524401c47c401d0280380c0e108400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 310900116 1250 310898866 310898869
    0xc020607080613110c0115080f0d1b020612152d0d050304030503120123040b011404080703120e0d1506150206070f05040b220b19110c 59
    0x1c850742c41201502c0d0b000f141c002c1e11100381c00070700c1950711851102802185001200006401c00c0c2c954545204580345110388030800300751610350964454030359602c4405410b1032280140f003000707411281880b00d065003400d987c02144107a4000074210442d1140d4030104100c0d004031104808205d601681c81c42d030811981c0d9026250800c2c1104527003290b4a141c0c200b0710040c0c0d0303010344c1100040d0b0300c4001d403919556a864540d540380c0108c00011300001b1200c0c00407070024002040c00700c641a09510000c0d034070070010144030003004c40c09a010304000d00482d10920341d20f40300e0014802008150000d107509841d5050154901851007030350000c00085070355020080c0d49078035400c1c8d035194003c10800d400d401c42095000080c001036225042c07002d403c420160b42640c000c00c803507206031841d0704d80ba09008004042280d0300c1c0314501031146211801d0008590001c0d590402d04441e43c0502c1d1040c14a0317456032036203c42034000103c06184240035100288682d5803042c040c2540440365001812a10550f00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 310901366 1250 310900116 310900127
    0xc01110f04030f020d1a011403030708070b090109020a0807260a0311030c0a1a100807090c030b15090a0b0a02030d1a04090308240a050607050708010507050304060c020607 75
    0x400500444007420f05074003955608070f042d16035503500a01e213600c0303203220743c00b050701c0e60b02c0034420704113008010212402c076401d020003207640d0a80c0c0401c84034500f0b0b88558a160a480014140480640d641d101000040c0c469141c030001411040008051441c0307080340a400004064100707441001416101d2078212100065100d11640c0c5802e05182c1040c3c003001c01ca1070b5020700211405103104180000b0240700d4064418480c40781d440028100c00d5585500000711381c1c1580c4240c040950222004100c40c02455014180048440ca008289141c13402e001403a0749171103191031240c2100c00120b00407140340880981d002825051030250502c2e50440021b074407409040c01c0c1c500c0894030b9650b41c240c04050a8805c0000e020001d00c1080303403a007a070600400d2a60129600e00218038103240382d81120340520260307680c0b4000180f013030758000d0408003805910b821054048980b4482d1080120740d0000c01e000b614800c003501c1c0d03a091346a00d0282014815140007410420654209000344001303d50b002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 310902616 1250 310901366 310901369
    0x40b0403020105090d0b0a0c0809010b0a030308090a0f1a01051f0804211d01030204030203070312050c0d0305150d20150c031803060105090a0906020904020f0c01110f04 74
    0x90820940312001e04c00440d50690720344400411022000040020051143d8070011402902c0d0b96440c0155444401150807601d60080c51640700c146504d00b00006849004002d6000b042c48007070b2280c0340c0c4d003944d0712804da084800301265007103841c0c440d00306440460003483d8010681103a1483c41c80c0726904142410406042024080090750f00000b400d00c00c06180352000b4000b1006522600941c800f001810f20401e1441d400c0702d61808490107016601c280252815250014040e0016a10350740e5003007101a01d44c00e5620034050280618500303914180075a800c03d00742614040313000e1038102040a54060410703400340c480c58107080ca80020904c50200364840a81401400000240401c00500c1c3c9504400c00920b41c40400210141c00c600040b028010008902580b40d080010740e02c10561145c04c00d0203410307046250744000417000100c5400c2a5101800b07180011303d0700c0c0054010905070790051445c01002440001c5000350170303009200b06441a44803001050808179050704109282c4140e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 310903866 1250 310902616 310902619
    0x3007030807110109020a060e01020c150d0b0d050303040506010f0e070519031103090a0b0108010203040f0b04060608070b0702010f0305010501091403010e03031e130210030c020f0a03050c010c0302040b040302 91
    0x20b0078041c9810600358400b4003510f4000308031814580d61440300030009410f0b00391250050044407007442c0c440c200000100e5140080350009810030300044a400000c02000c80320310b030701008070216000410003e000030360246001d400609a258106154000d5041080d80302c540340724000300c00c00181e1544801a550302c400c207500e02c02c3c82850a41c01c00c502511a620035580904070000130f00845850025500744d459200701d1010f9101da0707071541c480d8203d00003220301401003401050b4544c000f44500f156164014403448002942c0c9071911407451814626810080c400040010074005542c1c0102c10112040807900e410702c42581003c2c00207003050071034440d43e02560803070f03502d0006a41c0c0030341120441c1314002d4122510fa181000c608506c8051072104004102001c07401701d10381c8540c6020b4085000d4010303290f903540e074405170300450051034043c4015085008120100640c20010300400032518084c0e5101621801c0c1d200c20203085850a003094424584108020060120001d061b01c080b47d80 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 310905116 1250 310903866 310903877
    0x5033a050c0c011a03010b010314010506070201050403140106030611180121020309070311060a02060718090912020c0109050112051e0c07060f05040f0f020109083007030807 76
    0x5070050424160300840000d9100c07542042e141c428040c0c507800320038040d554100c0007030021000c2c600045d0304860065000114403441d000052150b400c0000c02410401c0c818076200740340036501d4550510750305030b101200c44140d4507400e00704180000707800349521842640006514240e216407404034440361407c0e01905001080030304207840e41c0700201808081e504090159030300e01d8030104051321444c141c001161a84a610807510f92400c2040a9865103030b015001006240c507820f100f50350000f000b4030342500c07030400594003181842c45802400c48180c4aa44602c0e100492503101906100e044464681003111000040140381c0e40404400c031901e20303014000460307071103c100340c1036031204040d2882c8206c01d0f00303070038045c80b031401c2d20040c50035074020401000700c56540405001901c0b4140c8002d001e58814042c410080760b26855111052481410030388040b6a036006000c1c10b108804004075000f40080100003e11009101d05081c41100000b1461510020307980c003030500c11000e0648000c120 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 310906366 1250 310905116 310905121
    0x901031109030a0c030b0721090609080a020a0201030f050c041703070b010e1e190e100f06050a142d09242b02060d0905033a05 56
    0x503044040750034401002e026544440c0803824808581c454070b100455a0403104000100c085202e143c150b5031103050546141001c44101607140094005809e09444076650b42e861000080c45107401080c82c0d02c040d80103000303020258000903044451a462183c069170510040102012140341103c099600441b00081800342c1c45000506e980079240006000090103400440d1603d40524440d1140842d152a22a04142c1c13114144100360180c600c0100c9202c480307100303124501160040a03074062800100c4d11240d1030440c0c00d50903600b40101c1c0400283c0d84030000d11183c00d0840e0944003070034160001c240b0500e070030380114843f400300300280054440d0000f801d01600a0b01e20140c00d111070028001340190030840c900000008020088017500700b00743c4008a4a41000000d460103a080d007800008181c01a00d940d6181241c1800100d0380041c08202200f03009502c1d22440258a004030025030b1030707150140300d41c000c49a40c02d5107807400d201d01b00d4002001c480744503401c010ac1d0815102c0031400c3d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 310907616 1250 310906366 310906391
    0x2030f0f0409091112030a08070509010215011502010c1805060f12152806050a09080f0705040606020a0b0c070309030501050915130b1f080f010903180803090103 71
    0x740a250048005642849012402c0c40704110018801140c2114000c4a042c40c00c0e2646a8a2140c11040c9010440c0b91000541c100e01600142020307090600540b2030040032148001d200c0d41c1c0c242c00028004641301900b10001d40d0912585c07010340307150705240484903000c040001c8038000605c61280b040700d000030211540790094068a44980a8010740352842c01c020060700c42815408041c507005005c0e44500614024886c0e80d120303002c50403103040301030281c1032110840c0c0300da00c080c400304184a014100056984401c00c000b001c00a070020141007003a09100401081d00d03000c0d17228404643c05004c295010800b00c1c0c00c1e4a400c4106186059956883c510b801c1e00e001910b5840681a0f501e0002002502c1320b0100d0600c030032100c102d01070302c400d075681c000030208107191020117040c048400300050010300b50980158601d05048042c1012659200e00407440c02000301c885403940c2e511201c000e001c050b0006540240c0341c2c0c0c42480f048119042000141e900d004000d03019040503100c440e404160f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 310908866 1250 310907616 310907647
    0xc1e0115080601031110050307080403030b1206060a0914070c021c0f1b0b180301150807080d0201020403080d02090103060306020408011409010b0d0f0c0909030e030c010f02030f 78
    0x40300d0300c120020039280d564408070390b00d5040900c01903402040c1c150144403649420312912458401c0d6440301c60030754442030f000321030591004204806041d0342d10102140c5681c1c1d40641020307902d0500007419140b508405029040c07400340d02c014030305801c0180400203068440e030303000d920548600e03010b0940394490002440e540740d26005400da450602d6142002d01aa5001c88200c90380a1515200e00c0c1c0e1b0840c644c10100c09040c442d80b003105109200505c2e18440500c01c4030701094000f40007090342c402d841480d03404025554001d46503940400c00803c4180c01c18040080990301c540003c60400346192180d071203d2003690f4502c01141d50010340081141e01a84c000c41c041e58204c4002c42d122600d23070305032500800c2c0c05401c80c0307541692030700007850b401414003034010140e00282c65401444c0307096841c4500e00343e142c0c100300e41c1c0c0030070305801182d8143c0c1c0d8417500450500903911083c01c2020343c1c00381400c00450884d103a04020007482c07403820f1b40f03800004444412a03882011995142894620f544 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 310910116 1250 310908866 310908881
    0x30c130f050705220f06031d0f03030f0108060c03160302130902211e340e0603040302060403110a0818090f0103120e01110102030f1501050c1e01 64
    0x303958507040c01d110505600c903002d486440c4c000c0c0c1e401e2610301c80c25503a8410401072407140036001408400240b0040344250030400032003100d50324002070034802000a80c00e081c40813010201a0b8404010070650300300f5400501c0c010000d00b406810507041c00b200041c0c040c032000744801c011145561155025910030350480d91000c540110680e200d40c0c44100000281d4415020500d614a4803601012550310851001c0d010304000500610003561190583c00b0b003030001000d07201d11000c1240c4c40b01d02c880c0300e542402e000a80c1e1404100ca0000c0d034980240c100803d400f88a13019002c00e20410000039000102e8540041c0c041c14070b02003001c02240c032545403119808000700b511201190300003003000d14810040719100c04030361052055461000100d80c03d10240b02c080c200010200002e020b980c041c1750408440c610624050004215400b0081d080e40d0042c1c2c1c030b42c0f0707000111404002c4c3d00034110030782001c444000d103081c030b14091740903201c4e5682d103105420f08580b402d0394200c1450014002d510059 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 310911366 1250 310910116 310910141
    0x2060c07110904030801050301361a01090b0301061203020607120e150405060c070510091b080c0f01031a09100302040912080105030d0507061814030403060f0b030c13 73
    0x589890f00345801030900d40288079050096080c40300035403440c104002205070040ca03040704420b52224a880c0e44144015812013669103812201c3d41d5000c3d111040f140d58044d2200300c2010412500304014182100c4032544000035030484004803c00080c0d020030290713000002403038400c03100700104440310010001c4590030354075403103100c060f455920400d1072030a1149000b10150b8181c0e590342401c09010703100c1c0440050258105980d0480d0102080d400111206c0c0a0009502c0308003e103040000c6460254101c0001c0764024240c4420f00e02c4c140c0c0500380e64420a2900b881002d00080200300201d01c80c41d000d03445180d0041c0000c0c00f0125050500d80110740081c01031000b544541454080c454552103d0400560428008903260800040c0e1070101480359441c1ca00d400c01540316400140008490070955006203100c220114101441c0c4480c05044003000e07550702d900d945083c0e8201c1d07489000714910759040c0384101d02d513a60041480280080305907a080d2010441c280480b00401c0c0844140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 310912616 1250 310911366 310911379
    0x5061c020d0f1a090106210c03090b060a0b030c0c0a060903050a17010f0b091c060b010e010e0315091002031501200706030b120f0105060109120302060c0711 69
    0x21540d141642c200c412480300c010000c02207000d044110050302110912890380020000d4010001c0314440c40e1000e0703110440e40881148049108041030a0300d4a49003500c000039180d0205c1014009502c0c00c0310b402280459200440f00e18000720340d1281c0c00000e000d40e0303884102241449200405000000e24a40d011600300010b991614000d4200d4008020f03050004450441c0d100440401620f03560684000b1218000c256160010070304180d845014855082410b144130f480c0c3c0100c810b103140c00e0b00340c4034a01c04a41102e02000060010048a1840307040100b07601c001412034401146d92103045802c07410b8041c0c00d40e191410030b407515406590030100c1c1840002040f0700b6442003c0701154004090740d030f0010b86204205096010302c58031003c418185c101800c10022203000b0b50180340c1c0000042e00c079050944042c8c003400d04181141c0124810b40c0d4503002004143c5d0303030020064010340820074a0950003840c80e01d0007035070742074010300c54605180000b5482c0c00344241e2f800088800382009100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 310913866 1250 310912616 310912627
    0x80c03161b240507020312060f0a05060d0912020a150b0a030b093a2d02100b1504030305160c1502010c0806030d0e0d051504050c01020c0a05061c02 65
    0x2d28062859000d504038040e02d010041038000c0c1c40401200c11340c81a18120341c0d07160f15040c081045114000b1102940500300b00320005240c0c4401019255542100d1000601c1001508003880c0d02c0b4615400281190010010310700003075809040120200b80c4102c0006180400e40040351413102c1c04e41006d0b10049010f4104200c000001560340840c422810201085451900098458840c151180445000001c02000650344101c800c6460080000010f04009042041044413851081c000d1001a00811000002c0c802540116401e03c0815200300c1d5400104141411545c011804020200100000ea21068101000011100c1500981e1003004c407aa1100841c1092203815201c2000d035003000f0112203c9170160b8005445142c0c06009800071040100084407800030240650354440c0040303c980011a000b0051110304080401c82e4440c203050a00b4090700d400802c01109045600ca41843c0e00705450703024070030044803400c0e00d81540300c1c0c0c10b0840303164014040f1117a03c007229101190 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 310915116 1250 310913866 310913903
    0xc02070308130b030408210411040c030f0e0f191a0c1905090301050f01030816170304030215010803041d0c09221a0a15050d09030f080c03161b 63
    0x4122644003240050300c0107e00320300c40708041104580180c8411203100900410341040d400503480d0800b2498006414004407919100300c6400440464682d4441075140032070800c200034480750101344a2441d03890700310035503640c600b002c00400318036031201c1d8220100700d640d448141076402d00400242c5c0d4414031061243d006000f0b03000365035920b202c2d600b00004610074540400009041c0c0750089402e514010190f07612000c4c01910300402c4990301c01d03514400c2d40c2000c0e60009035008502c40c2c0e0142c0303010060f200c0c0300c5d4031804068201e40d0050704100002c001400550342081070400c0d0b0301091101c19510b0103803c05150250502c41c1d0380000d00c0101c0f039148031a440b0518214001080401c0244010b150070000e01d10603003542031a0000981034050040c0041e05c1c50b40300750000d20307241062421012182440541d6542c800c12000b1402e00b001012015800c805034662243e0051040d5083d407415a6419504003010f4070182c09000b00c000705080e400078a0200c41072503a80120010820701942c45 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 310916366 1250 310915116 310915133
    0x1b060412030612031e050d05040804060801150e09180a06060602070f050d0b150a0b030106170f070c0c08070f08010b030c090c0c0106170607090602010c02070308130b0304 75
    0xe1115000a15110b400300d0059041800414650b4065403811550001804100c0f040b86116007080f05211007070003c070502c50310a008003449a0322500300d158980f07103000d00c041d0201c40e043c0c128042036482c502d1105e506a0b4042c1c504a0480d008640044003a2940c00c01d00c2d00b1901c0c8000682c9090085e14003c40900186802040440ea8181d089a80083d03840142000c42e14003030050310343c00103081400e01c01051042d11800d03040726101d507807c929182d041000a11000380c6600c41201c90502100402585070040c0d0a03046249410500d4040ea192280380306015420046c12035003808112443e072000d001d2003a10b080003915a05003101d44054480054180004035442003030181d600300780d407001c42c81c100420110101d50015044460a0f01e40d42d1980c0300ca6049034000c161599a1400300083d03070f800069201031300d0107541000d05203078101140c0050520017940c0005080d0380c11302d0301111038594001103840491760803a0030542c440001c0b4070a4500039065a00c00c1082d0f04010040c03000340007041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 310917616 1250 310916366 310916393
    0x91d011a0703030b091e010509090312060a1d0415110418140a1d01090309051302070503160308090c0901140402040509090d17090703060906020c151005030309090a021b0604 76
    0x2901b028045a03642c0c4200200a0341c202c0340c88045410034800306a507038510024864102d44024640301c000c548403041412001c20304810b0250000b00318041c0011f004120030f544d085141854410300c000940c9006140c00c40c8140e105100580c507031003940c008030a0803a880b8010580204180d902a130400c642d845c405000e0140380c1c3c00301061030b0030116090701014418086aa0303416200e9622140c178203802c01000d9551410b840020503001c00440300040c02c184000c050f50000c01c41151465205820f004248100003091001c60f0351005a99881d00c7c4c0d00c65121504481c2c0b840c10240441403424045006401580d000750741204074407052040c010800306450010101c681d450b6126030780950350b00109080203840030340290304201801e0000c10080d80144000d0342c01106e0151501c805902e502d07181480594901d410880314000380315620102451240041c10100d0007581041100400507108080c0a00700428881d8009801e40c0d0301c034001d0440d0040f0070b0003107068611510301820302c0e001e0320401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 310918866 1250 310917616 310917661
    0x10207080a110f0121020a0e040b0a14010509060706050603060708011406090406080303090f0d0215130f0b0901020702100813022b03091d011a0703030b09 68
    0x85420118481200080c280d03035080d0000c071210211111201880060040c9120700c1d4100016540c194a090204200000d8001c041c00c400594035080c40000a1500f040d800a040c81a82440c5840f2819660707840010150380b0110411310340c4603200c80058803e841802e000360f80000c004a054414040a9803000380700c2e410a60a903401951a41d104884101003405242c1143c2f510600c0003e40303082c00f6000d048000c0c070240002982c1d43e00d640350709245810454404010794000b004001590b5028400c90360711200c41c2c0000c00307070440710809100110f80e0003403405003d800041c10001c1400650349040c252035822040849070742c281020142c0c082d6000100c01d074000c20490709458200f42c1728a0b643c61255181b010700144500f400d80c20402c130400031004020155151519280f81d4400310304040351018801d4542e0a8030516243c0290070307240d40420a045030151150040085141100c20580d2140c2031491060b92820b543c0340a4009106011105070490710039010803110300c14501000b0001c0b0380 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 310920116 1250 310918866 310918873
    0xc1e02060f061c0b0603122b0203010f0605030c16120e09040309030f050a0212070614040510050705030f0f18150d09110315011e0303020d08060409150b0102 69
    0x103400c01440714000c280b03001d400100d0b2504030f8100c003042041c40c101d40c201e40c00905849001104411860440e004040000002c40419034440c081d00c80c220311000c1d148201100540c10744d80b609401c610070b04120311070041403000001c00100800091001c40d40a90400c400c0d44090200c02d090405404174410200c41c0801c40724982d1703050a283c250000d621855240c0c1d0b480c400c0764116960940402c10030081100d0500c07808200c0d20047c0c0d40d9885058103482000000c150561070034800a0404c07200c0854030f102c401c0d0411051240391503000d0100107044450404c0b0b82c0e41c1219151191a500c10051014881500450f0107504052070000515064445c0c1c00b084411468400c00c0001d01102d60300d0203074416008010b41d800741c2035030360000d4550600840e5a040c10203010703008682401100480c00480140410050201c2130413106484d5022400141001002e030a41d45c2c00b0b55a48440417002003400072401c00983c450b641d50b004030700317141d030700440526611020300075060162000d864114098003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 310921366 1250 310920116 310920121
    0x105040302120c1c0c0b0a030f09030203031501050405101404030b0a050a0f1404060b120105010b0d0501080703050a03140d09031101061d0109050402120f030706050106050c0a060c1e02060f 83
    0x1c200d898810303490382107100c0c05d01d05803411203100ba041e40701c2c8032000281134480410b504245914810440311500071f4014681d00c5c40c12050310400440ca2001c81810300a05100a00440d04e0322000f0030860281820a800c1007186480005424044c55000400c50201c5d4402c1100c148065048240103100b80007050110300c01c46840350341620a61100c00a0080c54140002d020031220382001880c5c05000d4160990400da0b0151a400c0d610240c000485035000003d070380c80300c10380510520b030040955101034030b65203003140c1e0780311b445142e03840001e0301f0040d00001d0f00c06013040b12422981a05c080010400014101c0c1c50094031081a015480c01c5075464000c1c0090090318001d58030000b44034a80d20700800d6804c24101ca070090074080c006030781100c0300c040c9170101105d04010301d000d143c0f164801940c0f540181e1500c502039942c144c1109082000602c088100d1081c001107240c0010340c454004590210608400c544a04603a424011240038080310320000c1c0e500441d105008001e10f46404103607a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 310922616 1250 310921366 310921399
    0x11a131d070815220204080109170a0203030406110d060303020a1505060f1c08042409050d030503040314030c040815060a0b130e0c030603010b090601120b0105040302120c 75
    0x10340c00f2910407124440000519a2529051202c07648000c8038498046240d454070300e100007281c000c1e030001d91a81c0c0d5034102550900541842c40401c0c400700c4544c3c0c0d803802c04801340c025140e0002400040c25641c461441c40084e401c50000d0f61900d01c07400e0030810034117039031b801c00a560314141e4130280c0d00300c810102a1000900305000310762181d83e016014001c0503242106010264071952104a00055060081000200c04800074001401c1103003654201c020006a43c03002560130010300e101b4032a02590410140e21520b8540382e2041d018100251613aa40b03050588000292210403900110000200301692804130301900c180c840c040201e4409a10742081004c0c024402e98003030707502c4060200200702c1905000c00901c02038190f10f4052113001e584445420725102e040e210100e038840c020041005e43d0609100c1c0c0d4400c06000c035220750301402c2820005e8582414914840c8269886981c0b0b802070380d011310116802103038050f080c640001091642c40340c85203810085d60340304140c4803410030f000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 310923866 1250 310922616 310922627
    0x120914040b031207051204060c02100221031317030a0f0e072705010303050405100206040c0506090f060d060602120301032f031504020306070314011a131d07 69
    0xc00380203401480800480c41c203e8010782c2000c0000c0f0f48911812000c0c803080442d00c000340005000075201c40d64225094410099007000150451045602844590000006807480b5a680c5005e400080b9617070f440386981e0400c01240c01401418100403102c1481d0750040c0840154803404004c034081244034030b48090081601c82c0f400724000705500c04581445050300c4482c880c8068080144107070422038200c000c00381928001d03802640031810104080015080c115010001d404040c0f014001901e020f45c0c0300c1e035845030716004181c001d107004294041680c80360740c02e1000030207008080344e03200e050202c00180030708454080d41c0014000c00303d41e1542c810b000400c1c0e0307040c2d90340190304003d0410b001d602c14090036440c4070788806030041088504c045883c140b0044100c0303921080c520704503140ca0300500d8034000018008c2401c0501e4420ba6445c0381e815055052f055400601c0100c6140c50780001d00f90b41406901300041c3c40790301e00c180c00215502c45098a4100081064180c0303c50381d10414141c03803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 310925116 1250 310923866 310923881
    0xa0209010902041202040209010504030209070c1203020901081b0c07180b0607030f260c0a030c08091b2b0302010b1e0103050612120a03180c0302100c12091404 70
    0xc0b00b1280b04c1400c01458260081e02281106240080c202580e03500000c1c43c0c52026245180411880350400060003031442d9003013403020803401c007076280c452004002414200b00802d100e40e2101014a0750901c1c602e060102e400340801c0c0c2c030480359007a4903400c4002220700070f0100340c14400d00d0004c0354040d501b0054282e40c04541c00d903c0c2c2c2c440103800810161243c04007503040b0a032061002809600c00040f110000e80030b0418001c040351141101c00c0054215091315280d24144900c00301005001040029292540059007090380504402980801c0f901203644165414507032016120b10241d00200c042c100004c0d000e540284410040d610512046a40b0001c40454010301d42c0302950842d402a080f054001c900904102f0320621840415820900d00303904941131703054000b980cd0030703180d4580a945203a81c07048500a51440c0c0310b54500c1d12a40d050320000340500b02015080311002c0c05030a02d1180c41e0f8004080070040d441c0f01c00010800300041c060b080e8400a0082040e0071420705100e90320 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 310926366 1250 310925116 310925129
    0x2303160b04050105030408090d03030b040e0109120309060b090a0b1003020a0c06020a020a050f010b03070512030406030c050706060905040b010e0f041e0c030c0e09060408030f040303060306020703020a020901090204 94
    0x3441c060030000110341640c801481a680084100400300c0700ba140c04102d280401d02136903000400004003410001504e04091021005a043c40541e0020540701200d04407114200e00b00004c03174003031502d0039401401d68288002c0c0e022031602f0400c002580140c1114100010468012503110303041071041e03080b070254030300520026000d0824900010720590041c0700703c600300d00468500428a60b03c0c240303415070001310241640d4540341d011000303080410070303140504001c03200301a80303640784070444c0e91f64040d5100c0d0008241e15495408540d60080d0111b07540240c0164061121603110612800600740a03a003c03141c144184000081c140041d100c03143c0142d05682c3e0806c442e440f29102c07001402c1c4100e02c002d02c407464020701c1c1b00000f400005110000d510406202c40183d03c1c280d005180031400030300e8034030f07036400820800002540c620f0442e54000e003090310604640d102c90908400910f01500010041403001920720b09240e000a400304525108480380d0065070b0b22040c120050307005a12500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 310927616 1250 310926366 310926389
    0x1406010807090c050d1805010605120316060e190506060f0f1009120f0501050703110a032c0c030c060414060d0207021c06051005010804030509010207230316 69
    0x380300d82c0e44680c0081e9900d50041c075129043c030301c0d103078810400c584003800e0320005038881c03c2c1044100142809808000c10045615a042000e125009501da108020030b050087c0b91410340e0504000556109039580103c0700b00301d68040c901075022501100300400309440920a0034000348240c50304844201607140043c116a407105100003e116042c21541c0f4001c040c01030801000c14201411f941c19010300e0301034081041c4000300c07402d0030760846101074510001c040c1082142c0045003c10802c8400c03511151a00040710351444000c0b01d1f07100c020100c08030302501d0340300c01e640c0460300c00a032800d02c02400724144c42003180d0304800c100c054800d41c816a1000b42034004000002c1ca400000b400740060213001c054a03100d59540041d544803401819401083c801441c1c203802e00c41720f480340315481400040003c0e0100e00340000a4022840100010100480040c0d24005a40700b0300c00302008110303c00950409454004240c1849507542c2003880c060311410048007050305078070108a0480b003020040c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 310928866 1250 310927616 310927619
    0x3121806170702011b032306090402060a030b031002030601020f0d020d0f230301182c0a0f0c05011101050103150902031e03030a050a0c02100b01020c03060c04031406010807 76
    0x142075468100801d0401955030b40d04003410902608201c2560344820f9607000030f01c10700144040c8002010440e00000500f65000411611381c030307607001c03068201c0e07011541140c440c940d001003180544a01d000f4a40c26026002c4119002c2c2d8407070f0055801103000360240c03610048009001503544548014130b400507800750320b948161038000c001c05010622545892080082d41c01c1e5403e141004084500f0301c9494004010011003494808a030f8145a02c1c0302c044c0010403401a0445511508006070040c2600d4060041c4004100700300190081c0d0340403211044007c0710303084c030b40c920117114490603000c1014500a04440f038010f00c0381c50b050302d078805440c21020130b400da040c0c0300030040c0143c101e0b05446880210710541c941100c1084488005000442d41c0746801e012407029200003038400311f0303500e0504540306441c6401040c41540c2000c1140005402081d01004034607003006004459003500612050090002c004001081541c1c01580c0d680c6045900d074140da5030380d4201f44075803561900144030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 310930116 1250 310928866 310928897
    0x60207060b1e1003200f181207051005120a061701020c072315031f0e070320040b190f080c070305122829030102070c03121806 56
    0x400b211111740c081c081c1c03034180c1050780e0070402940100d001a005400220b661b001c0c4c1d10b000d00000d41070305816100b005200b581e08281d00d54950725801514400c204029401c4002d0b031007502501c80ca0340e0b10803820062030500022850041c0182c1c060f82c9051800074816115801c41402100c00c0e0054080007403407074501d00261070001c10b00c1b1075540c200401e90108181c050b17940d010782141c1c000000703500f101c0d9a41880741e0708040c0e80013070850b198030f07009188004210443e01c180320640d0105003410041200c8401220b030007659480402c0498400341e0104010a509200d20301801f4480c00300d89c0134000043c01d81d03200b56090107a098010000410010024107201841c070003512106109042642c140160700c1111701041000b281c09516540d20307588120715804d5608010140007007184001c0040c400554101c405814103200c161018420110808070191802d5044801c0e00303402017400c5112684a1526080500b030482c425400281c01740c5041e40360044008464003111410345648032980f10018 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 310931366 1250 310930116 310930121
    0x10110a09050405061311040b030702030a2601030308060415140102010501091b1d0a0e06210303060409051f020703120203072f060c03011a1303060207020d060207060b1e1003 76
    0x426243c0709031082c00b0028230055603a01442c005c03a400d4003d075845982141e8001c00c140d0200b2008200f1315040641d811008040e820041e05494051074285030b41e5452001050150807507600200b15442c8035a0000b0b040325000361030b1490600700340e00900c03a0780d81c1c5102141c140c4244c0510a004016002c2851454a0040342484c4000d0b6080444030000600798002514001148d0310008802030240700700300562502418245008030388100d00034061051110040e84c81c0030052280740600d66510000d814403404000c1349003850080c00c003940a00848212202c080e400c01c00d4210b000c01c111003081d680701013580c0256403184055a4681790300044080c0b00c540307a0800401700c106040d44889030107010200a00030548684400900c1e00c0d5294580304c09680200c91a440744510404140443c43c00703a1140d0b030408003200c0e0001c40140c0c0300c2c00240001601d0444041000b0006c0d440099000c007041141c1c0c0020b40300500440700080c80284d6403041e20350040d0701e0150300e81d210881d51045441c980c081d5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 310932616 1250 310931366 310931381
    0x30d0e01090909060f060801051608070e030604080a1e050315010507050a03350c030406061e06090b070f020d05122a010603030503040807030210110a090504050613 72
    0x1450500344082c0d80d036203080101d45110f8010350781140c540140030754101c800c0c0907050080c0880c2008002e40e00d01008590803030320300320441c2c9003000821004144007903c140010070340510000e080c0c8065007003030b00e01100c0c80e51001c0f19907804102103040c0c40c1c80c10041c0040805000d540750b207509155a03155840001864142d20005041c808103101c07a001140d02003006c0300c0d03198820703101c200e1484882d6031101c1a410100d000c0702103400300d950790f0040341c81100348261f801000c528001c5460303480c3c518103000506603036000021b0700140c0302221a805541c913000c4030221502500c1c0c6a803480e0329401c1000b400d221314100a0300d07450a80540b1401420b0248101c4e00702402002550240d0940c480c681b40c03243d00014803086800203107081054500003e00b0705800b00e0390031a000304503452540d80c01400f64013000704003414a0101161410a140c001d02c030001c1d14a8000400300002040232002c100c3c660021209a0001400f1210101c1e882c01c0c2885035500641004148a845400000c50031010f003207403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 310933866 1250 310932616 310932619
    0x302030a03032007110306010509060d03110a020415060e030d0e09130b150114190c05010b0a0f180606050414010c051501080f0607050f07021f0908011a030d0e 70
    0x4070700f4503420041168001d00b8001c2d1107040c00d2040108100101482c049040c0c00c11407041981b0f509004941d91200008044644c1c142444500d02d1a98222641840c205410103500076040400078902103d040c02c401041d24004d0b00c0c0c0c0040102c1e01c1d0140740d942d010444401001c1200b01c241d40802c3d00d408140182e104004003643d4403100c0403580e17013950a003010740d02c07540d140d4494007003401c2543e00b010034608507980090f1403500b400b001e50b454950140b103a8020740c0c240464180004288802034115010641026203038040480d1785441008210440344900d00004044040c5d000d4080b52900407003049424543c0e031113080a08000803501100030124085040c005240c02d560300056052041321100c1509687d090215031510702400d040042c085503218068205a00300400f041d0805c0a5503540282030f80700d140c030b4880600c040345105000540340c26006200041c581d1480380e21245c83c3c000d66141e80c0003440290911404000a1141c010301ca039455048030a00100c458807502040790342130300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 310935116 1250 310933866 310933901
    0x60f021603031b0c0f0f1a0304030c080706021204030e04090c0b0306031e10060b120703020f0c0319021e0606120102040e010f05010807050403020117060f060c01020403060e0303010302030a0303 85
    0x54681e84c11940e1100b60b4000180c401d60004200114010301c2c000c4001041020b0f0f1050205e03038250710020407844001d000806014100c41e00909000c01c4206807401c996000300b085658500200441e503040c1012681200010716039042403202e820103001e4200071a03070298a40305e4003401c0089124080d0001050150144504030b8003800c000d8032041c0c02800714000304090000003545030304d507400713541e000e81062903984410025851403180300311849034041494900140c8a01814007109154490200e1030b80c03840c4404203840c10001a440800e0b00321800e01d800300c0e00c0740c54400000c00420700018001540c9900103100181031403d005a007802443c407080001071074140c6491600d04403002c00c2c2c00210300c4141901043c00b095810045207600829141400c034106481c42d4002080d4402c6074004000e0014880003051940d1a0009140312460f00245540c0d104da0040c0240e9000f5000b03444203542090500e0000010309a011003109d0503a6009000b030a180c655a41b0283d024101d21081d8204620 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 310936366 1250 310935116 310935167
    0x903020a06090e0a0b36060607030f030e010f020f1b0d0203070803130c080d0f0302040f0302061303020907051809010509130309031a15101b11060c030301060f02160303 74
    0x6d00c015422404003050b0801c800d04004031800b58640030004280900481042180a005c25000941001982c0091078041707488102c403d0054054407868002d81086d0b4004500c903c0d007a8100405050b041441610140c180d990540209030b0b202c40300365050016070001c1081074007054030b0f800103692282501400103d428616998000e10f0010760303200384000c2e00598030b0a07444903400701c401c01440c1100d00e415800c0c5400d143da40030f5546114407000340b144900107400c0800c907c514034050010740c0c000f490304009207810400079280f90322809a000c083c8aa00b80358074201d180c040c41e220b05954016012452a87d141c0985865142190100303506001100030004005450350200648030000c180e10030402c0e052451181c00c0302c04000585500c2400c4d5180c030444103a80c00300c001c511034030b80b03400ba814404030103040081a0000400c0c441c2e030002000584540c50311400001503040764120303500d403481d0508400040341ca0705000c00320070f01c8160711000100301003407091440d50b0200c0c03c3d0002000005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 310937616 1250 310936366 310936399
    0x8091b15040506160219050306340e0102010e0106030c050910030c061805041b050307090906030609022704082110150207050604030b0a0e0703030903020a06090e0a0b 73
    0x540041c8803007003c4c80414003c1d0011820905000010412044c840441c80c5082000082c0c8590000b055211505942120300a0b02003003100701403410f0909c0d821003150b02040110003021146038801c0c0720b001d90300705062503540c2c0e001417043c4800c5036003028904044904117070403c0740b081400b8042140020f00d8003404408248580004401003442e42c03541e0700e0703450101d01070b41c0c0144c8075940720600c0360b45480035621f8034a518241d000080741c40c0c0c0c07a0143d5659102501541c1201c00d0b0340162221303515042c00131080200c2648114807981c0210307a5242c08640f51002039080c23502462002c1c94a65850300801e000460103000360090210102901005a106c07011644c098441240d41c044c0700ca1956104001034021681442104d24103403026000302d07401c100c003080e19842940700060411881000040b0b011115510203070a400c200410360381c44070b42d6414000c200380410300082c0d210320349185002815900a01001045554014800c603131a035402982a0082400284168000ca1180d080007000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 310938866 1250 310937616 310937629
    0x1020c030c0309010305160e0f13140a050a02030610030c0504030b0406021e0301051c2a06090f0510030b040b120d03060909020108180705030a0308010608091b150405 73
    0x1140d9900c0046440c0c50f4030400050541d0b00141c410b10301e90130880c0801e19403d030710080541a6510503038007900b280c280c070400b04a8110701202540c103410702d0440f0b8020740b40c40142c2540e006540040c001d010700d850340304c00350f400ca2200b2390b000742d0710103800c280e204c04080c00713504054035070b1003031b0300780603041950344d8840d01d501e56411a401c585071640050040d80210301160b2003025502c4030081281150704105c081226140a80308a0259105221314107041000180c4031144280003c0183c001c58150380440c03100d600e42c18004d0f0404507041c2000803501c94820a2010101d031001040c52402d003a42c24000d400900b6030034a0700b41c0150b05c03000c0e020550380380c0d4113800b07034050020b230010700035217000c00c0c5c0c0103084404907004500c0350b40c184050f000c0940c0c3c5c4805482d40055101014880da2452548500d03d0f191071984016003600034850300d0b80515401024460407109103803503003001d0b0f40e00c200050782c50b00304030701c8420380c2803840e500401d8003070408010025011400f810050300d0640c035072000400c0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 310940116 1250 310938866 310938877
    0x1e010e090307061d10050103080d02070203030c031b0607030b090f0c0915040603140c03041101020a14030703170712110c03070b040c051806061809161103040b09040b010201020c03 79
    0x72600c0e2194819030091038108a17020090352411000c0010b9411555445022310845035a070b6102900410090155901841100c620343c1c2c070703c405c9903541d43d40000c14031b4403038002200a8055003d2b80c030005140314000e014104600500808141e815a18004244a0010050001c0d20484c00501c12a0b04a85946031908450310090399a251190302c0d1160040c140c807400007582c1c0d40942580e0a204800c041e90003540d800c103521a650500440031200100d240c40c07038815003d0300c482c10314880802084004401041180e010742d50306903084a0303580c103003c0c0e80d031002d640350400a00110000325855070ba540c00740a11003500141e5901c1c0c00713040301c5120310b1074101c103000350340140c1010144000c10000c81070380b1009240541c3c01802d07001c0c1e124114402070400506050140c480024100003010703500e803003141c80400042c402056820004621011702601c401e0324004581480034035401520004142c4045417003e59009190818140912024080d000726076810356400f0f10410310032a109002420 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 310941366 1250 310940116 310940141
    0x50405130213020a020a0f1a1008010c1b0311011803080f06042009030c0d05150105060331020a0b03150103060506030402040b2808061e010e09030706 66
    0x191054860041040302c40038900d204141502c1004000d4039250081189500542c2208010014181904010300741a13480c1c0369107100d0140e03413000c0000c84500e503d490000c1c0d446d42e100800035550440300642c2c0041f00c141000b41c0b5100000c1411000907c41c40c207240000103e0000490180010440c040b580141e841044001c280d5810030000007107651259260b000d0400c85040c40307120b0700c181d101c0580e80e00c21188140c42c0c0c900020102e6058a0410000c680b100d4040d298200200503400d0090f145c000e101005810411400000140c501d0000c041d00e014101101d01c3d4030744202050031010b04c503c4620344a0000700c000d8840d03c40036940c2d404000c401042541c40050792071070b11505002c101c2c01e0311806107040c94605501405261111020f40703901507170580f030001d40070b00600b0000c0c00c03850341510710807200440c0050107500c1ca03d10f941607004031129002154802d032512510141d40a4807014491481c002034401003140f4041401019004144803007964903051983e2550015159205d00d0350 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 310942616 1250 310941366 310941391
    0x60d020309010e1234080d0e0a0609030807021b040b0f04051e01150f03050a0b030a060b04060e06060a0c140a060603020f0102031306050a17150901080d021207060204050405 76
    0x20300140700710b100303408800728486000c40b0003040c400170130b0390402c0c0c11900007404400010a8203c2600442e5014580e09140d1104881d14682c051400710007804044004030001150000800c8169000107200d641d0840e151f0601640e032103140050000034000c0044a95111b0207a008800c2c0300e441c7d84c86924092815459402c4031410200d8100d6224103040e406050b2602d149000030381081c0c7c0c000f0303c01045100901d004541625005110301c00340030084081589405149000002c0001d994020303179204400f0b44051200c25920038280c0810032003110380301c0e00300004002c2400e03954070501400c5086072050550040d2002404059460401002000c56a859441005000750300d01700c982c01859400920045203400c00c004200303054010244116428090082107191a40d8054107503452042c1d14007000011901c0c02550060900120501080c010342404001064034400030030075034a040d2441c0c00400300203442d0b080c0071030540e0001100f559001e90a00000c1110ba50f140074045c0501c43c6900c45 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 310943866 1250 310942616 310942627
    0xc130f090e0706021903051303120c050d020a021305090a1401050109060504020a020309040e19150c02030903030315040902090112060f020405010e280b0c0c0a05060d020309010e12 79
    0x3070a207030101e190001000e55004400280140080d15011104c85501d490003644801ca28010490415400d030401001e1101e4042400c80d610792050381714184c28041c508503212070000e080141e885014148000c0e4104bc41303240c5604004c100b68105507080082d4008948102200340c6503c445880c400340c072004181d465100400400715580240d0300035080840e0300b1031400040e468060768070310542142c24025603e5000300b0840b0007081c01844841030400c08028003502c1c0ea40352100c0b40802c030340c1050a00902e0000b9226080e84000305907148940c0140056145d900c0d440180308589050951403640140c55141c140c2c0140c80e900c010500a0021031025800107100f0b107171120a81e810b0b02c07010040107105100c208840daa01140c6455045800e44204401c2c00001c8042210000141c0010034140d510020002d9440d003410000c0c0f0f60746032220b0a40d1021426002041540190b0f4843e10f03038407103030a2001e1001c1c80026401107402c8454040000307a01c030148810303141003440741180c1d0700341c80300c0c01300701d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 310945116 1250 310943866 310943891
    0x3040e09030f0c0f0c060a0909050601030b0618030f060603070b2206120b010e09070c02060f03090a050708031306030507110a030905041401030b070507020a0905040f1211060c130f09 80
    0x41c4103807810106e0361241001c9203120000c00409140c4105801c240d1a03101203582c82e4081e03400320701d010700094441c41d610601c094884201c0c0c40d040903d20f009110b181061041d00038007168141c002c15004000d0a0b1003450b0034401881a0000381e510351745280303074142001040ca03000008034010f00090304c441f06482c645a101104075006005100e0500014608000c04c42e41c0f0341d034a0755803001c0241020001d000703842c000700b02c1c940507400c010118440e00006100407810006402c0c1e200c80d20860448002e2074591030f81c03e44901403d00c0d10040002c020340305008040c083c2d0012179003c802c5140a48010000ac00c0281c500310f2008000d402168000000b80020b082900a4495400c8852696080c47d49076542d0400500d200a040a00f00b00010400000315600c107807180c0010400040300b40315074107141c00d180a18803104071080783c3c58505a58088030040c040c0b84c1030b400307144004014140c81d5885400b036450ba070b48898499010529100c030041010503400b01408080c00d180e41d80022142001c06 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 310946366 1250 310945116 310945123
    0x150f180a061506030b010e15091c0b01080d080a0902130207150605030d2307050d0203040905060a050d03080406110c0703020319083114090105040c0203040e09030f0c0f 74
    0x1000041014242217025006982004649000590541e1040c601000d460800c03d07281c064145020350150b1000310f03c5c0880d82580d4200c90500340a003100c10b61b56641e41c040c0e26600c0e0700c10040c40000c01d98582c0000e20b045855481042120b0016091280d2007120102460482c0c0c00814222420740224003800841489032103401d001c2c010a40081031000704102d0068200fd040da0b03251044d40004000140e0f9600341d610582d07040c981d009040340c10702521a0f0300070b074407a0058069a4201d0f440c0800007480c626024645104a81e800340a0428010b42d58508441000005009950813900c416058040100c250014562134800718040c00c040c5045104240c10704d0301c15007103c10020200042c8401144040b02180c2c1c881485000783e0210b6000f40b8400f018003091716180300c112551b0000e0004600d02c1c0c101da20007060804803a50640d50313888104100440d1218a013400c0181d00510060016003030144805801550410441f410a18480d814101079800486440751b540c00c050100360303ea50042 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 310947616 1250 310946366 310946369
    0x905060a0e070f0e1c080906070f0f03031a0d0212011b170105040c020d12060f09021c060803030114010201090c0b0909180303060d060b0301050f18150f180a0615 71
    0x201c0e142403400714841005907088140c51710242c007484000441201c0381c6d446404468560343d00c00f00305101000c1034100380f00041c00e03041080d80071904042d0012583c101401038050504001030954034000096020310508102c580c404007000c0d940c5402142101c4a041001001036400ea9a038050043c48140c81c500d415070103903c013070b0285043c0f408904581d134004c90b00d10305c030b0760051800d080c904003d6425030303010340166030182400c600300c80b801203a02c0310b8640091444100d503040141c45e8040400b072440031a4028451006c075604140300501015007c040ca074011b421051001047d400d03000e0300c4503070a44c161a442400d82803800216071620382800c011203075208092a6094001032540148a5124480148a0362081c0240c000702410804654403000c0840030240080015180005003000300706c07026101140e00603100603100000d030100294103411f44a2042c2c81c850b103503c600305204071510014000e020704210307070304180d01d103050704004505180c0c1c0100e801040c03002d0305094245411109 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 310948866 1250 310947616 310947619
    0x2e05040c030506130e160807060306140108010e0601030902091006020f060702071203200c01031b0212070f05030a0f17040206120c04050303040f0503010b09040b010905060a0e070f0e 80
    0x41008000e0580d403960701c0c0740c0107a40141804185e240010103160700b460306040c1d10480c540c805a00104104c0400102c680a5900704e4130200034140e01c800d2015103901400c1007041c00555840014401d600b0340310821034000c1010704000c24503a400b82d000603103005080301c25040c3c090b4040b40400400d541004010550090400034207150f00741240025152120b03402810258003100416208251141103950501901e602503030041444405080361690030b5041d80600203400e01a420086443c02c896140d15110f0b960003c003070b0f6405a5440311764540240200b0b0310200c28110382880458020720040560b103009503100e090711007403800d024048d040d06511350803003001d9150800c0f0068403801c0480e641d80034110503030343d4103588200b49500103120b56084036415000c04100014002403e01e084820307074000720000e00c42000008203224031a40103c501501ea0b081326401008020215800290403440183c8020012034407165104603006064800d4000203009150006460740d10102200030404c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 310950116 1250 310948866 310948871
    0x3120c03110313020d0c08010902010923010c05070b0a020601030c0b03060d020d060b0a0b070b090d0806100c0215251220060406020712020a050d082e05040c03 70
    0xd01e0400d4201d01d01004004002d40e0b444440c180041d035840c441c0d403504450303101007041c41c01515008024041c192024049010544200e4040b410000801d508914400b241045054114070f4000444240300d1130f51007910b260140d180e02081c0e03520210028080c440c9160000c0229500d10319120b05002c0e8164080c0c46088002c1c400e0050756a02d1440d460051901140c090704000b0710b6007000d000509041220540c000101c03180010701e4514800a0180140583d48a115079034400c4072440c2c60310078103171100001036000300008040d4a445009401401311a282c14410100c1d0390740807400001c6c000c40c800c3d02904022545188200707014100109040d01107010000403046a070f41d101550340c0600c4032005105803000d074108680a062b4030642d13502c001d030b0100c405500302818004000d41c0007450544d5220246804200da00780000307043c103007891b440f80041c02004080030040325510800342c101c04414a182d40b94003200048400514100003481000346246450802084103c54540700c1180c00e260 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 310951366 1250 310950116 310950131
    0x5070f09060f0b0a0e030105010801230f0103290916090e1e03210403020f07270b030109031106060a05010c08090102010e0303040501020301050a120803280903120c03 73
    0x50b2448008084401882010b600d4082500068a1a041e0350762056095840c0c00f000080c1c00205400031102c100c440b2082000d0304401301c801e048010800c8840b100345009540041001648001d0300070742074031403445070350820143c0407980710f01000c043e82e4006480d80070900301c0c4178042d00d811001006180f000000c00030541100c2e912a118041403100512120645903440078510050048075041080405005c0300403209507030411703901c0f00c00d4500380c0061052120010001200040f194152000e0741c01c6400710904820076403001200b41c54262101c0c5c1c0d203c9a07005582e0b242406110710083c465115182b41c10074404015150040040c000f910460030040200926608112070010281d08002103550382c01000c4010b03405851802003405c600e20001013048140041940507505076141104c00c3d200280e55150100140c00884030050040141040424122454011081304140c103155002000c203180486541c111340d40c0c190140c2c0410b070341a006d14105040751046008420581c01c0c10405103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 310952616 1250 310951366 310951379
    0x50105031e0c090307030606290f030402031515030607030b0d110a0f060c050c0301020a0e0d050705060f0c1e1e01090605040c03061a09070f050d0905070f0906 70
    0x718403041c0590030311440c0c08030b4582850358003102d0403101e0140c21507400342d54928119005040754800c1c0c031101b02550242c44003203415541c84481003010180c0d0541800e0501d8607500c1c990380701900403a454403482d0195402c0940c4400303880d114868482044804140400c24035090240c01031080c0101407410f04c1c003842ca40d4490504880150704561030201b0615181d001c20518a016048004201041c1e0030024510f948800d03c450b905204000342e91102001c00c050500340e02422002e040070505500130242c80c0c0c1003551103041564007030000c0b075200c5643e81002c130303c0035031220280500c1240000303007100702040c08000e0011207a081c6400d2140c0c401c60394881307a80301c60148060680c10040b9080341c3c0c089080035040760507043c0c1c00c80300030001c600b00707841d01e688c2010321403100302ca0440c10501140003003c100c40c6030910090700982685403960701c2807030844200c521892141e003070240a0021007414402849040801e82c03103000101922418000c000d07940308020790002c180700741000e00c02d0103003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 310953866 1250 310952616 310952641
    0xb01180608070f140301090504050d030209060d09060b040c0f020f060613020a02030d050c0702010912030806090601120509010203100510050d1508030c1510030209040b0408070b0a050702060105010503 88
    0x1a4a0310300b590651200b0780080300c4d010b91072840404100c001000120f82009103500990060b88124111a000c1c440d4000035820780c000d408030154811002e101c0b9a08400280c0c01c81e90180b4810304000440401440004040f40c00c410b984000042c0002d0b090084c003030301046071138900080540100150b02c2d048c00020b1800c040a50032502d1960082081c01d00c1c20f000300b003600e0881000c00020300c010701e80080001c006801103441603001501c0c0b0800007485864a5501100141d01983c0b410120707982c50090149442e00500018104901c1001810300002c079481402c0c010b8081400140c1c5c0e07402d1640c4042110007a5400651050941d0408010aa5046412610300c44601349000c256000c60660007818030906900102040c04000303a1078120440c0499403400d0418100c000c40b50940b5a0054a85450303254003000f50845e200ea008a8081402c0e101b44030382c080e2242c0c65240c40d0212039542d20802290030354026445644070b5041c80b02c401e4060140c103014007070030300e002d0f030031071038120f040040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 310955116 1250 310953866 310953871
    0x605010812090f01090f0311180c0306220f0902040c030b01080a090507051003020309160f0b0f040306060308031e0408041e0b03090309040f020c060601081e01090b01180608 76
    0x403da1001031080556406a103448004010706160102000d64034281103031404a40000c2d24403d44952a6004880301c81c3d80940c3d0240c000c010101d070440d070f036000a01c1503045074503003082d4103800b0781e980c1c90000c1c194034060211100542d030700c0070031402403620501050301e600c2d08108051505180100025903448400c0d00da200d404400085550314031070a01c182032040542101d600102031a00030050503415400843c058071300c03503044645a501052012041000d00e0044284402d800d9504105a0240d60040e10b4594680e1821503d05580c07566858212000341c1e000f00c65401011080060541a48194051002035035070300c1002440d09540c0c1040e98441c5015a0103946070030224452600300080c0d014000e41201c03114240d4030f0511002c0c441d0f880d00400c1801d4429070400c0c80c0381d21070b410b40f80259039200d0580c40090006441d05401510440c0c030043c00803004826520709242c0351018070b1100d90081c03500c42170000c0d05160710400181503480c000d89204142d080940100080f5038481c08569 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 310956366 1250 310955116 310955119
    0x30705012a080304060515010804080a050d180c050102060f0708180316060b1e0a09020f070f0303050a180c03060c11011b26060d060f05090a060501081209 68
    0x3890700c25003400380241c40e020160103009000d0120030881044443c0d4089801381ca0840100d000411210004444446049070f004141c9c20040c0302d135052860007500684441c2c0c48080000c10040c4240745c5828030103151500558045240c08810001940c040c000306801614004170386049103400440a001b100c0007510240240149505c1e0f084600c00a00c03e440c040f00184280380c4c0505038508003003003c0c1500c03c440c948121401104034200d00208440381c1c0300d5510203410aa42507240000b0480290400f0302003a203410403c00000700015420140c954000b4820389000545092401c0a8022280ca0010b041094414410686c0c04103d0707885954080b00d07400305012030b100900071030072100092900c08503c925801e1440b078120840c0079160141002109a884482a184140704103e400800b065a40e4000904902141c11405c0c40a8086e81090182401041320288001208100c0b4004c5070303200040d03002055001c0800c185400303802d0044c00b92900074480b400352403d12164601c0359140c0d16 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 310957616 1250 310956366 310956407
    0xe01060801150f0e032d0106080606090601030b060a1805010507260f070c05131125140606090a0209010f03090c0314071a07230a05030408030408010b03070501 70
    0x89800d030f8070a10382200078440c045c041d500d08068400c03038590920b07181d04114146200c02d4940c2c4180c20342c14030a501c115000038009001503240c1005000c4140406000b41d8105512401001590744401d0010130300d03a40d1a03030301c02001c100c060b010814140225001141005410080c03000464041a204180003000f01001c42d04480411100c1900748035401803000382c684080740c444240007100414404407802901c5858010b4003900c2d01208481c040401400142010300c441400c4080c141d80340b6006802d11090700880d0190760b16181056580206441c003994855801c00c60a810b24801352500100c07135410540c00c10314071100103070100c405805440105030f90b640d035031024007401c0000341d401160030412a690102600c0503203a21007601c0c0c010340e044030306c00400404003111960700301c3e0002a0807140c1c80000a8000e5408513803035203101c24081e420700c03078084610086601400100b00410354440150b5960b8545281c031403d66130140ca1203071084e00580c004211503608296500048400d00d00030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 310958866 1250 310957616 310957637
    0x311090711060112150903081f120b04020f0901030b220c08072907030c0501140709060e0a0b0306010e030a0602040305030901110a03090e10080f03040e0106080115 72
    0x484007100c0520081510b40300c0e15000013500141c0f0802141142d0142d9804030486564070911000d07a0460007000700007490850020b42d08040710009458040c2c21403545070400c40c2d4030780b01d50103a10b4070340c0000d6540e00c2c02c0e04144411407518042d071842d01c510650b2410360382c2d851078441642c080001000407410700f8888580fa07410602d0780b41103c1e0002d51198215410301d8596540960300c40050244020303d0b0301a280c81802c1c0c0044524201c90f219a1b819040c3c034000b116a0112800820303910700325115034031100480721002d41a80f94511503045a61000340083c82c149004040d1104c2c10f44650080c02d00070011320802d00c150044a5001c002800d00c01d002c1c0d68087c2c0401d10301448032130060213152001c21f0110801c10007100038a00000c0981c1d40c079111a441d40003103511008811002004101114070401c022014801e405501080c201103174060303d0741c0d9800c2ca45c03c180101d52031501c1504001018004100754650503405040305103000075040d030405a0b181c00205203100b140041c005107609 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 310960116 1250 310958866 310958881
    0x90501090c020c06130b040b190c080d0c09270b1c02040c09030c1403070f060f0e0a1d04051203040302060c0d023105040b0d11180708070810031109 65
    0xc20092100c03001b215a51a034440f1440c602d504981100e010960140c0c068401240c89640c1d0044500c1d0415030080c80c04182000c540b00501c3c020030b49800f802180400013440c412084500ca81100000411007405804a01e41d80100c441441700144140308071480b41e0700440c0c81c138445010715581500c00050040c41401c050307484510551000304050031920b40850260801c101454444405800b26241c0c035444980c4c0e61601480380c007468000035aa999841c200c01c0c41070403444680301c0060580d00c0181d03160844c9852911609100c0b480041c182420700c810028208240c80a000c04100712504505160303400944079500540082090f1501240d881311081305541219400000700d40110004120001e1310b403005046a4000d400a00031580e0000e1641054041c100081074000d0a01170301010039500c00f805000108243c58100142e583c146c1c00c04810401c1c1103000d18420380f1103058600e0032120041000c40000d00c2c0d00c40c2d540c48107038100700094490341d114040d85021140d40e00c4a680d182c6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 310961366 1250 310960116 310960147
    0x311090409110d08071205280e0a0b09130e07182c060a05010602030409020708090306010602060417130b220e06010306060207120303020a0c1a01090501090c020c06 72
    0x2035400c3c0d440301100030001c2c200700905004204451240306e02082c031034607020060301c0c1e5010b80030b00d00b00c40b642d01100088c1844c103001c0b01541140001d0420075403805281c001701c0c14171092900b0034203410740300240c031250340c1c03600352101c142144c0c0b030140c140310314950311429540301e00d62841000d0602d03031840e841e081c0c2c9408a8211049800f100b041c0220542d11551203408600800d40010503580940c44c00b090280c2003a0150724141c801c99001545005e1800d411000250711074401035554040078800c040ba903680a101c02c1e802042554014102e81c02c00d030800b1483c480c040c2009074030601c810030520710440101c12411045416500702030352603940841c80d5165241440416508100010700041030400c03a0b0000203010310700a90f0200b01d0307240c580006a940d6422802440f11aa50041a0200082c030a070010b01040b550b41c50500104841e683d2061086c00e4541c01e641641d01441c0014000c0c803519100e454010901c01c0c1040c024080c01c1a0042e40ba5007400768581c0c00303401e000850f40c00803102d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 310962616 1250 310961366 310961393
    0xa2d3212070804270c1d150d0f0b01140a090302010503041410060e1014090603031b030918150405040503041703030a0506010c08191701240311090409 66
    0x441c40c0043c51440c6004c4003620f1a07010b070b203460303086103009240f03082180b02c0d484c0c80441003058650154400115020402c0204103058550240503003009200d500f0703c0540620780161407907010111b034041b00d00001425000d0481420070b0803200a00942c1030140e80110720201310703074080c01e210796644c0321814141001c0c5c0c2da0074607240c0103120711030440c00e0005843e4405000c551002d405440b41c0d468410842e100013110b8400c0c142580c40c100381c44001860080c48007500107100900316071604202c02c1d001e0220007004119038803030b50801300300c03c280360038110380900c100e200f280b140c07000514010f440b60340c40213900b80185000740d40c4c800c0000c04000c01001100c02401e2900348000740300006c00391055890740101c82244105042c01c01280d0594002d000507207681e944188a6418101e0000d502d040082030b44640030208401604000425503801c05058040d251201462151b407003100391141101c00c0365001401018a441c039840e8070a01380e042a54005c40c0c0444020820001c54105182d02a420 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 310963866 1250 310962616 310962629
    0xf0608090307060c18140f1f0e03030705011d0601050d0b010608040c051905010306080a02030601031203022205041409060a0c1707030b03060108060402030a2d3212070804 75
    0x140c2c2000c01c00c1444406d055030000c1084a4940240e5404400d0083c1044d00251200f602c5002241c1e081009010340b81400b40e8100c041d040700c6c00c1c100ca81d150282500d0384141c8203424a500704201c0c680f80e007001d000307060150505503450700201c08030b80d449014601c41480381408004850004c9400c00c00c0700c0c42020002d1000810401010413025103a0700b5600b614800c1502080c54a00b0001e46201c011603000f0301a500140504250303880e6459400b0300000427042401019400c01c4250034030030010103040700741410415180707141d0b808c1109100885602d8004200c0201c9004100110700c0d400092a50b0310055544001c1030340b2000150550b8141003104e5010400b21003c030800c14050362642c01480490000c80440783d05e40d90750421161200d000b514013035016046040a90301240341c8a049513100c80c003480c003480e407100d030180d580f207282e1045134000c686560700b01ea00d402d8008a0000b0031105c1c3d41150706000060001b1046290740d8080002000c0e501c9030340440e80205019a0a00f82d5006051 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 310965116 1250 310963866 310963907
    0xa15091a0421120203091306081507050c0303040c0e0606091e01030e0105010905071701140d11041a0a08010b01020606040c0e060304080a020d08060120010e0102070506010f0608090307060c 83
    0x3075924020b500c0742c006070070160040703034040c110900051f050f0017000304540c030003006041100d0740303c0301c4290704610083c04c0f0313028000104015200c41804000451180e40640104482c40c0d0a1070040c085204014000c60b114610030700c00b000700c0d0f83c0e401c0310011245162031881c01107203c041d00184c0242c40d4011000446502e00030000451600b02d40016214540340e541d038500e01d02200469031140e01c801e00505032004401c0c07000c4015402c2c44461174110500034104054000c0c61a0006001c0c8d480070442c105540404039400015810003141e8480900441300081c024800803600007940c40c00000c0c01c4520a40d150402c260420740a07080b14084940f0190005035a89003505100381300b07038811640400144500294054114441d0fa4540e0184005958224102d090101091040100411202201d5589450b55000200e0074401030075100c2c03007640a002c01d5850300102101c00400b551201c2c0c141f04011040004044011040b201840c0e130018000828a4100d90220703600008559000c04020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 310966366 1250 310965116 310965143
    0x4140304060315060206041205210412080124030b040b030a08070c1d010b070501060b0a170603070825080601060801180605100309110a15091a0421 65
    0x2540741c1c003c0e103160055001005001542c8420403a564541290b002d01140c00900086030001d00c903a00400b101c81c200100e43c3d51401c2c4103a0b1140e98030800b9903044485401c140019401d07540c102217450300400d541070b001c0c1d60b42c1c03010120502d20002104244130825590341d005003401d03541c560104103094805421115100c0e11407400440341d520895040e81c41d00c0c0c4203040059407884c0140c1070b401080c1a000e2a8140703920700003600489800c45a0201c400355202d2802151028515021b45420100c55a0341c0d1240c07410f640e50b41c00c500c1c0d009007916009030030482c0c0900c011000082c0d0076031b40302118100760404003075294980e880a8200c1d046808180141e40c00014450b601182e0181691406503038407949031f601c001b100c2c04a992502c1000d8000450300300d6801010f01a600c0080400d014080665854030f1840010310510305980150481601a0241d031b55040d034000c2c03503d400b800c2d003802d1010010400e100b408440c0e0142e4440c0803840d00c08070038040b1050303020821021086078007801442c17000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 310967616 1250 310966366 310966379
    0x80c06040b0708090a021807020307140601260307080c0f060f0f09010b03060f2208191403010902070c03050a050a061b050415022d10090206090904140304 68
    0x107100648030640003070319203c046a07a00714049562226142d00800d0410301c400d40000030310807100c0040c90681075020605c603250105000d40e20300c090000c14403015262540c106443c02d204401c0304800d9080d030407902d120010700d01c2e40c00021521402d8101108030349a8003110001480d01c1c0028de441c419900900003408010948200300b2406400d811440711800d03924000a6402c82d400d1155495040d4005000710700608a800c410fa6000814020680e404984003403100310300c08041f490440c0c1e04040066494101915079140f1103107000d46281071108000e0044250605000601846075150750008220007001404000ba00003581d1000035180c00b965282012916003109a50548038036061243c50010309a54407010754004080b0f4076400c1c1030a00700b008032008081740e0403840c1c0540c07203403142c40008000d00b1a14042d941c004e117a03901c030400140300390443c24078002c080c00c11502400e2480c01d00041e0741c1e2405454840c102911004a151b50350b0911080c07441084800d4110b03800005400300740d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 310968866 1250 310967616 310967633
    0x816030305120a06050a181d0a0303051906080601170708030d0e0109020913020406060f050d0f060506030f100605090f1002070906121e0b0f070504082d07080601050d080c0604 77
    0x8147d03030350740d0411503c1c0001c0c6c4041c541000d03102c440329954124515a200081c060ba002c00d801c03520840c0d404282100c0c030002d200c11900c00703030001076981d4090b83c010840c0c5900c00c44100800c1740c480780607102080ca030541c116070780c2c040c914044411684581c0d001c40741c86401d5210312001070b0010241b83d6036040804442c070f8070311300840b4280c0c0900c3c03d0032000f00781d0074010301507801c000d078580d503036903180c500310303022110051401c01080b0701c4503a00d590703000071141c0d50240514004c840c0c2c00c00c0d4900d00d04110802c0800301400da40800f0500000f07014a041e1903840000d041c40680003a035442d1089040014101d040208540012070f00901c0d0620114408a0401582184500c25111908564507080300c00342c000e9070090380105500c0d5244000365400e4a0070385081c1d0080c43c07504140341000c0d00c41800c9810300c0e91001d1826032101286000b266100440030540742104000c0018003440d80c2000d1500d500c0e010140141c9020b40c00e00c008000802c200141111013900c428000d9801a040519080700d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 310970116 1250 310968866 310968899
    0xa0e030a1119020f120c06030a1508070503030706020f0c2b230a050708120a0605091e0603030d020c0109050d0513150509100206010816030305120a06050a 68
    0x98911071100c4035080c42c070021180e07000180d00141a02442c066000c104a080c00078189050518003c8502080950319400d0107103009008204000c1540d00c801841040b0b0343e00709501c0000654044041040360751030100c105c80c001178100d000913036031304000190b804252003402400407051058100280817241d4084240c40c4514910b140c400d45100b1303901b02142c3c0402c4020007080d140d4001801b061090030301c04000e1107046030a090250824900d030b01c1c0d0555507040304264583d11700003481000340707044840c03140d1805440b0484403901070381013403007140784040d0000700240784901612022521a64003002580c85c507200b11142595900402d01ea0380c0d0190000c00c408031054443d0342d41401803107019000340d41d0002c0b5080321325040c440c5090008180360080f0000c072410304c9010890f071222610744035090049500180c00400c22545800c082500d4104414030b214112680c410050000035402401c840c2d00c0300021400d20b9040e210041260002d02c5194021a1300085410f8000f500d01f100035003900 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 310971223 1107 310970116 310970147
    0x12030a0228080402040b0904050c0f0406120f120201020c0a060b010e090115020609030a1b14010509160909120f09050406060c02190614030a0e030a 65
    0x540418114801000180e4000100020f5045c0783c0208801e42c001981e003409149030507103c45840d40c5644004512510b01c241c9441826541d580110300a49151120748500e402c1c9071801148241210b403040323880814030300102e00756500600c00c0c1c4841130301200c00781040000c44d44e650802003010700c040c281030010358960b40400d6181d45180750f010748140b401c41002c104030544041d01e400801030804580368800c11100714400c1c1d210ba50740d0002c90309003169003203030700051402e20240c11040070004c040d9841e01c01000450b15001510713004501c80b11009044003501d4100b041c0951740703407403000b5022005400710080341074814a0303500a08846880e140c50081c2c1c60b5030002e0103641c5a0341c010400156500c09420552070701902c2186005564076988803100d2400e030707019017840c030b0b082110f64800c00e000c000120341d0003940c0c00003004000c01e041942e03510b030000340c00540589204030a40703 = true := by decide +kernel

theorem cover : BRFrame.Cov 310791366 310971223 := by
  have h0 := BRFrame.cov_init 310791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 310791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 310791366 ≤ n) (h2 : n < 310971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
