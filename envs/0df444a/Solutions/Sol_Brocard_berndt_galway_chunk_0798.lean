-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0798
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:51:49.86621+00:00
-- url     : https://prove2.me/submissions/f785dec6-1888-4b6d-b8cc-a513f2c339bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 143345323 ≤ n < 143525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 143346573 1250 143345323 143345341
    0xc06050703080703291302120f0603150402010c0f140715030c09090b150301090c03050f0f04020d0c08120d0c030b130504020612070f0e010f0e0108040503040e180114 73
    0x40e480c4c002c800e05c070703d140c405600d0f50b18800d004540340300c00807040d5119240700050300c2400c10100c0300c40d9600c0d84080c000401a00e404200801c88401010800e44652665001158000c100c90070459070000c02003090300c04035042e21003200320642d24400500700c0360309040c4004801e00c0000502800d050500f9004205560052400300545032400c10014600080c000060302c1030100c81480814050b00000101d03114420743c006490004680d1400e201d952100c00281e240c080d0111801e0080c16200e8000c200103141070102c890955010300a1191a1502c0e075800d94200382d942178100204c4100010514070011060140a40042c1c0c41d007001c1046407041000300b00c640401c000602c950581e0303200020b0865443c641640e41c00e0010548080581c44d018001501c1c44c0200320321280401c504890245181d0320400000d0310f100303225a00c075a542c0c0003090056805da40041c104036080e0006000108528040d00081d92003014036424052503800c6200b062821108407144102058071800700700f000d019 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 143347823 1250 143346573 143346611
    0x50c030d2105100e011719170307090902030901020c0f0c09180f030f0c0c04110901050a0e040e010c0f080103050c120c04111b03250c030c06050703080703 68
    0xe241c10020415a6031010341c80510069600b0442c4410019000450441036008041c1c0400c0b050904541038150710300d0f59040a0910310340c0092601c9141c003080891409800051a0000003504000309000c0d03c80d80c04005907002101c84807410381d8041805124010104600044c2c0341100f4050300c03070030840e070010490788003005100290125403070140c843c801d48100712503000c1b11101d5007030340d0b1105811080c0071542ea05c102c802c0702c15403041c45038081d0341e49080e11501c0464141c0e11415441c0c0303031b074000054079141c008040540921890300000356060b121341c0500c006040189000041c6007850030170140c60842940e603a0070802040c040140001800010017015000088480c4141d9403100c048a03490441c0510426070440d0030880410060400b18024001c200540050f8035994100e107074016550740161284040406810030f201c02d0b850031103003c41c48449016455100c1c480b40c40e500d4a522020459101d1400144002240e10a15621501194001a407885d0500040c2e10400c1209110 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 143349073 1250 143347823 143347877
    0x15032903100506151315021c031824020c010527030322060e0708010b01030c05190c02190905060a050f010f02010e0106060e0a05100909050a0b0d050c030d 68
    0x1507280024001c403000004440d0310028840c184001c0c4400440c0c06c2d009455130011b2032030061752a00140e48206150080c054800032000c07500f0840d104010381d0b101c05400350703009036940700d04010264000403040305500052401c0210000049086c0c01c1c6480388020b010800c0b0034844558042c006455107280000c012250010741100b40d14004000d0040302c0e030380303240340c0c408014119488e0201d001c0e1007c00205403131040740c240a008000b100c458000540c1511429508036000a030b080002c00d8800b400400b1400050751540703080e58000700d10b5404a114802048640c8040e081010010002c080185c01100d1380504150b0300c034a1a1480d010120342c10095250649050050000459a40500c01d601c030600c1c4030003036002030003055992007018104c00e040b074000500941001c0c0003c101410141c1001402e400710759914101c9500d0501000000c01000e0318641c540c580b160b0800c0020b60b20341201c0f0301c402c0d000340e01505990aa407820075103051100c0f4210310601041100350f045440080d060840b40c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 143350323 1250 143349073 143349109
    0x41505030c0f0d020d020c0a0b011e030b0a090f03020601030c050a0b121b0301090605030709020301080607140d02030106080711011a0f0310060b090102060901021315032903100506 79
    0x3c070051075400801034010020313003900880c400f02e00d00c683c0c60000100e079052030f8050030304600c0c140d0300c600748828102104000e4140e9442c4850b03082000814411050b60721151220340000e0601c4c80ea5103415103007502d65820390040c0c3c8180014002c1c08500110f040062504907083c4103450310b801624010f0340100001c000c1203248080005030030050f4142610620190130302d0b103598075a101c06403000203003900e0207058007034032501d5008114004d0301d1007140d041e85c45034001000b0342d1380c81c600d0440c2c4200e0203c1c00c108000c10140703c8001c0000c4103001450181000d900e401401c2d142141b0f000740403141406201589a0400541440504c900c001907104020142c4840c025400c1107008245013003d450783c10480c2d5440c100000801c3c41c40b400280048800990944045441e06803446003070340115400e0350804440000c040000074940442c084e113186003410003040003040103440304185015654410440c05152810000510b01030002c2c120000e1040800c20450a0107804284165216204900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 143351573 1250 143350323 143350327
    0x20a0603091b1212020a0f050f0c030a0c03110a0812040e090115090b060903030f0301060305070f020d0e040f0f0603030201111305060906040f06030f0c0305131704050312041505030c0f 81
    0x1c0d417082c040c9405040c1c0180315030b551590685000782d520041c0309a011007a020700d03e00c01d0458680400c00a003480d030084a42c003034480c290b440b03113111900c42e1100e1a90103003440c000083e010506005400b03002c0002110a601c0c0d502d4400c10710f80c805c5c8020b041944c00c0c0d02d07141141c3d0b03401c0c8140d403001040c2c40203410b000032185039610100f0303810300c241400036616100100d071400003940110021811b03a0b115a40503c51516070802c2a240c010040c100c01015030405400807290500c00d44040054003002400490b0b132200d00d441c01c3e0122103008261b0195180c9801d414002d26809014a40443d5208c9140390702d40306034400d076400a26003501515100c1c0b40000b40540745542d91500f1741e000b07030555031094090150b031042c002c0d000742103a8112203030b101e040043d0244124024402c041c81090403241040660f00035540d42000321000d0310f181118200180000314241d10b041084407c8840c07840c0c9419552424034480502e182d488020600130041c00304100400e0f4444c1c81e003070310903102d41d40c54000c1d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 143352823 1250 143351573 143351603
    0x5061f050301060909110603040b01090507020a0804140f032103061816030b0405130f03020a05010c050406180605090d0c030807081209070e070c0609020a0603091b12 73
    0xaa42848250312032a850760070420089500c0001d58000c80c0030030f2040c401080c6810400d000c0c45194001140c0150414002800400284d007003034120591241d55031050341d0b84625183c1d9418101d40051700300d190042000700d040c410500b0407055404104c0000c41c002d00d252440564241d01c91200c01c151000e03c41f078048003054064440d103803240507440c01501818018944014041381c4449100841c0380081d0808010212a06080c400d080c01032036401c2c01940d0030669a190000442403500c01182188242c0b002d5001142081c0729107282c8001a5490580d65460101c2c01020714505240d001c000c481059410403001c2c1d001011951303e800103440e02c98410786d2600b800c15814200d548042c00d016800102242042491001040300707500b8800c9282c8251125581d481d03881035a4004c3d60200b844c0940801d0b0703024010142290214400c01d40420b10b1450780d4003207801c41e03440b0350011000c00d80701c90404042103624500345110344c511103040d005039860004460072440c40042c0151801c0034800301c01c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 143354073 1250 143352823 143352871
    0x9041e05030705070b0a080703110702010c240f0b04020405030715120c0216090e0a0204200d020706061a07030c0606150e03070803040f030803060a050d050109050105060a030506 78
    0xb0712500c681060565240030f9a8800c100f500354480c452901c00102080000748003c0c0c0244116019055444807642c20000a0f900540c0d1881c6c0c076103025946106080c08001c04101d94000c2c1c006c0b614982a008140e1141c0c0c8400d0b4819558840f2215218a0040c0020310642c0c40019902d070450f0500c040b1080504c0303400c030050b40c5070041070f10009001410a03035925641e5400042c3c030000c017190b50030070000142c0c7c0c8044100407541c10480c49030070b50b0050a103280c007601d001d800408242c1050302c00090102102800e0210713580c4600c2410900307503008550301051004900c1210014440b085081910188890386d4619078801c12200a00f031125210f0324406101c42c60380420054854581c070b000030410314400140c210120b000355988248504103011865541c003006590441703000101820203503056644c0e100e456040242103d80026410a0003c0c103542d0303401500c400540100c000013446146c0d41891825140d0041009000300e85008040000400005195500c82c0b410f10708011441c3c08801c0c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 143355323 1250 143354073 143354077
    0x160201080a0902060f0f0c1009121707081005030a06050406050c0f0d0e0c0a1212090503030418020c060711010507020303010608040303020703021518060a1802090a2a02060609041e0503 81
    0x105440c2c910546402123201000c42c0e000c40100e6001d10702d0985001c15044003103490340c0400081504000719400480d6080b4010341c40c10341c1006079a00601c207041e48800209141846a290a070354503a241e601384414810746205150708004042c0b10b05140042c20148a140c501c600020031801960300d00c00c40941050134001c0c0b10004200a01598803030b6550390b542c0d03140c0c0c80e0a0344180c401c1c0d444110b46040b40341c05200c22a04468015011f0340c02d01d40b40c11030503d40b4129600c06c205055400f001800755a40e07041c0821031050041e600c500340c030410f0150045085130f00081088003950b00030070043c0b1030a034000c1c81d6503500581c0741c0b401580d2212685012418050000008050100c2207400c1c82194240084400d1a08410800301c0d4a00e5a82100c00d00580b480c41d84d030f516a41304000200310150820206c066409200d000000c54451703e0504585171031041002a1154010216003102c512030341848065007044007100e104449003041c0e202d00841c1861070400504000125200404001d02802 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 143356573 1250 143355323 143355337
    0xf0a060312120c170619080607020105011d06090f0a020c010504050303060f2205041410020d0b030307020109150c0203100903080108030406050d05060a0803160201080a0902060f0f 79
    0x810107407110300c9860302401c0e10b030141d00c0103681e0606103d4200d24007403042101c101c0404035881c04280d2915610f092260001a102400700c01c110398100108441104000e114054005603000003042e61500c01a5607919074500c40c100401642c06050000342d0340c0303548140350094036041039105203450306030b03600b0024459041c50710303210350a050030002031060220180d44241402e1b180c100d0884045820410110118400e125440041c0203155100d600150300c400d41c028480d691061150b072032040c150389080c4000b800400c64907000030340007881400742d0066000d00c10095004606201056001074114003040c054290940f1280d0703441541d8a03c1101e4100c03003070360050281c071030210512507214081c01c0680340c181d001c42c00490000440100000071035088503e5580ca0382d041c5810725158202900016080c1d0340c0c041c006800200304503c0600041040c404c28030b030600d50b00349a034400502524002008203025a2900c81d40700050784880e4200c0d482000401881982d41c44c41c90703480ea101d80606a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 143357823 1250 143356573 143356583
    0x603031315110a06050402011b05030d0b032a1e010c02010309110d0305031b0705060c03060415062606010e0f040609230a0b0105090103150510021e0c01080f0a0603 72
    0x480e41c2c80c148001c1c0c1c0e0005e80a90700070b0303850442c40d44040f420190000f81c00c1e5001881caa004000c03168814a26038425880d0000003416a40179804400401c0030065001604c1c1c03002c00d60003441b1484034a031650020f510040e4106a00e446201c145c00080d1007204c00c100043d0600d80c8a074007070001c02c5000c1004c4454010010000304d459400780c180204140c004560881c09004080e40042c06c0d06440d00070760340341560002c0244455590308109208981000c2c0140380c220391240603000d884683e0024680140c002542c911301144161814006400600090fa4000c0c0301e50006110305640d01402031400c204090b5150038038200c1c010f02107801001558000400c55251010308282c18030f180c104405015418030705c041080d11010300e50011102d41c4840180070910410091280b54002e4101d40c15420660303001d40490390b91500440c910040d402039100c01030308410820308181e20444602d1024400c00c0b80203250486003000064840c181c00342208903100e0b02400007410f08105a088840515445 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 143359073 1250 143357823 143357833
    0x60308030903070201091d040f050a02060f070302010f0c08012d080d11030a0c120e10080117030310270f0b01030b0f030c040b011701120308060303131511 68
    0x3401c540c41e181d03080407808900241c0201000902502c0c0040810040040c5410102d101d0701d45503031701a52510a040126840c0c0103486500000d81d4031032000e041e04e000500c401d40d50b200107a150080c2111143d0094162642ca000703d03100d080365020b80b1543c1501c030390104801081d4480d69200d902c441c081c010009201c0c24400c4003050160001c107031502c05507895100c11032266126900591680a0702d4a001e0000e02600c803640c002ca01001c0311010b40070a41d080c42241101d51101044030781d0340c0d2100e014003080030300d4010014451003240104000032403c3c0514210b05001403032441541d082d11680c1c0c0c420000e90740d500202041d1441311140c4200061003041224026181c0c080a880c88894a80c04240b50034103007182d90618640d243c600a07001001342c035203c5000c00801c402014021407280c1080310b1003010030a8003003052000c41c06400c2c50312710940081c40529008155120081416000340c2040c01600d034690243e00c4503900b40c5458144812804d10050700807a910550b03010155000d02c21 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 143360323 1250 143359073 143359081
    0x1a1c0303050a0f11120c18130e01090f0c060504030503070206070c120303050702011a1f05130f05040c020a030206040b07050715050a0b0a05010203040303030b0f0a060809010c020d09061206030803 86
    0xa2034003c2c0a0038554044051055a0720141d681b06409181c0c03441407501207035103c0c10310074900740c028080c1d003080240c2c0003c0c0b400c01c2108900c1c01c50b40748040480e0500d4a102041c402c0c01a8081c503c801044186800391031f05041d070f07131801d4481c02101c3c4000c1c012940031039820304010750001f20801501032424000b10340d244a0500401511056a43e080554600202410320051148131300302d040802406410001d00e00d107280840c80b20450004c0d0003000414000180d00c004c081c0103040007001c81e04c4d070011066043c4010403084900344000c8205551201c0d0060b40020780101e5541e5005401400100190391a808240c0c2c0a110707542c40280031042032038500300070441c90f070702403400380020340800c111418100040c080202614041c0c5800b5038001c0c0030800009200380c101c02d18000004d0301c59150b0121401c00315a000c900c2c1d81118020483c1c61041014140d024410400840c21601c0142110911404083d0840001380100c400308480d05041081d412181c3d040354004560101d90140e4038a8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 143361573 1250 143360323 143360351
    0x140d02150309240103030c0b07020c0a080309040e010c0c0b07020f010c03061707030309230414070206100e01150201091505011401020a11010503040201090e01091a1c0303050a0f 78
    0xf1040c0b40000340c034800440e001c1d0f1850040300000e041e00d515845201b00b64903143c49815885c01e000b403c410451242200d0400d0316220104c03410010041c010055455001c0b207010001a031b00c10a1000b8510780c508003100036407540c400c0b03084582c244c0040701300900e40c40301203049042070914600509598208203070072010719070590040301222102211a4204146c2003c0075468454510000e030001d100000d0503c1002205854001c82240300e095a04905604070007140a030390180d060b0240d94040c1008200d1942d8040c403040d0307842060502d48020369424600050b1568030b0600806114040c85910004614003d49c0641d80482c0c01003101810342c103690031002c0c06403509004540d50b00300da5040442507540002010100d01d60f0044140d420302891f5030044659410046c810307030400403103801c00038103141407400030b9000c2c1c6840e06011034854030303015652403152a5001c0c0e850003000740d401d1180359060f00c000d0329000d10742c2c5468046400c0d1200306c9440c0281a06000780c4404624048000007400c2d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 143362823 1250 143361573 143361583
    0x60f040f180b0105070308071d27061504060305041a04060c020c01111b030a0b0103050f0d110a02010e01030b0301060e0a05070207050a1e0f0806060f030601140d02150309 75
    0x1001c09102032040140400044a49000f103540003804500b808010034034550040042c0c80c461021503001f9110700e00c0361800906952400482d481810301c440d405820341007108070030070f035214506480104040040701e201d203c040c4518031030541055900d00115040001840a03d000b00c0310881d036040c40c6052a080c070b04002c00300007401c10058454032441c1c40e441e500894040201c1504c00e40540306005070003114420039054803142d40e1b4140281301d0341800003120941c003d400307503000b040100580750904c1c0c60315250444500c0d10405010040c1c000340400340000404145480e42072900d4510146e030200140c000d4601402d400d6499420b048010031003907000303c5118412565020140000c0d11014400d980b03c0c4094014550810603071041800b000f000c1505803440100742a0721030540381ea42d01d183c0000c0040390780001171180c110406011081c0f4003031b91008085c01c0100c0c05003803103501d02200c0b0075419010740b03c128003414400b81c0340c81c25551020b4900c1c0003d20499402c9549150040c03400f5111 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 143364073 1250 143362823 143362859
    0x80c19080d0b010e06040e0903090d0b0a050702030304170d0906021c14010b0304080f0c03070b0403260a0e07050301090c030b01080c1e060c0a121d06030105060f040f 73
    0xc07902d0003103036900940c8910903e604120003d060f281ca06400c1615070a81250024070303006041c0300c10000314056840d10400c1d49203441c00b8076245442030820040550640d44003a0120742154424403d000124254084e800400700300c00c22101c1d03954852003003d0000e40b222000c050305051001c5a12542c2d07103080420030980c0d4107034540402099103400d03a00a0080000e000c1c030400c0141c2480040d0005142100074812258200800c40c10100700d2800c0074234503031284004440300c4c0d1001040c8010103030000c1100200e0100300f0410132070001c60841e80b9059840040c084180381d40c65188204482c0d0b02130041d10090302c40600280000034943c240522485010f02c4221030130600d03c030001803d200c001c00c840803882c800070070020b80e81c024408400c036055590444258440402c00c149040d038001005500e80d0540305a450212804050102401013000d030070a104444070803109150880da0341d50102d9054030005c0325120344841404501d03140b64002c2c3d80004144110140303000c03841d02c0700ca050101c06 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 143365323 1250 143364073 143364097
    0x90c0901030302100b011d0906150708090a0e041518060f0507080705040b09010c080904090b150d02010e0904170f0301030219050303030a0506270603100605010804080c1908 76
    0x281503500700046402aa036903d05440703a1001111f02081460314010349070700482c0081224107690101030344507140e5031064508444003100000c0b143c03614140451307410014444180003049528040d15200b10500501d00150300302503881e0962000030342d80010002c007442d040001000481c0e8510b501000400c001d954440100350800d0000781018804c00c12034050b50303c1c4001440c00d003c9943c0042d503104240e00c40854189a05106120366030300c0b60b2050000d00c0d4043c8000380d11a0910051116101c004111005c2c0561040d089400251b60414042d03696001c003618044190b81c0d66041c00084c5001404075074541d49000622050100340500103541620300885e0301c1c7c1008501040c040d824219079120b815090b400500010b54500352550200d9801080a001e008008012605103610305480c000d10254944107003013444041e05003000b0880094202410810040d402c020001e04030030310040c40101500d00000e03d024145500384860f02540318212205640051503103000070f5103400c00e62203d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 143366573 1250 143365323 143365331
    0x1021c0518030403020d030e03010b040216030807050313140a0b040f031101090b060405040609050118030905040b0616051515040c0201050c0a050c010207050d03091a010302130203090c090103030210 87
    0x403146070301100301d5040301e80c02090454501d105980903a00d8441103e5929815544c600715422981c68500060000b40e00c22a09001032282620340a080c1d5100030307206004000d828000c1059100e28030620901083e00502e0711800014806845850a103a07858010441510345007170204010490003000d544a200707840360300e00c80c2c0c2e8003080359080700c1400202410511000d404034125080076400650031501401021824002c2911454252004118141c5256011031040403d06078861401c50103070808030f40034070a080131000007030110301070008240d800000050b42001044001c000b40c00ca9044800803080b03851400074074030495250b09004040c000c80c2091724544c0d0f114810310419100c1e031480802c2c05c3c00c0901052080b40c40e5000700c80c0001d503540d0b00304a46800300e5810000c0c1600b0a600340c3d40411009003031b2404a070803060700c0301102c001c040c0080061005a44d01148030f900c98904180040e229922152114980b21a800e03240c0c6e0803c002800100504d6804244005489000f4800340 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 143367823 1250 143366573 143366611
    0xc0b0301170622030e04060b030a1107020604061808120904050c03071d19120611031902030411130c0201060f0806010b0309010204050303040b190302070b150301021c05 74
    0xc0d200c00d0219074104449800c1d24810445080d40710f0381e104900e0283c40e215038190001c0011408441003500900001d00020081240c2903141e401441e81c1d17034014110302e50400ca4142d0200d0024003c50082c00284155240031510038402950b0a400400c4140101c4208610147c010002607000b182c005005030700341400541c4110350030702242c2c003480955544441c00201c52a040079070408010b481a885040a04c841080d00c017000f0610000d0300d00c0c00c500041c0c0140344d140c150100d440c034105000311400280b040240701380700e45420003000300b0844809a40c0350394074a480c56681c070fa01016190b02c40301c80100c04951519a44c0080b4174542283c0003080009d45640c242107100e001480fa05030769912a100600801c1802c802540d00000c440c000541400d0f103a00009056400c19003040c5582c4101141c80303030510841041d034001800745030404615140d840e440343c0c4064400100390b8045c00c080f04801110684007581220403450660b1040320900c04070a94600240006413440801c2c0e410000c550 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 143369073 1250 143367823 143367869
    0x203030a0c0203120f0702042a020106170715050309011401080a03090e1303030e0102040504060b0a09061d040b030a0512430c0e0712050901060302031f090c0b0301 72
    0x1035017650b10708007486050010710fa080101802a2001f001109040c40c4000320007284404a4118404051740010a41030b05061100ba03040e54400360245056008800402598460880d5004180b03094905590381b5615000040d026113640e812078481c0341c80400002072042004102c100e242c601c030b595100040c0c5e0781c0d9070407005558015a4040304090300700c6640c0780000e029910440300001044009818980d85000244c103c90715540300d00c07005140000e45141c0e0f90b1740020aa0003500c02401c0001030741849011840020721958a4540110b55030800c00201c0c0d68104600c43d20160f024003201c40340070410815070b03002e0300410515014440d042240380094400954800c4800691882036000d011039a80e6803682e5040801044d109104e40315400300d40d0003035000d0b6107403150425480700e801c0c0080c0d490030704045a2005240041c0ba9240020910040e94046180e091604410600c500c50040540c50800189403c0e20018110522101d0009602044034040d45c12180d0914403403684035511143c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 143370323 1250 143369073 143369077
    0x41208120f06190b1c090b0108030405130606020604030f051902010c030c050405030a0605040807080a02160e06030a030f0228110102061e132301060b1e09010c0203030a0c020312 78
    0x60495840050100914008904105042c0c117402000301141c007170b005840361000060700ba006800c4580002034203200504000d001e050303640503500401c011540c0380140c02502e0b0303000584010300f000034002d4040040d601c92030640e202003100d041d08031805407a000002c0e00901356413000e600843d00748404100310340e0046041d9001c5030005006484052503030b940f2400200780040c01121440014044040445d02c02801742c00650801c1c0c000302407803800303050402038103215980044100d20015041110300d850201c0c1140307020b0350604200c84144014202079003010203021210700300c0701c016040e210103aa826002c0041d1f80d80510714000f4070391000b400490b00c0703031401c654109402d20528140b1414148240010394018415410b6003a4042c280c4e48541d410274480d40306120031078145103a82c105c0c81081c0700c1c5100400f40502c880b0301c0c146072596240b00b0030141e1018030101040214808415034011100b40000c035600500340c17075654056200142c9540081e038400c0c2d003c0d125403160500b0032106102 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 143371573 1250 143370323 143370329
    0x70905040c120c020f07030b0103030905040605031b0f0d1b09020309070b0a0302090d03080f0f011505090406030503040b03040b01050301060302010905062d250206041208120f0619 79
    0x141e01441c4111040641e000f600000400c5802c40c0f00b52255044848001d11048003e140700302000d00d000d51640c1002000d200c41c0d904001d108500d0910304000700ea4000030000d0100204511000904400d03c00044039064503078031550300502105404400c000b0402407680b08050f0b0b4075041c042c1e150301c0e400c3c40b03404c90000301c0e12012607070310200c02808200c412801400a1038540d03d405450150108040350040d21081c4080300400c044806010007a60441e6085500903401d414001b1150715010f601400c40c002c001e440018028000b5015120b40c442c2d0300710001030341e000421291390303e560748000e01050740111801c0d01c040d4090310003c52107281c1030240304112a0142c2d84c9024103030030141005002c1c1c0c804e01e480b82040c241d44000101c185180d1041e861181c01010305d854071011203141d4812069165208110034a075031440d001c0043e641c100c00d603000d45040f10100300c420300c514508004640326080444800000c45800c00078102d00710890a4443c040581c4d003c00e0000f001580064040c417540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 143372823 1250 143371573 143371577
    0x906030b0906150d08040906090c11060411040902040e030a0c210207030204051503010c020d0e0f130b270601140a080103060b010c0212010203091608070b0d020d02030f070905040c 79
    0x9046081a24041c0c040520311350141e9050343c6001d81d61544242203940c154004280346c0c3d240c028480c0b10300d4016801409414500d000362113607242075039881482240d182c0c482846290350300e5605040d5180d980c0702e112a00c09640c1220755524401c00e02520174041804101c0c0c141400023005404070101c045101681c1402c1d4000b07142c3e00c0d05650800000d8480245a140811110900c80a01c0d80d000d0140490001c1e003038014090f5010840c0c0028101041d010842d03010300300b00e20300700e1b0030341c0c940c2ca00ca40e00d4200011000540c0000390340015000c00041c0300b804113a00010040c00c8540660390000c54003070007098881c40c1f000700407040c2110b01401001d0b81c0d200402ea443c0e004101140140e00607203058281490010380544555001500790980740954003c2694084100042c9000030410005980700c00d483c0300510514112100b561960350f40a02c8070641c102085284270100725030161540c0c00100b40d005d40d00d03480c049441900143c030440b20400055800e1000161508051190001d088055 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 143374073 1250 143372823 143372851
    0x10061a0301051309051c0801060509010503040f050102070b0c030a0c0306151d1809060901110a030905010b1c02010e060c0d1b0b01031b08032814040906030b0906 71
    0x4034040294580100c0901d440f55134075030458a00186040c86007038215419807000901c070b6a4140c0b4001c003442016081360042c0f100c20401c0e0151a82c01009481e807181c1e014a58449000c1c46180045c06400340d07420003091038003400c051090760801c000107148107514006040102d0754000804034261502d134441c0603e000720010366001120701c03900e000e450410a4103401c803d0b0140010228008003074a00505c5d1a82e03d60f00144000c03684144031186e0403c980c0c40080c00740c550442296002441480c09030703802c0c517680300c0c402010000d081d002407141450080451500c080500c0241d0f8924050803000c90008001441e031103d203161071401d880411101e0710041080e03182280c0f080e101c42d18a29406c030404220300305280c0000b21185e485502851080189280c950806551195000e03181e410660580d082070245621044508024a00500361900c003c0e1168100035400d440c80384541d0f1440084400004002c03e01c901190411002c4038494203540e00365030340e0210306689070041540e48040038890 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 143375323 1250 143374073 143374079
    0xb04050c0a050903011508010b011209050606060a031103041a3301140708071e1703061903030201150605030103080f250f03110f0c13060e0910061a0301 67
    0x2160001d403c1c00394000d4000600e0700702059030341005000581c04036980740c1d111a00b03540556404045c003034007920b51100c1408401c01c06e580e825155070004014500590002c65504c0185203e6003004c1c0342c1f0040c00c0d107415600c0c1024209481d07a5039110b1103a200400820002c18180202094410092400318405541f00021028081c05031540d558205040010020034005104207080c01402c925200361289a50340900745004c4a00d0b02c8400800d90901001340003140200d00c526034811141c541240c0555502d43e04d0000195400c01c3d04c00007410000c490300710110405405500c140401c130140c00003a010a03950ba40119042e2009010003080c003a000c4c826442c3e829100350141007902404c0015401d10800504021140c2c00b86460030b4441144048038503050642102c0c1b0084801e400801401c0011100003040341d84800079425180210350782104000342c400030f03030701141c0681141c0d40304260341e0800000c21a40c0340a42140c441916180520008400608806401036140c07000442d60a5030720f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 143376573 1250 143375323 143375327
    0x6090e01170d181d15060313110a030b1f0b0901051606020f030c07110108040203210d02130f210308130206040e18010e0a0f020a090509070305010b04050c0a 69
    0x381c81e9500040f24280301404242c01c0307030a95102c42c9003900ea0080c11914030b02103403102a00c2841030391040c0580030410510000c00b4000d1a4403e180d5001641114400d0340740004c250000d12982c0082c050b401c1c00000c1c062081440000c0d16005040042d41800941d00e4038070064062060280f6135000caa000c10030340030340c2101c0c11031035400b0301d0003131400600705802ca005400047d407003103071180f5070b41c000040d508040019401003076104540030300e041c0c80301e45819800f080c0c1d107200f00030034145a000c10380c801c0324250070041d040f526201010442591150100c01021103422241e0145510360803000901044c011005400104070995015952071108016181070368040c0c00a8030009040d0f86108408025854990082c00204080490000e1038034202d00880c0070700c0c08106200f1400c1c1d04080040124140c002840040181c2049a07520100140c2c40001c800280c01d51000d0000b0341040d04101c140e40000c90314504490040c8028071110b60842d00300401c64408860031410aa000d0108028240c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 143377823 1250 143376573 143376587
    0x315030605100e04030903051002040e1909080a0e01110a0206030408130306020f03040b1b040501050f0c012f040b0414060d0920030312010504022206090e01170d 71
    0x1e8440c08881841c1500e030004045020f408031070645c0400d242100c10030420004000b00c40484410100031800c0500b09141c00c0c3e00c440780503150b01e00d50000303400c400c80c0d112003036403060325481e5010705220380e0380f90044006000040d803807520038081400c5c1414080880c0700814610440e90b0b0041c04949103035101da0745e0b1907046e001102c4400c02e00405050100000328035200900c003442448400944902d8107252400c1903a070000c0901d841c1c910081c14141401404005403801d07503600342001034441454041d90780c1940141341c1000025030803e2000426046001c003014600000e000d10022300f13143c121070a450030700c100e02c6500c550420400c0308100c0b00c02026510010f2100c018007080c5088419000501a27400300d200c10f455001c1d03d0491241c1b01a900417144160a105401943c203103400310101c40ca00c2c8005101d12402190002489511302c0160250701c40c4c080d10401c61884090380301c58008102e4071003400b0300501d000080001080000d042c015030b140d082100b0008084282402c4011a494 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 143379073 1250 143377823 143377831
    0x14070e01050f1e04150e010603050f070201021905090f150903010c110714011704110f010201180803040201170403031a090f06150c0d02100f0b0d0b090a0b1e070315030605 75
    0x203070030034143c00303d46c902c0c0c00d4a8490013400b00c4d980200d4542002c10341c41f04103c60180549041da803041000200c2c4802e181000c3c094604141405e9448101c000c0114101171032800d40681d01c9603403109020700c500103070740c0580414a0203400801040d10b00f400156580440949000e019074031500c810810403001c0d003240040401c0600d441c400f41a035010300c80030514006e40781210b42500d4007194480c40d05040b2015001d034030007440244290005a4285d400c00a85034401070419100040040c0c1964051000c41402950710801d050301c45c0b500d03040c003c00a1542c2100040000b9604030003000714a03020300041e00a001c815a00c06442d180c9900300010040c995407070000408083c80440d032540d401744000c600e0b6810b2074018091002d030f402045001c4400724081d083c03c4034686850280700c4d0700c07141e000c0315002d42d100600d90141d48032502d02520b0481004401402d1444000c10000121100c111520000c501a01c400c560360312010020740079035075074480110040040d1502000400c200703030416a04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 143380323 1250 143379073 143379101
    0x6070b0a0603140f010b0a23042a0e0103020708030a09051015060210050702070b070812040c09150503060c0f0d090807020a0e150d14070e01050f1e04 66
    0x3101d035580d5108014460110503c42283c0c00240f6000080f050030b000d40c13a600101150302d0200c00c1d041c030307500f048080d18074000c0d5200003211110701010780d04ea50340a03604d41414003014200303d8030b80b8a41d00043d0440540303040c00044105a81c900a540a4025586811303404011641113503079a4904800400003c1000e0b19148501d81c42211080c16600c0341c1c1900307181f071450140c2d025041140191403c10b00c41b0a1003841490441000003035580443c085040d83e84462078217a481c1e10a0a2003410390041c200e500311034a1003002800204983c11171600102d9880ca24140100f1020b80d10401034610b5500c110358054001c003002815080300100245089071a5028203410040d02c000100100c42c11500100d0b4400c0002a00805526084070084014650300b1229501031428080807449018005d28250003502090f20340b00801030050a5062031940450484080a0351130402c028214000c1c03107524042d03c041800790165040096018120340e040508401c0071001140c188001400404c20500c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 143381573 1250 143380323 143380331
    0x809010b12031306020c092a03010e01050a06031a060f0c0307051e0712020603070c050f061b040b030606090d02030d020d020c091302040c1b290606070b0a 68
    0x801669490a488010010308005540f01c5032083d07900440e072611a00f00c103056601408840c907a964034400041d0348082c01c03495405403051064600c040c120440304907600c003031002000202e0229010b1003880d0490710100c1c5c0006031103a0384c1605500702c65114410f40d85c1c58060701c0300302150f81010001089104844031a0394500b032461207003142507804c8070100b10350540042c860300c42c2e8580c2d00e0303a017000c60480407809400314914100c50001100003858000380078400c0400020401c80c05400c034128029003080c21760342d000051540322503c0c2c00301155010b101609140c00540041000025203055581074542c1a00e16241d4a082100b07d4000d00c3c10594452040196280180c500340559030502005030000c0c1118082514084d00f000308416859004418120400c9038100c03411030b0f48e4260726015a0001780c180615201250312195605028140b90440d1054200b008207006c102c7c44801da402500154003a5082810000c0c00019030f800c6a00072828450f400210360300340d81c1035401c02d0301114001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 143382823 1250 143381573 143381591
    0x403120810090e011a12030412030203070b04060b0108070306060509060304080f0a08040c150503040201080a0e0106080c1206010f05010f030e0a03080402040c032007032007060f02120901080901 85
    0x280035a0304008000e0f4071651520030550794040380401100b15100c0c22a6684035010084107403640d24041ca1241d41600781b2040204000c0c14020310850701d40c0f9410808141c080c0c0f03010704100000e44198005140000c08203000904001d10a11414056400d03e64034607103440d4030f0804206640c2c002074020b82e107107141040300001c0d80b211800103207418038158495100358a41402e20140c0100036a003c002152400985052007075841303c00c40343e00940c2400d041200f9100d050150b4010609905210100e610740040414243c0b03000541107070006007148c0014444402100d91602d681c000c0c4529540b008070384030180501d6004003211a11424603107400034020b80700c00360181c1340c58007501c2c090b008107042c84180029400c10340038130450480541400e1141ca030000303010800c070341c81810030207100c00b101041041c200340c070038a01c108010b0f019a420a1440040b034604e00e4803003d85100c1d0a01095141004180103070000c1032521701e405403600e11074280b510f80d42c01034482d100c0c0284400c146568550b061 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 143384073 1250 143382823 143382839
    0x3070c0302031210150207080c0625061d03131203020f060709050a0b130b030915040b101707051302040b0304030e0405130b06100309050607020609070b0403120810 72
    0x2481510030301c0c900c6044c6458072414044850650244000315000702c0710034016000d000030440102d60741a1411952401c0c0c01c0345215202c00310b5a60040c2d08800100c3e820144190364000d0303207210f07401750300402c9640c0500c81590340d6482650312942e0204040d160400a005c981c8100a200324068016a030201d103030200500c0c10400103d5140e408540c00050922984c02c0005035503001c2e104440c4510301d80354280d003a28012540612403a9144000000081d802480a00620a00060025034003900341802d01d00f440a0003401c6a542480000f4070000250020080c0f4042800403640c80190000904001c14055070781c80c840e01644455408010004038440791100444c4924040d568a00d0020000410401914000b030004420146900c2c002000300d04561a49074108a0071502c2d014404001401030303029110203032015240b400340404001c07060b600810308501c682032001c05d03601c049441d40c058017550b000f01d002c0a4211015071408800c980d000300c0009401058042c405103819036210742c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 143385323 1250 143384073 143384107
    0x2010314010806090715020613060609090503120604150e1005120c01170106050d02070f06060303110d0c030e010806011709010f0e0f1f06050415060e0409020603070c030203 76
    0xc40da02d60781c4040c0070000440428003444024080555100c99a4008508021341e1494080c0204241a8020481208010042d0710400051014a60500c010003003410f200b6280d811400e581c5c0501b007014400910289407600c10000d03100b0103000a2200142006e01880d12114018480540e9074101d08010905645201030100c2041c0ca040007880c81482c11400100011011031805044001c550010f0100b541c100c01a1101004405030040e11400d039410710041c000c610203809400d041c0b0301207010040c554000d034021a190818400c0354803000c0c0c0d000003182d0480d00b060015001170425009035500307622a1114a4101c4014580305808075084442556850303001d540c4441b00d40e6656147c0100444a03000340d083c14007450015004440351303002c0094440d05204848680019802d65080e0b92050942c880c00145ca4007810800039802c0c0128412280811801a1004a10004d00d148503d142600401c003c0d43d40c007030205410354481e8038055481910b805021010b5001c1400440c0f005040150 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 143386573 1250 143385323 143385329
    0x3020d0614041a010e01050d2004080708060c03010501030b0612072001050408070f17041203081609030602030c120a02090a0e0103051f0f180203010605041e090201031401 75
    0x40c00034220104000441d81c1c003c1000c080802c20039958655a85c20001322094100c0a09110f03039120032461100c00180000400c404240a002d05c0e001d11084008000d007080e00c0c1c503042140c0c0450745a01610ba0341d008200c4549440f80e400300300600880d44071350096158054090025802c1c045221038020020000b110b0090015103040743c0b044451140000003003211040d10300800c564140f5803103c0026119010015200364014143c0b401088000c400541c841d19a074200d50703440e00d0305c0b001c072001344406061003070f00001c0c01440803842c0344001d000f49810500c619102c4585442c41c5648410194200508600c403504080c44085140f225601c1303840d00c41d106c90030006a580d00410100442c5008540160803100c0d0360000500002d03a00180309040b030301c030f0188140c0e00301d901c1405043c060304040741c080c4203050600b00300806414070b0030584500c0302d100710000c1c080da507290010700c0111b0380e4030b00c0116090b029004010200d04a61340c04042070724010314010840341e071102a4132000500c20780c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 143387823 1250 143386573 143386589
    0x60c060a05150d020d0203070819020301050703020306030303161b0c05040e030309030313051608011506030203070e0103090c0e0103081c020a1d0111120408070f03050706050a03020d06 81
    0x8020019410500e00c07406502c612180a50b0745000491004035400006004009010b00c8a03800403200b50341e000c110110050030204116900b2200e1140581d0705180003ca08a000b50b091001044903035000c0c1c0207481c801e410180003542183d0381e81150b5409248101c90413003c1c000004141061070b110043c900d0329050060107103a0503546001c1c2404102e030302022130b41005230010f0050200e120030110031681c2098503841f40d416542940e06004e41080c403408102d5184100f4007a00145009040d00a151080510b2102c425582d9641006170142e2008030307000000030301c4000700c171281c82d800707036200308060b9018024084086403201400e60382c1c40c400303810030344e02d1020202e02d000c8503070031012002c5a1000f4a0381d0544c00c010341c0042c042c0c00308002c030015401d8180100f020046603481940c0a81c880715032841254865400c041041c00c80c1c2d88180115201809603280103d088541c00d4003500440350700c10000c01c900c41c500007080320250880118042016020030008011598a001e6600a40000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 143389073 1250 143387823 143387833
    0x415020d080621010203130c09020406020307080c010204080307031205130203070b180d260708070f020105160803010f240f120e1b010305090c01031e02040824040b0a0207060902060c 80
    0x9400d10306000a01275201c4103034280104010300c18580e020042d900c0d02a40100035588035a8032440c950b02a0103190014021840045114800d15601c041c07000385123610500c04201d00e4460a000c01c12107022808082d4150303005e04410400c8465481c0105417800000c1a41440340004c000040c628464296058950b400e01c150f042501c0d10004001c03d64880043c0b404034038101c903d0341c6510356070160010141031028082c1c044000c1d640680c04441c400d5071103017000508040103190940d0760360028014038610b01e2045c500800c541500d8018003030451003602c05420311000c220011900402918102810800c80c2d06041c2807400080c001d5403201c2030360070302401d50800e912071612401181041007e0400d4180814031581032030202c4c400381d01075820f180100f48603a09000000c54291394144040c001880040d001543d80380100d1124024440303a4180080465a2216a9aa848107a83c00f0300189101c80100383d0260030740d40240030072840b644012444491a400013019508000d0b5420041d400c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 143390323 1250 143389073 143389111
    0xe06060109270902060c0115140d030e04050a111612030204030f06330e07050f180a031502030603060603210f07060e030415020d080621010203 63
    0x20218800b402601007000c1400c6070a00c241880c455208841920340355444a8000035902e4503411142d02100640090200e04400034103c010207080b07114075030418030f0031301c0f10980034500309621b00c020342e8051355030b4080107140c0c20402c0010030014145085041da02e100c0c8101c40010200608007d2425068280b000c40c04c038240014145284405070041510400c014400903024943c602510740c0c02c4440001e1000024460b0340d101c5100c42c0c0c0c0c0d0500e010351040b40c822685001e089000c01d071000160003c00c5511015170580e181c1c000c030824007003000c03001d010780c401549483d0b0646150000c02048070b040b0a81c1c0340ca40c050001220381001c2c0103181c0010030401641010449c542c0c000009800405000c054180314854038100c103040b20394010400100e200301c401f00c0340f06465074250004410801ca44282c003140b42d0303e40c0103100712224800c2c4c045400d81094004142003c100085490318466a604c82c82003011100d070f01030326121011000305c0030f24214502480031394810722603c404005081131b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 143391573 1250 143390323 143390327
    0x406030b15100f1d040e010603050c03060138070609120c0803070f05131d07080903030708060301090b0109060810091a04030c0b130314090d030503060a0503010e060601 74
    0x40d603103019904071441e0342d54007980a589001110110b00d0302141d0300ca02001c0c59402a04a52001071788241481c0344000011810740c4030303004a034810001c032650071501c4000d041e03c0c1d07142407049858003642c040450000704041b51801c2d4001c04030403440c8001c00e03583d00501d00680c2015905440f6103503210307804810484900c0007a0280b0700c140c1000804200b044e500c10000c0d1000074107900412110904006180740144152200308140c00f01d810025501c6e45409100011000952427200500c480440d1a00740151030450164414030040c52460340c03526800e0b81c0e103a41c050001a0599a075060700c4c0042802c840106001c0c181c508004980203140c0541b40349441c000348030401e585c51418100b64000b0b03c410000002650b807e25220300681d8441c181070343c2c08864003c015182d003d0500030403d9541d0074000e6001c03840e12940f20f460710541d115100100c280641039101d42c00503010000321020a01441c059a80004010400c0040d6600c0c0d01c04242565050030740c6515540c00941800815a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 143392823 1250 143391573 143391601
    0x203070b07210921030b030304030813050a1202010318081b0d02121206011e050903060c040605070605041401060b1e0306010819061502030a090608010501020d030506030c0406030b 79
    0x16902103018005800c0a454080c146070040149490a4070138070007070800c4138081d80003400200c0b402000d480d140c555a0a001031070341e2100c0800914644800004940b610300911018191200000c4580d02240231f40c0c010340040c00c064072980c5490a8140c2d40070001441d500041038072842103611041c408901e4044103162610180c0e1413020354128140d4008400c0511054504641404100b540302e911568016181c0400407015a4070400c605d000a40090b5002401030141d50403e50444055548041c840481405030b400f50b0000220f08010708404100c140e000380390030074011880000d50b01c0600c00812300710303061584030308107400003c02e0781c4048605140b10341c000c00201000261440c5044000213100c440000c203500305000302c0c820b5101c0c0c1c0385002d074411300103864208450480000a0749001e5070700d40000c1000350004450650100e5004d10854440f0b0488406030000c11007490280f0741a0050700d0000c1803030360544221070f820040383d40c443c010800190b0281e0f50244441c1011340f0400300c0e031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 143394073 1250 143392823 143392877
    0x1030f0201030606030501060c0b06061e03040b130b040305030a0b031006050901120c0605030a020706021305030d1e050705150703140f04050a0f1104050903130f050f0f010203070b07 80
    0x1c11b1604004000d12600894200301c80ca500901c0460076603074140000d049070180d20340d40c1c4614130048254801402c9038000650142c0c1c000c032400c07241c6a0391402450001e00315031034010324620607000031600080c0680041c580062041e500421071a00083c0404e291186050b41e01c03141c1a15007404001606000074074a01425030b141140e0174a480d56100c40c94219603d104600801c0000400905500155815a015503074040400e65541c61400c40b40d2a140031140070b06442802140306010440c2d001d051100c0c042d080e44070503d00310342500b080c00e0300d50b42c005050995480c051001043c4c0048000200c41d8480d91141d00c0c0014005002c010044101e00024004100c02a030881480042100000c550132490391019540342c8040241c40c0030218101c401180c59042070404080c004004000320282010414410507002c0281d65484418028a110b01c119900088204c1819440c1e0908450117095601d040c011a894221a0341e1819450300086484a002610104c5c56020b00c0e20a80e103c6002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 143395323 1250 143394073 143394077
    0x507090f0b030a020d03050f0c03090a0501030b030c1005070206040806010f0803040303020c0d0218040609060b010e18060301060314030910050406121d07140906030d02070314010b060301030f0201030606 89
    0x14400c1d1038042a9580740c1144040c0c8a0608500b068040520074800c40c0d03071100d10300d2541c50325039007a482c00e40e5490708000700c15031042c114400e022503954440e00c0381c05441c001c01070080810b1400d05040c4915030b40041844020418204000000350315880024401028404000c024a615010700c0c514000101e030050107158100300004c0001c6580010f80e01c100d032408451902c036403503031480014480743c2420002d909052a9808000502220740d110841403405010148501c030000c000440707202c0a00c180c6071f5800595406140e441003d507100d9140d015030b000e0000581c00d0346a4036101d002c1000ea5040d510342d68800665000390303043c4121003210b807030070034100603050505041002d40301a10103400d911540e644c50007040f210010b202c10903110f0780001e00940d80c030142c550700c003a43e21410f180700035030089460801003038107410000b600c00210784d6241c5c09000c9071425580c80c81014107601d201c011566403034030107003000b41c0d0b00e0b80c0c0114000d40c071400c6110183c20082c13001400b643e81d65840101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 143396573 1250 143395323 143395331
    0xa050105090307050d03050601030609060b0901121107080c0a050102070b090c0405010e071107090c090611150c07050a02033307081b04090f05010f090603050d0305220507090f 77
    0x10004000042c80c0c5d84511441c240411260384a0300102e0007003402d5484401140c0c02c043c070000d466040c0da8000c1006d11000c2c0c1c0c0d42d410070503100445e90183c072901c16190741c005008000b0440400c1d004c01c041c2c040712030800260782c43c12040d9202c00342603070070403a002da030006c2c001e206010750a0020030518120b20030544013400a58507107558010301620081440c0b0a02501d5a503201404000340201c3d0041c1c14440c000304071880800c003006201040a000d1200811600340483c031b0703000340005a120380000c440d20f03400d040e0394800c0840300741c0e50402803044400c1e124048007840166800d1114007044031003c4800c812035030011400e446000f03241100002c0d4622000140800c0c3d640c0104110340c42042151100c408480b0103c0100d00d40c802da5022020062816281440344000c940145040701c184640c11900d20703482d281c2a404550b054480144640c0c043c1900f00e01d101d00980040e035110300c408410039500001050300c01500b40103858100d40f250409141446101041c1c41079511083c0c403080100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 143397823 1250 143396573 143396587
    0x7080901050403020312040f2a0f05030c060901090e01060309060b0f0f06030903071406011418010303080402061c1506110735070503010f0b0108130c05120a0501050903 74
    0x139440303100754002d40e451900030320300050a015035100307010000c6c1da000700d010b1901410b005d050300b00200407080c01480718407070140015050440b08105419280000c02801005c9a2501009a031340c3c0100c40d454180b04c030485001410014407691607009103060344000c5a541c00c1303441c040c802c84a003903250512a40e10071a540d10365464015040001c4582655070607076940390f0b5002103141d4014414010005c0e104907206401c0301d1800b18080d41200e0440c042c61807415400402c00c6030554481907a4540031100d90010804a0321400300d958200f400902400d250400c52101603200403030300d51038200480d40b40c06007024080784000500c2e00810b0545440c2e01441c03105403819848844500c2a441000084103512405000405d003818010b0030f5040a900007034000203075540c54440300d100e002d04c03a5107030008030910400c050141e05200401695004090390f60780200e41040e242143c815240e545001070007007280d858010807040c2c46018000101403802451919509454000f4030305002c54105001039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 143399073 1250 143397823 143397827
    0x3241406031909030e060a2736060b09011419050702060d0e150a0506060412110613080709060312121509020705010c0212160809060301030b07080901050403 69
    0x24041040b10040c02080011003404d084440c0c001aa080d80d610200004e4000c0120390407031410003283c0c1034402507400c003000041c40180c000c07111341300d01c0b104a0240c40341d051150400141c9500140c00b0801c0c203c00c40c5921103915001c40d181f0350000410044005450b14035580c219110820030140c40c640c031840c1508008902642020b01c84415090020110703481c030840da10321007030b103042d0742818004105c41040800410b170ba0b24144034641080040e40d601184021005000342d40c81940054602860585016143e0251841c03900c001cac3c2c1c0c2001d8a0001c1466075030b90703034024940345c2d20700756000399450b04100c001400d01d0f16503032110a0b098900902000010743d800299032003810700781031030781d2680c208031229400f0304035030403206045a02c04c580c081072440c0c45e603000d440d8460240000300034a01d0548410f03692900b4944140c090100b0500480d81d048030954000326541d0702c101d000a0810112601082d0f540e00284c0003100c02c03803666401c02c0b13000c55001c501341b40d00c4019a0000e001e14141a100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 143400323 1250 143399073 143399101
    0x609080d0b0a061407060603020d08091309120503070309300201050105090f090708070e150103090203060609191a0108090a0f08090109030b07080601081612020a0324140603 76
    0x103400f14010001c10950184515580700b9401142c02038407512b40c0e030f9024503215a650707011510540c86124400080b0f2200941442250f150a6020090302f0a18468283c19503c0b500004d0290040644801c10900080e046070000f904001a0300900e00e02c4c1c0707126006074022040000d80c01d000310b81c07411004000550740c0b00803242d040000c9480f081030301c0c0c43e485402410200c0b1500310740407a03c541480012600c06c1c50b0f45081c810000d01c41801ca849511000440658035007107806985503022002040986c902201900e8222215101c100031003070201c40f04200755108040c01c8100d09039905150b000658104c250503903c80702c1c007000303010700d6170840d80c3d100045048000f0281c04090301088a8070b140c1d00450400000d0b54114411116510300300320020586141224620300107401ea101280f0b549250300086100c1e503100d6120000500c00181111009410042103c002c264031500d00000d1503100203150819004003483d92a8000d04003244244079080303030b02c0704c54000d03441003007005080803440ea0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 143401573 1250 143400323 143400347
    0x70516061416050307020a06080601030b150a0305070e1503040501110a05040b13050409060e0106080303061e0d02061201030b061504150309140f011d060402010f0c0609080d0b0a06 79
    0x19980642400b5403d095182d4040c0500003504250381d86000b150441d00000428450700d401d90b814005502c240040c00140c217000c55181400b90414032000c00c40ca07020390842e5512111514003808030088080026800850403e02d2104d1ba0700c002050005000c03080c0108207140c454072100d10b00e032650195005203584140e1158414424001c80c60303c11090307800b2800001004020410301c01c1c042039042500081a05a415075038540c603196000590040101c2a280300f004020901e1400c48070030100240580c445c4100e45902c03101e102e070700c0b80060369880081c3c025004e070f9595140d4035605510b4600c0b41c038400540310314442c07a1103441041710121480101c800381c078400001d04078048904401074000d03003000da0006200d0a07182e401e850800c00d000501000d01040e107802400180c40445507102d01441092910005402040029016500400a080c0c1c103170020314202c800303045e0503203400d070803a5010402200c442d800007a801e4a100454020140036280850f0307951081803a08001a1442200311 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 143402823 1250 143401573 143401597
    0xa09030903082b0507034b051f08121b010b0d0503090a0608040b04020607051c0f0f0f02070e0a02070501090b0402040c05040b0a050304170705160614 66
    0x600c507000441000e881c403507030f0a2030320900780c5188407075580100940000c07203200700000d26041c0080804458116491b551103840c12080402d062034100300700c0c241b01c210100d051620201180e0358007000540c8500c1d40320b514298030310500001e041c1c070180603403201984040c840d0f9000f032950b07074840f030400c104544071850400052582c1440364640c1038050104482c0455020100d040c2c80300601c1000b000400386070138111141d41191351244015100c7c0c0b0b00035200901452a49000500107080c040d0043ca6028000e40840f200350004000e40902c41c1c4142280c03400042c611102d00003003981001c0e9507400c624890911118045a40c4002503403540644200c0b91307402801c40105034034442c3d0381c0c111501d243d00440240040201400d01806240040e14100c0c051440d010700f100201d48180d00380c80942d1415100c807441c01920210481d010b40000e4010784a45000500c420301820480c0c005100f020300c507001a080d00040132200070359803400741c0d00002c10320410703000e945841c1074003000321003a4450764 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 143404073 1250 143402823 143402827
    0x40207032606091b1b01110711041107050d03050a061203050403050c0d0804060305040314040e040b160509010c0c09020c150a02090901060507020111030d0b04050a0903090308 77
    0x240c1021500804040e40d516a51048014909140422940401d10400007074901000c242c60300340c00d4603103403507501665032201d020600201d8610030501c1511701034400b110002081441c01800c0c5140d86a20841c004c440d041c466581908640c02c16009200c05004001102d5040241e0b9858064803101d100c0340c2c0c80c080541d500d00103400c07802d145e131000c0007904940c030b200700219940c0e14000d00942c6c000c0c08103a5444c814980c84c1401072401840c00148968481c105a05203840c10005030003401d8080c00840c24040da410403480300100c40e0001d07000625201101004500b82810410340c01321000d41000110103050240c040c1041c0c1220071540f80c08c00c207103010f0300c0446960401d100400920380085e03c0103400017842c151130700301c001240c143c406c3e100b00050300300b901c0c2c50459008a100d08e03480d2a402014501c010060300d4011070240c20941c1c010304182d10442d040c0c07811181580c1c4100d002c1d540040c0c0d1611040340908240c414642e0104071a05c04000b280e0543d200909144510b100041c4841d81c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 143405323 1250 143404073 143404087
    0xc080609070e1f050705011b02120c030405130f0b0108060109171c08040201020607091203110118080d0b01090f0323030c061510090902160206070804091103010806060402 75
    0x252000303c440c01000f00c0160400c000c014800208583d1021130151420741c20040101c0102c100c034004403a00e010981c0040c1074400013000c583c91260080c05140060340810300000400780c0b2543e040300000d41460400007102040483d030607048a80e06580301c1c0c1004159000c0101698021071a101900c500135500c6110209012100d80f0306082281c1c450413524402224406054000b800140102d100b40c094079403036918101d084641c2c08843c8140e281d11090a281c20010074003500031074460012140001c030708050340410806400d052407204507206c0320001042c0030407419910070500c00550174600b020140d843c1060403806c2e81c0b880e00010f002218805000f948900707404800d668000000410f0700e40311300f051010940c0383c0008441c00c40203024108900d4226240030140d00c64500b519848026401d41001c28190007504070070600b0f400c00c000c850460000d65030b040b014001e0144540d0449a807603007461842001e030340152560340b069807024001131240301c4010502541c0640c05580058580031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 143406573 1250 143405323 143405329
    0x903090a170f01110304060e03030c19030b03030a08090f070501091a091203071707080d091502040902031605040e130f020a2628020d0501110a030c080609070e 70
    0x444000260b11503103030200c2e4031002c0d61014007452141d806002d0806c0b10281c0000300e40d44900c4200d8060007091410048080400080760903a407650038180b40019110f540100407a02d1075218407200c0d40468201410020103030b4003048403c1c101e0103002c0147c00c8a920342070028043c07002500403c2c003041110059011854000001d4074500324004207444406130841c0c0e8540e40320343c8284000c0e101004140c0301e190101d110003044520140c4c2c8001202d01e010408080e030750041802c110211500118840a408040030364000b0300061302c9a000c0059907801c0007001e0360a0100540c202000f4480107120030131003d40c020070b1035640022041e0703010b00880d00c04e1400805000c04401d0003903000c13407081d10200c0e840c10010b00c0c4d4100101c0140b401010082510351040d036421000c030300e8428500da60400d130080c504601e00300d1318100f032011301002044151365451030300b9940780d600c0400740090042010703034103141d06005a001000c1070381003076203550402c08007141c1034490052490051204490306401251 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 143407823 1250 143406573 143406583
    0xa18080d0509060706020d090c140102060f010905090708011a01080f060108010e0916030605060924010e04020d0501030f0309091a01050f09030a060b1305010807030f0c031b09050903090a17 83
    0x900d0140800c0700c8c11407480c10260300704090180c100844042003000050b540001001c074090032600c035061645031b1030198024090000100752090501440c440003038090424040e003120407042041c01d803900c210a00005000140c02014107842c0c28424041c8940c50342c10500080c151001a0f201d61640c3d0b940c0c145d410f180403905c03000441c0807100007100000b404255405203014280481d51981240c840e030001141c2c13200d00c108040500b115145403501c0765070107100c9400784144040c00250a040e144125402201c000f640240c03108801800180c003050352040d400c1c2c018051030401001000d1342003442098440d05900341505101d07002940300c0644840100780c8107030080003411549414001d10f442400340c10503000030740c094611401c0c0b00b030040f180e40c05481c4c1a50149001420124a50340300c5a41c6902030943c10799040300300340404004550160a04056001c000580e881050701d00316011040310301c001d240d044550001d0000c00855a224481e001c00c40b04e42d481c0788940c80003892529400c003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 143409073 1250 143407823 143407837
    0x1140105181c0b07031a0d050d05090a030b01080703031103031e0714030702100e0f060c0f0c0a031112090d15230a060b03010f0306110d020a18080d050906070602 71
    0x211040004018085500d0b0300f1030b030741e038209111b5034951110954041c44070380402ca500c0100f0076042200c1013421244070b20042d0903181c80c0108480426070352512403600700c09080c0c000c1ca01d035410040082c818143c110700500ca0301c1e040390000f9071641c5044112804020a100743c40c8500c0c550000108403100e104030b00d07110304003000c104050398900386554080c3d61641010032000f01107091654603840100302155102e891100318002c2d00807691500e075004a035a00c014040c0c1b04404080c043c42d501c282e001c10103130003458403e4682c1c0c403868000e205c0c06c6140214520507981a81820000c80200d038458209070081268042e8030583e0b1900007103800d001503c02048000a20401260014030003050a5400c0c0e0280c40d41d440100125a2100c0200d01070344803d008003011000485000c000140c001c0e400400742e00d11441c0b4050400342c0c06640700050b680300340301420001e18003d00c01c414030303000942e06400407c0500d00806040040240186c400d002d034605551051802140304002d000c602d0b0121152 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 143410323 1250 143409073 143409083
    0x50405010b0909061e0108072706122d02041a0301181103060405030a050c010b090f01030209090a0b060409020a0e0108031306090b1602062101140105181c 68
    0x490320300801c00e1655071a0445058801d00210011154115a8a0000340c142d079002d102230941c15080c001031940130004400710b10a00390682c840d507403900586200f20000760050b011500320f41a0641042c480041d401041e9210710343d00d6074a0248039002600700d06e404550705640124208034410011140e848103507881c82d4041d400e01c03040721130800442160001c0f0358440e1003007030884985c41c0141030b640d1300220380040141c0c0c0200014942280288080c15009940030004200c01302c0e0900403400205c0c3c06d4a000c0500c021600042c030852400040c0039178004104001000e03e04841d4455030304c049030151501d8040c5075a01502170642d220812800d01400799203c1079900d550303645404c00e607281d104040034019000780c4a4041103180c0715211490490313042c0c9284604001305011035030080309516030100d1740036208101e10200d6801402c034081c038081d207038501d942c00c0d07600d00440c1c284950361445443d0b0402100304854500700461807610181c1d414240d82c031410103803403035500c4d0085642c0b041020f09 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 143411573 1250 143410323 143410339
    0x2040504060c1101090b04030e131b08010b0c0604060209121509010c180302010e0a090c18060201110d110f07060c0e0a05130c03020d0609020712080105090406050405010b 75
    0x41031202942044440300700d540d550520107403c9076005400c903034218400400c070030b4034540400c2c082072003005814110a0005d02078031006041e2131143c0c3c115520014143c001e0800741c1000f0b100309070080f80c130f9801408440c4125280130300d514130301515006d000384020301d103075808a101c40c2c080e02c031200c54800601201046071204002c0850048600100300e440070b4441d82080342034014140b04120480c400084640301241c2c480c11607006590110241c0c40542c0c01108080001130405450300943d2640031140e03d4421111340700720b0401c0502007440e0810415a03052001c7c1081220240d0111881c6801d811000902c488a00200107028480e03070750115030082010031240140f0901e5404240c41c5000e80c0c0ba0200150301030410300c07030b0340c40e203034400c09a1040080964040b0000c45400a01d0007610701d2500614028104140c02e0881795a5040020000e40c042000e8080010000007441010002e041880c00356140a00044801c0d40091004041607141e402090800c802508042c80328540105002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 143412823 1250 143411573 143411581
    0x903100e01020f0a0206040b1e011710090b070225090b0a03051204061d061204050c1c0303061409180f030a080906070903030e2b0803010f06110c01030f09020405 71
    0x941d1b4402c141d0f8280c07141607221010034050f01401a81409056860440340440d070718000b1180c00342000d0307102c151058000c030100255101d15922400b08220320890140f81a0308010900a15014040c43c24207405510481045880782840c04098116000c2c107101040c0b00b0309120100d509e080565000424038441c0b1105010750301c401e013001e0320503105141d480b503d4454032003110080650702104e00e00c0d0480d80810000d50504a14405c03194024010340880d965441003d0114080403818a072006d1000822040c04c410150700d03005000040100701c00252161840100045d00b403000504480800c2da03c10b41c1007460385800f400141000c1542006481e01c07128400d4000c0c101d000116240300d10b60240c4400100200d000c1c0d451001642d400da994000ea00070200280066454101d25844007880d01210f41d800d404107010a07111642e10504100b6240c0d490700e08441d0503000d003a007100090009151069089a00020f08222010300900c0d002c20142c1a004604005210084010750020300b410104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 143414073 1250 143412823 143412827
    0x60903070603200901170403030b090106030b011b020f06031008100f0e0f070519030204020d020a020f120906030a02040509090d39050c060315040605060903100e01020f0a 75
    0x40c1542c00210300c022070380c0105034031840706988111003400b40811b5000c0e01101c03a8582075044654054403e040000e02c6001c914009850240c00341c1c0001c00103a02c0e031803080c5207941d000904811820710a128a905000c49500084825690004c0340e4012213001c0002420080c80b42c2c2c440000381619802d0310644134401e0408405002114481044203080030401034540e400000c40200c09940c0c1c10160454509020400400d1a155502c240300e51084020100250f682d03407000303054800702e044005a40700c030101d502030300740041ca40c16004079411440900181c8044602250b5481ca812920030b07036690348030b0450b68001d0250340c10182c0c21100b0201081411080061080c07592000c1d40c8444041018042090405065116009009622445c88214030380744050441d03a80a1007031007501c04c11038107600445c105801c2101c1c08180d41d000b80f0104500c5080910400014060548442d45028034403400f1a070b40c1c1c409242c41030b099950f240b1400c410a1001e50649440204d60106030740e8803000c803180 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 143415323 1250 143414073 143414081
    0x801060501081e070e01120c02030702120307020109120c0306110304050601090c0e19051507060506040b061204020a050a06050c010e071410021002070c0311100905040b060903070603 80
    0x240d80c0807400b090049503d021805020000500301090300c0441503030382400803105503c1e0603400c14140554580c103500310441c00c0c010b803100041141d00443e11101e00d80100855808551032180031b9400070805500540d038019102c4060780c086c4408035180781c50614105103581195800500030038541306c02207594030710700c07802075000364003d4044804690700c030043d51049410320307405040031605804104d00581024800c0c0c9001080390603c00c401240c1c5d50001c15a42c0041030310000304038000140c07030420450144038087c0c00c10415030301009800c0d640000300d0394a10580001e4074544041314002011503580c80341c410080d0070080c00c607249542d07440c000942250010b0b0940d103029424411200d82c151000600d807800c4805c0038a084002c0d0042c041070000070b1012503502000c60141c844003c02110f0540010400144506408113100c0d1850525041c6120304c180751512500780d00c0311078002c49500c0b020b04000d0700e0741150001005107003000040d0380e030700c10709a009805000340c4c40006111034040d40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 143416573 1250 143415323 143415329
    0x3080417070c0f030b0f0609150301060f090207031106090309040b03010e010c0e010207060e0906060f0c010e0d080a020307170a0b0d050708070e04030f05131d040203010c230a0e0901080106 83
    0x61005c03586d440c0e29011a00406045032110f4005081200280680589411519401101400009205458421007403240043c2c1c0c00440040381c0000da654100360f80906000d8024103420007070012420403405c415180d10405d10303918800d5485008a6480c0d60b420343c883c40304002600003c02c41c415500c0070140040c0111940306015015414001404900801c0c11030004003008142813415591041040920340000c804610512018024144400400d22a5a2170119031000501e0901122040101002c2d0010400100c1c103005000b403101d11900441810040400110458100d035646134083d03006151240300564028400071011092000c049844002e4500c000d06070f45030300342c484081a003940d40541e8020b0001e000d95810304101c80c8900050182140150a0089150b130740e1014180400241c846488440c5240414482185003d1103800303058101800c1419548139124010704130080081c1c03420500313900004210b18000d1148444132010f03280181041c6585d6111a0a10300030f1820340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 143417823 1250 143416573 143416583
    0xd0b150a02010b120109020108040f080405031203010e070905090406110c1203060901060903050d050a02150403110106050109062c062d092d040c020c150703080417070c0f03 76
    0xb44140514503060141b0702c101134060315400440e488564450501c0c5601400a4400300c006000110301a1b405100b400892060b211065450354104558104a400050722038001d005054408000710348881222950154014030001491200313151404101e00c00e5003481030b0103000302640d5001220391017018502403035064401c600da9a8035164161403140d4a8040640203900480d0350700d450911540c01489401241d105448428405403081c180740f0300c056030210041800505851003520782445508018034007440d05a065070710b882409440d10904005022810011a18a02d0501008001c0785050740c000351406a0b0303480b09101400c141d80904c407801c412019000100d0340c00c42000c1050307480f680303c02014500714034038500d05222480c074a08902c0c540514452030803021591944160324282032190050038402c10704a0030801040142d01031044960f100b40000d20110358071001e805e0744964003040b5a00c4552031102c11240e00c4c0941300004010170b91100000c00c0c00c0c0300310842941240c1c031503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 143419073 1250 143417823 143417839
    0x1e03020a09080d05070206070602040f12030224060105070305131205060c0906090402030a0b040c030e160b12070207030c0b040311120604020913141b010c05030d0b150a02010b 77
    0x2c8100984401c0c0b025042c600040d0305005a2025141060081c9115071040380011703e41035883c1e072102c9070100e0f554051030964a50f0040c2005140c0c0520418502c0d1a00700400e2301360040660300c0f0401c4c0c08014000740d040040210700c4400b014002c40c1120012101c00092040095a4601c0c50700d42d105038440442e03050244001140902e010b14040c0e81000b00028100c904018601c01440000e40000301024443c985030342c0b203000180c0310f622405206005035035000c04c0006030b000e40107261071042e41a034811448078801c10040d00d403c1205481180d49100180c008075141d600d000c928000f49504043d00c040c421a400141d6045564014401c503407140700d4108185642d07000b080880e800443e545c0100d41c02c03101c0020014904030041540c440900e045501e10703010b0a4a924980480d0400c614606500150841c803245080049800c0b50f004240f80103a00320b107099071110345a010310805404160345900e9508000da03035101015903000003040015484081e1000020701806e1061401c50244181e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 143420323 1250 143419073 143419079
    0x170307031103030919021305040b0103020906120a080a020a140a030318020f040e01110c0106050405010506191b0b0a0b0f0604060f0e0d0b07020d020105061f0f1e03020a09 75
    0x10100039244100c05410142c54505844043e540c101884517108036400301e24009a51015a045d20401e070156009600c0c09480e5815803041c898044006010a44582c2030340c494400708407130003d6906c01d00c550082ca0070fa00c80c190500282e151141c1f04000600e03212040340d9100355801d0004813114024003940d014816001450200341c0d602d42003c9004e908a00c0e0700c00c00d14184c1c24142c01c03c00c03a110948000050094009030f9110440d0010610045165162002001070349424081c040c0503000031161030f840c0800c0b00c0403086040340b000a0303050500c00802c010407030a103d1900502c4905412400e9080389161103204080100486448580320320240550300c00390341015800d0301d040e24125165030702ca070080000d0070340300626503000b4594800e000b080400002181100070b1400b800258004000303c20080c10040c0c00e40344000c010078041c40038160803441c0c1807032051840c076102169080c1040c03142a05a0110741a0360341d01f001401140001341510217040c0d0550007044400c01d16030701c0c1a490b6071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 143421573 1250 143420323 143420357
    0x30d060609030807020909070b160b0a060b030f040807060213030209130c14060d11120f13020105390c060408120306210105010906080604021503070917030703 70
    0x8040e001c09001810f0038000d480060410340940c6800c421071508481690741d480d1103c90055021100c401070b100c40300313094501002a81c2c00000d030400d07030659040c4081801e0617031039541400004c04150408081e039000c502400440c1c01150040b5030080c1083d03690b03282400c80313004850b5992104a00410003000000c1038444d5501d01002942d51202009000a140111054100c245060b440d548100d00300034242c0310b1400344c46107190640c03400303007216212600281d0b07404192078010300d0707501c002c0381203000c100110204021145460707034242066511844043d14990152005140c0385850325071007001c190b2020440c0b218003003d442441c04844031020107400b03002d110701030b600c90581c0a610407529041c0f608c128002466111801038071262a0303a40c1a030f070244482c04151000012a55070b01e00501894000f8002c01010b03200c604018081030800d940800c40034921420b6120303202d4008000701d64414420140ca00c0280444480c1a5089411080264030780e404080c048010580b40e88440d11207407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 143422823 1250 143421573 143421587
    0x1b030c080303160f0e0904060c020c101b0809041817070b06040506060c070306140112020f0f060906040b0409050901050f01270f0b0f061911030906040305030d0606 72
    0x200301d51964200880c0840c002c4e1600c801d001c2483c814000001440000c0d601c45030f1034548154002e00020500041395103019003001141c00e403040c05128200000d200d25078005c8422000d8035200d40d07408402c0c00850802c9899070054036a000d40c0315081c84001000003004000c041540d5000701e108089098610100001c0344c03180e190010011004103000502618240d88090f40c0310002520262609100700300f603908000c9103800444040e581ca02d414002d444121039a00d024002d0303120105100708040d00004c0c40b0340804c80d01c071485190820345840c06500c0c3c1805480e0321a002400c91501d941c0c8400c0d907545203802c18040c180d21940382100055181e00c0501511b40208001d8001d54810703401e2005d944110744410b4110700c1010b4280c0c07a12131040007180b1070741c081c04031010000154040c0003004c00007036007640f41ca22440b903101032003d81c0c550242811480c03615181c80c204454580945080c880c1140125107125a010030003290000c24020080010b20540090000401c01d0544841d800c2d43d080c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 143424073 1250 143422823 143422831
    0x1605010c09050a0b03091c0804060e0a0b0406020912010615030f0204140d0302010209210d11030301060e0a03080f04061106010e16030219090510030b090c07020109031b030c080303 79
    0x1456a020400281400200458100340e455007038901e001259001452405468641f103c00a2194000c120601c80148103210f4501c290b08047d05100c041500d5142d42407002038405000e07564009060044c50795031907201c03440d40c40307410000d1040035a04c141140311229011081004282810303020361900066101711400c1c1c910000cfc034512800300510a000c1c4c031840d00700040b010340d0340c2040302c4441e9035039080c0a4910020390394080750046914015650030b150620418009115002a01003160300000c01507a0541e141c900d40080101003890000d401c5800a40c40074203441c1002600404020408009005652040d291610b808401c80d5490b940c0311801d1181031b0000c12030308045182000c4a800101003040140340150512582c2c2195401c1f80294402460200b500030408208a00b0401d60300401440e00d03050030020f0300030307440110700c6c0b0a800428104003064001a81011680200c1016014641061150500c2071400d8807035603c00c81c40740800e0728034860420000071715001c00012284030b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 143425323 1250 143424073 143424079
    0x20d02011d030f210408040609060c0507050f01020a0602030a02030105240703030f0b10020c090c07050c090703020403081222032705100309020a060e06040e1b1605010c0905 76
    0x90140162465003498204e10840c1886045000d0045181010030b503013280203d028a00742980d03146000800b4103581101c1c0d020109101d00da42011001c100302180d29022a01d0603a11000398000040040b410030350301c504000d00242c80070040c803800f920310f40d000e1416104281d9a0b09100c03a0240d03410900205c5034100b40301c907004100b0952000074801d40114049214503000420064a980d001a2a00c524060201d00603030010303403100020b1600325480c0c0e82005003011070920303000254443c0707030f1076403080d050300d5000e9480140401c02540c0300b9070440d0019070300a06d8003034469440e80d5109035843c40c240d401d01c11141c0c504000b004010241902032514942c980c550700c0d807044c164503040f0900c0010500c8404440d0788407900207500d84850488507038048580c1e50001e03050215104000c0b0359181508060100407103124024404d89802c0108c1d0300742c40c444600e680e100d548000144c841818114144282c40e0004611200408072801c82d0b0f04805110750300a02006106400455500880d8482d150b4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 143426573 1250 143425323 143425327
    0x905010b03061b04061b020d050a0203210d0b15070c0e01060201020f09090a060f26030309150a0b0d030f27090e010204080a1412040308030f06010e030d020d02011d03 73
    0x800c09000c0e10401485101c106c409841c4960541c0000d140c0c11418241a0380303e400c07541d110000c502c1c00340705410b401c413600950151550442071800180d03000302039052500c5e41c1e5401c003004480e41d94441c14034000030b221110550341d00c2e403890708a0740c503101403055110115032032001181050060090758a010003001d00b01d030400308280204081807402620030704646941d1000440c03181b4004166601a14008402070488820000305441002545400414a4000b8810310156003004540c040b449524881d1160882e01c5d80c000b100d0062101d591001c1d480240000000201a00448032002001090302c0b1122901e61601804408110003100415070b80740b5854240403c1a00c0c6c3d02c564081840301000504040d2038000c10b910300040701c3c4040c0d0708030029041407040c1203000c022003e29107507005043c070b0900349565518030150102409140e9420700500011310940d104a90403020310300f0003021154503410001c030280d100c110f504041c1c0010b509040c40d1840403030a20144649648403000118 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 143427823 1250 143426573 143426579
    0x712050702240702100206011404020415031e060e0f0601020604050a23010609060f0b04030302030418020918091b130914030d0c090905060d0605070908010905010b03061b04 76
    0x11014102d1000401d05030301c0c082c041d420240e240c40c901504400300b550020a025410702050110b03204400111a208a004000600c0f0311200703244270310169510342c1004a940700061034001517806150b0000d4481c01c0c82d004000404a451036812030081c080c113100000c1c280c650000490b1a010300b00d40182c40383c0c3c032400c0c0000c00550a510a80c80001081100300302d085000180300d0f0a461503544007070500b5803180c20910a060320b03564000b00402603070314174628051440c4d41c0070751640240d1103070038400441480c041c408504560116440022b0040901c0b200b0904c0e0001601500c070292186001131084802d039200c0c5403034120b0b842003006002020101c0041201c2455005041204012902141c1a000300803c1c5c2138100f002d00f1201010b00404111a80c0882d0700510f052410b07440305e940142807106016058440c05050700c015074015101081c03517920b401d000d5401c0300e0300f1341c491070080d8a404811010b01206500c480a200e000f00d080c0d0b98039450784804400105c0102c84c109072200800c000c20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 143429073 1250 143427823 143427859
    0x52104120b090f010c0c020f0301051009050c0d052a09010e0609061e03010e070206070c03050705120a050705011d0309010810080a030302041d04120f02010609050108030712050702 79
    0x855002c40c24404544811441000150079954000d00c040d0100307441c60311090852810607c1c2c0004244281c0003041145010b4401003080d0100e07204407c440e07559400805c0304840018200c0301200f4504400384420304114a10381074150007401d0044104c1d1042c80700c4800184a14125404444165280c5c000c140043d4204481c80c1e02c02084180c1c0940208031880700c15452660240701d00d440d6180c11030f20b0b985403043c0d184241c50000d001004540010f42045500c581002c120091150585000d644a00003480c00c2e602d0440c030706485081c01240420340c919150340c444000c000440c4207200034000c0c0c606959a40110118800070b42c00703a50801c1c0010b0b07803194414901c05034002c00c113000c01003ca6540c0c107075803800e14000ea5820342c00680c00041c10b00980c0fa011034540040070200c00e00c11400d00d041d845050000103104001801c00c0582c031030030034131907200350440700281060040030001540c1d144c1d131b80d076a00d500000c8211080c1c405001002c1d61280180c0c155008c5036000340c54002249185070349 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 143430323 1250 143429073 143429093
    0x40e07050d1a06180604050306010801020c100209090c0d2a140c0d03110708070602070c08060402010e010305270309090105060301032411130e0112020d060e031605210412 75
    0x1e03030004c0d006d100c00900c5580030040310740241a403000041e512900c05d0100d50400e0641c00b500032215004200352440d40d1603032964242d21200c9406601d171a0103407800c8000c00b4144100100300d281d43c000c007107103401240c124118405003038140c4548480d501043e42c0c5401a002e09514030101c2d403c0305210301c000034020b410102441c1d4440c000c0a14120955a81040c50b0f04100c1003a075034941d0101e001e00c10000f85207901c1c009440103200800380340c03402d03500080c41c010411550b41c1c1010b0f1503a0100b1440501046104080e2008a070b000c0e8400324107a01c042c1d60ba07003007841c001c0e00c43c0c0404c600000300b50906e5000c4034162a080764003280e138001220f50000129030100d80310014280da5501003401c01180c42c0141203c24948500c620140b490280c1100079110180c2186c01d6200d04a48042c0c01a6501901c020b4101d40c0201c010642c05242281503046000f0102c00d901605418101c240030007401080c3e00116642004101c520201c4840b01003410b80514010b440803100c800d0040c601246200349 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 143431573 1250 143430323 143430367
    0x61b0f0703110603041b09140f060d121101061206150803030115090b04030b1006020f0c040f0b091603051302100309050a0813030606081203010e070203040e07050d1a06 74
    0x310010920040004e0f40312400d15990110187c643d90710103d0307a0f54246e0030b00c065049001c255141009092010004010703401c1c814005013031500324052003054a020314214032400007410000c121003070b519418146000b00d404405c83e1a6072418040c40c0d03c40c18400e8030768090f105850011401c2d60300340301440200c5a03000c1010414040010000a16016508003c0c8099482440a8003945c2010444100d4200244d006882513400c4031034000c00c40d80c000108220801000c9501140300c09520101900504414000079040241e18040258800700500d84070700c070b030030155410415039032010a0401c20904c9248001d51000700c000807440440c3c840d40003c04c069000d8410b90340c2c2c1c1c80719551405115405903c1e001d403c0c0000460400501c0340d14810700f0000d001542c0030340861800c800005100b448140981202240b0000120b40864402c0042d04d01910380e046050702c890804000241164101c81da0415886042c07904032021041c00507039080b050311703010708001d0a140c01e40c81c0309407030000000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 143432823 1250 143431573 143431583
    0xb030d0302040e10060c0318031b06030e0a03081b0705060c030412020a0f020603091c021b0f0a032d0c030b0121060f020c120403020a05060301030b010504090f02061b0f070311060304 80
    0x1b23008030100315500c80e8940111181c0540d085001e24081007c0e05980708a115268a5001000303000d000c03a81007500668002d0f0074030042215405041c0c180e84581c02086009820340c8211020001c11184500085016600a5510301110b202107074042f40d84d542e020f0700c0100009190121407005040c18009190810030280589582c14403009007021804220003207400103030b0080190940d41060840340c0c2a8054064078042458035404021070202509848010040d04c3c0c0d4814900459519102c088001d4011003c41c40011141e402c00c1a07980308180400c0e2252074459000040310101c40f0103a40340c092544024030085003032500d0301c10007801001107540c800c0e5000c0201809040c42441401035074018800c4d81030300c803030941c014805c061141d038004900445d010001840410380c3c4010b480e04683d4102c8002c501c0d240c0c2860951134401c81c07075100030b4212002003a080c0104031040040714002c0d0240d400c40b11402c51050102d6522070301484054401c03100d40400100d1810140003c50b4424010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 143434073 1250 143432823 143432867
    0x806010b04090b0a030b09070501080c0c030403020d020f09010308090f04060602060a0507030b0a0e010305010e0f03070b060d02130212250305060f0d050d08070c030f120b030d0302040e10060c03 85
    0x25261b11480304c1e0129060390340ca800103c1d06200b030b0343c2c00c4080c8540042c141c00e0610b0400a41a602507540e100b6030001030301c102c03080511a03007155228003100c2080321b0050854040e0b035070340749800c000320740110b2903003071051003040d10207102400c003131240c502107e82560003400142c694006413002480d004c0d02c18000c0540311800c100c990f1f20b42011800041030b8110b500b04040d031441c01c003d800c4582001140340360ba00820f8254060a0000003640c455580101c0b4500043d110100015007040c03034180b009411000c1495080380790703080395000e0441c050260702c80b1031241e91180542e16a034003200200d181c905850300041d40a0328031a074000c692103023021300446d00b0100403e00003411080d03203000c02c441d20391205920b01841640b01504d0303600001181041920503179950307000b03000b441310011403100300060000d0040c0350100380d400c550f00745031014058035151080d844008000e9032081c09003400b44e20b010703400310782d464002403502003c80f0b01c50b50303401014031070300c1c0d9048440903c144d40021184120b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 143435323 1250 143434073 143434079
    0x4090b010f0f03180602180307091b05130905040f02030c0904030518040f020f0415050703050307030f150b09010201181a0910060801090b0906040c0510090815100806010b04090b0a 79
    0x8500c000d0007c604090300054100ca0740804261510103642c101c7e0412509103600f04c00c001d0343c1c10040c1c4464101c54103102c0d4440f0070301c002c0e41d21040520750100e101d1608100500051013251a005801180250180c401c00c41c464401d2000c0307004191030040000342c0800032070720f580d0f00840280126070030003000030450180f442140c4050760060011011141c8000604021802d45801c400e101c144071820b0503410b01043d074030058420700000b46103000f811b444090081c850300301075000e0304200c03141c0e0403095442900c0300481310440c0c1000303600c070f405986424034a0828124100000c14019480185a6482210500c440d4102c11001c0d14041c514800c03000381001c0c0202c82e000d10b10142100e00000218900d007428110180c41024210b4031007a0011424003001c40e841c030100c1025550103441305942c81040d15401c03140c14806601c806a0390003502041c400c0d0210000005d8017400c5011552010f198a0f9031800791264802e220b940e004110421082100d20f085400031080c040b8000c00c0402c0c0b2903a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 143436573 1250 143435323 143435333
    0xa0c02090408030109051e0606032205010606030b0301020f0904020a1b0803060102060f070c0201180b0703020c091608011401120e0d020d030507091a0f040b04090b010f0f0318 77
    0x20241e8049400c108040700522110001d40f04003540580740c10307203180c1002d1030440c0c00030354070788080d1280c0d000700307000400145e140c80240d428030a4480d410000e4810b002c0c250402074002d11150081000107810050072504519050094446c241c1c0c120282c2407503c2145c2c010000298000040c0a09118280d81c82405040e0982410681c00d40500e407181d0b92480c11400080c01c084004124031101904030080c0214158420940f1204650a00340604840c1c1460340340f00110407958002402c0c00c00000d4544100f50703020801041410301a103152000e40c80b148444400001c040c0c0101c4002200b0340c0c010441800541c9110300490410704002c1807209413a0841da0540d10b0300d00060440387d01c0140c4010b913860341080000c01000d0186030401c13840c14108030050042116100713014029414448181403078265000701c0300e10400103141c495a4950b1904003c0302500140700f100d00301d41c030300303959644070303500810015526282ca45d03031343c0c2201020343c481030300140019104420b820396444a071000041c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 143437823 1250 143436573 143436589
    0x4050702100507050403080304021c050f0a050c090f070810032f2d010516030806010845060c0d0b04060b0406030b030f0109030e120d02120a0c02 64
    0x404240c0c06090710798510344440054441c081c1140301085000c0000b04080b415040989400942c1101c84c40b22081e03c907022807680582e4041f024040b0300441c00300080e012000101000101d11030015140ad04040c082000440e0710104c1e04403440f00301400014100500c220f6900f5804481010302200407a141d883d00c040031043d14050500b80a00c01341c440058071401c0c0c0203103940f0075044410400ca000418010b50314039035104400d8400b9408203400e402141e008500b92040c0014081d10328500c0c3c2250308008080060035034006020441607400320300841084113400d00d44111407001c0e44040c116104401200d114914070711882c0c005445c003111101070741845100e010b4800c0d500d0954030707080601300460031074040304004d900c21840c06104112800c0708406903811100c0340d0500285c1c40303500c200403078203140b0034039080320392540f800c8007120406420005514404006640c1402500054002d0742d5070744604690b4100075a10690003604804d0a08004103120901860b000e030b02c940d16540892410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 143439073 1250 143437823 143437831
    0x71707060204030b060f010c08090402041e050103050708070e09071704110111030901020c210a0f052406090703020f0a1e0201181704050607080918160c05010b0405 72
    0x303281c00140410901c040e03100c000b50440001c4907850340c000d10740300028103a5011101c00a008120103e40015545d0740c650680c1c0081c80c0310208240683e0f40228070445000303050140c0c0780460300d0840425112445a45403c0c41080c05484290388924580c0401c01c0e1064024403e0007000f010a1006440d5022070131404d02591140a01808400c240400501007070049801080c1d01c3c0e000b444035030910380e0300041254191030300744c580040399004012080406504d803003140486201355280402041107205074040750303501800c25201c4003030030f101d46c0b01100030034000904007881c030341404110f10b1b142440019800c1186402c0040c5040e83e80340f1410640d07004100e0394404180f40185413164804071034071501444615100800100d604108403c3e078542003254050b0118407040300c02840102d610b4201c5014102c01009162200070300d00c0e11040540c85021014001c4101300c0e042250b010860b05440d001d03c02004020002c0c82c40020200ea081114007402c1d40c1d11340d01c2c0c2c0d81d035003903c3d15548902c50203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 143440323 1250 143439073 143439083
    0x60e0c040f0c0908030307020703141c050d060b0301030f06020306010201090501180c0e040b2707270b01020d050c03130609080d050405030303012705070e0a05030c030a0305071707 79
    0x30100c00214083d0070b841ca00d9000391100c0d0410410881a03640c08207514050380e50041404186400c80020145010340d4428003480f5846c03c03120340e00700341e600403001e08100e01040d40240030b10380e219200c4103151f02080c40000c0410540302d20281c0012035a0300a142c9c000303410f00c000500c0d0046600d9103400c0da15610140613000213068209000e00251075071190281613050003050f03003424140d0720103121100081401c82043c501406c0360401c0219a01310201d124401412640300e99150f440c002c0c14003d0002c2042030b900142c1e0025941e072450342c004c020b4110416009480404400142645c943d800030403d20064001001a912140c030804a04000751601750b80310f4026a041c18000792904541d01801c1e010b01006010804c0681d40000441c0c0c1910046000301c408038007140301c000c0c4609108240c88801d079007004100030076198403080740c45e0b00c030800703d0313460b0700c2940d0301c8003495120346c1003a1041e6019040b82843c400820b001d14021700c51507100d031030b1420180c07041c00482580381e00541c4c02190 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 143441573 1250 143440323 143440331
    0x10503130c0b181c12051b030a0912020d020906012705100504030b01031509080a030e0c040c050d050c0c0619050a0507050304031103040810060911030601050403060e0c040f 76
    0x4144501280c07081e070040015109100884080300c90134120b4000200010040d4032480f075150130581c42032080d6494022285006610fa182c89903109489030404050780c800503c023407200003111261685031400c07140c0c0103051205041029000e21040f10710040050741404000d2040c0b0001c2101074440e102441c07600000e007000c2034140020080c40030170300c03000a1b007004000d00091000c518000070250440798003041c0345032900904122000a40005030014000c0711010440c201d080340c0603007001d1010a90001510031204200d01000100d4407640b12107000194140701080500c0e50075030110b40c0024900710401d080a1545000500d480c0003150840104008200034006440c200c0c020b43e40c001c000711030300f4096481d000c20f0040c240d02000b0005010050b200c035841166600030b100301d0307001d01819000d542202000700d8240003e0141c0740302e40340240d071070300032840e003050040b4041d02d01500050f5190b51600349952100b00c040c2c85c4a0348c110810b4045c240c082d0b044ca9a89101c0c1818041110304046 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 143442823 1250 143441573 143441587
    0xb04030f051b0616020d020603090615061801030207020f0d120305010e040201080c090109030203010c0c02030601090c020303041b080304060e03150f0a09050a08160b0a0204080a02010503130c0b 85
    0x82c0c14503481c0c0e40100c0310324407003054070105541d504064880007500004224010000c5000103021502d580c54013a422403070010030702c00000c80104030507120b00c5000902c0030003001c00f40c0501c10184a1a241a96010620112244298400e0f0028842540003c0400280750f82e500d00280c2c188406000032108140344c0201d0600d02d50301801260f005042ea20100348440c5010b8002801015000707007001c2c209000000d410040fa0700a51104001d950050003c100600d44804050304c12031101d0400c0e4803e00c601000000c1c105805d00031070202142e90b901450940e140c4c0e944041100303800424030743c1038800d0040042103085007040544024030007996488101404642410b050501280b0300c82500240c0d0b1007044641d50458100c50f03045504410001111101e03401e20a040140c140c4c1e0040c144000021040c1c0f80e1841030101843c420f00030f550082103a12202d80302000c0307104a20900c4000c1c0c20840b529005036001d02c0196034000094142c0e2540d516240e0743d00702c85035401e60800030891070041995 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 143444073 1250 143442823 143442833
    0x914060c091903030915030e06071d19030b190e0601090609020901080c090a03021f090f03031710080d02010f0f060b09130605060705010204080606150703180b04030f 73
    0x80d40042c299050100460039a14001e18680c1c0d00c0c0a0701141141d062516540c4510aa1002540c00215000c1c1d07401360412030002858243c548401d00b8510151000c071046a00d4141c51401c81e807003400080b4890340b8559a0f56415141d0f0040c1981d44660000380c80c0c402ca1212801219500c1c0c810f83d0240040b90f0509000360b0480340541c2000c1c1d4010301c1402000740390b0344c003c051503030400c00000036643c41d480d000c0c0005482d180c0e43d4000a41183c42101040a480000d400c1d681d180b4103641c803480b040300e4403070034154001c880d1880003074001198041031903049100061842c0e081803000344122041521101040c1c03901101c0003d480050b036641b210381d45040383c01c1c0305640050710f482c6814094a880d29140090351f00507050418072401110381400400803055110000911000c2e082e152101480d0400314000d40007486099580c8c0948400556a890a000801c05d88440d58030101e051800700e071002c54454020301820356002080c1030020408403100406400110700ca801c11590441c2c0c6440d107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 143445323 1250 143444073 143444089
    0x30207051b130603030f0804020a0b0423102003130602150106080106020c040b04090b0f0405010f020f030403030f0605030613170301080d1206050a03060507030b01170106030914060c09 81
    0x15000801d240c00f4051001951055032005016550f14002c00d2a40341c90001034114401503010025000c4000380000d02c14540900c4400704280c40540741011808520500c080d0581c51012040000c42049003842c0c0144284200c0203800c2d4440c0880c3d0402c1c4520724900c82e815416003003940583c1c82151407410200349403001d40d024125518143c1801e51400780065994150320000a01c01e9481c0e694200c615110740c4c1c00f4149083d000f84010780c0034148007032003140c205003c0d40e0549055081c00b008041844c81402241c5a00d29442481461641d423918102c001741018840b10b149103803209000141c980d005c100c554080c41d4001e1055000a0107031402c041c0c1c1c5241c03107a03e031548000501c0100660000880c041d51180150f09202c9059840e80350418002c0007250400c40e840030111070007006100043d4030131841144c0d661401c005c400311303000064526448140020800199210040c00341e1446030700440e5a44d48184d4028500f6910032445c2c90510004482808418102140c0110b103441c003428 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 143446573 1250 143445323 143445349
    0x30f06050a090302071404020c0d030203040210020604020d0201050903010e0703060e21070201030207170a03470114030c09040c170406020a0c021309030e01030b030319030207051b 79
    0x240c01c1040b1900340c0d03030181d100e008a2140100070500000c0f945415200d90b0112030014041405550b005080c2c048054001c1d0030503038080c1e0083ca000c52103846000c0c00090081d000d90780040419540120981c01101c066014007a06501952506259041d441080081d14003541c401c1801041401e01c8412040ca17140240007400f10340300e11040d024480c03a441c40120303a6400c0d02842e02582d504103d0805954803445107001000b500341c0000e01c032a100d58140c1c801080780c0d00b0021801120400388503e203c010103c90710748c40d0001c250f161204240465150181c00c18001130426541b18071101c541e440007a0400c559a440718140003e10700131515240c4180380341c0e0516804d100c030034050003142050080500038001407045500041400c00140200c00204820f94001e040400700c8441c4002200a46071f2140c0850206100c91446400c40d07000707006111b220940600154103119542c0740344408007160384003082c14990300304807100100c0c4045c0114010180340352941842c185c020b80c188a01156052 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 143447823 1250 143446573 143446591
    0x6070b090a150b0a0b0c07030f08040816080c10020f150103020f0604180203060114040b0a090b09060a030b04060b0c03030411030a08040603091a01080f1002040b040303052101030f0605 81
    0xf0b075907408980c1c803d42c02c24140c982080c10561224000e001591806a46420142645081a40d10020001d401005005840070b8109541404000300d6100244135291700483d0080e4002440030301850030020740c0d15100a00c04c1c812100511448824a810100350fa81c61a0708005031a0040c003c1d404c118916400012044e25418505490901c440712101021072030400c80640000200d2a113a108013500311500000c000d12a50701d60340c0c0c1440da0030640c44040b00c2c0f0086820b00e100001c600b000c4000342c480c0c041d4080c002919107080900110020500090f409501580c0c0314130105403820118054000700c80650001e41d92814141012148030212500c07240c070a5111015010000b04602c0a98080740c849080100e00d0450910f84000980e0700701212100141910307000180c0507100040c4030f002c004c01481900e83e5005032101c4601a0710850144a80c811b02c10041040000d20440003001d460000c0e0340102401e0303408a605c8010380d10217a02c15511001750b205100b00f805050320840350040315032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 143449073 1250 143447823 143447831
    0x803040311100207270507080f071d010f05040b0309151f03020402092716050309031e04080109030e1512060f030f0307050109051c120b06070b090a15 66
    0x2144025920744140c0908890a0101060340340c08003171190b50102e5451007a0014001e42c608100c00821404080311400f01d01c0318801c02080300f84e40100ca00600b4070180114aa00c40e00c050303001035801411360310f0780c041048010400001d5128004014501890340040504100207850400701076404000e0f005141c051003103107004054030414040703e01100e0b030540340581c07250008000174940c00b0201e6801340c0c002d0968441f1100110780304546034458a083c0e010400c106040704011625400121070380c4009500403c540304030200c032403156000b00c031341c070300c10041c90203468542481c290b540c120030490100b180107040c07102c58a00145510f0b00060142000c500b0114140a480c0394060003400841c040e04031083c01045030748040c842d000c0c40d02140c0081320b558203414940f160083ca04c0007810b03100c40c080c01d010304030144041d1408e42c4030404507a640070041c1d011004001c0c0200a10030906074815400c220890000756078000c10383c450f450300d0001d080820014109841202c0628001d1500d80d4a8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 143450323 1250 143449073 143449099
    0xc02030319091502121008010902010c020f030f0a08070302071401020a15020d06030507090b0105120412020304050a0b1b010b0a031b08030301080d1206050d0209060d08040803040311 80
    0xc0078480300440303503221408168606507042c800182c1c1248031214008600000340c20b8250040075078818003484a04985014032607132040807600704c0c0e0400303000900060005900e80b000d1300c4d009001034540040141a1a40d90180a150034074100e10020229125040403031181300703040e0148100401006a03520f0700c00980c502d040001e480d1150200003d110f5513490007445844038503a8195441000c522030108a6a40ca0b8107040707030703142e90510078a403805040c403841d034000c1e51050090350004003054000503029104e980d511710000304e00b60000c00c210712051100081d40e03583c00021200522107080890740d100d01140482050407500244192944c0c14030b1803121254a0768081e40e4112a0080d0b0314491490112030bc00c840062164030403e00c501c800701c008075000002041c1c000340f4800c540c448080f845801c90a10041e250584142980a4041c030303e0307000541070160020358040380c0200b40c00d0185880c1e036101c00c5641c00039004081550f0001c101441004a009410348800300120380e000d0789810 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 143451573 1250 143450323 143450341
    0x5010603060e04060504030225090b0409031b110303030f0702061f090c02010605100302030106090e060a180905010903031d12030c0702190e0601080105061801052a030d0c020303 78
    0x60303c001c0401e44d5820000d814144240402d6107040c10054204170407450702c45510072407102c0360060884051604120016a160500c680c20344280d145d260007140004000074101907490200d410b85942842d03400d141140d0b6801c0c0020342c031441c9629040e02d19030504160091401c50010b2050713520b00049082c034403500f004900418115001c10102086003500c00030100e01620031503000942144020000340349103074154000d54140c880d242d07203011540d0b070303115440c407000c0b1806d4990541000411409002082c1100802c210f01070030001c002c10160040c0d075030582194980c080a030300203641c0da05880f074542c00300101e07a140c5004400c011b008020240424011601c40507010342e0300c0c524001100000c644a0b070903480000004001030444142c2c0d90503903030710100b0f012103241d0b0004a82c0400801d203403038140255000d1044180a10205811100042d203466022040c070740c080c9101d08803a400410803441d03900894401600107151540022a41001a00c010078004c0c415900140f040101e001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 143452823 1250 143451573 143451599
    0x30b101202030a080a09050d060e010b0109030c06080709030f050d0f020a0b0f090c090a0c0306051203030610030b04110c1603030804030e04140c130503010e2a220501060306 76
    0x70f400c0301046985c1c3c010303500240c2d10a2510750089070085e10070045d45050007425408031104400b0751000307111941242d801100c3d20151400001c100b622030760f1091051520a00da1142e000704507041400c0c002d62244c40381400d9894003101211a60301c48400c0c400340c281d000d00b1668111030f090000744002151a59090f240c0b4800518005e01d446c002800602040c0040041c04104203002e4080b050509103510514090050300c0110400f09007801d00000d0705040c184103261440280b01c01450560300c641c03003040000c000824000c000c15444003107071103460f036580c890805213088101c07101d950f40c6003500c0b038907052021508020300414100102000802d42040140d98801d0741480d0bd400c2001803080064002c0114180308004c07104d2007020000220781c0480100412183c507500300308038958803000c0500f618007400c080c040c43d0304503821081084024104103c07400803071440e070060750131140001c20368000d030604201c0c044440381c0003503013601c02c254819180034010511b020b004031403e2000b180508 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 143454073 1250 143452823 143452843
    0x1b021c0e06090a03240b01090513050a090c1203030525080a140a0b010215010b0f09030102090402031e0f010501020a150213030c0503070b120c130e01030b10120203 72
    0x4141c005001d410300c0d61031a0a400c003940d8480384100c074004450000e1520744548010310414580381c5020203242e58010303801e07081101c100800c000d031b5800b84100b0001c0500f202034440210292251001e00001e80400a14005010407242001001d680c07070800034217407100134040b121100c01458043e5402c581102c5440e1510764981811101511080341040003054070801c48560000d050707050011004a50300404e410103401d83c200c03202001c2c0c180400712030200070b1040c84407000c6d0810501d4078440024000c0e00140c1402000107081003c000c0100e400c0c1d910845991240101100703c042c84501e104162507000f82d40c0c00f03803000283d814100003035555800c444001d401c0300b50403580ca11144820f41c0440e8541c8514246440c05196030345441d810039103550103240d01ca4000c0b11030101c0d60000700419201c0340b03a0381020403070391506c80d118007031100c0d40010700d080c43e00c821541010802c5450402d82e41c1c005c1d48140c0183e001441c0003c8070085c1802682c200e2040c4100110190300543d42c00030712800c20b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 143455323 1250 143454073 143454079
    0x1b050402042301091a0702010305060619030e0f07030b220308010b07061b03091203180f171209010b010905130e0f0106170f010504020a0b0d0f1b021c0e 67
    0x2e01180e00503901c4240960003042c00025203030703c2e000180400d0000e8800c05100ba02d0900a075141c580c1084054082e000c46c000b001100c50680340803003407003504695044000082a0f50340c110240201a09020700340d0401e0f60f00d20b241c1024001c09914801100407907020518003403040d15429940100410b20600ca124411030021903034006010055124005010501c90002c030f950158400c003901404203100103507071200109443d00800d034005c0c040c254034074108080e00c03d804416507984511500781200309640c0e614003194402c0301451408018042c0811402c005401c40c900032039000d080d607002124103410814020030401042d100d2000c40604c02048203000301d042041485d40303501c2d14a1041c10760300c0641c00c00388005140e024030416035500c81c0e0300b8011354801402150714a400c0c0e420940c0c00a4121072440401c200710302400011300883c0104480200b000217250f80440d056450780070445401d41c080c403441c9840c2c540c0420440c0b40700782c0b850483e2070f0b0203207460308060854289220046c2c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 143456573 1250 143455323 143455379
    0x20f12030103030c140c060c06040507050f0f06031e07020a1103030406140304030e0418020f0a05061204030203070609081236100c05030f070c05100b030a050a1b05040204 75
    0x220904c42446400283e146c0645250b450381c41d00c16440e95540e1040c0c0c2c040d180c60041030000301e00360070681d188480e1200054013007031102c1a8442802802da000604110201d442039943c80415001c80c92380e640900415401414482450300f881c10141608000366482980100010003c80390040200c402545200200035200e50741c0c3c0c1029a40d45c41204030080d40585010755906440c1c910040c84000d00b8026a000140201c1400c00e00402014900a1590044050190a01002e95004840c1c0c1c13003442481600c0c1040301da980d5520940c1da80c4441201c0404010a16000c0c04c403441c107116a0045002880702c0301c0c01049039800940f82102101c50802d80144049101020b10030444140403505010081000ca09503103001060741c0c0054581016032014600404c2025200e11540701009400802030f1818118400c00070008005080308150540180301c4030001084050141a07c2e4601800c01c48a803244500000c4100e047c198100d00e225070710611050140340c041e50360b031806c928180c1d12840 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 143457823 1250 143456573 143456603
    0x80402010203091203041403070308030105060f070b01060801030201030b030312060118030c09060303031b02030315180a0c08010603060e0c07060e060702100b0402030402010c240903020f12030103030c 88
    0xb41180700700340200b50070250050000c141c10034008001c008442209940100366440e0000309901c0d10102e110150501d642880180070918000c00104204494850b04034604405a40d9001011000341c0c0002c000c100084010410355816002e04e20703945004034050f5181c62812800410305030340c00751400e410084074900c8035041c410600b6041c4003844d001141d040d0819551014800a010140001c4000908050148031400d2030062007801c16000340d00514155a2403158805000e103290b100d06500441d50803040049401740d521031800f50708034810102c1d01019888000d41a0031040c1d1092040526103c1e04200e813584154020f03422020b080181544c0340c80ea4108240500214040160140504000d0144660300040c00000b14407030354905000501d480382c10042280401c0b07a020307012480c1c55100c0c0300051348031001c1200102c100d04072031404803100a85581102c150710030072805030b440f140c3d4104c50403208000001d440c14804414524660440d9001841340e42183d800801c00e8103501000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 143459073 1250 143457823 143457827
    0x80a0615110c060d09140120071a0c09010809030307050f1b0f071703121504090c0b070c05060a0c0b1506030703091b030c051c080c150108011b08040201 67
    0x80000c0e1070303005000c9600c0745124030144c401811844011140c01e180c107124441c1401042c0a22400c480350b201d94a05d10340c4603485416125400f10384101c560b207002c0448501100101c41d50180647e0301100d10a85510310000058880300e00500006107581c401c0c020010f01a40c40000c845000e04401d648548034024070700d4411080c000900019054081d07800514415580080c80000301c9406100d1520f41809901440e900c81c82495044075448a05000166003d603c6024015280002a00c006100180c6855400c03074964960030011048d032002030f0039018004082200c8010306400c03103045180110b1503c01400c0310b8002c040041030340d10301000040c1307a1800d41a80d1607035254080e00e180e5991420718402001000d02d4403080300c06295100b1031488802c11055007001752070780424002212801c020030040c40003441c0308142c1300112200b280703600003020340e0007070409640010010113080ea40d09480312800301050700101602da01d000c021175591155803c1c24039020440341420012903c540c001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 143460323 1250 143459073 143459083
    0x5150702030604080c1006081b1201050c030a0b01050f070204110d06060804030f0314270102040f0501020d020a0b040b070c020603040b0105010e01050705060a0c1e030903080a061511 80
    0x1941c180242030400003403100d2900104510340c0c41e04140da50f001000d00b03002c41100c240f800f4440c3c41c0d9001045403000920b01c22070b0305840b01401000c200c030070404400d6050949030b04070713000c0b404280c020082c0301405d22140a00010007100342002410516104506840c6008100f4080c0c45651604078600c03c0d16212000c842d0110b81c4a0014009162124805031000130306a0381200002d02140e81e13079078450702c40d20420102c426107124501440c0c994421018244596000c0c20f061803600c2c18903581e10407030034030042c801007070644800d50b641880c0c0390000e810254401c0c6008155003001a00700001029000b40c9944190b00000701000e688421230111400584000002c0d085600081030005010700920a40d04031042643d40003808032740d15004440e14000d40764028041d500c50400300c0e94100c961f0b000b40c0c030a046145000680c0b5106c4920340007214240c1203954001c656210059024541d1140486a1003000034109020841c6803c030072001074101e08110350200030b041000070b044034400f400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 143461573 1250 143460323 143460337
    0x60610030e07030602040f05090f060405060a05030115030b0f090d05070c030c0909050f0f1e0c0901060903060b030307020105040b130320090a2f04030b0a02030a20040515 75
    0x402c07108080c0d01ca10b4800c000758028028a612001818000145840c01e00d040501c10303418003445144035240c203c20702c000b0b402c3c0a0204c0740e000b185224081410707242485224020040e6103552199249942050040c50001501406621110038100045054002510700001c811403800c240e4900480c10480610003160700014405c03a0140800104000c0075041950344900640030b4428010580000e44d0741c400b03040b840d11402c0d030007008030800ba06044002e840c1c03c00c8140c1c0c06584003007040ca400035603840d009801510200c0c85c1c1a00074402c1c001d03d40310f241000201600254030701038442e000648640140e2280000080d800914a101d50000002c0040255480b8003601140345004a0b000c01100a00c02000e0140c080e2400140400c0024084c080d6280c6a107400018a140020349991a00b002d011031101d90340360411001000549a10f40c3c184070380790342c41c0b0050322401c003040360702d0942d0a400107990020440701e00c3c0a000c00b028404072021140300b04e440c1101d48007000443c40c000c1c00340701 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 143462823 1250 143461573 143461601
    0x110112060306050f0405010c031b1209080f03090d181701020903060a0b030c0f060429030915010803090102060f090c0406030c030c0509090d03091103030304060c0f020f06061003 78
    0x41c8980c0704d1081d2001c60050788103000a106500000401b2011295550b040e89074184110441d9504c2601583e110b50740041c4100010800382c00c251510030740c80c2d01200d6103100d07000001040000040e802c0c0410901c1410714540250307508052608058040220700074051101100c503240300700c8030b00941c1120480000a42030b02c180c0e261910b01e60703005100820081c1e00078028a074548105180c20038074044010b038001c1c402818181010a00018101003004650050201004090741451054090351040c0601d1000700740c03940203500c24200004060344078944aa20500c2520050b85c0c001c0b900b85e5000e2080443d81d102c5030b0b10b044401e8071740351a8140903030700a841c244012050180161981043e00d028045400d9030030343c2d40007481002d603800c0b250450700d07401021012a4191113504090282805010722290070764507440002d00b0340e44251002c9920704d54444103110700720b40007103044e02640d095001908054104142551b01c0d040010240c1e482880c0c12030300d80e04503070f02030f500c4000d2070f134401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 143464073 1250 143462823 143462831
    0x60c0a0503070c1a0108060117030415020a170c011a18040204230f0702030301050a140105071509060e122506020f03070212041202040b010e041b0318110112060306 72
    0xc80c1a13a4802c0e2428050b9005900540b40049000ca10681550a0000c0500300841c03803c0d20700184a907215151103818821802160010070100d4070184240c001d0380d2854003030356903903820410f0290849044640c1c0e075400300c540d180200c090365a80d4108891248050130800e2580da100c3c40010002c040d030148082001d40240800304d4400c004e141058890125601512500d494a08040c1d03541e0100344034684d403011840b1002e0052030800030002c40b6a0006041060170105136a0340c140808555800c1e0140855842401805000190007510304c0b55541303c000d032280f00403041441081d032094040459a521080310201c0603044402860580389400a80442d00c5000024844500d503005491160061180401d8030a80036aa041142d046900c1c1001040c5805025070909c8054007070180040d05000c0e9024440820b0346840c0640f0848020002c10076419100e141c10140450303c586401e0f0100e150101140030004040c1654885082c10074206540f1017500400ea10b805800319410007401c50b420 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 143465323 1250 143464073 143464103
    0x3060a0b030f07150c0312020403061e05010b0f07020111030a02010504020a061e08060d0c06030605031209030705040b0310020408060403140a0210020f0403062c060c0a0503070c 78
    0x6268464026900214155250148034082d1075540e040c240c000ca05180664104a000d01809803010014080c42400d20401c000c0010304201e00b2a0026442542c0071520fa10342d0203120840d000400d81044d8980340d08000c1c5d5410030402000314080c46080303012542c00001c244c01568090460121480380d0007040b80d40d5621090700090280030181c500300d0049401a20210764a4003901d503903413845e1002040b01c03901350102c00085610040107800103412a8903100107a020030000390501003e400c81e81c6010451602c2c050605180010b0000142030901040c0310200042d980030441d0070440d0710844d008510035036018002800c111106544450141c0b00160010701d45002141403403040b40a503d5a244145800001c60498450000201e0060300000244062024180d024000c80c0d40c2003000c0d60f0070b0645a0795000100d4030750a034039081e00c2c400307485000742c414070303120102000f0010180a449a82041003129540380980007612042c0b02d4040005142248100c10842c1010b0300002c020740c088030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 143466573 1250 143465323 143465341
    0xe0a060603060b041d1c031407031d0a031205070212120f0a0e03030612070b070309150203040608040303051b0a0c02090a0c0e01111204060519030501230f0306 70
    0x31003d0700c0c07030089003058041c4040c080010301c2144080412009800880f0020302001c2800040492000c185a5504280400b42d2031200340c80d0310414454a001426261454180b641e0801501c8460704e0b41d40600b08400002c1d507c1001300b15841c107030413070100f05030729804000c8c0c0c145a40f901580000e20400719a000348818201d600320300524260b40341c2c4038152220450301040c0c0340314021500c00c580c41000810300c1c46c01d02d204801c01344a400b205462920780c4650201310755600001c0b00b540040c0760712809028142c8104030071a0341d0100c0340010b626041c0780510103042040300800c0a000e1694031000500380c810220301090480e0140b0b1411039403402c2d985070107043c095001405a00a02c6100000b0350124581d2103000c1c0c00101c1602c1d8000c10300603a800441e0a078034501b007070040f00e01403229140b0241c81004082d2028202c1d64950325182c0803020003030150350390b6180000c001c06082800421034039400d02200c0c2e10100d81c101140244040520118000c15641e00742160140314100c2000384180e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 143467823 1250 143466573 143466581
    0x9150e09191a0601030501060e0603070903150b0f18070809030d02040612140606190c0b0126010c08011401051902010b04060801360507080705010f02010e0c01030e0a06060306 77
    0xb0010280a06602c8071001101260024081c0401181f078a01c04152986000d2000e580d21043c14548445419220b560b000044d40502000f503440d951608002241c40ca0310070150b48980c4000e0342c0381900d01c1c00720001b040351480060240010721100c0c00206a402e030050007110105500e2100c195911580c90000078040c1d03401e60604440381c0e10b0403d420140c0201100c640d4022240200418140285500d0600d00103d000d21038009004e5210b912100041030200d21900a000394140811402035035030045031820070041c1c1554150345004580c2002c00c0c1c01c400c44070b0554024050303070b034a854ac2c501c0041c4c40c5403054480011248204e60170203001e0642c1504190401030080c0e030140641641e440d512400d8404241c204600301d428404001904a2081c90492405140305030100d0304031803946845003000a0f0303800601d015040410184995600040602040d41c034602c002c100251050a10680712000d042e01c80341015280c03104440c1862042003102c0310a90000760800015959140401c010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 143469073 1250 143467823 143467853
    0xc0309030b0c1809091e071701060914041a070e130605031011090910030f0c0602010c0906080403300504060f06080a0305210408031009150e0919 64
    0x10501886070300f030880c1014a92103008104170030003004440b034032502e0355500003400e0007071800300d2065200003e0501404010300c007414090500000f030341400c1200900a50b61025014011040d8130780a1200141d131800420364221034003040c4c41842d4882c40412540c1c0c170403c2658561004004682c250308003180d5100c0809c641040f0121096800e44001c0c40d41940d48101160215400034084624181031400a055010740c1d005082800140c0300d60b5186140e506c2060b00380c4011801200c103011a61302441018030b01f1030701f418548e160303d1401070020f1156030010002030030045022145c408000401d504070030300d141e0904c102244080040c558200420301141c081c2c501314141101200d40f2289446004d055a0410014003402101a10140c4d203582c018985000740d003c099881c508000c14035000140214840d0013115560300306400413a81502c0c0716003207042e55624002c038010003030140c44210b004451120b60041815904d00a00605080a040c0e040c80482c046131002c104012542c041ca0706c034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 143470323 1250 143469073 143469097
    0x91409060106080c07080906090307080303041218060c15020301080a03080c070317071205070302030118140a0908070b070207081b100c0f0203070e010503010b030606030303070c0309030b0c 83
    0x160382d075a0411207040c08280c0f0541c154441c200b003c0b0300402d030b8460017425080009084146000c03040004a0b2826a1550002151781c001100307100070804904002c02440f5502c0c1780040420700b8940e00c030b18140c040741c0700d420300b8000707a09826401c22030020300845500317424807030442d101d43e5a0410303e80c4910340090110000741e002c80004201e001c8040c203443c2c03031923015950401501188100c0f00c41c40400940303e081484a15195050b02840c0d1303024052040b40343d540c1c050384952614031050320054490401121803170070810003080d450500d0b40c10740d074410020a80400e4000e01e5081415840c4191b6002404081c100d01c20401c49640018a12049981020441c0c50015000142004d001041a04036511240d20050352882c01c0c440c0000c20724050080e240c0486c01519940024680321355035014501d01a40b00f00100a189401e12903403e40c82c000741d01a1559160150000f0b0312440002c0c0481c051106408004091605c1607035020061907000d600c100060034160031031245034103c3c0c03c003800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 143471573 1250 143470323 143470333
    0x15040e010614061602010e150d02040501121b080705070506010b0717070309060509150a02010b120c060909042102010203040507090b030c0d060b1c0219032109091409 73
    0x40d090400d4812155010803451111132440099401141c200051840466008180902d8480d07010081c01c020206a86901401a0345a150400140509a907118901e180c2442c00c87c0c044e82403242d01c000c140030150203191040c00d603943c608060700d15001d0a0f101800070304c20034001040748181007004102040c022010000540068a41d02000e4841d01a0080002e81d540d0402c000316405440600002d110040001080400140c074441031504040900340042c1c3d100c251944c0036040400c14004080f001c0b2000c0d1881e5650b640202d9050711415403000e00912aa0b000502400141c0c180e0841001240054003030000712650000d010b908180d0301603500b405543d07400985c42c001481098050703000a0040c4c035403a00440c0c200040707242900010b5517259100d007110706a5030b507140304801911016881c10b5400c203150340180042e015445114000d016040f80c02400824825a01d052b55072100350100f40049050035002c54050900382d001c00c8030b007401c002d42d0b021942480c1c1401031080b81c401c02129 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 143472823 1250 143471573 143471609
    0xa140f070b060915130506030a02090411120f0c1504090509030304170307090e06040e0607020a1a070503010510020f01090b150a0312270312021209010e0915040e0106 73
    0x44400030051031045c0d44141d03070141c601d052505581200e90322180003810b41e000d40c1410340101d02814021103045a241000c0c140420b22403420890740c848024120000703120f989440004280d5810180d64100e00c81c9401d0b092080c03800703400b042168041c0c0004081403003103041241c030f0240d4a07001500c04851003044000f8094070705c1303501410f40748038065070f03900c06540510303080342d4081303001014042d96001a21a201580010410402076009011030b500030201d4492a040c01803a01050001c0290b5404000081c40351a0340c4c80b506490541c0d50403100389a08203507000091740380c20074100e00d400e030a5007490321040c14030120b5410316202e44154030094079102140010010080f1081c0001810305a81c0300340100204d104012076040342d66840c2c1604031b0110804a0100c0c00b29a5034030403141d5516000c0c21521540c1d050262030b1414030400b4040341444c2c607540028040310001a4a0f0780204503510004161440084450100a2014000300074590001c1c2405000e00940e014100070182d20181c42 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 143474073 1250 143472823 143472841
    0x60307060c0309050108040807020d03050a020f0c0f0f06071b14010e09011a07080c01020c011508073c060306060c0b0402120106030803071d0a0b0a140f070b0609 71
    0x4044070607403603580c0359203440c1080010b44c2c00f4440170304240c9640078184811070040e115a00b04044290003522a0b548175070307030766500a181140d50401407000d07403c4586004e038141c8070440030309070080301102c464141c0b81548010032214019100c000d41114207204c00107400400c80c0b0701d43c0c400d0751041000340c01000d17421001503901c03da94241c1140c005559400400084448002681d0880340401c0a81e00d050700c1e98a5610702d41d08540350515842e5800915180948004d10910795512401440030f540249403c0d1015200d414502c500c4204020550991070900350428040c01034070107400000402d411210281e03d0406414050740001c280b8050012641d5030184000f50002a406514200250340b1a424800308800e03d41c1c02d07000719900c968000c03001954003170140d4801c0780255100b090910318814108110100305283d180682c100da401403060a00000460311060325038102400d800c0c2020006000c3c500c034054907402c501c20089501e00410608403042802010111a501c9003502c4011903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 143475323 1250 143474073 143474087
    0x1504030210091e11240307030b03011b0c0209330a09050c0705060c03011206230c0c1e030406081f030602030702010f14061c06020c0606030706 63
    0x10190250707100310444a0856015000411824400c142540f280e081c189407002071400492003c68994180014006071410208010100e4040c1d00c240420070542c0c04204401c0b621002d03240d0820140c4501107041c0c1900d00f50031401d41e400b049200c101204146000007000b001c1400807c03403041c4001000f240d4000f2440c1d68850b182c400444502e02d03460001c134100c85118420340340c0b031900209440000103910500384162842480681303040c0f0303501c0e445841d0082c01e21100500e81183c1c5401400140030940c400711030250011313844240080c280340c2c00c00c48030088068441c1ea07444213400394000c209410240d500540002c524000440b0b40300030004001400c0042507888d903080d02c0d070083c8410040c0d42d100340801a00301a603284659030100c0c0c40e90905507050150b800503a01c1c0d030b40010622070743c0b41d42485110001480124108440003000488501000700507110b54480d00e0440c1d50420510980c50b000c900c03203648010119030703e1b24030f011a561181c100300d4070144640940c120009284c0e008180f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 143476573 1250 143475323 143475331
    0x519031d0102120a0201060e0703050412050307050f03040f0501110d0c032007140111091008061e030114040b01030201090f0605070611040305011a0f061e07020102031204060e15 78
    0xf92907150a8029418440e8019103804c80c110341d21910001025082c61140600403507031540c01003074900d01400c04408040c400384410003000410002c2028880d804000d640ca54a030203054640c5c0d0b5255814000903c0c3c20a41c0050078039483c01c3e1008100f400c06c203000300790700841880c06009065000d042601107452041c07122821800690120004030b03108401400c80a11551040e8400000082180d003122540d03801c0b021400750000e9041002d24000b804030b06680002d2038a20aa85080404118414040b110f81c110300343c0364040e0030301c0340d640070b401c85038818280c00355410b140d1419040c131030b580210a1206038003242c1d14880205025407542541c900340d4100341c0300d80d031405416980d03010041131401c2c1e404900b51070074000071001a900b80100c2c041c00106a80c40140000c441007003006940041e000ca901c29030041041b01c03000214102c3c18400f6900c00300c042e0b900c0b03810b140010b03810361113048000c1d101c01070200308020030002c0c2030344103002150002040301c810505005540c82a9a4195 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 143477823 1250 143476573 143476577
    0x203060a09080c0d0507021908030a030c02010b1e09010501050f03070c05120301090516020714010c0521040f1203171503240916030803130519031d01 66
    0x80040d10410554021021403031058002c585050f001511071410003421341400c000045000415078103602c2d045803407003001700400283c01c2c12249801801660380c801d00d68074205050711100100c031028000c0d40b1070300d002079000e0040103da8400003810210110220700c07243c030a4400308004140e039481041a40c60f01400e015078640f442c0c41e11502a1071080500c8022119031280e0101c045040c540f00c405180244101c4102040500f0700303910503040d042000d08054119404585d04004a81d00f41d0191850b0030028208506030741d400d401c0c00c07170402040c07003c81d07100380c0c65607104165100747d11303401002100d1002c1c0002c402c003034a4240984220f000c464028000402030182c0c050110070306040240c00180f4040402c04c0c0ca410400801e0501c03881c80c507404a00e022410032004480720640c1c0da03503403003080403001d0031890150f0f141d9070070552441e00010700040000300005139840044500c1c1c41e00550441c003220407152074046c260480803032840c800c400003031100051010b0141c41d10107401c0800030503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 143479073 1250 143477823 143477833
    0x11e05040b07050316030305150315070507230703021e0108190e012901111005071803051c0806090403080a090b090105090610030503090108060f030d0309060f02070203 74
    0x44401c0d603802006040d212400304100001903280712042e11008103200391000f050900e0302030030751a00007030b034464814000e4210305000d9900e0010b12440c158411080c0c00c00e02d4554141f41003511005da90001e01d04012500922050000340c000a99001224400c0703885040408a00c8403454070500c4040c54640421031071001b141552800c50008010200000400240ca04010020034251142151401d0044000194160700484488484e00c4400c5c0207081180e2551500072041e5510f107010314112201564446c003060140b44200703c0c0c02e02e440b41c1003850f000c5864903404c03c9078940b89031100e080064a620342d081c1246034019031049200d613000600c1954240d4650f20300f81d503000d500404440403142e5036020000064441107442c0d001b1880003000003924a04a9584e51800310040c00c038001c1c07071051003000c2001400010403201809421329010310b03035032918804140c0440e84d00203245c1d494000c241b09894099496030140d020503001d4502401411030000000003241f1500e040a5055000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 143480323 1250 143479073 143479079
    0x501081903030f020c060a06030203010608010b010804080901020f0312190b01020c09071211030f15030304031106041203030c0807051905031503010501061d0307060815210309011e0504 81
    0x2680039485408505101600d0f0010b02d17444c03941012030032111710401540d00c400c24000c0d42000d100c0c810243c0790b620000c0140401304400a0800000140000d111940c00690207607181d1003404010f65201414013100e4580c1c500301c10b0101c00140403158105070802e4144100f0b000c83c00c03030049061440060b00546414003049042c07140c019001041d003000e1048000c814003012209103e24a01c040460000a841c0d0030400900607842c0c001a040e14441e641804688009035408404c840031258070072a210b4005804401240369801a07601c6079041c10645a070300000d1507055000084110b1455645141c07da40703442d811b8980c0d0081d0391108410584c040c1455100c64000c40045030000c42e50440600c26040300000642503c00c00d812500019881462590400344402e0b100007202000310080c000d000c2c184503005000090081c5906815004da03222075001d903d40508903100c0304005144030100301010503007a940c1e540702c040824000340041011440b50300700080c01040e00d00c883da880b54076145c6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 143481573 1250 143480323 143480327
    0x203120f04020a0e3402010e06011a161b051c150e0705040c020c0102060a0207051902041805070f061404052202030a0507080604051509090709110d0501081903 70
    0x5401170a0f45200d0b0450f41c8001c031091450300440c4e10f6405005c00c49040780c1c0190500909540b2480702c0c2d01c103c0c0d48002c0c0148090f0ba10700302070f070700c104070106003054844c007190700245100d040880c1c02404d26200d041c209803e0848058101e025140240d44445402c41044680001890300f0200038050015000e91302d20307241c090350800f45488211070100e82410b520ba0000408842c404c5041c00c1c0982c1c08601d0201c07807540c05100461788058018011800e01e51700d526883e44031074880203210805411101031804550301c940c007030043d0050700da00344640c80249280c030071758400c0180202e6400895402001850034400c015110307254180100e45420301c0d203440d0a0040414040001c080c01200c1401d640920705242d1000d9403181c01e10200c01325090038907910103000091b0203003e8a004030f080208001c00c0311031005560701031285c1503508040960b1104081c50030404107801c1039210a041c4a081143c0303900341006010030410502d010041666102403146c0d507161542120120300203440100d0005c00c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 143482823 1250 143481573 143481599
    0x309020f101403070e120102131211060319050f150d0c09090f150c032009090c0f070302010911010f0206150a0e07110c06041211041107030203120f04020a 68
    0xf52203091490b0f05c4452000081c02c041c804402212075691b020440114110240340440d00500c0d42c1d09152902401ca616140b880a40365124180142000004210400020304002c3c488003100d5200304083d0401000b00762034088250b4400c00380c03040003100041e15140485042c1c072065403013882c614031246441020f80280103014410340744280030500f51400f00d031100c036886422003002c6000144002900303801504031001c0d96040300407440102428007500c0e400204451030300004691340750032540c40300d118054500c9001c250500456011444004054054000340c0849100c0d9010f20354210368080111101450500a00016844940412082d150001414a0150002e000380c2c0c01152a0f060b90052540c0944020000540c917103e02d50003a1414410a010b14408980301307840d140c6455491040c4e0811848098a004041c1e0140c070444c0c2d803258040160f89040000084d15510741d81800303912600500300d80c5d010400b034680011500c0380a410300601c00da41c01406080081c1c10246440c500b0307 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 143484073 1250 143482823 143482831
    0x2030d0606210b0409060908040911032707090e030d05010902121303020a020a0609080606031501180b03061018050106020723040501080607021501050d060c140a0309020f101403 78
    0x302d0781e45c1d88880b0106905005d2000800c0c020501541e0f5285031441139011103151158500c0c0500e02802400085003242190440da02d1810b550000820b01034021141023130303840e0744030704c4042c0e00e000030301e030301068000c070240c2402d20490f01e0401c00781c1c2c2c4c1d60207160f00f64072416045510004524002414039000c00a51014442c000c3c41116460103140d030115101100d0f50f002a0003080d101702d01048070410820049a004009030054080112000b2080c0e10045060042c0002c40d41041120381401a469105800b56000202241c826040c2100100b1100025000d0f2502034810781401030311544a40c0505030403241e096004107030380351600c1c844486107540858001700f0044e4a0650071a20b03607550286034043c08044000c3c040134103006001a2a061610000c08144c0112400403c95903540b90b041d290059000207002c00c1e00384034020112030401e030130712000141c44400300b580740e500c0c3c0e41644000c3d00e0a20a8600d0180b441103d010040303c00484011000005d180c4134040819451030342c003a50304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 143485323 1250 143484073 143484079
    0x40b030405070f08060109061202010f08060f0a030605061f0207050d03050c0a0b06100c03021f0204030c0f080c04020301050d0f1704030515250507110603010602030d0606210b 77
    0x655074803a4034402c0a0f40096203c400258003030001800000181e101d00e20050080c0303942c5a2a030b06c02076002030003034506001070740188007660300081c48940720f100c46221310160041034001c8558407864220000d11040d503400780034100341560011040c61507800303140a605a5001412070300e00c1c00d010407810702107020302201000010300c0030494144c01000700c59540752280369411514580801800346204400c003100c0100300746942d190021a4002c1a07801c000308110351034414031034003465000c0c003034815540000c0c205005c003080020034500402d4440d0660b1103000994401e011a40308010681c0030030b01440d540400c007c4480e01c0020030045400804038850340c0c617920280c8502011420a8019030310668070b0b6000b4000300d01b0740c241090f480c0c9a01090030501c2501239560039064079084031460314a0410712030002049014000c0c10081c0d00382c48080282029500e6840d02002034a90b000480440b00c1d4505107180451100e00443c2854104800d5080b0180c0004400101c5000b9003d13084445030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 143486573 1250 143485323 143485333
    0x90a0306050c070c080105040b060402090f010309020f030d0206040b060406060905010305070c02100f0e04060308040b071a010308090301050a0605130c1206030c0e090d1209031806080a06060e0303040b030405 91
    0x1001074001c44c0c440380206444000002c00c5c3c9810300b0b140020744c0c401030032103121740d03c100820200c0e595912010b13a01c604003842c0002d8079000a03c04a00c0f505480c202680e414031480ca40310701c420ba070014002e031099101d00b4640708640c03500340a01c41550840e018090103e10b0b40202404154800d50015520588501d80085100080c3e008100401c03148208803000905070b20440040c15048007200700503042c02d40d03003040018a1511000498092402121011100001c008040c8920121050b628000310030044840396034074031b044055035015159041c041d50130000090649855841004e0450b44054100c40008000580070001040b0380303d000000e11510500880450b1000d11410020303500c42c3c55040740607414508200b81d0318000401601c642e038040c10420001d181d11070304050745800c20490201d604011882c1c00d1710141501c1c1015044031000e031000140003580180d115001e02d401c1c580130080c90b82c1f06c040803240002c02481c050f80550081008200e41c0c1e4800c40110360280c01502075803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 143487823 1250 143486573 143486587
    0x3071413050c0307020111040b07110a0902271c03050912030d090215040812030c07020924030a030c080a031116050c0405040f1203020c03070c1505090a0306050c 71
    0x1400300e54060b21464010300000c01040324050b02445000c01410138140761604141ca000004889032140c484014002e00d43c40901c60865200c2d010303503101404401340150745401c1885880004094101c10b000d003400f402c0003840b402030510929542039104c1072000403400c3c080c561403d541039401802c859400c407010b0015401c0071002880900158000880007164501440c01000030303522244130b140080c44400c00c42001503400001e032600b41e1007941500c42c1d86903036468000c000746000d1824041d410001c00d004002c10760400296001d481401c50350700418107803441c814151ba030b1344501c9009000c1882c40d4030340030115103041c002c0c000b15080b610b004600f45210204501150f001003a00c000131021a540b0101049014015103881d110240e901b000740c2d1429071a5989a29585000134180d03264600401c44414800d404031511615124112540c491403841e080071155024820040407504c08a1004825403084040b9100c2450080c1242c000c40d0564817090001e043c098261440000c00300621 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 143489073 1250 143487823 143487859
    0x60f040b0411011e0801080c0909070e040f020a0602030d1406010c110a090c08041202030a090506090f0301050711120703051c1b051b0601061407030201060e09070f1202030714 77
    0x110840140507074445c03015514202d802454200311400e190310410400741001034082001544004407144900d01c5920b58a0301c1c200706021141c4e1130806034000c01c0e0074001040c5140c00000034503003681600400c00c0940400400121950401e491050000300c2e21038000c0003044003c0d40c0121084c6004080d01400ca40d10350485044030304010800011071000000c000621180d514075080800b4540081e5180c0203440700000c080d10080d0080758800c0102044411650701d90f813b54004102c0301038020407203820803042c05807a80c044003d58050741e2144000c468041c20340f46054500301070b4941c9800341030600140c01c555055440f80c1c071180413180d40b0700e400c01c4069075184c900030440c4d6241d200c09a82e2003c111000e5a601d29442c42040660312050040001960081c8003200100711340d658680c840745039141c00ca01500381580031810068054060091403030300417840c4d01c100c1d00c000e100d098903030f940c84503c0c0490800070300019500d03402101080014456a5000d0090500003c001d08860801e071300722 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 143490323 1250 143489073 143489117
    0x90201120e010c080903070b01030212030706150f050a03120c1b060f0314090703121b0515090607090506030c071b06080c04030503030c131505030405060f040b041101 73
    0x6480507980d11180c9142e503403500540c0f520b40040604020b07528200083c0c858204140c5c040c4030003400b91520042c441e44280d018816900e01503072089050200791104003441c0381030b9131207010b5605003c0078100c1c00a01c514203102d030340c000c17a0340c464081103200e4071002c0161445401ea120a8030b003207108607001440305407074058120142c0325585403401e50fa00340a00c0201120486109a88124410b40c00e001d42100000707800000c0b0380d80310600e44c103d0041d190702112244000300ea542c1d200042c440c3ca007410400007041c2d540010080240e04031669540011303a03944c48100759003100c0440c103000400e000900344200155403090700824890319090440d0780f10802e009034002c2c4054046513114080c88910340c080c00307103030300040103881c001c0c1428216110152207101c040c0c20020401e400041c045c001c1000e180d4424010803410341c91b00b2020a091401821540c8221012210760041c440050070b4005451a124001d90f00145401001d80c0ea40e500c800950781000c4d5503906004d85001c0115241c0c40e0070f08 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 143491573 1250 143490323 143490341
    0x304081b0d0810050319030905030d08180304050a030620070f050705040501150320030717060418060b041104090c020613031b0f0c030c050306070c02100309020112 72
    0x4181c12050410010050070026244a24a90b12140d041041d640c0010340d00c200c028130a07100c152004007919003502c8554640d80101c0d0503020700701411681039001404c651044191100c01c0180d00b14a0700050b49a201c2d43c0100b80c6c4c4009040c00510200da09a8070468180d16074031079074135400c1c045da0171840c8c594101d102c1c1141d16407540c0034028101303c1c003844640028882039400b40541d50402071101c4024485221840070513680d03845918207095140805032650303110000d2959a400c09100013440d10811380014540501c1440100b0b00600b49407080180d030b88480a00c010b00004d0356520403024000490f40d465100303842e1a5240b0084001c13000400c001c10b04813500040d05414410040e061100041070314914a415906100201e90003900e0010490480300f8200d034a00d2461808030700502c2e600300f003d843d000c5030050100801000340d01401c00e4400450031202c42d03564541003216241d100000003034100e1403021001000c00d0203508864000ad10505000445c1500320b1011411128051 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 143492823 1250 143491573 143491627
    0xb0c07060515100c020109050f031204090b0915030d030c02030d0e030d0c02070b030610020f03030a0c090b0307021c03060801020c0a02150f03010506030403050c0609061603060812030408 82
    0x407200007491500e41c0b0010b45488990601104c850015000a044410f542c40f8050007205510003443c0705a4041c4034802d0414121010580c9450b181c038100070040080e244180d009280800200310301b40d48810300c4100045c8014000d00d000d451a82c001c4014040c007401d080254441402003070703003620ba2401049401500c1c500210344802c00844218140c0e4a180c0c04001903401c0440284400c5501c542101e0388010140c41a1110743e88105049203000c1803040c81400703034040031080c032441c480d8a4204469081481d90303403281c0152181c3c03941c0400c0c40181e034608007682c805d868001c8880e0310101c0701c42080c0c40c1802c3c0058010740d2240b65601360b9000139000c11064005185410862038807940c50158001400800b9040c507105e0701d441600c030700c01070048511800d400700000c0d0400d40300c1d0080700c40a4940c030007a548641404000150b90300170940f200d120703e030317600b01210743c00c94401e01c209011951414000c15020302d001200202075400030344241c031820800c1040c1d502020048641d554001115 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 143494073 1250 143492823 143492851
    0xc09040c120513020a1a040915080a300807200d030519020f1c0914030714010513030309150501061205060103061a280201020d050c0c0a0b0c070605 65
    0xa0300c104011196a40c1003103221500d40209041ba40c46150280e4040d9441c2e1b076800030300076584180071841d000159020300094454130950300b007000300101500008041d000710b001945a102d2100e06001c0c107800380d00b41c1c00101802c00145085200d6600d4030700b440440808201e2420b0344031107290424000c11f0001c00443d45480602045410000004039880181081142851421901402240700381c00c82c40400b4910091511205109907000c48021a400100300c1d00301c41c2c0c0c00740d00700d440f0f420142d41030310403070034400c540e100e200018001c05115900c2003480350400c6407035540a40c0285100074069400f1500e154600d240c0c0700315071250602800c0141c840304020b20b507240481e010740d07600410150406040c003804000003007480071078801070302400e03a8013503c3d44a614005116201d9a880b41916039001880c03025420f50198010100141a10400d000507581c04041c0f4000784500035180c500c690141103008046200880d0242d00013035503400c0300345011343c2c5403140e105031402504c07a1040c103012 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 143495323 1250 143494073 143494111
    0x20c01140d27110f100f1b0f030305090105060f120c090c27060301030312020d110c070b030c090103051e011d0106030e060a0e01020c0f0d14030c09040c1205 69
    0x10244a240f60300d0303044600700c8040c0c0c404008910600c000403c160180010680c01041c194007401c41c44071081d401d050b10000d494a141060410100c9190301900031914000c04900401411300400c1c1c428000501000e0710a07000e0828401c040102c54003404186c00784074000c101998a030140303076009510300a0380341d071201403078403194107828a0100c00083c060703400c6000301c40395102d00702901e044a8042c00c2a110021041000d4001391196035800001145049030304035050003254064803290048108550300e16407030f09401e10451005403110140920140101e101543c40307500a00e90042c0e100e403000c1641000c0740300da003211000a810545501c003a42c1c40e1140b00024502201d40100040e28040c0a081c5112001c030340c1b10900540030520003500c802490908003802d40445201d00c00400c00c4640b540360b42c0d80055111403185c046000050300d41900c0f6502c9110001c1524002c04039a0030089c03030310060b081000010600a0001018000000c0003d403100741c1c188a001c3c130a01c0748110241b10010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 143496573 1250 143495323 143495333
    0x204051e060a03030f081e040606032a1e1701051501030506011d0f030f16060f270b1206030d020303010f05190b040f0f06020c01140d27 60
    0x800070059401100c1010003000440d40c4418000d020f8042e904020300a80c644c41d019a510b482403001c0640d44000d800b0900c010402c90b40d0000049034050303080b00190722031000c05004d40420b5800082c11186c0408424440d0301095080798038014802190140c04c95683e2150300b1811140340307034582069641e0000c02101e8030208001100c402c00902e0108024a0000e001038070404121054034140840d1111442040e290130b00c12000c400802001c444034201da086d03409645e4241c5200381c081803908004000f4180f40629900e40320103540c0e03103640503012144600703005c05480e00500d001c3c0041e40c03042e00040410019004004c001100e001e20740d40c6140c914103252801c403d060101045510070001000017801070200207003a6001110b140c542000c001e04807090101654100324a1900005000245401034540e29070031540703000c41707a02c070325561400c0682c1c03180e02082009003c283c00d07580e001820415880104401003a00340006400d102e1801aa01d10b04c61524400b4a8013001c4011041806 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 143497823 1250 143496573 143496631
    0x80a05070e091603140c040f02041d09030a050a031503150b010c050d03020702061210030201080a060308030a0c02030d0c020606040b03160b090a0314032703120d09020405 75
    0x10800d00010a0701600e50f0000d00d480b5a0f082c407024200c407002c0c1c801c0a111080c144051142084001c0c000d0003424907106004000b94424032903042010b441c40304400080d004404001d00c100d80d4a03016508001c0c23140303c246c4076030380101c0324001015901c41480102c903061208480156000e50002401d40c0316001120040303030091022241400b03c0b6400c2c107400264000ba1404440401d4500944c45c0c03415880032802c0c9020340d04070b411200d0f906030304011669282d009d000084a000742d90383c41071a120702401c6408c840c000e0202624a1508200040d240f04058008801d030900c14030482e480c00400340501d5048440e00c104900058000c1c0302400528a8107009500c1002c40c04c03005000c41000d603291091210ba81441031003100400441c0c81d06580c1d40f54056000110f070444424981c40b500301d41c100fa01d903840040c407400c0040d0900c0c0c45041c0c1c0030444010042c05030020b40100282c0b0b1800f503074443d55800c10503034110001d80f600703010030040e12207004d05030090f29107400c0108034602c4425241169 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 143499073 1250 143497823 143497831
    0x40807090e0f070603112104020103140723040503030705010b0108010f050d110a0e09070e07030902010f080c25020a090504020607080705100207080a0f08060a170106080a05070e 78
    0x207a00075405088401c10100f110303400c5500c0c6040c0080e0508502c076241e0864083c04e15101803454007290514158592030500034890f81c402d0341c0c2040f4420b00c441c0200c21100d010b80b00200010614460808901d08841c2040141c2d9110250786040c641d8900001c1e103075611000e4212856510b4851002441d44c02102c04c6014000d06501c41400c9420b21001c59450300d200e0303002500c054410b2500721880c1c0c03986540351015046510032060f0929000c8112551140c2c280b0802c050007d100d000a08128480d208807840c0640c16034523884105c50031001240e0152000d003407401881420041d20b11120030710a0321001f5048880d280440010943c01040501e100650110320118109420040180d80e07120448803c203900c18102c9441d103000342850361410a01800e800034903440003400d0414402c01d00e000d449041000e07502c84420400309502180c10f80b400340d0702240c1107481c80d201030066103034101c1d6040b210210100001842d55032244001d28080220030300351283e8215a8080c001c0f1100305d5070084d88 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 143500323 1250 143499073 143499101
    0x4030504211211060601230d060323070b040e010504020d0e010f1401090903170c0705011a0405130c15110a0b09070f050f0105180307180b09090303040b04020a030804080709 76
    0x51a14944003150700c1c0c1d0301f1215008254030001c0c1320301014200358070010155400180c00203101000708141e862003a071800e0380015606c07480c3e00004040a00e002182c050340d41044801e0305c1c3c0d07440d10b010f000c06504100300d240070341d50b201c070341c12440820244501001c0358101c1d240480c048101603162060610180c0000400c02e00702090880420340000030480c0f00007842004d2109070f03494803499000d5010b400c0313000700350b54200005030804142e0382244500010b03044900b0001c0d5142c000009003210205280145a24905031041045020b040a104200e1042d401e012031601c00200c001814801030604c00ca950614a4041c4480000e0410110f409010b5041e9500141170400300010014070242c8102c9041200005010000b49a2406580c03201d0074040c003120000e503128a400660140020078140c00d1a26010250100b880c241040c0c5000d20390100c051440c644071b41e240c030240841d0040060b030304426030420003c001420b01000700010161000640006400c0c81d81c00c5055403011408510 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 143501573 1250 143500323 143500337
    0x12030a120b030703030c0c0b0a0305060108090c0a030318051c11030d020a0b1b0309010b030c0a0f0b0c011b02030d142e05040c0c02090c0304030504211211060601 71
    0x10a4a00094010130350742c0605060b03030a5190303840c001c805d098040e00000588200801e50512054068002c03500035078098031003400e40e0b07407101e0f04560b403000d40340040c81d8441c0c3c1000007000420300800d900b1008202107050f042c1e000c1c0c0c685c4089000e1980844903003501180100c000028088209104070180c03000b20007801d00d020300f080c4000d580701120f01c00548440c02c4000400c48030038412906101c0d128001401070340380c0c6810702c0d071300b8000e00a0010260090141030b00400b458500740110b08151010604080b25480c00d000007080c85030060910180c0c4c665940011460415840d203820001c240e0ba0390055a0340d800d082001d0301070b1341c4c1103480a10b40c1004034050020000144803505521060390b0062001441d040c08848150329070347d4070054100c0d1800341c0484107564000724410449000340c4d08003c46482c0c100001c13069100440740600060000e010620401040c81c06403080056101150042540c10b03403140f80da119a954540f801284041420008160080c032110350b00013001d0800390 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 143502823 1250 143501573 143501591
    0x203070b01050418081c05070e19060516060209030f0d140a0f080a060f12020103140606030718051005040e06010806102316030909050408071101020a0212030a12 71
    0x1907148119004003480383c0854510085510f0b880407014070f1302001c0060015080144009c0d00100c19041c2d294054500110102000c2465101d200700710380459440034a440005502850001c240e10350848095400300260031301558208854140b61701c03114040e00c0045508500a041d0003c422441c0031210350a221070b0400a40003010301100d520705040c010400c1d0ba81030380b07c03c000e02b84d540080c0c6201000c94400700d4407d080d4003046c10128800c0c0c804201c000b402100500c5a94021142e0551002003000043c8000e44190208500800380c0701881c004aa12000025036900302c56902400140c5c2c0407500b0040d205286040c150041c2c001c1c20300c15500d04146000c61000c640d100141c40c14403402e8061352042c0c81c4664181900c03250f140c2c044a40310001140c0e82c03a441d2440c14400d40004200003004680e1034181d220f4980031b158428000c1d807400722140d903803940383d001c40e03401d550560044100200252715040e0050304011825401741d903030380c11503040103132070410981c8800000f54584100700f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 143504073 1250 143502823 143502851
    0x602030304080a0c0b07052101080c2806080a0c110606040203181005061206101802040503060403090e100b04090209060c0312010819020120010f0c0203070b010504 72
    0x1241c01ca40c00604250b43c50f0580d4805440324112000b0041102c074140c0c041141280d8840040c1000c000ca002210300030842c0b820091600c00d80a01840d0566040355100200d9440c101e050700350519a54007101d240d041504520001c9003a00740e003d20b021603e00000c010107000b1a1240e0110f01340c1c02d0601c0c50310308640380d0748141d1341c5400910460080e40d000002c00d071900c259a9016840e41144400c44038900b04086048000e0b080079914640901c0c0580f40309403d400c804142588113200407113001d0079403031030b06038100805504850072008240c2c0c20032003c100c2c1c0c1c40074800c180c4140c0c040c0d1034580740c051906084152402c001841c07240c1000581509000441c0142c0480e400c031204020050303111540000010450310a1200d44030301d601c00010071001c0344840f00703110750480c1c880e102038400c4002403401c401d0b010000188000d001601c10807038132507181207840703481f0081551440001181a403a0b5810701c2221740000d00a03003d6403004c543d010410410420150250505032814012101c42c4940 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 143505323 1250 143504073 143504077
    0x30d061508010b0318071505090918030f0d0209090403020a0b010801020a05040b07050102040504021204050c030106030f060c0905210f070501022806020706050702010b0306040209130c030f0b01050a0609060203 92
    0x4041152004042900d1642e20801042c00603001e1042805500301c0d0050380a012a408540d03030351700403031552b000249810b08402e141c0d050300010364051071400300030903c0036040d41c0c458048142419402e00ca45c941e591508440503100314801e400802c4401403e060000c0183c00507402060160300402403650410f900406990465049514050311013041c0d2070858003a000715004540c0107071022500c1c0004558020060b070081703000b007003a070301d118003004107040c2a0344560001910960700901100005809a070102d220000145029079005441706c00052800394030140501e1590421208007080300020711110941940d502c004282040c60600080c0d2a101e406a400030440d0b82460501c907e05400410002d8007079228000319501c612500d4004002c0c10203503500c800561034546002820b04000807218003030b0750005e0148541382e40b03070380c40c0304262a5102c800300c43c1000e0046000000031807401c003202d040781c890444048658144014441001e0040d03000008112460204200041d00841 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 143506573 1250 143505323 143505331
    0x117010608070501050a02120c010b10030c08150609090403081f030b01060c1a010b040f05040504150506180c1206010207030807060c0c141c030603150e0f030d061508010b03 76
    0xb0002d44031b2600c10001da08022102480160b01e02c0b0000e02560000390640c042e4280210031071340a0b048105c8203604a04072281110007001040c070324008900302c2950304041c2c512150009102610f0640c0c8680410290581074038101e02003000e01c002d100050b88400d404002c141c125002e800707512484c41d103480719541410f1207441c0603c40d000001000384a4480344c002c8140c0ea203a0820003695075104412210703079000b44904841408450004201c901d45406480e00554105d6154011822400001d000505000e0200d50384085138002103080c0105d802c2882d8840c40c100d20b00151941e84400c200140e1902c0240341c9811500004024400580c0701020b07190010740100000841c2c0b10360315403d444d400c0895402601c1c4011800040305103d000158044620024020078400c24034106815801d0301d076903000080150b91030100c1d04046046582c8950305160f0381c10101c4810641c84c0407400d0550b44043c8068445686030002030082c001940c00803030042c09245014522580341031030140f03880c04007030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 143507823 1250 143506573 143506577
    0x80705013303150213120510050106020c120c0a0605040e0c0304020108070c020f060d0f06060e100809070902030c0a170408160213060f050301050606070503040308070f0602120117010608070501 85
    0x90b04140d00c1c80f1055041e0748900c40284d18840c41503445141c4242100b43d8140c040f103041c4503528810b8801800c600816049407265001445061994820008503500d021310080c076600c10704040c610302c2d6840600c100f00515064548a5a40341880e24400302160010065400d03010104240801030b640702d090564042d580d03240090401d0a0f910006051200313070700c005580300b03202080c0d0f0500c29a40f0b520078049000034060402211b0f98403041511280d9a070000558804d09080c3c0010502e070084142c0359000c20404103032001d09490384007a2080340c0084c0e40f000320001020802c3c07002c1c5a00000759001154980300d103a00309240a594601843c45180c0b404070702c010f4122008000c54a8a0844071030000a0105c02e0040716156400e4094116141c0301d580e100e503080c0008100103003008011100626085000f41d45050304548508849074401f00c0c084588000f00003540c404519288054007079400c0c4400e01c000254500840401c5841540c8412100350349005400c1120f044001030705000c0311028 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 143509073 1250 143507823 143507843
    0x90c090e030a1b02041119020a05060c0c030c0615100329030f0604060c02010c0c0209010603021605010204090501030317060d03030b0105090301050112120203180913080705013303 79
    0x1e80f40701480303007101c000c000d4000307040103010386140e459803014012900c541c10901803084406001240d442c1820f1034054203a4000c4400314410503400001024004d031010201c9281c40d0240c91041e103464401c072190341807041e4903001c03405103107002c480c006018041071400b4072580030b01465102070800546280c13945059200b054010944040c000d11900501c91030582d503542c80e103400c04101030a120070444006500c1c2a08480041e80030340f499a00300343d00606070403843d0303003820000e4000b90300c0320f0340300c0c0035940d4800f002900249090000700050903110102151951451034040d040b001c99052066800e076483c0100421602d0704440b91b490a83c2600d40032480c1e48004005071400d2182c840c880e80c055081030004154440e41d4080316a00b240b00b036040b21030f06034800000720703124082c0c4d14048081400da0300304551a8030301105429000000f0303500d2480c0c03d0046070780c0c00c91070383c1c000300c0225650b0f5182c140201004201d010200301240c4440310305981c0044c20035140c20503a9050200402504078 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 143510323 1250 143509073 143509097
    0xe24040c03091a0910020a170414030712020c0607200f060403050109050d0323040503211f060203070807060608070f030605070e0f060a0c0b0a090c090e030a 69
    0x110b904107200c81504151103122401c5082c1e94a03401c1d80e0112100401440b8450032200e00c84820310880703e4504090351554240421401c211003407410150064440d40c0c020300c0c00c1d110001082c001032002910610052a240d8090180a401e241c1101d408622803401404800003160480c003401d400201402c0c900c0032080300e000f000070180d1210640981d084000440c0210421a0552001e0062401002210350741440c14408a090703410707400401c02c40030403030303105044000d204880d401d80061050007038a090140c50300e10380c1400302450450801d040000703000d0100e00c0c03507102d0070303580300ea204115900f800a0410901952b03d10a000004024040015611043c4142544036030054042d541c191500a642c070f00b240c40c540c0c03d044c08103442d80c07403801c0003142c40603014102012010201a14840075a039500e130411107990880342d103020a01044000c1c84000440d074110440c80385003018000144208035050402001c940343c6c01c000c1032246489503803011070000000f6181d069040f89400034081039 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 143511573 1250 143510323 143510327
    0x904060f1a0103050f01120b0901020418050114152205040e0d02060a02090a0b090f090a0c09051e04051305070905011d0f150a05031203010e24040c 65
    0x2600c40c816050345180c618060001e18040c4010702007201d00340e07001d001c0d54071039558208100000303106140c40485001010800103049400041e4400c00c14000103043c660b0324002424140385040d91186055a41d400611040c0e091000203181c03024255000c1304c03104c1140c45071030f805e03106e20301070007401500c2742c200d524444105046440291801400c240061310b10441844c0d03880d03036000500c8006d80100c500050040c40f00b4425294a1100280742f540d010380780041c1d001d003642c00010341d103401c0360207010b80c0034680e00d4410100d40207001326540016110f10500300241070f02e01c0c6400a80c0b08001c01c080240e10385d9090b00e440044c1801c200d50028581e1a8110702c10720350744a00000074124052905e00141d00d5640e540218101c440d40d8241100d40c10f2118402c0b00c00c0070080740c4e95402d080d159004035046244005400c260340202410401c4425191000285407200100200d102640008014009004d40030600ca8103e02c100d00c80d032205031b10001080b55440601c0203050b006903920324402409038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 143512823 1250 143511573 143511581
    0x1050d0905032101050d0f060c050f03100510030b030a110604320a0602030307030903180305100b0f010903030f12020a0e010914030705060c0715080405010c180302090406 75
    0x1550100480f591080a45104981c40420300005a003003e852400010b06042010744003017480d902683c103090090715a51030707400505c0c00d1980c080c02c105080c03000008825414000b5401a409001c1c2242054980001c10010407a0150301104040c2000e018001a403000914120310705c2d031154070100c446034003102150540c00385500c00f82c030301c00412111142c006d1280c00c100c0e500700103650312032483d0480d030303418042d005074079100b480016401040051170301e9200e60f100080f01d501c01d00d1710450a102120050203070071380c1c076003080c1d499400449001114440c00d01c1403909450042d00c00c16450004000041c02041c560b00c00581842070780c100c0320100c1885840b0055003030720301b00d10454841001140040000440340001c40c00b0840c440360200d04c0200700040d4440c030108c0140248040e40c1410244800e5400c540304000d0700f4030a0107070204a80c0003041d402403c11080f0b6840548a03d802e042a0782554000441d040c1480b141206411004007607041d0070081d203805656a1801e611103103000c030010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 143514073 1250 143512823 143512841
    0x1202040b03061e130201051c0e120a02070f0311010f0e090f040b060103050c03010504020d06081c09090501030203070e070e090106020c01020d020f06061009030c03150c050a080601050d 81
    0x1406071900300140004104903e0040034100c00c2002c40907540c00c00c0010b42140c1d031600203030102e00c0901014100494800143c48001d4000c40040b030b0b448901c440300d502c0c1c008452040b408801021441c0803c0c0e50b410080d503801010303001d40b81030500d803840e11441d0509001c840c10b6030400c60740c24100c00711280101d41900a910000d040358219144c054002c24050308103079401c94440040001003200e540c071038002c2500808000595030314603460601080001c2d8001c6510f074500301d40351000080c5144e4107100140390314011800da11081c404001c0001c05140d02500f01103103480c41c107030041c03001d43c41c002041000e0310303140e41c200100c40c0c0390014169010041480700341d500002072000411201d502144030040b1038003e808841942c41c010a0a80e20f660045a00e148107a2140c00019614a0400c402c24600712040c2401941e5503165103e60078a008281c10940741000a11011415100b81d0b129080015049141c00d604091441c01b000b8050710002d02401c1c1088801f0840e0924030703a840c0e02c04161 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 143515323 1250 143514073 143514079
    0x70c090221040602090108071728020f0d0b030a0b010501051b1e010c03140408030414100203010303180608040204051f080a0203010509010603080d0c050d0507031d161202040b 77
    0xd0703180c1407803c80060360120009900007001203010a9102d8000c01d07207903498070a4403004401c150b803903401504580107025035492580603c402d5081e11031800740700425850f20400b0071240e8440c034840720f65003503880b0050454025440b150b9404086a251424141507410910304103a44400c0c1e00e0725500e1202c023180b4600c0c01405201d8000c1080d909528900300102c1002c0005d001c2c03112540300a0f0704440d4040000c81800d640c030320019000501800046511900c80c4030942500840590500e1418201c0c000046071703141d0000040c4241a08060291021511890241d509508001006100420107040280101d440d040401c8000300e40394420001d45c40c502e401040100d0b030b5005840d80c1c0c1c440489081c1c0c040d529000100d0380d40c00701030040f01d0940b500141c42c1d520307042d8440d810800400c040880c10003044814040d40401e41c2c030601a2500400640d030740070401c1c011340c0c010641000205900d90300258402820169540420101c2c0b0040b5001070f5400e81d005403070b030700108015149103001503034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 143516573 1250 143515323 143515387
    0x60f0a1211030a0c090b040c030510050d020402210f0f010b120a0b040513021206101205010608010507050403060c082a0c0a23010905030f1b1e010f02070c0902 70
    0x1d00101141c0c0b29a20400040361f0034806d103024507109078219a0251519140a01c5802050010382801042894403a10240c001464075040d01c503030348600340929620614100f44001030003401c06881c40d4250700b01c2040e980804007545865130152891140d02420705035500440000380140c01140d2001c0c4c00024042e0040c440d41c03500400c14003c1501e0301c00c0481c0b00b4895486c4008001d0340c0000d50b42c0c840c1d445080442011030a1140891582034003940440d03a56403030300c80110b1040e000380561402201c5071385945450354218a02041542c41e89001501045a01810404008203448080d18a48810401c007404070210192000ca107204002d442d9182d480307000480e80801404c1d00d141040000401c40810a0480c20208103098406c40d4202500c154414800225640c0901d40100512080f11218901c41d42035600c08500308903600c01241c000070f0720034044010a18080c01902880748401e070045140104955504c0403458a500801002950201d003068011303410108068100b11141400b00d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 143517823 1250 143516573 143516579
    0x315090a06050a060f090e03030112140f0a060c0509010207031205040e1503011d0304051c060e0a1e03020613060212090a0c0609141201180308060f0a1211030a0c 71
    0x1070702130078661044402003002ca0600180c46000e0344140c06031915400091855640b038a4480c0460340c20390442943c28004801e80c0d80d035900e000304003001d40c0d2260324000d06203602443c10120100c0c2d9210207824140682001400d840d81e03070114100042d2648003030308101c820700b81c1800303c8880c011600b0098010180c4000d02000049020072194400301c11030080c8288450201d00c2d00350341c665a9010049035109020a020301d05e04921001040d420141400c02410341c42d459150954800100880b4250031481e80d100c140f20424441e142c1203101100c1000c1c0d040040e5600950b40c0400400d024034181003040b0340f50400810b50111880a907202075084180c3c10400c0540c1e484641c80c071070858400014210009240d07006822182c11510301740c50700403141c1c20f942d091000221610b114480d85c2d541c0c4005c031603264428003401a00d41030003640c0320011850001c00b882101640480c0740b51080c02004004c2280d0402c481c180022180e100001c9030418205002280c900142c0001c01051002c40c001c1c08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 143519073 1250 143517823 143517841
    0xb1605120423070f08101e020a180605090a0b090a0e040602120103032606010c122a020909070305030a180e070302030a05100b0d0b030c060705030307080a0b0315090a0605 75
    0x2040d00d1800f41620500112441e08901f2501510740c202c0b41c19007410400715507000c1c0751b800340c401d95100781030000340300d941c031400c0010388412031b08110041040810003c48600b442c0c018a00904401c441840c034202d804000038107800210301c0703855410700d1001c2c00101000466010345290790000900300029503140e00c2c0182c03c0300010044d003941e0341030003030781c078203540032031310241400756006031036110700c0042940324803d00700d030a06d04100c288040300c058052299440c22005240710355102d40c20b1002452841041390740480508071000c10350202c6c9090001c588048201d0750000c1560411124018048040003540c1d902a44034a40c100002c804006100d60190000d521804001d4130801640e82c2d88202401c141920f030082203012001800514450801ca5000c00390700b14000301203802e020080e00c0022020340c0004d82c11a40c0e40c0001c014449016004054541c020041420a110000310500821394030380704c0003002c0d02101c070303040046420f491040c40421407561f0010401d0046107044005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 143520323 1250 143519073 143519099
    0xc03060b070b091b010c0b06240406090803041401200102030903121305060718080105040516050303160b060a03080703020d0801050303130b03060a080a0b160512042307 74
    0x2000c824001c4010080c5503e484e0401c070704070400705854194840301542c0300d15041040050415402001102e6445804406505070070014504036451942d02c0b401c00c000203200b40b1349a4030032090b9501c1404140300304403015080b100b9a80b000e28001098951003009a94075510f0b650803a401544000148407492601100620b445c2d9003007860b00e065a12001c05980d0002c10488020b131864000001084415101c2c90110322030b9101414141d8016071240111070841d42d00740d800b201c5a91007003586401d802a5010b40000401e801c602450405441c140c0a10400309490401880e002c5481c000401c15a28154a00055501b020590f500c400c0e041c03030081d6403981c0c40e80c03240c00440c0300726000040310302d40001200c11050081b1030011042c0c0c0390013004042500041c10711030b800100b603240422040c01c10452402c1c503c1c003842c02a852801c00352041d021005a0840b0541005820000c000c01d12310840340c1c158000d580700d0800c800301e41a580c8101440360070358245450340d0003038180001c0c82c25000300f5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 143521573 1250 143520323 143520331
    0xf060f030103050a1b050102030d0c05041d091005061003020a0314010902030603010b0a06020a1b030206030c12010b07111306030605090318030a020102070302091e010906060f090602030d0c03060b070b 88
    0x211702030381c2400b01c0510162001071032217040d0050b842000040001c0d070b041d8210307103440c21a40c141182002e0b00c58009076400b00c40c03600280340d44d0307134803104000001c0c5007004903010f4101f60314000c200b14184000031070840c0000e0860740703003030503000200740c0282031080d0300210094040e428040300c256164403945019500603501d1a01c80d60030b2464600385032808000b0001140d5080d001010301c09507558a03041e0f1103000090650f0041c500600020140c3c81c0c84000303521416146d024a6904d11000c494200000c0041e04035203880c070000c5c0a5180042c50000300302c05294000c951103441c1050a28080c0c0103801c9076040100a18104810f10100074000400703009802c071480d50b08a038150300c02d03051540e1254500d0001e8010f901450b820005030402441e850742002c2005001c104d581144251904012020383c8101040380e03803000100301c00340d03002075103190380700785841d200c5550351503c0d200950b24020641320030940396403a5024202030f40030b680108010310682c0b40054a8041c1d44c18500f1a0200442d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 143522823 1250 143521573 143521583
    0xc060703050a1406060301050d0f0605070e01020706180b0705030d060b04050a0b091e030a1205090111031603110307021e0109120f0f140f07060e0102070608060f060f030103050a 78
    0x482c46050044210f0b01500c211006490a41142e2808d000c00c51b40c00c44038001235a00050504031900411514003c4911a000c241c4481e03401d9101c809c00245007004683c000303400c100141030221031406040f400d160840c0c00f01d6a5468035001d06042c007a080d072041c120603030015440c1000c005034a516403c0a031080702c03011144102015900d032005000b030b104041d1119803000c04401c000da078800c413590312040301c0c0002030f0889242240547c0c0b0004061203a6440e4000f091000c80e1041701c540c3d01201d440c62a52030170340554141400c42c10341c0000407029070300040038001030010181c00d590b8104140c0d4a4642c00400001050000d010042648001c980d4000d000071103841001c14208a80d400000c8803035403054404201d0382040d201d2142018181e03804460400790b0781c1007034118046c1086040501784965008e4444a441c010300a8010200c1c00801415500640c804112241d00040300641c410010b58407101c0507a01c00c0f000440c5071290300c000200469000c0004800e010b80010802c001d40c2c0303d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 143524073 1250 143522823 143522831
    0x108010e01020a0905040e0118080c070506090303120405011815050105010804030507110303280e01020c0a090905030910110111070f060c090f06020a0303050a06050307060f050c060703050a 83
    0x1150806090b4407401c0c1404011580120007007041b400e055004400d4181c40b50000500020101d8146234200c0b00b900c000d8555960225000490f40c105010704002080201e491030715106481d00820780b2400b60011081c81c070380140e030000d000e0100039040501d00e41000781c0e41080c4040e0300d103400d00b4440010b00083c40c10524100c0045000c1d4016100203020301e030151200c9007031880b0303541e90000f20819000404c2d01804144280d55032015556201c120000b06100460f000c0903100381d00401c031024140e2114115400081608500c0d10365414bd54181c9560306c401003034a640d2403c02928522503001d6140e080002d12551021f403d6000304501407903440c41000388908200f0800c110264000c0282c0580078010b40d0f5a180c0010382c0c0707a400191448420309004801c5540c817164640307004840c0d80507a002d0381004400e00c080681c54801c10344e0194030020208509403c0c0380109640d0141401402c0901550308030740040240940140c0300e00030b030103404480c0725144c01c4c10002e018020a98010a00c5428 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 143525179 1106 143524073 143524091
    0x11505090622110403121d130207170309070e01030302060f06011209080d060b0c1203071110060e070206070f0f03060803040e0708010506030103030203070b0601120e06010801 77
    0x1258403c0e0340711840d40c140b03042510341041091041180b10280307400d4000c00341c2a22130305120f01b6070b07071550704c0c98030032a281000b4495544003416400680e03610010f11500714008501c620340306000c0d1002a82d031008403007441c1a003800000d016030003042c00100c180130011034142d07004005150048100c044441c0c82407c880300c2120036565008000b45000124650340a17100007020220100d510f821003100006466030621982c0c041302c0f40001010405940c4201e503118810b4000f5010f9500700585641804014812845828140300c4101300090b1468004228148210b03034546500f0344201c80c2510484640b01280329420903d80e5403c070101c0c05510800207003014040900c0b10304114102008060709242c81603020342e205844c1003005100107680482519140c0b54050700303064030b98440c07400580d04001d02100312200381e46407412201007038400041540c101c40d0884000c001c841a = true := by decide +kernel

theorem cover : BRFrame.Cov 143345323 143525179 := by
  have h0 := BRFrame.cov_init 143345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 143345323 ≤ n) (h2 : n < 143525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
