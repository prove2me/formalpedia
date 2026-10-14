-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1378
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:40:13.475825+00:00
-- url     : https://prove2.me/submissions/f1386e5c-f1da-41ac-b60a-dd909b2654f4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 247661870 ≤ n < 247841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 247663120 1250 247661870 247661927
    0x40809130b030d020706050a08060307180504020f06090d03030e01140f04170f0316020703150605040e1c0813052b0806060a050702031204090c0206011a040510 70
    0x141c00a03103001c48141c00301e8140141d0780b2000c983e608800e00c2205c01180080201920b1a4840d40017590f0081c800350444601607030f070744081c644560719010004461642da030140821031030100c140091401c1c0849100c0e0070542d0810010f6810a401c900041c103255a40c40c00c05445142900440e01d070488507100c0c81850726020b1070322001c1c3c03042103404545804002e17411407540d020a030241c500c001410311085044d40da912403200002c5000300041815845100800000120145d00850000c00d46010209455150070140020707070b081d004406c0700725008441e00c02c6c4600790b80c0c8442d240381001c5150094180d05c800250110103244140060802d01941c54105d10103020710342806525000c045183c014480040c1c000c0f07803840b4080d1441c40c0e200404204001607140b0403070140048a00003001d645841c14800180521607020354444040d603912241002500c0f034051220320300404900b02c80040c45840c1d908402c940d0310460041a10802072400c60301c80c02c910032861000c08804084070703650524500d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 247664370 1250 247663120 247663159
    0x40915051002061b0c1203040f0605010f0f050301050112020d080708030f04030e010c0308040308091009060905070506040f0902180d0515060102160b090607080d0507020105060607021008040809 85
    0x7210280c3d86002c003507242250083d000405c4402c03010351040548404882c2021059060744042c1c403d40e43c03031380d0108071000460104d01c01c0718000d1241d8244d41700040e140400003041459160f000e184a80d1610340100320151401c210b00d10402d604490503148009a45003985860107410809086020080204800e800309115000d004900075240c50410159003001102d101e040900010001194103010800003400350004940003d410380c142c54800d856400914221000704a060b034010f615600300303009000c800d01c0075102402040e20101d2426052152400d003000da86d100e183e2429600240c906030b52a002180004c40101c0101003901101d07050500d03075601c81e40d580a4501070700041000c104150300000c1c54502010506107449141841c051400000f03411448844c1d8105a0402c40403001907040303002071005010b6035100040c20f013051740d0000c2c21964000d003224080d000c1040510096641c130013105140e0000c0e481c02c3c0003140d81da450581d07c40c1c010b10403600d4000d090030703090170001440e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 247665620 1250 247664370 247664383
    0xf0a020304050a0902090105070201030b0301021e27100e030a12030902032e0203040606030f0b07140a0e09092803020c03281b0b030a0e010b0303040915051002 70
    0x70100c8074042e5154a8070410f00880c89403c501b0783c04034004225200043d40070750001710024100034001414142d07150f00d0101510b1062128035041c4a0000c1c0d90b03850b1814440c825081c2c4401c40c4040c00c017510081000c1070326010b1002d400c4d0b080c00001020074a040d5020070039126401c1e40490b600214002a41e070240103020242c070228440e00803980320307900500400d081e4030350051951a0351803081c070000202c04029400a80280c1d00307643c0b203c0f03012000c680d80400900049100703c0024042c1e2034540c8000300f00c0038550b0741c40c0502c0301e010401c0c00c40484c1d000c440102420300860315554113882d0310154919004004400c100d41c0c1b807603000d01307804940800c246400140c1c00f03a000e0352440d1401500705034641c00701d0219401d41c42032024402e42c05070a2201d81ca80550300ca031042e103400500c003080600e16994182d02c0341d030840ca000400c0002111f00c0d0b001d04150508090000e1103a0b0601c8800207849008601850980c55681d1449062082c5034a080b1402458060031020504604402c000d48488 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 247666870 1250 247665620 247665629
    0x11e0603060b120d050702040e0d050901020f0105040302031b031c0c0e0102060f0a020901020a0516050a050d0f1b0f0b030405011d0d050714011404050606040e060114060f0a020304 79
    0x240350640b48030441c100404224051400440640346142507403009464580051000f81d801c1542d42d1083c204a01082000100e948441d848441e00d864150f400280360085840141e0010390402c014400001d80000a407100c000116a042400c001d510058601c0e40c00354440c20031341c80888404280c09010b01d90700010303024149541d00062401640016a500d001c1610782603c0408100000b070700625a40c0e02030001140141305490703c0319540d4030b40920300440c0000351403049880600420141c5000710b04207009080580e801d400a0910351075400172144104000742001310280016031a080c4005880000b030042c60b10500b00d1162210768012058008840844080d860184103d4418140c0c04000020201d40e0000b070164070382883c0700322450b400c064000c0302e07140d12a515003011000203005009001d14000e409000e0340c50941040c41c6444030140c40903000d070f80b804004410707d06000c603455040d503901002001c059103245002c03c0c050301c03409154880c5008007061061403507901000910071117 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 247668120 1250 247666870 247666883
    0x2d0403021b0616050304050a0e100909030c0b0702070f03060212010504110f0a21050717070507021509090702030a0f0509060702010f0e040e030903010f0e0d11011e0603 74
    0x350000e07800c0041207402585a40c000c4080c000b95851200310020030741007034422400d803410701707649002090303030003d0540000010b000390303c04202c03084056400b801c1c010304a0782c0703081c04900707400d460103041c0180000c4043d180101450018500300e008005880040090032802c901c0b1554a0411200035041212504554081c65000054514150140d65035210701e00781d51074500750421040310016449141c1c48014070030000c516038001c0c44401440c8441040000300800d19141c6944001d1618481c200401d070089048810310100f02d0340082914080d60781a5101c1300000c40811a0509500900c81c1c000d038428500010010160350100c060040e80c4100d460307000342009018001d84450064a220a40004080c00030001541c411001c02c106155242002c0161f00e0854020805036070b112020098150700011b03205100e81000d00c180d0030702500d011400c000e06400c450006890380c1c0c403a030900080161170929803a02110a5000c40400306058403600d15030100c2c02d9409003d041c1500c415140d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 247669370 1250 247668120 247668133
    0x20909031c0908030c07112709070f1520070303020f0606060f091909230c0a300b100c0b0c0a090503060c03060a0506070510052d040302 60
    0x1c110a4042c0403070305580100d1250450b40c80b00d81c1480a80c01001094480c6070090040410705d40300c00c103e000c11400d0f80b1710032540951001018034030320300c0043c16009840e030001a0400a461001090301c081c0c52403a0070a41c420344c0818000c4400751802500d400400111000d003a00d442c0d8001451001c0b24030a0300cc1d80c404000d83c20005032105c0040f074055800c45000c201802c0e450040c50028040208000c04d41c0703030490451410802d24507950341250301000c5c0d440340520103109105007008107140d0280c0003117126280c8900214040d02600241c0810f01844005032090b0034200b0284101e8011070203501c42401c404e00d5800c6010b40344d451000ba024014242c1c14649040c030460810320803d411034021305080d00c4441540f1080d03400003900030304000c4a0307e00400c280e9020f00c030b400c1c0510390f0260010745a0925070100142902c1aa01c40391240030200000c0001a402241580d0380700302c6100d001455540d08200c24405100058880d003141002c210784000c10a01901d0641c041c900076801c6850 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 247670620 1250 247669370 247669417
    0x423030607020604060209121501091a0307030809150d0504060c030c0f0807090b0d06050a0506040503060c0a1e030e331008150106020f0318040b0a0302090903 70
    0x1180c9106562100043e0403400000f40455425001003403400d401a000c02c0d0200105031140303041c4208121101c1e100c0760500010021640c8034010b41040c18100680d40880180310b40000c0d41e1b400d1144001408080045810031041e62241c10100d00c50280004803640c0f0001781c9400c00081404560813544680352807038102c0454030a00c6141c100c40b100b52180c2080c581011010703500c401000f090601000b403c07103801b05e0401000d0011300b80e80c015104000c10101e00703010403c4030042da01c0e000f69019400c1400200256900028142e410120401c2072955900400038103c0700304072004403240d01d140d04880e01100340c40d816440800c0c9141c002065032440f0002c0d069a410000c002c1d52900846161481c000026180c07144040750400b6180700500c0c1d05030368803203040d0b0800000c06040b039000401d01c401008801d8050020101d41e00c9d056024601e000b02e20185624664030700145140140d65500c1181c03400d454541c02c00d005184c008100c1181032400003200c0b95a45d004154110700004203a56001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 247671870 1250 247670620 247670623
    0x10602030f03011e081b1f170a0204030f0b0f060103060b1803010b030a05071e15120b120102030a0e06130605061807020709050f060307090e0a08042303 67
    0x80c24484400d030650b00c0c1d646403140300000400240c403032600386000c0180004540e80c040101d081240c96610000c031104201c2010005900307544101401169560f51003000415030200390702800b10300140540c102c03501c0c0d040d02c040003405142c20040100d10248400f10600c110031000d24410b80d01008512410f60341c900045058603141c0c41011089901480ac6034510140c5103126020392502400000312268014000380c0380c50010745041e1000d401082041c00000e040d044040c048501d9070402ea1421450580104807001300046410200704a4501241003150250420318030360307000620403070304880101300b00c44c000d52060b124401054580141404003910105d112441041950650920906180c55540282c080140b01c01c2d030141d40c8224080540741c0042002c1d0040041e82c1c010a82c07a401e1494040443c2d2000d491083c1c000c45060810a156030000b5000084e41da48143c01b19501060b108460314101e680304008000840100d40800d080703880c18440503c0504144c0a080115150750901d03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 247673120 1250 247671870 247671877
    0x20a12020a2609090115080c0c030306010c080f0a170105010f05040e06040e0304030c0302130b0d2a0b03040c050f030712080403081b0601090507020c010c060b06070f0b01060203 78
    0x14034241c2c8140031001c501030051140c080d075500c2c19220703c1c64295018001160044240c101040c00b02c8210540041c5c158080070030350788401c00b503807201d10340300390500020795900000740345c1c2d410419520b21074400c0103007880642d84074640500b0826181c4c19690405800105001c00002d0443c40c1c61000181c15841603e40304400314403a01e80a141c641010004140c0e42030003443c0da50002e490340000c1d0940320081000300b0045001d02d05441c1d0107415441001540c03008500c0703409180d404d115092041d90380b900844805164012783d030000080200c005010010710b01d406100381503111a600164607660340303000354400e6104071041c012003034498040040301a000e000c0c40780c043d4001001400101038020a042c01c0340e01440602c3d080c10b40d42d41d20200c5c2d0307038400b0850000b0000c00c2100c4081905003045000d0142c0451207042c8000c0c508110000e507a400c00d5201e250420486a031b400d01400000e60000e0540040038000c82d988101c682081d01e401c01e050002165424180c00c0002030140c408000e8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 247674370 1250 247673120 247673123
    0x30c02011a0a1802072a1a030109021b06010602070611010207031e120c03020703080a050421051e0909070f09050d02040e060f0a2009010f1806020a12020a 68
    0xd10004500f8504103001c4180d000c241461150b500b042030101003141c0e03007840860403410755504480c001e880c180034030088000c1c5d88900224411040e000c00680f0142c400d49043d11104400181c41300c00c204215500d1100082c02c0c0403450240d100045070556000c07401c0c4040d185952214249080c0344a4020f00304d118030030307000d000160030101802c2410064003404201020f2807801e01010031040c14014202d4141455000c00700c1e500007244410582c200c10300c030383d0010303211004003c03a01e015161007024480000900e49003e8130031100c154001d00803070039500c03505000c0b81614401d88490540c40359a80c040b02d030a5125100481c00500b00c00d02c00c2da00c400388000543c2d1070748022441e040a00c800311034203a804991064464045e00c0440c05c00308410b0b0301c520060000004e050810043c4070303040b10180307054001e8803012100b00c940c0c8006100304030f0b590002e0a2038034a1b44100901802c940c084102c84c00300d25200d002d840001882580000c0c8001d10742e00805030203d592441200136655961010300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 247675620 1250 247674370 247674379
    0xd020c0d02091003120e010305180601090b150c030d0e06010312082e03020406090b06030c0c010b1804020a06030506030a021002160602031b03030606030a0921030c02011a 75
    0x2495001414040310303031a0030003c1000c0f108500368417a500d58041c990070070859000149001c0d82e8000035070b23060140c3c0c3c0d0007206264003002038500d041c0d622922140140110003401346c80c0d102c400101d4039803102e03241e003031103e0a0b410390b2980340e5056615202e6000d0304070042c1c61401c19000c003040b00b60100b1914106d80d4066904115015061030075201c2d89c0e0020822410a0324055000c6036040c1d02500b0b1540c9007000c0b200640c0380c3c81c154030410040b502c15800c07440b246031800c00803d21507140c0a003100d1f0403c601c200c078503888034480740c0c02d180909000c4405c00c2d0020010a220080c0c410710701c0b48280160710888415600c1c5440d084e084003124007c44a1a50607030125418501500307141d047e25162000034815109249441c2403100c42c1c4070081e0748103000503070002914000c0021040c2240c180c0303051590281d0301d18100b00d00001c0c0c58ac0030182c6149610340da030303401050030464010410100c02102c0c070244c000380b2000b2003001c1c0090505140c4c1c0c10155081050148010720032820a4a003d00000d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 247676870 1250 247675620 247675639
    0x709060518130609050a1202010c09090b030f0a0c062304092c16090e03030121061a18010501212004030c09021809130c090b030d020c 59
    0x9601c04a0108050810766034200380e920150007050803401428041406a0700805500c0d50701d24120041034000400381085901d021820001d0350f500c05080d0301100c240729070200c2c5401501c0002400c068488500031110310829840340100030310484880f048510380e446400c4d40d8160b40b03403c035900d010081104404954200400e0080801030b074402c62181e4202010b02c4e0a070001c1d1010f4032001c464184910646500c00703441c0341110301074000030b0000342c480a0403d00c4010b103401d807007c4d074901060240950102000807204d1907080320105200c030180d00302c90b0070b01464400c21a2102c11111703a145250082c050081e400038030105051200d812202c043e07503004000c0c2c0303a00640400c10b100462075121000d840da07802c01c030001c00d4144810780306075240040e1552a071551902c586c2c1c84556600c06e81d4800c0c01480712217100301c1110040300c020081521409441c2d99412603541030f080b410b81000b04409201040850035824503808044000c1040d001c48003048400c82e0166580d104040003c0d91000070007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 247678120 1250 247676870 247676899
    0x9100c020613030c02040f02221203050a1403100303030c0e010c080d0e0a050d02060f07020303040b0406060513060510030209150a020106170f06070507031d01050c190507090605 78
    0x119101101c2c034041d00d030601241c0b900e980010306455410409050b603e4000c01e121031100724598107a080849101e01c80f0079171601d00341c064510214100005014044003103030b0850704034003504a40e20281407071000c040d601d2810f510102d840912074002900040d250009800c1614058080c1c80c045140c16103440c103080309255036141c80d0307034031801060000c240c40d240d800f21407a40070880c05800e244610082d100c0b035450590003c0c0703805030061400512030340c0c060900c0001c98010045a82113030308403200f40b0841c0d903141440d0010305205d600c0941c0000c02001d11501618483d8007240643d20100c52201410078074180850582c019100540d81c0700340300400300100c0d201d0b142c0c000c1c48000010700011032895a1401c002580c00300c1c8440c0000b8541283e83d6424107200c050007125849020f9040090500c83c00340c50007084001c2010000c7c8028000f0081000168081c2c4142e5903c86001c804540680b0f00001d031803100c0f080b1749007003120607108550340131401c0c44e5280200407e0395409028407410003102c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 247679370 1250 247678120 247678141
    0x80903160501020c01060308030f150105040605131a030a060f080304050f150703091401080103111320070501050c030403020c0d060207020604030b01060e19090b0a0803030f09100c0206 81
    0x804400700c0c0d1a40d400c1280400480080c002c4400460091407400e89900c0c00d01d1139510000c0e030003000604044888803d800700c60703820006441c296083c43c0313001c0d6218110070308014006049a042070f191082906007465030100160015482003800c1f401c184404c49d59910070300c1800c1494010300c40030350018481402039041c841c03c40720880134024844e1084004440d0750b440c0d668089141600000d00e40042840f80b407811a00c02d00f040542881c00e00300c0e561440d2141c1035180c00e134812144c801c0d9055003583c03003480e00d26005803011b0f5010070007071040298403254540240e80500d000302c846500b4070002400052000060380d12490700b41e000342c14404110410401d00c0e00c1c40210850782c0640c00c3c8440405601c0e140c0140c4055481452405425410044003038094030161403050310564021880c070f40d04504440180e0200d905030302e40130909001200020f20f00b00300c0b98106199520010080023070040d40b1a00e1580514000c1027590401c2070355102d04000c0c0c40503600f1840140c0e00c0003010500d890328 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 247680620 1250 247679370 247679407
    0x2100c1e05120f070201110303060a030f05031c02090406060903050a0311030d05010902040314011a06030910110d051e01141201140402030d030e1b010e101e080903 72
    0x200e8020765032024140348900342030f50070410030707800c40038804100031007103503007003001d500501c1240300c01076007185402d0340010110b5203c0d02000789150100c5840d401000800c1080d580090700d40300f8240e0782d4000c189a000000d4200704203042c4180d0508100080c624050108502035070f41100c0540490703030154500ba101130404015a0780300c5e201c100a944a070050314400c80d80a01001c0c8000b41c0e8503851814407503004001303400c00300e0803645081804c0500f290030b41c0740c2000482050750b586c0d45a54500fa141801c0040031020302c006907050260b000b0a0380c2e0410014a0403d09902003004039444030b4000c155064542080101c4610b00800140005088104001100c5400a051500c1128006a06400e42d4500320151401d0348182d0305010841c5402e21090342e03182c8417403900300315602c20002c10075501c0700c119010380c101c046418010304259110b40c1d2072040d41503000e00000e81b09030380d100c00101000090b5481e6506111080040007031244030300709041c0101c014100442c103000c06524036801d40039 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 247681870 1250 247680620 247680623
    0x80c0708070e09100b0d02041d01091103071208030f09070521010c030e031602040204271a0901030209090f06150909010605030a0f150203010f0302100c1e 68
    0x215110000900c0482044003802400d40082e51208a00b8400340303c51400d0035102803e018141004080d229603151030315008181d6070102d401168208190ba034a100801c425a40d001c0369500384400003041c440101c0154001a2090781200c0c1c160f40e03511403041442120b120b0091001e88100042001c2d910f100640e503400403202ca054500455a07100007a083c044100c41c42403505980041820000b1b1007072184840388005030405000c4004001006500c1c1d10914050001d1078030108540c0c02503444560584001c0c2401c00d4031102842d0790700c915410441c1d050782143c0c4a00b07007042c42d03e4094040c00d24210600b12000382c20b068503a401c5500f044021040101902c007030384604107030350f01041401c000e0980105940c5a11404e1001400306111481c0802802609a6814440c040099860002d400144aa009144803c0b0304600e840c1100d4080111074009408500200010424442e1506900216482111b1880e81e038241d01f070050711600144400500303031640d11400760840310440e524024420703 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 247683120 1250 247681870 247681873
    0x3305030105120f01020703030516140318330a02040311060a020a05060403050a0908030301030c0e10120606140919050c0705010524060f1e07290105060405030a080c 72
    0x9514150882c1c05ca800c094130550029450340c05001d040740a901080e03480281038545054a081806051801c500c409060201d2446110030600d1003124280800103c0c0c24410606411006000c1e800403000c0700364007000c540c104442008500700711040c0c0300719402c40342d22405680d40c030b821a004101c2c080e04035440860a6005481d01040020b0040c0f0605100b41d220b03840d15903c405603650000c00a46545d001095a81e000b0401400400c58850500b802c440103ca07500040c0c0c1e423814030202101184d6840368041070f24800e0340000308001c41d0044400d6a1440b000c13214149406e408000034514180c1c6c004041100106103041d64441542003958014442c06600749403501568410342107900440303503035441d00c40f100c0e2080600d0144100e8800400d80460b1000d0404000c81c1225086105101181c011007043e005640505080401641c180542000a0292031401ca5040020302c0340c80342942d41b540701c280400401c40b0303c1d05a050f03d00382c40f00900286000d0400759140b80c0d0079405818081e00d01d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 247684370 1250 247683120 247683133
    0x30a0207150e03060718061724030d0203030403030b090103030e0910050a030b010e0601050325022d1c23040e04030921020d0809040905030301330503010512 69
    0x551070404c00305000c0c00d52556100459001810740e6403180354507405c00000c00600c903000400030404140d1413504250903908617400c43c2451910076100540c802c0d0340b6030301400b40d03042c102e0400d6004000f862182d4080c1d107080c4101c101a20400032201024000100442c0110800d01c0042c140b94000341d5100c41010509209540ca800014803503194640c0b080303400703146500040c00301512400e20141c1007082801c11908604140b03140c040080c0c22a6000655400305440158407640308210390075084c074520016404440c1c024600c020b0407480140c0150482c4540021420301070709241c8484861310040d43d9040d0f510340c880c0c0c10020303c0c00c28181d071203100500612012455408800503113004074440d45903108140d01d80f00102c0505418040030a00ea05c0c08010380703002603114503003407540113680060910f60791045900040e00030700302e548024059200200c00860f840000340003101c0422940302040d01210105604510800c06604003040061403d000400c20381c101002c0b140301800303865040d501d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 247685620 1250 247684370 247684397
    0x24030a060803040f0306150303050f1e12010e070e10120605150304031202130308070503120106030b01021e0312060a030f0c1d070206060f030c0306150a08030a020715 73
    0x10350340050f04030302a80d00c084c000400800c1124414040c102d04001440c2412a2558030f001c1c04034010340c0400035110340001002c490b0f215244590040e0076000a1620fa12184030b0080c428014100f40191600148498003061030b030b03802000c90042c4402d001742031301912031101c0740445000c190600c000942c59180d15010403d03980304150816a2190034141646900d003a06005001c146c0100196041d6481040300610000340509680b007940d4220000907a034000c0d5150030f0380b1f10307c249028076a50903a01000454071582c546c0210b514248243d0854228402012901d9200c003016149408103910800807400c6a2a002010a80c003c0700100410b80c80342e0f0701d03118801d501405100c1168410050181402034100b0244600c82d0001840f107400524a42880003954405000d45001c0c4103000044540d44150f03070400031003080c0200074080d02d4150522005c0b2844000d000c02d8101e00c550500fa20218032540c00000b91125019603074020603155141564401d140e44035440301c801005103071000c220 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 247686870 1250 247685620 247685623
    0xf0a020f0a0314060403020c010c05070b070305161103010606031503020d021c06050a05180c091b0a0314070203030402010c08090105070b1302010306140604051203040e01030b0406060524030a0608 86
    0x90382140003c0c003820b00c80ca000c0c03a00900704803c5045081c140f0200c0d92880c00400c800244030300555100c8140d442d900c0703e00c0d003001d07501406010381080c0d1000f220346090b0200007610500c90b41104080e070003031007036585903d82a4140d0700c10032001c15400340070b040c081016140900785408042d0003c0e150340d44000362108040f01500c4024070a81c0c11a8a403002d02403804281d1141a510001211415000054500e070790b43d01c0b2540e000c10700d80704032048001300d40500d42c1400c51122140002d078056075102104107003c0c0c0900f8410304001c0d1240b000b000042da2242c00071007220700c80c0394141c1d90520000300655a1260641050b07a203d410040103200f44000913500043c2c8a0140c03a07034a4540c60f034040b05100040940c1c800b03412520b0b88040c40e441c113021a445100658083d20b00840310301d12058800024a4514040c50303100c07208400e086000041804521240d141c00b4038022402440316948600612640000704941c1342e601e510341986030b003411080300014682203041442c001c200243e0b03810486 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 247688120 1250 247686870 247686893
    0x609150f0d2306130812060102070504061205070b0403050c060f0d020304140610060504090b12030d0606120207030f0c020d0204050403110d110303040206161b170f0a020f0a03 77
    0x20302d44000091400c0c4000c08003001502d034000d030f4000c11048220b5299668444902a41340c110b148650070303a0110303a41c1e178000c0c030407040502400b4200304980340d903540194400c1c0d402c40c80203440d240645400440c200e001441141c0c140c0b6048030003000100c02c032109010082e8013a4845a0294000307100d810410045c0d40021070055020300c81040c51902041340440c1400d9010b00030800c0c069144070b0800900b80c1000c161402c031110b200c40060741d03a00d0b40e801f01383c46006251242c90140400103011103000c0301c40c1c1c450780c280c4180e030f40c65180e000c50f030300c08420881c0b24080000d408101d1070201840103a2040d54074003c06803015080c109100415804030b01510310942c0c0c21404206654014001c0441c10048114003140070301d0f01ca0819419103c99a80760710016001034007400c0002540612005400752405d081c9a0200c0d20318445025030f041001515014003500c5108040001c5111003074100041c1007000319081e00161550901680c01c0003081c1c030f000801c0b1343e08803c58080000100b003000514 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 247689370 1250 247688120 247688153
    0xc02030a052a0f060708070812160c20010509131410120206070f050d020a0b0702030a2106031202030703090b040803031302040b03010c0512100b0a030207050312130b0609150f0d 78
    0x30100078107010300d5101030007010b07807049000c010314bc1040b03101141d0503070740219840d0344080ca45003500703941d100100c5041c0300c7d641c5095044a500b101d8800c040003543d000c82c100420241500140c0d403114100c5a14803440380c0b254821020b454000200945071080c01051103d20807420100c1c01c40c110390b5511b06004100002d1030241e0002001c2c5030600c8401d4983d603600ca15035101442c91305005000c003401401c440c66807010b500c1588022001c50000aa04c050061508441142a0224054002075503580505402c900182c000c9000003000042c910685007610f240801442c11030380d6a0420008030940da400980e4042d4817101c0300d511989003072042180880303c0e6902c50340e42d0b4145000804242c1800742001110005074002000251a8241907407111411441c016a84400ca400c000749180a405c8000c0052403100d000d104590386901c03002c03c29548100821403480d0303280800c01c210100e04903001c0e801c03000c44a00e010b1b420310303088010108090004159182104d19074440748409103203201c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 247690620 1250 247689370 247689397
    0x60f0a142701031a130b031002070b0702070f140402030a0b090c041e030203120f090306070f02150f061003060e0c03061309020616030c02030a052a0f0607080708 71
    0xc00059645130003102002c220108400c25800d0102010491900c00b0201009185035941001404da0350203100d42c0007580051001591100c60500300907004c030005666800142c85002c0c0c0008000401c110580c044501a0800100800d141030620011350b000402d281c80596982c040c0c0c2142e555400e9813a40944420410f19885074109134400c0d071001c2d0b0b408001140d020000504000682c4c00141c4070750006590641e07282c9540c1201000b10042c000c0d80e00641d0700d03000c0c200800c423103240d01c1510b041108215038211140042580700c0e24000010503110b41100b81080d000054039400c1404006014502920b070008040d0741d01c000c021a440700503214015003d10000c180903243c68000300104a10303201c1c00e0b040226003884d1b03000441d2403041c15900d00114540000c140c05050140485152164028055034007203241490b00396160200e0304640d900c600e006000e00c41096940c02180381d04060040e1030241c04810400800000c0e800401040711952410040030000920740380150074488040d55 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 247691870 1250 247690620 247690687
    0x20601060221090f0a09060b0d0506040c141b011503030f0809150604021903050421090e04050106050d0305040f050936010e0705040b060f0a14 63
    0x8500a00b00032600703104030741c0c2c620034040584035009003408a070480342d01154080c0160004001042140490b03500c82400f01e440c2103000554600e400380100704000b0006020002a42e0321320809c4220741035074001c41c0000b220035107000703440c0c0b00c4507006000c44903691000e01050b0010100060a640d50b6103003550b03020408040030010507401c0300e086485100780e410302c0c180c0b521f0000147c3d507495241b441c2075040c1100b0f403400f00c1c445488590466019030b282280c000c5485600303030005400741c074040d142210a10001c0f45000c03800102c80790004aaa0a65990360a2161a00408141c05000508161000e55030792400160b1070fa580524030941a110303031241500d80d86031800400180a05500032409400d0702020131141310a00307642040741003081c50b14044150155120b071240d89844642d41103c41d0b11b85492804045000101c0c00101d0310304580c18428030307950005009050080b188040d200b0b1b4800c1c8485068a4090300748240311159551000741040781c003660001414400307c85012000da0000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 247693120 1250 247691870 247691879
    0x3010c0216050a030b0f0c1303030f17160507080d050115110615100e030304270c020d0c06090209070f020c0a0b1603050f0d141503030313031806020601 67
    0x49030440100710850303e1010207451901d80d8100401c0007006181903141480001e142c072200c10f4242c5a0207580c0940002d1055140c3c50301a120b4580754088502044c800030851b80c50001666507a480381031000541340c08102d08130810303605500300c00e4080b10710032401d01c05100080c2082c03192900900d000080c106051030a410043d0220050f20360b400480c0c0c001c40c04108000c0c5c0a41e44040030000305654150b0300c1c0c0500401104da01d059201c44552600001400013104071009101c070350401001d07185410b400506c005e81d103044071710a031015030168100b0010104014007c5013942d40960040d42c0c0071034014030716030014088080c1141e512000c00d404200c005c408030360410030030303000c00025207551040600b0000c40380054010310301649059000c808400341098400c109448030b00b00b140c08145d407541c00400c0100c000e0311032038901400090101002403403600e00b0094041502070042e010710310b15198079440028100401ea03065050055030031212079001c0e610489400185600d901a12032541407 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 247694370 1250 247693120 247693153
    0x5010c02011b020a0f0f02032a010306090212180f06010306050f01050301050910020a050909040f02180c030408180603040606091805120a030902310e0c0d1103010c02 73
    0x2810702d0b40045500c455800400507028400c0c0c0300c041500302681c58080c0b0b00a1000030b18080c07642ca26002d2041c00460320110428080321800500907090700d06211003515107401e001240144540c20013840302c004089410b5001800c0348030a00e080c1002a68040030122a0750762422000380d100b00c0792140d03120300700002086001a010b001d020105c00902190034410b8403640d0780c0c0400013450b10b40390340c00100e8801d082e000e1812a1604240640000064900741c01c000c2200051710005a0085550905c040300c41d03142040c105218000000f052030464030396032940040e0f46c201c2e8042103410800100040c116940b400080c0d40308521602d00440d00b60304204810042d00c40d507841c2002d40c146030201c01c42c0020004a5003e04030502c03541d141d626203a41030740850241c12495070180d000000c00c0c80002c400c2c0b0102400c60b03200c0070f01d034030b103250f0a04196000d2400c0b00c80c1e103a840011038100b0300161403d480c1c1841030030a214020440350004540d550006030849020380031101c050390000b0319050b01c0c10034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 247695620 1250 247694370 247694411
    0x5070206072009070f0807030204081b040c020309010f260c0711100c020d0c0512060a0c08101211040e0d081b0405010c081e0d0b040606050409020a0c05010c0201 71
    0x2d0681d00c079a440c1c02c00200c06070100b4007091030b801c02d20260b04001103039075200e64143c0c1d00034103540c0c0454070341c051109a0710821000909109000c1c40c1001d001d4011140008100c1c1c500c0700c2e060392082e0285500d103000b26002c01010041000d014001d4034000d01d07101c164010140240c015103402e40d43c4082600d0640621391441e640c044c000e4113511307080840b440c1c0040c444190550140d955920342c030800d1801907100704068000c5580555801000e0b03004030000204107200316480c030300400c00141070301019618840c01b140d101c5000320a402d810311501c0e41d0341881e00c8500e8403a1840018904000f40000c1c19541d02c101440c5140e802040c0107100c007603100401a4001c05207145900d001440d000d41000710f84141d00a40303043c8011603d1400401103008101e410000c2a405411804d0302405401043c640c0041c81c180c000f1401c211030041c807480d0500c501c0d0121011500d4440c0341c94a00078070100a5008400e03402c0c00d004c003e40039000401e00c01e000c3c0c11440300b0141c1c00040c01600c8805542000d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 247696870 1250 247695620 247695683
    0x50105071e080402030601180f33031509080c0706020c040f0b0f0907090b0c0109230d030b0d0501020409060920030a1806020d0e0d02121204030507020607 68
    0xd0703a00c0601c40541c03070120306c0a0641e00446201051030041c0240500903280525021181e90b1502405c0090301224141d090040e204002a48140c4c15901c580070740380010038000a05101095045034004210f20703440300d03030750900c50303810f2905221811035418107101140c1d103e000941c024481116044c90710707106101c4442c001e0384040100d525203601265a5a8252120701d0082c01002e012442e0180506250002450079181483e81e03600713030016580c081c16900508070345651074280f0240301441400209649001000b009107004001864110007601c2d034040303110b41220555400402046081c00200040d250404000c0b50841c5072020200c1260045810300e40680e481c6902800502288001c0382c1d0005800e0b94046500c0401c0c1001d44206503401c1c500400d4180b000906414420181d000001d40401b0392042d40e429816400060341c942811060b1521a1340c0e04015052818072405201c60700312b800f80c0703400d50a114035980440c0ca40e0384080019540c0c0c1300320036001c0703138044c4c41c28450340c4164 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 247698120 1250 247696870 247696877
    0x12102301152c042f090d050d0314060f030d0e0a050607051c02030f040e1e01120308010e061c110a0315060b0712030b041e0f0f060509010509070903050105071e 70
    0x34800c40120a044850300581c100c030407100080c44140d035946e003128000c40740c4d049000c1d03404800a240c0c1c00b07001132569600e50981c1c41405800140149003142401544401c0034000d0180c40b42482c6040341c1c0002c44000c81036010380541408221621804080c14941d8031a0780101901807101d110002454248600002151300400c00310300d41d403000005880443c1d0602240d40107d40b24041c0d00c0b40104a20f60840324261401c038000034499202d130741e070150710074040d85545910b0798803a002e00209003000c503101c640002044204180c03496140c0290030059005401040741103201c20006003d08901381c3c0180c501da03902d0701e06581c412141e8070801004002d003040b2540781440c0341c1d80d40010070a08242c00b0041c940d0f10100e10405031181e41001c031808002e003003081c2148400210f400300a0240350005c04085150030000582480c1a00c1000305490004004400a80c0382c001003051070714006001d40200102888000b00003442401000e005511549610070b07180081681e00c0c014080500c20035041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 247699370 1250 247698120 247698161
    0x613110d051914030307260621010b10030903170f01180b03010c030c09050108190c140a0c0b06180c1812102301152c04 53
    0x1d1800151803291041030150081d03026142d003808500c00b0101040307070705107010000411508550101c1c250040720070107600c10300120320b42441c100030010115141600007102c4402000a940c1d20100f840360401c004002198490b610301c042600941c4039160a000300e40c039942183c0030183c02c0701384c1c0504000d030511448054a4164402c85031000c061044800800642290340009000c54005050500c0058000c0c4004c44103a10028000c00c0c1e29034203c800035840d4130380414650b101e00d80945c000d400e5903040180e0440c2001521006084147c001824400c20600f40700d0100c0101c0c0c00b81403c8607071512012003034000c0b81003103101404003c103494414440044a40c00c0c00c20a04070312130b008540c4400d045e865082c000e1000c05040086141b440e0301658500b210228a18006000e0780d038200b0954041c0700709103480a41e41110504400d014691522a40050040410007021076088800600e040e08190030402070b1001c8506007a25116140600c504861201342814081e9641c160311904007103c9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 247700620 1250 247699370 247699373
    0x204050310060509180a0f02010e120a11060a020c130902210c06030c0313110a0e090d0903080a03020901030612050c01030510081906020c0d11011103040f0b060a03050613110d 77
    0x100c0e00c1b10407000901c2020700d00f01e80d0341564802c21002c244201c02070400d0420007030740440c0c5a41c03101d84001c00c484c00324110001020608200c8144d9040700e59039001800b04081d1b4600700800440d05081c2d120225554001200243e07640e150300c0c0c0c8203160f801904004440f02459981e08040010030745601450041040c02003509150741166030052500c407811003070158a00c1c00700451000c046c0201c1c0d006000f00004640c07141c14041041c01200e410f0b0803900107240406041d101d2081d24480545443c0d824004941002d00a0b001850462814580021500e4452424940d10741d030210050300d456004601c0c54086503010300c54a41c1001040807800d40303451500c480b075540c0750301c40e05030a0000c1500b503020000308001038040d105084903800c02e9071901c22040e000208a2500108410240d41c24000485001c0b07052004590040703801c18413030032141406850b0304001d80c1c400703480541c1140a402001001c550140034060180781c01000000030745503182041e80c201070a80719a90b22802502c0c074080b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 247701870 1250 247700620 247700623
    0x306050109060e132402091f23070516060f03140112020f0607060506031c080604020c0f0106030b060a0806010f0501030c020f0a0503041d060121020405031006050918 73
    0xa900c2981d81e5130004000303946142001008080c5c002084000c4100c3c1d040401c4001c07a40c01500c105038095035600740c5c00c141200c00e151500040081c0d200032401c141801040c429900e42600c0107250620840c0f40341440583da464070345580b1a250017040428080144000b0350701400f0741c00c002e4a40c2c60148501c84403900c03048100d10042c1b04030034140c2034003079244046480b565424048a5402812191102668144071024040480c1c0f02131203030013540b01c0c0c1c0d45041c48984040d82c2c0304c11540e40f954100d903a44810310000754401d0303c11003551301c910081c04161220900418028500c074020012103418128107100301594690001c0da41034012100501032014150345410441d6003d117000301e9412001981603007403003813040040b0100e0041260080c180078001004204450301603c81541054844942402070182542c401d40042c1741d00112801074a1440c041000794545a00010329269032400041d107070042081d4144203da80345c0000300000d1a01000d0302e540320425682441304441d05034684da = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 247703120 1250 247701870 247701899
    0x1e070e1f09150b030a090302010608060f0619080a05010e0106050f01020a06150807080c010813051b030f0106260303040c06120f060306020306030610080a0f0812040804030605010906 80
    0x140c99565402c01102c1c40580d80d08181c0043c80b440b8460b554a007441032604020b801e03d110240c01640c00e2010000310100c002600910a015a01902c200c1c0d4072a6400c001c50590104c01c9802c03201082c6c0c50100710354a06000035864a0b1041000043e94181407807143e003036a125034056445031481941d0203800f40d802080520005134800300005004075041d0500c03840d0590b5820019284c030880c00301081ca4080005c1001d94440242c81d521401d0399a07200c00c03018502810300040407a0403154510203e0781020303090b4003107444001c0545000110741d100c07160031900c06034050f50700780240b080005004107411060002e610302020103145140340c503441e005030924851061804100c071440b8549050010b692080c00354551014060000c0341c2d03a4101039000e034006440d014407a0068002040140d0b0801d803d400c01c4a4072a000781500c422280c0350011300c000d003603a0903a65444100f00c071040c1c0402c07400c1c0702031056101e0700032031351154290b09196044960580040414030300e8864180301030494590f60 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 247704370 1250 247703120 247703129
    0x503160e1011030705070f0f0e0606040b0309121801110d1b0606050604090501170616110c03070b220b0d0f021c05011703070f020103020c1e070e1f 65
    0x3140342c0105410201d14500c10010b0240c068020340d180440c2e0000030130102c604807000c80030b200d01e1142e11030780a0715110f64244c600301c2d0b102404220403c0022148006158880700301c4083c0c03155201e20f120000400e6200c842e580300390780200c66410035a9070f0000204134086240200402c1100007000e00a0301c4140510700741010032000c003103110100300e0b0941102c0e0250001414890301c0307513681d1400202510082c000e100960004c00300b01417002c1e90004074580300388242034801950300321440095601c150511405076450240d03401070000303030720308120900c014448101c98a0b1784114198100c0c2610083c1c480c505590948014104043c038941c600ba14004494800002414606403030f03000d00903c9007481c40401c0b1000c448110740600700d503522141c1252072010465104d60340130a80305d6203d110f00c504c014403e4a00c828204c1c0554440d030301420a0790419401c0364103d0707001a012425500724940141c280d940190414081c8292040c1d0040d00006207800150403106083c2511500700c085004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 247705620 1250 247704370 247704377
    0x6020303061014070f05030405041a091605072108090304080c06090a03060c0c060e0a0803010b0d060308030108030c070501030c05120916081507090f03060b0103020d0c0503160e10 79
    0x1081c800a00f124802c440000c0d901000e40d0801264615119441e03420a00c00d5510581c030b0100107110042c0f0406591035010380080c402e0034996100b41d5090103d214140f1907408112080c030030540001c0c5180000000c015041c2e07074500c401b8281d540010000071008216480e039400c103200c20081c1c11000200140d031483c1c21110581c40d1030b943d00100304c40203050b0340090445810700942c04082c6800c0300d944083c440c06940d0501003015400e0b801580c1d0300070700d01c2c0141054010401044000c2d00751024104a424400010440503503e4903008119002a002041140c100141c503407011032003007101d42d000300340178201400000c0e140c20014100340540e503d058a1003445a001511112003402040403200d0940300c20b8102c1c0b500d07102d0741d0b07680706c0081208003900c803000710104000c20300445a030022505040c0c1522029405c0d6520100030f4407495030581e06160b024000320b0034049103401029415009695142d03200e180040800100314103240e01c1205000070560214420b0300d43c00d04a4100c1c0d0720b00d04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 247706870 1250 247705620 247705637
    0xf01060519050607060b0103140a09050601060816121b08011d0423102d052205030903100509010b0411161a01030309260304030f020105090d0602040f060203030610 72
    0x140143c0160200801e1001c03000300c060304000d442c000d140d000d00c20701330148084551582c1c0740c0d00151030220003503845810b002d800458600443d403041020350881f104066020901c04122805584a40b180d140390a02048d4408010b001d4800d0305502c8400c5007100c00180211400c1c203450313101c84074049098605041010b6245400e04000c100a55500d00e101403804010113144002022941c1c03000241c00400d4000c1e140e00200748000c940030702802080000e008081541d13203203a0307a0075000c0004100f101d140c0424051000280d07424800020128040381002c00da0b0324060801a084030284105140700d03500e400410418072040380d06607003c044c142c1e01501c01a007120709000e1441e60554400c50460582c1c90b00200400d47c0c443d80500c11210340b018480c40105001555006c2c0c8800c0f00d56140c1e05600c1070008001181d0680030170740000b070040c1480d6140ca013424001c1915515800415140160000340800c40c4448442c5503d0042008e071000e5425420040c1c00074156000d408281d00801c100300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 247708120 1250 247706870 247706891
    0xb0316081e192003090c0a05091303170c0405010f020102130e090705040203041103070e07020a060225050706020d0906080c0309071212140306060304060509010e0f0106051905060706 80
    0x154040300e03842902c021030a60b81440c050119002e5801295004006e0041c1c6907150003904022000006442000704a9041c95441103020321203174039980b10580c108038140d00c403e6804802e0301c00d440d00a041910310b03150341d01d0819001500b080e0002d440c8030f045a1041020310b031045124070502c01075a18a0783d04c8501c03503c51600091414040380c00c1a50300910000900003003001c1d002c0c214641d88425401c0c0c881c0c1c01d566402e25628103604860341c0000da00007003e5000020341950041c00840d811143c0d60100f920402c005214203108004200c41c1540b0580050044680401211000d41050714104003401c0c03d1a600610120380503000c10007440b00030010a003c1d81c010321021020309804000c107881d02c0c44505000414401c156140400f1544511218025131300b00011a8812800170f005149151030b1617503a10007c04000305071a100d550381c0e625540c0135400a2001884180d101400400c1c4c2c0380c1400c0401581c00c001100400e201c0e50030701820856030b02c50400740d41e85180c1011002910059a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 247709370 1250 247708120 247708171
    0x1b03160809030904020d05060901050f030d03090f1403071403030705160602070f0b040c08030313020108060f090115080609070c031202070c120308070e03031b03040b0316081e 77
    0x803802c40704c1d403050011444520440f074640c03069108071400c43e125401e90b41c1c0c820501c28000c0005060365015009549a0000319009070400d00415104848480021407241c036121082c4082d1840403a1941000400a013800042c8071142e840140400c09903180d420202e1002d44544603002d41c4400000d0b480030000140441da0341074504840c3c216195401100305454200c0c0701d600120340071541d030402d00b0b20200da42040003080e40d1049042100303500700744460f40c0054512aa0003400c0981c00104218003d5072a11030139803960003004500d540c103a0074002e12001910344c85004040340e000d810b10104021280d075020207801c944540604010407020440f5081001921a452000d8070300b80842c5c41c0043d24142061104000034084e40d200350403a201d00b28100c52110110305800c0d07056101380f1003a0080528650707040755807813200e002c407032a042c2c0e180002c5055070030071030303c80c2d018042261403005402d03001074440b40c1c0b007203140c01c40641d03603081d944c10b07201c0e84000a0017042c02a01d0aa50480d050620b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 247710620 1250 247709370 247709377
    0x10818190317160f03050906040f0203033105010201090b0609100803070c0e07170a05090a061a01080c1303060c0509180402010e0d08040515130e1b0316080903 70
    0x5203400900c1d261500d11a10f007001c0400070803280014565019103a2180d00c2841075034000c41654020709038039101c580343c14020321500c40c41640c0c980420407110729000c2001c000407031755500c19200c00d010072000181c4144202210790002d07042d6414400e0340800240740390040d65010204481e00400c0751905103a000c9420000e40004419220009002c4107010701d4802d0344003101c141442501e09540e8400d001c5914068991030100c0b041c07a01c8e408503042c40030350b4005503400007041086070520310040d110031081c0c402e09030700e004902c180c0e0740c840300711542e016001e541e010418a082c40e10b403100500303013281c28a46610001d0040e6640d0380184c80094481c904682c1141030040089194164544204a880c01c0075035040b070118920b88032040160070140c03061003c064004400a0600d881d01c4180f05941c0c205620040d92041d080003002c1290160b01101006010101041360075850b04035805034200b02e00c000620720401c001d0003040040c100000c0291680001c07071810615640b0b8403440940383d0700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 247711870 1250 247710620 247710647
    0x8030901060e010b12071d010f12020a080103110105030402060a051810120c09080304061101150e070306060c080426030d1a150f03070e090c03060108181903 69
    0x2c0c00c0c20000154804444064407054800120303844e8a612051170540b12168540903510b0081a44410032841d50b00541510386400c0311030412101c00500b070207020040303034020001c0304003103130154005109000140040203503c2e4000e00b0803501e5070030710350001481800744444840810600144030144045101400c400300a800f911032101c4812440c4050090010380f01071011091030b100075002d0300c5101c5e4158004a80440f009140350904004040b0341284030260b0303583c00d56403104109503c00048490710300040c04130300d11180450400b014002e09490240c0c2c084410003000f84541c0780072440080884080b20104201e0800f001c80300f40c0c4441d04000c030340690f030100c0d00000c50000f8a070364039a0052000c0d03c1c2c004844011030320185003003001190000d0803d1124500a01000d1400c1c2c190100642c1c10a000c1c0c244081e91865900000309490ba046408a042c0100401442000d5811007400d0790411f400011441074030101608469651000d81c01100c200c40c01c00c00c06105040c09440c4040074003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 247713120 1250 247711870 247711889
    0x6090d0f05060a0506100804020604050105180303131703030403120218030111130503070e2a21010905131217010305010501030b0c040308120c04090507030f0506040c08040803090106 80
    0x3e02d068400c0d00001c02c4201d4880340180c0c0752183c2c8548103403003602c5030391107140e004140600b014206001120340c2d4120b5490810200c1c4880d24444481e074042000e40b820541419075401c80300d05048005401d0301142e21100200c0d44240203100029400411204400819200058841903c0c00303d0351001f902091009416519010344882945010300080230107001072501c8007540d560344c00a25594098a10400d02d0307480c04a8003003089004156024542519508507000e600b110400000250340d21200c6004070940748040c01c0e00d40c125840c500c40d070045c0b0f0000820081031a01c1070307290780a41c1050400a212034810103458400d180610006c400841c1e4600800c2c5040d030712407411a009181c203000640e2424141c4000070b07600409101210152035020301014240079161541c0d110003c0e0207400d4000c007540510001c20384540c1d45c42500d11442d130958000c20269003d460380011240c000d0b113110f00403800c04250107210b0390041a010b2f0010351003480c0b642d0743c1c1e440712015401450503400200e002e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 247714370 1250 247713120 247713133
    0x109021305060a09051009030f0803151c03030c0e01020a1b17070f05030309010f0e030c06030901052403030a0c0809040c050c06090102030708070e0d1b080c060906090d0f05 76
    0x18103034001002816500709031080b03140d28101e0041951f00304014400202502c2e60600442d000a034400059a00500c001c07034901401a00103000820764540c0d214115032000c080001e48046c076615014000900110b4109088031381c0c41000000c0d26200d915401400025042d5101c104a043c2201030100910301046400725208440c045581c03921814403460b011000c032004085000e240200803901d5030201611080300c403244000c1c0030b451850211505c0342e41800b584950103243d880d800010742c0b03d00944800014545002501c9942c41c40c001d80a40b00c0340b159140054025407030001c1110010740f09428400404100c910f00101e10b80320b4140a540c0050034a2640c4200c150400050079008100c0400c0d120207550b402d03e80b500702d02003150444001070b1440e001c200c2136409248045040c5c81c001c0e040d1020f40e2001c0e1034554980d600643d00036007a114480d420000f005060255041c00082180d5692030f1070150000590240113403071a40740300301d818030f02000800c000400220a01c1d0b80c000f060310310 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 247715620 1250 247714370 247714387
    0x110702012f012f041a040806070f0f080f07120609020409020304050717060403030b030f0106030c18020408060718080f0309041b0c0b060103060905010e010303020f070e010902130506 80
    0x40d04001c0070f6182ea044183c011409000400e100280c0042800848a41010703e40303151060395001d4001c580c501400200b002048203502400040c0c03003884c4a849483d240c0090403402000c1004000010080100c1407040c0305003581c040b041150800c180303181001e001800700d4103031781c000d022a91090564138800280083d88410b9900a540310701d000e80c0544150b039a9801d41003403104100b000c0800190081000200003d001e9440b0410003600a421208040103901100e400c40e140d54200707584555007031740d04100003007201842c5007240c680301c0e4080d400c1c5881c0500141d03881c40302414010501c40541c01c3c28250900c44210f400007004540101e803001400c042c0342039129401260040d000740c1c140810561645e0710ba1250020441c0e10b5a50310701c01544545903080c030040041c050504040c3c0b00e0000240404090050134040c143d01d49c101001d65266141c0079140032600510340f1a150882c2e202000501a04071070581100c1100d840541d58143c00c4070744207005d000d9500a47c0d4800804242c160 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 247716870 1250 247715620 247715623
    0x17010806040c0501020a0f02011404030206070c03050f030913091a070e01031a010e040f021605060f062d0114120402010f02071a13171b04110702012f 66
    0x240180e0207031528030442511030f070049807600b0f0b62041c098007030381c0007030030003c01548506141000840c40c1440c0c1c9007016242d500003481581721007415a000c1d07109410910a000050100c1e5555000000003503250a030140041402c0840c2401c6103aa115610f070325900a0200d80107184803070542c9030081404a20b4101009840d0307615041e4807074000f03440c000641c00d0904aa403d00700f46080c0507128005003266041c10040034001f84c18070705071200d4013031203051010f17200c1d592000d10f9107210310041e1103180303840d0350003c1d2848402401d0030b1017030070000c0e81900f0641d108200c50080c00c6042d60034030586402840141c82d40c0c64450481c290075003002030340f0712040b44c10340b40443c0a14400d03030b80c000b003030650400c040340d40d01e00500505102d040016180c079400c003043c4d0010711141c40c1d0800c100b00b81650b41e0b40030014007007461110040541201074210500c1045285607001244211070030030003201019130410302c07402a898028144601d9244802502c2591441c400103509a01d00b82c107468140d2503442e5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 247718120 1250 247716870 247716883
    0x8120705010b150409021b0f1005130b240603160e0415061215080a0308010906080604021c0f0c090e011a04150e0c120a0209010f0f170108 61
    0x340c0d05546400054080c0c0c0c41c2c03c041d0880551045a000c40c102410916041c000394400718201c0c498120301c0c4420075003100d041c400103d8807a5000040c21074801d03490030400980e00000e041d0b26a4902c0206428002296403001c1034004408c1c100c1c41c81c400b82004101e2124008444401d03a100d1004000c004000d0141b01c081d20b4a0b145503038446402c481440c0500007901c1400e16042c0000d2100310702401a1842400c0e0325a0096a01c4408140e0081e01400101d840b84550000b0310941c0104c0480000e00d0703000384205004244600c001c100c0c031854401c4981d11010003501c001e21410020040e200e40407420b41c0c60231202c0343c2110448407044460701d01900c0d0150b8a204022541c2d051003550003100c041031050300b01010314426040c0e08003c0c0c8608000040c851115103c488100f4020b0101d484a0b50500c071500c5400708c41201d554461070203100d0b965158000709204a9603004200302c000301e99002689105000650610540803c0e61030002c1e580c0c44188a480ea10b24444140001084c0c031000440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 247719370 1250 247718120 247718123
    0x301180e07031b061202030403020705012303011d0c070b040201050904020705010e071e06021e070308030a1a0d03020c0d080f0a050d060603050606030112050c150c010b060a0c0f060204081207 84
    0xd00205c0d1814040e450180d007c1100c000e03025070071104080015502511529998800c0d100344480d03075924102c04213856400c203800800c0c04202d0740c1c002d4840f041040011540003580380c00756a08100c0595211307000400300402c0241040804160300c1c41c56260358040c0c0714800e920400a110944c00c000c81c0039074070591440740d4143e807a40c10b07814119500b018412032040d61200e41c0070b440762801c11003071164141d00891045c400351044200000104003c2d001842c01030200c0c078400300b03002c103412510360700710704c900583c0c07610900104100d04002500081c41141c46101524206080d000c20f04018a0710301404c2c0800e403070080c0009035182100c2e4030000400d468002036408201c503c1d290700e02102100e10840b05a900314030b0801c01071101010010030040120300c6102201c61903101d05c004903154124490316007001080114901128200030700400d540944199241030a15000e00d074000c010034454280548011100360201d01842001d030101d038007510042088582c5c41c40800703d0408036a012600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 247720620 1250 247719370 247719377
    0x150f030302150f010b04061b08041217030f060904030207030b010632040314010609110306011d10050906130f05030f0102070f15150b1e0301180e07031b06 68
    0x90340700c01480f101e0034180c0e10b600342c04d0b504044c2040000d44021000c0383c0c40c00d106160400700080021b040c00d0003040030301500320700200700705100d00c2e001043c100842d004404000c01441044a20820004403c5c2d0080c1c08940c00440354680b03040036800c02c1181d400c0904502841c20021901980007842400c0c1c2007035a01d0b241c0d00c0400b041842e550311101174422921030388810001007000c01e0000300e80d0f400c0940c82e03800000700320b0340d60413100080b11980445100d05182c00310410540b5070b04a242c484083c01c009030b1200e89075401c40006969901c0702d9144005100c0c01040300750359a00d800050303c410180000c80945055260304400c4461696481401d110f44204cd015004c01c983c18000d543c109a8010386140d9138121640d1030031003030300e0440d1500300c0c1c09644900f5481c10241d51107412000b06030b4102d0140e51034581c02806050400862201c00010300108010018915818019400300910b480e0010308400034542c01c40c2881a154030117406204918109071382e0504680400040b0b854548 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 247721870 1250 247720620 247720663
    0x1091209090e0c06070c08030d0504060c021507051605071403160b160807020418030e0301110301090207080c0f011505010306030b1906080f06011d0609010603150f030302 75
    0x207004002d482c051000358207580c00c94903541c051070400101402a10b403007900b10960840e1101d007014a107170840c03d44100300a454500380700034040140b04566860504e032002d80162020b0399400c00d95048050144402c22000240e41c9030a902c0c2007003420581176001040d208280d5445900703681c94580505c0d85480390140525002e14902c42008250882e650803800d24200106601c401c00741d984030305001e407001013040014500595861090510010000344510390130b01c03240c280100725401420006001ea0701d00351094001140700010b070782c1100c00b01980541c0d100746502d014481402505400d08551040c0c02d401c030300000040d0401545002c07040d5003101c0f81130b0b4800c01142510f10070b10029111441e884003007041084410f0a59450b606000c02c00702c0c1140e55071000e60300e0022152005150f9801420040c1b112030180650396040c582817078000b42c01c6080200005e100c440e0103202d001e0034540d640c110000303034400f0b05e00f9400c010414810700080042c0d07241000b80d22811025400d8070b0411195 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 247723120 1250 247721870 247721879
    0xb0103050607110d081005150d270204020d090f1505070f0e0609190f080f0c010e0d06060b3907090902060702060f1b011b0e0d0501091209 61
    0x143c9a100c9200080d00c001e001071400803100b5900740c0000fa08407582c40c3c00740b0358045400d03247c0c146440b0100704084401566250014052030071121981d14410300010007160910a00300703404994448907070100c034016992101d10001034005c1180c000c005100d048c240304a0320510403403070480c0501c0c0342017100900c07107a903860208654400d258001d04012941c072144060712400e0003005407100e03410140c915074050303441c0e41102c14900010380c0040f804044441040c400d003241441511a608a1040100880c4040c80d0000e40786d100c4041c4c0072402101200e1a00c070500106804c8000108203581c105561852010102c05600503035151701022451503c000d90441c103170b8080a40d92902080002d0004642480504800b6084900c01070381c2c0060244821005644c07010010000180350110441d075407013101c10800d041c01d41c1c00101d0b8545074076005400d4492074540c40c1118000c3c80600e00304410040320340c0040c808020218014003198031f00340c211800c0007400d0707a00c13001002d100e494a41c51aa640c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 247724370 1250 247723120 247723127
    0x1030b0a02041508130c09060f050a1203080402150a020606011b0f03030c140f090301180f080a03180303050406051305070e07030207020d06090308151c031103070b0103050607 77
    0x201d03c01c9110100d40c41128000152040c030300780d40c201c41c40c00e90580320380b4516101c1c00701d440c4164111803c13065540004025100104805500900059601d2580741c0d180041341858240001c0c000b07014040d16000103802c40d5035074160725642e041e00c0482e10f525000c25020080d0f581d01d04135000c5000c0786903241c40d40424036404488803445a8081000c0c65226040e9400300e0140c8a03403050304050083e4802d050020000c00400780440301002488070791100030740001c25081d540e4299950310ba1a1310b641581003c203001c04000304141d03422020055407541041c00450090880c20700b010007030900403460b01c04050f0306404c100c2c0290701400060100361980440a90b00e490701d000c008115501c0864200b11031030302d210b03900b548a0214140103052256540204000f00e4042c6401c541e070b1555541d2140030036802900d290323000002d4a00340f07000448008042000d854030902a910040310082800c01090702c182d05281080483c4000d40351110550310713100501010a0004032803030300440c070008040921 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 247725620 1250 247724370 247724377
    0xb09041109091f0e220c0504180c090501051c1b0e060f01050f0a08040f0b010305160b0313020d050a080d200306030a1e0501061d18100c110105090601030b0a02 70
    0x4134400c5091021070b07541c1c2e41200301c1c0d030170030111407521041a000075585e84510600c07400c0115224001020306681c98005005509500400f44861401d4014856038841034008a4a4050000d003e40280c1e61410610401060a19040d4034280c4121010460074a21500d030f0703018bc0c10540310318000d1700d810070040da658082c07c3d18103402e5050502c03820200c1441000709075041030041c00350394205c003c55181c2c032101c000242c005640540c03050064800d41c03040c482d0240028100d03602d030729041d41024084041c00c02c0c00b220307002e44580c012403d04002c0c02010f01582d54899480404140d50755100000c28000d01a2000c0d00525140f1510080700d1403068074046034412480180907008071501c682e598820710502914152200710200d1450000400c00d104031300c050180d8842002092a10325601c0d010300a00404500016540800d260207624000440050411080c030f030210317400c44030704400c8544e8100d03590788800a6080406012800d0000f2403002d040c1c1e80622440c0c0b03002c0d81c458410700300368070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 247726870 1250 247725620 247725631
    0x5010b0f0d090f0501020705060a060b040e090f0604030914060913050910150e0108030a02151308161a36030c0606090a060b09041109091f0e 62
    0x201041104a1444080c004056164124100140007040c5407994803081d0290a01200c05130750004800041c03120400443da80114000803c0c0110750500300c0e50f40c028000d44c0b10305c80c078a074041c00106248000a111f00f0b00000d500c001124401d2625041c000c1c80140d02e8481c0e040f0460540001070a1414070504440c07003000c0140004840c0500a000c01c401403800a0480010380510081e154039000ca50003400c4500160310508000a800c1c18480d58404006030b0000314241d1080102e0000d041d0041a50140c03090146144940e96450071344044440c0403030b100c001c1c03050380300040203807118803075641c00e0b06490b02595115860380c4203a00c80c000d04490030381c0c50191142c241007054403220012107490380181c0284440d80e14520012030407602e036030819071024a05070441020800d1600782a08100d0b444001401f007440041e1a0200e007407464491990080c2c00b46032100903002d80d00080104890003010b000d4510301070fa2422840030141c5000070801010f080d40b090b03d0000e10641c1802446000760b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 247728120 1250 247726870 247726889
    0x71806030b1e100b070f0305040812040905010906031104050403031107050313060f050f0d06050909100b09070f11030c06070924050a1d04020f0a0e0907090501120e03040605040303030f0501 83
    0x801764070342c0da915869004080701000f10400000c0350301003041c00409070718100c00c0702e0310340c840382000c0c081c0702550701c140c00240030185048010004121440980c0d40021070958000a1507150781c10204d01074411085c88040060000400c4010448000014203030940c9140da202030060300e0380f0003100c000031a00c291000060060020440d607954030300081495048503140002d20075a5107000c1040e1202c1181c0404094014801001403002d4500880010000c1200c0541c0d8501d00000080c0255039003104d080200305140c05a00028282001203501840b6070f101100c505181421008100c00d4580c0100d608407a54120304041d5901961184d00c844405529040d081c8003000a040721008401800e840c46000e5212503088280c0301c5100820508805050039682d800c032072080500400d4004030254000d198000070060950303404091a81503410034604081a03010f9a41004064441b2022a840d203000008000a1858001c2c008100f101c0c441d840500008411f00402000c43e5000d00c80d825a8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 247729370 1250 247728120 247728127
    0x10b03041401020d09080a020609120f0c0a0209040b090f0718020a0c150c020d110607231801120c020c040507050705070e0a05010b0c071806030b1e100b 67
    0x40046001e0360703440820030300041c00c2440f50000602a50000c9400b6201c0d400c0004291245c1507050080581c40000c10005108001c001c05420845224904280e8020302003c503103058010028881d0440c01a0020104600c606050070611070108041d03640c2d030340300d200d6030385140b0180740041806030456100f540d507040094444040200694040d0f6440010010401d11000000e4050150101404513460300020005983c4002a240c4009118154140320000070b2180183c0c0300007403000d501500a00d00340020250030008055a806038100079540c0b400c0100d052a075080502102c1c00404100366960450401004402c40440d2103c0710301100581003c2c00c14003813410143c100c19003200d558604a860660b42c0c0e11582e0801d0340c160045001941c0308802d10500600304e020345409015071800c4240b5004804009236607405e003d1043c80c0c83d03201550203a00032602c059000d0001150040200003a52400100c0c8a64000111074003641041600300441e082c0210718011006a900c050038182c0b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 247730620 1250 247729370 247729373
    0xc0504180f1118041506050a03080d0b040204241205040b04060b010e0a0b030a050702011e053301020f161419080703140d05030403051c0c0e090f010b0304 68
    0x90044520354643c0c0200c840c0d002034100300c55040c441846035010742030b0020700341c00d0410704d441030344c0981e8040303449000c0c03094007400412915012515000140d0100185d414182404507001c1d0255500083c0303c0c1145101c800b43c1511045881d402001007a55408024025580342c0070403a8815940034085404420002c1d00180300341d0f00c0003002080505050111400303d01c005426107805030841c8070102e0003c02400301c0c5d62018001e91360044024002801034042e5070703032070441304107030440300140d01038075040070840e003011101001b1810b40844141290140c2154403000307410300700b041c2003401881005800c400503900800d08022001c4039803e0321405078a0000740d6082079001d1140c06601c4184d0854440740c00354907005010041c41054042c25501c0d266060841805040f4850085190818501c100c0c0c4668044c04981e03029038541402034641007180c092042c410721303601a48440c10b26105014400759002914480f088004440702c0d6210b540d0325110032990f8000b8481d5801d02d00c414000b040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 247731870 1250 247730620 247730633
    0xe0a060b160215030a02040e06060c1c140d0212060103090c050103020a020c03010e240708010603052205061503030f0a050f070c0f05011e020c01030f1103040c0504180f 74
    0x20760006000540c40b0020749002c0b11540c0c01610044843e5500007810071030202c00542060744450101c41150901d003603541100d031503d00710f6246541e1001606451400346000318607a54100b0b041308100c64451a0021142000b503201200d04040243c10100242c410361090040000c4181c0c000c20300d000e001d10700001500650004d8000c1d0040d801400d50419041d1803d01c100440c000384a00202a50f00314403201c102410a80090051004000f60400017102c0e006070045044600d9442c00048582d183c2e180b501007901a45002006040d18400d80f00c140f100000e400c1d0b00a40640043d104482c400314205982c0c0e20901003100c00045041c0300b89881640240040e00f201010724030039500d003040c25603400d0040e0546402002c0d41d80340c6140103000559212420140c44c81e8500000407400f01762a102035624100865030904141d11550b241b0b03220440b50f04421500b40b460002e10340c42e4107040c41c1c078400c3c8030514020f560149190100490a0554031100786c80701c20781103030940789480300540b58030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 247733120 1250 247731870 247731907
    0xc030706050a05310509070f0e01050702060c011e020703090b28022802030a11060f120a0e01060e011e05100c031101060b090108090708160e0a060b 65
    0x640610000340448414000e0709401d041c4a01c4c0307161814884c4c3c2c200c007444500305003a1a00b01900604c1004108101c043d00000107140c41d1401c2d04241c10000303448001200d6038401d554009411080105541c207100350150800341c80011002c00108200b55182420340c100d0190802c0a00000e030380100400c1800360540c004c0142c400011499880c080100420228003d01440746900507070000810210500d01c16081e4070064101e207509500042c12a0002540d581c1e190f2409490106003007500d0803103039954800caa05084201d010309444088114404542c3c02040310b005d02e034681000c5070000120010f100c0d8000780e8140c42a2007145900701524280030501412080103945190000800c60741e68004200c1c0d0303074070401d80e00d0307000c3c699035031800070300030150380405c0e5071981e0509000b40b00b08060300d000c0d61841e500038a4001100d940c1c411142e40b51409c41d50040300c0c6402210500c1103200c81c038100340000d48180d01c08011840c4c8030001107400301c1c2c0b45482a0800500d040c840746504000c46c3c8002c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 247734370 1250 247733120 247733137
    0x82703120a0e03040e0a0c08040210081504050709050108100b040b13050a0b09131103061e0907020303060918030406052808090706031118030f15010e090c03070605 72
    0x100314100035942d038078541c440d42040620502c20b80c100000c00c3c100c7d000b4003100803910f2421015030305003071380440c00c2d0f25045810f900c00e00501d4030000f0b80031803200c4100302c1d280000900510003406d21401c0941075002e103000d000e00141900c0d0001e21409000c44089040352280d43c00341d46441c0c0341001c0340b005030b0060342d614000301e850254001a140d0710101f03440c020380b10708804603650b00181d00801040d01c1d00703d0006000c4904001648040c0026401942d9101c80280e030b521420b80340c00308413028100c0e9451902580000c0a00034010025400005188110410b4440704400d4440303408103103000301090684a090b0384100000d200d128800c00c060302841410030f080c3e601030318100e28441920100c401c0d07a5000603004004201c49c2071000c1041c0c40c01031038581000c201c184015552003656105400c200407c0c10901c110342900740e1410407100005030220b106031112003403440c1140554620a1198079003244d0907601107642c000780850103070030903180180148103d41c5440402d03606600070444 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 247735620 1250 247734370 247734391
    0x617060403080c070b0903120a0e070504110913060303030c0c050a1b030b0703050403030605010e09010902030405070b030403110d08061305040c15030905150c0d0902030109060c08270312 82
    0x130100040e10b160b04050055205001558a40c103440082211207603004000040c10b03800d01d0b044541100020070603005844055a010440300e4460003090076501c20010156005082c0100c06400c200040e17002e5801d49101e13640c20310030040041d1048070351710743c1003802400300c1d04040d592030002a0b214458142a04076864060311403541d0b0740703d1840e210000c81b1200c01007038a40c8100b000305070303040c8103000150609003040314440c12030350b012a400709014090f0090059000000c00e0030b20070b08000c69402007a01068469491130289001000401c02e12513204a900c03e0007181801c0d03c0c080c611807440307034170701a0040640c05840d00e500c1000d000d0292040d02c01c401e1240000c25200404140da0305a50342030f44000c00d1310281d0f881e001d441c1c1030b1559244400c0c2c20b0311300d0034007a54010360380446030300501203407001c41c0d400b285000182c010035420b000100203503e05003007600c01c40c0d00000414030812039903c0c12040c001d102501c408580c042c0691b5107050360000c0003100700c0c43c030711750366020340051a903030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 247736870 1250 247735620 247735627
    0x160e1e0112060303030b1f121a0a06090905010902120402010e01030b03011b090b0c0d0f0e0d230a020f040216080a03021b0f0d110129040617060403080c 67
    0x10125011a20b041d04280c0c0000d4889060055171b0526821035108580c07400000712400807072201c01080c2c002284402403074207480d00038684821503980700000e00d02d80c009105000706992424040e040100601c540b4080c181040b0000582402e80d1098921401048485010542d00d42d801103500003450031050f0706140c1d0341c441c004082d803400d100b0013030060316087c04241c040d07000707240c060488001a840b40c203040c24104000641800007040c3e440311116039042c004907804184409403400c0d90800103907904078050072045070034400304405041641c0d824840000c00141c070300c04581d0702d641700490065044405111000d04600303280c1d00a1400d42010802110480400d039036035042c645c00a00e8510001e038020400d85802c2c0c00411200b0701d51074501008003924103e10070082d8840851450000030701404050343d03003640f1400e4000050380440f0301840510310481b5202908540507100300d2a014070300d4184080f0324115441c0c43c240f01642060010003c581c2c559504a0752514001d111008141090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 247738120 1250 247736870 247736897
    0x203090d020d020616230f070b030712020c010204050103060803070b0103030e040213030605060f0d0c05191e06030606050a0503040209040c120b0a0c091508091f0203160e1e01 77
    0x500d03002c170340e95114540f0100c45d41c0c81006404c8100307502180c03000751500049000c3c01102c3d0001031110848291840b841c2e02c9907501302c029596a1176240b401060b46000040d00300c1202410740c0100306885017601d08216044e00c8a60640d07803070290b220010000180c510050011a02800b89040c1800c00203001515103200c011101d10410200c3e4003c503040c03504d5006000651500240704820150107513000c03400d900254071065810340c5644a0140501050f0410504020b941031401d80a00403041051003400842e00d001c420070131042c800c120000c0e160540200b81c4510802c1102d01941c213590720301342141c0f02c60302080100719026004584d00440b502c0000f03400101e036240030014038059542119036107820003001094640740d4000d20200b15a4500502110748016403454440107146400300072a5152410240f074985448a050021302021403004041c5031250021482038481d0b2801d92083c0040f0641a07480c045c40418103644544030000402c071141c00d4807038290800b101450704203959001e1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 247739370 1250 247738120 247738147
    0x30a1107090903020619090210050327030d052a0c0c180405010c08060603041101020f06090f01110f16050a061a01030506151e07021216060203090d020d0206 69
    0x104000310f0140e0826010051622a491080c4110a100301c0007400402c16660008400c214840200da05100c1c001c408942c1c2d4140c0050781102d4000c26000842e01e5012640344a40c1e2604691101c080321818400090714103084103080d03c01c402e201e06030300800010440e038a0030081c1c012107440d0a580c46042c410050903901c100c005048000b0050341540603091904049080d034030490901030503c8020b00500246031a00c0040341d9000b6048640700107001c3da803500403800c0058040151080340b0801e01070010301d04000c40d000710904251002086007101c00903c0030254055605403004140007801100840d01d003020030069101d00c0341d020381b44680c0d00ca50b5894201d45503420088528400c14000582c00e58140c03180780d41055007103480b00d00154044822900134030516200b4202124000200410810380c1015689600e6004200540c101100d042460390b07030f0313107240340048260301d040c3d00000c4c00d500100854025002c003400103a01400a42c0030701424000e424001c83e0032210402c0380d0000d6001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 247740620 1250 247739370 247739381
    0x1207020d0c0f0312020f0601030b0903070b0403030b0f01022d0304080303010b0d0507080609190b120c19060c0b22060c020106050a23010c050714031c02030a110709 72
    0x201c03107040b45460381182090b801c0301c01c02c580c4003825075114107800070340c201c00000c00c0350440b0350010401c251550303688241ca00f180185900200700d075085070706200815806411096010405030391a1141d403100b680126514858800b40003542d901e40c0f0b4100c000c2ca002c004100204800a0b01101d107841d41d516601071655100740e0000440d141c2c00704001d00e520a681c09101e0f0481c07514030b003200e110300b040d10020f00231b8000034280c0d00c0f404240002c164079580b2940c000030495000103004030440c2100ba03084a40b035200e116850f03071003040c10f240300000c09180e0042c80c0d016107d07165694a500320709951044d020000103802c804001641c0c02c0414070305131403100c0c03000000b0300c1480c010401280002002c1d081d5082c07a0845441403051000c248620542c86c0100c450340c1d003880d000200040c000000603241905000f4000c0d085004508000c0742180c000b40800003128416011140070f00466070300c0701400c0c0e2404404600507007042295040151090500f0607050099005442501355200204400c0302e4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 247741870 1250 247740620 247740629
    0x4050a090c05040e01270c050a0e01020c06161203020304050d050a090b0a020d02011a0d060f0b0405010b0c19032f0f010f05060409120f180e04050c0a0302031207020d0c 74
    0x40c0007605000c44602d5146c6245500b01e85c4a81802419603124028000340280b0f00828200101601283c01ca41c0c42005101e00945020304030a5880780540c485c81c0c0408a50032007514034110018080149503c0ba20880b441581c00801506543c10740c41021651607000351401c904001c1c1c3c100010419003a81d00040c1080c010940040c9041000d4810181c255880d8001c0c111851080d0b40d041c405580b00c0c004404121a444400003800030382c44610f403001498030809007074000d443e00740007242200c00500140482c1100c07400322900c0c2074401c4201c50210840f060028001512180c02170301d4240f013400c41031090700e100400c400e454441303c40c84614149000c3d0306c0801e181c1d1140310240300b4510703510455070800b205845c140245240740e110741040790080c24100d0f040208410000414a02c601c802d45001540c51140a4000f81d071005014040da106031015940d5002e00f00442d41d0614148200f80c0c12240e0260160118007449203a0604d140c01c43e130401d0ba04401da41501500103911050044040c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 247743120 1250 247741870 247741889
    0x304170403050601260a03020303011208121305070b03014a010911030f1501141306080f04020a18020d09061407090806010509070302090904240204050a090c05040e01 73
    0x10b401101001c1a01c0c000e002c000f1701c540d00328030f80010110b50701004880c10b40c0c05c2034206c001e905100c0d00d0146424892224010b14120300c0c2024009550352401001080c0c0740940308540d040b58981c0195401c9100a02c19070240768144000b064110000d111501030f122000d000010b0501c501c01035681800c0c0c0d4442015000100388801400322000b94410403682203140c984041c1989480e0318508000d07031026155242460055900300480c1c2e00c5010402000e40403c08040c1e120b44158001d002020194007c0030041418100040c050200305c05503140f003143c0050244210074075102054010041d9100f1101001da020444d084000718180280212680b00f8180011180902c0e080070301840c5024000c1d60400002030010070014000040e00c03030545c0e40441d40c1444640b11a42c040d4020b1140c505d849030030001c904208014000074255088850440b24460420100b030603841504920403030040d6544401484070520240c802d541c05800c800b4201d0600c4d5203410340707c4856120246090b4407401c101d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 247744370 1250 247743120 247743149
    0x9030105070e13020909040f230609010f0207050a03030f0f0e0a020a12032a060f0b0307050415030f11040e03190207060906050c1f0b03010e030406050304170403050601 74
    0x541442e01c182030801e43d0f160011030410056600081041401402c0541100c000360b440c241801704a00d5075401c10b240c4404490140c0501402c969110f00702110071580d15441e001da03080d407d400500032200341c59400b2014000a0a507a41c0079002050303402c0d1400034541d595412150122400c0c800c0f01104680c900c02001950202d204002c2c020070702d500300200b81c500c05401c002c000382d0402201501a1100540903010750601580080020150103010f4103940c1011024031002c0519404440c7c900000c1e415101e0841d103640c28401940c455180140889255030010030128100e0034040049500c2090304180d41c4032810001002e50315240034408441d00f000664168503808151b50f00400713100c50015002c40d614108021b003118a40e071042c80c042c401d0000d0200c0e4014018014000544e00c1d40c400c1d03800d14900701c03180038020503250003c107010703600c0c1c0300b6521010b16000060b102141d10320303075516140d03980b00e50320f5a404128000480c00401424000800050010f11045029105030b1810b05030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 247745620 1250 247744370 247744397
    0x1205090703020a140105034308070c020102100e010204050301021902100608120304020612010e07020c0108160f0c0b0108010207020109090207170306030f070b0408011103070f140903010507 83
    0x38056481e0b1001c0740b8044031a584d0034107660007800340d07540308106481e611920b2500c3c04284814041514181440c40410003c400a02841c0f058040c2c106a242e5948a503a44e5102030585115402c240003a0145c0e004440c1500940d50a4221400c0703080c2d030030005406c01d03640b200030a0982c0c100c1021201a034242d06421054140d04001020610b441d0540501882c0d20f0401850b1719070062800b25400400000001025904d40c0004c48900d0036401c0801d4101c1c3da560303808004100000da82c0030005000e4040d12030b0a035881000384902030029100c030343c2e0520b15503400958000b011540820103100700b00e0f00c1040801d01c0d01403020300a140010001da5a60420f00c001007a0119a401c9804414030500400000c030390151814142004049485980d94503581d002900c0c00c0038181101242d4400d00f0404280030128402920840312000000d00c079454507902c03004942d00003141d00200003103d00c0c041c480e001d442801c1d02000c1401c040d0009140a051101281c20f41c0c0003180c504003c00c6000c0c9118a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 247746870 1250 247745620 247745629
    0x90207060b030313050603101d0720060105040504031107080c0310060803091003060504060b04140f010807120908040e04030e040605030a060b0303090405270625120509070302 77
    0x84850402c4015603d07007840b80c01103000ca02072501603903006a00c04000a011940d0100310b82010340300c110640d01c02018035000c500c52601e4200d41c1400002c02100b02415020301007070010240c0c0d02484090180c503801c00051000a110062059080108480e0020701281d01030160902800154000d841c03000401e0b0107041c544082603808102d4603160003800c110780078000c4251541c4103c00c0700c40b854191450300c002c60140603983c10242c0d0261801c50000340701c0a0400080003110310075080c407507c540407801000760084554a056000c1048080091002842481e04e5003040c07400c218000f07201d005544030044150406d800c1141c05000c1e0704140424540c1019944900c154111414082c01d801c1001080d222581001e00401b03081c0c489112060a80d000e10a44001da032025204005a2401d8030040a04810f10741c003805a0342da880d803200310040e0010030038074450340c000e001e5581403145101d520b44050036651901c00400c01101910140f094150040d1801039003800000c2c44040e05500411 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 247748120 1250 247746870 247746881
    0x4030f0305040314030f031f050a080703061401030b0403081b04060305010503161a0a030f050c030f0112030c0206090415030302061b0412081c06090f11072d080409020706 75
    0x2c907030aa0051103030164106c01c240480f0b0b0b01208410400b1101200c41c0390550400f19a0303000aa4000780a00d00803448580004151040303a01410091010b0b02003403a4152303a948081c0000740680c4104000200401e000300c40c62500300310408050155207692207001581508242c1011000035142c1c4010402c5242c1082000b6068800441011480c2d00d007201c554540c141040301e4443c611008266507621a01a41c070002410850f44010303c07e5213420100ca5515038821100340c1503244082c1c00100c0e1000700b40165004445d40343c0c4805442c803050b40c0802525800030120300e50300c95181d10030564890780502c126401544039400414081c100240200610041d800720340716521810f01007088144071501406189580000959075118a2000c440d4288031080d00f90300c030b5150500c00d00040d0402c480c0e0141181090040b410869200424605002803140e0f950242441040003148902e45171032918440a9a560604c05003603100113036900c1d030140e042139008040c001c0d0301013203031410300c20503010b103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 247749370 1250 247748120 247748153
    0x3031b14010506090717010e070203090604091409030f040b03130f030f0809150112030207081603020a06030219120615030f0b0306010f03030c080f030a02090a0f050a030f060204030f03050403 84
    0x1c0c80060701e00c180d01b02030300d01c01441050820a402c0020901d21802441203031032981010f031019a6179600e80061101901803021101e91115409000030b601003004400c0d208001b44c4034102501c7c0610300841d40403103030005440070348074400c2004100c00103882d41c081240030921075200c1418050040101a180110052035184282c11544004441d054440000c074190744c0c49950007001d00d41e46003007c92808210741c004d4945445102c200101640b614541841240d100325029444262a0700c0100c05030700900044201a03a02070b1020a50180030f50800d0340354081004000500c03039500d804241c0390800b40142c08010039a01c0c42906c1074403000c1e009200260300280d0041460354507288106022412520015007001004401002080018411103034915141292541c036802c011140c00000d60103081c1c0c00d481502050230002d80e00d25800051011100005c0000e0304042c80d5403591407252554030350480e0136130750820002c00000c600081d134610884c06547c0d01c1d40c6550035460910808100300c240c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 247750620 1250 247749370 247749377
    0xb1005030903120a0f0c170105011404090903271d0105153f0a05060102030d0b06070203032a0601050f0d0201232703030403031b140105060907 63
    0x100181c1010000888040e0303440e16910541075030300c0d21001d60092a542501d013282a00700480d00c1401c641c860a1242c2c131225101607007000741d176120015980300c1100c000b541d13003401051004110321001a441a00414024103041040510f0115541d490000100d96445800c001c55014030101e01203054603140e4114010050034154103010015090440c42400012010400a0106400c8007400159500401c40c018200c07030029404000950000c40f01c0c24060b026000140040c103805041c2c040c4c1c500442c01a0051032414005c2c40074003000e09a42104144c205504200c0e00c3c1c0142c9040004102d14403280d4900440680d40000101c0105005c5200d111254480c5005012980d280c517003000364008102c0c0c0d12074011101c0d1005884400c800c0f41c5503003202035070304203030b0300341900c400c009203000220081c00e01d19892408100c4500c84030394941c12500340d40284000e100080c0100c024009610701516050b800700717610b0f601c442d42402d8403850300e00981d44481c20f0104604100d000f030f41d0000030500303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 247751870 1250 247750620 247750627
    0x3020c070f0506031f15171e04170c0601240c1101080a06120b040b1b03040204020a0203040803040801020c1506010503041104020409090c0f06140d0209011e030b1005 73
    0x3480c0d0301025154101e2003200980d299900032445907070700c0040134160300c4200d400c800d9000c01b4000040a25241d21010000000200d000c8d4898100e540d0309854800d19074104d4903591038403034504003007880041d030851341084165541d620810000380240b45081ca091450340001c94044038408200c180402440406050b950000b001c42d280c800f000d1100b803814600c2a0b0301c00c09a1006480b090348961a2000469103000c188210340300203501c1240100300c40d0724140c6405c280204051a00c100c1c0d8800c91100748041001480c103034004040322542d40c41102d040644078030030325040da405540130741c0c1039a5001032510003954080c00401c010b035121456080040c40c00c1c0c00081c0041c403000708024400b49005001c006607948030b5044c0c1c0c0242603103400c100300c00c00c40d6203003040220803a8041d5030984c100103040040c81c02d206040313038051001c2e040f1005003044c010080050281d00580740c0541030020054511070392440342c0e10f0009038012140d502042d401005010701c41c1200185290500300301080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 247753120 1250 247751870 247751879
    0x1090305030a11101a1203030105060f0c0f01060b0c0d0207060f030902031501060903050c04020702030a020111212814070606050a030f0209130203060a092103020c070f 74
    0x72003680c0002c000d500b0700102c1c0c0e090200c241da08180032280918409403034110700105014141403104d010b498151160510740d2000444595a40800d105442d400300c020050105685c1c2c001018081e26000034003290181c114045c02c1c3c0e401e54440e80c0000103030800c04929104da4038400c0140c01d14061050001d080c409007000f000601035030a06a500d4145500c036a400302c11900c0c2002000304e903c081c2503004484c1e50312084002c215035201d00c01a1114400c3c0807007000f0a14192080322000b9500500400601030540e00640d02000c15020300c40302e80c080d600d01c284600400b800459048041c1c90303078030303642c440c015800903104440c40d4005c8101200c0f1000f500130380e04d03008035000106e082940c0c440c1c0d4440d419803800002401003908101d40003401c0190020070882c1a085040009100310380703841803507413600342c1003481100001c0080c1d8541d00200100710383d0511607000d0707030380c00340039100713071802c201c2440401410341c01010031020000303900040c00c003500ca03024000c00e406018900d13403100049141c07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 247754370 1250 247753120 247753123
    0xd0801050d020f060706140603010c3e100c0f0c0c03320102130806040b190e0303070e0f0d03050706050c070f060212070e091810020d1a01090305 64
    0x280c0000c1c01003c0103080c0260380d83c1d0720341c10b403030359213034041401d11040a51031803a1809540903140c050080d0709010600c1445809a07400303610903401c148800d101060f0341c580c04e41c0b00720900c4440940d080500b074003024208006012a41e2505400600410350f8404c07000c00030311401c031100b140c0081258004100000403e00c9803500100d07600003600701001e06c0621100d001c454032800e12148440c49440b5035a0310351506401800756a41481c4044000070f5407060750948841c17080718011b150b01804030003d00100e16594081060f00900b610020780c00c0c5a000301c407440c1d81d00a481000100f582c040660b04940b0702020f00851420b0305035806100110741c1e55000e0258010402d00411098840c0c1c00036400407200c4c01900c0040d86c209030b81c46401e207032504201000390300401c00c00c028402d0000000d40c002e40144440c2c00d4110740a03110818070b1351111034824842051445101d080c0c014034581040d99801070024081d02ca0305400f00080f40706001c0302c0b901100c50f0031078015060010b07140041010900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 247755620 1250 247754370 247754389
    0xd030804030815100e03250314010b0414060f01050c030a0c0f050d090e06090403090303080a091401020a120e0307022407060605031e060114011202030403050c0d080105 74
    0x505040c801110303114448a80807a14200f8441d907002424120035010040d403111741c2c009201c20540c01da0300701c41e10f000960106c4511074440c003207084c41e40b540b0400004039038124414042071090000540e402281000909884841030074607038070400d01c2c09114880c6407801d610354500c40242022441d060010803000c0d124010b085090060020700d00d403c0d001c4c4150141280281a803004c15180d40c00000a0040c00c03c90050280481a045520004089042019900d4026900b40e1601803441389141e07000c0382c4036000181500c01301c985a01055002800c17900580380c0c0e800d184800540c4601c0365080c020204042d0225481180741004140c26441300003004481032160180c8203060580d07401030000b001200201c0c45440c00ca040080d0150600c61682e020400350b860441c162100b000c02e0081140400c00e410a01081c16004480100011030302d40d094104210018103040000101220b54401260000c64050740031810002d80c070300c2e180700c00f0f004c181c4200c0c00504012113254107100101c1d05a06 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 247756870 1250 247755620 247755623
    0xf06140f0f0310020a080f01061b0602120901020a140403150b01021504050703030807171801151503051b030109020306010309021c02010e041e09020a0b1303110d030804 74
    0x100c0c505a06015180c448180140d0580070307080f9000c00311842d600d50000e50102e04510b0000e604000459040c401580d08a030484409030b50b07005032881c2c0e0070707856421380d14105000c07901141d08100b00000300d401d03251800d100d800c0c3c41c0300050711443c9690015040c1060754100ae00140b504000910010703141c110300540f00300d80240002181548900143e06c1c00905d1140e201620304a0303000c00081040005400c415a4803983c2c40710b2454440440903034450720b0001304030459400080000321400040302c80d02030000503035030010454620b000884040410503404c40c4802007000340a2150860b0140a0140c00c000600e5000d1003442102c41e0030305640c08180100c1d100d807900000456030a0b8880d800c0001220340003021014544496020700d610300c126414103e001c2070b04031410b922075203000d2041101d40e140c4494004000d0300038685c7d1200070144803c08980c0481060008030b4006055405060241d540d05d540c4894942541800d511414000c960b0902c5071400140760750000e0360043d250398006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 247758120 1250 247756870 247756879
    0x10801180f081c060801150b0a08070e060f130e040203030a050d1d0109030201050c0309070909020604090203010305210f09010807090306112701140f0d0501180f0614 73
    0x4550510b0120a5407181104059050700f080d05089035814a035809078007100c0403000200310040340317194072001130031240c825403130403860500c07401954a005200b820340c00126491700013038501c48071001441c0c035040f1984403154000041100c164440340c2d140388602500c00c11070080040d292940c0003039528811000800704206011601c000e641c00740e500603000710b10b203c10104008101590342a402002c01e1a0700707400540c00c0a02040750441c100703040364001d400c50350141c01094109800071015200d01342c000ca80200c070030000010301201510146020b14070840180c0407290030454040903000d6840c00b06000c4440c1041603242e400b00d0381044402c504420f0034108050b07951001e0540c0d4510107540702821302d506010300d0810784000c0c00c00074015401e4804002d80010301d0b4000341d5038280c0000311943e01181d134100400c0c2c0303451240400760040901c080341c840c0ca403a100e0016107065130000c0e80031900d591219030095444660300c0c0182c880f540d4103110104601c903d848090030a805c81d95400301d019 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 247759370 1250 247758120 247758143
    0xd110a120516050607080d1413030305100e2208070305030103050f1207123c05040b040e061c0501140601030515190905040b040605160207050f04020c0d0e0901080118 73
    0x10030040e07400080e03100b108c08210b04d0591030300206541411841840840000c0d1800002134070400900d000e031410b641205188250940e10429074509840c4485000b918a032280d2001c81c00040c0110024040f0b28444e036100781d203039403651902528100011500e00280d800510000080e599042c098424160b00f12619040301e00c0c9501007650300440390702c0c6125080c41000401110244411003c3e40241194014407440362141070084035180118062452400d00800c41006440402d0090b5508280002c110b00c1c01b080350644101007064514008035071a94440a400a00080d010480d0354000401c2c2800e0055143c101901201866084800c43c0f04102d0b00b0791004a0362440f5907240090000058104498141420040018441103034102e0f40c050030440010180307840d082c4079031004130f0307260000c0843c06d0900b01003200358410300300401c0d0415428050801e540404000b0070704031400c542c82d1414051440c506004803c401608611403580c140030011160506400c0c01e207a03030582105a4001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 247760620 1250 247759370 247759387
    0x70210090c17070608011202010905040b030c090a0920030a030f02031b010605031b0307030807031403010902270d030804050312091b090c03060d110a12051605060708 73
    0x1d4100751500030b040c001e0340c4461003000e48200001c105042d50000d0300e6441c044c4c0e0b0703294210056000034400083c0003840e8000100491300301900407640c400402010340710003944030408104140301c106d07600d00c14903454840c25401e01c0443c1d81010280320400d0802e1041c40690300120b541c03002d0700311004080040c603403000404d05200380169440e0301104d4a81a43c426402039000b4003030300e107900425100e40202031140718542c3c80289071100003070001d80030300070142c40c50300d848080740c00450f016070600115100f0b03404690fa01100a6000c1c11102b6030041e11030541c02a000c1c2c942d500e585c5000744800d00b402040342d180e91200c07035000341a0762510b040c4588e83d03a24a0201e0440c0920710b812091354060409201005401194050042130300000240642100b4030800004031000d496a59005500300003164050a20032031b6070540900900f04000184108008501203080950107000c3c01e40400c80d000341000b03000d010900b0118402c1e0b8441200c68140b1000480034460104024401d1100095010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 247761870 1250 247760620 247760633
    0xb030907181d0705030601061112040902030150030607111006060e0d031704060f060801021206040b1c0506041203051005040c030905070b070b060907021009 69
    0x900004800c0300c5001e2200051203014120607009101101c070301030302014030503000082007801c4600040040c5000c2c0d1a04106580c051422142c080082c0121992043c0700e403901c400400051148100044c1c0e6580340c45000317420340000d0140403501e034900903000400c034048690710134100700740c8403101d1560060020b02e00e500036400e01043c40c2c140c01403208000c0e90b00c0d00520f5038051807220000781c038181030f04014020101d4540f0b01590700840e107041c10926081c03c1c0b1070b13680d22040340304c3d05150150131031400c016a0016030441d4120303a055158000713034240103d540600002000303101c1c000c0d030400b00e40e041400d4400c000202498001c1d0b85c2d41c10201443e03650201040c9600c1e401c0918054400860b003025900d030b24003100d00f0748401c841c00070030450741c1c2c0c030900c250703446000d100080030207503420300040002512403008134104040c0c5400e100004540280600002043c090540540d1080c140c9081044810010922031280a103001040007564000c600307088448101400001c124000b0315001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 247763120 1250 247761870 247761883
    0x509010201200c0d02030a0f080601090504050a0606090816050f0f060313030e0619080603030409180510180b061f020d030e07060c030804151b0f0201150b0309 70
    0x4450a03642c00d0000d0411540d400010720201e8409801d44084012018040e6501d00c109607000000584c0c2012101280340301d065003541111052510300340f5a580c1e00001000d0710010341d410101c03550307244400c12070540c1144c0200010078401001c0e00c01d00d516412504001c0303129205080c0120f614100d850040c2e50341340e82c421915140208616280e0404410030500a01002022001b00b8554450b0f03500b285030038010380d000450203c1e0150650118900215002c41d070160a085c1c01d0b110030702c0301182c5080c40b070013080158125a140440b1200d294103025150524040c0342c041e480303241441e102c02c195044d0908a10054010811070550389034040415454204e002040030034205020514030340560100b81441070b1390f842e681c148645151401200c6e240c03e0548612004500e0489100001074003d08003d41c3c0700d8054075005514080d85291801a5110004070001c8441049031440c00c1c241c014105070b0b107000e2180b00030020f484c41c11001024040050203141102c080103c0086c828240c1000b09 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 247764370 1250 247763120 247763141
    0xb010e0111030a2f0615040b0d06020c0c0a080a0b0a0515120a02190311090609130f0f080301081005090703150b0a0b040f0501030b06190207080a03020601180203060109060509010201 80
    0x81301d038240f8000519220041529041070350421405002c60616050082d1629003074000c042072190405591800000e5000b1381d43c2c10601c1c061002050101c1d42e81c0c5140c40002c1000c8009454002524685203030591801803200c04207c0c941000e2010100004020020b941c0301600c2c1c4000655410703210510302803a20070003d602c40b61244d000a0707090014103486c2c003164440c1c8050101070444e03100308801c00c0422034910350071221030030000c1e16030001002e600c0c05041c0500b619100c10041500c0c0c5c10414024000284e6000b07800000400107414200800f0311001d2050300100143c0c14007580d05500c8590600c00076141c40c42c0030401c4814204a42e000d101e074500000c1061004030343c0c5005090090300588900b588102d00700e000010303076501a008002c0700080080000b0b15010501e41c0b8560050131501041c003c6101c0e0742000f09820340d04004180c80c4c0c90107a0020300303003980340c446880603c01884454200035070050051103001d9800c0309100c1c082d590716007001925584043e00403070040084000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 247765620 1250 247764370 247764437
    0x130f0c0e07050d0b030a02010c02060a0516080702090f071b15050a060302042f2b02090910060f0804031103040303030207110307180f11030405010b010e0111030a 71
    0x5100740c0d00d401c24000c100090321864240b05840d44101010b03143d40c04841c0c040c2c00304071140701440c014501000200000d40890800078104021805c9010886044903000c990440c03001030048103500d80350038155400840d8100c5e280082c44c0c1850003d0005080c503c900005d001d16018003800c00100000720324810707118034003c201d140381040c00e88014044510059000e01d103000c0901c2c910521081d400b802c0306402000c0140320081d800c424a80e69407000e101c00b0350710402c003107212070100342405090907486200600942c40c1c0a56108001d1b42c41c202500c0440b42500c0340000700121900324403001e03140c00c3d90b4100450341e81c1d900c0c201910107400381c201500083c013002030302104064260b4040e0070040e00407440403c9290810040c981c2d141d03154018500030760004444103071180c006422028490600641c042900100740503c442250800d42d82181c903a51102103001c9603581c07140106c42030ba50240f80c10000b054010120548901c1035038008400c10144141140c030f545082040c030444000368a4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 247766870 1250 247765620 247765649
    0x14070302010915020309190c0b0316080f1009050403020106172a090103020607030e060a0801140d0b060f010306031a07090801110a0503130f2009130f0c 67
    0x60000e0080c0300c809811070300e40320481a044161243c41c420340b445440d00c074000b8281c3c1c05d4950141d5545219007041103801c48038410004c00d00e03181000295020f80c0c08910301e16890f00d1880700242100c0002800c141303550009208000440f00800b02d03680c12a40d001500181c6a200c40c04d00306d000d00001e40100f1004101000d1003c250781001034513000000e000c00c160022084004040d000340710440310455801403640d001030016190100051514038800d00307001a403402c50328081542500208020004039619400400140300034880c0f100c02d9050440307a840c0c207601d2903038400307145075809065240034007198240b20041d80d002c1d90080b4040e40d005603080f072401c3e00da01b05824071101c044400314002518003c00103026081401480755000d8490002401c000210a0845e4107400c0108818050046402200e0105480d10364000c1c91034007031100070740f044000400b06036030f202500e9030542c05205101c041004440081c1c0f1001070b40c41d1f010407116803031710303840c24200749000094110305404420070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 247768120 1250 247766870 247766873
    0x907030b0a030c08150610080709031b030204060510080f0604020706060b0d0e0607020601060c030512130b07020a21020309100e03010c05030606031f09061206060b0c0a03030b011407 80
    0x2200480448107254125110940e100c1380c5a10700c045e003501c4440e08045481c0319484600c1c01103004591040c0c05140800019560313441d1400818540300103800a13003640201130056017810f02441001c0c02c803e9580041705045408000d255880040019a01807101b0010541e82d03911501181c4e405601304500f8015591030340d44c600410fa00c0172112070b06040c640010070307001000118469103c0c400980150149a1074001700b641c0045440d2400ca0412104204803000031141c2c1c0e600600034103941d001d005841910f40ba2041c00c05a000d4201800d5500c08025000003c1c01403001c0f150941642c1080f03910a201d8003400d82c5076003e0601d409500c0402040d0202c0f502d82d0100712910714000c21002032040d44542c540139a0207101c140c0c3e0302a0010030820000c5e143c8242e030a003c00c03001d801c404a5080040c2d903180184100e6011307401020a112424200d0740602540f4050607001e42051011207143c800d0107401203603512400030004040c5901c60740c5440c4030340e000b0750141740808200b0a685540d404103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 247769370 1250 247768120 247768133
    0xc09090c030203010e0a06030203030f0d06050a0305030304141f110d060e09060109090f03030e0f030c07030515010501170901060b0301170f16050d05120d020306010f030b0108060907030b0a03 84
    0x174052002a01703460b800048550106000f501c04803038010700914500440061008041e91180c880d0050441c0c0b40c010000d11622810441001035005001954881c1407620b0010010b001e00c0300088001d6210303c181c1240030641c3c090b03402d0401d506040003d400b0b600c640a1107680c0c042c41c01824840e5240c000006241614501c4985c418036040d000e0382d00c8d03680c072010500220788900700003600300031b01c0c426201c0009019034071400d074420b110310803a07030224078071581c15165900c0180c01043e290015030040042150410010a40c00083d200d00c21a80d8100070009002050707011031091001840d00104000240070345c410070103090658403240c0d0340c0d0307140c6064000707200490848082c81d201c2d405514014000c04034990843c017450360040c010481c40c103810825841c0089405031942e0003010120003040b49550018140221100009a164504040050026140413403042c092505085001070503a1307214001541c0014101c03090b0481d45c4401d0002c4006010980c24683c002c5100c06002c01170082c3d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 247770620 1250 247769370 247769377
    0x5010e06070905030d0f0c14160602100e01141b16200607030e0405070908150402041d0d031a3313050d02040b0d0b01031203090b0a0c09090c0302 64
    0xf0030340440d602021040e0003155103181d1500c81d5030005000300040380c002050340c050500c00d001802c1c200c855060541d034440c104043c456000c40050ba1140d0b031480d2100300da82c00b80355150918a0020424a8810646450703500c8005184124800030300c01743c48281080309007502c5103480d41c10340610346006240f40062282c0c855585849012400c12a142403510300f80c0308490b00540d15688000c0d02021940c14000038050140c05041409860200407410003001c21203c90507500d04c40240c07045007131600501c0100c41c4240070640b00c40780803112a010070f050000c1e07450418441d0340381c00100310343c0000c100007402e4807280d015031b0711204c1300500c0310039081c448810f040f00700580420381c2c0d07040c0c9010348482c0c0d082c0309070150b12076240016541045103141164101400d0b81c0054801720f420792812002a44008030038404886a101c0c400040c4203026a03a00d01108071101d9090420140d401c41e11913010020000304030307892103030311141c0b0703100d126101e0201e50000b0400d0032303001d021000c08024007601030341 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 247771870 1250 247770620 247770629
    0xa020d0606150c150506060904270807020a060302070314070519140601090c02100b03070b03100e0c03040807060e070306020a11060606040e0403080411130506030c040b030d0c05010e060709 83
    0x34607020804034000b48500c05d20b40240d0f0700814151620300010180f1000d00a100c0009900c503c0c45040b20b503074000380030180c0071300b01d100d40707241ca903111201d2040009070202c580040b002c051042c001c10000a030000c010303856280c010710030704e6103c41082ca007603464501d610a241d607030072051a400c6010054010007a401c2001108142c2c1c18583e00c035903080d001c460310082c407440180d00c0001102140001644070491080340617081d1031400d5120004803400794000c1e11914070352000c004003003102115100ca2140c011243c1c0083c01e1442c01d103a155010b043c001c2010245c0210394071003400480190411129000f103074844425521000000c20150880c104030b44240c8076406203a00290151914400f22404e0b00c001d0003903503100f902e80361030403224604021710844121485003c0136200303a66034183d2303102c6200070820114040c80d048080c182829810017042c2d01031802c211524401742d40105901c180a80d042ca041d02003a0182c0c1041d902401e028181c0704058020030090203c42c603804005034003500c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 247773120 1250 247771870 247771883
    0x1050730020d030e071e0f0b0a14041214100f020c0c0d080a0302030615190f1706011202070c03050c0a15021207030306030803070305010e0a0e0a020d0606150c 70
    0x10441c460b0240c05994050140007500e40020105210a480c0c0710055074484115102082c00302c1d80310b038005101000d6070f40040d07102c8540407a40d5100d5590000d00e00c0380d500040003d0b07a050078540f40c40c08001c00a886002007496a0040743c0d0070800e40200700424010321040800c2c04061403507071448009501c1011080040e00410a002080b42805003d044032070358006245443e00c4490001100250405801294084407625021380386040c548017810405680001d00110208c0b8020050709018400183e901844082d42454052404007440e2507840102800d086001c968031500b200002d00c54004003c0102c6080c3c0004000d1120010b040b40010f00252900810b240c2c03140908211080c0c00320b0041c0040c1c0c403003041190301681c400090305d0030907c2400d01046440c0c50380d0740c511058204550560009644000400c014078172032f0200c541202152074104600849201141d03140d0b03000d250040e0180080003841b004000069010000400f810582c40c4100d00c006040201013015900090303541 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 247774370 1250 247773120 247773133
    0x605010201090803130302072c010611190204061206050406140402030604060b0303070c03033603061112180d0516151b031d0c09060105073002 63
    0x55005114600c84140c203c1c0f1000e04540d601d09401c01050b4071000114114082c2103070000c1d140742c40f613510b00c50004940342d010000340e103201600c8420b0041644101c0820260b40f00041800070b002c690f1030680014180c540c81e23001081c0c00414040c207016800300708074036000b02020b0288140e5510981c0154844c1509010303540010f0300c07002110f4000d840280d030503005100480c002983d15881748101080c041d043d83c0c10003a5588481c1c0d0a1036030356005601181c086200c1e5460075180079128542d100d06a403081c2c822601850078100e40301264000185400d41d658003030401c005603071050360b100044813440e41250740b401d00003803680190310702c42147c120b00c05d00b6455580b1a01400541d01c1c07407481e055203281c080d11651103103c01010240788003003190b0f43d00d01d502c0100d813040d4441028150b1990b2008a140305040807100d441946040c2d07851070303d0304800c00400c00c0343d60305108035801c03100910300a506c481050030402850039070031450030030410028518042a0106613402107040c4401e400340ca10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 247775620 1250 247774370 247774379
    0x3031b0f080a050126012705010516021b01050f0d0605100507050d0309150c0807091706070f11070e04020a0e07120e07050312070b07051201090902060f030f0a06 71
    0x60f510280a4051a0000c1d0b9020320300d07a071000001280701c02074035400401c0b40c500d8600d540e4541100301c12100c2d0610742d20114101404001d00849400010041d4807898905011a0003915003d064111000d42851110090341c160700c500d041d1400d15552100ca61365030303081000004020003c174800c80d8040c82030312084140b0b0342c1c051015070368003503001005010b039503180035801c8008003620795007100c0807030003204400c00c0c05504d8480c00ca0140c00b01e440d01c000c00d050190000e0700b03100c070944c001000104000c98080d25020040b03040c540104150500c510402c44a40f4280d403202070608402c1c4541c415103078005800701910710303444e008500980d85600400e488452080407032001b00c5072000400c10f1551418440c44059005016000e80102620011516040003d080811101501403c4540817800320288000c0050080c3c000ca001c3c01d0003440c0c4101450041281e00c01403062003a11662070085105540780c82c8120303000b500c86212000d03070b80c0c81c0007004112040e106488103040301e0f2800c1360216 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 247776870 1250 247775620 247775641
    0x1d01032d0914070609090504020a030f050c0a2c040218091c0c08090f041b0e0906030a0201140f07080d0203070e0102011a0f03010b030d050c1009030e0d03031b0f08 72
    0x1040c1d84e07041d55060100c41c141284e0002501000e082281c000b0340e00c50000020940080b00014510300c120080e2480701d820004204101419400801049000d035400410300c1c44000c0d203140c1d491072501518100365540340000380b420a19049900d001280c00b6040002c020320204900b494a000341180103400107403081d003102d428040701c4d00140710780002c0001d507410307182801600d10340d940002c02c08216145025104040040c00303400c5800800c0da01d4550a08510382102d090ba8092030650080112140355000205103c140101c0601d04000c00284400d441d4880300c200d6440c40c0c1c00031042a074030780d1020b13a0603000b584100c03116800220940401c0c4c500d50301c1805034040f11401030f01c98003440300f0240100140320055980d01503041d0360728060980282c0b81800700d8003a40d29143c4400351a0000c403550030b0300b0b081c00e10211800b107034a04031101000a0304402c1c04030303a5030030950f440300c140300103850190014881d42c00050700101815842802140c1d10900d402241c503581d41d191286070f00e5114152 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 247778120 1250 247776870 247776883
    0x901110702220b19050103060504020309030a080403050c010204060e0910060503070513050a06020115140603040809011112030601020721020609011b060b0f011d01032d0914 76
    0x940c0005000e0004401c2c141e2200202064204200d000502a1200340012140d5200180f001c0302d074204410b04109668261003140c00400081d00e040d45036203420340599869214410503882400041d001090501d803082042e83c4184443c04000c40d500c80c1c071075201a003000410001c640c416102000010100c14078020302e1000c962490300e82c5030452300c5518060b105074014005074074035048290341c0052940e460084d440010003058000003000d00060070f90061701e40c240d030410720349944c0c060150800741d11840c00300c1c0e134003d0300907101035103034803e03200121200d07030030719015034124400c0d41015a00e2411540046000381800d8003110302c01d5030350302040615407907080380b07001108810a0018000d4100907000f0510100b05144c030390180810806464003011a507901039426035603a800d6040c03030341441c0801415009090800c12968044507400780d11f80078201c070040b4101500d550700c041504085240e8007020b6a0124160303104401021402001000c034040180c50b1294180b01c01da00611010412 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 247779370 1250 247778120 247778123
    0xf05030403022d150c060f070f11071401030e0307060e0c030c03060f0c04030b0109020c01061406090d140a031101060f030314132c010501020c0a0512120f0309011107 73
    0x40c41548038000c04c000f40b40e100004503e0700d150082102d92500031040c40443e00c1071100c2110005a810590750090150103200380840600040c0d040c81c1040036400505002103402204c1c2c240505103081d80101d000c0c080701d040c0305119100108e644030070014690480722038000390300304079500c01d44408101903031000c48001e102d415801150120b810f04071039040c1c0c0d69011a002c1d448510f8942d03a6592001d440100f41d101550190b8045030350359494000703000b000c00038030800b036030442d030340c0c1110000900c5885000001480741403100c00000401c4280703801e464a00310003000f510b8090a0a0402419001d402d000c0d05003d5480c040c400f00d0001c680003084030559030141e42c0c030a41d00b813020340b221a299000c95507180082558020006960440101d039407050003504400090382064404500900343c0180c00590540d0040c0d640e04c1d600c1c1d160188000202e420031940d0b1048d40d030b0441002d9047c08541014403074038903000504020ba099002c4c00440c003c4010b140200f03c403141c80d8050440f6400340b0b000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 247780620 1250 247779370 247779439
    0xe01060b161a101406090603040302071a130501030e0f0d030c0e0d0809010809070e1003030f090e060d020607120e0306101503020d230106020c010908190f0f0503040302 74
    0x24240513100142c012070360b00030700281c000f80c5814001400152a0780088030210b005911002040c03082c161080400100b07148060501400d01206900048810090380142c0d810550b40390188020f14204100301a5000c000c5829a005a43d038000d00802500040709080049082102050042d02b0084c1d082c0540c10741004a260400c000e4000445100101030038014840c492024080340c0c0c0707178407407544034001c0c641c403a24149110b00d075140243c0a074410b43d0100701071100b24a010031001c0d08000d0030f103078403c004550102c040c04c0d0520018009010b400c0000e400741d0345000c0420311140d000031032880c050a0880842c2c42d0303507403540440111000355001e001420481134401c10a618041e80240c103c2030340314000415004200b002580116041020360303181c4242e450010003a80d80c043c0b180240100c428a40804c08505240d042c0e40d07190140c0341100c4013103d184604e5401e100406101c00301869000400100301c40d82424025038941103400280d1086500c80f0303118072090002c11518031104038010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 247781870 1250 247780620 247780651
    0x4030b040f08071202061b12070e04020d02030a021e0c0705011803020303070f140c0303070b09120301180513030806040c020c0418050c030d120e01060b161a 69
    0x5440d00d00441070340c01c046948001c1402000300150183c40e10711610b440542c002d0080e4585090040010303d552100107040c000108a420310b0001030881d956401015410040840c0c400b0300302090081c8034101e00c10280781e2012092100740020340d0010008110302c0460b21024610b403c1e40440b0300e11580c900d043d41c940c0001003c10440d4010f5180280b4420540d19030322401340c4c0c81d0007003811a4481034007140c50f802c960003c0300070447c10200031807448902e100105900d98141000c0785e170328801d4110250160024000103285e442c41000421132160396011941e4407541e480d058500d019084441719090107003000c0010380340c03031480d81d8095025605036a900711503885000501008106002c0b0b01c0c000c6000f0510724a4281d16203004201c0500000c00b80c0c004104100e0910606250580b085d8501c0394011050710307013406901020203403180f12080c60015110dd50704000c0e9004100300d45c8660121440407450190100042c455030807a280034420712080c2050607410304910780381c12109100300c0c44202 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 247783120 1250 247781870 247781873
    0xb16090b03010e0c07060e061e0903120402210d0f0206330324060402030601050304081605070303120e010905120f040f080c0a0803030402031011121015020304030b04 73
    0x40c3c0b0420341140900300400d160240b2500c2c3d80c41a03070410744199405603c02020300c85148030f80c0c04112003607130190076242e01504103104401e40f81c2c440c1d0081c0079807640c1c00b003000c10150350394101c0051007415000001c8643e05683d1081507180c9000315403d4010542000382080b1035400414007502c140548a030074003009501200b11040001080b0001d1074440e148244010f050b141041075400c044a0140110b140e040001040c2100c2d074402007459000307600610602c00940d8214064035000343d4420b41582d21500d03008100ba80b40401040042c09500c112a03001040c107403c002c2c40344007503040385030a204c141e0038540700c0c0d426079403c000014100d40c480c0b40880e40001c201009810700910000c900c03860a0b55071107010000c20741940050200c1c3c0c01440c2411680d160240658004209035400f0f90700314505a00002e880e00341501c010030040d038030b44101c01e031460a180111140c1c0b903c1000300002d20b08001648280105c6540a00542030b02495045c60140f4000000e44080700c1d8000c251548035030301d6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 247784370 1250 247783120 247783139
    0x203060d020d060f05091015080c04020c0a150507030f090b1b040902190801050a0b030c0702060714010603030f05070c1403030412060e07051c230a0b16090b0301 71
    0x2c0b940d003034541c0359035011448010340c11400b8040c014500b4100501406902200b0001203841020504641c00740d0150100f00d48400400c0514a9803801c0f00d00503100c1d20144030310390070300701520002819400f540c600190104070760340c0f1190283c2c419030b808202c3c00140d03042c028125141c121020f04080403078070000b140d5100c54680c07100c0d01545001c00600f0239030303a69051000d03604600451652814040018070103240e00000c914010101107422500d0f040c07400001c42c002d03110242c84094045000508001035440380000c442c00a980500d0704072030131080201d000d0003404c4500084001810002d50103285500c66070036103040c2c54020b13402c42321540c9460505803202c4c00c3c4880f019003500062100062500c030fa6a00c881c4814096034003ca22104160202c901300306064100c01c1c03041e03607491428841c0848001904800aa100b20114854000e0015a5105864040340c007009807280411103010002d60409450043c03c0d803440c0240c0d100c29185040e20001c0e0b49008840765200d00b0310040000440 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 247785620 1250 247784370 247784389
    0x12020108060f011206030c090e01020a08150a050a060c05060a02030601021510080f15010b0f0d02070c090f0b01080606090d030c0c050303070605071e0504050f04180c0e0a0203060d02 80
    0xb41410502c3e89040d44085440c05d5132800d40c0203840b0429200d10810100c5480d00440c40360402d600000c519108048001070000b4002618024040550950102594031008581c01c06800300402e0355103804d6a801008248112000040f24a4080d0b100811000d00da14000e81e4060034058026001c3c0c2c41c1178141e10fa03005940109014406a041fa0002403850000e00c0304000c038504504c00b0b44517098003140026110700040e403140d0702e02c5c40108680d9102c0c0801c4030540e09500003680e03026a58a4060a012080f80169008810004e14111442c0d41034007265001503001d09080e02c64118a641e00c4040112501a80243c0b41d0050110b030281000a880385059080740362049a0b0f50701e000c0e4072000031a1075030b00154801c443c4260b41d2414401d00c02d030821010420f000c085002e0001034900c00c0002011400341d440382900a01050800c08056a1903400c400c04111030140181d0040d00c0c2c81c01c0003002d0815506c1454203c04074000410100c21403070007205c1c460500500a0b5800207841c0d803d1003003104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 247786870 1250 247785620 247785649
    0xf040e010f090f0311060f0105090a0b120c03010f0504020a090203060a091b110a031403060d0204020d02030601090f0f140d0b04140f010c170705091005030406061202010806 76
    0x558600708034929031018407a800c8841c0c0074070000d10103074010f0719000d0400011a101c0c80d01992100c0d04001d90182581b00c4c07241510001d03100c2500a45070341c2540b0002d4000f14100c294401d42505100700000e500003415002c1d64021402885000340d2940d812040b640b0988002e504a110f0349030500521310580c0080d0b8015001501c000001d40d41e842c03180d4103c840482c201403402c1b02c00c64503059003540c03004000c450f0700e0306000035000e0040e55507030207006040780c0e07000300649020200014000782c0d946010810b84640240065650346c50b000d80c1c160081d40101d494501042d081040416807403418401e001c1680c010007200d1100c1424142c400f0044001011030715070060f800494000040e06121059019601c106c200400c43c403101f180c45800c0400d011102c10300790380740c106114242c50344800d4130801800369031a04400c648070010101d80d24807400c800107822a0131141c1010407158408001c521490081c031003086007580303880141c9160b1001c881c001e4001150100400d085c1c1c540182c0d40420391 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 247788120 1250 247786870 247786873
    0xc170f030103080f0702030d03020d0506060c0a03120b030f07080106150f1b0f060903030b06031608060f040624021209060a18060e1503070206010e0901020f030c0304050c010e0f040e 80
    0x500d51b8006841c108a41d0740550010340c011940440712149402117980082c0100c3d8103d042040c440d034a580e640c51040d20240410800040c0c14000350000d500c42046002e000e01030300c1100b091fa12440c0e940d034015100e1f40545600e44100090141d044101890701e00a190351480e00c0d445410104481c00387d2202c1c00486c20b10602180c43c0f00285943c4001d10600b842003202240052203130030b028003210401300d00d4034059001001044112828000f541003c031490f03003040d82080d1a40c5000c13400c400014900c0c640c00500d8410082902d032560748800040f070f1490240345940c0e00990b501240c442d100802200038642050107406828038000000d005125854a04081c4400140c0c9000b50b20f107409600a0000c076110480e00d03005810061000c00b07001d850941910310b2744c2411240299280c50500c00c143d140030b80d50b0f0101c1d041442c01e40496042040c112481e54907420800400340c035a600c242c1e000c80386072040d0301f134461182d40252a6000c512800410700c0c044074004806100140003400010790301d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 247789370 1250 247788120 247788127
    0x6040b0f0a060b031501080702122706070f0210210e0f01140a150b18121027121107030503030411011413260a030c170f030103080f 58
    0x10f002e50200607605c542d40150820055500030b1002401c0036202404200840d00301c2982036803204909011034001c0404100902d403040040d140c019001450310450640c0030900181c0c940500081e880c4a0000030300840c1d460b6090150090151652050344002d0400c00a8a0907000e103032000c150b1083c4000c01c0c00360b09840d5002c0c040c008490031150305130301290320001c14078207100040503284502e1904001c45000c501c46641005042c00c40c074002c10041e6583c0803400d02d041c0b240c2e610b40d21004c8100100c904103c0318cc843d001c04240c406441f001c0542800c5c0c100d0740e20a04035410707090408000c041c0e00b00100004c0315203491030890704c010b8045e100c600c0c01e108058000001030b01c1000250301c25805044003000130100c0800041c07122151102d9180c44903410300400282180051000c070880300100184c10759405040310904a4180200040c45c0030b0003031111440c14150840603588041c1c0c0314003c1c00c804080d81034146007042c01030b054120034902c2d06000510001e0300c140f004220340d104003031440c0d04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 247790620 1250 247789370 247789379
    0x3061b071703070c0b1302030714060f0f071e08031803040f0602030408060a1509020310030b01060e100504060f05071407081006054606051b06040b0f0a06 68
    0x15070b40291103090005950b50060824440e17034000094225081c4840d00e807002c103040e00029030311001e9024014452450003c80e0180d951048111071405145048075a1205d04100410303095801c4441f003034032030260380030a107451035604840591840380d0181c141801c6840e06554424000ba484d45000701c144410000403400030190a602c500a19460f40115a00d9061201c55824000090302c0715640c0c0d810010304c448510b5072000f960b070a0728402500140c1729900c02c3c0a081e80080a40d2024000440c12800400c440d42c2c04017000072800360940365070b031140900190448461003079100e070f600064022006441aa841600200b03200c0d030051400900c0d9a404601150402455510043c621741c00a0b00044140c034290180c0002460111100d009140800744050000000e82d4010340c1783c40c04040199801440240e9010340d950b92014480e014035841e032001070b21543c00054000e400e2a0f080f8100c0403c0c20000030300c18800ca90144201c0a251160a002028200060070072603484d9180c070750201c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 247791870 1250 247790620 247790663
    0x141c0603080c0106050111060708040305030702030906070c0602161a07080904050a0e0610080706120906060602011a0406030f03030b0619020303011a0a1d01121103010302040b03061b07 81
    0x29000d101000024413034076205c009402d4201986264689401610400074035541000341c0650154040c00c045a0b80d5407406c200701c0c2540324044120360b114802107162002e0001d00060700c025240150212000d04055610580000b004c5105030343e182a442528803004c3c2d581803024008442c82940d9050034000e0040c001419905d0489400b85807a95440b5160580601004030b0b94200720520b0859410300d0411803e40e80350461070081405101c048050681d148078558050185203030040400c00140b911800006c0c003802d0411002c804401003c02d42c0c1e11640352a104020440354880c00e00d40310803080c3c2e5410307009001001841d0fa032024090000c4415803a40b80302c091000c0c0807c2e030145940350b0500101200070315034031004000c854406d000d50388d40d0540180b1261030003800e86800b803d07030365119030048a0a29100444103c1103050504003d15500200e000e181a00e1080340c0500003003550704103065898000700c034000c24420048101c0d1041c000401c000380016401000c844401c040200c8151 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 247793120 1250 247791870 247791877
    0x120e28050d050a030f0f05030708180f060a110a0c06110408120301030201120b09070e04020409060807090e010510090509100203040308060108010609050a0501081e0712060501141c060308 82
    0x669098000000443c02c1542c415400d01848009083c621001c80203041d0040440c0001801001408001030201d025000309020503598800c01d1800c07039124218120b80940c98840c1504c183c251107050130b03180c150030385d421420303680000d000b42d8039014a4411034a5000241c98030040c84103c40f40e00704008103a4060601028074019044029076560354998400102080080f00c120303080d440c42d09014000c65070700d4418241e00600d0f00c3c50610700000381d00d00010024499035000f0310445291010004a4034004a40c1004440004c54100440b501810300340b420784104403401c810b058245541840b0806a81d88095013210a003412a0300100c51206204202e078000d6a040d4040b50059082040c650381c03044030a03000d04400c1c83d2600600749428045001103c407800303000c3c107000d400c0d8006224042c0060500e0380291407503005200904140001824240c03010351241d14440c00c00501159a50080400c803003032030001e10f41b5a190141c0694002d11510880486500440c0c480000102161010018 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 247794370 1250 247793120 247793123
    0x1b17210d060b0a020c010302090913050115090c081608012601090305091f020316030203090a17160f1403010f090605090f0109080a081b0301060804120e28050d 70
    0x1540d5564007070f5019103003a5010740000c0c105401000b40408035100c0510107504045074a001b1201e07100e6903c0e201e4050141c040c034a12000c0d080342d00000d00c0428503000200c9150042d1509840f540b1b400040705640703410350f00034030b0106440200400404502e0f07003c030f088902240c2081c0e0b410b0b40c40c2210306801d650107680144c0006402081070500d0b072401c2c07036204524602d00c0303018001d04442e01001030b44038011200d650410429920801d42414000e00450341400b0005042c00300e52501da0700000f4404800c0c0da0008030501c0f07185410b074086940785449509446084d003405203464a40f4501c0d0070302e884880c0c40341c1d4040d500c1c1c0a0407902c1d84c1450141c49046403142c0c5000c0b40f907140980c2d94602c0c0090a008000c2c89a04191010340810a8582142d2a03217803980ba020b00a40d951442d2000125a6420603018485c40003000140c8170342d015400342c0c0114030980d05a004981c03280d03000c41c0c240d000611881e80c484e40110000407000700c42000c0c101d20b26180d0303180400f110341d85d000080103d94200700 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 247795620 1250 247794370 247794389
    0x1141207030f0501050102031201030b070908031201030b0906090c220507202d010b0d06050403030605091501030f110705031c0c050715060b071b17210d06 68
    0x40042c210021030144901500d001e20055007450228840025208010310000d05030790300c10004511400e100b210104094142c0c1000c480c1c1d038203404000c6907800c3c4400d00c01a6800d200040100f901c0040201300d4030301031344201c070080c40b246402e00204441c0c070b00d920300041041000c0d003001e140d665080380110f611554054503a14484101c0b20142d14100785107004101298112a2052135034580c09002001aa0031b45444002070803241081d07180140740052a06a008605000d00320411100b90441c900c5184603550a004c05503030346061040e1414207880348040c4040604400aa9501c29805021010280030000ca03400c20417a43c40072842c0c0c404641664240c01c0068085407031840c4001404161043c40c0c410082f034260800d0042840c007070441c00030124bd2000c06440c4102009401450140a2170b01c0300343e0340e40c1715074a048111840403a50f0000c5101e24040006903030360b000c084c140000e80114010301100c80703e00040e41100108510302614000f802d000a07900b105091007208041c1881d40c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 247796870 1250 247795620 247795631
    0x8090c0d030e010212040b121008190309090203060f0607050a02150702120724030905010f02071208010311060d0603080c0a0b010b040305030904050a02070611091212090114120703 79
    0x10002400c144446507107076110712040204120072400001107c1d10180585c4a0346000d8460408ea00b08003109e40d030080b10300788030300a100c0b186c40e00b5071343d0f03550200c504c00d891b68010242e40d020303620268001215280d501c034001190820413420610010113200f881001a220a00703e941e00040548150382400f02c100e00006c1140e2045090030808000c0d000b0b6440d00410f00c00345843c1c1c004443c054410344404054101e003108508440c0a80c0054240c3e41c0d000c0028404e0b041241003450007500300800c15a510340d10750384c0c00044c41d170042d46030505aa4001c1c1450340c40005541c10722000341e00000020f44199540c0e100007010a00c81c4c406482154201d002038119060203080084654030103030040441400104810400074800108a42040c90b05880c0422a6580c0c0801d0200034081d010000d02607605003034007507d0301c825050042c65902c40844440b10809100107289a440e26002911045e0540400000d1150340c002c0403030501d6140310482c124a01004141c9403079101100761030040200b510365 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 247798120 1250 247796870 247796897
    0x5010b03120301030c120213050c0306180f0406240909050c19031b15030c0f0c11090c040503490e0402131d07050705070608090c0d03 59
    0x900c09102101c1e1101409400e40d411501c0da1510240d86110f18199001c1c00c0701c140c411501c1da8035117100205200d071810092858040c4518813158011241c50f0300c11000241c640c1c80003603801025500500707281100100543c1d40740d59240081a4000d08840e00b581c2d1843d20710030706503805410300c026083d01c03e0302140050b030500e803251901e1080d01000e441440104e54000c03205c041c1310060022680c201c200340040441142c0309144900c01900030510240c200c00c0390a0030b00e90590807641c095910f90392450026034540710115904031030802c0003020340d15203086110352071810115280d0014800c500c00e03031920383c2d2000020319110113444242c8030716000c10341c044820032061318102d140314600c1282030440900f9002e5080301c03618914110043c8040301101d038400341c689034155105c590751154030850a0352115007146c102c401c070101000c45081510300240d40702d0b11400a586030315074448014001242010400c4d95841c8000f48a020707188203860142c089981d4483d0003803132281c081e0f00c80d03c1744107101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 247799370 1250 247798120 247798123
    0x21e0a06050c0319050a09200102120a0c06021803190506010b03040f06020304050f030307030204090b040e03040501300504020f090402010210090f0501020a020312090c09010312030906060305010b03 87
    0x1e00520002000344108507002d01c0030b00e031640020220307200000c5d0725941e00000000074541ca07003018001d911000084001c6020014500701d50540c01d03000c41315510a01454041d65124540d900c60004110074001e60001d4207580140c09001d000c8407540f1b9016605070082480c10905a000010303401c440b00c0781a091141c144441405007410b81042c1f8990720307040e1201c84240742612401030a803a0f00000081c148031041c8480702c0301c0003590060300c0d03680c140000e00402a4115002d00c0f210f0070300c1c064810409141c640704a0005501c0f80000d541441e240800543d00a0900b603070f030082c03259040840103090312034070000c0171383c041b480304002515081c5030040c82030750480704c1c4045004c1c211070703010702008d84e030000361040319002641c0011980850a14003000c107a040350134010a598008a08c0d0b4000704d4010000d01682c51f030007a5020309540d910304031140d0301c0000ea07403001c0d00901c10200502c0440c0485100150720102810301080582031a41c0d610115022030327006544695560300c41501a150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 247800620 1250 247799370 247799381
    0x1203010612020c0d0507061808090f010c053007060f061e0b0a030603081201061724010306081504060b1e0609010201140106020d02070f03080316021e0a06 68
    0x300950850400f010800300da5501c00ba22252142400310104000c803c0041d507800007440400e40d03019821076404103103489040c64001107601403261100c2442c2203265446003000ba00207070340101c004c0142840340701002c05056040c04044d4a00d00340c8107610040c902c0741c03c0c01044c0b05441024002107040041c01c11400300c0b0800d801c521070084001034400391070740c42c04102005440f40b5002c4240da407001010150020545503100030500ca40103c0c000030640c094400c1c4c40e040307840341d4541c1803c01078511090b44050004403200c0590301d0380f840050402c800100240c0f00c15080c107060000d0b8503611102c50f81d2900a6100c0e42010b0402c140d0100004c001d41c40c012898a00402d80b840c40c0701010544254411071041800d10b4081ca0010803d003110f680300350001c200540d00a00075002075615500001d413a800317103180c8800941301e034410009910030304026841c1100e411039030150943c0c451004100c481ca002015a0045104103035100481210700106c490a200c586001001c09441e645404801c0d1217 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 247801870 1250 247800620 247800647
    0x9070c02030d05031b16060b0609151c020301060c1127090d030e0703020904020a0b0708030405010e0a02130b010903050601140102070503070e010e070c0b040605150406060e13090512030106 83
    0x405022507081a0203039050300d80411f604c4074000c20642c060201146090285070081940407400014138a0401d2aa02c024124141e0b61180040c025240200d414168030080c030625000a80310f40d507120209008a088a0ba030040042c050000751400c9000d481d11003a103c582040758402002c18020516001c00c2000000101c50178248041c0408404c00d54840100e440b000e0f0043c1700020005045540300340350303080940030400520b9101c50180c01c0194064004442c101d401d9841c017811a1900c100018501ca04190300804400d044540c190454002d051400c40d01414480c10820110015106014041c040c004250001e142050301e80002481c05400380d001c14001e41248100703204940300031105c10f0555080e604941603540316004119055000003030b0141448002e42c080c402081044e4015030f000b982a0408282a00f0443c4200001c840440c800d8a000c145019004c00c02c42c203280301281843c601c5034000052107081503e489081900d2054214038200e40000180405e0703030081e1080d160328 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 247803120 1250 247801870 247801921
    0x206031918050705010c030201060e0c040f0e01050604030807020111061815130b060d08070506010f050906031f14101509181d01090515011e030209070c02030d0503 72
    0x803600c40c1c4800383c07901001d0003240c4c1085a010401e006040c002d40140f001090305c8896030350f852901c0c14a2022a41050280c0c0c00f0343ca0080d0030003e2a5004d501000b0f05031039005140c2441d151841d0f403080510790141a04905004076031940701d40d030907414000103104403242d684010018110400c7c2909100400210030781c0101d140c014801c440d110003c1d43c0340381983c8071074070303e0f03240c0c59142c0015201c110100c0020044e400000e40c0d0820802c0120b03a06040362410003000d00100d890301d08028180c1000c075426a0168018400e81c651000590030001101124520000742c0d46040102e00c2180041194a41d104042d40401005102210502400b0400c1c03540341c1044a02e042280822000d030304085043c000f20703281c4180200c1d48841d00c0369011444203a40c000c0003109858a0559211104021004446640c0328000101031101c43e42d1003c1050440792910643d07402e42c1d00304030f0740c00b9001c0d08640c204800044903000507201000211000030064450769141c2c0307440c0032144060b4510300300040c00c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 247804370 1250 247803120 247803161
    0x1e2318030702091f030606090f0606050a0c06061a070213020906032e082506050901140403020a2301030c08070c0f0b0a02070212060c1e040302060319 66
    0x4140003200792420107074100c940050301c0d25824035803820003001c1c014030a95018856800420401194090f5003142c0c6a12402e12041c400e030f18940c1e00f182d480e8843e00c00460300800c0350040052256408181c05441058000b031604d884981c0d42c0d5410100c002c0c2c005500c40001801030943c6000e1450910f4141010800d40c640030500c0c010401d80e000142080074002070982890012284000000040c90340d08910b15419950704c290881d50348051800c1c410900e0694503002041c3c04042c6640703802d403a60b680ba064036082540b03004441401820032075210035003043c44040011f98035881c02074020300f92140f43c01880140d02087d800d0110413000201c1c1403501c0c1c01494003889400c0b0541541c804c030b540c01c00050200150500703012055402c0401421507416008000003d182030740940b00190094034076280c0d0f0007548228030b98070700c0252554101c1801c144010000180c0d4070203000084840380c404a070801342d5030b9020900540080d10700c0c0002c100e00030742045001c480d501c2514105100c002c481c901 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 247805620 1250 247804370 247804411
    0x30207051501030320011103040b0f06030a032f070609050a0609120602070201050c070e1b07080906030928020112020909041103011503050a140601080d031e23 70
    0x742d02c40403d04440005e01d40000c8103507080030b41c40700c0c3c40a00441041b982e03034a031900d005581440704541d500400703980314000c6003c0342000150070f4800da9040c1c6450b800c0c030191282c10b0421401d0300203010850f80502c00e85c010340e83c0b81441110014440c42e01e400e0403240c00c01c0104407025940740c00c02c1c03042040310301081049050b980300a03055550001001030f0340e446035000485051155500d0f0500b680304070903000030307040702c0e004040f4800c3c00c480684071810782c0b4040d46442c0c039220b5035002420203102070140c220145400c030006c6800540844c11100041c00f607000340c0080b011100515006248180c16200555030880703003441e80300c444034800f103141001c03207070014100400240002e003607501c15490000507030700c003544120030514440b02c8034802c841d03880c90010754410b030301d070340444980924074050b03044143d000481505983d000c0014003004aa9150210020b0680d070041c802d00b00c402c0016001021001d21449500d101020300300307d240e0f003142d040c2085203000980400010760001d410b501 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 247806870 1250 247805620 247805627
    0x8041e150e01030f061d09010c020c09011401091806080709092109080304230102030307020712030203040f0e0604060b030709031502040801060e040303050601140706020a120c0302070515010303 85
    0x1007500c007402c0005204201c51394500042100c0e8100750b41c60030f03900d07413400035179412045494400c10000000744402c00340b49030f040b0384401c45d1505150300150a80010300044011640462032090189051884194dc40380c144a04118200940005590b2800c003844080414080741002d441e54020034841900250395124100c8001c100a2590a14041c41d000a1500c07800441d0002c0c504142229200ca46a007078a402d60b00034004802c0f29400e009004820035400802940d10400c495000303000b0321450891064052024100201d0460004002c0030a441681da441d40000d0f0840c110085103600e01041408203c44003500140d20458041c403c01c031020744c0c801106070684e50b000c204452160106078102020740074a0700203120079400c0007808280c01462141442c07155000360340500043d00d0310f40040d64203036141141086488000c10281011603040d400400c0030b5078039031406144900034002d1000c00c070f802e0001c040300000c0c1c0018a0005000d800c00445801103d280815072065141d0340c0c015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 247808120 1250 247806870 247806887
    0x60d1d0d0f090819230d020f01061a0313030210020d0c1b050316060f06080c011e0203041505220503010f020405031e07031b0312020d080c09030a08041e15 68
    0x10420282c0c80900c5c4c00c0114403049140b5003500c900201c03201d00c912940069200c0b0b51031002c030345003980f91503c001a0b921090b800c10040f2400002c03003920f0350700c1c2c46500c460703600800d0205400350310480003c003502244600c014210460002c1300011055001c3d00010250044c07401510007024802d80d00c9000300d10084100e0b4420000102640c54540861400d000030b06590410241087d1810340000f03100c1c2800301f180b840344042641d0704c0f103c0010200904240403d281420401a4402d200a008418001c0c201c002040c071542003007030030450030451032400e2241820f2810302c440c0c01c4201c20000d60400340994829a910420298142410200840e43d14842d80404000d4041c4074aa0340c0032415091044001450f004022404040807595030101103c2d1244401c40700500311441d9201c106202042514138580255950b102588990701681c0e0b298001c580000c0e40350203203002d91000641810001c0004028450614008a500b2010b2a6001200744d020b03000e0b002101c2d00103c00650b014048 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 247809370 1250 247808120 247808123
    0x10504020102250b070501020903010c050403050c090705090303070c0512010225060e15060f04180f11040608060f0907080d08090c0a03030c020a14060d1d0d0f090819 73
    0xc40785880c010f10040d005240e00c0e03610607054940300041c580140041034008004000b020750090000d0703200280210384d64890b078840602160003810b0002c0f414500b90320015001401072820b0342c1421901c80003e4250784c030082d4100e48034002c0c0e203000c0103541070021142070f1140d204802103040c0070143d194100c4030a20b580c0004040a440f4100700d0401c5459400300300094030420032540a41454141c0032200300b003e4842da0301c583c0314030304c40303650600d09405040b01081c00c820912112000315070b10ba46d05014030b0401201d00050040b00000c1940300d611500004040b14801000c4500300907010700d244c1c0401a200503038a80105100b0301481e20005003103e8482200d1a04e202d080d91028042414150710f41c02c0a540580000070000c103040d4031a59003101103000321031030038000da601c0400b9150308020148594110005000800940d50158000c0d00310350a44005101c02070002c441517420800c0740b11250340400c040750411a01a0313072103c3e0240282c080c3c50700a1105501d106000003071042e884e0300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 247810620 1250 247809370 247809403
    0xd0201141902070f050313060806060304081606060812210f0619030204110316080f060d0f050a061e0b0102060c09010c02030601060908010e010b0a0911130b0a0908010504020102 78
    0x140c030000c200e034410182d402c4c00e4008055130f4030b070007035800e00840310320003446104c000804c0d04010803c01d103031050881e80100d511030412032421050500c000142000c03600c080d02c0381c5942d0000000c50316018041c80308000303544c00c03c01c1c8da643c5081501107500e02c400082001c03000c3c1180100910941036410700340d0440d00450315400b0913003811079140c00032103194100940140c14004aa0303000b00403800910b0041d0740040d2007003208620041c0031200c06d5011514911b5001c561000318031241042030034000254040c081d10306070070070141c60720742c5814030152088030010794404110f4011003071080c0d2070305040300411050003820f0f10007000071341d620300190a041d038185001441000d00c1e0b0081a880c1407480c0e01400b0b441456944101c003501c8004036100c4d01030356501307181890401e44418819036001c02c00040060740c42d1802e10303480c4001000c102c5508055403038200402e001c4e04001030485402040d00a108554500022400410b140500d60018155078140000d000050fa000b00704410140c08001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 247811870 1250 247810620 247810627
    0x1406040902090a0f0e0115020606091501020102070605101a0a0c03120905100e0d0905010c200604090e0127061e0c02071505030f160315080d0201141902 67
    0x2400200c29548036130030074400368200003140102c07111540c0c102c90b140341c070a21400817012016a10380c401101d5059100d03c0400c001400034111021151000506100050400b0841d41e10107003194400d0741c200141c0c0d040c079001008000503480006805001c4024071500308204288054032402d485000281840396550006641101c242d00c1820401c0d00002290020085095050020301845003100254092400601225402840100308682c4185d5543d03c50f20529111400118501d103004107210035207101c2c6180a54400010380060004550001400061240170301d08451080c0444c1224000c9485010514021000c1076420640c0107040444d086031a0966000394103d109440c40c2e507580340100103e18154001040030540765400c50740351107400151801d40d5107000c1100c42c0080d07040d0100010703051604101c81000e03010450b080202d00c091041c2810451818250003d013580d41c03184483c0c03800076509014040004480c1916500c42c1d081510395402102c0e5210284191140c001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 247813120 1250 247811870 247811887
    0x111309060513090c0b070515010e040c05030f0d050d0608070303110d020c010806040e0f01060902120108010902062a030a0c0b0a05090c0f0310110301031203020f120c12040311071406040902 83
    0xe00642484400f440c1a02e02c1540c1c444c956801c1c2b003041910140c0388242c05041c040f5503800d000031950255125400240386140305040f0031501c950220700301158040e1105d1002400300020400c030f00c00b8600ca900c80c1104150386400c00c92901d94164030b01001c550290800304100c0e60400d030300540019007071301c01181c00741403241081d20b440e205100102296290400c0000d10040070f0303025141c0e41c5015100804266654000182030711911107010327500000130001d0101141c980b188603400602c81d00c40c01130380280080040d9045420007824031001c502200001d10800280801c616030014141310100b0040c10070848803680c03400c162511034080c80e0996040e04203039908124031402c80120380010700096001d9a24201d0319003080c8000c9840403001c0002d0814140a030080c0e0b14507040207809142802d0000d4080c5408071005001c0603100c05040203914009180c040d111845239020740c403051a9681c080f1031092900c403e5a021010403081d03664421420b540305001c079000c6882c500300160f11000030303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 247814370 1250 247813120 247813123
    0x6050304030221091302070510200d140a050f01090c1101060b04030501140408180a030506090109020a140d08090102071701090203010f110d111309060513090c0b0705 73
    0x150003002c00f1100c5407031820852880b003c004000c0441d00b0b0350001810f4030319824040580c01403680050140e000200343c80c03580b40480d03000405441c0315820651202c00100700d4044a9400189050720b19a02d40b50090345007040840c0b03103500310752060010826454051344614039030806008000525860300e143c400d00c140300f80d5100e101003105038020000075079542c84296555001e407100b211954200b560a03602415403c4516104a80088100385840c0308000d0002d0203400000d00c1c25409260860f010000c1401002800c0c82400034400000d044009401040b1001009500581010700d060101c2c85440d1100011148215440202c180d25582318000503401c100a17900300504d252029102020700d200150804802c150003540200540c40d8902140e00c00d50720a48456901420100481c1100b9200c42e88001011410400fa5a003480801d04404104042607407020b00203c0d00d4103c14041490240c08001001c1c80050040104544960310952141c92621480c440710030085400e5003440310 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 247815620 1250 247814370 247814383
    0x904150503060f2d010f081c1206030605010603050906150607060203061f120b01030504020a060f090e1e0c070b0f041a0703020a0e040e07050d11060304061b030207030801060503040302 81
    0x1091441109074902515202c06040c0c00b4802d06a841d244944001030f010004291300f040d040c4034040148500100400c1946c01c1070414140d101030340d60310f14ac0000843ca43c1d21070180a40324640d804110342c20b081c0101441c0c06030160011081c2e5155034848030031f03980d4540840c5c10340d82d800000541c803642ca01002881280950004003503e010010b9419035041d406805d106101cac40815080003017520316401103084520459001350014128281480100d000307015a161103600ca00c2c02600060f110480b0011080094810200c50447d00710a50a40314010540da5442180c000c1312a0070000700791542e100d03011000d815a91418503160110b000c0c0403110b40883c1ca100710004111915040150300100258031606034800050241003200003d440e00f0b001d81d80c3d00c1914400200541030800c400c0003400c40d0070000840d56014a04884c040c6520b446028500c2107000f464005440c984921078044a000302e000c541c01094030400c4680d0000e500700039040c0c150b4401d454103548a07602c0345410784c03034400c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 247816870 1250 247815620 247815661
    0x70b0a030e010b21250303050d1e0c020d0c0206180a080303040309030605180703060c03150b1305060717030411060c0c13060b0306060a0203071401020904150503060f 73
    0x150a51040c62042141e140351a980303800c40000c403420071400403500305d2013401390343c102c0000a44803078040020901c590044c0c001034526100c0041c0c081c1e0184081e1b00d9502c5c54015401c07034240c0310070715031150540620004108000c0c5092100d090200782e0b0001e2010700c01c84c90020078504200f06407110325200d18501c40c0140c04075800716640c1c2d081c142800750800d0450701c800c607400c905000005500c0c0d2190a08400c2e114062030040c40d00a0442d45c816003c0e21040303148100305955020a4040380499010714402000303205400b9039500c2d4240141100b44005410641c0140380400040c80003d08a031460f04ac0d00041405071626078456107004036130100b00c0f01c8855440040403451010b807140104900d078102c0c204480324a06c0c0b01005005505440c064400c40003d52001e01c0021038508044005054100803841500e00d402c0f5990344a00460b030318034049401c96980803440100505081c0b0840610554103400d45401a29120009650b000020800c03144024214007050b58599040409000310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 247818120 1250 247816870 247816879
    0x50709080601232d0103020901020c1201150f0305070b03160f050904290301050c07030c051011040f050301090c0302010e0103060305010e030901080a09050a020114040e190e070b0a030e010b 83
    0x381548641d8007004d41c070f440d0324005052005480d1002580a44200e5440941c10307000303004a60700c00e42c10403581443c103401e00d007559500c1d141000b4181c409a11401c010305008050400c4240c01c60a20034034000c1640c01989081c4010020322458650721691036604050074a403111140001c140c00322840e00075078003da60020300b01a954000391011141d501c0440102880740340a0900c42030400d826604151003000c0744600420a1401003841840b00005580c020001c4540000411504804580311b02800000300700002c14240100c6084031078450090000b00e000303001d14122a22003a000610520000741484101442c80269034003d42000009640001c020008a656903190b1340e140e900c4070043c18001a0544006032500d1814801c40356003a400200030407203025142d00549050b00d284420741014103086c400007031821551808184140451414072101000b0003481c00207541030f4002c0c400041d003120005101c1000c7d07100075a0744a800601c0e0114072181c1940d000d90040c003050a080303400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 247819370 1250 247818120 247818139
    0x302070f06121a0604050f0604031202010c0f02070f14030a12030c20060105101103370f030c1103030906250e1912120305070908060123 60
    0x1140d40000c1c241e21042c86403081406800e0300c848022002e0451105102d6000c0d01c1800305004a05200203030b10051440640b4440c5420f84a0f03c41c2182c0103001010040141e44610380c0f225541e07803145001c0a0710502d40020b00d4501d040281d0b2400351303210341c05807881c0c800480d0203440c01903a0422108500640000c00c1e1390381350074002d00040c044c007809200a00418200b8400258900f1384900081509440f8070140c030151340ac0a0030088501d0484104030100441d04180e102010b0003800144582517000b080300150868828541070110000d03018221b15245000c1c400f841a83c0010807100390000300c5c9000110142007034016107440e020800020035500c00403040021a0a0028110340100d034103224051102e030480f0b81c004076038201017030700d0000500302d40100f03647e904011140c455424408000c441100f51903050250002c911403009460102610b281200c0c80740c5c06100303a507009031039440c3c50a00f007400e010026946101c10b10400c4001520900582841c1e5102442d40c080540c0081c02c6560 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 247820620 1250 247819370 247819379
    0x90f0e28020441010807050d201e13020c06040f02010513060509040b0a0f030308071713030e0105091c05030c030a02030a0905030106060e040b0a1a0705010b0301090c0b03040302070f 80
    0x7258190002e40c0700c2c44100f0400045401d2800140200072a035000300318508021440c0c1e03465200100b800c0100c290900c60650100081d69100e100e80520541c04100c0d5103826020010000707a448180c4c001c0c07444501c1008680c0d603640010074501d81c419042144e840c45d80d081d520040300c0e248203040e408101900ca40030702040007584a402015010001c9600b4071403130352004100461019907224445001c80c10080400c0000d01408045a01c07658600b0300600c1e4804040c0410b00c0624111002d2810704942c841000415401c1410020000c40a10b0102d050250800108000e4142142c1c0c0250003000da00c00c00f800c0000810866101440b904166900c50b04030b000b01950304c0d00009600b0000c9041d03500085194181481088222f841a60725440b2500b440010710008000c29890304e9013042c513258010403014081116680d4103181c81c004030b43e0320342050030300038210b8100d050b48900c241d04154119020409213907554003038651400700d01c0d6582d103661509a24161450b4406800c4c06410480001c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 247821870 1250 247820620 247820711
    0x703020c06010f061713050102070b0108100504050709021c0e0d11060c0f030c1e041a0708040302011107170607031a0918010204090f0e280204 63
    0x100e0116900d049401030390302c80c41c01c10001207450240d0000254801c4118041a080003800c2d034100300d10850f112072000d080d466503400e91340201000d4941d0f001200c01000322400800541368011050002046641096541c0301d44503c0d0702d100c4c42d4140c40c0c001c94401c080082881d0105802041403504001000b00280c000e80c0310700d0075420504c081181c040da0345800800c04641c80d445044074180042c6455102c0744400c2d0305400140060840c0c50040c0030b084680725011001ea001180345441003a1154505004107000c51708042000c8041c0100344406800110700a06580551360b09081090300c00c20250406890546154002812948a1500c99090f550045685806441140d80600810f55035480400d20300000f0a11960801f6485c070005115005522200200314246000903250541d200d00c1d500640f5554000030032042e030b4a00807581c060741d0402148041c4960200c13110b181042c086000040c105c04040b000e070056403180c01880345070031104055940101c2e82c138070403a2100003c84c07840 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 247823120 1250 247821870 247821877
    0x310030b090c06041202010e2715191406070203031602220902010f0e0108070e12030c07210f031817030d06060305060d060f0b040c02030a030f06050913030e030105070302 75
    0x51f0f000c10212200c030001d50501d1b4000c8081c01c1d4106031211100602e05600080c100401000a641e1a02c900032801a40d40d0701014200314101251a100300c1a003000789401408011411641c4204810444440140c4000c402e88410380024202003500e41d1038bd00218000c03214400847d1400b0301c62100d003079020080c0f540526446c07030003030384ca40030b2040080d40152400c0c071030101c1860210304802c00265040344200b580b95111000034288401d100c0a0310030483c0755402c9601e4072001d07604a13640600400e407030f8400d100c60342d66011604e01804e011584914611104000001d020414903071700707020070450b4000500006001e00808000d80ca180100e126803a50015004203100508203900003034400e220f4011b050088100801d503100268050b82c4610040c4030400b601f80d4100e40b205103180e5a6502e80c03080c86038401c1d4a03009155110060703080201200c3e414952051800c0ca40b000c2403184e038403070004042d03000606445401710b107085418244e405000e00100e4641c59030030a01080a0f1316407503000b0703 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 247824370 1250 247823120 247823123
    0x301090f0b060103050f06090703110307020d110303071e0302070b010303031406090603060a09020a0e0f01030c0608010819030203121807060504030f0b071701080a170310030b090c060412 82
    0x2412079a4503104011010780d84240c4201700d0711014680407990624040320b000e40c02408904000070301d5400422451016002110704d1009a00b00310030304a046c60b00704000e05461001715020b14510310308844040d1407049113210010b2800d05084a004415010348d04031640c0f150816030002203980d480c58000c000d440035581c110400a0001c0100740c043c14203000550140c580280900f010f40c0c0c0b54140140141440c102c1603920486055002450a00380c0601d070380180c80c2400d060401d903046007800d81c0e48a01e940d014408101e1141c00400000c3c03c082950b0341c902c0781c991001025282141000ca1840c000d9401313001c541000e440038010103c80b090600f0594207400815520f41c0e030f40d12202580e0b2801a444040c0c0f101551080394800500300c4c048a0b940402107041c01201544640c40260505109800440860380688118000e10221f01021410790080f480a00c0c61031030b0481c104140e000341031100a080c010403902082e0080c50500014145c1c0402402487d11980c1d40e8541d20501c00c0595030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 247825620 1250 247824370 247824383
    0x10504081c0c0905061806030a0e0f0a0308150a08030d1508071a070507030507030b07081018111b0c0f0f060711130c031a030304060c030e030a020301090f 68
    0x88041c00000035000c1e20442801c281c541d8603d00d4603003c1400b9496016110560030031000e0103008a0a64610002d94040ca02803440010000041d0f00040d1402440300d80390f12503503000320b0825000a03032240900ba84254070300b05080d030000025011a0324248150021419030101040d501e01a024903403015050380c0d00048804a101d0343c03a107210391600558083ea0344403100c180c20800070a183c2c01c0c0280f041c1c40c842c0f801c6940d0140e41c1d4039014200202a001100c01110b243c090244d901c1c1cac818a40350b049985c0041d040001440c140d80414602245c40083d0030755520f60301e92808504044080d161b059507551f00301081c000c040302e041078507054038071541d91140401010f5100c40e42005456030268a801030704203840c1c1611501c90941c0040121025a80b04024228050000c0c103d130041c80038450060f05c0214105401e071406148a400d0078070941c0c007a51050004002c841d07448000080c4080e05420904a4164200d020a08010240c500607416609050b60102044a10821801181c4c040d10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 247826870 1250 247825620 247825657
    0x30501150b1c051b040e01060306080304060804020904150e0a03020610060806010c060609021303021e0f040e420103051506011b110f010806100c05030c01050408 71
    0x201c1464a0300840c002201030714251800c2c0c20078082541e11040e004010700f81800b1030303c840c14012408541c0140c00010303244861400400c01c040d010f0254501910340c2c0000f071400d2030b04142004114101c0104082c4c030514103440400c0c10b2006004c00c0c0c101c0b102c6102c20030310420b4002484155500c40ca03400403401072154000145010b42c01140b060180c45c00b41c1d454281e59200d030f10045030b203810b44103020750703d056903600300003a9150140300801075a0b1070b603021003841d145140104800c5550081100302800078081c0e54908581e111914000071510840340080c1c50b050b40c09110b0304c1d1490240441880803404e00111404003c8508440580a814403094204c0904860209001a000c1c48000c0c0558006072180c180b104007468002c0c2d000c40107140148000d025100300189024100e041551700c10300303e05140d9501e003800c44022400e0b40d17082c00c1c0b84055040c250045100c0d8000e401004040100b0b407010070007041814412119066001c0d402400380b4146400c0c000920707400001612014404031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 247828120 1250 247826870 247826879
    0x9031b04020705060106210b030a0b072a060612050c1905060408010f06081906020304030e0928020703050418110a081e070f0f12020406090e1e18031303050115 70
    0x30701449001c840c8c0540a0300503a041d41d0f8442c00c0c030a0000d408001400701112414203408001d011503103840c01c0c0813072807901900442c180b900031502d80b60081c46044042c580740c031002c0f480000d60160100c0e003d4034010f885189544400c3c0c0c0c00402c6422440d809003000a000660354015004008031070f080d84000c22405a41341c0ca074a81d14401c120710b550081d0038103003010003c2000d0364080c55006003c1e0401002c080341e60380c000f81c2121012600b803a00d01d5561842007042c9801d810742c0050f1307510750050840c5007003c90745000d030940c0918858481c44001c01d100040e2805c5003a08a0301d61422051803140c1c50f40079840d00517000c5d003021030700044822280f013001c08040381c0c020402800b440858486032050003044d5001c07903c507412207c40300140074500d031071500450b405200030402801d40d41d4500c1010303400c040511040410240010100f4140c0089000c04558418511900107440103110350500661100f168154051a1030401c0b111118a800005120041d005142041155000d0300500350700c9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 247829370 1250 247828120 247828187
    0x30509060412150b0102060403050d2a030e060601020703080702190e0406050903090105030f0a0e100e0106140105040e040f0615180908090415030203030415090b09031b04020705060106 81
    0xc2d082c011780181d00c680702190110b805034001f0810001410008600a1a8042c5994501000d07001040c5501f0020580301c9000358144921083c203043c1d07001034242814880f00003540c900980c00040c01c03903580040e061085649110000d094001070b100d06440d4103542d140040103241c0300b1101603030400c2c14800000c40380d01000c8116041940d05031251402d42e1904492042140001440318081d55075505010380300340d1040100f500c0070600000c0c04105829045000d600752201e65010281041e0325a824041582e0080b007940c0a0310520300e07640f066655181030103600c0068080010740b80d0b40c50100080da02c2c1085003070344016034288454180c80241c041c40da280c1280e5001d00f000d42001c6007804120750b00e1411703800c24080712500100515810b912500040d007541c2c45a8441d41365038102d411100007668005107088010181404d0450501002c0300c04240c540c4902903006d090700c415910546566981c1c0e50545141642002c12540c1d01e41c4c40324009440c40040360700c100ca51001d001200e032000e42c0d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 247830620 1250 247829370 247829381
    0x102070b12040308040f1406150d120503040510020a09170604030909020c031b070501170103151e24051903112e0810030b1303050906041215 62
    0x1c140c0e40821403581e464030119002c02d8080c100301e07285140c100364440030904500c0d4005c0c0b2540c21502410740c5003040d01010000d1441c07103103294003d10989000a02148684204e6482d2031660300f400c90b07496480786056400d0040340304603444141c1c0701140b44071116520004100a07100c03824402c800e01e650007191681d603154201c0d4000e0001701d01d80310070700030b0911680181c001e864000702100d041c911155062014412021014242c0703034060002040650fa00604d0a0314841c014202034034194199120f492040480c40703265000552034940b40c05007416900302c0800d1080c1268002c03ca68036108850704a1007280b10000a00c2040e0b429009c1001c0c50481030080744020402e06e0111094510303655420703d0300080b070303010790300c8003000c2c10208500c0d00344941c2d042d1482c2510341e5203102c50841d070380107000c840024110341c8013024200414400281003407000e64000410b0304071200d000b11203240860702442940c240b590086404180000c0c90010380e1007080210f40b04d0460080d460300802c0748001241c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 247831870 1250 247830620 247830637
    0x506040317130f031101021605010507030513030c170706090c091b1b02090c3f1302120c13090201021203100801110304141c0e0102010f06090204050102070b 69
    0x2d1003540c0400030342101400c4001902c07906108124404210b002c03422a040861203054000703150769000104142803003699030004683c01d040059042c8812300789150759140f0001824840011508801c0c010758803e0860103000b541074207561007070745140940145c801e9000c00c407410030021902003048001c0303019140280c4900303600d0b5281e9180304007049074100351242281041c211403210a80140c3c40d0310002e070b845112800e242d580e480c0c00030000e181c454a60310090804414071104c03a102002020b50141c3e0070844c00300c43c0701c9519180c056100c078540c101d034140203521800c0c003003800100440114400d40981c100305c44640c2038962004480e402c0eaa03078031038002d0040e00044c1c1c0038480d800c081d8021b182c22050004c1c003089165117400b40c179401c44100002a43e80c542020040008201041c040e41d00c1e0f10b10b005001c0c0108548440a1104480000c0c04890a010188030a0b41099100b503022a040c65551403060226030f5648001d00029802802102d0050084171004a80d0719206002c1364080b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 247833120 1250 247831870 247831891
    0x1020c0604080d020c06131b15260a140c040b03010b07032006090d170106050a0c0f030c110d0506010b160f0c05010905090106050301090c05070f0b0f091b04020a1b0506040317 77
    0x121100e0000300c0340304018040c00c0124030001e002c0030ae125100b9041e210712030104000001604404030341300348040c01c402440e881811008100a1201460381021b990455803e030718202d485e000b40c0e146c241c170f40314004200f0b44108800140300380d02070310000900c1c600840d505010343d0380502d070440c0304030740c44050b00103010b880c007260100401c21940b155004140f007585c90f1401e45075981c09540c0d408080c4840c000150005075020100c5c5042c0320203500d8459003524100d40c080380d9a44036640b211f844640521030580540e00205400007122030803d4a80451540000c0b00e040b841c20524004aa4040c41d01403c4e0014154500119690402904060607143c2d01d440781e03400d503840c10b080314025020072604c020420005100c40350004198000f840e01403482020100b199180140d040135030a02c00805800240d800b105000c0342c1d00c14100c40640c15000180c42c0980d884040e080261441a20000c2c0c1048101c1103001502c203116005c180a4001c51080c3c0c2c0f05000200c2041068020100030740384001c1c01c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 247834370 1250 247833120 247833149
    0x20403080702091e040f03080105060702030c090405190c180b1e0105040b07080307030b03160b0f3606040312230309030a090801020c0604080d020c06131b 68
    0x9860005000d40c4e005403010300c56211040440c800440030b0400740c038102d601011000c811401c01d1303005550a40949015034004c1c1c00c103801600000c1c0e4907500c5280881c00780074003001080c00d0010502911801004e88904141c21400c54038124801d404240710ba03000089004108846424050103044219800103001880c48c8950700070120410314410000c506222040100007088507400003e808107502400081d9202e2603c00c60150540d0b2954400c184039030040700709074010030400c00c070340d01c1603c0260341100d031110341c8c9107480c1c80f06108105d41c486800c80b110081c0c4141c0030036000c0080001c40500c0c5012122145442400994000c5010080c401750f0070003643c080482c0304403040c0c050107441070700300b03141660b46030741c01600b0794400d8428184540000400090681d00b09034450024040c0400861424420b6a949038a400010b84000c080c08000200f0015110791034058888040c0d84200756049800d0461403183d0716503580a0840e4884041801c82203150008051002182d4854210a18 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 247835620 1250 247834370 247834373
    0x20606040b0d02100c02150307080f0906070e010203130b03040c0e06100e04020919080c01020a050c09060307080601060507110906031b0303120f0402031e070b090a15090f06030204030807 82
    0x103200344c4005080108412440700ca00035951340c1300b40710782a034062201e40d9641d0500b080c0045c2a4040103204040b40805c080900205c0301d0000f80c6640d101080c0e00e8501d50301001440100c0c04d40c4282b403a011003003040901c01182c00031020300110300991181194421640c1d031090030305440302d02282c41c4c56010103081c0d010480d050083c880b4000a4030020310051a111a10700091101c1c1c03441d22714100500b0003540d090140d07100c2000601400182400140455509a503030140e55407404200f02c0d0044c03000c1c10105081d6241040140c001c1c005800607102503603120203000303205400004050301c01311054507488000e810500d1580c2d01035803010303014140c0c1c0d210090f240c00600c540c1100242d00752004102c0780b50807a445802590080b101c030248080c0500705070040514060b90303001d04d110070724010007403a41400c07000039042c0300311290415001e171500d0040000a2144503070798040301c0501b035008002c848266004202905403000001603409094541e28110700700d00a03800003c20502e420803a140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 247836870 1250 247835620 247835629
    0x501020d020706260a1409010902090109150803030708060a150e010e0f0a06020304080607020601261e01020901140c1504060e0706050307110c0927010e0d020606040b0d02 75
    0x1454800f86400b94811000d01312000803001c00100d82c8104180e40d00d080000d0003c0070521b00c80e4201116000900c000c000a80009088a0040c824076a51a550f9000503140c820300740ca841c0c1c0200742c1001a25180c0c0b0f490071026007a0741d401c4520300e1040d8110348002c5844520702c00790107c130880c03e60390008100380314001902d0103e0b5190ba190307802103186449010680c0c0b100400c002030481c40d40a1519240740c100e50381e141040161003a002d6421100042c414030f1600b0010742d80301d0034400c10329500306d00c52100d01e50520740a003a44412500e00d03842c2030540444150000c000326007003a62000190803880100d0480d0f4000c60303040d0546600701c4004003e1184004a45540160043d000060780001c0c000206180010903800f0341d000c00c17004402c00c10242d030415600081040e00001504980248100081c2000350042c04c8505280c04045440031104442c00d4003c401d80440c402003202001d0105290350f00c890180074100140304090000364207040600a0348804600034240c0c0820043c41d90810 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 247838120 1250 247836870 247836887
    0x6120305192d03050a180f17031006080f04050d0c03050c0d020105040201170103020d2346060209060d140402040f020901021f060506040801020a090501020d020706 72
    0x2044415104801d105a070701a2400b564026000074007824410384401405848008110001203861301d0407403c0204000c408850680d0391102c585225110b076868041c10042c3c1c03110101492100102c200005044081005001d03644280c5542d9456521401c070420046000c070303030080c4245c0100700c5503103005005900c01c0c212144642012800c0850405e0304e20720381040c090100d00181e448034240030565810802c908840304c40740780c620301198115000315000e860124801041d045401d08140040d8144458604000000100352500680c02c240c4010031a10106403409200400c80180c2c0360b0901e650200301c8080729940a500c820041507260500250402c011007504024100b00c2900300c55990702ca00320b44d03070200d00d007901100c1c00d017070043c00100ca500301050303200c1c10b10401c4088416a00014400303040e07034144405224541490641c54094280b90f4807103901b00002003804600601d041d005000082041d41e03036007101668610049a4512074110703881c001d80c002080c02d1002e1072042f0ba44 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 247839370 1250 247838120 247838167
    0x204060318030215070e0325050105040303050f1e070f120306120210020a23010c09081e01020d0903030b040b0301060b0f0307021c0309030f141803070e1906120305 72
    0x4542a0365050000c40e00700308a17602503000d23560800751854211718220b64042c0c0a00800c0c40c0a609041c2507a40290040c41b8881701c9a4880301c010403000306100843c08038002140040400340d464070100d1520a1240d590303450100c8007001092050900640700b44112021600c0060b0031104091041e0280030000d01d044640b02c003180104070b01c4102196a0b02c0c0003125130740d030314003030303130000301c040d03c4602e401c5404001101080007025603082282d0400050040c00071072003402e56a001403601c0d0380482c0280300390124900703441d0401150b0401d041e016446586405016101400b500b901c041c109400c03a9468040c145048009110030700344d4030300b0440596441a42da0049030807a01040d200b00d00503114184c2c200300081d8492208004243d44444500040c5165041080c900401c9000c4900580180955040c17005102c0c540313415a0345d000c11281006010701306d00c50320582061909038020745140340004d082c075801d203000050b07a58081c070050070446400d0b544140c2404c4500e401e0800700b02c0c00045 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 247840620 1250 247839370 247839377
    0x5220204020c0c090115020f010207080d05090a060609091109130b07030222051305070203041203030204030f0602031b07020306040f1109190f0b0f100c0f06020406031803021507 78
    0x1000845a1a04e15155000e06000c803a50030b1948400708000340f40034110100380c16a13034010711004e00050381207800d5480047e050407020031290349d0685800d24000d50518050301c13050030150001044112a40007100603400b8030342d550301c0300c1110024425106019514440800c8805001d2408145d0384010b01ea0840c019140c054501058074040f022108203903900f0070690803054074200018500a039600b003c04003070321000c4c0141d26203060007030744901491180301802080400000200f601c00ea040314091540440d2800c11540a810503e0094000b110b110002000030501c0b000f01030403107802d03100d426900500500c081e6170307203a0b030307a0a40742c0b1160021244d10354540c0c05c1c04090750300c84101c24424100c95030403038a0394549001c0903059030001070340480918548130644240b61241d8400d42500310301990381103481d0100c5070f41211500c5100d40080d040310303503012409042142c3c0c1c1d00100110351071382c2d6050203281e01c0540d0b4907168807441c0d00020056444941e4441071f01c2148080b00754005200e06 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 247841726 1106 247840620 247840633
    0xa09021906360b0901050f180411070f030c110301090501090b1515360103050109020301050d060c02010f0e010e060705040810051f0603050a05220204020c 68
    0x505003483c2d0700144561a5034002e008a41408204104050761031003125480a443c0204150b04c46c85541805803d02205035641d06898010350014800400c9998598040c1e481e642a0700e821500000c1c0f20a8440b440d540a1041010a6000c0d40010510440502d400048014003c0498022030701c0700315442c5a584030110180c1b0b21a0080c82c581780d55403c0003039a0902c0e040519414240c240130702d6141c0806a4035810880c210700020b803811b0186d640c81d8008102a03010034041c103500700c00039a041401140454100030a2404540000603090030018140d10070b13509907032a0081169105c0440400808041050070780c840d003a8603100b410b007410011101e48880440e1507401e031050700e070070109851240944080c100700613004216040386071740348005805000110380c0b00d0707141032401f800520041e0340c070350b00c14030788410801d20303296205469400c2000030b41007000506150b1143c2da = true := by decide +kernel

theorem cover : BRFrame.Cov 247661870 247841726 := by
  have h0 := BRFrame.cov_init 247661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 247661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 247661870 ≤ n) (h2 : n < 247841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
