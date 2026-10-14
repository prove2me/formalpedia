-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3315
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:18:05.816975+00:00
-- url     : https://prove2.me/submissions/fe0f22ab-4d01-45f7-89ea-5c2a0e60103c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 596043165 ≤ n < 596223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 596044415 1250 596043165 596043191
    0x31d120708101406090603070e0a09031e02101509060b07060b150307030216080d09030912080d0e120c150f06010e010c020609040e0601051305010501081807050901060c050105010603 80
    0x2001303209034007494031000020660b0342c00340400b0340038104214074100c4c0c1c2e0406400020007485600400c0780480d50000100b481e502425070701031681c40c2164010100c20a40c052100060030704251022100c400e00c040c00b16210000d806100c0140a100241c2030b261000c5040800a44050311000c40c0941c00c08120300c0c100a0703245007200e501203e035040140c4d03142c40a00482c20349400c0c0f0760001c0d201c0030010401c405403289a80000103014001d170796041c4655216501c1d0151807496001c001c1040000700b0071701c03a040b07140303800103595049464207441091100c02842c3c40703503511500c0740c490b0b42d410030032500d220f00403141103680c0c01403001c3c00709000034505080003a100c1c0c101401c101e4144501c00007480110340e1a04226000c60101600030701140c619504076681d9800c00780101e81c802d94981105000c24880b9200c3c9904075a0140d54000070354690302018503400d8078000d02c0400c02d0050500101300c0ea01c981200f5402082d0a41c1c500c0691061824910b0850340107801c02010542014038000d140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 596045665 1250 596044415 596044451
    0x90b0c04030203100213030605041505010504180f0f050a03021e01020a0e011b0606090f182102030f160302012901030b06091804020102101404031d12070810 69
    0x9094513100140d0b1005030b000e101810718000e038401040142080c041000b0000550034030300c0300643c0f0500600490341c03907008100556010420004c030401c48980010041394011021704c505074042c40031004214500d40b251070a00a40b26425005a4041d07051740ca60000d126801c074444a60b540c00171070a1031003884004149488400500d0304001107070f8040703841240b80030305001c20242e0240382000130301d5031820402e000e00701603040c2c0c1141915142444021400e00c1050540141d4003641d44000091507409c0140c007180600c0f14041148010701648982c034000c00020140c0e16400d1041d03845000d123900d0001c0c03c0d03801c940410b00592007030105030802c3c128240e1411020a40908001c500e90410f0400701d10303903000717400e80703a0f46c40340899890191011444030098000d81c000e07802d5800e07050b00403186a050310b046180c180c100b403440c480003e02091195035661160000120200d00004000001a0701c40b4a862100758040d044040e081040000c10440c58a00c0c3d84c085806104030314116441c1251 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 596046915 1250 596045665 596045683
    0xc030909070c0b0c03270d0e0612012d080c210c06160b010e0417040b0304021908250f0f050d02030a1a0a150803030a0906060b070303090b0c04030203 66
    0x2581e01001082d1041440706c51140201010000801300c10040200a035035004501209804146942c1e5150741605081c1c0465009440c80d41490711180d00e41804981c174041444014100e81c0090030300f40e400d280030032000c2030040c581e0100416160480300100f11b0b0000020740c103030750601c100288883d200c0320b0108420f95101070495105495551004c0c075410050740c900e0004003a15030b208000300300c41408040280c09680a0440b4420010605040510740d1045000e500c500180900028005240290b080c42d101c103020f0f00c20224541e9134529840c548440000d6500c0900084d440c01c00302e41c41107071070510082c25024003840070240741c1801c0d81560201400f603940280c41d1514203c0941d201004501c1c1c20580c4003c0c090310030054640d09140045040e2188a400d03424029842032200400a05009880024020790718640764200c20000a0460140807203030562200d00019800544a01401131180039071004034611102e85411107070303488018080340024000303010900260b00d0010346060 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 596048165 1250 596046915 596046931
    0xa0306090c121101031d0d12060f060504230907051b030306011b06150b0d0605010903030f1b05010c0309150c0203030c03040507080703030905040b0414060f0a0504020c030909070c0b 80
    0x6013014046c2d6070348810780b8401425098034819221541761065000d50000c1020214000402500d5110004062002e025100e802c000900c280424441c110740c4500411b4840303107000d643c040b40e001010100e00b520900706c4503000811000f081d5082e0742d514203030b10801e040900e039002c4d41c51440c01c0c00001c1d084c2948281c4403180140164042010404d4035030103c810401d0b40384000590642d00d012640795503005e02c00440955040510006040d401140d40b0303401c0c0c03581600d4500d51440c0c402002c8501e03e000d0f1500c080100740f50408140450820300c160010303440c1070350300031540a0050030410000d0000c118242071040c58054950a02c59000c0240d90f04110aa00c600740e4a480314100310749804426000755849005a2030000201030b040203c2c40120f0703406541c14054003408008010032103014a40010600d4034000000d0128903140c1c003031403000000104502c84107500d410101701203810a804080c4140d00c0024a080145480c00c512503018000b031504400011581e541d0842041c2c010309210 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 596049415 1250 596048165 596048171
    0x12050d032702011101021b0f01061802070501092a0e16030203040201020a0b0f04020406080f0c060906120c03100509040302030702010302181c1709010e09040201020c0a0306090c12110103 82
    0x80110b81c820101140340c500741e00003e64845c1400300701909a00c008140025151240c1003079501c003080103006190440304001440c43d2040ba130354bc1680003a500101003103425550300c80426002030218207500640c40c0507088800058400d001c41501c511105801403a1111121010003034411900b03841820440414078000d40c4940b21880141e1606400d100024040303400c003400c11003001c130010340c003611407402201d007030291554500d039040c2c966000d1407001500ba08440d00120440c1414002000031903805401949807010076060f1003648042540d0840001900106105172507040007032100180104441481c0203090907035003c0d580c0e128484009040c181c0204208142141c1c081110410740c001410038012084003a1081c0a203c038a4142101c1d801c5000301100c1030700040b601a03403c20601a1143c1484442c14001c00030381040080c012411840717006c600700440c1e201c0c00950f200a520480002c28140000e2422540b6005203400c550f00f01c0100507021000f1660724198400e6690081c00c0c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 596050665 1250 596049415 596049491
    0x5010b1e071b03050f1005010302010c1b1521050105130b0d060203130501060e0115030905120a020307030207081504060b120105100501090b0f04180e0712050d03 71
    0x2010340740104401e0942d07074041c0498000180200810003034074207030b600c40079555105078a60041080394028080030b030009070004120000960b5001c020172104805240c0302020a41e640b40440e20780c0d02c01d48001d40014018002450941103042c07a4181c500c401c1001401350398148001b2405400940d410548840d460381e04084942e12170b106081d420a4011000790340e2840c021340c00c11031203100c4903407c4950f90301c0e2502c00111000742c080c2080c140e5151400381c031514806030b04110050300ca0714005660300d000e1001e20382c860035080c2d0010618504280c003d10340307500e0781381000b9080500c10b511505680d000074145000201040450b550301030740c0600d0004141c0100004100440000c154004080d8a0300e02400316824a048400c0200c0e04266100095213480d00003441035401032000007111084240300600c000c0042d0f0000e407011104038100010b000340c003014064540304880c0c1c80390494007011880c510520106008202c0c02c207440d03060500202244010480302c41c4890042c0481003a482110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 596051915 1250 596050665 596050673
    0xe0c0703050705070b03070813150905030c0d023403060c020f1204051005040b0901111204060906030614030c01080702030d050a020a110d0509100504090207030e030105010b1e07 78
    0x39540c8140c1c00030304891806440381c10704e41756580300f0358495010a40c90b4000548401d4a41c000c1039081d07604c1740100a1003420b00162001804c10203030126100d0106029043e4444010056a14040600e5004162802010708039254000160268880f418820f0000b113002c1603401c48000d085947c40000026429a1420200e04050030103c0140960044410142c07803c2c1c10700004c2c10a4500403070701800c9804c07840714107480750310485c82081c0e82d11380c003030000c0d000315801900241c07071060800701614941500032000c40c25a50054201c0d03800320305009014420f8941c18401e00001d4180103803803001880381a0300180e40c4000c0040d05c14100840c43c0e000501942c1b080c403d42d44c0351040d288080c405801c1030007210010b9040b641109002079403841c11a030f0322240000b1809890012510ba41e881d1001d030809000842c03030040d10900c24000104030004181216200074400a4000e0354bd518100344d0120030142559010313484040008018010385959541001d1005c420000b0701c1d101503680c50082ca0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 596053165 1250 596051915 596051917
    0xa0b0c0d1113061803051905030712021b04060503100c02030408030a0c0204050610050316090b0307021c052a070b16050105060a23040e0106090b0111070e0c070305 72
    0x2070600744400100b41042e03842c803910111420344a0380e803540f006581c0c20400d1204011560710000e801c5910115440c200342c10010b00085400c5e0044050705d117400455110150b10010002c481001130703119108031f006000c1c040ca040e002c20b030360880d001e0008d6490400080d0340c03002a0328080700825651034062408034020801c5400512200007a00d440c1c140d403c1c40500500b00c0380170107038012800d15000404500c2c0c810450060055640c903a6810764650007168100411044011000d2025040d0003113810707010600954441c0074240c0c020702400c40181c2c840c80c91b02c90291000028420b0030303c010020300c1003400d43d0380d0016001d51000d0b50048e111801c650b240c2071040c0c0c0300000c40701c0006200030140c903030710180700042c5004070000e00c200d440e80c1c0c0074000c0b0301e0201e202c0c41099080d0a1100c002d41c0707200e0380c004150114002c001096003c0c0040207942151010b03440100055650b00141076035503004542c00081c1c00810001e000190f24080011103504c0c402040d5100d0301c1c100040314020180500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 596054415 1250 596053165 596053181
    0x845040f0b1905240316030603150516020f030319060e09060403110708030d0209011215051e100f0c0f051b0607150c030f0f0516020a0b0c0d 62
    0x42550006100301440200b40d103241d4012113000c1c02809201d00030200401009241ca250381c09051460f56551040200010791121241400c0540f940d0000001c959580d09115003804103200000700ca0070050000208540f034450300c00155044803140c3e8014280200607030307a020020050032901c60702c0b9101c07110014031f410340201010031764403014480075660000e4043d104501c01e8072505007041d003a00c0b140380d0391a80c0340316500c107543c400c0048071001f242e5900030b89442c0d24107041c400d480c40054001541a55104411246003900c005810813a030302d000481c10b20078002945010603a0303071407440032482c541c60003411a0207000343c4140302070300380b071150550f2aa1960001407010b000c002ca40392068031140b5440e4441a41e0419100303c00040c035000080710702096010210400c4054500c010308060a090080b03001130503912440382d800c81d090b40c014110003640d46a000111450076924014042e00700100e810115030007400d03868001803000d1082600210b40c809421386500c12403549001078000c40d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 596055665 1250 596054415 596054419
    0x90c03230109050f0d081005040c0509030a0f0219050f090903190207050405010605030c070303051008010614192106110427020f090105160845040f0b 66
    0x1140408043c0007001c10410800184c603000c1d03501781200c20b141140d03c10015280e1846c400f20010080095140650100c0104060703410400e041940c002d001038180100307004161002e01d40b4054100441c074154190582004121240c20030160804c8003181d038030105001c078540240000f8010810302603040056a5982c2c0e080407104613803446214009448001d1442001d00480c100030001c0340550003001600d22030030b18181c2040c109809510124003518003d000c4840c08103a201d80420340503030038000d04000e8144480c1584a034600720060041800c0c0c03000400c105003c0381d4205102008400c2c82c04210141c0c41c03184011041e8031810705070010108162010b0034240c002400091000d1404076034004c82e13118803104034000911308491020303445461030015001c40d04200c02a035a60041300640b03211350030b450510540a03d181d82d810800d80c405091411501140d044492002503d42a100818901a060214540358200380080303051307409403586219030b455080c0c0039510710300341d440010000740c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 596056915 1250 596055665 596055671
    0xe1b03100908040e0c04050906011817030c1009080a0f14070606060201180507090c02030f0f09030609011e0f0e061501120212010e04050a050105101701090c032301 72
    0x20361511002c00d0703000d80b244010b400300240c00104e07462914001d90f411240043d12501541d990302c00110b5000c0b03882d02d04c01c0703800d00400303a0110b00e401104081038144030401c002940c1d207103076000d0350070319260b1b000425141190903e900b000005a15800340c0d50090040d0500d20800e40c0041c0701507071840409442521140408120301c000d20466410100448040d13400800090004000c3d03038550b00020380c00640320381d0010300708111210f0980e0001d034441901d07105490038081d07038003140040e80d4842d241e01c882c60080440c10840380c1c9814030440350031005581c02003103c184400542412510398021081d9266030300c1002011a8015400100c110700c0300c02c0039220580390a4090f0140041c07000c400c0d900040152041d0017040e0524400c5842610b816184810b841c1e181c9144401c0c006801002152180511007542d80095800d010f201c1c007841e04030030b0071100e0310304140d1b00040c0701c00d91146001071a818090314501141085143c441580e80000c98a540c1c40c0c4d099585001c260701d0304a503000a503203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 596058165 1250 596056915 596056931
    0xb033d050a0c0801150914010e130504120503070c030e1201021909140a1202010c051902010e01081e2502010203060f03010c0210020c01150b070501050a0e1b0310 71
    0x1505500545900c0c145807115052644c0303c8281d0700d8032400100d641d501103640c809060080b119501fa0300b1840e190145040741501ca0310b4404540e9180b805000d4900060300c0342c0a00041010b415840c0e921032445142c0141545040e8030000c086245c3c6940c003506000c14201810070079103807031030013110301d814442c02550360710341612401c840280c40350110313400500f2506012610140d60401908880d1005068040f03031410a08040342c2841010400c074140403032012241e0014605000381c0d270b00d032046030208034080340700c5000151845c1200c0300c10070304000340d5808010021080ca000e24401040c0c800030b0b104d040d5141e030a5650440040380f12803000051003001c8ac0c410550540085114800030f4891013030f100f05007001e15007604d602001f104007680115020b1140b4103056805408400c0ca01c0c000880d200500c0c400c02034007034010381c2280300809070005400e07042c03102c00d00485411150381d020030400c0340000e558058860003400c00308080d04442d090007440c141d500300b09503c803a000c52441080000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 596059415 1250 596058165 596058181
    0x50901110a120605040606020a14070e0405070923010909050f03040b0c0c040b0d331a011805010e060706050a1b05040f03031115040308060102010b033d05 68
    0x14282c182da0380c0303070581041400314450419028000403180c0b00c1e001031090440c15640c01500c0a9502134041040c8100100001d186110b2890301e400f9500031400341c10b42900306000001514000301c000560102c4c0c1c0201540403451440b8003074115014840b00040c8001c242c03a15600f00348466401342e64610000c500403404070a0070000717200c0c405014048683c0c3c03030309040612041d40c0c10034600b2135005004040311400700c0c25500c0c6594064529560002d1902c3c1c0b6a0040901031401101c10300c0c034540d956030041074600c03100c05d61209954007400c0209030390318800301440b4100c1c454060300e410440d00140040098840b80183c0340c1080c0d105100b403229150103d94040140b01e032100717000c40c88100c5210141c2072030059089400f510650f1000003038007411030f1001d07a81c04119480115140c4215103402052102038200203018034402e0b5260201810201c0009095400902041e40f1a410481b00d40c074030351000b024510070f042c0302d4200b8060742c1142d44004c010f4900400790141b01c55400c00080104d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 596060665 1250 596059415 596059427
    0xf0923070e0f030a120302032212080a050402030604060b0120010c0206060d030906030c050705010f0b0114120406050414060c0406020d050c060a0b03010b03160311010503040213050901110a 83
    0x705205441c2d401040300d00104040e9102c100c1070010b03040032003009004140500c00d030000c5601c844041c040d0441100d503050b02d013800f07851100341514042440344c0031588582d803000310540c02401d40b075424092404d207600066164040500010710456440c2c4001c2d40ca07900811b84d2042000700e46804011010301701c4070b214040d00c000c05203840140240b0000880c103203458620070078580d81664442645e203040020070740007080b00444083c28090b0a01507400002c109024042e100d1503455000b1440d0000d180c0003400845000d40e81021442041c080c01e42c2e00401d0080240d4001d0708a2000314480e1920b051a03c0d428205019441950050030100140c441c6404001c0040f10032550803180411840d8004880d913000b41070040d8201d4000a000c0303690201290403c840100c4018000141c0800d0712000a16151030756280d158220207552003042031022100c2c2c0405507250a0800c04e103189032690004d11040300400000e82d800e81e46d800483c89280e001d5008510f02d0513281006a0344442d858005494 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 596061915 1250 596060665 596060687
    0x30b0126041118060f010212030f090a140c0307210f1e080304051203010311130f0218010201060909051203090a0605040b0f070f021c0e04090606050a09060f092307 72
    0x1640d440031800c415948005010302408c1884107000c1c0c196180e62512a541b0040074101c0030081c8102581c0c000861601000740b0a031350725600081c00800782c45c00604d424064540d000021203000441512103030740300c0c501d22030301d01ca038045614002001d852034000c000000b000121060803442032600303001c2008200c0110b02030341c007900888203042424802c50300c00b44000d0000a001c40c104c440201600c1c1401c0c188200750003400c2001040261001d0601402c90300300942c0c068003081d014107120f2040d40c080c82054003500d2090005e01080220362151540c03407003403428020801000100007002e002c07003406000500e41c1e0040080c0601d04150a180d58a21010744000c00702030400404201141d02071070a07500c81c041ca580141422685e8241e040d008424040200c03420702404900c50b241c0c540e110701c2020400d62040c00c00154441c14a400c4c130403400300a4000c100414501501400300f45018110601222900c040100e18041600b00412464031000c2a02a4500c035410034400003079000542211 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 596063165 1250 596061915 596061919
    0x50703060e0601120c030f051f05150406210201090f0602030717160206030606090d0503030103051c1d04020405030d03090b1e181c02010606030b012604111806 70
    0x20859807580c03800c1135109030085008044c1c10448004100294540c0902d50110b0300902c10380381040340c09000b039403a040b095801151003035541c00401038081c92000021040d04000d84080190304d040a4045401844426111850350700014250046a101d1882480a40b84084030104101d946940180d50380d002080d01b01c1c0e4100803074a0003400260f040b0260358070712000c4611382e0800380c041d4080c000250b1024101d9600500d0030001c00c501600e4150344c54640a10030402540d40e9859420040c1c01d105403030000691007038820701043e401d03a40c0322b09080040c08030401c0224ac4d5080201c00180241715591007290540501c01d5200b54050301130748801405030290314841c0543d510f807030302a100c500c110140d180300000c40802080715444001c08800c0e0000240048800103c1a040a12000c5c40300d00d01040050b91203000502170300d81d0602616803028020300f000301211180781403210b00c0c0d00004001c0781d80b4035841000a0144010329100402440c00580074082c8100700403441810500220391b00740c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 596064415 1250 596063165 596063173
    0x70906050a0b0a0e09070504120f05011a01231c021c050c18040207020402030916080705180405070b0a0c0309141c0501020906131508070906120603050703060e 70
    0x9150200c0030103c0b4400c140710780d2400031582e1444200040d42c1c2010301105e0070002c081c0004038808014a1603d03803040d014030b0006200b101c184ca441420340d100d080426001d02c00482d080724441e41c00ca0b00505481d8422507901c0b081c4410007490148034011080c0303070f40040003401d0040744c00701e1483d1f0080c0302c800c02400350090100c911449403000d546c4140c415501c0808208000c3d0202045004d24040301e0300020409490300455800180990300156401c89581e00460718507483c0d40e8055120750000d0141002030310b1050700e40030014194141e14002e0801c50a02d10000030b041003400c0c09480302400303904010340d44802c0304c1c42004280c150109811004110190340102e40c05000c80a05540d80700010f10a1000a140b1351484c440d03000c0c0072004980130340d000e110220b504c4e5075000182664a83c0d20b00c0640c000c0f46070941d078010340c42d40d0590b102c09104800c403e00c040103074404083d1058a0315410040444041d0703000140c0100010762000d8602d0060100110820005400ca42c01c0e500d4070208603 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 596065665 1250 596064415 596064419
    0xc030d1d090c0a03150e1e102601020d060f061706090a0216051207060b0d02130203070c0203060a0e1c0f180b031905090a020901030f0f0203070906050a 67
    0x4401d024206a481c6039010500340a501481c0c0d1180c2c010f01030b8076614240c2101459980d03250050146401c4e101c0c12071410320707000070201c4d072480324202c2d941c06103203c954000d50514204070281094009078000207140302d804000c10b0489002d40440741d21250030082080855a0b5004c051183c4d07420f401a040046e2024040c2c0e9900440b00741c20720301450740101920034585648001400a41c4041c0e204903200d0081e07003030000030460a00050305444018295035a88400368900003085640203400c0380d00c22060540ca05d00580c0361303104800200e14007401d00507529191400c0c02d450204410000035032500c18801041a916296002805484540c000301c4842449a282007400e20010b803d401340083c0d1080c54440364107100700c807580380b9003141c02c4540150070748851040b80719900444a43c0c7c07072540640001d02c2c0c8440341e403040503885603a10b400380c440746010b80d0004a00400601c070140a003a5001c100d1001e10a0310b40c032041005a0050032688403a0750303500502d010b041e01d4072505110350401c0d000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 596066915 1250 596065665 596065669
    0x10b040c110616090f141c030509010809100f0e06060a05010c080307090f0312110303190207020f06070308070305060a0510050c0a05011d0120040e07020c030d1d 71
    0x10225845001d803000d01040d070b5030f1039120032060710ba4020450421103002d500082201101102c64090016018004001d0342c092080c0721441e03d4428501c401880d082c4c2c615004654808140c40c140642460203021a440701a60135207000340f01400300d400c56141c0040c00c0c000b20410740c0038910440900c415106130b03942e158100502c6800a2103850702060400540b5000141401700440c3e0110190500b0404252141071080e0204007a801c00c44403c00201004049290025400340b1000c20f0741c8019891072500c0e000102c00c10030050762103140c154011a07180b0171941c0b0b40c008000ca81e40301421550f1106a0780c10020b0045000f0384440c00824909408500c55080000006081d10070152060f41305482a05048030700c0d0f4000c10000c106e50007034049081c0042d000707000c0c03101c99009901a1848461031103074807c2c219a003002c019450180c400702440310052203030094504440300c2e1040c1100503030700c06000380d00f4414046001c59050041e00d24440800da0084404078601c180c69540e00520b41010301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 596068165 1250 596066915 596066927
    0x2010e0f031305040e070e040816113a050c030a0b01030b0f1b09220f1a0f040c051c0f060602010c0e0405130206030a06050f0303120105040b010c050609010b040c 71
    0x1581249800c030394014407c2d50405000650400c0c45640f0740c5207000328007501421600b50003102141d810402d0300f0141d1451910030344000d9444000f05024608038114042c80010080c05a003054032141900c1045080c0300003402800080c4402900b554031012280c0340416046209000840383c0c5000c0002180d0f41c020035000c4244108010000d44500d040708440d401c40d0307500620142a407160074200700701104942000003191020001b2801b050302d1040780741c500151484200d51855588000c210000307240c1c1c94001c40c41501d43d09881c001800000120212014032072a120309102d200300c408224141e90083d44030300a1820240700800c00c440d00c9150072800e843c50b11100d800000c615140743c01080c42c290380170640200c4580030300001c2e0000e6070f0101d403454104036161010f5a945800801403400d10455240e0021000c4014529240003420b4151300c184060050380c1c01150346100381000e0382d0049512041044d000411210700d4036182d000c0a0107401900c04081c05241410300341c0c410903000300d0f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 596069415 1250 596068165 596068181
    0x608040309120c18050601030b10080619210201180518070207080a030206090616050703030b06090a0305010e0d1b260403051c091401080702010e0f03130504 69
    0x9550740c0700c07051500030000710194030b07800181c85101d5101e60000b40c80703680c0016584030042c20000484c0500e0a0000901220400612a805981d040c071202c810310341d00c040d902ea406003089450711703404055103c68400440854000c1d5243e032640ea240c44288102000a0005940c401d90707800014641d9090010b9000d010b0788200d54000c3c42035408544a032071048140c0c0d901c0255441140e58460743e80301c0032450018201c0050f8050b802031002c4c450135240c1440101d0b880100c00c07482e0b0a102c1e1503c8401031803803040000140c02c05a50710031200c0550380c0c01c41101d50030386004003520302064903828081d000340103e8055801c540300380c4e1040240303180030b2880007a05c00b68000366200606030030b4540302010742110b610100c0ca0b41040d4041d80e80814000c2c05400074500a800500d520740d041c034807464540c0f2100484600784080042e08106421031a03154200c2c0300e1082c42c118000f5141c0e99401c0e4050b205031028440e10f405a580441411a800000381505104004201e03508685d00d1082c441125514 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 596070665 1250 596069415 596069417
    0x121606140306122514030102040803070b0a151701240909020303090405100608130c0501032408033c03041e03030204030b1501082208130602010606080403 68
    0x5000149142c83d04000703900c007521a001c1500c48002c0b481d2a582d282441411035242a51000030090011014124110300032503030a500852906091018095990158440003408201030500103491080180c00600f202c42912240c50500343c0c03a0156a00c10042880c890304440d8070f0401550786212807002d40603a601581000b00300e074141841c3d0100c0180587d9075040c0d0709403000b006506484e0301c80d842020310030700c45c01074842c061500384030005000e684040c16100607081c40c00312490124401a8007030382200d0090800044007441c1321050340030020442015401140c09110009540501000510584100b205100d80c441e00503000349030f0703909040b80d20a04000030300c4450807940b15000c00464200e0300550031140740b6001d00d0300e01008540a407d00324001fa40114040003007154100711181c0000708040c0b0f80e03003c81550b50009006d520300621200e030325440e2901c080c00054450341c1c0500c0c41900071140950f129160301640d16051494031030702006610304600010798030711075018503000d00d40c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 596071915 1250 596070665 596070667
    0x1300302061806060a0b0c0c06030a0c0e31060510030603030216030b1602030f16030e0a0509160302210103150905031e091f031a010c0b10030212160614 67
    0x6d124402911790408040607090f4850390072038110301d0740c8806c0650702c550744180001c5400d50290304001c01d02a20310f110b1600036410096544105107d0514188203201d114540745030084c12885940098030349075100f140c0002d09044206801a8150000700075a406502100d8017488030001c1141c18002521020f46542c50790b0001c250b43c4615480d0a0300c0715042c0340304032801c0c400610900f0900b507111a081c0c04a21300d007401d840b81010b400680c039540800b011620082140d10308408904030040041c5640d25090401602080341402a07040d1804440e20711035000c503002442007036840f05902800309513045100d0762a841c003501240e0181d004074560203406542040c5d044032507034219800c0044c41c0800d0390302c2401103510b2919442104030a00c4101856840d13014450344001d0100c132800942600104c202d20a00040c60f6004203044140075407102e9a00f01c66581d00c02d040001c0b203002d800080d8485016095268075240014000c0300817109680d0341100349039a00001ea54081480e1054044004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 596073165 1250 596071915 596071919
    0x1a0a05010f0302070c0b040608011401090f0303180e13050c0603060102030412080f030712050702010c0f0e0103271202010606140304020607060e012f0301300302061806060a 76
    0x40b00703402818900e80304c0d05060340d400e604c810708110b40d504590000c800055011004012a11100c11031186104080c2096440541400d604c1d4080000a00002d0140f001040c4580b03280254201c9000050001c50b46248582c28161405850018400c509685510640404000c00c0c034044017201e018110580007103140a140071160007004d1546001622900000c3c0b040021141c8118011849058143d440d00050b400086a50040f00c40190900c0304580c901040541541d400800d074180300c50039401c001400140a10040700a030005082441d50440c422400940c00c0070300748800c150803403003000c0d0001c4040f40300e61f04034202c5003d4032510380000c40b840307442c0c7c02000a000056821900240059282850540f1170400752840c40401040707030380d580d507e56070030402e05001440c4506450654074006c0b1407029004400ea020600544140c2079015907207990300c100008655401003024803005400c50102c0c20040d40b01c0400b00c03a800364408011210b1082c0000c00b145440c8110802030040400354 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 596074415 1250 596073165 596073167
    0x61d040c02120a0807080f090a14030c010603050a260409020a030207080304051c02030c0c040c0e030d03050402040f05010312080a0f0e0601172b020a060c031a0a05010f 74
    0x1000c8500c021003035028070301a2004000016009021022154550b0406800c106400426101000700751602c00e550580030f2008a04020130103152040c7c000790f080d0361140d520482e4038190310540e014140b80d5840d00344004100000801c0c1243c00c80c1c01600440051040e9030002d4070341110140d1200e400040402003407010041a5003d0000382000f898010b040c01400e9032000034540c01a2019945035000400242c409032250f81400200d018034400740d800d104008620b107136101501c81b00304c4e202e1500c0d401d240441e40d2003403011001044000301214032806101001900900f42581d041c0d0050341000d4002e50019140d008182c12240d202d41405d0342c0000030b08003103510303d401501c10140341d070700d4044e842d08142d5580a804072085000015020700d500d0b013080d04a1410643c02822280d4000103091003202104035200f00410321b0102400d9403d03c0c0c40d032000c80c04d00d0031104c0000c00b820f00e40316542004030b605500013084000070025070a4001008000c0206e18902481a42d00050050443c4035840d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 596075665 1250 596074415 596074421
    0x60807090306020c011811032104140f03120307110c06031603060312050a03181101110f1605040c0c0203060a020702150309010207210824030706090906061d04 70
    0x54500c0318000a0186d00707840c41d90f10f26172002c3c84140c50b500740d07070010408076103014404c176600070f4050a002e2165103003402804505002c3c900c00c40411110812071400640c9812116801c1e0800080c152103045050380141c85c09038009980300700c0007e40340c10000c850710000181940a0185c000c0c011400c0d9644e10500124503841024110205503c600c000400200e4240102c1815110b580700c950b1141e428080080c122206400e403401849000d035502c1e00030035808030382e01080035001c1c6404461561284140d03468101002c0085031a8403402145019030b607020320496007603440072a810702c00c000c1d80b0102152298906403000c2e41c95081080420305214465006042d0144050b00340004a5044600c0402c00d400881d5240c00c1070750000ba480c4100040b6400c1c82400520704a0301a9400301d010900403c140c00c0100780101d4580300c2059090a85621042c00560740d50040c21100800d440d090300420751031b01440752070803090a0502c007007203980c010002540c03a0229020301c0580e140b1584100005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 596076915 1250 596075665 596075677
    0x16120e0d120513152709020912030d0c0801080114010e06010903060905011d06010b040b0306180907050316080c060a0c15090c0905060108130c171606080709030602 72
    0xc0c400b04011400d02002d02d224018020686000c070050318080500f0042e140700030050080025010388207540013a190102c03035140a4850800005840e51659008210224081d082c1c1d00b20f03a01c4081546a0141455004644500f60359529404141d980707800300d500307903050282c01d922403411020050000751800d1422540c41a030514203501d2070341d580d850300700032524008415204c81e515050707a60386800c0911040368074070300344100030546580342c900300345c55501a9000301e0900c22000004200983c3d41d44100e003803c1052401d01e44907600b0204030182c1d84d0304003441928003038004da5220b20500074503000f04404440d140c0d03025240d401981002c0000070b81c000301244007404102c1c403c07400807911801006c8800080d280000070302907035504021310702e240306600080041d4141002c0100302d0340d206500c160000301c4840c0403c400440e0785000c00c1c100450717422850882c2800300e0381050003034000802c0c2055412020500c0b486503107030f900480303000d0801ca031a4000b103a00c180c81000040e4642c0e0083c10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 596078165 1250 596076915 596076917
    0x506180304050a0605030114030d020619060e0c03040201120b030a0b18030c0d17010b0a121103070c020405060d0b2701090c050111010506010e0d0302010e0316120e0d12 74
    0x1c506519140007458030340380b6410560004201100601041d4900e03c24169102d0080f40209600c0020f030070001d564550050800c404003015072580c286079003a41e0090301c06003540030403030102031804480491054000f01c400303a000070600d0715101000090f40c030407126400c0000c0c0140071180c5031038681105415024080700d900c9859034505481c18802480a4080b03c552100030305000340c6104d0f0300601c550020300a41803540040b0004000ca12001d108036034201ea414142140d0324407560390000020030340c90040c40d021000000400c811954040700601c0d40510071079003005503844072001e00030710884500008040c44800000308008070b101640a04003802000000c0341005228501f003402d444412004890740c400c444414005503811403800b003021540d800003085a8641000020080603450810501a4880500e007405042c070070b4000410131901c07441101c0e564083c03030703421001580911405846c2180203178014071000b071089075200358518009151180b046400d8940640d842c02c0e40803520 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 596079415 1250 596078165 596078167
    0xf010501111204120b07050408151315021e040e01030b060a23010807021b100302070803010b07050d02060408190306030f0510390e1903060b060705061803 68
    0x2280003084040180050300d0702d04034105413240c151420480c8000060200e0b014800140418800103800240c85001c100b084000d00300151501290002c0c01300a035200030786080c00901440440e80000d030010400030710115004080320710348907cbc86101e4010384c060380c41102810b034010000304007041c0b003042d04400002c000d45a0113950f082031699018041e043c040ba90220640e9074012981c01c40e01803a072004246c000741c02d443d0078035501102100c000c803803080d2040d085920a01040c0344268150740300140e00c001b01682e00d58440c0740803485a00210012583c2c3e03c144100466841d10119400303019a038040b02c1c0768184402ca2055003019089143d0079000c02d69900e50000200d4411011905014000d07030140075192800c11480b13040c0c82c1c048842c0400b4544400b440d001e81a4440807050360000f1a03941c041c8100562442140d1074a07a0070003050380141e40801c0e085441104100c2c0004483c85146e0070410910940709101060148100213841500802d0001d542d41c098081103035000740c409016a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 596080665 1250 596079415 596079433
    0x2040b040219020d031b02210d02120105130b0108130206071707020906011806140d1d0f0601050114131502010606020f0a05060c0d06090615080f0f01050111 69
    0x8802102d894044420042e8800c500005030303a038162107a00103950f801070485001e018418006541d500c005550252011442003001c00010000416641d42200180c070a40d03031881c20944002d003820003030044031312480345400261b409542605c10f0140c1c0301c17010307102c80626540e989000311584c400c0340d800b40d0b0860020400c5000103607000004244400003100000d03260510b40c0103002046c000105075606001c134000d030510a101001c030801c0c08442c10761902910306403c10394000454007070711900c115040c0c1400b5550800e4580c585545100030844001c41c0c0d802c042440c100c5556400030301c078507408601c101d271f41c0003a48001e00c402013028018100d038491245940d00021200300c81d0241e00c600050750344500a11283d0f80c1844400c480703e200070b00508010000380c885030785582c0d002e0240e20b140310740013752401c06025a085080107003441c0108111203951400d03046d40c3e030340d40d0340e00c100005100b40b400500103010140c0e0b194050f1410201c1403940c2d0b0300303143c019203c44180c02451000c2e44141015 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 596081915 1250 596080665 596080687
    0x105031305060c031f0e01090b0414071e030506010f030b0103180c05030d020c211606031a120703062004150206060603090604030c080c0312011701060501090302040b0402 75
    0x400d4003818243e45901d940b803030815180c1460040502c0da482150810440c108034440f042809181900c4500e000000d00d0303c000f000007170003412504102d080c0d060181d0704020495422504000c0000300c8407800040c001541e10048044032412140d171404a000b91505002491080d8495401460181000200e0501030554441c01c01800d41007103c50181156041c096400c00784546000c040140c001032541410300000604401e84c00b039056180d9003c114548c1c540c614042018103520145030100c12041a00c414000700039140100e14a45540c510703102000090421845110045c851781000e8060b80c1d042d903a49202130b10200171414040c6081615071740380100c280d00280014584000070748014025204041e0800b40c00522852050000f13000700404240040380807175001d94075203444440c103031241c0b0301440e56006202d06048184804100000c2000c5803140e41410390f070ae0102e080c4201803021280a09039900e501410340040d600c52410001824180c2001410780c0000340050f0510a01102c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 596083165 1250 596081915 596081923
    0x2070e0115031409010e071e030b0a06050603070302120f040f0201030e10020a0315080601030314090307030602160b090c0105041406040b07120314150603090a061b08130b060105031305 81
    0x113001d450f90355206008582c0c040c04003c0c000c02070a03041e100c0214440b000038000d51342c141a1202400440d20380000403442c03191a80810080c0000814841c2c070307170a111000500a4101c030000f5005403081030003013001c0186c04420b49101e558880c0840a000d510360b401103001c5c1c01407001c0304c40c4030712038154138201c192058005003202d240207940c0041e405540005501140c0d056038010489900110018404a0b0b80098103000030310080161941c1c070714403c00441c0c80d080701036201922503440460424903041125406c415014080d0f4110651622003842d4280c91b924103c0c1c07160701041080204104141c05c5030b06150108a0003801a42441e0341d03150071701820390069004689048020740048140358151280400c48000000002600c2c58188141204900b4012003d44030f1440440001c080130410000c4aa005900c40e01c01d000d50705000500d08040d0b400c4020340c50104039018006900e00c05c0100440c2040e680001045419442e00130040d5040d0703001030102d004514041c4603000c04220204 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 596084415 1250 596083165 596083171
    0x10507050903070e221b0b090f0f090a09111f021903090501112514030610270504080406030e0a0210081e040507030308060102070e01150314 62
    0x38403115598900740c0105401d004030f90308060041e403030081c14000d26502411008001108040004280c0f1480c2d040c04c0750755a03040501000c010107080320100341c282400c005810300080c1a14580c1c0300300c000074104182c0c1d9030b4824074079801030f1046001650001c140d8208440c10350107401c40c00c0140400001003241b5580701e03032a40c45254101c0981c40340703955040250b00741460380714041c45100ca25030b80d00206403942902c00c060400102d030303005a00104080c401041000d8034aa900b07103031608206400c94000d5024030820358000210300380608103003400305406115007072403c00910104d04001a00180640103c2e910300c0c1c0e0480c00c80001c0340040a481080d006500440055446520f0f0440041c140d41d222540002103800c00c0c1e807007030f0060300c07840054200d4402c507003840002991011881f020b14074045a035064128009030920050000201e480e81c00d8a00039a6a0001640d03408010790380c0710900e12a8052003c90103004102203002c0e40c90b80c089461840c40c002c64070103010948404184415 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 596085665 1250 596084415 596084417
    0x18190302061b1c0804020112111c0c02150a0f0b060d051b040e070806060d1812030513030f021504120905100f03022107180801051005010e01090503010507 68
    0x6000300c00c1d03440b401000300c2141a00110410500c3c61400d8000501d01d090140000741800303030188407080030f4119030300724161078400302c00d12644840300c4121007140103051404040c811813a02c005031041503c08a555452110600d91040305a02c41d003076480c006200c1482028030042d43c943c40498160740e44002000b003520070542c0403a260608024802c0704641441c0c0140340c001c81004104840802d041c5003541c40040d60901c0c5090b5514000800c500e0311410001181c0240fa003c048141c007a030444108880700e000710706080d0380e00d441000540484406590301d1507040242420000000e2041c610300b150702a0f51f2040e1990320344c5150000c0d80540c400d031800c5415030100a5409221548000c680c0000c090403a032030099280100350150088250300d003803100301600052010340100300145520b00000040e1071a80d40c1c1d00e80781c00c00400001d010b010749006051001e400242111050040c28040e007000725a83c0c0343c50f4940401036030061098549541404641a00041c1c6941e080c49114443c0803a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 596086915 1250 596085665 596085697
    0x308160c0e040c0603061a0c1e070311090106020c120304090612060b010c0201050910050c070815070c03050910030b04050405030c01150f36020403030e061819030206 73
    0x14545405070025a400040c10107140039407c10208420154184291000786140c40c3c1d0f80541900c105d00b010303280101c40d03144240b015808589a43c0000f491001c07240946480000040b400e030400203134280a1203200016441504080054588002103042e403907541800c991070325a81e00341a4040e524141d01c101c1c5103090000508091100c140500c01d8035030000d03e021050880c465001074100d0090000300b90050441e9140d00b41701134001e00440720301d90f01420484d81c0f159aa9461283c1c1d914aa007040d03e11600c5203804904910b0160021170900c81c0c1c1a151607082a5002080c014200b1142c14410109500e86a100d1a140c54600ca00b9001d075005502444e515110f80d0703d00b030f096450050100000c0c60702208100500ea042c46848030603101d2098200396601c09048850151140f20144a0402d0305d0070800300100502980c0140102c9110342c540c6c802c5043d884041291074001c000b10390010b030850200d0340d462403611034280b98540a580e0180c042d699181e07008160641c0121021030031440c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 596088165 1250 596086915 596086921
    0x50c190c06020c01120209040204080a080d0c050307140d18030309050c01111207060207050318030613080a031e0f05010302040b030a0c1715090a1703100308160c0e 72
    0x950003100050720450008000454010000800c244110b1109808040e40420107607015901e6804607402400400110755103600e0504000b0501d604c00708102514900d4413078211391250080c002e80b88108080d8030382030242407102ca44091301c0c2c3d00c0f032036182d4952640c4a02c8217501070b8503080c4045541d80241d80000c0c040384903180403441c1c10a849181d90500075009820426101c0015a890110301d5078014181c6800e224540038000e40680c9400901d140004501740152070b010007507482c078023241241128010b48842c09038000541100c10013819500f42040200105802504003240d8405502c084490328100759003140704850000841c56185c507115070040003907281c14000c5400302d420440c040c0510440756524481c0b15101c40c4100303901105c0000301b20419803024404401c100713001d11442140c62504d0a000303078803075078140c2044903c803a44410848099680b1000c0d0380c130400110700c14078426401c1d83c0302c021564102c3c241c0b41d5101608021100c0c0094a5000c2c0300c0b004003001c12201030142 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 596089415 1250 596088165 596088173
    0xe07020c010203030105031e0111190f0309030f0c0309030206030a0b04050618040f141606110d0918060801020a02060103030906030b0603070c080903010515040f0605060a0f050c19 79
    0x18040c14005045610a10041c4420380d008a000078640b150010240e0310321000300003003809081c054441c600201c90106d100c40e41914a141882c3d1050312560b50045401a01170042d070441d140001c019000581c954141220107010781140754a2038001e0500c1e28469940c0d1780060709035803049908101c0d803521100094030a041901a00707404c807104554a1018089100403010701200007000030f461151300f045114140701114511403005201c24042e280c001d05441d004541015a0b072054000217810034008120b0524045204a14000785907070b0185114500480303002c922603100c401c4682d05d40d85080c0050801000d100801048a1035005010290b1450501410551891744800141410208034030841c0d0b45450840e41c1c440c0b210300f821010b5a00d0740c02e08090a010b0b81c402d40b60550710b03003003e0000e400c40401c0301800742101240d00340049280070340ca5509030764680c401c0b1600103c0500200d00b41502030307003010300364039407030701d0018149044003440310310b84102282c0002e40d50540d090508140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 596090665 1250 596089415 596089423
    0xb220b04020d12230324060706020a0306031502090a141207080c03160311090a0209060a03050121150c0c020306180d030b100c021f0806040f05011a160803010e0702 72
    0x981d0f40f1504e440d0442c0b914940c034010201844016107050814084213206540da0002034400d0117030007803011911001e16500142c01884036000540380750014594160850400313000305e4007200340140c803100c8424074210348100c1c258400045950306c80001e001d210050034040200380010481d40340203103803c20242d000c0c9420706c001440349414800c03030b000b01440440e0400f02400003841c803d0303a000761265240d03140301c0000e004078641d41d076000d03400140319540c50794560007482c142e07001c1c1d44051603580360220322601c24000c1f0240080c144039a140d00f5440d241416032100c1035000e0141000003000c0081d90000e4102a800c071100003403d50742807900d82c0085800c006a404401da241801c11441440200059000f010549060100042c081108046441e40d500c40e044071071810b03000c0d500c8c01d0342041019100410455000d8056840d107880d24845c0b0780c55005090481e002154224a103040321513241200398408054000d40d0705060b0b01d020006800c503001180282680140e004403030600c02d40080c20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 596091915 1250 596090665 596090717
    0x203093012070f03020a080703030506010f2a0c03060c051e042402010e030301060e0f030703030905010503040f1a0609100f0506181c0b220b04020d12 66
    0x140c1d80300c290410000c0c1d440004445080c0d40003ca2500301c1022454202d20304498814000c14100e400f094613401c158068000c1d07405480262240701c1e84140280d0704540b450a00e10424410300d0010081483c00100126410f1030b55006504070541c040d144d07103a22080d9101142004001000040c500c40e15900440f00741c1400030b02840324600d0a454480c21480c0c86c48010b95002c5401d50a003e6842154002d52003004202c0010007a661a503956003000b0b40700c807070180126405610414840c0030301e0b1501007241c00c166941900e84035260340c2031400444941e0002081100c940117159141c00c045070302c2e403521003015004a5540384c040d01c0d0180500402030700c0074001c0d4030002000c907400e002c0740d02a250324209070740080c0c1d42d9540b200071092092088007007048186410020822100c5100e5280f0031200b0340540c010a50114107865494440da00740400400d001c04203414207035004005124200c105802c01d00003055049001010744900c04002240f0442101240102c13a809400005d40407200c03203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 596093165 1250 596091915 596092009
    0x90b070807050c06010e06010c0c17070b0c030d0c05071a0712020909060103020c160b040504050123010f0e030105100317090603040b0601020708060f0a1503050d0e01020309 76
    0x410702090420f0310341e50300c4042c0601c403130040c422400251164418000c04608581100003820110b999114041d544c80f425402c255041c0a01580030505480340380895a0911005009500d4108140d8100d001009a502c0100c10040d003000301c0c90200b91812002c24140740100900a0f9500704410042c0200240c0082980600c0c010700c085140c540e58200401d038018000c0c01d0259072038812001d40f03403c00807040002140c401144030045810507885c1702520544105071410011640c8641030100300c144507110084170076000c0c07a481e03046540318034030080d202c003102e050100c420b000e0440000c0c25200c0c12204902c00c900061403c1080c0150000b400345840c83c810900c5107000501d0000c66118407005001605c040810404228585d10030407c41c00104104019919607003050412503203600700c2603400340340b164100040f03031514410420104045961000081c0000010038109603011200b251354141540014005400c080e19060440072742e003801a261001d03442019031151040140b5411081 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 596094415 1250 596093165 596093167
    0x140703060303170712062304060f03030e0d0c0b071205040f05040b061204030206191e092109180513151b0908010513051f0f090b07080705 61
    0x403d40202c40e208081503850380549140e52008010b4410000408003078800d24a4654005480e03003a100c030300c4502441500f40240d85081400400041d0b0702e550094a240e414400000c0002034003800c00c2c04100721016241500342c21058560500101880d44610348407140007541c0740411040c4403041403c415142041070500c1d0420f00007902c0d0700100e000d024081c40d642c4100840c26514401034401e11800d40c3c2d80200c4e03038130f058500251108026030b0002c0b031004074040d2998041400c2e0040212020001200105459110030700c440985200c00043d07491241c3e040c13543c0c0c101e03034070001015640c0c0e205488180300245880300e244494215600300320b0400b07217410203210301e0507943e1600704136040e04820042700821583c15810010305c1e9114280741116880c9800300501c64110411100710b8555000821459480c948031000c072824410008006402410303a400c8400d0080101d45002c2c0505140050600140350588080f204924401c1d502040c5980c2001034950b80501180e138000c0711440d00b1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 596095665 1250 596094415 596094419
    0x140301090503030112060f050c0a1701350d0f090605130303050c19060605150304020d020105220902070b07110c0405040204110d0905071a030f0c0702060c0114070306 73
    0x400c1c2c8a0106008844040c0b00c4440080c1c10700071940c000c1080e09030030550401c51828030080c104801d601010251001c40d003012803041c00320003803054450403034581042c0c0211100031040060408101066150840340d02c0f1114644201004c100381c0d501a4940c1c0c0351407a80ca16500400340c1100101da004208001080243e038480d5071f4092002c004030307980b6042c12501c0d000c6218506081c001c5c1c1000308003080310074807882e5003030141d1900a1022901e0070b03101d03a88035507460100e40714148402c85001c0d4010070781501d81401940302d0401488003c50201f001003135011700001c42c0d4030245c40b075445041d10540215060040c0301c2a070742e10b41e801900c0d5080c040d12869410808944400c8103a0f08240301e59901d00000301951182e4000340d584a23002866140c0d50301041100074000d1090803416651803107160404038000c0040c803d1810b4050003041e151b42141c1d81c89506048000e401800480451014014078006072509405002d0341000ca80001c01c9024a01040062404008005100b090f0504200b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 596096915 1250 596095665 596095673
    0x20f07060f0e0610031709030a1202250b09280602010f06080f0d080c130305100f11221a0304170f03150a0513231006081e1014030109 59
    0x251011031001c800203030f92900c01540c0000c2c00d10180240203424451a1042042d00c1e50b40881d102c65440c001804551703364480620389014088940070ba00710107075007001a1640c52500a0149101c0905a50041c440b00c010b01c4c0c0e0440145059407007840544c0d100c42c0d20390780541081c0222b0b00a451090001c10429400e21070460780c1d850394201c010107012802003c00d008103407138021210090300301d103120304401c2d551b4605a81d89240c644107980300d503482c0900c001c249074101c0c00303245c949850310038040d410810980003444200784450400791040580220018480240d4030306c460600342d40c0e90801d0388034030f07250038500c0783c10286030042108444100300b4007018dca503071810340760404c10143d11442c0c90110500461500072440c1c001541c440c404ca00721400d80700f802d40100c0c8500d804048400c900701c0203101105440310f000c3c2d45100341348201450a02910b841000c84940c00806070024040b00400e06445100020060303815002e0480c071050b05100c010314004c0d541803c4c03a400c0d0020004c070742803600e03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 596098165 1250 596096915 596096933
    0x9020a051504090603030c050d020f03030a02090f0a0608160206161d15180d020a06050915040b091216090b0d02060c030301050a06050418020f07060f0e061003 70
    0x2034248910384520103806614000e6003030318080c3c10038510801c0556143d08025111140e040710403181c80c0b0640c840003208030310200b04c49044030310030001981952039084079000690800c80b4000c0d08002070002c0030400356140307a82070008259644940d6101c0c10407040540b51079148050344025580014207000c200c401405915818003c0c518054128a400001210000e400700041c558030080c0e10201240d4034015600a00620400c401f540c0010b40c86101441104600400086c0d400090f200041042074001c00c0100b800990041c03645c20142c0000181404680094209046940012482c0c080504100b103481c09038180c1d40c0010b0000401d2480701c2c15861a1500420b44050380302c407008005911780d0079908084680c0200324544564128040301c7c0d49800c02d1056920a0080c0d10700010224080c00480e0151020102c4110314202e00c00d2000c03005e540017481760705022108000341d90100b903d41c80344100344420b010780469410f1200c00f015192020103407149050207500d0004000240c0e00d04c07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 596099415 1250 596098165 596098169
    0xf1603030e2802060906192007050607060e0601080f010b010905060d0f0b1201050402040b12030706020c0a0804090e0c060415140c060403021c02070315020c0a06020c0706030f09020a 80
    0x10850303842440742c404900f56010705602c03941c0100d00840d2403a00e15005100006482000766214440340381c1c0c085001041148c0f241c480c03460394020700303418861030030311100404115028540200e2030000144083d8a001c0c0309a2180420707404c4051804880a000e002d070075501113003444c1c0503580508090004581d80b2a00b0152415135680d8000380600c04d1060300300084a180c01400142800349010b8624040c2c0f004131403c0744a20720340f400b030414500c5c0800441804a039050300940c1040303500d9417588001d40c02198008018031076001c00f80002441d080c0100040c00c0040360100c0ca80304210000b078036006034910424421502400244962826000c044850b46014a030007024644190403804161090881202c014001e8004010906800148981c1100d9101211130070036540b400080340c0f101c2481c000182041e100a00603008a117030354000d00900c0700150709545200d0360030b0761500c3c1281e00801082078203412030a020800c0b140c145c46000300c0303100240f00c184802200d0782e0000c0c404441c18 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 596100665 1250 596099415 596099473
    0x160801050609010905032d0f2503082a070311060a180f0f0b07020604260f160603021e03070c0b01260a0f080c030f1603030e 55
    0x302d020b0b046a840b0307130300210040c200601900c0d00722540c5600c5681104100740d692010103d507101c0d0071403c0f140056126202000000030707110700740341140300c084200d9402a5022000c401c031080440030440800050089180d11802d2600c1c4003594178030700305400b903c80541e490b5500709010030404103c1a480c602c0c00c90780111101551075001910139242085d4070029004401e550000115885250300308000541d0700d070610241c0156a2031086444601c0341c0700000390001d80030310040140903004840820a40f034803081c804004510864a1443e24051644a8401c1c0d03002d9880110800c00c01e02d200006003515140943c5000f02603a03650f03000e10000c0300d48d90150800000060394180c4640d20012100d581b00c0014a410351792250307440803001008518062881207001c0c1401706c0c2d00001082c03012640c2c0b152000710340e00501e40380c0e071544e038011189040305d6000802440c5074911000008005c00c0101200d245078003022403e0007402c88901c030280c403d0356270007111550004400b5051124114041c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 596101915 1250 596100665 596100667
    0x80405060711010216050d020c09011a070f0212150c040305072105150714040e040b0c0d0e07080705060a090b031b030c070308060406060c17070f15051608010506 71
    0x20034030718603009200f040705c8142e6003010910864200714010801c1880c0080541c200e44107901e08004000c4110b000f071082d40c4200c100d5070001c1e43c42101c85070291010034013600e6820b010b03440755000301d8500107241e0340f0b032041904040c405040b560101742006800080c0030108a00302415547d07540d948190360300516003c404010003103000e440d45441901049036008081c0d5664407408000d0f5105040c040d04c0e0400880d14940c4440c640800789000e840c121000724111100d42d48554460520f110400b078800000c01404000c10301c2c58000310b02450500c1701960000340a06850100001d0030600c5541100f032040c103003000302d4210185d000c200f002c15903034500c00c410341e2911045545400382c8140660100c51150100c100080b00d00418040d00016010340c881450300d0707690f4810030040b103a242c000c0401160f21402c801000c584174200640301141c24480d00c078a45591602c5514000641d99401c580c01e916012801030501494082d20350090415010050f030b403c080c190141c0f041c1da05010b0b1501070700b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 596103165 1250 596101915 596101937
    0x70206070f0c0f03030e061801080403030623010905040b03060615040e01030c0602010b03120f07030504030f140f01020304020a14011205071d06271807030903030605010804050607 79
    0x2000c0c0040d4264991052420310401e40d00c2d8555143c0250511055003c01d502411003c0c0d0f0f8280002180c0b00941d2440c031904401d00003030015269041e028005074101070342c581c0b021940603665150b945601110750071000d03012a411000400000c07440c2c00c42c07800340f42001000749141d100042d5643d04004100d8000303414440134100c40c4598007803540a00060310288000000740b040c0c0c6032800e42582e00341d90091007603010b40320a16603220307240703c060300c04054200005180d4509100c0540202d5100385040d910f00340e50b82d100d44c012840c5e4810140e40300c04c802508032035030310002c010503000310000000950452070581c00084030807445101d007002507082c0200c0000144e2050390700e0702c2c543d02000d000700802c0c20306800c002c08100e034488286c001d180c519030842c5414a401015111807400c030030f20031800c1208641c3c4200c04201c40354807054004000140310300183c0c448a00707840c8940220354000640050500340182920007030350180d4180f00500701803102089002c81c00c4d591019107800c1c40200d00e1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 596104415 1250 596103165 596103173
    0x30a0504020d0611070b010b0705070603050603010e0109080903300307120903182304021b0601060206061e0108073b09090712060b0d0b0a0b1e0607020607 68
    0x20b900c20041246241007240d82c003d54401014041d1103014450000290303885102c910301520034800040c140c2e030f204c0320003044050302c20f4100c00e50249003c2c00104403603940b807100c00d00b03403074005c5011501d6800c08116130b1240d0070b04020740012200884814003040442000000706c7e40c00c6200545041900040000c00030ba000e201c0c0700070807900e0071a080140708114103000b003c40c03000f00c0750003101d0103000030f00042c500504141c4142c2550448039510340a03082d50200070080d4400b00320482d070606100303008004024240159802010710707801a0503070740703422000c20160540b142503061141d4007105108241340da00c581c00650241090801c16a40d101c046507001c0b1546c52020124178a0901c02c602600c8001e1050000c00c40740025220103a0544a40c05507544494850240c118254803048032a008a680390704a821b00e0800070b13084004140c020b480f0305104070070840d1004c0020791110055101810304200d11841c500c080c50203111019181e8001540c24440e07074402030301c03840010444074140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 596105665 1250 596104415 596104429
    0x1d01150305060d0305073003140915090f0703080406031506090b03060d05030c01060608061c08031801060b07021e061b0c120d020601080106030503030106200105090714030111030a050402 82
    0x100d000b0507c17000d481d5800707200d0703145914600520300001c0c00c241454850902c052980340c0036402a901a042d0704c0719410340114070742801081c0302030714410384440d90322000c2c041c400302001d540540303100c3e0f0343e65082c810090281c0341800c880304074107a240f0100304286640550328600341e803015440c080d80d0703840f450001580003400c1940074025000c0040d100544440550240084801d80e4488084171360b900804c21484035019803003500b000a54251f0031000031801001568491071484440f41c4980e0200d41c580c1c00c503692a00300e40039030900041c003031041d45000f904000e141c139950030038401d40f0041d0001080081c050305030b41c031041c110050700d035200c62075083c4114291b00c00040c120803110b12110642e5a503425000702100d004d802850000b20ba150418040d4a086d00d4002e1700540c070303503440c1041c100d5400240d00c981c0b43c902c10166a06a84582c2c0070b0040c00d01914440c0700802049081c010403840521041191900ca81c4c03424500800d42804102681d5100c5a442c4c40028659264004102c0d9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 596106915 1250 596105665 596105693
    0xb030f07180b0306010f0e06070807050a1b1d1e0c0f16060e0a050721140a02120d02060c1b1917250c1d01150305060d030507 55
    0x2140c510580101c0c882001401444c881c00090340c2d42c00c0914001d203c15039001850203c0141c01c24400c00522011406180003840d00c60710940072202d0381040340e2260944018289864070712038601c4001000450100740c024102e21500e0810080c0394104401d84d01e064040118a160b40590b034100000c909810340340a56400c50b06610496a030307049800c060010301c0b01035080460304585407002201c09105c0024201c440994408000c0079400c0c14048200c00715940111803a5905120f5495600082e1010f400040c54420b5480101035a4841c0d2041219041003d140c112544d40808198201c945d800200b82d03801034650802c1070f64484100d010a0714070b101c2031001009501c80e02d240210880170304034040e001a40950305500145601c95000c1101d8401c200b0008044207a140002174850300309000340c601c0b40c4c484d04e10381c4840d40d41da02c1c0c0004040342d84a0300c0c002d00300040004008840555070110103030041c030700d4200f00a150440c009510f0f15800d400103000c100c0085030180800003e2801150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 596108165 1250 596106915 596106947
    0x15050304030e03030418141803031b070c091e0510030201120f020f1b011a0105030604090210020115090c0203072406032a0b250206070308060909070b030f07 69
    0x101411030a5600041c200400d4540c7d900a00e00c000915140142098a80a40b051202451858a034840c1c4200700421514414442c80c6041100301c0001d070b0824002070007808884001708141e01e4002c064840d400c51603210231926410041040304400c07020418905903542402c100321842c900c9641b020042219440e80715a40f480000c1074080d2014200191410072003440360410742d1328060b401603007a20140310101c044100d040c03051030300c07545c050780c047c56101002510000342410305400040510b40d400d111500543d6640700b06030b0a20f01162003620140003070381014420b2034a4644025500e00c51040e01038511407140415443c84003c80b25204652110b0110500481340c5a003480c0300c00d0b00c1c9c00200c000012103c01d80071010850f1810308a0104c4d01404416418001d900e10b21401c1d1030b200b6203864880144007445400183e4800c1301821515000e80d803040003510f0520f00340843d441000d88120000e5208000403c560080c074021260700c045464194081901c40c44000e44014182000e00b203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 596109415 1250 596108165 596108189
    0xc0c170c01090503031003120f0905121009030315170a020d030c06420308220f0302040506060f0d0213170f060703110412020a0b0c070f15050304030e030304 69
    0x109000e0712000c0b50071b059a01601e4078078646031008800790b486020003580e840c00b040c41c03c03004005500c2c1c00e82440082c1e40145041d1074404292008038400c0320b1502c441100441d681d94800d01c650300c5003411040280090607111340405d0400c01c0c08075a46c0303544141c001d12070a900440a03041600c01c8001061065000e0700500603081100030542e106036001c5000c2e0101c1003451038003c5100c0002c403c10b40303c81082030300807040905585403034000f0b03840600214500d1016405070000d02455600c500b004151307441c03100100e14250b204000c281c07900900200d1180742d082c444a1001ca44844c1143c21010700d540f40103035107804101810070301ca241e41d80019030070052105841c80b020000704920300e2207003e0000351002981c0c1d420098040b41c2c0021040840410144000d04c0310300b81c040c5401e6140340c00102405000d82c1d40e14114010381d4001d4500d8646a0424141003010603144034240300500000c9040c07108084c03014200800d031f4040100080c0400c2004044207096440500455018200e42d403940 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 596110665 1250 596109415 596109421
    0x4091a010311090c070b040b07090b04120204110309070b0c01140a091a0709090e010b1207090e03120c1b01021605070f3f03030e010c0c170c0109050303 67
    0x1081020182e50329005006000000703144a030f48008039041c59a10222012071600c450301d4080c0034880c010140c8051140702180829a0300c00c82001d40010411100c4c1615604402c2c0305000549005c003068040460b028024040d40000c045644002d0340e565409464881002d40e03003003405070442e1000c050001003424103020228507070b034102d00291030044c2c11040304c1c440000b41588500004540d03050010702d00c0c4a060200b111503420541480c035407a40045200708100c80094036180316080c004603254000e00303040058840758014018050003820146003801c4c80946442200d640003401c1c02c07005c240010f000030fa51005103c0081c03090300f041c0021900c4081d4120000c004040503d425140381c0705070f56000480d162604040070948450075558480e0325403280e800710740843e00515961500345003a80800150315801d02080402c0d020f9500420400300c5407501900b12001100d03840100f281941c480c002041f05008084e03400c3c160021919544c2e161511514018009070f28010150b000c00018 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 596111915 1250 596110665 596110673
    0xd02070513180f061b08190204030b0106020d080a05010e0601030b060d050c18040209030c1c05060717090a440a0306050d0f02090606070209070807020c0d050c04091a0103 75
    0x1a2203d4203115040401c08810045421403280c1c00800c5c0c0c160004400380001010011000107891112082c01303070250402c3d840b03070b5821203100d40981000c80140c0c01048131200d40341d4051a0240c11078008001042503504155100d5845e00005101d541499124400120161100c0c41141c050880c80a010005420b0800410280b84e121003071b400001c4510b02040480c5123007610883c2e6041c0f000900912401c80300c10140402801d0f41166000169100245000465014411288200b41950f100b8040541240d09951462000750001209a1110741c1380000030f8040e00548503182141200c55441c4c0300483c0581d00070200781c40b00c4860140031250505144801d01d00500344100090301e081c00026102e400b03004c4903091a410103400078001e20340c81c1000d41065444c03250040c1c030182c43c0610f415096008a0120003003915000d000450503c10048499414800181000740458202488428a4468a64401e2030b5046584550364403e526010010380241025140e45521a14070407036a482c14 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 596113165 1250 596111915 596111933
    0x120d09080d030e100e030f0a030203060a0e070c140c10022103220302011d0c010206150a06030b0d051504031803081b0c09010f080f0d0207051318 64
    0x20441000c0e01c542980d029185010b402420510041c440003020500c0004014801914400721a90180e020030080c0700c0c3d81745861300c0209003900031500e0150740c03410214180641a800c40d800849900141001c1c000c0ca55800a51000903039080607225000d211364021560074075100011103a4410901142905000c0c0c001c0380441010146075030103902081d09003000180c1e80300c100c0f9101d40c9200c0e1007403060f91001d44c0000c080b142074000e01c00000c0900750201408031000701480d5560041e4448000c1c03c1030741d070b410000035502c4032200700d541440c01c2000c1e0128032038420501a00d03080c540c50b0145032005850341c082440e0b405070010129403108107006441c0c2d07092031003030706c05a002071074660700382c0c82280e4428100011240c4c170411360fa02c0c0402c202808401320922880e02c48550044801001103965403055140c0600028032030391034042e00d0042d0061800c2e440d50021002604130804c00007465402080d040110b40082e6040a510381c03001c0300d010002d0520901541c170f0440d40b5503204080c450206 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 596114415 1250 596113165 596113169
    0x30403030e1b040f050702071802071b09051b180103140c0403140a02060f0a0513170709110304020f01090b0c06060a090b090103030e060f04080f06060108011211120d09 74
    0x288041007101c840c5020b29045c0c81e8120341507000341e0f008603003c00c9885050907042c104071226020060603c5940c0d502c1c03041c1580c0c1001d00c14a04040c1c070b00c0500a80c6158480c942e00311000c289880d103e4007200102e5070395406402982c1c00c00d0382c085840340e0003c0e40282c0110101c81542011140d0368580344044d0042a00680026a003c00c11807a8044660f000011005450380c4c0091000d800c0ca00c001002070643e500c80c00b450340400409000b1030a001c082c0c8103900014110940041c01c65582e944071141c500943e5034403140b0300070700740503e118035104000100c3c0d400c00d030165040c0c11418110001070310820702603071206954a0002a184520400201c0d10501405007114071104550352050748601b0345a0120b115507001001c0b0004100180c05016080383d0118003030501070070b120550651500c80c1d001a030042d5107942200c1c2100690480910540c0c1d4000f900b401c0c00702003541070500e000c034900b5061000828280040d512052a41d5410094007110500360044402044070040d008081c07480318 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 596115665 1250 596114415 596114419
    0x3050f01050f060a0e0a020304111003060503060601050708190c05030c0a0210090602060a0c030b150918011203050307052701120608030a05070f060507050a180e0408030403030e1b 79
    0x2d004114540707052410701088410103952008192540c041d00310080d03002400c1210003191b030030102182902c44072001040e0130515100000d42c240742100381800d111005140c181040307400c000ca140010402c1c003d803040b15004103000700310803d05000035100c3c0d0542042c040d04612002c100c01503032034000224a0201482940c8a10744441612401d6602c00d0030780c0120b1000d41c20000c0000c80b4280f003940a0403030b0b640d4070701c2c1c081a29204036021503641c0711400c400c03901041000803110341c5410300085c01000c85024141403446503241600071501c200041c0c10040800000101084140d40304405a03000c018505446d010500300741115501000724404c001c40c04169100341d030a0405031144a50004c5410340303005103241081c1c90000302c07842d5001002c02c03a10710714603159103c0454818400ca5214880640307426680e800101d030041c010340f848984400f0740020a00301403000b03501d22042c2d650007550103c8c03070a0f125246c0749026005048203500140d600d02c07070448229224084540c8240f4034000c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 596116915 1250 596115665 596115691
    0x140a150605150d05040f0c06090e0112021f030b0a0f03020405151f11030301060306050a0f1a07030c020d050105010515040e0c0703090815071710050103110403050f0105 74
    0x148200b40300d0800400316a200004400b400460100c000c50f0300700750341c8148140c030f4441401480365241d1203045c4071900882d0001c1c0c1c0b8000d050040c8160300d402d0724090310f41c107014241d03003940c2130303002030300700e8100440303c414001c1122000c7c07045900940141490380402000c81085a44890040040c1181d41c4400d900c02d44c04e20021031a15060000c0006034070388090600b210b41110a88401560026100f5540420000c0311307a285501c070041c030203035000c1c192503034012800d2460082001f811803a1500070401c01038040ca0100202e281c04901c11400c0c020401172540c4440c1c180c24140c50164160754040e42008403c40e12a0406c1419840356050710401c0720142480c841c481f01c40503041c0918065000080602d178003140400c40c001c0c0140c00309521038688540d100e903c8980440c1044000c0c2206008920a0000d10101a82111482c0ca58140031031180c0c846103007034a4429800080d0384111818103036102d4020041071100030840c2e02558008003140d858aa403200024001c2404440038410114 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 596118165 1250 596116915 596116919
    0x260414042423030f061803120a0f090f0b010602010629180303070b071209051b040e070609140909060103120201020d09030816030216030c140a1506 65
    0x200c216501c0a80d40c1d203003014205414104001c07070041ca0395100541e0760303440d4500c0101c00960b0b4200400d401034050349003d0f05440c02c024045400c200405654600f064105201142c1ca8a6a110807a507100c9008140410314041d40000070703008207102803000d05842e180b41400c400388184880903504848155000704203d41c1d07506d06c44101e0300b4105a2209405d2130a11810b80d0104111018050702c2c14950106040059840000b03451544205400c03514081d40d001040b00641e0090180742010302d4001051207800c40d01d680c0c06445004503001c2d400c00350b560708400c07a00703600c880e40b100fa403c0e00208115182e4580350600900694410301c00c880301c0900d85041060903003880c1c1d55242c0100c290000400c2141d081d9614110582c1e15040c2003001c6640c28000786800c1d0040d07008682d2214040d0300c404409082c618843c084001809003c1c0717042c54010816140c90041c25654194101e800d880c0c6408030812901d04451070540301003001000313100d44a20b180610025000c00146459242000c1010f20303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 596119415 1250 596118165 596118191
    0x8070b0708090703020f0f092503020703080129032403030909070516051009030806010c050d14040e0916170d050d0b0904060203100e04020d26041404 66
    0x24000710b401e03010036044000100010309054a409500c404000e18040030100e140c4080f52101004942c0303084940c1840401c034020300f0b07010048441251551409502d000c2890300e02414850040c460001e42082e013400d0318906400b020008006070340b8019010f42d583c10800040702c840200728018000f002000134002c24245000000c841c0124009800038034070f560382407410f960302e0700600b454600e040050011040003600501210049014040c2c1c000b5841816060050600200070065818005041c01f240081075001681c0a865129840c0840907151040302004141c01243c2c4020b5000c4040b00c00e10a00e5240800c0b040c1a141607412401101680c07441121440d10070007814180c590041c61804d023140e4406c3c0003c0190702408403000c01d03e041c0d014081170b400042150207958055011003031241249800715500018a450161103085041903000030f60104010309000304210314003400785090b1440d0884044100711030004990321266203a804480b00403a03c1040c81c4203501d0485c2c0d1700d41ca0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 596120665 1250 596119415 596119427
    0x403050a020f0613140f0f0102190305060a18021c09050d052104020d0f0b0f1503072d0605071b061d011e0512010b04030209240d08070b07 61
    0xd41869010720a0105445e1108400e1426010154145001d410754002840400b0015610f1100128000580d00c98140b807851903100512291182018204010300c50716607250744200050380d4440095074506880140020000d12a00207600040880701d00d8052800c9596400350745650701840a6800c1d440900e10125158032405500214400176031408101441229191a078014405010300080d4031042d00d07881d071803d031007100c1111114840010005c2e07a0000765400398208602c11442a03081c800080065124140c80c028411100d010b110700040880d40c00708036111000340d49408503030440c0c6403407004010742d00030942a64041c007500b00322640185841d0b40d40044030020390315000c0c020b0b9810718902da888121000343c0e040042c2d9801102c10590305c0c5107050702c070a82d02d80705c181c0e65610040c080c440110050303000e00c0140d0310030301042002d0b803250305200d9442402c0e001121383c001040da003c1d1342800c140303c401940201c481d10303418041010107001170004c54000d80c14808030381d480107021584 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 596121915 1250 596120665 596120671
    0xc07030503150a0e010b090f2b11040c0c030f05031029040f050307080601030b06130e2e0516180801020a0306031b0e011202030a0203060403050a020f06 67
    0x80c410000181c0024050b01598003514000300411111552000c8070030003040700b0380200812410001d15002207241140c11b07215020415204207011880d00c0d0384602202d074034041c518000e5042350208a040140c0304441085a0740d00600c02c000400d07000d1b40051200007407240840216298000281806028005591040c6e14900040d00e03894245004421801c0000303409800000b81e20701c003001d07030b105444003500160100001441c94585400d040500c0d08040e603100c508a608400018400b1504241141d54884010350742e1482400c804208500200b184240c107000700c1c020090107208a4499110303410312081c03c0c080d21980d0012440480c5c2c00c80780c0a48101c4049100d100420050030700404c501001c144011448100142d5180500c9017079030300406566000030794404c8240104a0041980e15841c54115407801c03405040c209804002c01d41070091110450b080740300c0d0800c5640800c1003940d800c0d4046c00b030b140389003864600a400380e04906510005070140034440d5085140004050388 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 596123165 1250 596121915 596121917
    0xc02060a020309420712030507020c01080f071b1205091e0d02090a0204050a0f0f150e31060311010318020f01020f1e06060402040b0a030b0109170f060c0703 69
    0x4503d03c100a201c2c24104c400e00700d60344805405004440102c1c0d0b02c40d4036001d8084054a020aa9103000840241020744011449041c46078400611890010304002954411003904202c002006807150380032010402d14401444a00492004201107521030054006500c0036a0140c030200d070350481010005044d110350607004882c03190260090b00d80302180e541c200385000c10040c0340c41c0e12203012816a04003508810311091401004102c294065080301001700741c10007458802d107490190060074036500310b040c14800c0d55054a00c2d5920407000c810096406995044000f1004010752540c01601e018801564810309009010002c0d50280c050000f503070200380c0300d00c4e0b4050941d600700300d01049000500c604503ca07001c840b118200302048038080002c14085800317600fa0b00c0d098080d203070081c01403619005500601c01044080024030540c2c0c10038005050100d020429030004030307603100d42c0d0b030320070480d07441d81108541e4285c9000c55501c0401e00d6240c2507031b0180da60000d461703481e0311414000134 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 596124415 1250 596123165 596123239
    0xe0a1b110c010c0809040903080f07030501030506070503060a0e09010915020c0d03092d0605060319021e0301111809010b1b030903010f020a03050f16030c0c02060a020309 75
    0x1e640c0d03104101580406201d402104c0c02c2c4440300f00410b003180c1c0c1095044012400780424040311a41f11100c09031b0101c140c0c0b80c10700c080d40c11690f84a0b1a0384021308603d00b80078010000c40c20755601c407241880a05a540c21b40340c228900340074038a02074000c0150943d5100602e43c102c40080d003280c022240d6400c2c50b8070050030b1f20790305ca40040300180200401074802c200260083d00d00940006920000d003401d03182000a401050700f854012680e018256612986c050050904040680301151007444d804868550400e05003d521904503c50368075455819403a02900c0300050010a0141012402d03041450704048400420b2001280c0c0070b006803806110240006120050311000b8520754011010503203081c115001c011070b007528403aa9a0983c0560046460102d0720362601c035203a03010301090b1951038a0b0070700180c4000030048184842e02016100c0941051890107206100c0364154003500c901d03501c0700d680400a40b40c1d041400d00902c1184140407280d4000d00141403281d407060008650 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 596125665 1250 596124415 596124433
    0x11040c02070b070c0306050a05060a24050c160b190e060403021005070501110414040209130e07030b0117010506010203070302030d0203130b0411040501050d030903020d0201090e0a1b11 81
    0x4002d40d0042c02e0110784000c0c01c03460200000e1014000c10307001c1e81148c07070081007500b800000c01480740c210307411112504a219541c1d40703040b03202005942011503141000ac0c0d42e481228801400d082503e402c51901c5030380d007017002840040c0d02008005010075401e0200104044c45d40441c2c0e20b6010008095021406110501c09458030520f0005555443d041030352912009a940d6170039500003003461000102c01140402c514403051660303003802501106d00310710f4148504005481d440720f0401c6996500d582c0da2610305c0340002000310001543e002038220b8559030b543c01c811950890840501034035542010007040165000006a641e940d615402450810051016940094100400b04070070303502f03030850b014041a86501c04600482c0580ca00c44039410030344e400d002c20341e0b2042e0b11441c082c840005489010aa2102d080c00c2500d604490700205e1560500040f0354221107038000c074040e0300c0d81006202161f03d107942701203062000d00c14480310301e11907030501307813914004184840040e030884505 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 596126915 1250 596125665 596125679
    0x1140d0b0f0903070c060801090b04090b0a050a1811190f1509050d050c0f0a26100221090c060a03021b07090204030b0f0105060909070c0b0a0911040c0207 68
    0x60030781c00ba401d20100e0381440c01d82d84410135464210351005011030903040040c01240c100b40141048102e0a9505100461050b5a4504c002c40000c0406180680e20008070303050180541229180030f0b0b0342154035200c0040c5080c1511940c105032481c903c01c0e0100d201804070300c3d403403200e110b08036032584603809c0796145050140340f8090080003068082001d41c040c00f00d02d03590360501c0e04941034000e40003040c00b14540d1003881180c1440210345032007900341550412440f004541c02244120440c1c072800b00801d21045007901d0600221001c81c3d6807400454140700030b0380080b44c1c030114011600740b040020348801100d6526460340910550300030000704103603403c1034040d4000344588400d5185104040051240560400c0d4440d004a5021500080c0400074410082c419036000403a8030784034005540350038002041d900c2a0b01045008001d2000010700290051701031036445500803080001e280380c4a41800014182d454044800c022000082c000d1814a446044012501f07134009180b407a0400d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 596128165 1250 596126915 596126941
    0x270a05010f0302011b050111030106030c02070f140319060e06010603060e0f06030f0f01020a2007140d080403050705011407030c03200715030e03070f020d210801140d0b 74
    0x130301c41601c40c045c509400000c1c400d1040a600c0000b03c884103480794144040102590400344e1000d085600049092140d824500c07041c1c400c55040300d02080c074426080000c40d00303181d0b1852036411301254001c0c0303000600c00390341c02140c0c412141c030059542130780e200d0a00f907084407094025165180c41050020300160038001500c2c0d0032030380080450302584440d501c043c0c0b600c40c2104001300242d401164003014076401c0240c5030310300d120011003d4031448926040340e07514280ca10810003018400902590583c070381a00074902d1541040185541d181c6904100307503960864400e01d8006020014110a02c000ca5004d03282c131158035545200c0030224580381100c4c0d00030514070b15280c002d02c407080760a18072000c01480000700f0045440905400250502600301c2c0d00b076421084c19504200070103030004106070142c1d40390b40d0381150340205041441c10400c13102004200da070380041d440050703015100da0b00800118100c60310b2080b00300e007411600381400b1040c01d00403001404a8210004241d100352108 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 596129415 1250 596128165 596128187
    0x3111c02010503101203120c030905030702090a02190306051005030103030c0b1510030914070501050301090507140705160b0c0d0c051005040309060e0102151302010e270a05010f030201 81
    0x40c10020000e8031002d0011614803d80412000f103203811010030030b082d047c2e0092001c10800b40c1420400807241e0707140e0984a10450900900c2181ca0b00300040d4440c41c0c6505a4810820660701c40c409004c1081c0c014005203064020f030b521510b00c182c1003d9105103e41c00303e0381078a038507507152000d142180d82c0d640901c0c4405405032904029071850407030030f80c075075108072140f40516a90104400c0503500700b81c410f40620403451041600303c1c800510869030813800b201c0c1181c600b0040040d1503541c2c528202c1e000c1400803445034145400040c0f5a00740440010070342c1c901c480315410180a6039481039650585d03c00d115208400e40c000c3c0382d48268203401440e011401901801c241c80302030304460300d10b20031204129411130200c0c1413540b0500169074401c600024403a001c0c0010040e0310228010380300c0407140141a00c000c1e155508852007103911584009009900240000ca820502250710384140f43c40700c401c201e01032840100088441c4494000e00707041740da125500444050940d0011200390340c1744 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 596130665 1250 596129415 596129431
    0x1b0204060510050706050c04080606010c050a050304060503041406012d170f0f030c19020d060f2013090902150f09130b09150a030503030903030103111c02010503 71
    0x2400009400c2d1100c2481d010011030750750741e03156960b00304d16006045075800b41200c24254028442407040900001e00c1ca904040242400580310a00e413520310300e407040c05039000305540004100060301ca604a00a50302581c403421460f154003c854021a03540c010910915515140c440c80c078100098042694111400d5440524900c4948825042074401250022410260f0015048400d584014000d0140400404002c4d5260814103040b0720395178840800264103521585c4410b90865594100c0c1850f003544c440018014208101404001440398040c9042c1413203412500ca1482015601200c409880300915001c016042c44600d04c014101d01008a030000c2c2c00105403401180d01f24081d0401c8005904469a283c9681042c800005007107681c07850342c20b00f0311900c06002d54407800200d90204880f00451450701c11400019032131815a4000f6056000010906c03500310004401181600d000307000529401c000300d0700340003c3d01080c016802d6840751001003c1c2c010340c8120f000395005402 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 596131915 1250 596130665 596130671
    0x5031f050a0e0a050a120c03210b0907090f0501020a0f1704030818010e0901030812091f061703030f010b1809070e010305180d030504060f1b0207151b0204 68
    0x44009858945405544113450a80c0308a4824003006051420b82d40b1501051404604102140d5030145c66808a9600c0c0d040b02d104506171040210038590040301f4440e8018025000c90070119005080d070f900c18040c104c9824100c0d000400d147d40005040c0c030641d603000c0f00e0951182041d841f51032401151906a5048040802002000c592a000032301404184040500f801100d0440007518805a120200d401080404010400302d03c042c415150710900020180c8031503590380c407000d402c00070084ac00c0448480c41e02c0101c074540c581607200c41c0c10b0303400820040d50340300c0e0402c0310280e03603010849124111401020045c0320104060303016141310140ba01103400d5094030440080c00f20882100d603100050b80b940180c03a00b83d030f1705010f020b40145400c650b0b210345a0515040ca82c4440c2001c0c1c0c000b00341921781c0042002c000e800d030320131010086a21802c002c184c44941d2010f0400d480f8040e2400107224000012412030b11540d85591800400d4580d40307032100c0d40d0340d42903040103441c2034140d1713205603 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 596133165 1250 596131915 596131931
    0x1412060a03080a0504061106220302010b090109020c0c04050402100f0210020a05220627120f020312031e040204150e07092702130902070506040c05031f050a 69
    0x404030001c0c20140d021130300d070313241c40320f041c480c004042000200d91000c90b940240140070088881c584d40d030781400349000e11044038a0030381c10160f016000004031690400c0d6114000601800c8640c007908a40c40018151194a40c601c001c2000380c80c0300340c0303002e035020400f4084c03025900d0240c19416402d1480340140c48000c00c055100e0b00890300048040d40c086034000840712050500100002c0b00301107621104076615082180080200001e6014a0b0300f41110780c08192207004c0500f5820010b2008518890303aa40151900c60340e4088030b860228024030450503036006003d40f201c207a0b4440ca18a00d090880000071a03100ba1003044007070130503a0060b64607000300c0f880c2c030300418a5202030700044255418a040442000388204459071100c80524006c2c0c5161007001007010001080c40300718217000d6120781e40900302451f070380e0960f401085002d00c0011034000b00000032030403030300c102d003c5d410f41500d0503170354828991140b0802c4441c4424200d02c410030f44a8440ca54819504074601510008a241c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 596134415 1250 596133165 596133173
    0x901020f12040518130303021b01021809070507120507060906021b191e0201110d0f031d3f04030b071e03020708120c0c07061412060a03 60
    0x190001d8422040c1000050288054200340c0410b41c241950b090010f0903500d0141040c044014001000404050300002d06200e0070501520111080060b88000c55503841002c0075405a040b5200300070f40076158080c00120704900401c00d0f104074a42014011100350740171041262070b40d002c0d900031106155a0500100890503038400b4180840300b04c00185002011520124504012210018102144c0995803800100007c1305212407280d540c006a040420b9840180c8481c00c108800480034402e11425500f8250701007013042c1030030515101044480c08054541000211080c11540d00e0740c400706441d014114180a548803c861481d4011100048070103803111041c901186041c0d524400301d014014055092505500700788a41040d5800e44d003520010050843e941d1045020f2580c0850800c043c0003c0700d0481d09907039842c002064680c6026881140d180d0486030b5681020b114540009c1501e40c0551920340986008014090612481e284001e5419034000c288a42040b51014008005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 596135665 1250 596134415 596134423
    0x2040b03010b0309100506032802040e07090b1503071d09071d06070309120c0b1215030c090117122a06011503020d0212040302010b030f1209060901020f 67
    0x180c80360098083d0b807400d2583c2c22526260704440340e00c0d225803400040c05610740c1c00041095803125001c2d55034850030701d070a03c45451034071000e40c0a9082810100121000f50000c99400103880e00c03504100101804401800405094441c034480311103420801708400500503205080d251508240002000e60140007080b0308000c1912018040340340764240c1001c0d52601c0e0b0055144603025202c0504101c044c1d10000e1840d801e903c41d506108500c41040005d1003071100254000e0003030f00f04010f41c1d4410311180320400e0581162909111406481e48128030301d40030985039418100105071140d1642040c89950401008000800c00e80c0b162101c40b00b4001ca010f00500314511503440d001e02e000103900500030014503030640310720075600310800509c816841000d03052420314180c500181c41e0410200c0b001c0080c410404000f03420b60140c402c1104041c3d0540003a18050402e030203032104001d02c19070099881034100d082515481c01071080041c242066030151441010501c100c0760707131400407581c560070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 596136915 1250 596135665 596135669
    0xf0a0c03060509032101053303060316080619090302060105040e0309030601080a170a14030c21060102010e01020a0c0f0218010e06030c060403211808060a0c08060a060309030302040b0301 82
    0x3100780e00717174010021131401c034001101c041d48030103104420100c5216401403101118003d20154000480818543d49040141d000308100e02d0347c00d1120103882d080f6031540c891044070000d0f40e0704c0c045405488e03010000d0180300c0005616030000c01081c0d0905c3c1c204406800a5081e000003844140081c818a540420242e0700810101000d00f42034045402c10349200d00703085403030611480c010400c0000e01540b000a00030904103d0351842d07203940300e6424144071486a411402d001940100000c1ca48404041a0f01d0140c2e100741c0081150600442da414240e000304c44540c4040b030000003c20000c11075501070305116a200508031010240002000e0400010a8001c01191b1498204010040c10200100501444103c64190400f8030b566100c9104402c0c0085000c40c0b1305180314200d9040d8000e03100303007100e0001581580c070fa158840d0b07030703255a0307042c00c0f2982c3c15440e0800700d044d03200e9401110031900840c0041e00c00d400982c28402d0070f80c003900304030600301e041503800c00000807207a88440c06180 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 596138165 1250 596136915 596136967
    0x30e0f1b03011b09090207030309150c1d0a05091e0f010609050616060218030105310b01050909030c19150c080a09050c19080f0a0c0306050903 63
    0x414030a003506140c21188020003003492140541d0b40c06a8041d00413081c001103602011001d41e503180586405c034040c01001500a00205145284a005102c0d44d084118030941700d50307030032000030000c0290010380034510411a81000c6005014400b908155100341d0380f0014804540400341c005104150a45404440a41c5006002c10044c810a035110f143d01c40100790441d0450704154801010321440382e06032200034031403a800140c4a80ca062181c52a01000c50014000c00c0607289c03035202440c41c4c501481c000041d0a5104840c61040c0b469140b550441e190451090709240c0e09180610208110142c02c0c40c1c1c540c4010b228940303030843d0801c043d070f90040b40443d1013031a00249181c02d01d148101802071200b503d00b801808038071150b1045d90035600c240030031380204541c885410f159041c403941c0e40d000c5802c000000c050000b80082c48440c01c0856020400b103400c00e400c40906180c8408850b5030003440c0306000700c1b007040810815001203810104101c01d403884d2803c030400c01102c02d41680c481d40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 596139415 1250 596138165 596138203
    0x6040911030a2108040302070501031a0405090705041512060e070f080c040608061302100c0204020d1b0c080712090509040f0b0901060b040b1e04080a12051603030e0f 73
    0x103d0045020340f5001c140d0b010b507042c02c140509081d41d02035181c80d254010181090750b0355a44403000c040601c040002100e001d0010443c1e4200020020303102d030310030f014160080303007003c400c03010b00310907145008100c400301d05542c9440794031544d80a02411300c0110a001c0e9128440011810616140341d850080c41840e004208140c2e105017800107661499001502d140c01c00e03400c0044081001c5810613825504441520b00100001c1c41136400716074a400182d0003500c0403d13030104010b02944860b1580d524000700035100f01c1d190004a8209009200003071043c80107200000024500c042e50341d280000070b0900d0700b4015120404038110a0342160217031390000c1848260300521030901085500f00302400300a12001d41001e80f5806980304500c078561540303074005200e031004d843c103602d89204d019140d04a256125034490555907581d402d15410b507401c801c0001c102c00024011011075550701d0945100300c2c800d4402e40c070150010514402c9030b0303ea90007582400c0c070694205000c0c07120424420503e0b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 596140665 1250 596139415 596139443
    0x1b0705031207050604030c0c0f0803070c05060705070e0a060902070f140d0906140c070f030501051e1305100e10151208030a09020d11011205010e06040911030a 70
    0x40c03501d00c1401d109154078000700490710100b42c0c00702e556a4065050b013403202c112111481c241040c000d8a43c0715027601c02c0340c001c0c0030401d514080010180300c0e00a10f010000d05884004100c85441146001095903105007003c11404802d000501d9011109050005001d940c0340c1c4070006070f0b48400021180d991942110004204580301503002442e8084002d08815100680150a591884c09041c05020100002d0082010140c0480e0074500150041c0d5154943c3c079108119039480a000848141d401c0c54001036900740d01403041007801040300c40d00910703602c0700400c110401e00103503001e5656010315060020a4200c9014081940c11407800402074020b01301456422548030a404504001004100f00700b0340ca4818040710360f4640140c4010390341c0d1120801d42e001007644d800003d400a04c041c010303c05000031500701100352002a201c0c141000c00c11120311045403424012080000c00d100d001c42c0707072400c040d0702c44242e6510541c3c0e00c03041d42c0d010400181c0703450b40c001003c40c0c080b24450b03c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 596141915 1250 596140665 596140669
    0xb0106260c031801060f030c240e040c030930080103122d020307060509030702030a1103010207150501141e040b011b061b0c0b010311061b0705 63
    0x445032580c6212038803000c1500701000600c0d4544000381109044110608440c00c0e000c02c29808480140341c490742d480c2001d0f03030368503128204080c80d101e01000f10090888620300d15240031501443c09000ea9144030003601c602c000c100060007926506420184c0d0f030741c2c0480010303c0450f89001c2c5c58003441c1905a42880804124101c0c4801803500c0e401c1084c00b000420004003110f80f4485801c2180c14098240545120b02d4510850100204010766802100d60742c049038000c80180207050141005002c180c1e503042100d540c0340f0a0000c025015484440c050010442c00b81c00c0111408009001520b082d02d0780e1a909a60881c0006038403d0b103580700010040c01882000598003e0303000d540401400300e0501d0160340c5034118081e4140129101c0300307002c92036071041340c00040705803801c51790180c10041410f040d801407450800808480803122070104806000f0700c3d210b41200c0d0f011104d03c4a5a00b165200da10f210744410302c0e43d401c1182804182e010440109160540b40d40e03400041c070549181c401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 596143165 1250 596141915 596141957
    0x1401021501061704031e0210240e131a060117041509030519020313080a1e060902060f030406060e1b0c0f03040803030f01120f020f031c030605121b1302070b0106 71
    0x1c14030720072807110000c1c3c80303280301290092700b101c00b010785040c66030b65202112413091102d0040102203200c281c1084a0302c240d039040e4240100404c1e61400318a00c610503020482500c01c0e00d0160030030344804000c0d8510101a00010ba04c02d10a10703110303080038008082481c0c1050560f05090250300042a844048240d0b021024000c01d40c0c8001000558a90307102e0607540021000340c00b80340b20030f0402031010f02c072141d009a54a030303501a2295136608001c0d008050590801d603030458106081c4032000840f40da4082d101c40c0a901808084200306d480d400c001b21183d80403000d10403580c0215946105c9688085c4050070080440402440d030b81c1c0f9114130500c0e091030b01608661404801e024080011552101030410030035415030b005042c00800c0c41c0002d181000044240e654200c815040226142d40741c2c1040c0100d690507035015500300310170a04030741c484c0003400f29040d481007013072040f141c0f0346414244e040f11000c003008010f04c6d000e5903895283c1c000e8800d03080311010030710b0030f88c1403d840c4032100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 596144415 1250 596143165 596143181
    0x150e090111040b0f09030604080309011a0f0f0f0a030b090601090614010f05391f0507050c030304061a2706040e071401021501061704031e0210 63
    0x20400d6901440070a1107502960140d245060804502c2c1c203180340915007203c0b00100e0003022a441e40c0380910301040301e5070040300d00c4d41a550800c190a03000030310010b13a0941c4000005c0004503010810030501510f203622140596101054031b465107d01e4603047c070250051400381036002441e00c1c0c1110064034009040c1d0003c41c1e8a8905401003100380d03c06c888443c41c0d41c0c1c0902c1c00070006044c078041142d01d4040e404030180038041c1000030068804001020148080206078080b0304110808103e80c2c9455046070710801c4414403541843c032114059002035031160060529604106d10250868550f8004503000c440c00d42d0383e01a40b00644008004c91118080c04445000514640740c1c09110b0510104520000811452001c1402d41d82e035a00103001085491046506450b40c1ea01c01240541c4140c481c50301600994600105034401f0000080c180e40340d6480744c400d0550503040d0b14401c918000c20513010040782984002c2200707920000c44090300000c0d40100ba0380c440c0301030503108a071448 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 596145665 1250 596144415 596144431
    0xa090203070e0f010e100510020a0611090616020d080a08040303060b03240406150305060a0608091c0e04140601110f1009080f03091e0706051903060504150e 69
    0x9000c12062002402429041d10002d10030a001d503107035800c1c00c000300007491f00100d601034003402c070422030b265002848046c0540120340c180007140203070f10f02c1a414460840da45030001c000b000703000c0100045140c40400030b0320240c00441275650580361b4050503001490414002002d0405102c1415894001c80010341b2003c81c01c02d1940c2800702c00006145003204a90a203200c030403003943c01c20307a11070b030000004144c007400c8400c20b43c107000e00090060400326000c510520040c9400f207485480740da41c03a0310410100300109000440038280b8910f01c84a050710307404100c54088201c2d040d8499001c2c102a045260740e03050304500344100054181b600100c440d0105500803280701b03201e4040041c580c100891910000a40300c1d80ca4205030859200e52006100301000000501a03900c0000800c0c1c01c604c217041405920f2840010f102d00d403108424411440061028801130541c03601e00701c0a0503c12045081c0000c2040d900c401140554001d0075401c07100410f4103000300070014011111030f52229035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 596146915 1250 596145665 596145689
    0x160813060314060909010608030a1206080d05070206070c051e12010504050601170f010e0708070609030f03030209010314040507090b090f130807051c0e03032d120a09020307 76
    0x24a00a18008440c001e003c1c0e4030900203e0b0200c1e01d205402c2d889000a0254907098a69502c40008090701e075240c54044040302c0c500e091700000ba8544007180a030890b0f102079031101e02c0d068036a02003050700c0d00490760680d1040d807040c0002400342d44003032030540c0c03e40020050300300c061003400800144034003c0c0c103211040c2c1d0620007000001500824101d0650788610404900580110b86091038088440700c4411b943d80307485c03040c60400c00d0000d8800e0894013050115901c41d0780720542102c6180c05403000a017031450aa10100029000e81c0191800721010714002503030b1078603507840c0f0740d0301d41040e10b0035252900000c1c824481d05d1024020040540000d4911000702e00301484540354081000344201188079225041004018400e070071500c042d0342000440300c6052505084000c141c1c032150061010452680c00120542808015034410305000144c01e900030300024445041c000d0600d482c400c000c84200940c9110841000d0141c0c01804448030018040706288107152a111594110341c880307110f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 596148165 1250 596146915 596146931
    0x509010b13050901020904020f03061017010e3c0a0212041115070c05091006050315060f040b1218030d0f0b120c150301050120031608130603 62
    0x80d0903481000104055100103219541d0320f02082c020b004031590968000d0002544004003080c001c0554000c0710b080300d10032402510544191501000f03920301c0c65558140d0401003080c00c0311403e4480d4040340b20301052400444822001c42d0b024a0f80d03c44140b101c1c25003c2401d1b5004500d0748040e88100700c54801c40c82c200c03041c0790101c0d51800c02840185407a294160b0020306072604141129507112410507a80c480c0040d1900200124481c080c0038020308a8900043da0201d400e1000001c070307411501c9482c42d50300d40c05001c4d000039840801c4c1941200c4100300d5880720342c125500400041c4071814210b51a060000e0035081940c60141001c40d2801d03408000b10f1615402104030790368030300102000240043c006c8000400381c000c01403c0c9501c112071054102005401241c8490b001c1002c40d41d0104074000030004210a010078000d0b1400103070940240c1c519101598440401c0314104003c50382070902e494274080119441020840301c1c4403011444551314070b603c004a4000d00680c0c1001d1003111 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 596149415 1250 596148165 596148169
    0x7060615051c020403060510080615061803070302060a02070602100606080f042a03030806040c0207120f050607230c0c0d02040b03010f0b0109051807030c050c0303040f02040509010b 80
    0x100590402e1160700c0100071480c1c190a015034111401941c3c0600140031a240000b01c2a54511561080c8505070041c080010100380f140094003200400080000f8209080d88404004815984a030603805210716080840582e1301c4101030610750034180c0c02008000c0c01c241000f8245203032003054105560a00506101c0140c01250f62a80300b000c5000c891020b507501e080815241035500c84040c0c00c5021280d854807080580101201901d0094680b40504d4441005200807680007040c9040140c001c44070501c49946e1610300c5040c001e02a0410b811121047d88840c1d041130b400b030740c032031001c43c1c102d107c2c010080d2203126219800f1010702910500b0050382251590702d0300c41582045100d080310403181070031541e950b4000c010700c1d81c014000f0840e0b507901d04120002006020600340c04203068203400109403804e40c0c20392036131109101c0c404108e501d48500540140603030252a80c20f0110601c0311880c030302c10400180d84103a004090f1144003c0c00c50050004689000c0c2c52803c50764100440711b10b0316 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 596150665 1250 596149415 596149417
    0x3092401150c0b04080a120212220f03050a030e01180c0608010308040b0310030803040506070e030a170a0e0d030804121407110a05180103140c0904080903150c0706061505 75
    0x800d41040105c3d0307407941031700421908040c2101c010b0303071043c0c03000c00d014030700710042244c4511a2140711840200c611580701c858250354100c034001030800e5540d8117090000391191025009a54860801003000c0c2400340400d030940782501e03100d0751201c406038142c00a001f810b400c038000070b0078242081100b07941907491381d40b214803c602401406d040008081820089001141c00065402000058582c2081c0c5007103519002c050743e60708000b64410101400900e408a00d0140169224100c00c071005500c00c1c0c0792038036401244880c400e104c400c0300d1a60040e125503e00e2001107209641308052803030300380b034131000c03001d965600d02080000741400c46143c00d901e030084805030b0f1341101888041d035595000083caa65841d800641d00500360f403100d0301400404c00d26460580e840b82c2c280c41c21048080201580e0794180c1c1039219032203002080464045240d5400601131444c0c007500b914403010203a90300b410b50036819201e0300d0075004c3c0040d1030707400c2c8000c511541d805401e1030400003201c0512a8030041c41 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 596151915 1250 596150665 596150671
    0x30a0c181202010509040c020102120a06050f0103050a020c011407020f030313020906210a140c01020a170d0603030f030b03010903080601030e01020c0f0703030909051b03092401150c0b 81
    0x1141e007484100300d0540e0301030826100c890100500900503050103130380082c00f075080b110603400906486808036902c0c800c180100c006480001e44206686880c1300011009020090440b514150b4208010000c4107801e01a10480f03105207a560075150809041c002c1c5843c0880030b80868603003080c01442100500005981485034040719000020f440d000001291481c0b9000b4900c840c14030740705c02d079820080100304600c0b420300038400780321590040811662207244040d002401a004010b0050000e0b08141500310b401c044441d0040c1000481e808180441c0c52940058000c1540c010351081a581c0c580204400500c00317a00034464946142d070301900d90030340904131034103145d11101038849501d02541925118242002110355088007224010f45940190100f43c000070380c418008510f105240c0180d074050301c0301000585030b0300000d000385036a07a040070340000c2c1d19000e152480c007507504a104a40b102c54520004500740c551504108a0403010314580140c24425804c0b006008660b0894001c2d0b4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 596153165 1250 596151915 596151929
    0x11d09010b0903010b0406090c0f08010815041a0a09110402090d0b0c0c0109080714030a1b06060e0708060a141302090111030d060801180503073302030a0c18 69
    0x103110b4002d100003e001d0034092400b940c00520b04000010707078900e1a003000825044c1c40e129034417504202c0780f04582c00e0381c090251403c0c135880b8007800880c101e104031100c0c0c0d200e4000d1140301e0a2880401c2038081c502c405840c80c2c0c2c0780c540c9512941f03041c808156146010104110b03021454100041c010503500c145192000d8100c40b51000051240188441218900745c0b19134020003060004d85044415500b051002741c60040c11410406d141c0d45001049030400c40041d00d640c000b0280300003075086040800791007203614a8035020001000580201d003980030342c1040e101d0b40401c1c0350080074030204202d02e41c88034084460009404849484000744880e4600e040c060161317480088000503100344444107032040355403000082ca03a100d940c0d1035200310151507001c03000f0704c44c0180000c245000c01e4420b4002401e1604200401d00008144140c0c81c080340302e22402e030119440f110105807590345072640501c2e181c60707000420890015901c0c41800e002031020b04102000101c88071a030a428200341c02200 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 596154415 1250 596153165 596153167
    0x120103110a06032d0b030a060501090506100207031205040330050301051815060406020f0f060c03010902030a0e030d0b030106090c1b1502030c07022707180b07050705011d09010b 78
    0x3031800019a00981c05c40a000340890f0004612468018003c1400744603800c1d199243c1008a00346250030604595854400e60003440070300d04503124205861510b4149100380310041100000190302c000c40e802d00c3ea815400340068030107540700c0e07400042070b2034010101004001c100600081c2d03508045140310040548802c161079480440311002e04070340303140c11603101030b01107000244551300095800000210350700360351a0441e5411207942d2110140e490380c05001e000c0c4010f003d43e00c441d0303001d580c0c40307134207942c001c110020f00751242401c60780b264120158040c0c0f100000318550400f400b4801c02008440f07401c21183c000e00c5c82c0241079030f540880300e14103214001c1900c014031440c440b00781141c03611020115070700d080100d01810103900c4100200d020b156081c04c4140078164001d504003604901058400f07050791850022a010500010440942e0801100c04100b110f03501700a03185040c8140010400c4500704400503100c10025000b011121520a50041d1710351510030340c1e941182c107019142 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 596155665 1250 596154415 596154491
    0x804021009030312200c06042109030807150905390103090201050f18040c080f040308070219050703060e060c0a0e0d02060d050118091a070203120103110a0603 70
    0x9035102c5c400002e05594800c0000c9250950300f080868118021803040c00c0714650703003040032207c504140c50380341d0500c04684001c50400201d05203c0040002501c0b880154001102c42010312045401141c02a9031544c030200c14903140c40d03034455201499010742d4110b003490649507031011103680d0041d0062410036449244000c00c69005005540c1c0001c40b4000440e100c07200300c80c40340001c11591500c02d110703a042c000c1e80305140b070003281224042d03103010114902071350300e0380c5083d07840c500050038203002c52284076510001000300d1061071164500c9500500101403a50510348141d98440701080c0080c8c0241c01405a81102d190859090a0141c20520042c10400001032208a00080065000130000400380d640260b640d20681c1030302c030942c810701c204a00510b0164100c9428440c000e2820b030040760350b003c2d030080d82207485030b00c00c0d050310490707182420f29030109441040a9000f103450031025242c1d00c0c0d0a1070407008020240032545800c03c00044440c00003e9840c6108081040c6c0b60640800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 596156915 1250 596155665 596155691
    0x30e0f04200a03020f270409030f21020f070b090c030706030f02090d030c03110303100506030a020403170705060115090303050306120f1005180303010e1305010c0804021009030312 79
    0x5880c4018003031204140c0301d40344026031618961502c0042e00500d542e006c1d4186a40c41e0074480e026080c0d41650b145800818020815038092480f1030801d41c40b007800c90a0100015014002803012081e0609016168401440d111031444006040a21503412000e00a0380e6500c0000342a07044549920707012440c000100c00d0f4900900c911455103421414000c0c1003002d250304000c500d0b070194425078400810361315403141141c40b4001501c4800e01205071600800c483d1420101440e08120318410051816689560b00065102c0d80b03005051909008a0405c051040500450340100745c40102c0300c001c6c0f004603500420020b0503010060512902001051711521201c0800860007640d800310b074544a413401c00141c0e540c0309103611403059810f02002a24401203076140400c200000340045056908200252802510040c808501482094000c4012403824054040742003180d0311450380c035003401c0c0107000482c1e043d690401c00340b000e011b00400010f81c2c40140481050b007100380000e0300c03152140c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 596158165 1250 596156915 596156917
    0x1061d07030e06010e190b090109020f0c0709061d01140904031704050610060203040b0a051c110711060c06010e06060f0304080a0f111207030306030f030e0f04200a0302 74
    0x1010b400079128a0002042e443c4c0c0c172088460294940c07040595280380c2443e0800c00b034407814011950090041c03401040104400c0c1c0181881041d10801a4240403410203124540384003544244081a110a4200f100d00701180d1032224002805038505d0303041d810943c2e0141541d1100c11024040c000c400c00041c141442081d00421034051802c150740c40381030502b03140d642c030a0251040a100c0400b80d07000a402c600000803102141c0000642d0317030500c034070080295416080081030061001c0c0800710079050116a10440c03001003040c0c4e840303503140c064034201542c1c081d0754103c0490041000b0031001007514400208141181d00e21030b10000c1540ea4100030400300c0c0542c900c0032059039808024041000510b001903c4030a0099070f41c5040c4034110301040700c66900d01d040c01c041325004000310342e01d0156002d00030940719001e81004138081d80d0b40c0c1e481c4010082d8851b015800100c04080020300ca203000010402e070a40d0480301803011490841ea04521207e895030840d035041e400007034840704540650 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 596159415 1250 596158165 596158181
    0x5030103021311031f1e0302040504031403130c06050a232a01050c040b0403031d06120906012c060d060914061e0c2209140901061d0703 60
    0x4005280c1300c0c2088180c205100b03074880034031845403840c0e0801082e0150550b90300c0c140c550100100245881c0340d50240030040c03038042c209400b085400800d1820145500d0025400343c2240440309400a000c1d0603da102d00a4a800c0101007080c03c03c010541c0d0f0790b000b40c000c00e54001c082c2d0403100200105c2446007151003181c00844602e005845000005d0140401411005140b20024041542c5a2400c49144d01c6180900100c0032020700040c00800d108100301242a0f0018005e051148902000103855400244604031016100d00410680100600c101801031a170311602020b80b90075603603000c244010907231805415521303400000d0700542d2404175002c140d0350441e4041010404504007020110604404160603108035070200c0c0b4030014410032302940300718003110008980c030f5540900c0b00ba81c1c0b0401c41c070352040c402041c84511002c0d81c1a8050020461713024001030b20901a2001c19207428000c09074505640740000c2008234400d503214400c0f4040324110415680d0380c0e242000c0d401070540b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 596160665 1250 596159415 596159441
    0x2011a1315090c050409110325030e0307080a0e040903020c040b042007050712050a020d0f05100203010f05010306031119030b04060b09060306130335040c0e07050301030213 76
    0x12002605403d03030020018025140445c4040c044146210000e80d0644000c1d1520041c510b401c0c5072900c100f95256030380e0b00395440300f40380100320880d44c0035080e03180d5006100c0580c0c02060000b0f290811a40000c400d00b0010005e0300d0a000d10078a03500c0207900c5050300c140aa008540b0f441e42d5140f0340c5d0341d0341c0c069081d54106030386500001c07800d07101ea0b00d15a0009801296603209030030300400e0309851007825540d4550f001c401803000d16010703828480409420030080381d07681110031030900028002c2c021248145920400186c0725803500c40c803c0c0034403140740e02c1103051528098050010502004032002c1410065500e101480000a50a00348130030b96440039201003000c0043c0f208000c0385400c041c440c804202ca10a10f25140c3c40704140d180c40064940b90884400116203000090148100803c010341c140b2800348071652902c90f5010800145000e03821100501042008000d42d582c01400078040805400e01c803441c0081002e05030340b2045c0000380c494103030314031202650240d42e00040c0440c407039 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 596161915 1250 596160665 596160671
    0x90201090b1c050115180b030a0b0402040e040f030e010e03060c090d020d08030405060a0b0303070b040302030c0d0206010f080609060c03060d080a02010c0806040e0a0209060a090c0f02011a131509 86
    0xb54079803100c04810600f54150009081b001c10401161086120340299141400603900e540c64071072900300101005115960440c1d000d00c40001d80424603101a13102c0c0b40682c4000d007107400305140080811403000c030041c0c10b000305030072898403e80700040d03182c1e031010b045c2031056580c14070580001c4c40c541d05100300075400594546c100d003c01a01c2000340d0300540c4128200d42c00f41d2035204400064030f00031580103805520070301804000c01c5000e5240358100780a0300540b40703800c0c40c1010f5107060982820a0a01503481310700100104500a41800018102500a0005401c10480c0b4a8480502a01c071400c80000440429042d944d424400e00080c2c1d403000444d9654904840040e02a0002e05039440204141c01c0001d0001d0070715000318022946d481c0090a00403c050f82000f854401c09028990000584403022030404d03450700c244549181d49841d5545503281109009080d144110018100200312105500301d0b07494070690715280c10212500425100c2c0c007041da4006c80c2c0000c3e440448a241 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 596163165 1250 596161915 596161919
    0x40506040501350f07170318010503040611030a0c02070e060a050d051f0e0f0f1c0509040e01091401060312050307021c0e03250b0c0a0605070f0f03090201090b1c0501 73
    0x140000d40d202100d5000c205141d0881b0520300103034480c004c3d090080c0130341d5500014030902d903208400442c0c2c060301c0307100002400018030b02840360726003044482d40402544c40740300743c12030760701000003400612420150300d84914205010034005049407044502556048407401d00b08601170008442a5454a40c003200382c4c0700203203000025101344035802640e80540c2000c45041c540104040d51032644c07200040040e00c01070038550741d66407c060f000500304507040c08031444c00c1e90341c1d020f40f2805048120021412407968103040f2440d40c4207180306110b581c500442000010310003200c0003004c05040c140039071a6070340c0c4207041c0d00b008150004052011110704100f410290000152080e0800075021200e2803003146208a00c2148610300703008421010f0101040441e00c5100189180d11a13441610204615662400180c3e4400d8a06601090300c039400d89808581c4000c8032800e0761400d240600034030f485600060101c070700501902403448800039030042c2c49125041e0300c0f01541c1c201902081a50703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 596164415 1250 596163165 596163193
    0x607170a09090f1b0513061d060c150f01030b0f0a09060905073215090306090307031e2f0d1709120f0c070308030703020904050604050135 61
    0x4504004e00c4038400d240b07038024030a40f01d01c042d0703000103155401c5211032034246003013501c1d0341c5075903c00c12614402c034902025143e10b071031000d00201140030005250f8048503036402d9a500300c0040108107507511000040002c00c1c0d002c40101e400c803480c03c200755540c0d1100d84040005c1c04d04000041d0000307040500201c20064005401411107442281c4042c40b50040441e410900603034079001d48101030125000c4205180c40d80c2c2601240ca02d11403403518248450780800c1c10490101d40c1800c0903080410102e0606800405611006170701151100000c041c41d400544060442c58003800e4032040d00240402050b900321038000c40c40031071407c96081e000d104100801c81c1c4181103030816001c1c2c0c504045244d5402c0000c1a14401080404940c140081d4074081205500079000b0088030784034001c0b002010034080070003540105225a40583d40d40350b03001c00d2109030340d0050010781c01149040010042c3d134450516804010310402a410304203030b95441e001c1b2400e14061104801d900400700b58800750 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 596165665 1250 596164415 596164421
    0x605040b06040e0102090d060e190317070c020109060516061802010216081e01020d02040f150c0b1b07082206090e0f041b060f020106050607170a09090f 67
    0x28202200c00f8030104024140c03003800c2c1e0042d00c2907203800c258a40c035030600003049904811488c4e00201e0498010300d0032280c141c080d0504110096010801542141c0651100401c0c140c2c1e11a006080070b40140d9410750001f000c0d050350b880b4000030020702203024040328401001c210b180d01d801640c10b111240a40c511950078810702c42e4102d01620030009104044450002d06074115030200d0058035410b4400035440d20100010002280b50b951300700000c0d6018175940c4043c1c000b824205000140040c01c204048001100504880f030510130300d40800000510780c000c206900c03222503401e20340c4882482003c14240d0007207000003410035102040c15600212610341c201c1e0003000c04100041c000b65501c2080d628120b01d4081c500c4d80b00d03040e4000034100d012446603203421a209146260080c0506517495030090840d800610005110409110750715078240104070140108440d8036140072165656140b801030a0b50004c0d025000c08549024040e0190032450000e12940500303101c4200b981d0807903c02 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 596166915 1250 596165665 596165671
    0x30c05030d030e0d0305040528110904120f120219090e01140904020f030d0e0a06050a020a110111030304150f0b060a20030403030206040c080303070f18030605040b 72
    0x1d01c62001c490300e106219020314045000038070054554080c02120440103858001c00039201c3d0700c680704100a80d1481e50810783da4040c007030308900284034400e1230a04d42c20b0014038203d0f8440c081040a0201007080031071903801c98141410020070307180010f6800e81e43c00c251500300130901072000c60ba803544420040c5035050810555911850160349a114001c0707074140a00540c104c00b840b4020502d40c41c1000b8140b142c0242c0010822402d0040c81310010b4500f80341c510b80c0d4000211484220041414404c5140c00030b042141041c504085100c98002e65607850b0584c040e08424443d0341080c0c441e4010300c00400d0034402c01e0300b40c07a83d80c68507080ca40e020032404208901c2040c5041084840e6520900c9070803c00710005005610380403002c8405c0743c1900c221340c40082d81c00d2103241c0440c4114010002040298800e40291005d45070501313004402246590005110343c00400c2003203002540b1003600e0300d00419a007881d148801e4071070302c113040001e42600000c00341850101070005000441980f0780c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 596168165 1250 596166915 596166919
    0x8010e0d020106080613081215040f0b0f2812110f01050304030305061306081b090402062d1606150302010816230a080c0702061209030c07030c05 64
    0x503500d460340508900701c6045118030300542d04207001040400c0c1442e419a000b95019031211303810600840e0304031242e40360659003203a03a18480c2c0d400740403a042c54001d0503100c5880034800c01880e107411001c1a4448411001c06104140a241c030404c1c6281d6032102c132440c428195801c030b01c5103489009071031002e036540388180c400e006e51038041ca04d185010402c0102e8100103039900d07800e40d140e55800740c1c080d000103170000e54801e811404461440000348141c900500c040301c024800c0d015a45102c10b10081c1540c80705028456200401015840b17210442d005c051103180b00e01032810003261114108a006150103043c01d400003000d2040541000c031004c0124003c15042001017100d0500081e0300d055880000d0100310f600f00010007440f101c0865013200c61850a04690080c2c403848896180100d102c9038800502d03010807000c08031540401440d0348801600001442c001c81500050540e00868440481e070380c08a100080c0014814170580d003071220000c0846a4081d102c1c98424011900c038000d0138 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 596169415 1250 596168165 596168173
    0x20409060c081e0108150c16080301090f0b0f090c13031208010b0c0607050a02012c1e0a23030c070305060c04180207032c211c11030408010e 62
    0x101c0c400b4000d140c00d07040b90715400013020703009100081c080044800401d547c450a4003403083d0341030414442c08219042d441011525941d42c1010600e40855501403d00e640c458a40311003800c5607180c20303004102c031781401c58100c20117545545113420a403003142a01100404180800410010000d00f190400f21140d19a04440c0c0e80311a000790041c0103050302c2c291654003660209e42c50354015001044101020703c0045034240c0c100641c8030071344082c40030001c0c92410410880f2100441400350704542030415000086a000013416136550f80e01184000c0e080c5141d401b00c4a0320400e540c210407003a440e140c4107580d1980d050482c4c00351181c4483c481640c80d40500c200142100ca4254211400c0d1011009403008408040190748000d40010100301c05011110203413101d840c0d4000048403103e0101f100116807680d079030f020301c030100c0580e98604908030410600c0414103000855410b0195088210322070647e0055241103481c815850380e0200a03000024001c83c030300106412148490003828115 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 596170665 1250 596169415 596169451
    0x18050a140d0203100212061c0b19021c0605040c02030708130e180c0f030709020c03120112031b0309030209071707020f0606030703020a0608130204020a091409060616020409060c08 79
    0x8466480360b120238054130182c10f88010340000705030207522354100c0807400e10008129400310340d4200300e038041406c191540c1d2481c1c441c88407680036030081c80e010b09000c2d1014440041e003014041d6490059050080c000b41020966581c650011358400008200344000340da42130904541040022841402c482224003030040100c4190030046110340c99100054000c082e1945401d00c080000c2d08003842d145024001003107a10441c1c0801b00c07a45000e001e4a46030343da5100c10701c3ca409440d84d494885012002100e00c01d425010030381042005046a4056031500c91340d43d560003046508032042168042c43c0240e501c240504241d00107402400d80c01c480045400c1030b01d40000301940c543c0b081c0710080d4400791301b00042c041244100300d40c1c0c3d00016011544ad050715441e90014099030007403404a4001202034001300510091003543c035003128010340d0f02c02260b003491400300e4820301c9155101c42c400d4200f500c2000c00c54503594406500b260b00712908212a0b03048890040914509840c462603140c9403082c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 596171915 1250 596170665 596170669
    0x1091b09051803090d05010b0d111008070804020f0103020d110301080f03040e0604091403032503090f060e030913050f070f0806100905060d0c18050a140d020310021206 74
    0x11010503900354020340c1040e00c103008000d802501c17404121520354890426620544038056824001482a003404014901c601c0c107100e5000c801040c0304042102d80410301001c0c58000c005640c01c2501911070342040001540140e020788684e41c010b165030f528059000186416100285061f11011000c0e9007180581c130020a03921b000d00c0c05019041c01203103000c01c21604d09607004460f200c1c0300c1e0300d19448030402091b01509541080301c84507d0071032047c00d141c929928840c900030700103105080410100c5220744894400138200900108a1556000c1200c01c0130010410b4658181c0018444101e40f0740c0300481c4005000300f80c03002d8400841110203d01194040d005108000003075558200361f6588000c10401070442d600d0003c4140540307070001081030744031800184404d60b42003401040c00c00301c9041c02050b4404500018107010b01000f0f0510144ea2941c820380101c6600712500b41020320341000181c5903503a0658002d50600c600c1400043d00d5503241c001e000c1d80b9400e1041504155100c01c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 596173165 1250 596171915 596171941
    0xd1b0c1118060d0f05030c010515010903150c05040503070611011802090408090a03080703050903060105030316030315080a0b01080d031406010c030c020613030c0b04030b01051201091b0905 83
    0x1d40d0200c07040c5408009040390601c0d030144940c450242c034201c03103600f520b51101c40c21a03001080e40c81161b5112404c00030f010b1810304078481500f03003c1c68141d040b145182c90b08040f80034095686400f081d11040c418001310300c1034054a0142a004059542403a6540300141800d80031020110440d42050558610400070000103007103542c000d4980321141e0382e60360341c107000d40d4081300300c251f8000100f031000300202d1007001c09084894031949a940d81d48001204251510205900c80d078401d40c010400e400c01d034400a04200c0420b42d050a0110300c0c1940f070b400a140780304c030503000b40685114542c8a28140714444140a040310301c00f03400c0d00c40d01c003070506045059034440340d52615a000500c010500a5104140301c0390b034940203140030050316004e580060101d0307104004000307010300701c41414828482d07a00c6d504402003a151100c18505803a580e100e81c07031904140700f100c1c07107040580500c020481c1c3c2904662079071540081c4041c542c1c0e0103161444070800260245101c0326185c00000354012100c20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 596174415 1250 596173165 596173189
    0x51507060e030f0304020d0c03060c0801140d122a03170901020a0203040b090d1a07140c06010501030b060c010507120c02030a0207180e06040b0f0f0708040201050d1b0c11 75
    0x8803005103161750341d8003401720300d200a10048800303640114000000c14180d214110000003582c0c0c0f04840c039490711a00380b04103280218920310418442c440d801c0040d5001c52002009020740c1400702e522041084001c46003600000c1d080546241401b401040540c0031001d0300b0801c80003501da0045032180381d1507908070702900c2a0940941e104000a0100000700700207084444801440101003c41503680c2c503c900c46540b2100c11201040824402e025405c128103600551590b074100e81408020308070f66a8072034041c42440d05144da14024007800c1d4691204540c0b12500080080c0100d00384820014809449600e070484410728003c0603000039403021044500420255004040761420300101c8007110900c070140701519075403000801c0c2ca50300180b141500c164018140a0a686801b162018000c40000c000c2000442101e0030030050a400c56103443e00250280f0f0403d8403900070843c0d031001000d003030b003a0940840f60000809240e6602181c0c4d66801031080f592202824060420b101c2504108 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 596175665 1250 596174415 596174437
    0x11100b04021c0506030610122d140d1b11030705090705090a0b0f0304060c110106090b0a0501080c0f0a05360301050c1b0106050a0e10080705010f0c0606051507060e03 73
    0x90721549000ca006883c0c49540e03804808042780512402c1515114024840c0008031076554200600003160036003030041e40c2c0780640d030b801c0c040b1030b4055480f102680700c1c400f064000d0280086090081c0592010450803000d400c000d44071082c14106050041c0042d04241d403a10310521400307402050358801d4105483c1c1c0d10000c8441e0a08580340d99440703401422445584004003e111004003520080900904006008170400081c0b40c41041c01849406a900d4008505200007201400040c030f540780300f1039a43c1c0206806103610740860450440795441031704241d406640b07c4d21042d447c060911884035210007500c08444500b00710f4001810b00382c40b070407264041c8080c800c0c0403250020001a03450011408681e0000880c3c2d5215000030302c1070711340707608114500002503003002a0a400382805c1005414440010f007000c51620340001c0c98031030b80304003c8040106c40482042000807640003800680030040124050329140340120146030000801510f0550402681d140b41074001b000312280003640d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 596176915 1250 596175665 596175689
    0xf031109070c02030607110f03070c0308070510020d060e06030d23040509010602031c09020a230406240c2a0e0115090611100b04021c0506030610 64
    0x80002041140e01000744014140071205410800580d41440b095100388010303140e480c2c1044196070920318040c0007801d1015564070801498010400e40a2031800712070f80600e29030340e500403a103003050070003809400e140310782c0340046541030022a440d00200c047d1900c61201034040d51354141003555648034002800082425200c50f1250030000840142260100101ca42e10700b036901e402150012000342d01540060304046110811040007507405a8421002c071003e014040c21500060459001c0e8440ca10085041e0004120203125100001c201000010001c00816540b0b051000409000180e05509049003e40312902c6c0c60155420414560700152440310240440e5404850b2100304050030744211103c01e000604241c0c41e800c0c03980601618902d040f40e40130707540300160000d451900203e06120540e0307a01c160b00031002484001c4a000101c01007030085050010500078464160340030403440e102c6d22070400c141c0080d08114000c507803d50880e225941d4500c3c060720505400e01500c1c1054070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 596178165 1250 596176915 596176943
    0x12330218010f1d010905060c060108150c030a150305010905162c060d02030313060905060a08070e040b030a0b01180207080d02070c0e011401080a02090a051e0301140f010f03 76
    0x2501c804043d950740044c184100c842e070b142d40001e030154115601400d50365005500600401c0740502c502c10208950000d1075640e800d010320181e00301d00004144c800c105958005074821625a42444030003107070004002c03c883c03006030a0141d200c0340d180340c40c404404590030b4005042d1800000d00038010186600d00e4011a03c11301c0c145444000203000e03a9406030784a100d0b000941e90500043c00480f00c00018450010320b80b401c0684817800961155114070f42c10b020841c03150350004030490b8080395900e4004001031035400000c00502d141102030b0741600c00c1c02d04482c1040540d10b6500c1c10323554800341c40070500c001c50309080306921410400405907801440313104800915a0094901d0510079480c0c0214640c0b21030b6a1030751010241c6c0001d03c4c0c1020340e0b03000707142540c2204800385c0001d00c881040d850228888086015503115105207070050301040904042540b40c501c441615004c010001c1c01901e410407018501003500f6198502106003190001400c42c211200c41000c6980c03010700003034490b03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 596179415 1250 596178165 596178197
    0x5090112060b0d1e060c0314040f14032b0911010c0606151d03012f0c070605091905030c0d0503070c06020303071812330218010f 57
    0xb0414031070b10342100428124200060090301c84203d040305600e8900b5001e0040d040100a8521040d102002e061810035000720114040c04055030180e086048040000b402d441c02814115007140c0b50102c1c0d0102003280080f0401c2240e44500e428025510080e804100050410888011800013810010400620766480d40a901ca526403036000e4040000c0d03807a51540c84405e02d01c0c40041d910b0010fa808111045015100303c030900481d5000d8000300082c024002d1402d909030420944810101e00c2d07021154281540d0f04200e605101412003694800b0756600d41c0a4000c3d004820882d10403680400c400312300101c00c032807440860784024001c017120241c80341031000001c0302a4080e60a07000400081d00818070311404100201000d50081d66039141001c0001c01c03120b4440390b40010091400410014100e48005402d80c494100021407846021203050844099603507560200380e00c0c2d1048450081c50780c5038042c02080031440e519040c0d1440c400011100e442141c05000c020a260260f560214 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 596180665 1250 596179415 596179421
    0x1020f061e07050d06031a130b0103020f150d0b0f090c160201050403020d0c0e0a0c0804020f0a0f031542050a0b07050d0903030c1101021f050702070509011206 70
    0xc50300b80e00b8824540aa031003414402d48115400c141c0d0802e020f508026442202082105e0744852900002004480785c0e40c0c174941d5203001803001a20030581160205410b40c0c0d4041c103500d40c411f0181606580382142a1954043c0000517030031403240303c40e007c001442d801c21000c058818070409a0b290b140c907081d009601030038030700c0303d40c00e0341045030900c40400161281d5440c0309140f8081e010310b200c1d1503c0d0070071000b803a80e002802400914107140030710f0491900035047c2ca0b00154120340000b46210030502080300044e456000c00c40c902d8960b4000400e2140d0224001101d107441c2400744190907001c018040140003181000b0080d0006550865413921180100c0300d061210341d540130012a41c800005400c100150002c009050f00010501e040040400a02c0a145414240501c2d841d1864a016000030146580504030118140c400c0d402c681c824011081580201002c94000710b01c01c20101c0020101118254094410000041500c1c58040c400fa4121800e02c00a1407102c0d5407941c620000e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 596181915 1250 596180665 596180671
    0x100e03090319080409050f0f0114060a0e1f0f0f0305010609140d051605040605090103020604212f01141c0209282907030c06140601020f061e 62
    0xb1420b010321000c540c817151401141e0050141244201c49811320f02c0c6603000000d4103900a40c1c0c450182a808481a00d88005454200101d802c0c0031102102c900042206401900011f4510405803c103002c12160000300d414403141007580e03689180c4000520590440b0020300840d40800d014107020000090303842d60f003c1c454039001d02000003000301a42c034186460300c08480364941031607852050182e41428400d080042c9000c86400440794035540101e03100380700c0e40c002c0c4000b103842d00002c96003446807442e00c807191680c8820021100d5000146640b03a00020b10003080d2002c0441580b0a0150300c40d01c00c60240560b4290b02900c1c242d4584401010f4684012a14100d29000c2c0801c42c015030700c0700c60500b500100403c00c102d80d4103840003503440b100c07055003200180c500302814103007902580900500c01d41c0baa1101041d614461800c095854241c2c01400408150800c101414111044041d0300c0c06030100ba0202d071044a440400280c98003421101044007106601405203031714444658260 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 596183165 1250 596181915 596181923
    0x80a060c031b021f1a04090f050a0c032906040203070e0901080f06180a0f0f021315050307030b040b04060e072903040305090907031d100e03090319 65
    0x1400c1c045000ca040e80c00c1511400c0c0101503042041002c13918214400e80c082c00b02041c80341044000900302075804808444415640115681c0c3c00c20b0b4204442113945001c5990400101d842c00d04c0d45141548100c50701d404111004030b100100100c0051021070f039a548c5542c9a040c0c0001d61343d6a00501009400040c5420f040040114a1813843d44401541d0707030280040d0b00141003a041f49151883c601b0b44050014240c11928203840081c8210101d112030410b548a030b900c8011254074148182da411f031078840658404840e6107480144461a4080200c907100c0c50881c402d4a1f6858013010349643d8203200142150008a0004000585101d0703441e5209100b2000014441c0452144c946040c4180c0c0000c2c100c83c40c02d1810445130140e29000e0031a01603111441d07403440c07034036a40c000c08a01805010300c0c09100c0d201c0110315203a000340c100d6200300c03002c40d601607048003056942640d1050710700f1900d1000c07850b0071141b40c0109c8003c800c65107156805001840340c0c00d240b4111754060795950b030742a6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 596184415 1250 596183165 596183171
    0x36090b130c0e0d0b041101110d05030a0f0509010f110a0f051c06081b040911042f090a0504051b0315090c070b10030201022a19080610080a060c03 64
    0x42e5242c43c02502d0300b90050b4246502840c20b880c00709610b002c44404d0a042c00b4560302c140150890005020a40e19440d180484c2c603502d0308614080603181040114070300c0c905000400c4007030340c01503005074280c25240d0402d0000c2000706c0c0325003005124400f0514001000501e500300307424054402800c5480b940324007040c0081c0d18050510441d045904038088681002c0c2100c44000000703080c3c598500022a020462401035503100319000401146507070040307031102842d036603504180709602800b8986c4155483c035100c10041c903903456400300d01005d100d00c02914010606080a1040d00d02c2007400c3c0c03881142000402d0803001803034000810030f8220f005002c44400741a00c1c0c1e418050301034503040c60201e03101d40952414090314580108203c0d07030308680740f000b000581e0740050000c2500c0d0b03903400c44660382c41043e5081e00c1192540a42c1c0394002c03480341d011201001605140804996143c0b0580d583c0341c071440917030040e41c5c50a101d901c12711351015100c0b4012542c150310603480c0c484942000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 596185665 1250 596184415 596184437
    0xa050705010204030f031d060304060c02011d07051302030105030a0303090f120c0b0a092d08070b181b01030c0e130b030f1f0c36090b130c 61
    0x9400e81e84143c108480c1744020800c1c0301e04054001c03000c443c0c0049144050541803454501152180c00000c20180c583d40d120621403910038000c6d842250340d0250901045401d1400400040e034940351485002c1c081c0c0201200304019018510999050301c1c001009410740c810300c1e8600302d0142c607144d6030680c0c82c1c0c1c110645110014086010a5184143c0d9454114040308242411280c0e6580104004a802e0505d10030300005026101003000800d02c031341c181402c55100c1e00c3c001c1700c0e0300402c400c028483c10001410b1002c1c019584450b0340b0494a0440e001141900c8d030710036503240d1040d204501d410b6070000c50095450340c0250030800807035025161440900c6441c8000031680c03600c41d803810302d45a5541c1d86d4000309090900c440049246814002c0c484400d00405e090000041500300b01078a90765141200c888500c02c00e003990302000c0342c10300010000d00241c800c41c4466450141c0703189540f09443c001400b0001809907041003a0003c2003e000d180c2406886030107080e0031a142c90400607050380e1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 596186915 1250 596185665 596185673
    0x70e0306061215070216170307230118020f01020a0b070c05030d0c03020904050a1512050a05060414060f0403140c010f0c020d080c030c041512062309090d050a0507 72
    0x803c038811a81e940c004c180541c0a08009524480141c01281e000d0b04002c2447c0c50180c000401c4900d8158003440c0d581d580c3d02481001a510301c01a6404202c035400c2c03981c00c9542e03d150070803000400d80210307044002000d100c001a03940d003a8000b03004113011112400143c3c034a000302c0d40c034845d050044081c2c82c03400c90b07205180c200712402d100301c81303010035408603c1c0301007801c0c24030410380d004010100c10404085001c410303005081d810f1040100040144580504101040c451400215401800c448040c101844c0c00319411800c040c2440d080e208038800039942c602c103107481602841d0103480f8907111030700035080f440781648102038850241d07480d003010756400340c1c0f58801e01482040307590141640340d42e4590300801a680c090007442c01e210090050003003448949048800b25100c030521101004e1400320305a0700e400b126107841000900d012000216151400080d00e5104138400e640c6c1c0c825120402089011314040c4d40031540e0ba030100342111416806000140001401410074501f4021b0a5903 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 596188165 1250 596186915 596186953
    0xa030608060709080114100902090d0606091d0a030f0807030b090705030702120712052b090c05040513110a0308070507081c0206070e1c05010b0108070e03060612 71
    0x20703000001003541c1e504002c0880c0038418116502c204082900d807e040900a1844200d207500900041e141d00042d40b505c10381e01c41440702100359100c6014000e085da0b45014500500c9024103802c0071261070011280502000300d0b1440d5456807503258041e580c540d070340045032840320007820581030640e05c0b1048540ba43e10304941600c5120580e54003940d9252150009003425007070070303040080d15024010440058031112a86150485602d08581c480795015401600a5650740581e014040e04524039051411a504007040030750040b0740c09001c0315a01c02c148021140c044421206c40346000d000003000605c824200c0c60340c81c1004002e030f10341c01e8407500d460020341d204490032903150380401410882020248a603207000301201500c15909d0308c00307040c084e458100003001c520821141d894000407554516488480d401000c9000d056000541e241407402440c00201d9180030500c1000001c2c00c180c46400440048040500074050a0301ca0703109112100c140c00760020064005c406005180300d410700c3d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 596189415 1250 596188165 596188171
    0x10b0d060b070615050d020a05060d110f04030b0c0708070b070210151e0513020f0409060b03040506010b0c19020d02040c270b0427050c0a11030307080106050a03060806 74
    0x1900040361400246103298100c04ca40c820340c003c2620081500160303a4086081045550607a4400e5491005408101c000c049141c03200c601154081405c0d844c1c0186840600240c0b4403403440e08202da20b40d040c85092901030b8203001032400b03030100705500000301e00d0005a9041030880c011103418030000c1306000203407a00890000c4040726040010008060b1310210040a901c080c44048419401c100228540340d1491510340318140e000260302c070b13400039218100e400904003000c0400101ea142e0315600c6044d030055070150364503c641c50001c41d01e4101c840403503840940c0304004001003440c51454040c10000c0d640d041e640141000921001340c8c60318010200308691036607c501c191240c1200075500c0d0b03185901101743d03216918405200503204401114240c0d42c1400d41c2c5040035021601460041d50740d504410403d81c1080144807040d0741c1e800103042501c0840e118900b041000044456880c0812185c400002d511140100b10b6980034400401c00707646640303408900395480c0e0750924a880016 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 596190665 1250 596189415 596189423
    0x20424120209240d0f02060d06060e2d0a09150e0a1b140d14060f04020c07050d140303160809060412050c01092001091706010b0d060b07 60
    0x20303440008519009500a0340441c0b900d0781c0314075521240100340c0791210703602d001c3c07809483c03040000c07070600c50201480c015980c0e008280a0741d90054907804005080d1520031034001c52180781021000e441d242c201520803225844101028600f8200880300003e0800c1c0400d03089003825802142300301075805003c00351a900350f04c041c0c040b8034040c1c248803a040010408004140341c1a00310000e1490700c6e241ca603620f0074502d05541c02c90041020800a03203c0c01c400068158903295100041c1ca5503800c4d25885071408461000811484d0f000344070a03803040c00141d070015006034005108501e480f00158074454001d80c64503501d40011120f0702d140d640240c138520316815140d4225404030f544810503d6000b030b21400504001e0030581c1d40c0616002c16070001c401880b402050003c58510254411a1201c0e0001072400e041c118000441484100003200d0b03a000481c9803201080751006207407e9810909500000c0c201a8a03001100c0c06070b401c4043c44844a60319804001646c842c9500a00351035805 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 596191915 1250 596190665 596190689
    0x1507051606060e060118150504210201080601210c05070512090a0504060503030715020c0304090e0f0d09060e010e0409030f0306080105060f04180c030b0a0c0318020424 74
    0x1401034a0a48400c010560b6040010a911071021101050300001c11a1f890000c01c1c0c0e40344000000c19211400307140c0014141104d0000d4480e0341d00100040b20b00c80d28001e07280c450791502c139000112610318041062071041507000302e9040103107003036a020410b024a10b20300340e0b0520034030f40c0c0c503a401d01e0050513240e190540080b60412991810b1047c14000b084125803c00c1030502e040c0101e500c0b40a5114041c1200c4184003034812511800e80482c0e2000b040907064079942c82e161480d85000340600184800c8521420440c0105454002841c031185d0036603440341d00c001407905100300c46101c40894054104a00440304500c2038030b4900400c1c040ca4031985a0310200c00ca00354005003200c0580d40107072580d0381030901380f06d000e0301c409200d507003d500e080e80c022600202c68010324251586000700144100c243c0d80000052110813101e8a01803060174030140710510002c07000b2029200001200500e40880c11031420041c90f0aa00105001900d011845085182c0e54413040845250394031148030211 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 596193165 1250 596191915 596191919
    0x15060b0a08090f030304020d12032021040b060d08040504020a1205060d0b0c1b030412140303070207060507020316090608070501020f0601050409140616110f150705160606 75
    0x18841c5a5841d9243e5008505503c1c0135000210a181500d802805981c518414240d05510903000f082002ca8480340c911a016072600e03160250303501090540405035101100c503441c58414090131b5020356003111140c80240c85003400c10081182e01c100858000008010028154a0b140003601e00d00b0301a03203540d804041101c00041c2603400043c02584a42c00c1c4810349400110b40c1ea541c03a80000c2e43d50b8a4035294200b80201c43c480c04c6100300898110700c03004c10f0000e050302d001290407824a03c2044441c540c07014001c81c0c15a240002d440100c09a00500b00c00d00500e80b0a00c040e00003280000d003210301074081c19540070b1002045401610740217444882c28040301c0c208004002c000c140c00c0c4001e2495070138601d407564a80e8018090184200e403503031000800c1c001d2240c80b482c500c0c40d80c40182c031803e080142c900b441004401642401240403485800c00903400420807520038560744d00039087c50b00d1800c82b03100c0703040401010001440001d08c41c45204980c14104442e41070b20600e00000c20034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 596194415 1250 596193165 596193181
    0x20109050909150907050a030609020f0109030f0201030b1c03080105091006140904060312030213050a0302010804020d050709150503071e090911041416050f0715060b0a08 75
    0x540680040d40540007a00c103210000000003901107011600403065002d5440d41420b860a01c207183c1d1041e03522000c100000710910000d944244e13483c41c4200d070580150440c200064800440038400a046000d00c0900d20025500a4110100c0000000c103100b0340c2c2c8100402001c244804494180e000031a198014407050400410003138200c1c001410080c0180c1c0741c01001407520071440305135000c0c0c600200394601c0a03100c540110000d50b0b031105a8061540d6001da00600075000109007001c100521100050281000102d14042d2501030352400081e0340c5540078000e1001030321504581302c0c030400b0000940c0007100c0c031402d4034400000312842c441d1468401054078100301a00180600302500c0700c81c00c54049005240b008130303480a000440c0a05d680e04141d03802041c60342c4516003050614a2220002c550b01000a20903002c0450b4003034444805d0310100c4050140f401d514248032410459400415081e41004c050f0a00b21500452404e440f451682c500d071704203588080c041a41d130b806000b01a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 596195665 1250 596194415 596194427
    0x120109050607050f04060c05071212140a05030a050423010f290d050f06010905070f09050109120c08070b0304290705072a05040608070311060a050d09030207030201 72
    0x8907049140c01d60902c84130b40403811641c42948501d005000d074000042c01001410300440b0f0041c00000e80701406904181400303505d080c4094103120020300000c400e2500034064606450368600540c3c0ca85003141d4a5a2202000341005882500c4540c031102c1d4444100100b1340d054504148441c002081c03002e4403d080c42e082c0d070360480c40b102803035440309445044046000340344c15132848100ca0b0104044d6450608900b071100290b1003c40c2800f42000103d18408250410760140003255121600003c40c20310072505e00d16035001e00360001c0d4020108112a0110010b040c00490051a0405141750340d2030100380303420029801f440c0c0c0c0310320200411042c885090020b103851004840000303a61025440070998080340140240e0034010f000c40c4800500404219914003d981c118186042c03030080a14401c00c12180e10489100b1401d0901c0840c15200101d02e03034040700d074005003442c1d00c03460000810425400c00010903042060034010010421034070301900322078a0103900504801c03400e5000040030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 596196915 1250 596195665 596195671
    0x307061d0724090302031c0c0501061d060d1a10080a1b0509070909021b06071107080d0e0f010302120411090106050903101d0f01060f05040603020a060e0307051201090506 75
    0x184910a00d04201681b4041038200d007202107102c0070044465082e0f02911030446c0ca0102510795868440041480314001e440600140820006c051050341c540d001c004100d101050003c00c1c902d82c8409441d8089040c4107645d410080e011003280030507407164244c6140001044c800c2d62032804088845071f0a0f00031000001c090802610170905c1403a140102400e41540361241c0e12045a0000d0404003c4400c2c0741c4664512400d03500f0f40301d040c10070360b000404003c490403c2c031840380100300d4001488003002074031001406558503404211818801004130500d8002c107003c0c103040e002c2103520440350354a8a600d101e140318034031105004450350709110b02804160042018060104012222550001000d0000c1031006401103014004000542e8402c4803840308860340d4410b00d400190480c006401803000d41d41c0d400c54002c0c841e80c1e09c1c0d04100030f881252001a4001a4240090014511618502e00d1414018086605169407a80821281001e5150b008440e035910703040281006818001aa0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 596198165 1250 596196915 596196917
    0xc23030c0610081c27060c0201021510060e030a0c080304080c151803011401082b05030f1b032401080103031b020d0503031f0b0c0307061d0724 63
    0x1c40c1000d504401002d5540c10a10041801040c942e030780c0e10b0382c82c21101040e40c96004441740d0b50540e924403002d8040002080102d01500034401c0c045100e41d00201010312540410174401c8550b89090007c0e20a072200c0302059030140550740d50600070416105040780208407040007141d80b41e1a040320142031410311180d1034403d0b440f960074060b0303802d409000d030380e801c2c49402e80ca102c41144002c0028010003e0703803144c0c500c1c20364020000a400d00d0128002100007120900c2ca003503100d20f4600801181107683e02100820418004200d824800d06500d65011844020388200706070921120340796600300300c50885c0f43c5101d00c40c40b184542c8481078540d8540d0820700303043c103465045580c05880070005000700c828103101841171006560720f02080050454009003a25070360309005080c521034442004107400600a04034000a660b58041c1c22104140e078064095800d000456440c040a486100e1004120480360103035100141130502002c4014042c40740c84543c0c001303e100011844000030002c42c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 596199415 1250 596198165 596198173
    0xf06030606020c0f1804030306090b040e1e0307060e0a0606080313150e0901030609061812050310031a01090e010e0c04020708040b03040c08060c03070c23030c061008 73
    0x7590009502e1060703500c2250310301c0240d0b691a01003200ca207004a44150688940401e00c800e240d01907102c031055824681083c000c40b0414014002558600d100b52807107580703c4151072614514051001d4030340129242968a0f181841d140c03034003074403082d01c1d0b020055002650308400304401e034840c0c0380c028410500518108100184203a404c001a442440c00a6041d0a40f0708038039031090000000c94107000700b400c3c18030358403418844001c100c410301c1142d9092600042c542081c0c01402c407407a52070f07804042d0b002400d9800f5002c4030f240d040905034880040d405040072000414a000703024a0a483d03040080321307585003024090568925800c40074041e49000000c1c00c2c121400302c1c103501801029240581c2c0c0342040c1c502a070140c450b59000c6a20b0050101c1400200a11501e1000444035607404444d1651a510820b15036884140d03954008244c0c16040c03100080c40030710164039a035024103040540c8500410b0440d0640d03006540c400000c2d04035008010f801040c01d007044014181d660024 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 596200665 1250 596199415 596199419
    0xb1806010c0b042a090f050906070c06060f03030203090f0919020f040504050115140a050d0c0c080309070501021608030a1202070204090b06100e060412050c040c090f060306 76
    0xa002452016005403480702c8410006013404a41d10102c074206980a50140c10200e581c22100801d003203d02032100f0103410404e062240050303601070207001d600403101400050b125400152480e01c1204411180701d6101c0ca00000d10385d01d01c501010007140260061039446a0050800036a0000c44008502c81c80d0310340244241e4007580c843d4030781c0400c0c0040c401640e070a2141492040ca0280380d21030399019051100100e400c909074056003107010000d858084001c980100c1d403290b6030058000400c000340c1c050051103552152504805c0d03800b01281040707817101c43c2e00c1c0c880c4440350b40112003142c030380d1307000000810165a041081c5e17070000441000c0d804186040083d03540d102d01c41c00301c7c100c003044261a1200c55141c050780c100c80324164000c01c00c00502c0902e01e0b10400c0d000040304d01c1c51041e0803190800c44402d000300f010000000000f451135240506040202484d5441c846c01070700d06210303485200c00c4a07107951040340c0d07855242c1c6e1034201034030b440d02e211303512014060340081c000c050820f901 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 596201915 1250 596200665 596200667
    0x114030601030b2e0305030406141602040c0e130506030d05030c0f072d030806060a0903030302130b1204060c020307030e040b131a0f04060608010e060105040503030d0b180601 77
    0x8200c0c0c0082129040130890107249080000443d800001200c04040c82100001080400002001250020307210052005d44020358015540540c070840001d00141407698401454141d0103210316900a043c001603265881001c02c0800701103070181c0400968400521089140c100449001c1401e00e00d40a440e601e8100441503c1e0300031912120503452021600b04100007a80b012003150541c84955141e908000c18040d02240d45400010703000b164201003c034019051003400c5a126006580320340d4012481c60f80c084000358071500c8041c141c1d44a44c01c000c0b07041c00c500e1005103100d1010260844681c00c0c5400d02401300c0b00900580c0095500406c00d000000341c11486000200d40203c40004440701d2010100300722881ca83c3e800e4040380e2900342d001100c01c1041105080100080e980503000410f40c03814081101e045000310808100c21200401c540a060000300c3e41c060010f240c024105650340002c207145401038544044820340381c030808449400d0440c80a031016180d540340d4841c0c2d04223000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 596203165 1250 596201915 596201933
    0xd0f0c090b0903031b012007150902030604020d05190c090f020405090f1302060f070302070501140706020f0421050d03110307050a0e1c15060807051e0414011403060103 74
    0x245178402e044180c014501008081d4400b04410102000c1042d2803a00342044da4030300c0c3e0103210101d42c00305a400000c1e803805207501c01c0c0900558050014a4640c03559002c10941c0d00703450a0480d9184a464000807030001d0a4035403a400341c4c030604e1000c803a14200800d074820b59207440c081800491061200b0080c40d40d52800d42600000708000007e00c41c1c03940020000081d0303103940040d401c034100080801235100d101c4014000300340694295941591280c00440714060107106800c2c0800090082c80f0205025600604a040607140f4070340c9020b41d103c40c02803411102108030004105456145400e04c40c041c17100c00b4480c04949030410202850144020b0329002c040d00d58000c2180103da240c090302d008188014550300300904503116800c10038801e4014a1140c0c404440303194116050020050417030003024184c0b03aa00016005450901c0d040c0405194400b0149100000c0705011084030b45075031041c201145500100c05640d50304040201800f00d9494a145001c2d03882200100042030342c0d50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 596204415 1250 596203165 596203177
    0x9090509031b16030305070b0f0601020d050a1806200601030f0f030201230a060602010902181003120e040c180501051309111b071505030c0d0f0c090b090303 69
    0x460300084101c18921043c6071107a0000c80800441c003400c1c0100505400c080540750f03a502c903c8802c1c1c0d00355280c00b2042d80d41402a02e400c0d000d40e1149908011643c091005000074015504e000141d1080d540e07a007424544840e809600840d0400340c8a4002c218243c0100b01512242070081019501d1741c1e07110700f40940c00d09c4020f0410300240d5055030401d8400c0d00429101007071940c41d5401c640c000b4015a80128050351400d2140d46041c074005119401800b80003d11a0020002604009491003449074400b004001c0c8103043c00800c0b010000502c035180c051a0076a20341d6a83c01451f90303e5083c40112900300703590b1418003001801c400c4031180640f2000003614000c0c40c129840384001c082a0390300303a52580285007a0750810313441400d40041d003409001d01852000d10212094081c020f02078483c00d1034098540c490040c041a600414014001141c014120103222443c1c80c41c080711a00443ea10302c3c00c40803800352140d079080c041c2c580c00b1381c0f00c00282c50090802c501c0d0844180019a40348210 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 596205665 1250 596204415 596204437
    0x70b0307050405030a050706030608160e0a0b121b220f1b0804020315040f0b040318080f0c030d0921020a030f0c0f030b0106110f1204060909050903 65
    0x150428031900c2600c008100c0a0704441d040174540c5013154413014030340103090000c0c1c030b040d00000f072858000520b09424841d407203441c01010300b029100c0c00d502c0302c001c00c49058144c482d8030b8091a5240d4440150b0f000e031030070001c8c00034071a02c0c0110b00c11401c0351605251003041c1007038400c8007100088611640e41050040c001909006030092980a09420550340b46000d004030300180c66160060a2503215030700c200c0a60700031080701c81c0700c07006a601c10f4170042d00da42510080f10000072900e0394903542003030003800c10340124201c5044141d45100d46811581d070380e4004900b0f003003450104010340118440114003800c00340040b03600040c4400c125120b15050301c00780440c441000c1d40301500000e1441d8004d4101d050140e280c5c2403081254030000c100b140c0c00c03002e03160009200000440b410381942e900204904e0964649101150300f4080301380e0115040c05103444540c540c5504204156183e0301516000d51124905a409440029541c1c080f1000908001c01c0102d040c8021003100d6089d505 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 596206915 1250 596205665 596205667
    0x606090606051b0a02120304031502040b090111030d020f0c0609060f061e040504031e0207030b01150e0924061306230c0105060f01050a0c060203060310020f0307031409070b 76
    0x210f030a146180034007101020f5080a074000e644030000e4000700090003581c5c0106040e220810409174803030100d2040b4442c508980b40f052107182d44c80c1d84250410040c40f10f04204403400c28564032072100807640f08040030f1452a0300090041c00c4a5000e000e001d40c03000c0098040d003118a480942d42004020003029140b2521000d111640050304140d042c1c480458080c004001c68030342440c0c05041e80c103410b80412803030b0382c80c21400043d0910014401092b030390f01c814040003a91030882d51a25041c000d02c280c0381440708211200c1000d4541010036071082000120300c40c40f407003071000d4583c80218505003240c003800c001c101c0c2d500401042d10f0403004031207442c5000020b00094040e00386d100a2062241d10540e000028400f1220505402c010b0013850100e80c0a00f4001c0d000700103585912400c110000400c240d05d12070400301d0295030180d0351180c03010b0269804919070f01c0e64101203a0000180c01e00c001004001d00c800b4070307803510802c291031606241410b800d04050700c03d01c0d44d0300380c2d5210f58518150 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 596208165 1250 596206915 596206957
    0xa11040b01030e011a0a0e13031803050f01060f12020603010b09030f0601031b061727070306090b0907050108010b070c12050a060c050405060a1101180f060609060605 73
    0x40b0a81c080004842040000c0103149103541059050041d010022840342c4040c40006c103505a0000d0094001d00880c0e64090310001035560580d00c01d5502100155505803005001000c160103102d100340241c1c43d4000000e0003801c02500d43d40704005500f1141414074490410401a11a241203a0544201200d803a40b0b986801c030010b03242c000009000d200a018040000082000e402e410183d180c0c000003129070003c1d140c031701c1265203c0003004040001010303240032491142ca0a552894a02d648205400680c190315034440c2c40d240c055802210625a1581142c040c819000d04954100310b84201422510703107407000090a440042c000d1410003030002441100300550f02101034010a1000401d80300b8002c1400c096841c0c00c204581528214200108030113000c0c4107200311020b5402c0202100d06040d5400300c00ca0325031001806420395503590384005410b01105060107071310031384038444001240c071403450084252145540200c0380c00b814041c040c0032194004090300c03141110800d104542e00c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 596209415 1250 596208165 596208167
    0x90c08120d1503081605060708070c2909070602060624181801091a2b05100204170a080a2703060b0f0f06030601052d0403060506030a11040b01 63
    0x1c0c03a203a0000b0160040020445d59000c582c054000266001c1c00c1039980550310b144060328581700c2100e2240000d031854852100117a02c000c01601c03455040e885031100c0c0c0400c1240364200110035520b41d81d25900c04401004000d5042142c90741c09041a0b40404184c080300d20304940ca2442c0700d100e074074054000f2440f400030041e440003c00c10094000c04480802d20050038005801000303025406085003040850928510340a00b00f2000000c040c0c07424400d4103034031110b1109507201c02ca41c591204560704005010450401c0200c00d500110030f00140c0c2c49240c400d03185000029500340100ca80c2140c140c1101081b08601550620450f50814056590045501c071070742c0c50b00300c14071000d02d181031240802404a039a110008180080d81c80c199083c5031301741080942c40d0342d0303921036502060810000300395510900150042031b84001101c86285d03a100c903c001c440b003104200c001a803c0c045030810a1140500850b50060000d8015106d5010700c0e4071255a84915003903401d00842d107841801c038103031b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 596210665 1250 596209415 596209451
    0x60b0d0303020c07050f09070807020f03120f01140904021003020d0e011b020f030405010c0c0306020c0601030b1b0d0c03022b1d0a03030b010e0d0309140a0501120509070b0d090c08120d 81
    0x2003303145003501c0c1d40e120f1000450301543c0003035603886e42d1b84110100126180c801091180d803000d0004100c030800740c2d529404c2100702c5080b41c1410080503000d000b2001c2050450042d810100c580c140042001004c0c2240c21440500b0300c00c50108641c04400000301c1c0003808000c882c240c41081c40e140c0c0c0304407480e00304040c18810542c03004050340d20006050110b0803010518906a80c0b050840403215100c1c0c1c520705030100f0000f000d03460448810400d560790380059500c416050340482c240076080c500410781125092a11400c3c1103618007010901c40780801081c881da070300361030034000b00e03a102d6224428101d954404101c1c00400f419aa210f41c55071681c001d0807440282d2030018409982410740b850000c03c202580c0c410910b00c004041809000c91a110031040180e0f20107079101a03402d0107003044070f0701074100075184204500428801140c2c12032030070018079056011a00100f01002c0e54500040301c5641540249800e03000200a110741c2c4203c1000c03038070440101c8a011810418200740f0310b8078 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 596211915 1250 596210665 596210683
    0x80408070212010b01020c01020f0d050d060305010507110606030105130b070903060501060e0f0402091c06020706110a020d030c091205011b020109031101091707060b0d0303020c07050f0907080702 86
    0x1104503030b100c0031480c110054020b0707070800e002a425a001083c02d5001680d81e003000c80c080264582101e011148000e109001419602c04e070086c000c54030aa482c2c5030b160071a1000d46000c0c00284c48080000410b03042004640c5c1c00440c140e0003002180b802c495107144c2c0004281c001454204c0c0e82010030b5000e84242c003203001441d0844c07001c01c003c0d690303180d0190620140302005405103480304c03200c0d04039150038425101e00c41006022680a00070248040283c0110f00c0c01c1100c00940c240544404205544200500b500036400350755615413a094002c0e140c035220088120816081064081d0700c0e03603114444008640c0c0c42003900554101901d8964050a00c001000301c0d00c140c43c0035038881c140d5054000041d5103010341c680346802004030301094240e81003040301400310600040707103c13000b00b1210020300a0034001c83c030009005c008540009c0d0300100c1e50303400f42c1c00a50049a40f000c60341d0180700e8130000b0101283c1c2040c200881034041480108010205414400d0344000a00003500910030807031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 596213165 1250 596211915 596211919
    0xc06010e06030a141e0303040b0f070210021c0509010209030a020402091311210907030f080d0c03090507050d030e061317060f0109020708071704180204170d0507030804080702 77
    0x4c11141c8480039070742e2922500340a9540da80c110340d00742c12a25001c0101c0303004541022002000b9030b10740c1c0e0010400440034001004521440d00070a103802058800703007451100e55001c5400012000d00407905a40001e00300107402e91040101c21610795000410040300da5043e034000d42c60301c2403140007441c400311030b40c1406005814150301c2e40c00302d1228002070010602d407015004003250b6001c41c2c1c10300108225410b004a1f80446d5062012804c0e0180820300e40e40b04808140c41c0420520b00032060b129100c1600b400b00780c4440c01201000b00c20300c00e20002d49401c1c1c602e604842d8481c6c400400c444481c00c48503000307001c00684a00f61101803410030b4082d2034440401000b034881040c0d21075440c00100c1d0741903200029040042000c2109008460f40960840203403400e060b001e403210fa402040b0b00030b112603141c50030440001d28501c1e90300000b4160a42100050315103203440442e0710380400500c107a01c407540118a0350341900c0e401000b99411103400d40341410840c0e17905c0c0707480a441c2c82a032402039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 596214415 1250 596213165 596213183
    0x902130e010603050d0c1a100312051c0b1005180628031803050a020c120d02010b03030918040c0503160501031409060109023403140c06010e06030a 65
    0x40560150005003c8903c01c2c2c0440b00e04010485040724040c8100000400ea9400360507010145400050065000300ca040582d80d081d503901d0b41c07601348545500b418003000c85c00204883c40c85030b510008115820340300c1c44040c09001c1a485c0014450000c0b602c1520134000003180c08903542c1e1449a080c150a070010b0595551100c030000007248a20114a8400c0ea101002c5981c02000d4840e01481d440b41ca8003007460400b0a44540d02075a10307401440028085100700c280c0c1240030769850708505c0700c84000368050602c241288000a086d18020054540290b03c00c00072800c45403500225464440c6070700a07406099182e610307200034111420350105906100c0c00c000f0341c094201003503078501216002d881c200200c044041180002610490740507449421143c01041000260b8004200c99201001c1107011100403081c80c0b91306e4058402041c1c140c0d4801c00c0c0034004c0580002c40304401c103400303020544c10b000300010801d941c0c3c00140216001030521030b0104260385c6007003080c540d42c558048008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 596215665 1250 596214415 596214431
    0x10c020c1c05010c05220b03010509060d020d0b0711030c030d020f040e01091a090f070e152113150c0516151d060f28320406090213 58
    0xf070454000c0c0d0300c0a58a1340c2519041b140e00039600c82c544040714030310010031b811686000100f111840d8000d14464000c101060b4801c016520114a1051f003403240080407524200000000c00d40041040b651190380c3c010483d0b0500410000240d4100c00000c50300580c3c1c030340381401c20440d640640d9000454810840001281c0d00c055a007280300000c20014802070150428410840342107001d41e003446a244041c030110b0052489501c04580000000e00a8651403800700d54001055020320340b8030b008540326102410119030200b4680d80c0000000c0d070440c2d14200c9a84aa00d600d558030028011040d5030341c0c0083c52800d004405840c1904130480f950030544059041014203001c0411208039114074110109040301e410b180d48641d110710483c02007070141c3d1001240030f103181d0042d00c40040300c214040f46590362015451500110350303100c40f001c6210200d581d213038400c0c4454201400c601a81c1710544131b450b42210103103664003903080000803420600300d0000c9031071002070025041040f810310343c0c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 596216915 1250 596215665 596215667
    0x180b2e08010605010e06030f07080c0f1206090106230a02071223061003060f18050304081207031205070c0204020f27060307050c0c0a03060c11010c020c1c05010c 71
    0x4441219002c1c4c91780d41449a040c020400144412104851640401b10120307092a00c078007580e5910000300c1d0760a604e1310104c0542450290003040f400b10502146004104035410120310300b50041040e03041c0405000b5403031110401d1580000c00412101c0c0011500604a500c00c000c52401024a400d010143d1703449418074548002420680545000a003510f03005800c0d00010340743d10603c4064811100d40707045640c2c0b2005000103d0a048070700785c0303d00b22010f80c92000101d2400c540e03c54030003159100d00c0d003d01c16007000f14606c08449143c0091140703c010940042c116042e220410740001401e0b83c421b0b00a0361418441c480280d00284042440c4c000300c444000244910040e4003201d00200202441e80b94001c24903a911310b4000d2805e2000c01c140703c0c01080030346204038916041e64407441c4a00f0108810010705c1c0d0007540c255441c0c404501405030070181d03400c4c0c1c09a10600034050f1030385003100030b540c8102a02c40f160082d2800340701101e80d40e00e464007898001b680304009000100f11154 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 596218165 1250 596216915 596216921
    0x503150901140306151302090d05060a050412030903080703051806010303110c09060d02010c1a0a02030402150c0d3005090c0a060e0108060409050f0a06180b2e0801 72
    0x100b035000b84690301c04500810128405110540b100622081030414070100b07000184d000313108216080040400c1420001d5024400300f44100440680001e552405003016003200d20541b100f04245490441c00d080443d50089403e0381c041e0782d6040214054856608540384c86171402c400c1c40d898055040040304142d0310003005c40c1c44094010440c0d0910b444001040140d60044d03130082d600140350000c0d01c0065015024580446e07000b03002c0d06034480d2100b0002d003201b03001107c0c01c010003540001080b04500e0001040105180e00090b12410111903150031a56070741007020b00000c2c0000c82040118003030721001d10004000f4901070036080b52500c10f08500240c82c0c29141c6010500a041309800941407501c0003000702d442d284d45100c40c40f840c040040d1800c180103003660381c1003920340c114407001c00d00420142c1c1c62500c094006240368481800c0140440c0c0040c0b0f1040600d902030158000450407040d1403d42004001c07030030051104c1d14051403081444050508025031a0201c0009403160040d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 596219415 1250 596218165 596218199
    0x90f150e1e0a0609141905010c0503150d08191d060c0706032016020a0608100e090a0b09060108060f010b160219080705010318030504060503150901 65
    0x4048a09a18840c1c0c001403210900a4030000154081080d00001c140103400c03015845004607100303205408004860b904001e440841d03402088020107050040140900c159071a25201d8a041420350500400d45a00003403c100f01f68401d010030a50a400e0000a100300c1d0b00da00c2c0601e400c1243c45030300c013101030301140000f01c0c0000c4121080040a0140c10080102e03181104080040c0400604081e025001840c408403641e41002e4481080e2104081c408001c18510008100000e80b580892040043d09501508520304100c4034030300784964030b5000d15910040e60071822600d5226922039807120300e005c9030503002606107e024401d01181c0748002c20075605903801c400540c0d24981e104803150101407821712a46480e000200084c48807200c81840030402144010010180c501d202d2808003040c00355600880b40c2c0c2d40203a9000c1055680502c101b00c92042c0d0380c0c44d2491420b050341c03030140c118010740c4500018880000009507441414500042d00c01c00010004030717041d6101e480c0c1181080e051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 596220665 1250 596219415 596219441
    0x160209090102040b03040f110d03110615010207060e031207060629070b06010c061d0709150e1f0b03010603111813090c0b03060a120c0504090f15 64
    0x100499040d95040c02102c0c10b83d00319918851079511079640d4011250740015094031101549080141c1c02c1e52040c030022000c6000740c2d40c0782c0d51000020302c82c9062410240130380074000303000b030003003401d50740c002c2040e81c121100303030420352550000e500101c1c0c140300c25841503903e0101e000a0754410408141d02140070b49021000c4001945940903842c08040002c03a1049141c00d4244513440004188060466004c00d040c50710040d1401d199881d8425201c0c0d9802d000c481030f200e801d9035140d18004110705401030100d20360505c25040d0407204c40501c0101c41c041c48000e071028100042890010200398110300b240400401c04031a40c4901c01500b40d003082c0100c000107420401c1014943c10154240e482038143c2c16010310b80aa614400c0000c8010341014000140d500c5a0000780411010724554004040807014156030b46055001c000c0c822545030840e42507a954241c180300407034011036900b4251a02510000ba00c4075450034030444482d104a802080e443c0541e00b4103110907030b05d0f0030100404c015 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 596221915 1250 596220665 596220679
    0x6050d1a070c0812190203240a0e0c18060a030f0b0114091e040903020616030509060a0506040204210209060a050303161110230406120b0102121602 65
    0x81d00008603840350004001a06030703402840b51029580201000a0700591768140f96126810000396400603a0001c51341d448017000d4003000314608003a2500c0340c0c4030515003122810005424162211602c10010b0041c807000540440c009041d21f40440d0118a2960300500b11501c40080b4000140900b0034502d00c08070040c1008030700910365001d0081c030780c1c00c80d0000d006c1500b007111100610809048c9540d282001f07480150010324152550720914603190b00030ba0251010f13203801010f082d40791441402201c205450041040402400802c1054004600200225468950200041c0039010f141c008a04065440032000c0c80300724820500c0440034400c5e140802e0300c3d03079910b04000344c05020340304558168200708000c00176600d401c10108a041c1c070960303200c050014400e020a069007407290384040841e5108042100c2242c055020704070401c3c0d4a01c15520b85030030150000c10355814541080510740d101d900c5070443e6802801543e41c2c9512000241d40c8901d0a54401d90300c171040e40200340d02400c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 596223021 1106 596221915 596221921
    0x5090a15090606030b09070917070510120c02120d1107080c012c122d030610030e1e031b0307210c03030c020106050d1a 53
    0x40700c403400140c05414220041c0442c0c001854151041c0c04500420002c10307406544072080e21889500901440700402c2003a1401c0300302d81011384d205010301d807288401d680c800e44450300070407144814411890300d008260703210012050640031560081100004495030760300170100041d0701280403882d00b400c6859040494108120101480c1d441c0c500d071407011007000e41100300311055503815105400b02521001d03600d140c40701c003071500c424000c1280c036000c500712416040ca000b0307010b000044005c200c002048481e407044130041c0c80382114a003003681c100d20a00c10061070400c0d800050044500800c036580c603010038900704c8000d500c0200302c9288044281e8441e01c3c0c007904000c0066840d113405180203011803103c103019450700c000c5040035104181d4002d46e0000c40c6a014140000c21600d101c0d0128007514041d004150003c40c104503860800c805036032140707010700307582403e0040d0351 = true := by decide +kernel

theorem cover : BRFrame.Cov 596043165 596223021 := by
  have h0 := BRFrame.cov_init 596043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 596043165 ≤ n) (h2 : n < 596223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
