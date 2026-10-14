-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2116
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:41:11.76735+00:00
-- url     : https://prove2.me/submissions/a1803586-3735-4091-be0e-0b881f750ea4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 380395683 ≤ n < 380575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 380396933 1250 380395683 380395753
    0xb0105010f0206061f0201020d060b0316030908041a13090504121815030e0a060b0102070e011a07020f040c02010f050606090a170c030d0206160e030c040518 69
    0x7007030900c04103201c0e1140001070710a103588401c040310b90541082940e81d00045560900014404414601070600200b44110020f0384a017420b018421000d4004129070040c11f19010a500000c0c4481d01a902140d0340c012100611201d2404444500c0c0300b42220702d1802c0800701300201d141c4500354029400f440c01000c509240b031406d19820394058010141d880b10420400c001005243d4464140be030381e05480380b4000c80c2c60780d500d5a6035450841e100348122440c50300c0303051100c0d895a04114200c014240d14800c100070394540b0b15080300703240704100000c840d924001810703c150745500c0124a660800131348104074450790301c14000d000300084020342d10141d0a10020800740d2405200b0740700c0c10040102034840603803405070403c1058050308201e0f4903500607689040d40d40d0740c0c1400502c64003803032034005d030601e8645070081d00100c451240002c42845101c880c502199100004d50341e07800c3c1025280003403180c890a00024400f8011901c03c889803007440400314084800406000c0054150000f001e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 380398183 1250 380396933 380396957
    0x307030e0402040302090a110c1204171207061a06070b19061508091c0503010e011505040308090a05090a0212010509070e1e031e0d0c0302030906071b030b010501 71
    0x7106034851488003a45c0321100d8008540e400d00950b01141a41d607021204620300681450359608100b40d1145401c2080c0d4003042c02c01c10b90028884200007031100740003602d40c040c81880c3c1070405020b08100600300f10f680c1c104894540c41c0d404544182020001c213200e4541004d07140240d600e401c11903440658500c03e2112101400c0d0030f02402d400c0e80d41e820002000300d00251411105d21070300804d100ca01e4856407440004100c00c21415841490903039640964039030420b101c800580c407069000c4a40c002095403080891540101a202501c5d8002c409540c0c40d140f500000c1c03c00559600f240d070340300030b000d4184004406940c0c014108942242e030035500750fa0f41c4408201b0709490071200300000c90310b48030448050b07241c61192200a00305040e040f00c01210f0081c003003417401810354991103034403100134124a201201085045e0380d10500d4600080e07400200e941c000c0d16401030341d0baa98000c4102054107002c008070900d5803c2c00301c42d05c4110544d11070703403402c214440300420300c941ca0114010311600 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 380399433 1250 380398183 380398189
    0xe010f14041a060906131e060c051221010f3206030c0c030304051b1c030315031509060b120a08030606070b070207031101050a090b07060b060a020307030e 68
    0x108003407001c0110210340150000c14403c0d00d610054906500403010828800c01c0054941000b02401a52240e22255008141400058040c1c3e400100900003070880000c0000c2c3d001510810449540300d8803600c44608002c1102c016040031443c0d0005810344e40040382000750b00102074103c80326040040c103802847c80200c00308101c0141d8140c40f041c41c400980282d414108010f542207980204185d00e0300704014041411a002524221241e82100e0407181941f100c031040b1081d4040308690950a896142002130400f60a86070000d05154a84c01010009010008400011904400303800702441c40c0803200c6000b0419032204a512600d08107510103e07051a01d840c003040c01702c600c000e001c4040c55441d010b94940006060b69400300d02000502c0004100ba07034841d0103100d044d00241074031415807500018500c1c803505414100107040c40b0383c040165000c10420200c8103a621a250f940440c2e00300800035000b141c41c0302d038100340e000403034a124990000003801a280a5500d012075000750b4010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 380400683 1250 380399433 380399441
    0xd020c06090c0a14060906071a0f0402030d050a05120402010e0d051e030403020d080705120d0c020c031609051504090b070e180115110f0d181a070305040e010f1404 72
    0x40c440c1c1040041c0b0421b500c40c10044c0003040b160b4040e0400e000e00b030064120748038107550304039042ca420810100900086045c20800c0002e80162400c00901f0002080350080041c0150300b61a4045a090030104d410759000c0e0706e03041207184000d400c09040100303500f00650b94a10611882441c20258441d8a442c650044180d4007640e600815081048035640c5907140c1540106600f0365850154010303042c511081c1c80028117624600160124911100d0800039050180d41413900d8000d8000d5041860100406600300050341e1780300800180a403141808005a90701140d070303c42d08549011162014410840c0600384911610790314000714001c09002d21006000f1405103990854118006000c4950740c80508a543c200a02c1c00580a4500024440c5000591030f000b00407500105d03031050718154480c803501025410703004c041044a00d8000700200000c075144104c1e1040d8400305070002011302c128221001040740029024013540c41c1c00e201742c00f00045100b060820545007180c0c041508140c01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 380401933 1250 380400683 380400719
    0x50d0c030810050105040515090d060f0c03200c01020c1009020a060c020102030406142a0c060c03031612230a050f0609060a03080c01050708010e0f0a020d020c06090c0a 74
    0x154040c00c003494074050000c248c41042d040030f402da20a001e400d0302a22611046281076008440c0030401003140b1f440003080b50300d4036100c40101410302032103460b24052201c140100c04c2d01201006c0c0e17207200c000241170080c05241100d405902402c1620120641d07140c000409c50750003100c0d503202190b581d40e030554a0502c1d1110090150b00248402c001d03050003111a404040c2006503460300d40b1200b40101c2a005003042480200d4007130500b111240040d0130000b000d1a08815191103207003445980380384d5030324000144084003040c1030589079030b5040d10408070043c24100641d0306002141c502490074200c40e4503440300080310812840011102c0c6440d0003402c2c0101c0036800c00c140c45444032414081c0c40b120040c00542c0103041504004000780035100140703044544a80002007600b4001b000520350201070340a90a41e002c84000c0c800034003034441c015a001740c010600144d5400c1108890400703801004103440e814014041005924940402d8840c1b82010485050811603110f0200105000a0007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 380403183 1250 380401933 380401937
    0x62f0406080408030a09081201090608010c0905040506030102070206070b040203100c2007050315090601171b130c050307020f030a0f0e03070803160302010b0109030b0c0313050d0c0308100501 84
    0x70000c6808100c02400443d003001d00440c000c200f030181034a4251481d44400d091028010914004110790300312845124080d06200c0000d0100f01d000c0d9500409120890007660701c100e91300e60209099540940c111284141e0180c601a00c84000b400c14190449044505a01900900700b0150020b81d40348108001c1c5403054840c2034102c500d00740d42c42e0844003140c82d428513500c00c8144c08180755034104145503550a007041612602c0c0341c6034054074200841a4840e40e060b180e0300300c0600c4034060125080351400038036011542c82501044c00205542084a034001c078080c41c01040c0e001d002d42c000e00552084000b03808481c5c0090307080e1000c65903445914804000039201c02403078140310f0300c10785040c00885002000c032040d06071649113540c107690159485420b10783c0078100714010590203004400504c202400c00489061554407540d0707800100a04c84080020000300192490300411114100701e60460304843c3d56030213000000c0e000b006061410307400b180d40040003410b1180c107000081c1c01d481d012b03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 380404433 1250 380403183 380403197
    0x3030c110603060d0b15040f06061806080c0d06050406061718100f0905030309060712020301060801091d071e090204050604030609080c011506200d050a02010207062f0406 75
    0x251169900d008010740100c48250b4a030080b009596a5409180c800d114400c40001750302d813402400bc0c00020110140040700b07d440c0401b0829039402140c000e601907011003036160380c1c040751034000004114603008151300520304903002c201580c0c407403c2c89603100c034035800f040e0894032180e5042c0c3c5100302c5060600c00550242c1d01c00c5103403546071b411002a890940d8001304180342c041e0b07078403400c580044800c3c6c0e405900c0342080080841d03225108001050116004505d95418280010810784050040c1003086840d01c503000b0220f0b03001586030401410380300903a18510b07221184007605801c8440081200001a4800302d0040c0e05442110308442d0010710a074903052456a8100240801ea41c040d1090141441800f540050a00039101600301100000b40400e0600e1006042511450500e002c0040c0c03c00d0503080c8180001000800c0310541c2c208a500c448484400b00d0181c0f203481002401c0074100050000c80358003020f00444080e1001058150548881446000902071440f401d00003841c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 380405683 1250 380404433 380404459
    0x180603020c0c0f01020316150507050307050711180403031a03010209030601050f01030e0a050105010602101413060e010e06010302100804020312031b030c0a030501080d020c1e090103030c11060306 86
    0x101d406243c0385a807040c01528241103c0044c00078801c104c500b41542c0c2c0a90b03211840c1000c181034411300b41d00c01d0355802d0560071414030090041440c00b03035810050044620440e842e01c0c42d40c032501c00d440c8174604191602e049103082d2800030050441c1d2204900890a01e03400c6c289145010300130f403110b00300090000d1000d40e1820b1f003000001006903007c50b041c15541c2e000c03221044410301154203100d0051001141c907500d0250001c2c41c0540f10140d0021492400d0301c0c2041c4402e01d41c0d0842d420441030228a1011105070410390000e102028070384445601c1e08002203203200e00812154101d0703000b210070b85a00182c1042c15240584102ca0095041d08000d10800420302542c0146402981c200211010600c10032144003460340f040d01d00c42c02c00d0758046400e040c0c542c1d141c00346c90302402401019040c4c41b00d40c41c0d400b83d503500403c1300ca1441403096070113045c1c003141030340601d20b0b028070b00030048503103540d50307082c05001002c56041c20f42d03013400c00010b2001d013030600d2021a405464060031500c55004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 380406933 1250 380405683 380405689
    0x180e01080d080a09020d140c04110f0702041e27080a0f09030b01060801140406050f06091c1202070b040e2707140a0f030b0a2a180603020c0c 62
    0xc1c00070700d980c429130741d100e04d0f40c005078036200d21100d8024444c486c541c550038407120b01c007440c116001c00b0701c07031213541000390106070440e009040e6503c5440c085010782e15204288002000750580050a483c6944406030600c00307038090350001051514010f80f9414603001c51103a07041c4441100f8030250001a00300021100f1902c10800340041140304d2074000c42003030301c80d9134a40c4007503c01c0e8000c00008030302c0703001030250404140d182c0d15004030884040020741d25000104507090398003481c203841908081200c10540d11428100e00660407414103221069845e840c0c120703070f00e1685509290042c400e141010032a6400442240c083d01daa00c50000010303511401861145004900401503c008000140703040a0b410010b42c0b01800d46d44035441c00440842d002d010424805d944281c81c40d8201d168200041803640a0741c80c0c2011121f84046282c2c1e8034903501d402800800e402004040c00100001c02a4a034881500e110843c10910911030442c1c0e9200c040b4241d00801c114503403075030441c0c40c0c603007101d113 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 380408183 1250 380406933 380406947
    0x2060c121f030809040612030207030204050604020909090102041a070314030c0c1501050102010b040b0d08090303070b0c180108190c12150306060801020a170a02090d03180e01080d 79
    0x11100399554041c40050103501e01d454100e80e40102ca40071000b098022184ca490302481000d0500410611070051440e10001e590710310038840079001c3c90ba5080492680e86950701116514807020348419914203144d01c81d14000e60041c030855034900701d00241113800131504421140503d0b01541c4803050300641542d4013480e9880507010840c0904100480b1071405c00502580d010500341a0b0850415850704c0c0002e030a440c82000702034407461070565181015903e004440d48803035003002c4440c1e218150000070070b00d98424244050704c01c15400003001941c0d54403000909224690f4000d84013a07110071401525007032400d986015021810000e001d40f004958ad00c03440c028a411b02e03140541c49584101102121445061038403540015942401482154004e42c00240885000ac40c581190400002c1c07402e000c1079041e00c1d2800086000c070380f8802032a01500c0803004018054600340606140c043c0019001000b032081c01241004005400c0a1b4007443c581210200030141540b03074582e280840f0f00d6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 380409433 1250 380408183 380408191
    0x40b0a051603020a02090a050115140409140703270303050a06090501060f02071406090621012403090b13050106080604061413030504030201050a050706090c050a0602060c12 76
    0x8141400300c1140c0c000c10059541c4400d02940150910340340c40d005021030314a00a040181c1c1c02d00b000d0040001000c81c1002846000c900c0c43c00345042006040070303581500c00e950059a109040c00c0c64515460b442c80c0300709000300d01d1510108030098003050901d4a1843c01520292103685c9070280e040842e0098100c03a920614000700028103a440d95542c80890780207030002070000307402c02d07040e40d0740c85d404200c800081d10700d920800388078a1130b81000903a94851020781602581010030144045100007000319141448144c0c20781c400e6840e04c41c19031701a0354001201509035001d21204611501910921110310b0700031240e2002507603020480c410640200f4000c82e035075983d5500005448000707001e800e00a0344210004070303003075681824500b580b05015001030754801c01401c03e03000003a0030004a40480760b0a0038404d8803402d20020035034140c000c0d41c4015140307a0500117943d0401c01c035143c10605132081100c02040080d194103040740e49400031107420784401000c002504a81d0340a101c0d650f40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 380410683 1250 380409433 380409437
    0xb01120506010c0b040c091107020918030c01020301091a010f080f060d02031b03010501170307020d030908030a110105070203070f082d0909010512100c050c03070b0906011a040b0a 79
    0xe219a966404c07400a02140d056a5040c81150b0030b202d440680d010f411030740300a070602070742401070980008200e030501401503440801e5809982ca1a902d061055030139400801d00219140d44e502c03008007024211001d1060203220002c100030300703503600440c1000308602c40d680d250009903035104540003c20703002800040e030125507a212000169010000d41d80c07840b5900d10701c159520404001d05003910b8060304044506299170128000200c07000050354243c54040f80c6004400e1100e0a00b520840160381040b0450b000000301203000a400c61032606a000360203000300450f0360b0f0380e14100e8490180c244010184041196a5004034036210081d02c0101c51140390044960002030080380c0300a810000c4028a800101e1256481c0ca0140c0b03103580100010b4603e0101c0750402d406c1203032034034604403401c0c0030036545103d41c200e918810022340e0380c0c001e166401c4940e103586500300f641684034100c1b10340a8a101d4003002040b001c9810b04c1804101c030a442c00306041c6401c000101c605a003000c00c0c01d8007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 380411933 1250 380410683 380410697
    0x512040303020903241503060c031e0f041203020f2a060709080c0306070e06030a321b120703020702040603151b120b0d050601090e100b0112050601 65
    0x150340500405070580c62042d0540c0400f00945242e2145c02001081410700302100c0c2410f8015442c003003511a8403075000d42c0c880b5a00d50f181e2106200c0c80e4105010003882d0b83e540b0041104080079040544e016a00515030001d482811100407003ea1260720f007440c40d803010610514010000c1d60f408500d9511440003404503c0d038240034098030b404011940000001d40916080002c1c10050146406e003c00c1580603026525100c0c1f4060400076440c40610702075100000061b44821180e80090b814089280400000f040780c54002d511140c0c002034507103c04009500402c3d803003204d00c245114a4611142c03d00d040c40281c00c0c40300789090004142006168080051000503a03451058902951040b2070b40740c0c40107244100c0d80301f110006028028003410b40c407440d0500b0798101e2002c0420b604401d80215414407a900491285590303040000d1644c070951001003200151074004d1348001c81c0c19003c80e41d020a014015000307580c1c185441d280070510b0f00c10300e41e14204c00c40d0010344c1c1c03000741810640 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 380413183 1250 380411933 380411947
    0x150702130f061d0c040605090d02031b0103140f0402010c0c0909051b040b090c0d0f0e010f0506030d05040b0906190305011509050306060d06090c0305010905120406051204030302 78
    0x402900e968400800560340e440b030050000c2030080054900582c4014540c920620b08400e49503018803550046005000300400c2030b07920781d42d882c5803402049038041c056070307180118031111b440040e0811150304d020070b0074046d189003002c0d03050340000e108611281c0280c426458603001502c88007022070080e22000e440000209081d0401d01441c0d180c0c81c82503001300030a071180c4501c02c0e0f00350380c0141300074460350501c0c1c090307407141c0d0700c00e000c2c0b503044211900d40f2640c400003e80440010040e01460f82d88241c00d019005900342410351012414407000f820503c0240e40d80800c141e141c1c2550509800807980c140310620003141608058378008402a01442c64089a444540c040e00440d004141c00682c4500062050700c00641481c502d082250034100d50f130030b080a00003034541030001c01c0743d8003c060341c0b5201001c2c0a03041e00000304268104e003544c0c0801e500c90038010b01070405640162a148580b0b60064107040840c02250100d440e00e070750702030401c0380c42081013040c40009801582015001c0c0240 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 380414433 1250 380413183 380413219
    0x1407051009080d08070815240705070b0f0a0804021507210207060504030f02040624020c1f112a1906050f0703170c0d0b0a0302150702 59
    0x1440c2545107522078031486440d0000076494190700348000410441114140a05103401841407074005a20700c0307040203280c10300008140e4100401d02a42aa0b107000307112070184d248000c1c0240382581c00b070001d490601c0d46616070ac0074188500d5000c450f01d41c0041000d209001e20500c646500280300410000382c140c60000e1501e0260081c0c4410355030b40302401c019641d9116080030280220401d8009840c0d624500000682180079522014040c03a69020241e070031503581c0d52050000d0207403142c1030480013101000ea00e40444000700905c0c058400c40781802c059103043c0d075400c990304040101401d4111010390f000c403000e1071044000c504600c204c6440702072100c80e040000c00d0641403174900210301e01c2d101d02001001e5402960061181010304424400c903544102200c01c1c41412030480da0fa60a4585421280307202c1e00c511b140326034011101840701d160110030080c000099140400d1101e081141c04010598441c1d21000b5845087d10744902a001c2d5800b001d029002d0005221842e440025401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 380415683 1250 380414433 380414449
    0x3080903040f0303120b0a15030c030b03011505031005040b16021f0f06050d05030403120c0f0303021801051c1805010e06010503120c031210080a060903030e030f0403140705 76
    0x710082000703078020244034140c901c5246841b00301203641d500207616120104504406200c0000101a1180031890049000750059130096002500170080c540b810030340c9040130201402414801e010f8040005031100903802164004c40e01b0ad0040f100646901c502d01e640210201800c10a5000d114040003090010006601c040e0110080104080e451a451501220040e0700014401d42d40e1801c107901040b00002a202501c0c0e0180c00d40c0718500724841c4c1555600c80005e0010003803180c0e148400c0405a26401501d941e03070b190244004544050401510140a020902107840c90304001e8041c40c1c00054008148885141810614409440e19000d00752030200c3c02d03d048641c0200010004d5080422044004210601246040920b1564103d0700c920406c0000c0c207004070480041610040c40c0e0312071000610903e01213a81c2d800343c514014001e05900c0b0001c0d4082071a104484001100100468114983c500346481c502410355443c0310039031881e1a420481c601c0b84c80741c0401d0907198450 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 380416933 1250 380415683 380415689
    0x30105070e100c030c1101020a0f0510181a04080d090501020304140a0305030f1e0129090a0501051c020301080f0c04020403032f0607050403030e090f010303080903040f 74
    0x41e6640c0404564000e200010386a0710300141000010a01600440d5100074041e42c45503020300c10080040321140104d02d4800070315400b61001d0302d0703501c10310100304002550001c21341c0000810321084070100724860340315100500143c911178040c0c00a0751089912112581c6c014401c1288034100003440304c1700e00c1180c6892004842d2a135001040c40705019646901d100303110700c24401092042603658004003d80030192030240066003250200b4035401801c41e0040b003509d402040404a9031b512000110801400f804c2400c8807800381e021a00403d100354100c4c0d00300b54005c3e02400c116440c0900444141c7d2040307100c071724140500c040e58202c40119000550007041c41c18020700d4150f40b032902003810842c82c4100c0c544078600c104400c0001a0700940c04500804c07003000c10949440c03441032115a1081d800601108600411003045031843c2c00c80d01800a0b28000d0b521409000c004c00c00340030988600355081d103030102c032100041000910461020780d100c108003080e60308190703032403120340d0300780d20150 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 380418183 1250 380416933 380416937
    0xf01050f0a090606170a020a15050403080d0e01050c190c0b16050f0f0903060f04110405061306030c15030e03041a120103060501061202030f01031b050a1508090f0705040c030b03010507 81
    0x6d220f640035071a00740c8660002d001503100003171f0400c0c0308100141c054031403403100600e8900045090114141540c0c400c40c809290700f00203000302d1800522501d903640c03025140d213149419003646050030a1142074000e081c654400b6030f0001d59103070b40c0003698102c0000c030481c104210040102104828481000d450350b201600c41140d2102c003003c00301810124020040c03291030300c020007000040b52402d07070301c0c00c42c4400568001506403208030101d4031850000030000c0080d400c0850010030404105040c07811991054211400360800150031000d480e040c0e00c170007086a0041c01709020040c0d40300d100c0c504a210302204036183c90700c40c084d001d40b88030b800d078010707200380e03940b100100000c0740c0120b54070b04564a0000110303c0c5141a404c404074112060001400c0300304080c5128410000c000c0810000d080000c1098070b009941d0f9042c0c5074413140071031210300050800740125401050009155a00e100345002410707241d81000d0600c801805c4030104d840400da1100300510711501e080c410300d8010b41482d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 380419433 1250 380418183 380418193
    0x110609210105070f020a150906110715060911030f0c0903060705090306010b040837060504060b040605010c12090306020c0a060b010906230d020a110f01050f0a09060617 74
    0x2000d005400383e204d0341c8950f010764101d009400006150001e140307441c44a0714100060804650030004010140500c5000c0e955400180348828800c3c081c4d91402c00c0341e0003c0c401c4c0421074403404074a050311508104907241003000e10102d000311024020a50740180c429a545060203180000245000401d4030f01801003000061a02040e0400b402018058403c02c0c00b00ca14051030030a10940d11461001c00ca220003d84c9041043c54149200c000e440121b40407407008407040c000d0030702400425040c1c0f411615075107418141c00b010300740383c040c10080703030b2050b110510104039945600704202500a60141000100340d400301c005032140c80a4100600d02c00c0041180031074528000c4c0440b42e5990b80d05041c4400c04004021140e80004042c811552006016000c030700c0c0414034038a540100c05008604900210700e140380103506c21541c100c2150f00d103040314191500080024201c070016120100c160ba110b90020743c41c1d4001750002c0b82028401c1030001440f036506c2a0792141c00900c0030810000e070b001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 380420683 1250 380419433 380419441
    0x402071a06010c1703100801060602030901180f0612090b010e0711060c03060d020d02040f092a050405250206010911090d020103180c030812090307110609210105 71
    0xc003810280c0d20507000c1c00c05560540e0b0ba07888014001034000d8807210750713400000008864011010350071009102e20300003130107a03036159800030352241c01002495000802003540800c120f1a00f0307021030101d5907403511308074950341044e904076070481105405580d51600e80001e203000911070340d00d980c020510400c1240f03c6051104005241d0f040b5825541060b034012024003911a403034004981e00884203c401040411203031021071105000e118020350b1242c5051402c0c506010250011040c89110b1904c04020303002080301481e03407000c20041c10800c00c00c190b5003403002c0e06042e4049500040ca0308807030981c3d40034202c4203140e58182c0f41081030040e0408030040144d01240e00403d40c024000d20151030400c50000040b07040224094000b1f41010f45513403005103881030114085044a80028407a23507001d03204c0c10b1020040c0c0c03100d281244611007900005120507004810750b224a42d020740050000c007558405c10034a9000303500e12560180b890700c41c1c0300b90f40080c082d05801060603c00040749501e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 380421933 1250 380420683 380420723
    0x703020a08031005010806012c0f04141617010303030f020705061303030b010f1d0120010507140301030506270d03090b010501080c0a0c11120a141f0209040b040207 72
    0xf601910007230500801500c600401c1c00c000b90362100800794240405a55540c1d81e0010340c02c2484683c0700c94101d454980864000040c41a095209015100ba00c00100100b41021580c4001c4201c00c64104544540144002440f90300046500d017021440035041c0390690300d6441c14a0400d540b00c8000048800350101095054003803422200d40900301000c0b0710701000400b80c803942040d1828149451000103001040e8003582200c41440c1c04507200300b114101c5015003034002c05040d02c3c460089100305404a442000f40f1017241e06a99120001d801103481d07103504807054a540c1c000700710544802c18814620940c041107290074241030386e5404644413819003040ca09095040c0c00050402400400300081440310204031032400c041c61808000b400070a041100e481c41d00f128090340d011400e10001161007030000b411a0400b40500b030240340d00503100340341c507076030750340e005484800c0d201c28404041504a540c0c0c0034000c4990050000f0a06e1802100094126444008204c0751480d015542203003c0d5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 380423183 1250 380421933 380421947
    0x102060c0f0d0617060601111f0905031b0f0601030c05120a080c010618060501090509040c03050105180d020f0c0d0c030b01061e0f1b110d0803090d1809020703020a0803100501 77
    0x80c1b080c00c0900f039400414080c0340d240c1e08403107651100340e0340310b050b02c003000080303584200d1640d904401941d807521640000c0c0404121b1602244030745205003608101240c2000c80c2090491790b0064000e55014545030600c030760f400071440d00805034040c1c00b401d04042401100241900b04001000041c45810081c0c00c281c0d050320016414040ac0c5804828065a41c00c01d80d14000e440c03088030910481d999610380030305407010942004149508120900808a0200032170215014820094078801d4001c00e030120b0f035869000c061401d45034003c8502441d28100001c105d25498010344059214030780365120002c0341c0070207078041c100003031420140880581c01040c0010f1600c0651410b5200f56480300780080c01004c030410008041c1c401000c201080011060100010100c007511817284803415041003502608215100300c82c50182d484403e482d51710900314000910103100002090504003210b21000b508103200860035880f940d6003000100e421800610310520300b2030089581d260a00700010104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 380424433 1250 380423183 380423191
    0x5121e010c020d26150a0902120406050c0c07060e090601020d17090f011a040605100c150f0f0b01110a0f08130503070f18090b1621020702040e07050102060c0f0d061706 74
    0x1223105010314200d0f0f824100c0d446400c00c2d08032502240544034102e400038107103c0e0041c800302d60b22840304000365064200c082035215281c11110415030341d5030240107985a90030303203003010300007901a0404080e40100442454114050204031444d102000d0180760858494041d60922594010120b200300c0c9000c0c0071321009020b042e228000034158554010b001d50740d0000c0d0041a86246000031404c0c21950b40c403400640385ca245c0c061009114518a660060030011141d900260b1a49243e0f1041c1100045860405a000407981441d80d2036855034000c1d500000f1102280b41c0da9600300064a070340c03c1014601900341030880c50b03034051404080783c110110003c80054054207249074000410800c0304a580e0051420740092100941d8602c00c0b2204500a44140c0060003291010000c502459001d402214400c1d6000c1080340604c0b40042d985080ca4421640144c2c000710000d135450716070101620004400c07d400c01d04114512a04000395291600400102c0802c1000c0d584a25001c01000303400c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 380425683 1250 380424433 380424449
    0x11030705030d0206010603021c061401080a0c05070f020d0506100914010f03030e0a05060307030e0609011107150e060c190309020f010e01020705121e010c020d26150a 73
    0x20008042c042e40701d0005214440c203055010034407802101c40c1c0000030048402d410300402082c0c1d2a00c040c071405040d40c0b240f660016074804005024130700300e4410a2005811901c4103810301c0c40e07660380c4040c0161400d204907040320082440100150741002014002e2103804100c941650500742240c0450300ca0100044421031180010030041d07100400000640f905881c054100c81081c0340401c10102c0c4991203903402c480300100704501a0f9160784101030040c220341c03d80300075440d00c0520900ba80c40c002511924000d003005000c2c0015010103940305c03a03985584010820400e2171004a05062007107402014922000980035054603c1700b09041110b041030500308180055600031660301d24003a6000e0341440000c106a8400381e00070000722009120003021441030302d2075112070548601ca68201d0b103600f6002760f40c52041c07520040c024141c1e0503c0f5030f80140304000074443d080794518001544101a00c030072130241201042c240c070545100d00710071209600f05030014401c3c042d21030075913031081c45 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 380426933 1250 380425683 380425693
    0x70207050a05060c1507030c03151503150906080604290703020a021002030108070527040204180b09011512050304030836040c030b060304060c030f02071103070503 72
    0xc5565078449120035218159041c0f500e9140c2d030941d0500d0822001101e580c045260010404d03410361503000300b200c00c00307655414480f205500c41c0c116114003481c06100820000d0760240302140e03210798415003012001e0752103007110030790301e031085411030f142500903c246400610800040c050001e009240b401d003546010382e442104101f180d07079070a10240c004010503400084001d4002d100700101050303001010411075607035a607007000f01d6489101d441214000c803180700c1a2124460603d8079201d1010341c2018140143d07450303508020003000809001990110500002d8010070245510984191018400083d41080ea040c1468120100360b02518036100300e0350340e046c00146c010099404590f809511180c84600c0c0d01807983c6c040d182070440d1062064401340d1440c90202461402d628200d00740c83c1000004130f01785c0f044041d42c030320704607a43d00684204042400912240d110712100d62151500094a20755414100b003683d014580035101000ea902c00741000c2e190602c0a04001d28088006007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 380428183 1250 380426933 380426939
    0x1290306030d0e031c0909110306030718140403030207200d1b0e0708072d05091908010e012714030d0c0f08161d0d0f060501030506070207 61
    0x6690b5162245242080001d00c0203100c120361410040c0c10051801000c288841144e2400000c1512490303201d4a03000a08001c0d00c2020701d0621000c40b80244809030141005a0420300301001001c41b10256400c00740d5120b5900d41642c40311a01c0c0c6020303510130364025075a603901e030074440c40015181240f66891501d500030154182e41c0c20804c5140b07258450120003100052040016031a101c07030f8014122300da0043d0421000341e40c4240c46170300c64181a118801d1030700149580c0c13a0080182d800401510704816200c0c40e00d10300400140c6010080140804d02540392240390300040e29066002480b41d030744410440665210a020342c02d007036520710a4402000040c007041320440e1205a0010700b0b90300010400d120500d000340111200561030420030700001038521001465809401030034000140c0441c0482e540380850354940000c40120341e1859110008070300e01d0301c1e00c07000018070f507a4840d0b8054846000240c0d081c041041444c01040005182d603d1070800e00d040c81c00090080c070440d00720000c24 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 380429433 1250 380428183 380428189
    0xb0307080304090908070b01151106100b0706020d0608100f0b0603061504080313090e0607080106050d091a010801061a0d0903120920030307170f09060301290306 71
    0xe0b4046800c42e1001098a80f414203085490b8403c1490240a03071800d20004508880280b81c105401c50060f650001c20a60143d0140d0721503005079031108881c1a0010100a09414030000d8010280940707001840c0c00300c03081c103010807034210b0f134080d4150360040c0c17003048181c41140c41000e1142404100902c10042c10130000b13180c500c402449503101e00b12a10481102500400646018100610849584503d4010084d900344514411880c40e40d0074028100c5000d2000315080d805440b958981818590030441c06503583d4000700d503600d2280703640e4484c1c1c6010400c0c5000a014008040c0c078081081d5042030f8038642564040d0300410450749400d0302c052142800d40e0f040701c4103c80c20000c00030304200c862804071030352000c1881917026907041020035000d016002540380c044910403200c001e00340412509143d142e0040a1014002c4a260700c3e5100c17410180c00014102d144280405500e010060000215a6002a004400e59880d0b600460f035500702c0c0088480200302144081a042d4a089000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 380430683 1250 380429433 380429437
    0xa14010e0307120516061b0e10081f0605071103070f0e130b160206011509140607051f05011d0103060c0c0501020d0b130603030206130c18090203010b03070803 70
    0xc0401e402d0003002403d40d48100151540d20b503800030912140800b5003071030000f5091003400905907050a401ca900c07005d000c0c5070380040e4854007a051001d0400c541d801a5002600100b904a00b0306980c070b00d220f540c05055600e280074107503e07181c0c00e46954880c00c01c4290001015000c0b40a50320800040c080515000c0e151300884008282c03100705540d46c01c2004140d020444002840e1841000600c100400c1d402e0310468072403119403c0b070b030041e81c0c1c1b1403c02c41100b0105945d03401140c0603100a201c02d0f02d03180070742e1a441c0800340000385002901c2e602c8901d0102907054403104104254440000c01c103050040303078010406086086408445081100034026061000501140c4d5030f05010810f00d00540d07100c12241e030400021512400d00d40d41c0c08029015400e03d081c4100364900088150041602c900c50927aa0143d0003810f2a0307542462402c416070400d10282d41c0e6100c01440028071b50301031810b00783c055000c0e85003c244880700d40b041c1400d5505004041e03100f50881c1106100711400041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 380431933 1250 380430683 380430697
    0x91501050d05030c0604060b04051f1a070b04060606080108121207030b0301060b090307051c030c080d02041d091c0e010c050a0b0114060a0c0b0709090e0a14010e03 72
    0x1000800c4850070b160140c030b58440d124200c0e009025100401c0103000041d806040d820500b99401d0102ba5078140102c07900c5c600c0504401c01c0c1608040081c0065130102100c2501c0c140c0340301c80c1c1440c156881c5c031a100c09100455040b00d0050321070300c09000c0c140c0d004000354014445040104040c00c000319070040c0d5401465070b8051454600e500050189129421030714060501800800044c1d4403002032002c50b07440307010014000c0c49002c400140724180303078444d40103c8407035907000c0041d000b040d41c0450b947e00311484207403140c0384140001d040070105440108014002490802140c04064003440c04180c002004c020568100c0200c000d070040c072840e003000b030030f004a03c0c00f500201c40c072000607200a0b03031049026003030340705150070901040400d44661303050751485a10481107203424020808030344146980900000c1c00c2c0c20022000403003480c16650000300d20f0800c010400c0d00c400c0c00604988440021040301d03407080c403030071040c400c1c40d03c81100300418003c024400d040301082d030b5a569100d181 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 380433183 1250 380431933 380431939
    0x17060417071e060507030c0509031c0e06120702120c031608040b0c070e0907061205040c0e0901050402011e0e0d02030f060702030c07080313140a08120d0509150105 72
    0x55020801c030041501990b48001c8144450003054942018001840101ca040300800e10301140302c1c00b60760144041c0d0380401e0f0300078014034503601c0740d0301d591a828040855071014441101300d80701a5580700742c09030900725000000d0203094541204020710f080f960381c0944070141d1007003001c16108503010007180c0501c0490101401b443d50070f480c2541c030500c00e551049840705004106640d400d40042410021503017241c402c81c0c2d940e220503c0013911151580329074004161034004024054001d034010a5115005e01d46010419641e4110210744100440300c46050f070b5505e5082004562b040303140000d490500030a903030240d112074003000d8a981d81040025104031202d02d864021983c0030044070390f00b0300a600681c3e500d410031060181d942e030056030280c01d00c0d014180000c030349004004183e4a104400200403905c0900d02480c80302d1482c40850312a4120044a00118050701c041110303e103100f100c2c4c401e0940d1100104030590440b2400f504441300c0da0095841c00c1d44a000400244e4103442c812 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 380434433 1250 380433183 380433187
    0x90a02090109090f020703090f060c0b10030f030507020102101e0b04020f1911120d050a09061103010f09140601051b0105010608010509180714030f060c0417060417 72
    0x5001038401e01040e41c4402000342c14010340085219441e0041c001c20382c030a4440123802501c400b92060044401c0c056140000c40c1c03c0e20307020103d005401006d400a005401c180c0b203454894507a40c0318141090030507004100002294021540c2c10087c03000ca59465140c2005403008881d44c88615103092006284c44035180d007803080895990754111100042d44019440c0d8540c544030243d00440503d120307840200f203115142c196a0400410014100c031500122945488030303d40002004010140103a0b020a80d500c2190001807801d1080241180100a103e61a580b6024601f0341c0400c81c1e030408200282072041030016034000c4450150030403c2400c085848842007140303000a1080d5400c500c040e90300701000011502c0e04a41c5040c180e03801940c000100d40d90707041042c0180c8170b18401d100d015078031050b030400180e02001441c2c08001e00c0202540c7c2082c02090043d0319001c1300703544841ca5110001020008021800003500f40d18424002034030242c5050f4550003004061000c51100072840 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 380435683 1250 380434433 380434447
    0x3b040c23040b0c010911090903030703092a05030606011b120e130e0606100c02010e010201110a0815030a0203030a031505040e060411241c240b09090a02 67
    0x4000d007510050300100c0c140075201e600341c800300340c080c1c82005400e0340d00e40000c80800240342049015148143c20b140d006514503111540704034020300300003205941c46100703a160140a802d2501c0b060b00e598100c2c0c101c0c0203a1600348010107061010280130b55050082002e4403014240b03480d00c2400c0015086030141024105462041d510740305411a40c641c01050a0f01d6210701010079031180b1500e1003880c044519a03920041446408420250b5003808540207950600066200b0744d0600b1540906200200d00c6030341107844d5000c1500003050020200e10040c007040141c6998102c401240b0360201c0040520b14465008203482e0f1142e484004101a1505811142c00c500c04141d003004080141041013035449910466403910001c1c1c8040710910f00201400340d080c0360021780351512440b0044035901c0301340501d1803160503601800148074400c03c40350800002071810310400035811888034400d0740d2042e10006200c41c848583c0c125081150b000c1c44400c082da212140d019078031100844e401039407110 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 380436933 1250 380435683 380435747
    0x11011e1824200d020f010f020304110603060301090206030109140c12010e070c0b0c18090402060a030c020a0f0b040b07030c0509041a03070f052b030c02013b040c 71
    0x401c2003242e002c02c2c89030600c0144025400113421215400090080265001074030710b05050380300a460262581c04e244180b60780c6840d08000440c0c118030001e00028080741c07140d011403803d4100741d02c00c00308a690b0b081a00c0140041c10651640201201c45480c5010b050245807001c03000f044c050040c401103000c0008a20398091020344251079004101007000d8a0500b0300c0d03c03803a9120038803038900e031502442514078505041c0342c03081c000c5900034003842c288548640c0131001440c20564140c01c41c491501000042442001a00ba515001383c00303c280600e00750404042641c0040c0c2a0340415191210744040c05074820103440003c1d034100d401003607046030100e0f12071103000700100440d0f160240c200c00040811000c402d810440d1001e03101c0c05103038440110f00340c451280200944045585498055000910407080124031501c141450b080503d40c2c074602180f01c8c0070b4888160b810f03615006554400080601d230100000e0300440d02400845901040107007020007501c10128104007070b04554407542 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 380438183 1250 380436933 380436977
    0x503030114060c0d0e01020a1407090b0f101211040f050f0603090c090402121f0b04060303080406151d06040b0d0302101d0a11090105030706090311011e1824 69
    0x280c1c009d0041c000161110100f0780d1a00064468042c46600e003d02daa03019040c064050b203200134004090020703a007001082a50704440b00c0382c40c0000c040d56148150009903203000540040c25400c03150300300650902e02170000e00700e0fa4011852142170248108452560001220341d41d102c010754034040144ca0f148042401c15a182d00c40c0d120600500600010f4000d001d060220043c120748400e00040e6581c00520084075800e00001c2e002030780030350008010801a41040f91201040180c03060541c0d82c403035412840c1500d080c030160051000006010071407505009030100030308110f0f081d0341d40500e1a540607548884018021160b1a01c41003281011080c3c40f070800300408a4100ba61680445071609550180030720743e82c01e201d80390a00c00846c0c60f0400042940075030b180c5466010003142940c0340d4441440c00044814100042c0c000340b8034011404a0030007501c4103040d26900000b0000702170b90400c5c44147c2c0c02c040c2800852010800d561202c0120a0051151301d007008070718607a210b51248220 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 380439433 1250 380438183 380438203
    0x3181106070b010602010509070905010605120405070306113103030c0c05090702030d060b0408031b011815050a05060306070e030106080703031e050c0d1202090d0503030114060c0d0e0102 82
    0xb4a074000500d00f0f4040d004284140044402da918054580e5464401c0f00d50038000c00e00060310a01240170703d02100414181c205008104403038040381d407036860200f03448405884500d0030f44e020070b15034508a0551080d0425903030320840007040003180ca1200c44030522502c0080c04110389144464248a090a034890152001609040442c980007502035601d030701201d50604000c1c40d20b900060052101002d035010b41e0900000b440c0f41c8501204404040c9c4262407202d19075568072003240b5003601040c1507101a051258410448401c3c8400c840c50440340010010071506040c00200b045664010a605500403128140840300c696420017103030050000c2d801c10741c1280700c1c1e85804001d15400841c8112160b2104590400500e0301318011103040c02040030746a4190712008a013001320340038001603941031203010b40c014101010707400042c00d00c881c200c1060347d01c3e0b00008014481c0b82200311a031785c03c007a400d440092038100c03180030551707071103120300800010403d00f0700155070240e00c240509214 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 380440683 1250 380439433 380439443
    0x102100f02090a08010e10020c19141c090e04030f18050303030c191d060f09090709140301060b0d05181209100e03030d05151203070b06010318110607 66
    0x91180c9a10802c0c0c000c121b28848010984500b41c51010000c0041c000c403005032040d0700c0903041100300421040000103028800b160482c10041d43d200b81c040003000590181000c510320245441140ea90107041c0718903e801c41d1880703420300e904201c042134105400c0b9004507014509070f81d20b040c240d0700072151f180144d00400e5140c0000418030404904041c003406405000148950350588010015034001c0c2c8030b819401c00703400740340040c80a00e1400318041d00750701c0741ca020304919007040d00d80001c0720114200d41c03000109040103402c0c49080c02000402c1280401907000b041807a0805990308424000d0203100c10341c503500e07140041c0701e0210004c0407031200b43e04030701120340c0d0a840c030070214603d401c1000440d004900c50b80422441a10840c100e020222014001d1868500c04588100140400514140c00121090300d01065502c803003522084002c1208059521070040349080c0f50386d458064086410141803c440244009010f4801882c05074040b102d9511003d016001ca02140114000a82 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 380441933 1250 380440683 380440699
    0x70e090c040f12060e0c0901122315010b040513020702040207170304150c140c0a0b070302070b0604060f1205070506030f0402120a030e010e130504061b0309020102100f0209 76
    0x18490702c00f81803981400303200d4081444030380d043c1e02c101d03582c84000d134400c1d42c1d010803040c00400080d01400e2401710300601800c0c45100c0c21441100e180060b0386141e000d00711a0b84480b00035070311800d0586000d4007500748500041d01d05842c2030000b070019082240480509503000810b001190348540c100d03450036500c50b10381d2890510b410980301d03140e001181c081d150082c24440011400645101d10085415951594824940348c46c0000c0030755084001e6402047c86032044840110b485004d609102d05160341e00566508a540f0f03040b24806c2000c0c0c822802242440310910041d05280502e10a44000203540c0c0444185400e001d450038840b5800150001d10010030b104806d045944030381e1013917009a407035000d0308200c4d219403a60f07580303000300c081d000900c0154104055842035102200c01180108004c8080218101590440c0c9c0c054400319080360b660a02d20200d11140c0c14000d05200d12814100300030301090700081e4585480c3d0780410746440e40d0f4099100d040700309906480c14a080905910 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 380443183 1250 380441933 380441939
    0xb070f0201021b010504150905062206060e0a060504050105060405220f0b18131202070302221b08073f0b0f150a03090209040b01061403070e090c040f 66
    0x2900909090390140c0340c0c00c8047e0f0f070004a000c418010b91261581c0070004098969500b01c0442100c1c1c1100d810f10102034403580c60303901081d868002c0d0380103446480c0c3c1411072810700180080440b0030035400240a0740c00e00c001004155551f070265400c8804c10388403080c0403055003805031064135442d03a80840c4c4c0c515141c084905014158030a2215040561b0f0680d090365101c00000742401c002c40f00312012001d42d100c1440003422a802c00c005031000c90040320a00f646a134001124544609040840c1d0b4820903c02104146140a0311015081c414891078840e018820020103820303009140c4400d0182901184800603108405200c0015110030f01d141d5400d4a22080422550319110001e04103043c000e103246146005000011175490052809190718030078028542d0130f41060420406140d40e500c0c2c16005a110800380c18441ea1107032502d505a90304200700a044040b4202240191401c01c0c410008426085010720302514411901c2c02282d944580002c600d9214542260342d01c00c0c0302034400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 380444433 1250 380443183 380443237
    0x405100201271203110a0e010210020a05271309020315042901152106030b1015050706090c0f060509040b0d08190507061508060a090b070f020102 64
    0x148107124600501850484640807021384e1780c104e04114160100f04220207026020b11060205003c040c01641c549010101d05081241c010451000100300d0000341c0015051410051004044004c01d0000d840c03a0b001c40828829604a2000d03122640d840540c541990350422034110180003808a41c5010703c0d0615102d4210906840b140001d00202c1441c000c0743c40743c11502a050710083d000d100c040c50b09081d0203d4018210765078101d41d00e2080540440480454040e1402540c0694216981c50038501d043c0340002c40700350300c4045101242403000fa08543c0c00002c844120350050400300d0040f400d4240803a880d1801d503ca19400c11300c080380014416001800b420700d806003120700304850310030f00d0140f0651100082c2d00921107501004403450b0172403801e42c00550085d0520307110b8244402d42d07482004982301d01d600e0030b0796030a035140700701700403002048803581c80034420b002403044824903502e0600e480005040e00d0180001c8001007400e851003503045d034042c2c210000c03100d00e004045144c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 380445683 1250 380444433 380444501
    0xc07060c0314070c1e060f02070c03170901121e090c050a08030708030103061d010f06030b0a150501080c090301060e010302090c04030b06010e040b0402120109060f08030405100201 79
    0x1040b0781200d0320000502da8030f008608940c64640c200028155104480044906203001ea2400300d071819900c0e001d0300701002161015008403442180000340090860501010110103250420501d01c020008000d8a90740444089918950490701080c000c501d01d003030420400750b200c6002c040b20b10f0080003205004074039210b9011601c060700c042106c1c903124048030382c403031089d80300262200b0010001040058411b41c015191440040e05040184c001154101d0a650f45003040c2100350b41c548406200f8080b140d54043e40001c0108070800040071f1031101d255120380944034060500c5149400100090f0f8820100c6a15a0006000b08540c80d207483e0444a450400e000c1030380a000c0040020720401e400404a500781c0f41c00038506c2800f55181b100440c1d0001c000c40c86c05400607210206070303100d5101ca0002d4a0310303050380d01c005c0d0010742c100020a0125803607503002d501c100b60001c0041124020100c200c40c10303150140d914240340344842c0c009a0141c407903000c00f0319002c40c1d03103087c550708002c00c070003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 380446933 1250 380445683 380445701
    0x5130e0d090e090a2001090506030103060f39020c060f12160207030b060307050915100302091c020d1704180203241f0e1809030f030c07060c03 63
    0x4444201d0361650f80c1559519180800001c4c116005201071400010308442243e0500d041458441d02480d142d60110740e0301d40085c0d000322109500c400c1310020302450790080a04508034030f82c2580852107110242c81c2c07401e1003040100041090750041c02c0e100c03842070103030107000800070b03102d5591084820800e004951003652960140e1042002081014040d103030107003012078060f0b00074026a41140c840f039640b02c0c0041e00084d810301c6035010000d00c0f0b40b6040d01c03040c07060380f59541002d9080501000d110076040380a200b4000c15204002c50034055448000b900381029030044000c20310492440850146000900040c04c641900c180340621941d0704001041038842d1804d038005501130004010040e40019130341c40c82e074855140610421070b0040c00d030910301100014008407032580c02100d80f84000106030044400141c450405041750b081c0034200315240725103c0d902c0c00c41880d200c621991a8090740304200b030718040000110b40505082d0095444040e0440010030048030100c1c0b0250041c05805 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 380448183 1250 380446933 380446949
    0x2030c0c0604061709032214030c01051c02070606080303041a010b070f11131d071a030405070801230610140a181815060905130e0d09 59
    0x110405036509206081d070342258020388460715880843c807800a00030700010a0108a40b00922524045860b808019030403015080328600805041910310044400719441c0a40250301c40e40d10404c040c0da00c2800c642c01810818030003280030300501c000c0300183c490480080c05031418200003007400b0724044000c5024522510310450a640b144e80c03102d460705424030441c501250184151004a0613851094880d42d114500c105180c0914500150360008045105145c0607520394a0546c0312800044101455045000030142e081c0b5201c08840001b10440c0ca40142e56404400f04040040c1000b0100c00f03403040400a0080d00c1005020080c1e002d04501340ca507080c211000410840c0c280480c12100c00100b982d41c541e81c0607211380030003078503a0040500c4000c000d0090107507050a403400d4603000180c02e100c6189201440d02003072803c10368003c2920040c0004084804008082c0c001030344904455007130b10500d40c1c808101a0a8000301420200c410740c0d80203000d44440d0460b0b01220b124113480c141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 380449433 1250 380448183 380448193
    0xb13050a06060c0302030a0503040206040b1209010b0d020d110a180c0f1d240408070e0a0605090129040e04020429013207060c020a0309030b0901060b0a02030c 70
    0x391030210703006204400b021300940c004008464070306101c1d000031030f4000e00240901d0319255031016519400e5101040c1c030140c15003001c0900606d61001e02450004017001c44024140d2805d42d00042d04902c05910b0050000003185800b04840d119142c5800040c41c2c041d880303075400c806001d140030140c01011107840c001102c14903a1b140741d50007020052a00000d4641001071610202d0074000c0e0010032142c4d00e00150601060b01120b0030300c8600410180040c000580032041c64074120040d80c100240891001034100b080030312098441000b030306c2c1100c1c40040c28480c1d88075100400202c10941d001c4107609408001004540401c0c150a401d000781d1007910100906034032140303000003024000e02035107001c507222880604030b0b601c160494455450081d8200d8102010180c41c520030200f41c0c1450464110b0201d10b910a002c40c5201d0503440d006180094940803201d03580003040380348a0700004103d250b04c00d0110308204000d51180d03014049001d0742c180c2d64802c2c000040e40d00d800c542803441c498410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 380450683 1250 380449433 380449439
    0xb0114092817211b030f04140a08062715070e09010605090f01140a091d0103032109050d020304090e070e0a021e0a03060f0b030601120b040b13050a06 66
    0xb0015003420048401c060791a03124615248110883d403104000d500e01000101c0c1022102000740001c0c01010032840e1101c0d039444c546520032219801882c14070380300304001501003002030004104140c0c0000a00d800c14041800ea0301d00c0c103d15220440600400c1c451a041c6807400502000c945024090944920b4000c5e44403104028041c0c4090144100060041c4018103050030082d11018442e80d05040c8258102c66038521b143e01c1c0e80100807079100180c440b840800189205103002104032003080f51482c280c0d81035841c040c0081d40c013034150255480b580810b28050017580d40c043c405844d4020150740b50703801c0d0044025540e421600a003071185240c01201c0300c0040c4001104000c60310426614002946e424910308001d400201d550b49944c00400b00b80c00342d811300030008010704400303924005840c9003070540c8507010740b00c1c86d00404a01e070004c1040c40840c1ea080340a040c43c1b503021070004942d030054180410003400000d02c5450b00043c0b11540014000e44031f03084103104d50400c02c007c11005075 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 380451933 1250 380450683 380450729
    0x3021c1a04050a050402130b03031608030a0c051326030310051207030b0c0d0e0f0102270102030304200a08010509060a050705070b04030e06040303020109020f01030b01140928 77
    0x141503800a5002c241540c1386000c0c441709400640c03001c032001342540c1c1445103101c540c40c00c10720224bc0488030b1031400020030034020300502c100008880c182c54403d0801d21322029561400e62075018221041c00c90314180b800c405240001528282000c03800d4035283e04050580002c040e0990040340e01c180c0c0c0c40b480d103410102c800100401100e070800750304480c0d6180e02d1500116517205d8114440025224200c02041c500100110702404170341d10001070f07850040000500004503081c15103075003486d503480301520307585c0e000080c0c0ba04983c00905801030307190b210403007001402903d0325442d04000c2100002a0981041d07029510a0410009450803a69846044403c0b520100ca4a0000c568144621404100e6000300f507540a07109041c569903011003240061030b0364020382d2084005139110001c0c5c000b10704089400c1380c5042ca083c01c052150820400c0041c06021000d0301501d8100c0c00072640190b80d0f43da00c1074020890080d81400b9241045400241c01164003034082c0c42411900b2128540c2111 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 380453183 1250 380451933 380451941
    0x1d04020f0706020c0c0303130807090c0f0e0a0305010f1d060c0a110f070b030403201009032303061c030e010309030225060e010c050304030303021c1a04050a 69
    0xc0804000c1030300d0500241d6507a0300035000000a110284245030304d030782054404000612803070403d0240c1c0c880262604102501e00059604510b10190600d000d980306a0782281c1d2804190000342004610b17020a2808111500d49503800545198280320b41113084011550081c0014240d038401e001152590301d42ca81c1d9103030002d0300c11a40901040200c0120244550740924913122400155400c10220101241c504049070b0440203800703a0002c18401010b40280f16509030a01c2c0191300c8140c0c500c000d0505031108007035030160b100203451346400401c152280707401d44020620300a20214001c50610005003581017120920b000f10412002014403100107041a40d40680c10780d41e40c68100e241d840110060441490210254416251042d1015111340690b540010502480010440c640340004000c192091180c5052046810980c404260080211005e49815003005030b65500030074100c0581001e203400c880c000b540783c460400407241e14401c0c41e00040c0c404a03401d01064071591340035009c40e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 380454433 1250 380453183 380453197
    0x1a0303030a0203040c0308301b1309020f04061701032607061b080a0e031b12040603140601030204051309060b031506040e070807030803251d0402 64
    0x5520510001d240c0c40455001141d1061240120b4026281c4c2e82e9607441e20360300a80462246901000780580902c4120b0700550410340c40601030105904106c0e018a015060f40c160a502d0110000380c184c0d003c3c031070100240000e0180e440110b40d030302c0c1440c2c0e012a10750042e005072400144010000c4d900c510754010154140c0f504105100440002074111041140c07403800851101c440a1041001045c1c00b480740d00600e034a5035a1000c1c1c00384913200b00074403030940207040354011407800c40c98180c003002c00020b130b443d08092407104004480c40c100320240341049042c01f0b24042d90b000600860b00943c1038200004103c440444001c5035260030006506074042c90066640054821240c40594003464000415590041500007424415170000ca82400314840c00300c0c0e4990f09000521400e424a485222846c88448020b064103600b440e0a45803100524030000d00b4083c808408a8803403000162181e0b142081c010305050842c0720104041e00280521085d50120b409100c4c050008d818207000700d51301d03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 380455683 1250 380454433 380454439
    0x1202150406020d050315120c18010b0409020702040603060507021c090b0306040c12061d0f09062a070b040506070c0c06050c0a150506090702010c05070b040f0f03050c011a 75
    0x1c0f001030950f0464850304020320041007034400310014040c5442d030f0412260a40000c101901301c060b1003030144141680c00042c40070102200b0301c0100103800e2040c040c0c4003581d00a44d00035a44d070a06000150140c207807500007a110a160000388250030f50000341702900f0900e402e403103a60003183c0650565800000c3d1048203000c60b030420018600745000c2c1c0c040203100490f420510000701c0c00c1840503044a185401c01c0f00d2403c1c42d010440b200800003801c40c0e500c0341c8003c10420251403c526019100d00c2d000d003107460400c0d0007104421581078803503220070400b115140b4840d120700c4a401c0c012040c0300c044d030301600e9134010800400c00c41c03403143c40070301d10042e0004203518666192103401c840c40d40c08411802503d0045100090003c1c60644850411110b8600003041e5401d01408010310648082c01309015a850074900728242c613007190507500300c1a08014400319983e41c90500c6482c81c00703407004c0188190b03510320441003090740220140499240c000002c128041c4076224280a01c41c9201c641c40d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 380456933 1250 380455683 380455693
    0x1050c101b0e0306151201063f110303070f110405011e1503020c0105160305130c09020f0d0e07080708030403020a09020f130303020703020f0a05240f04120215040602 73
    0x80f4100208030fa03017154400500202c900081c580030150031030300035401c1740442c00414105040340400142e081d0607400300401c0060713060301d00f00300100f028003d00000148100d030784610081841e5010700a640110381c001034075900d26051403500c003102c40d0407980628400e91415001060a1441d00031080002c0002c4803400d070100d00340340c01d44020014044800c8209a020003032200304010a006590041c410722184500c2d00c165102d015081e20001020300c25100020082840465090b03c2118104c59803072500507031301d204080c0005514810f5540f4031001074101020811003290000348503041315444426500000e80b01c961860700e070b00c21444042e5005a00f0a010b000d184129801000001201b000042c9086004910080340140a920075405a0070211080066040003144064550800c59440350081c3c10078000509150180710940c92166140890b1000f90200400300d50201d505185941d4899556140d40a401c0c015444d0032402144002240c3c02e0a42c0c08405681c00da81450300549 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 380458183 1250 380456933 380456941
    0xb0a0c0201200a140105010902030702060a200403110f040b0f090a18210306061205060d02090c0d1a0a2c0a05091903050405010e01050c101b0e0306 65
    0x140d8080585400b4810549103012240a401040010b5001540305a20104030040404d58103402c44005a00c45410640100204180c070307030313004c106c13135910200c502400510020744101072417080c1071171180105030070310008001c4180604000c003180f00b00400c0302c042040300404020301003501c0b6141c0d10280c110104041c4800203242010a03a90b01988410300080c61160103540940c0c42080710b582030304d21903d0901c100c444440540300b44141f980241c14240b00c20f03850100002d21001c00b1100c1e51503802e541d2808107245660f2a22040005c3c2e80003015003590b41040e100d20112a0b000300307031800e0303020701d400030301d0b2640d0300030081e21046000010602c0b0b080074030f049502c07081c04c0b07000d110380040c25040001012841c448a1000c0303004908110f40002c040c54943c400c5440c0103c4051109071001c2500da0901c0001d80c000100c4003070700c0083c1313041940a05018010f0b14503001d0503110144a0181c25402001111b044c0c1c401212200301c1800e68006421058041e680c1c43e0454900d1505600000006 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 380459433 1250 380458183 380458187
    0x40e0c090711010b0a060c02100201090f061a120d030b01180b03090703080c0105040c240f1b0f03080f090604030509011e02062707140d020306090102030109060b0a0c0201 75
    0x80c81da11020002080420104c000140000d49a07000100418000d180100c25810183c0c05500b2201039030000b002080c0460701e0707011041e038070102d004040549454030407407006c00c21105000030075406401100000100d50501d529801c001c00c1c900b00291401d102000e0f1584122840025603514802c0180d206040000602c01603000a00b8041c00340b26640b00040007031810030041806401020000444c1c4c1007524102d20103055603440140c888840c0101e0407031075a019421044020f9842c01c010070441c2c0149070544803400e04541c04c5c2018084442110700344800003480d483c40340c0c420b5031040404c1e5100071580ba003070b640c151040c0750551305c140d0000d00001d004a006064480e0b0506041c00000c0c6400140041a42400d00c0c07000181c00003401e20010381c04076603160a807800032241e481c54a40140a500740c0d11501841452103044d1844d0f001504c5449007000700c0d03400c0303030042c05a490914080400c58041d600a10030034580d58500080001c640c00007106030b9041ea1041d95034480703004a6a001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 380460683 1250 380459433 380459447
    0x506040302040e2802090601090e060f0406080a030201021b0706090909080f0403060c020705060a0c02040b0a0f060f020c01090f09050406140a060905090304030f23060f06040e0c0907 80
    0x40b407924855032a15203502c1d0380c84210382035204134060841d0120707003061041c045410070140100d4103100400500b44036000880b01c80507484201510444000701c0c111001a000d00307169404108035008280c0d12409056064009007443c1c1124880100d500022400a40e52040c80b03200f10f00000711840ca080c42600c5407500040700b003c1c010f09443d800e28030100304011f000e0b40264403c651003641c5081d4603030255014003203d4000d120450b45581800011917002d0880600684000c0c0f155a40d003c14151030740e81e01c3c6c4c0102c040c1010a4200c1d4449032580d20281c61040b64440001c058403c540041d10b81d0344c0300755682c1c4141c070300c00b84581c50170914206a0401402020b802168100c1d02e40300000d1109030348948052099a1540000c98542d1910490074201c4a01801d615082d80040100340007003041118032004551b806890806003030340350301010b07503000e403148a6840075005440a00c103000b0010b1071441d020b144110b90030000392005200f00d6903611500981c0d01d420034808800100303000e000b120 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 380461933 1250 380460683 380460701
    0x90d0311030318060f040206160f0501020f03090f0705150313170904060504090203060708040f0602070c0e010b0705062e030f0b010b07081606021207090312020304050604030204 78
    0x4080030403500085000c1c0c190741040b82d5002180c540144180810001040100e4010910103080140c42c2881e070040b808501c94005000000c1c5000007046003008128424008400d030070400031903c48903904c843c000707280c0c000d5800030300078842d04107040ca0420700440c40d1001c4440003850601000c03294450407550f604002d0052127028007a5000301c0101700d42c0e00d60b00124017400055a43d03140ba00c00108400c894454028500a500d003001480050b01e000030099080322040c10300e000c46540fa864103078000444101c00030040c03400403032142c2c03c00c10003400d000180d41410040329520f81e02c8000b00d8504d4095100054020752041000c24050008007000802448600e2440f2401c0b406284003074501100340c1c0d204079180c80511200b581030158180030540074054840055107000300f9916100224080c100320154101e042c0c486a0342000f08660468075800040a0f500c111450107520180484a03503101c2503801c610f25429078151540701008940558000800b1a42043d00703580074000103000942d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 380463183 1250 380461933 380461937
    0x6060f0e2b0b04030216031a0402030a020a0801050906010512031b030c0a0321090302070b0906090a09020a11030a0207140312131d010501050418062c1506090d03 71
    0x340c1c15100540d54890044080e401804480028103042c50020b2820085016140035410300c04420310014031009016494440010406150b41d01c450000074109104403e00a600013141400081c842c42c06401150ac942450b41c181c42503a80d1311800c0c00070b07051580000501d95041084421100e951092000c0c00415044007280d040030840820a407030304940b4401034011524911180035000c000d800b0358025030540b110140441e040c2603a02a5851000f8010200300c1080410001141e40790281601c0d803a0000a205442c4c496440c030364540294015016500024880c100d40002000000200d440c030045a07402490910f140403242d0f43d54074011005158113004402150410382105030140c104841032141489600749030580d181d081c20360311150300108280c4180104842e81c0c01c00300741d400311403c1c3c1d00c21041e02c03804406440000e000d103030072040680e01003000e80c1c100901e030201803140a40c01c3d0346128000380c542c03600321180d0352800300e55503a0042c1c0400c42d080e0941071806c00286010b100c0c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 380464433 1250 380463183 380463229
    0x30305040b0711040c0c1e030c0b0a0f140402030607030608030a0302090f060d0608060108011e0b010203091009050a0503280804080724030b0f190503060c070606060f0e 74
    0xf400902a141d2100d485e000050148030401c2c00d0004030a040503c90640c003500c0c0d000b5540c0e40d54040c0004040c55006032200d24083d0010704031a240b500070b9080c51504180411102c16200580039608005480c2680684100c5000886180c040d10a8205941940000b1403c1181070036044000e58000c02030b00e50040c402018259058a4003401382c60002400070b8045419414500c55501e402d1059004e440660304000880304089003650740030180490700b49000c580c1c3d80342200141d107148100c0e210550030005040608901903406101e600603074078129880000d285c2d0b11000c0581d01d1400c950780f0f142c0c016003140900035a105020300c0c1d008007481031030040d0610b9034404089041540d2503121841c02e600c802c0d07614103550155142e41e000d98070507040400c9440384500101d804020a02001d6010303c01c00d10601144180a41d066801410006d0071207101d4901035500d51200e812100080700c90f07a041100c0411207070f0040d9800220f500f40f690f100010140c3c09801c01c10740310600002030003100d03a0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 380465683 1250 380464433 380464463
    0xb03091e0d3e0c042306010f170a0f05010801060815100308030a020304020f06040608061018080102040503070602011b030207080f12090f010615030e010e0106081005060109030305040b07 82
    0x4242c5500380807980d400078104010380c8406000980d030485058513211581c0c100b1201d00c00e03e009000300d420100030701c0c108400e0700340114284d40852a442d9211120910b0b0402c00c40f1408642c4c10400c2c910300440d1060080341da031101c041d401c0e6926030140d607410340c00a401803a5114070341d0f440181d00c9a40b050005512560340d4551003030580c4260303929074015400100300000e60800440d960440007003a260365250625141c001022004090051792050320303a48030000701d040c402c403c0c010607030784045031021040d944c600c0301c20b00035401481014002e008010000416600600c110b01381d041c8030f81c0156030102086c51045000b58040c2e0b400300d40c2c003002070080c0101d040c0f140d009410404020003403401c1c5400c00009561502c810390303030101c0c0316a041090074015038108144620030384442e4103001c9076441c0111512409444951140030f600c0d860504000392411303001442d14079071000d00100b0450f9846e80d4004540303101880c04040e0105408110410001c24410020f10220b4003a201070300860030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 380466933 1250 380465683 380465777
    0x9031210150512070816030203090109050106080a0201080903120105010f050708040b0307110d09231e0112020f030103021c150f061706040303020a090b03091e0d 71
    0x181d0240410001d440458452424040c01000c150081480e00300000300d0318112903074203d8005000140420581c0120100b0f0000000b50400010a41c1c000020700c4225140c2c01e01c01d64030310000310242c1c0019a002d01040c4106000300031661101d1100d0000d411a07802e100040d5030000d0360148480c1000000c100e160003103130028000c0e0020304040700500340e580c00c1c0f048006101240c4d800e0003a00d41d420151904c130705150888200030480b03584d08049030940c1c55140c80d8bc0215031051010f00c0e000340203001000c855805000d18a0381a400076201e42c2000f540c50041d0604038004e011440704421000c100510142c03421802e0300000d103044119000080c08aa5580b03800d582184142444240c1c03101b41d944499a038038040c14001d8141d0326000400b8807511034502d81c0d46c4001400160030700d0740c001081c888191080c031055015120109856a6a0034201401591060100c820810700e401c0804203182e02d22001c510010700082c41d503503074036003400300d104680080e0460b0105480d07010006c41010403508 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 380468183 1250 380466933 380466959
    0x1031e1104080105091501080f0d03110c07080d080f07090e0a091416060507020607020405100503061303032a18050a0f0e0f04081605030702040f05070f050309031210 73
    0x2074082c00350480071001c107810f505406c0c040e0071a1540e500b114441c402c4001d0000758442030441d851501003201490f900c10711285102e40039041d81c0c14000d01c8400304190200003044103178440705560301e403820f55030403031079040c1c0601c180c481e84000f0300e500030108128144580c3d0300b0f030400c0d4200c6000608130782a64400030b800d01c00f0101d2031500d420000020f001c410741c51000300e004200500b411458540580e00155080c4034555000b48a281d82e80301007002c0000e04040503001e0314000e404c50304503041c40b24005540c00c00041049000900349804a43e03481d00005404070b020000800010752105141410342d40400208140d803030743c94512000080d48e55441c40c101005250758440c04604508100c08810321510040c10760189001c15401c1c00300142e1108101c4e405591000000d4030f05001902d005421407042100103540242040d4510000302040d91110380079079282c2d11540506582c44605403154002158288025001400303609404042c2a01c0d0f02d07405038480030202d6100b611068801072070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 380469433 1250 380468183 380468191
    0x4080a03121e0e0705010212040b1804060303170a06180c11160501110f0307030f09090212060405070c080306060723030304050d0309150207062009040b01031e1104080105 75
    0xa030ba1101001034079080f0038046100a032500f80301800008104d00c001171803a00c910322804403107480020300f001c100da403006800d00c070031400200140b0200e0b9881c10010311710155003280c404418060301c0800c01503107051280004841c0c00c11855090310103507030300880040c4003c01c001403c0c418003d40c20011b108082c04505042001d001c1180b641900301000101103880e1070210003c150301816074a180482c00105481d4416170514017450a042c1c8560f048500713411940c40714044500115402010b5a0141e0307405220b204255000c00c4569148002121065a0b0101c06810302c00700b000407856908016004141c494000c10006011040688d00360310801d401c041c8482860f0030120522081107024400c1c1d42504056183c10b00540340981c0b034602038000369038006e1000726800036000c1c1c1000a150829000170301004078079911414401c1100110b41c0c0802203403031041d89484420611503019100c1d50103005810589002c1c4541180e09003401420200306d0100020400e2000140c0340700309025807840707 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 380470683 1250 380469433 380469491
    0xc160308011505070f0b06030f0105090a060b0105070f02090604091505101a0f0d0612060b03010b011b1101050c0a110f0f3313180204080a0312 63
    0x1207614044180118810401c0400100001081400041001c102e000c0307450540103024400f458407003000107131a100c1c0207901d12406509040410000c00c0010a002e69000d004460511103c00c1650044030315200b0100e000384034007102d451301005828001071041d4841000352000520740c0d001d444040c24580e904a0300c811054641e800c001c06000341c4055038001300040610701c031000e0405840030380035003d4000030760300c01c002c0440c0304c510700031864100c075000f0030280c0c008a20864281c240789000d00440400c0758041d6091002c082419480703000c0018014010310440e1202510550703501103103000802c500c50410000b8000514a1082441030380c1040344100030a44141c0f07401010b0100c3c001a5840c4c80b4450241a0343c00c0d40e90781c481c801c1c046c491180072607805444500d1b10321040d4900046200010381e0500200d15200c03101c09004001007518000241040244480c10381501644940c3c050f0b4000c1d6000407643d0340000b80290200c084c0303103443c18404034032001d0001448828003840110401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 380471933 1250 380470683 380470697
    0x102070c091107080a140d0905030304021023071a010605030a060501020c0618030715110c0406051c0c1e052403130f08040303020105060a23090c1603 66
    0x9481c1c824424603004815515a15003004400c1c0c44100550085e512040180402d4443c8551507903081d0048a803443c3c040c503420442c07a81c250030308503a242c0007190128020300701d54000d070529500980c3d035080c0404645841c03000050490080040682084d0022200820700510f42503e2824102400c3d000e00002d03a10f05490340b0380000d0702026980303e40d01c070f2070541d00050703420720040d11410202c81192200301d10945a202d1f001004c2403a0024640c44448208540c035041c109407680509070540c070100440c1280c4464841404102c11140700c0d00c03e15a00800c0e0781c0007400b0b0b400249544031401402800e480d0b854a070b40d08100c600d10042e21007079a401403244001406180380c0740d08080050794250b0480c00c0001c070405041c0030315200c06840007004044600c1c4040c1042505031510002c5603010f03c01e941c5507079407442d029021340382c140da40b01d00c20300020707102103a015100c01c801801ca5901c03c1051142c1d90f40c075014856240c4016003045100e91040001e03c6840544070741c100b000380d1003561028 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 380473183 1250 380471933 380471939
    0x106020c011218170c06010803090f01031509051b030103060212130209010b090d0203150906010614040e070c060c11011107020d080906190e0f0a27020c0102070c 71
    0x1410940e100c1100c804081c908064a039410000315844502c03251300c00856007900080024901c458002e00c11144624410034001160400e000300182034980003d8030000415040d040054080d2261901c9004100018890803c200b02c40c1e41c101070340011240c0b40d20a1000e004090202559100742c1050724543d8000802c80c1610100c0c8002d81c0d40841351b142c080b46190b00660000301118010310070700343c444c1350214545c50660380312180340340026401004c9881e88118113413140e0804c50b00303c440100030300500000041c01c90145400c0402850b04400032450a400d058200c1007105001d0320a00c104106299410000350b00c51107030401c061004d8880030700d1004141200e609581c00c6070717102d28070108144050001600c48502c00549140d01264903500e4034034046c013203900d501454944a038407502ca400502d19040d080000c03031019810a55200d14000444428802c240f0450305c100305920280d00c09501d01c1c4c02d69844910800c0c00150000741c90101c3c2d040b10f150070785e002000c0076120500003000070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 380474433 1250 380473183 380473187
    0x100c0515060915010e0409030c060b060405060a2d050309070510140706182607020a05040b12010f0e0c030f0c0910121202010515030607051608030106020c01 69
    0xc200881400810300d545402800b046892101400201c6081400c41407003019a02840b080340c000b00010704208030580c4141002084450401d000340d13001850301008518030b00f422000c844c16a40c0c05407025181200640e8200c65050f26044003100c0003240ea54400001480d00010325100d419a40d11385d5240c1c1084031849061040a0380f200e8070480d260001c2060540d08010a240100c501c10f48481e203400c1c10341070410203052403c0e9007411410b08015801d04210f02070840d510300902e01c0206096034a200c000c1040144100d150203540861401d008200310b01e82604218040b6002500c1d46004158101ca00c0d400c1d20b20030382e80e451407a070b22907100c2d40e41d001081100600341c00d0118010207510301c043d440a51146040e40c0d00c1801401c81b080000c0d00070a4014010b8000c010341204581d4a11481c01c0441e108107903091710500550921000c07800403529200e03004100744006018010a495407101a10b03030741e105401030008074803004441c00c003140c40c82d000345000704240e8018250105c004400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 380475683 1250 380474433 380474443
    0x71113150e16090503060604020a020c09010b0703090e0c03040602030702010b040e010501090b010c0206030a0b0d14010504031421090c030a060b0a0509010305030405040f0b030f070512070503060a0203040f02100c05 94
    0x42d51040103011201003060f6900040c056800250540b401652002c1c0103204a090810305403043d9084100500000b400400303442c010441b8034041d81d031b003030412070f103490a0440010003620031441840b420b00c041000300b1101e40c0210340203072007030000140c007050140200d015a040e041521f001c03a59104010002c003641c40c0565030034000e0034a23100403121401c0e030010350320307000242040c8038043e695000c4580c551607141c204102541c014405450650f0606070240c080d103001c44e0b00700c3c0090340300000c00f8642410b60040e568194002d444c1846403045501442c6a0200010f014a070380744980850102c060310300340410503403140100008600010302d04140042d484140c0c0c40030380940801d10040006c00c801109543c15560102c5001c200d042240c60080c014103443e0035405d40c9401041124001c01d2400030340c09080340c00664802071078107540300c0300079114240c1d4821580c05030031075000140c140c000780e801944d100c0c2c0300340b0580009060380e0f00482c240180d002c0182011406d400414400c0c0402002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 380476933 1250 380475683 380475721
    0x12150b01050a1205130209100609060906051801051b010911010e010512270309090109020901170a020d05160215160c02031c0e0a0902071113150e 64
    0x3040c524108142000814118600448900c01d0743c1d5030b0301140016441c400617520850f00146800d11908158520081106d114420800400d0b280b690005200d402003400030111001620b9103410315109a985041090b60041c0c801e0401404103c5a007019086800d0303850084000000002c842d041031400e8040290f00005423414000e80540480c0d20b6a4000d045451100f140d016400b4240c459080540800310b07820b084049011403903500c5010100008054240003401700d0302050709076640c00401c0f041f031040c200e5180c006400c02c0b0340f000185000c1150035402864aa500501d0002131710040c108030340c0700b40c0b4980c8200340b0807410700061503410000c290340f05118059403001410501d448041413204540e10b0800d02922000490643d03600307001c42400c0003951450700c0e1540100320310051072a0368006a0903c070704003980c4042010002e51094483e81507010b10581848030429003000312203580700580000443c0c0f81c140c86070040c0e01c80da082c140180100d1000c02c5190908000e81038031114220b1f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 380478183 1250 380476933 380476937
    0x3070902040e1906120b0a0c0e03071401050408010c080103020a170c090405010227120a15020708160f301b020307121a09030304030e0a12150b01 64
    0x48000c2c0301510801030460341000591040541c92148082054040c040703645c000c560815036250a602071010214115114150140d070400c40b070416a0400d0345c1040110781c469030158400c401c06d1041507110282c1000700c8405040c072505280e42d80700004d095a080070b1414000542c0c0000420441c06c03e070f0302c00405800c2d40c08032640841000c840f203d03178501c404042184100200c401080c14007800303504a507508510052003c91000f43c0d1101c41595207542c510080c040c02d59101c40c2c00c5d8210b00828108603071a4044450b105294241e01c1d04406034002c0b035410380b00013000b04025070000040d15000e1040a01c103485114000c41c0c1801e012000e070b850460885400d60b076060403024a03a250203680c4649000ca420225901002e0000d02c41814281c07400003909440f41800119003102d010003400348441c401c14441554090048000d44031039030940d080d140c5035009001040c00030b4024007445810b4080501004c1006944a1000c0e541e040001001d0f2002c043d600c5124072010450300400144e64802c1c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 380479433 1250 380478183 380478187
    0x114010e0c25060f0501170a0b0a2406080603010501061b0209040c230f032b180909050c01050405011706060918100812040e04031206060201020903070902 68
    0x182100c000c042c41040c46a4802007002000030100c1c8030202000c4910380e0b04000f0421a90000c1820a001000203000340c000380c0c0b00d454181c092251001545160704c41d803214840300103844101c00c0002421800242c0d904070744948103048a840340103031440004201c02e42c0d0780320043c2002d074145402c480c2e040e000041081400d80610751841082100d5511440d13050340c4c1010140d4445c10f2000760703c1d03200d802c0130008031085a40e510006160001c0d0040540044aa084007405600c0400d80e5a4071196046480303e50780c0c6000003c010485c052a001d0b0021900744820171406030f520114203841240c008050403595400c41c074050050030003a50000b16000c0c02c09524160802c000a49800e82d84585c5c60001c101c410001401a124401541e111507409010a404c0d080317509080d10f5005000c0741d5503506070482c4040000c1c070500003d00c550f802c03141d80c0c0060b03260604000303001c1c801e100018001c1e03081c0039448083c448103400d01d201c7c48006000036400183c86481d8401094100a0207500245c013031401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 380480683 1250 380479433 380479441
    0x50a11030406080411030a1e03080a0603050c0d05030d0f0e0c0a03080f090d0503040b0a08090a0f030503061c050f0709060f050f1302220801020a20070e090114010e 72
    0x1928003908650802800f100b0481d062001031f00e44650000014800d00403050000c440d5a0075181c00f9403241d20076200c104241e070b00c1c5000c010454190f440040d0090f4800740d503401c00c2d81803001c030301041c8601a2050360b01c1c100c0e140c04c87c9015180016500000644e03105040d0074480340a11155a03075000450701c03808800d01d1a01c0e0078545000c2e04034101000400090345448ad0303034902480032180b652080c1038a4456541d40c0d0300600a23040031300b0300c4c80400c03040c80010318006000300d003050003140d00c565030620a031203544085030280c100070a5180c0054094030000d40360300c3d800b034007800894844d000801c020b9481111241c10080940d006d112a103041c0881445100700340541181aa942510010002100c0c800012000b01c040c0c0380c001c0485100040f8411071000d0072600001e001d840c204560300e0a03945a10442c203d106982440002405040c003000d1440030030203003904217410100465681c1c91321803940d808141c5050303d2243c0390303079500c0d02c64010b13120381040c1c41c0c0c2c0100b0345210a4141d80c07070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 380481933 1250 380480683 380480687
    0x30937141e010305190e0705210601090b0402040503150a0b030d17040302070b1306020d0f020307030309110406090506030105090a050601030807050114010305150105030318061810050a11030406 85
    0x40c1c96400d2414144c80d0400103040102c892409400103034440d03010300c25030744107180142c1c4524040c01a203000c2d503c0710203214020494018083c840c01031100040c100d50707107010300844c018414040b0aa5016030200000281917408105d0802030602c1d8004404e0207040840b92101120701c40451103000740c2010340002e0049400004200d080020382c2200d01c659512450200d05244040c2c02c541d6603d20003180302500349a180a4031005c5c0d031010b40071168210041e490035605400906155001070b0300400c880e0b80042e102c1d8000c034802a00c9003846800b00d04034040064140c82c465048034900c41e58038001c111461900340240d83d00000b51902a240708041d0751074003501c4400c1400003404414000030200c040003007d5021a56080000f20720340300715616450415110388481200c92100c122000000c90540b4000c003c6918933100c5e801c10002c40c00307180d401e0014507005a41195425900e0043e0f00030941c65011584448012070f07503681d9074418000c2c8001e00100e016118000c0703154020f02081c04855 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 380483183 1250 380481933 380481979
    0x11b1106180a0809040f05072610050609040f020313021c050304151116060f020f030a0e01020a0203070e1008060402010e12011509021c05060303093714 67
    0x2e50006126503595803001c1c042409004081d4011103a5803600007002016980142c01e800f001c0d0178036000e00f040ca00f0700b41c1c60074202882030328012280ca4407071100b046240340c0540140341500001d00081501552000490200c1c0c00850f000b42d808120580ca070401c624200c000300c0c41c01f1640c0f4044001c90080c944070b45940e40154041c0203070321079407401d940c40e007203014090780209181d0f010100c030306400c2c0113a0f40c2c80c01480184680700209110b402942d040c01e00120b039200c0c80b1040040154200040107100301c400c42000c824541c1980504604140507841c10320661b0090540f080714441c1c1c2e402e00c0054400503840a5000c1481a0040002d020050ba401522407030111800c8803011032030001121800e0052007841803080c880743e00280d000602a01030f4002d000c8035148409031044040000764540182da90481d103003545500100701d414001d00d000120740e1a0401700100d0522446041c488070007d1641c2041046450041000200700801e074103900288415002d4030340365540704020402e20980 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 380484433 1250 380483183 380483203
    0xd0b0303040b0f0702010c0f062a170601091703090f0105070503120406180302010902010206180c0907020118050102040f140108040f06020f0f210c1803011b110618 72
    0x90200040c0c04c40540e84601d0144001a80080200903141600d24101c0024140394515907a003646041c0d0802c182a4107581407403108403541c4410800109a4030120303045074004145034180490031001103150004441010000710151000716543e1108030b0401542c480d48110003410041e0401c2804005207000c42079500000d4841d04450090301c551030480090702c103032001c0c045030400004c01401070507070541208a0300c5000380c09546040d15a0341615050401220901c642548840521445070400c1004c260b4444101d100020341d280c101900c410198400b0030081e0341d141e4002c40e080c08200c1d56020f80c031000b460f14107031480343c1c082c41a002034680c200042018000e599041481c0301070140300e80440700844101e013001a5108128100c242c2241c201e003001402d52090040c0e040c0d00d5a20f10004603004a485072059400e04456040c00e842d031006005081d601552590034001c0902002d415070742c20220941c451141d440c0e00d0381c80c140d1a250005000f00c40c9054500c0c80181401404111020a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 380485683 1250 380484433 380484457
    0x50c0d050c040b070312290603061c030507120305060d0f030c02130f060812031807050303040303170a0b010f05090f180103050708030a0801050103091103010504080d0b0303040b 78
    0x5592402441c00950240307a00c000760302c400000ea0603040550090400c038220a074818100040072410380c0b001c44980c503e403021941c102103500d10140d5894140d02443d40034600404403030a52038003594140c0c2c05120305204401103900440c0b5401084040303001e5200324100c5240c108070354503141c2d00040c85644042405880c030184450381d9000c0c588140c440c003016580140c4104155040040044024aa11455100c1c0b59103031500c0800ca400c00031602104171400c0075401d43c1140c860248600b01c1000c041160040e03445000000542d0340c0301070000d00011400390301c401905c0c2c0840388418514840090508441a1400d800007503a6a00445070b5413450100340703400f42d02d94007560b010550f1100c040340c1c103076804000003000d45c0c4228030204906040c2e0b40300c0d4041c0e695256982d00d10a589000d15500c1d0008201c0200061001b54801d90100c03001500076441810401c003201c001c2030171541d0994040d034080714002a4450f18500a02910406c51002c1d00290715180c0b170121041d2950181c2140141 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 380486933 1250 380485683 380485691
    0x100c050d0f0537030501080a08221d06030d0206360109060605010507150c0905040c0c060b150d05070306031406061009080a12110f0a0510050c0d 64
    0x4040b84510152203205003403800c01c0c189014a0340394207900000301c0301d0384444010704800d100f0101e8800d0041c24120707401940282502c0c02d03a6a10002c164000384032001c0f00d62144005108003030100d00240001301101c3e00042c03c692a1044a2104424000c1c8414020752001d2094860316034009041c0b9400b04070982590700ba8420280c0400310480388028803d11b103540292100003551041d400395800070310407602048810760301c0c4019200c41c0601d22019218000a1580005289d140d4101928030901c074500307400728584400c0014100c0b40046421400120f03222200c01c10030540d80318001c88044100c40c818008000d070561003803544506c007075240406466002151001c2d01a40000000e1648850320103580041441c0e41036442c141125207a200b4051030100ca0841d501410400b41540d0805028200a1403c0d8a540030440c030608840001c226a02881140c01c03542840420582440c4a001c1c00e21f0342400d00b071051070a02c040e240301c03050904e004184004101c0c800c04544410b450ba07038001c6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 380488183 1250 380486933 380486957
    0xe1303031824110304060b1c060f0617033405033106050c0a021203070b0a02090f090907080102040e0123010503070509060405100e100c050d 62
    0x80c00341840c01546010208000303540010030034001c4014042c64608001803110303101006042c4265403460039044001007003000032030082401e58100e14095200544100d09060701c80384c00c819078018607001500c0c003e81c0d650800305400b14a00640b00140040039200e1a0500c1d01c4c2c103015128454404d2261900c04241e0208030700c547c804071920101c0c0d40004d807201c00348960b41006038a0b9400290300c000c2d054070124070038150108825581c040c00d9601080744c0030140c2002c4041c2c4d542d50200855000c140705103001035005a03100c040704222045414003039525819a46450550004040c1509800d20f00500000403d03072a046030303071099400112004082611141115828442c140d00045c18a500000e00450010b08002d145412a1104185400094882d0760a4402d4211800b15180050700c00c10101c0d5004ec4104058000904002c0105241c0740d6a000020107281d000c01850002c20741a01c0e0020151030140907459001c0c603d07041402511006640e01500c07205902400014421002809 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 380489433 1250 380488183 380488187
    0xf0e0105060307050112090b01120311060708041205160326060d02040903120203100501090e0601020a0602090a0503071d07050304171b03030a0504151a0f0141040e1303 74
    0x104115230400c080c1e000550311034032007030080342c0440c00a03808149150398000350030500040b011b1042510741c0c0c40b100691100d507101078a00806160702c41c00c00100340a1181b0a008138503003500c07803d2107601c0c1c0f00181c0401a84100740c1e081540c0300300d425082c840003009084e07111040d000b1300859040340c00040000052900341c0701d0b5a074a0705200d05c128808020400c0c0d00d01d06100c2c260a94a0907203070014403540d100030005c2580c904888030360050304015a500000303081d035005401d103550010000070700c054540010925019940d800181c41094032010440b801440c604000d400028500d845031451410361611514a03580c1e148440c5243d00002c0c42808030550800328859038445031080d01d5890504003a03c0004d05020340d402d407000d50103502482c42c8041244120000c0360301490000c5c0a4041031410810068030300d950217030503c26803145910503050b0415100d0a0141c00c00b50800b290b00c0040e140501c2c14840c0280200420006c010a125180c549104c07140e1000402c00e480f00460001e10301 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 380490683 1250 380489433 380489441
    0xc02040c050f0304140c09071b050f030c1501150512040302010617010203091002160b041106030c0c2103191b02070302040b04061a07080c030d0f0e0105060307050112 73
    0x40540b20354004070911040100501c1c00d00c10a450700e1040741c00540142e001c2002000044d03641c0c00201e2703507441c05050026401e00700340745813134010010b44031200e454200503410342d480581040c0150300011400c803a8441001440c07070150843c100d420f240c000c02c052025210b8465140d00400035001d240001b02011700c00d400c00d6028047c20340f50030b1303101011040c2c00b601030740041d00c21200602441c42ca080c1c0da6031540c42514086107013485191a242c0103500c1d1400e00c10340140041c1c81b0300c0f9100100d0703240d94454100441c044c802000e2500d554500b049402c90034240c5400c88000c1201c040a040e2001c0c48980007501c0d0003d5018280d100809034202c0200000c00c0b00c201110002c942070f00300014416000324804048074000d890a000c00fa40d600704010844a0f1800b0320440400d0010004e035000440b90080d010301481644014500007041400324038641044110b4403041d51103420050001d1154020082c42580d0b441c001e1000341454400070b40c9502e410301549041080082880c0164035007500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 380491933 1250 380490683 380490697
    0xe1009050d121e0b041a011d0301021902150912030106050a0513090c14040f0905071214011502011b0e0d150506040e1b0f040204031e0c150c02040c05 66
    0xc0e001c143c64800c3e9030004050300f5103441d2284a10310700301e003038143c86080ca0b51035804418140c5da03440d650000300041068000d1000d00083e010740d4240100d0260035411003c141c082d0881c0c0d001003094203062080d860b0300260052004000342c00040d50980b0380d0440a00340c0f07065510900300203850f00c41b5042c007100e0a0065841040241d80e4006000800001130360100081406640d00e1240481448035400042d115510480c1001d000b03007041000340102070707440540c00c980c403845c0c07000c0c080c0300629144055564180500f05000c140a004003e607400380c40b0001c40b040c1c2d4900090003501c03840d0f071451007100c23141407216041c4090640d01102550f5414500c48203268403450065603014035010510007068104c5140340950f107031440c2480d1458002680d4070000c9d0810134000c40002031082400020300e404152203402503003c2c0000700000d01405425405199141c090744411400c0d410b003402c0c5d440c40c03684018410b0b000700000e0046594402c0c01c12440c0b40c3c050724003003400c00124804440a1044c42 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 380493183 1250 380491933 380491961
    0x8040f0503130f080307030c02040e012c010b010c0803040201031a04091a130209150103060504110a0f030e0d05091f080925061808030a030e1009050d12 67
    0x509401c203112141480b000d0740d04000c0c80203034140d1034010080d81c074070400c0e0005e0042411030b0b0a00d8018035094000580c840e0440e800450007008244030310b50b01031000d10850300825a5039016036103050092090310711807107003440d08644240309515404098800504060304140d1621019141040301c5030121000510140c810004034040d0300341180148020040b410a4035071007000310b00480d0f00290b11240c215001018040d4903111411b0240703454072440340e0b0134141034a42d00005000d680307074858130000e910307001d1b0f056545500070b49009014062481418051610300900f17102020400201c41b400355035942800c90381c5904031070020b0307034105110358007510000c007000001d4225030344011098064402c0808540024841140b0304421081d40d80403540340345000d0004009161140d6103a040b003448403012800c0058503041842c1c11a4402492900071030344504210010384000c001040c4c012060540411003000035a9486888503a100d880320108114950b1205d1640d020b5448032014080b21 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 380494433 1250 380493183 380493187
    0x20d06022109160509070f0f0c05011119031b030f140901060f060c0b061323060109080304050d1101050409060f0518093f040807210308040f0503 64
    0x2d070441998400d0b0700203940302291412140003c1d9810720099440c000c20041d103e00065412180c07085800e24690510b00c41008002d40c418004075000381714401505001c1001c15503500950411800d000c440102607000b090301c0c003200d9100310040c010407580407070481e140105800d69114040c202420140a0355003265a400007405040401540104210744504c1401100d840ea036003000c0d54518a81c1901621008000e8001101c901c1c24481e21460450000d01c0000c0305901d448030300d82c002100d694044002e0406e8405d0054940e044010003008100312b100540c0b802e0705040109040c400c00441c028001104250114041d0b0300175800e6a02420750742200300a2195a809081c00d20103040c41440e014000350f481c809910100502c240344100e60020050400f2640c0d80c900c119841d1503010003504c1016070105840349546032207942c00c0b1100e001040c1036141c030300784258181031240e59407004038587c8001510041d152055040d8449540d058107140f030360f0f507845040194070702140e828024014040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 380495683 1250 380494433 380494441
    0x90602030f0a050f090c012a05011d0307150b0d02100206040201030f23060102071d010906050901080706052101170d09060903170d15030605070903020d060221 70
    0x410000140310300c1c050340c0e007480661a804541d0401d80026905e006041c0c008402071102540556182d0701304200040301c040302110051a0140c03210300d07007102110281d458801c041030442070211020381e22820000614500000c1c6e6039640215040c41c0d4000b1000b5032a41703c8000c2030381d6182d0110300d5043d00900341d0f0200415008000352100c4044a0403170209241c0501044d030030216124407652080808210720918188100741035107014001c2000341142700c0d030b01c40407505070784002030081c80e840040003003a07643d4140340620068560a03040075001d09040d60041092000024884080b40d070507007001941c0748181541411380c48402c00680130705e06a140300000701d914103404c840c003600d2251001e40300416124041201c4140541c400c05000076001c580c2071010032a080000050191824000343c0b402440b1208041580c1040d80014100071040b90108240300c118064039900c0000b914003201098103541c00544501c203c52006040341e5400304010350b09654085440c0303000710b0302941c0c0312141e141c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 380496933 1250 380495683 380495701
    0x3041e08010c093b040f080409200a02070b0a02030403080f0a0809010b030606010f0c0b040b06150f1b03070c17100b031002070c030b01030f0c050d020102100f09060203 74
    0x5003910843d500500c80c00030660162011003900c00d031610010141601d401e95200c03010901413000b0300180d50850744143c0c1a0b000981e040024001041c0300f5030007250300140445280150691420a0300c141001000072200b010b80c040740f101c040c0d0380140321140e00c43d12014401c900c0c500560304001d120704000503201c06c050303544601402c08103c5c2a1f40300303c00d5540e4401c1e56401e8841e0740c0b031705541540c014400f00e14a50b019600358130a1107040e183c0f16100308196140c02411200540341a00c0c000454021b2003041c2c10075004c141000442900058948168011240d407180b1640400b502e810550011408080c07a0038000c0354501504035181c104070544403500b081000c00d11052101c01841811081c0342034008901890b260b00c04010064890411000e640b44082d40c4101d100b00d400200181d40800090002102103010394040c6c0301102d030790300e503524210500c00c02c20340040307106002114480c00142e0303000503111074401d5180d00206005c208059400060f001c4450020030550000c000c01c042c181f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 380498183 1250 380496933 380496947
    0xa0804030501050115030e0c21100507170103120e0105040306020c070f060c020a0e0a060b0a080f13210e040c21020f0f091507030c03110f03041e08010c 67
    0x50f6821804203881c2144003060301107500601149019030001040303908149840c03149c19035200c40c2c4091121161404c1c02c2260300302002e0074a0b82d40155500e0091211480c3d000d0559000c195031000c5900c031030350454585c82000501030308004200300e40720710802220b910640983c0d0086903c018255124008150402d032a200580902c100d83c2900c0d40e80010850720800d65129542d40241c6072000e203e0810803c400d03907040052803a101c042d262080011614500b400800c0c03c0103c9548682c12800d03c4810f5008092000d8980c4031140d00c0c04121601240c21185c000b00e40d11011003040500a01d2210103894807101125000e61192406403289039407a0041c0703c580769101ca0008059105900000d00f50807400343c1e03001e00d10725038028420210704520500080040c00702c001c0c0502e0300e1098041140609501c0f9a80890004049810300010940c01014501c900a00301019002c810383d0001900d0b03490003144100c5513200303e40d80a041150400f079000f1409469447c0003401700515056000c0c05d96 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 380499433 1250 380498183 380498189
    0x304032a140f0316090203040f0503040b030f01080703030e0603060a0509011715100308070314030703020c0f0606010e0103020a0e030a0c0303081305070621050103121106040f0f050a08040305010501 87
    0xc10b20700c18034410615001c81d11030b4003020300c10382c00f500941c104003400000703402c0204120785501c2c2c465504008954104003400041c0440c0c9131940c3d80713180215000c0128003060b804540a94800981400000d030040c0d00602c282c82d0944040ea240e41e541c40009940f011903a0045130403008035000818220705200020810611540844151401082d43e81110410031116009a000045000d20010329000003c00700e5500030705cbe0021007005400d042e101e055109542140103e0303030001d01e8102011042c018206071404042c0501002d152800000c3c100307044074070344a410954000f5500c1c4040d4011401c41c3c0e182000581160703100350452600034848281c901040e40490f0b100b070000f80400f0160070300098180d80c40005801c12a107060b8050f6614058003080314561104140700d42c50407a114400c6500071405490090006035400c400a0000e8440329845007554200c6010080881c801c0f0740c041c505207a00c8007011100c0110ba0500ea81808134274040140280c200080000910405412036816 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 380500683 1250 380499433 380499439
    0x405030903012f03100f0806070f0509010f0e030307060603060b0a44190b07020d0e0d02030f0a060e12090306190b040204030c090c050c0304032a14 65
    0xb49858000c0d483d5280b200144881e001c980c20061000c50a0030000041c5030094948800d03202000d4880c8100d0034582d61a41010310340c0c0d4408020481d005600001c0205588a20308055240148160008020700901c9200c04288004e0955207011038408004175140a0f4002c0d008010503a1240b030510058840700001621803003c20f140481c6148403012320300312403041131055a102000a941100a251001461103c062016221200042024824203100000498541d04a0b4449181414180901602080466002e4080b4009040c0c01c40c2d0441c040800850f083d070030310692480003901d0000740c001902c0147c02600801c00800445800c1140d039825058140c4001310104d43e1010300c640540c4104d140d040d407000b00405c07065030318003400d0513102000c01000306440104070081820380e030081e030048076801000b480801c90b203a964410b06200c10b00c2c900d03015142607040e480300d558a021754003001e00850714030394600380c440c031411242444500020403d0002160f03030701500f51a031b000c40405540 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 380501933 1250 380500683 380500691
    0xa030f050c12030a0c230c150a0f0e03011409030304120f0e0f04021608040e071e120902030717060c070507031b0515030105090f0705031303090f0306020a0f0203120a0f14040503090301 81
    0x26007004440a852740c49500340d03038a01804054503000c41c0d42d2450fa00c0c0c0207800d5540c845403110b5112244621500c14034050000b581c0da402d19213011b001440c2091030300ca00f0803e50305110741c01c0311b40c4030b200d81d8240711049a0b26100d030b0070718000041c000e22961941c5d4a83c5d240b2994240100810440640222006403108800c0c0d503981c3c0c401a5101c4c3c8a11290501510b5460780b41c52140e801071074150b002e00c07030980300000d070500d02d9808079141c140140c100c007242c030425408035032403214104481035002c80d204511034241219591125034401c0c0e5804002c1060f0314245003d281c240b00040f50800514004120303001344403205204440c0d5500a01850340244030040c005513a0345291100350380070307580c159a203600d159915038a402d0700c102c42120480c01c00c025150002000100340d01c0580155028600c01695240081005041494822610300a54006102c2c40d00c410300c0e0710091b0b0354001c0000c0300200b241075004008030000c0a0348030b00c0082e9104c1da00140720074060b000029001340001074000704 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 380503183 1250 380501933 380501959
    0x21203181306060503070309230f2b0528090f05010201020a090e0a0617011a0a08060a05070c0203010c0210050c0f041809020a030f050c12030a0c230c 66
    0x941682c4050080b1404114100080b03503840313110360301c07181c00d003401800c400f4000440c001061002910007580041254000c08010500707600610002007181451248a52104e00214081a03030030104000c800c1030242c082402840202100c2003454685101c2d2040008081401005030610555002c4c01c00e82c82c20700140400e20b54014800c0b1000c0c0000c17511118200c074504440c1d851416801400018202e444943c009400c0e4141c40303182860a580d07000210704601e01c2d00410444c0030300c148805100d081d1580b400c00031404042881030300034241100101ba513903a580c0054484084589000b0342640c60041c2400189034003258405809a030303400188103544592040c91214044e5081c1d1226607402040304006038000800401a944000b00020940128940008022174516402500c01421064100d000c024040c000d000000000302c802243c54031140d2002076680c0108414101030145040401050040441c25500540c020031225000003281c488966100c0b80520381c0d4030b0240c40407015403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 380504433 1250 380503183 380503219
    0x40f0510141501122a02030406050d020c1903020307170306130e0106170d03060605130302010e0f4507081e040803071b0c1202120318 59
    0x444000d500c12120607a44502c2d6145401d040310504160601010380c50789000f40055010f40004002150003140c06100b10581c1c0849407100840c140045400c1080140541354200050b02d241e04102540141c85d501600d0a07246055040c4046042c0c44020700800b00401d0350000003828040e1050b41080f079250032501c10000a4003094038000e52140e034000100c020301e01d86c0d0340207148550a10300080b4007155103e585c540b808054100c440b4641c2c21030b0b508000c915405001c0c0302c005042502c0c04500e4404200c0c01030810f0350040c00003d0401c1094510010959110340450a180f0001405210001000402c2d40c00c9140a981294848242501020f03859944060b04200c102e03040030407614156109041100d0500d002040000c501c2a0349004035180039081440c50304c514452030205503282448400504412038001003250548a03a07441072000070031281150781240c0c010385110030f10144900c0080c03488560454452000d100c0465070f940c06a20000840c0385840e42961b0b031140002c2c088101c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 380505683 1250 380504433 380504441
    0x3060807140d151107151b02101515030e060c0403020d080304080d0507030b0f1503070305060607050706090302130504022409130b0a0b030708150105070b100e010803041208031806040f0510 83
    0x2825002d078110390500890700a103132b04214140c4800c4420060307042c0d22034a0a03540c2810751000680040c2c6e8445011006140030000d05801c03403c151001c6042a00d10790009102100c01c4000604002000c4089020020110305864210801c83c42c184514a0110f00090080040c0f01c0c0f214400d0031081011071540c02c02d0714428550103114240149140d50300481540600400303448542c000908100c1140452414002100540781565034907050170324500420030401205a20708444070301d40018400165600660300f1000d0090a8101d41d1100001e41d07083c000e4010800d50540141c90044040c0e16901280d0001c0680c00742282c03030040b0303962141d601c55890f010455840c8049a8070001049070f000d03a004041010020500d010f5140c00c6850744ea4007072081c0195210b2844142181044c40a0f03103e1420980c00742c41c004004505181c40d000c801c2c541d202c9030900140013a040000403440c28908426003002140782d403004ca40080c00e107032402000202900781c0640e02c0d4014158041e10040f06405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 380506933 1250 380505683 380505731
    0x2c0607020d060e0d090e040209180607090905070e0315100b0c06010503100b0a1a09130203070e15070312020c060c0c010c02160501051c0c03060807140d15110715 71
    0x6d8281015991582842500000a00001120035946032419507001c001c0101c180f240f0304a41d40d0b9044185440160400e4480c042e060000b406084d10800780240c40008221401c0c103a081448078030781d02d60150402150200d900085482e2000164840c0300440006480c0e041710416070403540890403209401003100e0b14000c0c050362004040705c08011a15080741c80300484402e05030314901c0c00301068009048880490700301c00e442c0b5004401c00042941102d090900e4038010303214201e944429100f940c078544070f003943c01018802e14000c880c0345503450b41d06803402c0b502803000720340082c01c00b80d6001d9850380100960302c490350300b044181c2100902c08200c2d082122070385a902c0403003d091000650b0150081ea0f2101c45017052092241c22071080d0340a0b000c000791045e10009280d908001c01e0504250458000d112481c0e0b1546103440251198200a07000703d4018424001a040750300761480544941d2107910030083c40420f03507400380300808001c180c00b01c060020802c201120f900e4178001c46080701d9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 380508183 1250 380506933 380506949
    0x80d12050408121e13140a03050f0f04050301020a02011e11030105120a05010c0f0e0103020304080a180f03050309040e011b030f020405090f010609062c0607020d060e0d09 75
    0x10000744440c0f000d803410720790800b500e143e40d9081d8040655008007035480c21a2495040d80c0014031940900044855122210352801d02500c46240d03103031400b5015220b03001c6850a4041c00041420000030601c080c0c50103450028000d540e54403501c180280030f0440030100761080d010805040034055801c2c03280b060841171400e500e60550b0319050420140400e10784007054a8003036202d5900001c0c03020310500f01d28881c5a120003640c5135103070300010f2030900c41d0402141454410000c0c800496094030a41d41c1090061401c40301c1000142501c084405450b402440e03250001c510100c1040b4000c4003502d6400c03c1a40c007003140c400c00502ca64207880c945080300c201402200c00c008241d502c01c1e00300340f006203c07102c800b42c90580c2e1030340815030401003180c1004c413003124070f401400300b070390b00a012500600e150702c1d0280041c4074001080f26100240c1e04c00300d1080107c140072800c0c5803100015141802d0f00106094112203480c2001c5001e0030f40c404047c04039015601e12518800e0003251400c094030099 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 380509433 1250 380508183 380508187
    0x606080111030415050c04031514090a150c09031203240605090d020a0f0b030f060303073906030e1e030414060d09050a050606040b0609010f090f080d12050408 70
    0x101c4e10010091501514080460100700008400301c0e14240e001d0b40d140030006030000b5500c100070012008284041c02c001060b03005280c1081c046885400854a039078980f0700001201c1e00e03148802e0f540d2a0040d84001d005070320804101050301d070580e001e2062000b48652000300760050721030110042c2d00364060017001c1802881480001c1c00d0807003403e041c1c0c40c4040c06180c204c0d902c031040c00040b003002d54071115400600008010094101c034100c1608120b042e8021803c00246e0354401005001c200180d40e01c000d81c40c1c13100003410b80710440802144941e20b04c15000540c0341e50004019240f041c80c101650311603111880f09513400801000b40401400e00036600300750600300540142600801c045500400500804480040501c60a0f284c030788514001c124402a07440c0441c240761006020504c2a481d0140d0000180c0319841150140e080919041c08a4039541000b0368540010350801d84104103a494045500740300041c45c406101030b10f40b280c0340101e40000810007a1141190024090071003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 380510683 1250 380509433 380509463
    0x10232805010e0604140a170703030201140105090115020c09040c060809070f17010b10020a1703100302040504060e0604260306030d0509130207150b030606030606100e03070306060801110304 83
    0xe00084903811002415000724aa85225601c0000144030030174080c3d401c682d0302081050f2f024841c89024460f6803650342101e40c07400b400610031b02ca051241000308208a082032270000e200b4041c1c8040034800420407111800c142c14540c0d20400280102c4011400001c042841000c000466008440c84e180844680300c1c280000350880c0c0751180040442c564885e44040c00702d60b6103201c0e008220712298002c00c0e0300234260a00b405040c41d030650340b4202410030070a01085200100e00c480540303405480218007500ca17881d066005000048002c040c0b4041d0809000030040c0005540800749000780e800c03107495007200300d0700704548410359135143d1680c41641c000410038000c138068900d00c400145142c401c641c2201482050340e00c001e01c100c1d40030303891000841030b1150a201e103001c90314081c0d0082c052450300e9404a070f600c1c040540340d0b901c5280515114404644500481c040401025041d516040e503245011405801d440c000c54885500300074070510040c0e02d51003a680301c0c03604282c004601c014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 380511933 1250 380510683 380510699
    0x402180610031505040204090f11041409040f02030f011b020d1e0512010608010518010e0f0c130605030402040b090606030c2212030905040510232805010e0604 70
    0x500c0c40f80352402d46041d024001203940c3c6a2000e00010100e02001043d4405001c122400301d07580040c1c108120304040c403003880b20290781a1002c821050580d00010305882c0c9060071504120400c03002580352007009140280d014040d000039041c02c0c4200c40010340040324100983c0c13244580040c540c00030300d80135091030901d01c0d442d10135506d030000c80c10041d1508c40c95185003d5442d1003600b141000c119030b6001041a4182112a001351600c0200d4108031541400b400201c0d0050241c6502c102c01d0403003010407158901070003203031000040d020307402140541e070340d10250854104550071b038419490030b0344d1881581002d100491107081c000b000c980c915134031f0740406009134100d214421382c1074807080300e18040d860071091440050b0403200094151401c2c42d1800070100c0707900786c2110b400703142080144110b9565812404040e103840d80e101c0d880300341e90240001060350950b4603040d8466261031243d04004800e209a034070694080240121241d1503000545040c84a0f0030515088142000100407c107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 380513183 1250 380511933 380511941
    0x37050c10051314211c0e0c100f09050303030405030708070305040f030b010503011506020318040b2106011d06101b050607020f0c1e03070902030a05040218061003 71
    0x1110441003a2000802d80c0c48403020142c3d0408908102d902044220494010001c0c690b2400080013130b84502d0012408220100d4074140203284032280d4441c4152016641d00b0700a000c0701c000e000d0300545480301c98020003002015071b05001d5021403030101000c01c4500340030044078401c0789c1180040d4075140103991400b1540d800340d14250108030f000d01002c84c8800610a05038000c0d4000d040307a2a25505101c00c250031511070000f040350f40d8cc3c558204200c0c1603000702c203031031584158074206404000b140c80814084c00d10085072542c80800c80300900c8900c51000000c41740050700301d044448580e255090052001c031034000c00f8920010401c000391592402414a2400010914060505440e010303100540076880c1c54089445800581c20048805d5041140010403400540141000091003001c1202c1e0020096091402c5a4401c1001da5540301001110010002644115583d280c210008401071405076000c9200300314901c0403071100010a45441e02030640105070b00e600307203a210b10943c018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 380514433 1250 380513183 380513191
    0x912010c140906160c1e0e060d020907080604020c19030f05030903040b1b240a230c0408030301030f0204050106050703051602280503010c05030415050601020337050c1005 75
    0x28201074031010030040404400f0340d424440481c0c1007806c0380e080c014158080c2c40c0007040d090180945861505c0940c1d2400300d40c2c1c2d0044e0407401d102e049034a0700000b26001e031003403103c1c2d80030a2190510000000620012000c2014001d907200644015400402c40e801c0c40305a0798020140d02c2440b09000400d8a10000c040079090146e60805600703c81d0540f905042c400810034007001217a4001c0001c982d010309000340d224526000c10002d000c0c4085001410302d00c1c10700c1c510510001480001d000940007000c40c2c1c082e180790401c0720345940e50303442c225100c0022484124011420503000148040c010300a441d0b21a500d9105e4600700720401804403161007580a060368011201250b001259a8035031510703403540381424600752514200740625083d6049006813004002c2c0400070400810500214549800700304031000c0783e15120803004034610f011b040682c00020b01620884c030040a90042610f01d1001c650306c0349091800900c0d4140c5040c0108031922815400c80310040d01f0203085030f8081d583c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 380515683 1250 380514433 380514443
    0x60a0627021b0c09010906080706120207050f0303071211030412020a0b0705070606050f0312031e0109020403030f030606090b0c010603080f0909181c050912010c14090616 75
    0x52404120301e0051241a51881c40110b4105200f04072042c10503041c014090030142c2c1062144a2130901266600c40007881001c040104038001d500e224804c0d501195206900b01e0111604036841d681410b86a5109a0384040419820036064504405c40c0c000c80c9c1000c40c55480d07180c00c581d0703076403511601201040150340441c05100d04800c0021400c1440340d014103070541da041c0d2100c02034074080d011611640c0100d48215200341d0b03141c007103540020f003403240b0b00b010160980c2c6a0b16007106004400c550400c444142c00c8101d8004100419a5805081128025034030100b480a000d00148d0490340ca80c010b41c2c0c00a1040c9000b030103a806003100410720079180100001e1260755a488105c42500601490340c80c0c078800085a031101e00e0110015504510310800030280d480d822004075170760b00b09455005280307850300150100e101d4041c50986c0c501c41e0000d0060402e00c01071150290003000050400d10103d0749500d1100351032600c12003a03a014000c05070905140c2206000b030410003018005084503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 380516933 1250 380515683 380515687
    0x60e100c0914130f0c020d05130524030702061e040b01030605090c0a0f080c100e0904020105070b16022103040b100f03051513020f150d0204080a0203060a062702 71
    0x3241003542c42407480a0700e84e080001105007500c0740003410480f681920100f003103018400000c0d800c025034a09011107200700c0d0b5801014a03400c05c11401c240c15042209480b40000c01040340032034020610384d107c2c03200302600c0c030b402002d44c199121000c0e4058801824054503a0018000204254482500043c00c802215112440c1200080d0b02c014160003d516000050300f0400c5a03240802041d42d42c0c0030201c80700071400d034640c50010050070401c5008c1e8419180301c40801c040da4041c0c1d0445504c070b07801c44490441031070b145040c10840801c80c06080014072501050440010030b0b00b0030405100d2103550302914507200c0351511505400081c0400805480304080000c01d81d213111400c000943c8580064010780203e81c4014a001400401d00340d00c00341d500c01c8000041c2c0e00c0d0201c0d2098220102c81901e00c9180141daa11068043c0c4580c044005100143c00300b44441e0014102e192284200c0840300d05071b950a65940603510144a08808280e000034600c1e00d01500082c030406000c00000014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 380518183 1250 380516933 380516959
    0x7030818190c0510020c012a0204021b0d03020306030a0308180a0b01030b01060513150e120f1002121b0f0307080f070c02010206151c060e100c0914 65
    0x14400c85a01c007001c07100c000400004009500b07145500340096901070000e40001701c105400a1300200c80b030341c0788100d40300c985507203000880200d0711a9021540c0190045445003407101a000000303082d050002c0d202d00c10402800c41c2584280202ea00c14100980501808152580c0548803000003404480c0c482403125106100650100440c0004030b0050520b000f031945141000c2001b22010313040320040203130401c00001136940c5164041c04696050070040d040040c0002c003150203c10000b0340d83e0384207002d0070882d1010880054250582c60044d0140d403c0c012420745050201c2c4504800c844140310b0002c00a0342c411000c1c52074550780201c0c24201450041042a450000d40c0212070000125101d60240440300c07580303690726940800e150401350100301090b0001317540c640c001000c5090404a01082d0485600c0c0d030780310a0440c14000d503a82195808601d000c00240c0342c1c80704081c80601ca00a05015050218000c210b503800054030741d210200c1c24510071010180114040942000a40f0006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 380519433 1250 380518183 380518213
    0x319060f18020c060408120106030e0a08070305090a06031a09010521030409050c030f0c07051b0310110909070527010e060d0c0e0303130e040614040503040905010b07030818 76
    0x201e2017584540722042d603c200759842c078400b102d0b0680000c0c0130113107001c0130f6082d01140002e002d0007180d004032a00340c03140354034502190588544204503801c078003541320014002da01500400040400451001d010014803010322800100c24400c4c05c0d80061700600c49003802e190380d01c406508854802c1600c0c030340313600c800900058074015112200d0386a00001007001c181012811542c11803400c03440301303150004030380307419640380d1458900080303441c14002d02200e039580070022000329100382e03071061203211410a40300035140c00051415000301d18039000580394034403420481d41800c0c8904a083d40030b5400d00318001d1600301c1c00358803e051003000250b240b420342d1080050100a00ca8032404034006841c1d081c000c1c41c076400894254084e0b881030000040c1019110751031816100b801200c65a00d59890030110701a0000300800440c01c0c02980910007400404802003040c0e4401c036030140710076640d40d03402607040d1007061005000a0350984c0481c413484200b001045a611305041214070340c3e0008401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 380520683 1250 380519433 380519443
    0x714120313180606020307030810050310141f06030e15040b060a08010203100e060604052808160909020a0503010e0102090f0d0b06010c0503130b0319060f18020c 71
    0x110842070220780204080c11800601924190341c0c89000d001d6145002000380d0ba0307018143d030013001c1c010f10100161004003e0b8074000b000704002800c0390100c1c010300a108000340417402030024012100c4000408034550000c40c00f8403d601d0803030407078506140c00350442c01020f000c601e4420b03038003c803600004202c043d02c0f034003170145000d030903d03001a003000820061400031a80c0301071000d900520410005402036003101044410200e100343c00d40d6a984005503441c80340d50429a031003030700e00c803104c2060600184003a07880d405842035569540c0d150b1b6521070350341c80000c00101079604c210f00144480c0000b40c210140d4039102400180005485100090070b450301381000703d030169401319032896285001203400001b204d003642c800e611418183c8514204072001031455052101e81d81110003006020400c0b6500c080701715500e03958064507242015860351080e940300c0004e10210360000300d4100a81710700b4003203d24030000600407528140450b41d501c0b8101225100c443d6003400003070f56400d81400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 380521933 1250 380520683 380520697
    0x50703030b04051005040506040b06091017040f0b010b03010803041701020705070e0a0b0f030c100c080304030e0907170a0b010e0a031101090f060819180b0106030e01020a0207141203 80
    0x103913046080c9018401280c800408040c03103581010700d00502c40d1100400c03203900500503251300582081e8a24145c0e103070030103016010340169400c0208030a10520403600144103124021285140c0d980d1054041c0c240030a008004103500300304402c000e1068101c410320749010b5400c0000d41000c41648a290924403580d02c50800059507804228200015100c0d22650700e0044500b8808011044041303036a070380020001d2809101282080035610703008008502c4041d602200741070307a901e03052500800102200c10345070b01420220004c0381c400c9009100201a4940300308000c00070b82e6840a490300a005442c1410b8103020402ea01e030245038840d0302060700510300695021001c600b204000420708030382e59001090840d480201481659480010346420481c98a0150740110350b0012800003031200e1180e48a2110030000715204000d2a03c1001c0c0c129503031a1030401071110101c550a00341e114103004d14005801c0000140312010441c000a61440d50182c100000680404103151031036000364 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 380523183 1250 380521933 380521951
    0x10503151002010e10091502130e01030602040501120905031815040305030301080601050a063005190c0f170a0608030a2c0603040602071b0909061b0f050703030b0405 73
    0x241c100004c5010003138141c000c0d00c1100c08020f00006602e5500c000c0b070b954945640100d400103600c0c2540e0044a1015014050310175038a503a03960342e480c1c844002c0d48503202d03480c0415402107405100c2c00321403142c1c0c034465801c14003462030564008005000c000441c00c115912900c1c008420b0a003001e940086c0010b144103400441e920350400d82858602441640598442d0054120074045030764440044d580b00303c060180758410543c0c04070f01400584c40b06555804551501040000f0280c07100546481442d24460030415801030660448420030304507695008030b20840103440c40d848017001c000e903006050312000241692148c80302815544141d03401000560143c20b0f1a0484917004038105001015441c0300503201141c2011445900000340082e21855000c039204090140c0c004940703e103602414140314406440f080c12900815901c0c0e03003640c2c2c291400c420303420070502c880c00851181d03059496400d0301d41c4003941c0854141e4440c4400b10b04141c1c03220455012603c1c2c9029040c014030203e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 380524433 1250 380523183 380523191
    0x20912100606321c0c0302190311040b1b01020d200c070b071a010807142e0c0c0806010e0702031801030c02071a18011d01050315100201 60
    0x40000b89006a540e10000858800c25000c440c078052001c25203840100e101e10242d15640c0750b40c2420004d400c1103052680d003509184000000a82c141c0c01401e0000c0b6000166040483c0840700324200c030521818070480328000c1105124003030310400580b0000125032000c594044006503c5c03800d80c2c10828191140540751941c0540d18000e401c000d8a0410302d2480d1541018220030280d40d4a152501c12050060f1000845206010503010240840c00e200301c10101c0d03a5070340b02e28059661b01e451203020515905030a40101c1e03407a10000703402030b03541101480303408540b81d91071010031004c011944001780030500c80b490000070704505225004050f45e10251035070b58504140c802d480da000906d100210f42040142c0300494401c002070312100c907028a40020010600007041e4a07060090300007150354010810281002942040141510104600680102c1034140300550365403240c0c01c0b40c1c0403862403d489040c030302d501c290090360b44944440641c81c040004107020960b5440942d2440b0010703512 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 380525683 1250 380524433 380524439
    0x30602160201090510021011070f1208060f030a08030703060302031009060b010306050d24060b0c100b0603040f02060421060b01081006080423031209010b0d060209121006 75
    0x28540c0101005c1c1e80313252111140d404001d40f038028030482c0700d28040d03990080c1552800e40c1c0c419641820f9001c0352135000140d950800840364110801000005020340c0001029030034001c1039010f54120140c0105280701a95540307102580000305103108256a4040000c050b0340c3c01c105002c404403141030001420200c9091080903601c9010400d8145400d1400822403a06d580d0340c800421034101e200c4807102c0074900400000f227003402128068081c104003011034454103110003850b40d03406d06411540304c00b0076595036809032481c41c11100d074080d00038400036001c980036401135400140300502d440c0c9402d0311002ca02e402655001000da8240190000310300800c804c45c4a40d0041c44000d0a00351803030310740b860101c0000310341400740908201c3c2e071901090801008044120326640c5010a24091940000c3c3d81640d0b500a40c0d60004014802800304030303880410302c1092a1364a000d000301c100c032b10007a12100301940c0301820254001c07420359a000720380c80042c000704940c280658004521289 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 380526933 1250 380525683 380525687
    0x9030a1b080d0305100b035202120325030b0906040b0901050103020c030705060c121f23100806040f110a0c020a08030a03050a0f0911040b0a030602160201 68
    0x30104000c0c2c01818640700070310805c41c07001510103045441904425513666038080e0041e240083ca03600c111301061a81c01500c0081ea40080d40e80580c4003465120350045c80300d5050310108004800035040560030581840c2510740042c4025a0b020ba01114020010500c814010070502c0c2c1100075000001d5030340d010143c5610345524107170340141040310b0501c06414500f0004000f800706110300d505042d40002c945807078440c00d2041e80d0403950071030150f41a0b0328100d86940440d5000c1281c1046030389008000076002528500300702c004e20710318115001e440b81000e100c41401e41c84e4a4904004002c100300c1100d07d50740c0c48110b04480c01c4160385031035541c1010414801661000708600c0805802c00d5161192982c10340c003a104d81c4000c0b4500b2000d601428000f042020515801c604058000014002c60003078264007c1ca000d1441440304000c04004960400129525004018120580106981d040d480c043d041641c003804000c2050000d0395803540ca0301c040380d000020300c8040b00601807601d1300b990703 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 380528183 1250 380526933 380526943
    0x3060b040b0f100e010c1401061a3406050703090302011a060d110c030c0a0b060a03030c120302090a0611150f0103060c0c0218060405090f100209030a1b08 68
    0x6000b074441e001a48203503000103803440c000c9101c01c8100016400fa21519070710940c11603202c10342025408001013480103950f0702900f814061150300003043d00c0480e0070400e541084a50a0303035165080c8183e5039101c000d104070660358003031410340c44484200440104d817140c40b401d401202d50b620000785040740c500e07002c4d094403c8500d80303d002c040d4022a041e150f03100c41080700d00c0c440c180c90001400c030103558030030f1803180604942e02505110224640c02004000600740c61103a020390541d0316036903981700400400341c410b80401000154800400400217104040061829401d0f0401504101c2d00801280c00c07c4803c0d030168000802c042e68510b54104240300d946440881c12004800901e404804aa190320040c8002420180d0311240820f4103842008030f084e515a004080c0c400f40c6941d0366504c4c5c0840c0c4203440c410b10862505001c14804800000c10b8030745020900050302504c0701488192000f90861000075416024003022840010a2404101c000207211171061683c41d0901e1042c80c0742c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 380529433 1250 380528183 380528201
    0x51014090c04150b0d110304152d0905150903091206060303090607030e04050a02090906030a03021c23030906100302030c04330501020c0d02100c03021603060b04 71
    0x6149450410f07600c00300b1050000e81a01c0602c0701e40c0c1d42d12421008104028403030110740d58107002010051000300140320085c04461300c1014410f03c195030204c0380b0004520b120510031344251446140d000c034504256000211041e004009071a00300c80c64103250f12120504407130044594000040c1101c1c18604000d02c03c400380c0e006001040035203001004240e582c400d94070361034405c1c0720100d050804c00d44503d0002947c124080d10602150502c0000140650800885984612504800141d81d41030001c0c1c2c0240c0a601580200304107140700c2d424aa4500100c20200704010325080b0041e01e024402d411000c00100800e6069039900e400780740c541c14294090501c00074000410300c02c10240c1d4000407040c0108100310350007c1c0102c640c030070a00d00b0707400404500d000524100040401c144042e001d620860b0001e03026501e0ba103882c0f1040bc00e052000f803400039803001656100591040c45482c0c0d00340d4041c8240120b0b1580d01e42c2100c1c0085820329503100700c490a8075113244a4071070070180103072a05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 380530683 1250 380529433 380529439
    0x100204140906030a0c0828030c110a05040e0a12020706021002250f0323040b0d0e030d0501030507050f01020a171615060b04030503040b07051014090c 66
    0x4080c20080d03400d0080040d1100355124051070710100d0700715642800021020b69002d04584000c5954072035154a905c511054248181003101c0350b228a41082c40300d14103655496960b80c0040c01050303548500b03101c10401542d07040280107401044030389540c07042018007240325004045c25685803600101c0000107502146c1190001c5c4402c01c13480d500011020480601c0d11009602c4190556074680081c1480709079501d41400c04003514240300a271107522401d0f5000e030b59180402518118000105400c00c091101103000070002007008a84100c003408058000c0507000c600040885d000a2a43e00504180410340755a00010010003208005800c0202020384620074800f100a0020b9101c00301c0645c003611100450003d000081522011540c0c6141d4a13004581d41e00b10f03500300301704401c06100002804c01d20307110300407039084210809e840480e5407000066240c40c0c01d00da002c04440d048038004441a00c161241501c4d00307c903130f014044484a05001848080c6414074100c1e103030204400703070680 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 380531933 1250 380530683 380530687
    0xc050304150e1e101b020105010f080d110f0706090f0909030f03050403030e0715020105060406030224040f0b070302010b0d0201020c010e06092809061212030207050a030801081002 79
    0xa5045400300d540441d4411110b9022445103c015403d4100035003c84480d03a80e924090003081c0455090070030101084803940200401e03070321049442841141c03806851015400f0780706003c04241304480458100100e002075608403481c480c45249084502e41100000c128103907020721406070850001c000501102000f07001c1d152031528080c0200c032018401004054881c2c0008080c54003940001c00c1c0085c10b54100d5480c107585c0c884189002c00700070800d00043d42400c0208031180f400b0f000b404143c036002002075645c03041010150840c0102407955107a01c1109000015142484400203001000c814a000340d8401c554500203086482141000384581000007c0b0400350340c2c00551480d00020a003820b003440c201040000d42103010b0882403a60103181c40900411841700703c0d4072500301c0047e42c1040d80c0c0e1369445858010a94290340204011004040d0a1002091001e80303203042a10550600520700103881e190700b802c041c03004c4410380c08224048010084030300100005059403404202c118 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 380533183 1250 380531933 380531951
    0xd0510062405041d0612071701060801150b1c02040909020f01020313350705040c091a0a03020403020d0c0f170c040209040e10090b010b0327010f0c05030415 69
    0x6150081398103940038403541000000340c840d03180c1a10485401c0001d80844a00c03507551a0b824080d420a0040c84160b5400c0100000301440d05004004103c180003c0310410142040c0071200160001502d0407040c0010b00b41c1001086507520060020b4196680e0101d911500c0307005000e030011080d5035141c1154000c005c00c070010040003240905507100c3ca40c1c254480d0b0740c1c1010288501c1102600c0248141c48181c5402002000240f210101d80040d42c051041d209203107170a44421140b88100d0030b00c01100b0742403140c44451030000740601a0181001030806890350080f58000031a40000c440070340d4803d40c04e200d0803940390311a030020401074050034030342038403482c0868540c3c0362880104c0c003490b00410b060240d0394032608030342c141c00401d6048031780c0c81081c0040c1002404061000340c0d60542404004074aa2a84004503480740342d94003541d03511640000c0c1c10b24460410150b10302c02039560f40e6000603111103140142c1100349a255107050312420103051525481d00f50a820201d010300e090401c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 380534433 1250 380533183 380533199
    0x14090606150a08070f0509180108060c16080901020a0f060504060e070b0708030417070b0a050a0c0c030e0a1a250201090515070501060e160810050d051006240504 71
    0xc80d480080c928000020084041003a94140200c02c0c0b450350080c00342450305c503000748c8220410704840c0e03101e0442d203642e11001924400381c4180c0c803865040512500001020070f40d104000d001410040c030480b800050b240d03d80c1c180c8500d045030122080c1361650180824801c070f42c095844d03280701c40d00c013419910b403418014400d10300c25010300514800c000310009041c030540712490343c04010001505581c4010501d4800c00c0d500d001c580082401d441c1202044600d44244245400045c10344c8030341d0310a070681d440070307160710060302c5d00c1c039a100c0050240422100408110380002800f10010940c90b54145010b076960200010b41500443c00819040000f42c0c0c0e120030f19804442c41074907642e0a5102c5520301d0300441c410004003410540c20134000082500c070b84410648614551104480c1c01690f0101c100d03901a02070704d18800160780c9044c18062490204030840d4114401c1e400c550a01c0c11201c1c100003a10869440100c1d4001110008020b50760104051810b210701460014545030900b408 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 380535683 1250 380534433 380534447
    0xf191e020f060117100c05040e0c03100909050a0212010c030c02060609180715080a060501170c0d02090a0e01030201090b030705041a0f121807052214090606150a 71
    0x4c3c020103c01035001100760706005010758904191400801c0c01941800301c00900b860784207208a181881004000a81001407042501e00800c00710300c02c040b085181030312030300c0076101e510400e54803406204402d900607a00c50401404c42001c2c032001140784500380c0c90103412626440c03100025500054100000399030b0707103510254800e2240d01c0040c525002080c60a01c0c01010341c1000808c002503200240445401c010709071310a03c0306440506c145501d890044540744407109101c92090100404240c00108000203441c00107002480141030004050005500000b40c0d03100051030301a543c010b1003956405103144000d0066100c800b484c504240390014594030891258012501c400c413030740c0c2c900c824602e0445a0f03042c110302255450b5043d510454407038050907a20390a1200c0541345282d28001c0100e03100381107034001408000814480d8140d00008240e001c1d00c001d5842c1d0341c0c11034900110700410315900030300c000c1d8000e003180e02c0c01d00180807d0150760050341201d00380c01c2c4500340341c03d580008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 380536933 1250 380535683 380535689
    0x60402040c02070e0103030306080d050f09090a3c020f0706090c0e042f0102030405062505030a020105090102040312110a050609032802060c0f191e020f0601 69
    0x140040c108a0a40d0101e080c00c0c074139004060301c5070101000209043e819040001510009000e8803000c2c0c1c000700f1305813441e1140e0306000c0e9100b03200b48140016864003145003540190a5000400c90500ea607800c000c1a6407540440124940f030001c600c0b0810011602c01c050341150070201310320f8124008050074460082c807500a080d00e403240d0441c4208001c036403040b801400c1c8080c40d4510360070986010401c2001841403090185c0906400da80104a4000200742041042c2c019500d064184801e100003640845902c090342c0003400aa0741032040f0381c00e56200030500407009941c849100e000000d0a48002905209060780144814030100b251900104924941800d0400f60100649821401cac01c5036480064800d00070b200c1000078010b80400200300c1495080406a0044442d4204410610207800c2c2280103a000300000741c41d001d00d16000307000025212010034145030210980321154244422800c00081140c0441e20103e008891100e40e80306d1030b07001600e140310349003020950300d002c144 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 380538183 1250 380536933 380536939
    0x114040b0118020702030105180f0607080106451e050402030601020f060f070e0a21051009061505030102190e060408070b04151110020703050c150f0a0b0102060402 72
    0x4042e641c00c0361042e604488825602600030301182c5031003880b001a104032540e02072000c1c09801c1c02c040d50359a0100d20144108090307290400603034200907044601207000039800c81c1c194100552454000c00782002d4180007401c0314010100c00560303180043c0d4840703071503004d05249103418010100c8005402d1406098074000d450042c0c41e0359613103004030720344041c0c555a02d45034041e010034804465030300795a5510a4090b074a400c030846901d03109008541e8018415110803642c00095000d900c03115001000441d401001102d02501d81d42e002d520441d10341071000c440c100da803012845103032158140568000e1000300d0086050410189043ca44500048900000c100c803034440c061370fa664442c01d4402800c500411200081c2c0c4a404205040e4024007034602c800005003a00318416108810000e40856400064040380110a08a40294200d410202c083c0b00c07040c0302c4000030034000c1000d001c0c4003070240104102c5007004801f21f607031100c010340400c1010f420000681c07140d0340c001504035003080d415 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 380539433 1250 380538183 380538209
    0x30507030f0f02090a0606020106170304050925030c0207060306140103151703040e060306010f0b07020103090b1302040c080c071709030601031a07090f0b070501111b0114040b01 78
    0x703140c0700340706031000c410082d408403138401807080081c1144e03c0002924a141c0080050301d40b40c0e0b00031002d0444000601c9840e42c420041400641404ac14641d0800c20102c3d14204001c0c2443c030000807110945050030009558021a16103030358100704240c014880c0341401c002c207030304242e4103680014041c84085d06044d1108280343c031301810000f51700c0040003200790320744074501d01102e06522982f0030300c50700d1545841500441c40758034002c55554100d5200540190503540b0302403501d4003d0304840b806030705160b0360b4802200495130541000384a89611400608501c031240704200840c2c00e01480c400c100404038081141465160040720002500410b4008031400c41003503c0c5405d10030001119054012040000301704201d1081ca0740d038403440104110b50a40d40c0c0c01d0222554141e52084090607682203a0401c054641240100040d50240e40041b40319182081844003ea01081120880240c04007060307201075005c1c820300040d0b204464180c10642055102ea40312140103009010460ba00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 380540683 1250 380539433 380539463
    0x302032808041e120324050604030b041403040311120d0509010c0c030606030302010b13020310030b0a02070c03051606020309150c0a0b15090a0219080a0b15040f080703050703 77
    0x1c0002c09420140d2042c4d12410244541100801809203000d1100c4800c0703209500800111101c0c034985c06590020307080e46e04040c0f0b1a100c0c0070304040c000d80140c5800003005240d04902c041400244090f501500b0400014103504040c000304119403aaa000190000c0340000e202d19400000c6501503c000d20b0216801c03062401e251404611f550700040030140307484000000c05406411200c0321200465802e2950303403c40107000143d100072503501c0d00703255440101340005136505071015041840e5040c014100101fa56400c05098815041a911540f1103e403648800f100c052010010b0189480918246030601000c56412204070740501040c000100c0d424030043c03070802c0702001d1990021041c403400d080039038203d1503125880061a0140e42a0000955090000e000300c070889601040c05000340c5d0700540c0d04580e1107401130440702d0816110200701000c0c0c0d03144010302110840846400e55030b6840c0444d2622450322a5201110304c1d0000380080000c91004034501303003269000340e51003400d60750f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 380541933 1250 380540683 380540723
    0x3060b030f03030a0506150a09090207030507050607090306050624161709030c010306030506071805030706030e010e0106061715150d0f061a1b0307030203280804 71
    0x1a4642140703a4400841040300c2002640c010500554080d1540d64820307001d42c104503201e00ca6804503101140742c200c0d007008608625401088114040d00d03040341400c005640c0e2505044041e10071200144203090140140401403040903006070007110680c003240041c000fa100c00d40c1c4200e0011182e8a0045406c84408903030705000401c1c50303808102c075015070f28015120b030f200d6045504098040e10034810110400d500038440c01c016650410f00609050307880c114110340340c2540e6142c1c001c5007140c6103c0055151030401410000e0b00c6151000f09240c501d00341c00a0842d560350a80041aa04125003000300790b81220010301c503040e01f107955240c1355607100503600317049441054040d00103985801c176001180d041d10103448401c8003048180900701c0c3d400300c45015100c6900800e20030103511000010031070014802480d07841c803400c0448948070f46094901c0d046802c0600158096080010380440c01c0002e484044803078002d00a80b44d100c8810f414005102d20741c010402098045120000c540d070320 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 380543183 1250 380541933 380541943
    0x603040501450305031612181b0b03011502030c060f010503060f1005040b0a090207061407030509030f0901020a0c031412030606070308100b070f022803060b03 70
    0x1c5201d45298120100c00e0840710815810380b0120545941215408614181c418031401d80076070f00365071200d007542c448240c040890b001501c0c1e0403040c0071800020081155050041d4034034904005d04440450b0143d0030f100e105220005815001070b0480001405405038a801b600d0544040c28010035050b415000e00740d22f5803169400d50000c510402c410001d143c044156101d059400c254169a0561030740207410303400010684000c800c0003c83c400034800c50810384d0144005050041108026550300d07850341c7c00302d03400081c05884050f00c60307802481c002c101d803844a07000220391404100620785452966240d000f18240c00c1c01000d40015220320580c402c00080396160b40007560429216903d1070001c031a1300c2006404440d50281d1481d0019a40600381901d1040c0f00203411030f403030b0210a50b400ca0302a075005000300390950140e80c003c01c1000800c000307428039a2080d0051390b4607880b00d0040014184221645a201d00d4900441d101d5034584020ba950803039905c404085103070890440000d00706 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 380544433 1250 380543183 380543201
    0x30703050c070c150e0f0901060e031e060a0b18011a0408011a01120608060c0705150108030703090e0c0706200c01150f06020601060f02011b050901020c0901140603040501 75
    0x501e540f103003c20383e0041c62111a9040c01240c483c2c3c02a00108000e0242e01541d640c6a107034001c1c400c0300104501c034000c0390310890820008013074507401100b1301d6803121440621b08160640d40d00010401c80c05640328403c070b05080d0005c45044060804071030420310908014050351803007082c09482d01c01c02d988a42d0580e40030f042240024485103280300b1818100d4180c1d44401d038005000404c040c54500031910031074041c0c1e030040c000f5001a5945030140c007501e9204020403a1244a651080d254200240329040d004e059800061599551581002015440103411500c6141154014407450f1601d680443d05001d40c020030104000742c13142e6044908201110765030104020006940d14000c0c3d0642c031a640b6403944040070442940c80740707141012a40305004101c0075074040401804054000d00c0001c0140c480c80c400031a0f004840d400d1032070680302c21801c4030041200840e41e05015038051018001818054403084e081e50b1519001c40c5480c2c41101c0418003a1000001160900000390045a80 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 380545683 1250 380544433 380544443
    0xd17011505160b06040b0406050312070507050a15080709050a090b0d0b0c22062c0a09020309010b030a08090103020711090f04120c0515130c0e0a0c02010b06030703050c07 75
    0x31000040c03c02404954084500b203114618010100c1800d24040c03081c0d20903148082d004280b000101c070365102d0158400f110170386007803103a018000707950303130f04c40c13400d0006400380c50b090303801a0407001c00123041d8001c0604500c1c1480b000c00810300240d111001c04000700c03011103002180c448000e0010030b8903001e100c103000d000244075000300201070010704020941085410f008014040075540c40e014140711070b0140c0c100081c00e44e48002d440a102000c22101e21116513a144030300a8240002100c4001c039a000d400555000300070881c00750742c00e00c9515207600c4240d01419041a9580c4d558995200303403201641819404034a840a0201010521480e400c014014113001d00b010080507030f80c0d5004440c02ca4081000c00754601c01c5070300c2051440b035080d51043c0141540010386034072400040d00100341003025200481c10fc400f0070f072410700c804000c02c10203c002040b4102046104203031551411380c001907a0411008070a0360701c1e28800c0340c2d400502d074540000e4540341e2070300c3c44081c4c0c85a2000580 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 380546933 1250 380545683 380545717
    0x190f0507020c03070501050426071d2403120a03020405090901061a0421060b06030f0403030507020a020306010e22200405090a0b04020427050d17011505 67
    0x600c1500010300c0081032030100c044a50455407013004450901c142e02884d0034203050071100c00074045010310851040c08940080d40e41b125206c08000b610541d80d10740c2541d4424200c0c00f400442d00c1090301a80c403e2201c81719400380c0c047d0100103e9920308103480021900a400103000c00c9580c402c1e41600e01501c001403090f0000c0c06c0c8007082c24042d04d01405001d8105282940d0110b00308852411242260309000e5400c048009140513070000303000742041558055240c0d0b00701c54942d9504030086124140b15040b109980c145070500038120b8100a01d11002d650144900c0c2015a82c006042c174112031444049024669914001c2e296186081910300200c1480d5000401000b03500641d000408070720940c3c8000d04103000041005441080d110415680c00000300705020698600210754461f002402c003207411030811190700e000c03141800c451141c4100041c000700400000b40580c4180400c18a07060040030519a000114170303c0602c00d41040541304100c501c112402101510000e0300b015050380 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 380548183 1250 380546933 380546941
    0x22101150b09030706021554010c120504050c211204060c0f020d080d021309020306210a0b070f020f16090c030e0141190f05 55
    0x208103a00300c2440c0b24807a004600340031841328130010f000682401007801e0b20009403504012044640d40d901c016441d0050110509120201b141c503505007030007040c0d8080a0761040c0c2020018910078849040130503a41002a881c001903440f04402180710f03c8488005002d454501c0c0082c5000808400f00390081021000102d54607910680400260403050556859070b0340e818080000f4880e5000f43c0c008195813804440c0811400c810524441d88050800030020720252601c0449402070006030103035540024841050f00742c03c0c03521000514140c0d50943c00e41c204140082c005911810100d15a0941c058481000990822031610340700c1d0420003126041c2840d2030014580c01c1c00c0041e81015204040074600d019100041e0b2504c51409400110040c90078031000a0283c60441c446400300343d107440300c14907a0042071060f5040301c03140c0041c051030841070079914074114101900700000103185440d280e040c0e11010300542e6108040340240e00100080b42030000041c0b0f41000515846440e180801c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 380549433 1250 380548183 380548199
    0x2030a032c01020d12200a02010e2a06040b0d0204050a050904020a1811040b04030b0f130305030a020c030d0c0909020a02100203040201200309090c0702210115 70
    0x100500c49030001d50300040d1400110000240e64144180d0060f844945501c061520805403580c030202c0c10140030480d000c100d0400105814403c000d1100c0302400120000c1c400e40910904111210003009003448a4105041080894000003520801b5612003003101c00e542d0744200310b0f0080c04880d20030740d44805120311120001c1d0030500919005050000dc04940c0d032a041c14514400e135402003441d80f0302414124247d80200f000704040c803005840d410101c0180b580d00300500080d1110840d030307580329032031030605110000d40640b0020000058905100e042034609020117007150f098140641d5a465a4401000900c200c009100760303400007094851a45101383c002c00c2c0c00003c255039240c1c2d0940c48d580688102c1c0b0032071000c403026038025400040c0410094001c4d55019005042240130500c0780d05900004441090f108151504002101009803500c0703911160800031070200b00781421a5a03010a00e104100206813103204c0704c01186440543c001d40000015000412a0b000129641c0c1c00b5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 380550683 1250 380549433 380549447
    0x52b3c051c0603150f061d09010f0c020d050708070606151d01050406030e03070c06021e0114130c15050c0c040504020a1811040f0311010e01091a040302030a03 70
    0x203010040c00d1a4a050721901d4100d0080c41d050702e80120420440d070300c078016000014000e84840f001e2650b191035001030300c09400700101202010034000001c151030854a01400c40d440301d000c2c2da040900e03001c04081825400940c140c40700c000c6003003141da10b010f9030070300850b540100c3c0340091a407402c21002150401c01c01a80d802d5000103602d85050302407900d856032042804071503441740003030b071300f4842006454460b8000e89441c55400040e41e02c0c01e02c190300d0303140302817001e90042400b50344001c40c071002400c3c1d04c42c1d1507c40110340303800070045400b400c503500700400c4026202c4026510020800b8003400b010011b21300050144044c00d03081c103c807030400604035130020200c44603180141014511a410035009252140381d005102c3c418003410030401c0b0107081640009084220360754020350917440c620000038800b0741045803c0c040d20b0392852400130203000752071100030304100500c955480700766000b4042206940282d078150121040418030307034a80780a55407000c0c1d414400c00f8a00b100f816041a4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 380551933 1250 380550683 380550697
    0x8090309101707090308160c05040c050a021c020d031e0c0305010501090e010506030112050f100504110414010513090b010e0711060103051203130f052b3c05 69
    0x400340d02d860340e0b040826144030080b071101818065040056000c12803015049005031072180c5061001c07d80c5410101b001c07620508911004101d0006507c0b8a541e0104001030407060300b0031a03102c2c41810f842000f5103420320710000200303068455000b43c01499200c102c0b03002c4035450a4041208211409004010300380c00c0c81607030f012074481c0ca00400e40030040c429080c181c3d0030203080703184ad591900180520300c5040840982e103134090344040340d04400d400e1140352042c1560180128140c101400c0c06000c1004040190b4401e6240009014a01300c6680100741128400c941c0e8180c00c0f90711450b400c000d04914240144800010b00000c22402e00d5242424098107150380c1e0103124104a1150540e81c4100780800f03000741d80014603440001c0c405100950744030344186d901100c102c055680d58038020400c000100c8090300040100040f481c0d0152f0602c8580184582103045050144c0002e8100c0030a091402c1c400c4400d8901d11a001e4040c83c011100e525901d80300c03808000c61510000c0540d00300c18 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 380553183 1250 380551933 380551967
    0x120903022706100207150e0d0606050411070302061303020c0639191707030e15030709030f0609170c07050f0609010503090106080d02010207020a0915060809030910 72
    0x1d070108042d803d20155403903150907150003d0007400d0416000b110003000540c8004108144200120040d40395a812112128410303140440c10600345001c000c252a0207100241280303c1c02e1140f030000c268002412a0400d81904000b5001c2145050480c28104002c7c441608807100150360105218100c6030f883c0c0083d03038003a05918a00b1108406100640701303207024101541f14105010103180c940c0c2240c038285110380d514502c030ba80200f80e102019040300340c059020407942403000c251418041079400c120550f0900da2807840c07411150207807032524580805802d00e210780c0c0410041044503803024000300d0700b120080c40b40180c4207807004202e9200c0c06180015020300f40c8006074909041084945004005041d03900b801c006100442d0380b40c10040001c1d68035900c6140004041c4024003107078180e441140c1c000b40e0356030704038014407400d22899030020840e245403444508582d140b00141c44c1c19907070149481415921580c072103920b540105040c5a13441a001218000c841c1d4204c0303440b1801d030102d8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 380554433 1250 380553183 380553259
    0x330703060302211b0105190905031006060219120c03020c0301090c032112020d0902040e0729071101020a06060b0d0e010203241c0c091503050a12090302 67
    0x10308000504800c045005d001c91410f0100f800c00c0900c0c4038145980b0350380d0b454803400303043d40c41c80020300e05408000810130080d40c0d00418000320b0f506020f59506403103800000c6201a4a9a07140b8012601c1107034810104003a0002450806200b4094001c1e6550018001c3c04550241e0400c9000d480940c8000c4541d084040320f10551130f0f020810003030900d066900c0d0980c190b00746a40c004041c2d031091440d510320959a0801e080160303114820070310036114000080c1f41407401c100d0f203070022164076005103940a6501c0d5600c000500c0c00c3c01151601540002c040071044e00b2800140c0ca48580c243d00201500e0a000020880c99a200082d00c11000c940d00d0600c013080c84c50f403085081340b1050780d14155a035090942030790640c800502500c8502070103803480c2c01e03030341204201d4801c100803490211001148010108118991400b841c100003103c12100090f10307185a540c0b03507480c000644e0003003051a05010503c03009001c1d00e00c00d001140c0140c0401a0030400d600b0420a50400500c661048006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 380555683 1250 380554433 380554453
    0x1050105030d0207091107150c030b0a03050622020d0303140a0b100e060d02042402280501020706020301171608030403080c16061133070306030221 65
    0x22480502c1095401410303500d82001400c60140008180e880c0c1409420030040780010b404107004c00c411098150700290b4840300c04001410340d4417004003984101c4814000b400418400b04007190490801e14940960b13051801043c00a0b01c400e810103035001103100041028160150400f0341c040c200d200c002c00d40e80d070f2462403550480d4074940c02c068104080800e120181030080300c80e07185c00c40000708503504101c0c03441091b100340c1e4860303003103c0d4130b04401c0300c000f0303551031140035180701a1415400034002501d010301c86030310a5500d60f11082860005900c074081400020340c100c5504d41c0c2c0105043d5170b60b40c4c6400e608403d81100c21009e0700544030721440034115909640103a015146c050024518143c030396207444040b0f801241604105000e40000031a020441940c0d0380300504558030b0300c010302e1810059250505207261400c0d8400c01960740510403056003040030500200301c110280e0b1640c2c0354200c04500900c0540c20007500607034030f401450f500c8620120b00803a042c4500080307a4901d59 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 380556933 1250 380555683 380555689
    0x6150109060e030708010c02160914060d1b0f14030d08220b0f06011d0603010603020a09051c020102071502030405040911130b040b0102031204060b011b2607020f010302030901021b030c01050105 85
    0x1201d42c40071400203003034001042c594901371006000d46402901000d890040c850900c1c00d661400b0351005070070701455031040004860a911280f003003641100503001d20340189402401101c0024504090f030807048451441010788440300c4040c3e103400c00c5014400d0f00e0300e40c1c01c02c80e0105003503502d940810583c1200d20000004441140707245080070307100f18110792a181d0190007a411890b10b110074000d0550002c00e903a11040b44000341c0d28060402d24400b0b0000703000280c288185900401e028404202e8075181b09900002120200e80c1d040c0d50006054005040c2040d08400300107042c4c0d40b02010725450442c10195030020806c100c411141000391040c001c005a0f52441421404c14074074100c1c40000300841d14561281c0296001818403502040305000e40e0607094284400c03c9924031507031100300003840910400010015484546289007802c15000686007040e030b80b4503181003580010018401e01350a405a80418103d09254902031012480e0745450360020062040f0395840c0100002e445d00e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 380558183 1250 380556933 380556941
    0x706020a08012612090d150207060b120c0603060a080f01090203010c1110020c0a051e0d0305040807260705030d0506040501050a0314120a1106150109060e030708010c021609 76
    0x62140103140300d0940301c036920029000f0800f8560311403046021b98000c25000007401c400c4410340180181d8030b903094a4100c080303403489401140140c00d02840241859800510010484400c8a81c10744950300c540000b9081e041d0b9400242d1580200c0da2000000c0905420a00d43c081c4224000c0c880e078001010100c2c0c008110000481065000d0306561039001495070040000744202d5090742c4d003804140d11420f240c4041040c0c04002c41552800c56071100d00c0a101a031200001440c051000e0b040c9601c490081c2e002e001c50241032201c074040b1820b000c0400440008820503c40040d0b502c9404604250340c036600594100c1140a00b407900146a515052103401d0680724014050024181151030b048007407542c11010308582c0c49501c0d11055100142c0d800761048a04654804210000c10800d03d8282107000e40400d40c0001c200011000e10703070f0026554400c0c0c13030f05840d08407288881640040c0c41c040b69039100c800c0315481c01c1210f45c0702d1a80030070301a209100c040300c038031480c0d0794039001d1500711 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 380559433 1250 380558183 380558249
    0x61406060f09040504170f1201050402130308030601021606020c130501050d080f04030b04060b2d1201090b01030f0b010614120604020706062c13020907050706020a0801 74
    0x20714007001554007a103825071101c3d40181c00758603d01c040808008808000780c0c084c18040b0014403010401d0301001310b205640c2405054161425070400794105c941d140001e00c01c0c02300509000b4040005051a4130800c4503a2806404201c40c800f420740e60407000e5251045100501d0041c500300c121001c803002c450145504890001d86250b400720225180c080c5984c002488507205210104400004581c1c80410300b40194003642c400102c4000c28030403c49802030b158900030a07020740d485102e0441c2d0300c41284075075004050f9003880c09040c2c1c1c03950071801011011070047c50704040ea40040248080d01c200e200b1003a100381a40301c00791b6200c0c0c04c207580924200a01d2110f0f000104104540b2100441c0d2039608050064005820b004483c0e8131081518160340100d0008600c1c54800140030300341c0340c0000b12521414004500b030381084440384440c0c640a08029000d032001c4000b0411840c401d2040719400c54002c50110b40f03e0001003801880c040080c85540381d001080204c01580c203100c3c40c1c83e5078103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 380560683 1250 380559433 380559457
    0x9100503071205061c170c0706110c13020c070302060d0f0509070e01090c0e0d050c040b01031503080a0504080d03090201020c09190e160605040519031a09160306140606 74
    0x8240b08a480e1580001c501201218104601c0207180e6006c0946030241c6908200100035015550a01e41e000b040540090052913150703122680f200d070a62900045070034809100c010150384c40b00c2d500c0940d4508141584000e411400c001404040c040381d030350152a1000c04200144060b48480314000c0e655030881c0034040c54103180f8001004040711aa100d00c48400003814126004074100700000e0f1001c0701c1d210199219000b000f4000c680b8038141c4165040c0403400d0804002e61001d030841d02190038800d00000301a40c00018a01c0c40740d6009000350b800400d03000086864412160800070301800031040200c0c0076100f10b10700d81041d4580081841e1080c01295000c00e000d0350701d00c01100250a81180200c15401544001e282ca0541c0e10a4440502801c0d100c00e6651803416007030102880c90144c0ca40d104800e00f02003800041c00069003080c8004290200d142182c640003511030419420030700e01c0702c0c2c140168100004120307050300070305840c1001e0700b949500c5680320070511180707104400c10b400c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 380561933 1250 380560683 380560699
    0x4061a03070c060902040912031b020c011107030602040605071509030531090608100b010e1003110403140606030a02060a14040503070b040e01120201050418020910050307120506 78
    0x7a1644601d5420080354003400e00426100c4854001c101201c02104041d2081c600186501e14441d030507006074100060815007800c1e42b00a0140000c1d03c0b00c1c07140381407a040024981003422248020450303840950380000e0119034960703684202411603848080111811740b149010f262644c0714601c82c071a0041c0c0c05813a0703a0710300484d080841410750b00c815100701282d101211800e0f43c0040c1d0b808611b000c0c1c05207240020b401810480c0f41481e103518500c000324200d0030103410b0102664488050b2481c0002030f10b4010b10703c03c400400384c001e0030401c456104a80408500003003484031b54103410b1821018201904c0b0301d43c44103420b0641354900d0703a10203904101c00300081c0c407420703105107401d525912007400940e04181c0c4540000c5c3c20b20616512807032803014089000c2c011000c00e03094803401408050718580d410520355001038100d004610031016022035803011040d02103882d03011a07181800041608410302200c2c3c4000e0300300e800a5030302000203003c50700e9080c0b40c80c00714410035005220060401e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 380563183 1250 380561933 380561941
    0x40f0608061504080a0b09030c0d110709090f0b2208071a0f270a050303010306240b0f041205011a06090919020c030c070816030b060910120804030204061a03 69
    0x207100307600d0240c0054448c0c8010030011030300392800c0c4042080c10f0400e5a03503503a21004242d0503407420308160080e08003945400c18030000212540805002c80c2d502105ca00d03003680d1000304c0c103240e50340003500b030701c140c0c4600426007001c000002004141080c802e0100c1904035080381219404a00200c0d0a640c8205c180c2c00406c040300c0b103103810b01c1c01103507c42103900044110300045034189041d02c0c8084a5942c40071005004111903401000202d9042d45890305014070038816102d062a464443d20304858070004107990225401011680901202804403400070003624080e80242959094006070107803a942d40d540030f18101c0201e84444400600f04501511481005100b55842846050200e6030030482119184400c1c00038000302200400500f2801c0c1c645000c440c00c0036107114203a0045461200203000041d40c81c3c040a8020200740c408419680d075000d6050f0340d03100d4541010366041c1d03120410004100c0504010030a583c400d03501444020754a80f948121a040e6036a03550001c4818070002d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 380564433 1250 380563183 380563193
    0x10605091c06020409060e090f011b030b21030310080c101404030605101d0621150109060501020f240a140103080403140c010f050f040f0608061504080a 67
    0x8400701e600520700146801c0e0340d64030010445400b41c1c00000528902c004205114800b0f1121070050140c042c000c3c4900c1c00c2202c0ca241d04118115441d0342815a0750346040056200d402544484080d90787e094a9241c005201701030781c0340c20442d40c05001d010b043e07401260090001c6000302c1041c0010340a8180c85440510955203000c581030042010070702803000002060842c09900c0c09003503c601d034500181d0900014241a40b0100030510400150307034188442d81d00d41c00440142c110465180c8a03130310301540c007081c0c1030080e24801c8060003010b00c400412860344036401041186c80903001c45641821f04d00034581c40e810071007101c214000190070422043c450500c0c4d4580e0155880c0000036050301d6406d543e00c0d540b2400c1c0c0066803444e0740070805101b0403405505006560300d010000700b41421681c40001c200e00200305808041181c08101540c01940c0a001d440250101c042c02e41d0042c0e4461000402caa0002c456a91085e000034034031030600c104550840c0c09913002c0300090006c424054603a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 380565683 1250 380564433 380564479
    0x11010914040f020c0604030507021509090406020708070501241202090708060d051b010e04020705072102041d070512100903111609050108032104020d02090c030f01060509 75
    0x8003402ca40c00700f080c41d04490050091601c980d00c603880e060344031070441c010700090003a0362007805103d28040114500a5480404040d801948600050f03540c040380c0c03404c0c03c00d500550b00002d001d0341c201110f4020011240340214101024640f02c2c10801d030359907100d0070590780e05040107034204a480780031580c4944a040c40550000e0041d05012148d0415a42c1070711305580f11855680c94038649042c5000c940e4840c40241c29480e04031425401c08000e40c541030b440d03054511580d0050314080704103c0c035a0400ca41100c12031500240b04014840003078454015000b0b50b0b0164130224003600d400842c0341d1030280c40b842d000301002c0c0010641c1d04040c070440310003060100c40640c1800302031191010400d9081180c0d107100c05043c403050800a28100c400e400343c60041c0c111036140e42080c024603821340c0c0340c05090321481800c0c00d045801c54907240003042c2005036139080a900a203d0404004410300d03a0401180240d11404410302e0356070380e41604407000d0042e601940d0f0311460302c00300e600e602c0d40c01c2d43c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 380566933 1250 380565683 380565701
    0x6070e0d020f150307020d0f050a1b05010f060e010311040207030f1b02060c0c0103050610020c010513150504080c10090e060310020a031d01020a09030b09011103131101091404 77
    0x2200100420410f5416815904122400c9005034443c0450102a50348500f002d03190890030704000d400c0c007800d101c01508042c0256507000540000708905e00c00d100e425080700c100b88041c403100708521901e07141d44a849040074042a41c5064041c080108130307003007234401ca421041d016516034141100408045910219190207081680240311440c009691040c0042207040824001050702d40305620024007910030041c54988110703c42424405103a40210342414201403d00e0324940c1c501e070607088447c0200311600100818100000580007413034000c0f000300182e800000844110190310401c1000310801e0b803e0590024180722002c00c012100c1040c215000300c0d008043e2043c050188245d50f0032030f04a0b8170000002611222a248417414820107102190213240081d89051079040300684140414400104000f440b140014440c403800e50241545070505614156070341000740e08502c10161420065810341c1e01d40000c5c420942c029081c80b8100c66800100072100660b000c204402014410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 380568183 1250 380566933 380566939
    0x105060403170f0403053a090b090301090c06030507021614041d0105091b030a112206030c06120513120306032109081b0607020402070204050a0e06070e0d020f 70
    0x7200205c0000d00a02c002d07400105001007019501c180465400754040b946039482c0c1881b140700c400c02070425801240e090595465200c402e6640c0b5025020900500c49000b024062485402d00429003940c140c000381e0141c000b5900b191000100d95055400c404400d10980e00c0000c0705c0340891219013882e03049006543ca0740102081c0300d070041c203011801e40302c1c11180810560002e00c940166000002619500341500f03800400942e1803541d106251201240c122601c20440200f20000e2460841c521800701c1000d84002d001003903481c0b41c81820540180500d07008111000b1400303545180f180300f0a44285240c1030460620a05621b64801203a1350450402c10503885007400320200312000201c0c5400c400000f0500314420758518010b02040c00303038110300e0003508102c103922560360108401d51100380c012605656140541d100040082c814508001d404c541042c0411450301c80c0c0b0750042c109000103905035240c40e07841034411240007190302035203a482400c0c030300c0b9100942000652079a21603800303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 380569433 1250 380568183 380568187
    0x103141b0f15120613180609050703080a03050a050618150a1a04210f290a0902040f150e0c04030503190f0804110d0302120f07030201050105060403170f 67
    0xa00c4a00c04242d020211081c0c2d001152014042c540c14807004060340e01309502001c100f0840c0c010302d0403020b5504006c024201c2034035110804107120046c02182c0080d9440815180d6404d05410050081d01d400c94580080c0d9140400040f054100b00d81030440c0f070583e4100d0428265500318100c10301841c040816600005802c0010440404d403c0d408000e440b030045807641c0300d51505e20384180001c4000304003e003012078141c0950000b138840e074823480c02513803010041d00b03c7e8403940140002c8201c024010741c00030440d0424410006400e03400402140c0c000e540a00c00d000c00c43e581802034802c001c0e020b4045903648001000820340400030190404250303000703141780607500d407180752450300b040301078011300d150001d500c00940d03800c02c08081108401e03050a0700701e4607181c3c0b6442c41c0b4490340c00c81540070b0002690810205403081c04815940c032041c0d10044e072205c1c4101c0114a05822090086000d0740c42d00d070000c40e543c9031010035a0122544090103100340d825070007170a0010b42081030156021201 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 380570683 1250 380569433 380569459
    0x30c1602061606050606070f03050c15010603091e0b06040b03100609020a110d082707060e040c050c030315030a05240601050903060612150405060103141b0f 69
    0x740001003445003850700310341125094900b0210120741d4064a540d21a403010045000040c1400c2d0191281c903400d8200300e5140d040d020707441414400d62240090798032400e100003103209a0194044205e10740600700b0386102c692007074040030028032900800f410240d0070701c0005040d403800d50071480c00724078003400350381e4400300c00760210055401c55007040210680201d40c010703030140c3c480301135881d40400e500103150300103903140040c0071950060081300b85480904500d10043d5840314200c1d07011400d8508582c211a5034540092101500c1d003110307489603040101c100c0c505c07031140d025a04604405070240d490740c0c48400940c1603240d8464500e0750076028010084010440034003449881c1ca038074481d6115804443c0343e140c00340b80c0c002010300b414080306025410b15500c00184080d40400706584044043d40c00302c4089280c24001c1652001c2401894208020094040303202070407a8482d9880b204080f20300c41d24a915101f00303840311640320202c070154041600d00308001c10a01c0c08090302c2ea001d0040d07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 380571933 1250 380570683 380570689
    0xc0e0402070812130308130204020405131406100206060d060e07080a0611040806040311030427050612120a0512070f020d0206010501050f2515050603060705030c1602 73
    0x10510040e194254003242d48140300b0b100e503654031341c40070350102c0b03100880060f540c004d0405800a084204070a2100703100030115191941101c019000041402c05461000b40c0341002070080e1032609154640709d07101064040c20035140d801d0400c10250094540c43d961340c03003800550b034184002581c5e41f5442d500301c5401c00c2c03020300141000d0080400944891582428008190f8110300002204050104001c00401d1000b290b9682c0190341460040c6e044250380c0126851401503403c010070717203040322500d0301407404860322000c0410403e200130f1005a55101c1004162840c02c04d6075485604400c2040c3e507540d6200e0018031101501c1d05005062030f4403001c0d4940b251408940c00c0c0d02040390344261014141c1c0400c105200140d003032005000e150706040c0003c2a0303014101c107225444402203040d50120031240c00890a14059848061590a16081035122421a601480d080c07900d4100461070505010a0041c030500c060303100d941c07030360311203030031360f0034168404001c400c4d10482d0113003958010b80d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 380573183 1250 380571933 380571937
    0x4050613060e10060519050307140a020c01080603010b0a060c21080603011b0f0e041b08160c0503090108090f0708030c07050423060118181406010e040c0e0402 70
    0x1120b958074100041c90400d042002c401d201c0e80002080c44418002525000302c0d07a2620240891203140103504c94882d01010b48404020880703608640e1008519a01925400260b0300b0b117025017680d50600948902c0280750032180000e0b15507401443c4888144003ca00030100c0040440c07040e00c601180071446001c0802c80344500b0307254000100b205c0144143c0e8903090052100b001300c0307501c10403211910703118050884140e0b40040f900b030042010700d940702d075a02c0c0d6114a40c0c0c01d012003c0c07038055000b042401000460300701c0e03e0840f039020309481e198809100c0c002e00c0045503800303c001c51404a00100644201c50010440801446a00c00000c00220b0511005004002000003181c0700d203100d84810f401c02001d5000309008078070344202c0701e0010041000c0a1041850224580c9454551000403606800c10708441c801000c000400000c1103000124015000d00c2d54020030401084903480c81ea00303444003566418001307a046a2905080d00d02a40003169480080c20030310b84104106c00443c0583e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 380574433 1250 380573183 380573189
    0x100e06070b15010f02010507090312120203010b03100e04080702010c060e010c0810060f02070320030a080403061802180c0c0d020312070c0c270f021e090a050405061306 74
    0x2952501d044140c0d41c12454404681c4d4040c0020300003031400c9036009244030748620016199941c0c018181d5401c501030075502c2c0300108503200556032584c5600014040e540f05860901604c4d00740c8200007401e0a10070354560095603c006664030f083c099400441d500c0c41d0500054942d140d407150f00c4607204d00244958030628005882e0150986801c00c0d0303030390041780503a000c5800d1108184103807a18541c04103503c81500d502c203404070350165500c40364000d10b4030440300454040c030800301403109001100000e842240d10602d400d0200e80d040743d144c00d40a01c14224002d4002d08101b250b21a400302008c8410f601000d41118a410280841403591500104607003403409a0000900100300ba8a03c8000304d9115242d41040291100a41c0e62070000c40c0c030b07074810000186144180d01c080e60000c2920301d0284030340c0c100140000070b03a40d0301450081d40000c400d4254850550701c035030b03007004480301036407040c0100802e001c003054900001d1002a203002000b4651101802502c0e02e00e1943c5840740c0c0010b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 380575539 1106 380574433 380574451
    0x5060406200a0506041b0605191404090204030b0603010501080a08070f080f0a12050105061608040b0c0610080307110f0d0c0305010e010b0f100e06070b 67
    0xd2251070391030501042c0101d1009009200001440e58051405800e45088440405d10701d4006030704c15214200c04900c3c1403241e00421803120310441c0b40305006040003849214250b0381c00c1c685a00c980c01034180c041d404103042c000c4c410000c020590110058000b04600d50401480d50740c0c410441c0340050200000040c0c600400c030040074090344099004c5445603c800c155504510590010401c0d0b40c0010010406880c901c40306000d040e04032003000d041585084864400304813401c400c9007040c0c9841908100c00100d10200074028000381e407102c0090055030519403110b4000b2111a440404264818005907012983d10b0300040f04001c81104d0140304400081d000c503a131000244009070507482c20840000502c48190400a030740d0001d0002005409042020008106841641550802c1c0c170001041a064041e039001300031400b00030081410800c2c42c2c0c0d180d0040d40811180031503 = true := by decide +kernel

theorem cover : BRFrame.Cov 380395683 380575539 := by
  have h0 := BRFrame.cov_init 380395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 380395683 ≤ n) (h2 : n < 380575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
