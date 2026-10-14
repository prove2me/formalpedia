-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3314
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:18:04.708176+00:00
-- url     : https://prove2.me/submissions/1aad4ffb-fdc9-4b44-945e-34e4da361513

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 595863309 ≤ n < 596043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 595864559 1250 595863309 595863329
    0x6060d020d1d0706020714060307020c0a060509030c01090311062b02090103050106020c101b080d09230312040f0b070215130b06092809110f011b0309 66
    0x120b01040850380681c6250800ca21500900c4000328855201042d40701c02c860302c0b003800020300c01ea8401000000e61001c3c109405610444410000b9510b4181c680401400283c841b0303a1102140320600d828580050000360400000c003405100288041070303000d4084009903581e0b0380340c40c0c3c111b5030301d0114507450f8040518a00d400804040110f00c0782c006040741d034001c0c0d070280000d981c1d9001c143c1e680c0c40a1010705520001d44529415220700c0340c43c0f20034100050010300036400c2003945803d00140d011114401c4078503181c040c40c40c00d1004683c030286417000001480346460518001041d10b9000c0c060304040010212004241800300780008581d069400000c4c4041174101984040c1d95002e00ba500e41d8070344400788001401000e103046d45401102d40018090381155548030800c0400130005028240c003044600c0a00c081e00041d407503c1c41e18503450200010034018505245400407505400c4910403208240581001d90740001c0d40d01c100b0f0280da40904c86049949001d940c950b240380c0000ba114 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 595865809 1250 595864559 595864571
    0x706020c0a150b1009050915032d010c02030f0417070918020f03060c090409081201081b0d1a0a0b060c010212090d0816020703060515010e030705010806060d020d 71
    0x8041c4940c044480c0c3d200881302149500c00c251000d50785112188103480d848840940080c420021010746500b0100009050302d10816420440c110741c05038220f441381c03c0201480c211841341c2424865511010080d0008501f402807003030131000d080c4503900800b07480c0c009001050001c900b0401c40c20307000d4107040a007071240d5080d081c4030080040c0384001c1648141400c0324503005904020030224003a549201c207043c5000124824400030745035250086406510400c519900140d0076490700b40600445e9025050701881c45c1c4401c0241c9950106140c49054001e000c140040d403404071042002d229151640740554680030454014041c1020035504588005050100004194001c1c4901e009100c6000929101c2003442035540201300e0392100400ca00c3c81c08181784040300d9030201206032107441155880ca4807681c07070205590095a20354544c041c21101f40c13545c2c0d07800500d8026411825401019200d2500000802e41c5001506030f80c09070400190f480b00954041d012175401015108040c810 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 595867059 1250 595865809 595865843
    0x201120f020714250b0a0e031606020f0f0d0e01050d110c07140d26130302210c1309021c1707080a080a0219080603010f0e030706020c0a 60
    0x751507140d10140380b4091130380300790303406448080c0030780e180d006691009420b5424008003118940c08498900d05002100501043d07641c0e0820859001c5400f2a0b01c200c84c181ca00302e00a0300c3c0042d000705024542c7c0144d03402c0c1c4050300300069008120300143c03402c401ca1140090050ba218814000c0c5803842c01d080504101d010400c190003045414150307402c07a040c00d0340c0c0764541003503101492000c607803100c3c0020451012032a01110030fa0113198411092810031100d000001d03056010f14003603000c0041c110fa00b081546880c203035040e070008030140602c0452007100900d64035031042d916801d01c6000364043c041001202a84000c0c200e5070302400380d00c9842185000503070300015502d002c48000c0300f100c4519180a24030000e039101a507010009904240003198141c0d05848000d1407007845c150300380186850040803464802020155031502180c034202003082c5030035144111a01c4521314100781511502110000403640c1071034105200680b90030b41d5202071801c01c141c0c850084c08904203110003c403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 595868309 1250 595867059 595867073
    0x321060a05130c09051903150204120c150c0510051503010c081024050d09170d050603031306050c07080105070816020703030f0c05010906180506010f0806040201120f0207 75
    0x8441001da04c40c041103e0b0380350100071000e10380301c4408510403281802040020001c503289080c0b08034003a0098286030321000c80780b02420741001c1c10740c0c1c03c4101030320400038224040e4142d0341c016004e251424004550f6100e180d52800e440159140311961003001482e80605184000321074880103000307101c850180c041c024540c1206450303c2d80c1e4025a03220018000c02c442d0340c1490210504c004c0140300001e40741c01915950095a1219541c50b21600d00000051040d0018040812080c5e1042d4541e05542c0309401142c40041c0850f01030750080101ca601c4034600c1e0010b01c1260741d14584103550f512a02c0e8950300b02101540007900d19801e2005100b86650003400440c8201850042c410300240c032080300302c3c1e8402c510f05c8083c000c24556207140080d50b10a55500174800d004100120f24401a542c8042c1100d881039036505801d81c40003a000c04011003405030600604100d0300010000d82004c100e10344a200c0030744000c2c180b104108071054065586d800c9050314051641045460300203504140c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 595869559 1250 595868309 595868321
    0x10e0415180506010b0309150903040305010606030c0206100f120809040f0b2805040b190603020405121b09090a0f21030c021b03010603150209120321060a0513 70
    0x1100d5000c3c0e2000840c1d111150403d03a8802e2840c900102054520384050542ca4800a85150101d020400c00400820000d00900e0028000c030b590000c0c1c950003241000b4107003040580000d0440020304010050001d04500311010748144440704a11100185003040c0b0741d10640141d550498105864100d0b099140d83c00742086c400140d0710309604140c0c840e25460b2001403c1c56004020143d41001e0025040c660700a03800e5000c041c0c04450714155105052680c3c105540c085800240c00290034001401c0c02d140004c85c001e0304038014200031810240240e020207400c0902401400268000741c1103000800030402100d4002c0c0402041d56800e0801c4001041601ca07108080c0029048c0010201d1081c4200415011250b010300340d4209030459044800390740c03614107079041d0b40702c86001c0f022904c01d84042000013886c040c010703910048031083c440030b425000780c61400754105100340e5147e060700c82c000c02c0a807003040c0e01d40e111603568503001030044401c81d00804c2c1c21111250b5800c1074909103074419 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 595870809 1250 595869559 595869563
    0x80a060518150306040b0f0402010c02191401050a051603050f0a021b120c1224010f050402040305030417240a0605030706020a0204050c0904090312050a050f010e041518 74
    0x9a201d200b100c181661346009440c014134014aa0300050700c108220301c1d05540043c0305142079030f200581e5400003404800d05d02c544d03800040d40c01004200c11190201c20140010702820b049041c260400c074060722a0007501112044081201c0c28101010312880490300300102402e01070783c403681100300c02592440b00301d040383c541c60800d0b0489405031070500300703600c0604d00c0b06008015502e6503030f080c01784001444a0400c241c1c03040c0c803806854480000c07d202512924181446455898000c40349481240c03980034502903071040006102080011084400761144102d80501003200c07003148520f01242d091960340c4c3e9005910780032545181c1800c00c0390203151044418809030361104105511240a8442d4101503481213007210300500705500107a5000034290700c514149052940802d083d40c80e0315008400250030320142d102000c00b2445016080346801608100901e0442000208450180503400c415485400003d080002040440c5150850328a090003000c00c146c404100803050b0003c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 595872059 1250 595870809 595870831
    0x20301110c060a0204120f02030a020405070315050d080f030403170112030e090c0406030c0c02040c0503190e0d03110702151b01090b040305130b03010f1805040201090501080a060518 80
    0x4101840154000d40e02030346c240c003100500c1102203648100341c0c50142c4004076090b000c0e4031001005a520b5208251103404161408a041001d0381164400551150040751240000b0351002c0085030141c000c0e16068810b0041141e5039480f50b06041d141c2d02803801c10807050360200400840c0c41c01c0b003004003000692190b241c428040d240c5004214203d0302c200c401c030646003410b0004100e010b01c07981118000306030900f89a88550a01d40201e41624004150070020510000c1440f54240d5507003401c820700007800b981041052040701c0c800d5103c030038200703a0300101a04d0340fa0510210380100119144c2e0350f401010b84502d840005028511500040c4403001c1f40031380414034044048060064882103644000000303225507587e03030203032416080b014034400312391141c140200e102b12211004601800b000101102c0c1c1d285800482d41203100b0b8910500e210f1802d107424480180d8000f4601e806603074013403c040d0301da0b070b580300d10040090000c5c0e805260b0200e1240070b211983c424000c507443c015148025 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 595873309 1250 595872059 595872061
    0x6050901050d11040b0604080a0803011a03150d0804090e010e0f0309010806040f060e01080c091305032a0d111507140c0a060903020f0610081216020301110c06 70
    0x40140310100e01e5006080c90404508080040c545540417260040004100d24202519101d100e45011680743c000c85080c64000018054860341502c40004e80102e8202280f031460a98000c032811300c2c0442c0302d90f00400840c6521010090f01400362405001c0310740d41000207612110001b0301914202e0b245050743d00608800e540350580101c100c9940a20684a01200352140380034000200a01134040c841c00d5034881000c200382032181e221500a00340c4400401180103142c081083c13984000d00705520300c1c626100d910001800100688440904a040050b041c020400b0300c1d0071030628000301c0c211103028056280e12140c1d042001001d40c01054000c9680d08c0c0801428020744007000e0712803d02007a840354103114011444401010030a49100680e14261260394408050766180c01c02103001d600700125a10f500704040001c590b014201000040c130702ea01d08800e2540700c4a145008440701400024030686403e094441c0445003076004d4001c01081d0015588046140c02a88010f082401250 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 595874559 1250 595873309 595873319
    0x8030702010507090b0c032b020307180e1b070312230a020408120a020106080703031d0414060402131d07090e060312031e15010e03030c060a0b18070306050901 70
    0x1800c3e500980b8042000750302e400e00410001d0306e0f40300300a400f03034250048560540d1030f659260012b140148401d840d0800461b00700c10940d44002d105030808905140080304000003086d1039000c149841680550840d510110740c00c08481e80400207a84492060070101440a54140c6020700c0c02d801052650401c202d4030799a200320203a00ca0b521540f80154480003102200110a10062070700e20160b000001d00315544d24a043d00301149903000340e010070340907450004190f1081d407249250060803070301041084602d621002c07100750003030103e6000715408101807044009605580c2c0290507811106601341c18070700d0315102d00820440f110347c001113010701c000940c007104084850262100501a0903030412003e80300c50142c000404031011007009d0100c01c007a914180182c1406001e04191111031010b00720005030140108048590083c0d100f08a55990b0f5400424480d03004603c420000c505403000b5070005804c0421280c03203d40884225082c01880c40d0140c4c07011007100d00c15180c0d010143c2c0c1c1c40f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 595875809 1250 595874559 595874579
    0x110d050415060e19020408072c0a230f010b090d050303090d0e010809031c02090418050c0102120f070f051608060f07020d0f030e30090d1401090803070201050709 71
    0x43d07c40c010740c7d1351040340c0038030079180307422004010aa2007040450203402c0c1a180e1440341c02c03059410301521952440c0c111003c1140664650380d118548242d4400340c10302d059481e02d40c0105101c1d80003540341c040f0ba60105547c035240001e03182c0d034000040701c2e140e0400310881516076107104140c90100340a1660218194041d45000d4400c00c0301c0720155041c440ca40c4a10622035548810007445980d08000001003656284211000c45800807030707400a0843c18a413491078070b00e074100c0f00360542d802210000d0400c42e03141c0403104c0305c940d092102c41c0c0300ca219103442d41d10003500b200000c009001d8032032500c8240c0c4031105520b04480c0e000084814986503038107141700030402501d942c1c0058000340c06403000d49004440e04044841c541c500080c508014400c00d5062040300c0c0202e0a08101104002c8982204c5032042040c041c3c1c0719840d50318021000c00000c0c900701d50040700808003611039014000082082d480859103d40180b07200c0d650b40740c0142c0003030081500315250310100e1407620000c110301e050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 595877059 1250 595875809 595875817
    0x61d0d0c080d020706110304030908060613020702040b0402120f0109060e070e0a030b1e0c09060405010c050102040906030b064e0a0305120a110d050415060e1902 71
    0x115880d80e40000340551240c0006602103541d04101e25020041d403030000d6114450725200c1501020407036200d040502d0002e10110b50340d8041c550f0766000c141072040030360354000a01c0184032840401a52040d052001c60040d00b80703456896032082c8085104000c102c00704101510440500707522036001d80e252601e038812502c180c080e9104a04080c000070750540d01542180c0e988840042450740107999903030301c4600c104400c890072040703a002541042c0c040007204082d5600b050004801d5410003081b1008220349026902c510b90402c4419030602040c000f0070b604031009000c40380c07003c2c041c580e22410601103001040e00c0c0c6074054500440c1440062038115801c5064807400c4a004010f0f0b4054070304e001445100c01d100f000c8922200c04d00002c0548200600b80a940c401d481d0151100010b64080e581c11400500c10000345050800543c003000030304003105c61103112a90005410b403070303608000c07001b80202c0100c846400c0c9480c1c0045000c07003817030102a101c2d501094074025094942d021440c16802 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 595878309 1250 595877059 595877083
    0x130b16120203010803130816060c050a050d021609051e0c042c1f0506030a0b0d110301050106081312030e1501140f06070f0f020306130b01050402042904050d061d 71
    0xa01d80500216102e8611261076038001c2f401ca03080e01000e521003c3c10000c5920686016a020481c507008121080c11001d00038102c41804104a203401c00c0c040c203003500a00c0c00c0040c6001c00d000011100d824403003d54018180c00c0314500300d030b80800141c08140034040410403540b28000c200041901c44c9403000e442e8240600a07101040d00c1c41d040030b124141e0400380420103525152003c203801511200c0d41a032849000c0d64010540c10581024582144c5040e04400204440e9204016400c0030002c5802403081d4061000402c03012441304c203d000700200d403903015141c0559080e104030901117100060503079080c0420b406642c44034108120550486c1d0700e540360030030018810000030841e201d541e40035240c0100210540c0d004254002400c1290480e440344c0d1140601000d00b0500180c10b401901400056904500d018108542564110700e05540c0c0d5a94480c180056001d005020064400906c000303002d986d0355100f43e240010180450b00103076401d940e2006142184280000341001c8030324 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 595879559 1250 595878309 595878343
    0x30106090e0603031803010e0d0c1b060c0b100b0309031903021624020f030a0c02010b0a030b07111c031107080306090a02071a0f130b161202030108031308 68
    0x3d00d03921542211507000c5c2c030341d4903415569890000072111042c880c10702001d0081e922502070021303070301d0811207481c51060743d0071035010940b40911045403c002c2200b4042e40010106442e955a450074100c822240c2c0c00c840b5450b140071050049818001001d080c0d5069070028980070140f040fa401c6080f40110b40b4844000f0448580040200e000a800c20b07008040a407410000310080c0c07012001640c0c007a1544540c4420008100301e002070140c841ea440800151000b806051104e500040c403019150101403d402400130126003158060f071101c00c541d4000200340c5102092200f200402c01c1200c803840d00110f4105001c01d01c255410104481c0300c60741c044907250440d04c1d40814048920402030034a031410350f0821114002c03403541d4100021650b040900c0501c5031405840024403200c0180c03a00b45848d481c0069080011240740616034401040c404600001240d25000c40d0204841c0c2c245d800c0e00c1c0d10000022901001c040010507944800192207620aa0341d50310042d9680318030920084c100e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 595880809 1250 595879559 595879567
    0xa0f02010507050a11030d0203100303020d02070e0c0d020c060a0b030f0a080301030602160c0b040f06031a010806190807051008040305040504050c070209090d140702060f0f0717030106090e060303 86
    0x42e0250b017040d460001031104030f0f410040c00080d40e81c1280e00541d0b6440b0035804201c01041019810094003189000d1071020f01030103840c2a80500310f1200141554220303507000304001031001e84503070569090940c040c04565590905a199500030569544407074080e003d00308022045150014020404c56030249034107103507a10315201d14000b5004488c6040c40c03580c0f80c201c51800304618507a0480074100c04407050396140e24002562544007500c1d40040c080c9820b003a141d6802c0000caa100440340c6000b030a200c0321665900000620340c11071b521540303000000354600440c214000061590035031b1010344070a285c01075034010554481d00220780080c0041c208020520103070610742c120a41080e20142914140303507003a4006100c220088400d209580d22800c2d4118007558020402c1011401940c001481e00c070082c0c022918610500140c610f503848005085440c000503082219210303500461143c4120010303a00041b6079900070f00c40c6c000090f80080c3c011270307001c20741040c0c50300034140100290300e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 595882059 1250 595880809 595880827
    0x715050304060e160815060904080702040902130f1a0603040b0a11070f08030a05010515040b0906040906030c030510020a0c1401110406020c01110d0207050123040b0a0f0201050705 79
    0x54030102d122807015018021000e48000310081a1070083e003030700c40c041e04005860000b150b06c3c5480060540388036118400c2403101040d014021104000c0c0c05880109822440d800800c0350700421b014980e40341883e220080000c0c3c1c40c25800100000c01d40f10514600070382e03602c100a2140400c0c1c901074800c441c114081044d01115a21045402c54101c081a0030003480b80c485900c0304075110025103281e0000010400c50004a200309405080200c85600c0c040b00b052941c420203010760700605240303080c000b4020840341c0c2d0b1102030300c1c000c00c02c52006204a5403680b4042050b0344403444110713454894186907100902080c000e80e010000a0307a909544007240341c581d0150504544813103260303956a41000702c0390806081c000c00103094035400500800c81c1c030300001001a00080181034090308040e800601c4580e02060090440c2e00910300140702c280c0f402d598161040c402c0b10000c807102800500064400c01c40c202802403800c060b210102c051160703940980c01d8590407606140019401c01000751 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 595883309 1250 595882059 595882061
    0x20105030c0d14042001021c0e010504210519020310020901030f060e06120106080d11070906091a2e12060b0c0d02070e0703020a0c061409071505030406 67
    0x420b11080c0200d41c80c003083c240c00c41d6900382942e055418011100c010b4912115144660032071000c00c2c8002c4c1800440c01d401c204611500c0400142000441c508249041e031180c801d48001c0d0403051505040d0f0726060f0400d00d008066a401203609000d16540502448036040c820040c0f41c3e0083c010385020203210420100a600c140482414540e49003030342c19507461580314000241c000030b04541034500b09401040341000483e88441000c1c0e0500030144454034002c10703540103407420382c04c00c1025145400601030802c0703403a070006507103035140090014107440e141e04002c44091440395035803903802c414014400c0b00c010051444030380035841d840040640e6902819100b0f80c4010f4500405001100300c5805c007134903080d501c2020850000305010084440c180a403100c0d04400340010020341740740c00c01501c40e64500411201c1419404940802401c3c014800c0d4042194080e03404c00c00c400c056003e000311200f0a07a9048170b14411408041228401503101802c620758948904e41917503141c4c1d503080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 595884559 1250 595883309 595883317
    0xa030203041e0627030903021009050306040804051f020c011d040608010609051003020108070c06090c060c0311010c1205090a0c080a1b030c0b031b0c0f0f0a020105030c 74
    0x80b00781100301c8001c0d0000030701c0c000751082e4522407400482e050003000240e1010101c030048070388844003031140d280000303074010844008803903058505420b0083d48504c01da0b0055000d0b40300c180c16009004c00c000c10800c0c16001402a184c040f5003915160020b0181c10b64204458146180941d0098114040360b6004602480c02c2500c1c4800880000b900c10780410213444265000c0d44041e91a8181404030040768010035600003180d014500303140349103800082c10210080c0141040c020181000814800d40d6042a0030240e0025440361000f50340300001085c642001d8020b40c00120130701130b00d08036000107000b10004c404055075400505180021824004c05001c1d207103d0b064400c1c80640e20000e100449403100070300086018210061302410442d40c1d02e84035013801603900e04050002c3c800203e02900140541b41c2d14083c150316071f42c0e10581c0c2ca481450f0749140118584002c00c0c0042103200c00100e50311690f820805985e540c0c298200e0555403a403401c403000380460000d0001403480708542d0b0145c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 595885809 1250 595884559 595884563
    0x30601050421290a0515090702010e0303040b0403111f1d0610030b01120206030711010b0904080a030609051b0f040b0307120e15040803060d050f0715020d050a03020304 74
    0x10500303404540e4911010200340c60003440100c2032210b03d12220700d003d9803c07660128448206010524103401c03001a110000654284104001c5010a40c407910075400031200502c44011243e890500f0304129031802000c4a08400281d070701b12030900d110201003007020480c11440640512803455001400240465001c10740540d4200400c01c40c108004122043c0075009500040103003505605005600c0c3d141604846c032820a0000c240f070044c3c50300c0301200d601050307501d4500360071855007071442d015207030315410641d02180d840c050009002c100c20007042584010348007000703440d80e00c1811001755482102c0c1e0805004001005000d0701511400611000c0b402d0340005103030948501d080c1d04550019100c0e0000190713210844410b1003114400d40c1c0c13102002e1002032403007981035441260107120091000f055801c001c00822019156120410341d03031a0301006031042c0220b81204590345403250710994210034541e400c8080498008030300510b05c000e540c0d42e540d20b481c0c244001074000e98805002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 595887059 1250 595885809 595885859
    0x70e0903130b030a0e0f0c090a1b02070501180303080619080d05190c050c040b040f0903021c030510030311190f0c0e060607060510080109150c02030306010504 70
    0x1100c40c0e0300c1940e101001d0814082583d0302c9050100300401216550030000b04590b001e51401b0712811000120f0400a4608a803114110703529010f4481c054160205180c003001d080c07000b040305c0b064000c58400c0540300d0a80e1135111282c2085403100048042e4800035001c0303551903005c1816030820448000f0440c2940c0348501181360b40309842441d202c80080d0100c002100802c20700e110780041d2003482400c3c4403600d402e083c031400c42e4640d04d440302102c4140903c29543c52800243e03940b900d0300500c10f020411701040103002c0302418065210505000c0240344514513510000d6054064420940241300b007946540b09681503580940d1211603403c8100701e075200d070204507038880c0d00741107000015601c00c00480c6c40007401454000c110300c04c10b41080a20050b074004000c042d480341001c0d01c0c0e0f80354102c00085000c2d20f40c402e45600b44480c5800c80202035003080c000c2d00c00e0101907548a0039951000504201c000810300701282c03a40419115180003403020001003126901c5120548e6401d24031550b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 595888309 1250 595887059 595887067
    0x3110609060406080403141206130e01050a0204050108060406241211040509151c08121005030f0c10050304031e0909140112060c052b0b040905070e0903 67
    0x100240042c2c02c42d0f8008400122104100401c15a000c0c44000506508035083c6040c18101c0c40d220900d2540108454015010385014030700f25030b03003078104140e07a805540007003259003804010b41020390301600499010400050101d0081c0c02e05200d44c004442006299514078032010940e6108010032028103002c0040d030000c0f81e03c1c820018802c0440c4002c601030a107540da0324150510210720001042c5200c0351100410015061311a82e0078000f100a800c1580000701e04180341c0201d850207a201c081061072240e108020302c1269420005040d68404c908032f40940c0e000c07092056668611036100c6800001003c0c59560083c0100d0241d0340043c031900f400701e204244c480000c860380311030601c00c0c1c001610602c41000303620800d00c983c074400380100840700500e6042c800e2100904a00d46001003056949500b400c0b5210702c01c405071080c064005e41075240350b000825000084ea0f40c259441e80d50145072401c00b22040c0382a1198a0b842035229014001e030520340b1000501c0d228005040e000c850000300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 595889559 1250 595888309 595888327
    0xc151303050d0905040e0d140c0307061113051c06110f0309060a0b010e01081306140106210605091303360f0506030c0c0705040603150b010305010b04031106 69
    0x48070002d250310350b540e2540282c1d442c103420007094410b04916400c45400000008804c954410283e820441500c0c0441da9900c541e09220340c5144950800600326504e0204110303441e01203c00184100050f00c204442c0240e214400c0050101a4081e00c80608000c00080000510107800807030742d24480d04c0c03002e41001811101e407441503000311a2411560484020007403400480d10542ca0912400c2c0380c15040700d0b10f0348001910f415805855400d026035141141400c220380340d08181c03503070800b06c0945915542c2d2050080c0c040c2100c02036008482c0d00e1248035184074940c910603d41182c0c0001d052200340c0e150381c2d1106031915501c40c0d0950030402e84000030b6840c0340120400c9035403103000b6040da00e60a541480d00c0303821805c0d141c001e1002202403603001c003c20b980d0601520381026484000a6079600e40301c007500e2a20f1083d60156400500b01600082403150a484a03c092070140327605020301c0400200442c203c5e017007400303070701d108140c188003d0000c1203c52580c64200440a41214649030f200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 595890809 1250 595889559 595889563
    0x15090a020d060c11030418020c0703060915050108160302060a090e0c09030c09130b0703140c0c06070c05030d0f0f090c0617040209010e130f0b180c15130305 69
    0x1c0c1c60a07030705951200444090715a22802a0550b03160001c0a10b082c9400c00d0141e110005202040c0c3e9985078000c5400c42c40d0403024000070b001903600940402c2040780901d4807407050301c03581110715989803038040000b41a85c00030038508000389460309480052809c541c03c1282c6a0440e601440030421788100100d03600422920080c01001850240741d221559101003600e05841a4030740ea00552028041c0034020060000c120030082d800780071140c5540d20140114024044090704040500307131001804800b0305584004e205000c4139005442459a0f0181e041d588821810303001041a8070030006043e0020f030075401141c0c00204800c002c608014010f4501c42660080001910742c0400710200f0405690070040c2000750321200180c0340241e10309500028001141489070521140110002452000c11010600d08465100e0080d00d8440f1850500e031240100444142c9040001420840c0c03181074001840c02d003940b0010030f00d00082500d62902c8a00b500841020b019100340810080001041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 595892059 1250 595890809 595890829
    0x509150c0d050c0414120312250305040b07031406010518130b0a0819021017090109030806030a0b0a11131502070b03010e150f0618090c040815090a02 66
    0x243c006040d211307414070b400000413074441e0360380a200701d40b11481510103a00c04400d603000c8035008901801140e03100944480b00070b6091400903452a0001c401400c40c40e0940c1c0010301907030140e0f15060190341c41c01029412104000d09844d595803002000541641c414002411a880c1c030040f50342180b142e59020070400d0b400100032440c0c4135101c104150640c140704650400030030721316004010205521541026400034040082d00500d0005600c60525014001860540c14400c410648920303010012600078588042e049000610b01000304034903240002d101111142c006120444684518860400415880ca440032400505100d080e00740281c0103175503001406000ca14612410034060000d0601078960401801c050040c401444004030b4241c0300780d40070481250702c1c0640b0201c240043c43c000000803030554800700000d11400e219050030914904143c05543c40c06d4151503418041109000381d00903c15164001200594100c0171a041e29401400c24003d903124240d1075008a400059 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 595893309 1250 595892059 595892071
    0x220b04230c27011404061d1008010e10021803060403050703080109110a050a03090b0109090308010b070206090d0318090e060601020a11040902060c030309060108060a0509150c0d05 79
    0x200584800700c80c2000d00070b002e24064007456211410000c19000c180b160320602404075400d030003a5030369085840780d502038005003903180b004044540009103a1480000200d0b10351114900401001441d58014020010390341c11401c054180700380302030b070b6000c000d4200b03c5d00300034050f04902c122189130320113105113030040b800303682d41e039a40309054107001d0044501070b441101b1035803a040c1c058440d0089801610003440c039034a0a89c1e030365500804214007500441c6c4003e8002036501000141c03102d1203a2020010300e00c03035142c114850b03a99520150702d038096244065002070003044000305030300e44107200020a510a06100d0b40c04400308010748058601030300070182059407294603801980b810001240e11040902c0109290030342d82c4c2d51b2000e08050304040c1400b640c1c0f1500101c085603268801c1c1c40300ea0405600f1281caa1600c0c0c02016070f030710702c01c1c40b0701402405000c0100d0020708140c05003501c1450381100410341503080c0e00480c1100c0720000c041840c07001d42403100600810043c014203002d14 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 595894559 1250 595893309 595893313
    0x90d05030d060b1207110c01050f1314032404080304020a0315020a0e0f01021002090102240f01052d010c0f030e031204080715031404060c0305220b0423 67
    0x8402c0d9144c04902180181a030313010b00040301c02d08001003400140724168404d0a29025031514440320b0541c0700ba010304a10488c044003014408180c01d85031004031761180d0411011200c61070380301250b42d03d04070a20511102e001c071603400003401240703008005542003880030380860f8a4aa0303035260100f0002490014905660b0002403400c0840e9221b0b08000c2c41510445180703114100c0500047d649001d540b149c050794540201d01c500d4168005e204c0c410104115201c0000501e08100300e42c200c0c084102c501241c0401e46c00000301381402d150400441640482c141845031540754200c900c80002d030810041d04101d4180d51100005500542c01c0551500c20f8551042d0b10b00248101801c002c04038100c0401c10805200800000800203400d03001c83e071004502103a55070304440101d003e41299038403883c600400c101840200704c0b00790300401c043e9119513070420076911040300c030b41600701e100b08a0190389200004101e002c60705440582e070304544149218281482d440b403088806e9200f0000d051625 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 595895809 1250 595894559 595894567
    0x711060a0e0f12040e0a060b0901082203020a150b030d05030c21060901052218060c050c070605040312200106170c030601060c15090b010906061b08090d05030d060b 72
    0x42402c0381710968110542000501080c1d0401201341c0030b501800c020181004000c03030220b0b0850314040c0d5800006043d43c00c00c401408540d0901039035604144201711026200403111503844030007441140550704004000d4000009041011250354002800442c01d8010030400d0750f927002c51070480403085485410707109899140103c1041085d200c140c2c40140204051041d0001030600110b174040c3c03040f5020400a200c42c0d504081e40380d080a154030003003405182c00d810128494002020307100422890040702c03242511401c04807000d000b10301c0010180c80c0800b018460090041491410440b448900b13820a000800c502c5825150365502ca15021103503007148504680c814001294001802d8004003103651500800800d041c00044000d4085500301c0800002600c064205034078045d0405441c1200e56100c13641c1e0b0004148600c00c91000c2008888807103000810108540f820340d80008110f42000584801d00c0946e042c0030000301c07124001001360300d8494a052190034040c2c1140d40c483c54503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 595897059 1250 595895809 595895819
    0xd020d1409060403210623150c0601090f09050703060608121804020c0f06041a070c2d06060e0106170108060613091e06050711060a0e0f1204 62
    0x4000030181c92211640c01481c10000071982028465501e00c1c1480c0642225010603038114005149039003018004211020350001c00c011060381d6070811001c11284200340b06403801d0100094480c01c6a0000740d6002070004001222482c0c3c0450029600f080002c0354100559440030309000f00383d041200c840b9611001401965010002c0d114442c007078a003190700d42907003164940b00c6408540180b40c826030300000c40040c454000d120841c941c04840c0300700c89050406140507840c0300091820b02480015013400594107510440303c000074281c010b42518245205005042d4404132400c0d220b044100341c0390044000074107188030b0b80c00280800740d155000703075040180c01840c0a9031079080e105c50040c0d02c40144000c5101003036058010b03d0889035020591030b81c00c012405440d00f09005018244400c00040c04071810780c0b041103810f40309800400140d40c2e40031068510311000300c891310b42640440005000160f841c0c0c45001d00c000018215505c450344841d050f480d00b0851110301d44205008181048 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 595898309 1250 595897059 595897091
    0x90f0907090b0a09020a0c0819021c0804060e160303210605011202090406090e010c1202130509190c050403030f030603030503130219080313090608030a0c0501020d020d 74
    0x40c0440c00814810182c03860000f0303020900f240100082564000b0345074519030f014100c9044403030b900101182d00c501c610200d42c050381e201c0d2560030307000d801040c5810204108441c68442c501c3c0140d00d071380103641c4035500c403940244100c080ba810319204105803031390412011290100150321a5440740c01c00c0b8112180c0c1170710325504000218016003000c5013804140c1c3c011640c030000d0030340d4200040e280c0c1c02800000b0043c122550048086074900044e424100006400c094207820329520349180e0042000b001c00d08912030012698441d0702d2100052203149000e0800d03680020401030001100e80c1c034410300c00301300c4080d220604045407002038104105034008007003c0b0020304604003004402c1ca152405030003480010200850f2500d001400360840d500c400c0803007405600741c60060001d9440310791040d969800305500410310318030320400042c1c0c0300060161900f510540d00c01f035810140c4640c3c064903494891101140e50355028801c0c1810700321188040c06500007a01e50205a0741e00000400b8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 595899559 1250 595898309 595898323
    0xd12141b011a030723060f07050c011e0c02011e030b01170106170402060c07081b03030717030c1216030f0203090d0e010203040902030406090c080604050a02040218090f09 75
    0x32002c0c1002d045a1101c1e40c011941400301c44070500346a0300c1d50030301c0e40100001c1d03e0749a1060381c04030010840380e03110f50020000d4940c0a10400030ad034200f0100c50019a03004242006280c10000320075080c01509100ba03009000b114818102803114428610441d000c14051021410000341d5880c1c440403290790241441c0a08141e4806001c06541041c00c0188150342c44c41d00a10842889001701d411511010100c8010240d980283c0f02d030719480308801c0b91600031005002e000f00d08103101c09445407401108a07135070300390301c080340d1044804010317030503095504001c088280100060180044505000c1403840c17183c50301c1520f0b07044006290318041e0032504413240714110301d48144100440b6410002d1041d285101c1030600340c04685e90480101d2861040d81c10101081f0300110902c401c001c0c2c0ea4115510440c0308040d03650029403103180d03450750781c541250081e08079404040d162025040c079500910301e0b880d4145d0003455081c1e40724081031224100341c41c11203480c00c00800708210500e09000300d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 595900809 1250 595899559 595899581
    0xc0f0f020301050f0f06011b0204022101060518100905100c03030510050d022211070203070602010c1704110901061d0406261504080a14090d12141b01 66
    0x403c105d05094503c540d680d40010055814000600c0480040240c2604409130041d40244295500c4141208001100020940300c0c2c181c1c110620010410b240280c003500d1011146104054115000c0f81c02c000f034402000d01c0d00750070b00040450109543e1154070a6201c070500c2a12003060540051a0040481d0001004030241c04010070051110b6603c0302c00b400c44d030a404507030402c5420082000900c8007180d200744407102900e0682940d00414286001c0c004440c000c030151803440e580c650080c1e0036140c40c00d0018000660401c41062032214000855070854054a444c0810081a00102c0d8101200fa0070542c0800d1000b02015481ba028401c200070b40c1c502640e007031043d58900700703500203010070590803007a484c00e0104400546450400c20480740c030340c0c00c221804283c101410b0200c92030f8060b202410004200784c046030052403030301045644000300030300360484402e040d44540c120703814402c0700002080140042c0801100d04607000c0d00b00e00031007030b0014400e4412815040c0c2150108001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 595902059 1250 595900809 595900831
    0x310506010e0f07080717090c0114031b160f1104180309060e030f060f010623030c070f0b0406020417010605061b07080304120309080c030c0f010c0f0f02030105 70
    0x2044a18154a242c05400100d14240388256448000d01521a11201c1020317101d002c2e219010042a0300c0f0000300840c0380701081e291a0084406c40d50300101c03512003100c895000405a40d0184010700802e4014817020681044501c1044460741e110103201c2d8108006450400450301038650b145824401c20580c1440161560041002a41c014008142910a500c28000d8200e15030089403424045075841100f03540560310640740811030b2640400d401c0c012000000c0a540d185024645010425500d80200b055141d00b9a55013441384101c0da0f01000003190310244e420000d000040e120744015000e184103640150326581803100b100c9001900404020160b81070030801c001c1526000d04031050f2101080d04030541c0304a035004140b80400c1caa20507085c0c0d100018000802543c01e9080d0769a031480f9036074018040d9501d180711030356a5030180119a050b04102141d80790fa160801c074041840e0410f0400086244c00d5498402110a00c508185c07810801c920000045140c28496035030300c450342c800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 595903309 1250 595902059 595902061
    0x1808370209060609060904020301090603050f03070c0509040201030207120905100c1a100509190b0f0603070f03062c0106080c070f03020309040f02090f01090b0a0503310506010e 78
    0x659140740078002ca4090200016980456154030044a21960001e0401d543da075070f585845c04000d14284c8400d5401d8068002c160281c4000170086840458118104c20125420302003048991980030740100d040c19820001d001c0041e0f0820205211109640c841e00605032a02c4203101724000020307110300802115205c0c810004203d000b121040d04260f1100301800ea8518207403802c43c00d8103030801944012000200503000020007a403161460a0810a1000501e620180a04941301c4541f8a0380803506100068280d07226012a004081c4107180200b0019901e00c02202045039000ca1500a01c11850b80505940c0c0c0c4030400c0b41c0106814a07022070316113005901d08409005070103000705101d950458500900d8420425075403000780c01403081000080c0c0c100e00c0da00a41c0b0807807040c1c1c083c0e10582e154101a40c0584160000c8544c45180280f03400c0d20081c04079100c0c1d00007401c0f406241d609800c02442c2480b9000305040c3c02c0e046c0f031480c0e0480c0141c0c1c28080d180000c1640500210b8078418 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 595904559 1250 595903309 595903313
    0x30f01060602100b040f0524060901120203130c060221040506091201110d020705010f050103150f0e0d0807110f0c01030f02070f0b15030a080307180837 67
    0x2034110100c074400c540050b813294010700140c06840714501098000e070411042c80820b191520090250041c0401e1001a503460300d0107200361400b8040ca40f90101d440080030002a6010381c0041d503100d2907410300000c0030012591041c140c030001d82c00960040e071115540b4009450500c1011b0300c00d42c180031305541440c0c5040c0c0004c655101d02102e80b030040c0440744a585210384250054a204c2c840c3c80a001e880310a580b00f028000e400040f4291030729130a0180403002c8004034802e03541a280c201d80c10288142d22060540054036052141c48201a9550402c00020341c080c040c042c2980025641c1600500707001310020f00003000c1d044c41564035000f02ca4034262868001901c0c110005081c2808604100004000c00c0280119034014180b00d104a0480781004803001034a44a0300c4c00a250500d580c01002c217065860913179500c020701d90703002000070801103401001610784e22802e202404c0055500c2d103440d80e08180885045909128125001d1210031004581c4192040b9600c1c2d1802c084034003035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 595905809 1250 595904559 595904563
    0xb0301021806071506090228120b06070b040609021906050720100c0201120207031b080415020303040b060f1003200c0303010302150c0703060c022406030f01060602 72
    0x300070303603441000005221002c2041c006210110b4201044081280796511494000a5407042c154020260303804449494000360820030b681c078400d181e0740c0d04611034090b540100001c101100005074400700a10800000070703440740303800b4402c510800700414582103602c140580c0f1760204440b00c0b100c1c1030401080c810661310405445560740c00075582201258007514142441c0d454134036031604810891072400d14190441c00200c0b25034401c2e43c55414140540040e030f4100d0042c000005c0c00174541060f0410080c84000e0254540b501808180746440d035900b120b80101001401202e0140e0000700c104010700600e000800c0d448001591200e030402a01e40c0014210021841410b040c180e80f00f081c4071241c0d80d112014401e01040d15641c80da21055842807582d00d0300300b488200d1040200d03070000d45804c509001903c4ac607240090041c0185030440d40d405000c2c02c80340303805104620540102036250b09101807140000d2a985190459038181901807508000c28401010a43c1e03062917070800c4001d40c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 595907059 1250 595905809 595905847
    0x203030f070905041a0a060504080c01030e0715090905060102030708031f15021005060a031e05010b04050406020901030f0c0503011203020a0218160c020303030a050c0706060303120b030102 83
    0x4500080303000e981d0703448401d80c1d180340150022900a031034600a52040d541085141c1d0107108104d40700c0072840d40e5420200c80b11b104a004240d61900240c00e001c2c03265010b50071032a1240c44000503111302036141d2009802440c0103d10803800500002d10421000a0921940c1d400c04020300c00355203420865225a078980c440688255080f00c610f240b0031181407510700c21b50001d80142034400309082041e1700025030740c6050070030140145240001107107241c1750413210002125800840185101c040b1100344001d0703d0700000a85940d5240c4c803d140c41940c442c4100c621a07403291600617242c0d051740e000102110301040700030010700d03d400c019558403600402940e044529940700303a903903540c942c82d0807400c0002c07064000b90064012155241001c10401040340300d5a000070109454a1090208507104c00da010030280d0140c01c00c0000c640588101d03000194441070fa20305141c03030480c20f0703500c5a04880d00390340309800081080301040c0c040409401495465101107000350b08108654000d4100204 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 595908309 1250 595907059 595907071
    0x3070b0415140a020c0d021b120f06010605070c1d0a0b130207060203011d0c2205120f071a16020d0506070905010905040603050607110325020909070303020303 70
    0x202030200c01d2045070306508801480259071001c102c4504040e00a90040e4000310f4036080d91b0300030410603194842c40050980f456800850640b07104141c0c3c28240051080600004210390141c0c032183c04140008120b020700826180d92040e58404450801060b04096601708003101015080040030340c1c4000003409400c21108440090800341e074000080b91624103c407840c44083c00450400c4c280000d950155040b1503a41d540213031a8011050744410500003201c03c001e1740d0384288800c1e81c1c500150407080c184070182c07440004074203480c1c00004204584e044120141a4800c40684c84400b01c00d101036001021002c82c00195010700c2030b08210a4099201c4185131407181e900d0000655aa01c41262100358001c0d040c1c0e0344a040444000b400b4029501603107001c40c102c0d40d8000380038202807145100712904003028210b40e45540d031302200c100740c0301d60b00c6c00c01d280701c288060034001d03030111402c0e001c6062204010520042500c107102d4500801050009241c00c0313007504001290b004000c8a030b00007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 595909559 1250 595908309 595908323
    0x20c07292802070518010305011506050a030b0315011203270302040905030d091a0606031306050613110d05011208160c0f0e0402040506040e0c0105070c090e1e03070b04 74
    0x210000080f49440b2030341c1d01050303001080c02900004001180c01c050706036802200240300c99a00f00c06450210111449207000042c410804d40303031000d100c0d40c403401c620000103095610301408264040c1c24400c00ba0802030070411404500d90816800c02030780c052a8000512f50f0010b40003ca5900c508005030b848041e0046403540390881c10030000b40101d6045800070f413400c0040e41c1103420008100e1280e01d60b07000c95030700208007003000b62402c076059071311030300c5544c1c05807140030744a60b100c00107050040c20030760f00280d824400b0140908140070303d4080b800095207072900d07144c05000d5101a608180c3c003403c004034500282c08041825401241d880700d40984c408100e5040c90710308421a420503074003501000c1d0050070302083d104138503000c080c00395008440910541c1c803414100411610050200754840e03000e010b0803446540120040d012050041401514459440d840303901521070010300d00e40550003851030b029004403025000b0f10040ba282c1c1c01103090600e2a5240d820050001e00013030811 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 595910809 1250 595909559 595909627
    0x337020d0f0203010807051503060d080c0102072103150e150d0503040f0f0b030f010e1801180309060507080a080402060714071814011206020c0729 65
    0xc9000e9081603003404407801e01107540f980e51303010ba0f98407126640940c40c401c8503c0e90302d100100d1042c50a6901544004004a40004c1c2c142ea42c0344103079001040500c6255001e0100e000441d800c0380401c5104201880441421380e00b441e4001c00f2100040500d00c4081c0c1081c9041c4800004000e110b030b84000d03a00c0440441c3c58080e000203003056003074a0010900d100008000c07c0640d06004440c3c1101d506403000d6010b6602c40f01d4660541c0001c491142d0128041001007003014244950301e40c2081441c0302850381d03052061559070940e580c846038050440d0403560403030109a8041c400400410541c6000e07410107e0701e42d00c1d1203482c4603031850002000801001300c0d0543d07454034203c4400319440080045040e69001c90355440d440c845c8101400550f5041c000343d04a01180039180301d01050030086440e0340c3c00d0020f075460740441a07101340e601c551700344000c001e81002081842c000c1c000f840c241d0b0508074220400681c0a15880e9070300710120310140301c40e00324201c140c640000f09403d09212503401e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 595912059 1250 595910809 595910827
    0x30904020702151c0506060f07171b06011d06030a0b040320011e061202040f1b0915020a030e120a211101060605041a04051302033702 59
    0x30b4200075203418507005600061050030441d403803250003505800707a5414001507940d8010487c0c28007070401d010070642d00c10041280010b0100c0d50140310303200804011030900d40507084044541000c46d441012741e80c00341b0014410400402c0170f2465008841034030448130f02e08000480c0d16080d151800a20200c030b04408070f01050b00680f40d5000000414009903078030585500c18070301030101000c80f407482c070340c4905101c0008891b0340a140c05842498821035039202d150707403d000041c001d00080300c94907a59018803481d440e005c58611101c3c142240da500042c1c0d418064418a00b00c2c0226400c41558011203800380000d401641100c1e146204440810341d1110610b00c680c14015810302c02004c90580d1540c980707a49401da0704070401c0c400e00b0b6030b5100410241511050889981d0b003c3d90011035418002081520200d1201143c200c0742000c1c00d83c100303540e600100f0070300e6444440945031241c010003000341102e9500f075a20081e960b001d0400054032003040c1d00342115941e121903070460640026034805 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 595913309 1250 595912059 595912069
    0x3070f120809030a030f110a030206151c03081902130b0f19081b0309190201050c0703060506010e0d0c0501030c0e030703150c1d0105070f0501230702010608030904020702 75
    0x18550b405803c1c1c0d04803103003d140040c80c4e02c0245004501260490403000d40e941c2e000240b4410542d4141c000740309685440c41c180c0710301c4580800c1d41c0d43c011114415250480f40c0a4800d60010344a81c489040b541001c03107400300b910a41550007481e052051040210351841d24614104846816041582d202402e4100007040d204181103103416020f03045160f0405a4041d408911a4001e440c4a01025405065154462109a0b80d02d901540034000c00b0080d02e162003003010303400d80305040051900100a0b00d072420150b0580c820303240c2d15a64400c0000950b0461041d624000041790f0380283c80c502980c4000244080c0d002d142c0c1095952064001d1040c02800415041c02c001011030f07464179a24504614080315001c041e01c0d00505100495580600a4401032450290300944070800c00e4540c2c0110b03425009480b00782d0f03540381c1c19040100400d070f00b80302e100094180c002c9a8110340d401100e051880120184c010b900f160300d084410007640d100441940c0c1100411140560707980c1d01e03800042c07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 595914559 1250 595913309 595913317
    0x50d08040b160302010c0e030c040e0c0307080d18050303030a050402041d0718061a0a090308030c0d0614010903141c02031b010b09070f09180c030b03070f1208 70
    0x40514040014151500b003107400e04101600d21070307070091107100e048040485440d03132085240d94041d0702c50308000c0200d14054001c03550b410b02c000200c8100103141c40c0085e10380b201d01d0f03001eaa040d401440c00540400d80c08104a2906c0e461a1806500300d89880086541c0b4800200f500c00b135555100c01041c2103540d0750b040705810032072026690b220181819049074565010307104d07020448400b0905070210342080c0c0541d008441c0b081075081e1580107a8180c054265120031880010800c03100800310000d05140007650051a400c1e10303c2da01d400c10b006e00401101c0160300031041c500d2511004404903070340240b01d141980d034400d00c81d22a00d40d0401c40240f0b803100c9802c22502c444001e115800604d0b90000c040c181c803054500d02c0d030391441407010006080301e200c2c80032035401c50402d02c00201a82d0050160b0100e1030140d00d006090b20b50f40300000107200102007a162605902d03102c00100c025411301510300303034230320450180916628000342000c4082e00340c41a50810b6001c005c5039800d100910301a5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 595915809 1250 595914559 595914569
    0x60c1b0a020312210c12041b0e06011803050c060a0203121303090905010e070503042609152514060f060901121a090a0503040306051b0a09050d0804 65
    0x340d40310418403c14444030340100300840035204520054240c140f05501507039000d441113103206841e25841650992480400a0085d00e206405080500c69041f4800b0700c50002c0c100f5041d515014140440010460700c58001001c0900136120024008150f0101c4c1e501e030a02011154259a0181b0310300690442c00740400d06080c230f80780702040180d007146020304901d1842c40390340d07283e12a0303407210000d1040360f03400e002d5804035a9150340000c40c80c50080d001150014011000c03414921050341c06101e800802000d102242c600c0403c1045007070a00d0340d4050021400301807441d00740f90195005086070301c90010440c240356210018403091112000c0a810344800301d4040e182c881c0b0b00031030402c085501c1601d0303140c014091400006074401400c40340d9002950f2148074804c4a40c250f00c1c10350030440003c2e2038202c55001300581c0d540064bd0400c0200000c5100b00b00100e1545800c224110000c0c2122504c0c02ca8810108010035039150310031070810588030b0858401003035503e54204040107004503008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 595917059 1250 595915809 595915813
    0x10603050c030c120601060509040207051e0105070509090f2d011e06020316020a050307030b090c03060f01060f1806020f070f12140a020d0c06020f060c1b0a0203 71
    0x2000340000468009200002a0101ea00410310300007405510740d1104c0091409400440c0140009031040300200500c4400910240c209811900c50314209030340c1d8040c00441c5129645400803c2d003081c01480c0d40a07400b130a0241c208544900070980440c2c005200070840e0a580000400166115400d0600114000c03d4051500c081403648602c0102c02c1c05410311981e041032061480e46c581c98641c0d010340c0c080354050b40c10a40b100d21440000008480200d13809410040e0200b42f80e101001588000c50007161001c003c2d06042c81003e0501d00380c0e00040c1e00a400040c200031445110021050441c1e4043c5404140c540844004442a4a03a41d4552000c1c030003807000001d546a002a8002010030b0b00c4090f683c0f03c2d80c0d00c401c2402070030705034414440c08401c4003400b000466060004d039a00c00c80d0481c25250002c0c10365000801040312030008541d0500700520a0000541c10445803840a8a01004026034180810b050030a07000e28840c0381184040400543c0c0503040510428400c0c55001d81 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 595918309 1250 595917059 595917071
    0xf010c15020301150908011e200a051804061d0702010e0d08040201020d0e031c0909150f06020a031202070f0b07051b030f04030b0c1b011a03061006031d01 68
    0x1e0400003215140640c040060764040300800c4046061180d619000950070700346940c000410080e1000c1d0030108040b802144407042c3d2110b032010044024922b0b400700b0703030b1540d41d20403000c00302400101310185030300d0045207402d50511203480309020701071542008801c54410380d612194100e01525482c0c0203084240a0044010b240507000794086000310300c00d03000e442480d144810116000011440165895403103507001c0c010207814001092080d106500d41448581c1d210110b40d401d030b44803520100c00c002d10b840d90070410145184c0c2c0c090f01525051000d400c090a660310300512080d41c9022401c000396002600b00c08101e107000508000550096908296203040c1c140034015400080100170f100e07041030f10040c84075801100300d40303030b40c0c004050036410a400c540f1a90519840101300d940f90310030070052503200c407040d009006e140500640001c40c0024400c0d81302c4a042503d0303070607a40242c0c01007007031050300038007842c4207402e44546180010381425510403481c09446130081000b202d51a001e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 595919559 1250 595918309 595918319
    0xc0d0302030a0b0301020c120f0c0105010e0a1b050724050a09020901080f0703081e030109020c0d0806010c0b15040926070f080904150603051f050f010c15020301 71
    0x240155100300070842d01000320300c2d11881418203030310400002c503036540c000c075050503200c80034100074012140c1ea03440c10601700307042c0d4503080303084490a80152800188482c02c1100031400c1d0b0241004071580c02c8000c90030f40f08583c0c0090030502800340e00403c20211340d00c5202c414402d202031003100d02007a501c14445824500e10f10401416840016402041c5000022131001000541c105000703007203400030300c1c115180d520380102c190404001e07041201071121190812422510217140070303251540d00141c0c2c82860150051800c042c10720b2110a00c9500c4080001c180c0e002540300d2030782e680003142017449984bd07801000c104000c00b021103500c2850300341080140102028070444150307421b442c2030f10310328105030561164014510005c10304009100800d0014180b8006803148400c051300104142101151814180c041390f0040c0001030303030300d40800082d80388941011071010400780089403802d040002190000d0310081c80c040c1800f11860a000410146031400026a201c40e03200f191296128 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 595920809 1250 595919559 595919561
    0x109111219110408100e0106052205090715030c030b09280b0f060a0314070f0f0305100b07020a0f080a03090e1303110a050a050102041e150c080c0d03 66
    0x4007040e14a85291003081000014808101e41c1510a214002d10000c010041d4110180051406101481d500c0352000165a15490441c2d214045c540801010f00311f00c005040080702c60042c1007503074075405841c1c2008010400003018a88031203034a0302181c1010f200005501826840c0e014542200181c030070403403071501c0b023030305084114810000d201e02c90910151b00810381b4601000281d0001500039070820910303050004106000c0340b414040388118449510481c0c00d6422583c0c180480e5030320740703101c070f105600c0201c0c3d030000009814100000e04020150034114041c0780a040c08441000030303a10b0555480a0645004095840c0320000300b548940c0d00030346591810404a001c500c0802011a4800704460780901c01e0803010140c0c1003442e025101250010103c8101c0d4060b40900c4074181c01064080c0062007515020382e001594992800c02c00300c041c0c010107460544900302d0040c081c0b207120218903542007240650303e041025041141040c82c15407141380c90807407007440b6194464040b90b403d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 595922059 1250 595920809 595920841
    0x6010c02030a0516060f0e09010e130501140f0a150302060d0b0a080f0d0c1136150105040302060f090f0a0815060603010b0d09110604230d0b01091112 66
    0x203a654080c040750603000c09503071a010601440703601c141c2c43c50061007540ad0700459a03a00c10f880070f41086c5950801d031280f42c03c5421801c94824502808402c100c1c00d007540c91005604043c610a0410441c200c05031f4220701c2440c01c0c040284922800624800c6c02041d50300a1403041070018540c090340303035a40d1407040c0d41d0000d110720f00c902805258200d03100c1d10301800602009a412203190b80350411404100050000c5217200d41c0b4503540009100c86a80c1016429071881452901c180c60072420300381c50050300440308e0105070b810888100300a00058407058142c50300042ca180c234650700c401d240303000585d0101490761001c0e0000804a00041c12030380010300e01c00d10301410507415280b92101010b00189210034003c56845c104100404041b8129031340c4241e0b10380340a080c2003140c3e103890000203891b0b5400341d8041404602c5c0a44103207550565600c0000f05e078841100c1d0100340c401542d07540c80315034005100b05034107555110396441100480300105c500c04420310111070258a0039840071101141 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 595923309 1250 595922059 595922069
    0xb040606050c0114220507120b0603011b0509060705190507031202071a03100e09070501120212012105011b0206060a0e0105040c050c0601060c1a01050906010c02030a0516 75
    0x804c181d00c3c50311140041090500440c24003200c1c00881140b242c2c980550b0317101050860300d620031f103e40081d1030740f0702485070480e00c1e11401c5100e619052601c109425600e4441914000301c0742a016690041c3e003001c00c51311510001d03140551660b90038107103141024205c00b07983e403086903d60050350802001207071351010741c7d01c034410070005400e00d04012640c8500314020000001031480046a003040f0070307000b460784000c84c140310350300780c0b5181c42c8a0703880a14152801d201320341c0f0145d0b0a004668000991103040c180790881181400c04256016000e07a0042c480c071806000c42d03e01d030b4212104c1428549840b1900b0100074051024039880000e4000041e400e5540180207403404920146801030aa004660b810b4a250741e10f6401c000c10413004000344070000d8140042040310300e0420b182448403600a0030951607004000d5060b041c00c214160a51410b13007111640c8000511003030f41c071000c8080e0800001e02c0e11000010062020a1800340c0b41500580320784a2481c0004d55045140e686600360b80c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 595924559 1250 595923309 595923311
    0x12020d0516020d0b130b070c020105040e2203030f0606080c07020907110102070309060f0203031e0901060f080d170c071203020d020706060312020703080d020309030f0a1d0f0906010c02040b040606050c01 89
    0x1596600e801c94401c230078104001d00049040004101d0002d1100700543c00940000d58560340011814403180b081030028000c038046074949045075a80c104602c5400020060f0703040110181c50488940200c1344100c0030003c3c46070307400f0307000b00b919540b0442c030091880149600840d42c9604500707016060140034880c01000840ca0300d6103080c8188040244c2e40200f80702c1c0d0603c103280d802981322070100c607c020b02c40e6006658889001800c0e00d030307030f0703594200034154007000d080e03200f50f40d0400908102409000356540c2034018103019080d2030300300c01c031251a03420086100340a05200c2046010703105604c1040c140d5400850250240400c031ba121408aa114250001c01243d0310301d000d0b41c07501c0043c4009000348005020110300042c0c03d0f0000e503801807a000a6910308502000780b80e6107500702c0301c411000070f1240b407400b0200341d8800c03071495600e0740c007211007181c9246a800062060000100b81c281080720704940340c000c40d20f4540141980207170040040c800075032541401001e6030401020b104441d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 595925809 1250 595924559 595924561
    0x17070818031002090303070b0603011b110d020601050d1103070b0301032003010c09292b1506030903180605090306180a0f0f05011812020d0516020d0b130b 68
    0x8525144201c441302c0c00c0c041c002d982441120f40b00c22440000040c9526059529126400014040541030301c3d00807a03d511514203202541082c1440e000c05426210103543c05500184903a54841c041c3e154102c2e405440f800400224801113810461140e00001075654040004410400b010701c1e6100d00409151080c078009030007500309820382e40308120000104100c01d4040c40400e180107200c08480c0c030281641442d641035142440c0041e4800c2800030000c1c42991120031203900c0304040c400020091000511180e038000c005c0c4c818100040c4924428035654110400c10103025243c002c8031812030307140742402d441c1e442c3e5002d0803690001103054428080c000000c0e60001d11384c002250314030305100040c110301d031080d13880038901d6904a1080e61031400b5007942c3c10009800340101500c10f80c0803520603004a4040c940109420b011490300801e40d04941003c01c1403aa02000781c8480c074803c050100b00170b40081c00401c80701080350718041e02075074141c0100810880704035180031031144150a00c00701 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 595927059 1250 595925809 595925833
    0x30a0f05010b30150105131103070201060503160303173619080403032f0a11010203030712021602120303010f1a0f0d2406020618030301031707081803 66
    0x113410074900704030380c0c089a1100500650401c85017030400c14094007000964000c107040320800703a400032500040180c0d12880103201a080074400324500100c0c021a911a590850394041e040c620914000c1a0ac0360310382001401c2d04c0b000d889204800c01043c2e40940d041e0344070716104d401000c2011914001d6105113540c0c01041d518140710100940d0f08100410704040c19aa404c4900500090400b16008400c40080780a0804191080c0340100c00741c00505d40c9460b14944010640d54504a05040d500b050040258140d0041e050380070781446000c006030f45d4210300307528401002450341c0203504204401020f140c142000401941640c0714074040700b05c201c1c1d9551400c440b40d18140000d5140040910904081c0b01d508009000700c0d44100d00c000c50071091907401e004001066a210241800709003500300f00042d018401250084400c0c41100a10040701400c01d68901c0180300c0100355040104d1840c900411040669003565803001c2c00175510061030400e1800b490751429a00d00c28081e40c020861 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 595928309 1250 595927059 595927063
    0x1d060f060a0b160602040e1f050603060f090c0d0c021b03011104031101210207060c020304061b05030f12100e0f0408090a030512070c090605030a0f05010b30 69
    0xc21214851040352900c00d146042e180c0359860210100d40450b000c6c00301081c1c04030f03c440c10340e10402241042011100c1807414180c0c60031030551185025050402c00e100c0a61110781e001c40e9001019216400c0c035844540f0f90020500c1135007582c07440f40d49421410f681c030a07804502c008020012103499100c03021000105401c884070300700e0b440764141d400c210810000320f01041d07038204032005050000700c40105001c440301c03103040d03c0301000051b94009030300d0301002410301c0340901110483c4011810241480406011180441808204020304000c42030800074200100e603048600942c25503201c03444251050002c8105a81c668280004142c0205080588c0c90000780300d07404410300b2000c0368441d5154501a41e12100c940d9070861140f040210101d1000c1082c40e1185007003149440ea00d68082c100b544106035540c20a64806050100400140c0d03000550401d10503045103035046102440e01c0c14500412b45400c4244c0c00603940c100e40780540034040c50b024440c60028011a11680a40c4416a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 595929559 1250 595928309 595928329
    0x80c15010e0f010303180807030602090414100611030f0a030606021009050712020102010b03010501180e2b090f0f18020306131509050c04150507050c040f1d060f06 72
    0x14610b051200100007103841010802d900461104051440686800d0010708184060300169800c0b60002450a5142040d102d05502881142e134041d4050420000185000b00c0c144200010003554000140e1217050074000c490051075154485680c803500d102c000750181c1510310502c4094098843c2854510002d40a500c2550341d200000d00041c0c2e003445580c40030b400c00301c0b070264110b40da520702514203501e0900c195406803002890458500c42540c0c50b030b20946d00c59131000034003500428043c2c11074075543d0309a00010901d441582c0d154000e108812160303144c495006465040c0c2c070031000100710030803140b954191914604958036414038202c100c804d91005690041d00508040b101a02400c0c0d00d0740b00249501000580c01d800c03a03602c0502e40d05441e02034a180c000c02000013801c02c0080d40c0e001c400c03074030f190f403d00b061400c048098940b65107071408c149095008940701c5122110b14051a40326607400c01c0c000c500c00041c5901000401c0c0e648000f200c00d4003030030301d54070b0205d80c0b01d241480c072007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 595930809 1250 595929559 595929571
    0x30f061403060c07030e1005160501050a050c120112020d0f061406270703020c01020d050a06050102010e07090b0a091b2a02060d060f06020f0601050d08030103140703080c15010e 78
    0x88001b080c540900c0142103025804008001c0103000d4100700d8150a07110810043c02000080b6103030508034180780417a071001e050764401820401045240b01e080f0003500e41100d02d01c0903582c02d0041580041600c202145000500300101590500c082180b03540c40703900b1181c1e00e0b5110f500b481d80c403c0207020314503019100c01d40b02c044c402d1400389562681d040083d41e1200907482d0240c200706905000c0c03800d81c0c2108240300c03e0181c4030740c10000d90301200d2050381c0c010f07c401d2009000b01a6412802522080c1500540c401c4644580c40192540c540c2c40d916002401c0c03d810070418403c0d62030780104002900754100e000143d10ba0101040401c25038003c5030f1180001030385600b032101c3ca42c00c015050303002c00689c04503a911540d001510705545a44000200450340203064405c2000012034107268051f0841881481d0751402c54001c0b0b1040016a030642c0d40c065070f264070948580d07203d41e15105203603200401c1103100041c0c89044090100300a802c18101c4500455142d0b250804035a25403011960 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 595932059 1250 595930809 595930817
    0x7140306061c0b0910050913030813050f0d0302210408042606070207030c0e220204090222060801050c1207090f03050d0809060709030b07030f061403060c0703 70
    0x140180b2102d1026503036407007921440094a481414080350410030101c07004402c80c80804010046802d0210440e5480740381858074031102e894a5401800800c0c000c2e14188002e6942e11418080000c00c0100042d0b1600c040120b48200035920743c01000307540901a011040d099800251440e2403100880c5070055601103100e40c14607060510f1130154250646134035140003030550401d01c01d032100740403190041d41e07140d020f46000b80c210308240385500a1a03106078001011102000310361400480f03005540d4121043c60500007100d4000100503140750303000070350300100d600e001d0b0301d100295103000c01041410030824003855503601c1070350b400c13507000f01c43d22036024000308100c401003002d030200c85911050038108103e000e501c03075680741d0501c0c001d07030000ca1341d990200101084a6800c1192150b00841d62001007550341b41401e40288042107520004001003001004940c140f8003940000070104004603080080d40c2d542d0404480d10030f042100c4a010780540b401240e414000c1c441164003682d01612 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 595933309 1250 595932059 595932067
    0xd0e0d020a080313170a0e030a05071e0905091b04090c050f0a030503030a050a15030210082a0d0c050a08010b130510020f070b0301151b0203010903080714030606 71
    0xb40e074011640700138412204201045110b40c0000d003109100c0d0020480c003686152200c0680d00003910070440d0298182c801e51010441c0c00005034000303049010360346d11915010a082103000a42007103865030300402d0b0464102401c010003044001594030710703131914084007525403d07810180000c5071000303c8080c2c112001c942c03051044c0c1c1040340300036070b581030050300418030300790780e500c600341103800581c1c000700c1d501c1c0c607101880603110b1b01c0d0003503104000420400007215440c50f40000c01320800e41d031b03600301801b031403c001915021403540036507980300039140408840d003140c420329802030f071180d48200c1030a450a200c081c00030348504155003a6801c02d1315510341c643d003806003070386043c1c12000d00c100b08400e42a6010032151141c03902d0b001c40e04460b070010081040030035501742c184400ea0700580c80d00c0100380010040582000d65200943c1014149100910f0b01100c041202140c4480040d4140d802d04c0044020594030100e92885140180c1c1c41405041003088040c1a620065400c40e0740001d040c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 595934559 1250 595933309 595933313
    0xc0405010509030f150709141323161701060c0f0f05030f030603060f060f010e0d140307031e050d11090a26030903060a0504020a030602040b0d0e0d020a 67
    0x14001c0120002c0181150450010301001d00c0c80e10340b41590798140e0300c1c80d8505004125400081c04e40c090001408841a2084030340003280502c5119004980d81944511100012468400710a080660040d05000c40340c42c206840c600250500310619000841c407082d03003841d4020329a40c850607203a0940e01e00c050700f68a41c0b140840018001c2055405072000c0c2e2213000000c00420040518211145140340c5924211007003504200e801040184c040d203076281009030310390ba25214003442c45001d0a007000120342d14000b00720380c090800002070850581d0940300007034070000030192026a21a0340c50343c11407480781c00100041c0382914039000100302c0c2070090001e042da541d00300001014020300c4042c00c100310364001400810b0f044c0d10403000050011031070f00346a000360342611130005094008518044080d80881c2d81c409000305280222175840b00403c3c1190342e00360300c00c4001c58208106540384d9883d100a508907034040c400c2896078a291404052140e00080b8000c00c004140f07401804a4001603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 595935809 1250 595934559 595934567
    0x309020f09071e0e010e120a0201110a05060901020702040b010908060705071a071e020c09040615030b0c03070201151d0a0b041d01060605040b180409121d04050c040501 74
    0x10307000d00d0034403c1c0c07081110110490794810f41038040340d95403405040504100013400700300080c841a8086c01c588180904203460000b4299525642071a165402c42d01e1807400508002650100801030b004074018070282000c1500544481c50007160200040d0440c0d4005548003201c40c4079860f883e030017580000c1e9400d07000c0c0c1c0180a41d14000d2030300d0700d52052401103807600040100c03020800710711820713540224040709400517001462580010109070b03194000040070160018002840c09441d01c0004c4078800464a10100661f4020304003200c500b00010b400c011a04101d400e140150700e00020b220f010200d04000344205d07850094404084290782e80d401d0b0a008005011800e010b031038018000303c584440c07054080c802d500b021002215a51070b160142503502c03070f41c0440708011040c4000e100030038501c01156940c04d000401461070070701d01d0380458042c00e908031001d014051748a000b800c016402a1140c0b80c4001d1280585040c0700d900010401101d0060b595034100c0e2034240310900c841c0d406 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 595937059 1250 595935809 595935811
    0x20304141f0f020409140a0c02010e0c0f040f060e090d02070b070f11031002070b15010905270c0901080f070e010f0210020408010b120a030c020409060b0a03080c0d0309020f09 77
    0xe09201514081d210301031441610061b035005002040c516007007003150f01040c400c40e801242c0920082c08940303105800c0d07e0744d607803182404900c00c0c000d4914820356540c880c5c1c4503103071b2240441f000744819070380c0b000521203a5904030b80f4101c0c18001c076001c6d02c495a102003001401c1ea102c0c8880b02d170034001241c644025640300d240048172411820342000d14203940070802d145006103100809a038501451030318142034100545180000c4201e07800b120b4540e03030084071001c15164251442d12039201040d1000541d04600d54500403420400302c14080640303046001004240c00c00e803286101a15201c0d01d44042d1242211884001001d480c505c900c81d44c81003100d04c0388801e80f032044600103101d03820f03910300301d074015031080380140e645501040b240d00f8837422580003c0c8000c0301910301d2814644026000c4080188020b200d141c0d60041c8008203c00c0d0350041e28480c402074804d84616881e442d040380c0030743c0010514541481988866001d4606c64059184100d42c081c02d840c00420707562080c41070107a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 595938309 1250 595937059 595937081
    0x20303040f060b0306040605090f061003061e020711100503040f1106120c0705070b0304050a060b12030703020105060a09060f030209150d2103112703010e01020304141f 74
    0x30700d900382005a1340e020450303940a00e00800c000501810f000008914001501d0007842c0c09812117820801900b110241c804101c1e5042540402d110104040c0d1444020000d00c2c2c03030030003e102040c4101482681e0282070b50034842507944001450742c15105840501088400608900c00c41d4a454001038031200f84048401014004c207080c9a9881d80100d01984121078000c842080410170b07005000c4101f00e6000184102d09541c6c4c0345003032645500340c03200941440a4001506e444011026489003040e000c18903105200b9603899800c80d250090203040140d4410784a4510708c90003080541e468850a812600280c803220602c0e072840c0e0034810800b4000300b06800720450480300c0079040d21030305c1207420790512440c3e40200c06181354058035030401c0c0610340042010302d041c0c2100c5030985c00c4c0702240c0308000b4403940e2481a4551030f0b249107000050030300442e01542425050110004150040c5006601c0307581000c050907446c10300b50303655040b1902d01c000c1901103408200c40064059002c440c01070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 595939559 1250 595938309 595938311
    0x20409060615050712050910111c0210060503060105031b03150f180a0c230301020f13090b010e21031303031206080d050c03040f0603020a020d050a020303040f06 71
    0xa40c0c1c42504a4a28140802c140081100002c01d81d0070882441d82a194107102d500f84181003450078800b00318801c3e107155040050101c000704043c40a01e0070000c00401004481d140c00e2400a81c420003500c45070308802d0005c07541e04148002c41d0926002c10b0041c182c40c0094010038814120400500601d80000c12150301801144c02070131110900041e0ba40c0302c0c3c04468003ca4460034141070300346084a1540340200950400705c0c0c6080000c5001c0c0c2e1403402c442c4d01c1c2850a007021030015041c600841c0000035181d0640c030004201c0070510403540a40800380c0d400311028800344c0e071080c203501508c8050301818009540e069515420745850180e20f4000e01c00c001403000c3c0321071b200c16564a541c0c000100100902c84501d420420075a0005c08804138008400007444074504d080162a51015000032200a20202040760140d080c401c1041d2002402b580d284d000c50300d070b5103c2000e4000d500c10310005005018420300804880e01502c1119a03c0189500443c0303540d99948400d0300102106000f1aa41 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 595940809 1250 595939559 595939571
    0x3100509122101090914010b15090f040f0f06060207080303070809030c010c0e0a091b0e040213170d050406120203130219050103050919020f0102010b1005030601081e0402040906 78
    0x300042c0400b0a019020305440041d000401c2c4c04e2008820050480c034100b1613041010032415915000c05844250a222204540380c103440c0c80010640c820001d1101d030041c0c07421a504510800396000044101350441c020050b058446501301d07210701e1640126856a882000460324503072041002c070358480b1040050b03900b00b0703800010032425560406000307400225106480c851500c0c1040e1850028088040c0030441103080402170344042c0e621686107028885c03159030074065600c56404071041140420100004035848031b03000060442c482018071905c1c41107804414a4070b00410440b01a40d800c1d880d8507107200c3d204100390019501c01842d0544452805070b000c00162200c0e8407219065450300d034007101050400e80010100c600040090260398071220080b180d06080c4050b08683e5034066450070051510040103078054204141c0003500b1501114401704190741c048043c40c01080f00f640d030110b490700d801120106040300d0203001c1c1540011384c00400d005142c9903011100c0303203102e110007042c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 595942059 1250 595940809 595940857
    0x70f030c05030307050a080a051e040219030c0906062609100221100612090206040503120a020114070813140304080d02070807030c170309060a05090310050912 70
    0x150f41054039120701040012072001c18560b0030113016a0f000c200154200034034a8054074401d04146c2c16080c140c48540d042011405540b98554003481c04d40c0250340100300a0365900c0c01d01002c0d42d00388158402d003854080040362580c4222984801380d00074040f461700b00d1040c02050501c885c0040c1c442080c40c862400c0c16004040640040c0c200c1000200c44000f08070f440924040c1e03078450003001c103501d10802c80c40a0060903001b142d402a09907108600081002081c40810131910a5401256140c8680e0308650b40c072005050091180c0d8110340e000b802034200c000866000c00c42c0a841203004201400b0000b8034546200c10107800e528040d1420520b40a03614032260304541c0103400c00c41c282d40028010525450f010000c0c04000c0c0803a100400d6400e24503103c1c6149047c45014240545c15400000b44a80404200341e03024800e00800482c5c2d9140168006001684501c0000340240a00e2800904904aa10549100302288005442410082d21140c03c0c95804070f000800112203110350800e03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 595943309 1250 595942059 595942063
    0x70e150414100306180c0816020616030207080c300307123306050c032209021801080a02030708040210090e090a05060f01351f0b0303040b070f030c05 66
    0xc1005c03000040041c01e00701040c0001d0500e07000920f005500a20603500355405580003e19a6200c0c2c441244040c0aa00c0840220003921800c2006081c2c820003144914624001141031002440c007800d100990000400441c103010107104500001000f0038000113400a00403044503407100c05080000543c4030701032559900406202c0d006a84070010040541d9081001c08e1364000a020241410f904007800c00302d03d16078a21501071040d0500381e00c08036104403903541201c0c1c0313009050003040554a03000d141607560300103003035511070302d0008401d000411450000303031080700c0c01a2081d981d8a145039945400780b040006103002030100308859081c0028404074944141801108141d000d071180c0402420498a0601c025268600d0410390000410150030034002d0458440418906e0f110482d007600c00c00c40340500758011906840c01054100e1000d540b41c0c03189030440300741c5410100031110055042c15500c1c01030340505001658104401004907042d10000c0c040b051213481d280d6202c2c0041c0da103041c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 595944559 1250 595943309 595943339
    0x120f02220f0608061b03012c010b0307020c0402041503201209060610020a140109060c03020702120106050d02040509010e0136020f27070e150414100306 67
    0xc0a0603981e0b4400d100340700b002e015081d0089a0010820b800e12004651a40c8610042c131a00075200001c0d081604070380c0c00c0c41c9001c1c42c282c80c1a841d41d21030b503940304041c7d48641d0045446800500540074031003038602d424420794066820403c080301c8007414603802034004040c40b55101700d5142a04801040c050000f400820000101c1d04c01c0c0da0003404d000600030701c1e155000e001d0038816108514601c0c011a4000380c42200c054000d030078207031902c42c0b0310315590051841c1c1101410050910044050568254000706150f910030303210603140304912403001d0b080f10a28020300703074030140079070744840585003542103035411940000c00081c60002e08010282101c103007104000c102c0450201d050304002c445042401c1c40d01120451450b02405680028032444847c0304251181c035008a407101380c070b01e80c040311540a821030300603405241007281d030280250071803104041c4640101c001e00f07012004901c040c1c0c0c045909800a0240030105001000080004d10485100305076503903000042c00600d000c615 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 595945809 1250 595944559 595944581
    0xc03050a121b091805040506131401090606050f100f0e040605100327170a0c02040911150c0a03030b120102030a061a090108040b130c08030a09120f0222 67
    0x6034500f5443d103280c218691410343e00c0d01c3e68180c81c080800c40854404500c9540c418002d2150a40300c0489140101c021b070200340d001074a542c6041d40c44002c04c44281d04c0813054400403030316041c40c04d5209042101441150022900080748121074203c1c03240942c0354048014001440403c0b00c03030319503002c0b234000106000c80b000000d884103000d10f00501601460459061109200180a002e644a64904401c4141c054502c3d8800080d18900c0340d2007246c0d0f12500c980d0040051024a0700c42c00c2001c4803580c0350651130b02caa6002c010b002407501da031408440d0030500780300c05840c1024642d2400d0b00249000d0f001a81c0001400750f65074200c6000f0300c02584110300360b01380080d1140c01c2c4022903601c0e0350b00c1d00c070441507814100440c0e52640e0300041060f43c0198002c0c4114182d65440280b800e4020080c4001003a440f4003050104442c1e401101030011603c181d500c000129581d840220000418000b02400d502da4991500f009428080c081c00003541800c0f40040034aa00041c0b190102c42680e000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 595947059 1250 595945809 595945817
    0x13110d0207081201060f0c110a090e011a03070320060c030309010c18051c0c050d0f0b2203030903030b0d050c010905010f0e0f0301061d04120c03050a121b 68
    0x80110f2108162a024007400ca989803213241404502c00c0644180c0c40070030090071100700d204402c4ca41d561030641200240400010034408580307501e11040c080c5c52401c1b5010b1840e03554046513103441c24005003100440f6000950f48060b20010795101d02d40c079100c0684190030800811101c014524100011030294030b403580002050344090301d00400500028001a10281d0011001c10607030740e0b411025204070403c007001240b01a01480e0500c9808038070343c08540c000030040b00101c1400400814056410702801021070617695000d09042030140c42103080a2020841020001103442984070710391140c4030713050000e000c0220b0000900c5921200f0030881d81584180360340040d55a110040c000140400e0070858003800c894240640b600c6007001c2014000c52a00072119126503094002c2c0008110f049140e002200f041d05802030110403c540c255002c0e0201304012140d144202100300256030107549060504050140454a2405920958403010340f038110048081c0030844c060100080c10b916 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 595948309 1250 595947059 595947067
    0x5190c1407080a050f1f0507090f0b0a08090d0903031121270a1703091522050906282606060a0b0a120608010f180213110d020708 57
    0x5021303468070706031503040c203240d40240c0b284400b01d8416070040b0580319425180400c4a5035140021960000c0d940c2c0040c400a50000c000100b0050340c00040012401d280c0e142d0186070307500c00d02940d4480750700a081000030158442000424450911001e44620707600a40d004400300c01d0301004228400b01c281105402c00188003030480c0c42212030008104614031441003800001d41c00110402da45104688a00780c00784070003a400c110500848006075002840b502c1d189000c0300c0449000c0c2c1220080404000040d141c4680078111201c40c5821143c0c01080d0916540d6114180303c6503a00a41901226241015401007441c0803102400054400d1078008501c06050a5044031110201609400d15030800b07024444c00d52a00800f0f0342c00d8840c0c41d29a00e81e691000340084403840310450030502c080d49000004114154190012400308600c0082030014803c03450030002c080c03c0c400743c000d50203500d443c0c0091022038240c100140004e070f0b441d002402d1602d8a1001700c141d0340700c28011510303402c00017 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 595949559 1250 595948309 595948313
    0x70f080c030a0f0806100813050318011103160f11030f0a210909150f060309020a090b1c080f070b04021908070e060415080303070206010605190c1407080a 68
    0x1402406021525241c1a004d03800c206010414aa034042e41e10002c1005000c0001c1c0c4503405142d045140f00c1d0320000321799494101440000d42032524014490000301c2c1c410240300d00f100d000064501100700b500d02101e04003081d65816040c00746000d41104d500d011b5507080e4116940a00200100c07580a0015245680c5145440140300114010940280030a5501c90b040c40c3c1d848089681507595174034000a1300701c80e80c042d03035500b400706911006858044520110740d1a500d42c11017080d6038800e4980b6001c15854640d40f0b4292550128000e800441001d11901082050440a20507078040c5416901c0d0071000c0c100b50543d030344520b00607507820b0100701c180320840c1403010a4180004403c0d1440301d0060409080301d0f20f072000c0c0d00c2084400f080c00c4010842c26030b02c603413041d00544109880c8075481c80e580d10040d9180d400440351440035018400001500500950071103080c020700003d440c50301c0710014010b96040300d02080030344200440c020b00d40c10741c44081140e00c016011100041070000614 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 595950809 1250 595949559 595949567
    0xb09040501090203070f1b0f0c06020f030a0e0d21111b06070b1b0403060f0f050108030405040f0f020304050303040c090b030c010e18012403060317070f080c030a 71
    0x181e0100d02d6242c41042046460313039114450705892480c034a004844a0542121001b0000140101500781046c00800104100c01c2104a108a80b0241c00340c448001c104080705451b40501052180414100c0080e1015464954440d25589101e54920340c89090b0301680d4803055200701041c10046056018420300e402003c100c003039110711060a410340005014000301d64103020700080107103100620b4007c104103521048e81114490342d1007842903205c80d901e09102c8041d01240040f22403844c5860b0321031800308502d000d0141070316030394801149801d02e0002444004c0c031a6014a5440c0340d41c620100c58012a1030004501403401071004580302d041504294900a4030f0703510806402d07250038208202030710080354584d4410000d0a001000700c0b000000302d42440b0030740c090400e4000300540085514240310b0b514900c1420309811400c4240c02c0c88005138110340807400b011304880b4498a6000d480d5203214000c01025110740c001c422024150b5840d8042c076013045140c1030950304046620001a1382c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 595952059 1250 595950809 595950811
    0x30d050a0e0f0303041e02130c031e0c09060809010b0406080703021503150405040309180e190b01140402070c0e040209071e0807020111041205100e0d0503041505010b090405 76
    0x1542c0c0c059451400c0c55903401c8011040c0003044441508011045019555250100c1d1000c14201c030f42880032a41d507100080081200761043ca003003410030386900140507103503c58484c400700303140c40310f001c100c1c10482d00b40d486c00b00080c40c5600c04e40d250300e990400c84e100c90243d20018000701008040c454214030421541c0b46a0102100381c2ca20140204800360340045080711103004261000143c50b01c4034142154110340c50b03000341e40c101c1e50340000c007188045203611021040c081c080c265040c54140b800c000c210f1310480c0c1005001d80d80b051005004c1d4900c4201501e0b040880100010301c0c1441d1a039a000c41855150b00224241c1e40c8031040006600700b0002081d4402d006140c02c8031421100183c1c0c19107152160a4007007000342080000b1441d5001350301c40f00301010b0541d0001d07259551030025202e00c05480c081101c180c06000300c90f2910f640240108502070000c80081c20441002610489041c0c10042c801c0e6200c00d820307205406a04007902c41c072806440c14403200340d030b5580d10200740300c140e0764 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 595953309 1250 595952059 595952083
    0xa09140d06090503041a09150306100507050304030209130b060604060c1112060726060604060513030c0807061d03030a110a08070b0f06030c010801090b1f030203070f0503060a05060309030d050a0e 86
    0x320401c200140c3d035484a032f0103028088241480740c1c541141c0e0500b60310354000c540009400130808414040c0da681410410301c4d000c1e1190004010130341e9190140221401144519800b041561080d5400600a54150001d0b40c5024094650760302102c0e0040c2cdc9482000d80e0f1050210340c0648030711540a080b10f01da24084043d102d415003983c04c0c108017242c034070f20661080001b0800301045a00e440d50b0640401c00c021500000c9a0350b2041d00d4012203031b1150744511070500890344044103104c0c40c040c218a8001c4013400100510b081c041180c000341e88040c10140001d040740113000c1548006003802c0060810306009440c584d0719441c0c6410703c640e118002a0619119500c1400d03e8081c1e41e90200b0300c28155060380802044000310b85004c12161040d40300318030340800c6d4600c492040c00d98994050b5100c0d603c1070307039045402400c4020a0342d0500c41a10840c0d00001d802009016600b0032000030340c3c0220020007260b260000014000003252002c1c2d031020055a222441c540c5444003c10121060b0a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 595954559 1250 595953309 595953349
    0x40b061801060816020c040507050d0c090f0e040302100f0f14091c020a1a060405100810020304022e0210060b040504110f0406050a09140d06090503041a09 68
    0x1504066002e0076044008000c1030301030710708004c1202e03081e20911200c0c2c141e80f00a801840305086c00000a042600540c9111440519010b02c0f010103c0c4035034441300031103044029105c40d040c10100300f1080d402c40280158150b03c1180d0b200c0c3e1245d030440c8140c00500994000020712000340007500c0c4151415a0780c8040c1d80b082d4071041c4000d91001041c280b9044108084001000c8840c200503402c0c8403070b0b8200642030071228144503100480340740c4607031f200b500203d03000c01882d0741c4c0f094907040540107801103071070b0b607408200560303c01c801ca9070056070414002003030318910000780e03030a210155840e40e0442e14800800c0c9069404a0b0701003122a07080e094490050022030709051644403d402075110b040e01c5580c46031410300301c0070b02c914100d40c041c44820311116540d07516024050504d86c003c10134000094503181c0001040d0300380803000f42a41400130038281d5410890313101e40000e8442c400051340e60380001c00c00010440e600e580080c0d08219001c0304243c075880b8886c10004002d40361400e0441d84 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 595955809 1250 595954559 595954561
    0x827040204050337050303040c060903050703080307030b09040503070b0c0910080606040f0b0c0d021207031d1c0219030b0615120a05010305100e0c220203040b0618 72
    0x10380c3c010403060b1032080407908180080030032480020500810f4144266040a07508401040c003201100035403003a400365100c07020841c0c0d5003030101c444e44103d110140994100310740c103000042c0010b00a6070400c510345030120f4040720b080002050341c101610211841d0340002624400c0117814801640d014030801d4029041000c3c1c1d50100d00c1c0400c50b00140c00030820b102c40020a00d907510400d540140001c4500074000540310600c0748060b40c4a0961500c1030b1142c20240d034555440090307180189035030100e10504142060b5019190700030540a50010014240270b22030b0541c50702101140180354444041d201100e04d801448070b0741c20003400c00358a848100c0014004506a240925007001040d134080c1c19910100c920701d956401100b00c0400c2c030300710070400d025040044e60407e40c1664060b8090390010811582c0110485600081800d0f298100d0481d0f0055071918915502084161400c0c00700100d140b0b6232540101c0c0c0c0225422650300c0c0252091000a0404403180320b000c1600c0100036000e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 595957059 1250 595955809 595955819
    0x50d0c060f020304082d0d051b010e01090606050108010e0c07120c140106060f0504030803040b060111010203130201121b0806130e010f060518040f0305090d0308160f0504050f0d0827040204 83
    0x72342c881c480d40d90b400d6071403441c42c02d003e02c1800d601109540f107a000c020010090f881c41c0c598041c2ca03007840758a00154400c030000c80c074280002c10050084644900c0301e0700d0b040c0155940800258901403071820320100003010804240b80c07503842c034840b1048000014005042500280120348000c4030301080090901041c00020707489000c0340c0e0401d820038441a65583c8010040724640701c040d106844a50011081c081c0b00002501d2008032140b00740c880c40d82e0b50030300c1407c407030071140704c2400d07042480108020ba83c010350188050175007200340a40f12a0f27590b10200c44800c15a01d2045c001300b1941e40d5085105050140e5216140c09803038200c95110081f6401468004943c0000c1d0005c0d00d181109440c007410140078104880c8005001340c001e036080101420040c5c0090741c1203400141e0609a40c540c030030401c0c822501c07040030b008a915031506050610b024011210a500c0410b9004010f181304d0340081a6040c029110020f40c0f155030210310114100b0391741488400c0f200c114041c60041c402449 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 595958309 1250 595957059 595957067
    0x31404060e0622140a14010e01030e1207050c040b01030e070902160c0e06030f030c120306270901060b0406080a02030a090c120507050d0c060f020304082d0d 69
    0x6000c000c111602d54480e229240f01e0740c40e4805085042c0968400b450b00040c100c600b007861407aa1301400c03515210b0060303541c100d40304250310380102c02e030000b0341d00c842090640d8000c0e801b1105c1c004c000f0f412507540010007801c0701d02a0340b103e441995264880c54040c1c2c6285018000da5003010fa0a2a041c042010811601d55135851039004100d00b40703070003040c003920050320480d40d809030710b03044040840c5079075503030741c3d50800c210080d282c06011303010f42554000500000002c44003440f54450003018964954041c4411307981004d000c050307110b448581c1500f580c11004001480310780d5103103c0c0303280a0031b0100b104c0d42110203980c00540c0c081010310042115541243c240c0781d200e0380300c040150b901da9601f40c26000609101070014090b4242c0c0802240c0340d0409510914402d10681c1102c030007685a400f04044070035612070050200c3c0d128041070101501c11103074402e65030307020700469007016140d001031414500c5030a02c03d8000e200382d500740c2d8920080d15a94281810b07075140581b024020703801c0024 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 595959559 1250 595958309 595958327
    0x110c1b06090d1202010e0a03030501090506091504110909010e10061e050702131b091e14010207031e02090a02031b0c0708071214030f071e08120403140406 68
    0x14041c1c500f0240e10f004403c0c002e400032266040c2040a403901d51150740350180c000c090038051040070600c1d2030005600c0c1d09101c5445c41c081c1c81c4444000121b905000c0c20080586000a40d000044801344065581a00d03100070540c081c0030101554000c41c58000808611010f1581c0b108042101c2c00400d00d0394410120070441280c6950f103003040da10307092400824865a19200d0481c0440c0c034003240001d00710a4200c0074144a0366030317a150100296200078010642c08c14150404820748004000c1140d4200c41000c0001d025044c019a0545540c90700c43c40308843c0e9405070059400480c0310143c0c118940040312aa120415600450075401d290140c589120f0120769051850700f40002c00c0000503030308208020040c00c00764102e4114a4031004441c0500ca202c1c0d00807550003d1102d02900b4009020040c0e40c015604103402c9820407a081d241c0c500c02528880006e00100b02c88030303584012440410060010f02d0b81d81d107604950303041520700100524100c080c1141a00e00922080c00031551041941d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 595960809 1250 595959559 595959563
    0x7030c020d17040305040b0a0e040518030f0a030603080c0a06051332010e0a0c0905010308070308060a050607120e04050105060901030203090f030c0d090803030f0a0f110c1b06090d 79
    0x140314983c0ca515068070248a187c03c4601c8103003006c2405000b841c1c3c45441e2801190081d00c0901c400d449000082011954400140d000c1d90000d005070200d403201c1d200a00612070742da15002c03a400c2c0c2d03aa203e4051561203402450340a07004041610140215030181c5e41d00000c5c6a500f0103501e0859880703100514900d69481050110410f10a4001d1010110500301d040c1c210b00027080812440003025580303007c901d0086800e001540d00020b59600540310b8a8100c071f400080b62858a02c0b2541c0860b05500003c1038140e01044a5401042c136440340c80103444040d116100303842542c2003488014100e114600b0009120700d00b400c0040c0032940300c3d0b4068951098080c01c000da26030b01e41d00100760500d07500300d5403402c540c8004110600c24840001e2003030a0410780c0d07159184491b0b00c0e011040d449100840782d801e410140702010518030300007940b0151100e54007010026095000c0d009418941d806442403134095480030303400c01c2c1c0030703e01404096242042210300303514101601c0041000c000c404140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 595962059 1250 595960809 595960847
    0x10816080402220b030c060403170d18080301030b1503030904020c0102160309050a0609081e010b10080a110c06070818070603021b060402030c19050a03060507030c020d 74
    0x403404540301c011200c031544401d00300340410f0500250740c2d40000c0c408000601e101e4880e44101c0700d0b01e41004001c0340c0c190390304042c0442c103180e060315240400e44c2c001c5c1c101d60341c41596220781550810004510b800c10920132000343c2e070b80c1d51450070b00803d50f0001a260314011004810225443d680020490344002429034001d42c64960791b103505802800b81d01514880128101c21140805600011000a48104079902243c081e1035000c100c4d0041c0a40c00b8202450740842d011a0700c080901205807911640a4004651858003102080146141244801c0400e64400134492a420180034040440711305615040c00d00841d21000e550303e0902400c07810030701070108007140e0b1a4400107420804a034424040318522507070b44400800a60011024108a1181e80014080541c000c103403035001e02d4000b001482c0d640e5078207080104849622604c0c2443d80e101d03603c0010309486100381c50b00203500641c40003d4078944030b1006415100884500e80864110900f5806150b8108003d4200340c156400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 595963309 1250 595962059 595962061
    0x4051506061611060f12040506130506061c060f150501050a02120306040204210b0f01050f04110d0f1406040510120c090e0d020c030f0709110d090b010303020c01081608 74
    0xc0384d0544160a40200b00d40400110100703446001c040c954000ca104a04840c000e41d02c02c0300c140102200220024020740021011803624a4403516a990842060f40c644940001a543d004201e402c001c0852150305c2c1c03190308001d901410030f08504020582803e065142003401d140003074403a03200440200c070907003020001c50020345460381660b01414014260f280d1803203654010407880144c06c601194113201300c1000401954a1000b028120380d005072070b94255801c40001c00000c2c129580f110314030100700340304841010b1040d000d02d0b04444560500000c0f00c1840640200000700000c0040e400342d414941441458210110b0180440346035150000d1800454a8501c01594056100c200d103181040b01c0145001c00200b0703414000d290b143c00b01c61001610070103050b242e80c100c2c05420080d4218820070001d0004030342080160005003441d051900c80c420f00180c08581ca180c2041d11041c04c0c4900510030550100108010304500b4205142549484550061000c81c0c882e1004200f1032500c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 595964559 1250 595963309 595963343
    0x24080709150803030c13080102090109380901030614060306060d0e07090b130603030e0f0a0521060906090c0d1a04050d030b0d02030706110a0506040515060616 70
    0x100c0c8a01c05840d10205903650b9003442c0101050680014016078240c00880e10005102d07401442240c0c412981030f101d100c07545107440490700c1642000c4856030841185c0391085080461400310f4200303075130511804251205407000c001001c80e0050341040e15005840c40a8001d641c4e03420081d01d92044003182d00030340d82d202c00d60340c04015000c000016003551040e183c000c14103000ca0b4110415110064420410308081501e041e0700f030340c1e410b110140c0440e1800d60788400ca804c00c2511000710039030251011910340d07a10008900a500190004964070303030b04141503c144030080c0310352500001c1c500000c1480c0d08142e0580c1e0346a070329918081e40b02d403d00010113000c0001224804480e03071030440200c010b914141c2003581e00c031907103c505800040d2504105038424501100d0036034880c0d4000d401400c1190401c0380544108004a8000d6110701c5056500d0b4001901000b0f06803081d845400a800c242c200c25061220300840940341c81e10070342c0148801000030b442c0030100c115245c0c214241031400007442e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 595965809 1250 595964559 595964591
    0x12150b0a020a170912010903120b041508060601020118171b16030b0a1118150304031128170409060801060e0c0f070b070e0a080124080709 61
    0x440c0c020314002c095029a4440240c83c070190008010544075480c01041070b01c805d82c2200e42d015001404070303910350525080000780d94060444424007030800540801d218101c9001d208656100c1c0d20700c0d80c03103042004500d503828000c2c1000480d05c5155002110300c1595844840084a818050030400200f100c00c140540e90000703050102c40c400a494100e440c0e080813034800a4a0f010588100d0719050104e005450240314208021829a01d00c50400c22400540302425400407003a5610003c518162229400040011400745100b070320344d0202c10b4803000965040201140500304044ca07400040041201c03034800c1c20303002c95402640c0c00c0349040c91990704040c90041d50403801d1482c0c50b01d1808903040005600030400d985289910100030707921180d05448a10500b5074142c843ca0b0280b0a401c0010304070310880e40c22021b5070a00d0308a6184e5400440c01c8015a503111100b81d03910b034115503101c40505c40c0038441c1c44038200c0110203060b0904842ca03a54214510500182c966111141c2c2c6003089a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 595967059 1250 595965809 595965823
    0x1051c020f090106050c0721112709060105030d0e2e2c060a110c04140403030e0604020120030702100818010606120b0d1505010612150b0a02 62
    0x802c5580c0c5542c40740c80c01030a5400005449001e0310403045e002c40e0311483c8030340e14841142514004110540b0560f00c4c1e40100c03070403041464000d45511424038051502403010a03040510034a81d121511703141241c60b10340324042e4000d0307010703400c0354005565565000d855101ca619040e150074400030100c2070310542c401c101e100c9502241000300c40d8141119800240b030b1110161320b40d0040e10100323904100c104110a03120700b055015204000a4019034010311030308110240b0701d0300751032a484102c400300341941c48034200b1800b529028003c000030542c1511860004c40f03010401080700e854180d0000e48001c42c092042e01842050144400040d101002154592540a0050038001c50b20001c064840e94081c6c41510b042c0c400c034003801021040c144100301c200c400e2030b5540c40c0b5a00c5a01c400900a00b1800c0d055030700043e8461003007000c0780d100c41c80381402084450380080c0c40c0d8900300004080c10b10b0040e0130303110307a0304000c18043d00e840c0900c1c115064131124048507603158294103090b461300e50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 595968309 1250 595967059 595967089
    0x204360504060b0f0a0e040b0c0d050703061502011527021b07050102030f1e0c0a0b070807050f03190213090c020d03090816020a1d10080601051c02 65
    0xc24442000704002c07254104100101040e07940e00030b52400c5504118003244c1a015062075904400b0002d00401e500000050b00800c0c18150355103031210401400c0181c500454140c03010a0720703000d0030400d14468100c0c0c60741002d1180b0080140c404c2d00f10035580c8046040c031812207003000c140b060b00101c40b045052000074250707208007150b8840001003200c80c1d44480724109181d40c052000000340d9940080101c0d9440c0550000b610f140001c5101c442c80d00d60342e20440990050400e01c4001c4400780700308004541903000f0702d09111946481200240ba0b0400105100100081400450070186041007135030b410102d0000c0d10144120080c800e14000e000302c662020040e4000d00c0001341142c059400080801c01550a030341e0900072030300042e0141d804c50074000f40b10000401011051065981420b25510310042800301c500b039903020340441c20084500001d1800901c90305003d119030244075110300904e1a903010b0800f039854600020511101c95540c0d5034140c10b43c811000855850300c1030681848 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 595969559 1250 595968309 595968311
    0x5160201180e01050406060507030f030513020918010c020111121b16030e060a0903060e0f0d09061b02010905060f04180f0f0506030715020f100203070909020436 71
    0x642c0e10324a0312082c00c0280b04281c0510701d814000304800d80302ea0200c81d421034040e01d07071550004881e901100100310081904036048090705450005070f4620b2520703030052010f0501454407004200003503084402e444040c2c81560300d801e038040220200c40054405202e050f0712481f030702c0c1ea40e5141030f0f07521114481481c001224000f0b91920307010420717110103035074134000e41d214040040984144011440781c0301d0b140010a50340041080040c0d916081000c80c43c80003410341d04d650f170441144600c1c000c410035400021480603807080c80055070240f0010900158402c80c145000e8441e00081d100102d540205801500c00190005ca26003400046600515040324030301950110010f9070401084108500d641035810724080b010051301501942d07002d120002e018000092a00006844940c82c034641c040c03e50241c6c008104504605200441001c1103011001d89d07249403a0340010481300c2e0035004407100c0c510510060101c282c1c450702558240d508089403003001d9040450389452072140810007840c02d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 595970809 1250 595969559 595969607
    0x1415130302120a0507050d05131401030f0e0705030c01020c0a060e0105160c0603050705190836150106020c0907030b100c03030b0604050d08160506040b040c0b030705160201 76
    0x81c84d03000000b010307500c0c0968160344a8011401d403c444600ca40500d1b0b10024070480400d000424100300600b4109405040029008140d031540500f585c030003190310f00064000da0000c00160409106040d4203072800d01c041c01c20a0311190010303840080500800040042406505000d039000300110f92a406410518800d0a985031404a04000e03446c01100e000038248800b1441a034016019903020914040c00207081c006d44d920115400f40307000f00131a02d00305170840c0e18000e600403440381d60b84060b988144600c400101601c200c0c40c0c02c07003480d021503841100348010800c042d40811480950701040752145002d403600e060850180541c0944998031002d030b8900d99044503080860200c11510a49052012803d55020403121b801a8810160000c5207003812000081e80d000040012003c1040d408030310f003a20380c40349850b1850440b800c64080c14984c044c0010b02c12003002220082c10008501440d520b010400142140a5041d041c60410b030031010340030841e8050b510504244030150341c00408 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 595972059 1250 595970809 595970827
    0xb0706020c070305061f06090302031b0a05040f2c060115120e060a0c0201020a1710081f0513020f220e031b0109050a1401060302040c0309141513030212 67
    0x30781c803210788000c6810740e1190000e0301f68018024802101d400a010b0000c00b180380d2050f00b40700c1e000810b41a400015903c001c00d69685910500f9000401203500151038945c0c00b4040c0080c0b12406454000100070315003103181c6c0741d00010821b0541e009410700301c0640e040d411098176a04000f2210b00503403820821610085000098020322801ca42c1502f4003c1c01c1e8900c0c0c05900300e2240c02c050200080400028001c076600d600700c5540c00071100341440070b41c565160642c40c10a401c618807182890540c0e99003044000c4580640c540041c040600c1141c80462940024000d01688100381d009840b8102203082404d403150f01d460300d2a084c12424003c03415080742c040e45980c000d60000500001034110b202c440b0320144103401c000303580900184504042c41d207800303564403084c1007550303095901d4040c04001610f950040011000c400d49001c500f038559460100d1199040381d09025003540604c09501007043e00e010749541140d0b10000c8103400b120039003012400e015032041c806481600000f01e44035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 595973309 1250 595972059 595972081
    0x50109060c0e0f06180109050319050738120a0c02210d02070c150305070311090d12020304080a050d08092a0a1d060a0b040b0706020c07030506 63
    0x204002640c52a00310001030007049410b507122016107030007401c28020b031700d413480d103007580084214414100704015980c2e4900180c641809541c002d50701c0000c02c3d04002c20000d0411286028114030000006070b410800e0300380070b00c1103110010000c6040008414514043e40c48200d071000c00d00c0e100d00c0903281c506250000040c1040c00810401441898041c00081509070200100c19081d840c80c685000c0d80404904080d4000e9075007516a104807c50000c7c07281c0e4194a40d80129049441c04117852a0001011702290303800e552410400504000d5482c0304e6032042d8240c601780d581310704503d001706c8140c02c00328554012134000100c18440c803600d203030501000189175211900700707075214005a694001c2d280d40311744449000004186020986285004d16030300c0780402240060b040c00c2c08959a003c2c001c04c21898640039168030744204080c4100c0341403802814014040f2681c826103014904060251580316421002d072070b8680c00b0445101c040740601400d401160006d044401604203442c80078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 595974559 1250 595973309 595973321
    0x6090603162003030a0b030712050f120702030c040f020c0d032027041b0c150e032a060708180d0c0f11030106091d0a0f14030705010906 60
    0xe40816014540c0c84a01e034480366101d82103110102c059429512400b0010010700603181c0039660600408101192108a608103540403d00580c0207100e901c02900703003d402c1003201000401f00307150400c00000941c60014905014400c181c0740091602c3c80c014106009000b550000c0a0a0054680420b0b625926400044c08540220060160040c440c01800c85d10701c100d03480c4c0c3c07002c440800121005c400c2c0070028100c500d08051320121382c944102c1c01e05900781c0d44c2482d42c0c402007000200c00405004040386018000f8000081c10000150b2014026551f4003840d60f424640000342d031403030758100c107900c460400762030441c808a5146080c400400740125004540040f40b00800145611032040001501070790040c4684414007001c0700713500c1d10110401074600585208203040d0024005031001d10903400104005d41000408114002c0c50807414855400c1c46c1d0941e03409403034403501040200704550105944490054a500110b0035198150700908801a1080d46040b91790400d1100a8000d6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 595975809 1250 595974559 595974601
    0x3002040602010e0c0612040b153007030803010b07050c13051803030606041809020a081c0e0306070c031b1b23130603150207060605030706020a030e06090603 69
    0x294000b0344c0110b050004a0103124010110f0700f0b200b1022034040364107416090740015070740150701d01084042c1c7c0412800010313420741426504810900e101d801c1c0c021645001401c0384100503026035891a100c43c002400103001d030301d0450f0400911002088810410b15503900300242a0008403d505a1048020030301202c0c0000d07131814150218039426004422070380300301002401c81c0d003401c2c1451458101240b0b080a80a10169610300c0312002d170b510301c10f00d0302c0244400001040d41e402c0d4010502c40c02c103180c1d00700c0d9051021640d8008400d82d0302060003540045246040f030b04a03c050705040340c0209072540d0224a64150b010101e0600005d02081110122040f110500b1950b41c1c0c01000c054500c0c000b500341d00a0032524140d101c619083c07801d0b64014050600200700c03282c503902c0c2d0000342201d5104105e140766001030407004114850007200d0080200710080c146440c034040010f911080031000040801400210035145541c80500303550766040058102d039241e240081160154900e90965 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 595977059 1250 595975809 595975813
    0x1109030705100f1d0d0c210b1303090f0603020c070b03070e0108180714030f071d0a140c0705060919080c030c01020f070c060206010302013002040602010e 68
    0x1000c105070400704041d030516541903451100726403d40c0c4088070304498001c0409480c0c40352008040c441d42e10a500e6a406900030607850b0345d520f1070b0950240401c1d681800c0003001540503010000072482c1c055000d03a00543d01c2c2d1000c50390000910f000c86100c40503800500b01180a80408511142d0583c050580001010200d0304030f035484600e00f0009020071a03509000941000c2d54024651141d040136400c1101048520010b81c4c00c3c140080c00c1c00f0040e00500307000b04000009807618035040240d9080d00c0328100203040c6190030080203c02000c00d038107035504074642100c0407520040785039000d2224074541241c0c109030350400c0c0380015000e51040c9400c6d1640d20552001c101d5800300816124803880e6141c82418100c1155a10030205421422600103d80410b000c0383d000100c00f800207108020004003003607a100d1140c64451300700d00c4240c1007002198010401440140d8000ba0f0b40303001c4000449400b0340002c000d07556a1052811007151000b00b900225000580c3c1e601508481c106440c1001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 595978309 1250 595977059 595977073
    0x906020c0a050714061206040b0310020309030a0306051207050d0f05010c0c030807030b0603070c0501020409051e010b030928141b0f10030203102412020a200f01110903 74
    0x420001c05d07020f052a148540382880020481c0c0c1d160a0340107100f20800a07003075030110083e141c18078003240c00440d0b8910040d000020f65030750755680752040074042e0101f115030400b000c00c2800c8959903030751a80159401140503180d800d0a0000b00c803000e4104a0380b2030000d000c50040c21100402e601d00b00081180840c032400c0c0820319150107401644160b01e80a404039040d40d450000407200c0c868201d0060302c965608100105003d83c0500810340b281c1c0c03107441803c120492960080c00c4c0604142d2102060340001c3c8240480c00d0340115450385400c00035080340b09002640543c2d44891101d5407402400b2240300d82c041044610085680780040050b15602c840052484092090700360000b05c42941c005020a95010461701a40c061034000241c00c0d403560540d511039040b44200070007030001c0403000d441c004100034440c0d404501c2a268040001042d170403c5803c280107003004001d080c0192850346079111400c6600010040c4e902500028402881401c690100443c1c883d032009001c5406401994 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 595979559 1250 595978309 595978349
    0x103181403070b180a03050a11071202030705060c060708100806070f0206010614031602011b050c070f0e061e04020a23030601120216020604140102010f0b030d030906020c0a0507 78
    0x648039445013241e01002c0c00c095a5643d070101c8040c0d0154449206002d0310f40800018200c0412009014000020b00740e48191028010503140c6601640200e1080404005d0002c0c2000c0104035190003c401e030502104940b030b2407844a0050141d90401d48092207140c04110a00d5480b4490445100c400c4d025912240d80301c43c0308072404040340e001c00d280450300700b012800501195441c011040350500c00050040b0625010fa080100d40c0012030002a001096407109040140031102c0100040060510410325143c41020740c4c58005001c0c5101315440c072136610700d0410042c01c0e103646010040c02103541750405c030303000f0b40030341c1150000034a0321071a000b0600240601908072800341d80c050f144d100001c01e1415a2401a510100304281001400d801d40342c0140c8501c40030b08058030601070303100a28070902d000207085401125110b00441c1c1050707600811902c1c0411211125411446e01044000c5079081180c00f80c8218921114184203200381d04c014440c010500301f098500d0000c203403151807850b07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 595980809 1250 595979559 595979581
    0x3060a2a230a0e030c0d0f1b0b0408010c052514011104140609060f0c0109021804060c0327020105070b0a020901020d030b03100504110d050f010b1e0103181403070b 72
    0x16082c1743e0000802007036500850241100241c0c21071013100d0058080450107802c480c81d1f8030030340c8041c6441c1d0010406000c00b12003800349403549112071034042d0030091940314081148442c040c3c41d49012003240180c005118034004941d80c80c152210082c0600c08000c0e0b9906000c0e44544500400310b20704800302082d5241c00e8048410000c0c0c020585418400b069000741d1150380040c10b1101a90342c1d40d03003840c2c0180c8803c070382c4038a0b0458a843d00c4405180c1070074a034081e140301e145403401301071400c8507004c08400c183c0c06650306070b4520780d4112540c01840c801aa0b5a12404401421108030700d07041080c000140d800074020f030442a400e03640b04000541041c1c0c16514003c0c4440e605422880300000e000c1c84650040754072a02500c00625004c440d00040f0303590700d40400065a09030052140c2ca80c41340d00c240102035001d0015074000e50380e2180c8103034520000320007215041c1015150300300c40c1608040009007a012039004500c02c0420308650a0142e0b4035030014804071400c9000c640051509403130 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 595982059 1250 595980809 595980823
    0x124060e12060402120a170a03141314070e1306150f0911071a010915030f06020f0910050a021605030d0e1210090203060a2a230a0e03 59
    0x1030322000b40441d454660030080000003140001050380b15000040300480c90b01d41700c503a800340018102c6070782c409860b0001410707110b0b0182421503800d484400d1100c04c8103005130510419410a041c0a90b08170b081701194240305499100c1c040d43c0c22508140f15000d141100007108840c800c803003c011501c4004400c203c025024460900311404011040141a07200c0d0094000c081c01c209289207030504a540f8402203003000314041240705070b40390060040711298031881440780303420540326651628669440c0b0b062101c0b4500102015000b2841038840c21649080d128035400041c545140c0e10035105005040380c001d0a000d01c014402d0500103074400348120800000d452018001d054214600c010584090304e0404680c1d42001e0100103005c4814018801c440380c0c00306505000c5240c0c4070500400d4507050002d410982c005245c2003003900392812030100c4c0244250508980305100384a0002038610319081800402c41c50418101e480c2000010b5000304290380850301c2d4400031702c1e0100241a51641 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 595983309 1250 595982059 595982089
    0xa180f030b0f0a0e070611030403080409051e061e041104300c05011803020406091d033105030303040614150303270a030303050103170315010804050124060e 69
    0x603406006c103500c80d90803002c420802d0000c8900e0181c0e6641c5e54066a80940e103d42906030303841c8207201a900456000d298042d2003000ea045d800e00306500018100b0204c01c0c4c0032001c00701d11030720070b4203952941c0e00181807800c803900d04035842d03da13a0b200030b103007002c0303044508416610290085070201e07406000300c040c0700e5082340d003010f5201d00380070064810880d40503098201c65180b5000000507a01c40c000d060141401303c10100d11034000ba040c0e403e002d2000300c404152500140300800300d0070100345800010b440495110010720b00c59002e601e4441301d103908002d0305400000100700c01d100791030308540001981e15a50021603a203c410341440030014084460780b5404c1080f6000d013500f1400c80d075003010034801c48880ca18802c1e990015104000c648e0044011a480701d0040061001c3c070f00040902146500340c4501d90300d88402c04d4a2030f031071500302550501810802207030502c80d0035844001400080880c02980500d1070000e40748a803554410200050441c401c0304400b4140b440010f0950f003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 595984559 1250 595983309 595983313
    0x607020703020405090102130306020429090603040c1502030702091e0a020a0e030a1101080c0f0418271e0c05090403020a0b01030c0302090f04080a180f030b0f0a0e 72
    0x3400c1d42d0810000e0200981048820364080c030403c6030703041c18400b541006601c1a1001a0780720301c0e112140c05041007200300c028401d445900d034003a1418510b4211054400103c41c682c1c2e407070741c40386007200b04482d1a401c0000c004141d0445264059000001000c100340216000612541c680c4140b49406110004400c101c078118000b26501410342c0d0054000c2600da0b081c600d084004101c003083c41c00d549403009882c1c010060310035420550f000042182c011500c41d040a02c0c2590500088129110300e1290702e8420103010f25850020200d903000aa0604440c140b449003c0c00c002c05003c00c00c00b215000340e0312112a42020580304440307001014070241d0188840000a24100400c8020803004209400394011004e5910000d00c990926601852240d898031041d1400c6006120440c20018065885030b01d101e0180408500f40310240c400f07a040510b0031091400010402d60306100b03c0341c2c4080d64103002c1c644080104590b002050744210707103845166034241e6540c0821000d56034050100c01d401e03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 595985809 1250 595984559 595984573
    0xa1b090e0c040507020f0a0b0a0606020f1f09080c03180f10140d0212010806071b06091401051e090304050d02010c06140703090201020d02010507050f090a080601080a050708060702 79
    0x242c1010740100707034446100c0c01968072024900c0e200c5820040c1f61902100c0480c0c1c1c09041041401003031041c4030281c980d5100034404609003031026982e900e01000d41000d07401501c40c45256a4503642c02003e15907078044030498a40c0a00c1681079682d4100c01c0008411019007219070b00c1d103080007840c0c01c0501000421081c40694044030550303032491a01d0110b084110200509072910700103000401804000c8210b030311041d07141030704880c1070040140c1642d0810204100b0642512002815541d82a400c031200142d043d903030707203403459900b002400406115401c00c010442c465110101d90114424002c409000c0f0782c0e6070001c0c283e00c82c880c60080302d0f070000c0200e5000000d5403040d00d1600d0140c0c0300d44000611880100c1e0300c0840c41d081200e513200003d440e803a6000031564103000f0004d2000f003e0000780940d007401075000e01139003d400c034166411800402c000c0026582d1070114002460442c003138030815611044811340300e0049074020f450710b00c104400006c540a000403d144641030a60140c54a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 595987059 1250 595985809 595985833
    0x40c11010b103504081b0d050304080f070c0303180e011a0c0a05030d0603020f09040302060106120f05010e010e0f0f04031b121110060f260a1b090e 65
    0x290140300c1c0d1280c103c114854442142424a40e078140d8040c1d070081c424241c841c1c228020000248246102143e46ca0300300071040c030384480c0c0086c20349401940c44000c05844603100d084913105405070000181001c0c000140000500d40c0010344c03543d40f92100d112218030300361585200082c8103c04c1c42210f500c58407050603030100840400161070000400c1c0141c407080501e40c1c1f035191a5412402003100080c3d61907108000f14900000920b000d124242c6201d49549415100a0740710b860520801c4140403070070461100040d10795100c00741e045494001000720396107540b24450044424055400d4110000e40425910400c4040d01d510410002069101d40c0e0344603034048a400d0003414880040c0d5109101342000a49060844101c5a0b41039890360050510004510314140a100800054520304241030041700300c130110840580b04d0940c40c1d06003000701d6500100610707800341c0b80e180850081140035410040418501c02c036044080160110032030b150702c034a80c04c035128901100b40c85c0e4401c1c021100c3c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 595988309 1250 595987059 595987097
    0x10e0910060801090c1b111305100e131b0b0406080912070507060e180106021c09061b050a060203011203031109010e090a090c090906050906010e180c040c11010b10 72
    0x2014822030190280c1d01407c00860030900751028680610b50700d442c20044902954000f580082c201001051000d082c24072039020f031011241405020040d180b5480002c12911200c104010840c44040e15515552003000070118081500e46510320f02a403030b820b81d00a01c00c03c0581d06440d8020025000c80703450030200782c540c411920030194020403c003000d118010b583e070000038020002034010781107004130700a6000f11040803140740c6e0b060007610481031101d0369004681d41c02d0030450001c080000e122504141e8605415174030003c0c41c07940008004240c6003e040c070101d170001d00c06e40b420f00181d1800b209106c8940902d034075045c0040d0821803008c910b880d05003480c603044604040006601405c0b51a44200c0c0d24041d08001d0b0b074141c07150b02d04820003859100f5503500c010302d0400f8102c81e5040181408091402074589819640702c1070201c00401010f02c8043d100200c0108100f200c10070300a0301801e00c1c440044a0800d651174039403009402e044c4910010b940c0c1c080c660760052076200c46030040c1d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 595989559 1250 595988309 595988357
    0xb010510021c0c06020f0a0e0d050622080a090302010206010824041109010b0301060e04090c0302010e031c0f0801060305070c02011b02190e22060b010e0910060801090c 74
    0x40100001c0401e4800420301d141700400746045902101581c0d4021418041c0040c0f8038085202d004200712402100442c3e400304106400070700981440e5400d0603052100700201100341009000d040303000071100d4182c0d400c92280002ca038401e03002d8451170307030f0b0352050315032144410311041e261101d000e800042d12070011072116034070030711a140c04c1c050448c0340d00200d00c4000090f08080d5030b906c000401480700d581c11184a00241204903818801200e40b5503e04400e81494803000f414800300320303600c0300702e640c3c240410004070a0404200041002d201002414604072000d0340c00402d42c524000b05465202e030246511800c942e8a820b8490754065004544403412544144c40d9031300c51034070040040c2d0303a00c04541c801e01d01c2c4078900400981040c141441640020f4000804151541090340003901210100c00066820840006401c044c500040c0d074070300800e4455a07070100740d1608100080958001803029204141d42d00b64107680c98203460000c6900c5260154003150fa8003200e140311000d503409503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 595990809 1250 595989559 595989613
    0x90610020c0d1505070801090513050a0204021e0d0614270c0d0213080c0d05060f060301110c16090507140d060803030c0a1205060901050f0a080303070c0b01051002 72
    0x242c0c1c02003000f6940c4001c0750000d403418030024210400400030070a85000d800c0d0010b840130b030300b0690003a040d41e656968607945140203004540100700c00d501d803040071803401c800e040f004a0710740c0c1e00d1240484ea0001000c2d00e000301c01070070b0318000c0f50014905000c43c1902d40802003404800000c014000c0c60004424000c00118090708200141000d948550000e080098a4015034082c0b0a0400580509180503c0801400780036000744c0b01c808600001815501305070300911981d03ea0303c8510100b4007501c001c1c2d02d0814101c0c4002080c0e0555480001e0b0303c400680700c0709066410356290f91a01c0c082e00c4d8140c0b0312000180c030807802c0e0230040c0000c000403c45450000ba00240072607032120070909540085844401014010800014644c0c01c14403000040e60f9448003000b40749404000108800d40601500e8001d1303a0090309029181c0304c41b0002005458024201c039286d1078103e500902ca080100800c5a01070800381c0006402e0414950401c0041c05d560050618405420409040c08200e0921 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 595992059 1250 595990809 595990823
    0x309010e07080a0203070e090706080c04050d110f0409110f040b0315041a0c070305072a090b0105070b0c210915091c0e0307030614010302090610020c0d 67
    0x8049540802041000700030500d80000d81070039082ca004250400c4240d9204c195000e41806c2003100088012418501b55030090600c5107040c0c40e041808401c0d070199030405904491020041401c2c0100d030049030960b40f908175a0000002d07805014003096400c4000001d0182001c29400180c03403030f1424641c0f042c2603000d000084c5601011f0002440d05540c4126030710615160710a01050084045503140c100c14004d03a40710113030800c0040300b0032a10071040042e0410001103084010002c441c00f9445002081c0c0d01e0403031404405917904180001d0501c104140c1034038000e40d429055000d14195901c9580011540d40c150380c60011300b1031140c1c010488020040d541800510b040034003c80500e000300d181c04000e00c0c1301400304460100c03601000c5d0217a1742c1544003510540718144079000c0402480210310301492584c41540100346003408540cc000c002c1c07418403628128014044d9002d604072402141d040449031a00010302c0341078903107150b2403401600308419000890508244002400380f040b48 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 595993309 1250 595992059 595992071
    0xb071d030601030f021c0c030803040201050d020d0e07050a06051e040f030803090106240311090607060f0c03090305070602070809060c0a030e0f210c0d050a03020d03050f0c030901 79
    0x40d0401d8000d8004070703200c1c1c80398001441903040c803406841040e000000204c400d01000c0d100c1c0c0c5003040c92071000800300e510000004003164458400da81c9c0d0b00030380381000d40d01da032a0004404068907411a040843c5d01c904080065540b03400c0c041841200d0b031607100d0b182b44c842000503042c1d0000c80000d5118620008000c00520100c081c02410029401502a03684174180b0306801030030f5507051b5101400c104517074a902c0c01c11080013110280009014140080c00c0121520540040e020b0b84401c0c41d03016401244807400e20880b40c01074442804070a40c10030020307050070b070b00350204c40100d20050b000400602240740011140c4d40289034007800348409600f003000100014240d540541039201058010307080c3c96041503000030810040c980116020f506d98452400812100c059210580c2c000e03c6580804109008091009008101c8007400300c1c0c01096460400e13641c2c5c1d80100741d0440051085a10a556142c0b10703104050294041540c00b81103500c40f10702d85420341d00b011300800c80755540c4003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 595994559 1250 595993309 595993367
    0xa0305060a120b0403030b03011a010804260408061b030415060f06030605030c0f10030b0406030b040302011b08090d0302070218010f080d08040503160f1b0906080a0b07 74
    0x5801082403500c100f004104918003464010191b81500003050300076030501003199401d8400d1480e500301c20000b803031f0014955480d428400d600280c115030429500c1b80013101559040d0103080104184c44d801000c54520340c840342d0031106c03180c0880b0600d0070806414800704000403480f03c9074a20140200402140840d00c1e030310800e1021100b5400b000100340d44440410580c00e00340010307150524115010340203080703e100881d580e138070b24800600030155500c08480059a0f641c0c845e2002c0c43d00240d154200340b40c1440c01030300030000d84141d20300c510a07014441003600c2c40342c100ba520900600c8040c020300b00c40107500760041d41102c40b00300e0340680003030101c102030824066030900030195078500000f010b144c6181e1f10306202c600e01d601030401c200c83c0200004940c000044892500c820710b941841449181400c2610f040540d0004116a008507500c8510901c01e840030015550a00d0042080350b0307480a05582d0303015401030060482c06894000703188140100280002d04600b521501c0d9a50b92030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 595995809 1250 595994559 595994579
    0x1021917041e0b25170103140a06020c0102070c050a060f031104150e15070f0803070e130c18060c2a081605012d030207140c12030f0a0305060a 63
    0x2200c400940c8221540364481c1030041e0140f81d86186624208071459514041307005c2104d980c140800380864200c0302c002e840c007000030409a8040c41d0002800c64461108109190103507111200c02d403507400041c48045590b02c0c080c00800c0c1114116142c140d004114904250f010386100b4402004180c41030000017801d85901e111299102125540c0280d2010310b901005a03440b141c0c0b0b800c403807035007041c03003a030000449074182c090405401002031900c0307590b44002140c0d542c84002900360014014003034038804c600540c200368240d0103e5203503030790f01104445001c904400320344211000500d0650b40310010510507010110034030000b10b50246580c001010600c800780e0298001d0101d58003004501c0b0341000c4400c2e52030050072091030310252411800449035032656000c1030071015112100305206041d8025170484d142241e00041980d0321000c0080319030b48038480506a28000c1c1617400100d90034060110854a91000103280d00b401d00c0c1d04a0070440c01803200411036900040c1a040200c1c0f40c02034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 595997059 1250 595995809 595995811
    0xb0405010506031524090909030a050906090f10121b0e041805062d0103020307061b0b01030803010303020105070e0105030a1a090c03070f02010209100e010c1401021917041e0b 77
    0x702d0708003940c2d202c6c0c020040c41084000203003894050740080c8249000e01c3d50050460380d00c6001110307955204d000d4800002c0c201155a85d000341d115403004501e690054118009076024420100d0802446c0341e01c82c3c4855200c0401d281c050300080360030300101c0079441c0c43e900101c981240d0b1900d80c07140d01d5a607903c1ca0f01d040f0064404081064504e250241905070344242c51094100c0d81403070100c19451070f808250781c2c1c440c6e40203d805101a407004050340344071801d02d20050750341141c1c001d0b103296500c0c248880144d0082c00150019401c000002d0b41c070900408801a0110069491914540c0c900c0442c5009216180c5500040f08580303c122505589818607207018002c503400003903403810200303030140260414050040079640140007116451342c5020006c0d562403d941820300c64070300c1e403c004071130072411b81100921824598822580c001d8056014010096280510b18030300d0001c08000d80e04108020b80c1072085000c1c0200040004038150521501c0e1a01c5076001034003d040c0d45e89540e9601c4d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 595998309 1250 595997059 595997119
    0x240d0b09010f0e01022502060d1d0d03020703110312060f01200d0e0a0b030705092805010306090207050a02060c0a082106090124090b0d0204090b04050105060315 71
    0x24010490401060b01c610706c0b01c41c4030119140b5050b102c50140c2c0132401d1805190f2044003126a01c00b4900e044054540b20b80000d80008000c0d00d5004400c4d41000e00250407262040d0700040301d004c48041d0480c4004201c41640200321700c492921780d25003081000000c924000d007030400242900b241c0c51101200808542c08141c070003d44020286d10300c00801c01079044c00414420b0140341020091801070b8411213800c4822450056030714130412002c12100340c8107450400b80004400c1001d015141582415010f45000b681d0501416070707a8070000061780a40c0e58050002d4003d841c10000514000008100308144102582e10b00e842c1c030780f9040c0c10364005209407007485011000e5811700100b44003102ea8070203400c940401c0c082d410400030000d2841c01841050390b03e1002e1204017407044c05003214000a002d60542d5036510425808104040c0d0014441c050119080680d004094038003400303140d0503200090600d508590300c3c7c062070900301040001240e00319811402d100d114502007007002c04211 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 595999559 1250 595998309 595998311
    0x3100c121e050601090605031801060509040602030403021006050604210615060905100c03030c0c020603070906033e0c0303040c05030c0f030d050d06090203010e240d0b09010f0e01 79
    0x2031030914001d825610000d03c068104001e4500912455400209483d04044103081d006003036075022020900600b40d9410541e4011440b40820041111a03002144603621075030942d45401d5105c4401c00a0b103084d80100ea52280d030611050044480303418259000c61340803c2d0041e040400c949130941142d4101041152080d040141444501d4000701d046006200c1620744aa0125074000002c1c4035400d080402000c2580320786a000b41a8404c0300c00c1810b10b81c0081c8100d5503414641070182c249600c901c52000840d00b890b4140000c280002d204100c0404c000a240e059503444c0a82c2c0001c0c00f403260b9462803450301c00c5c0308410200380104040c601c5248101110a00b02d03040030100751070480000c24562056402c1d50b5a4051920086015084000c0c80d0420350340300c03240c1d1003980300031b0002e5800c054112072010000040140b1010324040c0074000700d05074058010105501c080e01d044d41c907403459400c41c110f000c00b4400035101d03008940e4403440d62000019035880d008450000d070b070043c254280e926 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 596000809 1250 595999559 595999601
    0x1508070302030d0f05040b0a030f1e060602031e031902040b0a03050c1c0b0d1a040210080115140408010e0a1103031c020918010803070308070503010503100c12 70
    0x10308040250301d50b02c0c100d40c00c15010325600444003c0062140340650300d1f180780f0116150048070300a030011107a08254050a0004140301c081d0200c080000180c10b4200500f0000700140d054004011540c812407140c0c1c20140e03075854501c00c1c401660000c0c0030700302c02c101901003140d503480152000c0c002407c1e0359021959214146d800040545401030a04500c0d0380040010a0f0902000008444011a44080441c1d54444000019488070302000c02130501d001541e0400002441c02c3d00c1c40303105901c21a20940c0200b900c40d0f0440e840ca01c00d0068407440e96000e0004075007517000b0007901c8901184840d010f454962581c0e1118290740fa40010400c00d50301191a20042180c000404a55054298019800c000c0c61140f40740302010250840f4a19940c0004e805440d40c81c0c034030402c400c801d0002c25642141d42d4036000b05980343c0c4421425800100b0000c0400d90042c0704008aa0484100500400c4010780c0018400010005034000c070703050002d440724080c140d6090307004501010003041010044 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 596002059 1250 596000809 596000813
    0x5040303030b0a060e0915190504050f04020a030b0c04030f03050a0206090321150a03050f010b0306040f03121e0e100b091b1204120e030c010e0d0615080703 69
    0xb55030140381c90310b1088264600c103006455200b03501e21004002102e04014603202c0c00c0940c03240c2e01c504502d04e031b0803c048080c00d140080c0d01c180030f0f100b290b13000d40e030420050b507030940054041c66003602c0c02540710404500400108602c14040c64001007400401458243c2c1d9580b0080c207041070b400b0840c041407020400840f00b6406014480e4081032010203185003201d440b0030032680248858a00f8100c01c000c1780816014042c945260010313007405408181c00c40c2c1c803810130381d03a6003004941e040f40329801c001e00c0300818240868500d00440d80a103000742d0b504015a4151500307551012043c0e0041c1d81c1c2d072024079403c40244490446801c4c00040020710441d1200306070b00b00310140c14480c02d042c2c100140c4440c4c6da1944950950f0120a10b10042107220300710300845900e00c00c188010310101051414841407040260000703460703d5050b16a141181b440b40103054440320140560390100e509684a800740c3c2c2458091400b0140c4200300001e2000040440407014a0498000344030b103500124090003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 596003309 1250 596002059 596002061
    0x31e05041e03030314060a0612020408030a050c0d030e030901030906141510112d2d1c080915010e04060c110d0e010c021804051b010c060207031803030504030303 71
    0xa503400c01d40005e80e01c14644903000c180003019621455041000382e080754040920b295054602514004055950f200c181c200014295000500b00d648207000d0285a54034a038007910030b103018000c07400003850070108030740c00540c0101540da0068844070740f90744400a41011031000288101452442c40c0c040341301090500140030101d69903101400160402c142c50303200b001074107401c400101034269111401440084064078107034070016945114a500308101a4191540c00c85103825203245240442681c0c040036a039041050300c505900d2800c60300300e40003148941900e07a80319081400311100103a00c0d9207180c80740e1809170700070300c1d4000101c001e010421455001d07030007900744c0a01e804c003064010501c00a4681c06080c42c24400e010850a4010b1584d0141400007641e54000f40f000c0c41a0510300031210056000711411038803405816a0512004150690b0110460069507650102c80d0984d60700d0b0000d52180c58103406000303911a801300e03a10b00e0070040d100a58400d40e20140c0b110b156142c054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 596004559 1250 596003309 596003321
    0xe0d18060e04110706091e030507110604050603180c040207120c1113020d050c04033504080c01140421060609051305010c0305060108070c171317010504031e05041e030303 75
    0x695a11003a147c10340440d50040135250307019000300d00214048030040008100340f00700d03401142c0064006c400c11031802540d50f000c02c0340f96407920586403003000e240d041000302d10a442c8028401c5c0300992a0300401441801143c45283c8200d554044010340c140004000366050308411000e0364000584045c06a020300406070001c801c4002c403801c0c141142d4503800d03141200e1900030a050161140c00e0b441c44214401256448400d4598590303890f100d00085881c0c07041424030700d01054040111781c500d03240309012070302140c40712001d13904941070006060042840c010001c0d21002d03290103002c1031854291085900a840c41010108010381c86d00c0e0480c00d40e40a62900380515144c04100300c040d0341c00502690340140d00e40b40988102c4824174180103843e8100c425000100740200b00034110080035904030043e9442e185404400d1500811a142030b01c508403402000140c80c0c2a60304002e4101201000184240d4201903044c203440c2c00711240c120607409074900302404010340c00c005040e0944101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 596005809 1250 596004559 596004593
    0xf13051c0324030b19090309240e0402090f150901110a120c0f0c0311150309100207141501090e0309030c120106050d060e0d18060e0411070609 63
    0x501030100004481600d411148000390010102000060305d000358520b0350307440a60080000c100072022130500810300b141a0041e001d80c40042005144200074681b81c0980a00f1507650341d00c20031905406100c080d400c40c2000740d0b0011211108295030b0b82d00d1035001c4004404d2040c0361503c5802141c00140f04a030100c601c84629080700c0d60030400305542084042e01c0603910306090b080314105290a580c0320b02c0003c400741090f68030820220811440500320f8072440c10441c0d0700c420304070b4240d013018468803040d195481c2d80c3c0e000240b03403900490070781c0250005900a8010520300042c004a0394101020903070b5059242d0303030040c018000642c9520600a600e20134000031414030b0030140c08299a65100c03c199480740754210181c000c2441d0940100001e860054451102c11400e4640a40900300c2c83c400510705000c1da810f1050640e100740d211900010700041384203401d40c5040b1054941c004441c02542d04180c4175102c00314000c14450003001d45034815000003034103031042e080c00e400c00f0808800c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 596007059 1250 596005809 596005841
    0x21503101d0601050703050d020310030b0702030c1f0615180630020415020c12060603060115030b040e100b03160b0c0f0d02160b0a05030f13051c03 65
    0x226144410421820b500001c203081c8903907618503a0905541350300440070580140e40c00042001403e200c07038941401101d120380a041e0040e200c0450998a0340100c400058455000c107105001c9014030700c3e0403000040030041f0021f0b44c2926008034124501c910007140c000305503410040402a00c11000c6140109024503040d441483d800725116070000c0d24800000c08070260711a00020b65032181e04440c0101021052180e81944104020b5107030180c6120701881b4a422031440e01e040307507011072a58800c2d00000d0291200f41c0c00c01c00ca0401c58881001c00134200760380c48405a40d00e03201e600c9140006c036003c6c0c004181c0c941c00e10700d0301e5040da4500e034516070190b044401004096902e420070041607400f0a05280e8980e084050030a2800410200c0303c01d0501c9800ca184442c0c58010450200403200c58090030340765902c0344d050700e0b0288960200a00010401c000080d048600c1e0003090707800000d94000c4c4100300d145a00c40368940300b4210151081c00f503459521000c01c681500c150311480c544108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 596008309 1250 596007059 596007089
    0x20309210a0e040e1c0c0201080907060c02060a0306030f0c08060711061305191407080a0b04030e010c021f09050103180b072006040623060411040302150310 69
    0x2001881c0da54180d0b402ea001c0e50700c81c1810194401d040c080c600049000580601c1008000c150007004298101030613400724000c40085900c4060100e50282968000c3d1614010803040e5030030311581e0f0344061070031703001c040da614004800a40980b00520013140241e41080d4018280740c3c110707060690140ca818103128190a0740481c00384e003c191258840703030000b070702429442c490514904061000c06242c0e0504600d00341c503000c1061a04441800d070f15044102c0318915114040150340d80c041c13840141414101000140000f0302c946180e032440a410700d409502c82d000c0d940496811007400b00046850852070704000092a0300481c0d0300001c200902c0e0030f000e5200340c1e810022084891001c0580b040b88000005940c190017020900c81d0349c28410f081e0303005a15240c0000d61107040c1a80c0482c1c2c3c15041c444d00c04484052856140d110586640307003d041030b00e44008000040c07100000150441c44107000000c0075a50743c844848205035005030565803490044004071400e141c507004414080c400d58 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 596009559 1250 596008309 596008327
    0xc11010e09010b090103150b1305120c0906040b03031603180f032306070e031606120c020106050d03020105040b010806040308010b1318091205090f0103090602090402030921 76
    0x981c41d035044400d940c02d1681d455148500482c064031004150003015060040700143c1c0d51000c078028003480060790f2043d1016a03d490810070398500c541003268a682c40b0310200c009234907004079041d4004000400000d000f00300f217804207045801407011600c6011000c42058141600030001d071240e14034241031001d1550414101c400c452285000140034444a00700c205074115803640e4403070102201d682254076601d021b510080c00b41c02021300803802800382d40040c1c540c070b200c2d040b204003d070b038001c0d240c4006a840220014004101107442d2004541d260706000030551900440c640034240603a0010904d440d1600b05520311a40607400303c0010340c000000c00c00803070351001c00c040c10f5134080c4080c1c41d654410168141c030300d00d040e44c01c0001c041c042d410511a10000c541c5c0540c10a5110300103100c0c0760f03050b00009407040d02807543c100b42c200076030603c418415031296000c4500244100c900605040b48035003c10200e801c110f072540d009a1010400d12060444000c45c81840308040c1c015621f040f000d9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 596010809 1250 596009559 596009569
    0x406080f0312040804330503150f04090605100e150d120306210302060709060f2a051f021c05070215100504200304080a05040806070c11010e 62
    0x80d05400b1203000020b000320b020050710000311001412002200d81e919070040c0c1482000c01d01441c014000d00c8881081403208a0241003500c0c469071203c5144203200e428201400803151400030080d600c070f5540d10701100051024480d0a024410900f0300c0c001036814000c89a02540e00074100d0241c017007091040c610b2a40e541c280110504e070f403000ba014200e410004007078010385803e41204120b1100c180d41c203203944076140441c402d55802542101c201c0e480c0c0d260140d40151640c00740d4800180c5103a8a446018094050112341010702101019501c0400350a401c8049000c80112129002a0340c154001448104a80c95007295030000310324004480d81e4180b92001e9001c803050410381c0311000902c9007030091100d16018406441d4a064a1038078280c0c10390014842d0003110710941c0b034441361401c1c038601c2c0c513000900c1c0c034491940e0624544a640b114110354101005d181c3c100b18040001044d800814004140104003503242c040c1300208034a801c020345045002110b04108140310b403450140c0c0c40c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 596012059 1250 596010809 596010817
    0x2903070317070f060203010e10091802220905160f1d0c0d050915011418150a0b0a080a090f030f030f02040e180105010e0a0c0c06090f020406080f03 65
    0x19406005a56a08a1800301940740343c0b2240680650f1002c000082d080b036499141c28800c55040b0310b81070160340c80700300150407200808001d620207210030040c1001070402080c40944071700b00186030a1b000c12181d40c07103816501580c0048810b0707000700c0a4548070b4820b000103040501200110301c880203040514100e501e4581c000408460654040031681d2006000c08540c0c800d02010401d0120307182403160581d860071001d102d84003da416070000030300b1070303028a07000d501914003c1a00690441c01c1080b051100e0018140c0c0d15480c030360550811050f030b0b07000030580c01800c1c08481e0544840382c0c4d034806000d260b0001c02d42d459003810400318000061003a142000c00a03414201041c0402d44081c0850003000341590340306000340700140c04141035a0b40600141705400440c81007a1000d040021507003650009e100741041642c2d1500030520901040e009101034010520302142541807648500064800030242030781c01d840010208010f600b082e0103040090407011004152803401503580940d40d00c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 596013309 1250 596012059 596012093
    0x90906080712031d0904030815011b0809030f060f0403080a0209100507060f0f0e071e0e070c0512040501030e0c060f0a090f0801020a0216060f05090d0629030703 71
    0x109142c01c400070302d04075040648013401c000d0114442494517190190000c0d4081e07501400e400c038410007002c100d44c4035148070038a00c080303981c0007103000041e9540d44850750445104103a060058600d04854071108100da1845031059421a1085046c142006008403070013801c2004601c0c010400715005440d9050a2620b22036589040c4c0e50712044c605010380200b00c40b084c03d103481400d02140b81000d1500e904240d01c1030005005903903805a840803520f100040b8034080c0018044400e0040181d0090088800d612041d281031900c00c1d14050740e03601c3d0420b03803d848481181703030340484c050119590601c2404084010440123024029000300000c0c43c41c0100101da40642100180380ba05c0c003485407094400030021100c0d184e810f1611803450074081d40050007400c00501c80e400410b90701480b903440c2e040880e462900c2d14907044505c91801c03503080d40840001c41d00032440c400d4410000b0010b00c5183d544584015828145400109072350070601e051140f10381c8290320a24051021034000030100030b17501 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 596014559 1250 596013309 596013317
    0x90f01030201020309093417040b180312160f020a0515060102030f040e1506040f06050a0c15060f051806040e011805030301030201080a050405061b04051009090608071203 75
    0x1688100004100b24900e401000101f918080c86070510701a102e400525000d4a449082c03917510940c1d44e03078030300c070300c1c112006800140e5110114403d4003d0803c02c006082c8200c0a481c0740120700728412203614402c0d6008102d141c0c20307007034a240c0d407070340940960075030080c1d8405420b5082c119116940e460402850885000c90a44085501caa000300100e52403031020404e010344030f0350b54070407040340c400c4116500b0400c940308407603100c03403890300b041180e0985e155080c660360118240001110340360000c4521f079050141d054401008101a20055a50500306e410040350450404c403d0300c490005503030085008603840115000c2c1c10203140040746c0d1090303040e035001600c4100d484207503001d003606200c03050310f100105410340188507001c4011410f0300c3c000e80b22240e04e03071948913055003200c10849014290307801c56004030794002d500910624071050303248813003401c0544400024020005c06c0b0402030225898800401a28042c0c1c0188002400b840002d02000c0d071503c81072a500310044030b8010208 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 596015809 1250 596014559 596014561
    0x70e0106080628090e060f01031a060301020f040305060a2a030e03070b0711300901030603080c330408220e0106110703052505130506090f0103020102030909 69
    0x140d01c01c442c0014210700c0515420f0145542d421000c0e00402c1c41442c26000d03806124000b6494030340c241c44490403203510901d40140202d040b503018080303040180449605540030000001c0d1a6010700140010750b0040001e408603017040785900c0c00310b4a0000900155211518245141841ca03903001075070b0880c2e41c200418490030b00304440b070030f500c45e07038038010100c4501e407050000950744a441524021541021103076003070701029034241d51009807240c10b105025506d4070b904520725094050240060107040c0426000d4503551110355580100d040c10095501099860307444140003a20003030101c200d9142c000d001412580c1011380000002e00c09451841c0c002914043d50300031090040380c802540c07030b0302c4d264540c441d071b09203112003002e115400000380d00840506801501140200440e94024000c01d4401410503440d88541d0b41c602107008020500302c4d0018040e1104040282000d15031034000030203146c4182084004000501a0090448484c00600043c2d03000011a08400411142e084007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 596017059 1250 596015809 596015839
    0xe101b080c030a021803030a0c1a010e0103200d051c030b030d080403050706050106031e05250e09040b012c310b2a0418020403050703030503010503070e01060806 71
    0x117840000074164140c807000450f100040e031300400301098507108811412031055894966410800f0a02402c0710400414004000081341803091079928080c00000720004018100010502846003400f41d41c00c0e0090090815030360743d036000ca032140c1e40d6242001c000b6040e101001c00e0703484407051410814050500041014503000f01e05440710310350b100d1002d1100d503844440c01006842c002d8103152000c00c042d0b00070405a40c40f03005040c0314115242800b19800000003502c0603255000403194107010021220784801d4950f906158412801908c01d514154900310b06010185107246a4003404100c0640c0f00300c4000e0040310303140e0440e055814100c0040a13a150015484d44646500e005442070744140380300704000300281c644180c1e038410948941100314007040086868901451714440740030841804035016500c080b00c0c0c40030002c040141019160350302c0c0761070305840d42c04c1a00461804001085140382c03c0102c07001600c5103211240d41541352000c050b01510001c4c1c0310321700c120b207d03d040300c074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 596018309 1250 596017059 596017087
    0x903010b06040308070b0106050c0a0f03091a04171f05070e101d0a0510050d0f060e160f1407170a120608010b01090303120e101b080c030a02 62
    0x500340c14010852a0750340c0d0390f0f01d81540c01d42c0c003001d400c682042c11003000058240c05403065a4030900104054640100030b80e4400143e01c0b00310034210180035a9100c041b400000c004c4031111611110001c00d17940c6c0741000072034540d00951818070a0f059200c3c01300030642c0c00d04103404440d00704a042c004109612641e8050b9209815500383c1900801c220180410071944090b442d401c8000000c2c041d40c11040800c107010800b1404e000e1704e0381040c2415a504a00f922941c0241080d01308010700040d1400c200204006580c05a40910b44111482c4c05001c1c1d8600b10070700c0c0318448030140c01c00071800d05440e100504007806040c80320010705004a10f010030301c01059803111300b2503c1c00c1410343c0c1c0d8061080010304155111081c0a03c054503000b400329070300306c0502c1260b400f60343c16110590300d549140c0d0f04130b651411025030011400e0702c402000502150030031280390f80703180d04400410746507a500092308600711000e200000300328030380e410720580a0000046036081460240c0140e91504a622181 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 596019559 1250 596018309 596018321
    0x807030209042a08090c011103070f0b0402090a021c050c07060e010606030e01061206050613060e0f0a05100515090303040b0c060f04080d15080d0327080f090301 71
    0x207800508082d908009001a0040d0300304081c000c01c0c3c01081c1d000000012691000304403a005e003258032656420803030f0341c01a032019000030308210849140c4010342c4e4410075110048002203911008050a0208504c1c160b081c1c0d5512440d00bd1046003042c02c20410f001e010101c103694951110740c1c400106010700a40300840f941142c20580c180414180708074028020955441b5200009190041d0800d0982041c011441251900c29001141c8000c40d00c9441c0180310140901e54406180701c42e04040c440d080c0104402090940314500d0545414100510000c40081012034401e10300000c0049004407031201c00143e50050760b681d42c08200b054100d5006100c2c441c000c5034148808900000d84000c90b400800c1000c04180584605446044101c80d02c4030040e20002c050348800d00a55020f800c4940c00040b00c1c66036070300e0351001c0b0350340c3d07040e89824008098404000070307031560013050030402c0410510904c800c0300c0a0042015a5a4540c281b950080300d203503c0c1c4080f0001803031082641d00350044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 596020809 1250 596019559 596019577
    0xb0304050703060923070f0b0c03030a0b0103060e0703091a0f182517030a0f08060d020901031103010b0121021305060c0a1703040c0e09250501021204050105070308070302 75
    0x2441703120311511051381c0d0501d51240a020801d20000460714a948805480e182034108004500303607100d01c440b034806803100003a43c0c0c0c1010703520700001a00c102c1c01c10303519014402a45000070790554034142030710004949010060900001000c0c8030318a181440910380c0709800325031640000c544440c0c16810020031281d030280503140490204804602072404808448802156045002d4500c00d03560b12802140c9035100071450009406c50b1150080c0001c6500600007420351030080090b6000910b070400a030019034100e481c0e0201135205040920800840c2502400c24660768926002d06c03030114840480200201d680200700c07001c9044400c940d410241c44024030544e00c60007540303200b55489500040944601d100500c051880c202035004503401150881800030b403650515951404030400034003030300c100d40b182010602c0c0320050220b52100841c15198940c40c0d6130b1524000a1900c5010000b10203131001c10042000140e8105040300c502940c981056001561080d1084d0000c0c0920480 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 596022059 1250 596020809 596020853
    0x8090d030216090e0f01050c0a0f020a080f03040204140108031603030207330209030c040c020307061406120c0d0f0215040f03140d021218060c010507090b03040507030609 75
    0x102c2e0114040d080050002d131280c04a41031540030b011420700740c4034141c0304030303a105904000c0865a184962451140e07010a0700480b2640c4c182a558040c065002c0081c00c0100b0501005100862515000c4e0b11040000e20034400015410302c1c010549903c1803650010122a100b03420504242c081d405803660103800401d0048a540324103600f00a001d42d80c2000b0340402901e54500064448074801d407841030001400800300c6168490500000b0815200c040302544420700880000581d540221740aa4091812001c824200b140c04d10943c5402e03000c0c28034807a04611401403054407115a841c05268105c43c4a58041607180081409035a408507140900319000402140320310006402e441220320030403856440d444030000441d00c41181d40c400300300580044022806844c2884064005030a0b0410720038601a070351000039140b9032100e042e4103a142d44038000c0110580d00142c02000034440d10115504e0761803e03035101c0f030b21a201d0b03020080c200b07540e510030101844201250003540c000743d121 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 596023309 1250 596022059 596022103
    0xe03070803010939140a030605120a0506040204020f271c11010c050102040b1c05010506070c0306110403060c08090f120703080612010c05030a0c05040308090d0302 72
    0xc09601641c024000c1c410303507504011200003459650b81500d1562980e0002c4403041e454401c401d42945450100e401081150744031814078050708160080c009003910b92030001d9098a08000d0250112440c00090300d00e4005485410104001003121035006034111001690b4a46020b5002c0c824010302c0d400d9201e152604402244c0c02200b51410b02103404c5c203e6041c01d500081e0070f0605e00c2514a0100200240042401d030f91481d4000c12106500350310030030025040586841455129800000c141c7c00c0c070783c94034440056044070310b00c0ba2a01512068902a207800c0240c0c41d0b04070000c1e0a03100050116030784140782454800142c003514080c56120100b0b2002040e0b0210040c2180015207000207580903003030003a10030b11b8001031800c21003d00900d0190410051762029589003200406040d00702e8152903004202620a1040074411103c94503000e4a03400e202c100401140c41355000c40f014000c1c00c100074030100710315100390b41c40d0790780231180d00d4581c04c15803030102e04100110742ca40c10128501a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 596024559 1250 596023309 596023313
    0x90923011203091e06030c090e27011b0507030c0606060302120f06090a020702040905030703020d0f050f04050d1506090605100302034c140f03060115030e0307 70
    0x1c24407500c1c6030003503440304952622000c640028000981002c034501480200402117240680c002c52860b202504100800706c1d40c542200f60501801c0743c5075891024045403001c00700411010000c04041c03034500802151448020f8401c000800303040d480240304021a41c5010180314091106802c0c1c0d000d0000e03c12203079180809000b0350071110b081d001c4540380030001000f1300c4040048911404000740402501d840ea001c00900030347c05100c00b40c2e001a16000400d006c00c108000800e4118404d07402030030015080800105000124460f01d01048030410121900c000c008007643c0664204542500c4d0703002140c40d00300c1c4d183c500c055100b014517080c0100002d030b1128941c00f00f411501c068421302038001e0003800c00c504030701c811605182c84d0a2240c1810040800c01414042900310a504a80c1d040d07140c100103a1201c8030701c000905810490340f100780a08101400d0800c060700c02901c007a040a0a0318000a0300d035801402303100042801010080c2e03d240c405d402141c80002410141c80e5100524 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 596025809 1250 596024559 596024579
    0xd030203040c32030f01060b0306030d020607210e0f010b0906030c0d06050c09090c04051011210d11270607030302180a08010c09090c09092301 63
    0x1180c054a84200b500382c000303062110414038030340e40510a8141c9800110304200c0c44452640350803255054807483c01c034240c04003024440c030b4000d040641c07000c507142e14003a0201351424140480c0b2504540141f400d0000741c42e00700508a02c06070851070008802000300010f5070080014610294a501c2510700002403c0c0040d40030410914003074500381541c0d83e030782040c1039540c4864401c40e40c000e251001d40c0c0010030160307030120390000fa850040900e00f450240000ea00c420013941c140f20203a4000a01f00004e103092501120107030b00303d00b00099200c0b040c010094440f82165450300c002c50b460280945003034181422141c2c140e0310580104101481050081c000390042c03007a000c07800b854200c0941c8041e12590b544000e22070010b10a900d0302800740d0b812006904100c0e00c070100c000e81050030711030310b47d80d40e0384400c041d010303001c000100e040c052103000b480805594820030400e454008080c5da0035611032102e00c113441420202107a08102038016000c040340b086103078140704906c000041200055 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 596027059 1250 596025809 596025811
    0x60503060415060219320723010e01020a02060a02010204080f03031005100c0f2009090c01032a0f0906090501080f0618180d02060108060705090a080d030203 69
    0x1540c04100200c0c2c08010300c0450311450203540056842228110645d01075000301100040c444c0b5440180e820061400d10030281d08802c802c00c0d103406014443d00c11740000c02c0420001c06402000c601c1c0d080e01100301818082c040858681004200460007050382d00030070000c0e21040c1e014080035519803131244028001e400600500005025031000940354900000c196401244a0342801403c14034250030090541c00c0f100080701440040a0f0900c04908a1002003078404e0080100c5000c00c10010785810f280c10281c1c01d150b00c91722505040c811808000211203c01034400c0c04c0c00103840075100f90b00342080641525200740d009138036018545c142da101c410310384031072801d03200c2880447e12170509894001e9940515800504030700001020108503840041d0800c2d03016100181e000c4c1c0c210070301d070b0440d0b0040f2555015102c0e14400204062810450846115440d01c00f52100754101068a905c0c1d01018020300d041200124a030045580c0d4800354000802c841000c403105405814009000717508 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 596028309 1250 596027059 596027071
    0xe030a05070321180b210a0c03050901022106060715060e0708090a06020313062a0905030601151b0506060f01030203070f0c11030703082d0403080a0203090a060503 72
    0x1c0c2c1103c14450034040c01003642408285144905500d085c15220107485d0003030103249076190703940381c1164010b0078000c110301c3c05010092408951a0300500010301902c8025011003020380c41048a0b90300c00381501504031810310381e21140d24403a203800000070b203203010f4404040c00301070f1080c1e11070b005042c00d5485503044650302e918042e11036407114015101c1000803107007440190000941680000c001e03500940d40940c041c5da080104121607110402141c1e88445008507031091601c440620846020401548144500e042001c09041070702080d2500010f100d090034400d60107000c4410341e4080c6404c5460010860442e160003049420480d5440500780d58480c0207581c0036402c040d4651190003141d1190b000c0e80c4801c2d00d1110700020889030b4014000c0180d0700866403030071a41e182e550500c20100254055840503455206800943d0300311600070f08900d00e2011600390125202c1c00a1091300e08072600903103865165200001c0590861040031000ea03405016504003292594019000e540109 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 596029559 1250 596028309 596028353
    0x1b050d060f242102090a05060307172b020c060d020d2d020702060a08060109091b020708070501080103020d11090f0a0b010206041707150204080601170102030402100e030a050703 78
    0x71107654000d602c1014115000703034110340000001611b14049800440d0450409021030f0f000681e102c1e84020a80d50044249020b604001c10f90250441013034001030300b590142011640d40310400300003a42e40c3d044e044401d07000e40342c04140c3c803510140c0f07507054415500b1040414003a038a180802c1108011484946503806104001400d0b0580d4440c401e45640d0350740581542d1401c4070450040d01c03074103001490903040003d103880102d21550036000e1141791080e000703844414a071078094040c0c1031100ca5000000f0b10f41c440d110410050703900455aa0440350180c480320300300300303031170401010070708650108581055000c014070080001405145205144c0d000c0200404a910801241c4440042ea806000b582003040b5600e0824105002443c165220b4242c564220124000c500c041c0d80196214130803640210004000111382c07240c3c1c280783c08a01c14021491481d0503030005030b100d0034214600d401c10104d02c0f0340e0211031b202044003201d4141c110040740c03c800d43d2440c101e0820160540d240c03d0300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 596030809 1250 596029559 596029589
    0xc1b14031203070c0807060b130b0414061e01141309111614011508011a0a0803030c030411030f100b040b0901050f0d120206041b050d060f24 62
    0x100c03941c2007900d00039009960b03150003000c0b441d01c4080d6607801044003605c000c0e517190103035645556401583d00c848070382d1050114850307800d90304100850380300b00304c1c070010700c486d40b01081500d65944490444e442a0f008070110f800c0701240040320081c1c0c056403204004040006e44191001d00c0310400340494010500c144000449194560014060180784480070302040c14510005880341c902100409419000050b1910459100c40d034089242d51020003640d5541503610103c60440796080301065098960752020743c40c0003080c41d928840180380c0048078101001080402c04040c0d02d07103100e00001030403910f802113100c0e0300e540c44112083c0c90900041c83c01e0341612460402e80652a0040d400602180c402c0c1e01c0c00301800301031110805203a03403100039021183d002a075001d00d04039038503d040e07006048078a014600b5940d10010700c03200c0082900c19510401040d61090340100d0010362064010582c41813440400d0007401810005004113400600300b1b11007030340c0c240b10200846103400c44602117 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 596032059 1250 596030809 596030833
    0x9060405010510240203090a0902040f12121809020a170105010e06070b18010e1e01050417130b031518131b0e07032901050a0c1b1403 59
    0x5404014801d4004000385500c1c0f5110480b280b442c031500f0300f404d900543e80b0b058102000034441c0a00e580080406503404901800392461819140c000b401515165010a5400c0d4030b551902000da43d044804010034210724500d4103004448050050803c0da1055456101603140607048405075030500612075050070000440c0e622070000c1c003c0700000501042e151080c6611003242d1580c000340700c500b0075151003400e4420711801f44545900301c00514090400d10800b504c009825041c1400351624aa041c6414000071a120045044000100c00d0f1810b55070302d4501401040b510070355104803081c2002004100c1480451403080c014078004031014800078480c40d01c100034442041d160020b41d13807502581103000620300d05071001100100b000800c0015581d59564003008012035174803000070384031003005151081c0c4444840403a102040004241c8843c0030008103117001c0c040c880c40401c00d851300101c06001030783e454060100f190b4200803050540362414a050000c0d07046400f40a031140c5080c24907 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 596033309 1250 596032059 596032081
    0x60608060a06120b0118030b06010912050706030504020d0203070608151806040c140307030209041802150a1209140d050c10110c0303040f05070b070201140706090506090604050105 79
    0xc2d12801d4940c00b0050000c94040360052200ea560f09051101c07180501c001a100e0281440045206080b060302502c1c01000051a081c0d8562008040b4040024088000340e00440e4010030385504d881c00003080e5940e40005402540060700103905401b031994081259940010800d2260300c0c51000c5403207600030001401130003124660101d0b640000744011a03028903003a01321103502400c40c607244064800c48140151076503c2600c2c03080c0402d5001803013403414202030241c0c100b2a5801050101d20035002d030045405015185040e56201c01d0000d08034110600515100550700900c0100b084441c545151950001206000c94140703840390b4041c141e88588030768101d8010001038400b4043c200c805e504030030080c141444040c2996a800c0c480c908519500700040d61041e13024010040f10042c42d070400c281000700c1a04001c200c43d03010000d00001d40d80120311120511026040d80307a9402c001c0c14810005c2041480c02031240c000c0d00c0a00c00c040780001244c6000c0c0b802a8020001c6445068402ca = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 596034559 1250 596033309 596033329
    0x2030a020312090309090717100501050a030b150f041403240402180f180102040605070b1803160b2d09070f0b04090509010b210a060f06060806 63
    0x200103900401c40b0440306164070005580040105007102d060440c0c103400134616480860f203141c0054100703420300500c21011000f45821010146070384200724203160000b0810b12030a80410300341500c80c0407144c140d8031070f036030f014455460440ba641d0b100c0800b5070310100340d40c0c014881c16505c180070210850007072401062800a1110100b040000801942000c9054110091040c3e9108414965526400000340500b0384a84c0211210483d280380c0350603060140c582c4540b0700d603c181e10501c001c1c040c0a0304141203450303c0c1d40216480100d6a51082800d00307101780710100c0c0100b40404540d40707800081c1d400343c0d40401e0b88611844000b45c2d441084580b108090b0700107000b681910002024004480c0100a64000d402c0c1c6090341c07849a152070038500240e045600904050301c0c0041c040182c10041e10425801110030002030021180d241c1c0007500d07120480900010840c0343c5080c0c000c0705c0704104a09600c80b40e0004051224642c1200c01c0c900400340c43c421180824440d5000920914004601d8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 596035809 1250 596034559 596034577
    0x504110c1213210f14100509062e0803130905060109032003120c0708030f09011b051009020a0501110a0b0907030807060e0d09080a080d230a0c0203 65
    0x840a0a8500000d2041e1443c05803001240400011586004600ca1501d004440da015800c449800114410b0300791501d04400140d1030350a107400203000e85540d020402982100010001c070025031305140000300780000307281030b2080000a409000035000004000340490072100840224207554554030700c000d490081781d00c1d0340050401082480002d100c042038585106600b80400e1114692401003482c3c00341d0340424149040d00030542c480290700400c408005040c1820145040c0346401d001c2c00000d02400c9010f605103c1c00400107028102d01c40341c0b840020b0b810800f100c480c1180e448442c0020004010182c0c000d031014100451594000c03100e8140300505030000f40421980340c1c8908901c0c0310701428068141c0200c1d880080899140d0002e401c9080c0500000a0405400c40d00e00d4a031038405040c1c0c0f42400214202080b1f1902c0c08900030b55a503421011040e0b80380014944600105044181e8000070302811002c0d18051015000592041051440030003210094030030580c0e82c1d01410801c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 596037059 1250 596035809 596035837
    0x406090306090804050d0605040203161226030f0105181302010e041805101d03031b040f180e01020f090f0d02030105180c0d03080a150504110c12 64
    0x8200081c156030040000a020301d21043c01c258450000801c0800c18000903a0100d40300c105100c250700d07081c01710000c8940803101c0411840c1c41c018400a4005046001420120745140c0c0c140c1d0310341c0c000c2100d046d0380c422040825568602001842c101354001c2c001c06018000a098070500700341c00d042d00c81e0140c0890b4100c41c01c104003c1e401190491064101d99810545500141414990200c0c1101105202e0400340c4880e9411000f000c00325042d01e10b018424107080603480001400c00300480c0c0d00301a1084601d442c250100708224054440d55100174041c8080800002d41e818140e1450b02906107262000d0000600380b03e807581c21303800b60100ca07124207a000c20004a075480c0a60b441d1030715403405404003070b0721402e60b000030b03007140d0b4103d8400b070301002900110480040b09216421100c00200d0780c00319228000e07240103002c4d8100903d2054003d5031441900c00420b005080c100062000a000340505800c0f8035580390981c1000c00b0f01501845441240e204e030704c100c039003507411038444500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 596038309 1250 596037059 596037077
    0x1403010b07050a0519140c0a03020909150408031e091e010f09060b19060c0209091905241b0702240901080919030305360606060406 58
    0x2660900d5100100031075142c8514071440c000100f0502c480c00d4016a2080b80c0c6905140c5800c24074500d81c6d010710290314641140040001c1503403600380315401e0b02d4040d50708880564034031840c245030040c540a03640f02818240200400c100000d40290301c00c103001e036000c280520481d010340d80c03c0f500c282c41150b1583c10030b610b042140001c08030280480c0300d00c1400401ea000304041c0381c10840d00489800e59600f9221011406e050428034030391000d42c0d002c00980d01a0920b8690010040c0e20040802486020590003003140713580200400380302e5001c00c2401c0644002c4d240303422581c2e00c2d80c4040c410b0785030054002c0c181c01441040d42c010301c1b07080c1d0420804003e00d480c00080300d41d980011401c03039001e11442000c0703490031042205002d01c5410041d10036959042c80d40094102d8900901403104e0354400c0f00404080d0040c090301c000c4450340b40c10082040c4c1c40310005013901c01c0d440b0314891400000c4500a0030000240d6400d5408003180ca02581c0342510380e442484258031840c0252404141503003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 596039559 1250 596038309 596038319
    0xe0402090315060402120c0a18030803011a0408031602010305070c080304151401080d0306050901062309040e03030f0106020a20010201062d05060319020c0f01020a021b01140301 78
    0x1c01e01c55031010001340014130f44499601c4150110b0070590303403108003141c0415180741d4240c01002ca02441040160701030982440c5079a90384003032005010310b400b030140070030b42c0e03488034413405007a203000c0c010503002d50340c0f00ea96a07020701d031840d9010003080e40040d0400011840d0a4000c80041c600c1e030b504541c480d0310751340d81d9071a400307076211b404c1c1c43c1c0c0761180d03944610101840c00c0351032002d070103060400060700244610300e4006080d645143c1045204807c003200421606070024800180c01d885020009811101442583da4900442c280650402c0c28680d00e2052001d0100045200355400d1120302c2080e46c81d04c07000c07030f80e522940a00820311200c1c1030700010010140034803c0b4884a0502c001704456807940302034490401d071088400c048400c0881042d00e8489514000c03070107403d007501c80342d00714900124124804195042091540c80e400100458880f105018018075803402100a43d0f680500c00d00c001d6880315201114194540315014003d21980314a644140501442c05e42a045902f00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 596040809 1250 596039559 596039593
    0xb0315010c080c07060503010e0f0708010302010e0406050405012702090f011125030b06010309080a1b0c0b0c0d0c02010e10120626030c070e100f03080702010e04020903 74
    0x440a981890040c04800d441e140100b003010090050386d500c10781c60307524090110722030f042e000d80318054844166080002182d403101146044980900e4094507080421000c80d00038541604240c0d0401c2c00c143c00070859004180d24441c480b034034565039200d4011000e012808900406071040e40c00b02c0704050550702503110f008800d01e80070a840590b06210107664912540010300c082d4500789104960b400c0040c002c07031031200c0f540110282014005040669109a868400d00006900b44a0b102d56000782850313140e2a080b0f83c159000080102c6a601e42002075210303040802064514400c0c1c44245000a01c240080641964182c403040005d9103254100091141c1d92108070040108095907150740e400c0900aa800500c00111040c43d504814182d1103050112888d038000309610401c100700c0d22010000b44441241c081e0601d00c402611000d00d4517000400e207030700282c000602d1550100034170088500400100c2d100b40c07940b240c0800000c09000580c02540c0d803032581504035040000d000b80310 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 596042059 1250 596040809 596040827
    0xa06050304020a12050a0311011535011406060a05040e040303020705011a0306010609030201022517060106090f03020f040b06160606180501030c060c02010507120e01090b031501 78
    0x1000308905038a5440c0d0139401561000c0c502c00340d8066102107a4001170640240083c00c10040c10310091260128004034858452464403810341310891681d04410f8074280075101c2d40c41c200c0800c00c448440341d44207494a000e4001071403810803074460703500410114504a022249c01a1168a5a9040510f0202c0300301209800038401c0c2c05160b000c010007030010740c0038400c40c0203050507080903507140f10001090501d84030050700000140858100203001603a00040d110380c031499003050f890098403040700d82881131780b5030b5400340b46540b02100701c6182010b00401c18a040c0d070700c00c0e61046903c507a5100c41107603816440c40040d400c029240200c84d100c0c1071903004001c0c003075806840e517440c0c0711603480300d040e40702c00921081d00c480c0c1d071310b003001e10941024030b1a04180d0b8686040a00c510b5045494454520120b80300380b0044c0500c01c1441070071079001310151010183c100d000f060b2007203145a0094402d8084807213440c0000c002000115894190400380c0f070240f801700d9540e0310705600c084015159082 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 596043165 1106 596042059 596042063
    0x5010603110f0711030d11160b160302011103090304050f09090c10090308070602191e03020f04030c080f0613020d0f06020712091a04050a06050304 65
    0x4160415601603080c4141c85980d0f80180d46860f02680048110700f0342c26002c1c01c0042d555040d041005402c8000c1080284c0e20180c030244034028144a09008829031050140103c610b00d202c12090440d1a900c0782c000003828041b20090001c40d5003081390044401c2e03000290030702007401e001200c0c0c4242c0d14250b502c01000e00307000310340030b4449200025141c060741040800c080c615110b500010011900000e42c05e03622140c50400c00040c0d400781e2207040d02d60f01d4450701c40c1c0102d8071820341040b1780210141c1c092210854070004902940c015146407035040300601010010994620045008140e46001443c1d07142080e49202d0402d1030050100305a01131746844c003400741e1512010000a940e1007220014288020720300803000340190a4060b0024502c519403c0c002c0f40c2014124054400d800c0702840b03c5561040c807160301d8400ca0048942020200404205e400d01644c01781da0014 = true := by decide +kernel

theorem cover : BRFrame.Cov 595863309 596043165 := by
  have h0 := BRFrame.cov_init 595863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 595863309 ≤ n) (h2 : n < 596043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
