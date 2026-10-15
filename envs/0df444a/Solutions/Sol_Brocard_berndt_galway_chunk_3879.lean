-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3879
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:56:36.593304+00:00
-- url     : https://prove2.me/submissions/9b10a247-7d0b-4a8e-aa27-8f678777bced

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 697482014 ≤ n < 697661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 697483264 1250 697482014 697482031
    0x101728060608010b0d1202010b150a02060105060301061205041104090b07030e0309010c080a0507121115190c140711130207030f0507150903030f0f05090d0806040b0405160305 77
    0x1130740c410b41030700c0343c0500101154000792043c19100700010201e02410018940701c1c0c00008020000d002c9812801c050507004280d0b4090390101c1c1e0302c4400b03010103400b0074031a690001d1400c2d40b640c140c0203c0c40d07101c0358016024003580d00c1302400e24000f040030380e4240c080440b00810080308020299a140c41400d0030450b086000d146030051810008050364035654005d080c002002945034001400303401102c0c0d0b013551040d0021015140070030003410503440c014640a2178010b1018604030ba8550b00c02d410703c19a200300900f007052645000714001096140440018080503044103182600d0340030140200e030744500356803054822008140514a1030814000b821329006000150019070049100f000701e400501c0c04030340b00c501c1410034140081e1f26808404219140174810000e0590540284664403501c04051054030400210f0720100e4000701c0303681d0340c1501700d0043c8410151052030380e00d810100062001c24900183e00c00213045a03001d444503c2c003200303840c0401c000150540516030380581d88 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 697484514 1250 697483264 697483271
    0x70611070c0b0d0e0f151e0405070e0105040504080f0a211e18030f020c040204230a030308011211090702030403020310151403100e2410172806060801 66
    0x1c5d51401d81e030b04c5150b00f111700e00000360400140c61038803012205180d400003c1010982e42011b08109844084602607004004c44000000c9141d040034001c103800703549d11210241c0b030305c001545900c0f415006240e60108004602d03240140b290300300e26551100752840a0006920359030a551005000800154010454100207150710101448410952200c0e01818030126404500b141241445120710b0196800b920204c1d001c01c800d403003642400303000340615030600807140214080014a060303520008002411501c01402a00d03460a540d0345618841e20000c1d03503144801e0300180010200300c40346030040e400440c0030810341c6002c1000401100610340200716007101408046601042c41c05a5070f814242c2428840158070708101c140590403071a142003000c0340c00245110380b01c01e0244940c035281002100740000b20200b42c04854080d2841e40d00346082c451500d5a01e06a601201140180c64028404c1400c02241c0a18034015440080c800340c035500ca00c5417030490101c86a60300b15801e00d030324 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 697485764 1250 697484514 697484533
    0x60c150103030e012a0f050304031403090108150306042310020c0c011701030215070203010c081603060803030609070203040b070303020d061706060909070f1226070611070c0b0d0e 79
    0x11a052003117680d580019081460700340504226103103200759440182000c850038036241e841f480100c05010401000d0340d03407040d980c4540740c0c05a03c045c000e60742d065040e00b04401080002d41681d03100f031007040b181c0c0e02c1d006e440424803000c14107050b40d4007080c6001c0742c1c0025204070b003550240b001c240443d10900b010744022811203e22003002030140070090040f5000010084508842015241c0069005000344109030721488018400c110540300600429500040501098000c1c06844c2c161110071000b1802c42d0b407900c0400c03000401c06020042075001c100804100c4a50010080c0200c0d80a5100035030394a64454542c4111501e43d0711580c2000d1013145031040300e00f40840d10310b0304541c0880c2c80c0042c03622119043c4d802c05c0008c0c1d025541130403800e000001c1c0b09116481d15410140207500312528400007800740f41144206074043c450300d5100304030200004050f58030070015030403941c41d4070781404420340d01e0100e0404285c0015544c00700200d080c485100c5140102c0c04100020070240c0940304 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 697487014 1250 697485764 697485827
    0x60503010c1227142e051b0f130807050109030f0c080d02010f0506030c01090317131412120313020301110d0e210405060c150103030e01 60
    0x3954008080ca0b240c03a500001c4444115003c00f6404010881500c510141c1c41c040c084109082840c03d028011030900d1101c4407010362010344030074420b603c0456541c441441c0b4200400c0c0007417284184c010075204a203491030209010b0720301b4190b80d10201d55602c0001ca1401e0b0b07520350f00c1d40708005691000000307100c543d91041c5103500300c1c0c0e442010041a40418a42010305c08103903040454244984480001e42a6054002a49805014800304803d4454100381500c40b8103651440340402d654180410014074111000701c240840848401d050080c601c059a16a01d02c65000281c40ea0b50001e03005418940040da07180e054010400030700f140111552850100e01006140701e5802030a11b044c0c405644081d041654075152000055543e0700d450010750740100309902052a031485102c030003203070b2014050210201482070126640c145450034003081026441501d200c80c41e40a20b00c0d007880c49100c285a1039002c1c2d4440d480c0c0c1c94040015000052005580100c0e80c030a0040003840c140084 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 697488264 1250 697487014 697487027
    0xb0a05070b070c0f06060501180b040608090f0a030c11030a05120a050702030a080a09050604060203042705090709110f0304060b0d1e061409030306040f0608030703050d060503010c 79
    0x307079106090050580e90440103840441401101801000201c5400340130020140d003c0ca007500d20988440b100c40d8000700c071a810400aa0007101e40c4200e08203c14800e2034002c005250340320300918102c2e0141c00d800010f090030510070714801c0380810320001003042000241182c0700b1480b00282c004210712605503d5499640182d55021f40700220300045044071180300b50304886084e41c0140440300705040902c4d100e4030a83c0036001d2000040c841010120345031030310760200e9045810b00c0c0d000f03600b09070600c02442050031035000016814000542c0340a101410350049601c00d10b00b04028182d107500e800c581c070040c0d41c03906034a04004001040501040b4102106690300a41c111500064844100e0089070488844c0a00681141c81034001d110340d2542c1091034901d52442103005018031302001d03060076540300c001c0c0c820303030041e4006000213205410182c5c42460b0415400d10041405a550441141140d0003900150000b07400000c4080041c141400340c940100380982c020012402040c1006020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 697489514 1250 697488264 697488277
    0x807080a0e0c031605031209010c032d0804030e03011b18081501030c08280c0302040507050c1905030a05030a0204090c09080f0a03050919090c02160b0a05 68
    0x40e03565424003507414001040070304034000c00902241c5800402e406190340b003040501c9540d20a1084140d43ea8039200c002e402c0d92a10360741a11131340710310005a5404e0302e80b00c9c0070b0407210b000d80d040d101c006543e10000c10b40c000800340a5803203000190500341401003031102d51045050180e818100d500c1c00c800c4010380c0c24106a80386161807844860380e045140c558404c154031540c210f00c21a900a00700c40080c0300c40038105d9101c0c1400592140e510000c032038451047c14501040c10342100c00000d500c0b14000424516584980e4405800329120743c005004c4440c00d41d21f000c0026804590b10044c0001001285850100c04d20f140008100659620340e99229038610f02c400c1200210101d10641703034607010f83e009414049010700514013142001070100c000351091003e00e2180c003602603496500410100802074065541ca072070300c41d0600030f0080c0d40302181101031030040880c8000603c1e40f49842749001103c05030b0b019100749000802401c50740c4143d034120304549802000b4640c0e090b80c101c41280e00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 697490764 1250 697489514 697489531
    0x1060e150a0c03110109060c080901051605070302030c070e010f0b0f0307050a0c0f1a1f14010207050303040e0108010b10080703180f03270303050706092a08070501080708 75
    0x3410b8030714642183d801d4604400d500e000d6003001a95402c1000640000c00c0fa05016514005d07603550791001036003079600968009444a00b0030502110451042000b401801e019004884c50250711041107403604e6407035071060140d401c4902c0103004074200006080c1c0100b480f0048d0a0800c03408185161883c030003c0d04040c140310f400101c281e6050b01511241528a4008003075115400342d070700f040c0f4a07a1000032804456020344100041003101195403e43c0e4108901104a1040742050082c42079038020b0380125040d8468407400041a6504100400280c03001c00d0700407a26501d042c403020309403224140754070b00c91194481481800c65100c00e86035801910b6180101c0c20180050130f6500d240026140942110348040501c000d244e00020150104000e800c802603110111065419641600c3e000080004108200080c041852500012049800751070680350b1100c01511071200c51400980800b001040c0e000104001c1c1c0d0140407102c018003080c20700e02c0c003501d04040d00400c8428020031009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 697492014 1250 697490764 697490777
    0x150a02070506060d020a050607050f15071b020604090e070f0906061b1e0f0c050f01050915040801020310030309080613062d0e010605030d08070f050705120301060e150a 74
    0xd040d903540d06c0b001030091a0103085a40d40304098180301d52111203a0410780c40511511000d1000d40551401281c41820b0580d900c541d00c0003031090880104c014004180d0b80f2071018803010402c070b500780c4600d0b200d5810a000030041c09141181d50400b000d05940840c28562a01d0801c02c4255002400c0d800303035803c00100d00c1c0070b00c6214035009481c00c201b1403c500da0b041030341214404004503003426189160086035003500456440c01081240c840da0310002d4006801440030b0074541c1031100d54600450345010180e8207090321030081900b280c004403551060100c5400003007040c542c0244610014100c4e43c400b501080c81e00e5503040401968000000308990f40e544866400e03141c1a034800c801a400c4024000b2100d20f07102d1685000e000b4603040452954070f0880c001502d464001000303e4242c0340c0e83c80e1415151364240058a1640100c4415801d00808008a0002850500075031003000040c1d44030a032654140070008242500e0454a6401a0342c05400c0c80c40e851004816208502100c0c40c2c1003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 697493264 1250 697492014 697492039
    0xa1217060618210118030809061b0703050403050a0c0302010807030203010f0612090210030f0b0d050a11150c1506011d1c020405040506090c0d0c0504180212150a0207050606 76
    0x1c40460b403c1088420103520b01032949504100003a0041c8000d800b81d0380700c41d4291140f814407034071340c14184c44807080142081d203403031100c100080240c81264000e0400c1420199203032129420080310610494200d107000c0014402c5680060322640c20440c6440c0450035581069082c02141806d8042c0c0e40c280048190500e08201144d0404170641e40d0160220f00e00e0300300604094040c100d210026400c0c1814403005c02600d00305401c0940c3c0d00e0350031500800d07280c6203c1d101c07500c8502d0f80003020f42d04500910f00040c05000840018408504d8031001005414018080e40034514005011541040303207000d09200c4021101c0c5940c0841d210840b03480c4021203900c40248031819a08000940082c01d0108210a00c48040741c00d40c400c03040c01090729048041d040c1004240402c3c0762004120100d6400184027038141640500441c0c5000d030340792030302c4e034005800041104042d4400c1c8906a840300389088051443e1004854000f0400042541800c0d1240d984940300c1c04020641805545210000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 697494514 1250 697493264 697493299
    0xb060d0804090e07080c1801030b130804080a020109170d0f051b0c04050106021515010309170c1b01120b03120f070c0b07020d020d050a1217060618 65
    0x403200184102c6504000324810f1508180e290900f610a514881c0600b0b080520a070604054001072454035190602c0217070309594400d201c0f01c1c030140c8007400660501d4103400004003808010300140020740e00031300192125200040c01d2051540080b010b00c1c0810024034600c40340000c11000349929030500c120700310010401240c07140a00000c82140e2226403944000e0890045110f6464000039241800140e0721200c01b0307603883c2c940b143c01e0090742c0b00c0c020004a00d44540e68428003011070514012410300c920b515211840040c41c4840140418000f84070101c1302810442d12854580d40c4410850300380d079480011300080c9489055001e8603494081c5001b180e82c082c0b01c40f000e000603a402c1a07458041d4032070280302c42c0d04452400c984400001c00c0c0403565a548000395402658002e1081001400c0d41e402d0210000c030b6035200315018031070160180002140700b5000d0b15154040d13074130325000980e544907000000b100503159500541c802c110068400c2d011004d20a00140c080d108141d0701c5d075030307500b4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 697495764 1250 697494514 697494517
    0xc0a0309060615270320060f0d0c0801030312020d06120b090d03020702062b14060310270503040b2206050901020a110105210915040b060d08 62
    0xc0007070207940740c840c2c041002e14001849070041030070303a43c1c0c581070780382444104c014030f80c00e40c964000d0040980e8010400035240552642c2c40c0320200e1640d203207080003440842c01a0b005070000c110044d0021403141c266401c80e103e01c1c2c40800303040c50041c81035407441d200500900b103400103041e050340d00011a1180700c40681c101800130521904001100c0946050594901c00240c070943c019000c1c0a200d0f00101d8030a00130380d220301d41c000780a83e1818100303026054181c503000c0d901c0418918190700700c22503d0000e128200802c80b02d28110b0900d0b01d00701c01014100100b0041d00798040d0300d0612040e071f5030350011440131000c1c0d14118408504603824100705146000702e50110400200000b021911244070b02e061218240c02303014070260864982c2e00607034040c025808400c1c0168015441c0e54081405511550070304403040c10001e180180c0c11400007070610301c50401c4e0381d444c0f40c07003014010380c69405c02c180c00c059440501450540c0c186565841080300024107014440c803500c400c60401c2c411100c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 697497014 1250 697495764 697495781
    0x9091a060c0a020f09040b0a0c200d02010c090e04020f01021c02030702011e02030307081f0b070516120b061503040b0702060603070b12130804030c030b0c040308030c0a03 75
    0x341a00d840d40915100346580e6000070904030301403201d222102902d4140861103c1c0610303480320b50402c4c81d070b5a407003814004000361900c1c0d00400c004401c031800c840105400a060031411200a0200c82001401c080d0945070015049406c1040c804420410143c03270030f00040d045641264010200040c40c00106d10b0100c1d9200300c4c0c80400403814000c240140c002000740318140c801e80702c55401030910a100ca2040d07245d0700d00c80003d0b0b0020000212401d100300c1c0103903070203501040002c0c241600802000010922900541d52a0600007074480c140842003054465440408180350111400d051020340c903030010402c0204682038110105000b5990f02c800c075000309542c02504c680300e00d441d04000100041c1518030030098081c10005c500c5c2d904001c00e18800790740c03400c20580c0c58461005144824004000c0c1030310701d0986d05000b0300001440c4603000b80000d50146219041d48c500b181020324440c0300180c00301d030100c0c86c01c00042002585d40c0c0103030b907880125002e2480d240c00c142d51f03041d006041c600b03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 697498264 1250 697497014 697497019
    0x204050a0e010e011203050912070e09070618050a06120b311b0f09030507030c0e010b070506040303020f0702210c12151f060302030402010f050a09091a 67
    0x4280401d680d400019018129034040d0800801641d071001401c0554841e1040a4009030082001c1d0300d190a2072061504008140300c00c85040c1c5541d04a0b5004050041c0c030b41c113160360041e0204006003039001c3d403840701e903c030a01d00c99a481841c0a00262082c021403180d0300070300880b004180c2070581b00e40d200e9141038102818110480c062032140c24446001007000c10f000401c5c1480b0b070300090b1a0340c40703840c80407544100580ea441050441c2984c8400381c3c454100100481124048009a000e0010f40004c51150001d554102d04108030781a006d04140c200e409464004d00000020540000782c0390341050301070800596502c030380d003455080d034410002d005c0c0d00b081c001c00712050289044111174044400050584103510244410490040207400c10a525540300c0d50758143d41c00c1e0458405038103e8105083e801030b088844522644d980300d20790041c80440d41c048100800d658102584412104452809a2514401c000040e00541d91409142c5115950b0244c081c03030811180f42c01090002c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 697499514 1250 697498264 697498279
    0x162411010f06030204050a1a060313051b0103060b0a092102040e0d030f061202130902090a0522031704140316020406150203030406022a1005090c0a18020405 69
    0x26001c03040902081e11040740118500400178a1403583d0b403089002d14a0780c000c02c95509905081000000e800c05070174284e00e090031240c020002081001030348100410301e0303010501500c1c0440094111020380d48008004003081200d1040190b2000c601c80c140c41544402c80040001d200f03181046407106c5e50b0094101b8a0014130501c003610001e0040322400c01558140100f07004000c0c0302d0181c07022841103403500207807102c055005191850241c140c40342203884c0003072a00c407140c0000c1e14410301071b140b80740070315500e0060203100024069100c6504800d01e03240b0700d041d40240e400510140c0c8602c1c0c2813001d0354198010500700000f01c3e5107005428032207002c0380e46403982043c0e50003442001c40c008078810342c031b05100080c1e403840d041c181050300a47c032b0300a075045699035100e500182d8056003180d00742d040181c490013112503038454854110695070000700100700c02665418200d5030702030f1603510701d50310112030700c055581d840d03818209480c0f40b19900c440203440c104042019001d1600081d46c8060b5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 697500764 1250 697499514 697499531
    0xf031005180a1a1305130b040f0c08010c0503070807120606021f1b0f05070c18051812070f0b09010207050d050a02030301060e061306050a0216241101 66
    0x203078035041c0c0100c8054408101c440b80a016010039078070000100d07500107900b1800c42c400c58143ea40a5540a050410344240e000001d40d91445c514500325801c0303c8440c03541e91208140304034080d6050141056200030050420032840240c03135408010000000c224002002690251140107414270807004ca4006101082c0c41c0d21001e91503008080342d9820f8020070780b00310094044030340154403140700755010020481e12180400c590180c2001141000d0203420400500090401e15041005014401400003c032810400450035104003800750021001c000d00c0604100501240d104501c4126040b081c0c2d4131942ca14214800c548403100280040842c441001010789040d002021030710300c648242c4840480315403003941e050254110520040c0c1c010310061207402d0180321080340c0c001000f098282858140c00c80708007040c02c41d0300881d00256001c01e0303440e0700580402102e0800c400240008009c281800380354040142420040410460400d0303103070341128041c110802c4a40031840080c000501d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 697502014 1250 697500764 697500799
    0x90409060e011b170a02280206040c0b1809153303010806011206021207170a0e0a0b180d02150a020c1906060b070309080105090c060f031005 62
    0x207801a0f010108010080d902410740d1082d584028008248001200c1545600c1c04800080d044600c04140003418941003585422542c41980705941e40381e4014030103494180b9110310b061006500c5000c00f420b0521841c0f8030070f04040c0002d40540d20a488410b9140c2d50004001034210864441d04d8101052103810501200406004e040e0802e907015500b51240500203094036512007440344040341d03000038006102c2c0074023100a90759454000e400150400000095520788284d06981c10300205003d9680150140d03a2400c0c01903100384860f504000c1e410200c7c0080d41c940410703110040111510070000303000c20b144100d101110700040c2d07048514010741ea2601030b5690100140301e046080759000010582e02d4130380210f8600c0b0802001400e01d4010266800c1200a45004c04a5503e40c81e9403011030001e0184010302101400b175610403d9a91905104508480f0058651495a008441c40d82c4a40d242c0c242115620b4490328441c59403503a408540080ea60070310703000a94404e116410301030401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 697503264 1250 697502014 697502021
    0x91d0103020a080607080103110a0314030316030606091e03050114010611071203200d050d1103060109180e01090b04140c010e061309050106020a1e020904020402090409060e01 77
    0x90348240ca50b5411070b52298030803a5038100845a0800050402d0010300000702c440401802040c00a041c0c00038491703c0340d56a20768500303500b49101c0903500220400407040c10380c6c85a2260540d2600341008441d0625400815040c1b107800f824028245003414042040d03984c00702d960040d900100204644003008011645c500428420b8100107284111510300f00070010640804448a84070110f40034a2281c1c4d0965003540000300c1458021421861044055800c0c0305042d00b00c000c03070345d030b850703036074100184410450300360000c0100e12910a000304900c99030010340e28825124600c0d032a0b819000002010b0300904501e07101080b081d402d012043c1c1c20440710000310750050b0700c01c02402c01c403404031440c40b5a40303a2110000030b0001f24210f0000010b810403c000b440c055842c4c00c80112071740e848105000c1580d0007a4014001a40100036490610200c40c20701e001d00341164901c00514256500080c0c1702c002c000d0b10103440707554001038403000d555455100078a61948254180000440608060b000f07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 697504514 1250 697503264 697503269
    0x70302091c060b03070f081903051908160c0c09180503071101030b0306040201080708060310140405060c0a0c061104050904140115050105070b0a11030916150c03030c091d01 76
    0x1900c03400d1408501d03c06d90615080a81e0301050003402000115459143d582d01e24890230703020f20100f00220f4201900900b210820301100fa11010354604040e0a10108403401600c55003c1114076200c4000081c0742d03000309811203440e40c4004c640c43d42e002d00c500d081220301c40d070001c1042c0700000c0d66108102c04a5010404c900b001d1302c0070440c8040000901d41c9840045500900103a00c4c50002010305009100c0150081c00242c03c9900c040e16024500003110010b411a01007d028001000100101008040c2e0310610b10701002c1e082041c41d80c0c002d45044648440141280d444091442928200e50195002810010102c018508060408120300c07035104500032195402c00c0b40c072221038119202d80e00e04440b41a52032904d048100d40382d21180c848080d05c502c40c460f41740d032074440d440303400000594080d0f4030341009064840c82c1034866a6541ca159440104c00310041505480019008035008422603050708000c50101c540300c00880d01f00500b41c01944940350170b003001d2201c100d91030507013505 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 697505764 1250 697504514 697504519
    0xe0705090f06240a03110f0f03010e0603010b0d151e0f0b0103020313030305090f1c080601080c19020f030a0f031a1c050102040308033c070302091c060b 67
    0x1480355015504003d074045900d248299040001080c52440b90f80320006001071080e5050030407a000b04000900c3e0b010b80d174034240100020005002000d00a440e10741c000008500800070700c3d51039000329400c0c256059014241c0080d002c00310601e28891b80207901413180711099641c40c6641540b00000601c900f14a29400d60f00e801003060840d4000d1084030f00603007001c04601485021580e085000d00340003860030b40030313008141500141c01000c01c0302c001808a4801760a80c201d080f490010200b8030010702e42810414a403040c420340e130200c00d0482e1910341c19000940d84880c070000045e4500000f0810030700203480005140026541d11804411030613040d41d40c107000c1d001d11803031012100b8412143c003980c000c1031401080844010001c02610040c030500015083c56680e13240c01c603082d00110740707049050030303034040134000d0361003000c42d2003141224a0101c0f03070840c900c04030220110300c00a0049040c15400281d100302d5648400c6041620100c0c1e20040568554620b0844054240f18941a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 697507014 1250 697505764 697505779
    0x3c060306080f070311040209060d0c08180a030f033201090f0b060901111203010f050a06170403050d140405150c0a17070509040216030f0f02060a0e0705090f06 70
    0x60b00300c6004550442103a4112100010740b05109007044000c1d4040c0d034071990b105408006010340f40e540c500404e904d0400ca912881d5040c50700f04800c0c00b01209100c81c000e541d4200e199400c0001c0d8015940101d40c204d039141c0003e03060560b0310540c0310401651024403c0007003442c03240c001d041482d015103041c1d4068140c2030040c000340044040a40d0407044490340d100c8030510200b1441d52040d80c8030705036494007800f220565030000031a0140340e4004e80241d41c41c1100038100717120b98240408075800610a80c40c081300110003501c040042260b01410040402800107550b00c0004650f0700460707800b0102c800d002c1540c0c1403070300e8511340c0e0301e1429416001304104030f00080d0f03424140e40140c540ba441c5580328611040000c00e0075640c000001015035007480340600043c0c11702c1c0c07a42d202509808400488131b441f141841e013000742405002d815090704120358206440106076000c40e03869002840301c0c801107003001e884200241040341c0c581200307410200007005c202e50756042c0c120302402407400740e6902 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 697508264 1250 697507014 697507033
    0x309051603020f0f031e01060f12050d14090f040e030a0225081531060f06060e040b030109020d1a010b1e03061914030c0a3c06030608 59
    0x400e100c00000c9802e17034190055481e500300b81141030b40300a000030b031090002421035110f5010140103181c039000801e41c9001161107604011040045251111040c2040841428141000c2c0c18911443c003490f809504210680780840d207468200c0000202c1d4407068030384444000302e00940c6c5090500385501c0d00c100101c0d6030340002112981900a90342e0040242c0290503a42c0300701d88240e03001610a032050010a00301c010107030380217401034964911031484001045542d081071001c0d07034452040004214640142004403907000002c82e00030400c161800700d001041400024010810745070084c1d0003000c4444c0300c0040144080c0085050b40a8480140c09a6201c0e81021340900a40d8812411140400840b03002d4a216001a56002c4001080c58070b0070310190b040406011400e6025006103007000510035101e180620254800303c0090750024005454050641d01c2c1801e00b004510300000c200c010160341d0392040801e1004180000030013100540d54610040091000740f140b07400ea402030513000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 697509514 1250 697508264 697508269
    0x30619170309190b1b0703020307151107053001090813081b0d33061403030a08072304030b0105030109050c0103050907030215191713030309051603020f 67
    0x103d41520002c114150510075006418403004280d00d40a040e03070b208036400040140c0d0100803502c090612058481840b450144015010300003180038041241c201090500007a1114640807158140d0f85440541c400d01c0e040c200303040c841d07040f8039024055003810004070600250b90b0041c0401c0310602c00484d003045d03131072507a6503e440f000c0d10550301c2580d0004042910b445d004000168a5000d08071141d620f2503490700c101c91101d4000c404800116814003a10f114072210700c04c12004041e0700300e0860a000d02c0c680069224402c0d1001041403100304004a59614800e1400070030a622001c0546042114030011101c42e401a01c021211605200300110f40343c10107002d07020b24603600400906108079041c00560103441300421070046841030130000000345e0f40302c01d0000d0341c4210603140c169548561010010b00c440301c4031040d41c14407141e03520300c03105000c0031600c1d240c2c0036641517803101c0030342000d160031400780c8504007010f04148070749805e0b80411001c10f02107504407442283c012004c4000c81c0b05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 697510764 1250 697509514 697509559
    0x1c11100c0e010504030c06231204020901050a0f17011415032802040c11030d09171612020109060e150109110a08041e03020d1b08030619170309 63
    0x5c001c06411007214100082401101100f004140e045080132000310041881c07081d54201d22030340030b205072506091100b58181141d030103015110a5484101a40c10101011a0140380e84502c00da01d640ea10146034000b0420f500c48083c1e11100203030040d45003020002c91090280c0042c11720f109020390354011042e00d00c2074406444002c644c001100d07042800303400f0440101040301c040418040243cad44004075100070310007006986100c4a0000d0310075170702c0c10404100003048502c44c00c00e400030400c42c42050f24280303c0110195110b4444182e40354620f004074054002c29130014980350801e080c0b4483da04000c01c9500c0f0910101402d800d080e030342c504851003901c40d1940d2a17031040d00c00302f10307640078544550a0304c0c3c3c0c0039000d1102c507101303103140c00707a800c1000c0104c00058006821203403640415990105d201c50b01d071f40485110402c1c0c205140c686181c0b612020741740521840400303004000c900c0d06940040000c04035034610120f0180015404d40d102c0d0310142e54148030b061120301c0c00e804009400e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 697512014 1250 697510764 697510769
    0xf110106050904060f060305060106030e060105030c010503041e0c03080408010e120417070e040804150e1008190905030d4b090305120601020105091c11100c0e010504 73
    0x10300e80c1440f620f03a622040c00615010500c0ea59968680ca070100c042981040715a00914880d50000781c0404400c0000d4109901038000354400e07000481c942c2c20340d80e803250540e900305400002280c0403441e078544001d0249a4410001c1120303144050000078802200d02500495007000001d215175181580c0003511944a100701c0910010180410300400045c2c050500b2003402010450310020346412a48a850208072001c0703a4104e4001028842c08900307464030203501200b4140303234040182c014002114608441d65444c20486404002484544030308002d02a00b50008010400f100c01410401d45030750002050003061070031b02d04420010030f400040b5509074a10310348004054910310f007030241103088004444005103141c0712a4204c44c0701034400c03102c2e840d12030384034295180c210a0400403044001840c007819039141c101042203526001c604201000e104500f185921080030030250764080ca1800340e24500e2140c800d4401c0480c0c0143e0003080e4490417a2103000b0050464001140c0505c02c50 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 697513264 1250 697512014 697512019
    0x26060405060a0f020c120d110f0d0221090705040c051e030604090c1509060c080313051609050f0105030303091509100c08100806010b040302090c040f03030f11010605 73
    0x550026220384102d5000c41c2d012510a9000b500d170000340e02e1310070315080e120204030980c0c200005801c2184903052045c1c480c200000e102642c00c240100c01030f61154000c01c1c1080054a40004464103910041c62400740c0ca5a03200e10145410300300001c001d6a200b1480c09418016450401d540050714000c90685441210810700300c41c44049981003030469800c09080213810545540c6040000f441a00400000e8039080441e800c1d0300041003001000712980d036110105210b03180c007408000ca03070081c00300d031303403060009968241201c40e61070603d01d4003c080c1e02d420f42c0008203480109403e44543c109501560382203981512690301c2e041010b48910041c0c1d1368030707410f9100c1050130016015100000d94400c4414007650044210000c1200035034011540e00d10008981c0b13000c00400c1a0300d01800710103014410f0092039a58108032024406126034040640b02c4d02419000445034010442110060320b5894500d4600645c1d0b85000f070500b40900c8100f00100b41c1c6491040e26680051103500201d4000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 697514514 1250 697513264 697513273
    0x8120a020f070609020a0e040f03031802060a1b020604170f010e0607110709110c1903050307120b042d090b010e07120c050c19020904020105090d05010626060405 71
    0x881c2c0e207181c004d1000040c01c03078104804200c00160111405c54803031255000c1c403c4003c0c0650940340080440301c4061002803580303121004500541c80d980c003550b050f000c0c1410140c10301101000d50a488550300da10080d80080000b40104441e10807908600c14045148100c40300a09650079580c00e9541c0102c80141581c07213600060f071407a1081d6103602c660150300c01503542c040d0304d864010041c0d500030b0101c040006000503904807800d4007000442c0d81d240c082030740c8000c1c0f9507141e580100035120281c603403c200080784450719480c90496111005d1100c0041003049000315000b004071440c4103011600840c20141004850035140c28003a00240bd6405000301303034540e090551140e10132001620712070420a20010309180d6a0161040d261f282c4401d40790b0740c0e140c18003d14054034200300712681d1640f14000d8846900182c80b09a10710f5040350342400c1c003588541c04500031a280001c40e40c4082c0440d0300788200003600d1b0040441004910001800003034400202148140d60b91500b9500201288e02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 697515764 1250 697514514 697514527
    0x920150f0307090909030309030906230d0b19031115070308040609080307080603060105010c170705160b0915030103051c02012d0501080c0a0306020c070504020708120a020f 76
    0x8001107611052606200000c60345130308510b01268007100003140826943d0101809140c0c0091110340100750520309100e071449209841e213104a100c90094000f80e102050b010100401e980049003585c3e0054284a00c2c6c500500c9840c030195560701c002d0b03d07080c020205032030040c20b2181410381c41e8950510703501e162031050760b811101c1d0380e8000c0042ea01d240c1e503000d252000500e942e0007103020b04443d585481d401c1c108402010300f005810382c80281072100c0646400001240304e160042d40d6074560814036200c51a81c03c1c1182805855800320110404511010401048140c040c11401c002519004c55841407510041950b10080c00003615560102081c0164075504030038503000100e851002003600030090740c4261000030800b1891f040c109a100e00c0e84c1c0703040800d200e07850040c81210020201029144003040c0c4401ca02d00004c0d2600b50001503c8034043d0042102100610000e80111f50701c4d02a41800319a64100d481c80074005810314001c1005130201d0300a40f00d044c105403010310700d00207 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 697517014 1250 697515764 697515787
    0x201081b131d130b100f0311101d0d080405030727110f0a0c02040e0703140604260c07090f1802010f0e0a03020301050124090b03040210030e01092015 66
    0x684c0200a525120301400c3c000c550100000c04401c0214800d003259005408034904021101641d424090200b040320030300b0070400d4140c6980141c02107010b680304000c10b06142448180c030701c034a4202c1505441100e40015600c1034140b0307004d4075150143c20040c4014006243c0760306440c2c64078110078028000b4001c044d2a040146c00400160361a07040c01ca002c00740c1d590206050390318068892515801c0b225081062040702c0d05160255041d03038000c1e01c1f5a1030030b6503801d107940110030b20014410108003807a265642c00e00049401d10202c581c101c2d415a5500c408400c0507100c001c4800c4891814881407013131040c402e1400d010300544c1615150070002c2841012290307405401c3e00c5607407040c0740e51000005a00c0a22405002e81049007500425803c6500d442102c40c0d00c40c21080c04201c1807280822805002e9002e80c2c0c0c03c15812165803100c00c081d400c0880241440d0007900ca0740d5480c0907181d40c20052180e080015005a104181c0656403c80c410040d1011940064808480c000c1102e030300003031f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 697518264 1250 697517014 697517033
    0xc03071e0e120c10031401060806012c10050a020c04021606050c030f160503060f040603050d020601080706030b0112180f03030f0506090c070201081b131d13 69
    0x255034619169a4401901000510340802c01803916815048461124a01d060100024400c0541814140a485000360300c050525005109010410009070049603c03a0304c20b80846410200071150b02c407038050600b00a5807080740c040f664070320501042d03041d00e000d03d000d8400d5588600b016000303040706a15040a20029600c03003c5d078422595008500000003407034500c40c3c1d0303000d541c494072000d80740d14101c03d040f504030001804c496000f940d00c0240d8806140d005080f290b0055040d41d544064107441804a006420103420041c51409101c41c02100258002100f03030485210008a07030306244d0320541902101d103011029400038a8180180e03440650039005190413891980050702c000101e07843e00d0383d4000c0540c40803170001e42c940b000c1c0101d9181d40e0050f81d8000b01d084511074036608023004180c0c0319210303403a0001c0c1480030040000d0000805601081185c03031480c0c1880f0b41d54150170810301b4800100d03000d6240980c0c0110060f5407150a600c6920348181101f4204030340c0030f0219152040d44 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 697519514 1250 697518264 697518317
    0x17070e1f090c0c23010f021c020c03071b0e090319080144061005030102130e06040e030315030709050106020d180f0b09030c03150117030f120105090c0307 68
    0xc07003101c8503142c0d1020911407210000b01421b4016210320329020007903407618401743d5118295005009520854402000300e42034580e104144400c180c000c070341c2e5001e480d00742c0d40c00172000f40813240030450006800310042460860b10140e0f100e6148007030b2400d0f9801da0081c081c0c0d41d5a00c0f00c0c0000700301220f2044010070880b1500242541e03084c162401d041000808017250540607800a0741800440446036814601414080340298104804401503216022952050044045e1060007185003504d2303030f0f440400341e902890103803030392407402038854551180b2440120f4000e1140f190006070302200c1d4880ca0b0b040c1e450943c007404000c4502e1100310307030000180c104c1d50340a1103905ca0000315201c00e001d4250060071700c644540d40310000c2c60101403c100c081e5144600030b40110200b42c440c0720b001c0c1c000c0da0554001c42c0201e0709276400e040d03109240d4000c000d680120024002948169104034940803812100110343e402960750750039130241e071b240c081500c0b80c5c00490b004d1840c11200300d00c0300000398039 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 697520764 1250 697519514 697519553
    0xf05011b05030d0b011701063c0f090e0c09060708040e0f0a0c020105091c0c0b10031103070b0d0504022b0303050106050a02030417070e1f090c0c 64
    0x10811850301d5081c00d40d40b00b516410301036542c400314140c4a5810903c1c410a000c40c205141e81c4c0740d85081030140106c580c151a40b00250300460542c1822907000d41e10042c0346190040140d2003000701c14014005014828110f401301e040400000748030602100c440e0711824804805078100f85046051001681106008661040c01803101081c54005000d07124842c49103106489014240920a03c0446260f0107140e03085905000c2000341c200000115180c03246081100403006a80744001101c41402400c00103002025220600c003018541ca0008010b407402140c140750078039100404c042c0e5411880c400e09401e60000d1012070610038072070f400307242e00c18000f07062660410102e04070003680c5640845042c01c0340b41d1082000080c10b505105c1c841c0540040d0904515281d00d440b0060765074081c921850031048560030040c2c5041c0c5081c4000c800414203019510785500744540d42ea160340d0029075042200640b000700020380a519070068107400031940c0c5511a4042c8140c499610b404400700c01100c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 697522014 1250 697520764 697520807
    0xd060f0e0303040804180221060102070f090218100f050715050702030a17060d0f060b040903020d0e03070506180103110c0705180c04180e070303050c0c0103060f0501 73
    0x34105014001980708034820a81d03a5a101d04007401c0451100503030721340c074513403900c140510011070700c150919180141c042d02014a95684402c0101c0c034062041e0407031100030910f900000f40d10b41064014102c80170400c20f11a00c04031201c400e0264241244080303200040c108125900c41e14040c0004014040c0a080f006102d04055a00141911020340e16040142d0001803541d59051703100040d10703c070015803c00300041b401e10a00141da585c0c0c01d0603010f403100d27101c10031034020040b2a60007031081030400f074420b00852045040194540d0880002100410001c4040d20038a24000c140742059800050550303051500d8040c14841c8500b45407030361350515030707690f041d64194000b50001d8200444000c00030700301e50b41004244151072442902002190025005000429415038292410703920b404507011041100c0c84803460182508800c500042d0217800c0011090580c840020074500824104950145000300011802c807415032041110038000d0000600041d841150303051f110740310319074400303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 697523264 1250 697522014 697522031
    0x10c0c031a0f06090702030d1d0d08010e0702010e071202040b030610080f061b0901020a0f031205090a0c03032610212a0806090601230d060f 62
    0x2001c0c0800304240c0480d1100300040109991039002e080b980f103001501c5074060740c1005175029659001d014800c0180d20384444200c1940500468418071980320401214186032240300301414016085c020307403ca0101d4000000c3e2510f0050242c40d4003980c2440041900380d05d0115500c200450031a01242e000307840304a89030055a003005414000e140b05620010051702c3c103213009141c591804101e500c5600181c0400040301025500c4d002c103a014990384075038170810203004134117000b19a0340c000c0011214600c54418154000000c0e4aa00c001d074200304100d80380e803c54242d1326140325074014540f141106c0c0c00e10000b449041288001c0142003640003007100b2002060920b0003003102c200b40c100700308560400c9072041074520510044c01e075891070741d080a050384581e00c91a004914100e1000d400d0340400041703110100f4044000c108076020380301030341800360000d40ca488003803160000c42041486201200070040c0d55070b8801c01c03001405403c403001e0a030303a448003a00780109080c944ad660b80054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 697524514 1250 697523264 697523273
    0x1e100e07021b0a030b0103080d0605090103051f4a010b091501081b0403020d030c0c06050f0417070b040e04051204302f0d030509010c0c03 61
    0x10140609a503030040d14041940e00c0b000c014445422501610500c08680100f0201303011490b02810b59030080c00c12552080700e110841c4c05054240d2100781c01441340c000000c1030040100b06103e04210341c3c030040d40d950511951072802e0b81e25441251000c0400542d03a5030441c0c0d81c11442d000020f8040c00304180e02d80e6500c4000040001002c00d140069440c1d04010000b840c100c840d440c1e000d01c400c0800108110500002411031038000c000764104240120707880707101889142502c004584c01403811707103500e44030314006054581c4510300700d0b00c05200c082e000ca8210300482c19650303c2040780e204181000d240110541060345a04503da03203d0040320b4011a0001c0391000a00c013806024240c00201c0c10035140449c50011030841ca0404000280300078403020710813161524207542c3c00101d1910f000c40e5142d544414542408000b8003150900001344a0400140840341d038081c4c040c1c1d4000c000030072043c280074401c03480990013000a9003c1002c0720581d0b0151055103901c1d4000c140c00d6030b80079160360320b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 697525764 1250 697524514 697524539
    0xf06050901200c090c0427020c060c090915091504060b0a0917010603030e01032c2404050304032a06020606040506030a1106210a06080c091e10 63
    0x200007a6500842c008907100d00308501466000101200f610740381c0b40c5001c200b6050f10044494400c40345010721030100c41005950180d2780701089407415a1000c0c00c0c215126042c5502c41c00c80395010389007544c0020980d10492006004850740a030010b56942d40310400c0050b116003524100303074001da69040200e1a0340d40040648161a140c1c0c1f50200c603d400c000d51010400300c128203102c40c913810440c1c1400060752040803424008820f080206e000340345c0c1c070504404021603140c11901041103a000342c1410300002043d6240070102c070346c07069071b08500c0180d400068804580c041c4c0303e68003c0100300001048813111005d9801e64003540f00465001d6140e04034540c07015032100005074016030030301896180c281300301500b06508a0003080d840c002c40c0d81d0310f2225040486014400c04000c160501400035942e01c0300440e9540028202c51450035501420051407903005e000c2141c410607a0501803400c228040501880282d40d40740e640c0c5c00321218280071b0b070301c0040114041c80131308040004d484100304c030b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 697527014 1250 697525764 697525817
    0x1b061104170d08310819030c0807020304061d010903050f0106050901140915040b030a030504031101110723180f1b04090b0402090901030c0315060f06050901 69
    0x30003a00c006040c16100801c20080500100a040c44004a8030380d5100002c0c0d040c038030420099813040b107004240c2403000d0715010300091a4985513554030b881a4041e4581d110441c0012075441d090718989803c1422a40d900880c0204008909070b108104da124289102c407a050308414034103030000d81e449640d8541840c01815210005a4440c9402c1c803d42c80c111007104e026000103250b038064019140005060004041c140040001d00f00e855000c3e292590780026070000c2000d03049130341460103494002c10950044c80251552030704410f070250304c0d41c031403c001080a98407000070040c0300e0402000750161142c580070a1589011030ba42401161190310010310b124032415901e07122031410301d40c2c0f5441c52400418009850000c0c912130b96107a202c403000d44003500d05a042c005903042d0400c01090091007007403a060386c005615030001041000801d44241030703e20424460034030001600300f60080e81e0090080b5103002610b000f00b07000380b038401c2024190412051500c40410130071241103440181c3c101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 697528264 1250 697527014 697527059
    0xf0a030606170d0806010c02010305060a0b0c0a11060c030f0d20030126250e0c03072a020904020d0b0a05090d0c0209160c0618020a061b061104 63
    0x140584a03806100f07001940140c9031904040c0c1c03240c50624002881c0394010000281410b0b034030004242a0307201c02a00401031311401401c00d039280c1d000d031540c680c0e8007009001181c10310324061882000d418034000b56010f03071040000071410321110541e0314034581c104465400c100c81d6502940c0340180c2401d010700121401030000c1903565410325407400014451565003424540307090942c40c6007102c1c00185075641e55034507403000458040c0c0c0364030f8107a00d0540c5d500c201003482d2800d003440450b00da000d005500680da251542d6000d0441601c0904041c201090556034002c100410724015051610109910500c0100021440351043d03640031413482d019a0382c001d02d66a01d100f00512040c041103000201d1403141000d0f8030040c1154001001d14600500e010180d00c0340200d0790106c24003504c1800aa298012814001c28104582e843c00350540200b0903446450300140011348036004450340101c1c60751042e2000b003100c000d5124038015261039102c04031031000420001514840e40203410788201100d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 697529514 1250 697528264 697528289
    0xb18060420191202070f080f040e0a02090a06021507030b150703020d12091509050c0d1115120a051504060803042301120905010b0d03080612010e0703020f0a030606 72
    0x40440082843c408101c55011051042013030b4404580c0030841410400c0d8003080107665482d002264103918021588100122028001801800e04041d0040c1c08604815a022401240e030b41c81308a0740c0b4407212140349004850b8401054200b03200303030010741c05014007400442c0801e807038085440203540182400c1d8010303000f49103c1480d0b96405102080b40159100c0180842e105649507030003880360050081580c90754402c804010480c09000703003c0e0003030009220b40240121170501c082040d4041200b24443c0e02c40000346842e5440c15001c0d1003005000e032198040541d5040c007003000030440640710030740c0c3c006c2c4510400c45a40d03072030003200082d0071a10081c0d91110720b410324071040a45802c080d5014180d010307800b6951a648505400101c1c0c4101d100882d240c0d600d41011401082c080c06070a401481440100e8240f6400190543c05910309881d40c080b580405c40c2c440e400c964108681c010503402107c000c1000d0300d4030110b80c0050b2040205010140390340c075074440c402c40c1d50030f601400503d0700 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 697530764 1250 697529514 697529557
    0x105041a071823031c050304170c07140405040c06030b010915021506061206090703060b0a0c031d030c0d021305130302120405061e071202060a0b18060420 68
    0x800c100e00f950141c140d00908415900c00961001070341900d040c8000c2040210010b0144680340a41c0c880060a8400c1d0580c1d8a66010390300707071900314500445003410307d41c8540004605040c4a00ea00c600e810648a83c2c05a0038440210702901100c60400c1c10054008008900b18030200c650322841e580c130781c00400c600c3c220b0048040850100824151007a00c00344404403551002e00c090a5100030110f400704456a9000025001462a074001d00b568020104011340065041002240401e00030344841c5180c1c0c3c1039000320700503201c4054050b90507800c04003200b08181845149402581e2004242c4a00029103141c80b40c01c580040300c640d409100240207041c140341d0180200d20b1040d6038860040d20301820312010070720601c60ba903086d05a01c5a940c441c003248030489030666001640c801e00c040380c00920010001c0d0303550800e5404200e40da1400307032181043e1801c0c1c1d6600401c07900350204a0f00b1552450100401000ea84012640211020341c11041d1090003d0042c040c014014082c601f0703140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 697532014 1250 697530764 697530809
    0xf120106150507050601030809060d060e010609050904150c030905010905010504170a020607180518060910050306041415090322050102100b0a0b07030306080c030105041a0718 77
    0x11070750080381c41030100c01c000d0300e4085500400d5040c103481c0c0280100303a54441c0c2c1c401003855031090091200c9503c6c82e0507008114000c83c6001c4a0403030b00701d6aa200c40d00394441c010003c803101c0a4800511080d07281e200ba56a07011503401294498116050006402c000c5803101425210030b0312044070f8503591007003003004008101d0781080b00440040c0388141001e042d514007a5841e440580f608040c07204c00c006031030b808004c0ba20900f029100203046400f182c4600417803042e8454094540d01e1049280d03c0016400c059031010780c41c1211030003801000a512552141c981d2820012a116840d0060b0701e45150110507468010703019005040007036560340a134000d1000c035020203024110242c03882803010801603900087c4e8480203810000c00241e04900800002c890000c0b03940b00f6803040c43d012509505254040c2d00040403280303043c0661f5440d12000c4d00300360803520300700d400502c8035904a000e80500003403030001c50b038081464140510b11510301c0c2c2d042c0107640125444522401003044410b0b40c002d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 697533264 1250 697532014 697532039
    0xa090f0c0804080a032409021206030309010c06020706060503120a0806034c0204030302011803140c01090807110f0301050f07050a0905041d0d022a0f120106 69
    0x4030a841d091419003041d41d1640f5592042c0a040410907484402034207422401e54400951343c42030f100c000c41165901d00b40c0f031001c1d4010070010b49140184000141e16801d011089138a0000b0580d01d11221182d00d41d5900001d4000001c141c035103640ea01c40c0425141c42c100200e10b03000c0c800c68402500d400c1c1c008801820b040009195501a4020b035149030108041ea070071004800000d1120307002880d25440060507030300c00884200c480c121180c5983d503000b18903a802481030328003950003480404009446000311030071040d40100002c001c04c010b100e0501c510030280c9006030a000010640580c5038840e8070b0640c10280c01034031000305420b036409103898001e2310215421002d400901ca5860000b41051141c480100f00d03c0c1070000000d1140310280c4100c90010160400a00400c2070071560145000418100d070b40b01c1c1910b109074840c00310720500010f1191a09000d600a6800030380c0101d46058446442d40f8415401170700342e040c1c16007075549101d010420b40010a0000a10500e8646980502e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 697534514 1250 697533264 697533281
    0x5031002040302150a05090d0c060207050105190c1e1505090a0b04061d120c120f090d0204020c0d0c060b0105120a0c0c02090108010e07090c0507110307050a090f 71
    0x2400d204110400068039001542c80054001000540c0ca0b01050001603c1d05d06c01c41d10815402020614000b0130040818241825202c490b421200210b4860f00190344502c115060f15484030180e0302400c01c610320030b6103001040c9104411103072a07003124400c0701141400c00d0768101c0d5a440c0141d503d401002c003034480c2c00d912060841c003e02d0130355000c0d19811320300d0402810180c24103895450041c00c0d907030b40082412000708603504407824a10145a651255000050302c0c103018006c20512082c07201031002503600f0000340104442c94903014804110040344104003c98001d6028003001c0c480240c240f00b506900300482d140d00400c04078a1800d40d08484489064038180303d4107000320350503404001c1c0819841320007524002805c0d0b0400d203058078103000d01000290306c90280000805c0c101d8043d000901480c01c940100c03004030382c882664201361800d03449901c000600500c0140081801400b000690300c1b809000d40d181140c903000419a07880e00c4e500311000d640e4540449145040c00d6101c2c030113a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 697535764 1250 697534514 697534543
    0x1206090d03051e0604110415020303061f0917120d020309160b0901030902030708030730050d021c1b021005060f0904150f0e0c01080709210c09060503 66
    0x5954404000f40202c021020384101e000302c2c0d4a8024a140b001d039007040360060501403408038031403d12a400295254001c0312110300500a90a0a62410031400707041d809010250b2600c0300071600b0f00301e180040110200e001c0740103100380510003941c0b0700694010b02404100c080f02503903900d482079003145025800300c8017040001414130104449581da805481d43c60500b4600070803c00b415000103441d00076590003c06980c00005089000c01ca420804010f000700c2c080244940468030010380004488146001d801240d020010a001410135600801d003402541a40a552060130720090044030340117094134546d90601780d070000f48960108203011241c04902401c0c09a0b281c40c0c004140402c8400507114000c00710b940c04182042503004920090004a80d81040404140c602c0d00c0b003d403280b124140e40a0003800b0340703041c85511881004d0700c540011703240c5403140c0303140c00d01a01d01950110400401c401259801c000003079410024400244981341d800310741107003480d081600713058402c6400790 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 697537014 1250 697535764 697535791
    0xc0b07020708030f0a0314090d17040807030302070312060b03010f0e01121b0e0406090209070c0302151e0f1b0a093b040b090f060112021206090d0305 66
    0xc10301600001302c0311a01440340c1c40d45c2d203440d140e18060307019040d00a060075500d509081044504000001d601040401d03507552a050040030000d105480d0070309a90150602d081040442c010a000740c00600601d8443c1c5080300d078a8200c1080981190031941014851342c000000410011600c145800064141e0081e80c00c40742d40b4020410000803941c80005003000180709801042083c130000030401064048030500f01450586081401844044022841041b00d007022a0102e4400c4064a214550540090400c8070904140049a840007400001c2024080c00c0a0381c880b000c034007a0a0041d45500115429401c0c4420346104540b98109200314011050010881165000d100001125142180c080da02d221204910001c9032006103410100c00e0200d0700c0103440c0d02c2e01d4003080d1040380141030f100415124004001d85400c0301541240c1268020801884200c80441c02c0074890740c4010034102c410b5203a800c446007084001c82d0030300080d400540d843c41070150103001c0c20f84c3c040e050207540d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 697538264 1250 697537014 697537019
    0xc0c0203100b03150a1b05190305010305060a2c0c0405070c05190804050901150305090706210219050406021b01090608090703050f010606020c060f120a15060c0b070207 74
    0x25650013440c0300454480d06128041003641c50ba59101d04200080a500001803611004020f012030303122a03140d102007800e1021000c0d45610910071207040c0ca9015002d0000b540f42c203e261005050b2103002e40c013032400301c903c00d08480e0030040b0a08101e03030f80b4513000d000c0c0b02c9041e0041000f11440148094103000e41550a14001038020130141618176000d54102803664031070400c01c44500840d00000d411901890001c40e2207810200c80c8007940150b0381d001d00060361100074842d11001541325080c0422a0141002c04e01c2080344080f04661407180e0b00103042030484484502c2c000c4c071100c640da0119100007010b02c000c3c1d9060000c0306440c2e4108a03001c0709104501d00080c00c89403284103400802c40c1c654089981111f05102c00001150000c00700c2e801c8088a5003080e00800c0300d4401c3d41d01600ca007054500a60074110195a001810500e205041070301c0141c012403810f02c002c00d20541c1d690380301c0e62070310000720705500080582a10f50701c5155090703542c03038040103488018ac0080255482407404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 697539514 1250 697538264 697538269
    0x30b0a05180f18120415030627021905030f01151205070201090c0801021801020106030c14030a06050c03010e01320d0503120a05250c0309090c0c0203100b 68
    0x40340c2002d1500c00303084003651040e040090301010303d0b425a40d01e000300c44040d842076451201510945100800d03850007000071003c2981100d1141c8240c00b8280701070680400691245044103400f032851a10162a0200e00507030440070407000d0150318003140000c42400a01c0c158400b100e4003620304402c0050460a400c0405049a0400300f41072507040e40791000100702c00d200790402070100340d2001c80d4100741a1941c1642d03010b90800e010b000a5040542c4550046600c1401540101ca0304445810b40c0281002d00c00302c550f000d40142c0f10f030148a440301d07600c00108644540c42c8200c0451601984a505024084e80e600c0c4040c0d211482103481244654041100c1c2c60031100c900702d482c01d6900960002d80c0210b90a02c0d40745030050150300000c43d110618845540d8001d200d000d0f550010080c554804e800441404400324030f00d0800c07122216203000c01401103400b0710300d10380a030070142c818a0380c41008030b0503504400b02e00e0000030b0000d03400c041103040030072000c80c0041d4100d20034007104445001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 697540764 1250 697539514 697539559
    0x306060813020f0609030f010b0111150c030406060e160e0d0812060f0d030903060605090c0703050306040f0207050a02090c03160e0607020a06020601031106030c0306090a1b030b0a05 80
    0x1c081c2c49515450260261a03544804070b030014100075082d2414000c845814500800d61003d0390f9000c100901c2d485001500701103100780202000c0721000403d602e4180d8103842c6908020710840b24070b41d4440002c90080300d81c1c40168824000d400344101600c080450007800c031001081954000c051030700c404000100c41e9003d44070000c20054074004240d45020005d001d080f0b90b4110345411005a0304424240341c0d202e40601c0c1664081c02062050960f2138003031104e41d04045030010004a018850040001d12440095802400c024008220340600a010038101e90003a24116800e5000707544100c11424440c80c1603510012040d075060440c5404400034203564420103041c41084001480c0350750a540b90f1065583c5607801a201d10a01504d030040a560303240d080c041541c0038a071206061780310f4540001240c0c45407840145190031626a24103004071503002400036a001034941070740c0004078125246400c0b01c00102d507804200a1500d0b0207000b811012034100c01e014010403000f40080444108 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 697542014 1250 697540764 697540801
    0x40f171b0109140102011e0213051203220e0c0721090612090b01080607020601080c0d062315011805100c140102210a0e06160201270303060608 63
    0x4400e041541c03d10740040340100268183c0030b280c910314450701d14464190b94090290780408030342c5055034640301c40030002c209144603260300a0758810400d01501140c540c101030306821480c07042c002915143e051200d0356150860b4407200724400804c80da014040c4130798040c003411804000e00e0303d410200c810014005a000d000304000d03c0f102a0785d5031207400560b488203241542100d0407000d00d58403480c0e5661600004c0e501c1000500c191800811114000309002c0c0c0d441800074000c8045081603075842c000f400d00a1401e02d50790b10124226002c4040240380b03280b09144440302e801c0d00d440d0313a9002500c90340e07146a919599848855040c80b0070f840714460031041c1502400c28618402003460082008000800300d0300b959400400c001c140c00300b00906103259010021205400c5558a46d5400115000140c00d0001c661100340410810480340c1c07140000f80140388000f107001920008603130f1742191110304d44070705100c403c4100030a143d45441040e0183c00c4a14000e815802d086894a4021039100d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 697543264 1250 697542014 697542029
    0xa1502030a3914070c09110f032214010e0d020a0b0408030901020403170c0c04020c060f091002041202090a4505010504170a0903030e06040f171b0109 66
    0x107801c10b900c00d40a460300708080d80c0c610842c07503990215407405c2c0e030030034403a81308003022a414610808021034110741510500084080381500f15514012000c42480708a503114201070340d03603462800070a1001c2ca50b284111050000451801400090745161070887e00c8040e086400010f002c9000410301c140e2a41c226800240b00c540b02c6d111680401e0092050b680010441c07207040f0840340304600703a00048d0860f00343c80000d5410140004040c04140d12400300000415040200028503a00e1542551a00300c0049412583d415100000c400c00301d80c001e400c030310071030b021202040c02103103004c00003d507104440e070b00244031162811490880070038140a4100e5506880741d0400c074200303400703482c0d606400c0d4402e0b6100ca8021b624200140240800e80303054130417100ca1007540000f010300b442111b807110419512014000d24645085400d0b10340495841d500040401000814845680c10701c0b028003d1600302551080010396500d20300014030b44190b03d00d01c4078840b1560580c1e00105103500301c03000c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 697544514 1250 697543264 697543361
    0xa1d1f0c02030c06130608060303130501110c120309030f0c0a03121106070e120f070b0a03090c090617070f1403012904060e090d0e030a1502030a 64
    0x240d00c00241401e41a0a160f40c1100000c11691800c1040980340380c04c80d00c6c01d0f2151001600e441090540341e00c18001003424002200c1070070050340d40714642c0b122407a01d0440603500700c913101030002003a000745250000e0580e030004c0307144501c903e02400740c501050500b000038610300d5000c20100c0d20080e0b4610002d0300400c500101016403a000390400c0703002c1e400c480f05840301d42c9000034000d0000c00c0c456a0407401800c100b8035882a0080014603280001000401000d01600d040400c40c07403640140c1d842d1081585600b1040005119600c2e100c0c0075210b100b901082282c180754403502c445a602102c80c25581c00318204002802070142d42c03400f075803039000078600c0b00a0b01c84d0100f409420740c40181e05170b1a2a48228425409140d90a000c800700111014869250b45100f10f1001940c1500c04981030340000d901b042d40d040c095900e500e0090405019603504135081c1e180d8960444c1000814042e0350340000c00c10001203940e20555201490380028800000104258961101101c8682d205112807 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 697545764 1250 697544514 697544537
    0x405060a031202150f060d0809040f11030601080c0403080f18030a03180807030519050a05070308030a06050604060507020904030e030a0524061309030c080a1d1f 71
    0x160300c2800e101031500441552040c45189200958070f600300c2004010544900d004210b070621011407481c003a04009100040340803083d20342c801c40fa40300d050441d80c40f03503070b4048180350000180a2042500e14054110b1b442c1c1c030f130050016244640c0100a4034286008000a000082d03081080d03440e28403040c0c24407601c07045800c034003506880ca04a0515410b1054201c00d004056004110201c5011000c1c1c0614046590b460318a91740c0110b804024000c6c2c114144122a01c2d002d070486482e440e010b5400c4910b1158240c50702c03828041103800c26140702d600003003013114850082c05104010b0009542291915140460003461800b82880c020f2281b12240c000c642854820708101d815038100800395030b00b45c62249449691150002c0700714403581400d0720000f501282101e4018460140517141c0c00c80c400e00524006c00504c40c0c51001c409104010210801041c40e0328041e00342034105440703805651405c9600003101d01c3c13041d0215032144049040011401c0e042aa244107040c140d401c10341c58035039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 697547014 1250 697545764 697545769
    0x51308061e1b0c01050901060e063706080108371109070c03021216030c051005071d0409020109050f06040b0a0201050f0a050f040f06140907050301061e05040506 71
    0x101d03014601405801d010807483c0d004241035000c00c0c02110010003c010b005d581b409036150519044420396800200c8800c80300040b02021800c80c3c007145100c1000d9448482244421400c8107150040e400040c0d030140180000d5100700f043e0418414802980d54880710f00b14802c80c0c0000c02a050071500c02000011442000f8102d0007480e07501c0f0000303050640600e81a0b000802940d502c603000d6005108401c01c0c002e0003008a8116a225260303940804a414902e86043e9540c5048403c111190700c01c100d070181700c03c5541d01c00d103401000c0a40c0c444d07515242c0341c50410011400d00b505213208134501000340300182e800c1a6894200c50042d0345200c1010443c10004a141c0107507405035010450006401c40219410340c4030500c40d10403100071020a40f284e055840458004590101d00c002c10000814003181c80100b114074058031841021525660000701140d0740c00b016580700e0b22652080c1c1050106160078060300002c4c02111080c81300b00c00201215010002d1a40b280c0e600072507481c00400c100b0b8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 697548264 1250 697547014 697547041
    0x30f09060702030d050d1104050d12050c0303040b0601080c0310050f01020102070204060803070b10210c120302060405010606020c010207050f01030905030f03150402030601020c121c051308061e 85
    0x80d034008040d80c44130100a00007500552082c0c101007030145c94250a034060f00c001c0026101900c1001e80110700429543c0e0b0b951040281e110010300a110040c4400c940f001c60030001180325500c40c1c160050b280c10000005000b882001d4220b80e40c040f000c0c070803c80c00c00b04400d480c000f1100308840c1e100201c40150010313402803160200c042e40207810880081014840000209640da03c642001d004503514032929050000d0380d40240b001c42e0390010007010220351f00300c003807000c407a00580d4200c001707607903951604501010050003103004d41c2040c0204170a200c0280302d42001040940090110003201a00003074407039240d4010540726142c0c064240305240d200c0d601c003a10185e440812240da80c020640244c40c2c6400032190f02d03160700800002811141001e000b07803400340c50103800404071114484100b050580303800050341028400d00c2c103621011040c0039084501404203803501c44d80c41c00340c004000c100403415045a005c0c0d611000c140400c0303d800002c13035680001d9001ca0407100342c89005039030040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 697549514 1250 697548264 697548277
    0x108041509031e09080c04021903021305060315041401060c0f0f08030106200102040509131b1205010612110105030c04092310050916020123041e05030f0906 69
    0x880600d05540d200e1030700135a040e020384031000200da000d101c00034108400c2c0d10070281500654400a101c100034240030b90040c00b0038110710210407250b280c40e600400e406800440c2e0000b4034031845118648241050b2007002002800020b01c8560340d810f050b005090101c0000000b00085092810401030000c0c0502c8561026407044216590b941d4528009051011021440c0804421003e1141e00c1800c1442100c1c102c0c1e4029242130810390350300d81c03215140342c040307202540c2c042605844540c1408101c002c04000d4040f110041d840034219060030744c01c42d00542c02c030010380d4031a07000050110702c0c100b480c4110701c002442d01540d00e0303807090000e607014003c81c1e09c82000036040004461503910240c1d0401c0a0502501b084086569a499051b0542c1c809220300b81d0000700d0722001c901b03040040d506d01c5030280442d000118550100c1601d00ea1800c0e01d02201040d0b0740604024042003000c010202e0300391107009009400182540d88869883e4458108018801900061041c9403610b0b1201a03c49 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 697550764 1250 697549514 697549547
    0x7170405121e0d0b09090f0709020306030a12030f06050405010e04060c11010e07030b071806052d03091204060215310302070f08030f030c040f14090105010804150903 73
    0xf1183c450300450400344c5107210490741304404403000102071a9001800908968842c0000c006440c07070040c55200a43c03010340403e80500612054202003150741c0c8120321012015500060401d22620649045400b03030b821262040303040c80d0042003068010a40d141c2c1154110724001a00c2c0d4403800103886841c038141c0f5201695003420107200103c5400b03d429401c60740101128207107642e0790382c0103c5100000e040c0c50600058842401c0c0700562051010b0101e031103000050040c0f03402d86000c4001200c242e4441c00c01c15200000401c82620030038407440616840c0c003040c003810036007042c1003c0c0d110500b0110402c190920540050541c1c101007403205000303142c1018200c240da4880146028010b00c2100640c0580328002c80003414003032568402c0c2c22141d07140301079428200e29110701000c80d480544111200700d000e02011885610040705034008181c0c43c1b00d007850072030641d014411900c2d0140c2c800360602201e1000c000c082400a901310b07905030f480351400140d5551500c1d00380c8800d24110750406 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 697552014 1250 697550764 697550767
    0x301150b1c0209090a0501090516020d0f03020c0115080f060c0738070f110705010804060f0c0c172107140a0c02040b0306060d150e030706020307170405121e 69
    0x524241a1b82c1724a0588070314100038816036980a090050048000303c20400591054400f0700340c3c28412200c400d4043c1d030301e2034090b10f40010a03070804d0a507501c00c3c1c3c242750200d190702000c1203611010415024200d80c00c5001c0c00040c60320285403000e0340100000501003040500000c0310140761081200d520f02c00000107072007c28420710a910b0203242c21240d440210f02000d44001e812406036542d21000c9010340c0003442130f80d062000465a0f450054012505503480c1c0b07105090400c00c6002d4414850b01542e125900c1200741e0070040c499501c80070710310011000822403251003480c0350032440d0400758010010225911400d03c22501401c0707510364030682003004141025510740c401d01c040a0180215400c2c02001c421100700350b16101e06942c0c0d079038450003240c00200000d2440031807481265030030b600040c550480b03200160955012207070440312294000308101410f13810440c0380e2208201c8182988803031801703036103003941c51081c910070086040000c0346107400c2510360300c10100030a41081600b0b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 697553264 1250 697552014 697552021
    0x2060601140c070b12061905120f060106020c101106040206160c0905100824040c0b030c1207030c0e0f0f15030114150901180302040207110301150b1c020909 69
    0x480858100c18040303480f15096102081c40ca11f8081d200304d504020358000740510a01d00401c10441c42c06402c81c0361100d014400c0c0d0107110032418015940284101d401801d07694003403100f0410903002c20101c036003c0c000c62810310003c500b00013174480c2d402a81a076400d0f0341d80201030280800c4800c606002803110344424008940f5584540285000d03414000c07030040d4030390b03d4600d0642c4072031a0003000034060310242000d01001501c1a031340341d0018090a000c20259851b074151302019801242c2d1803850324400035291750900080850994043e2142c5800c120700414618000d0552301038210441c0b04209107400d0100d0303079986881b81b040c0044001e10f000e4000c0c00000000400360001d1007400f007a034032905c29001c80c9080900d2200e101200c65091f052130001c0f60070054517150b00c10040d903200849018000300040e00c4620041201c1d6001305003200c1c207201c2000c00c140c203485890590804a04021000704582c03840358080d92071000c940309568400310781350f00e0700078001d00840071000c1d440384100050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 697554514 1250 697553264 697553279
    0x4080403050d0c150204050d020d0836090906040b1909060f0501080303070c060e0304050d060e0c030d02030f090f03120322080703261f051002060601140c07 69
    0xf40791205224421000c0144404007581040703008500c5403d40001c882c01070100140f401d041020040c031310650f030b1181009142003241c213040d02d0b550442200b500801c00b4050403511b003840d5500004904643c030100c0d03032030300846039602d509005c0c00c0184040c4c400c00c0400c9099991300081c40e40503190200404c02e2041c14244000a41520030620000c41d01d05800420f1035040803049900c00c0c0c0941e2a407031540001030362800020032884000f131926020511000c0781c255a592031090001d0f0080c0d00218810014101c80c0c0e090001030b058040c80781e40b00614500c0c5607a0084247c1d00b00305071801405444101ca0b0000c50750740c0e0f007942d580c41d1b4036000b00c0c2040c000301c0d0300450145004070380001d5130040000f1011405002c42c42d5260020709140d0090140600007840341c3c0b800c080140150300903106100204e03d1801020006640d4030720807019944042040c030307062107400750041c41c04640ba445460314255001e5140c4002800442c108001022a0303001c200440c030454845d901e03918101c0d02c1d1700b41d03980d64 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 697555764 1250 697554514 697554527
    0x180e0d050a08010e0601050306060f04030204020d1a0a080d0509030c03030a03060f090b010c02091321020f060c0d0c1b2402091e0418060b0f101704080403050d 70
    0x201100802c0b03100d0004210f641035040340074410241030315101e00e9070f21030318100001c6030842e0f440380c0c42800713042002100584890000d00b0b0842c1500c940402e040d000c07180c001e40d894401c03100060041c401060b04200203880090507a108403214100390351b40301e6174000440d040c406180e100ca03405110001c1c8001c841d9074940c0c045021540c51084414801c0c1d01e135074910701070b03032100f6201b50700146a5000c9200546003c82c0c129800411410f911050b542542c1d882c0e480d440035082c0d1601d41c00d0046014418900d40602549240110b83c002a040a18000303071408014050641e040c50190341d50401d0001040c013920401040c90444c5015881007030326031401d10701c6204040c4d42d010f01c100700d2140c1c102d03046810303009031030788000c3c02016803152840403103c0703621207241da100700c82d401500c1c0c0506000700c40c00d0b00b2140c482c150040760045160f14025040c0800c0419039103180b4045c00900c030f00c80100582c031040321030030621005010700a0b5183c5040080480c09650400340250054800106c100d036088070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 697557014 1250 697555764 697555777
    0x19090b15010e12100c1106040302011d07120f06060503060c04050a0e061f02010f0c11070608090303010b0d0902040507180602060c09060d06030605091b06090109180e0d05 75
    0xa80301a034248a20041c001e4034800c0109440301a03201d08403640d02644d0a03041080c159881d0319150202c881e00e4a40507142000c156403d0300940d5581940b190f200e0100071209a80400f140010302c00c10745403d42003180307038000c050090945408062580c0c100100d0b904060002d05000341150f0480c05c00c481c48400543c850702c9124071516020780d00040c48001304030b05620800c0014080741c0070035034501c0032010742201d10510f203045550305c10701e4110032a82882006e1054800d640ca00064203488682c45150200c0380e0012410321040f0010007c01c0c0700c00104603030550310240703285a100c6828640c07130b2000d00302e440c2000f0b5100c0d04140030019001c0c0d118440c01e80108400b0441e0504950b1a18166116031069480340d0f1406401c00010403507041602c020400030b0030b105800246c16503262240b004030340742034484444a800000181000d01d040400b0003903010f50442d4120b140401c0e920000c0c2a84c100ca118070b455003201d004184500694230340c441d5056007801c40c182d40d2019030036440288240d01c00c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 697558264 1250 697557014 697557017
    0x7060320030403120606020a02090f100503070609031407050d03120209210c010e0109051203090a0b1b150a05070e0d082a190f0c12110102060f19090b1501 68
    0x5a000946c05c0c80081c079100200c1d00030348100020307203d49031400d9001030700409440501c0c1c00c1c1c0900254981f401c0190800801c0300c2d1390f4601c0c02d076040d407401002c45d005c0c5898001a951001e0014040d0341d80d040c001e408010fa25045c0310355080303803001540000c0e01801115591204462040080707501d05840b101c2441c0c04070200703403400320f03000c80010346108460340136076800a01c4c4440c0034801401e00c40e65005190043c2000c903401d001c02e4030001241d0f0003103038008660b61a408100c40428510b088142c1e0325901e8444050580b0101c854603e042c400b50040c442912191140d02060041d801282c46001c50300f405003c0c240703600e90030304190070340c0d0b4804000142510404031401c170801101903006c0d40d40d0903a45025040e5158605034103410600e180d801641d030440d12022240c00140d0086040c801801c801c40c0c0001078040b039080c001501c0582e001d07074a065402c45404c00c1800ca00e40d003200759110656090b0b942440031070344031010007082140070007040314807045c0c00d2110482160380180f15080e000d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 697559514 1250 697558264 697558271
    0xa030b010b310314032109070504020c030901020c0a03030f0305060616050a0c05010c080d02070303020c0f0601080d0c1a040501060504021c0f0209030703060902010c0c17100501080706032003040312 87
    0x1c0c211426980d1254010264100703820701031a010401c03040e46c40743d402c0005407003241d0340307562036900080899002619080b843c0d400060354203c41d5805200d041d4020908960b21002d16145460242c031003c40030740d03440f00b095607a8001032215500c2009071103445029148000c10046245011541c620605400344d0f01d080032044c00140c82d61052500070b4a00758800381150422a04d20b100a010703411854003141410303020301001c2001c6004011003810300030003000401155140c0294541002039854042c0308105030060b881003c07800d5035801c080802c000a169030301e141d0b0b580c14a50300610a07a00030f56805400003d045881111b0130041c81d40c4014195410440501600e20788012481000413260700340d005404d04001007070060f809504660f0060503c402000420756075031b8140b4549070031814030564100c4c07400d08010810884400030a40d0220100b02d0f81d410280361550f030308a40d00c6643d04060f2507501d00380908000d0012134007002a01d4404644a042c18074006e0714036080d0741c040904c404d00c1c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 697560764 1250 697559514 697559543
    0x60522030518040e0c010503040204091703101202010f0f0903060203070e01080a060f051504090203010f081006060e1504080d021f060b04060c1e080c07050a030b010b3103 75
    0xf42440b03004d0400305000e00504a1442801c01503e15800080c0103076402a5540c0c00b41c1c010a0598120160703202c19038441070307070380c0c130702452955020000c940120001423681c0c655000180d03000400010a80c2c82414100c00c0200c8191040319a80e002d070708000c01650011042c06000b0741c00580074480c111090b240d102580d030f03032381107260f00f210302c80c0c400c4042802029404000038185800b8a05008001c034001900d416116500d040c180d034020b0b44401c1c2800f40f051420028a102881100d5a00c6500c6009111851600000030441c14141100b144641041c1d9803101a4a942e2400c4500921203c0c0681c2c00c03813084004003030b403200000a9040580c0001040c40990035180b44038090a5841107584c1c681000e081c81c908039200b1704140c034200c0309100110022403002c0c880b004001400c1d485981c80b2551060b21681283c14890254801c6000c1c481c6001c1c00d0000400003030f0282c0c10359106800e2152903e458201c020072040c3c41811442c5580603100c960758807120561400c0013600c0c001d9800b442d1250 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 697562014 1250 697560764 697560769
    0x1020d140f0103080a020a0f0b06040c030209100e0609091815100b0a0e030f0c010e0609030c060702030109020d080409050c09131e02040b030609010503010507020a060522030518 78
    0x348121a5100700a10707000051001480b10703405406000f0840c4121b40d20034189a481100d09480d031001925091007003001c002c0d8500d02402801581c3c0280d140550400440c1c0000c01c101c442840041c1d814051200c513416000d13102c12094503c0300c0002001c503280c0d410f00c2901c81e2000c0034030803010315371401030380d00c00e2944882d45150580141d902541c01051603190411003d104d4206071b9801c0208134100c00080d9640e5030421510702d071540714031b01502c080d0402600140035814988003d0340285018806404c082d43c02094a0b03044c036000b0b450b881c0d61201c081c400640180001b5134001d500c030700b580700743e482072181880203001a00c9449004200c5900e130b0040c83c826034048d82c10600d40c03000602004441048254200c81c541045031a000c0c0b203c1007801080c54103030b1704140c1040011301c4000c401c11400b89440702501e80100000c0d0001c000c14180000000d40300d42480c0c9000d8803942d107610204a041d100c1100c00c1400d010b01074010344d1110b4030343c940100158050660703c4002d0007800d12454030303071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 697563264 1250 697562014 697562051
    0x150d081819030f1a07121b120207140106030305030f060924030709050c0706110f07080f070203010f0905010f06180f0608060c09100c0c090515100201020d 68
    0x10501900781d81c80e02451903641c5100c401d4010403c80b42d68568407031107201007580101c4035018414540314900c0e81e08402c070380c1908880c0b0b90120f142c600350790200032800c0e1542110468005800b2303944050ba442c0450f082040b42580211a01d500b11740ca1b040c000003d040c4c0c48000355000e4804800c0641141c3c640c00c041010300001030b1a0b041101c0880d80e0070400524004024500701c0002034160340081d80e640090008860003218001d104020016200b02009694418280c2c08e00301e0580303480c140484942143e016000f0301c600100644070008011006003096011f4504c4982e00400a1001c4000040c240c0050640000700300e80c6c944c00c20700000c00703842141c0900f00648002905c00c00300c000030103a500010b0440700e104c144110707940d51808510501d040c0b107024811050701241341d6850340c0302001e00135482221520b0381c0c10400c400b9a001c1c00034502c10f0106040310140500842c0350f444038040740c8954500e11401c5d0703030b2005801c00781143c400d030103402424191034000304c01c201442c145054074802 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 697564514 1250 697563264 697563289
    0xd0510060311090603130c080708190b0c030603030403080c01060e0c0c0a030e0d140d0221030a0906020906070605040c23040c0e09040819031a09150d0818 68
    0x603101e042c42289502e0503c40b01455000c1c1c1941e440500c4401c803515420a004288e03049105242c115440c20b1050400c02c02684501c1114011048103812040e10780d0503c00c5006400c940c1025000000b0a12555080069a000d10b801c00641a03079040c103000e20030f00030701c0c40d48070319003501541c080012440b8200320143e50602c4604400ba04072228203035000c45d01c141d008a509940401c2443c520f40106501142034003c02907104001c1c000341e40c503c030019240c800c2e21550146010b451200e01c8030041c0d01078060342c0c7c01a01d281000f04503100c140c41d01d4030181c01107520450700a5804100300060016039041140a18080e040b02010340703403034103545042c0c110102c815130a54441a910300c012070609a0041080121a151040901600c44001541d50358280c1d41a650781e0b03404240c8103030746940b16050390080803650404101d595541c5158065070000300200500c6045900c0015050701520108401c0e440c00041610300705c0942d9180910302030304000d02c4007404410541e01c0c0e009034248061030758003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 697565764 1250 697564514 697564541
    0xc0f0601270504030318390b0d271101030e2a0301180515060f1e041b090f030c0b0f0c030a080106081b03010b090609060d05100603 58
    0xc000740001c9001d006000054070480802d070743c1d10030719061694045140c03402c00340700c0c0300400700302d10301f42c1501512030304c01c2c0d01c10759215418060210207003d40c1e91400700c102d800681c01c581c6c48002160080004106002c4904140d0701c001215012521074150b0810342d80384142e501c0c10107551494011012500f8900c817003c5213502480700d0912150105034040d8038050a00c00c00340e03061a03000042400e4440c42e00c250968442c484011604210040c8116141c40c5c0f074a00c0c002c812440d141001481c10100f40c80c0c45801415a0b501c1c04416007200ca5180300000c001502c148030107408040303c03000e00402e8442c6680090700d902c1010032449000d0758980100da42105102c040e49083c1410140780b030340400e10307109070b40d00100860f00188000b88060110610252191390043d0700d856006803026100500300303106400030030092980201823100b86d07030640d051303416455207860400000c50110312070400b8540d4080c40c0459140650303241908124032940d19050b401512542c1d803602130b015260400d1100c1d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 697567014 1250 697565764 697565819
    0x7020604050601141c03030c08010b0705100c0e040501030308160302030108060a150906030b040b0a05070c11120303091615051804022215020307020105091e060c0f0601 74
    0x10000d0303130314a141c452071a0000d10410390008104031030401c500d0350241c11004a40c81ea00f0f0041d0140c2c1180c0c03c50f0040c40700030102d0b450609181d5850740c4500c4c0c2e1410b0340e08505c0c1c1e101d06a42505104012200020a0260040003103586a08002e0064482210060f814000302ca412100c02441390090301c1c102c40c842c0c4001c0186031140304001c0007030440300c040101d202804000009411815021301c2c80194016001c034100703414a800c3c8002859001014021030500304014014142e900049a030b14503500400340040c80d44280c0c00003003005030001980e00a910001c400c3c050f440601141c2664410604518a0740703680d500c0180710809450f000c441004500148199403500c11540b503c00446080200014545000107180d080884803003214503201410114080c0501c648504030180c82295074001181030110544c0028072601c41e201003207011f0305044040c40c0c0400c40120020310b444000400310303500caa01e207c405a40e20311013000180c100b486881c0c00092080c1f045001500c0031110301c80e240 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 697568264 1250 697567014 697567019
    0x2106080c1c0809011e0903150504150506030709060602100b0d12080a020d021b010b1905040f020705010c260618100504020a02010b15040f03020925080601020607020604050601 77
    0x4411680001e500c0905008941e002e800d94800070480b480c01c0c0b8206500c0d205012411420010707031403a1188e6200c0040c03460041400007044098003020030b07442c080440401c10799181000302c0d0405460368003048005080440206400d13030089000035100c48120410440500c41d00108080c0e0f004001d005803c2c0000c800f50400d28034851801d07039a22480d10180540303001d00c081c0c41d01c0200c0e805a00d25482c807000504900d003011034203001d00143c1800403120220305400151031426003049030303c5424400d668a0003030458510b240e03015658000c0d0004001c01640005080c044c12400d0f0000200302e00c4140480304154140300c0840f091b01414000c4c00100c8001d895407654180d042d00544030b8000d200503404002804c0e56240010010007495900104010750807005009050700c0107070411145000a000c244810507442c030292044030780407280c04401e42c0300c0300015050801c1c2c0c40300072881d0701056000c0300001600300c002c8500841081e401ca0740b01d03984204080303031620000d844c018001c2d04200b004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 697569514 1250 697568264 697568273
    0x10b0d050c04031e0302010b1507050f070f05040e07121b0602060919060b0d03090906080a12230301140936120408010b120a03080a0504032106080c1c 66
    0x400004c1e034403e000000b60000035a0018801003c600014603807484001100740c100403050000d81e15100708000184005c0e42004403d184034800341c0034450240c0d5035050001001282000740400801ca22004026070b075010b400d010598a0b202d501c0c042e16404040703400102c1a200041c0c02d48120016809000f8011010307080d44501144580192141c64640c1c0400c0d5a580d2681d000503d030b103102e03840341c4400300e1400c10300350300741c0d82aa4080076450300483c800f030b030200390788070380c00c0408041a10f005458440d50f2940070ba0000302443d4003060500d004400814481307a2540400e10514044410681680c0c4043e45100d00c01b1000541d0f40015040c17201d0382c80100021134049841400e000d05480715217102452410700341c0c22903440310f18240c1d110b14100300c00303051085880e16050200c502600c01c1400d547c030003410000740030f0094500c07203642e00c0003e418140b08030000050301d80031a1700e004003810000030010140c034590103030301c07803d005051890b84d981ca4580921b1110030055403030880c1c1c030081a100c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 697570764 1250 697569514 697569563
    0x3130305070c0902120a0509010903022d0604060b030115060c150b03010e1b060c07150c080c060f0a2007020d0501021201030b01061403010b070c0806010b0d050c0403 73
    0x281141e10006802c0d0110782001280050000c0f00462420410217141002200301500d0001d0b103801202d916102460022a43c08140d107440c0f0009003904141c3c5801c490408010540c103800c0100f064040c0784280f20800030030b50050000c2d07560071802403000794101c08a440c445403441c401c205c081040c0103503000005400030381083c24800c580000069042c5031001203070030b42d102d210000e140da41001c01c1e10403200c88805090780700b0782400d441d07681c00d005540d4011135a440c1c1034021041c840340b54026041d0b0562040d140080d600d541f02c03208035120b403803400c1c080350380c0d0005440f90a880a0031b0000038980088611441c1c507407441d914030b8558500740c0c0341001070103613001500c02ea80010300781c0e144002140c400d00040001c0401c0110301d4200f507156040c4448024810f03003004c01000141175100034000364000c10399042d500203d03881e03030f660300c21071400d07203030290165103d4600c0380100781c00040c03100d40788005000c00c1c1d40b00b1a0140529614085100303203600c203e0200408890140a43c0c0080c0340c03a244 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 697572014 1250 697570764 697570777
    0x503151011030313151a0d05010b10050d0b030f1002090f1c140309012021090102010c0c02091b040f0305071508100b0a03021b0609010b010503130305 66
    0x4003400000c2400c0c01c0d050460b4004c1341c030100140d146200c0a0304006030f000c090104006040000c0100c07030340403030791030b43c0340d07002c01145520804842c00b4800a1041c20341c004403058074014400c45105d80765500260464102c00e948003611450314460300c1c018200498503401c00d114410140202413035650020b4000e41102c07803003d4005800d4494010ba41e101d02c3c00c10207190210f0300c280c1000244919082841c400c001280501d15001880001d07101c0c3d800552103010729107641c0d011f00d41c500d0304c800d00614000d503285401401d15500e100000300c180340f20f4000c0c603c8010070390081c000c2d01d80307418095840c201200e070001d40040c64400014200034046005149007004038003020716255540b016241c03070300c44940080c0c8140d0010a010060000c510310719000c140b046007461607141c43d01000d080c3e81011030f44240403044600252a20510340b0a43c110350b40d600040c102101024180310400703507186000c0b03c144003103610b041c00d081d071250301400543c1d200e01803000740e0854410349a07808071042c0d00b103031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 697573264 1250 697572014 697572017
    0x1302130e060a090507081207060f0e01050a0903030b06040803190302041e080c090609070305042d050708210904110403080307140c0309091905042105031510 69
    0x90118880c1a1418072005005140c01140820920380b6820013070704000081e4000f4880e030340030440012030040e034502900c02c03642d00040001114505100e2481c003810303903d004400b0a501e80010003808480d40da0002c0c25550007960b00b00898000d450610031244617601a69005900c24044071a5121191a03030b503803042d1503440c3c054101596030340c0c0400c1c51807a100312040c50001c400014400c044041044d400d800c00c044500082c02d041803000304400e104040e2060080544600c0020203100d20341e0845000f9242c00b82ca407034040340000400c05000003083ea0222514001d158000a0ba00c0b0002a003540c154400e4a800e11540400b02d1505a141d110f4102c850f040380d1904019330840b42504044c000a5000d65a51540c0e450444002082c0924103015803c03070030700c1442091046440041038400b04081a40c0b07020780d544480728010443d401c0d800340443d04034100f00070081040351304654480d041c203030030007500c4030711030788a000b561240011201075604561040b5450304a21303107402c08501d001001e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 697574514 1250 697573264 697573271
    0x180b0a0f0e06361c0623040302060912041a0706060f08010606081501020d0f0c0b0412031b020c1903170703021614010503181b0a0b1204020621040501051e130213 71
    0x6041b0000d02070b40d0102e8043c0c0260700400200500d0103030501c1007401c041d0035810940d140600f820180b048220380364000c0c14207601c01140d24010030800d41d02c0300000e041714405000c08141e668800501a0071640103d42c00140308030042040c079040c5010080d0301d014140c01808208450b444211440d059007485002002441c10070500410354840341580503902034505440350514609001e41a1030841c0050108448a042041c0080d0740c080703000020f0200c21a0103070204c145490f40d510060441d600064002441210610a0a81e0400080207a10b00c20340945040c10b032b66410406a0554501c119049071072000c2c40001990b01c9503000303540c0114190501c800c0d010b209111301d032403c80d180201d21010301440f07084d5112071412034104401008000c44562a08440000000030154040c1000b40500d1020440007155210b8000200c000100d59420002d80c1c80c0c03e0900f540600415543c00c00305005120042c1c141e02a02e02c00c103072041d0540c0c40c640b06104510350a0104103001b590801c1c990696 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 697575764 1250 697574514 697574561
    0x1e03050409050705030703050c030403170c070c08060603010b1801060525030f0e24030402010203040815010e060405070203031503030d0606180b0a0f0e06361c06 71
    0x40c544261400b40f039480e92030507181c1c078101d01c000d011140040c0000347c11aa040c02000002640140b682d9a10016524048150f031030348150208503000720000240f00742c1c1c0d46000407403040c00000b40e507441041308400a0090f80f0505042c041c0c4405118484405480c000c4018016540983e0043c460095003080070500d1465440c014260b041c06a10110000b4501440341a02e66504c040b4070440d02d403007124083d600c00107160100c03650014508801181100220010301503a00070b0003954014542c0f101581c400c189007664034a910342090041504003400080402c54904040c03240e98818000768005604d503803542031740f840d0081045c0c851154035200811040c0c1c2007180c203004103801854142c07142040c40121941e81c030100c50003500052030b5060103000416020340d01c05401c01d4500d2050030301090b540300e01c2c1c3c0403d020b4403403842c0c515040680401ca00143e165070081c140007072000c2034038014207001140100005c1035100000d41958900d45d00486001c03c0ca9544000031140090002800c07055 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 697577014 1250 697575764 697575779
    0x1507020d08130c140a05041104050d052103010806010902090d0618021906020618190305070c06050c0d090e011715010801050f091f020c0c0a030c080d0c1e030504 71
    0xe20700d42061201c082d01c00524140c6051081e814001b0303281c01c0b14144003003205e00302c29041602071441903a100380d111030181800d0140c1849000c42002d100c96840310180d2101e003800c40765034800e200e5207009115900c0001612500e51081e61080c800050000100a002d51508009000c00b00141c1c8c041d2010b0011080c0107a07511182074601c130b070b1601d10310030159162500c044e050040080c081403c1010b2005480c401200121701000855010150113030540303028241101c603400b42340c400030603141044c000820840d80200c0900100000300b01107801c2c00e010201c08a4107466140306d045068ac0451005010300b200761529000b0284407003084910004201781e500303034009000c0c1d00413102c503550f500c00d0085906240d1381180e4450000d1000348000b40c1d8913684405034422081c240104d0560210f12044100810701601088001c0145680229903c17400d00b54841201841010454814400c04c0c1d464140103060b061886e0390810f00d4145684440203400048140f9054100e0030400c007040f0205622 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 697578264 1250 697577014 697577033
    0x914011209030905130b0f1c080c0a021f08061509271305071413141828020a030f03030605030c0d1515080d111507020d0813 55
    0x2c0c040e5680c912190314103c18000d84000030413041c43e08170700381a101e2886032242800c41448003415262103c0c107929014404a000c00140d00082180720005004554802d0020b40c10307070b44500031100088805103072501d444900c2403452904010810600000d01c19240802c1c07403012424511544628005025000900c900f4400501c00190b421144003501040c43c461a120740c80040280d90400000351a140c1c550350314100c0c403820070481c06005407081e0715264a03d040a0110010800b80200780c000d103105041346808484030010f1007000c0542581ca03450010b54100b02c3e507a04540c4c2d561104d007125041000403c0814140d8000360781d0f10700000001c81075604130300d84030b020390b0380010403034208800c040c205400035080130321a481c044d500c400460482801040901c69040c0009500c901341c0403050740c613030915841502c05003d01c2a6290540b80c101075041d5420240704207a407000f02100c5a15408090b040d14100c0c0142e000038403c40503203026508580e04100307485141c1c4a1500d985d5525a001c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 697579514 1250 697578264 697578281
    0x110309100302030916051c030e060309010b10050301050d030e0d0c060507110d0b0a09060b0303040b130509040b0708041a07030204080609070308032d15030f070609140112 75
    0xe42e000081100500061042c41320f040e544043c9108060319140001d9044007581d9184100b21400c0e5200f641010b0040c8100b040405001e04859105c0c64484c404a0080c501070206501800050035450a107510a0080341e040e100c3c000c0c084011074403944c408641030040440f10580241d014010715010409444150b00209565554299108160324142c5600919105202d004122660030b1400007003c184038603910071140c1500265040960070000c010b861611810352300750000140116050107070100504078501100e01d405551a92035003070110a44080f20083c107180d000c407001c12082846030280b141c004d0700488518141d04507494500c14024019143c8801180d800101042100010702c05160300039045005007038858503546413542c40e0302c802080c00c05030b081d0445810200001d00e0b110503409288035200301d425440e00240681100403003c1c0814401d101c0c0040d140d541d900c00160340c4003511000d548100d0f1561400988070300c4080307a404107506004030140c890600c90500c1c40390307060 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 697580764 1250 697579514 697579517
    0x1603021809160f021507110a0204060803040501110c0d02040b010504170d08090d0c260352031803020a12030621031403040c0914070804020111030910 66
    0x244880380b80310140400800a60310003c0d07410100030341c0740c090f1600107010f13030044590604a490b803c051140504007649035000a43c460310b094400700c0c0403100000a44113031402a00d4445400801d40c82031a5681400800c06501040300001a40141010b80005490801c103040c418101a124490f8042c4002c0c0c66080040366440078020030212039100700c0d880c3d000100c50b0050710000e85061750081200803200340c09010f800c03441d103000b54101855070340c40600c2c8045900d43c80e12424440d0001c000d031b683c025007100c003640a04c442e101304d40c1215004419920a105403c40d1445070796101203a000504503d402d0526650303004860000c0405900e520116122741e000d030141c0541880c204c00c130300110f05203880c00c0626151040c8120151040201c1e1200e0440c0300c4d62911128900e01124080604611006409400710602c41002612180c18003a11402c81051049c00105208103240710000c42e9080300169010020501550050b09024019100310094074076102581010808000b0f000a9600 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 697582014 1250 697580764 697580791
    0x60d0c120b1f0509041b180b1002010b01050409051003120e03010501060f0f081005030a03110706020303070c020603090a06180c1203021f200301090c03051603021809 73
    0x24801c101c2c103101220541c00125003040d540d0400001c5400c60780300400051280910a11402c0580c41c2406400000d044014511a0480c403200708100941450f00c103240c014110200c5c0c150101d801800f0b5040c5601301a500c160a0920706400318020b0800580081e0503407080103408404900b8400d034500124034036445a101060804c0181401c44005034054410042d103c40d032200701a5001c0312201080e80c0d08c0c42c010078191901100300d00709192170b1780601e0307141c401c0301995402c158010022a910141c41019031305501d550b00801c0c5d0b1284411a90440040e5245030071034010310b001e0f80070b5a0001040402c8462030001c664035102100e10528907542620441014031040014401061000e024400c20303141100c0310340c1d03601039aa40041c1c6031345c14a01800b010300e80c840075415030100c08802d02401000d50300101d009048016540300b801921142070900300d050b50414001d018860003544100c0202d5012110760200720b000b07401030b02ca2040081c590b0308004031250380702085140216080104034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 697583264 1250 697582014 697582021
    0x830160f02130605011b030e04022104030e0117013c0f08070f18020a02150c0706050105032b02070b12070801080a0503030601030c0504080105040b1503030f03060d0c120b 75
    0xf600700020607061408840305c06d11441b001a52144243c4090b0009417000b507192106450403100040d10030050000355901c1c1800c1109150340440b0380c3ea64840c0a0320b4a0944280c0300c405614141401d003d01141c081060508404107038001c841d0200b80341c14a04a003035900d40d90441403d00340394592025a003100b142c203048c880280244414030044c180701041c018502d20f84109043d110130107664541c070460b404145040010300030b204540518030f4940c40d0080074644200c2442294209442c1074588514007800411542400130f108030071411250070059903001c07041030003d204441c5850510440c040e5590019140880001420728040101c1c100c5240385415000100251416480300840360b100103031503008218080100c940100e8203103030108890740341c10b42c142c034a0320895100e02910744c81c000030002031210324130f00301d40150302202c503110301024410f042554078001c1850f8007500c00c4040001c034140745800c1c0d2080740311901c240f004041340e540c1c8242a05407140315000c07d41d210328400081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 697584514 1250 697583264 697583267
    0xa080403090609141507020a0b03041203060605071202030d15050f01080606270603190e03030709180908070b070e01082202130203010830160f0213060501 68
    0x40703001502241c82c02040035850107011405481101809174018900480c1c92a00100d00c1422204d00c1600903081104040e50381403110040c0e48211415903c4d10140034205003081d02c2809040c04607103050391040c2c10405c140d12216101c0c002c3c0222081941b100b046921440c642601564481c11000320304c0c0300b992440c01c003d1001c110201501d50307040111600800c0025943d4070155001d44000805c2c00c03050034682100c1070141c0d0360400d101c643c0800d001c8104100c1142100400d0891208130105028141440c200982c1d2800b00380e54000100e440da01080c0440d90582500c91121080500007081e400c0084e10b5400040e0300548c0195401c01d00c2d6401c2141054100410b080044000c1c64038201c50b182483c003102c805403003034000200442c90300d0042004d642c1e13460f9010b44c0006810340115503d580d200c4481e80d032081c0720b07002c012041a680302400c01010802880700341410500091901c6d00b00408920000301415040840e00d40300c810040c0c4003d42c58451a00d09903032002803000580e035051400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 697585764 1250 697584514 697584527
    0x10030201021b060f07050316060207050c0102010b06250b01080307030807110a020d02030a0c090f0c1b06050c0c070e060418210c0203030d020a030b01020304080a021011030a080403 79
    0xc100c0c42000040901842c0703511820112201e000d108500e03a500c520507840d10a0861207000305c1008030309010004001130203200e81c010108544510110b4568166003c01a1300340c6881c8010f40c1d501c01014880580400580c1a1303072b02d06900d058540951081c9150b40d40700c1444020b0300300c9a00c43d8400b148200416800c80019a01f14980c1d0920210351011069110754414444100901680c858540082152820001c40140c80d600200c1003e150b915000316400900c188460515001d0400711000b5416004140401800f0010142a0300b092099100c2101404010f404000c810750100450061200b0500c00e0790050144903070a40d026040020410054031191210f90041840813901000041c0020040c0c001141c604c0485022040210345c0640e9112003c15020b50180000101c0d805505440e5001f0302c068486514108604d080c0880120b0340d038022400b81d080543c2c40b2015060143c68010b031480480c0c812841c1a184a9220602c0d9a046030030000c000004a1083d00900c03041540144 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 697587014 1250 697585764 697585783
    0x141902040905012c0906011a16030f09050402091813051e01060501080108030a20010c02030d18020a120213020c010c080a02030c0406050306040b041518021602271003020102 76
    0x80001311070511540080e241c20040c8030300008814085c0c0ca0b40c54551034030080d2801c110110b08200396800703450030f0141c242c04a03020540006400008049064038280c420307074900d00b10142609040f0b54001c00a400c032650b0103000c8809003201d00c281d81001074400c0098000a40d4265050508880c0000c0003600f07440d00c54116038148000100188041d900010654550540614001241c425003c185103030f1582c0d442101b8180754204103c280c40150004001c0c503c0c10b60360581003200c50100c115880568454020003503000012410821020a01010100c0b80900042c100c0700c485840c003107154101d030b024406050459444200c80e6042e1a0040000395000c0341038102940b542c609401000e180f031280d030064800f4481d011011034642e4031960711050f0f40c4840500100141010407072101342010300f0f0f20855500c1c210050b030550b45281c41e4000c1e2540c0188100c242d03010200160700304406000248900c003803102e400c2d01ca400c00368002d0f41c81540a8840341655400150540c00024101003421 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 697588264 1250 697587014 697587089
    0xa032a0f1d06010c1403040f090905030a081906172b0c080706090c0e07091a0d15060305070f020304080d0c021f0306050f0414190204090501 62
    0x8900401c8040032484041c20540d00c568140541541c0d041c006940e40701d10342c0c80260814400310780c40e07030384040004014000e580d04e041e031560f0082e50720141c103c141d5003038882c01040ca8106200210441d409400016084001c4a440c890300c280a40a154103d8105600c42400d074001b00b00640b08444040c841141101000c06a0a2207405d0000403141160f503003501d020704000d0307010070301c40c1801100c1c4261070019074024818000c00c0c2d0f003820108041354150080304540560341c1c001c0790900e03000d90200800c5440c070382c100a40c40c0c1301071050494150015240e84824030f844049400400e8234020313150000d4240d0380c8000405060080c0014400e501d0100100c0c150f40c0704102c28800d01200048006541c24070f0b00e4540c03c01071041c070100365800420f1b40c0d1101c90440c80e60070407491030b805400000a440050f101140b10584ea9420081038540e4106000c03848a0503001084c0811150510500350f15108039000d490140e80322100000c0f00e009030301400e2609443c661500d41c081c41075189240c0c00303045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 697589514 1250 697588264 697588289
    0x150201022107090b0f07021201020703110304060f0305060a1e060201051005060d2a080412030515010f110709061a040e0a0c091d190c020a110a032a 65
    0x100c580905083c449018207060340c8008202804440650400c5804036036028158000c0c110154407041d020390884d44085012811102800200d041c000058404889142c1c0e92000b03c204401420b40050001601c13444c0c100d59071003404101000400400c1c003519820f00c1c0340f010800c1c81c200c002803c590707000c2c040902000403c3c0c42000039540305c000303558410b241314800203401180320f0704900078043c144075504138010035101035840c140c0d00803402d035109500400340c05001100c0000d0850480d9011940d8081682903031070288032551003602007440642041c2005000b041c121150207180201070781c050241140c6503031044c4054108041c40c411580815014242031070304210401c080c101009000c0201c1e243d403007100d1090b00f403142c100d1900801e05950421040300c0f03504210480483c1c2100c0e075140b119034a10f802038021950388103000b5042074a50141254401c15901c0d038010403800d4181c03076031000703803c0f43c003201180010804404c4002c04030100c08118940b92152218802954005d080a010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 697590764 1250 697589514 697589521
    0x6072301021611030a0606031b09020a05030106030506030703080c010f0b030307030f05180a0303030603060b09061012060b220b040e190f0906020a23040902131502010221 75
    0x80200c42801c02c5030340b1601c03d01e104042080840e2070710001c00c4c4060030366070406c5400070900c28488252107001d41c40d40b200441194aa0702024103a105000601c000a88100b004121442c0b095000940106004094440a0b90740e0b45910603140c0100100659995669582000662040c0300c1e0103000031042c0c0185050031400c0c0c401070300c1900700300904800c1c4400010044507502194050202c44c010081c40b240351240c0742e080c001e00400180c00101d441c180b0b01103d8912506c0c00b100454403030031004002a0311401043c80c1254060701101d00001c0c070300c0d11a903010a004c42c5c41c20181c54288000b0b4031140f9031340058601b040034202da9038804507a2441c2004107009400241c81100d0b4016005401c510030b9002ca028510020721600104591140c85d206045040201036002405070b20340c0c5981c2c84120409039010307200b802108901d0011505010007007000940c0090300a0034009000800c0711002e1542c0360040107001d00c0351a081c0300103035800203400e160004007400388074104105000d11010352a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 697592014 1250 697590764 697590787
    0x1030f140f032a0a03110a15050a0c0302031302100c060203091605090114270405070f080f100b0307033e03031c0f0c08090c04050f240607230102 64
    0x42030113401400b00460f001088003694410000d864070983c0c032060380d51000e5600c2011000908041e2070188840b810008000e007802e11074001c0c2c90041010f90f180c48610000c6d80c2c2080f80b42c82010302c10000b42f021040812000c40d142d413000d58440d44000f07011701040c4c000c110484082441c0c607000300e8401c0c2000300040c8890740b00344129a079400030aa8284e05c0016440e03580050f180044050340c1881d418030810007080007000f140d000c0482d1556400301d0340b1141c9524003952607520300010f501c915845110440000c500c141c100c0000c146014003610112500c07502c40c24048050180d08101c0e010030410b01f00c44080c0b400803002c6401880000a100000c100c42c0000e8892080648004040c458204040c02d4210158840190035074050010048000c0b1118003810545040b40d41c0b84c4503008269034007006007441c0c059a480380390120b8850760650354221341e4003841c290f41810485065440030032030300d0507118800100340b01400f9200404040304158108a06440c81c20381e00703040d43c0d006100c0d131103060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 697593264 1250 697592014 697592023
    0x30307030921061a040509030c190f1424010303080103151d0f01060512060417120109022706030705070312020708210403050301030f140f032a 63
    0x5a0b80c0c424040304001180c4070702502001e1000020301502e103064050307440000841400b4411043c01c0d81d090103140e43d0061019147c1c06140000b03022a00719903d01000003928040101c02640300e8141c044514000d61110281fa800c0040909001da1002486a840c042c4070440701800d070321f00c0015180e166056903001440940e040c800104036210101421500c0307841c6400031107400e007503003100404c00c08018001c84d541d0315842541c00e6a17940b8007000459070b410302d0b0716800a0700c0203060040c420703500c1d2070f07075403c8a90b0a80087c00508000c140b00c0340c0318641204080174020400c407100942c0b00c0304269112184201e54400801c80007914094804c02c544820081e05d41c8400142002c540700c0c0c0b60b03420161803104001040610452000172040c0c100030428015040d00010301448010308100520f184660480554002d800f02e4400e100400000c4caa00b806d81d21080c0c420000740c1c03c07244c1000d4400b03103040c0d5540f03003c22048d000491880744404c03e025080c0241080181001400d170f10b6610400e465 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 697594514 1250 697593264 697593269
    0x150e06180304121509110112060308040b0a11100606090e0637030b04031112090d03030b03150906070509060f0a0207051003090605060a14010c03200105010509060303070309 76
    0x18014202c1070b03d000d004944490780d20403940e4040501ca4800c5a240804804554510003070204104008060314040d15100700c1040e20781c42002d03945002d06004601440e900301c84900c10805c000000001e02802003071104041900c19008081641c905044001d0124038640d005110304604810401c2101c0d13441c6220102f20351448035004440991503d508070042c0110301040f9035142c80c0d21000000c001011074640e104500994442d05614680703c08071362286000607203044c6005040c00584038500c3d1001c031354803609200c0e0500185400d103440109042c101c407059a641d09024032010041c4006081c00900d5110400345892494840c4040001d041801102020040344a0110720a41103600070020b80026100040001e030b00942801c0000b405045005400c550490415000c1049030424103580401c0c1d80d003682080001843d1b100c0111140304030403d003034040007485010004030042c0308909007a0041c038a07001284a41c1400140a0811005081a80654001c0040c000400e900c0901d0005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 697595764 1250 697594514 697594529
    0x15050a0c0503070f030b0301090305030a0c080609161e02060a14090a0807140a080307022e05041a0106020708010b0a030320030936042a03150e06180304 67
    0x105040201130884c0100505013039503816619002e061402d05820002135403103180203003800c4c080700740030160031030740580c080c3c504641102081c0e001c5007803070b4113009100c0503c0302c1c02c3c030304120300c0c00340c00c03281e460226210701c000d80250700a001844032064042c011200050901400f0b40342e1030a10043d00ea43c0e50850001c081c018460201e0074208108001581007a058800c50484486400034202030409a1050318014054481d8540c00e00300740c11440d903107003180043c0c40290400c00301c180205d0000383c00700410440e085600005c44141021034038a9881c06400307160b0040c030780b6900307010031142160440500303144210806841080041c2c0d010899003a006d11684103010b440c0d100c5e038509460360203a20f900a911255040007003640f00146516044000700c1c1c48502552200788403c042500c907400d80300030303020f1034800040d03c41d0f00c03803940c000b4205496071500004003a0ba881d2a9900568680e078480c000782600d542010480d100d00300546904001002580400c00154500399642c0748114400c159 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 697597014 1250 697595764 697595777
    0x30614160801090e031c0c1101140f040629150f0405010f09080d1d120a06051e040c0801050601090605040302100507201e0f040e03130315050a0c050307 67
    0x840068041c0f00f9148000050400321b9042d0711003c2c107140142010b0b081000001c0c09010051620a4050054090444081c5020501c64031840f0381c1c007080d0303180104251101901ca42c00c0d10849002040c00b105200080c8170248041080041081b0026850f41001e60450740148502651400c2d034a01302ca0890740300f400e041c2000600c01605070b038001010b61017100d0500901071862101900409541a011418450a0400c80b49042001014000c0c0030a02010f070f03101140d03201c001050350348180c0e0000c8443d40c0002c0c10142141d9104c8030070307804807412501c205d01e0050030047d502c0240501900100d003400c0016000e401c01900400c0da004611010b4880d003a00303001e102c521070103081194001074105001a1030350380c0800004c3e420107800ca4507075014180c01c0e404000111559861069002d400a0000005511510800001d0070502000c260140000c1040f40101c8800f02c0c41040118410300a907100201c0c0c00c1034110841d64001c010702d4503603007082c503400c2605920008499115409041c5103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 697598264 1250 697597014 697597031
    0x1c060c11030c071401030e030a0338010305151002100c0c081603031104150f0201020f0d1116140601060e0a090203070e04020409020705100b0a0b0d1503061416080109 73
    0x124064a04510000454040080d27403e079410f0b8181c000c828a49111160b81444080c1d805008180b560480d01d9904075030100c0d844040150300c071f504910f0b0814100051903038001e40700b2000503c0c4036480e25558001d0392001c50b141031400142c2c040d000b011081c03814164112001c2d07880c1d0b03c40368401c1040c04002001c114000c00c04040c00380d03020381c20f4071140e1800d0b40d454580ba080390544030417525100401242e8140f4095007124414001c513000c5290a529003400d06600c000980087c204081015407040014030900c2e44008859513404952400b880a251080603100b11407410b20206800c6001081445052100c240e29005400011140e43c1100160340307a40d64401110707071007504081f003079106000040c005010111600a02a000c0c0a00e0544503907141c2c1d61110801c8035040001e030754105403511020010030041002a007207411480300082401c0b00743c4900f00040d4107040c1c10444100780c0d250a0708403c1003882c4115644205c480e0185c481000040a0160600d64144a03010300c6a0300c0d085e21 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 697599514 1250 697598264 697598267
    0x6090103080c150408030910060803091011010f051e04050307030c0501180302030a020d05071a06010c06060b1c09020117070903050102040f05010212070b0f061c060c11030c071401 79
    0x404402602c0d1020f00300090405284c042065442502e582c4a1072007040c9956002a40741d100380b0080b00d4500c40150728101c20030052048070780701c140505052000590664660395420300030b00a00180400d4000384510b00351000210654003030b5821060700c108603023040001107000040303d41c1c0e990107081c07511070041d4a24140d40500101c2001d940023014010070340c8205900003000d0003442090f5000e80305403404150084991703008420001d0800f020101281c4c1824001c803d165030854018508a8006845502c507002503c02c40d41c0001c441003400906859940301ca036207043c10151049200780403d5001d500020b0204070310030440201140c20a0100d01540d014004001c0210b500200a54945680d2801e035003522003248078090250143c03413104420070f0f5000f0708440350b840d404030600c13104d0f449005e41c01c069101d000b080282c1000b107a4802c0d10300000603d0300000c0052107101c0c04079405080b50300082100e403501c0c0d2454205c1c1c0c01401140240a0042000030645d82183d4040d500900100c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 697600764 1250 697599514 697599523
    0x18050c0906070303090210110703120e090903040315060b120a061d010e090d0507110324060f0a0b090609062a0f030406050906030a060e07200606090103080c 69
    0x1036548036038001009001c258264000388000c2d070080714050084d00201105895070039500700041156007000300c080c00015904200180f400c41c041c500700074511100b0010481c41001034442264940c80032070100200094115001c40c03a044003941030205900d0601800514018103a100012820280010b440040541e000100402c0c00840001c0d401c008400300005005080c0644a6145410320010b88010f0000a81119460841c0d542d14501851a1030705182c40981940c225494044c890034030b822030002541000c80e6601c60203154181d0b0901504000a200e00c42000d030307000e00020341c4204044100ea0b000d0351580da4007601e10941c0e69440f0310006040e0b100f0340039681c40740000c4584a03101c04c034820004244c0101c0440c122a2500b880c0c088160782c0340698803038100010789c20440c1500604115010f0b41e0400c56404002c6203850300c6a01c01103025008445070400500c5503d420a00290b80b0b500b5003080c1e01e01c0c000034050608000300803860f41d440c14003010300100350000749001c80304400c20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 697602014 1250 697600764 697600777
    0xc12060f0d0b0118060e04080a110106051f02060610050a0c0204060905130c0b090a210203010507020c0f0a0803181203030709060e0402090a0611030d1104031202060118050c 76
    0x501081d2984c40e400420500103502580c104020310b400404164040324910081c02290424a04c0c3c0c10202004000c9030b140c1e82c3d03618890069500c0d03c20000b103a448000e042d1103d1480c04e980d101502c404844004c1c0b4010b001003110b4450782840c0340b40703221140c00c803084034440b402e03070b1030203e181c0032080c000300c2c000d80401c2d40401c0300c2515110070000001e60b1008580b041502c1102030390b202c555181006001070082d156503981c800c82c003143c10418180c1140704100003a20729032480b482c0320b00a4000900315001101e103d00982c1004010321520b1030600744100c0d1221040701c6812103e8240700000f40d4a000b22460312180560342c0c2e96815856a8440d03c00003407400250880c2d640e49400c210090081606114060225282044a5500e07141c14025600e150302c0c090302d480a458036140085030003000c0550030380801d00027009074100c518014007940309001c5403100340341e50703c80c51762900701100f0140003440001c43d080b41d0014400d84403041c2c1c2e48200c84006001c0444c0d9500c0381c0803181c1c414400c91 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 697603264 1250 697602014 697602023
    0x50a0207081209031903090b0a0c051509010b01090e1602012c0622022107090509060708091519020406030504200109090f061e030b0c12060f0d 63
    0x49002c1101515804000c0c003141c9015802d441e04068080d00204405840d070800030046a20600c0c20300c0000c80c000d015020b80d811a00c0e01140500a03034980b079040000e00b400006520800c0010400c0a40b400d01801c8203910080c81e040070b1035440d05041c2d8403203ca015140c808244203010101e06c44601c02d4205d6440f00c15442083d420078020800c2d1180c1c800700e032000c1840580a05400180850030090107915130034001b010b0f20702d265444e0f40c02c10280488031021a2103111860540003680001044200e0203060b40705000540360403c03001c3c5918204005001c80e0401c8030300410880d5040c0301041401e500a051001c0c518252070300c440c612151401d038070040603014404540000ca450b03242d00701a018500400284600101c5940200c003196440d940280c00302c2e010540c100b060b40c06d9135014140e003407080c1400161464030b070b01140130003000c3c04213001400804a0300c24001d01100c034030907980220310036081d64504100400c9048003490001c110724403650165151046a0b25410800311030640d11 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 697604514 1250 697603264 697603273
    0x18040902030d110613020607030809150a020d0b031c0c0f0204020a0905040b0409030e1009032001110a050606120307050601240206100b070f06290f010807050a020708 73
    0x580300030003c1c1032425148a140c0300d018041504034a03820b82071010f02d43c002e81420f103004c1c0c4030786040d646444007400a1080b0b100e4484a159901c01410b00140a00c500c1d22000d6035071103460301c80310241e580c4100b80910075048400065482c0030005003100880003581070815034a515410a010380d001c45410180d001030000030010715499000d842030003601c50032202003219060007401d20003119100c2e60005e011442e80c80a900c264609110010025041c030326001080d207840b0340e01c4440b04030000e48194402d4203d45240340166130000d5001b04a400110000d02d0384244d0b41d11240ea0755440589014000c00c12401d01803464071043c42103a0160750050101c7d038065946864009007500640348ea00001e031006040403084500c04540c0e10300510103c0a000c01140c10540c0380b24841e0b101c00400c075000c5940030a8030000403118001c603506c1041d904c000e5180404010210128101d5050070303288200c00e800c40c0c000d0540e80001003103400240510304152561050700d002da262607401e0b04003803d04d205c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 697605764 1250 697604514 697604533
    0xa140f03062b1a09031e090a180f2f180402030907210b0a0b030a050604030c0b06040b031b011808030403021314010618030c0e1005090c1804090203 65
    0x8040345103c3c45140f00084182940d12400344588a000702d208440d80c511603500030034024000d60001d800040e00041a400519684044039102503054055800c0c02540b0303010940080d07201c034424450301c1911401d407000901541c111404030365400701e909018040b0b01050315a0243c0710750354a040d806801070021035070707410543c00890341c2304014410424002604014402e001e44031001d0403580b80d901c8a13610f08691104542071001d40030171004590148554a00140840c9040141a0046d03009844400b0f030181c541c10700c180045002040c10f8001c60030142e0854154a0000d007512248101c442003c1c20240c00c0300049031007548c4071005230442c1d4170202020681c860040f008000b103910884204160035640600710065030100921a0f80301d000401c0101304a5024110a43c0100d03543d443c01d01e13041d512507480d0146800c01d900b00003a2480d00004008402032201002c0002d08000c5880d0a42880d000740b030008584900070081c078098848492141e0692241c0e001080c816038000c041d00d24860 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 697607014 1250 697605764 697605773
    0x2040b0403050c030d051804051b0a0807120c0903020f1201020d0605030c0901031208040305071b051c110d1109010905061e03100911030d050a140f03062b 68
    0x140103a220f4070a014400c5c801110501440480700d80c0000c5800001d952a018001c02c401801c00074050001001c6d0b040c0216030281c2240014603040d20350b07880742041424613160080559500c03c00d10403616140482250b0003d400202c3c00003140e074110f07041881c03207500c1c1b00458882c1c0147e60089000758004610800080c0040c1c01002c00d5070019400c890301c48208508014501d603080c880501140449001408418899682c0b554407034020b003001807404115a5410300b20040d20306600381e8981907000c0a00032841c3c1007a08a542d0102c0368119006581c143d01d0b04500d0142011400340b0403d41300f01d03240100806030707280140100008210360000c0d03958419000240c4012152684120321a4034000070f282c403010b5107030030b07040c03405070003413030b0070210130342c42d03000600320300701c06840310300607449e0b211f07241ea50070890080c0c40c0541d0758420703854003084540500821132408030b5007040b080502a45080890000a490b03008004651202c0211943c6d04111007410402d2002c0140c0040c620301c400511 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 697608264 1250 697607014 697607023
    0x1f02090d060b0f0105070c1a12041a091b090a0f0e0a0b06100c0204020d14130501390c02030a0f021305012303071d0f0a0509030406030f02040b040305 66
    0x49405403980807410f8042c0b001140d55106400b0000c1c0b8505910303800f4000104400107440c00203040440682c90990781c4148100000d0044608960114044041c0c1c00702900c450100b5400c0160030f002000c015140360200f900c0000d1040c081c41c02941040b00140744495641c00180144211510401032400c1d280c19054503129a00426540c4a0383d61000c10b000d428446800c0e0819040f40e1785c3e084c414002a0301308000f07035000340303901501c0301c0e01c81400c81860070006c0f01da40e0007a02d400c0410343c2e0800c01032805900703640d080c07056202540d024030400c6000c800300c1a0aa1003261400d9203072210201d404d402580d45c0c00030603402030f4043c0325844110301040f074401000b070341c0280215440000740020140782c500703a40090040034002103c040002800c60280b61504041c000c0050668002d9600c4500b006200c0542001542080f00c0201c280242d043c1400700c2d8980003560703c44240300c0c5242100c4020340e00c0c416882003000701582d400050703012030340b20b505842c064620030007403a54495990520681e80d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 697609514 1250 697608264 697608281
    0x118031b050607031403040c0518041506051503090a330501050112181202030a0e0312030609150904030306060305092d070b1b070e06031f02090d06 65
    0x1542800c0c0001c1203034900700050f600030720761640e0381c0054500e80d13001c038031800d07040544110340c3d250024001051656610304407003a42c21031174810030054646030600c903042039082140b11210501d010340030b1045484054a02034900d401e20b201310707600e84800200b41e2406640c0c1c0c102400e0005806103c800c600107028421000a81402103240701c05007203003200f4100c0c0c0082c4a42804114060010303032000c0d0854020248140c01c1040c00900100e1580340d007189d02008501d5080140c100044401d14581c024a00c400140b4007500201151a048481640c6511018020a110715139241c0024417660000010440001c0d0142110000c0d04140c500034016204074041c21003ca0700780b800040ca1050006140018980d41120b0040b02818103e4404c400656019800810340124607000c1072031a43c000041c0a443c424241c500400c01200c4c42c01c41c244420f40e08284185401c500600050355000640b101700c010340000b103c40048415440300c0d000f032040540071074000321100d44090600015600000c0c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 697610764 1250 697609514 697609553
    0x41a0f1207080c032e091a07030507031a0a0b03131202030a090e0712110405090f04060c050a0f0509360c041a0309120706020c0d170f06011803 63
    0x60302d0385d5080c1020015458003c021003890611040e20b14003842940003004010300696640f0314010310b0700c86000240d0300896038440420b40325800d2000860b0f262051401c0c000d0383e00e0395000052105400505604641e2141b048209008004200b28400079848400d140d54842d029003014803941c1d1003e03440e40c004113024070102c2d8001d907001808210080b103861042c0c100355110026081d10284200c000c00e4001c200c01d40c3e07118180004075460700c0303461380140207100302c80f0f00e03035424036252810000750343c0d400b4150f208002042c0025283c06e40c008071446500c61050600c42d44948007070021a9031000000340c0514003c0e0070403003524180d81d0b08a003c0d0682d10301001003c0f0540e4075842a4156031040e88110603100c10176607200c6118070b101c0005146c001000c0002d0721450341100030200000e4006002c243c0d00558001903d12464408010201c400704541c201a200b18407004803402c491503004110000703140c621800549030760b00c6501d6407020340900c2075180582e191641002591035165401007003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 697612014 1250 697610764 697610773
    0x50906040605010c0b0a0e0d2c01080703092409111005040302040207060f060b0d0b09010501080103020603190203090c03011112010b0d0f11070b06041a0f1207080c03 73
    0x6485082a00500064030300c180c4480129401c603540d456143c2c03d0040000280613a00c400e91070034403600340612070b07403003540f075035810115100641003a484501c0e58203078295143c590078a48901e0703600101031310751103519810002084411410031f04100c500d007110280d000854150300603081042644505c0d00307140036500950066900c40207120202d000c1580c2000890700c14001000180341580081c01041e100c1d074004504040c0510915050307030b20380d400c501000040822004c0f00030b4064800c0d41654842100d41541039454403001030803180c41800003070f000d10800000a840c0c0e03901c10341100950b0404003011503503890a281c4580e2695101c2c0c2c4558403a50801e40c108480c1c000751030607a044880103101042c16a4a0602c104080381d100b040b10503c07058540c00c0362203000c40103108a5013800c00b040c2506503201071900e8007641000d0018000d070b03c00d528100401500344200e8030302118066080da9241c04040014002440405840036200b13410320480c000810344050118010f54080303000c0d021034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 697613264 1250 697612014 697612021
    0xe1b0a093804022b140109020d09020907050703140901050306010c0318030c1809151805100204030c12150b030a080d0204032d0605040218070e03060603030403050c210f01060509 78
    0x10140c410f00c011703119000814000521600c482a402030240e04204000050981d4240c0d0105070264800c9442901054022500e8402d00d500300d031240890207089a0045d24124a640000c2c0c1180000790556042110311510301003050300407400700554061901c0c00030100c03942ca00d400068000d841c05040701d6001c40d80e6002c1c2c5138001038012080115800010700c2d194001c031108280061800030200c03141580380c1141c00300824000d002e10100c105040b000560350710306506142c0d00009581c0c0c04001034440c0b0a40c0c18002c54414003c03020854501100030030301862490020f1314191040c82c02408007030700040c09080028480c1d0061013180c2c070402d03010b0280328100c00008016845048809241c3c040354140c0e44c00a48a40c0c45281d00a100030480c004000b1004d65154806508031000d0300400d5240c0910540341c03808100b000e030700003011001540341c903007981d81e01034442845010b124000e07074010030400f0ba202d2404150414420a200071100250090401607003c5c048502c1400e01070703000c603800b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 697614514 1250 697613264 697613347
    0x3060b0a030b012d03030302121003030f11070504020a050d06090b01170a0f050f0f1501052209090b0406050a0605180403030e1b0a09380402 62
    0x103181101e40242c2c020116038600125491000c0d140c141501c8499500b40c40c1284200c1c204601c000030350300980d801070b226030100821807460100640303558105030b682c040820000c0e5004c00940c00b16040b500d42900d5403041220658900040b40e0481c070340c001e0010400f00304170b46d80b10000d0070507030722824014808255641c00601c1141d94440006000503a00841c0d007030040d2440000c2600491181000158190306481600444905681c0020703d4500344040c420a904900c0d0056000042c00c0c0990607003440100019200340b0031444811a648217941c0c2c03841501001d1040038000303112227482403210f0071082c03138044071001c8100d604540081ca00300200302c15000c3c031321852059540140c501418040080c1c401c2100d403034014011010107403940350305d84203210240000c08400103c050500d141902800402890842d10b401c034842c00c601d0048900808070300450140300b40b0241e08508008004a51502c120403031a501605030010700020306101a80c2c1800d0303051900e614009200201e00159845c3d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 697615764 1250 697614514 697614529
    0x5270f060f01050c070503060403110d021f090303180b0103031101020c121c090b15010503040206160c170d0f1b020f04021612020c1014092803060b 65
    0x45039500001d99030320400403540608024034451514008803141680d403540080d10304001110203c000541024203000030b0b21040013201c01a56030b6002074409036a1814202d014060080b03100c0328450344800d418014035000386d012070104402a4625206526907040001512000788001c0b4009034809004403d000018030980c1e41150710040603003070b2a40100b0381d0b006950066030703022400c2080301411000c2c00f0380910075981101c2c1306015680452600d60b014241c00d0074001200744c10f0003020810000140c0e2180212003141220205c001040c10340350030800790501c42d030b4006400310761440a0300c0c580110001101c904900555980c1071103500703011400c4501d420308480000c04603201c0010074006103041280f18000304006480182450440c007000f480091001c00c091741ca544440c840b940595034140030540745004c0c1520603600f04403848034001d140d00c3c402e03607190864807000701780c1c10a10b0380d031801114032003c055003102400e4070346051041c040c00a6840115642454000b00e00c055040c0101c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 697617014 1250 697615764 697615771
    0xb040e1c08071103030f0a110d09020a090207031e0908030c300d05090c032b0912060507020a06020423041a010c05010b04020c100506040504080a120605270f 69
    0x81c060345c21a01e40d254400010903001d04500081c1d61500c405012407180600074042024100001103041d140d0ba006104800708240c004892950040043c41301003078105c00c02880311020b00c40b100c02c0659801c40b0441c0c0b001465000300314540800940d484008100050180e41c00b4901c40c0745100140c0158542c0b18030304000701d514070140070240300000400d45a0b900030356111581d101a240d00a60baa00003074100701c013880b00d02d8101e0904426440c42459a4800d020b1550040e003000200781e418400480c402030754615000f009030f03131108009502544280100b081780d0307038000c4007035403100c1e00c0356003140c084180b0800c5e00c41d03c0200e44422a40900c0c01d4000c00781417001601d003160440030101c4c0112a214540d500944480d0748400010045032074500c02444440006030240c2095150090040240c503c044d010500c9039007080d003408045481c40302218440344e03030360804100d05520320f031519024019950003140d024a191401c0881e891003058080c680d003031260b6250503103036100e21112811002c1507 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 697618264 1250 697617014 697617047
    0x907050901180b03120c03130b03091207030e130204170610060e031e030c06090f061501030f0507020f0f01050f132109150c030f030b040e1c0807 64
    0x4200c858041c80710398000c400c0c08802400b903e44d405c1044014030711590100c06200c207a58400070320003c0d41001c894224020f80300b40107503603207542800c02c3d03026510300685414a480780c8000501c4020140603a420034600f0001420702c48010303110303007004402500302d480340408030b4640040301c40c0080300101d01d103449640030705494200c40d81001c9045a4040074400d43d5501440340003401d151001500701d840580c50507440c001c507078408a51040c00c3c00c0020141140c1c4543d806606c0b50780b0305850105019900c003800181410340440e6000048020305008410400040e241c9018007152543c0861054250800d0b80c08030388040c502d8412943c2241c504a50005a0400c1000480d8030301c80d203460441d606502030b88a4155803d0700c414050251481004c2c0d0001040c9022010071000d8007409184030041054206100041c3c1e907034070050000f40004007a00101079544d400d0107403540e09d56005020114464007254440723149016401c010910356060700d00403c00b00400904254441e210b12550407110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 697619514 1250 697618264 697618289
    0xb011418090102040b0d020712022407090506180901050604120609060905030c0d020c01030e1b0102010612060203150306011d2d04030801151b0809030111030907050901 74
    0x601600c014142005400071400e55003c2000041c0344240380080c0c0440054a0001a40c0d8041803400c2c20452201b000100d0954000c03007104003000d5280054031001e5072096040345000d5449203003c48100b403058000c1c9900c9200451140d2805d0108a40304844903020b583e142e001c3e98031030082224134000e512a04091f01c80c1400d1400014000703070020480c0601c9210301052030545a5030310381c2190850030240300349601c42c4909614040c2d0410100700f6030748003801d0400c0304403502c41c840e64503413034460310550350b04031405800303049a4400d6005200503c0c09182c003076a407810924040000e944281c5c0c03c0b0108102c225500101c503e8003081a9049a0784452001b11060354011840407007140200340080c15070040b00c3c0d03244000a1140800160503400c602c150044c0b515240152800034182c12000030701c4540140060402e8000030120310000410025050020151900c051584242214240c041d42040780d103203100d890500255001e00040c0003a03603480707a03d56003440701c9400e0074071800d01540d01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 697620764 1250 697619514 697619539
    0x307030302180a17010609090b16020705101205090c0105031f030c0e0103060f09030f051b030f1308030304150b03010209030f0d18180c020f01180b0114 67
    0x3a074020092460401190510b000100001030450304080c0c0c00fa02c240b103c00b07000c4182416080c829200034010f05041080240025110350b040c00074000c200718113000324046e0721080c2d54004c000b02401040000e1040034490024000142044407603d0b00090060601c0c001c640c0c0003502181170b59501e60182c1d1003034110703074131071030541c07181080e00c986820706490301071011011842c0c080b00e020292412414009040d455032500d88100d94110341d0354000c0c5480c00502c0c10001c0d61120b2102c0d6515242d01d00552520100c9442003054501d0010341180e505c0002101e5100b444210080c3c5031041c1e2804020b6421552180c0f0141c0703034842210b00521a45042e20140b600c082240e200108022020700014100480480403d1408100b0421051a54401c150045c903499000e210485c1110610040b00c03071840c80c180050a41c4600c40104051882d160b110490241b8800c01c56101101c42c490000c0c0402441c2118030a07140d40c1c94030060f507413890808001f048641d0504400380310f4010103440d011501d403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 697622014 1250 697620764 697620767
    0xe090402030616180f180b0906040c0509030106090b10020714011b020d061e02121b16080703080705040602060612210c0709060503060406050714030a02030f18030703 73
    0x200303c4010708040c00f000d5903483c000910142c2048000d0101036500c06500c1e400d0010007410081050b5448a07400c1c1084201c42071754441c03000850f0051404e4074045081c1440704c00c15101c0340550703424141c1640c43c1c001c00160b0300a80350058600d0181c182e0b01b0507202042100308070380302d48090051440000c0c80031100241075100741e003030304103e240084c030b44810111154000340411602100a442894131074584c01d00a0150410005103a007000504600d0017000750300520440c04010700481d0030301e52840195000d884d403030007100c41c1d9030961080850214414900424150401c00b0294000b170304d80380001e03030964025401c4400b500e945400400c81a66504200891044a03100300e10705401201001441418074400341c0c0c400c482c0c010780e030310340700e03184601782620b0002c19601ca48100b03400c1050802460f100481c0e00d0350400d41080f00481c0c95a00d081081d640548002c4c041e402d20000042013042c1207800d94007550042034580980611500c8031104448400d0300505410aa90420410400040d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 697623264 1250 697622014 697622041
    0xb060c160815130f1416090e0a020d060212040b0103050c030105010e161103191701120f06090209041101021009050613030e09011403060c041a070204021903020a0e0904020306 77
    0x100e10501e00f000e0303206803a644041c140b0180701904042c586c0401800d640e011145014100030f400d803031000f04041500c4840441c0d6400e090840a03028240c12f0440d101804900c4d01254418048030100c040c0505007032600310302c100d000b440b00f6203050040131110380181c074060080030304039050b03c1c07501845503e500702c01703441450700442c00341c090000c00800090301c2c0d8014070280004400c0c0c00c1070b8401480f82c51a000c1c0a1003802071411901d809548010b0181c22044201802c019400503e00b110085403464008000d21580340060340c4002c24100f000100411040404607210702039082d110b4100820550b50141c481111000b0020340204d0000b0340390401c24200d0b81441d5001e0703d015441211008040f80b95040c0c00c0e002420051038401d18400a42001c10445802001011081d850249804005802d50508100a03203010400060302c01c103556941c2c041d1684080000101c800140701c03160050300030340c496045000424505032003120700349800e480251080d0b8000c0e0181840765200c1125232a032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 697624514 1250 697623264 697623301
    0x1c12030b0303090301060603050603070504110313020a03080d050105040e060906040813030b01030b04050d02031c0b010e03010f06090b01030204270e0f03041406030705090f040b060c160815 83
    0x5100c03c2c840c40c621650240998001482261070005990515400b17050601d10345410450250742008807194040f105141101d600c03c105248143c0c1162292000610350f402c00d50010301001004560345008039882d91180703040701c5045804001160420301d2080e110300e001c03900c140e0150460300000300818550383c0241003503801410405100d6440341e40f10130741c405080e002170b2000c05e025020442044410800300c842400d2038001141020640c4011500510180402c42002521a100d07848141d00074861041412001002032000510492211008203001e1045030b19080c14140f05082e554000e108035020340d40c850102d49060b000c3c9030849900030b2196182c4001c119503d0030500e0650b80240b003011400d456040256a0f0b403443d24560315a42040c43c030700e561040104005111900ea04103085131a0104141e502c80d030250301c00c800140084c5500101190020000909140c5055000c00c411a2216014400044d11510390000ea903984020300c403420207118041001c135141c03c022350346205e00d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 697625764 1250 697624514 697624519
    0x40f03142803030c1b11091f14041d030c070b03150609060f0a1e03140a05041b09060602060a140105090925150c2a231c12030b 56
    0x124111017000c02c289000381881980c080c8403144242d40c040c5486420250005070041280180c42110418039801c00d00610454600d1283c4944c0c1c0c8080d40c68035001540700c0004034950003038100000070103070f4403a40094000645ca00513400041901849881500e015801040c0300c0350000d0b2071207091086a51040c0380c0942d11040920406414141400c01014a07a109540b4100c0302116402035102042507409070300e040c5820040c41800e9100c036001004d52080c080440451161564249428003460740b044401032141c40180c0401c1901180e044030003214115401c0341e001d0769400703002c0c000301c5002140174000004a200100450b160120300642c22111020548884500c81d174401201c1c00761030164241c0711810321030200110f00d00100045506d40ea0b82c18049681e05039907607100852245411230b2980b080d0500444100251064640d80140071410300ca520315441112040d4028a040030103907119120800b01020a6005194035500940d0b114071081818040300c0e2003900a851001a05e58 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 697627014 1250 697625764 697625777
    0x30703110c0109080912011e0c0e03151f150c14060406050618042307080604050102070c0b0a05042c0a0608060c121b040f03142803030c 60
    0x1074406000784102c042c458480d484036640c584c0300c80d061200881030083d4800143c0d00d0204c0150030390940741d040c10a098081d1600103402134032003100703650305a04031720510740501c1101ea23041c85602d00c2c5035082d80151403a280c400c60914820b01100580032160003912406c4c0356941c84002c585028219001c0340391301c501c1c0c041d0f5000c052442c8a5103031000c11a030646241d5240c01c00d01103141404011000307030f40c0c042150000540740903102d240c101d582c40101c01400003410094041d40303200911a400180034100c00b554214240341c140b490213034000c000d080c1e9001c0c0c140240000c0c030000c0c12089450304a0303161901e42c00c15207070200381d5604181403810b41c5410750074140c402d04020001c4200d148220340241c000600c9e03a0a2503401481e00340010320007046094104100c3c4020b400704100f0300c1d48602d900441c140c0454485a5050250113954410120960001d1003c030030170908850b070056040102084401c0800500503445070341c0d204403544202042581e01a0010a00c2130b0080c4d2840000e40c20000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 697628264 1250 697627014 697627027
    0x31e210403080f13060903050316050705040c080a05060d0213020c0c040219080c0f0708071e03020a0b2a0a140d090c090527120a0903021008090303070311 68
    0x7030041d0f503c10000c0c07070340b140d0000610880c80901552139002520242c60686503407805c5584482c0e691040841c103a905248411007c02007100c2002801c0103000c0140050007071001140300503100440a50b041005d0f80d05000c009090307030034407070202424150020080306030035040207051002503100c140d01c80002d000710103001d02c0c140c42d01d0000b040001c200c4070244628440014000b4504d400280c840b03400800200040c460b082c058000750f030140c9400c030901542e92020791909121035810042c0381180c00c54000c0582d0203154010846900c494040c0d10710514079607072814840d801441e0078042864039400c505600c546603160704081c2c2092540c0e41000a00e206a4002d203000316000503082d048116143d84a0a00700401c1c01841001440d200c00d0501180c103181c0c0c002e182a040864060455201110360b12240c4601000b94030f10121611103650307910a00184010b150315404d02003640034402d20030494074040d12aa5481384100d0000c1c01841c15515a150102d0280503c42d50107010390005225a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 697629514 1250 697628264 697628273
    0xd0e011202070c03032006010b041a13030303060806091c1d19060e06040302060d091707050615090717100e180d0203070c0303081b030901060302031e210403 69
    0x3c107400786000f5124621650030b0f00760702001001c503101d500515500644010003200c02c1c041c0030380302a6803609000300e4440f00c0944450805004802c102c0700c852107405400414140c1513807151043d03c4612040e00c0d010703a41d841e105984d9401c814419502900c55031400400d075407241200c3e481180b4100c021a074242c10541c002400040c032800440d1440c5240c000402c122234001000710a091010382e880d5040501e16000118240070304402030b8412512010810100220501a4043d0150b002e4507983c98408a05242e5500c0d101154100305900702c1d001040710306e02e0a050310740d120b000f40da5142c85400804e000d090b40c03070040c081c0ca100c0da00341d1800d80100d000d1065000b080d100340f403c1c10700c10004007004240f017460040c0b01140c44040d9001000f031240850f0f4010010029030760103040100b9907884040680008840e09452008405008014080b440e8019009001124022412a100d241d905101c0d40107200200c11f0f5071105900c980070011072469000301040701120f541080d5428141e0b03c0c0c44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 697630764 1250 697629514 697629533
    0x31305130204082b0c0b0c181f0f0c1e030e0612090712051c020c060a020d020607112d160e01090606080a020d0914010c030b030d0e01120207 62
    0x2034821204c030302820000404844200c10b1015283d40c0c0b03060030418110f504c0740707810440084c00405c4248800500c0121030b07040a032400f001c00c1805000c01041428240080d09040311680000001802c5603460003000d602c40c1070303012003c0340c10804c4441201049100344900d0013030250100c0c1070000004040b402503480350054464540d582d00340e0040c62418050440c201340c40ea4018011041840019501203203002400300b5981e40110780080205610300016850480d1310704408c1d500550008495005503408600a11014640e400f1100070751180041075034103030340d884031045c2a9030051400780010301c0040c00400c088500c0c020001b010448030700542e07042c0307120345801704041b10350b00c9400c10211800320410350041820000400c01c10f420000028000c0c1d10240201c0b8100f6000318250203048900d500035001564896144d80c401905030a206002e006002c00b184003080c0340c444402c40c20305003c607513400c0c2400315584100b074071000309005440324180c041d103000c0d009a080c07142c480011010f00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 697632014 1250 697630764 697630783
    0x902030a0213150e060307110a0c080d0305072c0909070f140904020f030c18010602070f1203080403170a0902270105100309050102041205070803130513020408 70
    0x11000340e07071000c1d60b0116201e401c08030b5000d9507003461018000010b60303500610312104500e0482c0d0b00d40e50f80d15119802c40c0e000b01b200c00141e020b03000d4080054104604c1c10040001c8581c0c44083d140c036080c02c0701c0c0a50803110111800c0001c218000540d00b81c0740e03402d84414035910340094044600c84a13820114585a80843c2d640c2c83c0e83d404240213000c01f0910b5101080101040035021a01c2843e410104c5e170421000b0344001c1c0980704084c50b5008a41d000c0c0412012142c2c050304203450a00c1144400403549028072421015014400c0302142c072210701c0c1440c4081e0390004254821050302c0f80e8080b941008010026810411506101d103526004034800500030340c9035620218221287d4010841125060600c001d850800b07061039031003144222580c681180ca040340c000791201107215054004c0d04400d40002c0003035100007004160119840b4030380144500440c111198a0340390411603650344201c0f00b4458418008a100b04403505d481d00070300d9000c550020000d4281b60307030f07042c0c1c041c540390091 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 697633264 1250 697632014 697632031
    0xc0a1404120c270504020a03060f1d0a02060711030c0310020702041401080c01120e030c0a0b131a060402090a06020309090604110a0c020d020a06020a05011b0e0d020a090203 76
    0x1808500c0a120741c40703000b10083c00d00f21000d5001e022900405410200b0010800210161540e00040c155a16200420000e5400a00074055140c5408031480200340b10b043c1c00c011a014202884a2014000355082040d5805030110703191004a271100701140c1074018001f50300d0b2045010b0300308561014804401121035081000d40c850000b481000255080414050320f5180c405004000040002829089a610a00746981403107951046240540076500f1004014030000a08424940e4000313070314a0365500411200d0410b031500140f04000c0082d411010301024019511200045050364501da000b400c02400140790440d400042945908240c1c042c0000d03030804201e10b2042e09001c4049644044119020090581e001081e00310030700500d01d1140030030820fa01c3c0001191561102d5000c00794000b0302450416076121402581c80481940485481d400c0c0015403030100c10a510515030034070b00761205001c5581160500c4940c420001041c0d0f4010303000040028401d0f40c91000f5800742496 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 697634514 1250 697633264 697633289
    0x807120302150610080925050f120a1713090c0e01030902101d0a0e0412020a21050d0510090b0a150507050709050106030b01081e0c0a1404 61
    0x440c10042c1c20002203000b000145401e02040014a07030343c0d40b00481c02c00700c031410304100d19221007110600d0b0542101008600c0820048400d01008040019100301c2d042115900b01c1900c403c01404000418460007074070f580d000c0300c6400000343e0120300050f005200d03546072904180156182003194603080d803000d01d00c69621041006c54940c4807040341c2c00301c0e41c2800c091101d0185540070640581324040c035541000080c00301c10518076499010070103c61401400d03125059158002080268425501280d04800400030302c2000d9001240030541c80d030700202c8900d0107620f01c000c00e004001032002480d040100810025400524921030356008080c0c2440c103041c0d090510300c2507800c4400c2d141d1014815481140d0401c4144000ca04090900041c2d203020b507243e18451900501d015400d4214910301400d044c008070700107a165200d10030b140d80903070b50341d032050b120040c0d640090074400742d509001d00b0381017000602c801117a400a0480082c90b151000340c68691100051f0603810070303040160082079 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 697635764 1250 697634514 697634549
    0x120d08060405090d0c032109060f0606180905070302070f0f0c0602070e010b130302060a0302070c050f090a0506120706020606040501080c0a1503061a0306030d09050f09100807 77
    0x1842c0c0304180e07002d0100401032092030340d1240050444c82c90020014104403071854644815086110b284600c401144c40074003640c803280c80c0440c05414014a1010254075040f0300045543c812209d407075101c05905089406a8141051000136220040c4001700307054003040b0b11400290038500f4a060350380620740c0201c80c1801ca1a01440741a81540540119846914140181d040c44400c10341182d0303c0c0b840e5507955075070904118000088a910180d880080412b9400a0039050b80040900301e104210b00e51255483d0303030400040c0001d0440c0c4a13046041e5000050040100d0380c03290350010f0b001040000390110a00c101881c180340c50708071100582282003448041d003405d0186078090100c1101414145013414003244190f85c9503c80c003072003103082a041c810181d00a074442c1d405010400c4c03076101010800042c2100e964003e40b8018060f2040c040708501040c450f1102034255840241229103042d104020801000006040d6051210a100001900c004d08218400013040011807400500c01d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 697637014 1250 697635764 697635769
    0x60804020d020a140306010b030705040e0615030f16020d050a081506040603020405120102040311060307120c0306081b010e041a0406060f1e050304030f0e120f010b0406030807060506120d0806 84
    0x4048c0c0c00415400e13828814042c031a80c01030113031815079071406151042552484001520116601c1c0000e080c044001705014501c0103040c0e20344d1194100c14200d045148000800305c5c0d0300e46180c1c10038400a40140540400300b0703c503030030013034104511041169055482c0340004280740e1146d407141c5e0210f58009020070140c20308103040580c100717903e0021800d15145448013000c03040340c4584e9510900000002911160094080701d00c082c00c1030500300545c0c0000940030b4010403142c05052500c2c405d0340c1700b4181c0c10911110703003c4c00000680d0f5200c80848018140b2000d0500010b1450300145400c521316101c3d02c0700e1090b5401055159121a104006d044001d0020fa0580140f449100007503a2502c5c41a9004805c07640c12942c1441d20400640328404120b0742071040b81802940280001a601c44600000407202c1509000800810815240303804210407241140310061040e14180300e000003083d9158010783d8071180242500440ca401704e041e590500440f1041c0c04c0200343d0103000d200035070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 697638264 1250 697637014 697637023
    0xe0309011205040503070807170a03060501090e090c010f2c01181a0d09061e051503100c020307120302071b030b0f0604110d0e0c040501050a060804020d020a1403 71
    0x51142908100500307040d10b81360f803680300c1c01c00007501481d4002003002c01c0119000b04814030340ca9031480c25440d221450402000350a0300e205c0c007030000d405410f0203e600815520034030700442c140c800402c411080d4070700541e825a400915030301400b0005032050030000c104464004940754040c0115005020440090480c43c5110852006224091414041e1510058a40c1803c0140a0a0325101e404041d031850103001110030013400c96041c810300b0700c00b40303004040d08105a00c4400040c0316660320a0404105100040842c6a1540c00303414222a0300f1003d520014030b254075417050f245400511b888115034820180513420000760b0008503402840314950442081919003998181202c0c651744440d0000c1001508600c0310001003404180140d0f0b465124182056801112603100d00e15200030724018140b020030b240c4c450103100300740552898244144c2d81a500c000f019002050b0800b48125100b034402081240c10828a1504801581d207840c0050010003000305031821035080e550a15040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 697639514 1250 697638264 697638287
    0x1b160524100b16060b1903060902030f01020c0703081315120f060b0702041814030a0801050a030c0b0c010618023c071505070906080c2115040e030901 66
    0x3106418080040302c480007043c046101d98200001040ca03041080014035020540380c00c03241e0f48144803070700000700007140c0c0121a04900890580b42680c13051485103081c1e00c13400e602000c1603003180030306000040c080c0014017620300d113140d00c8980346030f10740c0c0340110015654422800868514084c0b03104c0083c00f402200680d440500742404120714ac001142d0701e0340200d100c024400c030b445a200c40c610188414100c1d00701c41d04010200300368090209020f85980c085c00c0040005036401c80081154245402000d007100d81c080c51118255203444400540c9400c80316239103c00e275485400003d10349000340d21030100c41e90000001a55258a8541d5855240100030900700407011076403845106a40c4282c420314031220318910941e24000da01d024020384090500f50140c580c0741c0004d1182450b401650401510340c15107404403207071200080c0e141203004042102d0809007100c00e001c0300c5100010000c035000400256902038610a41d4005000d4134240c401030400755001089411007584c0c4455a00304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 697640764 1250 697639514 697639529
    0x1150207030503030f0a020903070f18230705070c081507020f0604120201020915040503010501061b0f03090e19060605070f06021e040e0109051b16052410 68
    0x40891559907003d48900004000c240ca0a01d510001249000e40e60121030344008003d090b9a00b840c0c03a103d0001c60700900e4005c00d03044500d801c0130701440a515101c0c4d11950000c4076103065070b045c28400c90019014004241c4410040c040c0240d02c00942050280700187c0b0105000d0401c3d0709900d2902c81030480014440d00841d8015040007515401c040342c0d071a002600071a01c1e40c0d840c40003041c00d902910a5003d41c58126034540d441d4080307401d80c0e0010b017003540d200b1402441142d98885040b1802d02c0e01908140003002502e484800003804038a60161440c800d003410118656203943c11046c00400321180c1615000107105081011741d54841c220103446541000c034109201a01d910780c1c00700103054020003040d40014026403214042d400c20305884802000e080d80c1d10f0729054419a036020038031603d401c2c98100300200e0000214698144159810340c0081410409900c00070708040c110104151014050480764100010b68086070710100501d0b4160b200d041d0a12001c030144605480c3d21612 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 697642014 1250 697640764 697640773
    0x10050a08040209180304080109060c020309010503012114030a0e01020f100f140115030b0f0619090e0a020717191413060f02060f010b03060409031e0305011502 70
    0x40640110440d6000754066a0501066031035522211800f0009032500c40c0c50303c808030b07001071780640540200c407426108500500407540d419509031b03540d003c0d4103001804284c0502c014070104021401c1c6505132415480300c842898080d07164100940c0000c04008c4203504000307610782000c2c2d0410100103030480c0a02c01000140d0704084229120f0404901d0134107884d80761440c0e03e246d01d4150308600100080101c2103030766540d4803802091829019824000885d0400010009614000e000dd4440e2040a0b0815103404080d640d001c201000e02c01550003800003141c1e0224121440d01540f0f8402e2602c0750700180d90344024108542e0b400027002048003071440803c440d4202c84400b051480c00701d8550305090040305d4aa5120003003502540420407070b09840c00c040000c3d4241e0040400716420042c1d025a000398903800c4c40720030b07003220900ad9055042d00420110303029007090382c0007107607090192038840103244d10480e14400e00031220f4980300000c0e8940b0014031400340170b0064591683d01c1c500060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 697643264 1250 697642014 697642027
    0x303180506090d02010201091e020a0b041203030e15041511030603300c0312160c03080703020708070b04030207080604050a1b09020c010e0115050d020d030e06030106030b1005 77
    0x2050307071041d440103d00503407030f01c90202e045900075003000d48259408030001280080080b207a003442c9102410503441000b4030720300050040c40d000f04450030f645180103003502d00c1604da10154080c20701c00c0c60b42140ea03c100d994511152003101c01d01d901948c42186160201d0a41c0800034050319200040d03030280050400038491107580c0010034610341f45e49644124194440c0d0018084100405200141c004000182801d8949000710007820041c114080c0d610305616900d01c00c4030900941d80c4c01d08040f60310b14103d1030101c0d00a0042e507034010118034001d85060455078600307503942c0084804079170303142c26101408100b580600c011800340c05a14000c06042c0b03030a880e000c0e5114102034006d0300c0d140d03007000001c000c0c080d51110703a0003a00030160195a07070100028114001d0441014040903546003103808616091a04d13100c008a640c018072000f100e01154082102031181c5480480c01e01400d60b000b4a030030740341c40c40510300130b1070310b030320f001a24400d02400c3c044a004001403803c20008100002d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 697644514 1250 697643264 697643269
    0x836040e1905030702090f070314040206070f050705040e030418150e06030c09041401061401170606071b211718060c0f191101210204060302030103031805 68
    0x6003940260140341c40991010750341002d50071807081c4c2c40040c5d00048600304000700500152562070140b4030b5590300f0811580030104c04034888038280e40007944400c007080365801082040c18400e1806020300c0964501d0b0760f0f21000581280c1c0c03201c0c410085500041000c00c00989400b0b200c00800880c40d105008805401c03031420840c0840f030251154890206021804035182084005942032740548480c001d8202420074040080c481c4001c0c4a1940c01e0200218040142c000007070001a810703104c0412001b00d940c460804003200525083d0000000c1c082400070070b80b00310b60a40349400805001020a0807c030034440400c0b00984240c0c03108881c4010780c400201c00c0f0070014410003141c1480d94941d09040d1080c0300014149011030b50100c0041041d07405442c0101c0c201416a290101710340f4501c2c04e02c00103e900002c03584000d0401040d46201a0041d4001c40c0c0c1c1c00010f06e628ac0001120482100c5030318101d800c56001200065400b000600401d0b802114030900101c20524605059280100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 697645764 1250 697644514 697644523
    0x6040e061519080a0201110c0603010e010e0a0902030303160c2307150c060f0915051504110a031806020c100506010e0f0411210a0c050406090302010c0836040e 70
    0x4c000c0c1040600d404220454005000802c0111402801540d0f00d580d603c4607030b074580c1801c0c003452140ca42d425001c5040780c1131912646481035070242c051425581d41c02403044482101c8007440c828450071607100000107070500c1d40000c0300c00351410191820461030450524282c40e5404c25802100183c414105194001c90b1050b441030780305c4404100501480988030261002482c0107005482140024084040c1c03904410310419010044402c40e090703180421081c0d541442030401c10400c20491649114801e402c802c00c00c103807030404280ca0140c40c2e650700d4100e9108810b4100b05400076a0b80c01d0243d00c60340607c0740c00050074a40f0444001c5044001005d100c4030014052140b90341d00198510001c1c44425a00d80d41803052602c041203502000801c2d480b4021182c3c8044680381075003d010342801102940d05072851540d440c00410b08541c010740b07042020070801d8414080070312100c000300c40c86210314910201240c3c01301d2080142c0c0900c80c0402141035862070f1107581018000e04c143c010024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 697647014 1250 697645764 697645783
    0x20d06060c03080f07033804110d1805030d0b090c0712111015031a010312111207030c0209011a0f1b0105040516080a030507060506040e06151908 64
    0x3508465600c8905c0117800a00c009220f4408a8a01840c19101c03440281016051118080d081000001d00720081200701c500580c6441c40074101400005095099175100e82410408144110350340c04d5141c4450389540c1121042100c05a01d42c580f100c2d960600066191700040345800c00d508000680c0d480840480103a01a8800c10009410030780159604101905000d1402c0c1da00700010304507003130280c040c1809030105513000384410904500441591200b40d04070b941111045030300811403403040b11602c50b01d01d094042c5100f00d8542c14a8020120020039481d4800e40752002610752510600403540b005a120945c1c4d0f000310300c41811803440103011580072a16101170145c0c1c641c108010101300412448440c4100d61806c401c11041000004164031030018660010741080d41e04c1c1a441d540d1a511100200060014010b440000795107401c41c6410110082c40443e0001081d08220302d400c00448400e03c86010041912a041c107000c8103165a1341e41290541412905051180f980e03001100e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 697648264 1250 697647014 697647031
    0x41d0f0c090d0804091a030f0a031b020414270319050c01090302010618020903070e040809030a0309061106040506060d08040807060507060b03030901020a0809030f0a0501020d06060c0308 82
    0xc1d000ca00380d42e920350750040c01d40d100034019103139520f40c4402c1c402440c00031902290040444081e483c207180005240004405070b000800510040781c3d0225031003080c1c81031241410481a0090005903103502407400070201c03001101c03110303180c141c400152851030050f402d0811f400308070301801460300100c00c1300c0d840c1c1c02d8010201c1c10760340c6580c41202c05114041c078400c8203503c0c04003440200369064005400311180200362540104c11801d50108912592555541c16400700f4001c0046800944c4001e612900400203181003d0004022a0804220310000c80000e21114003e0156075007006d0107808030b41f4400020f2850b4503199954565a880150005118104a042e40b004101d4900c044170080c0407000141c1d9183c0c1d41d54a0081c0c503076040034004136119800e10540301d10905001050f60701070101640140310ac90b0040d240d903078007075201145070b0742c06015041ea42840031000b086124a101d224400046e070360b50a00382d2503030441f41e09030026410420207826180200758040441504030042 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 697649514 1250 697648264 697648267
    0x10c0201200703050f0a020415060c0b0c070501020c06072c0d021504140102070603050c090904030509060a051c020f0409050c2107090608090a060906061a041d0f0c 72
    0x52820b4035080c42940010854440c01d1030318900c1020128402135464130a031400c0c0040b00700440d4220070481980076070070000701a481d81c10b01144c0c1400c80c4540085808044514012440d01c0342401da90080b1590003865114400380044158420700c40700004244042040d820124000703081501707004001068800c220426951042d50b8480d403d01c2c2e16042002c030440d40c1c8955510440727107652a03008521380036010340c01000441d00d000e8001c1c0c41c81040120309240c40c2c040302d02c04120300404090800d8041100a0212103110b0300d070301e0300402354800107071151511880e01c003426804004055882010240c014014255900b8040c024ac0e8191648510040f403140e503541c825034014000c1c05405c5810f1805413011019030030203550105c1c02910309a84880606448013401d440700e0344185e45081582e4800c000c14000324006500c110111441404040361451340c3d400d45011100d09c066400392080c0000504004109014850398a80505003030380b05007070b1a06400004030240300802e5080035140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 697650764 1250 697649514 697649567
    0x3070f05270a050613090e0d08010510120203010b040e01080d0807050a180e090616020d0c232d0703031b12030203090f0f0c2404090207020f010c0201 66
    0x41d504041009404060071041e04c0b00b0000110901581e1140301d00d084951502c01f02000a00300030903e05003490031501e84841c43e900e004107021000391144000810000024081c045055480c0001d42c0200300b040d030100d440c0c50420150014001041e440f0903055485000d050400c5900510010380c0490b43d130800355210b0b00d0080d4140d84400089155034140020200045000c02284d0b100074020740f040001c44d62680e039032145039821000340324103050150740b0060080c01308a10600c0c0640349148103058000c4502d81e46000d1070100040200071034059000f214030444030035100e2480d4001c0780c40708480040101c034405156030b219600c0e030002500300000100b064141c685005400c001c0c05500811007451203c2a00d4010000c0d0000ea42500c041d000c1c1000300c0000c1c46000400150700c0d1800d00142c40e0091010741040300781800c0c0000216400f05812428403400c5412300900005e00c0046405079841005104119030f5109003030189060202094018002d80d030700000100e800e00d20840032408418 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 697652014 1250 697650764 697650769
    0xe0f06060403082b05090a0602160614040302211c1b02070303080912040b07021c050736092a0905010e040807030c0201090b0304030503070f0527 64
    0x7045400103010307041c0001d051140340311010004200503820301c1c80ca06010448001c84001d8401c156810001688500d560b140030495a500610318610622020300d00740502e80e0340c1d003082e10007034147e800445c2040740407c414190140103951940082c55180340c03080890f06540009c502070700d0040440900c0c81c0d400bc22102049500c490013074901ca07401c00094490a440003540c6c2c528500048000507038a9002c03440300380c400a401004601142c0819003002d05041c0251169042000e041e640440b208000300743c0d1564851001807410301407405002820b007009070041c1c1d03003103510591004100c51075250316805030b410108040340d0f0610b604040352008203401e01c5881380c2c0648000325140d003256241e03105180203d5101c0030846030340080622040e0380e511010320340e130f400c101d03070240c0003000130400000001d21440410807501e205040191145031122070001c403c0e00304940880101c0d00010a00c2600c0390011010710f100e074040e1400354038007914140010700d500a2a43c440a024200e4500d05589a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 697653264 1250 697652014 697652017
    0x60301060f120e160f050612060d02040905100b4e010c03060905010b040302120a08030f04140111090d210201020a11060717040609061a0411040e0f0606 67
    0x2140c00210500950360300080d0b084e150121310340b03a125807411030760000034085100d203100011504010031050404078a2560102070a900a065a41c04280703402131a0050340c4511038801998020b1005004810741384181c2d02c00c40e081200d441d0f00c610001443c40400ca030118170001408051001b0104c40300001c0c0c8610700c540e41c55000520f040402c2c01c0b0003da0038240552003407102140c0e56506010301c0780d4580100040310000c2c050042810001c000520150a0540e0500b0041031007000b1104402107a0b140c003440780e0419903940454071207140a00080c4076102e0030000c603142d01100200014000504110011302c101c4c24124094849007500009101242980000258002000b1200c00d403c01400a0007980606c650303001061030098064020440014280d105600607101c0d45404480c2c0c520701c0400140c020001c5800302e0301c81a40c8400101a4060702c0d0005c04032005403201c140c5d03c2c104200503100041e0f28032840b0175042c082003214001091071503401c03541c1c0745001465621414080343e0103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 697654514 1250 697653264 697653287
    0xc0a080a020a0b16091e120201140403080711090709181d0a06060815060d06110706060e0714070b0601020c0a0b0a02120f0a120213080a021509060301060f 68
    0x40980030009851070300e40c030543c050115075503a6040c1540b00e40b0300d200d42c03581c0ca0780e04009124040801f4449078100181c22940d02d4014102214140c400c0154040143d11503001101c454201060300c10811030710f80d2a4811526041b1004240c602d03040300001c2c0800c1151180f007c82040c10b040f8080100615440103120701040705c05072450000310031a4a998803030103041265194506a0b0010b081d074000304a210b40440b02107440300a6031100e40800a09a03080f00f016283c081d5184100f0a4801904000785842841403802003083d61038440340400c0030300c0007420041480300c00302d0f094400d2004038040f22001940a103824489440d600c0040b890800751b0ac103402c2d0015540200400e56150210140098420070340c22101e40311070b02e180301481400b81d070710550341044040c010288054060300e203021003001c15500040c1003600070a0007c03c410f21030b42c041c4001d07800004081c001d40c10611a85000300c0050b070341080c6001090b50200380213100510844040000c10100d90800c07511031840e1448 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 697655764 1250 697654514 697654523
    0x70f09020a020309281d0a061d0a1d0a0c051504061209080424090605040303110c031621021f050d0203150103051501050d1d0703030905010f050c0a080a020a 69
    0x120540b07030310100a01c6c3c3c0111070007075003840060000a8100605014240c103076030700281c401200a90303010900303640380c20103400d0085a603107581e130505010406050350461000140000c01c405805030611001545003600960300400f40940280b0703500c2c000d0400c44045800501d080e6940d45e0311401400d00a0404160003040f24400140c00a440c400c440c40710403644084101018192602500c1910000d6a510816000c07a40074402080400c0c050303607040c1c03081c0200b6401d4540c103400080000b81464042415905d010701240403c0c0001038a2042c83c3d5400080030000c000c075400550002401245500700407608041c8200001d280984140240c0e60484902c0205644a003080044400e1124842100704d0000b85000001050b203c0018408141b004040c2c482c00e141240a1200c40054480750f000001000c1144417494640a420056034004501a580d5000c419007058001441030b49140c10700700400000b0300203421003450204005500f00c0d0700145141c7e40300b81c0d0407404e9080246440002c1d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 697657014 1250 697655764 697655839
    0x5150714070f0b07020108040b06030a0c242307031707050d05070503040b06120106050613080d1112030703140405150a09031e0509030708070f09020a020309 69
    0x40e21080300244590554000c003000304070742034548440c10300ba4018000080d00048480d03004c034002c505040c0a003904980040c0654441400c143c40300c1b00c2e0000b881e4814944070034810072120b0940700c540c1c0b1003074501110340b0f05070f030303100d94051000111032488102a462603e80040c0c00d80406025050a429581666032241458a44140007800541060780c0c1400790310305190000d1481e41c851000c40344215131001c8001c600303032148001d0004850440b40d1800301903694480105142c0d40d140060120b8444e5140030182c0b19040c029007074180a91201c4100a10680b85030700d90740110b001c6955580d01c00c5100145031a680c80810403030140c07024000c140003550520f401d00c010f1200c01f2800500004040755228240c6d101d40c045142104c000d07001c0a80015241340b010304030240074082003048141b1030b151132402e0078440740009050040030780c8100000e82c01000104003024009240c5802010803420450034981080c0f40a500c920500080c01d116421400c440503040fa1142c886500c20b1038181c0000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 697658264 1250 697657014 697657043
    0x7020f0a2a060f02070b07080307181d041509050a030c1b060c03020706081b090d0503030c030f100e010e06131b020c0d0f0308040819090e0702010c050301051507 71
    0x43c210030100da440340e0040c01520f00104060076a2800c451a440d0f02c00e0f180c038035582d00c1e480c1c1280d150091500001c604003502c02c0014001d443c0144c20507840010a64000b21802e0510344076812104180e801c46890f804e007942138000c140040783c2c0c1c4500740c1c0c00d410030400c4401070b171520185030710620b00031400526001a001c92403e51200000c04018401e400b201d00c1306481d0107050b85d100d00100c94440081180c03018881481d00000c004c1c3c540d80b80007503c0c081d007502240d5512411034008450092428074080200440004420304c0c864101100c001c589202c503007030034602d01d0000c405000e443c410080040108050f80c4900c0e080e075003020002071007007210f01410825030701e08101c4207010300b0040c030542088a58914010144201180e40400641d062050580d41503070061401082a18814024408111010100c81012240c4403640e500c0d10344031410716010010f0000c0c05042202160314001881e403003140c1040c102d9065a2080b5681d1014080c8601d108056200d0b07c0300040ca56501201390 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 697659514 1250 697658264 697658267
    0xf0c06040c0303110601052112040b09032a012609070f0902270105071a070f02010b0d0219180b091f0905071e0c0b07020f0a2a06 57
    0x20794140e038429a501250301500900e20740d9184403c0c0110b95020042c4180c11401e0309901c4170040300c41c81c0030f00540711b0416203600c1d20009608190b0016244a0000410382e2051405004080b4080c0341c02c0702000300040100d011a40500328080000e040c080032030303142e80c0d621040015515031200f0600314070b100c80c80c00c0d403511619000e25101d015001c0038541400300d00f0005600aa800c620340c142c540c48601d9202600c28994510364011890501030100b1440011a82000120081424000703c041d005d0401400040c550b00903007070140304591401051410a5a4a000b2006d6144d01110301d164201c0c00d4480303180c04004075500c07007070741c441e004025000b40b078810b508028405802141c4081ca140d0300d101084442030084807078254141e8001409200146040d0f001682100c103503e442c0d0003014001e013440016400411a034804200088603031010411001840c42c1e100001c1d10142000c418122841e580d03c240c1000020941352650500c51030246011038541c000c0604035681507031407680d9940 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 697660764 1250 697659514 697659533
    0x1503010923070b0d09110603070c0c0605040e06090a02190323010b03070516020a081006090e1504080c070303180605070819110105011412010608070b0f0c0604 70
    0x126410101460141156441c0c08507812044914a03002c040c0b42100094a4000601558000722094000700d0420340c3c480c0c6510740514452030300354561a903100103074201000440a180d02000070001d042105200c2c010796000180e40208061304c0c1c8440c2915411901c1c00a4094807044030001020f0f030170f15000240c0d040d04000d80304070032214403d0705088c0000d01507010060901500387c00540c1007021640c0311f880b0720028816045003c000700d0032013415600041c080c0303510740d0010649611031040ea1000301086d10035103009088002c0100320048064040b0394550814801a0b0b03d00442540002d050050b142c0454078010030080a9400b50707601da280103411150f51000004004400d45400318802d8050003c0b03400d5a60002ca40074242040602d8004000e40402d402004200c85002c0c90304003910240501406000205848100007289000388010300740c0c4075a030203030b06a0401004011820f008140d050a4610844000c0d64554000031142c0407841201444281881100f0401c81803000048 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 697661870 1106 697660764 697660793
    0x9030307120e060a0314090f120c01060f03060e06070507030509120c040f05070212040f030803072006010513051506090316090204063515030109 64
    0x90200e81103070002513503c800710303499090056009034041c0300c0c1c6602044400081c258104001c2a8541d95001d501d6005810302c00050f500300000340a41290002e07203055003140c4611139803440e00b80000d044444945d2030900840340840c0312903205d001101c5855416540e054184010340c420050515101c3c000e43c00c0502c642480440750b52a80d02981134801c45147d0009002c1c60407880182c10000072005041c883c0d4030420060025400c16000c09042e00c2c0c100780d0a40d20380e680c0c00302c10794038401000c2544102d8440741390b201d0b030314184c0010054140d0b0b20990b000c0da607010f0f040c14058162642610041c04800010301c4030b140c1400c0c80030160100840080031550b014504100003408040603422105c68203030001030902041d900f00c82c5500740036503003a8031052441e10380b0806183d40011240318010765800380d4080703007000040c80410075205a00800800001c000c0e464404e21140040 = true := by decide +kernel

theorem cover : BRFrame.Cov 697482014 697661870 := by
  have h0 := BRFrame.cov_init 697482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 697482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 697482014 ≤ n) (h2 : n < 697661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
