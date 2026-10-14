-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3665
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:19:42.460977+00:00
-- url     : https://prove2.me/submissions/f3a3e145-ded1-4856-a739-b60e9aabfdb3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 658992805 ≤ n < 659172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 658994055 1250 658992805 658992809
    0x6010602060417070c1a040b030901060f0b12040308060d0b091615021c0512010e04050c060403050a030c06110f0322050a150b0402030c12090106142e18 67
    0x10f003036145040c1d8656510b00e82050300f0f2140c0304205500b101c1c0d006800c140e04080b00c0040000c5d040640d1241084800b041c002d0081d44641060b4020815002482d200d1000c1a03460780461040d100c0c032a0707039481c1c5060701d00440c000d040d5940900042580e00004076905450780c0241c4418009040e0500040300031192201a9002041100081c08001f8400c40c3d00151075029204c05c1c4042e040a80d40e907540a440c20f0040081d08050056088008201c180d0240886445a405501140c11208004052294074441d9000180040d00b01d80d1181000c42e008070000300165110351400640000381d01e07011031041c2c01c080914801810300100b030042248941c3c032001c0d88070400075604c0b54000851394400381d0310060030600801c1107804400712503141302d0982c0402003140300500255540d1415619140e5503900100002c444400682e01260030505c0520468040c2c1e5980e4400a4140603903408024100e4444a001c041c01c2c03084252106603c291803420060003201130300d0740d5030b80c2019505692410f032015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 658995305 1250 658994055 658994093
    0x10f020a110601080c031e0703211d090a0914010203150f04050c122805041e0b01060c060b0307270b0603060f0118060e040608010912031508060106020604 68
    0x5d201103841e9004a80c4100744500c42542001040c3c240d07029506002040d030018020114143e020b0341c1c1c203054203207103d41b80612541c0380300c41c0d8107501d020b4800c0103c1580c00d441e000300319500020900d00c4030790b1080700214000d144445101205010660a990088501d1611000c0b40074040849041c04d40421250103000c0b1020300c503e142c0070300a0a102d0140c044458801408207000c14505080f24041e8101d43c4070f039614030707560352ba041c02a82016007402d5070201c4029a1a001c5141c00c0418598a29840e60740201c5184080c1d2820004603840b021582080d9640d42d0384020b558165501001208010545403c142202464107083c000c0c00241e1000040320240c1086d401040d941d69650449600040844000d55820160401200c0700c5803c50805040101181404902c580e0080c0c41d030410820225014402c01d85c84000550a13242c482c0002040c0140e480280f0340c0b81802500480281800e4151060b00e041d42c8003000c9240107001e0b405034016800403010b00c003c1c403802d00028003c0c031003a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 658996555 1250 658995305 658995313
    0xd1205040206030609060121051006020c03100203180105011502010e150402010f030603050f011a100806060d0e07320306060405040804181410051c0203010f020a11060108 75
    0xe0300414160301c4002c00162081034440c001400341c0c0e00400d90103501101c0423550503042d00340d40c0d407018024481175800030084001000c001810030f100040e002140d40024025041e40717031203115440040d410281c000d040c0201c0d01c01d21034035203c0c1c0910480b0700034400d600224109250f6404c02070308540504030400840e0300103514040c020b03141100e00c2074021b542860501c0c060700410a00300c000382445d40000b00540500c403180d40050405402000012042600d4040d00035030240030003100980c1032850300301080f824000190030b480c04030040d0005010840c0040b4641c01500205401c155098202444029408aa08544219146c4c001015111071703400300c00202a200b00103607642034020955072080f81c03184000740400031001d060310010600c1e803440d64a8000c0402004001d000890703540b1100220806c0041c21070b00c1070345004400c43d10040c1010019071101c07c950342038854002c106036099900c900a008480c0c400340b0081140004690701e85452034020782115041500c103034040c05113680 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 658997805 1250 658996555 658996561
    0x10609080d08131208040b070503090d050708071209060905241c05070504050310110318190f110109060e1c02190f06140a121404050d1205 61
    0xc00050303440c894a61400c22004075550303d4444007103603001a41c02050407401950f840c45182d0020314040c000e5201d02282e5240c0c0d507403d44225240e00040382c00e0145580450402c0b0500c034082d800500801d8081d141003803901250340c5850305034103580d843d4040007402c00314007000303170580c0107040e40302408007100d03c00240c0003a01c00342d84080d807a015480f041c07003030f0010341040a003040200320010058815001c7c40b192428000103041e83d0031504c6450301034099039440c0103155440e07103d10600517080c1003142d81141c58980d8401c9000b204640005150700c65280c0001030b00402e0702020021038891003130a0350b80c0307000741b508a9100014505c10b606100000304103000c00d40e0000d000e0f400708070041c1e07440c064a80000068040d0700c1c0959001a40202e035072404007140c0e520080d0010191229403100086560b03454004843c0381910002c40e17a8405400d0005050f040d10a4001c140704030001c9001040c010320700f404e0b2803c4004103585c202c90030760041d2051020f00382c000c0c00a8407603210501c010400340c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 658999055 1250 658997805 658997819
    0x11011401090b01050c0a050d020c030c101b0b1009062117070c0b0a0305090a110405071719050c04180506011e0914062706040b070303090209010609 65
    0x94018000c0d081d001e5101e00c0c100c00e040e44180b082d0b5103200380100c103c440324092410150340320f40c00000725000500030071800100301d04000400382004c0902400964440356440d00450701d041e0649c1c90b038001e070040c3c1c8400710003090000c0da1540c02042c2c4d003034040c1c0085103802c1c42c800c1101c1ea140c0c00300ca4002d02c0c49141d5a480c1503440b00c41410103401045401d8680074400c98902d0328401d03104010122812031002252038041c0202601030070310941c074104481d40300d940300303140d9403e0b910000400101c07100d0402c2c8460305041e04140e401113a54241408034034001012991648800c41e64015100c008007029120501140181d54011044010013444c0600302100c90030014002c4146070710040c0c6032008a00280d111301101c501128800c0d900359030140110314020490f100c3c902c207103c1a40b10070050000b0b103140c030f2001c1302d050170502554806008031401070920303541400e855050b4041c906000009210808400418030580306e550005a5043c2c503104204440a068024104100414078240044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 659000305 1250 658999055 658999091
    0x215011e0e0c03060f040f061e0506092d120f0706030c140f0c060f04143408031903060b03070c150b0415090e0105042604150806011101 60
    0x104134107450030aa03c1783c4150114014109003420100e42c140b40200c0002c00d401010140e48005a4000007400c50715a03500c10000d050103108070141c1c0c4844040415a0341e000616402c0421000302000314032180b55030400100200c111a810380141e40120250310201481409040c003c0e00c100c2c1400c0214050402006000d4a0700d10150030411100080e42003006070a0401c0d038000d19442c000b1105503150580e00300c1c507180c9068400300c43c9110300d1500d00241c0d0201144d90200000c02041400f00f1200a09444400d03241c041d08e285013000001c03030007098000e81030001300704040c07800060090803040c00c100201103840e50360002d140500240140502180c2c07044152880d1030b003100f03600040f00030f9124010010030303007900c0c00ca500034030f4801d00f020480305142c14441151181c81c000c000520803030702c2c894261402114000c10b24094000d030114460010304140085210720b201c1c0504080d219524044803903d11040d010215000c0e20401000d5a4003030030b200301b90025480240615803140e01d6603481 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 659001555 1250 659000305 659000311
    0x1c0519151811041b050a2c010210053303013206090601080903040b0301060c020406050607030c0b101e03050705011103070312090503071a07050412060504030215011e0e0c03 76
    0x3007180c0000c4240c6c0c52841800b1100c049142c0d90800312600007103d039918042645090818094050700034a40201c460b41c2c4250380c40399007699101c0202c059400b43c10012002015090039082e00c41d10314240703050320300344101ca0031120f44400c11403100c2d030a26480d204e548480040c0b4001140300750300304002c80d256100041d40000c828200a100c94032694409801c40c015a0010b42d4090008000051404d5002c082c0030310044c005e0394204111030311001806033600c0342030006030110b00b2100d01000018810351040d60720904107a100b500d01c075261680d00410301e140c500100c004581500040c004d01c2021b103c9240145424203003101481c0031004074a449000e82c5002500780041240040740745126504a806129406010703250303182d405103003815500041038083e6110610040c0044c410300e006204a50640300ba040f22031910b09410395984025042c000d00440440c007070340030350441070290303801b889020f8401680d1204c3d0900348086c131340da4100c0746035211007803a052620500583c0319510f000c403a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 659002805 1250 659001555 659001557
    0x90b031009030504170706121815060b1605010c02010c08070f09050d0b100b131e120b07020c0402030606162a051c0519151811041b 58
    0x2922541c1c0e41400d545600030740c1d21600c0000c2860402514104002c40d078001a203025455940d5041c01c40c60300c00084a420f03100e2140b006d9425002c003000320340c5440c0d1024001d41c00d0b80001c183c46840d400c9285242c0c0050b211803c620003100300f94410001d003070190301c454452501c000c00440b0030b0418020501200a40b0b00803d00c10401180301d61107100792458030141101400c1c000300c0200e2458444008c40d002c503034000038082c2111010507202808012113881005082c984a84c15040000307071482c02c000c4619259095405190002e80c10700d51000410425001d080710f440d403403400103006420030400b526241e1003944100304008550380c03517105840d21003c0002070128140c0c4240b62000504200c4281483c40608004090580340d422541c10815107405403003d4480a50505e42031369100d0300c100d4000e181e90017800c6100c06801500d241030b40181e0080403440040400a4058402c454038001d11402c00300612921000303200550a880381c0071501034504002d1101040300c07600c154140c06500e60 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 659004055 1250 659002805 659002811
    0xc100203090703150b0301020a0e010201140408030601110f07080d0f0c080403060b06070510050604150f1a1e070204050c091f021e010507080c03221a0708040c090b0310 74
    0x8002c43c0c8007a171081c40c01100181c000c41d66030b4a0040e0180016440c2540c170743c01907080102c80d42401100c2c04025000b50760008074942181c503403200643c2c80b030800f4002d1414521800c01e40c0714800100b00b2440d00103110b500040c1042945492000303200c942c1321142d15040c00003030040740780010404c40c202c0e012030790400781c0017841c1d01050000039101e210b2001c025000344104034034180140c04550280d801020119810041c0e036200c1405a10041c03101c1c0b244003503105541108202070384d0310000300d207280000410f0b5246440551104030649552260000d41c0f00c0d00c0210385503045003014800c040e00f2001c03604403581484813110019100c411450a140d28105080e00c5003a400c60003000b01010540c1c1d040203880c2500100c0340864003c0c01c0c110b401000003903803603001c56003c41c01c0c0b000712402000c842203001e19002d079031800301040350012501120b0fa002a00e030740301c41481407201c5981c02010b069070b8400a600301400c182c00b09030003e4004a006c0ea10380711700e1410340c7d9000510588164500c11b404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 659005305 1250 659004055 659004083
    0x1203050a03020c0d030b190303080402120717210f090d08090d0f1a09150c0d0501091e150311040e0304060801061706100c0203010608070b0c100203090703 68
    0x481c00390150684207115407280d00858405240c00d40c1043d030401c001a07071140d68130442d1001080c0c14038094440a000700d0b000c070000c2805410311038200c058060031681100d968039038600b0300714202250070310700000c0381d08601600e034000380f00f40f58015030301c611007040b9074203003902c090010569108200c80e00307111303a00d48043c0200700320045081d603241300002801030780da0071203508005202e15a017110858551034031022100030b4080b024001400303511048020506042200d1200c00030140c0504802100802130109020a00c00d500032640605119580401d9003011598400e030000e02440a69a0b554207102a86e41c4220700e0750304903c11a83c2103442c8140802d000408100144031480e1307084001d0100040c040355035504119954100d81c020313030302c0705490440354032125040001034034819030007011892146000ca20841650000d240001e0002a0303a40da5101c91514003c15580007486d00f10010607600744101c0c050000c1101810384034401e5156107000708840703460300c45902004100303034107003440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 659006555 1250 659005305 659005307
    0x50a030e010f0e030703080901020a0e130905010906021213020919150305030901020615633702040905040b0603240702160e06010314011203050a 64
    0x8800c00c003880d10b00040200d200184241600c982c00180241d000c07500e914080740380b0100520860b1202072013541c0b90003012904200308516101140c0f0a01c0b002c1d40c9402441c408182b00707114101d0b290303110f07000059540da40c1c0c0740743d41d40401000740a188644c100141c0c4802680794084a5940031014581d01c0c0000e003000c800d00e07001003c5101400d00e9010300044080308204001000706010340317091f000c950042e40d401c0383c9580e048100f0200c0e180c000041d246045850f44034000460511110b1403505040c40c1061012426040c1d0907002c3d40c61541d29807a04c062802c0da441400080d00c2440100d01c02c020302e054181441800311120704030000c00c544000766600074040a200349411a580701c015542c6a60f074103450400340501790b4003943c41c2c2d04110042201840c0024010300740840a20b03e0004140040395140145c2c5002480402540184502260031011120100000e0811048540703a1820044001803c4800070740420b0241c5400c00014055410140f14581d4035550510304560765080c00e4174 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 659007805 1250 659006555 659006561
    0xf031115090a061103071715060c06061e03060103111f030c030b0d1e03050f07030903110603040b130302101416050a0509040506040905030c1005070f050a030e01 71
    0x4038000c0c09000100500c050000c010508940d4079000e8901030100403544915482944000d44101011403088011540c2081410940e15880b000d00b9181c0302d000c0c01e0a0004c20300707a5102c1d010b406400d81000d010484a841c00f19082e20b40e15620f00c89800d4180382d41e070701081d81d800f018003020740004940d42500e41c01d5503a1200444031443c00405d25910b4104003103001e0040c1014240c107030046410309058940d82d08120802c4da03a80b0344c0003d403c040f4072101c541c2c0401d90f900210019000c112003040100f050400d05002090002e20a0380d8a016a61550400012510640c0007070380c4501000c10600001c1460250215002584410b0346040310f5142e103402d916041ca0f00c401481c0560400035400b0240004404451142440307500c000e20818001310101e8044c4221011030300407400c00c1c480712002d401e041e40802d80c0098094030020700300003140c032001d140d81c00c4152011866885098540d045200600030260007010368240a44007983e00000904940201e0444804060707a84100102d4124250 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 659009055 1250 659007805 659007823
    0xd03061211030309100203030a050f100b16020a060c0c0504090c06050c010b19060e0103060e0c091908030403200a0501030f02190207050a0b090603010510020709050f01150305040f0311 81
    0x5e00c9a1001d41c0c500c01e0103500d03504100c43c00002907140c040003c025010480c0c1c901e02c910068000e281007942041045e4205030041c08015144812103c0b908005864224120019108644032001d540e0f040d03282c07250720343d280b1340c0005004504000505002030200b110010960b00c8509046442c2e00c0010440360052130440040c586c00013104a01c040415081042501038681ca0345d10950721800413001502520701c180725100e00d683d60310000420485016001c0c2c08480e500030310900004541c19030362503400d200340d00314054603000044c04104000002c13450321200078504003560000501c007030001701a0726a51145a040c99155841c1c1d810312000340c0e0442e000d2504001c48640c221032094000ad55907201406401d004076900600802d81942d1402601e01f0340000806007880d40c0e007040203006a0818410001d000e5100d0040d0215a6906501400d8071a2035107000e44841903142400090034803c0029084040c145400240400b01c1c0105003101011a0075041a07840450040e804906d458030702 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 659010305 1250 659009055 659009059
    0xb0d051e010b0304030f030504020d030e0102070e0108030a020f0a200f03240702030c190602070803090109020a14091b2b0e1501060f05121501020d03061211030309 72
    0x41000420140b010401850089010f0799030425852210142a02101d10513600079503c10a030400c9200080c0c0f03e4a19903a03400c2d4180706072140c00d650360201c110510002c0e0030102e115080030568460443d810041034122541c20402810182c0302603d4440307c014188002d80324000c04d0262001c456241c00688a12440010381101c08010b48246c0600c00360aa280c500d0900b044140085a82d5600c00000d071400142c42202828441071840741410126030b1000d000c07200240c0a108140204001d440654030402c189800401c00301510b204210302e004450704a44440c1d00c0310481c20120341c031030f030406070b03800b60409140400403000000d10944a0043c040030355180450400506040d034400e000040c540c5081da40c0c180702d48450700020685948005840220291840c0c004202443c0300f081008810503680c01c1241c5882035540343d0240b00c0c001221005450345842601d0141540c0c104032410626040e0310741002441c1c100710307613122100c0e81b001c4054004e4142c1070000800e0307601801124200000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 659011555 1250 659010305 659010361
    0x18100e10200f0c0703140d120e0c01270e010f0605040e070309030e030102041401090f0501050307050d0f11090315090304120206130905090f0a0503030a051f030803010f050102070b0d05 81
    0x180c080c0d250b52a187d1900e810000f035030801c032200d02d030b503042e00414684808034405083d41d56140d01c011034080491078000d03820030840c0d440350006905284014006050f10185900071581481200d01c0ba00d002e42d8003403001c002080004005948508141c1c1c5d0b0040c6845c0b07008106664203003422210140388500407549540300050004907110308400b40c0e031003c0b400f038076900d90645d601c4191001c2082c0b20301c1681d002c110f0800000380707502d1040000f80070034030030b240d00041c012514621990440390301001007842c40c08000b6a8407110314041100f00010f00b02c3c007a5800032440c010002d65140e01580c411502c400e04144042c5c1c04668807502502c4241e99490200400c080e61120104040c284c04c0d50a40304602500500c0800c610700400c010440c2500100110302c3d41e00d555408600400f0010008101d4030383d00410000481200d4003e03400a60003800203c0d140d5041085c5004807107981d511207810b42d44190001c212072003140007030716a60441000000b45d40d5a5035403100c0250a03401c0e04030b21100030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 659012805 1250 659011555 659011583
    0x3120c0b071e0207140f011e020105072007050f130e010501170a0c0b071707111201232502100c0509010818100e10200f0c0703 56
    0x10740301e100c414034100b100440072003060241c001030740c903035455000301c0c200c085402101e00118101100711036070b510010700d404820034060101c1c1d050034120030000100180d4544003031182d11030344421040407101a40300500784107a40690481d90796041c620880b40202517420b00c0c0700c1950345000c1304884103030340c1d244c0610008a80f408079a000388424051103500714180881d61940450018041d00300c164070091079458141401ca070403041d9003051030201c55001c445021101030359003d001600040340f040001240b544e28003010040000c0d001860140142e240c2480e880d00c1240b050b0202000c040d00b4000305000341c4805959805c40c043c040c02c480c8200d801c190010040da42e001030029821684061f0410071240d4920b003c03074180c403c4948d0f0f180003600c00ca010648240c014403c401100002c01d00312030101458809804c19540905c01040d45600924128034038802c1c6405002c40b4580060b21141d20480c4070700b15150213000d10000c09200d07000118a03050044420041d03400910b4020041c083c1501d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 659014055 1250 659012805 659012807
    0x1002010b180402211f0209061c0e0c01020d121d03040e010b040b0901031503050d03020c0714060708070f020910031209060203160215040909140607050403120c0b07 72
    0x5801d40d000c0340241052640404c1102240d0005000584002c010780400c08445800b010000d1190f103003090125400c015083c4190380d4000182100d24041911805400c00c1080c00d5048031070700b40305000345c1d401c2003c003541d9a80c1d0120311240482c18500b8080c0d041e902c603d408400510440168040d42003101801d44600100000900200d90706216003140e507a88822900703085001c0c5204400c1404000c0c000c518045d03020760041040c0c0c0c610f01001c0c0100c507a9a448162400741c1c0184c842020075400101403c8803401401460090200c03084004a550748a40c00b0800610501002030100c000100c3c81900b00070910306104941500101242d903d400c1c014502c090803100d5120848004500000c0c2c0300c031080c00340c4d500303904440f201d030003a50504452001001c03594409071301c102d900ca282103052003050040706019101600c40000c001803110210f26000150030f24a203018042d6600040800c50b410364800b00700c900b80c1e6400405107082c01c1d6000000d451040b01c1c02001071084040c503003008001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 659015305 1250 659014055 659014099
    0x606040213050d03051c020403020a14031606081009060f0501030207051903081006080708040213060b0d0e01061d06060a090e0a0f110a17310c05060301050f1002010b 73
    0x1540d6424446c1c442c810062039810124400d0380700c000d401c032244040c01c100f11100456a40481040502a00c0d203500340000d1382200d940580c3c1044021581034024050030b025804040d03170103460f41400401c072a50802d4030184150140b441203604041e00010400204201400000c0c410311949102e00000307817041c500900003035421640820072994074000000c1e204d215a2216001c0c141e00d03103402c0002d4a8035020b21610403003d0308a40103264607000c00280420100d00100815001c02d41c1c00a00c42c1e0811141a007551010b51156040090300007884401840c00307100d550300a501100c606035524545401910703004d03526402010590b0140c800c0001d501160f401c004c0290344035510401c03001d05c18042c500760074020b030700444000501440031280c3c1c1c680850038064010b0041c031f1030700b00c51101030780400d40408403d280381d888020304420b0000410499004a002424040b103085080d50305100104541507025044c282c491b000c02010744a240d4003e42c0802c40030b00000d481c50001003500d07500c007001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 659016555 1250 659015305 659015317
    0x1030e060f0f06040c0c03030b030708073507090b310b09071d0f030d050d0f0902220603060608030403110907080f070203041e08010f0c020606040213050d0305 70
    0xc050520b0000307512480c1074030407440108180d85804040000c0ca4404500404415518540512590710003041292082004034001c1595003981c0c080500084518012a60b1100c002150315000c4103120100882c0860185e050b1010392200123113500002001551504810700742c1180d032400d1202c090810f624140300341002c400b504200707000180760310081c404450401c4440c4c0d0300040b1110710705001180758848a0020850080208901442141c0040e00f007007519100074000c501c0000706101545c0290103280c07045121150104070036440ca4002c241c1070b123032401d200340d0300414500c0c1500340721111768010006580c11400410803030b80c80301d8025a803548107003c142d81803144100318007654a0401c100b24410000c9945002040c0c5540c00743d03000c9550050004011b41c0001d00000c04c10b0140c0d0304281208011841c03101144034507040806d402c40f10082211004103040801c42c44e40b1540018031107030003410940b070040c0c1c5c032030058940e1703885404141c005550000540d40007600381a132003809006 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 659017805 1250 659016555 659016571
    0x10f030f080f032706160c1b0e061c0206030414010e121c0204140d03050403170703030c020f2116080702041112010b0304020f101e0f1d01030e060f 65
    0x11420300c042c2d035000c0d614170085950400c2c1c18420f0b134021341502d129840c50107500384140e180c8502e400c0013503d00000c0751410382082e01c04403c43d0b002c2080b00c1c031300032101e0500d038020718801004810349900860741d944002072000d40228824a0500040c840940c8004021507004c400d4556443c000780080300c030740e40f0040c0d4003401e59004808400c13080005100301c404a0b5950580d43c50000844803c2c0656078082900030b40c1480390911002010035221034400400c0000d180480e030303640e46585070150480322890b40c000c08550000d40100b145000005174041e0104e4003a42c91340f0741c4058803104264a1084202180b803d4200c0c101038030801c051100a03000031842201c040c40882c08015030320110b40684084094420720703140041049008c0c200c0190341003030001e03010444040c04100802e003a480c03403002860006004402c02101240052014a0018203510308521404441a0020b0251706000184844a123514203105910b0b0300903406000360196200654a045c40c1809464413603000494540e0303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 659019055 1250 659017805 659017861
    0x40303050c0a0c060902150307092909043b150405070902090a1a0711120706030b030703122d090e0a06030203010e0d1403010f030f080f03 61
    0x4079981609801d40380d0340303011039030f8115541910362281000390402c0001aa000f80b0a2115080400550320045204000c030380c903082c0001c2c3c904038050111004004002c01180300c1c4420300030910740e400c01205c88140089401040078108482c95442c81c0c40e4a00c90711541d03841a038140c60010701c2c0302c3d0003400303c00702840035582c011803980c0c10340d10b90100443c0c00802a41052005024001c1c840c0d010301003840c7d02900142400780c450b1568806100e0042001c800c54401252400030094210898410382500780d41c440580040e6401081d034072141e40c056502459151450b0043c80d1311300b0080c4900854005500e00d468230031400c000382109600c10030ba1150880c0b1003149200c2c00361400c110203c9120700e039980c89031039483c0080c440e400d000e001c0c2c0110052a1201c0001000d40c1c1e0900038528204100d901034009141c075444090900c2e80301c80d0103182c0041080c030040120072a03000300d2004894111040411258503443c2080c91481100c21100202c0e0000c0140040003100480c1c003484001e0a01e220 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 659020305 1250 659019055 659019061
    0x90a0506091513060b0904151a0f040b030114040b0609010e01060c0b0705190503070e0d05060a09170c010605010801080a12050906090a0914100303090603150503060f04030305 77
    0x242c65184100400103164000400f00303010300700302c001e0400b003980101c0300050500c1c11100011545117081d039042d42c0040c41c0980340f06a038412807003030440c0310040180e4001807400c5d86020602a42103810181d10460f95640001131a0314290081c1402c00114030038403000e442d0a1a241400400c02c0e610a80500c03031000c00400d0304400500e9481c1602c24030340380c44040245595480800a40003071600082090a0012602c00c1080410101c42c001361602c078a504e0f8030f080380300203081550640720140719415407495803000c540080ba43caa0000f9807154042409142401c1c50105c0c80e00c081a441c801180008000388010300650008096070001d81c1c03010516607039002c0f50b40e5074112000010740340c1698000d20210190054000f45003d0002514082c14012584000341910109070700010499440b20140c5c5580c4503118059644060750314180088070381036440052825255009003420305580e8502410b400211030307400d100030038002b812150140340181400304807580c15641100828209004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 659021555 1250 659020305 659020321
    0x901051212030a0504121b02100306050603040308071103090a050d0303140c0c0c0d021c030e04110d0e0708030a180b21060603070f120f051006110705180915090a0506 73
    0x1607c09003000c003000000c00b8500580810500d031002c1041203090594a503000034050712100c000e54801c6001e0b844001c0c2d41e1810348409880d03803c1d64010380303000e50020005002d42c1e41d07070141c620082d504180c8100e1540c960b41c0c81c0a400034034010710040804140d02c400c0000c2065000020400c2107240e07401e551080c0401d6044c01600094440002e520282010213024002c44950440301a070f8024501090030301d0b180304c0442d049801d0040700710036030900061640c03107428880c01901c41043c045d40050543d14500740a2a40b01c0c002d1001134001c0186003805024030301c1c54000031201030013600000641da011240703103002c641d000700c81d0500c482d031800310f000030f030f1501e400e200341c07489400186c9039144002c001c0b8800f02e032800807146800950343d039640e070705a40c08132181c45514410b03480b02c4602e050f071074107011014084034108005401160f02c103031402d109503110540007100341c810741c8002da032542c0c80c0e02c240c007030034003000855110100420700c0803c200e00b44006600d180f401c0c00303401034424503192400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 659022805 1250 659021555 659021567
    0xf010207031713150c030509070f0b0f0f0f0301080606041a01030c050c07080c010909060b09010f11060f1f0803030112050304030516051203090901051212030a050412 73
    0x2401092495441101007405804540c1c2d00100112903400f0b240d8541d942c103140d41c128980101000d5650b5104104103a030903105d050b4126800344000c0000c0c9141c41061160400035010300030751903a01040f013001d095610016151446444000c0d99180c50f103400c0c032005181c2003481500814491079000c00c02138100f621030710310a04040396001451074254001034000c0c000b5000b40c542002010005640500410f0140d40c001d0410b0001030a1070f0b1150800050001440d0f0300801d110f68909141040031000a43c2120765100003030a1070f60201020300010303290189514614541e0707004641c10000d143d442c0d03c031218407903070100e041080026056900c40030700e9102c5006205880d801003005001014403940f00d0300c90301d88103404a91509880b80c0c0c1e040c0c1411a5006c3d90311407401180818000e03071500c0c03180d0420706001a40154280b0365640005540984188240340c05000e00ad142c9140c4e80c4400c2c022010560b00c074652540e61382c02c088101c0f02c01010f04a90541d01e034101101300d4100d1900c901 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 659024055 1250 659022805 659022817
    0x5030705161e0b093c01050f0301060c03090b1209070b0715021608120f060f031c02012306031e0d0e0d0209010801020a0305061009121104110703020f0102 68
    0xc512055800d0a08445405540c080c41305103500054205a08509042c056154103040c01524141001c031403c8000045844080071040ca05000c0140040e240b07a100407425641141c070580380040403c0c5460506507040c400f6a0444040390400003030b0000c02c52005207880b8040d0025074100e507861541c0c0e031003a2090b8015078000820f40900b1030304c02e82e40102030340c014000804145801609038212035652421590001c56140b03002e8900d00f0802c10900754444003940d0100050b50100882001d8400281d1224000284103c00316188003c40c4801407003503001d040c0740f180e5004002d80800c01000c1403060a40110348a500c644201c1401c00451190403480e0f03550310700001c0040003041030300c40c0142e461180c10002107811400d5100e01002582d1850b4420780242400c40005a0319a180c20005064070710043c403841c000d10703034441030350070550f4070003c6401107903c4000381d1500d0081510741103a0156420280550280c1054072100707001c51113800a01c100f912036000c980b9260b8050142509030701402e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 659025305 1250 659024055 659024099
    0x60f060b030423210904110c16050901120204050a0f0204090b03190506010e09010e0a030504140a060509190503061005010809060906041401090c0b03010f0b091003090f0503070516 79
    0x248071380c550040c0c3c0f54405000907200c024401724084010b5640b01803185c00c90610a90594004005a0b0281b558948213001400c820380d4a498a58100b8602602e000b0a0b000003e00441d560310000b144a85980c2c011100588901c0096558554901d4041c0240ca440082240319000f0310420648007806100c00b942c40a5124020344416840d08904110546004280076495521501c1c01e010b03c0d4002d0184088403486078807459111400c0050603280b10940300c001c240191180358041c003100c1d411400361000700708116003a046258001c3c4a41d050041c50b81c0c00316400d88110307418030565002401400b0141d03102a40d850149590b145515991000180d0f04448190048008500481e561416040300c4c100448004250b1508603660382160104d80e611800c4d149501100502018610380b01d90300090201c0e03200c80e410700c455840080c8542000790303c0e91043c035696075140f108024508540f180e41540201c10740b91100c3c040d040140d11035140b040304680b01080c001e0301080b1034450001c4d00300c81181c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 659026555 1250 659025305 659025343
    0x30d061e0509040302030c010204031a09030a09230307031104140403080112210306060909063008040b0c0c0109060e21010c05120c0405010804060f060b030423 70
    0xe04400d200c64150b0160058085010412003546941c03024001400250320a44903004408540700c15060040303005404500e0030b810410a4949042d801040d07041507516003a05e1001e031158140082e46d403006e04482a40d0140900b54000050200320f0f50010820381e0180c4082c8001c5210401041040e075040707d004020429130350052009950004000000c035228200030501038005580c1c0d400104120541c090001c4e48031102800307101d9100303a850004200e00b101c2404141e0800790300040c0304041000d00d445165441400c551528803c40c1854081d41c0c21036030710707075480d91a22204071440d886213010702e206120301403074412107501c0707070149400300da46d150b0306d25403d03420502c1003140031130075883c0748074105403003200c9191080070070300c150712041d02c1a44aaa80d5007414952580755114010300f031050505050200300710b80d0741c01000e80e6501982c0300500140b04007003034512a004184035002900c00d424044100310403c08491504042e1500d055400000c103100304030b001d45d60301850034011651545d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 659027805 1250 659026555 659026559
    0x60a080607030b040f05041101090905091b06040504020a12111c09020301060e0115020715050a0f0215190e0708120a030b151201060c050a0f150e030d061e 68
    0x4820f03440035040b280d00400108250107841c44090550b0400d44040d901002c43d14a100480d42e04403040c0300c010400358006004030f244c10220740b6110780c00440724031015000d414030f5102d596034200440d0042c1c20020030454640601c40340040c203000301548103504451600000300f11140d06e81040d035040103c81b10262100300070b20740405c4003074142240102d80649d207070000400c4c0315401c5904503001c0c10306d007030f03054038004554a4024588111a40201740200c0700340960071042d64820101d8000d222181004504000d86400880c1b4050310701d04081d440d06580300c10b019035040c8c0205140e21352200c1e20b00500941c46038046c1d89445080c5c40c0f040c03440d20f9201e021040d9492580c200600440040da0030300140e140c01204c086980030030070410b030401030140019207034a614421109a4050645407418245c0c1c2000d680c0c40585e101300c000c1e0003410a81c0581801c81c10403458440c0f51a9140048800b48403014562085c0c1e40e503a0010301407021070b01c1c00c003040070030a11103c1c071074401804460700c40b056580e4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 659029055 1250 659027805 659027807
    0xe0f0d09030f030f1b0809011701030c0506090112020c060a110307020c040b0a08010204030b04140615060d0e0f1018030507020d11060c1c0e10030e010605030f07030b060a080607 78
    0x1140c0ba048503003c0c000d55008220170803d0160038410755a000c0d58146d40c1c0c501e14100014071401c0c603405441c524108100051021034040540d0b542920400d581855640601c440140c6c0d01d051081c80111340e00b8000030300708000f044003040007401240c000c4401d0280d1400a128500c180c081210b0342c074010381c41500280306928194010030600340f009070441d0201038403190740314207903030054009840ca00f03a1042071108018401c1000800010040c01030410b504040d01d40d00d40a5502003081d51240c0c5000c134610031078030003642c8501540304582c1c2c2100c1300d54003484004da84500f55a0070101105160804840c0a0380102e50704c40c0d4540c0d03040d6659807504107503034200600c000d074692082d2082d2021501840c00742d00d80c14000c001c1484030300000c2901c0144c1018011548840100c2c5070100150064000e140351030380304558003280c1d024200401c4d040c1c035036100180107003030541c016641445020020352041001150917020780e07014444030a09596070700140f01002c001d52044071040e41c400d40c001071420f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 659030305 1250 659029055 659029067
    0x1809012709150c08100b04051005030604150e0f0702120403030c152a03110703110a0206210a0209150a0c0803010b0c100e060a15090e0f0d09030f03 65
    0x45842000703001c07030480100344003030200e0f180050fa25001c6510a0280321701450f0710301d143c00040c03500b82d031032924250511340803941c805a00100f0100f8418080007144540d9039070341040d028002084c2c2c8045101e07940f0402c648003150180c408008204200d00881e0701c072803011601c4403803841302c00f050f6841c1c246541d07811a090041c4503026140704c29140541d0f004500c070340c01507aa080ca14800401c0c8414404007400203112248000702c0280341c60100005940c294030015a9466a01420800030280500c1702d91130900b0742c1c5e100b000354844400102c509801c0050404401e502000020098259031000c000c0001c034480c0c80f007403690052121440715107028880b0b00800300b82c0103515025050015a503107428040e0000e800c1845c0c00c0f03c01040440842000708280040c614010009210f2010341a0244e0340b552030182158585c55242c00c19038041c1c0041e030f1112001803030989000c208800503030964684030983d00107400042d008449201b210280300301c0e08001039030f8101d18045c054030f100d0f903029205 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 659031555 1250 659030305 659030321
    0xf091b060c011e0204150306060e0909030706111b06010b07080a120e010603031d0a090c090512010b03061621060810060504050117070e0603010b030318090127 70
    0x10664880b10705808202041d4140b49660480f0480540c82d542440c80282500702400e0901e81010326240c0e040182d030707500c505000c664540688025449440340255541035202d0038401801c05070819208400d100f6461000300144800350034000701d4031100da15500d40f5114284200c400710042404814041043c001c0103108400326400d1825400550718400302c2983c035000d10038240343e59035403010400d058000700008501c0441e02c00c03082e82500d9140018040340e0103401103080300f642d0354ae0f4081e45a4040d61041000e00b40041c94250241c220300c0485000e02140c0546030b00038060100454a031034101d10303c01c1d60404490b04d5034140e42000650107010303103910720b40002001e510756000040450081c052505440c05aa0300440c0c22420302050006855047c6d00c50701065603103a50786681d8050100c2d000c400e64489024800d20740e00c41c40c000070b0140240c1e0781e01a074180400030758800801243ea1042d50044016202003089a9840140b02e2030080844040042011200300043c00140c0d10b900c01a4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 659032805 1250 659031555 659031577
    0x906091112010e0616091205070f0603050c0d11040f091b050f07030e150304080c07061d040b04200a140f0301170a061b030b041b0c15090b0f091b06 65
    0x400c6c0c1d40d1781d0980b00f10030310481e0000d40321904038030790903c0500082040071002d4101800d05000ba404c14100302840c2d44901001181c6840c1c0d200340c2644c1d081190802c580c01032541c4d04044400c1d503111101035008041c00d001055030b00e40c25505480c0410b004106403000c031800818060706080e5182c5040d034141008000142e8403c160035105564040c040000e1f500840c014804651a003001c0303001030b45840c0c03e5400c00414050400d02c1d10080110745200103441f4038050307402040f11030040c400302e0044c03c0f408089081c0101c00040c00082c1c00c400c48013400d181182681d4500c1000c01c0d0001d00c00141c0300320000350203ea80c0c00c2006004034400602c10359540342002c2c044030341503042c6813109401c8490307005210b010300002e40702100005906000f1801c550100321800c1010300004100001c00500d585565014407001a09490522034500c03087d0746000c1040030284200d02c0c0c00c1c5050050584102c610b405201c2e4030502003808107800007607041c2403120351207005d030b24021000d04000c8282c014039400740d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 659034055 1250 659032805 659032817
    0x1050c15010303050703020d0c051915020c03070203060f0f061c02030d0207060f020303091e0f0a080a120203061003180221061605090906040906091112010e0616 71
    0x1505005403200c9940218080e540d0a030302d4201601e00281030503488001c10042204012842e0040b0704003048004504c04c010380411610054ae21300110701c5081030386450703100e42c404148502c1000011004107031071031013241076030030565503200c1e40110940300303454000c0120144000100c01e404c0148404e0050705916a018002c0755640e8002850010301000c6500160020002000071941003000b070806110240051402c603e018140b0f00e5070b510440c449114003e01c404001c03c1c40150a110000765111404140e60701320601e8204180c0f198841c044038000035520b44604012007810f44240c90140d90001c10205085141c46012030150003980c04c0080b081021440d40b40040e503880015150030340444011002d40406d007150207040210041c0301d80003018a64007500840c950110031902c9a18013110490020340b03403400030a008004181c801040755180c0f001c082c0501c11044c48195012504840020f9004070501809003a65003070202c1209907072041c0d001c1442e510625505507503a001d50710b000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 659035305 1250 659034055 659034073
    0x5180904150c02010e0303040602090d172101050d020436020405180a030f1b081c0b062a0304030b090105070e0f0f04140a021c05010506040501050c 65
    0x48181006031021210000e0010910071050400d0260400c90240d07800204091305892050342d03224400200300510b41030340000c05001560343e200c120799000703411107851400d501d2010700140c19030744100301034a90241d05481d0220308002d103110190523200e000c3c0201c4141507040e420300000c0d00c00040c035954109a00e1100c00081b00804144c040010595181c400b0b1003d141c0c0103201c01c540f005090090107001010480f903401800080c0d2500d815403501d001044580341540031509058010401c03c9003440c0c09040c0b03014071520001404c0c81240c1a8101d120440e40c180d6010100c4121850043e00310700e00348039000c0e1208008081a034034444c9030f42070710340d50580c01181d80d040d98401d4000700c2e0220003080500440b41024800c00354070030a94205070003454030b500700095240900d007104d070b44030b05103010901015448607004009401a4040700c2102d50a1020f40200071307401c08140e1f180590840032851100501038001d250498001030221403806041c9801141c2a90101c80c0e141c0c2288212006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 659036555 1250 659035305 659035309
    0x50a060905100501110c060417010204050315012301020d03110723070905060d020906030c120d0f260c070b070f090b030402090c0c07030204140a0510060c030518 71
    0x3018410710680b500648075504010000d092032066240a0700b01e640804c031a43c101d6104c0001301d6050f540060101500f40e05030410302406480342c1e410043d014000c6100c010301c00201504411b058528240780c03103049031031540d2200d005140000d2158016031280441c0d0010500030f501201e2075203107840d20f00745070443c40c1c0c9400c0d00c50017000c800541c102c1d00000c04c44a07200000c3c01010f000d004010f90601882c10403074002115000031010191290340e0002c049441503400700040a00e0080c0940300099040a0b007004d1612262070507103100200d44125034a003a4103101e040d1111402c0c07450444140f180c40c075100d046007801e00042c500c2c40f841008005210104802010861003011155900d080c0170408400c010400703c043c5d441100395080c280f040c040107a6550707118a41c02121032656903191603010782c04c146000003a50029401c2881c0003c1c041c50780701c50403a90b80c454050724109100e10b84951030603650720b841502c901d10019024116010000e03224074001c01166111007402c3d07450100c5800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 659037805 1250 659036555 659036561
    0x20c030a03261e01050a080304031514040605060f0625050307020a080606030106051804062a03090b1608040f1a0106080603010b030127060213080303090c0409020a0306050a0609 78
    0x180c46540f00d0071514810844000107000603000d884140c078804005490016490790700d00441c00014850103550540302d104416544c8a40c85003080c88007284114109820600010319068800301d0080e07403031007000c50035400c02500701d44e82042d01c0c039030f8100c0c0c0340c14410300703030401c0300c2982ea00f1500c60104008207070160fa24000c0392009020700f04040c0280d07041000405084401542c4270b00e005010000c1a02d0099940b4403800e0750041c1c005001040181000082c0d12a4607519002d4142d03450b4160814000164158440f00c00540b1500c4401125244c0b45510703000750310400d50900001e240d0500040025060a040d4103030544a94407002034560001e810f03000c40c29098000c1e0380050204dc04200251509020b021540d4505070002c1224640700100443c0d02100421144d11081900140c90308110b000d0741201c0b01c1c0e0b201040510b04040c0c464080c1502d0380e0007071f075805e0001d100c0c80034607030082d140a100d80c6078a1036004001c400c0180c51079440f079028002c014030707525189a0312030001038100d6542c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 659039055 1250 659037805 659037811
    0xc0f030405060a0e0604031436040b1206070f031103011502061b180609030f03041a0c06190e011a10020115030f020604150e0f01020c030a0326 63
    0x702802591800c114004110341c030080030a00345034801014000030075008411801010b501400203070f666004074899035500c031002d946003d00101c41d80108104511101aa016010012101401502c010f607040102c50182c40c01007109ea030300f0003404550b08038080c50990080c11303401d0a020a1640700094001c440390800d074030011030301421200a08c0103550601070b81d0303070119042440e2941c1c042e8080b1180e103540241144480007020180c1552160350b24202aa01d10b80340003021201c0241000c0e9825490303410601c12240c418804185440c010a00c4c03105448440003680c00900e0701d56501320f59281009800d65607446415592001e4054144081c0118000c82c00e0782c1034400025082d100500590440240802003164545442074070380d1100e21004600312172f0415000c2042007290300014541e4801c40d4040c49400500207031450701d450f00710300f00f403442581c00c440d94010344004a0041e80c80303082c00725000e6415040314542c1e6000070b000749110708003161800c0c0d048010072600070050700025001e03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 659040305 1250 659039055 659039063
    0x3060203270d081b030108010c111b04021b0a03170a02070f0f0503040b18010f0305040b180f010903050d050601030c090b0d020d0c050a0909230c0f0304 67
    0x8224241c001d5014466800c02441e250640031100c0d29801d984071106404a00b0400c00c000d000705991003034040b1050707800b840130b226059581d6511a0074500808a580c0385001041103c41e80040034000810314007486007101c00c510b5030260f001c1c0d0402000354001c3d5500400144420f0315194610010841302440b28441e0b03c480b0806000255050031030980100442d20031801003200900256401f0b1151035844c1e80500f501a4400241c50502d00394003070354100c0e5601c1d503004206401c40c14200e0b404100110400e888040c0c4182062001310203481045a000d004ca0007201c002c65100310030b1b4080c0e528220701e0002030b40c5400950324100741c250781c0c0c0381c4000c0d0700081022618201c140003500c2126084102400c0400401207030b1240940188018490480300c4003001c259600c0c1101c05404994200d10002c10800505803080b4014040d40c00c000c1194000450451002c2101403091182e00c246007283c880700341c0350103078041084686500c01840704c24444410b20649000048080c0558061442 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 659041555 1250 659040305 659040307
    0x18190e06040f023906071d030304030c060503040515100f0f0602060609040609060617060a05010e1b0d020a0e090703181202162607230a0f030602 64
    0x34400c00c81540e000c05540b82085104004020020381e2000000c6000210800c0600316071000d2403080d144403803410107408160040c582000b0403907901214812910048000798007200300c41034141940d90049001c02003c1656510b0107004480c021409582c1c458821002c8800c64a005001d03050288003d65024004099071707030b0144450a219818003020707010200403400f080b072808100030341e6008003801640c082c00000003c542400455000010385a030041d1040c40b003155102c4040c0034407030801299079980c1c010140440d050700c11314003800c0d048602c400d9428845403200311018200803180d134030f0300c0c2c4510810890460724662a002410748061991a21145d070340402c801d004174030500a241c0c10805141c1020310904080a15554086070307009005404540740450040c0d10f03020b0404031a1070315040b20000083d02d64481c10f503080300c0c204958520900400304000c21a03981d0014007a00340c00054aa17403c8410b0b075004040304810450050155106955a6041401c840195001940c0c0a50 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 659042805 1250 659041555 659041561
    0x91321030b01031d06010b07030917030d0e01050708062101110304021014040909020604050319050d0201111902030f03090106030323090915040c0509030c06090618190e 74
    0xa00f62142c41c41c0c2c85a140e01048105240801090311102c0500030030300c60400200c0c0c3d41003070604c10344c41800030300a5041c1c0140c401303084071130b10303541c9030040c43c7c0885c5010b081001d0080f10380d0040c02081d0107000552244003e9440e10001c00220076109007128600d00c80007030508040c10f80c24014070a03032900d034800107681c03410640103101c0011840110340060040c95000145650281011a0200c03a01840d00080320071041c400100c440c0b103186c0c492176240c03003480880c802008208407500405440f0304201c82612010312030503400d0340c003040842d180754441403180c0f20a9280c100442e00283ca00c0d032050720714085000b00301d00c5250304141c03a0309a03242c0d500c59043c020542c22050705070360150300c030a880101e2149034980003414420f007025140228810f1000c1a44250034041050741c0d400028010701c0140315a0100409580001001c00e103c1c1c4a00c1400c0740f03460078a201121403008000c0c240700d2600300101e20500c171030701080c03081c40e420030f0214800e40c2003410311440210141c6855511100300341 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 659044055 1250 659042805 659042807
    0x301060f05030c030f0706030917070803150a0f0905090307050109030c14071202040c02100c05130b0315091f060306171c0c0309180902031b091321030b01 68
    0x40f800c504050180c0c0c050302d44007070410b500061101c1221072918000c107149d401494061101c0a008281100440380030484404220088025620a200c0340c15040040c01401c42040b4210090b84a10000100b661a040c40b54041681106030700c41001400c0340d2501082c0d55aa50865100c1902503001650700f03541201017280304a40c22a01c9407180009280050802c031440380c0c0980d9030070b40244216a1203103030900319802032040512040075940100086d1000b1075001c0c00c564082d14680301e000c00d42c07031004900da41801d070907680680307a40c83d07003090708039003040a10021034000790440000d103100d409201c03e403000a010b0131020700390f5640e0218507145804580e08003809503e1a0302281e8200140207005148001702d2240400740030314101e4428429401d00343d132890700c00d17041810f04040c800860650765049400c02e0261501c20303402c9a050010355404030f50004441180c10f503203c85140f0100d100d10044101c1080b00c00e00848000c90300420b0000c408100180a00d0310304046074440510346419 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 659045305 1250 659044055 659044063
    0x90715090503060117010e06091f05130807081c090201110105040f20040e010b1002191104020c0a050706080c0f070b0c0913020414010908150705090301060f0503 71
    0x416050500d8544103050100203030b00c551050007000c07003002407480040400c0d04250801350b8802d00b400c040d5542400c000d4115621192440800421607003808404038820010b849000d2090300e802e040c410380140e00356a0802a03501204040d070b40d9035803e100074408010300c800156884189042d001500841c103100240c4500d04082806c0041e0b4500030801003c55000121a060ba55010b58045101d0609048000b2120f4030404126001440c2600340301c0c0e4500154000d203c500070031500c0c003241010204080340e071032520030030352016541741003003d0340001c0c00e1502e5080000b5000b8405410949448a80303407600359801001d40706644103503402c200c25074000c881170b41c01112200038189012550700e503c14a1b8820300034014005421200010b042c0c8403140d0540d00002c80080900c1d8103480120888400f03900b10380924051a0059006414290f0003410800111600f10303001d090301070f44125130140075a00080c21341e01484010040700c0320320354080c46940064114940b104040c0c6042c0020305143c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 659046555 1250 659045305 659045339
    0x302030604060e060105180a17070f1403100e0a02270601020120090a0308041d010509040f06022a0d02060a09020109231806010f0e060904021e030907 66
    0x6140f40820a000c2140d9000080301d2441c1c1d43d580d610540140008041800d924040d408244017040d2500c0b540c54001006c140e503c212500f2001c2d4107805a101da1001070214004820f50354542c4c0104030b0007059121a4100d10849003a16007a07a00781203a60300402d64009000404000000801044401c1d10030316210710703a0043d01c203100811010702da0241702c444c0c1794030207804140b051101043d035a00559840321400301842c5d000c1c0303485841c0d03a541c0c0b84090b00807040036145400852001d00100729800c003d4103661141d030b04544250840b035055103602c0000d40c00b6450ba1002d040c101d801d401c092004000c080d940c248040390091100079643c100007818820f000e40301030f480c02d00708402000540c3e40401c1300415641c82c50441c034105c0c5c2ea11100d080003483d0300c03405035401c800902e0007250307500c0001c0d42d002e224235400c0e2641550113240303000c03c48510218481a6074050340030301c41d03801103044c02d030301520001c00600451100c17510301e1785207420541c00484080c680d030303442041300b07010840d288500c05003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 659047805 1250 659046555 659046569
    0x1c12060305030d052a0d1e0c0c0b1b04030b27030405010e0d0f240f0515030604031d0303160b06151c09060209130b211f1b030203060406 60
    0x804c5003109140240a807145171001140305489007035a45070040708040703a10710844200c008102009614002800c442702000307080c1c2c2c000711032400040040c15420034100700079010390103140c43c044c15580e802c3e0444801800c4481000c8403605000c004025420400a2001001c80119241c900d0030000400c4110141c12581c050038100c1c00300400607154840941c03029034000120306041e04406011207000d03040300c00c0394144d1410492621007100007030740918080c02421104802d00805a4141603984006131b4009000405c038006150300c41120804010b940300008041d241b9200b0305401e00c4005541c0e68109407490000c40081c480c5501d0b1420190103502da0201c2c225090020650029032188041141c11000c0c1d43c81300f6401d070400445074101d40300c07200700a000328405100f14907000c004040a000329800754400b50f60143c0e00120301641c03180900c1d5220b000b01440440311050300c10315120690401e40941e00c0361010340c2c640f0b02c06810180000aa036400685038a0b1140400041e1200c5a2040e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 659049055 1250 659047805 659047861
    0x1180b071706060a0e21060109290a080d080f0f06010c03030b0109030209150f030f300a0f0201060501090e04030c020f040f0b121c12060305030d05 65
    0x401031401684115038414800c50b841038441c100301d601603da170710076000b806900510035a2818024025009500d00b4125014120351084c3e0700da8010b003040f210580f46101c4141c8414a540b501c0220606284144981c003401140c191030750f800d074040c41c1c18203913000c00010450350700400404564001005610005841c47d406890402400103000500c81d42c00103400c15885264a0071a40d018080c000004c41d4003501d250102d00d003c50071484e01f4014031494510030110782688207194503000404004c000601c1016100a014070b90222444c00c11b106041c0107446810740000d05503e200901900c40711a0745c1c0c507286d00d580c140c4da000034211106a0082410b1244001050103c0c00d18421034030361061b490700300200100954000510701355400492941d02a040511103000ca02d2a40c004042409042c3d44004001c00000841c0340c40d4002e10031030b4040802403603c810303c11841115414590301002800254003a12511402e0030356021020602d0840d88a501f030023a0084403032012503030748a106c0384035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 659050305 1250 659049055 659049077
    0x1b011101061409090c030709091e0b0a0c140c0708160b040612020c0a051c090b070f081225020a0c15020c030f0d14030103080306040f0e01180b07 64
    0x107102c030100031119000305100400512061001c00842445070070003822100da5582e0f40300200007a0001d10780c11160802910180c45444035105000c40213150b00c40c04500301551913805c980c000b454000e403030030304001403100e0142041e800c0364020440d0011300809031000d00e05219440d440d08450950754082440c10003410485491540280e40603145203283c041c95030b40f08003600d1006402a4003c4203614020381e610b0008100c0e0019255a4803c14100240010a03481380300f0360302002ea510070300510510070080c1c6070000b1416014009200d218010060504070494500c1c010781c2d204665100718220150115910074184c0c9030045080c81c120304c01020754508983c0c400c0e081100038402e2682849a031081c10f00040d000b4003040060f510050304494401d022081030540e1015072169030004210708114424120306a54100c90581c0e4000b90958650749945040c1b0006000b000f0305160707100c0c1e4034200e01352070a1080c00b4085c902440d8028480f5001154200490755130805040312040c08004a44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 659051555 1250 659050305 659050319
    0x160c0e01030308130c051002060f010503190b09070315050405120306011b0510020d050105040b1f0f050409090605090c040c1b1401050c0403050106091406060c010e1b01110106 77
    0xe0268004912066840c0362030845c904000c0c000103e4021560040d4503c1c44101003035800910a07111b20341412808405903070710400c1c10344445444214920b154a110110404038400780d02e115000484d84003201c1015680303454042c003c8011100b6070f0184c5403200284414450100103080c500035404c620289036044c01000a88544101d20600c01310380d104400c428144a41408282d40703480c070120066558210a199510060209006051041d480e000600907241041503590100311126400c11054036261002510074115034822881000000c00000c10f1f204000d009402800340b28030000705141c10300b0800542080c0c0040c9006006501e00708081e000e690340006549000400c640c02c860b028059410081c4041420302c5d8441040e600340024031401640a8000700203c1c1d010f90020080c1030340300c8070707514140c0d0002809100024030040101c0c040d0318100008042c41c1c20910000a95074035810045070908201c12184480501a542440c40550300301407040c415202c40f80082200e01d040c030003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 659052805 1250 659051555 659051567
    0x70206100e04030905061c0e061b280e090618190b09131208040804090b040212071d240702030f0f03040303031a0306010b0d020f160c0e010303 63
    0x421014011140d01c085020306028940d07840162801400a60f521012000b0015500d1418210b55208514041c000845850003044188c007400d0303109004107042c3e0031403502e040280c01505030451843ca030880c1d642c03150420289a215502c9540e1110341038100c0c8402008650000209054065034603020f003024941c15003d4620f5001d001c51002806901070b6015002c000c05005003c1d50300449110148482800036580d80c02420f44030b5141c0300b0001205001c1180d1411081e01e00800c0000248400d001d41c07121600301844815002d400181081c1108203c501400410b50344c000100f1402020580c0030300134102e1040302e503c0140c3e064008010440c1820580c0700a40c808500781950100c0e5000441da005e000000030f0719840401c840140014105850300c0358401c1c40b046022918040d0f50507000000300304c2d4042c61100040140909a04c0c00020648a038895031501e42d00c20390800c0034000b12086000585246c94901d2071400c05809113180040124407542c210322a0080d10400400020f54054 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 659054055 1250 659052805 659052809
    0x60f100515090907091d0411040207021302180a03080c060903070309051e100e09070905090f060613060f0e04060e06150c160f0b040e0c09040f0e0105040c06110d261003060507020610 80
    0x11374016507800820480000c0191074404460740064072202c0002844214006842003102c4d1a050700c1c441c3e207030340c07160700e54078805e42c40000c002c5038040c80c0800141c5090903005890b0075224580c44049010200003c00703400c00c85100b8001301300041c140c0e0940c0d082c6130300069802042420301d04230481c1071000103400e982006100c1e8075400010000140d040c1c80e500d042d00d0b21209001c03c440345d00e071349841d00030b000660086000d60018003020141c4e0494034040c002e007000c4500d0324500b0019611031034140f0440d0702c0e00e410345000d10401040302d2034040c034040108000803e068588440580d003400701855120105030700c0560803403c240400e02c110b0b00d4400299402c94406c0e8246940c941c01000410b0103480b407001226907182c6031444902444406401c41031056200d084841c01c1d0703d441e03030400c0d501442101c0b01c5180c154005002a01041d018450034151000104114000e0409a10301030340604400c40d40a8901069514100100300b410301903203422030383d140083d045902d49001b5003e840c2903d8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 659055305 1250 659054055 659054089
    0x6020d020a140307020307060c0b100308030c071416060206100b0307050a120c0806042a030f02040911130f05030a15020c060f100515090907091d041104020702 70
    0x401e42e0342052034000c008813094940e0160590f08542e6a4882c050209040310710280d428403420400240d9407034083d130b540800e903907000044508644409038800d10642044c1c408607105c1c00880c00f4172844600401046040c01c03600c484e5000000d0400c032000b8104a0041c1c5090030384030750200180020540042601d43c00b036221b140003600c0d4110488100d840c8016980c030300b02c02914000c0d0f03881885601140141c0300f078405450038441100100c0c4100c80d06074049200e03903003802081542c01c3c0901e100b6003104a00300490507000d1308040e140c1d10382c41c044407111041040d40c3c040006041034004c410206510003850b89140410f88140343c50046500c0f25130600c0014800b03080c04001d4402c1c074201d81c0c1520078001e001da085556501c0c00382c00c0d140600009032020031042d5140000000c1518140c14680d0b415420802020304080060b8107100491750301034030404c144880c0c2107020559440006e07400c2440c42c8a410520342c030f030416007046403408100501d4240200d004203c1100581c881c2101080c00890b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 659056555 1250 659055305 659055323
    0x130f051212042702120f090a0302070504050a0f02131d13021c06020315030f070501050d02070614070c0b01091a0108070201150b09030106060509010c060203040203120f0c060106020d020a 82
    0x20f004082680b040324050242c1640b0110b1302c9003a040c0b031041d84612584441c039842001e81c40794803640d030742c500c0810340040040e445140240400c1c18517401098000c40ca00f6400b090142c803024410b070581e0406075412035004030070a0200a20708446040600c2190030072441030440c02c002c48911001050030401a0041c400f5481248903180100421201b50b900510210740346d060003090030a409080c014068424414011113002030f17100030074850f00b1600305843e8240350070060001c100c00794001000a960301680c039580c4000c0ba0780110b100920400382941c0741040c0340690305c1d10120704c40c0180c1000902900e00f440c80e0f850341c18403010303800c21842c0900341401c06540c0c80500328051300e482d004403454080d00d1f000c00a07003504040080c14103140110000d01c030340e5854500840351402000b5001d03000806c10010300740410034580c0155040750000d0140e90614188414001d815403042d0810a0f1540700012004081d800a01c002c41c052b111390320182107008000c0e03400960720005480003401d200c2c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 659057805 1250 659056555 659056589
    0x20a080402212a060403031701060918180203120307031a0609090907030c062102090616031205010b07020f030703020907030c0c120206040302100507140d02130f05121204 75
    0xc1204000d50f60b42c004001980e82c1e512441c0007400100d286000d40c42c004611400811034030f0045403404c0940b0414044918241d07880e4030540054603000d02c0c0351052400d85201b68026807014080103080c00404c0400f281d0320300f00702100404503249100655241d82c511003040d5555520b8008a41602004581c4822281c440c508280e00f451415400101311040d0300200240458010b204407210155480140c6052030000c25205c080c0d00ca4000d00e95480041017012a00e000126007003140050300920703040c0c04945d2100200700c111034081e000f1550700080440c0d10001c40c5001d95642e051a40180d0103000b086180d507000c42d205400c0a4280740a050312107010041c8079206010600f0040c0e004400014908020000a525000b058405400600845000400800300d80c050107006145039921110010489c1c0d080381d81540041c144100b0007034081085040c0c1415455200d00500074814007014a02c3ca09402c1080e5180c05074844085900203102c1c3d030054511000035a0220b40a003007071340701118 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 659059055 1250 659057805 659057863
    0x3030c0813032009040c270c0206011814041106090a0b0a2007091109040e010c020d030903050409050901020403020d080324210709020a08040221 64
    0x3000d1580407800e0803801060002c10701004001c0e07103000e400c602100c010001d8812091045007001107401525a2104690400040480141140c80e4902800c030028102c020a0109800d03646200050401680b00a006115000821425162500b0454010043d009402c581c00b9020b280c0104007401590b070b50084101e00d902e0f002c00725003507101f004005400f8952210125030658000c10004030000b1551a0804104640818501000c80d84440107003022440e01071640c3c090140031300410345150043c000d000d480d4945000700c2e441855020700210b40741116440013403410340340b034040f0810503042006801c08240c00008403070581e40d1000c03010409503142c1a096019100d2984002e41000300d148030a42400041e8004d14003810707658122008105400360824005038001c0c41c00c582c003803005056203040389000c003003415541d00c00c2c20588208954848584049070008440b40703002c90716100030403045143c005024200120181d038000780031300380700c0301c603076660020480180f0b001005000208522 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 659060305 1250 659059055 659059057
    0x6060d02040f0e01021b210c010f0501240801060f0e030c06030c0c010c2a02010903081c0b040c0c0b04030203090a090e011b0e0d03051309050f01060e0a03030c08 71
    0x482c0400c4010f00c4083c0700001114001e41c00380d11800411051b24004400d04440800d009a1901d4881c14208040b01d1a20030b01506500c030403401c00f030b690340e5544101c040c0c0689008440c001c06400b0441d00b15054000c0c40c0036000c0b41c8001015080090f414010301c203043e0070044500740c8a501c2c0c42c00c55007100c400d40110f46012000c1e44001e07440b0b000481044410b108100091072200d940d80000d1204070034809080e2000080501e840302612885c6e031001c1d00b098070300544650560300500d49111059543d480301c103c035510540e18100340001d16030781401616120700500e440d920702500c080020320610700000341080d40f510802000c051507417012509040c420003c5d10480e40004003000c00d2207a441100348000c1c0008803d606065080c40450b401803465584041c15081d569111101c2441c18202045900e0382d041d241203040c02000c2c40300141580120f503003100500b1002c0f20004690a00d15014100b08105a22810070043c0c8039a0042080d169520711904032541800d1806045141e81fa220100b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 659061555 1250 659060305 659060321
    0xf0c0605090106050a0602060411010c08093c030307020402070305041a04061205070c11210d140f0f0a0306090e010603020f060918071407050d02060c070506060d0204 73
    0x21050038001403004529065004004a030340450b022070001d561084281c0c2c4840003102c3c040c0100c41d0003c250742095000b8000207010900c14a40c10346403050704800a80c0c180096291400c1a00100744c1c640c650130908103030180c1420840020344039124038040040c0d500e00c00c1e058000d005a40101d00001094010030544000c2c000c0d440705500780e60990420040e10b03401c039100b084002442074482c1101e480c2a4800c0310701405036039440300c0820689031110860350076808807098101e5148058032046607c801d100c521104114000f9003009900d406000303101d0703142d016170303411041d6003002404801d0b00c0790400c45030b060f4040711405481f00c44896040c0e00800aa41c003502ca103501f84800320352204410340c0300030140d0348210303958501840481d0910007103008800c1482c1d04150400c110400e0b4542c1c0c0b8080c203603c40c4041c513040c08164110b160140154022000c1242c43d41c1c0000c502410307080d0140145540000aa0387d21400e150860b21020342e1894044c2403180540b200c00d03001002d40d00c803900030f115 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 659062805 1250 659061555 659061563
    0x7170d02130b0a02390a0b0409060302090702030306011b1e050a14030a0912050106050d0807030f0c08070f0312060609080609070608071202041e05121c0f0c 69
    0xa40180c0e51410070802e40e1106003041e00500486281060900c01402401070300c100f0090090020408800b440314050b048504a80d40b0100e17002001031028030b42d800500144c819140080750152540c8144005500301a00c074006542044c4200311180e688804d04041c1d82c0b12468030b1010804203414402c1541110034428286032440290f2402801000034025140900c140e064200a054000c0031540340c3c0140301201000a220410400880020002a00950f802400002001e41c1e481001440603558640229040440840e00030281a081001c40c2d001e00001c0c140740040c02d009640360141c0c0e00c140000285800c1e0390041c05418103201d00c0d1130200501d00103000704801a12218050028400c5105060252280000254050340c0100780314040398220344480141380c4642e0b20569420b44141c010300852582404000703801104614000007030b00c03801d42a001480d0401040c01038040d414042503129501190740d00000d802060601c402054407071806580d6105501400c4075206010000a8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 659064055 1250 659062805 659062837
    0x303071407021c020f0301200705011821080606040329180c0d0b0414030c120409180506191404061b21110403080310030c050607170d02 60
    0x1402c210100b940031101c3c500844044000c00c82c802e00f09800d0b5451940c40302090f140d07110401900c04401c0015115140c170a90010074014000342e180e40424240f540c0c281c901005d6850704100440380322407810000561481c11180900e44400400c601d80b050b444000c119104900c20700d00018601201d119086900e02e0070a000341c1410f412402c64140402c0070801305000d804103408152074202030000390a40d0011302162160342d42e0b100d10001d800350194040e81800204080c4a01c0242485500600100c003050542c580f030070300c100e18040301d140d420f26050342c00d030b11030080380071540004007660b1020800b078100e1284060007540a01030a1510824506900d02c0030500c020041190043d409020401c200c15418a600410403100780344041362140c40c0c40c000b18001c0c0529003040e0004080c02003540009850f05580385e48006843d80112a02201200121030500070418003002c0030b802441d00311402420024240c84408080e05a0300500380034041c00981d92030106003d405582000309080307419 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 659065305 1250 659064055 659064079
    0x310c090f182d05070e03100b01021e01020403050606090402031c0e0d0b06030c150304110307151205010605210a060e0f04140703033516170405030307140702 69
    0x48228042d80300c0e929490346080000280509200304000180703a000203004110310344c41c0c03000000050400500e490b0440c0110303d072441040d000c03954a02c1c0b8240511000607592461414440d08022010346414030403005a401c1c0400b603540091002d4809000a004400d00d1103d00c03030584140b1054807600d500020300c0710440c014050482903051180d58154181d0b0400306004040041040c5a90312001d8400c1080c40810041a10300342c580030340102c00760440b000c8dd525282e85009a44a0100c444002400c403507c1c00c2c030301c800d503014890041a40b41002c60910f1005142d00000c0b070409907403084040c6007000010710130380c1703150840c000030480c2000c0c040c82410b00d0542c1508100d0201c1d4255011708003032100c4d82d01c054002030140c044130340541d254184010325040482104040603e60240d0b80081c00b011a9400300070100e0307500030007802402c40e040d410360b060090010301104914105400a240410002c01c8021040741e6100310755142001d040e81201441070b109015914000e03401c58880ca5034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 659066555 1250 659065305 659065361
    0x503060a0617030304081b030405041a01021603081e042d120b01031104021b0d0e18011403070f080106050a09020313020f310c090f18 59
    0x10000039600761880c190303944141002e40b1a40d03440251030040c9100400c00c90401c9481c007406100d120000c16000f0f0700c1c45d05990b0f02c00a004d540b0811005240e0840c00603100b00c0a41c0c04202001c00095803c4880175600e18544444400b0f01a03d40c02400103a0f4682c400b4003000c00706000c690103080000310b0413850b045281ca140c001c100f0400740c1208411310120000c15034003041b140000b82140d100c11103914907030131170f034814038812446c04200d42c005400b4801e8492641805003006500300c01c01c0000e090240914030010310780c00c905075941340101140030741d1002017002d0144a5064806014900e41030390504800310b86891500e60100d6403414071901c0224940e5810b4002c14126002183c0310034155403100c505004030f20007503a00d800210312441d0300e08014108420310001040c4010070650354070751030000700785075840720356461808241003107031070198009184240c1d1880451032070402c44c1da078100400021200703014005d00d401d00d4400c242078a5101502d0704020740760710100e90601507600710841 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 659067805 1250 659066555 659066561
    0x31e0b04090b10151e05071e0f0308071d0f0105070f05060a05010f18090206041a031902070308070c021f030c020c12030405010c05030c0d021f0c080712060503060a 72
    0x20318030356143c440d101090524460762002489401402d11740305c080c80c0a0600313803080d42c0b105e401102c19a03410301800300c0030340c041041200903502660111026000c0345c41d00408031040200400123010034103407211400400ca80c83c5807003030740c0c0941d885082034810700f0040e00d00f8090340308000c09009002c030115080041c003207403c50151104290900c001c1c3d0301c0b42d003103c501410501901c03c0c1e54400014804071912a13410404070300380054219450720b902c03002c043ca000d290700c1a103080009000800e11001600f0740d5241006407001480841c1803144a540c003c041c410054001d00030820b031184142c00390340d9401d00400c5511810420000078860590024010b41403000c42d401c05405070b040c14200741d0803c8089041e2080141003c4c42ca041e04002c01501c03486061041aa814031060213441c04d0100200300d180c0001c141c90b00248615940d40c02900c1080c0e840d1a801c02c84141460349800b907580d0806d03e40342e004802800d004a5000c070400d20705004011700e60210354075200c1c03031050002c880c078654 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 659069055 1250 659067805 659067809
    0x30204150e0c070317010b0f03100512070602190c171507032f0a0f030e190b100303120203041104050c031b09060708071401060b0316031e0b04090b10 66
    0x384408140a0300001030f00801c20b8248551f04880800b004180c00d04507843c0025036115000c1070020b51115103500114100083d0090791001c190720203401813000b140c04004200400f100f0509480c40c090080c0d50b284807044441c4071790b10902030071068402000b070041c8210100322154111200540c03802d004000c0250005d1101e0800720034245801e842d0309400070742c44a0348110010102450719122000441714114100b03002010503540701a180b003100002e1080c418010030420307084140c0a13a9080110311342c800640915002031001604000081e0000540d08814180d41d4005071207560f14200f043d2024a21031200307510030315140812115480440185014003011200c1c20031440e900505801c403442054000750b032110702441008002207820000f0100c0501c0790700c074042031400001c4d80301d0941b84184c01c0301c129204040100203114203042b40d1210b00480078a0280581c0f00d41c203200c0441d04418200d002c0099444076245500745d1196080414030b9544498241d00c180780200001414440c0c074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 659070305 1250 659069055 659069057
    0xa06090c050901021c020a20010f0c1e0204090203062a0a0207050f03070b0309250e2406070503130909080307080a0b1309030905030313030204150e0c0703 68
    0x110440318030a0744640c099400101042c1c0040c0705050b1080036100c4c032044400c0c0400d0441c803c407070300b020000f4881d00c03100f443c4800d0300d03030520500e0201c0c0001500000691802408218507507000c90f0101e0240b42d04500e95050f1600703002140c41180c002305000c0c00800d000030750544075010038800c0c0f00c1410341c00508034000740c1501c034050f07400807540d80d00c8a105402807140180d000340e10510480c030700018104d070300c814001c003100d1495685820036107490304100c0d41c40c2815008120180062a8080110240c0d0b4520203144001281485d00394010350801030108140c0c1840d410810900c00170b100c0004854420050010b51510181c1c40c00d580d90b584014011510068101000504202c050242142d020342c0146d025041d940d4511044440d0400107010141c5603441d241003000b00d07102c41c4060301700340c2c03d10032010502099034100540b01c8141a48514040e0307000f0080385454401c580e000c0c1c02a242d0465010401404a01c1c00c0e00ba040910f4014540905070901480300c00100803000b403446c60f200f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 659071555 1250 659070305 659070311
    0x27090603031d010809150a1b0206070e01020105390315041103070c080a02150c0307111c0c03030e0303130c0909020f010c020d23151506090102150a0609 67
    0xd10b004484c07007841a110360b803081d80440e030741c0c04039004005c02c0240e00000307001001503508080310107903028014009041000d07803c001c092182c41c6a0044000d030380a4401e0000340003604144c030a108406c00700075154002f110040180401c1000701040a00c100e0034002144c6031a82000c48001080c88042860507100c0c4d032800c891714030310f1401c2006803803090159480d02c10300566691a0b00e1200e52202094004501400300f4440d013100c26400e9050081c3c010100d581c0d10780c0781844018060403511108184c8582c46042c181d1040c40d0542c0440c0c800b04680e180040902485180c2907000e040668000d00c074600000c030402c40f1540398000d00d0019140907480600100395a81070000132903030440c1d00070390006d0305224407580325400b078106120402d20160030091665056100c081941c0840c5081e800726507894400710030050010007903410324110364000d03120981001c0040902c03d00c0c068007440d0240c0008980c00c110783c1c0c0248102d442503141852416002d180050168000f013a0a0045000300d5107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 659072805 1250 659071555 659071607
    0x80d1209110d030207061b2105070c0f15111b030a0c081b1210052d0414071206110c03041205011b0e13060b0714010c050a2709060303 59
    0x43d4900007c0031150f00100710340140e0180c504043d000715120f0b0012001e00904008030400200c1184c0382c80b0091002031910089141402c40b07079038240d90899211820031080800390604404081900003048850461210002400001003428185003900240031200441e400040940e00850003601c001d41c00842046009040c1d410845c141c1d003020300d2150107034032007950480b01034000d030300c200d0f0003080c2808016109001c4031909441400102441c510145049041c0010001821030124160714018042c141c01030800821a0109140200182c0003940301d00c41c00324036804190488010381201010740e0760341d41c0c0b80d41c11218000e203048400c03a299864044204568050f4081c0001d4101441e51002c0c0390841030820008a2040800c0d9003902c980c1d00c3c800043e44200000050001d24881d440801c48a20303213a07142400c464500c8034900034488100300c20310050f070b840b42c4000c410b6008100360300e464504418480c0810803007500845000c0f0f240400c04418142c100c089800e514440d50f003659a110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 659074055 1250 659072805 659072837
    0x10e1f050f0109180209070f091a0703080a320a05150f01110105010f0e0a0513080a090806040303020318071a07050c090c1201080d1209110d03020706 66
    0x35008503014850301c4810300060120030601c0d000345050340d1912500d001d110705540c00040700381070f0030b070b4014012401c0d48000f20010368021030303140014211540c403c810382c007008507911103d00c100c400040c10011440006540c601c0a0ba00951620384140241c620050301d0075400356911030010741040070b0b0142c02c4e0008141240c01e0090030300c00e1120005403024048580e09000b2a140000c820605001e00c400960040005c240300d007d0091041c0b0078150700d82e61501d200429130013401383c60b50800c14101000c00c022140d40c801c1c41018964011141e42e51650054001c4413411600e420803000c41c000c0c8420b0205140e8035401460240c40955400d40d41850b4400803d0760341c94003032041e100c80035a0051f10300c0b121010000175248060003101950101105d40d00083c0810000715040b001c0900c001c44c43d030040c140e00a1015015064000c0104102e0030040005016040e10001190006071285c48002c1004410398400c040c801c0090011140c2580710710b4040d4588032503000d80c500007203920200352100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 659075305 1250 659074055 659074061
    0xd06030f11120a0f0209060d050d1809090804031e0804081e01090b0a11090d1a0603061b09060408190201110a080f0c0705120105011a0403020f0f03010e010e1f 70
    0x160303000181070304084d4994244040740078000c0c1201c0d4084019035610012600500100040c1e81c40c5a803a6500e5080c000c01181c041011a00500b00503480c01180c4400144d8000c02c82d41617030303080050b01014048075140c00000c804e03181002030483e08049000500700302d00151010749010419500c110381032081d40140e00b240c1104802070881011503010645400e2542e000034100001c10034240c2c9409100008120914001c2c6c100b11000346034420500c8100c6861014503070440d008030007505103401d1288006030b8444240c44045541c0c040054442c0503943c480045a00920107203041e910b4200700d40d07030314a041a0b039822090b404034013100d0400039070b540d0114010a030143e0000c1c44504020306220300000940000c0118495407080070000b01c1c0d56510504071050740c00c040e1001080f44e604008440c0d450100070044020741c0f4905000a20050f0384244848030b001c51700783d50106071000b0900c0020302400868009002c035510f8601c0c285210980410742c011142c030701c208031036001c2610b81101d100b1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 659076555 1250 659075305 659075323
    0x61b050c0d080715020a0f0f020c0d0c18050f01030305090315040609120509031906060308190e010306050f01050c120d14011403060f100816140a0302030c060d06030f1112 75
    0x15880014021240c1c00307280c103440723078140501c1180c001d000801c010440b041040ca00c140e0301405081d104000800008501c2d52440c00905c400344002d00344001210020031041c000202400717404070701412551410007994000c0c22607080c442806040c07a041c0103000305003000060303c8044182c0d22007030703000380100d003180c005034000b50090208000750803d2040f44c0036441e104841c40fa880d04000800704280e031000d0100c607102e4081044061000c41e0020380000c222074095814142403100412032a0b45000340c1c252103d10a0078150744e08c544200b6500d003084c0c4c0b840c6003440c01a5000c0341c6505001c2c02a84008424110350403000f1540e600c3d99900f1072003d110070103013a49a8000800584480e859041150300004001e1948050079250382c0e10b0b03030a0050380142e0504210300c40d60704001e00e1101740b9054000070004d9034502903550640c1c000c02c1e282c5074110b900743d020310000940c0e00145c10301e07a84064010758004842030340652840ca090400000d440201511804044500c50200340001c070300305c02 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 659077805 1250 659076555 659076557
    0x7080c01111908161d040515091503030d050a020c12130506090607141c020a0201080609160531090c08090c240c07050108010f061b050c0d080715020a 66
    0xb01400b0360b42c0e085a69000454413a0317200d41d0944c0303818603691031754010140207040703a041c00b0920311a18000d114040c03000030010230740401d05038105a840c0d01d000c400c941b0100100c00f40454541d4500c0561006442030511641176441080c1d1008248603645c0701400d803021007101c11038070441d41d400400150b0300503c03180c2c0ea0300c010200a1200060740140001640c10f50000c01c1d5146070445411004521b1000e03c80140942c104850180c11513030701c54242544800100c0b119034140c105801c0052054010050344010b102c4006815000720140201d0f40c10500d842078100d00c40741103042401400105940b00d024090740c10507075401c4138030340a4880140310b601c00c440200518844201088038404a800b0110116400b4980d00c144130380c5541d00a04030040194000d1030064a410001811004140d000f01205441c8074001e00c015644124020840701808084c072501e05040e0a0803818200c0c074582c0c40f6805a00707451400700300840c0201610303045000c3c0c07410b001e80b003030341910f2081a40714500440c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 659079055 1250 659077805 659077831
    0x4050108130c030210030605180906060f01020f030703031a0102060405151017031c020903151f0305070602010f1b08070306050306191802010e0607080c01111908 71
    0x1e50000e150180007000d590088066002003030366a00410700901180c0921380c0007030f4880500344500d00f401000d09000c030705107001c121024900200169250301014140380c0c0b01c3c0d489035500c404107030b10800c13034003100124100a0381d540c0c001901c0d01800401e400c1540d00000018841004130710360002c00c0c2c1c0d40c403079a002006040405040302810441c01402407155464140503900030032613000d4140040c18001004009590f10350b05489040e01c0c0360002003525402d94010448902141c8001c40c0c0e44100107003800c88485c0640b549100ba1203800100041980001305480000050110000300e800c100e034500d8000b01321002081700704500746c0720118288800410006020040d140c0f0a450040d40490b1070300d80001d0080d1100002400c1082c2603c419036440c104120081c0c0a039a035200e06000c10402070303800000b0004903030000c1d0881e0350300d0903610304c602c50118090041c070062004a90021b40c0c484000c02c0722500010101240b5040000d40d519107904080321980c03510b010304110f50003004450515 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 659080305 1250 659079055 659079061
    0x140f010312031b1713031b05010e030f130b0c0304062f102304020d020315250c0302070e0c0403080c01060e0f040308041101110a0b06041104050108 65
    0x212800024074040c40c0802d5a1032a0350a20301d40040488203025009035030f4849291031000d888000c0382000b40c404142c000d4030558481c00260401c0400c002804403605000d03070301d01c3d01c2c141503005041401e0304030345c0c1e80400550000d80d2034694005008510310010310722a41900c43c06040d5a900400541510a91041100b130000d01c0c000d1800c141c0414140c06e050740b0400c2032400c084c01070101000c4142c3d81e6840050300083d2065140100220680d8101c40642c00c0307204004404072480024001900809000c0c0000040d92828131181041e6805000101c0140c2000b03204082c840c0d2140550030f8000141c0d44110b90071038401c188441031580c00d075000709001401d00c51601e400c840c02800f07180c1c00304400c00c40000061a40320250102032003000000a0242c90118410000c62004165040403e030f080200310002c0d4101101980241c0c2014000f1007500f40480140c49545135400c1c846920b1081c9410107040005240744039200d0301050b5804d2000b40c1040311a503040380641d000e818085007101e000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 659081555 1250 659080305 659080313
    0x403050613060b100c06060602161707051903020a0b27210c04061a0a03020307051b0f1203070c03080a060f0b04030507051030020301120204140f0103 66
    0x101040c18029440003808148850002d20f0900c0c0013400d2102088070000b50209010711445203c00034901c900151542480445800152403e503018140000c41138440c00385030307441c1c200040000b8000c058450f43d01d158030314200c000c1d8001640700880c8a44486a000f0684428100a881d0b80760341c407507a0f503034005c98120500c01003200403181940c0c000b40d00e84107162080310034142040c1000a0070b40540068220a42448159013254102c1040590400740c0203400001c0801110000c9a040c900140c490b16941000c90341071043e0741411043c2180c04084801c1a4004200070452003440c00840f20120f010062102c00f50008494410200b250803100ca00030074091807140b43d0080048000113101520390340000c11000d015005008010400b007818801c02c42c0800c02800034050441d10b903d950054018000c1402c01426400015200c4540142e218181c2c8007100502c5000e0b070f048155125a11100340006504a40b030050f44603500b000e11081c0003c100e8101c060080e01c1821780008140e0a50f16 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 659082805 1250 659081555 659081581
    0xe13110d05010f0c0c0b2d07030b060703080106020607110304060c11040e0619060e010909020f030106150905090c090907020a1e140c030c041802030604060207060501060504030506 79
    0x10341d00d95481d02e041c144440c4003881070181c0307448107840d440e6206200c3d003007000c1c0704000203104c0120720351000034888000700c1e040b01142c4221018510184c282c0e07107100045010b049038958040d0800e90125a070790416401c0301c1c0c1d00f4182c1e1a80e90890300266106c0310103e905c401030041a01040e001000300b882814420481740d43d40314003900000041d0059000440d003256008140e51055821402c203204809015080c4510002d24441c01402018105103485052420600c07800d80e0740765849201c0c408640320f0900b540b40000300100200300003540e54241000013203541c0e40000000d9400b4001050030703e4012180c60203040341311012410038003103800344402c040e03024100b94103521a90a1040008440c0196000040c4208250841e0001d04d07203003034220400e100c44004601c1e003044e11050002d88000801080c04c4104403400315410140540e01940482144030194141c09040d08000a0141d99001014200c0c4106000c11050f070381e0380310031070b03542c00340d0300000384940c001601050300b180c9054 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 659084055 1250 659082805 659082829
    0x5090a051504120803040309050105031608130609060b040b04061a0703091203110607111b0109080f010b2e1101150e04060b010e0a0b220602070e1311 66
    0x46200b46040d403a014045020345407040200c074041c1000040004059014481500818007820030605600340a055200b1981181c5406410070440500140d44003160402c048402c41d044201044040c00301e0034214040d0802603c1d480c011414640c42d14031303d0a080c03180c00200c42518070300c1c035600443d0804000c0a940060f0042e41004940749021410300840044030800300d12940b00d105410200e0b0055904100009024505102003410318002e07015002c11030130305021741500c41d5031030b0034118070050358440c645800c074900500c904039601e003041e4030551001c0d03200c10040b5034200110720346418001c407a1301c40d082005221400c880035500300303070700440c014800d001e80e100000c034a11810806d2a6004030a99124407074050781e040900090054501c10f006034488286041e0f40c10300d845002041d042e206ca41b02d0001604000115403003000c0403420040030807900b620324408516900d10000303503144180d02580621128480c08100110300c0f440c0c84039001c89d403044415650400b01c1040050780c010403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 659085305 1250 659084055 659084089
    0x5030a0e06090d1e210e04090f032610030c0e010b0a0c0303020708120103140601030b19020d05040c030209150a060f02160611010c020a020306060f150d020304060c05090a05 76
    0x65900c0f440059000c1d1000c144000c501702400d410301d04e04150081c15141800b000394040d0703103080c89020204221261540d05180c041c10043d04140c5000300d4905110b5405002e190540c0d500c02c28030001e0f00607907403003c0450340500e074860030490329048a2a440c2c5028814451550340400036034ac40b81c3d004041c0b10140c28000d040060800c0043d03220964207234007610b5040e1400404000600c20004101c0755030315a500da10004101660640d6120700c03030b00328080c1c00d502005203a103807520b125a015404658441818420512190409150080120310340b070104178441c03064000066000c80c00040d00c0c003441d001c000c2c00503502d94605038060329080900d4100030300314022100304c014107195950256009281c680c0e00c51010289521410382101d406020750f6045400413151a005a940043c02a030401800c0320041940198a40040c151004071021512000b1001c203080800807850350185100318003440083c170030247c2c108001c442d2446030300d018079030040c02e04d003003400503040149050502c003c1c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 659086555 1250 659085305 659085353
    0x60121050102030a0203060109080d0206010b090a08010f020d05060118050d0c240f02010903090e060f0d0302030903070f050121021e040504060b03010b041203170405030a0e06090d 79
    0x55446150990f8411900400080d030008248101d0f07581c00020000240294400781070001c015110082d1101010710414035034850108001d042c035601c1d02c02070001041309100800c642902004110065004511100e907070600d090005482e65000d03c10444410905d0305940c079a05040c00c04010144603042e0007076440002c04c90011034490409000302243c00c0800c00325001038240d03680c004041c1d201c040141c42c210b90624030000c00090704150548180d80211300320004954600000c1204101204a5558085061800001419000700003040c002806a069601d91515583c035440703071150910610340090441050210328040f01651680e0302c205401d409442c0500361007000c000c0001410b92910000000141002540f41600c90701c1c00501130741d4640d6040d580b412400746058010340c4a045811440b10000c94101403041c400c0c0801042d01d503074ac425117030819080c0341d0750741d81008003560049080454001010b02e0280140e8a00c520028000358002c031a43d940d15440811032a1041c0305040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 659087805 1250 659086555 659086619
    0x9030c1e010606030b132003040f1704150c021f170915010e070e190807080d0c0f050a05030d090203101b03020705150117100c09050f0303090d060c200601 68
    0x247c0801903014500450900501c0c030007504021040100318942228001420041008160741902d4901c640d40100d04010444030b0450011481090301c9981e401c0380341d0fa1008400500e1a00915081091101c1c100d4205460362180006e40d514031090305003c03805498440108001d04015220950008103440c14032500b9000101090b800c0c4a5070280c072441d10107401003481030300d8041004000421300ca0b801000c00c030814402c040c1441045130000381c01982c08010070001e0000403c000460161b10500312a9121764a8120742d00426292004901c60b00420f894900040594010b04280100b07030b40c182c14800f0003040c0154000d620810040740d80d8041d06175010f04044405040314002c2c110290fa000d00c101d07a06441c00c2c14605d02a45916000d8070300301c24148181d50162110f03081d00c00648100d20040603c100080ca540603a040c0e195014100a4115041190a801241c1401e00c280c4942d441c402c125401c1001110300c13a0703044482540710000400c2a104201403821840c1c0d0b40c8200010000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 659089055 1250 659087805 659087861
    0x50f040c1716030f0b090708100e10140910050609150f070c1205030a1d09090f060604060e0a020304080c06070c03020d08010e040b09030c1e010606030b13 68
    0x11030215002c1040074885000402a103415004100c44000f003024108a284000350020701d03d80f03c00703003401080042140020344101400030200d005490414607098151420010198a0703000a026490016451074101c0c0381d9410b145a50500400411018811482c108400e100b0203030010801d0030b512055240c091301408140e03178020900d12400d0038890303a94124a041c150008c490315400a1804401c5600d88404118080143ca100502902d0959981402100a0900a1403880750550720400e00350a0009082000929040100301c200540764140d88083c1000110b030118030400464000301000210880e00300e42c001c40e40039108004144c2856a0080c0251500f58200c4407100401d01108001c0c040c0b6804000c88011480709103045035241d81003100d081c0f15140054002805826500c3c0446c022180c01c0c4252041100340808445100e542c501d09654244c0e41000d4171880ca520f054000301300144a030080903581c0d14050502d1302d81d0040f01150303200810039880412921a4120600c0c5068 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 659090305 1250 659089055 659089097
    0xf040609050406052d0901021b030c0f0706050f1b0303100e0c040311120f25080303061c1b0e061c0528050604060507090f050f040c 58
    0xd0682504009450700c1c00d0301d482e20840d500071782450718204561031040540c4503200c02c03092a9220b2a0800c2c01d071a10b03100d02c91406401a0746401122190040e0024001000040982481044d101c00c460750121810802522142140110b000040c0204203d022240c0c4142c000c1c11030320020f28181c4516940000b02d83c0c25604292100400c1d2607091200b040700c1100c50101540110b2001001c1d864941b03995121003403007820b41c98050013040540c145071900f0720180405d80c55134580c0c100b0741d850b561440c65601c040c10020751109480c0050700001041e510310000699111760000350400b0700850a006000506050000c001c407441d000c10240454074a0b24008460018126007103001c869090800820201c1021030302581080070b8020500c0000c114001614501c620a000302041e000c411120103085a000c1030001424601c82c4c0018002085801d0303000c0352040c4016a40c50419981359124012842c5851040c00d1380b01c4d40c0d0250380011071402e50f200307406d01c5c80700d41040241500741641d203007a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 659091555 1250 659090305 659090309
    0x250305070807230109032d12030e07080d0305040c08010c18080a020a0e0c09041805010e07030309150e0d0b0f0a1103041713032405010e060409020f0406 67
    0x450704881e108102c9034114a070b8040d0b6880321a450f06000f4242c40300020074507a214880034010400e04066580403941480d00582a20076112152404c0c081904000015204902ca0350000a1801c10b1055141c1000b03d0040240e031510340140004507a03e41e0201d003c0c15014100751480354032103d0008000c2c200b40300b0302107620b5030354440e0030004008403101e01852405921000d26030b00940c2030080140d131041e1440c0180c0341c41c1c505103141502c0f4000104181c1c002c003a11160024a44192004036516050202c0700310f130f215400034007400190691007070b2942403d00c002408295140800d021254071030b0072410f005146842c023148200c000f1000128040302d08030041d1500e08040081c029403d001c402104e60001c4488820322110462103042e04071407000800140440440714105801c0d010b0035402c035002121586032084c40340b5280c1c14800051070307040c1b0040b440e6a00c4110882011541c5000d5207040b01c006524024070360b41c81a040c0405081c40100c200d0740001d004184c0d24085d62140b241c440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 659092805 1250 659091555 659091569
    0x5030d020706061d0115080f071805030d05030603060105030d0230041d0a050106021e010204031b2102061204050a150b010207090e19030e150702010201050a050925030507 75
    0x100d552500050700e841030501b420304810800302c081044614102e88069503040300b20b900c2c100e246942c803410344560214040d08401d07490700940500400c01c1d580b140c0598003c500c03c8050301c4079a682e030800c1594903459124100003680041a000101a040098281e09044040d0b0034a42c0e820307200b00e04c6034181d030158215115540e4403038013101002c00781c84001030740000402810001c550401402954600740b1881ca0100e0005289034001c0800082d01900c00a650040b03811201500c803560b8902042601e005552612030340380c0152840003880d41c40310000c1746e0050506403520f602420280da04000040c015503052151003038001c00190750320131199a101030001c000414400c2040028103191240e031012000701d0900041400003a000714087d003940445034445000440300d850140c4802c50180b00803980036413164004038000308188014000e02d4801d9000700566500c100380b9604484c400d0f02d107451244c1c0203100806501040c2c0c0c0620351a0004000350b00015640c070350f181d914208203508100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 659094055 1250 659092805 659092859
    0x1b01051306051506030c0f0d020a020f12070305091516050c01021b060a0e0d05030a0206040b011d010b031302060d2003041e170c010c0908010905030d02070606 70
    0xc801e1000c54401d494011000211000c20959124005109400050442c01050100055414554003007800b15480e09412030010754a601403e40c2c007940340c84e118a440940d40c00f442d000d950f202c80044040796002585034903100e0505001d001400301845041403034040f0603808004030b20168078050020903d50b44614010448503600700002410a290b2080d0014000d001d450088400c1d5120b9040d2425412a0f10b09102c42442c40c8000980b43c02c1003038006043c40c0400034202c0708190780420207511483c0101506002d90341e940d004003044041d07140e100c41c100b01000005200e001003940c002c54000c041249110801480c54000641982c8055000278416a4030000010340c55800780c814102d23002d40241c00c82c11858a6166445a411001c050111070744100a08504104900c40c00c1d03903411001c100510b40b01c0c4000c101c4135000302961440f100c040340002c4030000380c00f401401100040d55002f8091130034951100c420b0b1020703400641302210000e03194032000c1b81e00c0ca0a9090a125880b0205444d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 659095305 1250 659094055 659094091
    0x80702130e0f07080604060b0a0e0103152d0e1018050601091b0f020709060602010e0601080f0a0809060c01051021030903030804032304030312140c1b0105 68
    0x6898042070886502e00750300090001c000411000c40c400b40e1040e000500440d14800d041c00286c02410759070048842c0102440020041c018100e860f1108401c14000c2008282c64a802488110042e0740c4034003206003220000301d10642b44c07500f1510102e04110700715205180c5960b412740550741402c820481e03407005450320038140802003101c10b00408070b010007081030a0034a26501000040c2c1d01405d021310101c6020045d0640c0b00f04180320051000b01070401101e6202d02c4024040d10380c0c840d000d807603442040004039400c2c901048900ca00d01d4004000e081002d9140d6031403900c0c0d04600b0001e541f000c1e091100c045080d40070301459114000720b0744150710030750800e00c02c060740100d620074440c80e640e040c0d986040040e41007039242040d65050f003031990141d95645070032a00341c41c48001d0244600520a41241503400ea05d01501c1070741d21a407160071070303d00a0810881210002000ca601c000320210105a101600500070102002a20307918044051a080b4003420b455068821146e418103249903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 659096555 1250 659095305 659095331
    0x813080f01140c090a032003010f05060f1f0f03020702040e03070515040f03080c1c061401170a0e0a052505040b0a03030f0201020d0e0606030f06011a0708070213 71
    0x2215074090f03446070b0410300307068009001c2040720809000003000d0f455a03401503450b69145500c26140014014004d1015081500300d05c1c1c081c0c5030940c1c042c1d004d40d1203044000030501c0c20314251080f80f403602d143c1a0a081c40d0312011100a01d0b04291001819800c000110140c1c41d980a0400c008056078004c65072580300e443e00600e003a074410000c2d0000b0112030244000510104a030b444ca103a01442c00b5801034035500d0074a034451103200c02816000c0c00394002c294031416141c0040d021111400a03d180680701000103581d042040d031010f007510403203c0b0028903c0c80843c2d201030840700f5404201d4180364803c0d980c00745000380d01840d0402d808107444408401d0700c00c070f8150201400050b2006c0c03001038006000b282c022661400000e0034001c0701d41c001c4869901c01d60540308003400102d8240f0001c102a01955103d44064540e24040c0c00741d0144e82c0d901080000d81c19040b505141070180b962400e0001c2d0300301c15040180110350320350041240d0b402503903d1765003441e180302c2c0400c80041c680740c1902c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 659097805 1250 659096555 659096591
    0x309020312131502070303140d1b08062b0503130807050a090204050d06050a0216030809160302150c07090f15090b010e0f030a060504120906021204030813080f01 71
    0x2010b030f000c0e050003040e40024144d01103290f004903a414144600113100103c0e1141c40c4e80541030501c51480e2400214900e225a2202d00600b00c2102c0e440c1c0380aa619100d080c08008480f90700320407000a10300c880080c00c0b11400c0c03540428640108240c0b4188202c080709480c1da040d483d400070740d082d48500418000d078a8100f0340d00c00107180c21f2004514007460140810340581c103603080038017415a9040014060907241d0115118210003010350040e40c1c00600d406001034a00791a201c40910a2040b03040314210546c000c801a03a8000700380240882c411400d0b465940c0c0b0503207003400c1500030290009482c0d02540a0707481824640840070036540d91020008940480c01d52018000303d081c00400141d42e6040b0100c151000f00589070000031060500101e0315000030308400402643c03604080009006002c113060089940c6503940c6c0540076034840040b0f94440c01320070ba803441c03800c0400c0104005083e11004003c401c6d00300304084821652501c03106d0621900008900a07651980010311350500e080e4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 659099055 1250 659097805 659097809
    0x1203050d05011e06030e0705040609020a1202090a230d0303050f06010206040b0606070807080f04030b0901020f0d0c17090304080d170106051c1e0b062107030902031213 74
    0x7500312003c58000c999606101e000718410702c01416954288119100e005000d954060700010384240191075079005254002d60140d4984c0d800038540d508280500c040c0790007140c01d40c100003000071781024145408d41030030100b002c114100e00f04108445c10019101d56001600390783c040e0703c00145610746006640300481f0010b1600d8110741144041200180410305c486130401d40c1907921544405051405030001d11540401030101400480d400189009080050082d20300c00c2d8909410b40c0c03034004086090703004039018000081c405220101d0300d4417490b40030009505075460060284c0440c900e0b40c1c010440c00340c0b408841038000041c180320a010803c200c69011041d80f5283c00031518851a404001c40d060103024100322000400e8083c10f00700c111309247e640d00195042200c003001010403403940d0089120f801e00a41010800d0000d450715005036030226007141282d584216641500303e00d2840010400c00516640d43c902c1c00140e1003c010a00d01a40b051405950b50429600701e03403003198060b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 659100305 1250 659099055 659099069
    0x10f0612090b04120e04020f0d06061d06030a020412030c03030b0a050102060c0c071a030106020d030504050a031215030f0b0105030a0c090f1e020a0908030406271203050d0501 77
    0x44480400012128000503a103d0340040035010701c1e010306101261000704006129620031f0001c18040350108402c002030030b80b02c40c42d0008021032540c40341c0a80350038241c06600880b104411070404013a08080e170045038000c01180c401480c003503d41140c01d0b083c450701c070820740004982040e0801055011301c2882c030701041c101c2ea91042e2618010000755076603030060581030303c8036000c207a044050340108120b4018004014100c071030355401c14094000c6810903c60381300144540040080114040c1c4a8140101d40101c0981241d112640f01603420303d850442c4100c3c140d5442c20201d6181c03c211848001441c8100c84404034030b0030500b0000d08603c01030308182d00c690415410707000002c0d03900c00ca1b80b00704c420400c40802d0300c902c101454001060111144600045210141440d00e0b105a0051003d14019110f000c83c09071591240303581c80c0200d0180380e000c03c00c0c01450b424003039000c0c080c0d0742e4040304100f054803841d83c40d8400b002840d29004003c42c00300d04045500c20083c030071070054502600007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 659101555 1250 659100305 659100311
    0x2150705012405120c03070e0403180308041214060c07021219022e1101050a0b060f130b210a11030c071110121d07060e0315010f0612 59
    0x10034031520b1a082040c071806119218002100710310321400e002520101c20010240c0301201c0da1084007003040d4104030781c1100003860f003560100d0b10036072062190702560342002649042c40d04109600900700c003035040039038ad101c0c5403000c2030801c81002c0141c6445880d90010180e107501843c810f11909500341903080aa0790029008586040e10455641880c84e4044941008020303484c0300e41c1c3d1020303c0345080768103091601508200d685400002c502c2c861070320a0001c10640c1e80b1841d080045510305070710a540024104500d102188104010304907062000024055140e62029201d41c203512011000309100c06200882c7c40000601900583c441c5140f202407009070100d440030991031000030010400d69030701040b03400a002100e0212140080b0103408401103526151010301250001581d01d9002420640080041c040221004070f1450070344c2d00a2017075500f401025108208413040d02030305442803e81003603203051301030b510a00a190b0141c4501e2001d080620082444508110902601742 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 659102805 1250 659101555 659101601
    0x70b0702091b04080604051c1818060e0a0b121903030f020906030f040b061e060c030909160318020f0d050f0307050304080c010905150f070215070501 66
    0x3240345455a1000212042c03041e480e524844140e414050741d0000b08072440b0303e00402c0704200e4009050011102070042c88990325004400c210f418041d2220300c00007100f0b8603503040001803140d0380790030304c0703143c1052000c68400e44568465600b04000c4807405012915a403540505007801280000d0400d8481c0c0544901c6451000d805100408180c4c024101075456040c404113003015170585850074002000741d983d82c24680e0b51a01038038000d64080d20458041c00c049002450a061380c00b00540020106c1c1140006007004c008480d0803950781c01c81c441c0001c000c1c04409940e03006036284900302c02c180190006001402c0101140c50000c1c00c001c03c40070345d05c06d240140c0e072403009014481c68100c401c03104e030002c517103070090400350310603c41d0006100100b00c40007006000b1014000b0b03948400129040214601c0044801031b00d24800c06030000b001d241c5d01402210082c0c02081e030002030070a5640381400503404549800304541d4000010140400c0c0001005020b000708925210140e0071400f00c09 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 659104055 1250 659102805 659102809
    0x110a0215161b02040b0a03030503070908070f0e0a06050405072d05030406090c08060c0414180c0d0632101b020a0308300702060112020102160f08070b0702 68
    0x1980e000c0b114010749a21840303080465031030390840b9460590240036481255030b039140291140e0026103a03a0b000c50894040031904100000f584000c840c2c40c080c0c00e00410345803500e910858074025088904503601e5010205041e01d82d4065a80078010720380d00c2c401c07039018100c446002e04484010440070300d641802c20b0010f07141e028064070b401c103410a00000720110b46140c0051100641d038408080360003640d08216209200720040c104417a1351404421282c0e100e07500700507082034040d04000300131038190040344226400380080c088822041e0170003d02152121100c1a08030b0703000001541014665103101100315524002d00b251040a40701414100644140030b40741c4c0c20382a02d0203c0003415513480d4002c0d5543d07200800001d54011880c0c42e502c2c18030700d00f0792410202d4074603141d200d540e01604d0501200d6003a0744081c4181c0d00703a40601542d03420400c6d40c090000d4a8217044c0e0442c800c00e4110502e00c00405498002030061828240d00c15182c03c41c440d0502a00382d0000c14001c40c240320f0b2201507 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 659105305 1250 659104055 659104067
    0x60f0515040501140c031909050406120213020912010e0c01030e0607140319060803040303270b030c040308031305070b040f03080f07120f020c150a080a110a021516 72
    0x30b04041c0404d03850b030001300041440d502a044150302500b1503290220009904400650140c442c1034805012198890380d080000b03840c203860003500720001400c89500da920035409041e005034000d040e0f88c10781c2a400c000c242500d035400484421074200d050703a04195230305841405400c50821010b85414a054100a000d100b10001103200070f0800100150035144582c51111351000d104a0800c41e960b100c402d1356070b8981140c0000c0b408250006008032400c424802e090303101c00e5410079007040050504035003400350b41024100240091041c440400018016000b540c4100c000f003401c14000e81e124203149280080d20b034404052980208000d02414070f42c40b08180a50307401c488042d40d21444454080040c0c4600113002d00402d150030050000e03198800c000d07111181443d801c6410030000d485c02c200c2000120650004103040c204800b0f1059401442d40690000c0030501c0000d11589041c0307a0541c0da030008282c04016004055412940130140b0030050300001c0c030104560105510003805441 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 659106555 1250 659105305 659105327
    0x40e061809060a0c180f0914010e07033209060a0204080c060310050307180c0306180b010207050616140111030105010c140703060e2512021201060f0515040501 70
    0x8907131905615800a801551001d034a02881028007003180e80c0c0b8a2280d540c0e61040c080c00c0071071400d020002e559000001000c9050b00d4079000390400c1500d64840c190010050300c101c0d850b10103e0b05484c045c0d1b440d083c0000b003d0407030b20024000c920f4548007915a047c802c00501c00840c4920602c41801001400103e58864004c01e8805513502c1d203035100d04c20300001083d4841917040c81900307008646000018143d40165030700000a0002c03102940d0b00b0b5081c1c0700180501c0e0300060400d90322a15014081c1c200c010900c0301130041e1000c0686550101e2440d51001c0c42e07400548910361192402c1020201d80041c1044d480300003003201c01e86880c80d14040e03100c10312800e0b04202d07031001c240c4288104000c040800d00004001c07a48099520310f090805001101c1907420a4001c5241c80114408003004000b610340074010240d081905000c5141c40104501009036000f00e030044841d81d441e24240310f0a006040c0b8007640d010050710b010100084000b51081c2d0100b41070090104001c42c1c1d0300a140a03807 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 659107805 1250 659106555 659106571
    0x7020705060d06080f030c0615010c0308180115060f03050402150c12180f060a17130501060f05040641061201141002030d0903020111040e06180906 65
    0x10340d603404071a10740c010f070140c0d4000c4400c1d4001e0085440301003038000002d04010003508240e646035a2500d8420036620880c20b8694045551920035000291047c005148d111a40d8070042c011204041021401c661980249034501d0b180d0090a21a442e082215844071003200d140c28012841c00781c2c0400d0408069420200d00c507400441c4840740c2e401c0501c01130f210300e81c00d0000a515811000e041c450202d442001080c040c0c1c008601b480ca050500390200c3c3c803c01c2c1e26442e00c1503048404206158445001042d4030b0340c8005103c3c02000140d002e000e014010410005918062801c2a0412040391000d5200110245805119030700c0d5202d030000201c0701e00042401c601d030400c20a512000319000d00c2d071100343d009000182c3e007901c0301ca031000428140d0360f000c0d0705550085400018850080c0d0345c0b00d03025002d68030601c114030706601710b500b101010601c40d10000c01ca8020104c025681a00160800d241074480e0200b08442d50420740b00080108600034034080a60078400300181d151000940200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 659109055 1250 659107805 659107807
    0x10030636030302041a0304020415030b0402010807140708030a0b04060f030f03050d020714060123041d0a03020d0e060711040510030b270c0a1502070806012303060702070506 76
    0x101030501a83c1039400400c1e45100e001402d18256a110810360b00c210f4007203120300d2a00c1d181443c400840d000820030740364003102491162721160015151910010070321030400c07510320110300315014644060030180344581441c0d91030303041010450040d6100b003c241030050b45402802c2208180d2102c2c0d8000316074001d40b509800024a09084585100d41050142d14600006a0303000300081f10300800d1602038800c050300c03142c0e41c8442126441e881d541d0402d16a80035151001c22031481c155104000701030041d01071285200c088079440382032082e10381068001d60040c1900d000100d801a07402c0010542c00c0314420b2400c005a0341d458883d41000b540c640c003030f50381e40d03000500040400150070007464001144403643d281001803080b280d4803031800c22600700c084200c031801e40e245c0068100c00f20080104022441c50408001d009503c040704c0441085210300200080c004200740045406040e40c17a40c5e403032540720720032401004400d40703242043c0a6801407081110155021903028181d40c0119192 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 659110305 1250 659109055 659109161
    0x6040201021e030d06151d090c0a03020702090901020a08010b090a030308190f0b030709050405210d0204090c0e1815010e03031c0605060c060708040606030b100306 72
    0x42c41c40c50080300c3c1040600340c64210042800108600d40c2140e99030740766503080e0202000491000340078454520641c020295201007189851450007524000002d0700d001424915030350001000203070240c0e4040c202c0c0c1d50005001000e41d50002540340900780300c0c0c0d00d02d0b01d05051200401c48030007040c0b1020701003000d19408a00040286401c44450150441c801e12042000b00240b10052088030640d6100e40f040701000070394040d403802030620481d0040080c1c83c00012026181c6801c801031048248120780c1040030000b0741842c0e1002c0c0000d058103c02c00912000c03083c002070712900c01074000c507101d5200307514403900700d4094016086c3d005071400582c60b002206000180e84181441c0c02d4150b141c00302007412405070729880402c129032030805c4820b0018a6541c01400300d24494000030f188944c100c4070008403814060f62100e031b0418413500f000a405aa291501800b000302514020b42000b903040e010024051140102c1d10070a00d006013501c0f0700e802541202503110010006400310382410020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 659111555 1250 659110305 659110363
    0x3120f071509052509090807060b0103021308030322020f010e06040b1810050a09060f090510020a0308090d021b040e030c06161416140111070c080604020102 69
    0x80715550951100840d0060040160650500384071000341307413030001581c0d00000d008000da0144a030125008001039142c1b9005481701e1b005410b00380e241034145602040001d1445c038035000510020080e400207540c03a400c00903004a4500f074030240f5203882002000c551030140c0e4502e41d00c3c0c48962400d00b88281200c80314800b040c03890080d03a104400000300402d021450400701e01c16003800c00c0080b0303205600d0000f540b1041c0c40c20300550685000107104e0301410301040d4040c0d4078030303020348210307007002048180d4032030014816040c17a194120041e004001e03174004264005400c4c507082908070024107c203101054000b503031809654400b0b407141400c015042c8064449900002c0b014441000b607d540311031984460345e88040980c2d1010501c0106201d078521544188110400c4a00c4010303000e26054911800e8511007102082c140c0f820f503842c000700300c4001d000b440344154690350f00b02e40d103848a0341d50429003000740d015800b40e00603070000c100300001030783d01180700c071550798880b400d40301002078000c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 659112805 1250 659111555 659111561
    0x9020f040902010c0822080a052e02040f0503010506090105030c040b130212010303080a0504030f050306010e0a080601170703150509160806010302040c031802010e0d0803040b0603120f0715 83
    0x7410390100084d02034965000e081e25406c0ba04180b40c3c0420030290761300002650b81c810b168001e0704541180380014040a00c260f140e900024102900c114580300021210007203070302642c440502c801b4140010010340c1070078003e01e0f03032142080300c0040c01589801c020a890300000b903901071140743e8810352681d16544560014898410882086403141000c00ca142d07601030007070005402140248000030b02d011054016241303d20341c1aa1081c40c2208005000d65658102519403414000b000c00800c031aa10780f0b0902d40028600b04000b80080d52618140348003900041c000c5003450707040740c10b052002c070b906110345044a005a4000017100c0d51025030050801c11001500000d010081c000020040000945141039078001c503802c01150b001c11105904442002e007022411040040c800d0000d9070080c40710304e40b440805030114000b0b8043c2da40e900c44e0b9078801c4a081314449100801c2c4111402c0c00c01040d00d40d00c81803015280341018101c403008181c010400003d111800c1442001e040340c0d2960 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 659114055 1250 659112805 659112827
    0xf021b090901091e031106070507110112050424020708070f0807051e06060a0806040b0a1e051803070503030c030a06030807030302071202011e050c040b040f03060b0409020f04090201 80
    0x51350104413030030281e0300381c4126411100181e0004a00c00c54418450401140da680107072002d0301c40b80c1c503240305a55030400202038202200c0c1444608002c168003d2400d01885105038840c1e51110650a801207030116500c075140c510058240c414020311000074480411508550303044401d0702c1c0316801c20710f0310081510500c64010054005c0c0c0180504845001e10240c0f0203041c0101600c3c09503407040103001c102e0300070b031003002e2441e4000780c0030501003007c6101143c1c200c1601400031401c00707000c8098501c20160601d410b2000d40d07031401000310440e41141640740e09041c3c02c0285140403144c1d1111035807800054200d07640c90800002154058861f0740c41000256070140300c2d240c03903a44a09000e40250080c0000ba9160041e024426607402c0c4184168003070402e00c0484900306154280c0b21500a1400500d070510151040201007030f660860005040109512400515054103501e0050191090403000900541c10008204016a100c1c000c01107400000e8800081c040020300040719100303000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 659115305 1250 659114055 659114063
    0x7121a0a0915031208010603060501177008090709050403050304060f0e030406030c0e0d1407060f080610030f09030e100203090319030c1703070f021b09090109 70
    0x3e136154545540d0400800c0c2e0480d40745171010007600e03903202d0040d030b0045560000100d0300c03940480010034a0042c00e01070940c00d80311404542034052001128007480b26100d8034a522180d4442110345200001c5080706108003051b0031440704540b10610040c200700c038183c0d41505121800b400903840c07000c20800134004124619003805142481d080c0941542d0058030185c55441c140200814881c0882c01303982c80d0007910300700441ca4030385401d50407801090b1496104c0d080107146e0702c2401e020345d01d0403075800300c150041c8016420f50800147c841c0c5040203550200d828000c401905540f4141c0084e200c0c0d078007c83c140c0b10213442c40d01e08c040c1100105040c0710f03510100c40c07810441c181450b03480f03282e43c0300740d03a015100c011a1010444c4240da481c0a0484401d505070301c84007544c9464018040000c4000b4820300300081500180e55071910000803408044001c41000f0081042e42c650258144922403080d0000c3e10146000c1510804981e000d041d22034020410880030492400096103c0c602080e00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 659116555 1250 659115305 659115323
    0x608212d0307080a060605070c0302040c18090c0206060a1d0402041e0e0f0708061b09030304081b040605090f10090f0f0c0f080a0506011707121a0a091503 68
    0x202c0340000e09868010b6401c1007040e0300c1c00c00d000c030354107000780201c460603a0400b20728400702c0e00e59400c04c000f402c080c203182c2041280d002003a40309403c10140c61405040001c2000c154603400110083c94010004c2009204020b000803c0000b0700b0695800e000143d00c3d8062182c060741c0d00c1c004a03001e4112030030b506524030b025031080c00007060f042e030102400042d0903041e6a001200a82016a60301483c003031401a41c01000100c0e199118080003d080f20201c000c0c01c03402d2903004000a0f0550700240d12568032908003180d0003141c07441e07072001034000c0c50044504010450400012a0080e140240403540440c9030b2404100921000742c840001880341142c140003e04940b80c440018009100801c0784403030030b2022038444a40100320541600e181c0b543c1d400300c51707654040c400c0081c0c000602098140102c1d508070b540030b05038903451184216030382d440b951180c3c03a00c40840300441e0114821411200c558131850b180a40e0341419283c105e0301510004142c801540340c601e03084d0308650744002c01500b4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 659117805 1250 659116555 659116561
    0x1413150b09130c061d0613030b100e090303040b060f011101050c0d050906090a170c030f0301150915030905010b10031409071a03070c0f05010608212d03 67
    0x788607440c040898810302040c58416690760081e1014041760600301743c0c032900d5046030403881c00e020000d00240c42a840409108643d02d85400d410031409171801c030740da103202003001d11500603146000c540240001c80111714502d455202c1203e821400f4161070710401000203140d8441e88039120000e011122140200483d013440d204c42c41682d8130040010b41883c0c240400101000070101c4c025104081041c0600301251495a4400141540146071409500148210707440340304100003520000000200c07087c1c1d039504200d541c0c0c11206625a0700810851844c0782800b0482051101407134030011422302240c01180c80c13a0040c054802d2221150704210380301d284070103043e45038000c0e10001c00d0a4400403665262148501d0702d0380310034084c1100d07207601c0300000e0540d442408001e640c484494540391226202580d40e24401403040501565640c0d11400c083c40b6545007401103100c400502808013410280041c0c40300e00900400700e006005a03c0704041c5190350032050303043d0480d4003076000d01d04c0d074a00e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 659119055 1250 659117805 659117821
    0x5130b07030618090b040305070f061e0b060a0f12060905090a0209010e070e095115030601020106081f06060509061902010f0f0f1413150b09 62
    0x80001d101c0c1c003000180c105111050a40d1a1013a030054980001c1d0140c6665142e480a45803070f4810401103d11201c800740e4200403449510940c51020150100302c080050710101c281c05403807080070802d102d00c100308a04d40c0d000c1e4002080c0701c1440c203a41002c1e45544080c1a43d04010801c95114861081c1041c0410803012000316074584034900c00c903081410fa90322013000c1c00403844200c51000100f0740404c0703506810f29100e03444581c400303d03c6580700c403124030b40c00c0010760303440c0100c6c0401a5450b036200a0780d0040100c0304c100040741201d5007001c040044010004461801d45107d4840c080e40010100c2c0c0564400e41002000d05500803c4820703000442e0b03003901c08403551680c018446498000040344d154821021110350361001004103040c00c40250040120045a104031000c0d913690300140c103144001d60141e00e2a1500c01000060058081001c080c1500c0b107068030b844c14061141c04000e803034561124005c220580003d6141e40001003c12450001c207410000740ba030000054003007006207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 659120305 1250 659119055 659119061
    0x50c09040c090314070f0e06030a0c06020d020f0c060406140405040504150e011a010e01030b09090d0201051f120302281401050f0a0b0a03080a0306240e0405130b0703 73
    0x407880b45035511121900d00c0006902e59640c0c0c0680180c46c2a12802009500100d0030303810f80004000f8161801503981d0794400c1c0303000009034040005038020703140e80003040c0c2d0180322801c01c00d110500549410420303440098050312440c0914820701c11480300050a20801d00103450203000003030420403903810103082025030440e038442400500c0c1d0818014012900d03041c014100c07144288100d10b20b0420f201c2c001510141c20101d00581015903816808006a580038103513400f0700c1809001e8400c810069000a00392103004107042e228516001024480703030702040c0385030122103103828088581142884c04a00780f40c452100b058807102104510501c005000070000c040038824012210781005c1103040c20309a075030895400c24682c8041001441945081d0080e1145203001017160b40d05944a5680c640c440d00700401010000766544001d0091861304920460800c11000790540068100c960041400b07d00800c0c0d503000d030b62540007041d15080300c44d04120045900040313001c29031030301c0c590003402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 659121555 1250 659120305 659120309
    0x50d0f11070c270902040207060c1d1e090718030c060e0d020d02040e0a0b0901090b0f09030304120c0602220504230402031e0708151603050c09040c09 66
    0x100511500d00042160340d40d03440801003e4400720680c6855500300d00c1a0040c070403424181c1e0030070f03002c00043c0001a000c0c0308007020342c81980c4414001810071189001c03c00e00c41d48015014a12400718490b80401c0c10403040ea9000b0111124242569007031411100070700c403400c04404001c0700035404410400103190803003c0d200039650310000c1d1042041040703c4041d6410b030103134004440c0c024003409800c15410210b1103d0b40482112042c03031042d5194180301e142218420b015966841c0040e041141512610390440302141e00d40a180c1003181d2130544921020704010102c007070f2003031003600142c082e2503101d02ca1600301400315280c141680c0500716022000c5410454510401030205042c503080c4280c40c00d240703802415600c28088011301b087c500c080580241c2e032500c24004070440c0d004c0c16001103062448000080e1001c0d40c0740182ca1490b100003040c2c06032000b05900f040050042001f01c014509080707502d000f054640700c000c6038041d10b200300400550090b050824a0700600d402044a01c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 659122805 1250 659121555 659121563
    0x14070801050c040b090409050309100302121501050313020d02210105010b0a050406120609091b050136170114100302090c0a0e040c031e06080d050d0f1107 68
    0x220b54800b0a00c0c1064416400703014000b15061212200350704241c1d00140300c0f14800d5044900c0d04d001400080c0b03a0f400f010b1a10303000650002541e4983c5c01c402840c507900107005c42000c4244815240c0080d02e140030050030401d45081034285401507541d040044a15a80c0181000e20961000c3e011104134030440448d500d015820f000001a511000a0440c2c808401c1507540604190a11108940442d05510040d5845803981000b14003002544a900b00c000d1140c4807450031590b56000f46050314030f1552005041c0b20210340700b40e1121100e4a27056a01c038421a1501103080014501c0392244000c98004210080d20b0340a95108040150f224010010820740e900d9611b580d450004400302c802c50100070b420400c0c2c140820701606001d0040d086200f040c3c10511444020300c40031030300b21904522100002501c81008104078419019000342c1d503260490207114107802c05001e90b03034400020700784c8000c201c400281c801e4100a1503010040080c0109028010b0403100040d1403050381040303030192 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 659124055 1250 659122805 659122811
    0xd1401020d020a0c1103070305032704020a02240c0d0c270501021e0d050c03190f0806060306030a14010e151f270f0c080703060b040b0d110714070801 66
    0x45c0c20724001901ca002c5030340c40300013589040b40700d0f01d83d183e075000d24485040c88040c0c0365103114000e03a1940007404000342154010031018038201e28030003000720b524090001c00d0034106e081c0582d140c40203003160803080e907400c40401c0805600c401101c4159074460101d11502d2210040ba511022103c01481114400d9080f21a9400a090710704000118000c0c00226941706055442c0300c2c038000c1015000c540500c00a40f0b0400c1c143d000720114560758a0814000500c0d801d2600300402c2e00204500c1c0c02c00415a03100d070641c98030748042075481803806c030050303d441c402c4402c890000500750132214400b058001602c090700c0ea106480d401c003400a0b640902c1803106545940c1580d840b0790040c81c00c03200018402c07009241c03031840c01015214100540700310360b034542588030480716080c000c40e201c100c40d6580d03100e0302e4135029100404683c12078101c0c0454410407c02002118802c00580f401c81d009510000b50b2908a4103030300b0924400c03080003d205403058005040100008a060740803181404028 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 659125305 1250 659124055 659124083
    0x50d0b0f0d0c2603030f0414060a0c091a0717040902130f12031b1b0b03060406090204080d200a050703140a121209141011090d1401020d020a0c 63
    0x110031200c03100b00c003d90540d0700c00d00008680000150303606801500481c0326841010128030f509040c86400c5410211043e181c0302e00a510550003050100104849038500d40b09400c0301580308842e01c03e40d0000b40106802e0b9004441c185540c03070840300284070059045607aa0080001c0e403c080c881440340d0862890039001c002500038840c01d0a031411079051b070b40c40c88510100012041c0781c8100320000d40303241e0300c001901041200c64004030000f80001409880c6c4928200c002c0109660075034000442590051100f001182c90029202704040014200613010308050311319825005041c0e006800d05101d205145e200b401404500344040d68080c1402600002c80c0715020303540c610486500401c2d011125800d010241c0c400d105c112034100489002152142031074580c208080030b2000128126081042d0311982050640f00d11480c1391912104a0b007042228000a81c10080000e0054900790344400c0300d1010b203c0c203604482c94040c081d030045460300180b240c000d000414101d001c44100040b0045 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 659126555 1250 659125305 659125349
    0x50306010509100e04330e150c09030f0a0605041205180103050c070f0b060f0406030804060f1211030f011d0c0c0106030b0c09180106050d0b0f0d0c 65
    0xe50388500b065090091106280a05403581248014010b5800c01c06c645907100001d034481d910384200d0800241d001540c0748060300080100c480d01d03c0212410b5104906003503041603a01c04840d8007450003102107890302c41c010007080c01c020300721140340014040d14146400700f00341603004a02490248054150140d103c2200303031a80d21071401c40907600d41c180e0701da8191640c4030342c20080d44900720440c1c039803c0043d96910540450341a0301c0c1150207001c048100181070400f288009400241100c091190ad45940c81d00324a0380704138018a810800c0d0f03d541125840d0040303005c00001c10f0b07084410417145c2d280b8140c95040e60400d0b00e10a084c049154000103080140000d1074a902002d0300d0440b6031034591151059859001400681c465520303824000f000c1102000b03010322805042107265510b000c1001007003002c500103003154080510030030060006a41c0442a542c0d4652144030000e0007842001c001800c02445411596003d2094a0003004015a00900070201c1d00014255003d019510003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 659127805 1250 659126555 659126569
    0x81006050a0803070609030c0605040b04060b1804061d0703030207060206010603020c03220f0e0a0506040e120705030418020a031416081801020f18030c0f041a040e070503060105 78
    0x880c20b2090303401800b260000c58901c1e8084000144603041548450010f80e496006448080f10305031400c3e46500c0070001482054060741d4807403a800c44181d10814180ca0700c15080350006400504100d075a000f0740c1700c1203480c0c0860400980f403a8401c03101c03515541d02d4002e513528200e0003451700500074400000750060007070080d501c1107034410000d5401c0151010600c2c2109003c510bc400c2e030500501d00005107081c1e040c24030030103002480503515803440c180103c90240c41000e001785000324544215140c0e032460200d038611000000440e060b5881c021030030a1440d40c0101c0c3c006c08040030350441d690f0070b0300d8150360003081c1c2080151404e000801024482d04580f40d41240c5042140d00300c903032280540c0340b01d064510361240038514070301c0e050b0001c041c05508a0b0000859030003070440004800000103950340c4180e140f203108500406100201d00003246401548022142c0200e442c0c40a440f0000020f07010303a540c140020b44108441c0114028185d030310540c81c4141c43c02070103000c0005c103050422903 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 659129055 1250 659127805 659127809
    0x80f1b0609130203060f060c0c04050117060402090714161407030305090d0201140301030804180207030e100507020405090616090e072712060b03210a0207030804081006050a 76
    0x1c00c018608000d2100010180d8001850700341c6c400c65500110f0f000303646590180000b03403114001003c61804810910080b5401a0021608015544402242e40d100000c07005c2d840342d03054400b5003a94582e41002d4030b41d58004009111039410218000400081400700c40a440f401601050280108841c040740c503001e003404007800086040011a40608040c0410440b441c410f1600c00310b80c0f03c502100740160b4100ba003080342e5040f00001e08010b420024035000c000440054021480e1800a5502422107100410428003c0a0711124010042c0c040e809841a0395005802070280d49004116180c441d00d007110042c049014a1522a0141e803103242c05100ba0360f0000c1a0f407800e5155070800303550300304d406641d200c07640b0124602c041840142e0b40c000380080401442080c2e003d44c9a19100b8103442030300003024066841058110914407100c40000d001c0c0e234540716015552089800308030b003011140c0d0005881200c000400140742200082c507000104a805400c202c6103443d042045600e003554 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 659130305 1250 659129055 659129059
    0x9170a030f170601030e0a0807061515051602010e040e0d080c040303082e080607020d080702251203020307020406050f030304180f0e1b04062d080f1b0609 68
    0x502c001011035001b9800b0f00c1800c1d009100b102d01c200056660303c03420760b10031b8008444481d140c0301003081102025405074040e15441c414002d1104080358028198059071160050540308102a80c041d6401110551040c6001a006001da0080794250690720010034040314000781c000d40c0011001140a4140da040d0b07941550745607040d40310240360b403800420a00c04081c10300a0900c201c6052208003180c54000c0c0600e1000d072440e03140805020341043c031020010750501000604200340551701040340b05986105000d0030740c2c025441e180c41c800510b01da41009544000c9180121b051540000240c06041d100325410722180391945c6c28000244c40f0701010b56015403040c0002e1003183c101409180780001440c01c002007151844079440700b5196040d1110038540c118241840c030300d040034424034651440542d418440c803880d11382c202002c0711f82050072140b908028041c824208000d40c44250040212900300da02030010001d80c0c903180c180b080c09201c0301e8414541c1f00d1400b4200755007598440c100c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 659131555 1250 659130305 659130347
    0x306080304050103020c0f060f0907050a06080f0411032e02090a0b070f0f03090503010c0215070507110607030e0306010e041112160b0c07060305040f02060a09170a030f 74
    0xa410b00660181d04010440302690003403034040c01d05403208000c0f03d0320840b14005240e03001d00700300a41a080520301e4215a00544005034140f01d41d0b60001c2031190000d1009030308032101d50342c0d800d090b56018110009198140903812640703101100076403006031400658040c4a0240308000d001e0300491080704040f9400c41c150440030001d0314008405082c9540c0200386140044070b1990764010514682d2900b2030200b024084107100745e040910500026086500040c00344513040c9548222650b00240f0303907420060300007446010041d039041c046040d068041d00c00d9031100314500c2c001c0c09200c19003600c0f500911600000180030b03100b29201c9070042d6040509041048000020706c02000c0420701541e556100e480c0342c2c036048038401e810300300090103010b030941d848403142d500190130400c1a502c400101070402040c08041007500e9240344074258111411961401cac014002d0310000c04690243c0b1001c02403150101c039400b0b0106411914912aa542c08000301c0d1400060380d000724459042828648 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 659132805 1250 659131555 659131559
    0x90803430e011d0f180405032a06010e0615030a1d0304062a0803070201051503010c0206010b0d1503050d2309040906180f02041a0102030d05151e010f0306080304 71
    0x410446004a544001c5d04145412244d03d0301030f41340b02e03c1170340c04441c0d50703000280510007081d0b800341900300900012a0130310b040706044000c50b611001800740000e040320620102d08503590303202c140160104c00801710391302d0303180c0022143d0007846030712008003041009442c090742100d000f10880d016240241c5883e0441c204012400d01d4802100c80210b0000c0b6100d09202c0c041200c1e80003540c82072141d41c0c004030fa507187c031183da00d540c03001c0d400040d8041d03814030010040309500490103034196078040403034030744500c0a10404800b4280302083c8100002c0100404400d12030041251000701c035064442d40c961440c0c04030ba403285051031000c1e400590750144075801c903c2c81c054014a582074000d40000c180140034120a004c0001050320460350140d12030075003000c5007401d0082c10707035a4000308034a004030b609d00030010352030b031040740003540e001c50f902c0740001e182c180d0b503092081d904003010704503034049038010212031055403039100228003040d00d46501e5920b02d48a0300402d800d5803149005181828 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 659134055 1250 659132805 659132809
    0x23100812041403010f050f1803130902030a20030414030f0703050702041506090305060a0608030a08130b0a050103110d080a030e030f0706020406080703090803430e011d 74
    0x11400c03800643d499500c40a1420020645010309400703592156071300031003410306480d811400740000ca48900c1540051210100401c50b0b45203040c1250000c80c4003603500d03510000d04500078480035840c04281441c4d014018114850000a144118130600005800e54400050103540380030b04058010301100400140307001920807009040054809000030648400711141c40002102c59000a80001e5042002308103201c41040200d4101c80381013802c03c031302410140340d56107038810390301c000003070000176404142c2114021605090460b00201010543d061078600c040c041c220070311094508022110348004a4139200906030341c0c441e070002e0b6243c540304800200385c01038904182e064440c2d00052240d074002015210084ca1003501c65103005135507d0074414084c0c140c02d0054044000c15180c10302c844002a0640110f079000141561001c03006400807443c1d040c50800d070403086940c200d031042075001e070b103048c0340b50408000f0540e1101c45c0414038403030044030848104042400c5100103440040818 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 659135305 1250 659134055 659134079
    0x4361406190204270e1506040b060304151107050303071205090d02060f07050f0c03070b0c0f03240301180c05010f080114120a0b010806010603050613050a2310081204 73
    0x802549002180722020030f400107042142001c01e800141c2c62140c01c0264601d8035105101c001343c811510141141040d0f00c551032090b000b40200b6550944d25013b1305c020030300c0442070b00d03c03840d0320600310f0360b407460108001400165090914801c1d6030602010480100700803c24040400d401c3e401004541c3c0c03032482c461803003038000c0e20100905c10f04210741e882c1030039100700034000c0c0c1480500441c2d50b0b016515210584d50b01c0209480040c05c001d20804100380c0c03110b01181d17041003a8450075022048001d043c0c80712140d10030035071035266281a150003c1c0c2c10940450341206402518007003030655035100103480e4504114140b50001d108800140000c00a0311462410010003619107500b6001d160041d41c61f0403810b00040c1d4030108070400400c0f108804022070750140000d481c090109050240201c3c1a04e000000a5008262030382d000500013641584a01c0c105038041301c03d0b45801c1c54005031000c4694003607440b01040d038024070717000c01c00e031800058078028038400c1000e4a2405107481c800c10740c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 659136555 1250 659135305 659135369
    0x602070905160e0f01120c09050909012a0203040902030106120f0501300506010b040f210311010f0204090b031e03040e070909020a0503090c04361406190204 69
    0x501c06c01d503120030740c442c500e1301c03404204421a03201c1391103042c240001c0040c40d400017007110b05160f050289659036800d09184c4c0085000c200c41508400a04201042e4103500803034000740946031000c000003130300a41c401c0450300c0c1892075103410040d4a10b0403e04a0984109028142d01960038403000d010146607440d40e0042086d1140d545d0307110340307116581c0c24100702007170348400091100846d0074807036181c54201d401c00030813500400e01510903850380e11070031004038040064284942c0c0c1c550315198071801e410802c0e441e41c20000071940c0d181c5440d483e00c01443c072000c01074001e1146503281d61440ca00780c03a000d48412982c01c000c50400b4900440c91440040c010121000c1104001001a16039510700103010050f030581c0350703070b61286480340d41986000c840340344041c882c5042070548903ca00d81020510400600b42c901d03000c41d03d075486102000354a50250003000192070440b1160421800700b0040e00032007015194110800455200d28242e00540c090001406121142c1c8980c0104030f401c44a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 659137805 1250 659136555 659136557
    0xc0e0f061606050708010918020405091005010305030414010c11040b030f0d02030403030305130b16020a0c0803070c0b04180b0d06050702150601090602060a0905030f03010602070905160e0f01 84
    0x21500034600c42004046801c0441210580c1d1104140b024050700800c84502501603004104a8200c002d000584421601e400183c09280c0d0703000414110a801d2080d00d0314070070303412014803c65a40b40f40c01540d03a80240301e0600500c900300301d0303282d042d840307900e81d2003d0680000300c451503800544104030060110715210756041c46100c5080c11900d03402d003e201030a0f00d0725005140c41c1c901d1401e0140a991000308103c40c00b142e043d40100000d48504c0e11103030040301c002d03000e408030b06410302c0076480c141180ca0054140c000b84400001c8a4100000400c0c005120740d4407000800d40d12000100d443c0501d0140d5417031041d00500300442e00038682c5c8216040344c80100280501e0310b490300c41d1011a4815501100107800c009106502000d41e902c105c2d8100170286010300b030080c9042c0e4020348505000d0100ca21040c1c480c80903506128040040d00d00041c600c510a50303407541d60300303800307540d9039800d01c100c5035010305240c0010784042108000352440b10150310b03058264550041040b06c02400445d0310344c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 659139055 1250 659137805 659137807
    0x6040c050c060c07061109010203070b07020c30010509070b070213021603030501080d0203160215031e100f0302240408030c010f0c09060804050a050615010f030c0e0f06 74
    0x4600401c2080301074041e20140202d1075460003142419416038441c0102025060420080001666400000c46412641204801c622901c2e0041d00f04e06008280440940c04451407498a0200389028202a0441d0825101c0c00b544192244045d013a29800c85130700c00c0c036801041c4100100b0180308014030703c0c09d1005016035092290654044200d0300650900024600700501c00c200b0986c140c4141405400303c0c00040c0403500c05560029901c0c4111918209078070000400a4115103503400021340b59103000119a880345051010603030034012240d0150940880140860002c14140c0000803d80303c4801040003400c0c21178091008519031003840307014050801221075038441d1400d0260000d010300d0005156240141c8040e1402d558042c0d502491803860480c43c0d0610360740141d50002100c2582c1804103183d590707406c080d400c2c43e9152074060410302640c0100a00081c0c0b8900042d11500242c81c0c40c055a204110210119031030300403410081904410f81c20014a840159440c00340c6004200e0303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 659140305 1250 659139055 659139067
    0x302150c0d0204121e0206040b0d0603170310060c031d0607060c05030912130e040f0807050c01080124050d090c0b070201030b150313030504080d180b04080606040c05 73
    0x60070880c0d002e9444000c1c00c05601d55084104207944800e12040c01c450480f000405145800045591080d44078880380004002000c2040340e21030340001d80103541044841c2001c0d51004000c01d416841162044020060280c020400900800d40009110b070199520718040c9525507588824803a642d410b02da11140500c8640e00180783d034064940c42c0300c1c0c0e59940d03649a0610303000301807500400a00607030801101740801410030540400c41c108851108400d01403d840300d0400e56513112007510080d0046400203010414464001000c00c3d031941d082ea2004100c2c4e0360344403c4003042125041d18a600c0c840d40d10400482403088001e0038a0320003510000030142c4107641d680041009560201503802c038080740f0141076603018490300c1d243c08006c1c3c9501100b108040c40c150901e00c00180340001d4001d11150440c2454883e038141d0f0007a0090740300303ca0300f01040c020701404600c51244c0c2403a61801122004c2420350712041917030700b1240c03070800501441e280e0034100000342407a01e001c101040024058 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 659141555 1250 659140305 659140327
    0x3021317100506030d120f0b131a0f011e0e0604060306050901050d1203020d0b060a08151f050304081312050708030f030c28110c0a030302150c 63
    0x480000c4980c000038848012440800ca0545800520440c4a82c00c81d283d2250126046588400c00c14141c9100292009145c4004c600038050310701e045403c02d4065a42c09a02c8100b54000500c0c8820f1b490001440004601004040b040540c0ca0500042c9062240d0750702d03001090400c024860301e420644000e00101021075080d0704140c1c8102d000a44442080006003000162a4050001900c1d00710100b002600e81540104000c0300d00c0d010075031f00254000059145a00c802c0340c0d041c00800d01e503520420828001c100c0788041c0c4420207140380c2140c0c515558038028035852246000d008441c540c1904040c82a5201d03000204140d0750004104600014410030741341c040c02421142002c0c00001e034580c24030a2920207a50003514a6038000c110f511285846401581d500400026001d6614540306484104040c000c05111100440420311201c02c5508a1845024402001d04981002c1c0c206020006001a503110150241c0c202d40200b42104902410350344c0c1c01000144107501e80a44060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 659142805 1250 659141555 659141579
    0x8090d120207091a0102121c02070f0209061f03090f0203010501080601030312020418090213060b030739030908060c030f0703051006030c0327020901050901080607030213 75
    0x596500182c1281d101030000507200d10520290301e074030407400d004102000c1c001035910110119071038210400410100306402c200d821007111204400415501c07038045140080201d00780303010482c402d1404c200051120b0801804c40110350f13000340c1e0180d64074030408800360002c00c5548400d03910440001c00394000360302c090046038000d1084070001c0600d5891400c009180e101c124078240ca900e401000704100d01c2c2017003a21094101d1075000000394200107480019800c00900d40304101160401038002180104c0c0005588281e20a4444040380384090380b900c0c0550b000401a0805803e0303034aa4402030f5001e44107200c0001d0b200c0c0c00c1c031050851700c0305042450030314202d5880c0f0600000204014102107011001904495035090600c030500300995113400716100c0d40502c0e420141c2d13501c0b0f03000340544203800c410009800c46c54080e008072206040301703000303401755601a8084c0991400000d40f90601e81e03015412a14420003400d1240c5074940200c01942c4030401c41c180c180c5c00d128002c1030001d0225 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 659144055 1250 659142805 659142833
    0xc06121d0d030c120e100b03060405060103020f060435011404060f09080c0102030619060e151905030109060b0f07060911040e0c0907020606010e0d1e03050c010b0906010c08090d 78
    0x43d000701007001b007002c0700c9019a101d0107402e600907004079041c800015000214075040d00c0c0d0445d0301920b00d0f1410b0010500d80d0203560300500484084140103030110040803031460001b802c5e09446542c50200c214503909035102040311103124076810001402180150f800070103c1e800d803220204514030039881e140c0103034101482400303e903580042405241c1c0b8144101b5001c01c8140100442c10300d00d005c4e000303001d00c0040c940440c0034102842184811100560840f200e1058500b90301240250320980240a50002d00800414030300e400c0000ca500b02d100400d803503040344e040000c1c92030640710342d4845000c3c000c08141214240d040c85900a240d54a40c010803041040b50f0f8002d00c5014200001c001e18032001426003015900044c05104440c1d9124012015540040d640e030321101e0018580350840740c00d411080c8807a40640b49150080541c010020700c02ca610040082c07080110b00c2081019a12050310034602113140b50050000080220000e415607160042c2a45101007440c0c4442c90300030385074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 659145305 1250 659144055 659144081
    0x8100f0b040213060f090506030703020d0902030f0a0507120b06060d06080105070e0906221a0d03110610060822060f05090106140d08160c06121d0d030c12 68
    0xd0b4148a80c5a00030445c41410146103803103010645494045501031002601c1c1c00c00705900040c000440315200c0d041600c4080d401340490f603161014007011900d48200f54000c8030540603d01c800940c8000b0729140001c4940c018181d81c8003511000c04000ca19400050860005921040000742d0984284141480380c1c0c1244c03280142c9042c1c1c68100310f05468001c04040c0300345142c0c5030800022345142a803421050701040c0c00182c000f402c640c0460700c4030b0303021001940000000b48610406501040c80c1059841e001d080780ca09468411010340f844406002d14000030304204001445848a20030843c22000004441c220718045600e8200a4500b0041440078071a183e2050044190003440b0303d0004115440d03104030150015030000e04911340100c00509840c2011650005008074805d00308d000039403150311444d0555481002034407002145001c1c0a480e0300d807401c6811078101190310b1501040000000e80552a0f08100540003004800400d004000c000b1070b104e50104007a2244851000c45 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 659146555 1250 659145305 659145337
    0x301060e031501150e01032a051c020702120d0807050f0f12090f01090816080931050705070f050715020f0c01180e041106030403030209180108100f0b0402 68
    0x560040c02c0c5c0344070041c45504046c940403500002c0c11544046482c0c411144c03550003502c010f0101d0844031806441d40e802425100c03c28200c444020079401031004910980d40020a144908100c58a869281c0d1516020402240000d501039102c8c2d40201080d248054000d42454034020700718800b600728544601c488103051040c40700e040000c01004071490a503000901c004022540c03480014010b006036030450300719801d40d00341041105000d0b160300210103400c40000c1404010a25801500710030b803c00c43c80c0c82d40c052401860740a0085a00c18641d90b11400d1814856a6441456541081741501d4a0147c40000300b41d02c4540d02102074601d80a6000b005140048a41c49090000850445040c0034494948849030314082075100c0860b9940074004c00140d8950410844414104064607445100082004101509079000c0d20602c1c0040e0380c98841d6100114900c680c0140c01c1c0039113103455001e018003a1003114560007a8520107092000845d80000200200302617811030007900d011460 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 659147805 1250 659146555 659146589
    0x24030f090506070909061401050c100e0a15020304020108070e04090b011205010e070f05061e04060519080f0c0a020a0506100810062111090108031b010207080301060e031501 76
    0x51300c4803002d406411101400c101d001c0c03425401140002c030308480c1505216002c200d61101c1e04007404070441411060300c0034050031044c0410152900007400f01290790b110045562184000303a882030740c0c855581a10b480110f925448816602d440501040990154036160800000703080850741074000c0001e01804004c51445180050035102c40f00c0b0051303203643c0b0640e020808181011008021170f00c1c1074402d1503403020403016aa000204040004841940004e00010159807000003415642d500301e0b503400d12905001021501c004040d504e00001c05000c4e03000c541d10301c6211000300700310b6110f401210000401d542d542c50400804803a02c00d030501010508221450301481054000c0c1c11545007040b04504291080648885c42c0b8946207824644a010388100105e2810081000e80e000303003411403640e900d8450a50301c0d40810a144a070002c4082d11200a2005009540032540d1200c0f41c00c0c1235a00b03098080b41c0d00c0040d0b0a80390b5241c400c00700101204000300494138040c004410010701046 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 659149055 1250 659147805 659147807
    0x51b010e0105070b040201080402060c01020a09170606010c060b1c060903030506120613031202030420190317090d0605041e150b040b12010501030b0f0124030f09050607 74
    0xc0e80080380038140641007001e6400520901c3c90300e5070007076090a05c0401070b00d4900115485000d1002442015840060450344050308540700c8000c50301d0f00d008603110b0301042c41c401034503401c00b660485d0200320036042d4000010070310303000cd80c0d10f2038000e4522080100301d508070041041265506981160396021401c0505900d802510350004040c4c901d45007003401241402d0b50380c08000c05042400040d1030040080502c500090650b111b10303d5400d54072810a42800409907040c03038401d1140c011603800081003824510614190702c0c6406c0380f0000410300e9070312280b0603040003210340880078504201940203540c1d551030075000c1030f0054400146601d040d00c0e1101d001080e03401c022040820246420380003d0a1490413812140e0301a0003003500b020742e0000c1409010100881a07012900581d040c0400805500443c101da004501581c101c0d00c0d10016410110028080c03200800303040c2680b425189240000c408030301c850340c0b0300084c040a50b00441d1040700d9140c1c0049803d50488400e1200c01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 659150305 1250 659149055 659149067
    0x50903101d0106060504060e0307091d010614011d040204050312031f21061b0f140703140708070c030f062d0b03160605041e14130207051b01 62
    0x140307406900811440e410040042d0150282c2d100f074000b04542060300007201d46040c81088000d004c04034040c000c0181d268005000742c0032811203072303040b1b40c6040d10000b00e01070a2044a0780071201a1103100140034284001e41418981d9009590401e408000010b030f541c40c1080040c4880058000d5152681445540007280b10940081d400ba043d81c4c1101c00d100b040200c5075100c44030000e000c082204644240b404c140940100b0703000c86204050041c1c04c00a0982005020114081e1903540700b1426003d8000313480107025041d400380000e400180c40c484a030404100074038010303001e807004a081c62190740c0d40032031a034180c0d0000c03518804101e50440400845006000d110719282d001000d11440c0c52802204041c91040c60100281e1151141c0b92941ca080c4034482c5a02d200d01c0e902e60b840c40d21884082d00d15802403003070035042c00026091800301d00340c40c0ca140082d5100300c2100501020703014104070b903041e00c4200705a0101c2d420032205001030410810006203081061981c050b06200b07500140c41c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 659151555 1250 659150305 659150351
    0x15020703171005040f2c0c01080108210d110d0e1b0405060a0504090c030203070b040605040605250b04020f0a030c0909060e07030c05030705041e05040305090310 71
    0x1c28080c0400340302409807107281d03600695a081e50b000941d5010041d01101030301220715802c03107600100010322805002d85503001c030605d95040031100c006400c4001104d01400904c00d91746c06410440f8107001002c40c080c2000040300f18903d0146c204075440300e003801294400c0f40b4180c1c1c2442e001a801c60500701c0da02400b807802810748094880755100d004c4402e03c10303514902c00351240e941c510004019555402d4480060180a0710400c00c0c102d1929141e03814440c40e001c240d00c80e1140c3c07040022400140c40032501624030558401d820b0078503110301a5143c0d0440700910324141c0c10818240005001c1404e00c070907541c040c400c2400103040c240144640d419030b01011070b0007070118100074008205a000503400700c401c0030000041c00001c5003403050003450007507030341b10542c06143c4001003844404203201050310b02c12420780380c599940e101004101d90810746506100c0ca0b01c90707140c01219001e540701d642d1190107420401d00e44000034001905104c1c082c43c8400c1265030318129a05030100848440c94 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 659152805 1250 659151555 659151587
    0x1180b0307152606040b01093209010308160609082709060607140a140f010f0212010324020a05040f050a060e06030408040909030c110108060f12010915020703 70
    0x1004041e201c030919a205030041103103000b03175190005461b040e445680310794000d101d6402042a2090000071044d090b521842c40415088402e841080b4a4a84014154100ca80c006142447c242e0441e081c0a05400c81c0582030b18007641c1c03010300304040348210b0001d241c6201c7c11075098ad00d0441c4a512252006c000240c60b5008502050801205803615011038075500d030131401c1c09403110f808100c214078140100310024810101510006280c000c0000e003455280c2c3c54200030b014141c0890010300032409400c600b4415407104100400105d0700300e00c075410480400078400760700181100d03800d0083ea4800c41c1d4060001c1c80000d0100304918070682c14201500c2c04a6010380c0341490281c0003051f00b51522107a0348a000d00102003020044a84c045400802c0d40d01414481c0c010340e824041d00440350003400361621182441401c3d03681d813013003407003038030800c001020313410364440103018010309501e4202107280ea503513280c8008011030400f890984825001c6d6070096a64041480c009040341886c42d0841c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 659154055 1250 659152805 659152847
    0x270405041515030b01051908070306021b150103020907020f1b03160e0a150f03030207060e0108060a061409030304260a030e010c0303090803090c012601180b030715 72
    0x40001030300c035403811741100c604640311501d94100742204400f81025074800c480620503c14000708000c0e181d0064801031860b1039801005551448055841d8004041d0300c07100f47c102c0600520040c40c00071401030700b00e0f050380704484613000c405554502c1e00ba055485c52000703110402030082e040c5800c10211144003000295455020701d005215034403400d000e007004290a803a11101180044089100001021480d040d407041a649040c00307900d82d90b09000b61800074002805000c004d500803a41d66010344009050011118131305001200d20005010208040080c01c101d00c655595041000c0c102030400d040c2c102440341a19190310000901016215101e604003406003000310360483c56102c1001c60a0801201a07003c901c2e0480080140000090041401006104a0620000e4055281442030300d0315646000d400d084492281d040e4000c9850f54407a140047c007400c504081c124000c22600c00307000c1000c10000001a040980079000b095500140b2030500c0300c080c0d84412b400104106c04e8100d5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 659155305 1250 659154055 659154059
    0x7050c0a12021603080a021b10080c09060d021305030a150e070e0901020309060a0612030c0c0e01080f0d0f08150a030b0109020403150b06270405041515 67
    0x180c640101000151008104500c0030180070700070702c0102d00702054900060b910586030b140c103024a4120b2841c0400500c40c40c0c41070b07050034940d100d0026049100034803140e5007145042080b1100e4500070710000c000407040c4400000d548a180141000c0441d12101580322615480000c1a410050348540d02c60782c402e0034440b0200d100d1441582c155801c1c0d140100e292484541410324100040d030100c440d590086041180202066018601590642060b990345498422502d015603107140100c00c50881100300c0580020700071024040740c10303ca51101e25503c2c0d650395100071030120036808a284c3e600080360820b901441489038034001e440a090007402e14a20b000020b00f0b012001b08002085000980c2081e040c0d641e00031510010b55200008010968440640c40040d40051100f02c0c0d402c02d013a501e40ca07610526008184405c04045c01d0f06080400483c910307542e40040b0240c01c0d01c2000039180c6100d150b1158051a032040b4090910081241c1444a600302212005440740c58469240d000c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 659156555 1250 659155305 659155327
    0x4020d1e090b0c121303050c16090e0c031e01061e030b1803040e0705070b1f0803041a03060607051b0a0b0c060610090e041101080f1b070309090c170705 67
    0x1801d41c2003085d20003038001d030541c90318081c0d5031842149801c02c01e0344160385031841800c80055245080d01d4150b00d0034400c2c8a1181d42265640f14500d1840e5415042940101c211045c000c07400c01045480c00000b01d0320b07554030140002101d0f80c20805601240c0045028001d00945000640d0498566000301c085000e0742407074240c8134000ea0054032000d00041c00425409171040080c2c90600d6041000340c0760700d00b0040000c2c100d42d600d01d255499422006400000d0184004c0700740ca0440b40a55066040421401407515945d480100b034103078003560500400b00803400c1040309003002c1d0001c826040f0840815410050b68600e80c3d0f1028041480400c040d0718590b1011030720541118050b01d5190401d03031b031207805881050741c42e005015035a0391070041009000521316134020141c0c003030701c13001c0c00340e1101d054000c40e15104450007054144400007410103c00250001c010143c001d280c000d41c05a110710b07000043c2c45001c00448001581407007030f50140035904010981040003402c29a26017928158 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 659157805 1250 659156555 659156587
    0x60708010b0702010e0402091c020a0902120a1d060703020a021b10080402040b03010e060a0507030e06040b04080f040803311a0705060c0a0201050a0c0e04020d1e090b0c 74
    0x2c00904008806140750426103c9406550100200520048008c00308410880f0505049d100030303441196140c4000450160910803100f078161401c901c503019079280740a000240949190320300c0c00b000c101c1003003040ba140a00406000b240c55030b8015a9a00d0009802450840503290341d8200400208261586036950070001c018032038103081c10f00799030340d8a00000b8000c0a00c200c06603099401c00f03044041d01640860454070a44002408103c99110004120101c0d1803403803050310123034404004540841c2c50440d90545c001c1c03103120168542a004141d147e1150066030004c50380d039002280c00c40c03030380441074644145411100d2241000d10047c58203c4503c480038441d01440b012032145c5c400c6551600c008850107150000c0440d0306a00705500b0400060348842c072900010352909010401d450354501400040320129902c14a1400c055010000298442143c450300c842e039030102c8400701006031001c4900300c040c000001980240381e0400440e82c0b00024002412100c00300048129030030342030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 659159055 1250 659157805 659157817
    0xf0303030e0c060d02040303142d07060c11210a0c03030b0301060608040c0b0a0504060503060f152a03030109090f06020d0204210b0a0c1709060405060708010b 70
    0x214010a4211900795202c0c100303015140c2640d0000300008180203010754580051045910950700c80790501d40780c40c00c8028a000b03c8030240c20402c500148071580200c105c1c000b05420541400091030451107a40348021600800d40403404a00b42d034030401342002003445460540e0191030198081545c440c1d5030012a071158140c00800d000d440c2c610001454409e5101e1007403503001034000c024258440c1c002400900c42110115014500148042000b001d2a0141c075015800d07030300c42c5e03420705081040c16a1030b0b400c010403180d0003c4220b07180d001d031a0740d84500070050400d0080704a6031368081460781ca4440e41528001c0c030701a03003012040801008000304990440382003000c0006d040c43c152501c00d4848a4030140908042e00114103101c00c0c2d250b1340e000703000712105054100107038414182440305010a01c04060304850004d00060f225220a40003580701c00c1d05842c3c41541500d036503811042d40c20782a91820f94907800780d810042000b90070808190000114205189150324010350480c1902c03e0b2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 659160305 1250 659159055 659159057
    0x914240d1704090207061d0f03040501050922050901050601110a0b09010912080717060603070e030106090e0307063e0f030112051002030c0706020f04051005040e010f0f0303 76
    0x22808000300410203000d071000f501c03a030042035545800606042c00035007a201c04c189155450780151440700400000c08000c14020300000c0e50400b8a010015070340c0d034000403001d0350031001440130001e02c18100b800c4030201c400b10400004150a01e11041400c4820040c487d07810f114400310a4040001c00050f01901d0f56031190403608aa516001d01c11b015001030000184101c0040203400c1c0b900da0070100052090702c80b550360b000c031802d0006940402d280241d03803183d0040b80030004641201d100b000364034106c190283c00420180d650310400c104442507445800031540001c124001080024000c0003000354014581c01c04480c1c0b0500a42c0035140054101c42441d8044024010182d0260341640c03070101c40b101784181c81c0c0d07039250400d000107d881ca80850b01030140c2040b0100c3d4040c64401c5c1c0b402413580d03080440c10036415940e031500960081184804c2c1040c10701000840f5a14034000d198030001903555076407103d28000d0b0880c0096030603003081c0c03410b69101c4424099002d0f2582e501040741c2d01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 659161555 1250 659160305 659160323
    0x50411070507081b040c0906081b0c1b040504031b0309030b0408030115020601080705100c0b0112020907030603020d0f030315170c06070812040c0914240d 68
    0x1144044215109030200145180100c2900003207260303020406011603403008031410000c2c903003402000304503400c400100f80031a007000010320010303108541e010750102406103888101030346c2840c0030240303400200d42d01d89680c1c02030100140c0d40f000c2c4c2089055842040d034040c812070819a5000e40314100c021002d010203a1a14056824180f048a50000850300410000c00500302400c20300c506a109024101d1080444101c03030a2013440014614102c40c1c11201500c499802c200422102100742241041000080d0500304040364140c0215070080c29520844100c1000510520820714070042060044c0f5107480070800241c1c96071242101a6640000703400142106071900b41c0040c00c003824000010054944003196003480d22402e0f8000c050601e040319100300d140000c02c070661140030303c0100002e005000742c0754030b060508203040d00140301300020003200e44c5a1405804407442054803441c101100307400e104074000910b04450703140c040c0c1c480c3c400000f4a89030101d101c14060904c02088003035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 659162805 1250 659161555 659161571
    0x2070803011208120f060906100e0f03030f030f0403030c02030c0705040b0402120f040201030f0c1b03140d0c080610081b040512060a0e0d080a021608040305030711040b0a0504 77
    0x58420104d0f807020840d4080f492490074401409080200b08075001d500800004010601501d48402207525402250340d07041c0c0b50270111000d105280004e00d0886825201c14400340c208541000c0c06140310799101d0f00d541c5c03124035040c28000c01751058050580150b40003000321040c604008620001500c1003554007103040503c2c1e03c003090007071040440d00100d1503c80d0091080c400e012510301d1340200c0c000d84c0d0500c00c0c800250840340455884044080c0130400300018500e4400460400c20001402418800450f00a140c981d04981d813100028105696480f0074485019401040240d003001003981c94600000b04040301038131204020780f0000081f0800310362281044c180c61300311805803202501013260a003a07280c44950703407407050310400c20075402c18541f22015600082c443c0c2c90010160745031442e40d00d980c4501c10003580300d0604108030744084021400880c000034000c0c001513106900844d0f81391900d0400340600496401864132460415203411603607030b9140ba00c0c07400e6440403140080ca42c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 659164055 1250 659162805 659162813
    0x2e181703091218100210061a07031110090b01090608060105061b210705070e0f0f0a0908210930220f06110a0308222004020708030112 59
    0x40c48491681ea1013040c8864015880707501041c00e5030061244502446056214840d000070040500345c40e0054000034400c0c800464030514440b9078241b90201640c80c95144900440d0940341034a0041d11280100c81c0100684c914601c5610300601c5941c024128550600b40001d80e1403040060340a0042000c0c10034908500041c0b102d958105000c1c03042c1f416048092003440403580107150156528080c200780081c1c51130320b210119210700005584000e655031042a040a0a0342c043e00740c001041d921125400011000c00040400003510300340701e1404440081000981d00004140180ca500015100041c841201d80b46d01b6400c180e0120224840905040160707240c0203400364030f051400400b209100e0300b0800056034095621111500c4440364540c1030a40d43d0803c40e0403d4462540b24000140c0820702c5290a242c105682800b0015010f84047c07140418000c0c0010698030612040d841644964501d285a4140c41090b10190b06010064490f402980030501c61901403140c0020010100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 659165305 1250 659164055 659164087
    0x120a021f0e270f100504021e160b070e1e100f02030d060b04050f09010608040828030b0108090a0302030f0901020c03030c0c03010507112e1817030912 66
    0x720b6103110030304850720f40744507106481d801c141c1c0c000c902091956400303c0c1500303150088804c103a200b00c070319030303141610411200380d0b91b8012458000c00840540351000001d60a110300380c003840c0141d58180100405000b0880220101d0284140146803803501c4603041c2c0f540b0000c1c0c48040342d98105540f412a0303008040e82988910140814694036001010440b26100d801074020307902c0a642901100300740c2d0090050494080c09900089511200042c00181314417000b40780d01d4041da2154400e084482161440030300044210001103515001d52148a5900c10001c0c1c3c5e0001c803400007001c0a44da603403001313500c034407456039103002c8c0300c00026070905681d0082280d1045483c01078202d80d41c4142984c480c0340c4031307003401304901c1c0700b0b50030980441e140c2071086000708105040c110181a5014080d2245010340044210001c5264900c1c1c03140c0c40015503a12603004612404031121032041c105141c072116140204215600c1c00704140148850580001a9483e55060b10218a80c0d21501101c0034100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 659166555 1250 659165305 659165359
    0xa410a020d14130e010e0a0c0c0609030318150c020613030806040608060906180c150307020a23010506030604030e010c0c1a0a021e030d1a120a021f0e 66
    0x490f0300342c1d00000440c0d0901011185c100c60107070140c0c65254858071010750640c0c20b282d44050000c0c06d0401c410000c02c0059008110444c4a030030700040404e02c152241151802c10710040c0c0d07600f98040011101e104e854010400d03800201c0c4003900d0b07030745881d5130283c00d44503003400080e082042c0c1100141468560303510500c0580030140896810346004401e45980721000c40e510180010301d0003d0900355840061084000880101300c08000d114041001405401c020007410852184403108004600201c1400e401003040340c40d0380d003207043c84449a40c00e40f40040c1900c1d0080c8c5c00307401000082a4081c40040b40720380d09182c01005406141040c410004054000c5a8180d10519905804000a00003892651f006030280c0e0f01a030401c800600000064442d04401c50b0001c00c900c5005046950100d41c020305d005000c4100891400081070050740c2d000312050081d8050b00301307078041d4501508600303845062480440021010040020300695622182074059800c030401c5554080b610320514103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 659167805 1250 659166555 659166577
    0x30d0504121104240e0903033405041e030f02040e2128090b0a02030f0c060912040807050405070302070b0a05040b06010c05030f0a410a020d14 63
    0x486092481d96030311013400702000d000b601e01c030300d2880098003180d1150560300c101c1448000d07604694602c08500b01c0e4455007400c40302e98250310800301510501c208940340224050380d07103540d103943c2400e5025811045170344035240e010300e445c00200000740e035040b440d240785981520040791128400041c5881c00750614000c801031a144004200d1b40031803980039026041881606070410340c210300360840c4104828208500040182c1d0042c48000c6902d4020401e484007407044034501080c44101c1103950300050407020064201c18180685144100262040240213030021440c05245c000340039924082032141500803612000004e103032a01035415280c440307403c04400000c0b442c0401d0540b00421088030111646003080c004a502941300380c0c0340210181c2e1010003545028152a4681455041200d00e0b400308814000d94041440b451140e9000280d01e00803032201070515191040c03010743d1384103c074054143c8180555400030394001080101c003642802d0001c1ca40b02007009481d042e02c940c41c0c03412 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 659169055 1250 659167805 659167811
    0x40918051b04050f06030606091b0a020616260603030f040308121b0405010804020f0d05100b04150b030601180620010203040b0105090a0603050618010b030d0504121104 74
    0x545201e000d05044902240d088804002e81e030340c3c00d48004c2c021a42580c3d060b416034811400580343d403c1c02a246600407a030b000120010039290260301c1211b9201d01601c20058002c0000d00c0300501001409040b030f0050782c00c194011500d1107060b0040f1803d160740c00c010603510b02d4003083c91914103004503000310600c6011560342d01d071203040c6603445900c000b04181c40291113a0001d911821020020400a00040007440c0750914040044401c200054000d903030008080c000801283d031880c0b21440300c2c502c82c8016000c50541c0074040002c0b600d0141050b8017032410b18070f000300c01036203440100042e5802800d140d9200c1d00d44078012141019042448606a0410070300454050b400201509400e4405050291030700c403040105400e07400140c17001071841200100602941c0f0b00011082d82c00008400009907660b602e8985920300441500ea0003004c1c860660300c8800400b081c02600360042c0150001d01c004092004018550700c90b910882c5a84140c0c1c04407081080b0445031018081c1a00a00c14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 659170305 1250 659169055 659169073
    0x9050a230d050a02100605130905010b120d1b02030706050d090c0e100b041202060721090f080f07060302090f0a03110118060801180905010c080a0c050f04091805 71
    0x2511590050801d80050305c12880040c1c01da24880c020f103016103201414080d0300c80e218822400c05040410390450302552152416200c503210103000307030a00710507800200508044500094443c0e4820040108501c450341c00c00b0340540c0340042c0407012282c180c50280d50b203d8040c8103440081031260001441c001404000245180300380314030740d0040142a510315111540d410092103144602c0c8a400d41d06196261000050f103028405801000d02509086036404c940d00040d000818200501802003002c0280078002c007001e00b03402c4000b4204500040c4a044000e54109940740c1942c460142090f0300040c41030303016116841c00b00b0590701d01600c0c1301004c0e504d030301c2c1642012108070110341c0090b51654440c4040b010641d145002c0312115120728500340d01305621001a0b20440c0c40316862a88c0302d20040e00040e00902c0381021003803890b0741d282c0c103038144002c001055801d40c1d8130384401c008090129450559202c03040768221b40280d9400603500d000108280d060303509580c0007a01704e01681100d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 659171555 1250 659170305 659170307
    0xa0302010e0c0a06140f120f070e101e0e0303040f05040b011b120c1a0f060405220c0806010608010911040605030414120f0c01060909050a230d 63
    0x40185000348450603290700320303158020f0240c0406244140000143e21348a2140e5a04a500080c03d402508143c203d00d4034400900600101d1000c6c1c80c1484e000907014108559682c3c0700f8042c7c68151400c0310003442c6249840300c020150901048140514629100b4410440c2e00031007540b04070400203801d6944071542c4071440c80700f00c03113030b0b2044600407030605040820030740c032030b101016450340b256894407411089907c90500c03001c010b20102d13091010310840600410070340340d41002103060401d1a40c41ca4608840040b42c5480003600e9507010310f041c0380611070752510074070074640810719083c196603004c501414407050714070007a0301901860007544008210a40d101a105040e603103101d400b480b91690782043c0c0c2590780310750f20460000070310a0011038006404544464000c0300440308403905141d502403465081d502c2144003010104000440e001106400e00802e402003440748030030812142c250b04c0b455111088840000c001c0504d000a880206204044405581f45604102c859840e180c00c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 659172661 1106 659171555 659171561
    0x60a0b1b071d0603100908180301090605010f030210023013142407060203250c061406030d030b03150a0b04060b03010806130c03050a030201 62
    0x1e0000e5090007160080211001404600146080143c1010719007484401c2e02c1c03505504140481c000329681505072407060014210014007000344a00007401400042c10080c600c40c6800c002150701301780d840310182980d00c00d42d16070240c1e036840e480a9039922405c1800104c82280031103540540d00119140810394907003501ca040c100825035071025194440c54008004500d420b04e0340540e0f910b041000700e040b00f0809268859000e60902c201d03205842032080242100d600000802c0603000349003800041c0442c000d0803000c0d90110082e005103000c407944425500035003801480000c11102d41c0e000c27030046034014010302c050713103e00c0300580c060486000c0140d8140a054150300000d60464181032046080c0f8000080004602e0100811034007560000b00c2d81103003e10051281c103400140e2280c100e40e040c8220f1442d1400c40c84d00c00e24000864000901900031117184904142d0150 = true := by decide +kernel

theorem cover : BRFrame.Cov 658992805 659172661 := by
  have h0 := BRFrame.cov_init 658992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 658992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 658992805 ≤ n) (h2 : n < 659172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
