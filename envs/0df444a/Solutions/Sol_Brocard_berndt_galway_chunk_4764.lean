-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4764
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:39:16.583453+00:00
-- url     : https://prove2.me/submissions/0af56479-4388-4828-8762-4764e9d6601c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 856654676 ≤ n < 856834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 856655926 1250 856654676 856654753
    0x60506030706080f07200709180209011403030c0a03050409050705090904060b1903030e09070305101502190b090f1c0c140f0a0b091603030c050a05 65
    0x800048010646074562034003c0251601801c1c02c452220061000040152010402c6441c1814551103c45110860010301600341011050320039600301c0b4003110403c100700ca03620320140c0c1e6007020890451300301c1c0040b80290484000442c2c110300c14030301c0c000081d2003560700d85001c0540c0603005104440c5440b40400160b200c880045034603101d0000c407203500c0300c081c00c04507010440c00d51200e140200002c1c4102c0050f80c89001d401c0184407140d205402061310f040c0360410302c0c00d01042c955400324a510b010030041c500f600e0000101d4a890090142c2c10305140c2d0740d400c00034000c101c0c82040343c09400110b206000580342c15000b070701003182d41220600440d506841441000155842d04100d040715040c001240c03000100d0301003006180030342d5488803214840500030410b1101030641040d200140014508604103c200305001900300001513000c00e0160569020f00c0244034140c1c0e80c50715005070a001507040c800d180510000010740725001d900c1800d20b418140d41320413601c05844521340745030300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 856657176 1250 856655926 856655929
    0x40e0a14040b07030c3e07080a082d091002061027141006051305010f031b020721050c090712020c060a060801020307090b0d09081204060506 62
    0x40406507801007420080c0408a00414007a8118084180142c075214502160f81c0c0d50841400c5602804d1400741035a401d4100185074042000e8010b110351000181480c82c40d1481c0749903100e0b00c3c50320140c804a00420440664002090700c032b00d582c4070600c1c29031002d901c4150f1400707090f4015054a48648080c0758000303100c500102e400c5115400c051141c1c80018540000c40709400000c1c130a00c150322a08401003140441e185c85044001202c43d89034104a01e000e400b020b607031007841d40064090101c180074a00300d03074242044080c25a102031034608141c13030245c0410340103004480e50741840c01003040e815480c15a400182c2008684400c45d4003030020600c1c0400a01c40b02e507030007010b047c03a005100d0380c03144c030301b0b01c0341d03500b60055501c0c40c25680c241c40c0f1f054440e080b41c004200001c00f80e0007400501c00414014003a54000e8540e1800844c9103041029016140b02c41503c10a0400100070802c1c404240481d404010181c2c0c000c0c0525640d01892040242000f6080b42c044a20301c1c60800454005d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 856658426 1250 856657176 856657211
    0xb040e0a020108042303070b0a060b070b0a270b0a05060a0f0e09281a0f06090405011b1205010b0a0c031b1707140c3003040e0a 56
    0x1154040e140c030f04039074807140c0b1441c20301403044956942910174808200e4403c0e008200406100e400381c20000403a082a8504000f0741d0780c292300c03030070751400b00b4040e18000c1000460036642043d0700c5100010b070700e18450384050500c1042d06198204910100700581845007020301c1910035044100d003000566214010001c2c210007600030b501d0b400b11114070502c81d01c820700c25003a81103461750040b01c130b688001407003000b85900c06403000d01918405c0a5580200540d5022394100300d025045110f4052409865040c90780c0d000a00781e5101e2001100030130180142907000ca12161011801900340c00d01ca08000f504c85802549070f0741f05039280000004040e04c0c20784c00c0d00c2d61076840781d907142c1404009032400c031120400955103188511004111800181c1c01240003001d9116000000317440c2e4109040c0f01010115403410404290051034101220b55280419503203200f080e06001c0030345180100203030032000355550b0805d085102c00500452901d840804a51007811b40312400d22100c401c4103881c4c01e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 856659676 1250 856658426 856658443
    0x2a02190f11100c1118180c0d02060306010c0c030b0c041a070b190605130b03101b050f041701090212010c0c0b191a030c0103051003081308030c010b040e 67
    0x1450348245000040d031024035450071010003d011403100b089160340d400910754250384442801b070148103289403c190030300281220708401c07a130f21501014560085007a900c4014903840c10011040c10780020003131213220820107160402e45641081c6002c40000c0260341c0b050003519800b0450080841054040104454005030b00c6a03407100541c8a01c1840c0c44030300080c00d081c0c4410b5859400c0442c090700e44c03103803500716010381e0703140480c911903110181801c0102070a540c2500e142040310b00000c03550018440c12548a4501e0b01d5070352280c10340210041c80c01550015148a1020040c43c000d0ba0015001411600c1c000c9070b982130944108841ca5003211281c2d01d0741c0020809010400e40841e01d60390030340d58082c920b140004038880c1c0c4821120122145440d642001c00c45070754105406080030000702049040a0a0810650910000009402ea05440001c007648000200d6010747c01f0011803c9000304410001c59482e00c1d0b6000c0303d28043c004101101e0300852420740060502c0100040144 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 856660926 1250 856659676 856659709
    0x60406060f051f0e0a03050a0302010f0f0b0f010509040b180f0708040308010506070311010519050a020a0801150e0a0303050901030c1d1908070b070204050a2a02190f11 74
    0x243c00e0310305006a50b4907068400305036019440041c00008030740700b488201c003203a12960001800e2100241000101c42c02c44421407416031502041c01d405460380c149083d480842400e007203885850381c00c00030b0040c200303903040a5004900070326481c50001d030440409000d001519500c603a1035450140844040d0404c450140c002041c50004001c1070600500400c2060b01074a80801c42988405034182580c40030340e81c0340703051614034241d211510079500c00c00750884058401507103403001e9202c0c01801c2c19030601865901300c203102c43d02c02034540035402200c0700107405400809026503038200130348140c01054845000c40c0c02c08921201091003199001c40240d845410700114070b942206000c884294068039081e200700384800800c00140c10415400281000f100380da03a81d031200c0c03052000b52100a08280c442d5414141c01c000150421140b22480b0072580c80030244850031401c080b0301e8501030050100c00c09800c458000144003c042d9507421090107441c0f402d904003550814060001007500f00b070b1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 856662176 1250 856660926 856660969
    0x30b01031707020123040b18010e0f13020d0e06010f08060906060d0b07020a08040f14100e0913120c11030c030c061c18020909010605010c080c0a05060406060f05 71
    0x8003100c24009215030a021205140e941050b4860080503e88d0307000c10480f1a1894503004941c00c42c0d0b034800180c07403081000351501800d0010040c042602e402d5103051340581e080e000720301e1050b03404c03441c0d10040032025200100d407a030396550950f0484065047c001d50702035021f900b001416250340003480c50b000340800b138104c082030121620b031410844000380c8140300318000d10f55100c1c041450000034201a140044141545070320708400030000e1160500502c0c0644100f02a1014664102031041040c01c020340340d03000b15554050342e00741c0003009294018000c412480700040344c03640c0488600100c6214040c1c48a01d0f900420825507166003013460254164000c8007142918107044001e8054401610600352040001c5413104050b5044e000f50f101c411007102c180b0b441945481d15115400101c180000c00c401400c02c40000c20450341c1c8100a07003114030001c0d0b10455030404205070094035801c05d05aa8540c02c0925040010b80020310a0b0240345103051004200e61821030011401a48880c40c1c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 856663426 1250 856662176 856662197
    0x902121311040e07051804080301062003030f0730110c0109080706060605040b040b0901211d0c0303070b0907120f060f0b030d0c050c0a030b010317070201 68
    0x1156200e80802a048035288580605126a900c842c00ba500710100740001a140090500043c014548a00304424201040c11405d00000c20301d03100c200d90650f03000d8980001c840e010380d030316105003210b9050981c500d407100108201120341c03c5950780e40900c019a441d110030307440d410301101d88400d0480400c1c0084218000e018601c0c036060340a4603041011544081c00d10480d004840d0858500290a8441110004103241000620710810001c2c5c4124100030782094144410a10b4a0140e40141c180e00f0340300080001c1a07a016052103284008041d041c4c40500e8100102a005029000c1c0c0e0961100c04205581d10100740102d400201540090000c2d804c044039130701c9900c2e606a0291600846018681001c260b2200075080310304140c0c02108400007940452421030122103421400c40360b81807501c01c601003507a0340468a04003c05242ca003101402445007842401c00403e40c9103194004500d030170010411409481c494126800340c1900029101480c12480403031051183c002d00049030b1201 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 856664676 1250 856663426 856663441
    0x2070f1703120613020d0204030b0604060602060c090307030803090f0114060f06070807060905031b061b0c0f030324040207080f030712090807111f030f0f06060c0507090212 76
    0x1a00f07900100080010707101e40a00303801c040485e44100380760030300250001424024403910040340341e0440782c241da00300700c0d40e4a0804000e407111406000200b981c8400641700b0059a01041b6210180d0b4002c0b000741d40d2420480403441e41c800e80d03024440e1065003800c01c03c01d8403003012908680b05100103000c040c03034001444200106139001750346c02c641d290814003102000c80e02070321034010158802c00095aa4084503030320541b48010f41210130055500103030030041c2c00d8027a5079413040300c5101c1004040c3c40300302c0c0b42a401d00306800040079019912000c82080b401204140740040512034020310300310045069824042a803007000e101600010040000520b40c0e00600e00030b41d400f10305490254800c8540446017070075105840b0095410100210f200c030107102410340714200a00084514080349501162503003601900d0b02110001d042d030300c0d48600d0100e96a90000c0032529401c003410080142c80f00405041d14907281c009841600c07034040c0219481d0b8080c030850300c071194843d9800300c060b5200d90 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 856665926 1250 856664676 856664707
    0xf091c030206061206150d060c0f1101062301030f0905031b28030c08210c071a130f0506012405070609150f060e13031d0604120302070f1703 62
    0x86c00a500242000380e202d000c10054468540750010a641c1d501c2c084111400080103e2509660141d8507494110100326001c03903800c1ca18250b0300c5056400303000059030801a00244000c0d0003101304242030560030741c00c20801100400804d604d004841e84e040c07114107103169660b0742d00d1090b0303140c6403480c0d070030000c994030b150407400300c410f101349007062694503c0c0c1d443d50001c1e00b00440c20700c82e00800340b034413080001e50710b40034550020902d0400c50402e11562240c100c9203000c2d0441080540c0c0d10404100b0090404044d14482c80d0030101780c2c4003020040c0392850340d1711000d00c00c0003a00c0d182c182c541404080b04254071307007050341596200da040c105661074070350042120700c404075030180040c22032038220703c41401121301100c440c0310000303107191418140c1d0550800060041d030503c5209448000002c1d004007540c02c07084542c1ea10110958840c0001c43e0192086800554000f11440440010144d002039101c0950b0200c4070150901c607640c01c4119001c00000800031400e4106218030400c401d11107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 856667176 1250 856665926 856665961
    0x90e0f0c0d29160e030303270f0c0415050105030a021305040e010e060106020105060a09050c040512030711010c020901090f0b060c1005010f0e0c0f091c030206061206 73
    0x800242e031080400b001e110030803151620381e000e0304080c11001c00503030b01402252811241c1c07090030300500310f01e65900000e4030384c40002c2600400c0c003449602c01c85a1100303028a505000454001c85000c80c018201d410358440403142500d10403800d05802d0980e222004900744102d49043e180d1500755240c0030500e80194000d00400000e5004405002640d81d550340200b5038041c458000009a40300c0c024543c609011058002000f036a0418040c040b144d00c4684901c0100c0d0140080000d150320b0301c035004181d03442190f0145501c01d600e000648007102c0c01000a110751417140f082c4001c1c0c0c001c440b00564045c50a810085c0d41700c050440100070403415504a008481c0d0360800000b4986070041c0081c0544c1c12502245096034091003040350020417038851070340540118001c00040601d410b04c50a10010018500c40501d20f002c02c2440c4400551b1040e21716141d002800c101c550700d41e400ba00c07590702703014100c1038006104500115155052041c1580c6820031610701401082ea00c0c603080a1841c11903 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 856668426 1250 856667176 856667183
    0x1106070c120521031f063009080c16080a060b040b090c1306091526190f15031101111506010806030d02030904091a090601090e0f0c0d 59
    0x2c124510300414030711561810840700da80401c071307101d0410b41803107020000d000c00d01c01c0d0003e0001d4002d0021139004440d043d8000c20340001c1080c0c00e6030010b1450031403804055041340342814014910104400d80b07000e4a0315441c0f034001c4680e440b041000a205107142407080c03954541000d031007040403540541154041d4240034101082c2130029101040c210002140c40c10340079000850a4418825680c05160040c401d514018208a00386541d404902d110014102d0500c000100710301e55500200c09990519010984c40100520742001350210054488203003241c0d99180001104444409120300007004402c10083c010550556599648060040000c00c2c1031096104540001c4401041000c0c0c246000d03003000140303410400005407000101030212482a00104100c8800c5540001070312124602101c001c01d0301e4a4030305007540103900ca130b0000c074400c5000800b040b1040500003201e904907020f800c001c00862414044130ba03150906a440c3c1d030201d422581400c641e9190042c00c07445050f01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 856669676 1250 856668426 856668433
    0x1507050d050604141302030c030a080412060e0d0513090903120b03030c030703020f1207051b01030902130c27120501020919151d2e0306031106070c1205 67
    0x550400012103c1c070031036012032407441884845e011401d06002c11030f41007200307034010271040100f56039154040c02503000f003030080251f40c040081030001c0c41d0015429002203c06481514040390030040080d880451a685800440c10b8006070031b0210741300da92181d03905691240280507e622804015011002d6071700d41c10302c000c1c4406c0110101c144020542c113482078004140e604a82007010b42414000e000b00109114248501c0e40460030216010f901200c0307003003010768801490340c0142c00801c2040000b03904080204080c4140d26240d91104044079070310340700c54040c00400c068610000c81007100000c0c404241e0ba004015030151900c038100214030810001d8104403501012601003110300030603116500100004004011044c2020703206180c0520f40b001441891200540310b141610307100c0790080401b480c50f0010b81c3da001074900c43c0da002c3e1041d100c1c1210581000100030300010b000594200e00c19002c00f03111071800380111005154404134440d90342d407422109214a106454060b2350900 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 856670926 1250 856669676 856669691
    0x20d091404020d200d060504061a1605120414030705130f110325020a0201050a0e0105190801150302040f1e030b0708010e15180c0c010516021507050d050604 69
    0x1300c048440241c19088040c0719240d0058a6201041e51a141d200c1e40c09185030035000e00442c850042071480d0025a070b9001555a04100e42d025002c00c8800703c050580d02a140d4a0f0082c410100000d0045425001400050603207035002c145d04e54030345110340c40d8002c02e01403005040c01020b81103002d0b5550941d80004000089214564031688211102543c106d5000c0a40c035003041c0d401c60490100710544020300f08a54190f0000c2d0043c4601510709062004858070a0b00302ea1140341107541d0a000000420400565018042d100c205d0030b01503500106041c0c16030301d0000d071192098808441302c00c03520140c0c0d40e00c0e19941020109501400c5403817198202c1c804000324440c0e00181c2d010300d01d103503a031208a61602181c1415580003600c0b21038240c0090f0b040c0382e00785da84c81100307240c1c601d460311405a1705d849003d442004d80c411029002c8555007007200b0000860010103030030040514075002d44801c501940301d83da003007010841d004004a030050241e01c1e416140e40e88110750007540a400002c088 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 856672176 1250 856670926 856670951
    0x12070503011112100e040204110910080a060503190605070203041505040617010503032a010612120302030c0307031e020f0307090b0f0a0c050c040e0d020d091404020d 73
    0x102c0141c0d1110403548000111110b03404078611005038044418108030400e6810140082002c49002d400688942c0e20380021151201c0d10340125419118002c04400b101c00401702c2c0502000d0080f0342c100703d070038a4100000340301e04002c2001399590071214110501c90215584d00310040c0005040141188010310001c1581c2c40c460103000c2c42d0382810703140c0540312840c0c2000100580903290804030380054240c01000151400001c2d50603181e501b107101c281c00a8000034001c012039a2501c04001c640c03c2c01000103040104803900758101d40a5061498095880b080076010380c072007a038004408240c208000b882080c0301c3d500280310554400c0c410b201c940d005500d080f003030760000740754406c0500d40082030101c240d0b000402c0d10000e00652060a05240344021461031034040c01075000c0c203020002d1500700400400740804481008014030800c10304641c40c4005a554402203420005841040000c020042c00b4500240451302c1c0000b15018030a1204280310203500a0b08050704402e89660249544 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 856673426 1250 856672176 856672181
    0x80901060f0303020708010b0a050607080306220f0e060601080f042619020a05031606060806010b0406020d172d0703020a120b210a0503040303020303061215061207050301 75
    0x20b5000354000c001c000c0c14440403038212002c0030780041c0328098050041001d40c480c40290382880e41c000303403d1500e03603890002103451400301014030f02c0c2840e008141c1d02050380c036176806081d407017103a11010010440211074060344c0d8070044c0d840601003800c403400200503a0052506540c042d02c165103501c000c040c18000c1e02540510311100000340d80c404500d982202e1080c0c02e030602808079a100502640866480c1d07943c4911491401c0240961240228824803000e600060014030300c80f001c43e10b05607501d903010701c1d50303420501400340140a8003000a55180c4500e0085031440344141851409840701c10b10183e00c0c2c1000190059056900c031200344c0d100c0302c014040c41c0b04d8a010746026035941e8800d50f00404070304148842c0002a844c00c01d040c0d0b1070740c5a0400c900d10805040304030984480c080c03c40d26103050402c80b40100240b200007004000c140e0301101943c090a8165101640c80e240c0c00381860322910f55204140cc3c90302c040c0c0000e4801d18001d107040d280c40c00d68005031505075484201203400d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 856674676 1250 856673426 856673429
    0x607030c0f05060610080f0a110c0a060b01020705010801031a070c06050f0f0703020c03120405120c0c0109052b0c050324010f081b06040e040b0402030607110a0201080901060f 77
    0x1083d030030190410095007400203000600280501c2d058010386410a981d610744180a0030b500d5140780d9a10603d00f05207401d40888040701010422144100110700e4032802820600e80e44a0050140075070001c0d10b0350050000c01d06032688919000d003201c504440360b00c07203c4002082c400810150400315004540c051040c10b0045188110300c074064a4086860100761001801050402d40b040005141c100004002d40349480410302e000201c0d40c5840c00c2c414070b130041003003448141080010700140d50790000034030001522820b80382d218403d40c0c0c4d00104141d03030240d560080b1f240ea15003400c00d90009500201c29604d5403042046201c51515280403a10300031318110300440c40400021003106402520494500400070612502403440c203005c41c164031035505d1541403606030410180c050543e6520000d65020305040d0886032024030303060421350000380c07043e10140d010380198408680018465403454401c82504002402e81c800d1550044a03aa5001061403030a956103640108000010032070100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 856675926 1250 856674676 856674683
    0x6030528090501050702030c0717070807063504020d061103010902040306240e0c040e072a03080712060302130522020102120d021306021e01051003020607030c0f 71
    0x310807030540341c40c500315640034181c2010b640c018860035485c43c0000503090291a2280b00b408031881074411141d01d850200c1d04924218000c140010814681c0300f4403802032114000c0e1200218090352a422640c01440c2040b003405121440014002d07080440300c0302d0035940300d4000010f80d100c0420313404880d81c00c203800008006400140030411301c2200c0c06106681274840802c0f4a003108440c040901d98034070740c4203a1807119241030004980125510680740205403040808c0710b1454213080c01494004d10b40034607240b5a041307081680c50000d42c15112920150301d512030400c292a290307025685446000791440e0b000d9100c0d007001c00146c903541c030741d01207454520b5800b00f418245004011203020b1401d00081d4040708145010380540e0740000c01c40d40482034481c5080c0d550310707060780d240c01900c240035040340482c0d0090780c002203040e800100801083c1481404100328070302c1c00070060036150150341000b090791a00d0800e1025180207401005824401d081400851103541e562600340804450140c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 856677176 1250 856675926 856675931
    0xb13050f011b1d090603100c0f110d08070813021207030201090b030c160606081e0610051509060c0601030c080c062106040b19080c0405040c06030528 66
    0x900d191450300c802403442d90018103025102c0c0c0603070425039501a40d1108828400c00480011481a4406010200100d01051828004a41e007807102400c1400c2d00d07081003001401075445841b003141d011403660302d00b00e0345503101801d98541041c101d4213090040d1244448034124240c100040e5100e1412400389940300c405020310520314000074148805c00d91048280f0401001000101501e0302c040320b181d13246031003030380320f4414403401c2c00c80c001c2059810040503417282c0c810100d4181c9418002c0340071800603004468071a6644441404074030150f01c2010f0700b0032400346143c01500000406010541c01c06031a680c10700c0181c80a40c1d107002c00a0b8016103400d00786a40c20f000c4c800090010390f140c0300c002d07901103190248080907818003200d1190003000c00300030000801c403190365a41003260041e01c0140110382c00c01001041c000603a01c14400c9408620078030170315281c681424021a88902d07005940e00c0009860040305402406004201c0007d580300000e40c0c2d0f00340a00c00415143e50300012000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 856678426 1250 856677176 856677191
    0xc090504050109020a09180f0e0a021009050102120d0e0610060201110f041e150e0348041a010e0d080405130b1203130b160b13050f01 59
    0x5000480744107030000d0103500e004202d000ca0311900f08601c0d00464807140107442c0b8011346600d001000313020084403401d1702404d0401c00c051041000803c8034240b8021120070140c400e180f041035035004590b02c0f0b40f5016802c0b100a0f4040c5021450103450702c8851600d000c0f50b02e216200d00c1c17074144007088800100038081544148031440d070920514a40e80c04440903180742c4624080b881e103440c025849181c02640c41551022802e81d619040d03c0f00407c030803030b0b40400c00200784002601c000c81048040307000f407007500000805640c0522010280740d06a4180c1c460700704000740c0f8030868800b180c10380c40103840442450b40b44e5072511310881101052002118120240c0c000c00100502c403007003e001d1103168081c0034000403070a01c400b2102121003c90b489011040c80e00110740280c808180c01c550301007103d402e2602c664070080000c203460aa050a005c0c281d54444c0034404e04c0c1d010b155200706000390f0000c03000c0005a08581b200340c2025140070242e541c2c0c01203a550500c2d241e040078481030280d444264 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 856679676 1250 856678426 856678429
    0x703050d0606030509060c0301060e0409060e1b12160311011715011d010e0f0d17120105150d1d060412020c0d030509090717011d060616030c02130c0905 67
    0xe080d001300c1f00300c54440c0b45524158008054491882000e031140750380d00c030750000700441d03a40070040014486040d07030310300724541e0720003181c812664086038011440c4ca001040c2c1c58030f022030364240000111014134951415501c940ca00700c081c0d0503100e03052141c1c0031903580041e1b1010784858460f005030712906a03c116408001003443c2c1c016502688c10310000c00e40241181e810140c01300640509480c026511000c0d000000d03490144040d028050a410021181c50191204020211491614004041d617640c510500071281c110645c1050450000d0008004c0540e080c0c00a000020340b271000480300d100014030b070a0400d10161801c840200021100007401ca4040c000100100811a043c591803215621f02828030301c10112124030407091400000c01c05400780140304001008030044044c00c2da110a441c50040d200203001024041c0c03610b0010f07240f858658101c4a024400d0107010a5100840d40c1c10b540d10080d08400726444001c210301c0c0b030a0b000703180c8120540c2100710755500154138034010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 856680926 1250 856679676 856679683
    0x6030109091703090a02010e03071d040501060501050f0f2a01140f0910021e0304050f0613021f030e100b120a120809161212180b0703050d0606030509 66
    0x880c4101e00b00802d0081240321080400c001107900e80a0034203403514803016000078140300403500807203013118600d40c1c04040d0294401466208030300c10b2000300030007611080196040c1c00303018076490b0180303410041e201e56500e01902600c42c1d84c40060b00c0c1580010290214411540c007054503d44980d5504001c01d8401050314100e5041003c0003908030403414802c510750741321141c03200740b504044c2e0000f40c030005407030304482442c80c00190118120384a0a09140903622079100015101252044501040701140205907210100e07034014001c160090100070705140162813007800609043e640c00005080d0740341800031242060050100082213100340701002000002820311000c664841d8170007100080e003218000790303840060700b0000d90590301c22801b1864500d505a03d07580c50604024006044c2507000c0c003440d402c80c49468100002614030004440011045c2c0355030343c40800f41c40040056100143c02850000d000e40380075890841050308040c01c1d03031001da00c4000041d40e183c0400c411503030f060 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 856682176 1250 856680926 856680953
    0x303030f041a070203190c1202030a110303010f0302120a021e040e060606121f06051b03070302120f07080c07141f0305071205040b01090e0c060f180603010909 70
    0x10403151950f810032140080d9240100c00034001031040020b004503c4034054041401d12a034018441c0041d0f0781c42c80b5009441340c22100281d8089019501c0c4c030b841c5900c0120559041e100b01e5617082441500e10380802124621080d54111207001e03501c2d021015031115800110302d584400901e204651890003400122a01035402c0501d0340c005006000050340c9030400c0780c0071224100c1700c0040d1070712103a00c0e400809041010900340b02d180c3c688001205600032001d42001650141a003a46039402080b6a40328401c2240040042c0c0181e00d04900f0304081c4005055403050200c030050500ca0a65901d0380a85c0c000554070007240c1c0803007000c201d1154640c203040036007038040d00c083d120801c58056039040c0c90007490075001810345507030008400500c1079012510301c4900d0401030125007400c1c240390140020070b0250034022401c050b643c1d01c841d100014080301c004400392840745800e00364a003890581d080b05804060038664042009615070344c03800918042c003100c0900140c203485924040001800c0c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 856683426 1250 856682176 856682213
    0xc0a1101051c2a0801030f020613080a0302160608040210020f0a05030d0f020f190509150702280608090106030204060b0c250521030309010617010504081e090303030f04 74
    0x141c0300c03c0c12074154003020007811254081941300f002c607040d2000403110302078074252141210310f040002503410f00014110315524003136000c0e58000c041c600c042e2034812159014840100e12140e001c90b006080001420001c60241d2040e610841c091030394260406400d00c500307450660020446800800643c40383c06201100c841085250082500c640405409100e010fa040d40a0702440300303101500510449070740700340c01010f19110100d00328806c082c5404c07070003041e40201c0c00403441001004180b41c4c03805624606103030407032815213400b20440b04002c0040a56206540f03406001005031182c0c040e04000d030600310f04035900d4031240d16460345080c00804c940800a905111841a240300507051300041d81c03c1a50041c0b545c0a4003035155840c0101025079103903510000042000100c4194403010540c0c4500c41095802800c40f01c056082c0c81c03042d07402500c1c4060400000750004d1080740321421030050342030b500d81000005030020f400d5410884000299900c000200310400c292089412541c025 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 856684676 1250 856683426 856683491
    0x1060515091e1026070903060b010305061f0306030f05030421020a03020409230d02070519091508060403080a05010504020c12090d0204050109020a140c0a1101051c 72
    0x200350340020f46001c2d49015500030b011304070640000c40300700880715032954004a0300c11099410706074801880b60400d40f20a071102e6107000b40150096100340030301400340b0002041100c0341c541c501801103206400c0c8000209040e55642c00100003041400c159160750f0040e806180c49626120298007a910078034039818a01c07016211000c0187d0b544588101134035015075000466020900e0600602806484050700ca0101d00709840c28803800028046480c0b01c6507406d0b07800203580d5000b8010700602c05554034040c60301d8500240701d400710580c0501c4424400001690400f079a0701c01c0c250420b88142ca00780c0000740060200710324030120703004181c0100000d4a0031440c01085191080e1102d081800c2c40e008070b074001503810469680c0c60544000c1e990024810403d0b0359450740f0140081d071103a020307580411500034608861030300e85420740d980076101d80e0140c204402ca80e40c0b40d401248800d230030241070000522142c1d0b102d800c6d0f104540c900c0c0d40e0810000071280304200e400500b00401c06400201c125 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 856685926 1250 856684676 856684729
    0x71a0c0d080925170106090609110d0203040f02060a08060102010c0804200f040c050306131e020901050f04030f0311070812070501020904020a020a030801080a08120601020106051509 80
    0x140d00040c0f11201c40e002d07110f1525028040d102050380c0c072086511580702c04410625202e0741e41d0041d4400011210b1100040188554030340c40501642c15000743d4102900b03040c810310354441b00e50b400640d482486205036070710402413540003403410303040040b8000004c1c1d640300402c6515602441003044944280c00d0100c0c4920305999080ca008000c2d2502129102e510031003c02580c4402103400c0560b400100140055042030000500076001281c41c240706140c200b904034584046880384461041c402103e00001c48540d00d401c8020b54800c04416040150802110360030f60854000360028501c22030314410500d940e410003d01201d00300101c0383c1682c0250404101485000401c0c00034009110316050321000c8600700031b402030081a05540d0403500008110f803403d0703030200d01c8110082c0300340c445800507602c49000755601c0301c2c1c8050041c100c00c030410003c035500d038075140720952050341440041100d0f512a000b04024020401a000d0703410780c00300c2d41e080685880c0c84056002c04a0220404a48 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 856687176 1250 856685926 856685941
    0x7050105070c060c23130503370317090c091e090c0906040c020c0a0312020708070807090216140f010f090f141c0c022707050c071a0c0d08 61
    0x41040b1103000e41c0201c0001d086e542e1000c511501801008020151251503402c401c0024a410022000c03003905c110040d00d201d00303110079026800450f509607440300104601014001c40511000d008580d0504c038409600d006540d44032a60b0b440f40c0b034940310300b4642740864102000d610002415140d901d8004400514540e1110440769610070001c40d0040f501100c80282030f03090403040c0040e07980180c03002001109004001c0d41000c20348641d90308440056640f1800c01d0b0b142c10706809403246940007098100040740d991380280600302219400c83c1c04050007903071a03110301c0154852046454001340058032048000f80710312815031003091024003505d00a90b03102c041e00c10700d1b114010110220481c4009030b840c1e040190408240890003510f036032080c0d001014007030b05941641248611074001c041440e010712141441c40200860030389200300e840f10b440984a680103103500d00c0151113500c00c00202c001902209040200394419160390b00c00304902c000c0d040001d1114030b001408015420310505 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 856688426 1250 856687176 856687217
    0x60501033e03090703030807090b0301031113020c071e030c0504050c09132f16080f07080403021503060603130203031216110615010302070807050105070c060c 70
    0x11010a000701c50400e40c1d6408440103000c0e5640801c0c039900a0110800c840320200040c0c0e10192400798682003465580c4060441d82c411050192080000c1c0a000400c0011a0b081e4084c5030150020f05801c02e84484c41512001c83e080140203000713039400040d0820100708403101030003020645820105209080d0303114403211304a46e1080c6805143c0c0c4400181c038078a0540c081c0d030360311600240054002c500b142c01c001c000e801c4591059003d0204942c3e240442c0c500442c086483c4071070300221031b050107000c4960008410805000f0303240030104100b083e004003003442c001c1c403002d0304c01d40050f5240c80c00c500600403010780040700d80c40400d00402c14000c240e5911801d4070743c05607000c01030441040359403002c2415405103900c820301c1400e1a806010085010302119010482107590302d419030200121881d03550071081c0e8010448070344011b000c01565102c0d8008003d041d01540c0500c1c0340014513a55982103c00403a6023400251085014800300501402051816a039030310301504410740e4100000032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 856689676 1250 856688426 856688471
    0x20c0105092b080c100911010e0d020a17010f0c02030915040f09050a2f0d1e09051e07210512221404050709120c03020406050103 57
    0x118816016103808151800205603000068540781c0b80484141403414070030755040750742c0c82c0141e801281800d07011805140300e04000d00e5000000d030500000454019604d146646d00c5e6940c221850801e0311000d070300c40c40c62004c02050100c0510b00d100e039021611508541ea9580c0d6800e06030b0515540f61b001e41c2e800800d492904104031800340700c0c07048040e05c00c00305125607400120b5041c608040041c0c440034a90042c1d00c202445403090043c98820050610246100b400503a130840582020521a280071000303428110100100041c0c42403440d061042e410501c1c00b00034a1a030b84030001c036010050107000d5600450065640303d0200000d81210700d45034685802440043d00040006034a40c120b0b003048a030000380c01c4008e8442c0c04501d283c0d01026a0b01c543d2a05001003050350104000210b40c210720001c40c0c4004800000c0d0380b04031707820040507100180400c02044a0320002166008040d20f000006501c10006241698558814403045d900380303504c040d060501d0301468601301e0403400c25542 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 856690926 1250 856689676 856689679
    0xc150c0b07050a02070801090f30030b040e010504050105010f05010c030905060f161a01050d0201090311030c0a0e1f0b0d1508070306140a020c0d05030402041b080403030c020c010509 80
    0x70f8941c08010800ca180038102c3d0321010031582001001d10500550346000f081c0b4501031086644c0c110610103050300750b241e104003003201c15415610020412031180d032000210f01c100400114424807443c0c40070382075450035541030f2441d035903580c0100a041714603440c01e8000d200c28280340d0100003c50f18054155482072068500400c40000c1b44241111000100d444040c01013010b0070328800141031045400c0c0b0010645103120403154008122880c10b0810000e006905035a807039030044c1036903120022110304000c0d0982600c80d4810250036075507401031407400382081820810300d52034450813901c0300c06c030800c640c0f5210f50300c03200c42481685046002c64131300d4076042e440403801044845009070202c01070ba2084415000d44800401006001d810407800c00d00c82064000d01901c0741c44100c8200c1c13191181d00c1d00c0c0b0744e2141c00348603549030240d00550760040c00200006a00600a01c0111805114100080000f032407141044101509803085d0500611607100810401c0b03111070000c0d11728440ca11546 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 856692176 1250 856690926 856690937
    0x70f05040c171f14030106060306051c06060306020301030f150212040f02150406050c100e07180209040219120e0706120605120106150f050403060504020d050a0c150c0b07 75
    0x10b40746444014036100b144644840c000c41c003542c44a91166000181a079107211b9424004005880e5200380100c0003a51030003081594000a4505200d00010000300100d40240d1030b10030000c0807400b00d00c0910b00031070007110055819a070030300c2c2c04500e0030b41c82800c21681510601c0301007400079821101c554004d5000c016448801c0c164000541e15400c0082501c520707500000d4041600c5074401c020b40102954281205c080c842c14401200955032043c0307401d0140c1e801200200001e11030251040c03070103024040014503060409010400340e074043c0f6a0305103414108003000a03450f03406802d0702d002008420040000b00b10079400e06880c0c02084c0300782020003d210b12134084004003940700100134200200042a0500c840621138040d1040d07202d103500ca201e03031808500c030244c0202c04400c682003495452900d01402c0d56118002414068000d036040005032600400140007000034a84140c05071412007445481c05071801e01c2c8254a902d400d080ec00000d203e500040c09051000f0380040f06410031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 856693426 1250 856692176 856692181
    0x60108122b09060c031d030f0d180510050105121c1805121011161e0501021b010c020309030604120c050d0f08070c1e23070f05040c17 59
    0x1440040c22900d42e000d000c09142507100c0c41d200d074040d40300780000d80e107000c0c040c1401590b85600c07079146c0c041d0220440d24120104400da0b50403010340e02c01402003030b079104c041403401100d8848900d000403804005c940c00e5a9039005011525151030024200c9004100800000301d016042560041e0420301001c141f015a2410400344495611000c0180c9000f602000680724420fa80540d00d40380e81f8101c98405141c01d01d85140746c401d43c0103c4a040142071112601050140d030b0b42c011200c04880c410050070b01f020510000100b083c0001c10f606140e2a41240c2c1c00091508101e0840b038070751041e1425036008003d41c2c006500c0c003280040d441500940070750203829000d403050310621142e210040c114040c081d0240348058100011300074040c4a80d0b50301100fa0384602044d41c1c0454044d07005031444580504031201c083d40d0741401a144c921408524000c038103801261544000b0b161003e1401c0c4d0070102c000d208190320002d85100502007107a00f401103041e0720f00301170502907c021380c26a030402240300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 856694676 1250 856693426 856693507
    0xe0a061704061b08160201051003080903100204140406080d0e01120e010908071b03020f060304051f0204080c0604030c0e0703110a030e0f07061409031e06010812 71
    0x2203c03104044884001900301e00c10b2009043e61402c50304441081800741d803508246105219251195980040c01c0c1c08080c1592100c0c05ea94000c40e84480d0b05100d00515122040c2041c006000240b2803100c0310007650181c40308200c10384050341c2102803d0b903c5a541e014145500c84140c990000e428200500407808c1000141c000d49042a00d001c400c5d803e005d00c420411804c88000c0981070b0141607080c8881d03240c815010a01d00711484041c2d404001c000501c240e5180a400035900719204504440000302c60940d039030004850f40303442800c500d5012500b084504414042c0300c9422100f102c401c1d1400e4156030740d0404a105600a0040720040500010b0501c0c2c001e50012402c4111040ea55803075130b16a10004001d4481000003422034003400220713600b00f00c00000c1940a4480c140c9651244644044984072560000540c2039454401d2070b007980281181101142252904000034141943c10105114640b50001040812061040003581070340701d4440322552a414805080600ca50480103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 856695926 1250 856694676 856694681
    0xa030b04050403270303050d180209010b0a0207080c1f0210020f091507031409040b09010f0e011505090405061318230601170703140d0e0a06170406 65
    0x12009038115240ca0148403c1c1600000f102044100444114401c014403c01c80d121070011403000502003902400000702405041d00000001310300f02441e994900442c1c0c00040c450711085e4090480c07410005926070000b50306100c3c04020b0000781008100c1c4491183c08950400801c0c070400c040c0107008184401e409200340407000e07507007542c20015511420b10814034003055000110147c410200000d0401402c0c02140c01d5910390340d09911071585c2c558440711241c0d03031a8040c540e07070781d8060f99400551300720fa03840012140c0607000781c02ca032200c103d082c8100d60f0304110301170f00914040c40b49603081c801095841811100016016103001c2000d0320780c440819145158441030030402d60400c4220001040341719641844640544458151154480780c40000d1500c00011008030f44c2001005116860b00504014404500d00080307940726962a15150385860003150700300401c2e0002881000015488074860300c020000b1680001c0746d514001024020071958402c2602d80610700000509029140c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 856697176 1250 856695926 856695941
    0xf0a020f03031b0705010f090602031206040204050a12050717062a030103050a12080114040216050a050307060507050306010c0b09010e011d15010b07080d09080414030f0d0210020a03 80
    0x3e00d15032010403003000254507a25640a40d0f80001c50340c2a140c2c018911510070307181111850380156280080ba220002195107005200680140e002c2100280355142d19080000601060010f4441980c051400c507040040540c80034111025030412240e400c2404902146c000c07151029410550000e1281c000c002400d503514041c070392001100007c140034000c1040340c0c0d8503100d041400c8480c10085402d0310210400e010301108150030b00c140d040700c2d05041e801808500000301c8040300b0481d0300d80d281d928020408800321110b40021038a03604020003030203035030b401010908000d0704501c1e010300028401e0000e208080c014060aa01040c2401020740c04250030000c801c009101c80f10082c4000304c10815041c9201e44582704803e240c2c007040100c0038806050f20824804580303494a1b60b103030345ea403d4211946445400760317200790041c00201c489000304010813850400a2400a091041505240c1620041c03d5290024003208007101d0340401c3d004e14043c100c0200589524038039000328001c0205 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 856698426 1250 856697176 856697197
    0x2060f0d0e06151003060608160e0303040f051323041412031008030405030a03390b13020d12170906010e060a0b0307120b030a060902040e0f0a020f0303 67
    0x4080c2030001541da203da040f050b000302640e4003603110b0001141241200c00d40d01ca1900052262808a0481c04880c40180d584074100c0c90f00065a09104c0000781c1194026840403040304203040c410001820608810100028008010440c1c1c0c1100e604007110308841805c0d110b00c800c8100c002804001e001d040440c00fa9841900321054000d0f200d105081c513900a441f00c40d4070b503010b0040003484041c000200c03001c1c0e54000d0080c0c04040c4031940c080e9120207540704459111040d420381040c04125a041e00440f0182e4071111584000507810041411a4054094101001d07031000450158540f074060046255114400400000742e80404079040b038a141030b800f00003045101031140111001036803c0c180c40306400782140300d44611040080d440150300c41c13002028030a10000e00f070076008a44c075020300c00100d00c020401c152103100107030070200b0104080f00d2040e0303910070342400c2d070400c6d108071504590504004d10304115540700d581d556015142c0300910a41c00643c040342503490500c155003210705c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 856699676 1250 856698426 856698433
    0x203070221121e0f07030b121f02041a090f010c0b06090a020408030c0f0706020309031b01091a0703140f043f050c06040e01140d05030a0c0308010503010902060f0d0e 73
    0x40804484e11088000d445810010781804003c05040c030b401c140303d040e00c0d00944d00402c44110304640c038140b096640d0f00760744002c541c02d00c030004410b07200490054030900d0403000c16030360310b100c1c0c41040b080034410300d08141005a8000c0c00d500180e550411030b504107a0888031010969075944024010f88203607007080620703001c00b04105080d030000041901088a810301580c40c21511030b201260380e1f001c0c0d80c00450b403580c054001c028000381450084280c241c01072401e03021550b141d82c400c50840340c1c0c529100b0906a00040c06101707040c0d1107680c514200c101c107104a450b058141d02e2400380c41c06207024140070000300b601c031040c2c10851139480710100c20700100464012003900d0107000c41b1071003840c0203403020700a00c20740341c0b40c1d4540035044800755a094184040583d00b0b103000031200c0e0041030b10068000d81003285000c00304074200003604d00c140b9255903112082e040c0b0300d001481d0403c1a48a82d020381c0c140320b013982c016511007060362005c1141800c401c0d00c0d01040e90035100900101d9034204100d00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 856700926 1250 856699676 856699681
    0x1e050307090e060c0a020c10172d1005060c070e0915070318111206100f08010902030303010b07021306080714060306091504020d06090203070221121e 66
    0x2a856000048a8002c000c280c3d0701d950340f00500300000e0711802c0300401c01a04038440070001c0703142410400303003481ca8030f14165410398200e403112078140788140c41e504400c21241c054041e000c0303035250040008442500300218541801a10f07401c615149001c2c0921542d40403848201c4104100811001016100b0303045071142407900c4030540303681c80719150800881c0740200140310303e4040e010f03017031204100744d1401e03154000c0750311031444042d9146404c41d4030640c801203c8401d040100911030240070700b03241c04c00c0e0240c580303000034030700719074641c0325080c1c82e4104a1708c540943d4010003a0386c115459a4600b89d5540c0707035840003410400303905c0c50b5003544a1030241c02140500e070005072202640c10a48a0f02040818041044179030700013220341c60b520994220000d080410038400900d03034000051300150900e80007001e030600361203d07030704122080ca50200070855100d42c104004e03071000b402080026949028034504902c0ca11a10503048c038200f40398070204402d100c2a42d0591940e03c06825417000a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 856702176 1250 856700926 856700939
    0x515030115050f01140702101418090702161502070302060a0306082a150f040e0609010909081204020a05040504030e1206090705040e0a0f050a050f0d091e050307 71
    0xb4081c1c01e015141d030710b0381c0c070034075501600b40300800340354031a9040d0409050f5801c120b010745180342160108522250981e07442c81c801c03809080d1002c201c03010366600c101090144510964010461000c40d403040c14004e80c0001070602c2c007020360b030010629001005924406901d0000d0b00e03440290846030006005940c2a031541c01501910361080c10307a903c400c04a12210306c0302d485620104100c61000000000510f040350300e040365a98840c900301c1c1002c900342d00b121400d03000b6134041074030145940100100e519121110502411400c84100103880146d12041d40303500810300c18a1449010f00b010800b0f40d40e5000e60a40140750041c002d020318038003481c000f40406440c4560a0003507108051032000008049002841501e11400504096161800300300160441c9005003400b0f0207051403200c0820219000f030511180a04010b1090405a280291030080301c240703901101d40041400c812010352144041c0d048803c0032040c0c81d01d03003800b001c80050040003540010ba05215070207000810 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 856703426 1250 856702176 856702211
    0x603040302030406121125020901170f060f0f071202040312110a170f04030c0608061e150c030c250b030c07030c081b0319020c030705010305150301 65
    0x90382c0090740d034174a41c00c03130908103101980d00d104611410072605002c01c164080c50603c081a0b0245079101d61040d2030b8450b008540346400c207800141110758291184c01000c0d034101320610b02d1707000300b40042032685030074840c82400ea200a8160039150b81800b01040405109401507030890600d401c0440d5074969078684604d400380c12840e07000104240d02c8035040c00000114442a0711074124080c60380400c80b0041445040d4440a000c01c540c0106000201c080f0b080c3d012040003a0120b07071580c840c40d06001080050720070200c441c0300868085520a4000b035211444000c2a411424902c241c0361344035184158118001d041306030b0150b20907042852080c04400710005000a8800c111129854950401000714441103d071040341200030000040001e11458450507400d01540100d8104804131f91102c1343c10b801d0841d40b64065001203000d102c0e06a03842c6040c14144490300041c070007440741e200841d4827020103214160505a550300003450410204800500182004008000799002d41c192180c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 856704676 1250 856703426 856703429
    0x30a030f06080c090c03131704060206010b0c0a020103180b1e07020114063106050406090b0108150109091103090d03180f020105130612050a0c120e0c06030403020304 73
    0x400c1c01d0110001d24444086010300c11000098100845950340800340c81e096030000d080d15009421100002002c6070440c0400c0d540d00707580700000c0740d566240c00c0f4001e2500d4410f80080044038810000c040301c0000004944010a6081c200452242d09200303100046859100000d450080c02104201c0824901102e550702e4810403e40f050302034656a804034200d54040c545c0c40050341c40240422102d141694005a0002c1c0007400340220015054000c0c558003c60b0170100e4446440343c0081c0311500cbc0c540241c0004d010018010010400341c240000c0078040d02420031800086400c2d071100803a441200b90201500818500344110201c042c1c0009582d071084440c0045402601d100340610f42c860b005070130789040c900307071000040c4510b91540340c0301c440c032203808a0502504110180196060281600c014280f513210044a230080100c1e00b02900d03001003001c03560310304c3c1c480001d500c3c5030084180303600c100d00b1400c0000d5002801d00a03602c0c24540c040b00070b51100c4044104000c05500000510 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 856705926 1250 856704676 856704701
    0x90306091b0b210c0a0e0d24050105010c0b06010e01030902041d0c040203250228060e0a02010f1b020a0e0415050903121e010803041a03060904170705030a03 69
    0x1218202c140461000802080e2100780610008100e030009072885280ca40f07000c02ca00402441c0d0045041e0740386c890603848004a8040d000101d1030b2000c1e80c84049c81000d006000038203000315010040e40c1d4000d080a170080c40c082c103028484590701126442a405078160075405402040b1070368800b102c070b61111b112a220030649114061202600f42030900940c1d00841c40d10061010040c02d081d0400d200c04e500d0a4814214443c401b4031600744c40d08206a0075000780103181e12400d020560511303800340c602c0c1c0050030b4100c0c0c0c001004140140d902c1100c0311014402c1e0328049602c0e0070514140d0400c440490070281d07002d85146000710320404404465402241b00700038080040703400c0500311040e50320803180100640c105000440d01c8140d4003007902d81c00210024068000c204032024603401d81020380007403440d98400b007000e0008280710301002d02503c10044d0f084d429450501c00007041030100510041074003004c500c2031041c504180c4242d80300e6560190a80341c4410414100078001c04441e00202c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 856707176 1250 856705926 856705957
    0x60513051002190507150b03120d050609090a05060c0a0315091d0d080c0a0e10090503070b130b0d020906071b060c020306060f030f070306021e0a090306091b0b 70
    0x407403c0d140207004a82030703213034440c13614034403282c0c003408074002050141c9026405010b024480300080c00803000409903c0f808482c0064581800320030311882c000000c080480d26441040a140495000030300d080c2d102c010400103680d0365a105000f180605030045010f010303108510b10101c2c2e4a0807070b0304101525a17a07202030078000d0030401002075450752018040d102007400d4001240e80014004020300e02c00110b420a81c101c041040041000d16400317081d40000103a00700c80c03d00070351400b40200002801c0400f0503909102080c1c0d0f1440c807124162181c00303142c00700003c612028002980540b00368150003880c244e151615030800100c84458001381e050200206200406c01074000c00d40f154000350050018607844c1d5983d0309006070501e00b003002c2e03545845514400c50704600108032210141d44600c10150f162540c0d103041201d0705c004040900b04281c01031225800c010b610011200c21290020780100351000107003010000c061218000210290000b480450400100b500901c044070107550103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 856708426 1250 856707176 856707217
    0x9060e12040515030a1515110303061c0f081219090b0604150509071d0906010f08042604030302160501080c0901170702010606110d02030304060513051002 68
    0x309040d105078052a98001c06180314034240d240108040c545c42850034500041101680517610222019980104031001750b8a0481030302a034864005500c860f0b102c0000c50550600b140021010808042c040c9445489441014203101502101c0101d4079000500c142e03503940e04860341080b0610865100e420801c0c5210f905161000600c1400034050308070300b9100c11610781c1c0003003002500304244079560a146400d00450641c0c1c4608070240500e40c03c1e1034801d99403050085407907032801400341c80ca208240210800c0001e076085003405c4000b003c0d501e09010305540ba0316211211040c2c3c03400c1d455030241902001403441964200400a990094003280d92024003031040c082050940d0180d540011001004141308030306c070b80060401860141030109800141c03148040c024001201c4a40050307468a00400070b5a03000a5899181074401d0094403682d29030410296680c4400340000300940c1c0d4550020301c0e10205078900d2500703540e001342524491a000b000d400007039040283c5014480c1e80c80d044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 856709676 1250 856708426 856708453
    0x1b0d0206030a0c0906080106020c06070206091207141207050d020d1220061b0903011e1a010f02031c141303020105090313030f030512040b15040b010e10020f0109060e 73
    0xa406d412101075a0040100e546440140503440e04150b5080b03800003814441e080031680c0303c1030101101050b80c001080014501000290882d0050802500410092031904c4c1038440109200c425601e06940c1820809140c0c404101c0001da42c11004d071000100c0704411000550022072080413a00c034801c04401e582c07140c0c10140d1545410303540c1001000301c0040006079000d585024143e4400001c0001480340209504c01000c1c840701380c0c00720300e0340e9590f1400c041c1300c10181c2450207584000303180c2140b0fa0002d81c0000b0750f84c1c1c0701d10300c8400303404071410b83c800c00150041d80190700c411074034106550581c00d050010401081420804030095424000000d04d13800c0000b0641c1c01c802d0b4003244c2900f200b451600e4440d0a4620004180c04020040200e810101030700e1090b680039520550704e04245260540024514405103a0702c2e80c401c0703040c0f0401d0841c40e030b80644090f040c25012166a01d0b00010030100380c0c03070b15841c4034a080543d402c0c10f2081003030180f030343d014800034141c40f401d44980f40204030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 856710926 1250 856709676 856709687
    0xf130906051f0e0f061c0506100504030f060207050111040b031905094b070603050106090e06011211070c3c03020d210801081b0d0206030a0c0906 64
    0x9800800045400840d40c40074545996413001061005c1c003d5860300d80e082082d5000c600d09a00b20b0b0701d40c0c2e521181800068208a5002c10a000700d916002e8105030030750352800c80c0c9841500000d820f103500411202c1c14010290700560900502040b12641c5a035140420507560300111aa100101c0c3d01c00c5420014010728050036108802d40009032503411507180012800ea40c0c1251394500ba8961a00c0c1807120800389100200c05080c1038a840104200c03510b0881d20740030300d5810a000700750400d0010404a03070845021404e0310801c140030340c1e40da0745060040715042c0c2900d000040250170603022181c941800402021014026061240c05644071021000801c03150300e26548440e04451803d2154000070500780f40e504042001d400b9125900e40000340d150400483c203403a540442e080d00205030380c80c8003040007000000e01700088658584141c0d1502d901c45c1780c2100341c801480008414040d612a0030307003008154010030342e079141d0808000d118014044181c106020a80c400408240c05007c0c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 856712176 1250 856710926 856710979
    0x3010509030904020d021b03130f0e0406020c03090d110a050904021f02071d0a0f0c020705060c0c0a0e1509042a150809060a0209030a06020f13090605 66
    0x100040d4900000c0506003c002c1d072098000e0300e1150342c00e006e420740c040868082c07101a00c0c0395000075a101c112900041c00d0724440e9600c110030001c0321080420a00c1914084943e0182d0407680c0103071241402d003003e9086109500c1750543c4031400c40d24200c1044441c1800e8045500261002c194807a00c0d40c003840306c0c0650035140079500c00f400c00078190a18100c003011041500e428410780b0b007019035034000e1a050b5440c00c505055004030080420064044502c5a128800c005450034001040c904001079103405040c083d250240d08001024900c484040002000581e80540120f085541e15007140303621103000c1d2000081011030042000c49482d051002500a541001511000c81c5686a82241c459200d00d510320500b000443c0024603501d5000501416120740d4481420f90f1500d01c00d000d0030254003c10ba000c0e00d510502100310f01c0c1d1000a80641c4881e03010400580c2d40440c15400340d0280a039003520085480800c03404a44070074140c0090046690070b81d003542503150240d401c004c061140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 856713426 1250 856712176 856712191
    0x12020a020a080c010b03030d140604093f170906011d101503150f0f0905060a1a0c0c180703020a2a0203120c060c2115010e030105 57
    0x800381d001c04907080500414559a40740000a0001014004030341940c000140031038140340ea84c00d0111036551081c408a5020804980c1000307441850350381c0143d03058500d280395002030f40b02c117030700b0311284024107140500d0a82050340c01004003801e0001010042c8240040c0d1020500c20041000d02c00e0009a4a040c1d03204480d4110b80104401080d2034006402020710007e400b08140010720141c40c2880402c4100980d41e0105407500100d510201c014110f0344900e02d040712034002000110420898001507810007080440d0544405001034080c0c1406d8002d030481e0641041b0240030b0318000001042d01800d110181d58400b0191400c0160507450f400c0c4030404000c41070000707000c0c1842075005000b009414100843c0200c0111034840460004512900b0103140c481234503020752034104a414020302140e005149404440808142c0b03030003001d000c0c20014203022400142012680f20116620100181c9400151600c4c0c081c1c40354420240000c140401c00303005507401d0702c0c00c040c001c1c140700d03628 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 856714676 1250 856713426 856713433
    0x30702190e010302150f03040309140102120a1b021309050d03050103050c01080405190506180f0705010f20010c09060c2607081206040e06070f0c0c2412020a02 70
    0x18540170b0000c03640500c44803103800350382007041c8054041003001641c09203000381c0e5450b07102401c2080700301c070300191210180d0565124105044507181c83c44100c840d140814a0300e0400c517071903100c0d20b240c1180840c500960050f103603802031102948035441403107164040d0342129500445000c051382214000e020107456034110783e10030101d40d40210030b916002031148080720a14084641350150000190b0412034068007c5802c0c0684955402c00e005400070044010300500000741050a80d110741c2840394505009819048640c0d007801402d0808400700605001c40481520020344c90013003000103a10004150220740104865120f955943c1205601000811354404020740c030b40050b0306c1c1c03a240c09040b8003042012500051808011b811840001c4452000c0c90904108000a9400400407015181c0c0000c0801013440e50007050380402202c0350600300c0105146061018101d5030320380185c411101d03180c288174002c0c0034070020081540c00a56800110400c2312000c0c805a115580040b40140d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 856715926 1250 856714676 856714679
    0xc010e06061909020f1204060c0210060f1a1903050a3c0e030a08040507091514190e04140f2d01050108060f130c0e13020a08030702190e01 61
    0xc080c0d40c000c1c905041c4c0c038417610b400c1c417840d1010110501e02c200c0342194599101e152003181c1e20303010030041c40045220402404698107080c4040c0200313080c0d00c22640d907000c000351704106007900c50301140c0000c00c10846001301e10241c030b0b00140203400181d0ba9401c1061801345004001d580700d0700398040f0100100031044464525510000311201201410035215955580c12280340d581000200079020040d10b50341d01c245443d080103403d0001603030106090508044181d01144005d610190a503880c40130080c501c801240b0110f43c0c00f03603c2101030050005841000709400c83d50042c010312880c85850103424810b841040c1589582e9500c1c00e1011682c001401c4505682c0441c429a68244004602021440001d1b000d9400d50343c00780d100c807915400200c14004904903d65905a0058500d080d44100071455074440342000c009100b03402100110101080e003808000740e903040c2064008040034221900c55540a4403940312250480c800d5803021001615403500803003c07800c5803a403102686070f0303a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 856717176 1250 856715926 856715939
    0x70803030c09192c0a0506030c120703021c11030d0806010f11030a1806090803090d11030d050d0f09051e0715020a02010908010506031002090609060c010e060619 71
    0x102d14500f9025140f12141401162034001303552005181c020700d15140004500c0041002844030b130180c00044007074104410403032075881c00140c020440c2e000b5680540c84100640d1050f0410141c2d400007940040a540034010210500c0c500c1117240740142d402113060500e1004256456041406c0030010451240010b036041d80070b40d401c00769226050410200014006081030300396404210543d001c0748561505001490510381d00c200500954140700740040e0803c071100ba50ba00900c9810740c1304480c214508001c100b048084124510006400c6408040504101400541111030038450481c030704503407000e89075550300031544203e820038050301c1c0340202404807101c4125100e541940f2881500306c0041c9440001d0b1041007000150b81c00740c41c440006100041c0703424083d60041e1226070520040c0002a80c003c10303a02d071030016050300142c1e07451500010a81c1400f9030514582e0010001c500d2410122042d0061300c4c03010100300548042c0c2e5241810030500d00354440d11b0041028440320309000b203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 856718426 1250 856717176 856717189
    0x70b040e070f1218060f0c02060702030403030519120903030b01080a150e0417030a05090706090e15010e031204090f110708090d020405191401120f06060f030f05070803030c09 77
    0x40301c20302c640021340f254181ca0398070548100b0b44d403d902143c6e4900f94801c00c0c42d03040c00b103683c020b8500d102541c901840c40d2001803442c09102680480040d5485a01c06140e0050310030720341c11078070240c0c2409007003aa0b0402034002e080b050b05840c04502c503c00080e212440714130510741040c0c814941c5d5030045042200e00310079860300410483d1481001220b40309408a204091849400703a1040460145003035101e00c0d003445540d40c0000b0074000c4144003482403140c40d24109a12a00809180805100c6500121004107266144035014062010b16494054a0200030415150460002d11514011500d00011910300c52207464010205128070000651580300a12540788000c6c68400010a80e0300060300b10b5a040c0c4e10080c0a6843c640255000701c45402041d0403002e4424104c54590f241c00c000407200c0600aa00410b0b2400c1e0480036000c0000a0b8080b8004d000034070b80c1107100d00c3c1c403440e03c2c03042000181000d44441c401d0080c00503e40c9130002c112845200110030203412b00401c502403000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 856719676 1250 856718426 856718441
    0x1021902060f0301030b01030606090203070914032b090812070320011a1008010305071505071407050a081f09020609040f020307030f2705030c070b040e070f12 70
    0x20710050030400302c8801c103a414080c2d0b0186018400340307417040d451490301c2001c807041c507402090640c0c0103100f042203194000640c003044960720102d03c568401e026002034200800300398000801101d980100c00d04820942c0b01502d1542c3d2a241c1590342510389102170f40d22401d100c01f9454100c1c0401c04c110020b4810003100b0b205040c03555910841c00705a400444c20344021103542000181e58200d40740b000e00e0642901503c0c000706081c1244d055041d911a0758540078a409010288054032261900345031003507084a00c019081242c00200c0c5041021142e1200300c00d20030103100b40c10204010a400d01d0114a48101103a03121020700f4001c0b0001c004406401c02e00da0607a40301e80140815152519980a00d03503007250b10200060b92858442400b9048404010902907010310b007411002145484040c15503061684900355121502e40c0c0c6070451451148045844682c05021000160040030802801c1501c9145190040554652100f1140c0d241e0303c40ba80d200040e450140001e104cc4154008035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 856720926 1250 856719676 856719679
    0x405010506190837031e05210711070f060212030f0a0c0306030b040501050f0a14040602220806091507120911031203100503060118150e0c121501021902 67
    0x1034091342c0c4201c503000340316042482a800b1403080d44902014401001281080b40713843d04101d410103545041105020f012100c3d11810014800f0110300c5150007003c03400303140380402c0d040b0354a0584500a0303c900c1902d41c41540054441c003500900408922000d4a10842036542152010703610600914094001d50124105140d44c90101002144090711500e21840c0102c00109041c01d01c0f007052403d800000f840c0c11354640c03500c84000090b4400c40c2155810a030011400750315065102c43c10000742c850021342000b1036803d000009140100403a01d84c0c40f46090f00e080c0e0705070000c44042c5a000000844688000822408007612188580d90100c08a00e02504102150004d8400440d00c1c4c140b043d103400070005400303c104010207804a0380c01001c0c100035000f500b00c0d54540300f00c484c56030f0380c8040350088058513a40441c900d81c0f00310409070011302c0758092902040c1004600c000450740070602c009109a0407900144007a8003184072091581010f038010b00c001d0f41c45140c1c00403000c19500f0200d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 856722176 1250 856720926 856720993
    0xe0123090d08041a011d07140703030504290702010b0103092414101403010b15030a0b04090311060a0905072303010c031506020a171b010504050105061908 68
    0x18050701e01564031406000089a4106140400020b140680c5001001f032030820210700140118052050282d80c501541420081895140c6140c8020300c0c0c114524019800f00809442c503d400b82c3d500903190142625400800103211440d004505440c45068090800310001c4200070801f0359800080c414000f10080001e620595a01c008001c118113503804200740862007018083c1c400081c5880522040071070082000700d40354808140310004640706080d903e40c0202c00903007408000c0e0044035001d50001d00401400c5010701d030160246610314000700040c400c21000031605c2c0c0c014441e6184040e00580100707043c0b4680030440060205080341584c104401c85050140f40d202401030306a1941c65440c04940441800f841000c0d0034216406141158002c151080201da198450303200c89a00c6d1000c0b0a075540c00d20713a0400c40f100010000c0914a41ca0002004103211042d440039008040c11604030040000d401a03240403401f150003405003582011308580d111080e9401c1c5801c40c0c000d8150312 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 856723426 1250 856722176 856722203
    0x601110102160302011a01052d130602070e011e0311030c0409110436020a050d0b1015120203041e060e281103010204090e0123090d0804 60
    0x145041c2c2240c1e0340883c0503070f44580030030181c210501c255505440007803800301c1c00d28024098640d080500c502042c40740c1c4844001d0440c582150b001100c0382c50705001c100c041203581d1010000c0d40c030030a038030034001060b41070800480e40c6000e9134101000414402000701c025410741c0c4820211145101445a041c0b08007242085c0780c1d01c03a030280808041c000d1464880e5030f01094280000e42c0e65025410503000d040f0328000c154110314a46010f100352004a41248a54162004c101c851a040d001940d0003440f46020030100446442080d110381c1c1003079040e0240a0307030341e11102c4110a8244011f00406d1400c030740100b00c0141c9a01559006000303a94810034401c94105a8501c228102e41c103035903098640391054009002004000d40032684052104000c965201100589014141d0000d154200c0c0aa0649159078250107031030103402080804c00128000a00a034000e2070300300408040c050300e140401654040ca9107c1500c01c0c0c004001078218040c04030030403580c20300e000b00101c0b20309201451 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 856724676 1250 856723426 856723447
    0xf0306210714040b01020607090308070609061b0f0807020c0105030a0609060b0304050106052418030106090c0e030105010e0610170a0207140d1d0d0f030206040b15090601110102 78
    0x700c00c00402c5042040500020444240800e407180242ca0034155407112080c004841c0e03219100780100ca030440c0c0c1481d120542c0b403822602418044070b001e00400c4c00c22045004000c104100c8990b07811050b05c0306005946025000d48440d001101d04c2e82c09078000d07907c00d48207540640e001315400343e103295000843c0c9484a2024044a81a42142c1110303e808401c1004000c000d01c2050080c01c41100d80725204403190714100c201c0301400800c640180c6010450081081501d2050031400000500030b010b06a1507820042c01824642e100100288400b000000e00c0e00701881540c1c1a1600590240090754a030000d00140400c000f458204110280d01d80c2107801003550f602d80e00614400c040540c0d2220941040c00f080c502201c0c070100182c1100f11404281c640003c580da11819140602c0074500c00c040d400200ca41103821009030440c20a5a5001c04240d404195036200c0c41c030076280da440720346403c1403c04880003004600c94001c0101004500c80350300410101d0b411070145000580380c11007164 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 856725926 1250 856724676 856724683
    0xa05010b032716030317040b060d05030d06060f0f0908060604090c090c050403060506120c01081b030903030f010f0f03060f06091e0f0c0c110111070b0c01050c0f030621 74
    0x400c0c83c1c400042c400014820180c0c02240b00703030030035050000310045051a44238040c0c10080a00190701c21604541e41808000d41401500e0911002200400506950f458080c20f0030610b09001c20000d840d465003014414010400031091301c0e150070003002150340d4002848000e01704a601510314000010703000620362014001d44400741502e542d0b29403220300d103160600c01d491001d88481d105400070042d801c5103903c00030f40500c94960034604100706441e1a03c2c120b14181005640b00c180700c10000402141e00c00c000011405a0110ba0806403070b0381c0e841452205c00380c3e690140c2004865039200030000f00340560040001c005000200051841d0380c0c040c120704035012182030203100c907401d07001c1c4200e04559100708040c94901c1c21050151401e9010000c059007010345004041c3c00304c0f116400741a91059034442c1c1c0c800c00d180201c80072140c9614482003990482c1050100e150b003880700040c50340380c415003560707507130352000481900307640350340040248110034000c2440449110440080c26200c080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 856727176 1250 856725926 856725943
    0x1501090314030405031203061810081e0601050103060501080c030915190605100504092304080c0607020a02150c0c0616050111130302010f03090803011401080a05010b0327 75
    0x140300440d9614031384401e0504000740d51034400c00200f0284100040c0d03481e00511428403440c042111542690398205a55640a00390041c0d0030902c40c1c2003080c9501c11040c040341d01c04038508401c03145107a903200011402e5952a005850000745418042080100200081d40e0010210300c15141c0c0c0d040402c01c0d101d140e01049442540c10300b03203204002001c0810b44118406050156014101100c021b0f401500310702c100d01c17601224030741d1042004221404a40000da040c5064018101c0e01c2c1854140702515801c104c0d2000210700030700d80443c0150b8000154405100d078058415002c10175a07081c05081a0040c0a00c40f403035019004000c4480e903076440c014240300e03d5400e5044824a401c0c2400c41c21588030040051030781c2c800308100541001521100c0c81125030919114110803450740084000d13024100300209030030400301c0007145010800c41e100e2401d10083e41c5036803a40d41c4010321001078031801c0c41400c2c0c800ca07080000c22403440c0302c0c90700b511000c03443d18003040d181d144a1004602e007003020b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 856728426 1250 856727176 856727213
    0xf061b0503060405180c011101060f170607030608150703091407080706031a060c03160c03020405131505090309030a0b070e0604080c0f04110a021f1415010903 70
    0xc1002407074540b40c4115500b0a141941c0000e45c1174082c603035650303034141e610341403030521070b00c0c0e810300e01003400941108015050000700b003e8595907882e40044011510518013485008070000291072521034032503101282c15400050032070083c0382c0500120103c0c0603048a080540301e0100340c0104522011503901d0501c070034020324400b45080600c50409119400c031804050410048d841c0c104e102041502c0c15601c00c0701c15a980e0780d584c410766407440c0300b11150150600d1624030030009102e0200d451030212402502e0510460b550380c05120311403441204014026005004002c1e590b41607a80650340c868910f6003141d16009104000914006a0000454512200c2d404010700c00f544142c0340120880180d483c0c60406060050458545042c5040c580c0991081c4c0340410709507803680c0101d2a50b01c14001c2e202d556410500000f921000100130640450110103e8000c0c404514418003190071440c10081066807280d10781c91003d010b06821050400988540c0031011a042c000f40e0200c00e4003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 856729676 1250 856728426 856728437
    0x7060b030f0c0a050d0b1906050a17061024020309030f06061e100e13020c1005070e0607080c0f030a080708070f052d0d020d0f0203010f030f061b 64
    0x41c0c2c4041140a9040d900f0890003a00c150b407417800024000c15485030004800514000c2c0c42c188840c0710780040c600f81c0e021541c0804c08a41c0001c0c807409402d48101a8a600c0095907000d80d158182400003c8043c820200604190000904940028501c1c890200d5880c4156440c001480c00000c2c80c10b0b032030b144250500d8201100380502460803800307075400b61009082642d95040c5803000108010380e014521000d20412401e0910503a841d084c01618110300c408003191542a0840c0d503560324440030001c4540107160101140c40b19025016840d0b080318028599480e0100c00e031344070405a086a48180805e20401c2600031030b0500038006060740c1c44013941ca0100030f280804000748040c0d8054014018403c8018200e031502d0742c071100301c0d00d0007440701c2c0039000348403040080165280c3c00d101c5010300e0002c4c04581240d03490308030b40040040401007801408070707600400006049100c01c1c42010900b140f410820030006585902c8002d00d1070048000240803081c0e80041080f491140c1c4441c40001c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 856730926 1250 856729676 856729693
    0x10b090d170f1c0e192d050c0109260a0209010b07022b03031a0d060e0c0f09271507080a020702030c0139030905030303190207060b030f 60
    0x9140c001010900b0610b01424401440d03200b40007600c07102c4280711740320b012042c5400d03032091200180741401411682181d441e8607050201300082103d548407800c9425020391810741002c0c0d8410f07490481602c0e0000c1d4103800b42a1000c00c6204030401c0101e03c4020780c0202c1802c580036075581400386008281907210203503543c0652040015110b03400384600225000400b1082078000f040054070155035050500082d01c84180014420441c1c0503170415a02c1001c0d0110141048450740040700c3d520b445408882000340b50303904000000c03148041d000d40050075013000445010300d4000681c0210f888444188188403e43e6035142000c81c1c0c80b0003440c0c0c120100d8148615103038498200e41d8000c8218608604200c1c065001036190000c000400e410040803c0c0c041c80400003c03254031515030005003100203092255600421a50007a40301680803850f41c5000103090305000c8200c0340305105a48a4000c1102992868002034005210503034089503510f40d030080941b0104110100f01c0f455000810b14103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 856732176 1250 856730926 856730947
    0x23070f03080705150c1630110c011e211e050105030a12180e190608030307030218100210060503031c0207080904181406010b090d170f 59
    0x31001c007001900903101d0208100c4658140400c0e0381021403c6200890108441d00f02000d40d40c0c000600c141003c0382c2d1001c24828516950700d090361803142038641122003042d510107251200c1c29012864041000d080384415551188101d0b0080bc1000e41000e4022402814100c540981e502d6580c40e8150754032003031030824201c1d4004840e89451101d50038081d941c180741c0803d03164510098000c20241c09021940d91407400b0320300142a1140d11854044465501c403000054000252091115020a006112840c0c100f40c0590000d942c0304a0003540756480d5000205d000798400041c8041640b40848103111580d501107404a42030069402000041c410540d41400c41e002c0c0d60006200c1d5008002d02048a4524280c2104080410f10010389030030b0141091301080c400e01a141d54406e18002034190851061010b60072642d0150030340c0416400c80d1224907690303440038061030303094040601158003580b42c2540050100c81c400d00b15550002051380040e407541d0000007440d15440c40110b58045e10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 856733426 1250 856732176 856732183
    0x150f0201050919080d09061107060b030c010e011416120e010309050c0f060d0f02030412020708060c030901091202010507020c031b01030e0a0b07080f0601030923070f03080705 77
    0x800803210281c03411040f9100b011000030300c0d0301c030f0082100c1404189504d148645911032001560810002d21213581400754070b03c1c0a0344074200c1101c1a500c0e00c55070100340d007000601c0311100001a141c280c00b5101600054641d5010401500780c08a41003081240341190300f80854001481a4041c0c1d03548000000041d03c401d00180c1d2080c100340c80c0c50b00b018040740001640800018054580e20305200c118004201d8a100d40701101c01d06908101d0400e403074952aa005610650241c43e0502c001c814400c42282c0b00c0186108010300c5038855000715510b0000c1500035500701184100004001000f540d421141486a49000c0007607550b6600b0040d1094040c03009210020703040303000d001e0490012294141202e0000c00080c109540d5a400070704074002044055180394100e150b41042d81f8140c6801021010100c40824030104242d0200392654003038040c4108090707001c0c2c009540002002c442410b005480041b01807207100b00e0f1030000c1c0050518204c0740c0a1400b80c1408c942d0382c086c13428400d15 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 856734676 1250 856733426 856733431
    0x80403150213062d02010917070c050a0e060f12060a0605102109020409021c0201030b1002030a030e01060519091d06011206110a030f1b050a0315150f020105 69
    0x140f000d885000d8000382508284111304002e0101030144c4010100001c90040c07040000c0100250700d1144010040f80001d405008214230501c0d480d00401c4e1a801403007000700b11446481c522548440c0462454500312214100c0d0b20340152402021090a01d0340700e00c0d041055401c07403d03140c0d03210000d1101e41003241030103019401701e080c40013442500170701c1c0310211900e12501040307460350341290b40c0c2107503526003012104640080c850030b00b4641c2070011074208407a00000300d000c02d10b042440c06250500c94800d52110003d90040c50501600f04003d0300034062a1b00841255541d6500c04607041e40c61000190000c004d154018004500b800401411510001030030f0f8010020000c01000c1d80c00000303801419201c00c5054821515403e21700036014000d50300c1034085031900410f00d520701da43d260307001031a91000c0c1e40301800303040990207252940c11802030314440065001c0102d500100c2c0660003460074621003503c0c04500b5582c405821030403428100295001400201500c0d456560902070240c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 856735926 1250 856734676 856734689
    0x110411220905150f0303120117010605010912110d02090a3e0703260402010e090702030d1e020417100605090a05071106190612021309080403150213 65
    0xb450924544055043c0e40704a0031034031801c10400007a4880d10107005561000300101e01ca41c02c55610351524908480c007107140040690710f4040c000a0f0781d841030101d5411151918402d491104c21500d501e0180310064080942210074211420700580340c01d042240b10395038000c40020240300031a00d08100d841c0107521a09038000c900300240b5140055589042c55040b401c181668810103450b09541035044464400a5200c401d100c030881c01c6548800a441140300b6641c0f241c11302074900030403450031800e03105040140c0c401c0c0700e200384400c125032002950001003030171130f40441c81d101d4010040c1d1340710341c10100c0100901d00c08881000c1c4200148050b00c0303c1c0c1401440102d050402044c00140700415059001d034442000c1030701755028200d5101031032119010741313499140150601001c165441c070740c000f80c01e103460000070b42903c0e12040c00300a594010002a4000c41c00826030300a400303102d5050b1a681020040000019054071107402d58401d8984050b8561410804401c00c0e04c0b200c1d400103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 856737176 1250 856735926 856735931
    0x314120408030f1b06100303110607080106030218090c250305070f0606210c060302040b040902070309050907030f1b051c1b0206100906121104112209 66
    0x902074080044161040c06803046070a640b40c0b0000b040c000c62150030303969451501d00481090281003a010500318007a280039840e05080750031200380c402ea5500040311101d0014440c2c000510041748203030002c18066165000208622040e0b8001803010b007001e40d0080705005000903180415445041c5940d10b1076000032203031119001c952006071103442001b90003400010620b00726801c01000c1d0b407141d0003401c5240803000c0e0034401d0406181081800110686011141e0301c40000c11034444d0080380c00f82c500c220071407818503240011a002a40000004900340308042002250320340f140800244030f50070079540070490207082c100820460784c1d44000b00800030505500c9190342070700308044441e0600385001d160812804481e0a400811080840707516500c0305a01d44094198000364040c0652000c07107410b24580c0e0780d944030900b250f44c0c6101c0c1682074212250500c0124032422850700984134041c0001c80d20307034849482502c050340011200c88070085546100080803c1c54003080020300b240348002c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 856738426 1250 856737176 856737179
    0x8060a0902010c0312091509032c010e0409080f0403060e07030c0e15060a03020d050a14010501080718090c03050a0b01051611060a02061b0307050316021603141204 72
    0x3c20442c0490301c0070b001c0c8940d050b11980070007410781c4a20341858103c508085020074110000e00030300760f010f209800003256111010060320300b0415040ca60700c6020042038031540000f00645544074007081c03140c2c0c081c0d601d00d003540100d080e103001004605521a50035607290b0a620300310b0700300ca641c0c0500b103001da031005609000255958051506480e0350000521482c4c0d12440070040c20844d4500a42c0c20220200d4000103081d010f80186c2050910010248810303525140000c0c11204001d11348200007030444010410795018009558200e99281750800703903100300c1c0801c1c903101c110b00d5001029440d40c801080d40025814450150400508201440700f0404000000e14500520100a1048050800581c02c101c2c004030109a60040034002e00e44032410644080c0d110340007100c59000741d40f049580402d41894510489114070f51503241c2600319110361009020510004c0ba840c1c05600c260b680c40300a06160001000c0150302c681c001e44400000a11540d0402c0d82b200c6c039017405c5030402c0c0700 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 856739676 1250 856738426 856738429
    0x70602030f0a0311070c0801020a110f07090b0112050c030f01090b1e0109120b0a200a0e0409020d060911120c060f070f150c0804020f040c020309150408060a0902 71
    0x100c4a14075101d14011400703004094446844e4403400c00002e080031400180014035100c190060084140d03d42c903559081100140581d8503028141c007040d00e50f4008030b00500c0181e5055008680f1080107241a105510f4002881c1d0100c6100b603d407c205072a012040029a514900326a40500714224050099001b07841c041040e010b545c2e120b500c403102003201004813503480344038524000c181c0d0807145084148036080110384141c0603a41c0c0301e41141020060040f108810703d500c1c5264458183c280d2602120110403200b00311940c0360640d000c2c5d151207081d405030303071000d007c07090b00341c0528000030360900d1070724090a0400519081d036004103410b1030200b030070b80e40200e000c00d03c0e54400d498190b0f07038203103c880b40102842804d000030324980c4069504428010020f10b03c1441c2041c42c0b2003000781610358103040c3c81303403072048070001d40c41042508000320390306080d04561150a01401107074100074041c000240140060300c000008020041020807034040200320981c0c0150f440082080030346410340 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 856740926 1250 856739676 856739707
    0x13060903020f0d051c1218051e1905031e1b0607020a240207030c0614060616050a060c0509030118030921020a03060c03050717070c1a0a050907060203 66
    0x81204481106000040300038a00514404003072103d001000c0003026600b607d181601c0c8894082a601e51041a0007116442004405000208284130003098400181002104401a10101103400e800203020b080082004030032100c01c102e0000190780d40380d03d52544020300c4154a811140344981c4201c3c24403601d40d0700424900b944a402507825810522802e1400c9000341603521798540076880020b0300020305a01120701d020035442540140041810480c03402203005080d20042c0d44144100309090100040c5001034680301e05c100705680160300300c0e465040c1140c4514099201041c0001424840c529081c42844030203018440e01840000107070b14010b000c001c1c0c0d4061840c84401c0310f00b140c0380c01090f903c0e42400302e0354000e25000f051612440c100c1d0141c044030040001180c01d00000c42d00b00350142224080c0f485101080031807075564808122080f9400200580c1c1110882d100b020400b0000c0c00c0a5100f451588400700f400e0401e50304161425805500c2603085401c103012801d258207400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 856742176 1250 856740926 856740943
    0x90f0609140c0412030e030604050a0201120b09270a11100206010b0702121c1d0108130303050a090b041112060906010608041401020c01140c1303060f0213060903020f0d05 75
    0x41c1140c4c4000c00302490190f078624103d40e001903043c032a040801081190015204940be4801ea80350500843c020095509607a05c050080780d00185400000302c0c0a030240d03d050782e03245a07421034083c40401c08022030b030030040c40101c20b0380c1e0400340c0340c4001c0b540d04140740310003103a804a10080040b5850a1001507480c058204000d01c50390114400100c440710400039101c6000c0700c5403501502d403d80b07610281102428079102e13030501140110b00300c51580580100349c41118540c8001000d400303141d8086005050052000003c10350340d005d2080070a54840c08948140d1044101c030341c40580c2c000400600600d0016600d0b8070f0360003041000510030010501c18110b9405040035480c6440e0352404003034014003100e94003080d40c07022031030040c1c450741500000c6c10321003809011011501d0744c4405c0103140c49201c98048404903200010400901c065002d0340c85c1407589800141410b03640000d8800100c0c107580f0040006140c00c0060007075180001c0c10701311034001180c0004840d0030998400b80c235001d19 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 856743426 1250 856742176 856742189
    0x30b030c0603012d120507170303072304260c1c050a170d1a180a02090409052103010e040f0f140d1704032304090f0609140c04 56
    0x40710071111141361014000c100302c824071002890328075240d85440c584209400d100382c8080c410100002038a0310155904070780f80c80b0900c0070358903680d206142543d0742202020681c00702c1c0d00521854102c01a0640130308003a14400c14041c0c2100008400810f01d21448034040c07210381c0107201c190100d50703912030500b90078120a251010003403005060032070030711000d80000340100d8030f02c10b030006010340450024045041400000c11040c0b414940c40320700b00650091407508244016400b00010031000650303680121000e401618080864000ca010b483e4032410480d401c0d03000c0c81c4032044c210a100d5000b4000c0f040000303814150341c9080e100309410b83d000b8001400c200c500f4002c20040c048c0302400000003903084800c15240c062200d10340c0395585155806100000c02030814140002145030a00b4011501a40e91110216110050890503d4a00d0811150050802000038060410700030b80710481d0f0f81c031900040d01c91070103a04900390b4903c070000320030542c16041044580420f10091310b094602 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 856744676 1250 856743426 856743449
    0xb0a0201060f2105070503100615080c1b07050310020301030506070305040804030308060303120115030e06090c21070303050301050109050d120e0103060b0d0911091e060a1502010b01030b030c060301 87
    0x260308015040c01741c80c0d00500d426001c3d42c0a00c0041d2405038002c5000c40e000d500b421a50080188000c4034100000c3d03c412030314600401000c904162580074410061351001d00740c400300355448001074a40108540040307642134000c0010403d00c04184006503000c0d210303040c14040d9240590310140360303100307a00006042c0b105190100301161020016114184e8444110300d6144d6116204a00c0d802042d415800000781007416030040b00360040307501802007256030001c0c030801c210881003080c0740c011071820346007100791071040d51801c5004110400007540681c54140d56541000001440040150010b0340114198000d210000710600394440d17551101d4581692404510801200600200c1d4005041c4101c0458150b05050895110f6220700384182240040030003010240300703004604840d0b0319080d8802d50403103030003240340f1007580f584004014200c682660f21160000a4001d85206d00300c0140e40d62080184035580500c034040d0a03500490060041a443c04000b54aa11050142419440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 856745926 1250 856744676 856744739
    0x506030a0612030c0507050a050a05042f040503190308071101060522060611190201030902090f16080c0406030f060504140403030b06130302011d09010b0a0201060f 72
    0x9103a120303001400128408407002221403d0080c60f4000e00740064549020304900011185000d808035400c907503015000542c810310f4413081200800310a280441010351035120103065030b68000d51040804071028130140c840d03041505040c60002e0002c0c1c0160742c0c045200701080482d0300002c10701d81c00310341440c10142c1c60084044e01405032540364019500702a104c0101220149045901c6c150003440001c1040301075034910f003c4030748041520038510385800450b0240e00718061151211420f0b8018180440d2440742a40814203102c001c43d0740e100da00c2130103800d000c0c0805241e040d450500e606440d00b40b4042c2044040440b4620942c0300c3c3c002816514042e81c101c040458104c4801001c000740104850b41c15203840356480c1b0403c0b5400c40009151181d01d41080c038203035041d154034070b505a03160701019082d41d00545e10011030b00540d1100e902015103050807980c6a6212a01030250349020b01d450b940c6d003000c082d094a1050f048596804c03003140007031040003481c0c1172500717546580e00e04031010304 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 856747176 1250 856745926 856745941
    0x2091c1523060f120f010617010b0f0603041e060509010b01020d0905040c020a0c031a0a0c0804030815031e191a180f0c10020c0108040b0a0b0303030a0902040e16050603 74
    0xa503d10f04140302d56000d905c803081442d070019840b001c100c0c2d21800895180d00e40380d400c2d06007201c2000c03040ea940142411010b8516052507030240d6401445414248041c0450403441c207188446180121007035620b41c000c1180300c050a005482030b9400038001814000901c0c64050002c2c5164003445008540d10442d043e403041c0308200d007003000741d041490a600e070350716404e0102c15030303500c0f0b03680108a546210100300c801e900c3c1e100b06141107407190342d043c4803920b8658040342e514202610751000c041c6d07001d000041580e01400070740184600e00c18000034903102c0442c1c3c03505203c106c0380a01c100d481d88518003004034000ca009062000d0b0f2911010003107980303405001072482c1e90041c40d409a0302c104501e105004034009441c0c07604284c11a0f5400000084500891340d0b188000700b030b0b50004007403602050010f00c10300d0074690032440110b00804c610385400c01091650b0030856030340400c1516512980c0941c1071501c034843d90341d5a0752015207450f40b0315420031503895805115a5028080020000e102d2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 856748426 1250 856747176 856747189
    0x303090a09150e0c0c160f090f0207050f0c030c0d0515130c0303091a04080d0f02070b070b0f10120f030c021e030f0105070e0402091c1523060f 63
    0x15100400b00f041c0c444c103104221004503002030101d200d00380b1901c05059030100c9008500b00448a6446140a01c203080c0303480400582526070b209c2d440243c0921000000030018881c5c0c0c404e490440d4000e018880021342018a482007462460707001c0c040c140520f034045000854030070920b5100b10f0040d00c05866503986038402e00745000340a003800c0038000c0c0c0401015400441c440460b154426205000d0210100c0c01507076200e2441401150750214445002d1503008d1480d51400d03c20b54010f59140990f9101900000c2d03103c000c0851342d12100704100301600c0c1000606640241d075400b02c0804144c01c0c8049076818a14540e406805103081a03180001c06100e070344240d0390b4540c00340008454080d03000c0c0150101407030350a828824003402e038001250200500c260703413084429603a00c1c0e2000c2221030602000754061000c1c0d40d0441000c403024410440522054403890780b2982c0c8503034130502d40343ca4002c11940e5a01107503010114081034041c0c0300158100694100004440105070080000300141c00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 856749676 1250 856748426 856748429
    0x513140d02013c020f2a0d02040509100e0706020d2111030f1620030c0303092404030906050d02130608150a0302060d0531110303090a0915 61
    0x1040f8100c058a104010105120464544181c00720380745c500355103c1c500d8407583d80b403880c440c2020802103190300c00f0982c40448400088068481081c548484e0045815500c044030200c0042c1e102880e0031000d03051500c1425180050880980180d80c1401802900e484519203400100711a00100d032502c0312009020007403040d00444108100f030b45014010410380c0080722030208109121000801d040b41042e164641c1000c1d82da05c00e407a280000b1010105090715010843c410320084c00184070f8090104019801030141c10010824907040424540014101900d00c035404250721051000080e0072149610a990150418684402e40c9240400090250807030555000b4034100c070000300950031202d030074081c40d25100c0c81c0034214440030a00012442030b00c0029040042001030103030a10740c5610164100c901948807244000d15410f4600e0b0120481c51000c15400302c4000c007208201004650041d5000160095800c1c044802d00141c892a59846100610340c0c8031014000d81012010b0001d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 856750926 1250 856749676 856749737
    0x72c0d03030c12020d0605040c051809150909010e0f120d230703050106110703020f120a170408070e0108060402010e12010609020d05010b19050a18060513140d0201 72
    0x107407203442d88030170403000c2d00c450321813640501d01c0c0c0207001d241c85208004a43ca0844481d51151a40f05e00d18144141070b8801040404407180b81d0214a40036034505031100c3c000d0384540008a585001d0462550410860039810000341e031120300440d0100610005492850890040020380071581c0300a00d1010b0328041c800c00da0791304940081002580e01940302070b050759142d07a68010190040e402a59880d00c8902000c1d50140360034500094915242c4c074580e5040e0301d00001c1d0f642481142d66544110710b02c00902280c00c04000c5414412010100020802059a58040c001d1940b50400707241e02c03601e001d40003030b041202c034581d9401d458031340010260200030310350001c2010703550301c0c0498802500710144684c1014109000040c2d1b094a400903108aa400f188005441d0601601300741e5955114003122800e000c1d078520384c0c2c0c2048809407600700040500da122185d503924141106800482e0f80d40081700e2048100300681117a0300c80c014080c29584d420300309100444294020310060b511290b52a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 856752176 1250 856750926 856750931
    0x8070212070b0f06010e1c02040204050d030203040e060414011401110d09090b03150c1c060306090203100c0906030e030c07032603071d0414072c0d03030c12 69
    0x8020000d100b6051031042808200241042d1207060044802003007052000394071402c80040410041c400c01540700300b00b172005000600c1c040d40c43d404030300c2c0ca20305d4503000c0d0301580002c9800c00065800344951039200d038049800301326044c00301070710524a80c4180141c01070340000c0c81a4075000e90184829490741c1461004494075005a01c40080005030790f405408032407410b00b4600150740c200058510b0845440c800c549041d540e8a181ba00c1242e0800d00c2d140c403440c83d5055100d294046a4401c03900503501804e008500003100e4018186801e44044800321742c1e17480c052058071207990104102d01901c04914000c42c0c1090032300c120502c0c50041098901840c003c030f00340042002420028408005241f502603e0081c0605a070065a800b04640c6d035404a51110364241c8680741201c00e5110004008000040b0003501491a074458001205c441c03020a102e5907601900c0458440000e4851a001c0700781a55050b210020074010300f00841c0040a141c0c0751070942100134040c1c000a0340300c400d441d00c01c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 856753426 1250 856752176 856752187
    0x403030b03100e010506010f020f07121e05030706050c1c050601111c1103030f062119050708031e0a03090f050307211b03200105240901030308070212 66
    0x11540203050503900540412311000510000030300106940b203a82411002a0007100d107805e071940e40400d201c11048549501c19030031050140242224100182c0c00740004540701d02491801d18104c40c40603207904240030041c0641044c0d40c07140303020354020305180304010600b92507410061b540c040c0610400003040c0030320350f40300d00214003041006219042541d00c078190609101d004649a11003550741208481070900025041c2c10a44908189020307140b00042c5034607a40d40545052030407000303d54046800c54400301042c49400c02012000e0034052000d18075100c1019441580c2c000c050b151f0307074420031002c00c1078580315020b41e00c14000b260700146245042c00c0785260581d100c0d403001c641140c0500c0740b50000a0782801840e0980c01d0300300c00e612002006010070808204920304442c084082013410714104004480310070404404c0b50300d00c1d0000c0f030141007141c1e4841b402080440910103002c00c46001c112190340c1e000480b41100d8241c241034206440315401203042c0171071140104e0024000180 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 856754676 1250 856753426 856753451
    0x11d040b120a0302030903100603030f1803170915030c040302010e1309082101061b380c1201051215040305030402010225090c0203040302040606050403290403030b0310 74
    0xc1078044d81c07c9040d14100500e212000f0f08481c82ca00014000818141102c0b000c1f600880d00c2d001c04d107154201c002c503019900d0b6641c0e000600c50040c00042c2d138101040218050600456100c513056018298608525001d515907041740101d00c0081c1c100010700a540741e207501d0b02620400c5a04d1401c000380010841c0341800c6106074800101c07502c0100c400182c4141e00c400408086042e9150341d40c61141e100c540c1048140310341040c00040e21035085640798400c00844415010000481d000041c031102c01c3c1d0b4450600f00004000d203e5024140100f00c0030b035a2034100e81045042d900f0444010b172400c1060040c0c185002402c524044900104a041c4414145c103e0061889039101b40d0071500340003003d400c2000030802402082c1e4003e000d059090040800503000004908220310480c1c4c106940c1e0b03000201541d11590104010a0380001c052090142c1d003400e880700f00000000c4845408142c0f00d480c1d052000041000e02050344d0342c00c0542e501d550502c600c20b8409606c490074004042d6011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 856755926 1250 856754676 856754683
    0x11191a0a0909020703080403030b0f1905030708060108030a03241e0b1603271203081303050403020f0d0b160801080f070e060102070f0308030106020c011d040b120a0302 74
    0x280c03008a10103410000e8110014001c603a80c0c1130f07150740c079100d254403540d9003074002c0d01c0111505580851a41d10540036500c17110740e04030303041210041c0034000610380003c0c1070522a640c2c000503000c0c2c1100d00180b18140c5d000007200c03900724440c900002d00c1c0345542e1111101010411440c078074407070800000900009444040c800e280d80c40706000b001140e4400001d916803003040c100c8d894101c0050401e04c04a400b40259150201c46100f961030b4208030a41881c035000c40b00c0e00b20006913140c081c240e10915501460301ea43c484080c00c10f21940a0071500c0242070b41c081d40c80700030b125440e45d903c0e2496945816001550b01907001c0d100c04e1680c2403020003c5102c070310034081080091003030340000840c10800280352040b034148034003600c5503900700b4014a69101e80104501d0551085400020740b0340c0e1580e9004000350f00400d0034940f01e5051a100900f026400102c00d0304010080822400c45082e0001c8020b20000440d0000345124510002c05d09510300e00b800500c4034000d00300000107064011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 856757176 1250 856755926 856755937
    0x1b0601080705010e010c03030e0106090606021f05040203060432031905090109031b030203060403021b03030406090b37080a020f0906032e031a0411191a 67
    0x180581d80c0181d2114011103076808001c0c2038500007484101c845020070700035400f5002c19204500049200e1791100381c141c2c1a56155030082005070b01c9580e035a0300c90100b00e01c0c02d04a40c07600c2c81c003c0c000d9007819000607907942000307840540028103203400018480c0004c0c504409054200024078280604458401d071603030856103410141064414400600c907204004455203a80141c507102c44403819070b202c0b0205c0d5a4405d88560302c402d0091000310140c0c0d020401136124070701c00d60040c038815a54980203500d280c40b45650900036801408103024042e08125400145c40c00e020b02c0c1610b0303a98550b80072004601c8240c8000d01c154103070540306003000454203046c205e0004c035103035080070b0740301c1c103501104034410500d50181a41c0300b4840141103250440003160040c068001d902d64600034110342d030940760040240e0880045000c1000c204214402400804159114007400e05605d0603440c1c03681c8441000e4080da10588035166054550744070310340c4e40f07809400507403082450401480082011070344003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 856758426 1250 856757176 856757189
    0x1b080103050f07081207110306152715030c0a0806100626091608030901030c1d120a170c0601050319030f120218010e01321b0601 57
    0x2000c542060098001404004440c080d04c0102810920501d0205171078201c0c010850758020f0400c0b8110540c0c0d000c00c415401500141106031544018400300108581e01007840c05410040c0482c0c0c00001c00d080740007607070048070034640d070b0414070300d843c000313410a60303001103180d40142c8504001c1441440020803500c10244100e41000164039440d0540f4209003034618072940e0b803000400114010500071085400c66006400ca4030510409803207072880e4902c0b0b800c0f1280950010600c4d032030075a40344c0554404072406e810820429200c00383c0380d0b403102241560550044903003441c440180c8400b00902c480064018040e4143c09506614000c681d5000d070b044400d40784a510004516460b0104d4080ba0007280c0c480340040e4080159010303600d00c9a251944014000d810003807002120719800148801013400141d007104140c1c10f80050280850a09818104881404407035100341c11100c0310901211200c4c039038540c86d684160020594824200040405151802c582c8511000011014180d070707079 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 856759676 1250 856758426 856758433
    0xf020d0b071b0f141204171002091c0c050411030604061a04090b0604050a1410081308070f08160c050102010c0905040504020a05040614150301031a0a1b08010305 71
    0xa07070700d022180c00440c1e4090302405800b00c0c2c00000075241d00d200309100c0d504d007040d0741c07065151100b8040280c2141c0c3c414209a08010400701008006218090382d94200c294114100303985200401c1d01018401ca60342c0c0d141d00210000024084600c2000d8000c00c8020014800f188420f6201c4001e50030645c0c0303060040d400c1074404a080d54482c00100104c40380248241d042c10300d441500c2014000c2d080d00316400c40c600304808180341d1503c00500019203031482480340000480c00c00d10800840a0010800f0011110184400580200000340c3c0a58201c3d010304e464900764141501000c0c11580000c1200c00e00103812034501c25162246600c0e90f015100c0003031200d54410069003130380c840109000c0000d6011000344070350315144e40700a030400e00203054194225141c6000c1000c0b20165008409900c00b0807070448100d142c40324201380700380c0c0b41c041c92600755455581c90340803a155076000946109444000a02445130950040002c044007019482c5041c00d09240a40703444401c0c08213580c2d601 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 856760926 1250 856759676 856759697
    0x3308060112110906031c1103070b0103051c0f03090201021005040c06020708010203090706111e010203220c0e0711011a0f0108060121091b140901150c0f020d0b07 71
    0x252001c3c1ea184034010240140c2040c2ea00d8070300015071240324058240034000d100740740342084007041003c1c000c0c0520800c0f1103001035041d0309041d40352052059280c806400c40a100c1802244d02011582244d4000e0070040303000945480141c0c20000c0b02490900c1c0b46181100304414441303203e049008590054003550417294551301428281d11044a034050251310116080001610071042031121090300b2054400c00102c00d4403640c12041e4001192545a40202c18040d488048803040088403510003d4074240e01c20607500c4010003001031003910741003d03c032030010740403a002d2a4820844038120008010020034020380302c111600f000c8405000c1c07104010f00300c0055018045441c001c80050319070031751004040f00c2141c031049000348c803d82c031a030300c81d0440f6001400c04030304030b24a00100202c0d10089400e0040c40c3c0401502c49950754403490346d400c0100701c5401000d143c404045014540512039a070b450418030020001d030400250000009215401400244c444850055440b962002d0100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 856762176 1250 856760926 856760929
    0x6121514010308071721060103050c091807020a021002030703230315030c19080c03120307080903130902070611040f17190507030b0703330806011211 66
    0x2440c0034080103020500410808020441c01400c44203000d0f000750500c6c1c5881c600d001040120141d107010f600c2401d0300b201c107128456030980591076100c0846844542010030702c0001851012b49208440049444200880c103094801d1003c0c00980e50081c1440304541c003007840c02036881e4400078042d000150441c20b0414076030680c5807401c1c0c8020300d1500ca9411622900f40340e2a240868014007a0306104044031300b041a119000700182e540d149046542c0700e54504140c0768241407512003010301ca034004510341c8100306c5008043e88c0d0081074514101040340ea03528149031171841280c07165624180c0001000445c594503400601900788105800c3c050799102c80210082406980544048217440b190305014010b071a1144441c24400e81c1b0894045001c80040c000c5406e941c03b0055606401003141802408200c12409401955a140030001c4200e00c40350b0902000e26119194440f403240508117820556065200000d05410750980304c0550759100f030030b4244584444102c0324082d20902d440c025 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 856763426 1250 856762176 856762211
    0x806040b1b090d0201030e150108210c03190e040f02030a0f0c051c0b09040f0201020f03040503060f060103140c0a0f08100311030717060f01090b0f011101061215 71
    0xb11100a4100108400603500650161864040544e500d00c5241120080d168940950350700070806000580b032020413511860b45043c42c41b03207000312101c104000d05407d080001081321b0140c2c0e4456606501d0b490300340c0701203440701502c0703003002d43c040d040160403103146000350700450007402049001c2004241000d80c1400344d403e4802510007244060001c5203101c2e50070340500c035501c240d4442c001903100040c00000c850110644050b40c00d400b11144013011540c040020708449a286d00003141801d140100183c0d51b0f0f88020100e440e550407000206015034000d0b004144c2082101d8111001e900c4e0104000c0e030315800404221f0001155202c140c00040d024010300c50103441400103200d03206045132070382c401c0c4c09610310b556038062060a10011707400300035143d0142d15122101c00740c0014200a4881642c41c00181c004411461500c904645959034681030720080300b00a00b016540100c26103001c41c01080d8943c850140411200b900c2420050b89030503941c080f00d040c6404008000c2c1c0e14115401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 856764676 1250 856763426 856763437
    0x8130317060102030c07080601060e092401200a0210050a1202030c0708031920030f0a0605030109110901060305070c0807020a0b040b030603070e060312130806040b1b 73
    0x8a1005220560041800e03004264815018012286001e0407036980c149410955401a84150041c10040c41810b0340044540316241c411124000b00f070605850101403002e405c0742d40154014030500b003820590141b10394035503c48400c030880340401e00c1c3d9941c161b160206420b049106070041c0b1191a081d6008000b5070b05803507013603a5000401420001080029030001c2c010340d050410034440400060700d02070085101b5100c400d0001101c4c022211020241c45041c403c50841c1c180000e1410f0511341003506890f40413448400141b00e07030329115440c400401c1c02e80c00941d055402c016158003417008100141e0344070034066803580030030303aa520b900710102d800568440d4002440c8000340750218185d0070103000e04030b000134210040d0a90382c1030185502c1e80107034400001070001004001c0103283c20b0040000030101d44203080010718100700002d40300c0401c4581e405040101141c10081c80d184052004080c3c911501103c08905203804d00d900900400c503032036000b182c034002c0c001c1900c40c2910259074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 856765926 1250 856764676 856764683
    0xe1533040c050c0a030305102706051509040c1106160e03070501020604080307050f0d061403150c07051006090b09070c0c0e07180f090b01030204050603010b030628060813 75
    0x131a2441d59400720003038030000d1702c00c5100c4a083d660100d40403000d200740290000c017400702c900b180c54600c0c80450035590103502c09882804442c1252004085000c2141e110040844d80050311111414090361044080103c07000c0d1803040d02e0800441c8070444004095a1900791203400f41c4074070400400d0b5460203180507640c0160064004100020300060141d03421050a0400e64144280c24448000681000304c1d010090b5403900c0f400c101d0091020b283c0c80288600348c001e8044201c0d80800d001d442c05000e003031502114000140c040c00d01c002844000c100c0340502c1414401650360701035590240100108062151510750045250f072800b4803001c00105030b21031400d022645c40d141c502203032000300510749014000c0c5c4103084044110140c0d4500007401003814100b61003070409206404542c04078030181d040c18030402050080e503a4041c2070700d0450300c070540a160f03266164404144041d03159070969012082c0b0b5441850080c24191103081654510381e6001d00c00d80c1d4440f00b041c8400d00f4000d018 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 856767176 1250 856765926 856765933
    0x1e1c0c18110a032a090608010b12190e0709050103060e030c060c0d020408011e0515010504030609020301020c0d0c110d08030a0504061b030603060f0e1533040c050c 72
    0x2042c4481c003a4221944881d130880d1142048080c5880081c1ea2448449602c40000d104140512182d50040901405041c004c00c103030341009408181c1400080b00031709607404440300d91002c60348181d029080781001c00e5000c0e05030b45040e540c50a200000d00f1007808100c4000e420b10101d100070726400820f0b030348100b10300402480c45031074003003200080d9804440d86c1486250208004200100240540c0344214401031582c0d034652842817160017101c1e0083d01c201481000d416401460b6a44142901c0a40e40c1101000620401c14400203009100d1702c81c001d00700e802080f201c01c031f240d40c100d00e4407444107004ac4c1c030f440a080124020000342000c6001e005260402c184045042903000342e100a92083c4a03220028003540c0440301e01c201600991110740c000780d1a92410320030003105000d00e4038580035112041c4441400d03511000d0b200c00300c401302210040042030003e40354540c0b900200780d20440300c1c4001c0c4042d008000c140c54851124a0b4040d008904117591202120f10138412500007000d404041c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 856768426 1250 856767176 856767187
    0x519020a050f07060f090f0302010b1927061707080a03120902040e0106080102090a050d05060415020f070305090319080301120c09111213021e1c0c1811 67
    0x1a1607402280d826280ca9541d41c0c0195100071507480746c81c0d8171600520640006089a140003425181480d03030395406410000c190160030030221041006442020140c0c40c180400e007440150512901134040401da42081c5000a106440761b00c5803682c0382480b81a40c84054841092580e5241d076000f005000074100501d0782581c0e1410f034401c83e901c0b40b004101103071906060340880e003580c0d0305d90401c1d415a54000340000f4140341000f0b0020090606644411405c05140c48007911000014400741a114080c5100c03c40300324594100c81068840307507010394a481c07103400e005011b50004c5000703501038421b00640303080814038801d0900132198080840f61842c1e0800c40d442038406400c00c001c40f80309880b01408204c020b414081c4240c10b90a9808079501c401040c2048020b200001d0607006890081003414400340c0c1f12046003080c8030182c0c61030f048031910b10b0400304038440140781421a810b1180da440d0b6080202000c10002100c1c0c041e01c207060b2103600e00c40e4007001c94454400c00b403064601000f4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 856769676 1250 856768426 856768447
    0xe091807060305070e0901060e04061211040e07030f080703080f0907180b0405041a01231011030c07140406060c02090405010b180906070816030b031009060519020a05 73
    0x10040d40001d04d85488a00f40100101007200e40c40c081e0415070200d55003418008517070070b050bc101030040c02d41104160350348129403a00d200b24560b103244a4000c5440b2942d03050020800c01c46040290780c0801080c0441d01203052100c402d422103042100083c0662000c00c1c0780503010031619004010b644003074000e1a162010288072201c400000380007180d1140022101960b4038400c4a100303501820031107407d03d40d800702011103240142c0001c0d035443c18407014605080c0440d90005800e400c2905c10038400352001406444440540c81d00c001d0500c8000390070394842001042c40012944882e901344c2070903801a0810059034071b0760140d0070001d4410b000700d07401342c2f502108031500107016000010301000c07080c0c0407541805000c013007181400d0b20607091240b5001e04000080d84118a03252040c40f6080c15202814007085200700e1074100360f140e0142c0e4100f6a420720080422041e9400c04101890507450400040d1400321800100742e4003901c00c110308010140212070404059984061400c1880c0c1c1e03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 856770926 1250 856769676 856769681
    0x414010501080f0a0f022a0a0c090908040f0602030702190b0d020304060209090c12101202120c120a0c05030a05030423100305160309080a0c03110601060e0918070603 73
    0x429010704e03562500c0350303551400c4561008042c1624101c008540c4400a070b144c44039070060b03c0c100450254410f5420384086401c0b1541d110980d160740401140c51000b5040c185e00c580986e800004201034034403400958960008024103041d8070070b503014003070700f84142d840d10b42c003014622491000c1d80c010480c13038119444030f500550340140310f51030050528607280c021504009040b80c081c645000c0c0020141402e8120000c0d06510141198103040c0090503c11740d400340c0c07140c40b880280500c01c020490385004105011404d50700c0c2d0050034403a07036803080726691962400e003918243c43d04d40d011700010406040c08643c01c0701e42c94000009500d082d142a0700603107240001d9035807040300368180c0c02145036031707a07481d881300340c100410354000c501420401100c00540c00c408445000b030501d4201c075100010241810741e81c65003498102141c1d80101400c05607044030102d040d00146000e00d000206950782c102562550b09d042c00e481990660703540000c1003070240c0092680f0701c50784e80000c10401c000c51080c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 856772176 1250 856770926 856770931
    0x20112090302060606070804030c12032c1c06090b060a05060712080718030807110103230603160801020c060606070c090b062a010e0a02060306090403031401030506060414010501080f 80
    0x74007d40e860305660b601c8100f184507841d04410190914514800b050551110380a010400d82c1220503003180e2081024200228189038a680503055900e04480c6000c1103401c6520126080401400281454034014120680850380700f0711810b140b910205c2e0609041058500d402d9000c2585110b221a2840a0716540c0b4010101e00410100000750941101d280400d0301c0114403948003991150301b5031070442d16102c807080606040510b0b006244240c4620b001004184040200e050f01d85130300c9550100c0d040080812800f0180400d01e02d00140300601503000340f00212100041d0388491319010b0804c50700e07105050b40501083e0681d2414801071038654006107101d100103110f0b51400e01807440c84003440d0030088816004000e070031030210001000b07018100700b1080c842e02800c42c850103a03001440502001c0c2c1694082e01e4120000740426000380e01405013012040d0380100303a5a500d240c55a43c4007000c481140c011820180414901c80c1c4040c5414140c9105840c0c07030440b03586900e01c1d464142d200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 856773426 1250 856772176 856772183
    0x6091e19020f06160302010207020103060e09060f04050f0f0c040c0203090105250204051614090303070605090709060b0a022b030b0d060509071d1501110a02040f060302011209030206060607 83
    0x100241050704d40c3c041501c00c0c03458400c0e00056103072012800013600b1190103078065009a058401042000a40401d0b41030b4002d141c0114580b1689a03820910310f803c400403800d5060307101c2e0750800144048009500c2d162900b040398140b00d10050240c0480e140d010354401e2a02061041c460458034141e841c83d00441142d80d43c803080b03203800460700040d05031a029111516040500b0300e101050b1640003214400d100440800e03075240620401c0030036a40c0c4140d0902400707403652007002c1610a5401d04c0010010300d2001c1c403d001c0b064640112914681c0301c0601000988202034104184c9094450140d100059082d40e460404078950000e5014003128468554400c1c04a41094001340c842e20850303028036180c030001c0c007455091131072602066442c6402001805074120400514042303015016040e408286807034038038098a903000c6841c00d04c5c3c406009600030f08001031206400038a6000d402182d000340c0c0c1e06496100207402c046c084400c05800070340142c202000103003945c10b00f54001c1042e04d11 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 856774676 1250 856773426 856773439
    0x301061101090606030629090a0213121407090504170705030d061e05010503090a0f0f0503030c09010f0e0906150702150712020f0a2306091e19020f 65
    0x1c590f81d9000c2182d51a1304121203103569202d44050f101c407c503240c520650700c040420024200d00e6000a2107544009084003055900000c1000c490301c2e92985040041100c084045c13900c13065890260500d908201d48461544180980040c0d1100b043c06081c2c000d0740c020b802d00b00d001329032040482913070340203070f005580e00e1204110025104549125140050660300b03a0441c0101011402607035054030f582c0700904001e000d00611403012008030381054083d500c212903040c0c6090310318040d41d00454056018206000c0031040045040160009003c2c10300c00f41d030386115582104000303a50306007140c20744c16002151640002d0990074448023a5108502c6141d0507820406c1d40d500040108104080e00b2989503c081880010810410300070398080c1b0b4540050100044401c3c0440e82c1e4414030380c1301800401c0464600c065030391140f903aa407280201e2034195981071500c01c010f2681e5601d80e503003c112a550310408121000c402240022541c3c1c5150107040c10518560200551180c2c50542d1036407022 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 856775926 1250 856774676 856774691
    0x421090b1813060515040f050418020306040b06190b0720060a030207110d15020a140412050f010c1209020a080312011d040317040c050909210a050301061101 69
    0x1620125140410309942c08081a8a0300307220600c03d1058000124041c6180107001c1400b55001c001090320565400342c500280d10118076001c44d210385242c0d403001c0c2d05402240c050001744003a0140041c4645025140096103a116041c1518007407207034410781803c1a07007402010002003111000142c20302c1d40c15040c00c03240c491103001a4a50344404a0354010a5000801c030040003580755014400c040c085800c40340341441611501400340e0201908007110360f001a1001c1802c0c0030b2041c010301040356000450310f460300c4000030b01610658180585441c0300341d40c042100d9420500400301c02541540d240d4040151000e00c002c0603140d9030700d0881e402966510b011801000c100050b02e60001e1103a402c842552400c0460078a44440b01080b8043c020140200000310782c21120300034403011f80c0c0228421903902e50520a060501640240f503102411000344840c0150001c0d91a1128040025507210000c1c80903c809051154400d4000400c8042c40100161400f800204024010700e50000c240135 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 856777176 1250 856775926 856775929
    0xe1f030b043201090b01050603100303050a09120c0608060f01120b01050f12012d0b070204090506040b180609120912010e1b010f0909020f1209060421090b18 69
    0x204207440086000f0f07952010070106003c80792140038010503054458501c4c0d424104100c0c03c0344600c80c04040c050010010311195500e02c5014042e0050940d40e082d0000060145003214070600340d80300300c20010b21180c01092841c50003421b5146881c1050710303404110b54400801078041c00c500c1c2e0f2503605201c801d010040c41c04440310700501400c0c0e1148040d000d90b604000e17590340e43c0e003210840004d9045014002c2e4162142d015140b40542d445a84000d85601440c800100940101c0d00020941c2c00307a00c1c248001c000141040c2401600f0384040b8002032902c11044a0750381c0021035a4200940c4102c107811440318080700107200c1600080d1403112607888050045083d11115032043c00e0795840551002c0b44285141e1241a070300d1f000340303080454054a05030003449d030401c0c0d004940d00d4a50008175404500b5051080f038103000b03ca51120300300380c0b50510100d61a5403003120152901030720b05440120701341c00d4101d14041103910b5110603014034100f05490265803c00205912810f01104189484c0e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 856778426 1250 856777176 856777253
    0xc080a080c0c0607120f0c17062e320d060b0706090c050613050d1403121509090616051e030f06030a05120307030204090615090e0112200a0e1f030b04 66
    0x20485001a5011198080040140310614000c400c1c1c402c01c40007098210904501101c141c10304007103c80441c0c551500780c280cd40188400c0d1b00620b12440001000e80c204001c0e80c00421300640203252411160b5540c1060000520403c0e0441d50b10001c030b681c050040d4031781500e9000c3c800d030050001004424000d0340103803941e070200c10740c103200701c5840d0200300d2034a818800703a400c0f2010a8989148900700003440d10b40e00e680203480400100390b0748080005145c403500c01d817071240941904080e5a200401c0c205804c6500a82c0d0000421010704002901c501b00010f4000307106a0220007065900c525205210140c0c00262074141010740030000054040e10601800020380540384103490309111890019049249542c400350068001070010005100500e4240d0354803500308040c1c00c0440580e030780170400401c002c0700c0d00d94801d1407080b0100d4150720760046288584856201c07812104403210003142d101c0720620000300109440c000280010f9200e41c00d0140262028a0001b401044490340514 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 856779676 1250 856778426 856778479
    0x120f090803130c0503120a030b01020c040c030605030c040e0304060c080c07090617010c020615060403120809210d0e010e010504050c030d0c080a080c0c0607120f0c1706 74
    0x403100b1803a05101444042403070800189422001403054464400030410303103000d103040e0036051540d06c000d00300c0b20707034024000c518031010020420002749000d910041e001b4a400e0045074085d10070900c1c000745a003414420094a802802c000b18242072600c5800c542a22240d402203c0000090204a04144042201c940a88134190011411904004000143c8046140d1124a60b030520040a81c0309401040b907541045010b081c03400b2541500d07002c0368407403089034001030644088a2130030181580c03041c42e50f80a003010380d041d40c2800100c05140300170b41c072201c5440311040c0e00c100400c000c515100e5120080c2d0056140011503103c034402042821a042117038243c0d0660031002d801c507010300e030500ca840029001401e091040040c5078481d52050300074a00d4800c1444041e40c00301d0700c08482001900e20900d151821540e1a1400381c00007031041799003003c82d80115042044681c1c802c1824040c101034143c4507902c440200c000d0020f5007501c5e01001d041160080002d010036003003440701441c03521 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 856780926 1250 856779676 856779691
    0x1b030501021612081603050a0e100e06240118051207050f060a0203030f06210a02090c03090d12150b030405120306010c150b330a120f090803 62
    0x303804056a007880d000c803e85a041c0001040032610401440902420301402014010300e4001030550310303201060000d24495585504a21800300d003413080810342d41021200e92a88010358100d0303143d80354410740140d60620745030320740100c000e40d84040754403071102c14824200003c00809000e82d2000821040c1a402103c00e030283c00282040c00281803d00300410302c01c0702078410034642990640003d45900009c1d0190b5580c48114000c00c1c00c5035200040141800c0526400f2100c41c1540a901650740405030401c90181210200203103100400d801075034402c80d1480c02810300402282c4040b0f900495000a440b05240e8910303202c1d0510f410103481030b015007694400c0582e0307070810b0304080b03150118032030603000d40c0d4204208200959a0110300904981e50020010710305027030040c4008081d00707031250b9a90704040509008400803038000d204242c1c1600d00c18214041c0140c0b13861000041c030441410384040390400c0400940031501e58000300c0e410406410008400921350350b280100c1d4030030765600303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 856782176 1250 856780926 856780957
    0x60a090e160602100c0e0f010309080702030303070f0f0503060d030804140d02030d0f150b03130203010c1e08040320100612120201050403140906090904082d04031b03050102 76
    0x144482da4043c40f1740701d5808650704184060b508081c000400c0550300d03d01325810151504401010080c403041941e2200da13000f01540e49a2a26032002005902e5440000c03001a50480011543c1e034045d01c12280039500140400c104228140c07010b407145040600110740b00410320240c113000d1801070015018011182e80038550302d0180885510983c0d00154058182919160030b003060b0305003103030b035482c115480f1540c407988035542c541d40f001c6140b0007080e010f5015400c0c980510391030b40c1d000c4540b00b144043c43c1d001c06403032126024100c4d4000340403100140400c41d880d500769201101c0416003845e018480d012207080900d80b481d80c400382d800581c41aa1541c104403101c104114803840e004000c008248000c001629103a21300500c80071220300e019000d064002100c5845885900441d41101c10152504503d81001e00d4209443e5001482500c200d00c2c0440b034188401e030b02c103030020980802c41941d245c02c0c1403c548403041070035450f44503502540c160100000008800303001612035a282c0f0620f1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 856783426 1250 856782176 856782193
    0x4060c031206090b0f030304360f0203040b0a150902030c040f080c01110d0c0609080c01090b010513060503060a0b0d020a03050a0606090623040f020c0703020a0806060a090e160602 79
    0x1484046088014600c0c861b820a000500c15100720400c40410000000c40a010074200d0b80009c40c1c020528a12100455044c810785a5040740c0c0d58004602491040104060b01d65a5484003405c03110f142d0b0802c01c1710745850004001026a44d0080c40d000301e8a02c40a62410b6a142401d85865900d40d100340d11681102c0041080b541e001010b48000c0304400d0054294001040002000a20803240081c115641c6200d0b0b90148003044095859501c41480200800360312410000c4015100344030b1503110b03450070711219104412034081c2100710340d8084c00611541c2c07911152100980710500010390420f80c02c80030304016030b40704800840114041e00103080115a01d0925400780c6a031a009000c2c411300b0a9001c02c02c010700d038618044001440b1700f4a601201c1d07950300140203030111a0075a00c1d4280040b803800341c2010f001c5108022240308030b5004052581e20340389141c640d1002c0b2600c551021144000308100d031210b8100003400d4509000b910b91507441c00441004101545c0c00440050b40310026 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 856784676 1250 856783426 856783429
    0x30f060103060803070f140a020102060106050f0f0a03050907081207021c02180703050105010c02100c0507170c0306092b090305032703150703020c0307120314011a04060c031206090b 80
    0x42c2040c032030300d0030050100348c506500042c2d664001840703000304100b00001d80101c02c4000c0016540804251540c0036170ba0110010000c01070b01c01030314001d20340d0149003000200b900c0001520f640d03481c10b8180307040c01d019080e001c00400fa0001c906c01521600411109001603480302d05015240c41c60600359125401c00c0070005080300c105070407607070500c4a0721003010050303520760104289080c0c00e460203103204c6489241150500d040c591020384031002da40024841c003500407580000101d0240c003107415a80e580340089070b8645100e100c404071340e40d0403881951481c0c4003520b22b044c24151400c0500e40156a681e4440c919806080d2049450340410072542c9041d86082d44100154411001080d020886082008050742c0c00303000e035428941d0001d129101a18244281c0b07000341d821200d220103107014007001501510f0461031075200a020a1b0010078408080345140ba80018201d180030308250820006841225030704a0039020311001124505980c106030040d0030107400b90200c0450914200030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 856785926 1250 856784676 856784693
    0x301081e120301090f02070c0e1b0301050f01031d060c090406060201330f03060f050f040f081e0304050717010b180c0403080c0d14040b030f060103060803070f 70
    0x38018180e800010104186806940580703043d00c10500340007580b5403540e241e5000a00c1240c400400e1400c01c20400204600200c48140c03042440080e254070503008520740d40820321090203030561101e02c00541e00303182c2d40b00f81c0c05031030094004098040d640c905501090b1521408850300c01d039103100000d80e10f803181024052100100b11a00080c4625a54000002240d0303604559214110b00304ca003803148121704009482d00241550300003c1100c03600e90401c403001d0152100803041141c10400482d191050703804959114a801500305242002140c0d0744a0140d4032046110b08184100134034000509051401140118030030001401c2080c5021418a1300e003040440010450345040c120070aa5241c004800301401444402d8640d2a5600d20f0410703e0b43c0502e40010f80015000304404116101c0010b8031460b0508a85403001d000c0d10b40c00094144d0312a0f80a0b1300000c41091000c2010108040030903a0041014100880c448e0340768840c0754a150080b090a94849507810808014007a064 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 856787176 1250 856785926 856785973
    0xb040e0a0b090601020d0c080f041d10120f08310801021314210303041b2d03120302090112050f06060711040624020f071514030108 58
    0x65601c2d5400e86003500010392501801040d0005100c001040802001014411225100041c602c0c0301d41f129100d90301c042c1c000c02d40da0104808083d0250202d001d042198549604440280191f44810034007a0307a00c801e041a1a84200c030f11040612402031f400c0301e140c00082e081211020205008005c0000d45d60b12981540d0228a031079204004a0100040941c600e0b81600c0301521110300004c1d91030b020070b507440003000070800b0920302a00c03480d2440c2c10100003580510b000780040048145184121a16904a4480ca4484041e05075482020030844407a0072812601c08515040103a500d44035511064000d18411000070390001e800c500640e0401804c01d10402008401c10280c6810301c0c940b40300c0c4001030541d80c0b18880100e07001c02040011070484040080141c400e0107020b80c0c8515484183d4a200c10f0072691500c10281e41c5004c9100240c0045120070f075074001e00885107010f600c12400952503003c0801c001b041c21040700300125490045008100160042c50750b8500c0a5281c600e40000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 856788426 1250 856787176 856787179
    0xc150f06180105060a050c0c0310021207050a1b05010e1507030f02130e090a200a090203130209060105070203030714061807031205040314010b01030b040b030a0f0305040b040e0a0b 79
    0x30758014080c58440609444d41d0082c241801c030380d01c000d0813081e03518044008450680c941303c0c50007110144071080c0c02418800200200550041e1111507090720a0b002c0c0d40e00e00000600d03445c1403440310003000400b0000c01c41c0140000139480140001e21b030301300142d90300c2250302100d4042c18400301d0b03545031040d0950a0f0f4004001c508010032030201241502b054418034524541040109440100a01811032420381c0328114a0003850021320300312801c00c5056503140304503038001c40050030000600840740301e408070b44602c0c00303120255401c20045c80d901030072485c104242408ad010060311304000502d200341c000d40c100107175210316810304ca107403500043c204110061041e141a045620003d80070080d41d0b880380358000510b140c1d2204035007034061948040d00403803107000a2526844194009444840d00fa40d0512005166409000c00d9540089000d905a070080070f0007000724804801c9845c0d070621a02e0680d2801c2d039603d00c051401d41054001e80204080241402460b01662041c4218000c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 856789676 1250 856788426 856788469
    0x20a0b010522020a050f1306090e0f0f100b1204051e0304030b09190b09061f1404151502060a050106080c0304020a0302121e0304030c05060c150f06 65
    0x3904007030000c12465440b4001119a004204021000d0140c0240c400c0640d01400558494280da42e120603040c08610410b000310300340d4480400c00742c1a619002e441a030482e5074210981c0c64800c880c80341c641c0028441c40c6c410300c6030000072030180407120050001444816107509a401c140c14414101115040c0c40c6026030341004201060400c044180d0701101d800c103c2000495484900759420880d0b00e01240b04009078043c5c10004101e19200e02c54050041c02080315000d50f41e81d010090042d13469500d2240d0000820010040101c0103905204604009880444e6011003d4005400505036402c400880c07280c580407161810780c1000955403020280c40103200c6949454005000c254018160301304429000000405548410740300000071680a0842c01040c522401402c0d2146023010b0f10100081c0800c041c0064544c00005890540341c1184007400d0071842d140400c82c1c40d40c440d03410b80c00d40703001701d000c001114101d01d20058821141480b01d030440e8942501044071560a816000c46c0140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 856790926 1250 856789676 856789699
    0x603140c0903060c07240204140a03241e27020f09090c0a03060203070e06070b01060324060f0807020d0206041218080a0318030809010c110907020a0b0105 68
    0x2a80054140e411a611040030b50740e034181030506c50030001024140a406640c1e581d090300e5a103446134003d0040756240a159500a640101085148003080c80080c2c10321000c40c006104092640c02c0341d8100c03800d50f074000508208850040300b030400180241c12121543e81c6144050400c0250380b84070291404120000300101c00d90018144036070b03011409008a89130300000b001098100001050010b004003000c120342d5403440c0000c0a54011500c1500103501d20008072642c2c18400c040e036036141c2d4010b401c00341684c01c00100b02c0040c40451407044170a080413426103110f1302d605403090050304540c0e80304404002d21035030103068400f01802d14001c40d0b0218100d91021940422440d4000f0341c01b507a01408403041040483d805c1ca0071074126640a0700c0c08400080c0304400141c035130f01491181d02c840c0d40640c101e0305601c010503450700c030280c440c400800a0b52a00d61068a640720094419000392507404c07052008100c10140465291000da0701c0048481c0c10b01042c1c242140c0180401c43c3d1071207886 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 856792176 1250 856790926 856790929
    0xb01080c032d151c050a06022a0102190c0f11040b0a17100e06070c1509050c0f04020405060d020d0b03060c0409060b0901050a0c020d020303040603140c09 68
    0x10721000b0456280031119641142481030800300800c0710403211000300a4900307000d410300079801c0030524024800c1c00390810b402000ea0400e040c201344c00340c1100c0030348000ea18645800340690b01025104420041d412506c003411000c4404c80349404004200068450040c0724204100d03a8100b10132005005841c003a00380054030404041030201d50044610b0401c4903030354045009070002a00d900d600100510001c5030400c0e0602c146004142250f0440b4042d120002c5000121800d100780412190019800521114040d07141003e01d0b900c5040c441a840a1070246501290220302c0c04580030340145542d03e041e8078147c811400d100314111030031440d2624000010b0040d200b0800d2500303545402091b81c0706c044d49103034003000c540140076041c3d510515110500788120f510600961410616141e808100b518004c4203554075100c06850740c03883c0ca1100d4400381c8030f080720818103d130302801d00383e04280140c07414006070004028a4901080010426031b6000f08041c004004010b88070007400102c01c42d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 856793426 1250 856792176 856792201
    0xd021c06140c09010c0c0b03090a2a03031119061a0f01091521090203190201090506030c0c0d03020a030c020a0b06010c05070f060804150b09010302060a0e1504090b0108 74
    0x34640c03d08003100c5917a07403071500003218031a660221840010201c01c1080030040030421025451180c074101440c52066440002484103c400012001d18441d10138000a03000c0c2c24160858202d200c112510034038500c02d44c902d1000111400c8a0603034a6069840c4443d08400529002c1c2c201103464018241000e40020101111407050081d0030001080c403204c0e4500844207a8110340c401c0802100c092001414400a014880800c03070080c800c0c004900288542d680f40b941225505035288214035160104001041d04090a210f032142402c002a1b41c1c00102002a0101c020f456240980c075802c29070b10260464030352022a0b020740d080764040c40c00050100c48050360241d024208100c2c1c82c401401c00e03030301d404066004802d00d101c81d00808903540750030516042c41241f18941310a2107251007000c5006407074910f84556000b0703506400500062a05c10007070031110929141c00003480818070b0002c0c1080c001503010401c00071000900b8413400308640200504032001b0b08041003142003241010f0207 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 856794676 1250 856793426 856793437
    0x80702040e150727090c080f15010509040e030d14060312090409050304051527031b01020c040c12061410050c1606030f05010e0112020405060d021c06140c 68
    0x40007200300c0c10140c00c90380c90702084030402142e90701805550b100c03a51040201541100280800c7c6100005400070540d807032418452420150684070201c80013005581a811070300d1910f511545408100d200044200b0240c040d030201041c01107101540c4112480600c14098909802600032458000d003140c0788400700c98454a007550700080d04103550800f00d0a50080b5007080d58007500d101e820b2085a88001d0250404080250032071800b149901040221791003040505034040d041500300d0b244502000f040880c115a06006a60300d40072a04000b40c119403000f0303199404a4100249100350844d23311841019244030b0002205001c09d071000244143c19000c202020000001201204014140041403103030004400310b00038261504000790280243e141f23190300c2c80b0315040c0001071300100d030b440c414101e41f404000c41a2020094081c480540402084940c0064101d4044001070321607800180c852800d01e014115140100c4c40c01d24141d8100780740015808942c40140411f00c00c00204665 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 856795926 1250 856794676 856794691
    0x6060501022a0d0813090b030312010608040c0b1c050c030108120a02071a09120114060d0204060b030124023903010504230a0c0e04080412080702040e15 67
    0x108030382c40000000e104401c903c00c01401d907800803895030780802036000b44c0002c0d10107820f03090018001d904103050340c1f0301440c020b03c080003480b0001008180c1c0034192072a00139001c4c106684801784c80b11898038640e402000440c00706080a00c2c10080400d9a108949c0c21000b502e1400b45107516106500b982e130b40d6020700c40e4406520000700c0e0400140200180c800802c83c0d410148060051408600c005400c941d44041c0070380940307030307283c4010b10041c8140d00400700c103241145001d4803038800b4844e4464080a04980041da41c00000caa54004c05014600910400030014051800950001500c00039800741c00d0039503022140240e181c5000d80c10311490140180041911f1030789030f091880c1c948000b4908150035510380381c01c0c0805c2c482284a44440955545031616140b4038410a90755039052280e000f8000400303002c0e00307110b0210044030294015009400315030816440340030300f038070ba2520340c87c046075000b130001a50421400c0c68000c85000b8902c040c041c004040c07030a4a40c4041c02001000007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 856797176 1250 856795926 856795993
    0x7030803090f0a06060e0f1014062106121218040f0e0604030206100f1703090907090302030c0f060d05071b1419050a0b04031202160606050102 63
    0x80c6040c0c000b00030905124002000702c40415007582401001803025014100a0b03500c41c40c002191000c143e01410700841c1e000c084102034a247c020103a40d802c0380728902c41c0d40036804011040300c00440c1c002983c2018022407840180d4103100c010024001d0502d8a12000c54110444411540e074550054a0201440c1d206c0e1464030802480010005c0c01700076490080140340401c03040346080000303803052065100360200d42094440380d094520030782403446845e450f1281d02c074092040c0151065004030081005040328103140c00714000502443d42241d10b0320011328602d8041013940340400c0b00445501c000d9541c40c070200a0400413611910400441710a00c5448202090405110351001017010f00c8444c48800070f95654500000e084d08800004100c42c891b50320802070030325610580000513a4040014400545655181c84016200400640900100b400e003102025410700013030400b00d4418001070741c00e41252500b03200720313034854221504541c00300710700c000c404d810708000c00c08030b03021038081 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 856798426 1250 856797176 856797181
    0xf0c1503070341091213080601060c1e030804030804050a05390a0e09011103040303020d050702150a02070503250b150904110d020a030809040b1207030803 68
    0x940143c02d2101d0b207103681d1a900b00410842100c24401e01454800c1544410841d0126514951030f07800284c4c0c1c40003407a041030424591050108000749004015141607038901a40c5143c82d03401c0120907800f8102103032801441c4010401b8580103a0903005043d02c9107042003c094038001c2c8600d0000300000c0a003c4040007090900404001c9804819440400c8510300000350f800320100034801d12410079045540034005038818490b0601d4400070401a20301c1c3c446501c1d01c110710144030005400c0c64865562800342302c03440e43e0240c0095101e180291005640c03210b240344031320104c91004088500310b400054800304049485100690007003d800340140e12880b1a00313109065100c0c1c4010b00f407510880010b02060941102815070010b4040d14542046940e1404440d813001c080e4080c40390f024a0440001b00040d00b0800b404048182c013821102c60440b0642c0031504205940c0c106071001440820022982d1400e4000e03d500d05400b03030703460b4810300003880e480c66842c904c07808000c020a801100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 856799676 1250 856798426 856798441
    0x150323030a0207151205041b080703080304060b0a0801110325090515221a03070e0907031d0616050702030304150201020f040b07030e010302090f010309111e030f0c1503 74
    0x12001c50325140404201b0460a00740352614a041c1c1d00e15030842801c0c41d0180005d070806010a80b1750469801c920aa45181e40e2680d8000c000c01c41110210350001740480e0125600000748202568400e00d1446030b6a40c0c28801e01c0390315480880a81040e10014500981200310ba00103800380455409944031800c6c0080b00600c00464012210040d01d050041d000184070400c4000e50003007114a0f1300e5202610801d150349400451004895500100748040f64412481c205600c0f040e42c4414503107030000c0d40707000d030160071001c40002c02c0d5607003155030101050240640c01964007070884409414510719240c1244e020a440b40118407070404030183c1c015048084c00e0007074040b0f45c0c070710010303584540d036a42e103611103828a6000000154002090b24040503000e5000b03100301c40200c24020580c09582d0242030046001e0028540c080f207003504040210482e03900c4009003102d0010305074040c102d2040c02c2c0c0040c076250040c40c4410145d26806042080c4c200d031110080c0c0e98903604507039000c1c0d0780c0b030307940e0300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 856800926 1250 856799676 856799687
    0x3030f110f0d0207090b060a051209070f030510051f050103111209030705010b0613090213150e0306060f0108040308250504051e0a18150323030a020715 67
    0xc1110320300b030040c005952140359003c00c4031025101d0309841000a440900c0a002c11405021341c58408035004005444049006101c80f96000380144c3c200d40500d6181c0c01d0006da00c0642e0b9204032021343c040c0c80c02d49141c814902815a00a1085c83c8580b04621801041040c80311144611810f140c0e40d0545282c06450795030460758021a0300091006500304201c442d40d6a50000170159490b5180040b1300e2040e04e4103100312401d80c0401018401c00b40d0518440c00025402919840344c070401954000072064030b00b04581c01d20716140e8803001001c0d22a04103050820f0001410309201e24800e0307202002582e0400d1002c3e40254052808600c0380e0349070080c0f9002a01913104882c508103450501c48030143e8004002e00507914107851045408a00c13000d1550000c040310f15080d80521000c0083c4048040010703900f081038540c007008039010b0300781140e229126076590015903201c00025140d200d2180c050902a602d852820011460b03c0500c0e40000c0d03e8004600500060101190745081c06501c5078 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 856802176 1250 856800926 856800943
    0x60102030414061e090a081605100302120a02041406030c03040f05070e0a0c171009020f0d11040e220308250e040e07080c0d0f05060408091903030f11 66
    0x100d8468031107145404c81c1c00503600030840043c4581d400603c0407035241004a04904861008100310329032a0900041004042240c15901e041641c01d1008044a41c0c0840030b5902503440940e005986074281503281d0b00c07011402035141e00400c010402d004038900c1020480b40d0180d0080b050204840f510f1901a040c001c440d800300304401a28428001c1140c16075100d81c0718502952500c58802486502017905c1c00411502030b900c0b10090362040007512002c2d002051400c07004800315140503024000a41215044e000c18504c6480c0071406000c006000c0c820f440c1c01c224004450149035008000c00300500b1084030f0024100103805000c21a1180e0004049204002c685038440c50612040c00041c07620b5841c0200600ca00e05060403440040d40100783c0300d0a980b82c100142101c400302c0810700c840c110b80008101d07000a155691603000c0b681c10300800f4010b03072054885e29902d00c00c000410003010320f01f611081050310490410070019410540d0705241200509104010100d41a403035030508004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 856803426 1250 856802176 856802197
    0x120a0504020a060309050303340810140102031902160b0c01060b0304020d060903030912032405102a0b04050601090605060316120f1d0102042105030915031e06010203041406 76
    0x20f0700300442600329504030704c40c5043d00bc050101980d0f404003170390705140640e01540542c208120200c0038902030009901c0c2c1401c0b0740100c6110031070140e003180a000b070301d60204a03000800324141c00c8007d42802090003c204149080b0b0860034030340c0000e0074462800e6002040143c0e1041c01004050103034002c03031070300c40d00001c0300305000f008044081c0c094104d40149100940039004040790704040c0f2a503007400c0e00c2e00a014418601e091001c00d403502d248104103d8280c441d0440d03e1034200c69001c10f5000d01611440f46040c0b50304062401d03a00e0504103800c00e01055003020014451030302e51005a96201341d268010b5918181424400d45c1e00d07030420901041d80343d040800c1400300c65010b03000750512000002c40307a011440c061984030300700d000d0340c000c3c41d244441030000c00c03554000055100c240c9074054401d49103884c1c51400011108040b8a14a0710800004410042017050011081000c81c03144003070003940e0701d003540000752244207a0142450440742c14818480c00d0f2900d90542c0c101065 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 856804676 1250 856803426 856803511
    0xf03050f2b0c231516051b0f011b050c1002091305090304080c04021206010e0312030717180705042d0b0916020604030c08120a0504020a060309050303 66
    0x1c1c03180061881c3c5490041180031807090440d000543c0f00e40b021014415204020541c0ca406017030b20301117407198032542c1c150b070107254481e8604220070300610107400017860f4903000040248240d2041207921100040c6070003488400d00c1621084040468019071450100702c0051303031003d0000010ba884c80710580110110342ca06020450f0b400c0000004205840544044030340d41000002008140d100b50310202d6099501780c1c0200b00036501070841020222001801c0d45c48411103841e1020b202e800840e104c40000e0907043e60540802140761155802001120300c100c2d00354180c0c070400c4c0c4d98078050b01c907103801990307504030f03416208a1500c1100001d04141e085005c0400c0312600346409460488400741c4200c2600002ca2881440f2487d00315410041e038002d4044d07980c0c0c07628143c0d00600d29200c10784401d08100488503807201d090080346c2c4141e002c01000078890910340148001c21400d5003003d410301d4035000048001c41d01c0041603c3d886002e1000310f100d13000d0408019956041a41c074100322011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 856805926 1250 856804676 856804703
    0x703062d06030c080c22020903150403030c110319090503030d0b1e0d1103160602060f0705250204020409050426090d021314010f03050f2b0c 62
    0x318903420400440b8054914410482c1c0c450003580d85410740c1350a00d59100104a000880c54908001140030120f002d10b001400c1c10820008681007240200040014080c41e804120425406104007811b0f035101c0e1901e0601c0c2c1c1d43d21503000ea92445210889204043c03580c0810300c9151056000c0b00c09008050152070b2a15040381ca0203002c2c14982d100e082c404c014404455080c1144034140a181e48401000c02c041482e040d225840c81c00c0d205052a505230043c03160114162030703001341d01780050540d40e0007001c0720b10304070716689801c1e500a04014100142041130b4090400310801300c901c80404054038031076004280c40014028440c50b88150486418902000288509003c100c1001e80f080b0042c4030003e800300b907510045100705803406500100155141d030240c01c04c40865201c800b4002000200030381c50442c110303801002607108400606601005000308002401b84550104512004128403203104da102c0c1c2c0208101441030701201503c940aa00052190300400001500b1000c1d207103060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 856807176 1250 856805926 856806011
    0xc0f0a0f0303020d0e1e0c0d020d0f11060f03010e180304061b0c0e06090c070c0b0715090b15040b0f0d031403270c030c06030613110d0b0a08070306 65
    0x3240e80311307541e80e1b0b18000e41905500d1070800314050103c0702d40c01810341800d00599039407016010200b080503905401e500c0310b0b0410720f4440000801c80c0c1c0740f220040c207840f985000b034422490480105441c5401e807200341491034403000001a00c003640c4850820021040701c00c0b104501c20040ca00c0c0103041000c2180000484a400c4040309000e0359050f189903042d569240e013001c0c2107200303510000304940a540020003d42c07100d10068041c03c0d10400d98038983c80038966680060b1007104905907204041d810074400016002c0072a000041003d032014060100700c0800151100b001c0b03065580a40c480c4544542054406ca04450f20310500d010295120709042c504035100d40304d84281d480d1415480c416110890000148503007007604001c0042c0404e554460502140c3d03000030700f0035030f0400c00510040f1110f465a01800c009140c15108181d00ca040c407111810603110070020140c0203190650b03040c0010707000801c00c0c100740c1c0d0304010080b500e401c3c1e0200c0f198440b140301e4200b0408100e40c108850701e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 856808426 1250 856807176 856807213
    0x5150405040f0c06020304150503060d02030a0b2d0109020c030c030a08070e010801080c040b220519181106040f03030e010f030b011d060712050c0f0a0f0303020d0e 72
    0x440e004480f0541c01d291600c000343d80da0702c50b5015200800030308814800040e0701c60002541d0003600030f401c18010011541c08a8508080140200d0b03000c134a980c2081191100c110b505104005003c1c10240d2141e020414104c1118041c010312211035000a22103040700400c0049601006040c02181da443c1c41242004044082c2664103070001350710482c451450b503101d0b010b040d041e10010005400c1c001046004c000c0100b00f5581c0c05074011000b00840d0850120000c3c1703009040b001c0c0f09000c140e510b45004503242e05d1484481c41040140380c104040c02482001031100d035050360084801d5034034009400020060700880d4442c00c408991102c01000300755201d024810b22060a80b5640110f1400240039402d5034032503284580001d0b00b8641d15282c0110260001d030f82c03620003811942c40e0990035110792048441228214011071400a107176114a0020002880542803c82c00b41c500703442c0750350740d10300c04501080001c0c0c209a0081116200704095a000e0a0f030a01a5011181100b070000311341c489 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 856809676 1250 856808426 856808453
    0x609120331090506101b060608010e0106120803070c0f08030a0c0e0103091e08040e0903091908030d02031f03050d020c0418020d0302030d0c05070c0b18040515040504 73
    0x900382107080000c000155004541c01010014501c103030302c0202410868002c001001c2400110600c00e5820010070030038821680035000c1c400003c0741548039020800d0940e9541e60001205192099245010461900035203800c00d00601c1c1c6101640d205003000c07002c0d1171110a02504400c800410300c60034860913071080f41d0384060350301c1e0a0300706000d08005404076506070078054030300014212904901c95220b8104c01501d44100a014107003611201c00c1c002e02c502c202c8000e01e0560000400210600d000ca00d00075108122405c00da00c402d040c0412544c032070107050f9520304403680100c0400d000c4580240e181210400f040c0248600342c0e035a08040703590341030203d64400503008048010115040c14011542c02c0609010401c1c84030402d13600340100402030040c16400c500090003004000149409880300203020341d5110768036903030a420050303000701140d88580d241a00800c14031072120111140e1140c0840c040305d00154607600c0100381c05d030002080b011180c1c0685013030100000c00c000e0041540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 856810926 1250 856809676 856809757
    0x90109080f060415090c09050a0e01020d0e160b0405010804150e0105100803040f050f0102191110050301060c0213020903010609060305010b01050f1b0c060a0c03030c0e06091203 78
    0x1503800c960f4107100001c0705d0b818030b000b4011066129040c414080c0d260801c41d04031002d40340004001805420990032600b00060007403103142c1720050b01610305010082d40b5540e441700404c00c030304030f8500312115105104901c101818800880000b0b000e220900304e040d00c00c9044d0340b0b000d010020f15480c40c58000c10301200c114848100d040804181d1443c00800e5500391a281200300080c0b80c200020822440506c1c802c0b5411881001c17464003903409607101c0d0102c0790b0711410342505a4020303c0108100036034400000020401c040c80100011035101450501e620b8040d288030a1b003c58043d98203001c1d2007241030540d01982051000161902c050303018004507030081c4001c024031100c1000450340e912490107100b5540c3c4061107580608480c08140c40c59440c11102100e646486200104411740c00c180781d5200400d00901a5505168050080c005074034118504400303500f1460b800100309000b105034690040388050100c002142d02002100d06010b103003020011011140d403080d01c41348d0301076600d08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 856812176 1250 856810926 856810943
    0x41203060b19080606130e180a0c0b0a200f010b0f0d020909030c120a030e1204090c05090405161101050f1306021c06050301060602030915090109080f0604 68
    0x34450312001c058030b8141c014040d00301040303010400200c802c00000303007040da03020108101c0300340c555590712803071802481c003e0501202403030400100c102ca1004507031a600246c00800c030f180002020311100c00301303880c90209401e4484032000c404a03401c0406030000e0300e52203203001b10010740c0304001801401c3c201c1c2c1800244810b50b09031044c07281640040c000350b0340044100b1001001403611940b0303a64086144400c41e42013520b0100003510b861003034a4210b0b031060000860700f1079140d146c0605240c044d9108020103412034400050714540c410307846240c007030555030101c540181c0d00c01c40480e044c60342c009000380041d0130403001c01c070b0900800c001180d0109036030a0031050fa40c031041c000c0610449100501c0e1004c2d83e1101d94a10713a200703034400304445e419400c0106001c04144070a401d41010614440001c0a90502003410700310b032520f40040c41594401c2c03240d02e40d82d0351880c03c8140a0310014510503107804481005881091031034124040b280260f501c41c4080100c0010030511890040450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 856813426 1250 856812176 856812179
    0x15051009140904021c08030a140702070b09010c39060c02040f1404031110062114030304060c08070503131205210412020d0207031b050904120306 64
    0x1035485444034460410032048005240219142c01d02d501980540041c081c1c400340c08120030b0a400a400700e60302126407050200030700c103407001b09100e40c680c034445101045405080002c00603550301400c0c8203441e440d17180040c520b42140d03c0307000340044040c1d100c8031003040060b042e200c41a00c1003400700300500c0d10010f0b8444031071350210440ca51040720155102d06040e08042d80900c806401c11103070301c040c001c0c0c482c1c40325611010442d94440c403542c003d664642e0504460400e1900300b50120714405216824007005108800c00500381001d00000310004494035a41e51030316060000e10120404420701000c42000244640c582000039203400e03036943ca0565607035000042d100740c0401c0d210883d0226451000c240045c072200b0702c0c3c00040b41c003400d20504000040c160b04a03c2c41c0c082c807070b10b0000c5101c0300c144020041540202c8010703401e207002521100c0d091500003560b81c500b42c40054175078240201542d040c10090b060780c0000e0500605402e040f490641014036141d0f00100b22240020700c0d1410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 856814676 1250 856813426 856813459
    0x10608010f0615050c0a0b07020607090807051804020301060e090f0610060828021b010f02072d0203150402013c111b0114091807050d1505 61
    0x1000c060700c0b105200442c1c61095068101d91541013a03c41d001e1740d2280e03443c0d082c00709002d449201c1c8240d0070f80d0300404071841d108800521005466010a2160340a1401840b980d80d5484241d50461b01e400310496141d62107000103400740c2025405016502c00903800e1200289020400d16000300e2100c00715005515481c1c0310000d0b2501c2489000002180071000c01da144101d001c40842c0030017000034440c5824008200705080ba4000901c52280b180d0f60154040034050a00400d02504041d800840c00d10030306440b20400c0d011102d91408800092180c0303801d14100007202c244501c1d401408940980ba1102c2c41ea08c410741041e40c09070701291841c1146060703400a9440c5504a0380381d052001040000d0110050007a1a4150306105000d4100300040c82c400c0c0801c10a6071a9081c42d462050740072110002514911140c002e01074080801c1040c80201d440d039000c1c600d4001001030041c003855442c403104851724010042d210403400d0802c1c5040001c1125500031000751501103400880710420b810 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 856815926 1250 856814676 856814681
    0x904021201030507060915050d09050c1f030f1806090c1d060f0904050a0618050312070908031329070b0402120a030c0f1e060608060a0b01020c1e060c010608010f 71
    0x620300c2c0000b84082180741119275503504265565485503003214071b6040e0000006809842e4013045130150703040f840300100803d525000707040044040d1201003010043d038407003c18088000c04006040380741c0b00c01240d4200561104c4407030042c042c9445400105518586500d044402582c910744103c100c40b0340850a45003c54000e40070310744c068028500898a0f56079030b0050541242c640f91006880c40c40030011030400c0c0010300e078941440c0001a070340d00d81040060080003a1b5008464076610030700c070303020701140365003810003c0c7e07003841140c00300002024480070b41c6010314840203110403102040820030800d070030b1006401a031007240d0500070700200c10f502580d900c55035070021740059615849140800d9100c12141c40740e45c024404070700001800399080c10745883da80c004488a542e80e07441042944000d0028a4001e83c81c440103001c80100040000d64a0280c001c2a51080c8144418080d04c3d031404549071441c400044c14854072036110a018600034090384c42520300950034403201920694031071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 856817176 1250 856815926 856815959
    0xd0603050d1416051612060609110d0e0c270702122208010c0c030806090705071203060315020903120c030a1d040f09110a06050f09040212010305070609 67
    0x614000c0c02d0840000f481d2040c015505810349507170069034220905822400140c2001d402c2d620000000f40c0024a4100304890b0554001d050305890300d000910804801022178145101501011619100f404405802c0101044165600403c5c25041014003460f0f140041150862140281c17195034444805a0b21100c0701c41c8c490400c404100522013500000c0102c0e81520b2901645000307815403542202400c460002c1c0140e401701700c5038040b0780200b6070b00c04145075114200f0b940c000240d0400d03040c094124081c9441c0101803400c10300d110781c40c0034480d602400003103401c0b083c0c4c51451a542c00600d00250711504106001c4e00510b4400013951a9660455000002400c0198a0071000300d008840c0c05480c02280c80020a09205a080a80d5240101100711180402c0000c0461413841d02c0541080d030307084403601a4180d000108583c58110f0b00b6148401e001c00d048a80c0c1e841200c000034020310480c0e030083d00840082c0004014080006000d100b40d4580b511101d50701901c401aa141300c0090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 856818426 1250 856817176 856817207
    0x108090714041104090207140d0504080a0201050c010e0a0c0f0f0b121306110405130506030c040e03070b0406020301080f15060d0312050a0506010f0e0f06030403140d0603050d 77
    0x321621030220305090b40300f002c8420b07038005903a05140d2684401c0050740d01c00b0100340e601800c80501c07224610f505101002154006081c401e107060300d40303101d9940324140f10340042c2c1400300c0401c04185c40d150a411103803454902034155252281c00f031a00c061400c8140c0a2210b001a20138404900c107207804001c401a1106404054144102c00080e0030650350014001d440840c040c0820380001030081c05084100b00180014a80351400c10b402e10402850000024001d00d00300000d1220070b48020802c04590070050300c0100d0005d2034025600d18501c501e8200600004490b000c120500c20f4550155042e40e000b9426108002500150716a82c0d1510748034480d130920319003020490307924121f421301c0215842401c1030f074156004c045418040358011101a080c05844404104280d81c0c05022009491a54200247c2032a60031000c10707040d00c60707514254052a00000031500b45800f481c2c50b406903142d04000507980320190f00c002005414a40310480e19841966080240503014207002d440d0401c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 856819676 1250 856818426 856818449
    0x61d1014010f1206020a0e0a23040b06070b2505030a060806010305100b0103180303050402010f0518010e040b03010204060f02071203120b01142d12010515040807120201080907 77
    0x10f150711003100035841a00c0c0742c001d01071030007605550341c0c0f1420031100040008410441e81d500c03042c4841d91028440c407410030322031407600c51529819034994013a0f68085400c0034145a295a0b02c410f0040d5604034401090200380c0c072400e40140e0513502c00004d40c4902043e400a00c80b440d81d4000007981d60b40d0a000c0104181c0102255241c6805154000d50541d4814500840d404540c003a5141c1c4450080005400003912082004150751304540941c101c040d035494000c0c9803840d81301c8011501c0d100345c0c078441d042003414100d25030b4640c0d03250403c3d4120180207008568450307441501030250700d400002c02c0e0140c0180f0f1000190f500c0038900c01c401e5242c00d1f03259119003001010b058002880c0701c070354942c144a104128204070154400242503005c0c0074403154804042d501840020151110400da07000b0ba030b0400c8404195201c0c9055241122800d0ba2001d0f0003499804260320706024540103440184101c0100207891900280a040d40c030b4002c0e00c40152580360102c00315280e21341400381d0040c0f100e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 856820926 1250 856819676 856819709
    0xc01020a080a170112060c020a110d06020d060e011a090603040f05030d0e06061e060a0c140f031908090a112808070509090604061d1014010f 62
    0x340403000030028500030340343c81851005040f44440b180b43d4217800900829441107070a90420589216015070740000703000800c2c18003500e507140c1c15040110080b85000b901400c158004102e1a501501c0190701481c3e4140b006a40b1124280d03503041003407085044d407403642c80e0001d04003200402200e44101d0058062451343d0b40c0ea8541c600b48403039150703085603244420450554400c0f941d126426240407190060505070034200104000d50b00b50484020290f03065146d40c40b000d41e503001c201c0b40b102c0d6650030b00e03451019450800b011540f150b28440141c60050340800d101401e004030042125200a468604919038400d104035014141110000e840d0f60041d0264404200540d800d4200c0c3d2400500d400f10100100b0040740720106031807817400040c3d14245040c440c00c0000d1211001400050701c0c5a00d440c13402030602507480c0c5003d407021b4032265031307424480d03a500c03490a807540d07520301e03081c08491441003400c10202c01080005031940f000003141001187d03c00300d00c0c0100c0e04680120281c0d00214 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 856822176 1250 856820926 856820933
    0x2150c0403110d0b040f030f0207060203030a0b0402070f0303060303120e0a03231b190b1503010204051216210b06030703021807020d0305070c080c010f1d0c030c01020a 74
    0x286401031140c0c1e1000f10006034000080410948a10841c440c02141a11003800e01d009041c49260500440654008003002e010081d40041030f01e81c850f0203c0d8000c600900aa000701c0c00074400d802e0007810401e91482070406054154110b982140d220b40d9468029440860542003211450084890345410510381b840c08039102d8100c0400302008000301401100c00c021100d00c031680100740d00104e0403118030030909001810300c080d1068400503441141450001c1d6210b58580c000104403400340c020103c0d902c912a242581618041c0030054010a546441c41c82015503d0709500c00216113034081260225400d110703c10010004103545421b8100c0d0b64640c1d650303000d00080200303959090701c1510300020240e034917102c100d880e014009042400600b0100c00090038080034081280c01e050a02c801c1c00407203940045101d003a150003540c2c6e0741e20380034415201405030601102c40d0313114130f0510410f0307a40040090300800e50101250211000e280a4005041d290300c94008014050b03080080c034100070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 856823426 1250 856822176 856822193
    0x601080a02153403020708030a050307140405030607120b010c05060a090204181112160513140115090f15140c1009060b033c0f010c02150c0403 63
    0x407550f880200c508000310002c054a10740d070300c00c2680d030080c00a007801c0509154042c0710020103010200702175443d00a100c00c1c003030100c2c44042c208408220646c0760682e107001d170300002d8030040d050080540c0e40a045c008801000e0031108035100d20401c0c54507841c2601d41d0300444403804110303800009016550748009501000305204501aa081900d81c0150884003518101342c5a40b5031040f4043c03103c40c1d1000d424446ca40c1c1c0f8688001d41c0f2548001c10070724080007000540781c1101c00c11282810b00040144160001e0300c003611207402c024500c4c40002c550201045800050303c0303019651020312590385c001d0381480f0402445490b4a800e64000c2c2040c045102d0300c080350041d00300001d41490725542038100ba2522034245e5030300031400c2c0d843c0441402c000311401400003662040b0003d181c40000c00a6401e80b651411034850007200211032800e0916410140d90708040c00d0042c1591790b00d01d0000a83c0b806041262402001801406800da00124000031402d02410001180c0c5003098190340e01c1500d07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 856824676 1250 856823426 856823437
    0x15020d020601061209140d09060513050904060906020c0a1704061b060b0907050414060c06070315080a051e070b1e070606061808030a0f081b07030903050601080a0215 73
    0x519522030310b810000c0741d8904000c100c1030341c019000b0006911f0f2840020702c01140741c3c0260040100400c09181914603030311140701981e03401c0303d408c9044d89032132500b68000c2c9038001c07000345030a0003c5101030f6041004616116002c2c01422016000802050b06444501c81e80c001d1401142484040b40c0e0303801030070280340d0b40081c0705840002c2e081000360300003149407a0445e060300004200181c1030098464003a003500b060703502a44e5540c245850500c1032900c540c8024918001c06540c0e02c2c2e03051811a002d80b1000c02000b4a0065a0503105c25040007603d5034060040301d907000c43e900c8281c003100080001c4030411102d0380d10303040e03003004803040381d028141400c240000703c00402881018040750407442400b0040c041d03a202d122000c02143c042c580d8498180c1d01417502c5407c1441200783e0355410070100c821200c42450316849561310030f5001c0b07510520407080e08075241e00c04545501015001000b200c1030342d005e002121b00580c2d88110782551201c050f00000d4010202218400440302c11901401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 856825926 1250 856824676 856824707
    0x3031e0402060c0102040312140a12050403181403010b030610290a05030402030f0d050d0e010204030b04110108160906080a180302013e090307150915020d02060106 72
    0x245030400783c404080c02ea0304180c02c19580544005210102079804c060b112400d80b2803c142582800d01d0003502805403407107004400707a4140c65034006400c15200d00425078182100104180c116503d0784141b40c100c002e10020039000b5880c040c0754548c80d00c0d0000f641c43c03082c01034842c000740c0c003070a01d82d0019010b00001c1c1840808041580800e21441d03c2d8809040103112940c0e60a40700e19190040500d02603010340c0d82001d03500111007410249622904603582c00c03020402c08514200c1d4511500e00a10640d1f0000d003044003c24244403c212070f469004483d03200076030310990f064543c1410030140840480c803980c080390301d2060400240b07004116055000c01d40000009140008511b24551110101c1040303005035501c00040e41c3c1d0340440b000b110480306240364030294800c5031948401c50001e054800703508000003c104141d41340d50400801c0040c00c5901201981c4114500313024001d120140540808000345522001060388006200d822455003035009082591a180050300c841c5102c0d1444c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 856827176 1250 856825926 856825939
    0x9020705030d20030a0b010e041b05090f0402040b1b1204030b04030e0306090c10050f03061903050706080411010e0f0904211d09100b030c3903031e0402 67
    0x540007000d00040c605c41c3c64000b002003000001ca9000400e00c8281000d807500c1103280c070ba2080e4416105800c2030542c09030b50700740349070740704015000030b403070b450002c413180c1c1d4040d00008020400340548800b03410400c001d1b8601c45203000048014545810581c41c0e105c445a4081c032081002c5069403400030b80290080c20300414444001e400300342451000c48104a0710b501c5145401524200b015008008040c40e1610031b00304400250320321031521000d00402c0c0300d2244450a140d0302d42c00030b070001009642c0070b000c41e901c40355503080190005004803000c0d110683c5c1100c42d040300394040c0440307200300d0a000300403c02e516542010401c4815000d40191420200881040384035801e10250340c007114155102c2c07400600a5a04205076000c52802480c00f8111503014030417285000116003059031540801c0c642c90b655094023100c418060700d4030038480745240d00c0c1c8800041406051150403035141421a070078580c4220410740ea00d11094803109050481c0d56010390030b81c124aa02c40390010f01c001d045 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 856828426 1250 856827176 856827221
    0x31b210207021302030906070f020105010501020705091b03180106090504020a2c01080307021c03022d07030309140409021507050709050c04210308010b0a11010c0f030609020705030d 80
    0x403c8201e0f04210b0b44440302da84140f00340449141c0002030400f8012040c802803100358101700000b0740703034140751059900629401002c21454510009190261407442100c82d840f8500b04201540c84042c00301110402e51902a000c81c201d503603406007034411500500090811031401d085200c80d90144c0502010000c0d07032036034030324400d08c040e503405e0f0090198800030754070340a45004001ca411801c0a440340308000c80c1850500190b000300301d400381040b111407001d0b22850070740c0c1403610f5903400b41948030300c0d0f0040304004010160400105402c0e5801940c1d4610620000c0c0140411602084406903001d6640d80c034106200200c50000c004003442801941c00c10740c3d441031120300703464050b9641140d800c00454203102700c1c0a03580f14400c00b90010511600c0400d4561006840d186060141e145040c0300060221580b501034001c0000000544008003c0200d40020042c40310703a5035503200e40001e050500000b03210304a03000384c40c802c54005019618200e80014450300500d107030204018244c4500b580d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 856829676 1250 856828426 856828459
    0x206101502011404030906110105041101050702190b070b010914041704051309020f09070c110a0b130905060102010b010e4b010c030c0201082203031b21020702 70
    0x140b25000d144203840d868441b9060a2025240c001d04c031120b078066030b1400f0100400b00f6607400c03c10020075001e080140e994815400812280440c0240e8420940305002000810b440034030f004201d078600417020000c487e62a00d068100f5a00c400090007000034100010070b0100d91801582500e44280e00e480511305035603080800c0c0100c5802c98020002d5a03200001c03019030034008102e281c112421940d41525140010f400f07040092421400350802400003c0d000064945400f00000352001165080e1100d03401c414201c1002d006005064801d0705190100340c4075401406040c84500e0161210702540c43d0340d00034040231304c2d0310307040015a044011502d04e8420100036000030343e500c0000c0c1508608001d85400070700c0040303880c0c1518100850541041d000c00e50041051428550920f4410480c3c1c8a5100a44000503203480650311042046020820142c0540c0800c14040340d20189840b01d84d00c0030f1041e0342e494040c194004206659500c002002842d9a004226042c8001c04480115071000c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 856830926 1250 856829676 856829711
    0x50d0f052803150e0910020f03011703090904080703020f0714040906180503070308070e0a23060c1b0306040803010e09070f150e0f031b120a030e10020610150201 71
    0x1409140641a910144000b261080c44810700c00126406d003549040e0440e86418401c0c4414440e03610f014410380320182c0d00c0c01e014421a082d224000301100301c4d6041c01c0c2801c9440d035004030300450162140500c9240046c20201d0283d085032169440000c12a003a5018003018090310901250559581c00b40700c10442540413816000a01a4008540b04d046c1490b0151004401a1022080c0951906038501c40d5031600540b034161000402000013040c2c0c2540720388004108130403d1a44407002080c1c401d06040b00143c207480d141e290390013889480c40340304c0505496400c203560141c034080c1c04000501402c403030b040d06541c00000400c1260100b81c0e0f40c03881c80c00b40c00540d801100ca00894014049031b0160300412500c203c610459141604151000c0040c0c0d482a80a001008035813440c01840f04a83d1600b2025103122020025641820030741c0c90f00910f0203521864081c4103110304800390315920310000e566031041010400d050780c014280544071022665040c0c0c501d045649a042c03601c18030a550 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 856832176 1250 856830926 856830929
    0x111011104050306011d011701091a0907061704020d02150408060a0b010219110406031b0305010c0807390b01090b040c0e040b0406050a03050d0f05280315 68
    0x40c045803a941042c04050034100181c0c0b04504244030480d0032101c2e0f084a605082c11954084440104411102c00d100e014040b101070241c405051956410035408082d01d0b2075106010690583e2600d0344c4465081d41c0400d11013046040c14500c50b4009030043c20041c0d18001c030580005c0c450380c0d10314241e80e0340e10915400380e0045695508550140700b803620301d6000e281000d00d401d0000d007020f6154090300c100c40048540000d0b04032202000002c80d161a90381c4414080d40d0461341106001c4d2000035040e2145401d8801100c003903103030501c00c480003881b0780e49080c01140f0b16a56642010701320120700c050781c1403070340ca289503032444003016030b0601c0412103041c29010312641c07840180d0340c50400b40004840b18007481c14007680c01e0488a44000c0d50100030782401c01c804560026400c6d103810041002010160001600700d450b0283c0801440400030364001519601e1355040010f44506004440b58001d0103020940030650303101d43d14440c5041031500d620107103249800906003d801c0200030201005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 856833426 1250 856832176 856832201
    0xc05030609030a030b0d12030c030b04060303030914060c04170c060d0b090105091306020f04120c0924050f040b1c050c100f1206031b051e030c01030b011101 69
    0x100c081074584c05001e1021450012114400003a4103503c5911240b848140b1040030199070f0300e140d000740c9000303501051f1600b8014108004454076460058004c058001d816102d28040241744206014009031081c440c0144400d0141418904514607032004208c0c6d020798082e0060400450315502c0d0078018180d640c19588012611700310132400d02600b003a06802040c040c5000104000d01c240c6401d411101d03040d404200180d40c5c40708032107a442c80c0d0140e5007004c2c16203070b0440c0c10a811b12050f803002006640072103c2c01c211405d0500020301c41c00c0c07135214002001402c0410304100500e4050014000588040e101044440984000071074282d1034442003101400781040d5001406005c00c4010849038042e901510031b070302c81c44000b420030010342c03045a080150241200704103000e9038000d0001168001c4450140c080e03c0c510345c2c2180c0015004441c010003988072025074031052661400101000503015000300e4040c074004501800107020307401d062108031019100040c000b40319184a40c4030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 856834532 1106 856833426 856833433
    0x50a0f0201061a0c1b0a03030f030b0d08180111061b0403141c02010c09090b1810030b09210d09050616031d0a0206070c05030609 57
    0x1203e410091456241c000350203266007010014040740c030518000d5800300c0d00108808420740c0520040240e126001d420300f040480c0c0203500d1920405150b00c1e02141400e1000f020540b8802c0c110381c200c40300c0c0702c0007540c0d00d50000300c000d48000d611000d10f03085a07030340311401009613181e1018220301040c01b28844a10512881038040310021039022000032008c480303c002180d190741c0e109052841440c40080164106407040c498a900030b202920340140b0f90b07080c101c0ba0401801400308940d002070104410001c070441c080203031480368011000030040d4505616150071001009461044660712a14402c400d1070404843c17a94901d01e00d940f041d803946078010000e0090541c0b2003001d4190701a1005102000c030100b02a0000400a92070a005031004603040091041c0641c1841549811154003100145009802060282d015140815485860300000303424000292008005d662 = true := by decide +kernel

theorem cover : BRFrame.Cov 856654676 856834532 := by
  have h0 := BRFrame.cov_init 856654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 856654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 856654676 ≤ n) (h2 : n < 856834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
