-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0461
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:55:54.648017+00:00
-- url     : https://prove2.me/submissions/bda59e47-7a62-4329-ba9b-e1cc704e7b67

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 82733814 ≤ n < 82913670 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 82735064 1250 82733814 82733821
    0x60311032a19030803040c030c080601080303041e0b0901020c0d03060f09091a0108010b0907030207030f1b0c0803091c050a08070c030209040c061101060617070c050313060e040501050303030f 84
    0x2d15a1503041d80003d4600c80d0008140800c10800d640c62004503800b4805915207039407103500660b142c00c0c082c424860a41c0c02231001c41c0109e664001c0c41a6604410040c0e000da84200e561036101018048402c2d5680f82d501007198445144240124071484c0441e11b02002038500300250000e180c0340a000d942c08566881d0828410024409201118400c60b100b00050300d69680e09202c5c040c0110011250240c0c0c1500b001c02c0c102130090098586869040c1c4a11500300d0004030112026040b6a841d540899a8443c04c08003060300820000e01030030090018564500300113081c82100b0301501d14140f51240d0071030308000170480c086801072541d40d01040e00365482ca09030a00c0c441c1002c00c0c1d080070b94030540040c288420082000254011079906840f0340202c564411a01401c030740e46031007150081891170038610304900c0c100685603071124060420240e000c006499013440c0d42c2040072501268556004184416a00300c030b102c0d090200c04480910085d81860040303034881c0400b8041149480252022 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 82736314 1250 82735064 82735099
    0x30c12020d0e030d090c06050f0702040b0a0b0f1e03010305060117010209040f0c020709021303020103050604150f031401020f0d020306130c0c02120105010506090607080d060311032a 80
    0x940a503402e0030b000c890b11813020a40040c010031008070b04442400d011400007405030b00078000e842c0a601503881103400c0c04480c0e001c1c80041c1111200d2294005503088010989840690140002003540394009880390348840e1240c00030040e500c65440344002c1030004100042002444506440100118002b800040c02c07150340a4014680c203158000d0070000900b080501035401510003216036404c9414003035503060020100c0c0b0620a2290441403610070607c00b55001e0703007005420403806413000961000200b02c001000042d600160081d0745a1002002030202d088401021500c0351030003149001c10f0007005007603d11404114100c425000b10004046036190200c1c2c0023080300e4144180100051014000c204140001c0c049110748a14580503a0480c8144541816190301401892801c0c1c0c1701d01c20000301d0b1b000b60340101e44a00b820000b440ca84101406030720001d41c400d09104440c064060300700740c1003c805109468860444140600b4008001c031554600003800362a03070000c5804100d0b8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 82737564 1250 82736314 82736321
    0x1b01050714070e040318031509110405040506010e01060f0801060e03031b07081002161707120305070806030316080306030f060c19050a09090b040204180e0d030c12020d 74
    0x800c0003050180b001c00080021030207040da4400c80c8079a803003255103489a0419102c88800d408003a0240126080201040d030007588001c070307150f0050030040035003100303000083e047c1c2d90225021600740c0c1146004004213030064608902510840c1003a550079895400001c1082105120311010806542072840c225142401210280e01440d06e8041d17085000170750f0a07540740300d64862108a803059003400469100c0a2082e036003035400c50000759510700000d0b1110f541c0c0c41c003082a01071110800f0004000050180f404801d100c1003940c501140c0c500d0f00c10009047d1f044001c1480d80a038004105003000343d200b2150201c4e0b26503200c07510035200e4440700007281c43c01500c01c00081c000c1c400c080600c40d114901801038030f040f60071108041c80000c8140030031036944c040e10701000c020880d480703828450001150440b00d04100042c200508140c3e5425a00c1240c22401514050035541c0341c4c054000c6034414041c01050720502d007403d00016540000c000e00141c1c0c004e82c654142c950114181414444580 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 82738814 1250 82737564 82737593
    0x81506070c030f0f02120a0b010e0c1309090506061c1202030d1404020f0105040612051e010603020d0509060621101e15050a090c0c08030a0b121b010507 67
    0x42c030a4101d10001e180400c1e000e0581130040e44503d8200a42441d040c000181000140d82e000d560800c143c4d180440040c0c11001c0036142c4800080706004081c1e1a01280c0d800c02c0003040c400d98040703400d048038142141040000780069015031071304c1208440b000000c501c00030032660320540f1013483e514100c1c0301300d080d0300070002c48180f0075041100c0f5000b042466220903006500031a020f1495050f90401074500741300320b118404c040745a1044456681c00a40d01c91130f0b015407a07011000003000e01c82c0c255150020700342c0090300840c1e408100000050002e11031180d01100040061170300f03080a038001121a00c14282250881d000c030b07281d04036808402e012180b00d00c5981d0009001600301082d0346100c0581d000c0708000e072145800d80c00303540000c1d0509010110b948c003030040b0702071600f41180d0364098a00784485500780031105444100191380c2c0310045201da2805a00001c0480c0c59030100700e4494445117200703c080e409209401c4032924bc01c1d2203100c41100900300a996084180741c001c0c084000071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 82740064 1250 82738814 82738823
    0x30c0406080a090b090c01020606040507021c21050a0e07180c050412030c1b03020d03050304020d0506010f08011a15130b070b07090611060f0c091504060807081506070c03 75
    0x1e400c3c000d0545e07000520540c40c42090b000d5035105d544200600044030021901080184d0010700899500100707801c9440d440511850400000e80031040070001d030f920000e00c150034150784ca50820610030268416021080300034000340c40420b103424580055018460b80110141e0f6540d0f1210b4401c0c0c0c0184200e0380203240e240240c1d0b18111090030003514410506009598100c1c1c4e12490a0207802820b000d40c00341d981c014540490088143c4003128590070081007203802141c040354010220380300708040c40c0281801c0708810039407410301507224252543c0e29800400c011103160140c502d0341e2400d19582280a60b898003a440c7d00c44180741c59850541030313105d900d031078030006580c005000c7c1b240115480b4030f07110f0722544a49540c418049620604020000c1910b810110205030f07a500c44c0003145805c42c03124102c40d0b05011110001512008032422021040900058100078440e080035a044c3d0000990801d03001510b0140e101003900c208804910748100c400040507820440d454a075000515080f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 82741314 1250 82740064 82740083
    0x915010507150207030905090c0f07060b121615050d0c02010204030c0e0604150305100c300e0304060912030c120c140712060b1c050d0e06030c0406080a09 68
    0x80e40c4442c2c0003548200710540000740c503090007045900b03040030034900a9032400361040c41e04034004c64480b03c03a085220b007166400c0c0c2b03564594a050b82c0f14400b00170a50080310240c00c0311380030079a08001c2000c0e56403103c00c1a000c480c1001e40303110b400100307403001e90644a0001ca11f09160b264103d00a220306d400c0140900e110110118100300d829900074441c038401d86040040000c076031240b00004082d4800100705a200e02c1d03044110808a030020341c020f1318503040100328161541500d03507807c081003032100d03c2050120f410101ea9005402020a4544c241014611342030070428000d10105040c090b11041e00c0b004010802058420405404100e400ca04c2f0171280d032500b03410051410400f40c5040e0369160f00100b8900e1340600100d651411502c0c086880c0c540303004185d50b500064155201c4a80d80002c0200d03500c2c10b04c403252503c0f040201c0c03084001e05040328042c0400761074806116440303270003844140704008034500b41400710380070740743e007802e101440c1d545440300e11000d40561440102003c21 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 82742564 1250 82741314 82741343
    0x210b0307090501081f0b09010303050d1b020d081e0402090c070b070c031205150d020f13091b05090105040e16080c0420041412060f04020109080a020915010507 70
    0x1303000c10582c4407206801c00b40c21990100c10301c2c2d90300b680c000200150380080c241004100080c0650b00900303280c4074401d80410a903154042006059061340e60b03200c0503030800c004124800703030701c01c400591020070034180c83c0c002c55114862005110004000034050b51102000c5181e504100d001c0d03506241e44040320301c0540c5410003000f0001c00c28000b084002c5100108403001c09503050103414415065014901d130300600d5141002141d02c0c518100381d8100c0586804911a43c54004110030b40481d214000f0030101c005103028410119044182d800124043d2010b004982c0e130b0440140c1103400845000c183c41103d003422504040e0001c0e50250a2801c69030009613082d40811103034881c80c0b0880381000b400d2840211781d00300c9072403107810400900f000c000074420700100380c0104541e142c015010800c028101ca0841d40f514405075031812044010504010456901c4480000901000b00143c10f002e030107980800e11588020382200700d68152003105403441d074400c0042d50300040d0071041e01d144048 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 82743814 1250 82742564 82742579
    0x204030c05010e0111060705030c090310050f01170304060302091c030f1425061104030c0305060112050a020d03030e0d050408010f020405010c0b0702010209040e0d0906210b0307090501 81
    0x15181d20460b4041807030001491419802904400c018034190806407029613512502150b4a0344001c0051401110910284501da102004002a582d240c40302c001030074180580c101d9010030b0164050922000354003298240080040295422a1103500b40540c98081e90800224800b10304149161103660806039003081c1507104240081d4007001e5165120050305e410b8a4080740d2094035050001003256082d09002c400c1014094103c50380603550000311049442c210200d01c2d4010f80c010380340c8041c266014818004c0500c1801d0040903000318103006100280c4c0e565032078506a0300d01074803400340c030341c003183c189030094101d201008a05003da44483c03850007800f40442e000ba0081c07158070761a10460361007401081c400c48055a01c140c4680304c0002c11aa5480001c481c0105507a045540900510711540c03a14040c00c0e4010490801400c0200c022001c000c1c40c50000d94801c40c100b00196150020990744200d0000718524031400114501c080303440400d140c1009607001018061500d0000291035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 82745064 1250 82743814 82743833
    0x90c0806120102090d15020f0c100c050a0f050c120a02030c010615080c070309050402031003060f0b061602180a0203010305070e0702060115020118051b2b0312020403 73
    0x2010300721810300c940300805050600700d029046006400c22041090207010a03d08803000000591110026103841e010740403030162604400c14414555019051111402c03201c2e00848656003642e2414500307020b5401c04c0100700032000c0c0d542c0f105002001510f440b04c5079060010074201d0000b14901a556206840025900d512100d4801090751800402251220285820207202d55103a541c9010a4481c80886445641700c80d608a0900c06103090004003500d4600266100d03c0950382507c0c0401d2845c2459002c6d1550140d207204802d18006259201d586d401c015a01106c1c105140d200d074440c0d40c0e02c046400d200080022600c420b24850070000c1c0004150021416248110107550305075585101d1f00c1040c0005662440142c2c001c00010302914503561040c105001843c400450f485601075065034000d40c2c180c905840c2a00100d454540c0068507042c40c49528406440c0da0301040003e0034054140c008182d4030307480d500d414800340c8051501c600d0760703802105010300d800c66442e0313620315004103003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 82746314 1250 82745064 82745071
    0xf0408030c032a180607080405010302030606130621020a09230a0b0301050f1f050a1b0c030c05010905060d020307050715060806070c0b060d0516140a17030708030a06090c08 76
    0x18101c02e81344e000070b28140201501c00c010341c8144500d00301400c2400543c040d400c0100100d4021b00c0510880b460504c000c050700c001082c1540340d40d6807440d0070285841000c615014109a030500400111007255031100010086800b202120000841c200590000e0008504030082d848070440c000424440f06400085048a02c11500c9010428228061204035424140540b07840c0749464142802d4601a80003001000c11300d1030b125010341c01105003803c211a004c481a24081c680080510030400342c94000c50140c40d003400c000c1415440c21000a49512170011404e801d580c0100c003242d2894010400c1d5070180f40d101d1540c03000c0c003a24800303900040c0298403506000d4880c81000c51841c03070060440030410358218600d00c540b556403405010300003103c848119218410a002090054141c0362180050100b50084502c1201960208140c0240325000701d14001c400301c0700300780f2440d8004100c815495102d1492901d0707540c0c000d44140107009580c4181c6015040132001d61141f40d000190521 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 82747564 1250 82746314 82746337
    0x120d0b040e0601050306310303090c08071206090c17280c05060a09081906060b040b0714100f0f1d0d0e03030d090302010c02060f0408030c032a 63
    0x2950500c084165200b1081c421a0703010b800c540041546001c0304121688403400210f46140c10040c004409680510005410780003c5d5a4201d16400c1008a03ca160b00501c0140000c0100d28240310a041220203242002041c80c0e94075000300003044450400a401010070040040c2d41600c514507180d121b544407800c04e060700a00500b1500c02002c0848142c006c25008020706844c141000e06000f12035104000540c24010141c0700002c5c4004104180111900c46003058126102e0b68588038081d41c140e03400042c4821000c1c08280451400c0c5030039640880d800c40340401c00d12180d808010b040c04103200b005503021b4200b120742d000024542c2c00c0400710003100c030410848242891050306141c1900c02e2640955001910081410b0340305140000c54070800070241ca18000d0f4900d0358408031114140c1c11409070351a400141032458060000c0c50f4452804240c2d4440e5140c6903641507014440102800000c0c3c0011004c00d21140c0c1021f40c0e1140504521a440d10070031140c200418160055480c454 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 82748814 1250 82747564 82747571
    0x1050108070503090a11040b030111130b0304051203060a0b03010b040f05040506010f0305100e090708062409040c030b04051b0103090209011526090d080403020d0e0102120d0b04 78
    0x941c018858001c80b44034454510140100c0c0600d6521400600c0c01c1004890340a41c980034102c51654081c82070002d6a4100c8510580ea041400380480260901c2d60140312008000e00c100300100e5008100c3c0420152403010306641c0399a0f03d40000c58900c1960070a614800c8040b0003c00c2c04280b0200034002c0e1200c161406040996a40410081d18411600d041c00920040f409200e5280290407480d0010b0710144079413401d5486030302d0090301010840d940c00c82c0380d118030010006d601007072000d23541208069120420015200a44003010f0020b048194019010000041d00f0301440c001000041c55001103410080e0609017016a500c0c0085550500da07840003090842c0e641d8001d00c104042d0aa000d0300400e0300360310705510f0043e108200100d09007800400c9140800c004002d80740c41c6088100c90590300070728140020824030f00450100040c00384001c060a0001082d000181014000340910f00403c0141107900101d041141d400d8450b200b140e004030300820225016049600412070945040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 82750064 1250 82748814 82748821
    0xc09041a0408180d0809090405031b010b0a0801060b0313050703020d0809040e031c0e01060510020607020106090b060d050910021b060610080105011107030f0b340e0d05060f01050108 80
    0xb0901c00d004e000512115082005007010b04001482c2c641c0503014100b0780f824201c5000b448a03060944403a12103403a556103044400e9407410a0b8040e018040b0000208503090074003043c00480e1002a01d862505903400c945042008410000f0f85c3c06540c4c081c01105d00e0040520702800395820031845603201ea814040201e41040002050310f01402c80366881c00d5510450b8015180180801c240c000060b548680f40424103840310400c40e03110100b280d00a101c0351520b094003d0844600381c011056003030074550b88180a03580d00b010340740c17000c400d804005801e450b68500f081c6012031507501c4003038050010402ca00d600c103d104080030503011000540d00d940e90344030304000c600b100c06403894020031280001440725510030700030b00c0752404801045a614075125222001ea14420a40840b40e01504d80104045201c4000000b44e03180d9039603404014954a005a4400914640318410100100168a000c080e9244d0301881010f5404c01d040e0703150360600b0340400154050034007846010400c4078011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 82751314 1250 82750064 82750069
    0x240c031a0904050c10230406080903070c1815090c02010608030f19090b03010e0a23160905130902010215010614070201140c0604030906050a020c09041a040818 70
    0x501d48140e5100700900004090141082501c4400500403410030103801452007880444050320403021050814254450789031403002002c10000800c5d0708078a420502c000f100040c031700d031702c0003040d40c41e40a0040c40500206110000038000d0400d28403007500c506000207903248041d03002c03403a9121070341e00900c50540c4844013076513284104050301808e840304010485402608058070401540ca2b40b604001180c3e443c8d600022036002a0000480b0119030300600c02c105210b44141c00140c0b0b9045003040001031254114079080f0002040005030001144c0300313144003807007809068054140101158034144030300e84004014066400c0032405841046841200300300010107a50494040b907490b6841e20b2100c00d5410807031341010008906110004104154104880d006400502104030040c4203030701d0181402054000d0340d6000e0000d001c1c040018210059001c00c018107044416034850b811a2924139010040d04800f44004090401071001c0c0410030603400000d008820340c41c005107110a80030000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 82752564 1250 82751314 82751329
    0x30d06080106120b06060a0516050d0207060f0206160306050d06050603070e01050a180906090b091509030d020c0c03120a03060e012301090504051006120c020604240c031a 75
    0x10b1309240d90f0b000000c009180c050002c0201c55594074085050210040da074039100c4000560490b62074010500400446504000c0500140b40620703107070003842e540c21001383d02c0780000382a44810303507040d4944850300c0e03020340c010200428001e003101001040358200038005000c15643d09109000b0000300080145456440a040e1840244104031b40d038a00881056450140c0a4108529480e00e6080b0081120f612920f08040c1c007580c00e003002d601c2c2402195007441252021110702aa0401c00d2125104002054400c106041840141c1d503407081044603240101e070b00342c4031f6454422020b502800b102184081e0a61201c2a18148809620303107a1024080030240603c5680024547c41c83c0110b0714148181c540c00041070604840840e01c6001103000e80d4070482e4407114031506210104481a0300583c4c501003048030b11b10803c03881400d0f44c0001d403105400381024083c44451402d8a8841ca2403050780611801c025804000000c4c4054014005d01000b140c03a248602400d144084075003410300c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 82753814 1250 82752564 82752599
    0x70b0114010912051203010b0a08060d080301051005040b0d0e07090606050a0305070c02040608060601020c01050c0703020d0804090501080106090c02030a0e1201060e0f060f010207030c12080903030d06080106 91
    0x840ba20101c5051000803450395070000030503156442001c04400c0d0343c0d04000000c50117060f4180c1240e699a5000c0000340c0111030190904d07000340410310071000488d0025050340c0c1920021260a4070b00304e5507242c11901d90003540c20100d21481c1c0000c0c02c80e4184900c4d4044c0e4801a0200c0a4594480c1d40d170a8201c01c50341140b10781c0001c55000c0010440091103588245c0c1d1189907420501444800703a00460200c808540140f55594403c009220740e40da010080d10842080910b013a510700f469038000fa0f0384404103484028000c006085010b010005c0420030740300500042c080401c030340d69540d00460301070101481000b80403407a005052100c41c0c800b004852100c01c164494082c80d41c0000300788240c0b440ea0040560342c43d50703200301c086906051041d1150103151801010781d010304044081003d05809000398506561001344108002501e8030380d03101c102c0d902001d4801800b5414180030b000d44c41407640d41d941c1030000161100c02c04400f54001d01c1500d840318020050985c03210070004641ca400c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 82755064 1250 82753814 82753817
    0x5040e0f210d0c08010e010b0405031b03010e0a1a010f0b03190204150c060e01050f0f041a07020f06011403030702040e01110703050c0f0109022d0603010803070b011401 74
    0x1001102410303030001c030000180c40c107200e010038a042c50076081c0c84200c50b00c84009a0000710b80300010001c5144130f9008601511426203600d20703091500c40007035603030369208201c07444034108482c440403255020742c440b061030f000980540741e81b081c075480c02c403906500766001c0444e000c2c6080c00104a1240554040043e20784480e0914a1610381203c03000c5801ea00c0340b650340c0500c1e000c00000c21035003598036030303e100045135031600a00340010745082425200040e078040d80903072404041126800002d61900d807c02c51541071000e0a490350700340014003280107448054558510310621001a03030004850040d26240000d99000c3d9803900540302041550146441c0e155005109200c0035150580c07000000202180000403014041545040d60381c00101068001c200086170080800c7c8040c44010100c01c0194001c00108120b980098441c1d255000b41001c07544194060b4001034400e00e440c848040030003000e184e240d40c3d507480c145a40740d019003011610710311103070000229046254013404084a05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 82756314 1250 82755064 82755073
    0x4151506030902031c050c06130201050a120e0105070915020c03070b0a020106080d0e1203030f0c090621060a0501080408030112170418051509191409030405040e0f 72
    0x6050046010b40442c110030f03641070150002e0040c11001d0840071600203030840e2100340d00d9282d2200030b503042c000c00030702c1d03515080140070980c0f0060f82d00200300d440442035824032465014941003e04020405820402403035032902c82400f41940e002004d04e01100c0524540c00114440703e10126184c0c0d0000c0b4042c0c0d0164001c81050054007a50400b03040c0252140c400015259902e480b00b5103440420042280450800d1281180c941000801081c4e881094002507146050040385256110301c000e10311001d11101080d02045596607034200c51126000301a22100c03684413019007007540f4802d54000d88601d5007000005031f103501501d001c2c0d00c140d40103130403d03041d68640309104002404820b0101d500c4051191052000c003403101c041d101a000074134030400800c6181c22400b040310009025451841e0360012a0016503a5440d1055440224608903003810302c00005020701420700b011410061120410801006410000c060b0085034070481d424070003800d044004a4545010354044078945c4c11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 82757564 1250 82756314 82756319
    0x916060e040c1b17090618010f23070809060309061504060f051c120507260a180504092103060605070609051207030810050f010210050c040306050f041515 68
    0x4c1c590400b50440060100091524452034000380076035112510241032080707085648402c950780700140d04003e06070303420a41282540210444807000790b05114900c2942e00103010410014403e099400d5810094200754072410642c8206031507080c01c440b4a402440031241b0844103140c40d00540e421a4441010001801d0030641840084110310411001c0120080402e000150100000403404c8405680c2d43e0780f9120340d403178192001c1003a0303020700309008200d00c0e8594034200310380c040b600f1030030550821051700b000241c0d9100b800c0c0a1780e44403d921504e44188a028000045000c03001c2e40303411142c07003d500e080d8681c19000c942c003602950000030320034032481001a006a21540c2200d0181c800c444218414140800035548440e800f100050300d080207000d02d070002c1420702d20203000308545808155688000017940e600c0e81c1368840203032a840c2d10210f4241644030040301c0281d50040002d000510349065490038803241503130115003000a080903000152014443c1c3d9903640a1806059030692 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 82758814 1250 82757564 82757573
    0x23007080702040e0f1b030102040302010e0f0a032a050301020313021302090306180f0c0616060216050d020d0201020f0403141c0201050601090503031204030302030916060e040c1b 79
    0xc1081c1012038010f80e8880c1a0350940c1820040581c40441000045c000c42d10080030f145501d642c3c040106000c2c0e0b006010500050b0b07084802d01403503180c1a00d44018003042d03040010407174040c650004c2d21035201c04201682e401d601a0b005600400361a0300d11030595503035030905081b44812151008148400740060005203085980c402020943c0140982403a0a0a0000342070600590b028905190b0041e0580440c050138800c8181814422024000107a440b40c0840c1c041e11503108400c0d4250408180030703040003442d60650b13046c0050103481c50140c01145c5802d0b90b5416909890030090320949202c8540b051050080315210580300011908040c41e6517241d0800444440c80c060060003112072009803e071190f07104445032070b0641c2c00441c0d213040907030000d4841d1649401141c040d80041040c0c9007026104001250072035810716006a90740c0d10706c1c10f403906002c290561300c00091a00d4500044056000440140c3d00f4000c1f02e0070048000940300c1aa200301d8443d030305045c2111301c07103004000304 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 82760064 1250 82758814 82758817
    0x305060307030605100608150a03080903070812040e0c0a0207090213030206130906080d0c0b070c0203030c0d08060d051906060b070821040302071e0306060602300708 73
    0x60809000c465829449588060a5810865800440501401003001110741c0710405580114484405007002581e11020507100c080c18040648100e50010b0111041d403003c000329401080710400ba01c07840080094200345c140d0040c0304000549080c500403c140c0003500003150101a02900146130740c500e0040140d02030b40060302e222280309000100000503880307407001051503940c1c0170410248603003408003090499a00b82c120303421583c0300e03649510400343c0041d903042e202904110f01e050142c2d0703060307402c90b02e00e416004025003600004c2120f104007c000110302e6440c4180e502c404445549440510500b4410a80c0150071a404031100800100604225020140c05a007021941540f996600420f07640020011108224005807250407804079403000c581003d101c405420709070078070381c0300207513550b419009400d01756541400000e07288a40300740e21b000035580000d060009650350f0b00c020307460340c503800d842d0030660f09201440e204d911542e2403030782000303440444060b0802e9216164100c0a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 82761314 1250 82760064 82760071
    0x303030a090305090a0f1d071e0507120305091005070e0603040204020d0207030c0c05010e0d03030f0b030303010f090b0301060605071403090d12020606030619150812040302130e031215100e0a051f0305 88
    0x180401080000033159403100071248c1600291404102401e21414183ca420134003000400400c0c900390038822075541c030400000c0304040440d40c0720344070344031340c0001402440360200003070000f407000405204040c0c000c00d86141d007a008030031029056945000540b0521b40f2420803a5010030041c0c00300c400603011354058101d00c400e000002840c0044400841d145030300a03040480350005044040109810fa80103401d00190168001e00c03100f0701d031600c003038264022100000c000c1242c0c190ba0300d04018040040d1840c0c0344006100f00c1410786503041c80204c0010704200381c001070055800098a4ec203000030124010f8014801602c0e00342001d240c1c100042c10011200b0035410b18080c4006202c0790200400b4902c0e2607009640d603640e03031552042003d07840004d01c00700c1d00203041c090200590b801c0441610001c4e00740c032030555140c5c0c0c0c910380e01b20b04001d00d00403001d621071202000d54107100e9004151304000d95054071204080e5072980708102a64401220707600903000f164500e060410311a4200640 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 82762564 1250 82761314 82761317
    0x70303020706090503090312040b07060c12020d05151e01030e0708030d0e010c1407030804080702120604030e1203070212030f03070509090c090303030a090305090a0f1d071e 76
    0x1d00d0210ba440400ba155682c205940a900200740c4804901d0240881030720a10449202031a0500d080c00320a00fa000300b040181505a075150801c06007406901c80680078001c0c4902195111040418000100010780c5c0b001a115060a0f4030212800c0190703850080c4503400ca50f0034825800080110050700000d04003405a010b01800020b1401d800c00250044000a201c046040c1c0b1002180500b190156080c02080058106c101d50f4a500d04500311060513030580b80c0040c082d61740c0d0403c014544100b00f0025041841c40c07810700b050348404140180624800d1381c0300c0000c003030040e040002e4120030008585c1d0a810400c8040c0043c03030700a4400c4a01005001560b04082d03203420000b0b0306030401c5502c180499400a80101c035444c0c61105164440854502c0900b09044c000110740d483c00010714410a89540e00c52003010701d4000c00132341c1c3c032201000780310045040e10740885002c0d6000610907001403094911003c10408848100c6610580c0c4540c4ca804c15100142d507104c2030020300610000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 82763814 1250 82762564 82762567
    0x3140408030612071d1801150612060f0b09100e060f03040c050315041b0b040303051308010204180f0207020603040b130b180d08010605040b090f0301060e0601090b0a120207030302 79
    0x1510164900c1d840301c204510401e070030305858a0310b051202500e4140013111b80381d26142c2c8042818414058030020b5980d50310385410358203228a0528028000d58000480c442c2c940000001d0403011600100609501602c032045441c000d56801c0e00d05403120007416500080c1403264243e40b19010020f50fa000f03014a6082949035603c5000ca42400070310107800b14985034001c1000140800e41c80301ea407081d8a6500760311181031070112564960300960000400700100001c03003120005ca442049409040000021075950341d4818505c4a80100601000c601c0c9051840c0a81030700d6081c426076000b5030b0042c1c5010700e190781d107585d41c81481e08000e243d800c4106150403040041801100365a01c6080803142e00540b4125070301e0580c0c90020403c03d210100800c1c400107224459100341910200e40c00c1856058a40d5409000500b80760307801d02c05c02d6015803034050001201c64100a48a000341001e0701c5912582ea111340ca003005501c105581600852002500c50882e905a503004096041c003915006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 82765064 1250 82763814 82763819
    0x201020405100c05190f0303020313020a060f02150408090409020105041e030c0e041a07120905010f1b051603110f010b040516020703080901022b0314040803061207 72
    0x42c1d03440103050a080005841c03a641a030070440c040141009812401110074603008003a41c03200e038805002d2000400b0141c011010500c006400701034045050f138001c1a80710f03076688481c401440741e052003001d400180700d610081268101c0003e001c1d0b010303e8202440034507124501080c0801380512403030890400501700310001c0d8030000c008542100340c130250b0403007c1da01d195042c008444441c2e500403003a064181000c0c4000285051004802042e013040380c50469642c5400a6408516801310f2200c224103003640c0200f000411b5218040d03101140400300914201c11100c0342c101580031500c5c6000c100d003082820341c0c881212242d01d00705d07403003403410340c0300042030810180c00c008003a80e1441c2c56a45030401c81e00d081c0b03040d0003401d50020154410004a01e100c0c038009603640d04500c000340501c4c400180d440c410381d200388410040101d40c1d400c089a240400b040e000c600c110b02c0048100028500107040c0d10900c40d0000b214020350b000b2000c9411030301c9100801c4000303100c421a695081c45000b400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 82766314 1250 82765064 82765069
    0x603041b0503070902070201021b0f0d0507090e15010b031e09100e0a0c1a0f07051204080a0b010b0301140910170102071407081905101107060f0623010201020405 71
    0x20384001d401c08903400360b01e4000d140300180c03912000d06a0980701c2650ac1c0ca80c000380307031a603454002c1d0118044440b00c26005050404604041162b0055250340d8200600c80501d4240042c481e43c100394140b44190b91a03036a07114050340d50000341c3c0c0c1182900d00d40314008a040c1410400141c1080c40b002c02d8622080c0d84170301f04021a0a501ca20021581000010009024a075180b0700c00070400900151200446420b041c00107108160b8160715110300420030302c2c10320034100303e004208000e944103550349507109c4000030755a490000007112511710203030000c00c00218690a990481d66025880e000d525070700d0042010030756008107219000f1400c1100090511406000d844040b004e00d0001607440006040003400e080c0c0b810f07803100003544880c2c0c042000f01e00000e4008060b280305903550400701c680b4038000d401c0070b44613030540107090f080c0342c01c44e0b08081e494401094214821541048965034220800d002d40e01c0d648905040114010054030580348801120803440340f05100040c902600c4000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 82767564 1250 82766314 82766323
    0x90901020a0212220e010602010507030c02030a0c1b080105060a08010207050c0f011101091b061704030302030c040b04062a0209010506030703020714010b10020a17180d060b010206010909020603041b0503 89
    0x440400c01c0304001000031980a1140503003006091403740229090b90002039524824900c100d0204850301030210b06000015000c010512002c40f0380101043d903441070b5a002c0c0c601a50002d100e2001e2100c001154001482120152940a0064204560f140342017048440c90391000074184010002c0c2c020b52024203102d5038508500c81d425180720b212000402ca0711070881d80d0019000c1c0240700f911403d00f10800407805601a6051601507503e555050103892980625071101c4c0b82614045408603415401260350b101c1c07205040715902c0b1514200c403142c0f851200e030040180d0000038901c0140318030b060410041da40300030706081c090b15200c01e95468000401d00400d41c140680d6403241c1a011600c3c2800c1c10400d00c601c9403004007000c4009855040e800c038820716014031451000103804e80070090760f0322848041c0d100140312000d000e5a60900c640600768400d001d50040c0203103000850300d81200d00c1002261600584aa410743c1c1d00c0d03540d0300d040403e1181c1c2e08000682c0c4102c0020351070b6020003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 82768814 1250 82767564 82767569
    0xe011a030709180e0f1203190213030501060602010507080f06091510031a040c120203040606050d08120f1302010305040f0f0c0e010806071d13020a0509090901020a021222 75
    0x14000307600f00e65040b030b6a0a01e1300e114205915504101b0100e101c0108600c1a070b9007040c0e4840d0724460b039107070aa503140004e208402d0b6090808604000010502a040d400402250815002400103a4860300100c500031740442d9a40b09450742c402c04282c20b400c16070080c80e0312a4000444c840520602c0d0000380c4543d449541210001c0d0300c0d4100c0e001d01009200305100180401d036401d0003554208a4054008a0105a0084242da0200014084c8801500110020800a445005520b200341805a0158419a4500c0400c22018007003034020746403190b035a220f0040761400d5000e00b40142c0c011030142001400584003040d00280c0c45011900d42e11991006074441e551007503800b03103028587c0c88800320580c4844a13542102c000c1101c0f40e500a012030340481644042402c900b80c1c1c035030018210b1312061a0020441d031002c202d050070341d80c002e030080810210403100c080341965038240391820b038814000800010f81003da205041d401364a0f0251403a0039001300d80003815503000b01e5000c0c009041b40d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 82770064 1250 82768814 82768859
    0xa1802090a05030604030206160e04061404150b030610090510020304180501030b07050705010906060803041701090206180d080309011a041b0f02010f021c060e011a030709 75
    0x2808051a14003203407034400902c0300742c020f03100a01d05510043c2d12420014021040c8641054081c1d5405108001d51403940030020b00c100605c0e03031288000001d1f8040c4140311805035107011100307101d50950a4120302240d4034200300b1861541c80405000100c074404545074188210b000c0042034555550390b030354001e6429640203580f2035280c10210310400c1000005ca0802624000c014800704581501d00796004506040c40d560700c134403a18007e801410440b0019201c140b07044030204800e14044018070445200b02c407082c003c090244040e070300302c4a24a000a502907002c100141c6000e403c020b4040c244d1340028850400208940c13104113041c1d02c21200c5039410396440034108295110300b905005103d40548040107070600c4408001128284120100c00784005489901c032054400d402030751030a51030240564075a080710b819034102e005400e501c40b003000e0400d000450281490101507048802104e0041204007111850b18265803000d890308040010ba800f0204004d041450383d02c1441090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 82771314 1250 82770064 82770067
    0x7020d0b100b030906011406120a0b10030c08130809060313021c030e01030518011401080f0d050a12021306050d0b150f0c0a02090705031e01031a04020a1802 69
    0x310418a0741240325800c40e80e1400d50500a10502c280d0008500d419585a10514082403000400003000c6002c0e9065011000644404101d0f0300c44803600f0892021006941c04055600040d005a081d540b800501000191203940014544182a44a034903028090018103207450348a4010801d070303a00c103c17200446030308043c485008504214410b102c072400e80b030050b070100360030542d8000c000c14402841d0a04064039030010514a0410b101889905034161008200d604403000795000c951400344591100d500440c41161401c800c0816101ca9032295952090300d01221102e081e602c001d100041c01e034005600780108400d005085510300c01409035a103859803241141400391003504d41210a4038041d0002c00a9100e1901d00c007000d88101100311410f0f03580368207480505034030780b07030f2504806035100d8554410b001215030058011400707030410141c10703210b10030661008507521000388402031600c0c9039002d03420344043c0620151600148014200c1524a43d1029000c48002c0b5181c81e04014030360 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 82772564 1250 82771314 82771321
    0xd0b180709170304030209040308041401020c0c030f150f070201090b184c06031b08010b150307050c010903020106081911100c080d06090b0f130c020307020d0b 70
    0xb461905030302100c0380c41c40203518150866003c00e0303444070058001420f10407944081000c020340c8441d003000d0a41107100071502c5a00c910304c429960a4284c10390b50090040d4140440c4210011071014000100c529240c030107911900100740d030004008040d030f070441d541c4040810000f103c1e60100e034010b014001b11f021410a07100101814540f026070005815007903500001e030303d07640e107a0800c1c0c8100481d8003411004003030100f504660750400320880350307a149800d6022041100e80c034103480a800c07101240714a031070749030400d490884504a000303a070312a0706104200354041d1604001c1d03034440d01519008c1d04210602c1c45c041d0960389500012000760351a94000c1c41507000400c0110070700401041d00c84196201901d03031200b032445111406000e02200501c00aa0a00448404403282e600013401c564444c20040c1410050003e40a42d20390b8038181040c03900c0d1480d010761403014541009003003202414070707405810010810b101000003540010b109540c0541c2c3c5821484c80014061200c01c60300c0e18 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 82773814 1250 82772564 82772579
    0xc150c080f0708090d120b090f0a0506091014010c020301050f0117010b090a1a0603190612051507090b0408100c0305090d0509060706021b010b150d0b180709 69
    0x9100404042c01c0041001c10080d49100000c1c0808070400d490030000140000f00310203501402180c0d0280790040c22100c240b000d0350540121035403107241da84804021a1302c800d010002440c0f004c0c1c0e40301a14100c0b59034184041c107050041c0c1c1e00b0544050402c0784001440340d01203802c2d5402100e0701c119031980c42004104070b42d0b6000d540224102038a000300a4114804000340881201401031840b944e50742916030030030b480d41040754421200c02006d240c0c40c1d18041c5800100d12582c402c0004c1072700d013000c5000840c083d9100860010550000282014010040c100304001100030445020445640710010b90410804010700181c059030018040c0c05020820500541c1c5500c40b11101705840e01d41000b16110020940d070081c000d1510f0700c1d035a58803041c00090b92502480c080603181c01d02c002540c448441c12941000c4901d01900021311101c1c3c2c01c0010420007540c02a24008404400c1007c5050b040a0b6400015406001451582015240001946a0f0004503010780111310800307400e01a11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 82775064 1250 82773814 82773841
    0x302010f050a1503030806131401060f03050c0304020d050a14010923030301050915091501110a02010e0f03010204030623010e0705040902030c0c1204090b120304060c150c08 76
    0x1903402907080c0b0041082407006200d001144c40080d00b006100c0c00030400c0790340c44100c003071062103242c0340034000c2d10f103d0b0101003403c0c00203118040105005100c6401d50380d00a016040c8201c02d42d0013214195030b180e401384910b80180500488403030203640c01c40d40005808540b4110600203040000407080690700d020040d101c10346600c0520204400b0f44400c201c0303c00811241540c00554036003800f80c0f61014038200c1910500a01540001d0790402c0064685a4a50007080d8600136a41c2000040d100c0781d03459218950458041d0008400100c3c800c00c904042e0042c82084070041c000511702a92925550b045074000165007101d403c0060400f0750083c07003901e0b002c0c050146503040c00c2d02414001c4026215200b18440c4410598000c00002d041405501c16548010120b5081d41c4600841d6a1940e00c144e0003801005201d91504940341110b04000e80340a600c0a207410040d07180504025082d1000c1040d01c0c41103405c3c410140d4030540001c2203001c1e4068040c2c1640700c50b0b0345400c002d240946803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 82776314 1250 82775064 82775071
    0xf030307030f1401060f0c0605040f0c0902090306010501030e071e0e0108060705030f070c02060a03060e070513090f09080d020702040b010807120e07050a0b09030105160206010911160302010f05 85
    0x64103040e00030400036981043c00e811034202c3c0c14010102002c1c0070080e502094510809820b071840e0074100700500c409407018550152250000207a9180c403040c0c0300d000ca0141900040d059403007580140010750103980705002c504880000c80e10754030340c1c0f441c2d40104c60600c9070449a1076040444104041201c01024601604810029092034500100000d0460000425007040400c41001154003c1c1c0124070000b00c5a8020700f40c641d0311900480c018029041d5031144001000d00440080d50041c41342c1b0a4600c1120240c4003106620f14040c2d1302030150460f0f0b08213070000caa42e400600c0000c0c0070341e4018042400352481c0580c91b442c90f80104411140310340001c5051000700010459481c0d0702041030030008200c0000080e100421480907807030125a50081600401112408140c140b82da1016160a0004500034010307640d0380700d8580500011120410056880f44005105e0610303181c10004513420300243d2542001290f210311902c08001244c01d0340541d6407440c1003c1513170a1030203402d90 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 82777564 1250 82776314 82776341
    0x30c21020106080111070f0609020a0f09021b1b090a0f05011508010503030a05030f0711030a021015030c0e0705070606031101030b0405010812090d050303040b011e08030f09040e0f03030703 83
    0x1b070005507110740c07002c02208207009100c0b51346e80d0845011565103040e660043e0140098030750b400c03030302d821a09000b07620881030340c40141c0e202c2400400300c180002d2a504074080081d00c4100201401c0c0611401c201c001e0414006142c55811401d8464890701c0366034000c100321f40301c51405000301503025203000b8060304407e010303070000c0024140d41c0e0707005000c69400c00c02c503074090007140e03075082301c11035080405194107142400001040c02440d940010048480c565611081021b203c07221400306160440344001408841c0b9001f003004000130070f89000764084d207107091492420a890352048104ca80079042150f01c210004980358603075902d4461011070040a41c1d04010b01d5040203209542ea40110125001145002401d160030b0b480e0198907032001a445400c0300d0300e030301f401d18003400c04020901070f84148100c600b41c40c00100144501100440d06540003171840d180d120264504e455010340807103500035440b51403581c4965800c10100703494104102c00707103881c1d041c0310600400f40d0b0801d40a00e107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 82778814 1250 82777564 82777567
    0x1b0604110a06170402060703020c0a03080405040b06070b0a1503050d031505010f0c0809030304120c030311060408090d080f0d0606020601050618041d0a030302040608060108090604030c21020106080111 88
    0x589011420303c0f5240c029404441c0c882e02c44005113005c030f240c0000070002940020300c2c00300010030408041e0160046c2c4008440c2408100d483c10f041c010340f40114880034214092090201e080303403040740e20a41c0000702e40741c44000f51075125140c2d41d00d0240e1410140000a50b160f5800c0c40c204001203c4501521091801e440f8031600c001c0001c0080b003e041c2e02030024100080e401166a134100201c800600d1141c40c60700c0100e00714100001c00240c03a200c00d8010850455220000940c046150380c45640c1c428075440c2800c40c2c403000d000760140c02440c215030703000c01001402c0e0b194456034003800d40139041500c0401c1890030640c3c001d04020069020500401041c80f2042040c20b62910180040c0d1041e9030000b605010100f02480702400b45400522030700610910740c2c140342d85900248244c1e02c0c00e0300c0e0311106441c8c500046a90003011207a00d60b031500100c01040000e403003240a08410b5000350008807501d4509072845410000f0441c030840540c4d941c00701000103040030300401031400d0f4a903500c00e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 82780064 1250 82778814 82778837
    0x60c0306100804030f120f0c0c060609060b040e09010b060c0606010e0105092809021902010c05190305070c080406021506040203040305030c1b010c050406030b0d171b0604110a06 78
    0x140004108005c1e103414800720b90039510303002d45554802c01043c0244c1c8402d001042c9010380140c180448454241e540c035080400203c0ca02d409401060112805400602c2c505890042400101000501040d040e95255460304896640c1c08001d0301c1c0000f642c001a1445003003100001d8010321009200c507050090030f01141d42c995450209400900c0c8508140d052001274207110065410f0068004000041c07001c2070080f4100c4a500052440304011f1b0020046210b07001015101c40c041c2200c0101007544c4121110303600c0340700b40c003c1e0380c100c1c542e811320883e05041665855020340060700302d500140d0007440104180410313109542e4128030f0a4808510f03500307060314020042e200091000c0300100000846040540d080116084000c8106000704500c4004c458000e00ba64001d104100004c0e0600040504c203240841c003503032a250340801c5403480c49660710605144c2c0c1c2c02456030f00c00b5050300c1c030310040b0314070805100161003248600f01c00250800c1d41e004024a000c29034102808005100310761 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 82781314 1250 82780064 82780067
    0xe060f091e0d05070203011503030c150504080711180a021306030506030703021012020403030314090c0a05040519020f03012103020d180815010602010e0d0c06021b060c030610080403 80
    0x540c103038459a80350003691841385001190160041d1114480c800429244c00024154032440c2000c1c514420200882060314842c960070542d88223072409402c44804110444c000f0340e0401001c00c05500107007100c204820500151410508121001c01c40941c001805202014243d00e81d03601801d000e00b000c05c014144100801d80c2c030701c01400001e00070704000724052007641c020340d481d0300510706501c3c043d0b5985d5240d280042c080c000003404100c4403c41103000c2101400049040094500050154002a40340008102c06001d0107045681e500c2c006c0700016000356600d00040c0320b0340010902c50342d92540341507520400720b5140001540c01c40c1042f42010002a40420054864446450001c0c808101d030080462000030796407154400c0e103d0040b9841544122050090499199400070400c00006035880c54459010701ca1640018011500210000c0d249074007604903c0200317021600352802441e080d42c50518161643d56900b1400b0040164074900303e100a0b007402200d10b0240961708065a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 82782564 1250 82781314 82781323
    0x150412050304050d1a07080708072d0203090316030b0106050d0209040c0c02011101050709051203090a0305031b01020f0301060c050a0c0f0501080a0b030c060a02010e060f091e 77
    0x50020060024204582400400c0058901a10300100310f0f210780851868074403080300504554144030701000000510041c0101c0a003031042c207c2e07484038000365030340340ca044440c848209140d81c01c003424115019031068500c603000c056189241c00650f50740140504062410203044864000030011600c24800100a080814115071141c01c0042e280c40d5031300c2c520700280c0240d81e0107540181c900140d1200c1182d000394401941c134001c1e00d0ba6500412850105400c0e1502102c0441c0880c034031540c104064280003505018002c4040700740c901b424880000202030120a5000307131500c1d80302180c00d0550040021841e588031a11500840c5062501c1c03841c00b0203400140b083c48184410612480107202090008560321030784100c3c1001d1207a2102061130381c420039400b940e80059031000004440019a1003204260700000380104111307080b00c4204200d0764024404082103548034010040c02002c200075250246c901080c43c8403103480c0001d013503494082242c2c4840c10041740f03804070040f030800c0444c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 82783814 1250 82782564 82782569
    0x1090501050f191e05010305090606010f0e0303040e07031e15060806010e040c020d020f0705090105060702190f0611010c0804061107020901030b0603150c040e0403090e04060e06061504 81
    0x1a041a8002c542c45441c0843c00616400107419000c80351440c1c8031588501c55110555009880c10896a01c42540460340d0321011100d05021800c40c9034080081400b861406400700e500904072484c0c551190301c1d0b1101c804090700c4080109848410340b8240c014189119880424600070400c0600d010300441d85508115101c0c0c401800f01035404204a030b40b10301000502c1b2031000c2c009016a02402c0d00003562206c002010342c006005405040c079000f000030038500d0486500420050550342000704201c1176511441e8203e80c05207a40900c1003400c10524030070310007425407a1402d081103203082005840e00c490f90b80038640c603074580b02001100310340181030300b90440c0e00003c000950110190418415110700c0ca4080d42c020040c40002003041108141e0b14400e0006809541c2044004042c40500c40c0c3c0c191482c0010100174403086c0b001c420500c0f52281d005000c2d14004a02903680d044010324400190b4082d070f540b6894080c00000e03250108071803600400252a07425900901c00710300c405a00690 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 82785064 1250 82783814 82783819
    0x1407080106062c010c050102120415060503100b06130906030210030e0303070c020a080a0524010b03130203010603020d1b0f210212010c0c06110f03060603040c0b190801090501050f 79
    0x210070754040c60740f003044242c401c0b5901038008c554440d280c80505004103030488044544240c1040c400380000c0d264001c4030300301c441c0a0b00a002c070300030803a4128060440200c100d500400140310180715501e0f5204490700500080c00001001815401030082005980c283e0600749410102550040f410001c1200d901c11080d141240d00c542c01440002c80c0803480e40c0c00300b0540e200c1c4014000502001044124043d400441e8510010342e56010301441250248113034480b988081c070005820222498060021920040c00011041d03106d07800608028000042520203152606000003001506440c0c01d0103400045c0703102201c2ea243c009e41403582a13072003c3c400c000a024201090840d110007900d12000c6406000a0044081c540401090b0031108541079540c0c500340b11141619034614800c60799070204400b5003900d141d803603000f80322030303a40054011507031203c1d2968005030303140b10344020f09240340340d204045a8018007104020022041070f0001c181482c0350400403c41c5035102e070071251645109 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 82786314 1250 82785064 82785137
    0xd060509070308030109020a0801120507030b0c2a010b030727020c0f010507140a05040302040218031b01090801051501030903050c0601080a02040c0314060906030109140708010606 79
    0x101903089003400303050350008081c440c1c007000114141c41b0a801410307000d074143d6605032030384ea039810701d111845d82c205102409503003200c0e8003440810741c950541940140140451884c2c01c48407644661010342c11005011000d0340304084a031a65000c0c003c6d00c405120450007890498203086102402d1400032114000915414400c2c920050f0b1980540324103419140c2555600a10041d200d400f07040111400300004a410040f00072400443d41a80c0d62500c1507980d040c1054210f500344002580100c02c550306c0e007205001c10302203682e410800003408249003e5405c8480f5100030025003280000d80002c20981d0400041210702d40c41000c501441ea5000d190216101300300c0e040c107940511503941101c005000c1c100000c0760442c3d000681b542d0992096904128801d8610803c904075100710340d40d0306100882101142091509410007034218a0040c000108050344d9035840541c0d100000745180543c001c15810440030b14280308840c001e25050801114601c2c03c401494529005040040c01d00303000b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 82787564 1250 82786314 82786321
    0x6090a09020a021513020307060c03020607081308030907030c080a0503091005120f040b0703020309100c03020c160807060801050d030309061401090f0506030304080d0e031501030f120c020d0605 85
    0x800c1013407084e00816040100b006040404c680941c540040ba800e0740a0b100b420400250700340704121101c17001d909580500b1964862410442d0582c82c040c248001c02c459900801c0b0102e0020700055000c1c40a100041a4952031441c0110400600d6803112146400004d42400441c00c00b20440c0c0111030121030840803060b840760306036194000c000e00c1c41840700c0c2c840104181d842026070420b010380d000310ba442da4550740e4004c040341603200c00ca4404800c0d411559503070152081071380080d414140d190401609140000c200d0500e04450910f4a402459031040d080240c10005d102c1c5401134091803501e030303001d50b04080c0400c0181c142a07800608040d40c48540301c0a01140e503010210041015850b55160350703494101402410000f040440190305d09400320741a40703000411541207460a070b002e807081c0140703454255401004000007580601480c80c011354206090845107000e90300c651405011408681050f82e405010000c43c081808183d00721000903a071000c041212041e03001001140603034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 82788814 1250 82787564 82787567
    0x30412060b1503090a06110a140d140a2307090e0c0f0a050903011b020606060d0b0402130608010909030c1e061d010b0a05130c0c080406050405040b06090a09020a 71
    0x2091103240d400a40b2010007441114000881d0113007410703008000c140100c1950524148462140301c42000c0460302c05042a11443c052102038021106411000107080701d40e48004c120382e190488024043ca5901c05d4003034041080c0240c0c3c41644031035660380141f28035000e1000b80c2400100d004032521110254009400c001040007118040c60084607030580300d0320000700280140e000f05030741c54441d500348000c034024208040001c0801090345c0e40180040c1d00c84030f00784070f90f80e80030003a00040c040d110070603142a6100d500050888450034544520070324030f00710000703181c80010307006014000e0511038002c0c04264044d0075415030507041046003c868600c40e000340500c246415000f003817503084c081404603c4804404407201410400b000b80052075962041080518560152a5101c0440e0517807040c10342150303011001b00c40880c01e001d5243d80c0c05490b040e4007608590711103000036100282c148a18201400751178030380441503c04a0a045c0d50701c00180402045000b0b181081f075022502400ea00d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 82790064 1250 82788814 82788829
    0xb03070e0d12020106060305090d0e010f020a0203070b0d060e0106050901120e0a0605040204060501021f0507140409061d070509010c030311070807060e03130e060105070204062402030412060b 84
    0x26405500b031a000002d40300d019000c0c040c18407414000c0b0307141c8000943c2451003c81d8001c0c10302e0403079a8490ae610101401564440901d02c1d40350214800c0109000c010f840402c1074402800101d8001a2149042200c250903a000e54110020031b9940c1e00040105035044000d544048809080c8480f900312014018002840401d1180905108000c0100148040c99010500460083d20148030660704c1d0710041e42d0b43c50315031140c2030221a03602150f4510f1030180c1c0c40720b90054110701d401c2d05c00b8000031030070b40c0300c41d000740e0000c440c9565980400c0040b2001c48003512120511000ca00c004d03440c040001034114006c00d141c250501c030f803d1108608152003503001c0f91110361601e0b404c5480720318070b040c5400d071a0440d500480e0894603181c2020441000041900c0080c40200710312215503007000170848160402070229811301000388450001a80d490107960050710001e0158080403500750100b0240707042c00020740c41507400030001801040c2c070b10366018071a10740151000c100040140080380e8031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 82791314 1250 82790064 82790089
    0xa0e13080313030201110a02030906130503030c0607020606040506060a0309030311041518050d0f060b0301050a290a06030c020a02120f060708010b0a0309060b030609010b120303010b03070e 83
    0x600004014031401820404540c1a009034000c00002c2c00141140d4251f00c606812900540d00502002d6401d00d000c40c01015110049240f00c42010b5940000c6880c50304586024030684d08064200084550304201481d4000c004880c02c1c400340c10800e000ca050b512403100312000705515400c2520034180660050f15084507004c130301c0740c0d4030341d03803030f10030110201c8510052000288803401034182c2c0b08a00c0c03d04800c3c2e450051018591140650300e4004813220803c0c00c56160f501c80304e4282d81c6540a10030103109203c0210f0103d8819601168010301110b8141c0224003040c1c0c80780c01c80f00340d844407400d2905451150900140b240074400c0705910341490410000d5100b9103403504501d03208070209194585840c0d0704100d40c00341d103610006541e041800d00568a0a040c240700010405200750001e0010b03d0007a0000103803a100320f40440d080c82811104518143e4441e40540c5440c109060484425400300c405503085504003800c3c034520348000351095003007104444e00800c40b9070719004450036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 82792564 1250 82791314 82791323
    0xf070311070602060115110303060d0c0f060806040c0f081801060e0c040608060d05030901080a0908121501050f16030504050a1401020601060504030b04120e03010204061d010e0a0e13 80
    0xe101d42e2520029643c9a00740100340d080c00c801c02059030b40a00400a0044442c0d544029504603a41d6109104864000650a0f1a1448286800110020b07001d03049409098107a40300b14151400f00240015120000d0b203600c104603000000ac544168440e0790140c0001a41c03603028032250040d4400c5000d48156004140f56000f540c082c0b101b01d1240e4401401107940b6500c0700c582c0e607900c0004000007003058280c00b070f100d60410040c9088030761083d04440d038401c05060001560900388e44504009400010a010344d134080b103c24440420020820b03200c200e902440c0c00d9207881c01e21882c1104900030200b400300e000d41c0030ac0b404001c050040042d074001e000081d0032004240e03690700c6015204160144400e003d8010880085080380c8203200700c8040d0b9802c2642903005407601c0c0e440401c00c05207002e59804010900c0200c02c026942800100f0040045941c3d0800040b02c240340d5159504940458905001a91450342e00c1a21004111012600001c2c1c001c00d0b11b60760a40d4a80c03411300810002071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 82793814 1250 82792564 82792573
    0xd060f0e0106080307020f010306060503010315110301031505010b091c0203070504050f0f010501081b28050a03140f0c28110f011505040b04090204020403030804170406050f070311 79
    0x403c80000400351507024000c4504114a101c2c1e98019022102c26000c1d110001b1420001400402d8450031101804440100e00240440c0c4400c0c00d074074143c0081c2c100300c80a41c005d108000040c0701c1c1c2c5c02040c0c00f40041c4580b40780f800200000081c0c088d040701e5860074075109400346250544d501804000c00410002c0d01c1400146081104044044002c8034107407245024a400030607554414000b2030300c16913244581c111011140342c0c2c040156081491503200300340c100d580d41c0740d204010310080324800d4400e4582d1500c1d1114080f000d01902c020f011440380810b0050304000e80810b04100c11a08010401e50301a0f456140c00b1641d883d44e168032030b0b154003030754188010030b1086501c1360741c00710104000b1042e100e401c02d0b0701c0704103070984000100802244002007818005490168060a42c40c4d40c02400062840c0043c2d001c1801da0300181d00940220303141c1c01c104418400011f03c84050301c1280e406c0d15103024200310018080b802851070405010b40040350010405005280000002100d0720854 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 82795064 1250 82793814 82793819
    0xe01030b15070203060109020a02030706050a150602030d0f0207080f070c0b030903030708010902070302060708060607050609011508031c0b0604211403070f140109080a0201020403020f0604050d060f0e0106 90
    0x2260582c000c0400303e00920899000080c80612482940c10581150303014510f060b1164a402c405828060288100e10b6035841d000101000b10341009001801c82c1d401442e2180f07501e00000381114042c2c0d03e900e440b24010410040040c3c0c0075011582c0305d0556208080d1145060f05100c00c40d8001604001c0304180008144803030700300000041e510460050348d92034401da0f00c600c1d41d00180c1c02038150040260b0b01c20004503d60354001c3e1b100035488840505402d0030001c403622081d140c440b0588051201e40d540d040769025020560400e540a0540031005601d0010040b58080103400c804c0d901c0d0083d40e84d640101440c40d982e02048400a01c824080107045800503001140ca01412007130850359000101800c000032180402030728042e03500a40c050300c04000d5a01d4032041c444030500c004080755607480080300014001e20107010300003800d03800180c480e419807052203040e04003001c00750b02c181011302c030800240e83c0d82012044900d622000c0894400802c2c1e031780901070003210503809503d5082c511302 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 82796314 1250 82795064 82795099
    0x9030d030615090605030402040903020c040f02040815040f030e03070906060e2b02090c0c070e15030105010e1302010e130b0f09060a0608070c0506040c05031b060a0e01030b 76
    0x2150954100300425031030882c2509041c2e6405205104007804074000b03200050140c9096400403000a0103801910300944170b000000701203038400040000200e50108090140da01e0400120761021280580064a030519858100a0f5030302100c00504105003210b4180d000d450900404004000d030030014030019403911800b50040c40c0500f511405511490040e0b0111901e0702c0d4003c01e4084100d4070b41c0002c0f012902848221500100300c01e2542004101910003d04200a940020310203190050420304002c1c80c0b0301d00040c45880c0c4584a6810080144042008010b0080e0820045903182d1441081840142d50381602008c01d55804119100707140b0308090941c001d809950030885480030b080c0e4000c0204402c50b181556151340041d1180c0090003030901030030485030803810f5030601030318007041a0b0f81c141c5410f50480d011181314195030810086403c8c100f00e85c15020910418030103c020384000031840601542451008000c81500e00100c2a400307640800601c020140c078511240302103180 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 82797564 1250 82796314 82796321
    0x31030515090c09060a060c0206250302061602100506010e0a030b0105030f011404020105070206070609030e09090105040f11061c09140a120e040f05090a0c080a02090c0c0309030d03 79
    0xc0000e820b00904002c1072061400c0e51525120300720091000914038100340d821113200e09403400481e0401010842030304404005011390b84101f00c1003511811030300103460002c0c01c103140600036a000359907500400307110076004101d0b444204040c603400116581c85400498440c5024040185c000c0291440801070044903407a440c103032503050303003150000c68860b0751007030880b501d0241c80d00340000f901e4003080c0191300c03c800400400740010b10160a100017611041c0849402c16000c070b02080290040700100d0502c1c0104940c891001002042685000c0d04c680c42d03890f9010400414400411010030b2003a9078203000d948040d02ca28600c10041200c800100300203101000b81501d421010350110f891503c00000d20300c0380d440e40900c032402c001441c901d00766846c0340807803800303540320742c0b030301c4050b40348810741d114691141000c400140340565190600c240c40360504d4001446035000a01d189015865101a1700e41015030342c01c46681d0b400c000720102d0300310700071204001d50500a0219480d80240d0540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 82798814 1250 82797564 82797571
    0xf02330f0d1d1603020a140d0203121215030c0409060e070801090c080307030f050c01060e160908070614070f0b0405070611010c09061d090106030207060e0331030515 73
    0x70484107008840d041020b80f0186901c40254880c00400e0240a4143e2101c5440801c290203800d00662580070340c0000d0618001c00820a01c1c201c0214030b2400340310604c115a130b00030f0f00b88804880d2190490012030b8403140f002c8003081c041d40e00c1e044100d08001307096010f12483c81200d02503640c03450300d6010f81800b0708007141081e80c854054001c0401c21078004800c6272003485d0b0584400328020b14854003030f1002d801c80790344812607550350400040c501d6008070006109407001e00c0b602011600001c4007402031652900800c1d0681d008807000d0080c160491016003440c4e000c070b070141e034840f80031385070110900e030300910014002e4500c00c0c2404100000041c00310161540790f00d07040d0b8000b0a142807542290080724482c0000f4402d1642000002d0240210129460000386041410394500c00400c1f0524802c0c0e0051f40000e81c0020304101303001321031082140d4603110801a41c501044c07801c401d0003110403040c0908800d2492030340301c02804010f00d65000150350010581d58130004071101e20707540b8402203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 82800064 1250 82798814 82798871
    0x70b21060114030c040f1e050d050a1a0a0f060602030f0f07050a03030e0d05070f080f0724060603090b0103170408070603020306090a1503080a03060b03040f02330f0d 73
    0x1c2d0740100d04101000c40e1000740d014842503043c2d00514050030400d0236001c00030700752b500e4040d10700d010021458800c01960540880843c445c030a080c407100440031030340c03160b90041c1e10515040d07060042c1c07035012049404205168024603220348151855000e5442a0300f0020543e2040d04960700030150940c00c10a0207a1801054501c0c449103808151200c0c0308036400100120071042d6603100003120354010700070b00c040b84034050341440d40c9540c8010030420140f103501151800554550b1180d1081e0154401504541c0f40500040c142c030703a280a1101818040103040c94441c240900c501d0499501365401005210101d03420280c0e520809002540b099401a00903042c0400044001e40d6034020134203e09414070002400c1c52070341d182c510709a00201c0e403c404050725020005520008400070758040c42c040c60340c00d012040248100710320b1441004181100058007154903070783e003484005140c0c450f84603001065a132030321ba803120a034500c2010b5000401c586800660b6141da480031066540c8000d10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 82801314 1250 82800064 82800089
    0x1090303050106170a180f03080105090117150606120103030e09010504020306060d0c0306080a0507170606010903140118060f0c0915030905070b030f09070b21060114030c04 76
    0xf00d960468040349a0244400c41e12030070804120500d41a6202515640039400d6414560055a844020301c00580c80150009100e140040c40701d40380c1000924014600c1100142d0750201c10b000850702c03240d990202c1c0311110b25040000b850303501e80108a07940d00d503040c01c55005640c0c4910b400b41444005850040c001c0f0041e000106050a00340f0880307008003c01060320341080540d16000c4c025000c2c040c00107003090f440f00300c00102c0c204200300a0498920a07070103809031a0906c442501104425080200079600000078001716036009061002901d0304038492101c0090042d1645000d414054603070710b070480340c02c0c08841c20b00c103080c4d20940c013981000509001d4820501c0049624140030300440148040c0418005034450103030b403007040001e12035815118010307a0b0304004442c94104940e40383c22480c43c002045282c00f424801c0b01c1c05000d506103c50b00308005950041c0441e040e000f02600b41560000206181da8001c09811648007014076901d40d40c0c0c644006000c031140c00c41e2150f0710f0300040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 82802564 1250 82801314 82801319
    0x80102040f090c05040608060402091f050a020111030709030209100305190212011e020d0b04050406020702030d020a1505041401060303090f0503121e071e11030c03060106120b03030408010903030501 87
    0x2213001100c04442030380e6914042034a889007080001d6000c8589982e20550040340c854007401c1c10040700d0040c01e816141c0589a01600001900f91802c2038270754000c0c4a4104204005103801c25100700c140e0347c0507502d0714003e60390041003070120562504040c00c00d10900380487d102c20500070541c03150a100b81c2e844442c101d0504105402d0f28588000c404200c0641d4002c2800003640ba8040c1c11460107110700030400b015000301060856000365415900740c5c1d00010700205600f4100549080d2001c14030080107009003a4882802029501d42d44045064070350000c20180404070350002820295640200000c0b5928034015050360802c0c4150b100410101d6000200c514012600244080c01b0180300d17898581ca0f00d411469408222003011644c0c40213100c039501084440500785800003400000005050b10383c208000c503040c40080b5a0321940c0406000203107900c000c13a81da81121028144030800e0b07250801c3c0407001e80f111b00d01e4140c0620001c00c0005100d18150001246940252001c10407131340c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 82803814 1250 82802564 82802567
    0x102030f1305010908060403080a020307180305030a090b0403030813020609101106011d010311180705030615030103081c1805060f01050609010c0314120124030b011d0604080102040f090c 82
    0x3d00451f409804140c600000403107404c4160000c43d0301040916001d0145001c0031500240c3c070b103042d00700f69842e40c80407502c051103d402c8107042c40034042e0032200d6410986940d600400780c140003496002c03c0d81400b00309104549500099402c0300100030003107824440c944400070450003503084450403e2040c0d07000060000310407041005040142d008400880c0e0860700c602044484540740e0b01e07001281071403c4050b0751002c40c500e5010b080a075580c80da5901f030400c100410030b81d0407624509403010400040000901d540100c44600040700c0c6021200075080c0c8080e80140030b1900039131107440720040321400700100400c11522800341c4d00402681a62101c041c02018010410310b5400b140440d414000440d0080c1146044594116840d600c0c00c110400c19140003982030380714245031241181c8911664440b9058010320220030320b0204001003003200000c04941103c03804940d210404409030703400e6125041224094207800e402955659907403520f40b100032000d4450040d895103400e0600300d006 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 82805064 1250 82803814 82803823
    0xe0f07030213120f050f0f0f0616080a060302030d02010b04050a0504020d0206030c090607030c03081b160606081501050a1710050601020c1906020709110d0b0102030f1305010908 78
    0x31028a0303420902c2604003045094072001d02102510f804880034407280c0007440c108803a110504450016050301c0e10701078a00d62500d08860030070001307908000c0821000e00292004150014000e103842c019646a0b812558014141504080d405016a0040034003aa8054101c10a0b03070400756000c224a50f00d02001404464003660020741c8200c081402d40017501d01240070f103411010143d4100d00c1c1960543c009001e503401440100d02044001449405142c1c0010400ba40100e41d8459115217030b2a242c0818007a104020301180b025600302c4a01c02448065481000234103814803c95074120030319100c2c148503940034030070340b40302d510388030004202c40203141100880002ca88004002054550240c80c000d23082c0140039a045106224100c0740d1641c9030302c099110113662070000f079186420000000e00340035260300aa04584c1c1030030481c60480d04403004850114201d00000140751030000c0040f0304600c154401e00c0100800030521621400d80402c1d0901141d20980725202100e50f07450415445 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 82806314 1250 82805064 82805077
    0x60501080615031b10020312010e04020a06030506300703080c24270303040303090309090905070e0408090909010506010f0e0f12100c0801081902091b040b040e0f070302 74
    0x1c90501340051626080080b05410110b090f80142c9003801c440540070340306500260f008003076610418043c801581803000780071020b0011b915042c09075182680220b540080c102000a411048003019818240c1e4940b1309008409005015500003035540d0520314103030303006402808614040d00c0c0c54102c00c001c0c91125030700141c0c2800401f04144c3e44a42c020000c9004494400741d10328041147e601d52000c00340002c44c8614400d4500142014050a0040081d103094001003400c41c0380c0f44400c8041003001404904a80c00c0c45d805001590712440c000019000d00300d109030700103001406020400d90190030243c4664000c0c0e0310b0700001480c054007143c8004c40d0070082c903001100c0d107845134024100085400f0809000c081154514410601c030030044403400720f44080050100001441240fa061041101d02e000b41d170b401d58031014858001030103514003c0e00050810112403c82601348191505880060030303440c919540315139a0b4039003104041c0c0d0445010312001d55100c006451140a0700c2500c4c1c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 82807564 1250 82806314 82806343
    0x40b0d060603150e0c09090408070605072a14011805101404020f0a05030d090303091e060513080a060203060301180507090209040f1a010f050c030a0e0d06050108061503 74
    0x410b501e4242442c108100c0a4007200b00c154042241c20b540c1c0d00d810703c070301e8003c502c126030b51a036407121400c00008948028101c4dc00300842c04080d40a01142c09400b07618510148580381c0a086a618140100364401c135481700d840d50a0071206114020340035829140d860040c3c0030b4a4420b11030341190f06c1212003a440b000002521000450054140480078080c03080000e0402002d4503151000a4a050383c20381000d4001a904402031042661000000004051403148110084a115800600500280500c43c2002400f007900d602c9824420302900007005036009655501400303092010182d441101c901d070080d1b080400c15041c06002d900907500080d00711000c0c040705410005040041d50180f410b43d80e01a48800320700801116a01c56940b00d1410b280d100750800a07200b002408c210260040030046c03100901c1030030403400300441110b40d807048510f44003055540690000b111007240071070160200d0b02c1d14001080300000018802d020340c0c049001c0700b140742e04101c20140d8985c1248407154 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 82808814 1250 82807564 82807601
    0xa29071b0e01080c300601091d03030606070204090203070b0c071a0705070306050721060501201b0a03060c0f030501051002070b03180303040308041203050f0402150c03040b0d060603 80
    0x4000200c4030070110160f401540000415a01010510380746d82038110324003087e59010340c140700e0b0303156100b402c2070004240c02650461429070700054160045603400303401951280400c80855a05000507005813030300c90112a141c0401d26019a9900b01c140681c130f010390550072b940005d160070b55040c0c401d0170b64000000c1001c0c90465403201d000c0d05018044005100051283d10081c41240440049140681c0380010380307203141c2400100740814010b90b10458500340048024108800300b08904d2100e0000710b8040d080e0320703560120b440c0c0001c0d40d20190141c2e10300510109a11343c0132036894024400380d6001d201d541d803184100701c01d450715100b803000964440f40080040035441c80c05150700082800d4101151514001c0c0755003580d00c103c4e41180041c44000410041048001001c0030000caa8a0200420702e020b551080d07400748050806441074161000e16003071403c04000300e5154608443c150b90b00e841e65200440484c1e004202e00500d4942042c601061913446813042e103440038094070440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 82810064 1250 82808814 82808839
    0x2060714030714040b0c0f070e01030209150d0b090a0b0c041203120e07030c080607050304020a051c140c030c0d210c0209070c03030b0a29071b0e01080c 67
    0x81e1428203818aa40303c4241040c8000a41204c0c0b0710081c00d036001d51032018004920307100d181d0908020b80d40e0002c50601000c1e03401800942c8036a2541a80a0004000c004d605a0f2480c001a95408120030040c80203c0b01c100700240038002080409280e0300c10030503c4810740b92001405402e00550207110303503801940302294040f81c841c4223800039031903503100d000500a0041c0300317041c00d090301a0415152600040c00400c07002c40c0c10040c0c03940c0402249425800e40c01c107640011002c020034451a40704502904011001e140c0c40002450155070005074005802d1144c9206501c1c3c0301c802010510034061102c0c200c0f40343c1000a04250f056a005402c4c1d844501242865190884424464400c00100042d0600107813aa051405d001d52010f440c0c80d988100e2a2500070182e588004040d802104810010020f510b500100d0038200b03100c0e2841c62aa901901145400e140194034000d40304c0d00d4440f4103452012b009400d074200760341101042074003581c1c03109480d1b0303070b560044091180c1042515015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 82811314 1250 82810064 82810067
    0x60306241f03061701020405010e100e040e0c03191101210212010906080c0907050306010507050a080426072601050a0b0f0102070608010b0706060f06020c01020607140307 75
    0x11400c200c000074810100c1e501008480054400040c58007030109a84200a200e0711228141c41d80b0402403034402586040d00b04000204050114245a801448034485540113140124001c085030840a0801c00181480718a09962003203002070840c002d0040b91060410311100300c0b02034190603040722074405103000c904011103550380c00640200d003000a060110b010504a0b00080040c00c0c1000200c4a0301c1d414111150201c5e103103580601c0e0103a1110b46100580d8071880803070341d030058181c148140c6035511080166150b11a0306d5004201d0301558201d00200140380f07014005031031801003402040220409140700c101c20b180440340f019803000b141080124406c44090002c0c10004540742041001c08020900790390083c0c40c410701154945181c3e0129090240180e060f00c0400d01c000c15481e45400b0000c2c1002006021f41198648002840010b0014a401c2a00200760404005031a0340d61400001e44580010f190107006001d50000f1509040c49210102d035515110180303246541c0301c80d80c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 82812564 1250 82811314 82811371
    0x4050907050c1504030f05030402010c0b07120905061005010809060c07061b0309030f030614040506040e030a020d120207020f09040c050a0b0405010210050709061b0b0406060e060306 80
    0x4400c01c01004005032800340700280318a160001001400020604043c0740240a1586a18a15003001014010000540c1e4460714902c50360342c10021481c40c6481e0740345c00f19120b1729070b40c0b040340b42a404c0407043c0e010014009802403081500d420b0039880152034400440b008101651038224581c49800868150401031008001552040d540001c1003408113071320000e544060207c090200eaa60651310082c55005410300c00c403000035107010801d440c101110041c1d10000c1e010f0b01d9005650752800684580c80b282c1c8003040700101c00040313949409161600039901e1041d20b0034640010082e440010000c81300380292050b071503006145440250108041c0101c61a0040090f140048180e200083e140c40d65003000700580304010f0038a981c0c03401e11001a28000340040b0a00c422480d282c02c1040455004456509030340719881c0c0320541c400244144103104055000103040602d01006000030032204d54001801c5401541d418022a41d42c481015107400088403806422541440c1d24001c0c4200c3c0312 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 82813814 1250 82812564 82812571
    0xc1203091c0204050118050702010903120e03070f080a200a17190905030d09050d02011809020a050405130c08070e0a0b0d0f06120807080d110a020705010e0a0b040509 73
    0x222040e0651001e0740005003998400c0c0d0001041c8404200c12002040e0a409000d038006020700083c40154890f40d8014040301805603c004070343e0380d03284c4400c03c00e0b06c1802284e004070b40040b012480c45c03440d800e20400031b41c0000c0b00000070452918100c1200008001c00e012603007081005454620301648404229000026075203486050411429a0701030701040c0204017410150358000089050005051070b005a003404038041c050319050401041d0340324032440200070b9080c03078031403d200c800401c454038000182c0c1001c0c1840380013080d00d02d4110f82c030001030821140301f118104901000014400c0407199040304901c00030350000f001521550150605504800025000b000301d10780d186241d285071741000300c00c0c0c400661141c0e800f8a8880860203114003400408803601d503e49125558031002e407086c080004d100103c041900d1511184991000b000308142180265980440e00402034440c45a030068901280045101c0286420540d1011050b0b4620015079840c00b0f080104204800e41c005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 82815064 1250 82813814 82813849
    0x6070c030f05040b130806010909020f040b0f030a0f0b0a0203090d11070b180406080c1011010209100e12010501060903030302090409020d0b1006081303110a0209090f0c120309 77
    0x70000007941c80c0001340100103105015160000304c1e0b0900000e58100003060b0b1160644070b0410b174410016a03165a00d50010141c11680042c03103e490341c020810b1074840c40c00e000d03031500a403400078081c40741d83c859040615125042c000707051781e103150b032032012030009461162859002282200c40d0500410100026032042c44c00ca4a103140d82d480000c0329944a0501c0c2c11400b4840e54030283c0300d05150090303902404689003d013055032200740205142502c14103407c410031400c0000500c0c5032200303504a40c00703507401900904000408841c05070141002c117110320b016291a613012502485c0601c51981610125a1010407161851314101d002c0c1d046442c295501c250f681800ca4016901c2203c2100f9280c0710302c200414614160704074030000505544501d0501500000b00b02580080380925000c55038941800048540d48104035480c10542c1c6000a4000c0640800d218101c00001010000f2117011002c44103991940c1d028411061070940305941c0b503602c184044540b516000c1d40c56403207140754 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 82816314 1250 82815064 82815067
    0x30f25080301082109150d06030203120403030e040911010c02060c030c0610060305070503040f06020903010e0615010309020f0909030d09080703030608010b1302180d0606051206070c030f05 83
    0x26038845000c55403081c0d010041c0d0b5409181da40c0400982103541c0f04008200240c0f503401c0034000d0b408503201096406c042c4071400000514401121050340c0300002454000c1c085800720b009042161256500c1401b0a602284c80c0e0540c0320140d2501b401045226948160011901c4e908180107440400350400708a0b4004000e10041c0d6117802d041000c0d00001301c40381c0091140d81402a401000101c00c3e4001208240c00c100800c621140c0103000c403a0480e91040f448030105200e0b060810081c01440e0203a41e05500740340d0464652030b00080c07441c0c0038042c0c807661420f40380030000c0190300301c80080700025008840c0c03040a40c4540350401c042c42d8004d8180040c2c9142c40b0104140604440781d240342103c040c00085404e1080c10303030610954015001c0c0700d000b00040e6243c0d0300003844101c0c3c1c03021422581500040e001c2e042705034201d04c240c1c600748050078118440e5414540900600110302901d0b000342000c000d40505100d0000e04540250120f868035414441d907514100c0b40040c41c01070404c1031150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 82817564 1250 82816314 82816387
    0x509120a0e0d0c0509071d09131e0c0906060e06160c06050307120608031e0405040204060504030501050601140f030a150e0f0a05150904050c040e030705060108030f 72
    0xb5003090780c03142c06105480c403000c0c650070f0000b00200040c024100b88100041210803440d8480e0503103138504503010440c1c4a400c5a5581607000021004140e00208141e8503038004031746a20101a500f4041445581c040789040c0d2100c480400312913083c40741c000013410508030a051800c11750010038182040204180403a810b40e01c44c589084180c0d40940c000844c00010090181e0780000349082c03020b000c040910000b45407a0503141e0302d0240002e21000340e40e6442d02d00c10b0b001d038a00210340040c40046c00554640340e58840c05029500944400d031450350801c000284250711034a040d07203005000180040c03c10b625480c4405a58000610640001d6a1400424040c05a41c60301d48005c1102c03030701c03101c3d02d40350405c01072081d5840600340b0032001d4100740a0081170168040c0d840039828050300c0211309680c80e802e01501e4824401c01e0300b508185040e44446c050039000c802401d0340c5010b0300880c1d0b07460360303100d50043ea40e11848515074030102080c0300035158213001400e000c0d041c0c15100c4a42c2038400e03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 82818814 1250 82817564 82817569
    0x706020d09030207031208101403010e060901060801060812030c030a230403030c03060311010c06020d020d0c08090a0b1801200a020c0f09010e13080c0a020f040509120a0e 75
    0x200398070400e0700540d0090a04000b0000b51600c00c403007145e40382c600200c581c2003042444d201020301e4000c4111000410f07500110710340f0300754003116485240d034040740d400381414001d0500a00c440e0146002c0795003405804aa038540000b981c2060360551050755295644180d603206684d04003500034200f454486511000c0c18040c4000b10703030755101c0c120100c0300038101450003a00310703010950b541c003e05040042c00c1012403000211000c02d103100f070030000108401c51070314000a01c514007030005a14404241c81e4502d001a6004110400964403404500c2d1180b40b5610350b140035070400100044007400004000540d03085824441001b44000131403031031091b8854035401c450a8420442c5120003140819825074108034200200c01c056482500c1035074000f01184c41071005001300000500e50101240540b62024180454590009451b64032142d10016a64592582c0c1d9400da11401c807462000d1058500352041ca801400350000601607001030b80325031b9100360003094120061121f0030355a118541c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 82820064 1250 82818814 82818821
    0x60f0a0306050c18040e0a020609011206080303010305070602030408100207060e01091104060605160605041b0b07201f0e04020c0109140307031d0a09020c0c0a060e0a0b0706020d 78
    0x2084012003c0c1d80701e4054540408064855a141d07074030072820300000c0400900041090807205070140c03001562030030450016030b0754881c084100c074491807070401e0000340c580d004030145058034840c4040d00c0007541d941004a81d00e000b40e00606040b0740202000c40e80f48000d030b5005180c802c0c4501c5002ca00000703030000071800c507581c0781000d80b04c11012198001c00c500c3e0070300c940c1d07004c1c00a1707042181c200005c010f81001c03018400d4000034074040d511300101e410b0000009550300d0000c4d800342d00c4800207459800b0a98690070040301200c440030040d001520030440c004400f09142c03030141041050160001c003900d00341040d800a00d040c00920903011070280c40d10300050031001801c60002c0b407900f0340c81c544144014801e481c40d0409401c01d1081c070001031f60001603a108960100c800101340c2544200040e03d1505651280410b00d10002d8000211000400c0c00d802220041700c001c0c00e170759138810041c0c07a1500d1041c000c1da4090400d041c180316802d509d80c00351464038020701d00141411050301011046 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 82821314 1250 82820064 82820071
    0x303060911090307050301060602030a0c0203031204240603030503060108040c05040e070302120a03140309070e0403080402010e09040302030429160c0f050d08030405011404030e011412060f0a030605 87
    0x51100020b4440c0140c201080b01c130000707080c103038000c00520b440c10100030b4580c000c19030010100b24801903800103654040060f030308a600c00b40c100c9400703400c19140407022291684184a04003100c40d1400c1c004221a05c94041200c2d0142c44891940da205801142d07900310040040741c0400800e280820103403154851402815020b100800d000d03400d500411004030300e02201c45040ea44090044800070f0f80c010700030219034091480e4280c880c4c46000321141080029001114100d050004201c24168030614540c022030007070300d484031f03555007031000c0c41004a802c0b40c0140240c0c4c410402045100460182c045100b25200c28548202e03c8108500c0d80f60fa002459048818140703518400501004001e0358009200307c8150030303051761820000c580351628081c40a40222400300c0040c0074403000703401c0480b0b1400c19015040b52450149405000ba00c0c0182800380010a41000582d48d69600d8044070039000319403200c0b01c80e550780d0743e0401c281881d20705e0034240c0040300501e000000601a0090500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 82822564 1250 82821314 82821341
    0x8040602120f0601030e011505010507080408100209040506030606010f0f032a090b03040f06090c05040516030b0f01020c120c0a090203070305060609010e010f0e0d2301050103120c03030609 83
    0xb007818428001016100716095a001c240d240504091101d00079400c0201150002e003005601e0340385608040c00e8034040ca41c460f104a00842d15141a004000d5000b0001c10a04890400481e00c42030203050340c4402c2215058086910b00791260b500a02403031017540040c841e072502280c1c4140703580c10740c010401070741042c0c0302010140d0003862015030030032041409030407203100844c2189050340313401041c00d440440c09410796958401107018040503802d40c00103884041c0c401d01041c00c1c0b606050000031107404488c0c0010b0310341641c44250745481c01c449400040164001c00d40602c4802c200000003546510f81d6a032172040c807070300b4140d50700c0300300922008103a0b51000580f46d29003500301400340e400082113103102c0c0704200131180003aa0406102800d050083c40c05500000c003558096615551004540f9804003010910500f00070440e03211510348885407403403124682c88990702600740c070401c2c04010290740c4e0060050700c0f4107106007181400c0d94020720300400c0c45991240303550100d52809403441d5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 82823814 1250 82822564 82822591
    0x102120603010e0c150703230a0206010504060f030206030c070f0803040c060503070f08090f0732030d05220e0f1b03070309030c05060a14010b040302010c030804060212 74
    0x10607103420320507200840340200140907455030a8000032044003148580005000c804201c60040c584140e03c10b01030808036000020302d000103c40b00c060f035a0850900600144aa100041902d0034a4000c1d20700b00e40307440c075003202030505540c01c2000030742004100d110155406d00100c80810f0840000707031043d902881d10103949003007500b4002403c0016400c4013050203802c000707100e41150320001d109110390a503d002d48003a22668011410204402030144c04d500c1002c0021511880c2c1181d10050b0002e1a40e018516002c2800000142c1c489145016859004044004401406840108207000b0304c81000150590407c4001003003010360b0300241c3c0c11003030361000c206440f036907010084e4008811a000c101c4c2600c549200450900c801002d41d4101510f4910f04010580907900590b0307140d41c01003e4480ca45800c0c8403100c0246140c8180f0820f050031100009801c0030703140c0c125401d803a0103940c0c8101d01012518242d48251001d8411141c6039420450455240c2d00c080b861406080c540c6101d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 82825064 1250 82823814 82823821
    0x301030c080f07030f151803020601170604050c010f0513030b010510053103020d0602030709050d050a020103021308060405070312030e1902030109050d020f10060b03040308060a08010212 82
    0x45240c24a0300c09000ca0540c0403c41c00c0c0b01154060440a0a040c0d000d501515101c200351807800240c03081c2003a020a40c0f0150b0352000800d5004a680d90607120088072803044420004240c43d0749103c02c0c3c03405480c64101e040e040b2007030b5214800d0340c1040041400d04610340101d140c00c01001403000e52054513003010200043c445480e2184660791501c0c0c040c40d00a0078850ba0380303152440d064000c991240400d000c1d00048c1c018450380a6980d0013150010400080e038005410310401952040381c0c00c9001442055000c00d8502e400d40c0103000341c035005001450031400b41d900550003580700000b408041c65803500c00140d440010002244102e219401415200c1c0c91803070b25020b200e0764000070109140c1441090b170982200000c8030071045241c211003030047c0320640042401803002e00805082800303101040101c140c1c0004107a0284d100000498401110a092241c2162107900905617100030070400325010034858011182c020100a02c024071150340c80389542d003260f001c403042403840e40c00c00e400c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 82826314 1250 82825064 82825079
    0x302150702010f06061715040b0d0c03050601060206040c090509030409020f07050706030612110d0506240603040308011e0503060a0f050f06031c090911030f15010206070e010507080301030c 83
    0x20b0900408281c10100c01b00130310090054000600241a001261300e500503684542d43c84d03030415400c43c4400b40c001e0503615010700340b03c8088032890009848503c01d18000082c503038030004106204079009040c80c60520306100000c0702821020b0250843c0e444203101c0492210400d00c001e01e1034244040c500c83c0d035101d092801e40c3c1000b0281e4000e00c1814504001084078002c0f0b41204001c9a0344a804240303014101400240303a10304200010b8068030074682005043c502820060003c010f0084401341c428040d2004c00c46581700441d00100014011001007044241c0e42070400d07e605804c207040d0b400640c0b1000400c1ca422001c440c44d9048503182c0d00a181079202e68420300c3d42010880160103130b24940940407139602c250b00e0704070468146910311f08800e880e11882c84103010b856404801c1c001d602d540071803d0219042030b55501120788030800440c0c1448916241d090056006801400c0140d4452800b616054210100c00c0e0512008000203800600389000840c041c6100d01a42c0d6100c6061958 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 82827564 1250 82826314 82826321
    0x30a0518040b1e010909060308042405070f02030f010e0c01090504110f1e030a09030f0206060114031b160302210909060402090402190806150d090302150702010f 71
    0xe00a014a240400401c100d407504607a10701e0035284280d1032280042d0800040b58685003640c80303440840d15045012041103011001007040307620b4100b4041d0220703c1e02e401c000030a903501d821500450743c01c00c44c10000540907040340b404503000509445c0d03070718040300d41c40382956242c00e4420f007103030450101c419081d80c0042c07503280988400e8408011b00c0700102c0d05401e02d403003030396550384000c2c0001c1051903d10303000440c00c0f5104c03200c0d0314186499007004041c9402a0000210807804503500f452002c1c500d510021b059403140d5416543c02c0400c03018561484000c0d800a0400d81340340600004127091351b82c8050080c2000e84d5038007140d81412810307090083c145190405d501c1c0c0811814030180e20780048140c26034100900803115100ea6844400004000307114200c03e09030081c2c00400e808291004500710089081640e0f101c41c90b80d9500d980810800b06007072030000d801202c061029a0748003520703501c9107090b9440b0380111880d01440c403000c085545801c40b8a000140e4480500401c2c5e24560301 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 82828814 1250 82827564 82827607
    0xd35040f1b0f0308030a0207020604080703030e1f08070e040204060c0b0105030d05040b0a0504120b0403110313180b151c020f040504020d0609150e010e040209041506030203030a05 79
    0x9940121034140b041400d8014280e1001401203800440400c14005055041358282c65004045a58460341d4603400754803880d603032000b60b0126144269402250800741c100c1000c01c1e02d4803401e1960011205400e8840d400c01419800800ca00501030844903100d51005002410841d103841d05044424a410034004505800190203a0002c1c484404503907001000d070b50588250f0312602d0b4844452031012991801203038032a01134002c0015490003031056031109280104d00035581d218408520700c04007a80c030f10800b01149001c1c1c11003c010040340b00b041c5082d4100a60040d8003003030a40034840001e81c0c0001d8003105030321110380010580e4000308100907880b010020f10209505140104a9543d0f29010b507201d024041d0b40c000030007801d410300c2c0b0b5001e02d000c0d0000b25800c0081c0603507400418a00f03105400f84610b86028500040b038801d40c0300381428810b5900800720b408503900c60341c0f009604c07101d0b001c80b1511242c4462021006036003e1025041c0c2c5c0a20359a8241c9440703105201a03002803528 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 82830064 1250 82828814 82828853
    0x2010621140c060318030904020a030e0115030b0a0c0c06090b06090708060307120f050d03020c0f010506100e12030a02060a1419020a0905060f040302030c01020d35040f 74
    0x140c8040c1e441d448200c192a400780d02c0f04109071801700364001060a6115440005612500c00951042c035150168042d400100c1da40700200140c00c4500700d281070740d26681c00094440303c0b258001580c2c405454001410040c41d5190400f0014516074071001580c1704440c00301c5024440601b00314441c104030440b298400d90500d0700113050f00342000401d4903403000d40940401007550007400028040c00340c040d038000d07580c0b110440381007286007440100250000a00a00306000741070001410020500555008a40060414100d0a90041c2c140e038082c0e000c29841d60800c82c444143c166092088c0060524200342d0b0700a03221034a0b2080302003040b585144c00d0842c0051550090015610b080d00c40d58844294030f0350011703175403841e860f003e440c590210790100ea4803d800041000c044850b03000600104c900c00e408460b4000d0310341005a80705c513107103401e030000a1021007100f10000c2c00619140b094000046000c83e01400c010b124466400040310b050360007000c0d400d402800c12600c10000001c07585034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 82831314 1250 82830064 82830073
    0x40306020a26070c030507080a030e060a0608060c07060623040f1103060910120f0c060207080a0807080904020f03041103010e0c0d060b0d030804030206090a020f0d030201062114 78
    0x82d18141e02c154002402c5442000507209481c010180034008403803100350020500c640354010110020042d0110781c0074070f6100d004031000300310081207500806081c0c840c000003502c01e5079500c1c52001d0007030700644030544040d40c41707a80004001c81d90054280d030700500c05c8980c4190b01101d2050009461100c0004039640b803070a020f108030202d81030140d07600108100ea03800584e40300c01401405120454002d566940380b00c2404008004403050000000c0b48150720200c0d070540d0311312041c0d80ba810580b107a1000c03a001200c03204001180b15006204441c1708003089401c007451340c2d011070100c3e000f203070500180100002c140401d000403508940744104040700207001000c00e4012043c1c544899156080c050301c4810b003440c3c20006603410000426a000c0c0c2045403039034035418010031000703041e18160058000c500101d100c0c03020200c0d4140d500f07600a0219060342103202c060109c44041008160115581c804021580e07568200c11b0329440303000c00042e400580801d0034201703000c42c80d01d02c103c1030300d500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 82832564 1250 82831314 82831367
    0x80603070b04030b0403170703020d0e060603070506030c12010f080c03060c04211509121701030206030c0c010501030c090e0105060d110604120b070e0d021302030a020c03040306020a 80
    0x1c0341811102620341c41a915803032034036946000e5940001c000c05c405041c00a0004000c103442c0c5c942e02409030722006220a00141c03503600030082e11444290303103268244e003140b0010311035424010300660b0401407050805181048034980e5003100c000030f802c00060304031010b0007004803503c200004650914218054040741c10030440d4503000c2d2045110b16200c080d41ca4039020816011032140068141c0c0028480c11000d2080d4107420023088420301c222504102e0b80c15440080d8411400003583c020600390600d150703400c580030000250801880c5040c5140c0030815901c980900b802024000c501c601881e1070a6818600c0520960b07030071724811080d03689000c041204030350328007184d1010307107401c114155001007902700030800318401d54004010b01c00000b00030740d0030840b81c10b1340640700310360a42d01e551340324031007108100c6180c0240038060b500440c140e103624446d5145034000c54025030740c094010700e07000c15034641c5800c541090344207032906540401c170300d141c407500402c40030305071018819280d48814 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 82833814 1250 82832564 82832579
    0x1030f0b07050307021b0310020f0403020a0b071205130312020703030909020c0712020409082b0902100f090f0b121006020a03050703140408010b0a050103020306010215061f0f08060307 81
    0xc0c2802c850b00d8881c0705010115500751000e0140d8107842d500c101c4155030b0751072b0b025004c040703a03030280c8012401015036980024155902d1010381c2e03840c540c0040d14080c0c1283c031080403510f542000d040001c941c24100c400100103640b40c01901000b4045801810700e0a140d81030241080031603034000200240100204820300c5808a003120944411400c0c101410400d4004100140610781c40280500c3c80019600d00480d03c0d03d22001581080106104080c0c90304500b280543d001c12034000d401c000c568481c00341d59801244107810071200ea150100e0540c0c2d8a24071a56841700300c0e4000700c1080e000103084070382d8080142e401984500803499529025107000c100a50f5421400700c00307010040301007004400c140c42440b40421008030080b065444584800c0024001c01130110310714030400e45002d00240da54081d009580c85000160041c0280004400b0107080d01034000701807690041011403460a54803000407910b0782000c030703542e4005c0c01100c3c0040141c941140074041c0d44c46070b80301d05c03800c1000c0c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 82835064 1250 82833814 82833823
    0x909021e0d03230a0503043e040b041805060109050105010503060910090504120206091605060703020c130c080708011a09041d0d0210020c0607030207080f0301030f0b0705030702 78
    0x242e0503d4503071620001e019815003444022245400e02e8400041e0403808903500c4400f0b10301850180005104440100072030742a4030140d9260004c400003c1d2001075a10b21010005010300d88006d417010421055403c0010111a58001d01684035103c011186080c0041000070700c1c0909035900b0204855414000080c189000050425104003109400165502006850b54000348101501403105040c01d1400c00a04031400c1543e20041c86400c0005c0c050300744c000b80f04070401104001910384c0034203202c184404c2c0d078403540d0150258402d504580e0210b84072502040c0a00a003c28001542d01d04144d0041900780302030300d100c01300011003006211b0600c90308190031103403000305469680d6100c00b0f0041000b600c90684100b0080000c5803803450602004034411001000c15800d8440500750361005004900900200041940c0a1000100550b0280d4014a0f01d1800390390303d24104010358014140c154000d805c215072103000d030074800d01004642c3e070015420810720f0800c1d506626114500958070f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 82836314 1250 82835064 82835089
    0xc0306010306020a09081b12210904110d0506040605011e03021b060f071e090b03040201020a1b0510051207030c05090a03030e1212040308090a09060909021e 69
    0x2181e60004d1480f40040c0104105c0c03000745121410340391115100030811010703800d403d15660041646441c1d0b82881d000108100e0500c0c1003044018001b0031110b4114074042e00000e06842d081951520403551221054004d826401e84c030304004109450140140000d03207a86900240c1030000c0000040c0038450011049000362075603181c016101c4148461542070200101e40245482c0181024001001c4503420014800e16aa8440d84072850400b02402c8203d0307054440e000024412120900000c2c41e903130004c40d0090b00500c111401021580c413140e61a0200d020341407400320100d50108220b00b4240c1c1541c00ba041e250034141e041c440084000d005403003006001c082015900e403684101c145c0204142c03580504040c01301d004003901c0340340260004403024843c0784502c001c0e4080302d1940b8000600503125031104d4221070306282c916900c00005070840b40f2429480040c03004040303004402c0c1d204440003482000004500e507082c5005010310030b80003070210b82085894525006107038032070300800d104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 82837564 1250 82836314 82836323
    0x209010f030f0b090f15030606060d0f060506210105040501030f02040b0d06050a0c021606020307030f1b2a0b19020c0d05150901021207050c1603230c03060103 70
    0x2c40e0032049150300018801c0342d1503160b0000000d002d00520070703031000d441d9200d12035882c0d0742c003446901e0030109540c949044840f0380e48100100701d10b900031101d54104856014807600c01040c030644800003d8610707000f0032101380c64101c6c0f0800e400503070080c40640d0381c0140704c159010400c40d411034031031400d0a041c07884081e0060f900e400c484001515011054200e07a81c01010170001c600b4913207001c0c80a00f0745104070b0300040c428240ca0103c1004416540011980950019445c04415540540700301342e00303500d82e100340501244501c0d5900003800207402c03544d10030380c1c00050241c40300b042c001740700c881d000712086543d104c100d0600803103224100322840254140842c1c0302c9603020500491801c2a010202904444a942c034001089070018004204504800704000c1554811000e80d080740108801c43d484041c842010482050040d0000e000e094410400e80d0400911039450040002c502c0d40102da1000d0344200d00000c400c090400c40c00a092650013920310090f003100000d40d01c04041c0400750 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 82838814 1250 82837564 82837571
    0x1e0a05010e0f040c030608070f08030307200a1b1710020c100e011515080105042c0d110102090d15090507030f050c010e0904240e01020415030209010f03 67
    0xa5069039100403909020400030700034040b072629000001d0241401348286207c034821684c001c5440c03103441c0380c24011340d1500e0000311b00f907a4819008540100b0004200030500c0444032511000752000e1103e43c80d258010000005c0e45080c21008002c942e80903400811052094298150110008902c0828006500c007016840d482c40410f01d030709205c40007200180341407500c070342c866042c5010f4208410880d0307002802d101d02c0341e0b5440008800075404003000300003250500107000a152691004000100e2210744804000c01d84051400000f0703044e5a05034645e000f14100300781c8a0b0b000107100720684082009600b0210742c80c02049841d005440010462101030b04402c4005843ea40030384401508079045801141d62801d0418503280007000556050240602c1c10140b03500500700d031074805030090420341403a59907450702c40b090690003c9203025008801441e550a0700309001d6004480268ad000595171071620b082c10400300f0094401c00f060500600a624075a030300900031403505000d604011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 82840064 1250 82838814 82838837
    0x5030a0b07030e100906110304030512070201020706050c2a121b010c05030f060105030402100c0201030f020406090524031605040305120304020103050901140105010c0305040f080a021e0a0501 84
    0x2c0d80a01884941c0741014030400d4009030146445030440341e1414002c01081041040d0701d200d20300544405c0380c0190100710300b006081304c5a60044502175200c0c3e01840018104282d5648410035504e06403411489003e020400c10310449040c06544942c011030301d50f0014904c1c001260f55141d1540048a0041c51000f080b1204041104c0c5401e17510703c041e481c001c000350882c405010349a80c100341d03580310790b90740320300000746c015402401100c0c0a650000c100d81c0d95a102028121024500701900701e0400d80c468030f5051803220140060405015540c03070304940a828142800f0141780080481c0103407160140d001c0328190102411241c02800b8143c0d4401c40e0700c0c41000035641c601c242c0c4d1004282d03110b01da42c01711600068401941c0594403d90f420b21060b21002c180900361500651050415036150004120f1036015490402c0c1940c801d0805c981059580c0c0140e68100784503512421664001d14075490441c582444480040c021445850622141420114854800754050030f412321201d440706 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 82841314 1250 82840064 82840067
    0x1009060b06030c04061b021503070e0a0e070e0103020712110f06010305010b0f030d020705060a0903150504031407030e0d06020408060a0606200a020d0215070f0c05010905030a0b07 79
    0x1840321100c0903003000e42c1c81c2000c00d0b008035141d0051144000042e421081d0708140f03150342c1c18408440340c00405017000c80681c62004021a0b1018114605102c45c81140b41c007180c4841205100400d005000010603161030384000e46405e020700940b9041600c10060100080c3c1e241070b4101945c4941e2406c1007200c480041d6043c42c1181c3c00d45c0005c145d219083c0000100881500a804170800a89080e6854a40001415900c0090b002d1400158105d0141804a0b0030400060845401c091504d41c1c920740c0d0b2500d41d0000c80107034050503010140ca400803c801e054001c00d0401f021480e11641510340b1545480040c0303040c100f003030100d1281c0c4260600400380075860701684d000d00000003c0c2c03102824009160001400f062155001082c0c154148195003910046040100c529580180000c401d0315800c03c61000001e81080740c0c03000ca444440d004411032100034003503480c400c0b1100102028a03050150782d50045501490400c82c00c01403d028075100403c0d2134094580c0b003001c5151940f80d0000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 82842564 1250 82841314 82841321
    0x91a0c04032004180201080a050606041508040501061409041101020a0605091b09010f0509190908040e0f040309171005100611030412121103180f0a08100906 69
    0x301030621055030340d00803918074100120b0500350030215020080318140919203000082442c1019012580c0c49000401400341031300550f52004000b0800d5180c03641b103500d5007000c5d540c050b04050029140104010401c2802d20500000d00b2000704800142d11340d1a0009031890b4005000501050403489020b106074003c00299175060b0784400107021320325040d000642c4e5915001c060000702103c1c002400d0b8941043d41e0314a0580740000e042020440c10802030240a50000d48070400b000940785514261900520460600d288180c0075190354520b01105106010720140c01140710444500038000041e0304094003000b1210b20740c028140c440020106181880308280c80982c0300e03400d003002c100708040d072a900c01c4199a1a600c030b86404012001c11103903a4052409410300014003010003102180c2041880507060a83c3e1410303100448203802c2013070039508a668205c46021164100034514a001284070030040410f9881c03103011443d000b22580d551220311494003da40da40c09990050110503003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 82843814 1250 82842564 82842569
    0xa03080d022a3a0507150618021204060504030309060507030204051305061e061b0102070c0b120103020f060d02031e1308090114090d0501060602060109091a0c04 71
    0x761804200001180c42d41c80b2010b0706008002c40c01460a2280c80c4526101c1c03d4402c50041101c541640c005a03070f5400007032003040a01800d0150500c0000002000800c807456412800071020035264a06040d02c559500c4010505004038014000914403102c1d404101c0e5200b0b410960114040c1c0395401c0540003826015405080d07981000e0070003501d0307a003580082045540a98101c0405411307941240100d9200342c4040360710100862540c0394001c0e461250481c4940c00030440b41c03038050f40d4061606026000d104451a03650049422000c0c0454584400002c1c031045001501c1c105c2041c0343c0c16900c1d0300502000344140c0c562185110507442c2d60003035611b1a0b0220800b107603030f824203401a85c0000b40360751220052000210008403d0b0b02032200051156900040d2141003242900c015a03000741813500c0300e140002c0506c401040c954442412410f918000d0b0b00000b44141407500007414410145c00170350010342005607481c002100c0000c68410b55054101d0b40c0082d880c1d0801140d044c9c825a03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 82845064 1250 82843814 82843837
    0xc03070923010210020711060711030a03030501140d03121a030708070509090f060a090602070204141611030702060c0708120408010e06060609010804050f030c030c0105010902030103020a03080d02 86
    0x8807038100c1501c542556060a20800b42c00300d07034107180310f420b805051b8850300e80300821007540b44050303002d107040c03410103440503034810017081d40c181c03008401091502c0e0003403000f03900194903000104002c0a103082e29424030041595003911614803600c018000d504000001c100507982c8002440308690740103000b160007038000b8162a00e59079200c0303855554000d0b900607203208400e20008100a13540015542d03400888840181809554940c00c0c4030003043c5008060300e15640030002e410059807a4400d4a8403900c00b014100f001e401c0206c040d80c544841c00105400307114190704902070003080001a00c50403603040b1401d17551003420701101401d0000039032009110f403044a204180702c0c2c040b0f002170030a640c0c3e501d000300310082e610100a40d41d42829141d807500702c141007001c1d001951048801c0365201c0c1c02407045800080e04a14045d265901682d011083c03508041100d00d1240d4080c05000e0040c29003a40c05d50655046400241a40280340300040401d0300004000030140c07000d4040d036841d803245 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 82846314 1250 82845064 82845089
    0x1005030d020d0306050d110105030709030203060703051504060812090a0e0a0912050403030503070311130305031305030a02060307030504140303040317061926011a03011d03030c030709 81
    0x40010350b0301c604106003400480d0900340b000c105400c00a0031104842d403c0300e902242c0f0802c80d00151150740c00541810104041c4807008009a1010000e0307070302840300c0340d80c002483d251003404043c4085200100520a506090081040c25030015401f40589640070800ba55629400700003140c2641a500c44d4510a03094401c000441c0a40d0340200105800340104070442ca2010340203c0d00c40c17007a408000c01280b000c0c400314240c18402c0d030000031a007419000841c5400364240c0541c944640d59401200c0039400001c030a01b8508803407020741e004000a50090080703011315070019440e4000200002c00b0903548000007014004107901c80340c4031610300c00980355642401c0c24028100d031503184600185001d21400700c0c004d03003865646009002c000403079070504107046c400420300301080c40c01c540c2081d4200e04145601d054080c4282c0c4540d00d06c80ca0116040e401600c181404c0d182820710101c41d6030320714011100c5491010046942c8010360b451643d940b541c40c403000b6030700c0f50f10640200c29403260 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 82847564 1250 82846314 82846333
    0x9090604020f280515040f06030513022d031f020c150403020c150306010f11010e030f070203010b042706061203050a0215070f0c05030702040504050601031e02090609100503 76
    0x10124180f090b100b040d2076016500182601404043c8154410000d008205817402c12480d03100e54845504107482040c8603150303000c0c54000600b00012082002018011008060b6a02c1004054000d0601c019030180200e920304c00d0804496400450700404015000030390700c21114024448200000d0205604051034102420000c0d5201d540c45260380c081c04500326405061506001500c0c801e400582d0703008000c0020341c504552816064220403095034031201d502100c48000e002402c403ca2407180e000d9111f82540c010142903880c503040040c003d40c42c0003840c05100110022020b021090b84c00003090541851401034014000e030b60108030f094040301322440815a00100500280099030b00701c44800c0364241e80b09000b40401da80c6140400d400b2a4041603040c02101840c48440c0260140c9003000c000d0380108045d20003c42e81112250000c0005004020191454845024200d2000c146030003099002c90011b50002e840140709a20081c005501c85c684210b801000d4400502500e0f200b0700c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 82848814 1250 82847564 82847629
    0x6040504020318060906010f03080a020109080408100b090f0f04080c1507020c010f0206070f02013e03060904060506120a15060e06091b070c0605030f010509090604020f 74
    0x1240500c4040f50f00414003c10080c0c900001d0702030681700c05020b80050b0900c1c40e038901105034000703100384d000c0d55254208880842e0003440a84002c1c10800003802d032010040c0508000c490300010901d1103038038540107000315404d0345a0981e60103a03010512200c542c4075420a048980101e90444605201d0380b00d40e00b080440d20740c00c45010780f4564007101c0d40c0b04c0b09480152200e94462080c3c100503030104000032250751152003540c0442105000000e0400845860083c0c07100c0300c5104e14820705280d55038401c40100c015281d00c5c81548c800b03d420f05606250000070880c04010f400038000548074800310301c2595a40045d21405c080790b00460b05002d169240000076800000a60300285103007401c00030701c49aa00c100240700d800020002d5a5a58800c1140340d480b0b4101841030300d138013100340b00500000e05000c00c0c000c0540225101c0030b4503403804801185055005801050003264004140540c8640016070300c0e0b00240c0c1160064001d010203404510b55080d20383c80035414070107000c00380410f0b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 82850064 1250 82848814 82848841
    0x6030302010b01121803050306060723060907150c0311160e09010207080706090c030f030302040f050609030a03120f14060307060806030303070c030210060303020c0901051914060405040203 83
    0x2402038071045400200d6070340c4c081c102c0d2155890084404480c80c01d000000c0d10901c015580404010032442c100100340d26683d250080854005d013001110481c501e00840041000d5580090034800409490741003200d5a4030041b03035609030006100c080c1341070340c0801d40100709a82c849a02801124504903c0c0880041100f400784149032000411901058040006000701c0d64521341001070145054202c1d03583d580286a1244d094400346410700e40400003c03c0c881d1999140d074065500507850b030b410001d500d03209070000d0b80418841e5000700314070842c0d42c130302044c01144580c150820425200102451a0242104140c04541c003440c012100c50300100c04103016003d000154211a98107850359010307107076000241d0f20317039070705600c2030001401041c894029003102c180b007441030350300c50341c40c0810302d10684480b43c20880c00b5801c19281c440c0b29003008001c3c180100422a0101d032900c005105600c601c1020340284240701c0c5260040484c99140e40c41214000c25014008660b07030b00d052401c0109a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 82851314 1250 82850064 82850081
    0x17030406060609080312060f060304231c18050301020c010204030302010b090708040f030c1a2202130c020a08120610030608070509060315010608090705090f0a0207150603030201 78
    0x1481c501200814010710034000b400a42e02400000d500e0402c40201c030f221100c200802d902da12000c141c980100545518000d035008921402e07520b90111182d428640f6100240b40c0196480d62040d501c0200000941d40c5000070090380b418540354102c02d21050344c00c1d41c0c50503008103801d9800064440c804020550041080300e00990013001040008800c00c071800609840100c0096114000720b008150840346109466220342030070185581e00780e6031070b004004030100300c221540c69401007004d20703240c809007900800007150100034182025400607045001900d02e18001030395440c40c1003841802000007081c85600510459111000c911202250f50340440300705019501d0440c444c1c154074001d005400540d40401b000d440110b040100f400102c5100800c04c0780c2c10710070803001e404000104090140a00400e41d102c0c042c525100d56481d1400185500903070042d510ac0d07040190070043d4040703c50f004044c0d034201503034656013402e200035401540c0340038400386464498000100f540540c021440e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 82852564 1250 82851314 82851323
    0x15030302071505090a0911160b1605070f0b060109030c12030f0207060c020405100b0c0a03031109130c020f070608060307060309050a0204110d02120f090705010c080d020403170304 79
    0x51411060b0085915000304d40040e9044190202e0902c040382c100e421062180c46860f0f000b0f4201059801c01c200c02500107241070301d00500d040244020580d02044a403064482803c019203080725070fa03600300c084610741c50050203107100440451416881020540d00440c0c01c001000320081d00c0380c0020825168094048021034030020700c0300245400450710384221038054842d89100803440d0280b00c041c1c030b0010000090036a0914000c215600c500001e0034641c030750b02c0001e01c0240d0303c52801800322030140400d64000c0d07005000c07880203565602c04004045110840225100310a144180d00d4800b03c00700c509440d001d200300202c2e0701a031040060748114000c07000c903043d50340e4809003a400c8a5856002130400d411900d102030141c1855000200c9200916580382d00c0c1c5030414540d1000c980040314a28548150300081c400815202d44059400020a4003d8206a45000d001a00c00f50390210005c1c52080040f80102034803206a040d0b03801582c202c10b0300321041070000c100d40c42c10383c01110200e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 82853814 1250 82852564 82852589
    0x20c030d090e04120201021b0c090603031819150215010f0b03070e0a0302030f070303080612190503090a030605010305061312050d110a0c02090f0411040f1503030207 73
    0x40d00345100d18012421070340ca122140780107840d035884040c0c009001d001c0c0c0764207640d0204610720090040800d440c050344035040c00707440d082080c0c90800210540c05801a07200e58424008009074000003480303c0340004007112131849400301c070b001c0c054610390103900c4004c080982c501400384858020034800500f51801081e422142c1c1c03582d0741e182d0a10014001d45c81e250006000040a95000d22240707440e241009002d9500c01355a0740c0003e01d0032075000d80807011504070083c10402c0540100080340c0010080300c101c04030b03800480b4025900c1ca100003408a81030001c980d0380e81030010074000c07030316a078030041d00315900e042c0c8070308107038010304001c0c4401c880c64443c4c040003500c5000b103000000a06541b2560300400fa44145804441507000422076207015503035080294000d0104030010168034140741c8410510820314010004c0e81345d40201051580d0040e20104000104610782052803868210740025480304408001030007040c05284402055600d00c0e408030602d5000240001295210344d03889 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 82855064 1250 82853814 82853833
    0x2030a0206040e250518010e090109020a02010605030606130c0c0b040804060909050405060f0c0d020403060b090601050c06010608040606031a150303070b0c0306031216020f040507120504170703020c03 88
    0x118400300c43d0f07136100700028405100c20034441103051424403194005142400d42d00c004200000c143d14001c4e80f0201d8595800181008403d40a00a10b001800c048020f000d0918004000c070f81c0c541e807120402c84044c0c3c0d845412005690141e500f8490094200e40903038018a41413404484039801800342c000803170180b840010305500103014040c821940200501f49988035001d44a0900d200a0b00c03644481314140850a00c13822180b0190008500561010070803502c1c210622589507400303004641001010000c08600305000102d080c1103e0700c614203040f083e6101d09013100101119007004051a00121050210410706003542e0f014041d00403c03501502c5181040507034910940c1001041101400005400d400d003650186a0105014060310525041004801c029a1240200e98a0484520f05c0b000c15800e1042000702c034000240ca0800c40da0a01c50000b40456940d1111b0040041e1900300040030800000c151103030704151007480c0c2e170300c40039280740103510382c40850341325801780c400e80c50030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 82856314 1250 82855064 82855111
    0xc0304030b011401120f0f0903031517060c0a09030f03080702070f1a25030f1107061b0f02040f0c1d0a05130222080d08090d050702030a0206040e 64
    0x185143c070360584034074040c42c40781ca2a0802410049003d402c01c01c0e55200312400c0300d03903540150301900e80b05e0782e8001070040b05100142100b1500360400303059191a105071002003180021201e40150742c04541d00d07100c410005040f0354180d1036400050443e031440c078641c0100354014841500406041d000e81c1c1442d03881d104007907610482445170584040e03201c10441c00405160000300700c044054480c00c1441d985807070880a540724185c00c1140016000348003401600e0307101000c008900c40e5040a080c000e4a859001050035501207000620380e0002d00249040003c0100e410030984d5016100780841119410102c008010319072600021650303400d030704c0300114416204075207180c100401d8022820700304000d01c00d02203000c0c034002c019a80e0030003000e020040e01f0300c42946a002d140381207220082c1170026075400c046894000a0a200030b000c180b0160f41130206442450b0706940c60314507101d0400b800000e1600f0724120020b5042603000501003045508124900e02c1040c1100146c405480c0700c892 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 82857564 1250 82856314 82856339
    0x170406030c081f0504090c050a12050d050c07090b03030c010c0e01030f06240c140a0201030f020c070302060307020a0c080304090b060309070603050a020403081c0b100806040e070b0c0304030b01 85
    0x48801030f07a0b02c24200b44454074140d40000b094501070305002c0000c81c2c90780c010903205120394020500000e600d0302805d0030400204000d5107070904510b03005003448880b0942c203503262501d01480c102d0070b45560480819450800a58101d401c0c960000d2080b00781424014000481b450034143c000b80c10036844180d02d180c03502619044503030340d0f03000318558004002503a4000980711810000c0204600e040380219041240d1402e01a0148000c0c3c400700443d44000340440c1d82d08070f60110b11a0050000d07809038007002c00e001c0112501078501c0d940e2503035100320803070800c0c1d00c840c0001d0211043c83c4010400100001c041c1041d20755010b000c10003103115000304074503404100c03103240303035544260014010b10380301e600061b4008201180250606440b80e503010441d070401000402c003101c41c1031440d18030101c280200d0315422800c0c2e03440710b1004041640100711120062005025039240c901120042d6410403080004140d100241501c5a0f114840151658803034401652490407030000400c20000295 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 82858814 1250 82857564 82857601
    0x60b0d020d08090a0b04080c0a0e15040c0201020919150c24020d1e050a051005010302090a05030105040503040303090902030106050d1d06010f0e010914060d170406030c08 75
    0x409814120003159140c050300c1e800003d04a8000703850300c00001d0748030500d81c0030b8409049248082c0c00900b400600b4801c04020030341c0f000c25064554810300406c40104206003107000c0e000d07240031441920504080c1d019125803816035030050f1400380d03840b0751600c98803080340c280c0303107a06141d00b60460760107802c039490b00807880003500380015080b03440d001d25a800000c80814044000150501c1c403245c1194044410801c240c0c402c208082c002416071803880e00c0f6080c2c1c07090011604020b00d0030800007802604550b40580c80c103140e40040c8a034000c0e0f40303001c0c2c184000d2400074002c1c0074600d0305140c165100d41042c0320840110b00b1464000c600c0038107074000d40b41078640d141c3c4e4130b07400c1000a5942d00c1c05050240b654500301d05951032811882c1e04140301c1d05010340044840c075114549000381042d403009050f8400002a032500164401501e020102903402210481d0700310f00f503108a040c030151980300156185981d0400281c000380443d05500314055001c0d5030349600c0c500741c2e290749140402000d002c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 82860064 1250 82858814 82858819
    0xf0102070e07170a050106021e03030a021b070602031e030103050c0d030302070c06030204060f030e0613050f060406090b150d081b0102030406060305160303050405060706020f0a080103060b0d02 85
    0x1000280320148154500d2644100c0b41e14201c02c110155403d04980c80d030080e620358116544032030060180540400c000070f0008010410080c4261585003000c1d1240005441048802d40000708250141d074409000d2204d406094243c46c0301941c0c4000281d6030358044240b0300302e062030035103424640c3c0c1a45015a41200c0d000700281c00091050020071240c0d1450f90011401e240c3e09000882c0840c001c090807070050032483e01c0c0180c0da03904044014040f1805034180000705410a000c0303d05083c40401c0181d000341c041c16160090920901c0d103d41000d0321102a940148500010801445500e4210404e028090300c200640c41e103071030313804283c5100241d080380c0d00002c55103081d44c00030b82c04200501c800c07110f0b01c48031041d60007216109402c1e60320a650540c1e8403500c500084c400c0c80001c0c042c02084501c10605036503040c4c5543e40103801401b4910a4501c195030201c2c1905c1031000c02d40480320b0604c14051042c0c0c1d41d00150b000034090003801c3c08150b03140c51800c0c80010032800c140700303080c0005800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 82861314 1250 82860064 82860073
    0x40c110303011a0f0a0f0e10140304050c100201140c0421030201020903011418010c140a03020403080a0c050c0301110706020313050f1b010c02010f05090a0519060207050f0102 77
    0x20300781c1141d80c039010889110100700c02040440c104540040207443d46083c0c0c0c6d6105400348a041c1c2d030080c11480f8a02c4810310581d040241071840e2500441c4544141640c860019180d40d00d0b4108603040c1020070191030341114510102d517030801d6040d8416078844040342c0b44900e0585511901540c103006030300070480e14420b0004245201030a20340c0504000c2d103e4030000d40b030300b4040c43c00300303094070407841c41035281100317030740a01102800089407503035003962031802008403403d0000020144404228035011081c0e000650841c818072940481e03018541000b0015030310307140140010b1260040c10000d84450060600306940c5203418000c001c0c800d1481f44880381000010b48412000b98000380084076100054413071800002c80c10b00c80484480c2648000e8103004100c2c280c0c1080ca0170040050314100150b031940580141e0300400000b0b00c0020303901d0200d4444d1645404614082c030990015940018040a107544d100aa00504001c0e40c2059081d00d182340e80e6003003441000700d0031307a03030540c0560030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 82862564 1250 82861314 82861319
    0x3070b01050d060902061602010305090f060609190501380405010e03070302030708010c090602070503060f18010f0204050301150b040e0c0d2906130e070e03031305040c11030301 78
    0xc062004121882c026040050b1341301155000488952101544038000c040d50b80034102907681503c501c0340c1c4044550064200c1c418801c2485880b0b18006241511400c24039000c2840c04804002d11000003903a80c400b04010b5031107642c0d007098240141081c030001d40f00480b2000070948500f1051041e12005c90803142814140b200540d1a034008a2086405114180303000001da60208078110041c010000001a02d4020b041c008001c50001c3d0800c505640c41004100a15200001e0043d8032001c01c0701510a07a40303c08102030400c1407251920f289079828000307800c110644039402402100d8084000708807651400c46943e070948141d20035040d42c01802c2c8010810529001380081e884851071882a1030040f01c089003500725140e10f165030009080c8599407101e01c0045041d0b003240008100c2c2c106003480710b000d02161b056a0301b4041c2c0407031040b1000100b07a289001e54240051040014180c07502c50784201c1c0d2000c0301881070710585108600300b0100c0700c6070600070002a881d50f4042400f5510f16030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 82863814 1250 82862564 82862569
    0x29010611030d060308030723090603070302041e08060106020712020f010207080a0b10050103050405060412020c0a03060e071202150c070b040b0d05060108071b08040e04031e0203070b0105 82
    0x240080d03404a0540000c0185079882aa54402c19010b580304442c0075861382010700c0c004000306081c0e085611b44011507208070b40d1451400d003c0c0c0b11107070021500c080e80c1c0c1d690785800f00c0290181d070340300f0482d8030842e01d030452414400040400686242c503007219020383ea154012aa9442d5a1254030b040208030803500004d802c141581ea5085c0b0b0301030044409146c0d69064071880d0011400c002d4031841c008001f8803503038121205a40f40184400d1070140300c241450b0701ca4a881e12f0000c0c01c000c0ca1081d0130b100400241d8000c1c0500462600001c2611881304c0d0b40341050b1008d092182c10007070450094003008912103c020261030780035900580a400c07141200020400d05500a4681e00c104d4402e0a030300103040e014400040018208550707105484e045c07079003580c1080c1c41029140c00c4c10301a001c820054610b921070044502c451400b078024410071300b2410080340714821900a80c1070004a9010842030640240c903000e0340098010125041001c0c40000300d840e0300a0b0b5000500602048004200e00e1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 82865064 1250 82863814 82863827
    0x2030c0c030c0120070e100f09020f090d0203011407030e10090302070303120e0a031106070e010e2e03090c1e06030209030309030a0b0a06050105030c0304120c050a0b04290106 77
    0x1c6804040f03503442501c407061014250310032101c032500d01540400500c488c111060600c00201555441542030400e58440b6030000d00402108038041c1480c96804011b5540035007103204e4a26021801c1c098900304600000d000d40060000445c107403043c038062607460a900d100300c0c001a90564080c10f5042d08603502120b400d074002d40f404c0d02803500c4a070001090030041c005a4078942c42900c071110408261700a0030b0500c500105a402400400f410446060340c0016050040400c00c0325101060f1f402e180c00b203502c6281132109403079030807001c2c03c01c40c4189400d0b13405168800d014114042041e542c50000c10301e0b00b01400d81e0705400311a0000100300d014061f4028000550005003500d0400340541e02080c90201000c03000e403403e140440600103252040d22551019080a203480343c95490b11038201e80651001400c000e0540804c0c2403a46116403058440c4822603a000703060350000001e50503c40d048400c2a82e09484002032880158100c01e5001c880341d80c90884120140311580c80e00d9810703540e4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 82866314 1250 82865064 82865117
    0x909040804030b0c19030c0e100504080105010b1206030601140f040905030d090b0a0b030316170d0203010e060d020f0103270819030207020a031104060306060602030c0c030c01 77
    0x80e29080c080030000079901e2201c0ca20652250b00e0441c4c40d0400303d00078440001040d84e184060510700040c05d07080d103078069078800c3c0501060350100e00c0301c0c4003c94200c80a104e40d500c001c2c1c20b075182c0800803e03260346140007422803a00302544080c1d00c2c1c460200b0540c41d05420701c82c002c9590441c891030320143c20080c203000ba00e49401800001d0710003a54641303500f141d108007500440c035075172038602c0010840b450240302d42022885074100076080034600071942d03a218000090907540e1481d408070301001064081130019040340c0b054191101c03180000540a5002809000f60031040c010003d0b90a003410f6114000280c0c008104040013203d200040d002072506124010104041d0725000c50304408510a0180c424450850a583c0710b1801c8a600c074075070b001426810400d801002007001503a22a4146802e40b03030003d8a0100c503000c0800000e00400850740300401903420240005003054000c405084141d010340f041e0341d88000104c08040d100d81d9140303031041c081408000003000c40382ea25510084c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 82867564 1250 82866314 82866323
    0x10512030a08041b0302130c031b2102040504061e09090308010b091305131a010b041701060911091c080a050a0c020402030f06011806020606090405160305060a060515090904 76
    0x2840d03206d40100d081c1c0000f494054030120744980079a00c2c070940c0b41c410041c610903806045003001405000007070110300c13084607140303013000110381c3c03000010b001d41e0444004000003002003204954442048998600c16088000800d09021001882d15038a02845d16944e5043e901c18583e0b85c24600000701ca0b401907196039400144a500c8520720354a00d12440340903d0001012500703c41c1c00c2d140403481101021005020340f03001c0e100402a40507501c09072410384074070b01c25040d95040c211200d20b00400f01030b402100840d0802c10980e200c02c0c50f0300018005075006940004064040c861125405403545600030519081000308041162080c2c000c2e1640c03101d2441c000d01c0540d84d03600040c080e41c1007035603641e203464a08804d10149c0c1d1380240f01d400e4900f01d03800c1204c0c2e2052030460080d4868400074500b601800e0964002000c200c42805000480c001c159100d8018940381c0c14030568860048401000e00342c5003480124003807804500e1b4003820868521950700d06800c40d4140494004003500894 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 82868814 1250 82867564 82867613
    0x70f03020f16080c06040b1b0f0712030f0309020d03030c0210050117011d1c09050301090501050106090501170105040c1b0302010207030206060901150c020118060503010512030a0804 80
    0x10007199060003401d90744100004036444580c2400034003403c010319600c4543c403c100820040001000c0e0200380c07150030b145907008034886e441507041d075820805d02c650034440031700400c2408100e000d0304e22011004c05000b42d85100068048040980c00c0b91109400a588005c1c10701c20540024400e81041e144070740c0b05d00c1998081100714100c05c040d82c9003030304041d5540c680c200480c0e0501a00748145102483d0002850405100d6400d03002e03143e44418501304148281030482101341070194507443d0040801900030070030504a820704d140203250038003c0070700055416200094a41c46020600c2050700840d0014610340d02e06001c120017044004100402e204964040349105103002c00420f0400303002e82c0002d40c1d2506189402800d080340141254407d14481005220301030182040440000c1345080068101340e103800103854081100c1641020b4461251707010414030703800300203141281e00981d8a021000100240075032030380110180003002076000c00004001c540c0503880c012a00140c0581e69 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 82870064 1250 82868814 82868833
    0x3240608030f07021503010b03040f06020f0a05090a150f120908070c03150908030f04050c03030c0c01140c0c01180807090c180b09040e07120c030c08060903070f0302 73
    0x681590040c1c03104402082d004590402582030400c100c01542e10a80d04240c42c41d030501e41c118070306020280000c0d1940380e801c0340d603908205444d4100d0f802e100684900380d03180c01c4410383c0200180e1103007144500503418060000b80b4465222108401c40c801511000b203005200101190b024468403001c03c0540d403501314010210b03141c10010440c04e130041302e000c07141030f0031410201c0c400b840d2203040403d118075007480400880c840b1816240c0050b43c000f4250a01c6e2102e080c101d24100900c018241d041c04001b5528022080001c5d003200c500100781c03030b895041001c80105004600071490700503501d4025182200725076200f40d10140c02e06c220941c45118844d101e4408510304400f030707088002503a540d20340400403942c00c081c0c1e040e819032030901e8600b4450b05200310701c8218042c2c504407500454880082e00311850040c0000d81c050080c04008a005c200c450030140301c1c0340d000b4441941e07903403404240842c4e01c004c00310700c6038400c1c0700c01c4008624044140e940c440501c5400344041e42103005000300c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 82871314 1250 82870064 82870079
    0x312040303050310080a05030a050a02100f060501121e110d0203090114010902070218070909090b0106270e0402220509120408070e0c0705060c130906032406 69
    0x60800345000755900d68482c0b50101e840c0d015501184c1041002d5808a01c0d5800059400002c9640c090b0062070050b8442c465601c0a91806c20301c541e09265190801e031003a50320716056070008046840c241c0e1540c88101807030078564111824030301c030060b6007405201c0170310f07690b4241d400070248285020724240c078110646c2c11a20403604140c4030f0707017610b035140c80340303200400001000030b400f42101600c03c51070300209900003490080b2110105400c88003000005a985010700c110400030600c845c4240100305003458001c00d0fa1100b40a04004284d01d840c4120340c0346902c400a03405100d03181c40f01414103090001c0c03025040c40c0100200e074883c034605105010210320010b00d5059900e84000428030b81040803d15081c1310003041c4085001005100030000040000388280865040550819103038845141c00003491050343c202034500c0c4103070000d00002c4403125008040a60080e003c21040c0c0c1d41700c02c10300301601c009100140100510412035103030201c1e1280500c1003102e1144001030084d54800d031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 82872564 1250 82871314 82871317
    0x18060a0512010506010206070e0907030b0604090c090306060605030915270a020f0603090312041e0c0e0a05010f09020a030e010519150609030f08090d081b0a02010e0f0312 75
    0x1c500078242d46910502885580411105130400b201f81404404440e0703400125445c0c0070024450070425488441d03034411a100d034800c8a0140403205024800d081c600417024000f441d5611048130080d240c2000095141e10440c00e5900488460b0007038100c130003440c18400d58221001d88100e0b0307081900402e4440440f644041020500790240c05485102c03080e004101c0b204404010190241d68100204500f42c0c1c0c0220468043e601428401650758603142801141141c2c1c2c0b5050f0000c60f402100c0e640248000000c0072402c0300c0d900460380c0ca507a5150101401903032000e106845075803441d080b00f84a0381c0d515402405000c58185800540f2039605886103084d64825039004c005901c100c0c0241540c907d860058210710f450410035055480d14000b0000d000843d1381c40083d00d99800d418070141084442401c442c03c0c414000d0001c142c0e1074460600708010ba04c9840150746c800c400021020541c03101184400b101380c0c0584407e04541800d509110404540f150402d070f2502500c1e40014802c09183c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 82873814 1250 82872564 82872589
    0x50a030606170a080301051e15091302070c030b130b040606060f0503040c050d0503070b1f05030c0f0103020c07050d060c030b030601030c0b1b01021605060a060518060a05 75
    0x41020841c0382c54524260a048500c00001a094000318002000f1640b0071003124116078040d240c5540c058141c1030594031810784084400da0208142440520001d44030001d8000000215203200c81c2c4d40d5403000e20030880c45000001030892540d8201000891a007011659010584155855810041c4c1d950004100400c580450706260348180c28000c0980c800811010640d40f401c22520b035040c5a2915a440d8085114481c400c660410300702c002c02c8000d0041d14000c99010100c1c91082c10100001b0703e0031115440783d245000104000002c5a20300041d0b40307844000d0140c45540403628035030044000e5440559119410300c118580010307152034403001c1d010403d01038000000ea40c80c6280005054941710410244207510550060010410b2041d02000702e0340f0038003000b903407001014401ca500c400042d84036000c0e9480460000004509502d26048042c803600640b48a90354075007207401140d19601900303800041c2441b06031419002015401c1d04503000a001c03140883c2c1d0340300001c80514012 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 82875064 1250 82873814 82873823
    0x30f140a110c150d021b0706020601080c01050a050a030908041a04030204050a090305040909020d0f0807060509010e100b03070317071e1106031003020a0902040815061804050106050a03 81
    0x34a00010072000901c80120010b5044904a03c040c2e04981c10325610701845441d2001c1d90750008083d1070580ca41206035590046032815036032419500e180194494909106031003884c043c1c1207549030550310801c22180d0140f101d0319410b0030040d030558118010129164121040d00701040049001c402580400904500c0000c0076691a81540706000030b41f4400341482c881c15080c0880c030000641c000e01aa0103550090200080014803030001400c0c42392140300180424801119140510440e02d0007420aa40a03803010702c45500c901c0101822203408008a90141d009241d560280c2c4485810445414a0090846040c0b030b80700d4640d0414400440c1d030526000c00700165500402110200310031040748421204103c440303580d02ca002c400f0302e00380d4405124080000c0040c00045a103030190001e150050943c1000036141d201d910002c0d840b42c090b003032052291041282c2802d00000815104907400b8100036014030010707200c078150380c001520444040d5281c12000c113050312803940c44002503004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 82876314 1250 82875064 82875077
    0xf090f170c0315040308070e0d0807060b010207050307210b0703150e06060301060c020d0b090619050603030403350405090c0304030c020f01050c10060302011701080a030f140a 77
    0x511140c18940400409968002d03040070f005011140c250b040090703402501802d00b01d9060343d810404542c0e9028491030941d010300310010380d00510002c4005416070b60710603103041040040384801641c1c1c85125101d82c0c0e83c141e0010320140034540c400720076403408517400382c2008000030259031030383c00702c210407600381c00020f070341d034400f5880c4000e01283c02c4001d202a005540103820510049540f07448140541411b110910312510119241c0c2c280c840c192a4200035020954103200b1400341d196102034440007a00c0c2003108c106da00e9010741e441614001e40008008601d407614540c1c41c0b203c441002d6400c20000f010580204a03400d5406035a0000d450303900341d10a0307455040c03a0400c00280c10151500c024580140208000603030083c0c0c421503255012640d542c0194404070040b81c240c03045100010490107144140d10284140b9048441a40d100340c0701c4481c080b030780c094884d5824000348140300881d0b021202c05004039020390400881000c040c038242640300074104460b54030b94040c0000340d0000f9078 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 82877564 1250 82876314 82876349
    0x90a0e040b011e0905041e060606030501090e0318010306050307060c02010201050109140a0b040605040c030b040b03060702120a0318050303090d050903030a1101020706050f1504020f03070f090f 85
    0xd0000701c041c050b10f601e4440080c94040b50444182540503401220b40700c1c0d5403a0040703003d020518840e0059043c04c0d0132031200c8501c0500e002c202402d174500c18080401c0c204000401c03400c1c070310b010384544442520300450414401d0300d00b0221455501740b07003e0600d0303580c030004551900d0500a03140585580d441c1c1c0095403400b0b02c002800c5510503071100036030b40d140c95070310b103020644a424a90007a00702800410880075050000e40203200c558480c5501901c0c1901c050081501900800700445013201c1c2080030310310140905486034001c450800c0103030458006460000f15200180500c80400d04d400174050154286c428080d0901201c240c40c2d6074000b0040080b0100c0800414030802c80900d0554140035013203002c81c0e500d00840410409109035401944400c060035416247c445c0d4004c50107010721308044030116405a010380722100d01403054003019180d81014021540410080c0b40503d00d140c0c4e40c0041201c0d4098240420070402c4000300c400100001424011030207007681d90b440181040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 82878814 1250 82877564 82877573
    0x20d21091a0c070201080f061801270b060a05030405030c01020d02070506100308090402071e08120a050105011205040f170a2a0803060303070c0b04030b01050f0a050f030102090a0e04 80
    0x7070000301803249101c010044440142d9002e189150881c1d44071031006490740303902002034010700000c0e03c8007440c51903c000005201403480036026001c541c80d0100c50304141401d440c10107461050490703d4004404004981883d440707480250341c002c2c0220245c0c0e003000d890b4074a40d400c2e0b80c41980007108a94000c943c1d00e060080030300600c2e4105840030001e0080c245559500030301409004d02c118415540401c04405120b030030700b5019019115051900009449032414900c150020110315103640b543c800081c62140840c4100b50603914161620303081c0d4002d41c22a5400740070018011a888400004030100080007140c0803a422246001d0003516580445001801c0c40958005c01000e1800d0788201110710f4040404140241c3c0c111030010380da40e81e204040b0385140f242c0341d00107140b440038107000a4104d0691024005407840380c512103149907640c60070040a2880160341590014026100300420314040c1c5410880f8403001c2c002504140550000900f034941c40e6000d0146d00030304104000402 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 82880064 1250 82878814 82878863
    0x81c1b0506101508220212030c07270f0f020a080a0c0201021206090402010207080703031706100f1206270c03020705060f040510020403060b030601050a06020d2109 72
    0x4100241c155211a242420f0040803008060509015007911403801d50501407038907030350b07003450b500038080c2c0b000000c0010200e9030360381c05802004d402d8020041c0c0410f075000d0a0740040d041070440e00d42c0901c0040c0d2850b4070401400b00308240d6801a40c0e440543e0750004403400030301841e6007076440b07080c45860a913803010706a400c9106000116481000141280e45900241c65000f540c01d591540142c0e4807440140d1500c0303096004448940f00e1450000300f01640160380380ca01e2404080131148680b0b8120138062090441c2d000c000104d15400307420a4942c0c0708074000420100c0c011000b03e10141c1e10301003100e03c0342094003040b0101b0f1080702004084210781c06490f00a0400c0c1c80c045240202c580c450310348804d001b07801c080c3c0440000c0042014007404001c08031302d40500328000c41d0b6960792460610024140e20010340d019006041c000075407441c04044000c00c139405078000c1c02400590341c200301c605101d01c4905500301903070032031049071596807881a107980318440d4107800b006900140d04e9a041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 82881314 1250 82880064 82880069
    0xd0b04060c020d08160302131e06090f0306091406010e040c060804020d081804020d0204050405131113060b0a03051e091f180302010605010212040b040501110307050105092104081c1b050610 83
    0x1d000800d4810040a40c0d0000f24000312500413b001650104600e40b81e450750381e900e0240d0303501e84203940000c03645c1c5880f4400e0714011403082d040640007d560705000d480303041d4115000782d40700314810791000220700950000d2440810b00a1844004172680000800f03e800c804c40703100001d80c0c00310f020300c16801c1c14816950000041c001850780d201e040d0351644901d000003011030340545584a24200c0c4e00756182c000c400900541032030b01e6200c407904007004000f0007048501c3c813005038003d40d0360803070f400101d80d055005604031009480c44d1031170003812440100008542c4807420b03994040c0081007464289151044a1081c2d00201d11146400002483c0660b008012386e08040104420000f036003001003114120780c0b003801d210380903010b10300070070b4110b015805000d4920750070301d0100014010042500707a06518005482d41454000d1b215140707060199000d5060b642c4e00082040d110040240c1c000c5641c07030802d1600208841e41c851510341d8074548842d00b250281e100d03070305100c546810454441e02 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 82882564 1250 82881314 82881317
    0x606030311070f18020a02030c0102030f060901061d1e0909060a050903180103050403090504150f080a03080105151303141c02060601030504110d0b04060c020d08160302131e06 77
    0xf407190600e500f003980c0d0072003100b40c0740318107900240b007500d04c03030090040d5003001c00311200864603880c6c04103c068181e039080f1182c0d0f100d01500c0c00082511401342d1864120b00210990780802d038400c400078000b280082403803094950000110f001005d41d9102d064074170555209004e07003001d061003030072902a66070142c0101130300c1c0c00500540e0380801160741119440c1c9824600031449895506050740c040880303400464209042003400821040819a548100d0791503007524404181d0711020b8603210740e01d080000b00001c1245e0010030161401040c4134080001c0b491080f403032301900d00802c0459940c950310885600d0316504148844031400c2c0014400c0c2da0391105a0b141e00011410001e49a50340180654141540c0340085801d010213000104d070b255101400700755514115040c07142e043c40086401b00c481500b8420598021403011800040019254840303003030740d0b210003d04070341100c102d0b0200000c0503401d01c422a5000c000d030810400800050160000c3e04607014a960141c5038140c11000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 82883814 1250 82882564 82882589
    0x605060a05030d0c0618050c090a02040b220b1b0d0216180f0c030605030c06090901030314220501080a050f0c090f0306100f1409071b060603031107 65
    0x6944003c01c030000c02d54028501070102c07521900c1c091000b040264103038180550814035400070010001040e02401e10220740c41c03152070340c9019201060780300d60f0040c8490800c041c091003040c003d441e8818a4030781d0136603404c0910980c45018140c10794118580300300c80c6100c0030004580c50329003070200c10300034a01c51001c1d204e1b03004040c8580d60010301a1043d003040703926801d00c100014603940d201d0007100c0c0c8440014041101480e800401030455402214801c2c0a4030350b2041d1280350440444522002c050007103041686152000d64050f00f00c1c178808402884104080510306203070b429105210800794454440c024203100005000607401407540030390600d0f0405200040ba0400c0081d540031a2041546a85001e403802007481c040d400c020342d178ac240c400c40f81070041c0842180d45034001d039182a08803140750b0350740709049010019068100768212601c07101140d82107214050145e00480d40a0300c00035249140c0d40c0c2c007002c0320540e61042c2d00040c0c4000356080c080905002030300c010f243e0703c41c204 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 82885064 1250 82883814 82883819
    0x1812010e0a0b0601180306020c0d020106152703051605040e0a0b07050702031b090c07030c0f031b060c111b0f04090b01090624021905010b04020f070605060a 69
    0x40c0e039076050150000d0188030501d00018400e81c4510f441e8070106410342110813002c2c2c0d6034640000a9007010325400003d005100d8807901c894814030842d4102c6502100c4860342c102c2d0448141c0d640c0c5d4089400544016002941c60144011a8050401540b14a0090281090706030f078041a006c5580c01c02445a810314115007100500003030000b0b1000e1300250044580e44640c04142c40612603004029054015411030410a000b1007801902c8104152803142241d5100c14142d407043c4180b0030020302007116004000081800070014a941c0d0b44207007000002d80b6840c4200e843e0000280500f181d08984800000001c21341c4071110f424a06400030040038205502c0d5880e00d480118003040b24002c0d804c08130804001d42d03035600214110b90700030100401c10750712038040300c001c1c040751300480e0390048250b1408404d02c1d01c01006c0842c00c43c059405801ca141c4003101c9042008000c010907240e5640711400d810341c0351384600c000c1501d0351140c00555660103103841e20005883d0b0051010b88900c2d40f4039402c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 82886314 1250 82885064 82885091
    0x10909021215131103041a130602030c0d020706020309070608090d03020304110607050d02070506070809010804030311191407050a080f16030c02240901030207050304030602181201 79
    0x9182d040710889002e500c1d80465080840c003000c1283c0c1458540e039007041e0400c088800ca10b8000c40c001c9000f401441001400c0c5242ca0041072015510b501203003540d82806008a11294050342c0c20425130704080f440c00205808a006a0300425000c0e180b595000050004c42c0d0f20410003c0018801c50800d42d41e0b0349403890b080d0b030f1030f070182c09046000c0c0358000001604004108040e418440c0005140c20349519103810099964100910641c015104e201d0011800c5d10341b05c1c0644244581c090511f51030000c0c900e0044800d000090021401d0580718007803e07595100c85400b500d05402050702ca9001c80c030030f600008080592074a01754a800c902007000001140003c1001401b10340c00c05c4119968000203140e2a10910518009000306025040200201603010310300c080c00b6402100c60710300701102d160140e081b5601422100725402001c01803501c09500036006400e0b258010415242855600c1d1140026603000303c9038035043c4c00c405c200e0680c0b03902c0c001c11035442440390f41d4001c00003010b10891 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 82887564 1250 82886314 82886347
    0x120e071404091515080706020114070e031f0f061406160206040305070905010e06090709060e240307141201050409020d021309020901090c020304030b09070e130201090902 75
    0x38015900c964a032400d02c80101c0c4030b03074900c0f40b054804025507940e424021840001c28001c17900d0f036000c0e00200280c40703841409040f000e0140d030b080c00c0540782c0f142142910120410302100344c044c01000c0c248200c13542448060340d2041010350303001c81e8034107081c8200c3d8104e91150300810030808848800c41400d458100c1501d44180340700400d024480803600000c0e095001f103501c0100309214003000801c0500ca6500700f0740c12140341071a5598543c0307030076040040042c02101e0f18000140348000410007107104400d0340c641d0400c00351204522505e402c040d243e50103620006412050000400d04c58040e03030000800b030039803415a50940c1030402c900176110500300c042c420580715a4490710303403100f0355807101c03240d00000b41d00410200c242910010002c028103001c00060703105807220000020442402d0107003040841d0a54081e61800b815540d5070002000050325500e00c03445003200c0031408849404007240104020404150100c4641c80010017103001500310171110f40c018403180d0890140d600 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 82888814 1250 82887564 82887599
    0x10060503010b090d020616050c010e0f040f24030b0f0702120309160e10050a060c020103050c04050301060b13060f0503010b0702040e190209100302011e1806120e07 72
    0x42c2c425038918409001540056403110041d41c4024009481e03800e240b031041c407556107640f25405880c400d0300500c0040d2494485000b905400101d07921342c28580d840c080d480030074000c8a120340041e0702ca480c00202402180024081e10000c0b0000c10144280860440700540c4015002414480c1e0701d00803400940b02c5219102e200d41005c008000704480d60420700c006101201c503124820100c56440050000d501401c0c0c2c1c120850526102d004100c50504042a80540301c00317850707490721043c0c0c07640110001c000042560301d440e50103100119060f41c0a000c0c110007460303241d4905840324000f507101c030640c6030030303070302003400d0241c290b1b040000c180d082030a90341124454200141c0358003c500203d030243c010f50071001000e0007a0101034a00c1c1080d1414608168001d0359590b1042c0d64103c03420340c45500fa40000703030200750703541b607180b003c481c0e40c20981444585c035107480399990046000d06000340d407050b04200003280002c056000c01150b01d105090300260000c0081c44641e18100c600c1c0345490b80c01c1c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 82890064 1250 82888814 82888829
    0x10b04020901050712050403080d06170a052a0d03031e02040501170a020c01050109061703070b010506160f120305090a11060f04081002120601020a170315040903090306051006050301 80
    0x810035090b50760040d81a00d0045030030004e000c1e4ac44800350442d81c001c00e598041d40d0540002e502c81c03107180190001c4c4000907154060700030019058407e00c440605020301d280e40c82100f50307080540c00c003620303141c54a015403032183d100407030040d54101c010340d42c00184500015800380305000810050380d1004420012000461000700580c45001044010748a100c954240e02e609280001800a5881c1c0c0032000300c501c4815034880f441d0820141c540c4078032541c0806010000382d0300050080e49400802045085409888211002950340d50140140d0b40d4820a40c2c400d401c20240f14030494060182d40d80c885070001c042c3c290a6850307503600c1054580c14840601800c00031503d41000000c0300d040b1000b40007000121040c0e0820240c030103000c0c0d84429441103400c056040031603c15400010007107001d50344002c0100d0080c0c00c1c09207100d11a000180021588a0015014207080e120341c40344038140c900980d4ad140049043d4180081605c5003d81140c0600405d0002001120341c4075003a00d0546140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 82891314 1250 82890064 82890083
    0x6020318031204021203040303021c09030b01151b050d03090516081e01020f0301060f0905090c030f0705090105070b0a0e06100e060402042417090c03010b040209010507 74
    0x11540c64200e003000e50844030985110014900511520000e40244035070310844100b000001c503540d81e15141e00a82c4070080c09a880102101018031001a12181d40c0d04149450030155950740c6400306805003c1e881120044000340c072946045500c442e0502c4030083d0411000c03130192813696007540c0e860200e030403101011b4ce18903001007002010302c010b00401c6c0c2800c2000024030340764401c1d15141d485074914203002c854040545a40c010301802542d410f50100d03182c613419680307800c10585600503400007c0041040d014008103965950344040c07806020641181500c070716084814003107045001e0701c000b040c080f05000c2016603a901400316007099600c100f0034a41902e540100030080d1030100b1903207c881c028442040440705800b40d0280440340350640024003a121801440200d00c218000c4450401c00072403025a19000c8100240e11039040d45441403a101240e40e80075201c07a41a103803001ca41d00318000e1280e0f90310f000d001f01d041c0c801080310114600711046001030300303a2007001c00044c68880b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 82892564 1250 82891314 82891321
    0x312120601030911010509180a0b091305300307030903020c0a0521010e0105070206060a1e0b070510050a06050315060a050d030c0503030403080a0c0206060a0b1c0f05090d0507050703060203 83
    0x4400245e11240b0700d554052004500300089d002c00501010201e090151050b1800600070120b4203940c0100b040d0480054a9915401d41402c0079035410f1181070301c000e0701c1d5100c0441003008000b0003103100c5c01050740c002030b000e001480d00138288144940441d00c1844000014042ca0f50341c110100f0748100182661841c0b080910019405092248039401b0154030300b50401c4805038010071540d100d0361080350340c0d02c6456210415508000c80d0000303c7c051214500c0c074140720903482100108102030140c8100c80a03141041801e00c20761b1800c0b40d60400198480400b0043c0c3d041c00c115801d88988102820841854141c1c00f0411a01d203c1c481d00348100101642d4074103242c05001040950b07500711043e6a941d00d00307410060410a01900e804a805283c081c0c041d44051011403800d000d600010044210b9914000e96800c1c00e4105903a0142d103090380c00c1002c5550078852144000b000c15020f000f080c0c924000780602d041c81e60728414213051100801030382c0c00040c004540d22040c1ca500500c01600c0782c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 82893814 1250 82892564 82892569
    0x510020913050408130b1c0b0607050a030e010f0201110913060b0d060812180108070e0a080114061002100e01090206030f041518030c08090312120601030911010509 72
    0x3040d1069075140e00b4030704010701080c090024000d058001061510240030707691900382194910800c0703031012141d903903d643d07a2031680f4150080035011000902070b5081480380d445007810003181c000d088011409031001d01c178441d60040b105200b040751700d00080111b0200c0759901c205600c04d0a00c420310540b400d61850342c00724815403005028206001819403500d10b1409540d008061034000c0644c103200f2002e802d88241800011240d00e004030fa0002801c003c4031500548001e44080c10709028003029018262941d140e221100008005140001c502340850340c6028850290140000e03004400304c0018440703143d0000384801100c008540006042c01d001c40c3c0440c010042613000035400320002083c404c0d1880c40c01400ca000b680903104030481c424000e00100110340c00742004900c0e4000c07601d00d00340847c1c060b26100c4a0340c0e00800c0b1542c41c01010b03500080c100001c54001e00d000e00341c08240703c5146070300301c2c1c6030a03071040d400c0c00c00701b06a400c66129010303610802c800c410b04005001800845c180c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 82895064 1250 82893814 82893829
    0x80a110a03061107030311040f0b0706061701020a030605030606030607050a091212030e0601060e0f0402040504141006050703210b100221090904020913050a0615060c05100209 77
    0x642c0c004004000746000000300240c640e101d0501500000e090001414110498100b2201103815540c4008010307464001c0c8042141c0018106450f5555100c0000858030300128a104501181200042c0ea8100d9808064101c907200e800c420f000e13610400c1048020f4500081c0c140e00000f0300c3c10615201d42030f40e0000c0319014802e030403a00c560104016003004000c0a14011110009207071014403c1300714040e0f13143d03a212401d128000c0005c45041c90503402d800e000040c211409000f61015180948880229040c0e400c0440036920400e030110400410030304201e1210058007003880c0061500c8040d40b0014462030354412000c07042050740d0090084410550b01c8442880c60291112208214415029496500c0c1c001e200c4e103205c04901e40c0130000f440ea1801c54159400c020300642d03064450b6001c1c081c00341c400420003644e03078150000802c00310b0010002080010322070b900101f8000120241c2c00c0e05d081180e8040d20a208001002d1030010784049002c8081c4c2c03a122b480180c0300e014030300c00202c10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 82896314 1250 82895064 82895069
    0x180518090a050d050a030509060702070306111201030c1410050703081e0910060b091503090a0803040b060a0909211404090b0f010c0b1302060f0f030901050c04080a110a 74
    0x250710405840d9000160131402401120380309440820aa94803440e81c0b40e11402e0841c0c070800103030004882030000580c0380d1301010348104a8806c41c1d003040500c0141c2d490405080c3c20541d608400030004000c0c10710900c001c40382d94002a900028144400e41d8080e04a0003400380007070600910303034000340c4900b043d019000355110040140c01c803241444903940391a031340382049000308141032550128061010310b0803240c0640010b00488030a0108003445039440c1c0024001c05c60b030b03025002c580404118101c010714010b50061891503060b0400800708211640c00354000c0717140074108040710010500044190383e01d99514800c1c4881582c10301c4003118001803600100d10754078404240843c12181960201503564410764110503070315500030043d24800d032120340c01800841e001c400249614290000000101d1001c0c2040c3e050603010302419000743c000d9070000580314000310422030b10756000d010f0550094030154210b441c280c00c090b24181c6440c441600036203480c038490500007058450300b0306d1000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 82897564 1250 82896314 82896323
    0x3010b04020a120c0206150909010e030403050718150306020306010e03030c0a0519051c030b040c08071205011a0705030d050a0506090f07121805010903020607180518090a 75
    0x1501c800044018003928186808428180e01e001320303e001c041d00000e2818000e440c8001c826505480180401c490450000d00f1074801d552075000260301100d0400140020f03500c00c5e0050306540c0c2c00c10070001c111070921400384400c9420a2681540500b40c1036108080e603402c05405a501e9984000685143c00c60018454062000144040c03402e0004564410300c20320036030a42d002416200392600d0010f6206601400c55084001414909040305000a50024241c1404288051150001811540090341d04c8010075402400c11084607171185103030703031218020346040045504040b44410508101101e140c11f03048009150014031004200391f41d0000200351051044c1c0c504805004042c0c141912098010740418002c00d1074207031403c072034510030005503139170400590080c06000b0162031400c5a400703400c5816400c00d030105900380540740109019800400316070401e120028052407504401500c01088007a0600c295500c0f045440018684c0d2242100340744c8a500c1c040d03092080c0c0550081 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 82898814 1250 82897564 82897567
    0x30e010212040311010c0e090f101701020a030f05070c0b060103020706050a0b0a0b0a050d1109030a050c0a0503010b0d0215120f01140105121306020c16090b04090308041103010b0402 80
    0x8101540010313041c0051852000a01c102c04039801e0a80f43e0328a48900140c1c0714421800040d080c4040d48034142e801400b50b0b03051040719035110740e0108410101c111090313159400042d0500d9460b098061800f01495000c01040b05d485c0c4800001c160904104000702550b1014011900743ea00c00d07015104459009041001a801d10305070303140040040302c1850340110980f94000030044180402d84d21403941d25100c4518104240382d07104010300040c003681000c00320078030080c201c5803020480480d03294030810040c01c6480380842041101d40700ca9120510a03810308001000380d885400300c90b80c007180c0c180e0741c040044241e83d010241d02d010718200c2c00c03000c1401303a00300848110182ca810341241e59002d4001d1b0125865001140d052180c0f01e082a0040909d0b000f281c411004403400400081c002c160041c02e101004000505001c0d00f86c240050a0400e038200313001444241c030a00181c80000c65040000038926540a404401d004001804c15110801151220707142904046a40c0310010b0046 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 82900064 1250 82898814 82898821
    0x80c13080f070b04050a03080307091203020f010b12030d0b0d17180d0f0b1f09060501020601050a030b16090306020f0414030a0302030301090c11010528050f07030e010212 75
    0x6545000c41c1041c2407040c421900006a4509980100c400350b50015006142c603030304540398082c255001030b200c0c00c2007201052000403a03410403464004ca40b4800e80c05401c0c9044542c070400e007900c245814407071290020440c22106110000304640d400c148903e40499034103c607100160030043d18800141820324094000100d002000004001024444041000400016040c01290501d612004250500700890075011601d981950340d40aa61204964032209851420801205042e0b10600303800740c80702c50034030041d03805001c800c3c007410003503c11880c010f00d9500c940490340070103801040100300c440c1e0500c0c0c56601c641024809980c12a41c15503031103c002c00100810b91084c0b10701c0d0b0001c25004120100c0e481c000c03a0f000b103120707095401141142d003016188001890340c07004000178400300c1e42c0c24035141c2c482030241a01c10314441c2c81c20309141e0035010741d00c54500b1411070380960341441d03e410000000039038441079410403110302e00000e100200140c032038024880e068030414249401000c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 82901314 1250 82900064 82900079
    0x20d11071806060215010518060d140303090705040e03070f0201140307050a0e01020d0801030318120606050306090d0c0803071119020102010b0a050a09050c1b0f150402090403080c13 80
    0x194116000c40c1e086540903615041741801303801c002e0103255448040101d5844403448810791842e00080c0081c031030328a18519545481d041d0004080410940e00040208580312105001010040274140c1d0140021003c51040300c4e00d0b0720500d078004010400068003030081d64420101203403141001c1f4030450341c0c2d00304014081c01a0700b00b01400300000703400c1080003209500c04200040700e091241c4502020740d0075070740c080c0c1c0c01030609414181e07814180f00000030515032200030784000b1400f444002030800e050509040c201013005104004a03809003903144403660340032804200321034006100035241d4503900d8045440b0500d03c6080c070030340e114158049000302282404414154402d8008102007040784091240c054681e210341c0303034000084041003003d0072154011503808029540c07518908209484050001200107018461aa00c00800c00042100c100405080300101c22003106070742c40c05900248400a0041c0f00908200100740468400d1003c0d03070603a0324116080340e9050840742c44070023 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 82902564 1250 82901314 82901321
    0xc06231008010c090e0a0b04110d0203010504240b0c0a06050103060e0c010201150519080708030a0e0a0f0605130302040e0a03080c040806070c081210030209070f020d110718 76
    0xc8036030551810301c000b0020384c007681c101340031110540b0b60f4a50941e680c9006400520410751384c05e421980b11421654451071240040505460300480180c49505140911086403074184a0114094070b00d400d0941d64880404000101c68010440c5a51031580706402410110000c10090125017030000110401034560000c4030581c1d106011550320881000c01242614a4503403513900c521100d4006011754240b8074450403551100b0a02400c840b43e4601c1410303e08051075020060326040400c25102c07240d07010180c0c1100403800c445040d050b506080405519107003d10491003800000241d01e441030f14020326900003590001c004218549800e0202c80d20390199800c200c0005800100040194004200343d034141d481503c0101001d031341c2d400c004d030b8282d46c014070183c440b060f0501c41031248184e0704601d2885101c103200940b038254914030610010480107000c103401e00062a5110300856030014a04404142c1480e00c0d04250741112a690b040011980002109040029694082c03404540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 82903814 1250 82902564 82902569
    0x6090506070f0f2303090717070302060301230d0302030414120d051b060a09060f0207030c060b0a0506040902031f03030806041d03180f0f010c062310 66
    0x3655099680c8103401c03940b0403002c116a9000c21809510b0209203807181e8a6414a410070074480802c041d0380d101c1c202a40d800403102d165160384042c1c0e062200c00040e0031318035004800078005100c0a421580000e02501050190442ca9941c00c1c4641145418000d540f149980016100f10780c005003e08009440c0d038000e00814001d2103500992040074140340d404950b00003401006410b0030803103090215040d038440303826055201140000c40c00c2041041c000240100200d460008003000d0314608901a80d001081c602100c5105100300404a40c104540c0314200d80d0290b80011030b41d240c000010540c80c8540c00c1150081404240400ca41085500843c0170307840c010b000d2222020a41444c14489419010040000380e040000c1441800d00b5040f04070218084000b001d00a00c032080094990b4200442c103502c4074034000788007006030510241400302101c095031858000840400060004030f486c9600400d1035642d1041aa0300e20802c1c840b1034400808420100716038100710b00c203944c00c05040d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 82905064 1250 82903814 82903823
    0x1e0d0902040c210c1817070501030903170604061505030105040f050108070308090a030b04030c06050a0203010506070807110306010f0807060813060509010905060a0905010e06071e030b09040609 85
    0x5081a100c150048000d030366075140c80c82e0100f0300f041c2e100d90150302900d207000c924024040401030324007503081c0110104d8081c1210200c0c9550f0b4900e400c4100b03280800507072005041c03501c0c0c0081840030030b5100c0c00311040f503c20348510000c980c8840f00890020580d80c0e02c81000400d11441c0c6100e440e6100b4011130494101321010310080e420032040300c0456000388107210719a03001403000c200140048026041700000204a100415501d480d40c401c44101200c007200010303c4030345090108089031003240d800c00c4665104509660401c0041000c9110310140504105004601e43c0f0422012920369400c8071b00240503030300f99596400c0323120802c08076800703021000e0141107400304020344613004041c4500030750315070703031207003024075200c110003800050a209000d54882400e10041802080018092080d07c000060001654201982120f149915840d8503402c4202440aa10352100c14004040000c08055015502c9020164001d002c1c19602c19007101480d010042400002d17800560200e004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 82906314 1250 82905064 82905071
    0xb091006091a03011a130605091503060a14011202030f010f05010602071712160609030e180405031218060a09060b270c0708161a0c0f1e0d090204 64
    0x2218105070980710000c2807044182400101019189088400c14000c6c1d104000c00280b0b03e91900007068038a442199062a00703500c845c0c0c841400d080410603664000712024007040003404070070a80b07180e00010300c00d04450a442c00d00744415517409200052094110100821003520fa03402c403038019150903c99100503000f007100c0000c175400700282c0da208070503034070010f008a65031130f501c00c500ca43c0145d10413a03200501d44a18000044461250a0105000e5215100707503118400c03c001104c400c10907842130284040003400b001600c00026a181007240442c4011140c0e94002c640110892081100c0b019220b00c005006a040c580c0e840408100d003e40c0c000c0c82107004000c20f1040c454009107a4190121400040507d81c01115070950b8020486800440c80c200c1c254407280d60302c1c2c00000502101815954174841002800007a0340c8400b0382c080300402c224542400d0040bd203004400e10108402d10004404c036035054218115107450000c4000280c07540e110500e0200246030500e0103d00651a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 82907564 1250 82906314 82906361
    0x414030a020309040c050408010e160506070510020c03090306010f061202090d03031a030102120f0f0c0304030509010207050913140105060d061802040203040506070305070311070b09100609 83
    0x1204545404986400031850821494240310080111425040c1044803e00c004207010100f03001d01001c02c50620000c10743c0110880140c0040c44031903000fa44558404c0290a0001750b0206080d402c02d9000701c00162580a89070342141140b00e0706240c40d44c540100f5002081060500100c801541d5a6589284c005034200d03030f40004074420302c16450340c81031710000e400740023034801d030090234066040b081c011500b00031140110382640c012a5040707901500042c108401d2030544502e8035400100a8014061800c2440b1501c80a1101034000f40401c0b10016084241307174000c01c0040000e08020300004d10034a040c01480b8804003505608562440060701001e10401050080074000c0400901502d605056550350300024510070946205c019042c0e00c919001d0b80d02c40c8041c5220f01c1c0250041c050303070b20301990000c040301e50050140042c1440c2040e8082d16041003415100c0c075941c02640c9462a271640c01c40c0340c2c9040c0d1004001380030a03061a102043c40300054001d4070940c898410038092118 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 82908814 1250 82907564 82907603
    0x1b06050309011103040308150301060803030a0605040e030414120c0901090f0b01110705130e01020d020406111501030209180a0c060e0312070305090d12020a0c09020913050c0c060f04 80
    0x100564024002800e03c0c4041030000e00318240440c0748d00340040000410a50340c2c078806045030400c80c1c88031792075a038410003002941403602030100054016005140f0b000c0c14802110b40007085c0ea200c040c0650140d0000c0d0072803540402c403c455446c4000c091061640e55008400c01401083c00000303089070800a4011195003d00035260740a50b0707201c003030301c0d6035400c0c207050010443e41d02456240c00c64a4144d107019240d400e10003072082031100040541c0c1c542c2800030113081c4c1020a4580d4809910000c5903200c1c3e64500e40350079055030343c100c0760100c00da216030b102d1407140384a8400c1c0d94103a0081c10300320310800508844800440b405a2a05601800720108042d140c0c190100d45420210003000410001381c4900001c20442c3c0c4020a40583c0200ca500c88048c25850700c070710980564003000c010302c01e0284458408005005014041d45421400000f103407003454811020314001d911000800d0030b0001440a449014408008858031890500142440503405917400d5850311001c184420034103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 82910064 1250 82908814 82908817
    0x605040201110c01090b0f16110a1505040b07060b09130506060609060d09030315060909140705120a1805010b0a0603020c03161a0a020a09080d020c0108041b060503090111 75
    0x40f5051311a491103615202095606503c0b01c80ca146007103c08005407601809200d8075101418020302c00743c07048510040c14803100201d50f801c02e24140242c0866014007560003411501591b0802003007903100d1201b131408a01503d04050341661000e03061041203441034140301030010140c041c800300d8030252140c40c1400401e110b00395860750011010000c01204440603088015584d01c245000104103007014410542608903400503800103d00100c204240c100c540101103610701030f01c08102c002d01b0f00d0301c40a005032141540d03440c24442c440000840603515a8000c0401a100c403c1c1820000710a143c064000c0141c00c0059110307418200300810074501c2407003542d0110007484002c40ca0081c206154124850601c0d008581002504c03d130034020910034001680640a811070150300c030400d20350302820b120103d4000315231540c440c00400d00701590000b41a9490035085c24480304540700c60500e68614004403a8050200c00e1044000400b142d0000007940b150816100030007034401581c20300f1025 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 82911314 1250 82910064 82910083
    0x14010f0b09100306020306060705011d102a140d020d060b0403020901050d080c01090b0603150402010927090309030b01120f060e0a0b10150c0b0a05090a0609060504020111 75
    0x5120b44020310019079141d00660704000c00030704a5041c8005035903024203640800340c00c456021030520942d20040800c1003ca400401030b0304007444001000e485170268070022412500c1d02c1a424808200b046020300c04864100d90869140c5690b060444030b600065400103000c04800c51030010005031468220040d2001e89900070b04e519243e0b440c00c0304220640845c5d010944070040204403452107184e09200e06903066100711001c0d540e03450a4009c150910021040c19594102000c0030000141ea1045a0b0003c0d07800c800c1c40c4101401e6903480001582c49444c840500c40340c9888119018141c2100d8900308032031152481030301581e02c40044180f901200c0b18020900540c40b42840001503264000070391a0a0450846a0311101920348100011003510400140c3c085a2001c1c81110030040d9000b01f0b401c03540c01c1016016205a0b108081c081d03000341440c50f6956508085159503070181300d201e00a98011806010000483c14031400414003038070124042403040c10b030a0045600031460500c0d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 82912564 1250 82911314 82911331
    0x1080705210c010f021212061002030910110a0f050106090501060c080d020901120212090c03032712030a080906070e060a0f031b0c020306221101020a14010f0b09 71
    0x15080c2c00e08015a102038130b0f8010720781580100c018888078550f40801405007003248000195a50811105114484c1e036460408070444d0020800598070361201200072420722101e00c0d260480100d4000d01c2400c00c214030100800c14983c082c0c138903003400340542004082d912824010009a640d41006a65400c2c41c2c032801445200b0170301c203d281c7d07251107501a00c1010340c181410305800310b0a010007012030703121100a83c6c590002c2402e010250301d003048803056943c2c082d03000b103180c0098141161500e0f0a4131014000410114140b41000d8865448a0f0307036071400b100c02c60343ca6043c1c51101820030041100c01d02a071748550000078050038820085200914006459949412003e013403c50701800c960707900109040d200e00300381518a1100040b0610359000c0c0e6604000e200d0031344105414207a0280c40200d10b400014003d0a5426005a030b907986e1a41c854402e600c00c062050050341031040c0030b040500507803508055040480d60640100d1140400f510080000e0f5601004120804200fa20402c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 82913670 1106 82912564 82912573
    0x71101050106021204091806020703050403030810050904060f090804060203070204110c0c01050705011b080115091a0904060b030405010902090c0304080324090108070521 75
    0x1c0c054515480540034182800390b45980ca80583e02902c9000c1c0d944003880b150702c0c800446c003400310030b80c810703010f6481d10319030704014100d034115110036030100701c1030400142c165010070414802e940000700101c200d907c56407548001050b1200910400366501c02c44c807030110b21010b0244c401098954011940e400340c1d44103010581e654070319101c407500024002032a10400214860403001400c1c648181c0380c00150515a0140480d1180c8403000d050080f40480780a6010a00505880d40110518146030b042c403421641d20100b0b20805000d020621800201c0380d500400a00030100000c2001c01d03180d8580ac1f005a040d80700303903000c480d6030b999100000702318201480741a074040100c1d481e260451410740c0355008184001010100c0303400c440c0454081d0303001440074215096001614036000c947e1510489a603c5c522402014400c003444c00400c00d81069400301075880b01008005031 = true := by decide +kernel

theorem cover : BRFrame.Cov 82733814 82913670 := by
  have h0 := BRFrame.cov_init 82733814
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 82733814 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 82733814 ≤ n) (h2 : n < 82913670) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
