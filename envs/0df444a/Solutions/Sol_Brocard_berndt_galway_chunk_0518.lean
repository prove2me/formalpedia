-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0518
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:13:08.420584+00:00
-- url     : https://prove2.me/submissions/987c47e7-8e64-4c69-be5d-b18ee7312f35

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 92985612 ≤ n < 93165468 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 92986862 1250 92985612 92985623
    0x19030806120c060903011806050709090c02070b0a0c0203010e100b1801140607050d090303030507051201090f0204050613080c010f022d03031009050705130e060f0d0f050127 76
    0x80c111410f51001e4109087c1020b0742500103103011154203003813025020496440c0005800c0303031004035140b20f07544117608a03450940e0042048034100903001c5c03400d600c82c0c182e090038800d01d808500700581d424094440c5410b2038801505040f0030103060b400a45d5480c5500741d00c01e074007503100100341da502e0846140c111201140c1080c4103158a102042c3d152281703205c00341c81030040090b03403002260004604022a8400e07501080702e56901d810849203030194442c0c1c2101d070703135070b0703c004104100660b0801b0305801d881c5600140703041c0d0f94400044540e408245d840101030680401002403e606102c0b0207100c1c102805d0084c030210102d9802901c440c5140d40100303200c081d030f014941100201510509011041002b01d0b42e90303040c0707c20161030039640c91207030340c014500b000c001510092044065880c8103060307690740142103040c0241e10000d464020700840d00803041074680b101596505e900c251045000703528280a404550501d142900c148081d450500c50511920034031218400f00440b10464004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 92988112 1250 92986862 92986867
    0x503010b1f05071a15010c120c02013b0d0f0605220305030a0c021204032a030807140601050609060d0b03010f06140306010303050a0513030519030806120c06 69
    0x10107480600031144050008040d104c00091800b2000e503c4030700580c01400365050000c40380d4011100d2a031100401800400201702e074102080c001e44016028920506022460107080c0e146144542d0303c030107409454007915420005005400d840c905040c80007580c00061000e40da86a80020f8410f02500403c11a40c80c0300261f01800045c040380d640307040e0540d010b41ca4a04a06004042c0d42050f114803101c04c0c40c01240c071031020b0001074080d071880244c00c810742c1010310b541c0701c1204000c0410502d00340c2c000c8140113140c040030f401d4518001f440c4102c40072903c50034681000c041c4469501c2024007103601460050020345d4801050381c2c15164100e454555814050071030307038090040c04140350703095800d101c40d0160300e903d81c0e00040700340c401d16548101007280305003c02d583d62400388000340100d1810051040b83d588100000c10404805003032442c034180e1350781d54440c03514411103000c0d02140c4001c1514010550310209561304040100c8a00620810055040d5100d825902c2246d21800c0700 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 92989362 1250 92988112 92988169
    0x5060a020d120e06070305010501170603071503060e0f040c08030a0206061012050114030c0915060a091203020307120309110127031a06091e04150203040515010503010b 74
    0x20b0300300754001c1c843e007800e6440c5801d01c0000500941028003450780411600c00580d5080040410354500c2464020f00800c0214600000c0600c242c9169074050704054480402082d51145869000d004a0b03100459400e10303d020b0030015250b446982142b03a1941080112034141580095840e40002d0120303121407030884035240503106001c1c0b81d0119003c007800c2c8000050000d02c440c5146250000980c1900d01a46418040002c1d602044640c607800104444a1000a003801c41c007501072a21141420b160746515030741d0381e0300c0390b10300c4503c00c0340180e00000e250010422600902c0f0302c0203215050030310209045545884030144004801810448008034581899111400340b61840d40e11b1090070314119205d040041340344001c03c0c002282041981c000c901c0c40e040070300740c0504c24810355104a00f0103404540d500c4505074003030019140c1c80031340701131411450130520046005504c110010100c01281d0040380b001010140e000c00e10030391400151640c551504170190741403011710300002d8138171142c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 92990612 1250 92989362 92989397
    0x2210c19091407090f0501021f110301032a03030206040204110f0424020a030801150c02040c0c06050c09060a05090319080a03060b03011a0702010e090a0603020a05060a020d 76
    0x200d64400c20865003849104480c01c20071108141c0240c5140d03683d82055a142c40c9208000307101d0b84a0940143c1c82031001303103683d0010041540458061160218114403030b002000729a070401c0c0c005403800e440c00c0034021082c03c0d1b20f600c03110341c40100000b001031892560720065180d44004102a000f0398658011f04c1c03080f52060212001d074542c0e50103103521030b511401c135015243d458580007515000c00403003004c1914000950040c41590595981c0b24980c01c220712040020410030b000707414045803006070742c011ba60318054401a2020b13030359003240f0b45220b818004213442c00030b0040c04841c001000b031401e490312184110340380c22281d07040c101d548106450110340750440b801d0000c80343c040307000341843c01c0202007002009a82c440740e4040c02038a4a03010340801d580300038410800d0b1b0030142088210350098180107400007134014100203005010720380100d01c07941812a510424159201814421482d0031461038016100568400c0d003019400c2a01135650a0149000c00510070003001c128200030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 92991862 1250 92990612 92990659
    0xb0307090e150a060e0c160b010e091009050327030601090e070906050109030b0c090a0801060503010f05040b01060c0c080d1206080c0d0803130c080a02210c 69
    0x9449400c00c41c01120107902a1191840c0b140000e9544105010500341c4015000b410151082845000b900da200c0c1010190a50310000e604c80703600c00760446540106a000a40e68020519120b121145140c10402a0b00303011010301c02ea5251031418601c034000c51000815074000c09840300a0b14052004005400c2140e00f40121640d81071145100104080c40d0707a0700403451004104080700c104c5501e440e07849040d52024081c050010300d002c00c0410104a46028491b004000712250f5131806c224803002c0b0703890b80400d401c2545682c1d1111410440e40c01c0074461111aa180354100304a00d0400f0346d2846020103043c4955070030041c4210090082c46403904544000b00714110880742404040d410140c028400008031030581442d103600021302c131802250541d00c0c200020040003103c0303460340c3c1c0c401240d040581103050030130070341051400103881544400c010f8840840103103150001441001712032001b00c0c0f030020201b00c5142d629002004005107040c8491000c40b92200c00906501c4130130030b00e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 92993112 1250 92991862 92991869
    0xd0305091f0c0305180309060708040806150906030106210303060806070305160e03100f110a0e0a09090b01060309030e0a060f143103170a17010b07060b0307 69
    0x900030741e802006482880e07001030300310701c82e548051205583d407038580414910098003070459900308120001c100d00d0070b403004101e418811240c1ea0f060940351100c113840c008040b501101c1304260805032038032600d0240c1400c0d07071088040b4020b016190504e0038814880344050542841d444150300c3c0981014000e03007060f000380c1074804c2260040e1400b00e8005001e05802d580907600803c001d8544580e61744140c9040b515080054003c081c2115072005520040c61507c14415216a4035681071403c175030100002c0c040009a0b5440c010340b484c00c00c0801615000e07650086105a00d048265000544a001c03c141150405e0030005684070300c504003034810800e28100b07194401850000880d1207904403200c58442001503a8182c500d041801c0541481c1c803c03016001e1440001e01044881014503810384203000c054200e03030814840ea2540c07030030800700007825414011100850159402c9501000c40c000050180710303014519413500300405c10034829070002511041e1900182003e68a00f0400300005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 92994362 1250 92993112 92993143
    0x405060f1c18062f0313080c030c060a02090f06030c070f080301090f090302030d0b030307140114250c0618050c120102030402030c100903080d020901110f0d030509 72
    0x404890000440b94841402c02100c0d4946043ca02c40960001031005603010210142d111141c08403202e01044a44c00082109401e42491018040000ca9510140405039040c00003107441c1e4494084150034904001d000d01551361051045803010b982e80307807240004120554086540740c462a00c0090684039401c00a004040360640e42403c0140040c0294100c40800e401005044e0005c0d1078181951403142c0b000c1e00692080c0000281341c180c0da88408d95000b00207007103a1501e207055071850550381c10481c816050380d41d6028401440700c1200802540f0106072034034141e4001c8040a00c2e075801c03500004200030003401c1c0c0e810104014440e4000c080c0f01a0a03009203502c1c01182c0f4200f5643c11078844a00d000d4590b0001c0d0050144050007941d00443d0f0040261841c2000a130601400c2040c24540400300068050000042440710b4010600b0462034203007d80e440c101040003408150600800104c2030788030b0440307100c0f523550105072424030004038036000c02d450b1a1456081d2070641c040c10000603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 92995612 1250 92994362 92994371
    0x30c1c0b041a0405030d1824060e0a200a090608070c05191218030206091503090a1208040506060f010302090604081608072d09050405030a0201050c0405060f1c 70
    0xd00c0b02c000060a0102c540c506d082c05200c000d0004d43c100b5070f0840c8030046c2002401c117003051801150160300c072000e1400600028410b643e441c4403c00407001982c000380740560f02c00d11001e400c58070199210f14a500400c225143c80840400103004280c644504410480580c0102d80c3d801d100d0180c850341241c00c00c048961030517280345806c0455207128400c41c1d184c0550094100d000b40204c0500219600300d100c0d0a1ba0145140c0a011040d403140300d403150302600006880d50a801e440300514000c2c507004008114651540c41d045089410180040040c801164104800584001041a4011010744800c0f102d4078810f40140c0203800fa01044550289000c1808078200000040312240003505da8401101c041c3d40b246400e171501186c0c011660383c40e80521a400580c00102c0421007111500e000c5646042c1e0f0700d0444a040302c20603141150707650000034523185041e074240540c1d500018210009854180380400213100c2c0c0c410902d00c80c003001000720f8641c40100c40b1810b00035200901c600e0911 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 92996862 1250 92995612 92995621
    0x1061508091c020d0905040c09090b0f12060f090312040219050303180f0402070c0501140c01020307030b10021b010c06110c010603020102070801020304080a0509030a061406030c1c0b041a 82
    0xd446130041d21401c800541e0500340004c11b0725081c0600003000625884c1c9440c014100300d805809455285607864020405039000451340e00c07424958241c0d00c0d0580c01600050800e11184000103c028000440711351090000c4031440c000000c40c3d640080c0c0c11215815441040c00003140200750300c3d445a40c0c180000300e00c0d49030111603001d4501c41d4070811106450200560b00400c4201d0140100141110151210034052940038407031aa0b0701c4035001c6246800d00b41c210701c480342a40e00403209030000a0b01c92001000c14145080040b02e194058000b0341410301e024412501211407014505042110f090410340901865a000410301c0e03800340c002e03941c2e5401e0010194041d00b0302d844107c0c0107200e44070380040c0a11041c420744c2d0040780c1c040038440ca00905907030304039804e40007440030311341c50b00400c0ca1210001d4264810344105500c0c1200d410254078111040506010611039614090f04071940006040348100581c01c00055100070008040e40f00c43c184405038200340200741c00080d05402c00d01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 92998112 1250 92996862 92996867
    0x11040e030316020a0b0c0f0403080d060303090b071208070e04020301030507080c030a080d0b012001090b01052b08071a010305010c03020a0503190e03070c0807050301061508091c 78
    0x85118000c1c40000300b40100444104a82e2801c4214000d00300d000160301003580c50314060018045008003082c41c0f130509485ea1140d841e00d81c0a00143e80e0101d42d1410200704145e040594080184175413000b050030179005440b121402d8260102034010001820001485180074141a100c8040c3c050801c40d201e40c0c691030881d5031440c4a01170040a88101800e100c41840e0000d21084500da10044440c1006c00c91700d0603030301401c800031009042c803040d03000303011455600c1e12a445003a0310420021504090a05004043c3c11040c0c000b64000c00551030111480314981041e8441c10b480082911907810f494200340d1601e01514000800f40d901d0186c5100c00b1041440c10700c0d05883c000e074001c11551402e103500390100c4c490000f8040110b8420b2001038501c180c2c1302452130321440c40410200d0f401e41c22841c0c080c1103600c122f100326a18626441c06200e030800c10450000a00000e4008010440c2030805152a0000c20900741003008403c400042c075038403044c8503031141da00445401c50162138031001c02 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 92999362 1250 92998112 92998117
    0xf0201140d02040914070c170403020d0614060a060e010c1502070305031602072301030f0501060f0e03120f0d140a05040203010b10120c02150c09031002040e011211040e03 75
    0x130100d540707080540b0f820507044001046401200d0544556004000700e60780e010360080c440040100b0320000b4080040980c84400c1201d0841d07101c0d480004034010342c0503c4403103007000645114010b0000c0c81c9c00b4800c203a08420703000e02111007420040c0005030706181a0705403007840c0043e1010203002281000c101900b26001e5405070b51410740701d20750541000b10032686d65207a482005410300280884070981c0703440401a510900b010300d000319100701d41c100214103494003a403100c800070300d412032003504d440d80c400004039640004030090311440f90040803094a500540000700e041d41800100250f01c02c02a03800b201c40404620768520452038884140710041001301c506038001c0d4205103010456181419a6451150803a1150b8481c00b91501c2941c0040180145038025407140045003d02c48102c180040e105a62104002d6038851800c000d05081c01420b18900c12100e00602c400c1c000c1800c03188000c0c3c1034403440b02c0480003048541c10125071040c0f00024440e00705203803409988800401100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 93000612 1250 92999362 92999369
    0x10212010e01090b0603040602070827010906020304150e1804110108010905090709020f041a072604030f0201210b030d09081504030c0c0b03250c0f0201140d0204 71
    0x110328101c0daaa41c81190140c41019854a52218082001800080300f0303501400703010780907843d072a00300f07000031026401d40c00d8440c0191141c0d60080d81c8441440d07902c400d910010f00030030303c065410146050f10090780046c1d02043c6000340901740c0440d0520340c0b6962105d088070000c00f14086603074101403d10500f900502e00080d40065032480010801642d10300480340100000001405038038907245180b0000d400040e022450200f00f0840054100786000021503000104484d840d46c400d21031506003842800d40d43c120010000c0744100c60180030000b000e03070381140d4000301402e0111081d44012a104489401c0e8a294883c04d8500880c5003d0180c0c0300501034141a0103e62595004000640302201c0c58407d1a11a9104900000a0841d140d103141d81051080c240520541d20554030b16007400e05941100c981c405010007041000a042d030070060171856400301030980115503c81c024101040c2a2025241c2121080c02c0300440e449032551003409040c0b8280310303403100800c0b01c28401a510910 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 93001862 1250 93000612 93000629
    0xc0b04060204050310090506040b10051e03010f1515030212010803030603070e06101d09070c0303060e01060c0605070e0303031e010906060e0d0609060c032301051315050301021201 79
    0x401700d030700d4002d482c41000261500100188816501d0b40e48a64282c8070091a0800d003940e040c1d00003070b580c1c55048221a034800090b40e00b1000151043c18582120040c0b00c007500c60758240607440d140314011901c400156a40001c0c400e60030980c00b50141c020344100c101d00c10691000740c0c0000360600c0040080c0d401640102c0c00d0300d0030180d840290700f0460074140d171490390010003001000c04450155a03848110b4000f120752410a000c0400000c0080204640e1440410b000c00360640415501d071180c0c030040c0009698801107941400740c01003441862050041540340e87e0070200d07602c0b60155403903c110302001402c4954915150000201e280785007810244c00740e2121001040d1940e9500824050707403000c0c1d45038800d880b02e400800049008202080d1506951034000c0c0020651600035a4807000b242d40b00850701c0c040c40101c502412001d14500d2100c0f5000310018401ca0751210910140401340c00301c04a12520a030303c10b03000c0004141d101950543c400511488200c424103d05070484a681 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 93003112 1250 93001862 93001873
    0xc0303170c030a02090a0305100c09210204020702010c05120c0f03040503060705070237060c050d0503090f0613030801050108040f020915061810050a0806100c0b040602040503 77
    0x9250619422909441c000e100810500010700080c425501a04a8900c0103080e14422a07994171007500b40640b0346004883e190716400004800381e080079004c001860002c855012003a01400c82c0d401c40505d03800024030840d0006030b10015684102c1c52200095001030966039058101000000305a0103118004202d000b40b104a041e0000080141c5040b00c0010f005081c80c1e54500b20700310340350340c06200304aa0104001e50700c064136510120082c0d10040000c680484030801103040440e8a4080b80c0c4000200040300026500042c0080f90000805070035041260700c0f031721041c140300e040c0b01c81e010f001c0070f991040b6003c020320105914003004c0124060748070401c2c1c0d030b41c0b11001184c0082e42214050300ca410130504000041c208910460750240580c0d40010101e042c803400182154010404a441d100c6103140c0c0c4011440c18034410113440e510b6081451071b0202c0400003501ca0700b002002d00d8032607402c2c819021201800303110310070110b56100036500042d14003894810025005401024040d04c41e4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 93004362 1250 93003112 93003137
    0xc0a05060a0b01091a0c0d02030a090b04050d020405270313090e0a03050309031209100e0c01170405010906051303171e0a0f06080a020301110301050d02010f0302090d0c0303 76
    0x11485070740b2240c1010380d1000d13103660514002d00da500002c1c651080800004022545040303030103102082e5030801c81d60145070340740728001c002002c1c1e09490b01f00000092081004211607914030404401941d170541d4042141d80c1c408030b14414024600e0300e0030050700c0d900d40d07035120a05404802880030100000e81310070642c4c1c84801c40070031200d280701100200c3c0d120400b12070101e0301800141d5488071a003000c4074508011030368a034112410640d007030b0225901c840c41200e010703600780c0584080800800010400203860000090a01f480c044001000b05640c0c00401d040c40f00a401400c10301c1c0d001441801242440d500d0725800349500d203c2a000039440450450010a40040d558050031049100c01c0500c0204a0601060000948140301e02c40d0740b09007003c0060402d01681e001070080c07002402203000d8a00506003500c1043c6a00444504c0800040c0704a98640741d4800c215502843d00110044501e0000d5000344240c4020039408280043d801c000c124801d030b800400d41e40700799540c1340d03501403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 93005612 1250 93004362 93004381
    0xe0910050307050d0507080d051b120f070611030c031b07150b040e06180706051e03040804121104060914072601080105060109080a0b01050112060b0c0a0506 69
    0x5060240030340c0354105403003c00c943e01c3c00c40000b401d605d004405803250b0755a9105824644042401503030003150b804150300314a40d03104900c40740c40f420301d4030240c001c905080a000195100c0c0e8070802c07540160205d01c1c1000d004d9554071540348010003074aa01d6503410001001c03c02600101ca1446000d00c0420300c0c1c2000c0c03201d51003034505042d8001903000418540414217400b03440321401140c0c0282e560b07500b61202403c00c00189002d120104a014030440583c150395090074065004002444400c1012010454482c01001102c10030000d0680d141e4403582750140c0c25109a90005c4074201d59601114244190200c03002c0300f03040c0485040000c59603130080401610581d8507007100b00340b480400a0b034410700600442c0000c1c6101042840500307180141e00345402002c0e0440c1c0d486a64600400080c0e5030080400400b611100009001081160b902c410307000b81d0502540e410484107000c0d055070060250010b2024045201050362184041d800156480c1e40343c3e8010303030702d51007100045881c050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 93006862 1250 93005612 93005641
    0x109060b12060106030203041103060a0b0a080111091e06180f04090305030a050408041203020601080c0a0308030c18060f0901080114130203060d05070608010e060a0f150905030304060e09 82
    0x2041c1e9000382c002a0700c0c2c490190020b41000f003080d61142101054242203075010b10001d44240c4003103000003034028100d000e104100030340d40c100e502168503152001e08001d050130182c80030380340201c900e2001910002c4005c1d0f03500032040e1500b074100c2000300c4d01d00c40d405031000c00816a5401607544c07c0c2040845003c00c0280d40e681e95000d00815420800309505109a801c0242d03c64021041c2c2480d09a039004490300001c1d420106600581000e0010b01080b0014080b003900510106c654841d09410340e00c1d003021a22010304102c051400000303900b40060b40000c00c443d000f080041a9030740f20690b452041d07100342d2240c8001d0740040ca0000002c540e0704440c40782100d009034090f001c8655000c40c2e4038030b06c0086d030004d415036601080707000c41c680010780d0402c0700d600a0100d507503914031507515090181800c49409044240318000380340050040c5141c040c000740460340d0310342113a820f040c038011040d2601d00c400c1e080f05815000005c2d01103941500a824000301c6030081d500c90400b691200d02d01c04040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 93008112 1250 93006862 93006889
    0x90a0b0406080c0906030406090c0f090f060503070b090d0c030803070c1e1e060209060408010b0108071b0b06060910030b0a091b0315150e12030304030e09070201060f080109060b 78
    0x5642800841c001ca8116800700d01301503c101d072b51410035900d410032200380d03007425440f0507021600d84541001c000018010000100000c0c0c0040a0b0303a410200e403103115004001c8a0350007010800454014030500c298400700031500318141c1503036418030f5080103000d50300242056035071340c10f03010070b2580360030314524500d10b0a41c10003403050100781c14403544046101c50140640344503800740800041962070030010001440440000503c122111002621030000100814144018400260000d515811012030469440a403908041c0d8560001404500840514540215403210007411244c1c2691107210805001c490b1190724a0360f40302c040050301c0c1070808a011007205c514424005601030382064501c0900e0040ca2800142c5584040d85502c45c1682e560700027500c820381d0240141019040000c0e4940b0b01c0d0065443c40c81d054601500700c421080540b8002c0917202c000840b540d100b0740c4103002510f01e5440341e0761b40d2384e6030754500c5011b410003240607600e140c9000403182c540c2c6050100305504 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 93009362 1250 93008112 93008119
    0x2a10020d09050103150b0f0d050c030f0604090303060815010f080a08040b09030f1c08070503010b12060103020f13140306040308180313150914011b08090a0b0406080c09 74
    0x154244001140134200300000590b80c8107245d0000b18540030600003410303148028280140e1900140101e510650b04090003e1511443c20014424418521494558003240a413004140800381d072904400419442d1700070901c9014814014500907000c54065040b40e41c500c3d0701c004880e45a0300e1090300c4c0c0070b92032001801030504020400c42c0003007403400f03000150001425200002c904c100c099090050308807600c80c5840c594480006026080700403290000c50600c1c00ca03017198180f11140c60315100c4c880750803d4488483e4002803241c0e109804503005492201102a140e880311061a0100001402040c1d8903880c1d0100d8400d00f8140000d8152080707805584880c82512002c011040c4003882500103c8a40410403940c424501d03e0a220070090001c02c0c826281420150b03402000c0407051741203e50780001c101004412a80e00003600c140280c1080740002051890f0b1428849500c0340c0c103c0c80380c12400c0b12800259074400710001d00b0856126131501c201c1641c4000318880d1a01c240c106050f032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 93010612 1250 93009362 93009377
    0x10e010227030c0d05030310060801120201210e030c0f03090105091203040803040b0306010206092109010507050a03030522020319020303070b090106050a0906050915032a10020d 78
    0xc101c104200740c6105800601518044902c0801003040840e04540135103e590000060042c40768202e100c0c0c000414492410410341d50501945100800d407881e4003134104000e1a80118080008010100c1300303010304e500c10001181085940764494005450901440c021440c0000c4041004400c842c08600c5c140d40716440d200c04a004c0103064101a1081615440b080c000860402c000304000c201400e0210000e503220701d45907000a02c0c021000f0025846908144c001f1486003401d13454030906100c02814150304c410b40d00d80101e0700c0340590752015203a446000d1aa209141d01a030080d40245c00c03101c56049032500c00058040c61101e00c941c000d4051703000411940761041d00c0707044036500c40d00c01020760f46050780c1074403444804c01c0150781500869664100412680c074029040c0f800403c0d01001c03d000b4146450700282d0303a9200208108001d03000c8030b11403a0305580601152001c0b41e58170003aa003080140d00816000111a07031f040310f0258280f480003005d0f8600000b00a071800a0f580e440a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 93011862 1250 93010612 93010657
    0x50c1b0d0e01230318033402151e0f0d050601090b041202061c050f010603110f030c0403050d0c061a0303031305010213170111030f01121a040f05010e0102 68
    0x1200c90341300401410046200c4055103451002c10310051507440e024455001042c00c0c0782801540145010b040d02c0100c42020102400580790090f003c200c0000e081429903c600700200308900103109007041418034040065554801f001070406048860090f0710100050366400005441d02c001c5405918001c0c40103200802941081541c0d035010603201070300190400c1529851200d8002d980c4910482d0740780c80d40104084080d5120300c003030050042c2c3c80c0c103000014400c103001c02c0c180f29421200311212400030001c1e9421000d00116402590322804680101a06240042c111040d440013116620700f4060082d03a645004841620224802000756266442d0f4818210b042034528004969654003440020700c140664440d46000782650300c000109003245031b039042d0844602d480d4240031850706000344059451200c1d0120b06584505441415503400750420310031a00722079a00300d0203ca4100d0410080144001c0d030401c64521030760081c404000c0b013108071402e0740116048040900c0d501d92021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 93013112 1250 93011862 93011927
    0x6060311120a150801020a1116050d05070e0103150c090609060503100302060d0b01021014040209090f190312290f060a050702010f030605090109050c1b0d0e01 70
    0x580e00b090100c580000c207060100ca180c01064840d510610b940c0e5404610320b40c160741c0055588070750000d050040c041c5407542400c0701140309900d008050085e0300b0a0281410082c041040074050108000e03154400d44e0b6130304c1c040384010351000766010000e0412554207100c500036110081034851036200c0d0041a81099411101b54000074041140c0c0b011505c000009a2070344c03401040e690445980110700c0c1d09155002a26010104917115111813402c1041e40d170421414440c690090350407030307102c0d01940307410700e14a00e09243c00384090524080c8445407503880c0c00010008150f68420f8503034070720b101590b030003000844819800724405040c00c8a030b1402d45840c07451800518a100610010480e11000301103609030304412941004104002040000c1d9a004154110002d0a0745002d101c0d0f542018003143e0802d07018030401e880039880b50003241c441c1c2c10400c103403032401f035007440002c8500711130303010307055880c901c510001012907000740c14240340c0c2d41304540386d0380c4c03070503034061400603e0b1070f0400724 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 93014362 1250 93013112 93013147
    0x30611070f08190801050d060c020f010c020c0a0b0a121d011a150a05040911090301090c0504061d060f0303040810060911071e020a0b0a02010f06060311 67
    0x10200125010048800003501d111292800039024208183d00c82c143c064800320388800c0d04051030b05000c40c40300100060b0b030701c0c05243d4000c1c41c2d04c00d00101d981c0319200400e902d400c007194a000d290f035003000000a0f015600241010320321504851202406070303141042d440900c41c01c160b15000920030002010341e03060a401c0019110000c1030030f0561401c8d4200d65508440903421b506810300e04440700441c0a00d062000d000108072000a920300c0d01d18a40d40181840c880d40c8506007a164a036580ba001c00240030303090b80d1041c030001e4002e010f807a03802e240c404502c00007806168480c500c1c06202280c03280305021b0742810074201080b1009244c940c0c0781008010141c0c0c0328440d6040c80100302c0402c19030010b00c88a02d03107160070100403e07101e04000c8250241c6601d092191882c100500444011500211000d802c540c0440703100707420305843e8004140300041c2c5420001080900090f200300303a5605520072050b0740b420701810840651510707003c0301650311421fa4103400c91801c5c00400c07118041c0110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 93015612 1250 93014362 93014381
    0x30203040906030b091e030304030e040605060c061b0a020a080c0a140d110111031801060302040513030215040b0f150901030c081606081303020a152c070306 69
    0x112800d2960711041c400a507100b9800c01c803107003800074051080600d0108980143d40b45e0b1440e00160b00544081e00e01d80e40e0100400c0601003200ca2100204c16480350b60044020300382c050030b00d507a2505503905e06a034400050390404c2d40c60032004010165820000c042d56030101656015140c0b41065480b202650381240f000080350740200f03007044000400529001c0c01c6200018090041d4014800c1d000c2d00120401d001e1040e1079040c40c0c40d8080700001d540031070f070380711040548111a48808207403290041c076480d003000390030601d00400e000c4074415510502098522940c01c0701c0a11110f100440401d100507100102140000c2000c00c02c81d4854081c81030340041030300103d01d41e030f10030080002d494035400c4c0d0007521000282d410500c0520400e11101c6481e40190500f083d62038070f070903002454424020100c5807a481c45032201e83c1090b04c24001500c920380c100c810500541101e0700038100030141018030140002c41c3e20100410104440c2c40303054150304400c003416180d403854940c0c8026000000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 93016862 1250 93015612 93015617
    0x1d09070c0203030904050703050601090602010606080c0a030e3f0702010c02060c0a0305120f060906040f090602071b06020f030901230c01090b0106110304090f06261005190903 77
    0x704544541720361083c1c1d031085c0c3c050f40d00800e607801e240300050030a0600b50020300071039050441c00d0002c40d410810054020f0800600156261482c440403001030501500040c028050b40c21314081c0c1501001103050b1641209242402d403001d074802203941c03000c3c2d00390004204802481041c025600401541b04201e00240030075281100400c2d1060618070724003411000f1880209448000c41241e10049070f01080a03009046ca03400d0500004485100060a5511031a00d0b11650009151308c0d03004404810b521240130b40d00c03804c8a16211580c221041d040024003800d10308001051840080c0304422a860400610f01e0090b020b401119040e0800d4440c50912014515a02442c0e80102c0104902c43c580c0c40002100344503441c0046800720180d02031010000e018521285c0c08102004a5007103500008000441b564400e1600f00900a20340c03000c2103001c5201c140d801560418100c4c50417002600c3c0035641546040e1654004452003543c140f14405220b0104a04e00d17005580f103c1e4800c1d0290 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 93018112 1250 93016862 93016867
    0x3060103080304030903120909050606031e041b0b04180204120803040503040e010306021305100e0d050f060c07060506040c080a0921030608011b0f050313020307030b071d09070c020303 81
    0x1303440300742001036440840000234030813510402442c0c69034030030715410a030101c422620b103082c4041c0300d0712100d0340f02600190035000d000214042243c00c0858481400401c0c042018203a500d24034002c080d00544035154480c000750214104540c958821141070b81c01c0803440350f01ca40425112221640c00c000d00c2210310344410007000c0740b440e0075081124000c500c528000f40ea0340d2a0300e031403603116641030b81c0164068000c1c15140c07014030b0f4002013081100030301a80c61a46440721401c1c168689840d04541080c6070085200f170003a136040040052110030300a01c07003803003241c4500d030600013140c600240340c60024109d080450b04804d100c3c5c01104046000d6441004041a160940c19403000ca800a04d000301c0ea40c0c420401400b442130094845501e440c01c2a0383c000e11313145102504003180540c070701d4200800000011001d0039010050a0f8294024040390550b503100d18100d100510140c071180c010500c03400306e1441412881003500039018016281201c140c65a0f00d09a50f820700b126000c0364940001d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 93019362 1250 93018112 93018119
    0x3080c0a03020d02040330020705060d06030f0b0105010f080108120706090c0902030115080f130f080a08040c05030102131401140d0209090705120f071704030906080a0b030601030803040309 83
    0xf0341c0054000341d4051401d0b030034404860090120780001d03000030b00708001e5442c4030f070300e01c00d41e000310708541150f03015191706540e100c851949400821942d000201004112403100d01031242105255050320b10a03281d80944450301481503c1241c024451141250f003c0d078510000c402469000d043d58521546011071043c81c56a5184003507030480d0440010710794003000410280c0f091902c0009620010304209000303042c880010a18100020402d111501031001c90008002c81c1c1745408032401d401480081d01e440303443c03000810000042c2d8060300c00400c006404107170b502d418800c48001103000d8198191603858250030000700301e400c3c80308605115003030820030309500d0102e0003080b2000202e0300060303441e110b142c10031407101c2e805000e1408100c424420007002031840d889031074018a2410180599a403a02d00407104550f01d00709071070780042c024040c0420550082c043d07000342d401545805409a4038074510f613045450045400f581940000010400314010400a58101b402460f140440c940c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 93020612 1250 93019362 93019387
    0xc0807060e0a02030c0105040f03080702030c0603010816060f0e100201150807180501030b010b0711060a05030f180a170c010606110d1d1c02100c0203100903080c0a0302 74
    0x1e5901c00c5149a003107249528210300d0140000c220002c000d0030040d08040c20141004d48001140c08018811800096418107540c3d0401030b0071044500244600d95940e15407190503102c00c55414405034a80000788041819401480e0451440e40c0a64a0245408028041085040409903010107556880c90305003460395008100300d015008031002805071a14204020000903039101c45885128076101c018070009028910b6103046940000c0e0058498a50f402e010342c40c524130300401a405000054844c0a4a8218000c0c1d40304101c411807080e601d40e40c602410b400c24000920440668014000035800100140c00440d401480507103a5800d18090f4501c06003129425004000490460004c201c81c0580800105035280e0341850300340c0140b030100c004086140400410740340708540c2101d9022a81e0f00480c01c40d5410740d00101080380102194901070309060305a002603000b401031a083c0b40080b00741c3d000e1000344550558070000c0300d03034a5042c0c140d515080b0f00f0341682019000c100e034412110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 93021862 1250 93020612 93020621
    0xf060a09050c071506050603010b0c070503030d0b18060105030619050603100e280f20030108010c0c02090708070216180b1f030216060e1c02030310060c080706 70
    0x45048003040c0d0b44000d28100341011144c240d054124540c1060414012601c071902900e045505e21100c1648880e81504164109191074022a03017502c0701103007102c1ca40d9915005003070041415958aa9420203002904881a408440341400300c0c0c0c04101048403410700780141d503a40000345c0f950200c130300c1e200d0340060070950082c1c45042c18400420320902070222000300c0143c1002c540d5414038401d4a13203880c0700c074200074002c065091896849050070000714054001d03050002480b4004500b00c058000980310700d40027801a8103c0c2c0d0b280403889040b1a0040080d0514182c00401503006076641c500700310f0342108020705100c214006d90707045411041181c1b1003503024060b041600d030300c0f0903103040400c400c4550540d10148180c400007010a5100c51410058130071400c10701c0c0c00b41e91031a050702203000500040600400240c034049100482510209280070403e4007800d40941413041c3d19002c0703075a800295041c2c400300c691780e81c4c1000300c0c40c043c2c64034001c03540c4103400d41030400d505500c03031000300c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 93023112 1250 93021862 93021871
    0x516050913061203080708070207090c030209040c030c031b09051201020417060103030e1008040303151d0a05010501080c030a0c12180b01050102011e0b040204090207080a03060503060f0f060a0905 86
    0x10100e42c14108068116900c0340e07004106e8542441c2500c0d04500084d9075801911072240200c1e5101e100d804960300ca03070111040050058030a0105e98035102c0014010080526068006881e10300c405807240803070345561742d0041141d40c401c1ca40605110820001814005080c00150f40c00c00000485042086001075040c02d150040c296a40c0356040181c4070008000d069031081038000d070764446030350300921101c1d007150300b52030000f0b0400d41030f0103000254a0280c000d1040740d00300d00c0c45c1c0c841040303003c09010301c981c2032160207201c503907a90001990b60400945848001001c1880003c2501003c0c4e8403213618002c20b8a083d1051401d00400300c022280301d2100c0043c2c540c270448040d4284802482c1c2c29006000a10080068482c00000000211610a1803510060b00d6070f200e9000d03a510b6405440281901001c2155548102c0c80c240105078071003002c45011a061000000701c81c50003041c45840380150001e41441380d40e52000d0b0070800d43e402000284e124080b40d20204034a01c480c8241d038440c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 93024362 1250 93023112 93023129
    0x4080a0c14040507120b031e01021806031003020118051503041101020c10110709060801020a02071406030a02070f0b2409010f0b0f0d1a0a0603051605091306 69
    0x446060103003a007400c0000aa15030b014604080c24072900581c001d074102908405620001103103001d140019013425001c01d103544800120001d500800c02d81076000703110b004216000201100d200c0300034003600b030000300c9011142212002c02000503501494500900010140800041584541c0051810007480324180600407002c0100410003070b01b07410400c1180001d0004044001b000c0000541c6081c8980c0e10703108000c90081c0c0141900001c00c035150240c42c3c1464180061526401c0c80740c001c0d000380da01000148aa1500060781740200311802c56001c1c4083d05882c1b8540d546030314070010b0740c043c82c5c0889450114210500c0820302e09000316000f40c03106078030006100700342c282c007013540546580f200c0e1095074035200400c80d240c940d0354280c084585209803143c85e140f9605943c0d07035a014801c01108140e040c1032011a411904088241d40c00e03200b1101c10391043e40303643d421000c88604aa004000328a66040c1c40e807480e00034000b400e4010001007400c04d404400f84000016100541e000080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 93025612 1250 93024362 93024383
    0x1b2803050f0c0a02120105040b04111203180102011b0f081b0a09090f0b06041205030c07120b010609030302030909090c04060815090c0913080d0c0e19060906050f04080a 74
    0x8605d040721072007401c55a420000d22850030b15407030300c20088a0141004100d00c00448841340303951200c141e618081e02203042600e0311094100e101d10540176085402134010751800c2d88074103016440449400b4000816070390170308030584c0b8900c2900c1402000d410400c00303000e07601600b1180d00d041c10003080c0c2ba850b566902d180341442c02c03016000f59080c003204819124113002140645484090540e022148030b03a0684054015600f0320500303600c107840500c902400f4144000c01d417060340f00a00c451a0344110310000035030ba40c50038215206407042c000200141c00c00c001816552402212050b00151036070180c0394110b06400000e400c40b810f690060390540c00682c039401d0701d1585499030550200d03c840260089084480004d01205001851821040c074031010410a000f08201503500c16001401c080205078482400035205031310a0300110300c14900042405510b1494207064801c54030242c4420b0542420541d058809030410f060321184402c0a0000164021003003003110115409202080c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 93026862 1250 93025612 93025633
    0x702011b11011b02030f031905090609070b090117070e100f120902031518070303093206070813090606120204030f030309020301090203060c1b2803050f0c 68
    0x50079654041c1d41140c0503202d044203c03500b590040200c400d005407886140c1c1d903a40d075a940d50254402080460780303106180000708000300400040c964002c02d805411910703203680e5031065401e1882588420340c009801e20400444104660600030b4001075142080629111100003050b6a02d404d03a040100003100032200d0201d031500320300d40c982150307208901449042040c0d001f1995407450740526a00d01041c2d80d0006050b018540300080821070baa00690318100c0d030b039003801800c28020340248003151003410750010002044141c51011005541c00455a07036668908205103500706003401c0c0d41e00d1000300405a09540c0d1400c0c0440648280710002072500e06102d0000c12075516007180c100300751705c1000203001041851780452440303541860042800902407010074003511103120002e400d0f1156074148020076803c0e801919954031144002c40450000c7c0b008181da5008090805520940c82d0122a0400744800d801c11070080c081d0422a03c0d00d13600e081c85403c2d9902c9040c00320216040040d444 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 93028112 1250 93026862 93026897
    0x31e0f0f03030209010e0901150807020307080c0309010e09040b0601050901050c010608060403170f13061103131502040308070206030a0e0a08070b011a191101090609110105040b120702011b 83
    0x4c001e00c45055407112040d41c14207045149c5440e003844d007002070045200018821510030001c03154001e03480302206884003800c07001c00b40d030b0b40c000000903404036658061414460a2620415105070b030400c00210080c0c07610740043d0b4065010200284c10031104001c0c4010020b403d00a000052070740790002c05403481d003420010261030140803400e010080300028840240810040a03070003c52145400d501c41005107401c030001c020207501e1505040d804401c00035660707600074807600d05a0040c00f9600b07444a685c0b000100701d100382d00004042c03900901c07541300035040009c003541d400100c0140014100c050082c0e0f80b8034060459030300f150554000a41c001c1085141300e250750041100b10480f10741089994441805070060120000401c02070340c0c9013a40c690310074010b40301c02c0307100e5030002c000f0150242441f001034012000d0075100d485040d10110265407080d4101d038120f6002545050900c0e403010302e6084e0418016200804541d25a880208280c9100c1c201105043c00c0e5222000d0044c0e00d03140701e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 93029362 1250 93028112 93028127
    0x9050309040e060103150504030203180d06050403020309010809011107110f03010504121e14090a150f020c0603060907111606030207030f110d12110a02030406090f031e0f0f0303020901 81
    0x11b0105030390811007800f0000350000706484803410314001b1015060308800214002c5442c0c030001400c0241041c1c203010500d40c010000b0300034080c0a07078805d021999510440c0b400e80318840b0114081400402c0943c01149000800c00c0c04448008c2402c20302092542c0000d0a4038800d95064610b015000d074205501e80d0801103680c200d1960b6000380e4074445045801510076075a20010700034400001482c0c104642d94501250003074a82c2c0702050501c141c00c41c000038801010919848098480e20300c40503a64030b495420f032881080000c0c540c08031a9a078507822222a140900106551b01c62000f21485024015041601400e400c2c0ea0058803462241030041c0210007646c0c0301000d0092005148071305080116101c09000c800b1304210a02e0711056800c4002008440300c107070072010340401c03440c04013079000c40182304032101d9a4541000303035102c07240c0100058103031000a0141c44c0121035001c00c0720185081c058558010580100101d0f0142c85128402d000c03500110b0010b030740040d0a400c0e56810030503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 93030612 1250 93029362 93029393
    0x209130506030d05031306050a060f060809030414030a080a080a060e150906270105210c010f030b03032b0b010206040602160c09050103110411090409050309040e060103 74
    0x500c00c41c105070340880d80300c1100300c0091080080000008070880c000d65100031826a00c02c0041045182680c4000001e180500a810081501840006115216118680c059038514010310720301445c0c50720012019801a0440f5050302a8800b00f2010a40d003001826404069842d54165490117000210845e8141d402900200c80321205115401051803102500c0f0801505c1080310f6480e042e00288150704844809000c1480b01d40200900d40028032055040300e0040e40d401201d4000e4000c40700d414048490074151650090103d0280d541c0304030480c203406025801d00240507501d003004203003954000caa80700a07240d400d81c1000c0040c10655132054200049880170000421180d000035194a00030740050991500480e18180c1c000c00c0001d040c2006500100316000c55680c0d040e042d0240400348015500507004103004415400c080c001d065405400f00249403910715200c04100050040e02015108d80c4070038825030201d515a0f2040c0400b69680000070504c1e503242d841c12260f9045a0075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 93031862 1250 93030612 93030649
    0x105060c0a021e12070302030c181b04150c030e12070501050304020f0907021506040b06040303050c010b06130519030341070b071106010603021b010c030209 69
    0x40306034203001011a42081c0c5030741c11640090a82c01c03d114000a8141d0085425880b10f112400051808400122501201c1c800d4041d140e41c18100e6041125030903102da03c07a1040306030b04001a000c41404038003d4480540030701c41900f0a0f0311814074007469190b071285040410000e00c880410f040d0000200012258101c4010415852000d55076841d044a4400c0505104000c4003003011076039140108041a80c0c080c0820440d0b01d40742c04001d6403440d401d8481c968010f0160042003450900c0d0045d11a130b03001c080c0c4124a041c2c1340d0380e411076a95001e1100461195a42e5114040c0c07aa00c000040c06254000d0f00241070050a01d001c105100d40044c503a02280c00102c441040040c2d0009840c1c4142038104003074440354a00d90042400c00e10203010407001280d401c0c00301d82030040b8140c000e0190035006456038240350b80d4a0704143c03007020b6981850009548101c2c010446a80f0035001842007040c0710760542e0f200303200d4035407040c00c0d031388407094202c0403a8004c02c1c0360140e030401c0c045142883da550f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 93033112 1250 93031862 93031867
    0xb1315090b0f0108072114010504150603052d010e0c10020115060302070302030c01060f1a0901081f080a0c0e06010c120c080708030406092303040e1806040503030609010506 76
    0x7807149507881e0b4007803140402c114920ba403040e03d81d8001c0101d001c1441e400c05550700c4591070000c47c0d24000c20040303a08490b0b071021900300e5800c0100610503002603907400001009d030140c4810042444503803a07201c84001841c1003400c505403440038050441c2921001c001031418005440810182080e4400c3c8a811680341c000b5aa0907207946140d0b12045841c24140140e0740c0b885420101c0c114401d0300c0c0c01e20015800d10710001074000f4044c01d0501168a0400d120480c1d0841d205048130a02c030340e012081c002494070000c0384071081407404545660700e400207a0340e2010f0f5100d05a90800c1480303281968617201d442010016082c182eaa010f170301000034038106500131400d984914541e44403203100ca0801141608410800020b44203c0c4c08050708111300036202c0c40d003032425601600c0c0c141e0048030201c00102400105441400a4450640d4000c0c06107040c40d0500005010404c401404201c8803024469038000b40d00301030000d00c0c0214020307009981e6924085040c400002010b9000c14040e0204 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 93034362 1250 93033112 93033119
    0x608061206040f0501020c120c120702010806040e03040807271404120e041806060b03060d0609020a09020c030c0c090c0d1a0303040f08060c030c03040b1315090b0f01 73
    0x2042507640280d02103841c1c0c14030482da0130064020b016403801d44c0440c1c45000c44800e00c41c00410080e00d2030100c9402200c0da80c085400e0040418018414000c2c0410710100204a0314680b50704032691580c2208102c03401e29039100205440e03c2180c3c0d10254110f100e414003100002400d040c5032400c0091118180714105146074a405c5810000f04090044900c5c8040541c04c54803070b40780e4030741200006006100d2002c2022260101100300c050495010b8a01400055141040010340c0c0c4504001441c15480e40d40989440c005003ca124007280c0c085019040440c0c02901440a00100e20801d00150f883e5000d0b810308a141c2209401500d11840c644400c00920b02c40b800c0071a003000c06080c4020480701c03104103c524000c41e10780c002a5240c000802c000c5a10804c0d00740f201c0c11a004030303003214603584800c03040848904c01039411800d001c03001c000240102c0d01354164a6040003120b191006801c680351540560202c3c69081101101d4481903c0d0b024001961001904841c0613956105a03526 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 93035612 1250 93034362 93034399
    0xa0504030e0603041a162d0c03120203040317010b0304080708091c050f010b09010f030206031e100e0609062107091104080f030f03040201051b16060806 67
    0x1404084144546000000a8204809400c0d140e0101030031801d103005c075040a0900645104400b20600001600124501600d0001d903140e80040d170000e034540500c0d40070500e01151441640c600c150144030508011121408986c4021840740d4040d43e5101e6071124800711044e00302c403040c0c2c881244a0700900c148804222a4030031110020790025559035502d84003000703d16591507805488808040e8114010203121000c81c0d00e003020703042c0314001c1040004030010443e00100a000c0c80074103d030854014130042c00c088000b0340d0031100301e0007040240040c40d4000c0d2200d05c0d04803082080b40125038400c00040424501c25504140100c1d110b80d610320780300c804210805450803120b00c080030529118001e80724288852409042c950106025082140d002d1400030362081c40347c22014071698802c11120b500110913201c2480318086030915544494004503078a07086280840604a480c0340b0301a08200100898510f400c118003402d1442407078004041c20011008241e140101224900c6280491 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 93036862 1250 93035612 93035627
    0xc0109030312021b0105130308010801060e16021c0906090501030605010e04110f0a02070f060219061a04020406030b040b270a0209090103050f070503150f07030912170a050403 77
    0x1001c2c0c0c1401a11505404042a106030f841c00c09072005518100034801c1f01c038a0141c00c1c8203000d0207034071038a5040e45da03021000d00b00c810605c200c0314040400001700300f0700003500743c0b40f00e103c0c0454411035400b070200365000c24954881051041c0841c01a040401030a6040501d02d0020082400c0030003100d860a00003910b0f1904040784984a5555021500c014280301780c16102c26059081d00544c65035134101019646820300d01800303450300f12211002401602c0000c03641c1c0b075000e03a510141202040ca41c4c1c1d600241110f03102024000c081c404021089440700c0c0301801c000c1401c1d0b900131071100140070600040b540c9000d040c82c041d000741100409001d0440c0d140c106c0c031010f031903441071840d40c2d4241c4000c001e009030354201c2c0c0d00c154028000401d01400041b2540c803800c54209032003159540f1010503688075404811711111182600005021b0000d82c031125601c0640da050110f031b02041c40e51041501d007102110f1001250180008511944401000d15400000004200124209514040e0215 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 93038112 1250 93036862 93036887
    0x10020a050304080a021f140609160f0e151c0e1209060403020904060b09090a03080402100e0a0312030e010b0a03080a05120f070f020a030f0f030608031b0c01090303 72
    0x1080042c00c008894030800010b801c2c0d100c6c9000a078002c0450354075100140c1040d01191b824065014003107000c51811450039801403ca0b00300079004426010005d0f542d0002c07000300030043c409294460800c9803144541d80108141c02c44243d951030400070301d140052582e00c008a0101858818502c10810340092507402c040508200180c650b187c400010b0f4140c440ca8000039041602c080a020030000d0307680180f50001012034a5804558400f031400f5a2901c1d2420040e00260400e804030300541041c990614440900c0e14203099228001c101043c00c4852035401140c003001d01d005014901541441008241040b800081c046002400d0010f9000c082d540009480080d00150020b0050b006038101c6520219118130710798985400c600c100310b20b110840703012000c50040004800020301c04240c000342c2036410f455030300d40400200300464808a030501c10006242e51107e002c1841c02041000c1c00c50036945034803003101056900c8050707003454103100803d410301c00a5501031000a4101c00f804802 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 93039362 1250 93038112 93038123
    0x80f150111070803070f0605090d05070615090207030909050601090305150a150e010e0f1315021b0703021206070203160302071205010b181911070611040810020a050304 74
    0x1c0c80d9405441400e29845a11505aa01c80002e45400304403134082900c016074000c01c1d0401107070740c5000c4420b4885010300b0b10400065030800c0828001509903203c00302c1501210000702800d07403540040c504a9121103800d40115500000c204040e0026000c4d0552100081c81d104c400545560703513060362140f0300b201400b020094480012100040e9904c50881721441d000001c0f042ca54450f51001640c1d0203000d0a807002d6200c0c0001000c006825941d04d000300c0c01845442044085600c1c2c4000c0a20420b81103143c05d60204800000700d08607040603440401c8103000b41c03011900e14410803c000510074a0301729a9040002040348407500030050311046404514007159040c000c1c94200d060040a4026041080e5595100418404150310515003010140e800c10503106010b4041030b00054104c80340c0400070300d0003a8158510080380c00500c0d040f00303040070940c146041662402e003034030050180c04c0000708000c1410050108100020040141600011490440102c4e0010114400104003030301 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 93040612 1250 93039362 93039377
    0x20901260c062a06010e01080c0303040b22030c18061203020d0f020309060301060f11010605060a0c170c0609060c03040209040809060c0105100501020d030501180b0d0f060903080f1501 81
    0x1c03418401c3c40360380101c050390025142d0940c0c4a410725100b0728401e000e0b40490b0311510890807078a003800011501500c24081c500d50824035203481c1810400c5030a24403e007848200d100000c005940c0300c1907500940612800000c0b205a1025020119035207940107800c00f03c1c002107640b0110303070081040d00d00c0c0321b0300e464100c001048401041e880c0d03100e6a4212034002e2800000041e400380e00004440360f4000355030302e0340206d03110034625901f07031581e5005041e8007034010462844454002c0c1d259502540c841d4118071504401c0d060181001d40005c65012060703003040c0308004180030240083c6034815800c1c0070660444c01d00d90007007410101c0c000d00040c009500043c034421140d5480040e60324081105000f0b010620304001b49803c14042c0707200d6030b4050703c180094110300c10300030b0017014140d1310f00040380c150307a4608001c0795024103480d50301150062090500140400e07003404904098038020800854100100e00d402800503c0041c01d007034401c0f044105029403000c1d08008400000006d181010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 93041862 1250 93040612 93040657
    0x90402060903070315020405010306061106070302250f05070e040b0105010e120a030207030c05040c1b03030204030203070b0307080a090b19060503010e16140a090216020901260c06 79
    0x81c9000700f2504064044499191307402d01d6402150010401e4402c00e85e07040c00940d50710310094507030722001441490300d600301100144e0901d2281e4068006805040301c5e9844034006003030703147c105031150041914801038413450501844820401c0200400f4922229101807038540c0f2400708210043c05540d040208107038812050f5615445240c2c0460407101c10b43d0345c0c003009458040c3d524106171008881c04282c01030000b1705071400c0c3c4102e040d09070140c0c03180e15400482e07120304135403074180b000106c0c281542400f0110160300c0c20015080070741040c07a12241d407400c0880c0c01610016008090110300c07410459070100090000d071840340c1006401f4004660b4188c0004110b0142441e07401c940e8041d031800c1d8420411000020750818183e200003100d080c80703500c03031010440d0f605680c088a40c005044010800c41c01c0c5e40f0381e000700440000c000b1094070001540c0c0c0080d4002d00207074890b42c02c94001510030f1082c038880c419840b1012042d400284a051458808a00c29028800554181c10003454241 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 93043112 1250 93041862 93041869
    0x2113060203091318411b03030705030703120605060a05090d03091a0a0323010b030405010e060c0304020f04140c0c031e0316090803040b1c09060c0e030105060904020609 74
    0x30f50540e48010300c4220342c20705c54032030860001400308021410b8034180c1200e0103e813a501c182c1d903a40d6254009091654120003040c0e07070184100012680622040000a012400070300251101d00e100e0303918034200c5500701a02005461490300464030514007081100d002d40d401004803041510140e03440c4146a81908040e610400b980d408130b0358581150320040112103498005010441c0951001c000385014141300030026000400d4000409400b04014442643c040b800355038410301c180004221403400408050070645d00762840114041c002c0b00780300840c680750305112403602c002c1d94100705050341c1710360700000c81e40050314070300c81e002e000a1000001d10060086400032901140300030504414107034024007a034400c8910200c140c8113405441d85007441a03290004a0b00c4c0d400055007800d081140c0c5250a0348600e40c0c000312482800c81080e02c100940c0584403455001da8000104d94020b100d010f0a088400003005110781d00d82403c2041559517400040c3d0000d8059940b2078648a48a020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 93044362 1250 93043112 93043151
    0x5060f062b060915060b030f070c081909050a05090403140c030c12040f0b03090304030813360c1b050c06030c09030106090e0a031121130602030913 65
    0x42c041500303109100c014041c0400c0301182d03481c00107500700b1a02da6184d80015550005881d6601c3c1034a19038089284584101c2003054403078010400f0300c0c500840c514a8a8030400c0c55074441010443c44182007006140103002440100000c0d940904a032800c0c1c0c1e00100180402c01500072544008511040401020025250403c41013411100f81005995a0b04059081886071480501d55034001003900748108003507a0180d0782200045050904660302c620300c41d004036400800c02d48458800184404905040c4144d1a040d0070383c141100c400c050740007000002c030b03030901800c2c14142405024450f600450041c1102a2140000300a42c014a80b503030401060b2401d407a4010000b0051202d03001410b401804030020440c000c10149a03101c08810035508844054010b42c0c02c907100480110340039444a0f024081c03020156800710317144412044070b0342c0800d000454500000f090395030180525860120151589000a40c14441c44130001000b181e81d0303206000303016440d44503841008070381c5140d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 93045612 1250 93044362 93044449
    0xd09050f070b040905060a03020607060209150301061d122805060f0907080a080301051c0b011206050a0e0d050f0d1b0206070c0b06100c0510020705060f06 68
    0x10750307108942d030b0000d03a2001e0700140501c444191408003c103000e45090744a41c41201c1d030240900d401c0c80f402ea1507500080d007204680a403c00850540e02c0c00c1500b0300c900450103061182c584001d11401c0f0550f41d045030380c0c1c0040040c001c00380724036454071803600000c2c01e045244c0403082c1c00c3c60201c0e41c01015102420b2141d4010003610a0009000150f08514a400d00c2100290f00301c0300c11039900c40000340e0b40c0b0f81c206030260172500c08000510460501044140c4a00c0043c805024120f03155603074403404c1e400903031080075140c3c1f100b50040c040103030078000c80c1d803c0800da84040c03200345404041c1031703118281d06582405103c4002540741d02000048180d659540a078201007220188600e00c0200640384500b1040040c0201c100082d5078038001d0400880c026003092400031155514400d1000201c0040108010b00028489950018800304400b10042e0481c040140e140e00d0320740350262030700c500a4042070407405400c0400001d51103882c02c08449045139210440d80502001510720803030552407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 93046862 1250 93045612 93045643
    0x90e0112021207060f1701270b03070e06010e06030903090907020a2001140a0e01030c03060915031a1302060a03090203030706050f09010605010e0906010504050607060c0906030509030d0905 83
    0x10f0000510ba84c10800c801c1d408aa0781d241e00801d4002104a520281001d001e1310103042c0c14072044c09141f4030003144081548000070700004086110f280060f207007103140c1d48201c0606285908104280d688502045509901078074024254240b0070900d079101d00030210024010b402c20740000700d0040c400c010300078000d6044482c0d402c100340c103841802c04001c5000b01d4a40407034014074113008051048021222181442d0b61544c60310510f02c00114080c051000146c0300f050344800e030102cac800809214181034081c085000395802895450420907446a144030b680c55030703105004105081800d1242c4030407095040701c4455450031244010760013008005400780d0184008140d1070100302c2d86920941c040d004440708000140d445480c035601340d40c030500590740065404c280e00d800600b0400610713a00010141815810651110080b40716074001d400151342032a1101249c3c0e100d140c00c4900303c000b40c0214602880a480c4c4103035040e03520301c61503903034400840c0c1e114025005c1c44410b001e042399503801070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 93048112 1250 93046862 93046873
    0x100318030201020711010912021306080f0601030c0608042a0b040b03040501140105030c0103050907090905100609050408071104060801050a0f050108030703020d1101110a110d090e01120212 83
    0x2810000c0c004d4008090848901d481c08000c0c1980c0c0d80030b001c2840844400518014001a495081c03200360841354102409641d212640481c0452050101200d12803064006011541c03450601a03400c0c6090b9000106000101c0180404280608400f1032026185ea03d10400095481ca5040d03c615442d03100c1111030a0205001c40d5480d600c1d0b000b94000c0340620000c0c4100c00b441c1164501e845000c0c802c240d4940c0c800b0100345a15400b0307401c581d03404121102070701c090726980c0c4510410380d0b01c0c26008440b00d40080894000811262003500003419020b03404020502d060f07950040148120b560140c901008620840d2017a52150030038400fa00040e4000d001350f04184c181c4502800800b1402c4a1050800d0004901a00000240e4161607010350080040c5c0d4101c0c0d000b038440c28103205103003805549480c9441d18110741e0600a0810280a0f9101e51b00c512094010500340602160070b4810003a00f00ca040cc219030041e4211819181200c88401030802c0c18400034660202c1d48808005900a2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 93049362 1250 93048112 93048161
    0x30c030703050301060e03010c2703050105070806240d020c1f0501260309010806010903210f03230603100e0708060601050c06150a0905090c1c0305091003 68
    0x40043d42c104c42d441d8603194031480c591410075003a12100d050032000500c1c9424048100044800079040c03c6218044007807125840c3d460307480c03e50307401f1615600030440000c140089030800329a4100340030601c0645822860f411048558030744244804680741580101c2c1211000030207000961080582a4800c1d1070a2161030030324002c0c1200341300d410b80350040702030039280b206c0708100101c0d02d503074101f000b442c54140305d0401074035040005003c06041001100c00800014082148030444490a203032001440b142d084008001b60500c250380b40415003000ea4203228540c0c66102e40110040d0070901454682e20303400440e00c1c1101c4000002a000d0409242050303041e0007140550a554040e070a4640c2e568404006589a21945a402c40c081d170180000803c00590741c009014054002040e0005107030345c0342201d20580b030040d01c012490307401807442c0702034600c0c0034105000e403115000f0701d00f241140a5180a07005005074500c0c03900402140c111061410301c2503204402c203007484842c4060a500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 93050612 1250 93049362 93049367
    0x1212070207080a0f080d0c0e0f06040503030301030803040f0b04030201020705010b0f102703030e030105060102060609011a09100815030c011403060a0504140406110324180a090506010e010308041205030c030703 92
    0x84494a0107260715801c503030504e02b0710000711026158050000d40c5140d103103030750341641c5500c000d1003640c18225584600d0006052040c0448c040c600aa001680301c801c03904005007180c0d401d0b6442445210700d42080c403490b45030100c8070100c5010340d050480c01600c680c940c500725a58881c3d0303201c880c0800402e0101c01c25401c24203030a05004241c00800c440e82c1c440c0d0040e40e40d04e00603102c00e58000a440010885034180141c0076210303034038400405003850203410108110304100d0800340c0218101e6000c00c001c991020382ca50b407a040303088008002d100344d024006484035441110080c4005070010009041d80c0740d1980d584001d02c4050803c100441e061400c040c4022001d0f03074101c3e885810000b20f510302e034403600292030041290605070314140d0803007025151400c0c181c80d4000e81201481c504013040c03140308184207105118003800800c40d03d800d0b02c0c0803410003405800c00c0c0305000e4514018404290410155000c3d50300c00b898040c0e2825090401030f1441c016140307103855910001a810b4109070b03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 93051862 1250 93050612 93050627
    0xf061410021c0f020708010b031f0608030409020304060c03060302130b040b090901060f0b0a0e09040501090204051008010e0f030a030e0708010203092109010815040209031212070207080a0f080d0c 86
    0x4107580c244c1780780b680c0703484810742a41c0c1407401c1e055041d03200701d001c500c445c1d500c0c94070740050a1060700300045240d030b140d014a0460300640c0c840b21210b07034048100002e005042c000d01c5903c10991804129090075030340001c18081405104440340d076601c0050b1840c80d220340c3e02105400b44010900356980c0780140113180038000c2401610300b17030541c1a9000481401b1002070350304e0700e20152281da10541d0020140700c00d61000500507078040d0748401190000da100e900c00c050040b10b942c04051a0a42060303002c5080d102c4071500f60000354001e40980c0c0e061407002c016148c5800203484c1c046080801549000e280c000b03070350000c6000394400400c0c010389544c0000d10031104004100c075014000c04841e1000c00d41d0203000808c0e0b000c62411800603003c9941c04c040c0c00c4203080000e00041c24001e06a01091528100a49c074242184002900d15643d160b02403490307501c41c4043c4024002c1500341a0001e84881d2207000040540c59010080c5081003804401d8894003594001c04025829010700c0041001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 93053112 1250 93051862 93051887
    0x18090204180204140408092416030905030313090e0c09130201030515060d0506041808031f05030307030e04090803091e010c0905150c0106080307060f061410021c 71
    0x880c80c4c850f200d41c8075003204c1d109500c01c1e60407500c2c4604060301a818499010030f283c8418640020f080f042c0030002203414003800700100034070180485802c1514021b4080c0003160096442948140034082c036103413034410006c058801d400004607030008c18015091a0498030304d103d40c1e00454030b00420041440e465200303c1c906000743c1c1cac1131240c0e0315180380c1c62401980c50291503400020822036054a40d03025000309400c180042d00000b6514190240c1a5110460010440303800a00000b4807a85444006c64040b100080440c1c10b2081c40c0b80c8030029940e4412001c0040500c0540d007070903682541d131548650144c82e00460f545540303150816029403503069040d401003a0720f5a8072104525900f051052413a801100d03128a03561505000030003400381c1d030003140c07014204000c00c10440040028002c0c1401403031309a009644403501d52402005803481d01c000c8549107032400300108501884c071000416400b0064800120801200100b20705001d00c4e4611511003503c000e40004909074000042c2544 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 93054362 1250 93053112 93053119
    0x302032a0d0807020108042607060b0a0819030309080d1d06060108071407020d0605071b0b07051b0604030e030c03010e0a03050a05040807060504170a02010207180902041802 76
    0x140c21000007080380c40e00c0040301c058109501404040010b50207005126003041c0240071000c0614000f184114000946012420407a140491798404122580c0151070242c98101d82160040b4202040396030340b21008207250481d030040740150340c02d0501030740c005018150408003e664071290b062211300030b0904641c0641c568203a020301008070520114485015540595441c48240c41e0854100d518a00001040c0c400304000c1101c080184d4607100701c1c07111680325040c0070036146400a005400c030618985101d0700030704012041e900107659408c0035603100300c2c10b080c480d48544c1e02255010742d00d24890681565413007240180002d141d007000c00040da6000441c11a05604c03d003505260903038541c24054406030384003030309040009009801402c41500945040c80c00d044d80d500429103401740b20341c0f160010030300002d800c1c8800c0c100110750429105070b62000303000ca0986540001d55410081c4200008422994103007071b0b0300c0f4915000300c50810780051050000041c504c1c0c42c810100e075807000c224031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 93055612 1250 93054362 93054433
    0x7090b09040f081c0605092d0c04180c020115030b0c031302060d0504110103060b071115040e0103031806052a0307031706030a0206071410050c0310060203040f030f020a030203 77
    0x600c3e2184034003810701c04808c030144805941c02d26040c1d01c264440680901e9071000248000308290494a40b90040300f00030070404504060545e0010382110b5a45070240401021801d050001c00d000322500c40d0000f00f05800c2c0c0d80e480e42c914204800141c00003400940c40300d00080e940407490420f8103c10b000d94000c0c0518023000790004c006600f211010700c034220003802d06112a1000c50011041c60000d4a0040c02c03031204c0c4010030b800c000b43c41e8880d403c00a26030441000510074580e01200300703480103002c0c0034161603081c10a074019282e40501006820140c11b03100010000c0c08030504d980300d40c070421504132034840e42d50b450081c05158103290920300740740140300061003078039000500381d8010350007400075443c2c460651140c0300300c071a032840f90b0441c80c8070380400a0407095103803044912804144c6074440c1c0b0307810310003903140d00084036a11000440d4018007007030100310b0341c690301141243d81c00070207491244800e20104941c05010b83c400b0f0f60500802e40f0810051200041c0b00081006000c00b114 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 93056862 1250 93055612 93055621
    0x1527031401060b04080c01080406090c080f010f090b0402100c14030406020c0d030503072d0e100306050109060e0d080a0c1401090503070b09011b02010b0307090b09040f081c060509 79
    0x1910f42c081d5114440c4c40f80d215400080740da502030015545c00a002d943c001c00e00c00c5031501e4444025880d9409025294815110000c15407801e01c2400c8181c1d151220502c23503510281c480541055000d04007030701c2950018100c0400d06d00810180070110b50118446038401e9041c07907429125081840707410058001d0104150729460859030b00081c0d541e25484843c2140c4030a00120b981141070800b42094046a8074820850f1410214071040c0f95140d80e191206007c4000034800c031034512248650515040030301c10b0019a0f0405044c209039850351070425048904480080c402c5c0381036020281008200040548040d1b0f40450150581c030300520a07800e07149404d4050a00f200c0700150050b00302d400074003d010004400d66102504150b1080020500f021030190403c54445c0a10044025070340d05c40345010719003000d006440c003c020300c020801c90008000b02160101c007000b0001010021070940003410004104151040b641d851613014950b0908006098000c160780d01030180315002060024 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 93058112 1250 93056862 93056879
    0xa0f050c03030a0b0a0f0e01090b12060103060b060702180405211206010e1e01030e030c060a020c03040e04050a1a0c0702040f060503030d05160504152703140106 71
    0x210300864a520046207981d4a05580c04018446018120b901001031a00002d01c03580c480040b8024210003c0920f0080d450300e400030084900d00700c0c4041c003c4107601240000442c010405904480d005030003c5080d00074040050200c0c498180c000350311010648001c0120702440c441988160b2040b802ca40030f0102601a103551000320fa64000c903544002c1000103c0d01448800c01d641021040c10801030081e10080040c0d50349030f42085281c540000c001328010103690501a081401c120300c000f5514100a00c1d11590310303100c0040c2100d620a4000580612048040040720010920b104e0210b080d400c207840c095071901c003046020b079040240c40421000c150100526980220b0410300581d10f410700c07aa00f408050300c400d11a523490140e50306800211900c0902c014400b4a00c03486d000590b526240d40c03c8042d00000c25241c0d4200b00f028081030100940c5903480f08070a100d00e091903589403041c036484c01d01c1c01020703d0103811010140325000042140d80c600c46095118403c0080c4002e64540181 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 93059362 1250 93058112 93058117
    0x118030b040b010e0f16050904050903090a09020a0909150e010e0a0e0c090601080603100c02160b0306030604150f110703020c0405060a091e0203041103070b040501050306040c03140405030a0f05 85
    0x1043c0c4a064050101d106c0b006901011543c0c200382d0308006091014030b0703000078101c1c1c100325515680c6400004910200c1d140590400000e401e1000c0110b007452030104006080050034080c400d14155150284030b04012070f0320024000300b0100c81140010b41e142c10740c801c84810103446880c0c0490401c0c070b4500030400e020603114a0701d10094441041e507940c071001141c103070101520301c640601440283c00443e03030060003503030501441a0000c1220099480440d040d0740300b1527110741c0c00200144203115469402040864116030015511f104000541d00301d1030003400158040a00c86142020500e40304006e2006403140c10b00035001d851507140b000090000b0b840c0c0444407164003058800e002c2c05400f00b19131050212010413605c0410b0b40181d5101d45003243d01c04d541c00e5078441d400c0202c2500c2480c00708003020241c01000455410249441d00280c980d0101a015034071803901c1c0e03000030200d10712a82c004680700d038580e81b0303420381e03410582002602c9505c0340c0f2a2600040c02d007044100c50b14012001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 93060612 1250 93059362 93059371
    0xc1404120204020322050705011407050d032304120305060904021f230301051002070803070816021c050c0103060e190b060f18040c020a0201030b0118030b040b010e 72
    0x10921400c099039080100130351000b040485201e90400481400c907803240c10b41603c00303118000800aa504003400500071080610003146144410850440004d5000c00c041002560a00303003c9103068200c001a8090881d4071019182034440314100000e01c2210300d03004410102c036440801160304c0704401d21240b0101290065001241c100c3c0300c21002e08081d0038000c080c0b40928000013440c03020310132028120150803112407401c20100043c41646041c001c0c2c040b40b0a000e00040090314a041d10081d107e004549004d84500000300d44000c411042c1d0440c81c1d4407690003001c0072312420210440110740401c840c03060340c00b0300c00d007079020f50b040d4001d11641c420740d402c074080035a4950340e00e41c40103005a035140340c01c2c801c11744803c1d2030101c0382c4983c00a000b0b14a0324894840d20380407051443d01540440408041c0b08a007010414021280c000c85c40c070341d440340c080c80d000c1100f1520b40010f030b400080c0c2404101584054110000a0004014030540650310508503280d0f07590360b581d5141d15074a0140d6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 93061862 1250 93060612 93060629
    0x220918031b03030b06040b07020f0603010e010b07031202030702030a140412020f03010f050f040302010c14040902030703060e010602030c010e1612170316031b02031804020d09060c1404 81
    0x81c4039a81502462960050003842440c02081d01c000d100040380701c940041c2d00107400c07090003080c244114a409080301240300c5003601c2903421503143c0300340c03200e2151040c824801e44910009018083c188103901d14111402c07421010b42d0b680c00d2100000750b403540826921030010341669141c1005800b048112000c54100000d480500505502080b80510070045125495035982030b2030b500303030bc049000c1e0501c035440c40720142e0f2852920303041c040e02b5a10600000c4c81048440400028101415000d450a84068000042e200e80e41c0d104140c3c020800e41e00300944503400354000003a25030380040103002c01c410200c000c0c8040a0400291380e6035508408000811000070305081c002d80d0209895080282e004928155051011214001440e401514001c40610001080b614241c3c0c05000744160440b0440c0307600100035a04100941307034007902411648440901d00103c68a54031601901c41003c03030400e0801103e01140380900051820324030002c041804148600c1e0305e1514441a50100c43c200c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 93063112 1250 93061862 93061877
    0x10030e0c100c050f01061d07020304091107020901080304090c05120402010302220e180607020a080c07050909030c151b0904060914010303020c030f0709050c22091803 73
    0x303001c1194122002501e1400c0003410a044800304208020000340d54002e03000020350b8034100004a100c84040c02d16101c0c4c94881042402440c660010480307044403044c0d0000a103207400c5c00040125071282100113503002c002c2c000045400724010000f442100c0d500e0b402000310340119a8295640e0140c0030340c01a164011200140155010760000c01e805071100004642e000084032010700c400300107030001e0030780c25010020001603403401c01302c40b48000c00d4100201082c2c81c00c0e800c020f68500608400902c407450114641c40020004c201c400e0203003100910881c25458061143c41d0fa03500048203480e8244104003800e000300d80510388945c095104a00020310345001c0c510818500c0c2d00c15582260001d07691040060721050504c00c5011101191b6a44980c0b5455402d000f498203a1a02c8810300c40d8110001140075400002007400441e1444000400c055036088a44031540c0036042c044043d01440440c1820317802c1c454403880054030103010040244480420b500702502000b00e80040224610 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 93064362 1250 93063112 93063133
    0x4090c0e0603030c100606020106060306030f03030b0f030304030b10050d150509160305010e06060a0b0d05090a1703070915080c03060a090e0f0c04230c1201060c0210030e 75
    0x148509140d00101c054100d9143c4804c0282440c074003120410303004074060340c600b014450309a0a004080080c03000c1d1406100b4a13045440351400c544442400409041d41e07000002034a0310f521450b07104004c801015071341c45a0b540c1c01e1698a84508658542c2e41c21004a0040303400d1134038401800c0116000f489003c10340e01103981c1c940041102400078042c0b4412005418140300409404801a5100e40000701d411000249410300d0310710050700040c8641e5164000b0b020040c1103200341e40c07079207040e801f01041c55152403058a00f000b200e00000303450211035010242d4181e00c60340040d80210180d5030391b206003a80d40d08840d181100030840280010f207000000c16007501091015640200004114600c56551036020380c0840d01040c1101d0413a4202e444600c10901080c000c0e9401b036001600c040c0011590216003040f0a8582d41c03043c0d1903070543c0804220300111a00564220b000d04a10081076941c507280003034640100200c0891240005c6c0d054680780038840d0082d4100d03440c0e1000201507041c207 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 93065612 1250 93064362 93064379
    0x7020a080d0503130c09090f0308160e01050706060503011802090106050a05090d210224040507030b190e100b01020309130c0e0a03060b0a300f02060c0f060604090c 72
    0x482c00e6040da03c6200030300e001b10300c2c0d208503c00c4181d0384c3d01c10240040c04c10b00c0c1e4038014110300c400030415003414025192001501d5007101010070042000d10b04079a0b10030b1507251038402009a500300507015071810701000461f4003880b1403101c0e01c9000311072106041c0c0e81c3e20411a5144100d01600002410070b211590407070511100880e040c500c156240d01065141540320641e601207104d0ba40f005070310210f185021400c0d40c00441c15803506038101d09400e85000d032140d647c0c4419900c03001301001140000202200c0340c0203400e55007580c0303600e000d000c039101c0c03441003a54400c0351881034901c00d4513041074051703990300000442d078405201500d00790304405410034100081407002400024007101c92481c03032245e96514140360280d482004005502680301c2c0610200344810380240100b0070302d00f0b1502e5441d14545117190300030b0b81c0c0701205c1118501180303032400d04441100e400030340080e00816456900075001c25040266454081184ca256561904200c10380b0508100500f00d0384080205100400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 93066862 1250 93065612 93065641
    0x3190f020f060712020109031d06040b0a1106090c1008071e030f0e030d060e010320010332070305060609130905030714070503030a08010e0709050901090207020a080d0503 75
    0x700000e10950601c1c41c680c4400c401c0b4a04254042c005035034452140c0100354100c00d141030504000748030a038085079100c010034481d10503409884e105840c0861000903a511074001000411207041c10303500c0e1410400701c3c19984000c00c0507014400ca0006104100d40c0384036442d180c2c46281180c1e50841c010720898035610403030918005540070107469401e0100030b5602ca00524044c0c1c03013500011551004500c00003c21100160004564601c0e418010004510050b100110440380e02d00300c6c07000d88200d10016402000c1110501d13182c0d05900544100c031920000014100071114040c10000380c0d2000e40c1181120400c07241c2e654800c60600c002026400c0070181d40700464800900050300f03110035107a441c41c0d034102000072181c000c250615510003038070501c2048020402a001903041201d88040030b4052201400746880001103940003502251140c440e0070024103000d00000481d5071582861000b9512000061f0f002d1004231000090010300080c8030542c1900e41d07519a070650700c51045801010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 93068112 1250 93066862 93066889
    0x303090501110301140405060306060906010f020120070605060a0b0a0c03050418320a0504050312040303050601020c0d0f030c020a0801020a050315061612050d061403190f02 76
    0x9641e1450590003004001d0010f5000c0c007490096075403001013136400c0005440c0c0080103a8083d400032010b010b000c0e15050310103074120109007050b080c0b280907000f00702e0040c8411611030a5140190249030384000d200310043c00d58a00516040c0170342d503594814060912014410380c0008001000740e05101c5200d51280341030240705e4a481d920b060703a03602e0081510085040740c076110710795482c0f0009410300040e07840070800403a91004c4549811348c111020808000a207007000464071400014208441070048a001c00034a00700c0a046052605004000382011604c041c054480c0c1c000c122090301d402c040810249520240e952a0101c0690301103840300380d5008204c0c3c01c9060400c010410b03c00a001030100c01d0030a90f1001c2c1ca91605581c0e440b40c181406001034000ca204120310310aa10800056503402600002d10805800c064001100c03184128003804ea601c628040010650707140900c100c091403201102100d03022514101030311052001c403d001040886045080c03001400d0000025808 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 93069362 1250 93068112 93068123
    0x831080d060b1317060f0a051803031e01171c03060f0311010306060e0609010c150e0109140601061704030201021b010203062b0b101a1b03030f04030309 67
    0x81503514900b20815410807943c066030481d1208003030120a550f0900f0180ea085100d00400041c11710041248081c1006010610095281e0000070346d600a020b8088480c005000304a82d901e01d82451010403280320540c4a05400400b0800001d480221031048086209503001502e50b9124061031490b04004c0c2c20807801c00d160f1a0800080e981400101440040d40070707101098076030803100001000c6a01c1900071a0a004401708440c101e41c490800343d0340c400d070080c00d01c1683d9058509080c0301c0a401e00703103c0c00055051040c450480c18064011a0f03100e44241c50b00400707a1030715180703c1e4450509000300f0740011002001c604140450058094010707001e80001442c0c03003840c0032669020344100103c0d51850303400006115a40c180880c101048030314400701c0c2c00c80745500b281d90701040100090050402c041da03202087c00c0025550ba180c0040000c2594201300110b0329000442c582c2050010a0804403880000341d0b250301c0101c1202c1c4211100c9543c0807040c1c3c1c881d40c0640060944e440305450 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 93070612 1250 93069362 93069371
    0x50303040b0a1b141b01050301060905011b170406020111070807030f11010c09060f110606040b040f0c090503160f050d05102a0903020a0b09030f01020a0831080d 71
    0x4150a810b622461402c080050b098200e917140c90041201c0c0c40001460402030100010000720b03500001c4082500c40920303003c0c2c02010410080044e441483c0b0303000d03200810f804815800312207104005c208660443d002807100c091840701401180c0103415010304100c0e0104000000a4810f200840800010341050324000114004403800c544440000b00701043d00010705000450304a08194200707034070303450500c1007042040e810680359072025110500442e11401071001d103070b403260400d500b00c013403040c0b040040c001415402001e40c40a07100c0da81c06409121080ca28610f440307100b03402622380d1841c0d104403540c23620003440050802408240c8543c091107603500d0901000e4081c5940008022004d0304082c001e64488041c01c1605804100501103000b008200684403281c06c00215503c0d050f07800c0d10f88500c880440d04103a01d81d50045015440003906103003803a0802d000034050844100c4811455141c28110400c40c1d00144241e46c40d2420300800c0d20001d50790704014040403100210105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 93071862 1250 93070612 93070667
    0x606030a0908220317090a0902090607080c06040b2203081e15010206010501050c070e15060d24030201020a020405150a030507090f2c0102190513050303040b0a 70
    0x2100c0c3c01c2c3c0703210700450105001410000d111000c060285040080c0610030f260440503000034030003009500c12940c1c25a004218001d9030760b07800c4d0a40755070070703040707a069503444842c000401c0d00d4080c203c2d4210380003e1001d000c100d901e107000040d18031440d00c030001d501c210121502c0540f80504001d24400301801c0c0707141c0c64941c0d84c180f02c00f02c6000d03405904408090100d03135000a81030030303016004941088001d200000c088a00000c800c4126101c583c00600070b900e40108041058200a03085504100c000510f103142c0a069400002c035031441f2942c4144020340c4104c000d036991118403000c1c2c0168031458805000d0f00e003941c0b04175004081007407600d10310031514000c40c80700303011a48166582d811402040001d96880d014011110644407000c115032a1484004950010003000f0840200720400300922450003d504540080c07a070800c042a000006500040803540650000c01001c0c5000c0000500c90800000781c034243e030350440c5843c2c01d01005140449002c0100a03c90f01558201300c1d004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 93073112 1250 93071862 93071887
    0x90d0c0308090307080c0a05090c120c040602010c031401061b020306010b0703110d170403020109050601090506010f030504020a06030b06090913030906020c0a0e04050f060a0b040605090606030a0908 87
    0x400118815180c240e1241464420503080955a178012840c07500220314041856480f0f404410950740202c5158609846200319842e13240a80e004c0701c099154001c0034001c44c0a084006002220340640c000e10006e09441c0c400c50070381c3c0781e5848000040744c620300140700c2217001d1070b8030b24100301480304038110314901a00004c0c0750440a903c18000c211001034000f00303055009101403015041500285003e018004000f00040340b1600f010030010040310116080610070741081c24426000000c88116585441c0d01000030101a22000d000c034442410740701845000c1c0c0038141c450340e0028582c1009500d088025030107000c1944e2510392006007045005419601d504249001c1e65449a070404100660b113400703000c1d010603822070401d6510000009000da40c41c075520308140c6014089010742c0d502e43c1c1c64117518060709191800307800d014040802891011503445200c506038119028815503039220b0911440001c1551030682003507041000404050b00c0d80c00a0b00700701e1003005039518104850050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 93074362 1250 93073112 93073133
    0x6130812091e040b150a09050a030503030402010e131b26280608010209090c07110121050f06090106030c0212180a030303020c12120711070b040e0109060803030417090d 74
    0x207000d03101c0b10208031a0181d59120307c0d042c02400064407030007040e90031626440c0d9a40070040000381005142d14011340c90f0780b90b00081280301440c00000344030140b0000142010300500800c0b5000299081002c201050050400b0720180c07245101209181d440e1407031451140100340c0c0300b001c81c07030340003141019040d80e49100d040000e140703240005894003401c4d8100b0441d400050903c14201e681403050b20003188030823000d42040cc509003401d0285840304807100403070800344205a640700e480c1c4010003948810f05011b65110310403c450030704150ba21110254200d40e83d904141c00140d0000e4020362044082d24001d1825101c0d142c2405001da518900150601b1242e400440c0002d80208003107415681c2001030078003a2a134110601c0c100040705040210b2410000e144204100100980507540c640c1030001202070142c142c00c040d519134030780544090070b000a210b1480118540300c000180d1b44804029240a41d9200001101c40c580d8100c104a003030700082e0601d0f511100d0032090f08001103031020b0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 93075612 1250 93074362 93074389
    0x10905031006080f0f0d03020306011206060521010614030903071b030606090b06090108100801050106030c080a0c2102120a06031e0c09180206130812091e040b 70
    0x301140c003e05140c1000e0800b0201124100d1962000030114213000020880444d0320a17540341c01601ca0b6242401210015080301c460907820380b414901050090307005000b0008c4404404072540803c60064107114140003d12414000a1903e203800425200c28401150001000310459003030000580b9142c21090201038112071460094104104100c02402994001c00080004010580231000418414410702c1e00041c104440355000074180040382c201a005001200e000300103d60b1a80f201a000700407400742d80300880c04000c00620307444480d0080000900c0b2642d034031240700b001150300d281c0e8040d9004880702441d03000d1002010740c011040042d031040c417030f0b0310000c07668a10b1810461304503113460f0501000c3c814002442004552001c2510303084400203800040e10755103141e0f007100041030810000354000d074009001e0900e600300104c5441910011400d40701100032494074051a4414540b107640c000b14080640b41d4902075060692410800180010840d00014000510529000308 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 93076862 1250 93075612 93075643
    0x201020309090109060e0106090b03070f11012405030c0a0902070804120b01030210320904020f0705010c020601030f0f0f02030f010903030e030f0f0d060e0a0e0d081303030b01090503 80
    0x5c404208940959220328014002414411019800c0c04110f01c5180b000404500500170b04085111205101d800e680340d4168004000308850135401164104084520b40e00c410b801134541e00c08110351401044c2910084c00c002d00b22990a481c2c001040045d400000040d074100c00b00740800540c1e00e21500e2013008262054050481c5581140b041208440140c002d400400c08407008201010104020851070f2121081c07141002e1504015108424800c0294280e04a4004a040e8110501400141514038070440091018484a81049a40d04c409104c040e02d200950481e6801007104c1030440b200b03081c01180340d5546460f07140c012901d48003034510910081e030355403040b00703050685c103204d4085495080342c040d51030500d05004464860003460880d203101d110004070201e13a002180d01610051803160340010301881c081c40110020810704449480074054540d0340004188a40c00303082c41181d401e0b1000c2d06614007134404400900b080340c1078506100c205c00001c120303640c041082c402010382c200e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 93078112 1250 93076862 93076871
    0x22110f03010e10053007080c030d0f1b050a06090809030d0201050912030c0412030f120b1e040e1009140a030c03051804060603050a0c0e030c04090201020309090109 72
    0x142c03100c00844010b041c02c10341c90075180140000e82d01ca004040f03401c8a41014503c1e01c07900c4a5018006804103504c46903548580c8134005152100410251003440003101603813541d40c118501940c1c0c100300c5450802c001804c11500340501c0541d0840c03052080c0c02581191011219550f03050200e13280800141c8a0344000f213a0035049107401c04c00e15000001501c024010782c00c010044564400c101c048100c022540800060f1941c3c407698256002000490070400c0f01454508019048200228900c00044c1040743c500300542800e0103a500807401c054040440c4214508072401900350940c117207131307019442c3c0d1512003502408000490049844a00014002c9180d1400540340350b42009201e04c0c0760001451200401d801c922002500c03501824410781d111359801445442107a0040000e5015192107008106076a0640c030152044000b4101080034284031074065581c0203410a041c3d40c50f9106204602460802e5000909840d2040c0101c82c1001141e900061081e0740c01d81102e1400c9aa8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 93079362 1250 93078112 93078119
    0x6020406090311040603111002030c011a03060108010605031209060c0d0e03150906070305091c0306061b0215180915041407020307030f14030f0708010b040522110f0301 74
    0xc5600c3c464040c0b404950070400c441c03440d65028078002041594a10a40b40e82403484c841600034800c032041d00140c2c200030410350801800c2c20148560003510719009108010000c64285414881d40f801d0b80c00050050035100e400b150841c6250307104008440d0000000c1c0b00030011a0740400610008100c2e984584000c041e50000341840c10281950641c180420314080c4024540041602e070380100f2607243c049102eaa90007406447c0c80f03880350040c801c9481ca10300e42e1802943c0b550110095415a5032198402618804050017141078044c010354800100c1a0110703840c2c080d2001842c80c003044406001e001c02103900095041981203840c1100d0f0f110b09400c4040a240c14801c100c410300e01100030320900d0624110095490042a00060501c010200010129401142041400207040e00343d69660300d4030150326802910242c6200d008035912034000700c3c400d08c090059a0690700c0250544420100a08158882c96041400125442c1e40d41c080703030030300000030001002c120f21900d1505540754503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 93080612 1250 93079362 93079373
    0x120607031b0c0b041e020907050a090608010302010813150c030e0105010605030123040906050c09010e060f0f0d020408030408030309060f0103020d020609040e0106090b1306080d120603060204060903 87
    0x107980000402c0200310082c040024028021643e0000c0e0401e80002440000303151504800c2c1d035030303003010390302a42850800001542c4030004000100e00380e5a135850b503965035841501c65007828000203021070310200001c2c0d01c0054642040d100303103014500b44d51502c0c65006149040380c07007481c9050000380e100c0600201202003400b4a500425592a202c2d1841d807405403040380c1e403480c180e20800041d0790210b0b0b51130650750f19040110903c0d04060300b0001d80c1014042d460700e60b802610041d0112308c40c034200c0d00c1d41e480c010007070311801440ca000c028900702c0d611038000c000358400421000d0081d0309010200d2181c404201174000b805034a001036550b8100540c8207440e04500900c00a80d20002c4c000500058072507800c2e02e032400d030741914415140d806540000b0301500d02c40311902020341c6000c00c00110402a40c10000100b03070266501189140ea0b807804000f500da507801034203c3d070752207501c80c041f006200300b100b124200109580000d040b92079607034444c240d078425800040003030500e5005005110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 93081862 1250 93080612 93080651
    0x2030619060e01110304080d050f070515090c090705030703090507080304080a03021203010b0405040c050d110a0e0105250219080d03110c0a1212151418010b0912060703 74
    0x130200da0045051620f45542c4035aa650071400440411201040c1d0542d03202c0343c00f040e90340e076580c440190381028094440d40840c440302164161298410510f40c0011810100c4c0000e008010b55910286941d580250540c00383c84210300071200c07440f4034400018056024000741001d0311401018101c001064200245020000b4505850a03c420070041111481660403541226415900800d06040140302a23989010741880c600725036041881c00d4182da0210f8000f05a00d040640b240d084881c0c4442c0111703814011901c0000c0c1170111074800011005080400190103440101039442e035030401340350b403000c10403107074081420b550101501c0c3d40c0c6943c1501440ba02981c000d45080d04013078940301c0380703030b03544c0600f541c090102c40e03065094143d520f03c52444103034005483d5034244465044210701f084458024031a501e044522007140c00c20502d1b1210340250112817100a5080c0c2e079081111001155000700075940d44491040180301c9080d0050000a2146515442c0040e003000040c05801425 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 93083112 1250 93081862 93081887
    0x90f030304120606052e170907090e01020f04090b0303040302030a12021207080a111002040f09061a1801021c020a02100323040524010303030e01060501090902030619060e01 76
    0x648074908120005406e01c2034003061964400c119580440160034241c811103011110350180e407501e00704110003803200203011011230301c0100c0c1c100540302580d02078034202d029110202980701070401040061191582047c001603400800b62454680d0f6540000d182c00c4c100d04c002c4894040105070392043ca601400310341d040746505e113411403820b42c0c00c3d0b880c1c0005103c1c5181e10414828202d00c40c030340414003048045000d0180a0045641d80c1c0c0f1040c4804507402180f2481d5006410500003040c4c40c01c0d829120100c10551415203810008070058a00810941088550440c401c09461007a54001c0362002c41c41038400744c0290804d54024018088010800c020440c18175080440300c8100c070900c0038200418000704440e04a684c2c40d1450054180159400d00c5580000f103681040c040c001881c100074122803194508001c1e070424a0107003400e0392246d1107007502164107485c0030007003110740342c0086900c040020b0040ea81c501e0980410b0166522170b410a100052201c0c200032000c0d43c10584811a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 93084362 1250 93083112 93083119
    0x3040b010f091b03020c0a1502040f1202100804170301090221040c150c0206030a0e0d0c0c030204090305070507060207090f0e0c010f021c1817060c090f03030412060605 74
    0x1101d8100d942d00f07003801c5050805404059000030003020079001070148901850744403060903418070301e00041001a402034007900c020042c1d01c140c00910405040040d040495002e04003460f44540741000340e40c3c641c4014010b55524200c81c400d0707a40b210003007004502030040040010b8440b0304070564120700b040c45240841d0420031100a000100b50030864100440d0820030700d0992a00c81a10301700c0f5800e4510500075007003000402446480d201036002a1b4040103d03c00302d07588204001c40031111042c100301c010300622080da009001504040c0c01000010340203060861820501d40d450f03d18080803580044010f0300100f40c01d004e070342180d001307540c8044003685051040ccc02d0500307401916540301d05280350621001c040304d842c520340240094825062801e800000250603424080d001d840c0c2038000c40c0400c41d00c42c0e400710343c00301044880f51080d940c100040c0700ea581d82000514040d84030380312560b80400d44503228121079170704100500141010f18201b507488526441d00c903003510200c0c0c021611 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 93085612 1250 93084362 93084371
    0x50a0213090519050414060603030403031d060f0a09080105130b010504050403110715080c0f0307030903020c0406091406031c05030c04091a100906140c0f0303040b010f09 75
    0x904040c03190510203440580c1400142070701e4080001e4502c00039010140b8216060408100078441421030003000c42d1460020386003583c1c0c6400c1015100e125174080100810200d00c104066a80e084038440403809002d02807a141404040e400140c5070000c6440700b0014080310345c01d0211100a018140d080610380380703241400412640c400020f1001402041d005a507140c0008c0c00b8103100b030196034502d02c20b010642d003215071620942e10202e80d0348403100001c45c0c00a40032400c1420710108135007014007010304542c150b44841ca000c9001e410146d100b502184512860525580d42d1131050800510200d0000604e003000d00155450151004140798800d8021020805120b100c00c0504e03c6c10500514055503a0755800842c100d1500564000d882c0152030701c1000000c102c03d40804480c0c036841118842c01d00301608a00b11603100c83c034040c41001550344169074100047c4d40002c0c08010300a041a14030031000d000203207103950000c131000d82c1c1408286004000a070b03401e8444d1800380500c0c11080c070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 93086862 1250 93085612 93085627
    0x1b040501020a0b040503040b040e07090b070f03030b0109030503030a020406030e010b010c02010f03061d0a0b0906030d050a05070605130c06030b060f07140f0c120a0c050d05120d0f050a02 82
    0x75150000741c0e9002c3d001803a40000501006003c1c4102c07809811071040181e100c03038607036540640c002012920380300407846069005ca5186801403e40e01115440310440b102d50440da0b50481c054032140c0b00d10fa040c050041808000641c007400a0742c0701c1c440c2e64a006864500e0808014203941c4031142e1181540d00d812615800f036640881c0041d820340c0c088c20010140c41820703404500405440d40f00328040c210403103221403140d0441381460b000f03d1000c4401d2111014960030040d400c1c1d41036408980c142d2221048140300c5000740083c1c1449001810721500340080794a940e01030b40c2080344c0304a44082c00000030400c001d03660140801616051404202e1219040e010560342c2c0319410341e4502d01503011450104214002c03980442d510050010b5828015221400607621208000080d01c5100b102e0300c10002e641c070000ba001e2049404c40c294170719062424092041c05600d0700d000b682c9034001c0200e9060145480e01c0200900505510000394052200c00c0d0344040754130103800041910300400915 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 93088112 1250 93086862 93086867
    0x1c11071a07030318140307020f0f090a1113080106030506010e09060105010804060e01150905150102030f09010c0210020a0201091505030411040e0d0302041502060103080d0f0908070b1b040501 84
    0x3201040c1c2c0c1403c00180d200007001e8a15003100807080c00404000c441041d41c54a0000030015000d807510964800d460152540200300205e41c20100351074010403440001541070659410800c1085903003480f4528200400c135a401940b050b44d0410001c6a465000420400100f004024014121800d550110b81000c0d00e006840d071a0620603503040151080200e020311016038811814009900d000304582d91200c207406425072014401d01004928100025446c007444502159141c00141d014624105a00030168016040201e11604008000281900584a030b00450120f5002c940040840000d2403000411072907103030300101c102420400c0020b2040c0e070444103403900035911054103100516203001044c024003810f10110071920880321491300240c1c06038000c00680b029220601c01382d9400800030380c0d440c4401c3c0300080c1094810400711140e0600c950021600b1400d070310021881d41900e440d0606150424601070301ca901c0b0b160240b241d03002c0c1202400c140f07116503401c220f041030300e4007002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 93089362 1250 93088112 93088117
    0x60e010504021303030f1e1d010f0e09100e01180c0504061d01110105180f030702010f08090f0a080d140c0306010f020c0907020c13140a0209031c11071a 67
    0x742805011928901c400d40520034402c47d1020240000125510071324004141600c1d20581c94a2000c840340c070500c0f594855503007d00c42d18525107034103a424442d1003c1c00755a082c0180080310700c5e15800303004145d0030b4225111500822300501c034110500042d22800c411138040300005028030030200030800416400c040c450803844250710381d4546041034000140d494901010200c02c2d19440c0c40100f040d984403c4004c500a095503074110384030b100c0102e81d03113907072881000b80203404101901c03010b08109100b003071605d90200c81e0b40b003a00c0311011040d0b0b080f1715008060104540d403449c0450b000c56603090622500c070034604507141c036109506240c00d034030360b451001428650401c83c04441c0500d540e8000c000c09210740c00c0181a140182c600400d00130b4894030300c060440e1291549a6068208078910f016900208050074a6980760b03446400c2160020b602c000e43c0c503a003600403039040c500d4044026010345146401c540321340440d040315188007030400d0419000a41c5150310b161358440a4002d9609 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 93090612 1250 93089362 93089369
    0x10213082b050703020a0507030308071101140a0519020d06031e11011202040305070b030403020706080c0405040f09060c09080709020717070303090b0103140c0901210c0f0801060e0105040213 84
    0x408583e240b00310304089080140410f0094500c0c4201c10001003003590000415101d9070311540c0c0c0802c4100d418110609903201007508011591900e004154050600d60025411512100c89800c2c5401d0038001942640c100030301c5402543e030745207420014400b40d4030084501c5182001d03080000d240c0c5a0780d0020f090b40c52864141001078403c0d4200000e0310940c102e40240da004803c40b8515139513030f1400a443d900854040340140030700d40f400540940101500c40c022609071059508103400c05082c00028090303038090071582a200c1841c500451042d200740031091190369100c003030103800d041046207071090540c03000c4e00e800d10402108021a20304514401031609a00300199a8525070800f140034100d1401c001d410504107070300000421001170008503101d0003040989085414140c100540c42200344102d02c404410748050840040045e04030b9038500f40710740034900400e40c0355040048540701c3c03600008001e0703545050500a0965548034280181030446042d4a060500851101c41052a10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 93091862 1250 93090612 93090617
    0x601050405091915090905011805070b090612011202120705030a020402030c040302060a0c06140114090a0e010c05093609070509040b0a0509060403090b1b010213082b 73
    0x1141c50f03c60056500b0000c14808094200c2483c4c545422104008041c0b0400c115200c0d860151802e40f040b905504000f5620f4006015121480c0f41990740200c85d482245181d81c0b144007041400c0701c00d040c0120326030107041011024100000ba40c0705010120911361040d2100b6440303400100400d81d000140e48109541c10307100035132661940800c40b040360241340c000942c04180071851084040e4403804c42223419000d600c0c2030001564402c400001000d0a0088541c148040c45a40540707041c0400501e800118004000460300e9103090240d003110407003005c9200003500090008100d250040300d400d01c64580c0000ca0740d83e82014441841801d030142103070403114007890f001038090762007408020010200035041c80d40da450a803416070a40e030021500907414030701c1c01000c14000d01002401506c5244d041d04c030101841c2c00d009441c22182c1005025440001ea0b5400c5200c5008007030000d000510a850741c075540075401c00500600304541564261801c0e1403400030a100088142c0b44281541044d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 93093112 1250 93091862 93091891
    0x1091e11040b0d06050901080c1e0307031e05011a1513120201210203060a21030503060409020604030b0f0903031509040c0306021602010e040e1c05191205060105040509 74
    0xf80c441c0040d15440c0c1c081c907801040e207000080c00c2d040100d181c1c840514205d400d001c80c030800c0c1041080602071403607155016400310b4001c3c80081c0c03002c1e000200380740c0361003800050744800303503121820741c1c5840210320920f0000e400e0700301c454100300380c0c81136014420441c02800c0c01418100074518003010700c160100018102d41c20000e5901504048020b00e4003202c1480c0c0c50182c000b00716000c1c0d481560701c6401013100c52800100300414001310401145031144130007061409481c111519080a00025401940d641040380183c1c0d401000700001c52260a540c2501c1c5000b191022004200800c80c80c842d4000700300304040078a50340105064140129050601c6480b24103004c10001c80d503801c020f01c001e100082880042c4404400510800d10076683d030010b0702d00c2d010600c801d03150072008500c0704c1d41c8a074842007030307220b40044401c1c902a03803480e020341072021202c0d150031501c0054100d40e002c1500306a10300030310a450b014aa501150078240545824a002e000c0742d842c80005085c5071800805 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 93094362 1250 93093112 93093127
    0x22404120903080d020304120903030e090a0f020c0a02040501060e0102030f0c0304050d0812090304060c170f03070807080702150a05090c04020d0204050102061005031e0c0901091e11040b 82
    0x1110241d010b1900401c6154560411040f5075000394000d50b41a0341018004c2e541c0003c00c0c0c41101c603282900e0b4540ea408040100714404e1101d8100040c2607a2400f64940c85041c401420710310181c45002aa80000c1071114441d0040c04215a0180c00000030000c242000e0403599800104a03070309054081f079942ea0b51144220030600b1400345410550303001880c012050700344010500034201c03c0302004201041c0d40c450041071035803071081c1e22502e40851640f0029101080c8445038a00920b5064a000d070303d0164101b0808800350300484010010070000c40c140000294449601503200318140010300c881c9041004104144d100148459407840d16140024042ca1040c42036040742c101c083e01c1507440d4080181d401d40a908a4001c3e9030044c421400041d05030880100090f003259005009460308021159100c01d0a250f1005141c20078441c516004c0d4068950465007070013400f600c08001404062000e0f000442c2c141101c54900180c1014620780805452500300d0b0304a4140c4600039545154 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 93095612 1250 93094362 93094367
    0x3040e07050c1501061805011d04090803010306050f13032f060405031c06050a090b180a06031707030e010e0d020402030c0a08070203040e01050d11060c01090302240412 74
    0x500c003110505000f5468080480d651000b801416654039441e4070009200019a0000c60405441081e0003e01c80840c020407070841680c02c60b05585002c0c00c0030420b40c911f9192201598420f03801240d81580c0d0f202000a46030302c07a0f0031075070420b01a0b40e50100000050314000e0110342035880030221020295100c00c2034541080888203890032220a4406502d0030b42070603a2a42c001d4040d40316000c0483c01c16445070300180c07040d90280c503401043c0c071809038182000303800184203101402d40c000c02421102c00c01c3c10030484000744990984040801c04a05602c1c1c080d81c80701b040646440904014407002002a401001031325650b0700a1802c0c5020703000010003e0580310000300701a400c80d100105110010039154010a8002c0396512441c42c9521049001c0b6075901c03544c032400c160180715134014415490300388044c07000540550300c690841e01d20000050702d240d11440311091203a41d111404401c140d014803a00402c4004410180d0104034000186401c00000810040480b8440002d51600a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 93096862 1250 93095612 93095617
    0x5060c1e0c1b0d140109110f010801180608070909021005070803060d0203030f07080c0607020a02100e030c0418020102070519060318050106030c06080a0203270a02030d020c0a120503040e0705 84
    0x5401c0b43c02c1500c4c01c480040303400c0c020650050b0a80707280244603084140381c100300e003e46415020607901c801c11030b8684003071410302c0b500400c40541e20545400001441100400181c80600314440000a501a60b48100441ca299000c010401c0c000d0a00c44100411403030804c1e00e6001800762000c0358040c60350720000341075102d90032a4014507203010403180207001425028010520210044400c240ca48400503a521907099600a5205071416051020306101d5842c04501580203030403512056213541c00201134a0032404181c10303070b18500c0c210406642c0e0400030000207080680e10012694040e43c484a07a095250080b202416140e80a40a0003800d03c0d2030150403681250080141a480e0314169050b11554810840050001000715800081c031344200e074061141013400d01820303810016400714060000704050075900440540c8800350300c090103403540103603050380a0480e20084108100c0d01e0022034016001d0294280744040001e64000101e1301920400801201c45e40d650302000c40c4c5c5d91 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 93098112 1250 93096862 93096889
    0x6160309030822090b06070f03090b1903150503070b0c030906041205060a05061003090206070c030b07030608030403020a0b0f04180515090603070302090604060305060c1e0c1b 77
    0x8500025a0310034a83e00b07140b0003298201e1850511403810b07a00c01035082a220314926650303000b00d040204800040345140000072076442410414940c954072140554550000c1c24100e40c1603052000740f18405515200e051841c840807d4480c5c800d50404010035139400760740c080e00ba9188000075642421540800542d8030130b09009081c517549640f100d42a1605a007200c20446240c822240032404110340342c0212132103544050101000e61400c0b6078101d026100922050340c21441c00c1110b00c0100c2c141800c1a0046d501239a9004020704001100504440e11036004072001d800900c030500040ea104c0120200311049048265180c03620705010411034407580d44510088007a103280d6080074031081d002148203620000d403c1f415a1003420502c2100d00b000c0f25440d5040c1c00c0250207000510b072150301c050304030101400c001042a00c0795149407524806650081c003241c80411580c00c950503810740d02000c20704100700941070042d1050890b6580d203400c1e48480881c0020b00c0044081e841d000000c1021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 93099362 1250 93098112 93098123
    0x1140612010b0d08040603050c121302010903120201062306040b090a15020718060302030c040507020f0307141621060906050a150905070e0f030a060c02070608070305060616030903 79
    0x1000e44c0c50301440aa10900c503c60100f81001c0000c0e43c0544070200341c42c2d07240e0b04055007a00c0d5513a84022a8004280e40400702d052003040b000c0400030501c0c1e03902c00c2401d42e0f15500002809070500b6144000d10a003100b00e01c01c031030050180c096981e1120800c0d81d048400c5c50b0042d644412210300001c990302504d80001510101085c521100d1603070020344881200e1102e900c2d103420008411100040d100c0030300010790107070700c5100594180c1c02c1a601841e40507407a07105480038850090103060840d48142c6040e204412a900383c0b242401046c4070044c180d85088210800c1c05180111030340e460800b21481c00c1841850600382410b001c80d0741c000d00c0403075034000410415480e103170b042c550003448400242c0e4080220b040c00802c00104034419580583c025484414a1030802c8042180c4c0c08151303c0c00d29054040c580f0854001035843c02800e1843c420340d00900781c1c050030200000c160741001429032041504010600120351a0042266030080c0c0d11846501ca03291142810f4403000b4803940000d05 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 93100612 1250 93099362 93099379
    0x614131b0503040c051504140a030204020f0909060603070813050c060d0f0c0f050301210203070b070b0a02160f031106010906090b06031605030402030a12020c1201140612010b 77
    0x1000381d808001103110b144520342800d01d1588502c14003020050b84000c0803050941000140020b400e90908040c0c0c0c51401000032000c42c5d22076000c10300b645c000040203011100041f401c40c0c0b8500d0025801c561242c0151441c500b1890000e0300246000009080040140d0b0082a08403d111017404041030f4514050031055840200322400da00030403070312070f0070781c502868414040002c901c940c01e140004619a9240e80c01d40c0d00300305141e01c0000e086440b01c01030026198200c0c0050710b044c030044009040d540001c645481c2c1c642491445524000c0000069602c104804000c8150406c1102202c9809c403206800d0030a05280554502c2445034042c00d55106640c000206c0c42841e0b0003850641305003041c00d0080128003020f000c1540030a68903410481e180c04403241303500d031144c4043d41c1d100340018211003c407041600e43c501d800784641c040c00c1c01608000220f001d24104105207080808179075000700f000b1a0042040c480005024000c80d10400d400001c2c840001e409420200007404000d1040c034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 93101862 1250 93100612 93100661
    0xd0602071b060f0903141609090317040512031e040b04020307080d050306060a410a0807030b010306090e0a140319030903090b030a140901061413 64
    0x548886811035440c251600541c010901c948108641280d5541d651103020b0b007030b4150f42d2510396100f07400d614441148210103918540e440ca1010003002014400c00c0003c40d078185040003008100c0503215569003003403020520000034000110500c20010090380310f44c40c1c0c0c840401007030358041d0b48142000003078101030500050002c12907034070b4082c610880c2107c3c0060b80e036040042d110304000800030045130081c000141c6608040c0000e11100d140f5140240e4030200c0c2085110f602c0407180c8006007403807212020805142444032441c3da8280d6004055403d21171401c3c001000080003c100f00105510b4070380800460740a81c000c44040c00201c0c4d02401400d4880000c0e84d070300d0074249402e4a10a6003081c13011301c03000c0044125030001040c4a00c2c2c41342381040c900160b02410700c01004400300141e5042c00507041c0d400390081c40c000c0412310008100e0162000360a5406074020341503408603490460100003132850803034071b2280c80c042564801e45421006e44088018121a404000310403106c040c4407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 93103112 1250 93101862 93101873
    0x10203070614090c100518060c030a0801090b010216030807020a03020a0612050f09060402010c050304030c06030501061e0917010f0207060506011e050a030f0219050d0605091003110d060207 83
    0x110b105503c0e1070202e5420715640c4040110740300301000780e000861400c010800a06007844032401d4240d0015008514007104421501e18581c41500e0010004044200604c20b801180c003404c44511401d01c02030950030021001050001101c0c40000c1040c40005402d00854491940b040011a00101001d441603520300340079007411182c1901c400d0b200e00e0180052105103420003281c3c01080030034028811695564015107800c00c141c00b040c0c81034030041c031001002440000d035580240c8656034011a40d13503d07280c80505600380e0404d0004442020200000580f540301000c0c0d800c655245003001100980c1914035801041400d1854280d01d000191403014490701d50000c901914082e071b98000020480b07a551500c0c060801c11020000328100300c036504d442c1c4640c12668821201d02d90051800c0c04d0b452607045410101d42c00c40d4040750012a07100c50341000c40c49048000c040a80f0b100401e490211400e94800016000040c20700c1504601c01c107540d11100301600d401544118219903805007070416 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 93104362 1250 93103112 93103151
    0x1021c0801060f0804050606010305190c0f08060405190c0e03070803090f0a0b030f1005031504060c0302120606070512030a020306040b0a08100b0418030c05060601020d14090102030706 81
    0x807040464220f0f10101c2c1101d00c502c58075485241c20901138030751a2035201c011002340c040a0001d804900a10340b1000d0b40e1140d6104507802c0900039124020742007003e00001d400807000038002842a413904082181165050084c20b1640400242c0054071642c505000c0d201c2080d401010354161145a41c00b2130702010020061003614422505100051281000c00165400303600a108418400b0700204100c50703d510007042c0c02045080f0500c008030f0311200421b1070b142d02c3c5910211015918814081440f00512641d0b10000301880e096190200004803240544405480b4038091000083d1040601c02c05101005802c5245548540c2c0c0e4108100c6a0000e50001d65170944114a401e20041540c44c040c4100011207030018040d001045c12207200c28000d002000d02280c01c40c1c1c40308031070030840c2c1c0f0103503603c041144241c8500040c58240c0c2040c03860514010090740c113540c810190207102e2900100c0311007000c02ca40110f1a502c002110040782075005a103402082c50b41054140c8900e07a140010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 93105612 1250 93104362 93104369
    0x150f0b0f0a030c060c08040e0408030f09031305130f021b070b090d06050a0902030102040602032703060105130e03070f02010f170c07050109021e0109080a080f0901021c0801 76
    0x40315042844440d003003014403106480000e01060010b0020020b60b03024401e0710b0a507a0141c21410b051541c0c13010980030f115000caa04807007802000041001000c04a45140d80200d800c10085041207000c2c00340710100c5040307001e05440740621b072803555800708181e00640885101d0000c00d41d20b0b0140e040f00c02d54421103803207503000d8502a0079004900c500c9a10255410300000410801009070aa160a001003602402a10105485514500c0543c409000401c0144101e9006681d50303800d00c000300200f07012103480e40d00b80d070a058002d400295800a07610341524000c071040c3c0b0740200000011001808010039250881c0404242602030003049901142818000e03202d180c0380003a030140c01c403600358483c03582080701c1005101250030400d00c4400341030b15622850000514400c160006035200c1340b0f4a10405540e01d588000d8445542c0c001e601c08000c0c08100700400c0c455210b41e844031018004c0b584c580545000c042070305c2a181e80308000f1120031001c01c0300c0114940c0010780340202252001d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 93106862 1250 93105612 93105619
    0xd15080607020607120c020c040912090b040b0d050c04030c060e100302030709030809030f0a08030603120a27030813030507051203040b0d02040f080105010602060106030506100c150f0b 81
    0x40000d01010b00100302244589541d61700c420124401103019001054aa81c290086104480300310595440d5403107030285003400741034403c4941d0094040146000020740244000c1c2c4410703c020000707100030205407034840210010210786036a1b4000144854025980f0142910352244800603d55030084804075075600d00303840340030121400c44020b509034841620b0303520000760414010400708281c80c1c050b0005120050648081039090b40c1904d01e07081d091501510b07022000800e2100c180380c100105030307021150f09005ca050030542c84001c0c1c140143d041d0748203d05075540d145482420503403265000a9580010440d443e05a45000300303042140d540000c5505106215000ca02460480e046a280c11028130085140c42c1c186402e46003141c1240c00943c011036028000415550010715141d0050201c0000006280d03240140c001e20300741040c0c2c0144245842c14046c00001d4690000340e8404800c40d0800301032402c02e0340f5000100b01100d00004105d10b00d4005c100b2000e9055401c81d020b11501107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 93108112 1250 93106862 93106873
    0xd0f0b040b030d0c1502040e250813060b10080901050f06030d140405040c1d04050105090c2809030201090803162010260c18060d1508 59
    0xa060200701c40a1080807641644081c1c02c0c0600a0302c100700c143c030114403c0c2104400d06144060741c000740d81041d000b042c0c000c0310800401c8001d200d84059105040a46c41c91a019002c2940c0003034420755001c3c005003001d00c02442c042007400415080340450010182051884410821340200000000d4405102039402c0402083c1c2404900741414080c050040140011090b981c80640d00200f00e01444243c0280038040040d8075030307481c8143c02003840a529240050703140158640c8d00901403000080c89140b030213005002a4440e9031304c41f075001c40c662411a81d1040d007021040e60714011007203006c12480d4403040603100b035540710000000b2240b0030380300c054000340c80b52500d544a0141c464441c6405d4800140360022608031000f8242c00517010029200454612000c03850700500320520402241c201e00c04819071411401c800d070441c0e903032042d005956041020340c0d02e6551080c91150f4801a001c060901d03002d5907040f040311450319110340b040050400d14040690204814420a5514080c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 93109362 1250 93108112 93108131
    0x160c0c0308030103261614070308030103020922121101240e010806070f090807090c09090903120b0406090614010f020312010e040309030203030711090a0908090402070807080d0f 78
    0x4e800c12849810105c0000360b08005c0000b0094403a16903094003920b0400c00e01d480180c062000b480704038065402401306699a60450040c0a2140d10142c01800102c0e01a81b0241c0e9005239401111019540110152000c841c282022500c6610320100d00c00d055207403100050f250f04c85103036000d5264461206000b02d6950391801640800e00074451262541c100e8000688114404c128603501300c1c06504201403025210005203140c41625000500016620b440a00142c1c1c1c0240b42c0c03d00515008074240700d40581c5a400130b020014031008002c10549802a00d240703079450b03412130009065801810030955945401019603404490300084c041840000041440c91000c412290f411740000f00c0e2202e140d103400000380701c84c40d008109a041200c0140301100598080c0700030440280501c41405500c4d210030204810f810300036040d401c6461901c01620005070f04ca00945a8240049500507210342943c104a4071324455020300800c1c092000a075200c43c07030b07442d9000b245400e1100400f00141c64a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 93110612 1250 93109362 93109403
    0x5070c090c092103020705060903070b03010311010306170a021e030a0602090a0b130b03061c0803070201050601110a201809060601170c16061a03060a060b03160c0c0308030103 77
    0x282d10107130041e0098482440503080207030045c816000060110b80c0d01d15542c1c0b00f00500380d082a003007160322041e01e2a02024660703140c002c440c064510030000030011001c3c088450354400b1101c0d00240100c3c0c4d284130b4044001101491200341d0340000d01900c95404861038500000c6d84001410792152030b843c100850701070402001e840d050105015554401410400103854a81004007503560002000ca9100000155003c480400b58401ca10594407070500c58006429980024020b504000180034441c461040020b000d21180f40c1042a030307141108911f02802000a6103542c0070340003103402640f00b4440320300c501450710400b41030054808a440c0c1c5001103800c80702c1e0206103800e01304224081101c800080000b84021281c030f04100d070600140303564030707002e403140052481d2130404107224811081c242403000070350010002da070402c9401d080c0b0480c0e10b45404081d00103640603400308048102c0078022a48800002e4200f40080c3c3d06603038a25003d10964401d000840b040d0440c1018401c8012 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 93111862 1250 93110612 93110669
    0xe030901050901110a0203072301020120070303090c08030301080615030c100e0904051e0102031e060105040801050a0219050c0d081308030405060105030c0d050d05070c090c09 77
    0x59640a01d010403142c01100d0444010104105030301400480d00016501000001d0040502401004111604c0c60004030320341100410b031810b69040448901141d10075400010f400309201d138002d5100c480c00e08048005040c0f01000802c0b002c1c49100100300a180000514100e540d2a0101c40c00341c4d8030b40c035105201c40e01c0c2c0a200394155010940c070021520300b0501340b8460003018641910240074485c006907101c0c10540b81680d00d40c101c0001e910030010032200340000201444002c2d442e508108541006211070900c00c0e03080c2c00da641c80442c9680c0c2c411412035008007060b100902450030144e0103c40258031000c0110b0b1401d54041a18801e18040e00503500c0441d0540003500104522106c1a19040001805040b44401ca540b8141c00149407070041e500480c0a84000d202c10b60412050500d40010111200d10803010905003400190000403600d50300101031400c5903c032400380c5000c501409030342c2c0160004500304102e40b030343c050f07210220500301c0c0c8231001044180c0d841e01d42400040c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 93113112 1250 93111862 93111877
    0xe031305010c1502030c2a0601060c020d1101050918010f051f081f0306020c070902070c1202010c06050f04050607090f0902030415090f0c0509010b0d091a011401030e03 74
    0x10f0000320400750720349003a9806161300c203440004280c0380c1605640c4021800b400e00580051649a101501c6c502140402a8901414080c01c10b40a101015000500e448009480081c01030181849000ba40c1c4d2003801030f20580d00c800303009840c05030415502490024400d001e01070854600b41000603940c5072407079000b001d40c001496143c2d40e4003481c1c8002c9800580050604540c00c20306900c02f0612910300074040020f600a0b0310050701c178050341d030805050184960088002c40d00501050303010502e00c0700c9201c210303034001800d62401c140a200603900c160070000003030b01d494604800c01c80321000c0c068802d4800c61284081d07480039914030005496a00320b038081c13000301400140b02030149441d20750040d40c01900076400840702d84500300d40c9034241d5101c4002286c400e820401001c0400040b400203601400c0100c3e40c0000642c1800a1a0258040c0c0701280b4039090300c0b09042414081d005555512032011000c05c80c140d0341c0c450180b000c40040501d003441c0040c0c68481118580c85002c800e40d001e8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 93114362 1250 93113112 93113123
    0x80406140c070204020a110607030903090b13060c170403080405040506120715020c0a0312020708070518070309051b030c010201050f041211010c090306110304050607110309040e031305010c 83
    0x802d8007a409010003500000b070316406021f00602000790814003001018850715144c0d401064003042840e004001302c20550110220050500480343d0703006510140790103a4400e40382449107050075080203130402e02c0000c00104e9210780000c0c00300c24807031010300038820342c0c0701600c061146803900c0e414840c5002c00e01210710042e07001484103204074400c20009000000162044518100ca03440000b040b81042c3e500c2103c0c881030a1048440715074041c858100144408030140450340e15020101d0729000350f0700e420b191f5440c44e250014070b141e4040c0c0c1c07107242e4058029007200e615404080b003012820b1501d20740c0c10321038801c4150262880d0710501485200300c040400084030380d1541d948001720500d500c0380c0f410034422050400900850244a481ca101505550310f1581c9483d40c00c3c82c60460702c400340800384040e8200100004110001b802c03a401c05228034040a0789041520000c1c1113001b0440754a9100d41800c01e4103900160000c05069100e0004030110301541d6038000550740600c0a2000804 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 93115612 1250 93114362 93114367
    0x6060a05090c1b100507020f030703030507091701050402090a020408120c0c19030c0f2301030b0d05010501030b0c03010f0603020711041b0206070e280510080406140c 73
    0x2840c00c015981d40d8001c00d50080b40d904105800c2c2c030200500b032601d1540110755100d840c514410701240e005464210419002a001400c18940e500e5142e110b254405001e040c1c4401c040340101e8404e840758001441d82018500303110241c0403030107002c1c180950301a442030310300ca030200e08030704810300c00c60b01190350300001810362010f042e007400d909400051040c206801072102207041a260030f85c0c1d8841d503041c11300d4100a040d0a520b04134107400380340d80140c0c00e103e090074070510070203100e40600c51030014010809002c0c0c0743e92100480203081c1c00000c540d0040101540207081020540003e8183c034842c2000c1801641d51840341c4117140002d01c103075407101000c00802c10159010394010801c0901450825070380400d1640400d054850107030000104181d4015442c19080d4148080c1c1c1c0c101d9507502d0011307001d095200008000410700341c003507c101950301c1080d1050803403860208004000c0948011700e440314410000c2d007001c004a80540c0d0b00c0381000400a1440001042c0a109034035a101300b50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 93116862 1250 93115612 93115619
    0x115030906110304050601090f140105011107030c0605130504090209060d031404120203061510050c0304080106080102090111070302061206041821020a05151e0703060302010f0206060a 81
    0x200036258054007a01c0c4a5551480080311025000040d4440c90288000302503d5140103114812509916441c0c6245891701d150080c1c440c4800d8402030449a0900c3c108040342040c030b180a0405107280c0c00140000e603106000900c3d43e0300b11010308101031041d5040d83c1e00c50365940074801039400090009502103024070001d00a0714050090300240f078000e16210031004c41141400f0400d80c0a504814481c8603945888001c500e01001040d50200b407803200301070044845004110940408102102440000700b03c4404000040050310000c00011009104039030f41d44040718001d42c05200c0103400501c80c008495142400001c180044031f5018080d1071a110103101c0050f1190030240c0859031050301c1c0c100e40d51401d01d2210000c554240241d421543e880c02c003100307816490302d224640c06c085d0b41115440902080000c0744142d180c0c440503a06880c0ca070f03280b00c400c540c0300302c6c101300c0481101003035400e102d00349606500140a488c0300380c903181030300e641140c01641c0e9040200c48856112400002c2231 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 93118112 1250 93116862 93116867
    0x303060503010c11210705030c0705040c030207050604060b191716080c040506220606110705010207030821100603050a0605061815120a110a050f210703020a1101050115 74
    0x5041d218001c0446046c40401d030342d841d003964002000c0184a81c001e10092004d440c20b071160801c1621207042c114a8002c01c2e03501ca5498000080001d0402642d80d0b80007040b035111504210100704100580c02045500c440442d0802129922020a5032048019202c07440501115800950701e20400900782841d1500801000d04402080581c0060800099091415005495800c1c5c1400d110b00400c1c55030078500000c0620715507c1902115601c00c0c03004201d1170340c0105007070341074940003443c1d6540c62256000041034054540080710700d184140b001c1080d004201c103070140a03501a55014051620b800c2d1104007607900e280100c990211b010414003081540e1544100251180504041408669203011100310303080306400d2154046c1031403c200d1000600e00c14491180050136565040c441a003200802a0094801c00c040150001801c4e410142103211741c40004044040f01c3e45040c613001d078006000c0e4015600c41404540741e00c01c446600d035010300420381a00c0c2c2a5041c07486005034500308 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 93119362 1250 93118112 93118153
    0x60905040f260705011d01020a050a080a0213030c030b0a050402100f090816050f0a030308010506070804090f020c01150803030601030914010507111209061c0b030a0303060503010c11 80
    0x2c0402d1038500d0700000c105020b91018100d694050400001e56140240c8002e003141500051103889910402426401c560040c0640d00c1a00080c600307842030ba62070341c1d0018003c3c4101c80c0303006082541d0780c10000c104a40741c0c0100054030f1065591006a88859028405850003541c2c0254051882c503c101c0c0300d18807814080d003004d1f4052a1102e11595540390702400c002440e01d5840d181c1c0c01c2a103050140d82021a12450580360030341d0051f0040d45152002440a801070180920847c0000317018010702101e03201340da01912240c4000c10811206c5000b0340e00030b41c040318615034035501304050101034501200428040303910b11070240d442c550703d81c00110000c04019170b040310740c00707821030007141c011a092140c0751080307069071143e1116084d000c0c2224946102001c903484c03550300c00c10002e081c070740f26182552050302d201241d811040d4003825802001d00021100c140e058030421001c0e03010700d070341074001034100c0300160002c00511441020803180d41d0340c0d8040625656108662811000012541 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 93120612 1250 93119362 93119393
    0x103020306060702040c031d0303040803010603020c030706020307090302150a020a0209090708070f0509010f0602032502060a081506040803070b090f06070302040f060c120c060b13020d060905040f 86
    0x122510300000f5600003411a1111015040040d0782c0d0072280c440849145e0643d07003204e209200441c15854a5665401c1c588014005d81e01015000b150751f20b06000e040095644c282c2d80a00c2c159168a4103500c024002c8141e44400e1340305420807141c0c0215503400c0030840e00d40b50415806004810165024841c10b02409013000600c1d101d138501c00200040107000c00d038041d018030808145414a0300d007c0088440040e04004142c031142c110420070320741c001040354941c020356514907049402e83c0b40c1074507001080d600c0203900000d0001d5600304d000d40c840000b13441101600303481c000551144050180500a5001d008542e910030028100400d5041220940c4644080c04075000b42601420840c20a0310541e440e42c0840c3d00802d00b4032808229402030f001074646490680702030341d4a80c1b55140b030002c0c00b40c400014820301404502c1445240d402c500440000505042c00c4080048070b1840207510840000e0000d40c5048030105280801c0c0c0296409950800301c6a0f401e890385d6280d0441400d90311a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 93121862 1250 93120612 93120619
    0x70210050d02040303030f0f0b010219020402280f0f020304120804090204030803090c030610052101150306140708010509180a11040e06010b0a050f04080a0605101a0301050103020306 80
    0x846403041c240c1e000600146100340d03030200b042c241400c402d03030941e500c1c03092041d0308a00744178005e80280d038001250707403050b80904104c400c0400640041340091050700b000c205070b0402561001075095552108800401c11956089150b5044210888003c8606001702005810400c410061418003609240c442801450f205141c280d40c0c2001c00c00700d0740705620031554003c0100400c0443c01c0180f05903d041c202c2500504100c0c54515050083c50326103020ba10701c620713505c4061040701c4106004140034420035500811890b20b03414070b440340004d81b6100884070a4106000e0798409820a0300b01400356032140c40741d52259003403008000d9a180001d24004501081c4100f0002603002049200303842c0b4001c520341009a1150000d00059030398500102c00325900c14001006079101110403240d110110707251080d151001c0b4240300c1c05503c0303182d11039820303407040504031420310413990300c40ca000b103070340080403100d5a5644144803e5488140d85081a070f09040c0010008d039400b0382c005550000b80113 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 93123112 1250 93121862 93121867
    0x61205041e0512030a05100e0105030a20030d08090f01020408060c0a1e171e0a020d09151b110a020105090d06140f0105060c06040f0203071a030f010b0f07021005 71
    0x1c50b60a03d50022079410450984075401c0c4042d4140404c5070390050140b00d03442080c69818000130a03a0b0782d50a000042c11070100490b141d801900c800126100110014180c0d80300300c50319a03009142c075502342c0781443c2c070b40500d15040c1c2d010841403003224202c07007081002d091150349103031107115640c00042c421801e00c0b485048854919a00c8050031015040c3da4413a10900030074441c80d0100444010b140d0881b144210920060079640550a00d50100a0310350160b07403407080e00400009018160801000002c10700c100e280101d05541089484195420b664480755040d510100ca0442c1b1102c200326817608a25414400b65205d0301c014402c0040103009009001c5950741e40c2d00441c0c21032604c0780002c1c0030150620401d0064608410300515048400320b0500d000b030f8180e5611000054001000e0410324412001103480501115009001c08030742c0f0300c558107a0491205c0f503039004441041c00d0302d80800c000310f00d9144400540341c0c80c480f40084141452045d50910200801643c001d03030901805 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 93124362 1250 93123112 93123133
    0x30603080a020303040c060314060409020609150909150d0b0a15080d0e060f0d020310120c0e1023010909020c1006050a050625020910061205041e05 65
    0x44001010501c40795402035a90b4541418003450305001908858101424400d041440400d061100d43d0040000c803400106410780b403001885c0c91048003109034101586080d03041080306110082c1001d10810350b02140a07588400300d420000d18980e0303407a80d00c140c20711200f00c0460001c0190302d600403652103000400403455040e031803c1c40c1180d406022141c0c44080c46070082035004508425200c02035030b681e410304040e50b4801000380104482e0f04403da41c0400054405017100414000801d890880701070320460600785055185981e0080d041c0e40004100800c2036194140d00520442d00c0e0003005040308208001140203080480b8050f6041202000f0b012030030811502c020604040c503a00103142d07030711f101006903041e1069540b01c81d00ca02c001100c20041500ea204c1155034424900458800d42c0b001c02c03042007540d044507a0080e401001d00c2d0104203070b0205102c0102c0564000c1e80792490030300722660700c3d0b106030790044500a092190354103200d00c81614031104422007a00c90f50603500084c0360b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 93125612 1250 93124362 93124373
    0x20c0a0804080d08090303070c2d0512030f041514100f0b07020303090d15020f0702040e03031302091801020f04210c0e060103092003062202060901030603 68
    0x915800566036010002402c2042c250300b008032084000300ca00b4258268900480001d03103d00005003078100b81300346410700008000c203140c0c1c2c40c1074500324481200c2404600514601c00d0106005040325248205262100c40081c9001a00d100d00b81d81c505008959546658501d24252040040e020880d11140404800d0f0b003000d003060320907030900804908151401c81c00102011065200b04c0d001ea000304195000740c0c5001c403c59801000981c0c0c0c1000c0d03412946410050410b08108420300300e0b1000c80c1c001d400005000080c074116000711001d11001c0035210300300fa00c83c8403c0c0d814946002c2d43c00103800060400c110501d900c40c500c1c1511010110900c01002d080e80d110f980800b0071742200142c1800b04108000b0b81c0e4901120a030a02e0000300c00720794070540441c0346400380f00010179075a400100580e03c00c2d0000d50103c2d5102500003500170806040d0046100f10a010078441d024205c0001d0441010b096a070441c010290210700301c0d22100e8013408650317400400074604064946802102142 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 93126862 1250 93125612 93125623
    0x60e0d0209070e10030b030c100e0303030106050712080609060d0c051804020a0f0f090f0f09080c01290105030a090b040b040b0c0a091401020703020a06050d0f060e130303020c 77
    0x1003603850f5003501044460402103040441d0690005140c030b0036030300b0001e41c1c0740000c01d50309909040e81d822014801b05901680d0101c81c91a045505120000000c91015030000c098134895214860b0080400b1200105031034028084950baa0000c4403480000c8561a240d503141c0e4005015680d16580309451718045110716850b4a20b10751758064000900c0110705000c44208010200ba02650101728142030980d600e480b805c0c0b0542400645450031340c0e400c440703103601130f0710180c411003020041000d083c0340a207525000b0010b4245694030f0070381400d003c2ea10001803d0810351071070f1440c400880040f401522a500098000100300d50f4900030a40000c1d80036241c40d00032801038040501c2442c2510381076003102e4000f0045565440c0522000c4400e0f60042640016900f02c0b10785c5051780c0c900540101d00c0c080d615840a9401402c0990010311180c12600900340550f0064091086082c1c0241c104e0541300940700d1180205156030004007000000d2034004002c6110b0302e00545403a192100031071604 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 93128112 1250 93126862 93126871
    0x9060c29100812070308070f0216030f0b06100935010501050915030a02040509210903010f1a010e01090306060b04050909010e070b16141b0613060e0d0209 68
    0x1001c4803000c0c040907504000c1c890f0755641c00c00c1c00c41e1800489a4000300381c0c00003e03280b2003d010075440c50a02d01c5000f0701880e080118081a0f400021f9a281819091072940c15800d4030303101500d10100c4e1044c113043d45401d100261607100c440c2a03d1074641e1482d140400101940e90f4107000b0064101d80d070043d24135805403028840000301d071f40c6d410241000b2140002500349040104c8840e580b62460b10003180000c03405404560014555840c0f605040c144482c1e04030a4a082140c2c8404555152040d0094050948160002c20800d01d181480340b003107503413929849002500c2148a51000d42c800c0301201031100381850060401aa40e135542c8090300c4041c1c03c000d03204180824240503500300700311074a51241d007102c0203004070719a0000c410b44131855402400d4020300c00041540344410b81840c0702003c03a1b40945402800d00d00240c1c640d0325058906103c0d2002d0060700f003003040c0e9241440560741034024100a41c0c2c141071a08809071169502c2e0703606c51f9045410051041e02603030300d8131840e034882c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 93129362 1250 93128112 93128131
    0x1080a0c150215180708030403151d0105040c0f060507050601180207050f0f060c0f12060102160e040b0603030f161e0803040c0b0a0905010c0c1208071209060c29 71
    0x34213020062a401e2041355007014072181e20910003000880c0400c3c2d010304402002c00c0e000034504024409100710b03d00c040200c09680c2d0309005c1400208407840680504462550400004080d1680c1d4100c445201364040034110f40d21020040c4080400000c3c01060b007100c0c200c0c01860402c150b034855041101e0642c1c2200240c2000a50b012040000c4c0300090748080200b258905c1c0c01c0c60403801d05821300131a2002e071002170000d00010850390080205001e0f0400f00c603241c04950f81d99983c8091150001c490403a00c40b00d51002240d00d0f4240042035404e115150000281002000000045500e0300b0311000d5900042c0450100b04208081c0d0030a017603640104141543c0e1704d002c1c00d02e5102d40805600c880c07003201d01001941c844d140d0003501081951003d00e0b02c0c0008075140d00704452030100c030340c00c090724a001d18080b6508020034040104062445007010320000410b44806454629561095102040d01e03001003100041c5d0070340803e200b086102420030601c145024004610b100200c910400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 93130612 1250 93129362 93129391
    0x50a060c06060609050607060e0a0c0906090f02030705030609040309032f010e030c040b0d141e061b16060614010e03070317030c071709010801080a0c150215 69
    0x50003000d004060143c122810804403035850500814102e10807070b180580032565560340b903a442c51060040950031600400c411800584030501c0400403d0940310743c0004030b00c1d003c003000c1d0300262030080e24490f510589030315046030b841c02d00380105124020022410085000c3c008400520b0300401204d916514040484040704e03d02201c440c4a40030511f0241801032840c1d5400a07030f0f0b4006100c0d19a001e05460201d480403640002c546200605140241511040815019001c070005098001400e10314054a803418400000c161988020f0320012004540304185120401c0d9a1006118008050f20114221111910b4417003c5920b6900404800b000108541d5031569102c10030a0301004218068405c081c034550350300d00005114005551521008800103c13461481c0080d21031407500180c0303840c0741c4103d911a4034a903a00c10140f0a020460001c00440c046e6400200c0200ca542e00c074045082050134207403c0d094040502804008511600344048501e5202c140110b01603110300307501c00d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 93131862 1250 93130612 93130637
    0x40e150c03040627150908070f06110f0909070e04021215010207061b03090f14041506020c010e0f0a080606030601170a03050903010908040303081906080309060c0106050a06 76
    0x2e03211084d1802040326a000092582040d00044d14400a13034821044582c100c20054080e0160030680c601503d200c001081b0b40040c400b00e51102741c00e8611a03181001143c07041c1744009281c2c003508218040290301031100316228202107607199008005420001d50005244000400760b903c4210002400491102808100c0c1d004080071010003900340050004a402c15000526914a4000d00a101c40d0804405000d03d8012480e032406007a1890400800503251007821130640c0ba560714640c0a6450b000c03440441c890b4611595085d01d03801d502410002000600458801d040350121503032140440008000950b074041c50400244000700142c0080c0c9020410503040c040140d10034001d040d03d00d90380794000100072035050011a45810940e4a510294011a0042003c200010450400001d01006250700070044500c42c85e40103010146050300ca0b50f0701d2043d82ca075449000a80e90090040440c1483c0100c06805038074080b9000003441a94cc000140a0f0f080c50750106001c10307200700b07284 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 93133112 1250 93131862 93131873
    0x909030f030506030c150d020a091a040b04061206050909010609050c070b0112060204030501050c0d0b01030b010f0c0f0b0103031806030504020a03150e060c1902011a040e150c0304 79
    0x801400d440c0c1d090400280c038064000c6910760046100300d510842e074031052085218041011b80b0000d0f62406000c5488410140c07000c0c00c502964050a0010f11140c102540304035102c100306d8041d555610310f0320b8181032402d80180c82c07242c1041e040c001840d885aa02284a03114000a02c1c420000040080396047c5400340400803501c0140c18102405402c0091002050641c80a03a044500d161b0345180034011070300380074009005681000300154205001c1c04955122540038064880040d02d08100d541c550070015402c0743c039111203103400f00710740200580703010f4024805041c10311700401040d0804800c3e951040c0031640240c1045001c907900b4070004501c940303035030844800303050541001c01139820250001001d500c2d03284001019145000058800076016401c49015603d07407008071072403420203042c441c0803a001111071200e0071007a140c206207001d2050089140401e0380b140351124200c4600180009401a050783c80000e00c95a9090030f03505800b1401e00d0700c1141003460301c1e9220308052818 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 93134362 1250 93133112 93133127
    0x30702011b020319091d070c15140604090b0a02090a03081210080a0503030c091c150e030a080a0c0e03070b0d0f0c0f03090c12051b040c050703230301090903 69
    0x13144100085440140491000040d9a441910349444584500d03658070700110b030f2101a12100500d0725032000310b0298042e919402070020400880d11005495540c002400304980d8a11000b80010242c0d001050414060f68000c1c01c40307801c00b51412041a4494844048540c4110301f540850b06510041240350206440000007a216103030260140c0d4900352140344d52400003500d103409080d800103103100c2a43d280410b0046501011501030b50305c45050910300d80c00c18400c0600c942041c100803540700d6006000c02200d50710034040c6c44210b5103448420000d0000c0001c0c0b45102e0900c020410000385994080000c040103214040105075504000c80102c000e03203040c00a9aa595030802903078001042c0c000c001801e0144440c50001403509090502480e07011503548031480301c9031440003403000e03c540800e00481c10715244e03000d02003030740390314040c4000c07039491507002d0000600600050000901c146020b100384419410024120305034030016941c1c41d4402c0c0d000c501391642c1c8511420402d07821040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 93135612 1250 93134362 93134407
    0xe1018080d0503010509060316060f03060504060e3c061512090c150f0306040603060e0a0203151608090c1c0b06040504020609040207060603061409071202011202030702011b0203 78
    0x20f462701c142803a43c0100243c00d18020342040c4400d0203224800e6501c6070340900c000304030043c824032240e50390750a003080000c42a60b401d80304041140250030102c200901d0b13aa101c40104141d802504000680c080359014083c1c00301c0d6000c07007020482040031060038050221050400a00491811704544803031030f0a20b121103650041415000401d10310700048161004c41d01421005031303030382d565000040d0040c2203a40005212528054601115a4000604100d0a4400c0c3c0c1280c0d07803c07151080e070440210044640d600440c0e558122040e0303591180c6d1840f078110040c80121003400b007103100040d0000c4045003482e000c40980040c084140a01000400d4200300181d030108500d00706600840c295200d40070065020b503400192400800c800d507071140740110340000c0108640d5001c3c28921903140020746102d8040e10900c41c1c04a101e0300210402107000358141c4a440040c5121848503000c1c2d00020b0002c815551381b20300120400d130842c4417201086004e03602860f40c2d5582c0c01c00e20760103100d1940 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 93136862 1250 93135612 93135619
    0x608010e01080d0807021f02030114031b191502060a05070f0c02150708031326070b041103060a0603050d0f02070e0408070c0e0106030c0e1018080d050301050906 71
    0x30041007034003404216800d0040c914606945180d44800042e0b2801c00c24040b002ca020400c500080302c0000342d94082c50607a40c1002c1c040340c0d00741440c0c04059903a072444140c011407600101c1240c00c80e191112001c40c512a0800316030384210741d20401114207620103076a400c05a0070060410000e500d662054039030012413824034260300c04201c440105280001c2c503000f40140f2030000450300003030601c0181c0e10300f039030305c483d0f542c0c0c0c0d901c0c207040d1140c0018160001162903d001e0681c1004172030140090300c241c000716841190803c20075482c6d0090010780604142c0d50321010301c8102e121303614103000d5180300d068100d401240d0180b42d80360103403800e07205110600400903c2d0b60420302041e40841c0c40c200b00e41c80c107522401503071a10304001c07565102d40b45000f0050040c100b80000e03c00207155000d4122403164800f001400071030441540c0d80c0709400012540f0124066448a216004011901428011084406045071203268a604e0110100c003518041900803004110918092600325030003d03068 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 93138112 1250 93136862 93136889
    0x92d010305101a1012020c03090a06030606050d0f180305090f0f01020a0f050c0d14071409220203190b01080a050703081e0d050610030905060c0d180507060801 70
    0x3d142c01180c0c0d41e02031940c80c4100e003800d03880500184503000c54081c6200e050800c5564400c03003c4031a070f482d070214403602e00507010700000045003800392080004580321900c62074942400c41400344004d114000e070203a00303c4c0c1c0c0c032500c40700e040d40d100042101e898401c0c0c58881c2d503015400d0412001d14440134040b840351010080700d0700c1c0b50342c2c0450b210119661240f894104100b81d45801820710180b01041a0005003144808043c40203074054074074290008019503088a88a410013031040311011701843d040303581b060100314070001100c544849408110701d480100765460b8002401d0140000521082003483d10b460800d2203484070b0302c00c0c010700d980401440c0740442c2c0d03903581352070350703464800588010004540141d20800000004200070300843d41142e80e20a2180205c00420060720307020300070010303001221100d6000f881340030300c3c098004c0300502a603510041d1003100e941c0403100080449841e1000074080d4218494180d01492094010b0400c0c9810520002c210040c164007a65001804 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 93139362 1250 93138112 93138131
    0x10e09040206090f180f07080f07020705060702060c0105040309150905030c0105030612030304030903030e041503060e0a0606091d190201080717070f0210020a0509092d01030510 78
    0x291021039680140581d141c0744031020904c005403201100400d0303414403280c80001c22a5030410ba0315818442c4400e0784400b840b0307489140d811028500c044a14101691240745c0522a0b0b1506130302030804e481c4003c00207803500229050550079600141e40440100f44032a80a20210240c2c0d0f4418900c284207107030205070a0303e040002552008210300c00d6051240c00408a041605e031580081c00e4022030008490b524240742c68010000000c2c0c0c4000e400003040110042c4451400d801007080f810314202d81c203c102403d40d1645001030000c00b4a280c1135128107400d0700700082070380c042d0000070501e02e02c0001702c1c11002e0302076140c260685080354410780c002808001d0309039007846401d40840e0302072800c107030580d441c4081074070f907103503000004102004050200050240d210724081074103007043d030079500750050281041050340110700c08007011910030300101d01c843c10080866944001c0822903025410b04003050488060200d030864100101c03030384014400d00008000c94545900c0401040103411355 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 93140612 1250 93139362 93139369
    0xf200109091e0216020909060703061d0a0e190503090a0603060501050d02070c030b0a020a02010b0307051305060402160821060604150e060301080703020102060a020c120a02030705150105010e090402 87
    0x29410116451036400304a013003508a01d07071515003400e0b50140610401381001030500ba41c494084070031030300081c184280070031483c0f02103080044404401c0501c40c065241d111404000d000c9a80c0b440780c517407007241801705e10303600001d2040c02400d016001a540d101501c00c184452080030b504000d00303160402004001507640401203480142e42d040005840301507628104440c22440d920180c20308100c041441540e10441d4002c10380032a0f5500200940d0003150149901c82c8040e21a85500115028031b011284c0071603005030b540300e000140018509030440944586d00d446100054030b0246020802502401c0d8060000d0700c040e04444400140f89400c0340003402c240308034011b0700b09000700304072004440c6005000344110840f009008a480e0360b16007041c2665130004d444183d00510880002c90444502c62080390200200e10b4041d00034102203490883c04c40c0d0050000c541140700030001140450810b0120350b42d58202150160540d525000c0014408c40590302e200340301c3e6803568144001640c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 93141862 1250 93140612 93140651
    0x703080a050105060717070f06020904051005090a020d06151107060912060207020d2f040203101203110303090706080c0c07150903081810020a0b010308070f20010909 73
    0x10360250200c40300403607206c0c013900203004070300d0007c180801c140f83c403008204264000e8006c841c0240d60401c0b295441d0b40101c43c4814542c0b08468110045101140d1115282c0c0c000f0702c0f001c0c40c80034000c50000c3ea20f00020004141c0003184400049050701240c07580041170095000400c09440c003000c2c0c05041003428440d10501003401410b16500103802c00840d110003404c2c9035485d03041202d078800805d5680c012400c4180d034407a040d040c900b07120400706552070144266802640c02c01c800a810b54101110600e07101540f01c0c05400380107001d02e1007040000104001d503c1015808040c00c081071610802402d09000a45424410302d002e005e81e5410a03400141c000480d5440c2c03030192440307080b02d1415500e2150640024103d400000741c20031180e4991046132100910643d064402c2a124102c12030b114030313410b200285080342640040002c54001c4019002c0c1034002c0c980c078004100c0540d035207090660994015410308508444410300e660b0030007052402019032400078050603070916410081c18 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 93143112 1250 93141862 93141877
    0x80c03010b0a0e030307140606041e050703140406090b0f0402030319050c030406020a0b01120c09090203010f05010e0711010606090501030218040207030203040306050a09120804050a0501050c0703080a05010506 92
    0x300c0340460350030300051152020000c4180f01034156550354001e0306100d81021581e24080d480d500c682c00114013981020710030300720360380c0c0c181e5032000043c3d81c4880701d074021b0440074003200308154442041d41100f000a496090140b40b00b04400180d040711071500c00d41d0000018411203000110600b0800981c40100c01c4440c03524610714485074496142c0310656460050001100c114407012070040703003042d00020402d1323681340910380044240c0c2c0da800034280d500c1500c520081100c03100304002c00940c4260340010200d40d10040010404154401031682114000d86c4421442005071040c412003980241c0d00b0384052181000a002031170800101812040300b078400c09042550004140c8413100c02102c0d075550068004000355920289030074025a2604280002d541480c074040c00304e580f80c0e095100380015194440803444084064240075580490010010b455034081c000c81100024028801d40340300e03822010301d1984541c92814010030301302c0c004000140062900c2c0044c00385031b41d840c0582e840c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 93144362 1250 93143112 93143129
    0x903110405060d0b1303110303040305040605030c090913060c0807021c0e06031f120201021903030e070902031501030b0a1403030c010f0c030e1506060906090d0f060c080c0301 77
    0x152100804543d00862680d03020b884420302c0b4003840b280d03041ca94921504640256a83c10302418440095900c178801520000c0101d2404c120801800e80248080c6074003923400d1111b242021442008505102d808031060032602000c80e0b03803141048018030682100c0e004600c1c12441c0e500c0d00a001a64441c0d00e01103580b035020f10310754405581d174401c0d1144000c20401814040c1c89040400c079030744403804000c44da041d241c503582c000410b030340120300410092031f90141e00034004c209641c00c1c11195041201c3c410b078105502c1300b030300045030101000942e00418200d0350044e80ca10700102c0401c1280d00c881c40c0700c0c0c1058240214080945d80314490b20090314103403214170b485141d24100080c0740d403044009041080d402e156455074180500e511481c000100d40e1000c9c80881420881c4a88600c4c001d610200704103c4100469403608141d0080e016414014017400d00e4044082e000400840c2031550440783c500040c00813108103c46401205c2d0344080c1821308603a2410003140203c020b004c1405007520 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 93145612 1250 93144362 93144371
    0x309030605060307090906020702091803030c13030210080601030605040b061b1903030c20030d050402120313091107030212070204061a091906020d0c020f28050109031104 75
    0x1441c3d80600091005007000d200402c04000301d880c10034081c0d00292000d9208110810000e8402c0c3c10406070305000c1501e41000d14655514903042c040190001c1d40c1d582d400da40100000300050f119804101c1403031700980c80354207262604d100010300707541e490381002e4055420076481094548558060314a1701c4203c010204c0389881e401e4405180002020a0880c43d204900801c024107406a0007030700000910b41d96011406100ca100462401446070005450380c000c00c4004034500c500c2c1d02c62034100f41300070118481004916602c5107942c200d03141000c818070015030100b06042c81840340c10020701d0013200c11418000c1c141c4020f512007406844a08c00a02c00064030411552640e1124014080c0da5000005540f115200c910068209445050240c81d5082000b010382071441c0d464030856a0b65801002d101401c5141142e900c0700e159412a0800c41482d81030029035980c0012503202003601d80982c2c0110700c1050600500d140951041303041c020fa094040c0007040d070320100010040b07025900402d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 93146862 1250 93145612 93145621
    0x10614030d030e010f0203040f05060903120103060e0f06070f030506120703030c0c03060207060204050111061501051c0f02070203150105030a0807050f060708061201110415090f031104180309030605 87
    0x7030260240e0140700d417000e403001080204000705806403c00342d9028104071100313682c1e4010301c180d90f4490368500000314458040100001826500010108403c08054a808413810031b501440c00c0e0003030341c290001c01d415414a0f010103034544980c903031022046800d00078008016031a81d44544260102400300160014140b05000132070b8a000300840c2d00103000c40d40c0c1c050604010000703401600409001411010030059000e0b00050800c0c010f05490740752486900e568001504e0550086c901ba9031072242616066030400054801c00400094903100036944001074030415040c06002042c81b6189486840117228540300001d000240c15403048501e60340310403500b042d03450103070f070000c08072502e1250303a0410003240d9102c44214003800c401d0b1210555588000d1501c0d00341c40350540c000786c0502041c04100400424002d1a098803001414008100e0391a00702c01540c0e8030342a002680e03e0000c000e0780b5811410140b08184140340070106002412144d542e0007050310001e03101c0a03001986410115 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 93148112 1250 93146862 93146891
    0x16080c07031202011b03020304050c0f011103270a03050d050d060509070e01080108030405090c031003140604021801060e010c0302031306080915391b010614030d03 72
    0x2040916000321801035140b180000003400b03007a242c3c142400081c2e0700343da034144260090095900503640880580510081c4406101001036543c14413030401410503d1101e140006000800d504064001d0621815000020b41150704c8a100a0b09001b20203591080010075804180d000101013a4540a03541e0440d0704003210240415400c8654030001203c18040180d401142c09403c808080c0c0724031409a0303070307480803075224091071240a0b000301c540c1c40043e8044c12400d00440d03112411900288400707403241c0380c3c803800810740024aa0b440e403005040c8070651a05811017180101703800005001e660510400410410840702c1032814061040494803c050007402030710400d8000b04031a4030302c550707191401400301070191800605801000c004000c91110350501d540b01d100d0301004240745030080c101d482d01040a0701d030300809110060700c89035910f561801c000c007641c811208002c00303d4003500c00d0b01401c5031101d5020200c0c031a2800d080604944001c5000d0098a40604000411070100740c101c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 93149362 1250 93148112 93148123
    0x1203010905090709060b1c0e07030201030b310b030c0a05010e220207170703020309060c011103040b041b080606060a031d03120f0c03060607060f1a031216080c 70
    0x20f001d4084c10018041010100e00c0080d14090703503009070308041060501c1907c401c03144070070042e1a15030441642072000d135001e80c02050101b400507100120080403489400316801a1001d286181d41d41400400c0d03141c1502e0040003800c001c202c002c0e0201d200780e01d0028021400901c2058140131895401c0100c655540718100324688105c10b02e51165030036281941c00a500060080710385460324400d10500e59105001e550400340c0c0750700110301d0300700002e0800c03e0365044642600815074880d180340080b24240f202960082c0d214510000e00740c00d06161180c22208104584c0c94100380c036110800000d00700081003a0480b00903517a039940c49424040031005403410f0070040d4120b5804000340c2a1034100000240705020310307071005101c00d4480c2983c01c1002c03501907500c40c10007002407010544502d8003c0060618a12030240003d00c0100000c018040c0e8903441003c0c40403000b140c80107142d6040c2800300060103800c145520380b828891180003015002c1241000e00088004510589551020000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 93150612 1250 93149362 93149369
    0x1110a020301091b0608040803071b0c26010b0a090e07051207050a0e070806010302250c0302030d020309030307110a0f030501022101180e03090d06020408060912030109050907 77
    0x207008000c0303e42000d83c100c2220308061043d40000c0c1c00d0004c0d8580c0705d01c071400d002c0c0e40c3c00200c542c07458483c1241250905840d0a1041d010b48004204100141000d1101402043c0d5510903e81e00e41c0c8038083c45d000c01851900c4070903a641070100201243c1c0d41d460200c0180c4e0182900004d40040c07904206107000d07000d8000c1030b0811013038120700b54203850028400003251821609014000d480f4614a900c0010980d08100425000c40101e90558081d40240c10140d4411000707117100c142010001c084c66401c40400c0e64150b03880c40c030600542c20180180c10818069000440c903254500021075900c2c4150800580b031500009024045035840c00e03100401080e044d0582040e46440741041030003903008504405015a90200451001c030100032200c0c102e0311420000d20b4042c1701040c1d450083d1054030100900e501081000d003092303543d900c401e8801c89014040041c0c440d414030140525241002d800030190b0380c080e402030901110040100ca05540d0600d40102c0c07961649004580f80101310f40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 93151862 1250 93150612 93150619
    0x50a081902040602010f11250501090804120606090e0307020f0d12020303100e06060f07060615020304030506010504050c192c100809030421020a0603061a090a0501110a02 75
    0x1500140f050750540000a035440c4402c0200700d242899003120b080ba1050b644481d25205281c208661441c6501000c03100c03072070050f4004140480380342d130743c02500d40c06038200c010300034614403c0409000341d0f4440d00010300f4031120200304c20381c50410309640da0700030900000e101b41928841c3c000291a17440b190f4041c241e005144400c0e12081e041c003c0d489400403030304880300a012820014460710b844032880d00071440035207580c2c5044643d121402c0c1903032200c40141c0b582a120b440014000a11440b1254429016030107075407034074114541242043e406a05c0a48a503050030144403005191000710340c1e404500201140c5105485c48060700d20000d040606c0c4802e1031101d03c4d0b80d01e00710900c2103d45032803800310b904150032000c681c415541d400d0141c03000902036000380020701840800008031170f0100035581d55050342c13004da43c3c005440314040e41c106900103511040f0400141b03000c0c0c140b24a83d16030000700d86040004210128241e091544100d81c100300d6a01030f1040180c800340000f03803005401a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 93153112 1250 93151862 93151867
    0xe0d08090402070b010512060f04020108040602070c0305060714040b04120507030c0b1803150c0d060321020607090303050d0b180f0601080106020118020906030f0d090905010510050a081902 83
    0x5003003010354138100340720b1035020b8101c01ca001c0b2038001c00882c80b00c1c80307001801d0320102151555001119145002001250b140b13a00704169030206040d50400c1000314400c0b001410185000340c4020400c110950b20031541090902c024003d1035100c0341039a0940d151217a50304203504080c144645450380c0e5500261034500e00304c2000c81d405045600901604205408100880d0106020f1503034806e203049200400c0382034280461200c3d02008014049080e203c0404a0b8585e100e40f1008a10411100151002138090745101c88450301403007070070fa10502030300744055082e2a68070080e0003481001c030b003007011644d1258001800c1d41c43e00d01690010303030b1400d000c0d502480c0072503e40400050603180c60b404119204000903500d4414021000d0100c00c040511406130965802d20103508800f40140381e26000f01ca120011007541041100058215641d43d08145481e220840c001c460040c0c220074061450985142d00803034200302207698111440c6029550303962a10001150010410b2400c01c405000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 93154362 1250 93153112 93153127
    0x807031404091505090c0a18050301110702090f0c030705030a02040e190b09010609030602090307031406160c03090b0306010e04021801020c040b030a0b0702030c010f05011d070e0d08090402 83
    0x2582e10400f140101d03100421105030b1510b007000000081220601e6000ca8208100c9000510501c0300f86090f4007100b080008031510b030310010f070039910783c010012480c02000c07402200307610f4403013003243e04001510543c0c825401e0900d80c0790f40f140b1008004400b0b0040000208000c0b10384c50303040390000c010390000200c00e03051100c02440d102505980030951181030a411b100d103464452512812103425485007076400f407541e640c150281d00083c03140d941c0f5000d00e103c00800314241c802103007640082e4502400c000c1c50711020511062010715002400c002c0c004810000003a040005081580c41000c402030f20790b42c070703038004980028224800a0300329001041c05031400c20092003040d0f506009800b5607428030440b200344000c40e151a0805a81940a400c1c500c0c00720b0440306415404c605984152490006130300300203030039030b440350b1147e10030380d5a14401000000000001a180b4401036015080c076414194070041508041070051803181c0b009020401c10083c06c2c008071900e0754000f0340155183c0c1d00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 93155612 1250 93154362 93154379
    0x60b090108011a042d2d081f020405130e061303020307080d1d030a030b09040c0b07020109031a0a0b030604050706030c0509040914010b10021b01030621110a050d0807031404 76
    0x2000301c10803018030b400c00e03103d5100070405010304090b150400c0040400c07070208c0022203160b15078620801c0900b03500304404601512803d0707079242c440031201d2000c00c00040f070628452a12500802144800307013040e007103d002030750110454203507039041803c854983c0320000902d401401040312051902c02c0e1701c28003d241060110103400880403946040007400280d509004080408640040c002510582e05001400d003c001034141e55006160081003039441c0e59070b1100842c9061a00c00441d4010410071000c81058002e070000d00d90b05030064056810700b981c41940c3c031105401908281a1200b403807000c038178460070035610009401403007408030b82d01c94100000010b000d0300019000e0350802901403401e00384026055a00442a170041070b0b94010801441d031b44280c1604040d042585400d000100300070001d043d4160f112414075503a01000407454044109400031141c940145140f20003001580d4bc2c940c408106650410703a1a992140249000c869090301503114860340a800b18003c01d2a00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 93156862 1250 93155612 93155639
    0x14031921020a0806010809070e0109050a0b06030903070204050a0207030e0f0609180a180c0902132301120608030a030906090803090f06060a0b04090e0f01060b090108011a042d 77
    0x30081e06c4d982020745980004a444084602035000a0400e503001004407240f2030f84030551111103058005444020180010300c0b80d8010b48110080e0361012a418055141501c80d880c1c116804080c1107262848965001c0c00d10703104050054031405043d03d00a0207a1030303000c1120303040c850081039202c3c00303000c0ca00d2144100000396800d031440c520f0849640c048030004400100c040e9003141000281614158400c0042d5004400174110600d01100c0080c1d20441502000080d10f0f400604a00c4145030f00300041860000c803000100e0b050a00c5010080800e012080b2101c001042c40d01081070a06800e00c0b034080c1180f1040100031040010800040c4400811410807003d6a101921429103d00c002c200708604240141d00401c6003c200c100b001401a602c1209401d140406450a6242c250030306800c58905511a440d40e28001038040003d6030f1001040b409040fa1888001e600d4009403c804c80d0744c080c0740a0201544804445030b40d560114045952000310240d21103101251103001000c0040c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 93158112 1250 93156862 93156871
    0x51c0606090f06030b0121080703090b160302060f010303050415020703140102120106020c09070c02010e0306010f0504060506040f0e04020d08030a0c140711152514031921020a08 78
    0x5201c4500007054600c80340f07405031034105421020818816948d2940b146540c00000c0c114213100e00d50400007144900d07070028106030448160140c806242e54100a0b09180c00280101902c015041c01400029000003d076001d40346020b0540c15040c00241c1c3c1645420000c1d0000b130035544030103111400c032030415001003003020303403590b2013240503661150103a13990b0350001c04a683c03081004000513009407250781030030b0360300d80140740c0620f940d411040400d0410701c0c2a0403000080300841000e100c5410140290720003408141c85262806180c11151640d050240c0a400c44000428004c2000d640c1c80d0a080c8052a0308854000c2d030724100516050020000c3e40201400706000c1c81080241c1000c9809440382242c00143c0c07440c40daa00c8074204118a091069080503c2c0300501c40503001004454500c60744800a0034802491081400e084c6030000042c2c1a10301140d000b0083c42d038003828598440480d0102c281041072281807104004040e4690014018030f600703201103a40090301d5030108206014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 93159362 1250 93158112 93158123
    0x706050a02100213050307050904030c0b0604091e17040b07140309030d0e1008060f01080601020111070b060f030a031418100503071d01200c030703030f020d0801051c0606090f0603 79
    0x525910003e00c903030703041c0860b806408980c403340d41c000800c14050400b54031000040000480304402c0da18504866000315002c41c2640c00303140e0b44800c000d0550131285600c0c06584801d814549030480e4408035102e001d0008100d0f550301d0008100e4510208142c940c0c4440041c20b90f02041c0b40800300410040c25805214803501d00280e07205071180c0200d9041d0b01a581c0030f0403004050046000648112002038041da04640d40e80c1c001c1030909180601400119104006001c0f0604110040203040301605482c1886030300503810b41c80000303420440034806d001c80d502d030003070f205c114980b12460080446240c154211082c1e21580076640c2d444001984902c0f02034440514103860340d01a051000b640018070790114070002845030b014140c4070322010030806407000310b407180540a00460700300a600d600c100c0104058002ca803a02035010700208040e4111031400000755031421002681d00c1c0c21440001c01e0107111405201c06000301600000d01401185c0000e011010b4000340d0100140507038441a45c9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 93160612 1250 93159362 93159373
    0x506010302090a060c1a09010c020c1c0b0903070605010303170901110d090204060317090102240411031507020d140f030402040216150c031a030706050a021002130503 73
    0x11598040d1003618101d15000d082d084060381002030580786480901c000780c0e400c03946000762100a06c1940b42c100d2081498000200e8442c3c42e507440a46404000045070b481170f42d641c07100d00441201d10004400c4280c00c81c000e2900380c2c0b40c03c8507060661054440182440f401c010001c000d15401010309840b80c8030b48940780096550b07030b902446c02c075021901c00f05a061001c114002d5081e00315084001c009000034000030b089035580d40c40c0c4000c140754000c0400441c00c00304003087c4968040c00b840d10011210000300c0c0300304002512058030542d00500c014900c01e1800282da10741d440820a01d0b07002c4c00c20444c13030021400c200c58007030360b201c601400600c002090b8044609061100c14103039103811200f4941e50382152182e908100184d004490101d602c0c948240b0440003050b03904c034080079905401000051104a0103030001d0940d0103000c910701e0400040741c204003e9440c0022800100c0c0c480d844c11a8883d180040308a08003442102407a03507142c00465050841550f0544050131104124100c40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 93161862 1250 93160612 93160621
    0x70f0b0901080f1801021305040606080907091a13060f0b040b1e0903030a05070209060a08030904150503070b040906140d0602160c06030e0105090102031501031a060f0a020105 77
    0x46a11500ca603250000300d21201080912038045800d03038004840c0c40c2c00408001c090722030242280c20003010680c10f40c001200800840c245441100d01900b42c80c07070070700c085103002e40910381c0d030305000e1240c072b440681c0c2c9086182012078001200c85160200500142d501c003807156091002d00054020b0015035a0380c1d100001c6c0384070810f030460342100e41140949090842d496117440742c642e010a1400e8200008118560301a81d0500042c400c2503540c6e20741546410144c014003103500c000510940c0503550b42c0405000000c0008280c4050321812600440d045201d05c15854503c842a0301158043c03043c0e030000f1030050740080141c0b00b6201124000c00c0101d07a20040da068100e000042c40e074011100d180100040740060b00240b104401c04840d07441c0411041d0780300c16102c00583e10880c006a90b5403801c2030444030a00440b038000300f040e00254254108880100d4420703000118241c141030b510600d401c2c804c0c00320924882c074080d0041009850b002d1000900203640d001c264560015441c140005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 93163112 1250 93161862 93161879
    0x2070311030c070611030d05010e010e090705010e060307030603050d12180b010b070305040b0406050408010e0604020a0b18040e06040311150604020304140604050f15040b06151605070f 81
    0x807810b001c04507000b42892481d010f8183d03080b1801044203101030100708980c10300a50315000d001c1c02401c044881a50641c580b650400507488098005022608824403c00103a80d00112400c0d460030b0850710300740e0700d4503074107419001015103920040c0709004030b50809a0341a007240328486021030380c02e403e124294510039007800c189000300740141040c0700040140480d84001020b4040d491090070300a10340f07901c40e8000700f0720707401a5006800080001a051081c1002030180c540c600c1090780c01041681080da00040b000c5000d40500030300000b0200741c1d43c404d0501c0b1a1102203000300a0030030001c504a20ac5241d480d00740444054000c20240a0807070850440090b9510790070000c0c03440030005407240380801010f940040c100b030300d58140204040a80c0d4a0134021349000c1e80c8200c0090402091540009050080244c08034682085641c1080081a541c1075500c1c0d0101d011a6090f55094401040d40e402e4010300344040e10121901e00b510080102c000b90640594000c40c201c102c8550341d03072810 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 93164362 1250 93163112 93163117
    0xb0702010b2205041716020f03010203090705041a0607080d0e0f0705040f092a08070f090f15181503080703031a031002031602070815040804050402030a0207031103 72
    0x4280e001c00080502e02c81c0c0e0907081e40070f99001407050360f03d040281c5880b060395689030415400062a010340b1501c650071441c0a00625040ea00240c0081d41545070079180641c1752141d600c285070042d44c48182d851040510341c0309886020200900c800c2c0c482c522424140c109400031008911b550b0301c2c0c110000c40501001494644042008001300364550600083c0300c081d116804401340303415290f84000e00011410140500e5172044090038440d001d058610344018040d9a5125a040b0307040f602c01441844400e8000304140e9841d504085141040411564010403007501d040f0145c0315103040201d03040c2c10300400ca542d01010f6003002e200207626414018040c404600c00100304450400c00c0b900000d02a402a5041c240fa8003c18000f44040e040428100f51b034003003140504a6001080201540f41032580102050180c40180040b0303080045103035072566420f40020143d0085400501041090f034100c501611001d04103540b00e013851704800d800307504692400c802140ca25111124100000002d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 93165468 1106 93164362 93164389
    0x1f0b04050f0f06120d0c1514041a010b04050d11030102030c131505040302090a0609020a03090b09160506091201110a09080c091b0c07030b0702010b 65
    0xb41c1081c0040e0003400740b0710911009145840c240350025882a585180342414402c0c003801e810880c07038503a0710008140c103141c104507a641480940e800d80502441c0b0402c0fa04402420341e81c00030b48483c109000e004001d070b0060204004501d46030640b00301050081c141c000e02c520420004c20b080e03a0084600034402500003071007000079417185088070001d0051215451203240c007900c00500c00d100c1c52001911542d4070401040c0016003d41c45000141160401190b440700c0c00c42d8050090011840e0590305501c54800040c0c8001d400310b450f1041c3d051a010a018641c10038041013200e0b002a43c203a1b40004480c00701d581040c1d42440307040305581e5800e5180391034410040004085085030f030041e400c1a0040c8042d558a0303151250700a401800c1c01503120030364403117005001a64010408540054130a59038004103000d1000340352402850154000e11103400703090b05000003500c0058 = true := by decide +kernel

theorem cover : BRFrame.Cov 92985612 93165468 := by
  have h0 := BRFrame.cov_init 92985612
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92985612 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 92985612 ≤ n) (h2 : n < 93165468) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
