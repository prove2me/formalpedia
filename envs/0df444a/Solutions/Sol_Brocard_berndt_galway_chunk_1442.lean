-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1442
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:00:38.88249+00:00
-- url     : https://prove2.me/submissions/080d7066-6c94-46b1-8831-cd56507d2abc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 259172661 ≤ n < 259352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 259173911 1250 259172661 259172687
    0x2e09061b060e0111090a0b030705070f0206092205090f0706031a060324240304170d060801060b090a06140f1201060e09060a091a03100b0a0b031006 65
    0x41e80c0b01c14503950428244240c141085024200c0741da00c0345102d04010303000c10303a41c2c00107003580c80c100200544a030b440710680c0c00c01940045940c0603840a0710000c0e965000380002c0320340040d00c0c9542035451440c0254035503190000300b4000c100f1034440c00162502d49818882c4503400785e10000d0100440741c840d0340b105140c41c2d90001541c141452a5000a2960340252000729071040f81409148261100712007504140e10300722207040448040c114107003840c0d0032660412170036190200009085c42407199000e015140006030881e650007a104844000b48998007862030550310708a00441c2d882a14422201d140e5001003400d00010301c0c10030125081784808403031002c000e500740000075141c0a40e0010b0010303c20030030317034940044d814200f00034107581ea071112040c8246107010500004c3e40340c00e000c0100382d82d11250003180c03c168040e107105d0700041002d2600d800d40305e03003e100c80e000030300c0e94009140031900b00e4011207000e0742c480320b0f00c0d01070200b0b55041f1580c0e900c580c1d080000c907005142112040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 259175161 1250 259173911 259173923
    0x1c170a031409030a0f0f0906141303030302030a150b070204020919030303061d1b0a0e0604080a0b010e090318010c05011406120f060109090309052e09061b 68
    0x1041c00040c0e101c62040300799070b810070940c00402c5000c000768002c490521911064074040c3c80c903480d040e90003007400d003030307882030000340252058107104000004044521032442d0442503040380c0da03603140007002940115034040815140c000c07040c000d045030388001c01c121400260b120342400b09036000c1000940c402c0c047c80350b1012070741c10b90150300055400218001d5000740c80001d042c03441d20344500800c1071040c17000b402d00c910480401070000081a20078000d402600000d58a5048000d42030300c00b001c5020119a100e1800f0400140440c0006642052180303d8682c104460340d03140b000481480041c0e07206030072034006101580040d02c0b888412015864145003034284581715440740c03421034840064840040c001c00e82001128284681078100c0420f03c1c40050503100000b104032515150b060044050464450880d0000d0510407201403010b007200070300f507080148614030b5030a0410910f8a803103001d88100301075844858042d1602801f04e40e5552240700025042c440c00d50780c030701c00400e411200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 259176411 1250 259175161 259175171
    0xc0c12011404060e06101d04050708010e210306011b0f06020a020a0506010f05010f032a05120604021c0507112a04021809150414061c170a03 62
    0x40c00004400390003030f8050305001a110400700012070801c07400414a5441500c0a070040010034000e4404003541600a03200c0340c855141c03454040d041c0101d50b409002550b0818080d007184103008542045010400b503e48200400554103204040c002207038114080f075601d514402401d520003c0385c0c99030a11175020642c101c1e8084c1d0b6200100e8108560200c0107038000800002000000c01c0103602400492111407001480d0600081509001a141804040d100e03550300500c0c0219251944d810b07200c4140105c214824420000c150ba0441404044104504804102da50815200301c0c0c03019001902d0004120340c1d683c9070301c00603000140c003d000300400441c0d111200b1509003d492000403c0749a004036210a00c1c2900303900d26101c80545200e030b8410402d40551004801c0d500e011040b05a520035a03079070714001d03d003406442e83e400441e0000e0a06180801d02c441d00780b5114402d0303008494005810b1880c406110029800030340040c9180d00e4a4800d0400461841c007a0880d2042d6147c0414 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 259177661 1250 259176411 259176431
    0x51306030c0e061e09060d06200a080a051003140a0611040f0e0f040f14060f061c0f06200708040305010e03031006050304020d050312090c04020c0c1201 67
    0x28106401d0b9018281c04801c82c070a0203482d240000141d50182c40c00c194403842802c1080010b42e003141c002c3c0040b40f00d05a649000400c10400d508403200c0e41100d458100760f4800a021030200c164040c02d60b500c00250000001030006000e885054001d000c4680c054015504690307030703403842c004500d464010510031800c101c40000c20501500d111441d1201c40c454440b850b050314450035901c2500a05880302c1e15204011020100640a80d0b1003600804041192482d0f410030100c1d42c04500300c060254000c1c3d01c20030071340c140000009401820140d030066200300c03050740f10888060150000400305080881e03100c0c0410119085490340811034036440400550b003440d00b04080d4000401159002400714041044c0032084c4101d07102c200407880610304e146011806a40411721070700411046c0440131002c502591152001101581d0707000c01100d940300810b00c291444000c0c1103600a05510030803281002c80d05103802611311324942040100031100b42030042000c004070301001701d131040d036030740798014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 259178911 1250 259177661 259177673
    0x609050405010b03100b0f1504030803072601081c0516050708060105010503010f0e15060403031110060807120203010b1c0606050a0605070206070f1b090f05070203030105130603 78
    0x1400359200318000262000010141428200c44080045850385007400700c68940e01c0d080110b0710320345c05c00c840d50080b0120004800e0040d0180f40c20103440c03800d02108200d40140c00001c00c003c0c10441000030804011011501d07034840c0b00900400360a0303049030701c0320000140b05100d441c00c410010300b4840d04021851681c0d1420004002d404d8499034014101000030300d400707005060162a0a1034044d2442d0b040c1010109022102d100b0061000903440014940742e0074005500e907403001c0103000c1175031990769040040281ea81b8140d102e0721030151651036495a40184100412568904040c181303547c5440310300e090301d159510742660195204d8083c04074942d11129640004103081042c2242c0c4051410070008a034400d400407805200d8680c8140681c54201c3c00703840c00282d04881d1959150340070b01e003042241041c1c0e503009000710540b5100703c0b51100b5849158090703900036282001407590702d0001000b610f10945000b40542c1040005101038144a03e558460382655100415180c3e130f2681c0e41 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 259180161 1250 259178911 259178921
    0x70204110a0c03080610020d050319020d0204060f0e131a03150106110a05100f0905060a0606020c0303030f15030f0d0306060e010804032a060f090317041101050304060609 75
    0x14500080c282d860040400d6040140960040d500f501c40e0070b404030600002954504007405190144540800080d4001c1002008401c0d000f190450564031030303082d041d0580180d0401d010300e002040050284c02d030010302c01c0d616528540ca00414102041816040502c000d240d8004041300c3d15400d200c1c2140141c608000c450010211408000001e44c50000f0050252114554a00d240d03000f044901c07022130360000341c0c880d13180c1c0070341400281c0f55040d1080744000c0580c01c0006000380100c1080201c0d1948650001c01200d483d902929800c0e5280c0c0101512844202c1b05c944c4091840c6010885c5400c0321241442180005412114007440c0000e08900e00410f1800085c0001d0322031506000702680424908141c90081c02d1000b95401e041d9400360603821580b00043c85802000392044500620000c41c8814580004040119080b0051140042d02e0488003d501081d40344100c06c1009600841e61032095402c54124420b13a03030604011501079102500548203a512101d003c180c0d0f0500d0701c20 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 259181411 1250 259180161 259180177
    0x50f04020903120307090b07170a05210712110304230313051003020a081b0d0c0203040e0c0712030c0e090c0c010c05041a07050102070605011206150b070807020411 72
    0x3c419104d24200000034102109500100f810010501c40d0100185411384070071026010342c40040c0d190006100201d8240c02415100f150010100381185501069038031014080d8240e03659a4420014a503a082d0a4400b0141d03511041c140800010b00854500324060000d14410f0071481c000910b0582254a5a00440c03404901c1c000421400c00c850300e8140084d020000c2c540c103055060500100340030300300c1c100043c1a105030080f403030030710300b00c51084404440400e0140c3c18100425440440b00070350341c1d003260041403000325060010585909040b829102002d07400360403000411440341c0201c1c09002c010f604101444560b06203003850303640c2c1c02c2c608c07441051182c2001d41c540c3d010290485c00d44e80466121404e20804101c1400a01661000c401113107401040c800d682e0740c2d4501d407450081c03160440c003800f501e140c54008940c5000e000d17030101ca00b40c095502070004500301050324429540a02c1858445c01042000f0b800007526000504581400140002250424004900318950200b0f01c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 259182661 1250 259181411 259181443
    0x10051207082406010c0c0e01170c0307030c062007031416050f061309021b070f05010203070b0901090c0e06011701080c0925031401060c0309050f04020903 68
    0x1040c02020400c000c0090b048100c00480001c1401d400840c4411a0b03010740f074581082201d03851181400500722804000b02803a0034204207660755400c4410008607a401d0000e014010012181914900000d4070000d0360b40124409038040d203840c0d020f69603200849103006851842c2a40303a064031600f03200c000019070050624002a50b000c903c80b80c1094640b15403404c0e443c0e0511000c1c0f10580710081d410811000030f541055071002c80748160f40c3c107042c696005245403800000c4404c4108281c01d003040c094542001102c904c1e0b5254426181500320601429005030300621003180881c0c0324840c1107030442040400010001c859446500035030003030340c00c0002d100344c00a00b0f01c080da5034000300d04119840341340c04000b0030394100302819848103034407400107129103036160100381c0411080c1180e6400c071040c0b0742070240110b4400000380142c104c003104030b0200300003c0c2c00010034a01811071121011781c95921078103142e091208011107501e41018840e0060750900900c075031520b04100c907402e4a000aa = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 259183911 1250 259182661 259182673
    0x910060311090604180605070201180501090201080c031504020a0504050d0308071202040b0904020c0705180106091706190b06040b040f0909120c0512040924060504060305100512 78
    0x70091040640000e0840780c0502d00c0c00c0e215000c1070b40c00d006211041a030148022441d074840442c2280500103100340c00c9100020144818104001548030000d064401c1e00c54900c0307075840c40040ca02a010456080c0405030a0201c11945450300398000c0400000c0c5083c03160034103480394049540041c020718210302050601c0c0a01807166000b0700320484880f020302e419451726051040041080c01800c00c080e0203540c01086902d010181031100c900906405801e4484031042107668070000c060078840c103000700e0f04914010a40320303108010904c002007001d004084a80303c680d03281810303020702c11407551203581e94841420f0039550440180010000c103101a5280d9040152600007a2203581c040319020b0f241c003494900052040301c0940740742d8041d04004180148078107003241003c6040c44540c820140004000ca41c0f500d05501c001003858410008003060700c240300001100840e0360103172101103001803100700a035a1080e086194000100301d108464070790781c3c40210303202000d01200c00398107821071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 259185161 1250 259183911 259183943
    0xa06110315030c01053702071401050a080f040f080406050a110c1507050a06020d0f0b0a0602030d0207080405040e0a0b10050906090606120c0306010912080a0809100603 74
    0xc6200c03071012030011405000d2104031400082c0080c03080c0402c203400031580c4120740c4190040b114030b045c0382c020007400d04c5080719600c1000039110075080c0113412010b54103102c440003551240b001c1c4d900d814400e48072a078194981e081910800c00000f0005c0320300b030300d80d007039041d00041d40380010384003c2138140c5031242c99902591011b0103503c422a584400c1d5800b8a0000520750783d052200d680811000360040c0d134801807030401c0f605202036500050003481c0009100d00181c11303e41d1069460041e601020040e69241d1810442e031780d80b980c070652006900500a0181b0006181e000701261441141290f19150350707080801c054642140c0d004900d50804025001400100d0300e9499105030500740d1600d203d428030001523100200a400e442c05aa440d50000300c950f12541d0132201e1200f0209010141c620700821055410360040307514500040c2490000510341804282c8082d09680c0048035034100391300ea1000301c840d040c0043c5441c42500c02e00c0e0f041c00c038205c0240720300000346000d6200d407034452810b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 259186411 1250 259185161 259185181
    0x30207020409320a080405010305040302070e09071a09090a0519150306050c0c0303070302211005030c0f0117061f02070915060f0c060f02040b0c0d0206060d0f050a061103 75
    0x802410f0b044250001030352040040e240700e00b01c409403030b400d08001070141c54038242203144c4450b54225035410100780307042c400d518800041c1c240454802155548403407a0010030307240240115848039400004440120301d0488080d0004c540c88041c08150b5a040f094001e2110706541c540010802401c0441c032081c000d0089a010b0507522071401c11100d840c0c0b03440d183d441580d074400244200f0030164007041c00580701c3d80c0403044894401c04145107603500c0c1401380e05211082564411303148a03200301a01c03c80e95080003900000b004005031200c80c2ca0710044602c24a24160050465038031401c030400b41e005c0c100751044048440b4485900034030180f410305001c602140d440c10340041222180000404c5801d82c003240d07090f86d1083d1881c001c42132000354039100b0080c10002d00003040c3d060000c00c0210780b21240178080c040380b0b01c40070b04403803200301100e80aa07120b4000351900c541100e041ca41d25400b00d9000761300c0034900f510400840e280b840541e12118221034004040c90b1500c10000184000802 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 259187661 1250 259186411 259186493
    0xd050603030301030506041b0e01090c090608010f1a280206130206160510020d020a031b090509040503090301140103120f1e020c060c07051e0f01030207020409 70
    0x8003500154a554110740f5165a2102c00400003490040c02d8001c2c819040081c0b901c1c0070040940112607601c030b5031283d8003400035200035503006000030300030070300000c1e0707a40f0800d00d0310b040300d41c22500d45410604015950400007a0071000d001364400810000030b1040240b142d14009082c0e1904500c008021044000d080000141c10003403034550701c0300303120050780d40e2a045074500348040d20380c200011510b107490750a2158104000c07294a02c04603182422000a070000d00c1c0501c02980c0400c1074804d4900b0140c3e040800221141c00a005003406104909040800c21317007060088003104c0c2025440c40c00070b42580d0350a10720000d0100018010810002012200c445149250410714044408560010607410f4002c00440340c1d40f60070181b54110500900050014240140c5a180d4a80c09807100c03683d40c0d03000c1e12034140201480d038152404071320b84205010a480c00100f59180c0e007850030004501039040703c20241d0303200c6c0d80c510540300080c80703011903980d840c18000f59011a80001482e8900040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 259188911 1250 259187661 259187671
    0x5060909010b0102030a0c1b062001020f030103060b060c010203101a0901020d030c0306050d050a1101080408070b07050909240f0603041415070909110906092b080d05 73
    0x7038102151406035130780210640b07940407690b00c0e00010100301303800c001c10303d8003044c03010790300d08000d070b00380814520380c8405661096401e0001d00300b0300c100744270f0b080742c201d01c5540e289110f9074001740014070000d140d40c1c0040c555900028002da00700320031071240c0c0342207a000740d81c12524a501d22408002d008044810080e00c1c1060b121500c0c01c1c14030180000c0d4841d406000718604060b620302207000101d02036840440500300140c44c1c0d20b54440d1358540955189403040040d2801001005c0010f515881401d1b8275100d2907010841c0c1c0d04002441e0303605914100c0103440e490501c1810700c01603005844001100c0d00c1600e080d0000494910400c0783c030449124643c900ea8015401c2c0080d1260f135807107400440e5005a0b03c840728101e42508407645504242030b1103600202c21540301c041c4002c4a80c448050b40a40b140c9010030440903508400c00083c0c0d1045540041e0041c01c20b00511100e450030006402c104050441482c50070705482c034207010007500d907403800c451002c40403d10b50a115907901c203041e482 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 259190161 1250 259188911 259188913
    0x15010e041709010c030e1201020a05030a1401031e0302100e030904050c0a0c1b030f0b010e1609060e0a0f09060305150606040e0c07080a0e24090d020f1305060909 71
    0x441c141e40c000810f540c03d4030744d01070284000d41402c0e80490f101c0701322032040c1c603060500071500d5055188008246900607101c44c0310003818480b00b807959201c56a0007a04a9500400140c070071106030b1548529980d01001c02e405501401d10100b000e10410300401d0f030790610480145658203e0b00e010001205d2025151a00c01202070110175807890304a0105892142c00903906d1220f841c8140b00812802666000180910404013080d03041005030b1403a0307410390f800d9440d8121503a071054040d502c03002c91200301800003400f01e1000c00030b0500425080b01d0521010300102c003820340b214032001707217841964010b1201c00d6813400d040081c07010902c020743d0b010f0b95007170000107a400c000c400281140624001c080c5d030070400c0303c0803500c01117440c02103c4400d0f030301581881d21031501203c0588200c6588050750b0040c2020442d51401a1050f22f00d402e0280c00c05c3c00d054140030f084410720081c030311107a004076005064406800c0c59035980c145400d15001d08120702082c6890400144490369001030004c10072 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 259191411 1250 259190161 259190167
    0x18050906010506041e080d0306030c08010902030a030f0215040302160506030903220e0a09150b360414010e0a05030406030b0616060504050616020c06070515010e0417 73
    0xd80e500d10742210101d03506103a001c44481c80801c903030b074a96102a44070a40920448021f01c2d60760703415030040401c6a0180c0340d481816036844040a007038545518000303500d03800140300040082e02404405151326030720710440380f080e5800d09806007008000e82e0140c0c00f607440707030241c44040050b0001c00710141005480060039400c084111640d64015203200180c1310180038400f040b0101d04180d070380000e00e48218030b807043e0f06080411034001c0c41c200f601a04e80d16a0000c410013603000300d015028480d000940031100200d100351404010903100c06800c8101814001407545680600407114010760084040b4440051111122400c6688854003501da681004034400042038020044d0b8003100c00307d08001c250400e840c000140c03141f1030807400c501002c009822103024041d00340d20082c07181d80300d441110495196640400e44d01d803c0303100400c2c0180d000e40341001290070904060324096116504881900980f180740a0030701c03074243c201003010700d80c440400081c04240c1d068400c4032a1900080c0b4a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 259192661 1250 259191411 259191419
    0x515070c03021c02030c100e10061d0403032c0c030a020631080c030c1219060212090a0c090204060e0913020301050907140402030601230408071805090601 68
    0x5100c04040407151400d43c1d105410041c400d00070702c02c5a5020300000c058903981c4050316240d000406901441594a1051901c2c1078170301060b604c10841a10560b000d42c0c01c0c51989d01c41c01c41c0d00214014412820181c407050302820003810780000802d0786c2c1034024411011400520000d203000c40180d0100c1c441c1e485100c02e000561150303000c4900d082c0c0504038640440c0da2491034070b45241086807c3c442c4042c071409000603680d0010801032881c0d0022801d580704130f0441820010800d0f410081151207411045c0c109240000350007011802501c504c0000d130070440c03814110494440216800c08480c3c11118001003008100045c02000d04403641007141031608042d8002d118401006010b80101201ca000c142ea0000b201c0300c0f80d04d81c40c1d004000b030280f80350160845440c0c51030b81c440c0420342c2540030f213284800c1c6824000c5d40d10540c010394801300c0f216003401c1074410307100407840030b200d04090400c03011506000c00c5c4103943c09030507501410038000f0b407a0700c58442103d100a1010807a40c00080c0180 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 259193911 1250 259192661 259192663
    0x30e060c071703071115040501050604051005040902010903150e0d02010203070f0809031218010c02030f0d0908040b04030f020f031501061110020415020705011106071b0209040515070c0302 83
    0x55103030301c0700400a44035900e03c2c40546034400310303c180445c507225444407190740f030f1015424175215a21841c000d10490f00d60005100544200f51a154222103940d5000e101c1030400360720020b039890051500055041ea00c0e100c2018861400000551068459a03401c3d01ca450030008a100004648005c40ca985020b0000402841050582c001005103500210ba001031040044e681142101103021000341030540140c0c030741201d051419a0254240110354810341c2c00482a03e501a200c00602071401c1d0000d1128001460a01c80403a96600709000c04907400444502410103584100b1840c00300d40b0481c01080030741c1c0d00994070544241c0c049002c03e064030708400700d071a04640307581c100512101c00c9103510b1400c00740c211140b81d00d81c91001c240081c10719240c0b80d116281540940039502d4480d00c90004469060409007102c01c0781d1b101c030340814617840c8220482106040b02c24405601a42c007036000511610081e01c090390154010101101c00b0612032010070b0b009421030a11902c0c18038039039000303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 259195161 1250 259193911 259193933
    0x1203021b100507091a0d02120910050106020d090e13080c0a05060609090309010e151612030501060f0e0607020d0f06110a0e090402040605090c030a0c03020307211b030e060c07 77
    0xc40f10170002041100640405405845408241c010900170500d00341407801d40c2d4034030728004160b41505000002604a0001c200104e801d0040d5940e8510a810b141d500e078188003020b000c81c50040b040e80030071004952070710040e128681c0210080d1100b601c20b410400c0c60000064142442258101d09002c000007002003211140e140270700b0a441003940c004c00103802031361f1940c2e4403141100005040009121030710010010346115080c080584d11221404504482c001d004240200f08181c7d0b100c003442c0d0140d820740303210b243c00801d614039180160340480c0110281d41000c4841400442d201c0d410411140a01400c0c0c40e10600036034104400b0010041002c1003204c1c2c0039015410440108041d901d440d004000030b4000644440460b0821500041d42039204940e280402032410203803006003442802140d00440c00e540d12400a004008800c101c0c2c44100740000c40c1903940c4901112400843e2180c0f5030641980391400106280034100c0d0030f081080c0149035030302411080140314001a80c030204 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 259196411 1250 259195161 259195199
    0x1b15021b03122206030b10210f020d050c31030615060206070c02061c06080616080702060105010c02220f1e05060a1a0f040b21131203021b10050709 65
    0x2103218041d8230582030040381008c001d89000740c20306200203000c0e4403980040441c400b84190030030103a500e105001a4034043d517044480d018100030808102d01e00700d034902c41e99a42a2851000035290b6075907d1808075000340344106c818100d181010841940c040c00150b0340128181030204400010f0717400030340b0714400c00b02da40b91004801c0c07044031100c64040c0d204001800c00c0800300c0b10310b8207041090a0781c044a9540d00e2001503a10b000140f1400d10108902e4102c4d076041c0c407001c55000b550f600300131070310081110034450041000c5070355000c2c544501074044684c14426001410703c1ea048545d548042181e0f020420391824882440344c5500ca040c40c82d403c6444003070071005040134840d031125052060140540d241c3d0400316000c0750307610080b8001e298850071001250021840080c2880740c1c0b0804031189800d41c040d1140000c08201c011991000000da80d03d001441c003a03011038520100b11a040082100358015513501107103288034414590003a402c0d04148100c5482c12440e00031621000d04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 259197661 1250 259196411 259196417
    0x9030803070e150306030705121002090d050303100302010e150d050402010e100315091406010f120608150912031311040204031b15021b03122206030b10 67
    0x200003680148210b4042803840c8009004141450010b80c5022070784c0c009584c000e10034022003c00041c14640b451000c2c920403407c0c4041c241e07003422400050003e400c0b004440e90004075240501c40003c4061008520032080c640301c60301d0380c5085000052803008143c40c100e0160740c62007003a42d4021907180075182d40c81c00075500414a55078900c012101402003082180d0440c0700744407040d01403a055000310f01020008a9080b000b141c4da0315241054424420a400d032564044003c030b112075104030010b0310500c1c8641442c0c41f500701d1030600c41e01110a00d602035036207500f007000701800c4c0b40019609240c105c43d0f184e000744030110240c0b001040340d1201421130442884a0400102004580701884240c814020001c5444594038107145441024078424607081e000851408140c0c4000f5095007d01d03071590380c0c000c109100711440310b240116a114140c40d8584605034880c1c001411200003001c00341e140c2d1200f9001c00d40201020a6012200d800290a00d401c0a644101070f403203400130a05115024a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 259198911 1250 259197661 259197667
    0x8060a060b0c0c0d0c05041401170705060906182101150e070809150c0a02010e0a0804090e030d0606020f070806010806040803151002070f120b0610110616030b0d03090308 75
    0x200d40140c40101a86c40316800504000140a8110760268002d04a5800c0041d01309202e00c040d410b2602d071405402066404481131054400d642058409401c09104030405200c84600d82170000383c411401000c03540950382601a0071020407001e00401410720a603103c0104210305040e001c07520b03502c0c018044010040c05500007898500b04000d049001d41001040362102d06001881484c15844120341e08050b6080c00340c1c01c0041c1c00c4c00103640a81302e800c001d02500b045d007041c081d4806011443c0a140b110701c01030090341178a07649441a8401492240c000300504170b282e10101c1c1c181350060788558240d4001000400c4214030118a1a50203036000111a959507140100b022070039890441e050340043ca040c3c025a4100d8000580000390750f040c0405242250350388400b442803800c0100024501c240c1400071a40a0a000310301c03042d00350b17250401c0f0740c92803240500c0c1403038458202c904180f038900c2442425004c9405100d04440c4850568140e01c100c060360b10041c1c0700e00050320004110000c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 259200161 1250 259198911 259198913
    0xd02040603050f120f04030803070c060203090d0e010804050d050f07080f071b060801060e010302120f06120c0f060a091809151a0906040b0a06020f16080d050c010204030c08060a060b0c0c0d 83
    0x12f8000c800c140c0d070312038403c54503810641010b9941701d2800b02d1080204a000d04081020b40c0540c004910030341d401001400d2a45c074170310302111140c1010740704130702190303040c4030f0100000c3c4550301920700300b0b140c1d1001c1600c4104904064010b40101c04524104659480d01481203d5001c124241035410900f0132114811100004800070b2103840c0d80c24560780204e1080c007449103c1c408a03280918802c94050258255924030f442c0c0303c90490096030382c428a0410001c4950405c0740191402c40100d0402154140e550200e11207070300c90907554201200e0b0382e50804c404025081003042c24143d8074000802601c464080004140c8289816880c81100fa9800203501c55503150441903500c8409090f889a0540d1100c005c1e660b9035001d00c01e00010b004901c40f09034980744845007035040300c0152004090780510701c681645c442c2d1000044034080e540030032021001c2092920074000a10f443c10050000386400f2a4080450341190050500d41e0810840030a400c0d42c0051085140e8800700e904a81070501 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 259201411 1250 259200161 259200167
    0x120601150504030c1202040f060521100203070807090806070e010e220b0102062212090503010207080415031a0613090510051009061403060d02040603050f120f0403080307 75
    0x50760b030005000b002c1145020070620141701240d050305100342c40030310030304800c84c401000b550914081c0c180c218500321180d4522100300720b80c40d5202501c507001d0b5182c44803c444170000f0b85e44201d8411001c0b8411000740b002e90781d48070100500170600c69018141c141040d110040000041c41c0986e4108008052140b896503154480380348000050003010000e205443c803403d0203843da007400b00b40503015590004030791410401c41d00c1d51590740d1801200041040c0c0d40da0405c41072180a200c0c04000540201049548091000340b03d000e009031a039544031032400700c0441090303822030304140401d0b0401d4030054044000700f01080101c01c080700c03150348640084001355640d403c960310070401c090410090212000c52909036401f540c00648a05030510580c0c070b41031383c5101c0d16200706800520701c3c0c524800b01c58201d4000d55041040200703183c1504007550005015500550000c1d90940c00c010400c0b0105c1e941040806640344200d8019070604e0310488910580303018a10020300002000000a0202c600c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 259202661 1250 259201411 259201417
    0x30e010b120c040b180403050a0c24050705130302120a061107050c060a020a0b04021f030f0b010315030206090103021b030711010806031b011107060810051206011505 73
    0x900a003031450344100d00595036a4400b0580c100d6400340d864500b98284034200310365250b0200b41400584040c0703840e990b4044034194001c500301010484603198070000074100b6816402d89960034080c0481560b030180b511300c110354020b401c0c00706009040061112007414400500c040780d4044660149200130003000a0810003d0300c2c0040c00c0500d480c041101d5840d030b040c0074180f142d01540458030841500002c3c00305c4c5105140065016a204115000001e240c0e4050258420b1019114a13280903030110a0002e94110105a50210f03445541070b86408101d48180036508070240f80034000d01000005030800310606002c003078000c040016281560780d00940440310650000420000c22415104a5030303140c0e004886c0448501c0d0b4050050246c540c880d0304007a008000c002c0281144035070f050b00e1101d199010b03585113410b10142150a08010600340074040c018861515100aa0f1400c0394941d8a8050340b600003500c00c1e00c060282c11010003000031618195001c1e00070202c000304540714240e840340 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 259203911 1250 259202661 259202681
    0xb0613060b04090b04020c03030414030712030b010e10050403030518101e0810052e02101404121d1017180c060f0f03070305010f09110406030e01 64
    0x68240300001940a0049004100321040b60404010b0307641204100b00036841071500b598440e510034004a400300f00d102200c80a400410703021a407800582e42d4640303030b46202503100d403404640c0d1200c0704281540c0144e0ac88090600894144c081c403400c40c0390242644c0241d000290400c04080f03003004518907214494206034000070319005a00200140080c20f09545030790003951082400c80c2c4001c0903004d02c2840e1300030000341c04007007803950030700060100000241110140c14800b462540d100c001d200c179800d070940c4410354094550a581d000381c10f029a113140c110041c40310f00c03a01c00c00010a18511491098102503d0010482c0070401d141440304140100c4d465440101002c07841c198640100381240c0c00390f0f6100c00d83e2029642c81084040e0b041d026850321780c040e0040c65401e480c03880c10350300414841100b48501c0741003480340e04685050b60000c42d0020b010a544100501040c2019441d1344002d2072540c0083c0b01c4003a566600140300c0c01144102c0003890340b510b0641941e40402c0d08158a40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 259205161 1250 259203911 259203949
    0x7050a021905060403200615040f05150a230603060a0f061707020a0c0303120213080a0b2404090206090d20010320030403090305120306100503130b06 66
    0x7a0582c1011030719003000365001c50200c0c500c01d440c10013600c0c20210340441d0380b0702c1d0303c0500655510b506039140030071038141540743d1050343d0390400340c0750801511400c1d0046480311281500c800d0418240502055543c010a07a2007800880d072614854060342d8444d01d020055a415445e07440316800300e80c8181031500f02211041000c0c4003c1406940800d60444c000c0501004036415141e60400b130341c6545240b0009080d030901e00c4810305c007080c05200c66001e000c050303800c010b10f080071002200c100c980d85500201020b42026100c44203205e104510650440242100c048400ba40c0b040354943c0745100c0016503009039103c0c1070480540d42e40b0400d0324003041c0050103050110382d8501e01507101400001042d0f100304400381105005521038403581074442109510f014a0304c2c440641181304c0c0e00014000c0702000004040800068000d116403440c0107201503a00c0e03141d08107101006801c02a5240650070803c041c02006984001003100440300e80d00f208413030005841d00d60118281005d00d00c01402a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 259206411 1250 259205161 259205203
    0x120b01170a090f050f0f21030f090705060f04050a0905010e0a0c03060b0304050a030815060a0e03070f0b0a120203190903270e010803040807051002010e120a110601050907050a02 78
    0xc0e802006c56565011503080d02907a00044907132407110b10450207031000c1c0c6442d82081c80000ca000c107900304081c0c2c008540c4c5040303486003a0f40d580002c0d132541c40100c47c80000382c004a01008541040e114500142111040c24002c940c1003c03042282c80000402091226480781c201584541c001c0d0b1081c40580481e042459070381c9403a00b030841e80c0d40c00840d821000500004001960b8080702c031190307007826400070b03ea645041c82c400341c1210020300951300540e05005124000581d0003446c07180ca8020070030004515181c0603484400b40103418482044140d840c010820068604410b940842c40b0030020400050704071075500f4115140d6401d0001c03002900501007103200c4500c5201d164500b21110140d000d12aa07803910181034407401544200e8007640d106c6101031100d481c02c001f001601010700c7c400041da002d8516040ca00d04051024880580040020032081c142e0740310203100d034a038010000070301c03480d4905000b050b1400c80041c075140c10844041400b0304841d200303005080c52501c503c000400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 259207661 1250 259206411 259206433
    0x10c0f12030902090a11030604150506070f0b0a020f0706050a0f050a05150103111602010507080307031413050703030516081206100207030f12030e0d120b01170a090f05 74
    0x1807041070b40681c803403c0400f0006905004c40e001d0f0001660750459074a0442d00c0700c2051001400e08030110350090101c134100030800303458035000390925034003900e900110034941c1e080124409001429281d80c5600400c840c00d0b108250303108549802c1d038030a44c0060386603580000d12004001c41c0340e010940d141000e0034080901d1141d00924001c0d80400d10126260b0310060042d01295100e102503010f1030400e120308071288214982030306081d03006040c614541a4030b0340e6225450f81c006c460140100e90351714229800100040075481d4800540d00f107002401000d0f4440c1c45d03503039000c0d1000404000001030303403c04071100070a108802c1540809125110b803694200d6214500d001c0310450302036450304003505403207880011008100d0b034003c05546110005601c3d0140714003200d131a14401e2584512048040c03030350401c4480c1081c035055440100505039071251030305940a0102d114100581451110b010103e0421141d801000180c400180380015103032050964240c00300160482c090031526030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 259208911 1250 259207661 259207667
    0xc020106050a140108011505301501051e0c0a06020301140d08040b0304021804110910060921050f15010503060c031302030717150901020301060c02010c0f12 69
    0x101a41d1003118444003854841200010030b502e0030030018000380d6407000400c00c11015921f035140110a51a01c1e0345005503010000c18456079042501080e020000c2000000c4594640d81c0387d004003040c5500d150740c2d00c101c0c000134102d00442501c0b04c000d07000c1500c0c002d002407646046440e542c4401080d1442d00105042c00c0c2c00a4109102d80502052100884401c42c40d00d00494280c10354800c00d407a09240c1800700e40c04040c0c00040040340c1081840c1e0306151520500b4500c10300c2148a101c051013107402400038090b01d054060b08400d00c0c0002d080060281c1c94025406005603090010443c0d03c0c104c4020411101d40342461000c0c16a0280b001c0d980c0010300d010412480301c0150b03100c414216642c84040c0f5a03241c5003150000d86030a02440818888184010038034402d50005080b500c03929150f4a10080040c550490301407075034001e145021141600e01000d50f408a05600210704640c0342100181ca24003159030000e04000780c12490100b00402c40d01e15100c0d41e9003207007100f049480049405 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 259210161 1250 259208911 259208921
    0x1020a05070803180f2818020a120903020d210c0519020f19080702030f06070e061602010e1203040e0a24140315091015030f021003020408010c0201 65
    0xa400786003004072007080e070801e2a1901c1c0704503400b505c1080207210340f1440800c1440340391840c481b00703400d01c00001442c03544c0600300c44115070f804000580e07548514002070a01162a00301c1d000c0380b418008000040380c1c0101e2124000b01103800d00d400b8480d0058000c1c1c41c42c120410001d0300103803800e9401c1c02d6495020006d041504060a004580040080400d90b541c0c0904020340d0f000754080450036554800c4681102c403414821000517007082010b5000908080348074040c1041d90b840300c020044890340c0035408000041c001d0320210716002120b11900c2191030303151406814000c4030081c418151b01d514030040075851240054a8a0300e403203d1311b0849144050f289884941c0c1080405000c2d41c1c0d0003411095005449009400b04510b0040e0445000b41041c0030260300d80a402008000401c0050741c1c0e80c031440312134004d4083c009100c0e01504c1100d410b020700c482260203183c01072000805407401c00d5013030354049468007401c1c040f05204501034401d58101c0f050950802e0910f80d405034054110b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 259211411 1250 259210161 259210177
    0x408030f070204050903040f060e0109150f02010c030b060d0b18090a030f1e1812080403140f0304091a181b030603120d02131d011508070e01020a05070803 68
    0x814802621780000c3c4503680e00070303801515844064004104071841c056228140141810b041201040d581c0e41e01d1784058041005001003c81c840c3c9214400c80d075420710514800304402c0c14100141034900f400b2a9141c00340c01c51005000d91b8510044459a840b00d881300300c00c107050082c0903100e1600e191034a40311401c14804070086003c0a40d000401802015204994504004800304d0b275500002c0c02c560b6000c03c040d2488d01c0001c4880003207550b41050068a4002b801078190030b50b614510300d031007900452018121403581e0040c00ca110409400030048500b04c0350070100100b0050050005c103032031514807220069010480f400c528401c5002c500c500c0c0d00c5040200e00c640f0401c0280c1003815290304c0116010781e41a08490324078510106500c0c013401424000000050030700079500e60010b1685c0c00c3e82c200c590001d4400d10a021421007401c5c0b114003504240c0140c011500d4007000180800c40c0142100c400d1082465040000740d101300100c1d0710b041e8005089890140e520840d43c1c0e1039600c6050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 259212661 1250 259211411 259211419
    0x171506131802071208040c030501020309030414060f0307080a1806050a0b100f0c0501230103050d0c1104050619090c02071d0105012105010305010f0e01051017030408030f0702 77
    0x18008540c0c445600c00e49024030303040783c2c0440300c20800f481c046172460001401141c4403e420704000c404204248040c500c0b034500c0c01c006590741c3d810180c190740c904024080180c85480100442002002481c0c16650000071034240304050351211200d42d03025040700b815200041c40480008000d00c0002d41000f4010035620b2030800c102c141900070302c0f919441e0100c11a0200d9944041d1a4011303124686089800307010301c000107400110b0740521902603110918000c10070314200c0060091100912401d65030f44428200110690413564a4003039990416100314402c170750f684002138254603056541348000c0310021401894540f1003048200412505071140300601c40d0000105051000d0f00c075000203002c1c6502081204d0b840c203801156107904817071800c0c01c10014001141920000742c01050b000e1441000086035070340e40081800c040f039907101d1000520b42e042905121203032090911140036140b003016141000da9400034103502c1d5200d550301000162200040326980c1c00c588801810005200300c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 259213911 1250 259212661 259212689
    0xf02031e06031b040f0203011e05030601030c09050c0910021f06030b3c060102100204061d0a180f0501090902100513051201090b0601080717150613 65
    0x3a0040380800c0c045030020741591002e1007103458581002c01001e8a10402071000c1910341400542c64180c0e0800c0e4040414400c6080354412414075242441001c0c9c8001c0d8014800c6600d10b44034480c0100e03c6110350040e00396988042001340494904690030000701400011685011342030095039640b040344103d80252003140e0b404200e8105016440840340c00c58403c81240e241c1c41c54010303c44d0040709540b081442c03011800304008502c0c10031005040118414106140b43c02000a400c00c0500300b1070008040c81004140001500408208181051401c1041813419860040340c15920340c1d420040c8910704c9000e0004a204040e00051808100084140b0880c0d0b42c614060302074031107946000b50710001c0316010303181c654480d8020300362100300e11000500d560754810106c1ea5042d2a0701a064050f51903080d2103040c0a000f003a0750740c102c20280380510591400c11801012800d00b0901043e1242d5000040f880c0b0400c011210b21f2100001448545d4071246000780303184410300ca00c240032203070300e0b50 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 259215161 1250 259213911 259213951
    0x70203070b07050a111924150305010b01020610170703060f02091e0f131103011d090c010e041d01023001050607020409050a060f06081e03040905100305010f0203 71
    0x10444030400c800000c038a00103000b07147d40b078102c1c0c280035030700040146c10f28550884511071035009451003100400e522820712400c609006080d955078042c00750540d8020005d00290019200c000000c0342c944819142000c1c0c1000d10803410031841e0307440a41524100801c121500c0207943c01030200c031200700c03860240e0380c1c000301012590700404c80c40035034001100c3c048801142071401181c42205400100012108500000342c130594000f81c00c50401080d43c803501e003042c030980c0481140c200c0c030321000400d003414403800002d01e02d0541c480c03000e02a0380c82d0035268540b002030030604da4850020100a5486080c0c10700840380c00100c1c00004400700d4075089041554450301d0303a003181a01c101601d220300d00b4900f9024400a00b99030401113030280718056001d0042041c0b03200c3e41103a5684400049041c81c60007030480c0c54070001c2c0c00000c000307851855405449440c0042241c08a51742c3e08170110b810f5444601502d235003039040c0d00241255081031602c40c0a00f4190380107600c03074984040070340480000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 259216411 1250 259215161 259215163
    0x1b0706090807080c100207080f06040201030608031801120f0515031e03030c07082205030705011704140a0b070305011e08031b0106120c170303130308070203070b07050a11 75
    0x2403248444603041503203084e8207402c2c5030101300741d600e581e4011154642e941c1d00071149054050000c3d0361281d00081d00f4841150b904d4011003000b458000300660810326556a000203400d0003821301414098a42001c1807840d0315504180c541d1048030004000c03501e000390b4003800301f120301040c680c802d0254170f108010780c8403e42296039546001d040198110b559240c000b04160f0f102070000d940d00c05003402004014504049128195003c030700e0505900d5142409061800f1a2604040d0501c09404428040d4000c0c41d054264080d030000e1142048104104100d801c1a0b907080000c0c114600c4001042003898043e042241241c1c4481c00c50300e03407241c01a880700720b4901d882c016410550400c0002c05a086010311968801c60700f03c1000250060703a51007000c141c000351810480d503105202c0802c00c290815466001040e14012003d985545080e02d03043c00c1003c2081801428070101c2c00214440600c02c00549a03080d80c481c010b01a9070a00740d07006003031034010800f240b0000d49522a50303040c0307540c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 259217661 1250 259216411 259216423
    0x1a04050a020a08010b07060f0f020d0c0503070e01081504090308040b010503061b0703141605150c1e2205030d020d1d042003011802040308180103021b07060908 70
    0x5a0f0b948a04090f4213000e103c00b060f83c804c030400d951868840703124000c2d10701d0034070a44010300e00351034005940d035415081c580259034144d0300c148203000d0180100100e160700000700500c030180920f4003c0242d620099440b40c0ca071080c096664100d45400d211400701074006580a004030702411046400f81e0f071b603004041c1c1d500804c80d0b0000ba03500d042849004c100d044000504100340c0319092442c0c04800985612003e504030000d0341101300081c0d4582e41c244642405003800d0742c0140c809011051400f20a500510320a0300603540c0d0501180548250003087c3d502036031520082c020714420724404509030480e103003140c1d0003668843d00641140c1c0d0101c0d400060201892103043d100ca03407601d21541c034400400044c20a080742c0242c2c43c1d41d0280651510341144d106c0107031070880300c15140e50400002c6003800700c0114000c500c0620400c01031020881842c1518000880d807184a2121303102c00c80120082e0080c100a16402d81111955014035040070071004103a0303d00b5628803110940d50060181c0d188 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 259218911 1250 259217661 259217677
    0x30f02011119030c030c060c051c061a0a021c030906180f02060a0e030604210906120f0617012901052208100c020c0103090b0f070908011a04050a02 65
    0x903410b01d4400001e4010080490114000e0910340070061480d254a8156034030f1012590005c0d000042408c6403032042c0240a4072311170315003410031542d8106207d0341030500e420802d00300180390100da030f103400502c20010701a103825401d44035031113016014400b8010304840c1c00211079241c1030112544501e044100c43d201d225400c0800342040d14555000d001a40e402080f00408000c00a004245a920104485405a44a4440b60b445542200e1114002c09005040c2c0010413451a02c200801d9920041c821035000341000c0019424480c1000c081c001d0a0f2648030350518900c01c03840d20100a0b041d440300c454640b04207171114818030701e45124002e65009000050100d101885903011a611a0003803180c60720109400b50300703941d11f8840c2c407071402540e040c3c448851034580b504800015070503c101c41c210403007070030140826007041d5580e8070101c000500f0703146032071a04800284403e1181141c8402003000c0d0000300100c0095601000490300d8203420180103604100210354140540d1003103900c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 259220161 1250 259218911 259218943
    0x509010e01030f0209120a051905070303031e0e030c0606090c071716300f0813150c140c0303130602070c0e010303020d020d0e060a03060e01030f020111 67
    0x1000d1500040d4000c1040c4403c000c00c003a401d000c0d0b05220b4607400b180c600d4806002c0024007000e0300034a01945408241d00f062000c20f6030742c18030100040c10028045059071751504012075404007000c240c104130303552490302d029040e090141140380f00034044000d043d00d030328240a807080395581c1401c1c00141e040940c0c011411010402980c0c02160514507100c000360044e140315442c1032a075001c250703052441c502c4140c5000794a01c2e010007003e81204002c808503855121822850030000c000646415034055009003804a06000500d95610702c4204040c0d0aa0041c1d0b048503400101a0b00001010103402c03d0300410051903c2c0f4201c0e0805030b040d01d00c1060035500451440d42c640c0e0003c0c20f0940081c00c100e50141d000d03c01c0400194440600802400045d50350141c1907266040083c540085405500705540105520203200b0358881c60301c4c8518507007500c090b603584241503421001801c0c10342c0200c200c03504090000c41000b6143c1014948203000b6a104040c4d080203034175168603140024003900d54 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 259221411 1250 259220161 259220177
    0x8100e060112021305071e140f07110a03050d09121e0c09020c0610090e100b010c020306010905070f0207060206010920130512010605220213080319050901 68
    0x300700704204141401503c050151644c0b5484003032008152541500c91101143d400040200c04891503000740858900034501072448900ca03152402c0e4038410380f0344400d00755800141c00021302196003082d481740e80c400b510401e1200e0340c0f42401c5840b19601d44102c0c00043c400b02d000204000070110190b01c2941221039030080b019580c0201d1040f90700b4450031240c0001c09000000c178500c0d2803000c1c00d4141610005485a46006440945c040341c10f5040040000c0ca08140e84104500018042e040208448000105030b0100310050300c1200d5510f078001c0d85403003030b00000b0900c2c20301500030782d0040245851702c15040c0c031241d509176114040e80c0101401a8080b07401084141f260383c10900c0d480e070700c00c1c071400b100d440e451281d01c0769980302141d1240640c08900e410006030500c04580ca0344c01401c40000c006507400c03e000140170544c0040c1c180042e0b55544820b50548000d139048512040ca440000341100e541c0c1c03481c0980703a40007a0800e43c43c03a2075107013000070380300d005104450700300300c059540510f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 259222661 1250 259221411 259221419
    0x910030f38180715030e03070f1a010303080a05040201030b0312120c030403050a0503100f03030804031404120b04050c0301150602060a0203070509220c0e0a050d0201050301031403071b08100e0601 86
    0x2403640d00201303a41c4205529150001d100040500050a407a4041c07101c10100c0c05960400c41c0d00c215012051034000c5004000410210303030700102c542c0c1c01c16800200418543c0399400101c02401070118055414000c240703455056010703e030024108101411482d94141d174440e224940980401c50340900416801c002c0c4c02071642c421f4000310b51241e400d00035045981d440e5603c1201c0304803503400460200e407088050005142c0c1000e081410700b0303106a0030320b25203402c000f4244030403807645000409075500341001c034003000000c3c44111200c0d10302500802001d05050a030460300f00303d41c45084094000c550118421164a0007180c0c407031340310b42c0c5955240c51341520030b00c010860009114061151040b0025810360a54010300001c18501d80c1e03894400860070f410010606403030303030006d403040821801031341c0141d8100081d241100e8002100c007081920000e2040c0c114421840300401005c00b0504d000e00ca01c4c004410042622090030490380402c0c0341c00120307000c40c2c0940811000b185d004000400c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 259223911 1250 259222661 259222679
    0x30705011b05070e04080a18050102071206110d0615030203040201020c010c11120303010501120204050306040602033103081501020a08030c040f080c0f0910030f381807 74
    0x6400248540100c88043d039072520180040003082e01c08072404000081c4001040c0d0b440340c41042101098544042100d00d4600081e545140074400c69440d19621055807040c810700380c0c480c1050200481021b503660209082c1c200040490780644d0a0300f03000102001c100340d10a2090342d10595043e0010311082c140304005507507024580340200e401a0301020404410b450f04800c48091004500c01140c40e541444000f51001e601c6c0381d01c400d92540306100c100074544e000916144c001c0c0d001040144d0341c1e280c10300701c140d085044449a84c0034003030311800d5034405007003900350680450103580e502565450380302c1200b61440b40721200c40d005034000681c080208411800a581020200258a02e0a95256200a0740c01d500d9031006205401c20301c806082802d100c400000b1001d0201d80d160040c3c64074070178200c40b42c2c0c1030b4000980041d03440d481420406c4109125149a40c85107500c5202c0421104d20400341d18541a0b02c100c4400140e81c08102c440189442100c149040d100c0504004c41c180700c04a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 259225161 1250 259223911 259223957
    0x803071502090a03140105090f16031211160e060609031b0103151d010e070f11150901020702120309010e041a041803031a0603010611010908040617010503070501 71
    0xc01c1d84400210340004c0003c06402d15401c90903a0b41001140c4c7d0300c1c0c0241018101040492011520b42003040c444080c145000d120b074080d6680281034419121f03402c0300884400c0e003001c0b4401900d1084c5941041041042d0301518101ca522801030411680c81c0000e01205020701c000710758250380110f8406142950602c00702d0792400c0185000920b001e0ba004840c8596462a44005024110f80d054410701e01400d100b4140508100d40c1000007900b081c4100030034440d1034402030350402c00341d03288248840030f051100f520040d102d15404906814042000c40c000c0d841240c00701d128201240c040641104044291894118140c6a00c1c1c1441110b805210240511000300540c0c5201194080403035035841c82011488104a00c4e0402407082e1403602134203c078440721a0721903541c1c801c00145190340e1001e0449065450743e1070a1004102010343c0b060140c00880c0d03005108040114002c2542c0781d01030040400c02c014082100b081c0d0366a03034103054948081e8000c0b28009032055120505440042034a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 259226411 1250 259225161 259225177
    0x160b0117010c05180609150d09030e09061008070e0301020406120e1605060d0b03060c0301030b0f0112020d02012607170f01050f0303070c09050f0a1b14040506040308130803071502 79
    0xa042909031f003101e2130b04035583c082d40784040595901d14011080c50b6100101e60341850381520715049a0401200240100080c1554401007154900020b400c00d8880c03043c0b207190220140c02503442c0c0d510ac007400b4011243c18050742890302c0c500034120449a20000300b402d4400c0004002152450030b02050000e9903006c5030803c0c0410b500d0303440114641c0c904000180c0b05031605101c0725181d50442c0b0700750000c00c802404250081c40e54400510031116075074904018940c1c100c4203000030159910040e90384000020080c40e111603403000078400c03925103001d414850145a07580f04042d01c00f0501c403403507000c016560802808241c100511403030178101d0070f00810000003000c8038103041103562683c0c2081656042030080585400a114910705a205000d400200226080c42030100d40540442c05400100017034080010315810403079880440012a0301804025204035503560f140e0400900982c030110890444ca2102c1d01c0028615a001c8244e80203e917208140b0348a921030060343c80d01135001110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 259227661 1250 259226411 259226419
    0x60108190e0723060c060f040317160f0302040311040c031e090c090902010203180402041203051207092412051e0601030b010c08160b0117010c05180609 67
    0x80e8820581100b0000000100008425403180200c40c11115003401c9500c0760080c015441031042840c1548082070b5aa84200080c0d5401010360b2a41003c445801040d9070b80300e2030717464000901101c0c100600180e0aa08002e84852002400c0005e0460807482588800350074180c40d081c0680003440c0913000044218007070314000c550010203048811888ac10030000d410083d9603990000c00300910f101d0b5890081020b1001006103000c1a00041d4a81c880d80c240f541e4511114104907510b555280d043d038000c1c00d03101c400241c41c60b010703260140041d40407020f09141d00ca0914002441244076111840991b41e20f103031083c3c1000d04000032001c038a59241401030078066041074040740c03c0301d9407041502c603401c0311036002c402a40c20300c4901c450100181c0301c141003609151185c81241d03001480310310710b13a80c030500907607403000340e0a00c442e50f02c640200d0040ca006c1084000144008100146241c0302810038000c009210140200380c44c103200e001e8400840154a02802002d49000400340981c010094 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 259228911 1250 259227661 259227671
    0x1a160c051006063605091e0a020c1005100b0c0f0610090c030603020109180605040501270c090611010b0a0305030c0d02010513020904080705030d02190806010819 71
    0x10081c01500c00540190340001c50140d01801e50030003208600000001a2600b40030785020000d8984080620b0f0085600809852012450350100f0801004112090707808000c45e90400d242850007a60120311100075920851580c142e000d0141d1052a0003409507800c00d4014500d440c01d03000d0260002c50701c02140380200b40115540e01810301040d4401e0340844080e54100d420f00c1e240e241211083c2d41c040d03080500c2e241092005036040280c2e070064070000342940c0c4062980c1c0d0391140140596411aa420605060002440c03c6010003600380341c0454880012102c0d0000d0003c00031079208251190000d04100c2d4100318032806a42910701000c940030001c9002e031008000b00b2030360b80f4035600484035540700280009002406001000c0302e5050352009110f6400e103855003c203803d00c28540a8801d1042c90049010070919034211403100303a0003000e417a00c4002850040c0000e42200e40d01c54000c600e880441000140b180345141d204200507124542641c9130b014803901824409444510215612 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 259230161 1250 259228911 259228933
    0x609050f03040906050114121f05031906200403060902010306090e0a0203010e070501080105060904180308010f24110705130614060a02030406030b010c1401091a160c05 74
    0x140700500282c00c0088010540500d4900010071043c1c114003142c045810a00500140305050315442d90000443d490104c102881042c0451203203000d41d00540e8140702c1c1102c4084002c1e40c0c0b07042114071038002e000030440302c5000310310700046840d5070059080c0b580d820013060001640c240e10000d1440c0c0103150014819807184050004c840310380707400c1180c41c1d010a0b8210110b107024050504232201c00805402914035145c0082d080070018041c49100341008294560203881d09c0e40560141d42150310f0402d403540c410300380502581401c3c000d0800fa0410084003003400c0c20710300d0f150030991590300800c41c1c038281c41f640112100745030040000005d0042075800155580c0d016642c40d0000812640024617074a04003c00680d100c200d259240200010b02c40701e44810f40200c299801c50b806800d0100b8001c10f0a00100d6400c0940c82c8000e0210f405040c0388640709105600640d030451180107010f0003164218500c01c0c58400445401c081e80c0d55160310b10441ca0b10800c004ac440900c1003084503029084 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 259231411 1250 259230161 259230163
    0x109090c050607110f01020f07120f17040303110c01080a05060a0b180406050a030f02010f030e0601090f0513150b040b030a03030905060c03010b0d0c0203070210121d0a0609050f 78
    0x8031506441c010744c2e0021040140c41c060700641c0da1042c09000621200e4034640c403003901da00c0c80e03100f00211313000032000d08024054645400007009030b101144642c41c40401d01002c0c020741040c00190300003024504801e11551000070f03440000c45e07050310756203601e03958482c40c10040c01d070003001103400500b98880040c2030b06064018000100c1c1c06110750b401000901d003400201c4401c0e9105921405840d8410000b29002d030318074140141c0c080c81d0254035504649801e0300600540000e22040b032103120300000329894030380e0140300445c2404200784041e0301c0302c004d007507100f041604014006030a14154042504d2165104e42e65114000e0310203e030040d0440002070a10743d00391000e402090300e81e2240785c100030003400002e510011001b091415941050038040f4240100105103e1080d501c0c1d01c080c0b5030500030000d41c1c50349940100380a4500b2109040109000280401d41d110035040030b03040c80d43d128441400480c100f40d81802000c44480b00e0300c46c0c00241a030503001740c4540c06031a0040b10f41c050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 259232661 1250 259231411 259231417
    0x4050606090a0f1a090913050a0b01080c0a06050c070501032d020309060f011208070309050d06060e0a0605150f090a030c0608010b0703020607080612010e0105180a0203060109090c0506 81
    0x34128000000061030104805016040c00800503450201080301d64034079a00c84160b0f030340041000a0387c0404041038a800ca290000510024001303014240000504000020b000d40c2b03140000e0b41d0a4141c07950b036010544032401881c45840e0150010b0307000340819446540869036402d032004003004200e550640402c1c00c0320403104500b1031290004100f02100004214460700009802613801076907150028240c082031400d50001c040c1c1c140080c17400c0500d0311030f0380a41e01902d401440c007030b56854146071140003444c103072040301040800480003402030742c001e1042e034084400180807981300c8040300092504070350220320441c00020061044a140791120944280610301c10f0709085100c40c18a1005401000d0580c400750034035004009180000e42c1c085001d6070800c805042895003a100c240000700d030b4420300244544150700c1d0030762070700076000150032550003000b8075503000d0b20000c218070880c2c0d1201c0030950007035090ba00000040005c21680e5000030b40780b0340200c017803404454560b00040d029034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 259233911 1250 259232661 259232669
    0x9090f0204080c0f01170603030f030f07030c0201051509100902190215010f03020d14100b01080108030405150309030708041203030f14010506090102030c0f010507020f01091104050606090a 83
    0x9601007400d00c0104400c01c0409095981100e1102c5001c070044002040b4801001000040d68030782c402294480e20100162004403c0382544e082c1c42e8a1f00b10065442500c00b02e9450000904061080040324011b210f1140180c100694001e82d00349403070280700724602c026009032018005400c00245094441c400307001400360310709094103540c1075004020b240604c900b0b51010b250350950010000311303a0a50441c0200c0e5030540e000344962546041216424915502d020b80c0b0b03000f0845c1c041c81c2c0e0380341c9902170031456409072600c100c1643c80d10304082e5217004078025103400003010101842e41c0794100f0080c582c012800c8007181d1401d640303599805010b41060744810800d0340401400300425400d401039803040174440d5010000c8031620214031840364410f108450140b000081c50030810391083c0112920502c1d800e0450300600311181d0300d60f008080440300340d40140255480d030300511b90103000c1c0c008040c2d04080308800980000082100a01c0041e100686c01001001748810b503440300322401c4020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 259235161 1250 259233911 259233941
    0x608030304230a1104140a020301090606020a080a1b0f08070c0b07020d020111071d010302040b0d0506072d020f0c030a05032a03070804060f030605030a120909 70
    0x2400c1a14000c5402c0151070514240040312030000c030103842000036882c070003079003000a40840c0800000854000d00d0003d0610024414000402c681c1c03403031780c0d001103048844002c010000740f0755031030040740c40f00003806000302124820085203140d07074032030300c50f80580017801020b9410010b51a51003120124600c01c003180c2100c000714040090000c5180360f0001401c4101005250040300d81c0000e402c1882498020b050054541e00303013030000020003c42010b410040d40400d84000c00e0100603030105000d01c8124070650400c1c02034611410104807031020346074804010210364481e400161360030342200601404903032683c030148056008100c40b000b184981ca402402d01031003000c00c1c0601308442e084095001c2c1d40095015400108000100c850140802c101c24121501d40020781a03c0310f00741003441911712000c170b20130050106000041003214420786900c001a84054000c0d020381d58144503459054001000704000b04860240d03c80e114602403500300480354888035040206e40e2504e04024103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 259236411 1250 259235161 259235167
    0x1a03040804081e010507111507110a080c16050d060b030c0411030f0106020d02030f09150a02071404090c03031209080c01091104140c070c0e010b03060913050d05090a09060803 77
    0x103080428031a540d0000407034909101018011401f25564904c01e034107480700e84e403038407000951a6200d0b610001112a401040e1440000c40e41003c20303030758001d60500385181c01040d540c0c17005011071555402c01c440020340301500004040e1600c030014600b00110075058041c0ca50018040c0e03496204000d82014800070658407410070f150900038903072050300113205562003500300c158081c2e000400e503002840301107d1155540d01c0103001c00c000142520040940060118446020903004241c6e1816500e0401302941e6480141c000c00041d22403015015190030800d11050000c00d00c00d075144915100382204c0860003001654035800c00c1d074081048003030284d43d036103c40001c1104e00290300d00903c2040760b0078003200b000384100f2055180301500c8440c03d0030000401d40c040119048442008003a081a40042e03983d455801e4100da500413262540b02d1100100060f902010350048200500c2c0c00400402c4a41c11101c001e4865500100c3d116606c01041170000400c001c041c021b000181000c4400782d91 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 259237661 1250 259236411 259236463
    0x180c08010b010804081606090f03020d080a02090a06031a18060301060608061f090305060c0405010e04090314090109090203040c06020c09070e0f0414100303020f071a0304080408 78
    0x800c50301d10460090400500406100100700003000b640d0b90788030000c14a4030181c0f018903001001b814142d03401000701000c1d01d00030050540106100143e0034040d1078a083d00d0b41c583c000007040748101a00641d1011107031100740a1180309034482c410134000c9a001c41d8843e1000c900050074001c81c1201000031103803d5081259900b030a00404008025a050004150801400092100c6030100c0c1c490310182680300032a001910980305200110307000000d0780c1d61810440b1684259a01500810340410100180c01074142440c0c0b02d52000d1a0f0155620000030b107440c440c8540c01c1c0c1c002c02c4540d04001c0c080b140481c0a1584d4030045000303900c2040d06a00007031074410f000c1d00300504c02d03a8051059940204001815400520030505070204a44083c030020302040080e00809800b0751940c010000b12040240d480d440840081c1a24040e03001c80392007900c1e000c0607a40d101c135203002c1e0f04520411000c04039401c61180000e180c106101c3e411050030035440341c00756807030b0410185c540d50248900b001c0c081 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 259238911 1250 259237661 259237663
    0xf031503010e1204030206070c031211010b0604270e0f0a020312040e0109050406020d021b0c0a06120905010b030604150e150112050106032114030106021e01180c08 72
    0x10745089500340c0074040e503c1000b6500c0445000794400070f03014400c00660390041100001c0b44034082c56108207452004c48521000400d180d002c69880c0605600c1d00010308010310303001090710210380c51044004050108040c2c16808046000740340c002260b16030824000c0b1440c140242c030150a4a14007d00c80c04000707004140c689016021111500e180c2000148070309410410b000e07055039440507003c5401c0d107480c42c2c250300911903800202c03d100d101180d140c2c5040c20f0402840c20040c1260100c40390013280404110b1b0f500000c0c4550000b05801d1507140c0d015059903008251007a0241000244490356000400d041260413a07007100e4801b80d4940080300700030340f4402e001003d89460001d02d801c0210442c1044606d4060054058105550300202d0800109420040103103510080c201c0e241c0001000d0011078120004108020a1400039503240d1280d64500f640d0482d25241e0080120407007a8030f123010000900b990200c4035540321f8100c40704170300702c21003038a800c02c1c0310703960f00e000c080d142110b0b003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 259240161 1250 259238911 259238921
    0x1c200708030d150312110705190815070207090b03030403020405041101080705070804061d120c011209172a0d0e0915010e030c090123010c081903020f03150301 70
    0x41c43d02c01d880c005001141402c82040b4001015017006201d45c0c6484424900c4c050280d8001988100619444030500d881400d0711070494104030700700c846000c050a030310403010100311049030040e400001304009000441d08048400d403000b5003941c1c07500f506c070303008581074440455003560581008e5900b400c482d68400002a8450040e16080b41003000307075529000240300b00c1c42201c081200c50503850850304140b03009a150014020324140006200c1d200c42d544900034030003003034041906541080c103160310078003c4002195001c1c40381d2906042d0907000d4200d6070010400d04c5404d25a8650020354009902500c50002c0303003000050811400321180103060f20f105104460081c503984043c407004200007851615115004d00f412421182c103207002c2460030b042801c000358407403210f9000145410980e0b0054148002080c282c000d0100c0d85801952a01078440e07004002010401440c000480b14840b201c0307046000e454054540310a085452205400554130085480602030070303422589024412 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 259241411 1250 259240161 259240181
    0x10f0608070b0a081906080a060902030d0507080304080a021c0e0906121e01151202090a0e1c03020d050403180e01050a03061a03070f0807081c200708030d 68
    0x107091420400c400c0040c003064000e0440342d0411648045e00c8401c82c1550042000380c984030080315289007880c01c0c58405800030510030790082c0148a00804541e210381c00300c1d4a00c0b5040005039103140c5580d9035a84180e4410000a4214000c03c0c0c0b100a00d00d01500d000445c209003980d5000c1e607075240e20204240141e006e44030300d126921070300709100341040215040d00641c0100c1905400b411070250f4003030242c8031805d1300c201c0140e03143c1c00103e0040e4071008a130a03a14002d45003881242d40792600708045400a070340380c48541e8010180b401e00c2c010782030343d0190300310007500d0003504001d000d21a180075200192022804950f8403501d20205035601d540810081030040588035003949880003094007200c160001600e10340d02c8244064410b108241080034481005d400c44c0c00c1e41c0d0391030400e1403480b1400d0064842074050410006085003000903000618100d0706190a800e0500d050300396501c1303940261030301e106e07001d0101c805489281400150014003c450242d6980c20a90903108102c801e4002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 259242661 1250 259241411 259241429
    0x90e03120c07020d120909060602070e1e04020d1401090303050411090f1306060b0f090a0e01050604121a0f0a0f05010e070507050f0718060905060f100c05010f060807 73
    0x4018000f5070ba90560a02000b5080706032540720310800441140c070308140d500700040041c2041400149994001121401c94440a141d04a1030301c3c0c144d40f0b5070141c000c581030242c0410b40100864003616000b0a0f68801501c1030046405806440d8003650039074180d048103401290307490040005004013510381e450040000c807444601480e0000030140640006020f42035003070380540c0c00d4001c00071142e101c680078102d001d00ca80d4642245181240035076220701865405103411050000e000b0440c007482e07606a45004003c40c0c202400c001e00c100040b481c1480c00da410000d03501b10380c0513075070000407864052610105010940d18110011606441204c400c1c4c2a11615200040000900601003e50454014507001e955147c1e00c0c1032440c68201e060140c500a8044c8400000d58070b03282c4e1114156003054411306100d55a9201000702c2101c0c4100d408c190000004190102549400072501c07003016000d0a014814600781e07202c15007110200c0910502d030560345e50b828052a58204041001419245 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 259243911 1250 259242661 259242667
    0x2206051b07020d0312090206040f080c0901150813060219030516080c13030506180114090a03110709060f090b100c030e0a03082107030501061d040204090e03120c 71
    0x141c0030a503e0240544081c040205402c2c0610b42030740690410a052074006282540751902c2c0c00f921342e15950301d4400c1c8011445250044a280c0c10300a1880d41240c400710086607405a0341d000540f41103000904410b51003c140f5904e0700080c8203480507010100f14044000d0101c0c010000140869001522010700b40220080114040354030603003071a80094075040150702c40880d5000b402a500c05900300416034069081009a01800c412010b164880540000e1024641d03040c00c01b1544d420030f03201780440350042c1d840c40c400309005442d841b008649010480f180ac41c1d988900d48101d8a0503040803484240d507640c10000b2120301e0207400c1004c442240c01001d1f10030340e981d019114400c1300c4001804d0058104844900341d44003a070810045421240d0302d6928080e40880051000400e8240036641000f80b0101c1c000d00d100b4455141a2140ca031110805242488060f203864200c1d070710b2041e4820b030201b001180c5515607000e288040d00540f0000c6482e0741044484205002c401032070352100c1c0d2018 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 259245161 1250 259243911 259243913
    0x13090f0e01020405100c020f150307030b04140412110303130c140a0e19060b070b15150c12040f03030206070c020f0f120105040305090a050307120303052206051b07 72
    0x1044c1703080311107001c0d06100c41400140c1c0301198070030b00c089098951052521444080d252806002140b0078806560304000e10300500701044100c80c0108641c0303107030590340342c0041c0014804015000980a050405a43c0c0140001d14a40307141e0003112444004102c002c030341420020190140405081140880316000e0255408101c4094aa100e842880b212013008110f40500d50040b42e400e403841b2040600981e074803002220b1066100000807030700c45e50004001000c00d50865400c0000e1740000f0030440c08103035055000e00c4680c20841d020300003406141082c2d55400d819800500040c40011100c0c4540c52860802a06081000700140140810410b4140069032410403910440c1021a82e2081301e07211200842c0311400c90301030078801c0d5840c0c10180805d054000c000b034980e5140c04c035000f0404a4440050545402440c410105856505022640003c4c00398210580c0b2510036490750f014440301c5101c0b203682c201e4045040d148180e035081886210100140d00c503c04c040300071441c42c500200f03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 259246411 1250 259245161 259245169
    0xf0602100608100b2101141305250e0f1602030307050901230a0806040c09030203060411180403090f050d11040c091208040503011a011d0613090f0e01020405 69
    0x2083d01c030403155442449101030f40c0c400d42e04030180100c60b140304252642e10803610740202040e4141c404140b07101c20010740141c4408100d03c200c1d40d40680906003180078643c0703040102154031400e001441c10300c440031603105048103d4912801c20311007203034041d00f4010300c80c40741c00f0281c214281c115001001002082508a03003114960403080c030f007500c6000f842c02c5458500300c42881e41d8089920f00094200001c580c00000240600e01c00c44007003003c0c0e0740c072940c1541c29840341e12000350103400840004010038a404218110168042c0c0808100302c140c00c5c0401da0550111022800b04d54019414440e4000042da102d0140c801521130b180c0011546d00c0d807107681840d1030520307403107151284104400d2500c1444054003c1110303010b50f130030000c031070300d0850041e420502451303009620b044420642182e86a110001140741a100c07040950800d417441800303800c0464010360044400c0150050003d200050003000381650400000c0d00703000003004505441300c0d600001017980c01403000b4009a55 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 259247661 1250 259246411 259246423
    0x1103030304021011150108010c030e03030105150c0f0f0a1a1003060207060e030f0a12060e04021509100507020f030601032420030118020c070b1606060f0602100608 72
    0x200c0f0f0521540702142c441e2802d1410201c01a9654405c01210000509480540001c2000a0b884e06c050140460044185031390740001d201d42540a201030410720700882c400c2c00141564007001003650105070800b441140b40500802210915030300c543c40302414012a00094041c0104003000c1d50395504080d0003040f0700035220b01000c2d2229a0003e01705040000940c096020a165141560b448104c012003c258503002007100f580402d11a035054841850144201c400380c402918526910362074540a100075040007401104843c8010082c0e0b03032643d642e000e81180e181c61035544907951034000c0c0c414000110410f0300018080e03031012005000042034100500000845509403001000c0c442c101c03a4064100c41d8090104081c030030420340b07030040e15600118185c0707841003103d00c45602c0308811032049100380c1c404c1c988241c00c444000d02010481400400985240441d0101c4c144469150321044034065448040d6105440b0070400c0b58a406204603088082c0d03000c800c000703103454242507548600e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 259248911 1250 259247661 259247689
    0x20903060c09010e0d0c0f14031002070213020d09060c02060f070e010207051302040305060702031e0304240b15120f060a0e010305060105090a0b06070201031109030109030903110303030402 83
    0x3000482d5044069104809998680070000d01da00c54081850401580454460060f0302403e294200c0101e82c180c059004038006a074007500620300c1031400706d8000002e40042c3c01c1240e02ca0041d52001c04002c140b80042c00b8004d8020030b00140711401480d1080856217100342e03d8040d90481402c1100f0b0380d00c50500e00745c0c802c925007000e50b100b480800c0100c0c100021500240d6206140483c43e26402855501410a49109400700c8902e0b0711001c40991340c90082ea003400c60250b40a45803072020b00c400f1405185c00c14850b074006420300070391894000402c2c038010707520061541e07201d031b4140c4240b501e4a40103c030081c65005440c689400490a039800c060001c01d500f00300c0c10300d4000708072140c07201854031008141c64400b0326402e58492802541f965030a1241c3d911811003840419070081d0140720701c00101070001c11140c80d0075030030b90041d0050142c4644074524030105002200d05510203015407492903100b41d0b1a20541429460040703080108085000e02990050041000503290402450765203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 259250161 1250 259248911 259248931
    0x1a090706140a030e1204060302071101140304080c0c1c020a05090c0d0203090f030a08100e060603190e030415020709020405090613090602040609050117070503010b07030e0901120c0902090306 84
    0x3200d21142d403241741100480e00c0001d5000000b5001511562550251060901c2502d00950004d19880111416001000c5a51907008c0130008640050913a83c02030509040b48016210707641c20800008030103c2d560fa0804460001c8040c42c3c1c411071809a02030809040f044071030280e1410500300001c2d89005900d4510065980000890b48281c0c0800209011020000882c2c1e5541030030381c00200040c20a4584808810b14503c009c40c1d02c00d011090181304420282400782142c1d54031445081505040c2000048169107420484060700c2c28801000078042c0f410459007078800a000091030322581e036114613110361040c00103100707543d2800c02e410740081040750106885480604444001c04050800400051001500082d0075800080d06000c0b03034026290780e0790008100e111070300a40380c103c0341d240c00641c00308018003403181240007801019000b8036094220f003c6a4000c142d4180080e0059898118400400e0082000000c103d01c06040304030000d44c10000b120f00801d54601c005480c0001c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 259251411 1250 259250161 259250171
    0xc02010f140f0d090b07110f031806031e010608151f0507150207061508030a080609100f0801060f05060a02030a0305070e0d060e0111090307050603090102071a090706140a03 76
    0x50000743e5000f01006a4000c102c10256040c58034002c4c200b00c00d40360381d001d0240240c881c00340c2c5002011003500d01540804005061071601c000c1000115030000300108450220f4010100301034401c1c1c015140a40001c0d2103405003400c12030004880703800340c03c440074891841b841c45482c201560584d54180d138100da04003591102d20a14040300c612070b1201d440241c007440400d010060000d550400c2078401b0540c0040c001035501c2e60f02841d00c074442c103009800815034000208220b400d10b40907543e4001501c00e0404080b42d01c4204542940503150701c40c2001da91201814050410300c9112040184001c0340c800b854051407040280d01c1e405140d620500f419038620010b5402c60117030700d81c1014100000d001090b140c2607458802c00130130020401054661038070590f81810003d000c215400c14400174000c24800d841c0c20708010166000400078080b654092140d07500249a40c0c20040100c215002400c51625005090900e0702c2c0a075400075081115004000c2d0100c80400e04031140d0260920340860 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 259252661 1250 259251411 259251427
    0x1e120f180302070e010906050607110a120506061519050d02070210020102211012150e0d020c031501060e04110a030b01030e150f0a0b030d0c02010f140f 67
    0x20041035281260140445050040c8041581c0800d200c2c007038038001c0103850039990f00e4594a10884d0f555004260b0402e008100c000c010800041c0d003150001d80040407401d4003911040c541d01032044000d0b045030583e010388103003c511701c0c0c0244450000400302120b10b00f00a0401c0da00d20300c00c07840c10041402c0c04030001e607200070201182c0407103055a030050076041c10121710520080c000d62088503c1e500b0004203508040c0000c2101c0c001a00451803504c91440481c14456113200762000b0308400c0f680040d11a00307011000a06004d402044644140035049404660401900f032001c40301c82544280c02c0001c08100041c6003480040c1901d095141c040100300002c0d002c500200030401e03229051000204032006e00c5503154000d4002040d00f80ea0030320081004000c3d547c0d41c0d11050780040800b20075600000c60101030304841550140080c2c2010500403146000310b42402341c405214000215024911004d41d6003089610380c2d01c10807464600000c1c5c5403c2002100c600502203070041440000501003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 259253911 1250 259252661 259252691
    0x3090108040606150815011815090f0305030c0d0c02030a0b0402030a050f07091d15040201050d06060801060318030c080a14030903090406120308010b0706060e04050606011e12 77
    0x400307131201c0070051941052084c405040f5420855003034004288584800c0440e5228070140500c004842d0b0080780c1d89410a15110018103c0a40c84400c128440c007000540f40842d481580080d40114095035560011412840c20a0000580e160502c04103018443c0140c6000031003054050300710250450907241ca200180c1071480b440c1025095106806240302600000b2407110200d4100b6001003140000c0d000810004d211003250740c01e096040301c00c0c84171021750310701d0345035500610500d4403501d443c8111800c1d00860f442078103d4400101c0800043c840c20340c00d8070500f1640e8a0201c0d4002c10349000744c0d00180603d42402000309680030200e42070b841d031802100146101003001000c0d644918209150942e139030080b50000b4030031400d03c440000e0200c0720b142d0b034800341a0156540921603085c580341c2d20055002c0d00040344e959950f0900086c10b021010b52040c0100e100e030002d0440d0b42040400145245203100c40000407000d8944003005454100d0300c0750401d510115070210f03031603071000021 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 259255161 1250 259253911 259253921
    0x6031009020d0e06090d031803021506011806030f050703060305031b0c04020a0201091a0103121409060406080f09030a0f0806030316052b09090b030f0706030204180e030901080406 79
    0x403c50500c162002e004490b000441c54010390304032a0740420821a0007a280e401c058401903010340541c1042e0140c900d61304250f50304644c04081810305406000c000440000b030118103500150000b42d0b218003500d50302e0264092a80c00028511b0700744030481c03d54a4103512032040c43c03a4903d800d801c548003029440011f01898001c80401032003151a80c2403020b01074041c00d141841104d90038084035000070072010105145040e01d4010b1903004104039040b030141e402043e503910400522000384100503039543c0b508010805000240e41d0202c05042143d00c180380800003170310142071500148416058103512000301102402c5a251015658542002080c00c6100c0c0000c58030026290352421030900100003000f018030745011a400c8446400005c6c080da155500c1e15a00002844a40703003001556146c2d00611540311000f0700341c070850090048400d1600d09503030b22001c04250007182c100903034401441341a020b80c5241c501802203283e0010f00715140d124101d40b1300e06115440700805c06101141e489 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 259256411 1250 259255161 259255181
    0x20d140106030302010e24070207030b280614041a0306010801020a080708060307050105070203010e070807180218010c050a0609030302070b13020307170c0613030506010506031009020d 81
    0x1445829440000640c0c064506800140d0256003008089626640001a03010b000941e91100ca941c071060309a00a002e0500641010210710510002001040044109034010541240010f007129242804846559154400d401005240850800004081c440e0403603061401325400a400011514041c01c0b084140440c180c15100384400402d0000055004003801c0e00142c1307600b800c80d0740d14002151903440848034140c2581000004001650040d00a4449184014008648141c030858130740c0c0b81694692010f1110307032004600304641040421001c400da020300b2020b6103800f09843c8000b1001400364240360400c1120540720090207001d1102800740c940c8040e00780810790f09400d00802039041560262108031808001c1450b0466074020340b00d50070b0340500900412072030a160303042c0840f41c1c2400b0041c280524107034604940d58840040c0510843c401d0fa211100e419820660720300703903058001c07900409080090058021160410a08540d8000c00259850216207400c0020b0015000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 259257661 1250 259256411 259256423
    0x2270106051c09050d0201140405031c0f090605070f020703051b01260708011d1b04080d170a0501050a0b0904020409050703050603100203160503060a03050609030c0f0705061204020d 80
    0x3c68801000404104500c144a4a074028840c402c11742c00e2400340c18005590090283d441000040080303600a44000c4078090b064400140c440c55400030f5000386d6401107021100c2c107540300108003286400060075a040f01d4a4070050030024119515159074070340c400d400c0c074146080400c01c400765a10400d054092007100700d0741840c0600c42c09851588404007038548002040081c00045000392241701e56451150390450880320076110400c02e60301040d501c03a04615900c0040001042e44081000306d1307464a8403c1c0d640f14206812603034040d80b5000c01034000346406041400410041c0d4840c64084191882e10656603603075030109000900038480e6074849090030382400e08100c1e269070550310031803080e14182d050b1017800c1030b140c01e00c0040b440f089031440e98144c00321008a20036403040001d9035002d080649038008280c2c498440c40c1c034003001124100070176480000c681903074407418001d024080030120002c0000c41d00b40000682036004131f0005002c2d40085000140540d0350b00080241d400340c101ca = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 259258911 1250 259257661 259257671
    0x240806063708030a0201050604021e03060d1b0e06030a0201091502030706150503010b0301050403051e0c06040807031701030c0509070e0a030c090608070e01050603090a150902270106051c 82
    0x202c940380c0701d0300b10404040265103040d0001e1402c1c2803d000300c84000c401d036158003480c0c030b83e0704500064039040030b805c0710741020154510000150175800c80030411424a0008282107103481c1c0c0001c1000c5000303043da4001e401089400d80143d8200c41c8070300076190b000410078074029407140304906c0c40c0907001f4094078080c1402c1c01282101030106001050314402e80003840710b0140300090609840003614021b002501c00c103c00141c000e040602d00301c4100305414011700e4144161800d51401c1c0c0240d40545445e10001266030405401401d5400d41c8002d00c6450300300ca61558461091455152080c42e00070482030300010802d174810820001d040c0300c020020702c04180c9908010054449501030020910f11380f28010800140c001525000c03560840940b0b1005d0b82410203115450708003404010551003003c450701c00146c50811505458014640001400a81da004100501b4003032020491003911203000c1e004204c018060b9241580e49900f4250ba4a154502c44074032010280100180703824505 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 259260161 1250 259258911 259258919
    0x8030307053004030905192d030c05010e031b27090a0303110c0604060c0509150910080103030c12021c0207030c06030203010b04060e030109062408060637 68
    0x402c0303818040e40c000e50300c8400d00385d02e9000b4006001c200e405100356014960310200145c005004008800811070003520404801401403002100603680044908094424062001c0d592000c0340700c03c0c0c000300302c00034061090584100c0503100c001c4508240150340030000030b0704800200a0340403a401080303c2024aa02c0c010b2191503d600e2455411800281400481502d11380b034a8242c07200303812508058201a251690360000a10300c000e4000180901408400040d55500d00b140e030840c0d04100c001d641c6e42003d0030421640004901401081c00081c40052011030b03803083c4011403003580110a01034020503039000360b00d0300f50400308508240745e442d880c10200c16404104501100d01c03030416032421702e231514003d60607030009003c2c0003181501031004003c0c06110703002d0f07501440340c041c0001800c0b600d50f842d2101900e0070f03100c10801c03408441e03003004116503081d8507040c01066004064040340c00c1c9a000150813540070328011141d07054a403a0b08030400f41228805170300a2880444148807561 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 259261411 1250 259260161 259260247
    0x50a0602030315060309120702180f0114040513030e0a09020307020a2306280216140a03051909050303070f200607060e160b030a150803030705 63
    0x725032028010f100d004011000d81072070f0081c3e0340615004009031004400c0c0b84a401ca0075041441c040e81d0020214a4030000700c044540818050f0752800021001d17581404003500d56003001426060181d4a0b000c10811a49482c551a10000d5854034001c180c5030040400030343c84448079041241d43c1403001052181c11500021440d80c4103208114071140c0c44101030140d031184405d0710f0095115001040010455100e90340340442d00e64000403885400d01280c00c400c02207070403130400d07031607000000b00340b031014802c10b05440e51080981c400100540626940c0042450103031221055401c82003021303000c00c0c00d0254038910081d00000c1c0032a0388030400c5081150b80f03030380744400030b84403c0c44620042e02402e07040015a8148032000e4669450013030543d40342e0005141c111484402c070301420101200c1440f45040d820300401c0302ea41703250348a0031b01c1d000c400d04442180012118820340b840040112440100540e030f800003050070141e49403010000c0f200c121414282d480114603040201422000f20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 259262661 1250 259261411 259261417
    0xf09011b0815060705100506060408010501030f0212010b0d030f0504053f0a020f0a0b0a0c03091e05120c0603090303010603050105010e010804060e100207050708010b04200307030204050a060203 85
    0x500c440241d08000d6880b01407101c03511600794050465000f040064189090310b03008243c00200c0600b1140c41c25039035010327548c00c580007a0000c0f00c0c2054038400717081c15441c24402155281400790b00810076680401c00154030114500c1d0014184204034000c15010742c01380013580c009140c007601010800c88004c0e0080301000c50700c00d0b01c50500c104bc06c151045248169500e1203c4d50303000c00105040031040e0200700e24109a4401d203648901d444c2004942d1035142c0e03018290307002042d100c3c40070007031480c07030301401e402041e0f0400c25401c0019242c00c452a030042e035888048540c00d8984d00e1b000800a0141804c011b40c0d2800103404c00b200006001101900000541c102c51070303958108650b9886100440d101043c4a0501c1c1c0003030900808140450791307507400718203201c02c20411956400303622140740d802d0340c0000c46c1c182d45036003040c030042000d40401c0c0107020b01d5a004443c10070004c1c0c2c6100302203800242c0c0340300a11000c4004000620424020340c1250007616004105185007a500c3c20000c1d902c2e4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 259263911 1250 259262661 259262671
    0x12020102041d0610081611010f0e0a0201080610020c13020c030f07170a090b0d0b030d02070302040e071203270b03010302041503260d020a0206040506010614030f09011b08 75
    0x140d051404a6244c0c5c3c400c043c3e8501030760010411311160a42040e00b103403121122000100155620940b294108020f4407038058038500e0034003d0104601540005403080400070900c501031a014550b03135500550108500490081c2120500034900209500354000e0188401450180c4000903030300c21002d82580c043c00b9102d02c42ca0144281101268140741c4038010685190302180301d807501480003001800140021403426200080c21a1000001a1402c0c1c0002000380140e0040103003172055041c0390086a00c081113070030007040e0329851300009150590750114050108281c0b2030b000b5201103a01c02560000ca5207510024103001c1d150496482c4990007880300300e101d64640640940300c1040c02c1c503c102140e4014034101c1c000c941e42400c4241c82c00c03520308541d4141904110400040d100c0f03201802d1403020301e81c01062145014945a458694180c01104c240140c1c0102d0419483d0404122644040c180410701200c0e03d03842c8019014040c640c0c0c100040b04c00c6056240307803540d8440401c130b10807 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 259265161 1250 259263911 259263919
    0x180c05011407061130040807080c010906020306151c0b1c0804060e10090b090402090d080309071a030103061512120e010306030b010504020f04030203070306050901050c1612020102041d06 82
    0xc11201600c214117001c1c1200c0888184107000001400310b040440074100c4240140002c034607111506080784e003129002c84080b41c51035070101c240701542c10b2403010114049550b0010610300100d01c4008880c034081c1003081d4035a141c5417174a40c01c0c680c4401081c40403030070b008424001c00e500c0501c3c14207007640060064400041203940b0928992808008102d0400000c2c2c0b5000d10361414050280021f900418003290401e400f006030501c1c81d212800c0200060b400380c1c1b91940c0301c0c140b80c82e115050002590154585422529500e003402ca0401c04990443e81d1200000608416819025034455000e9001da05219100803c1a0500001942d1059034046580d5552035030b0403a01c005400715030050002400c0d4001c250014083e40c2031030b500800d030840503111410f08150341c03540000d140101c990030864070140c0f40d0b401e01c500c80100740910740c0c005545c2d08565003401c40c2242c0c80812040c550401801481e80d5031f50300c0d90094002c2d0304850207449282541c12201d460020039940d042001d030f85d46801 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 259266411 1250 259265161 259265197
    0x9060405060a060302220e0a0302010608060105090f16030b100302070201140c120d06030f050d0e0f0d03030228090302090108030703090b070501020408030a0909180c050114070611 79
    0x8074100b94070861080e20b03801010114002c418802c3c584100110210150100d50b03070b41c81a00307407c0020020208110710a0740046075980c1402c2c0780368105075040c2c0c4602d015040d01420b001d82c40601106641d0722804c44805c10403220501c105c00c402610031070f0b0110341c1003a480325136101c2e807660540040130742030b000b0b891380d00300641243e0140e00301b44a88c900b82001a00000010790488003818020b083c40c0e070b00300c113020907010385a40715280100568001180d132a13008055405040303400280c001c110340c0c01190703581c914101d0040426540718061000504260b030000d401010f400e00010660b80150b46d40b003115982c1090035030040c102d00351900007a440b94000b0000000c04100004c00c0307422050741039981c100414904040b9034615080b0180460301e40d5000d0102180846082000d404030955a5841c444003919140e412401c1f030707100003c140101211030400f0f0001c995810702020171180207107403482d4a6a1070306081c1500340640140108105e04000c0405074212145000d070503221040720303400003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 259267661 1250 259266411 259266421
    0x1e02040b0f030c10030b0a1e0b0702010207060f17010b0a02010605060906040524030702010f0c0c2d06021303050606100e01122310080304030809040b0609090906040506 74
    0x2a01462010819600d0f502000000c00b460030200031181e03100c81c9078200850100380b00c6000400f074000e0b07038220f601c8080541503241c3e1008180700c008070040030503018440c42c3c0280d50300000d448140c240134040a0250300144640c00511503000400c400301c0000451801303586a05039592241c2c0403001e25001582040e201140600d444002c442d01010b005003464586440c1030184000440324154080344503400c5040c901c0c1c214258001140304924581c0001010028440c140044580e450502c90070440720705d100200058000341e100020440d05080c0144c07103196486007107088001c00d13000810050000ca91282042d40307046201094070301c510162031156807640305000c2041d588603648030010342440310189003540642e0f580034084100c004007080c1d520b001e07811400704068400d4040724501c0d840c810810040e11810f44d0341d02800c5010090f44c5410b1454884104034000c0208845c8241e50394031a81c415540d82c081112071210015002c181949068104e40ea00d50200b1101a1000c6c09200000f039 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 259268911 1250 259267661 259267669
    0xe010c0e0a05010815060c030c07051f120f150608010e0f13030e01021614010828020c07030b04050a14031c05091011040623090105161e02040b 63
    0x107054480c182d4a44040303580f00c00c0d41158a070f0240011035004041008070008800c000e100400510950b80d00070070085180c48184090703121140041c03000c402c1a181040c01007648440c0140501d02603400111740962180c0424004180f0004c1a440c1c03084c59000024090b50000c014078100d402c1401c443c1044d50700d03c00c3e010045401102d000103a851003800a10009000d60031100d041801032040340d440c1c00b10726407899500c440310340200e903004861074150303411580d05c01c48140e4011030080c4185c2e850804c0016241d0b252415810680310107401140c0b51111a000300901c00c019a04580850b140c0d003054201fa54a075400004241c030b95420001d9602c040303640c00000c9801009014100203031200d11001d9420090a003d0194413aa0181c41c4070f48410003942e020341c42004200d60f01322944c2d9490300001402c160700c80ea00c1c158011030300c01410400b250149094900038a004c0c204103607030f0040c8070300e80e19440341192401003414280a90b50300d0300c041c8092000142c10f200361020002092010104 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 259270161 1250 259268911 259268929
    0xf011410061b0804030c090e0d1106070f020c0301020d0501061803020310090f0606141002010605090103110d120e0a140a05061602040203040605070f14071211010e010c0e 75
    0x4140414038040c0d40030a07503803075002c00002190054603c6801d05440755184000000300381d1100300303080d45480d080b11031000140400003400c030007420407150b0a0000c01c40076031500c40090510082c803c65900c440380c403900a100040010b10014000c40d075490544181c0001031000380540c034002500c03181381c410313003010514031181940d800070020080c0d1185a040c0d07001070800d4040403126004103521100c0060301030700030080905a40c200c4a17100403400401d0040d10f192440c550021a070518000b00034a40310720341c841d41034a400c42c402808803803103a008076160001c4604003e007021342c0c8104803c0102c3d80030302c1035030f1030300e000b290701c2d04130315940300d03221000d24040280c0d0f244d2011800f6420062440c07d040184a402c480070007040341c3c0000380e00020101c0c6c20481d0142c505989490070066802d620018004044c090703410640b90301040a027080f0b81b54001d01c2c0000300455103a81d5078030f00c00780c01569074101110740e1070001d04c40c0380d100c100c455010340100d030840d02c00304070305540c00030b818640703261301c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 259271411 1250 259270161 259270169
    0xa05041e0f0b0a1d10050601051201030204050402010203120901140717070c031b05060a050112030203120c04170f07090204082503121d03030f0318010b030f011410 72
    0x11000100c426501d420401d0300c07000e0321803c982aa5111062158034922114000d19001003001d4001610040703002130a980340184254100701081240e06081c40c0c0c42001141901e4054030001055a91840107034618840e840c0c48001d609200002c216035000b054200c0c00a80b201003400d244070351910101520000b0446481390701c0c00c1781981c00909101e10a1000014590081c508250707801d0881d40400395008018109481d0758001c501044411000c81c05081d0040c001040c82840d072038200c0c0c400948900402041c001c03411964804680d011780c0c0401034138058405c01210448165206400c507644031015110072121b40651600080c03034866034400e503800c540c50704015104005910031a40318080ba041c42494120203051008400300740f42502d8101c1c204169143e08603034034207520480740400c04281486109601c1000180814540303c42a0303034008079061a00c01c810311451020714054480050310319014800c40f1482c18854005420001e903500500350f554060791182d0714103403100c6140e801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 259272661 1250 259271411 259271423
    0x5281e08091e090118110a080610170109020702010305061905060702030709060e06030f010c09060c0f0204141e010b120c0f03010807050a0803070c031202010f050a05041e 75
    0x218650341d50030900d003492120395141003200e4004100600080c10070100381c00c29011043c00700611814410284200d6003000290401e017410440e10b00c0000b80b02c207200400c1c07513000700c2c9800403004407540940e559960b0040c40c0d4a00100319a110141000290801c600903400a41040086103017410508009500d2243c101d0418400c6801c15040c0a500e500155007284c061007000d1000441100a1180d08040d10380c1c0c04120b1214180001014904992440c01c035145134544020900400d4020041d00c088405070b04100c11000b942e0300b825445030300e034008040d41143c103000d854440005c5291505114040c4660400300d003000d00751411011000c00d0080810034981046050030b07000e10160016800000c2050a82c0b9201051483c800f5941003a4045285030744010801e104030315002148002810201300111704000f1a51595401485144800341c030f1400e0b000700c0d84400034400c1d002407543c0581d040091007142402100d010082008031410754145114401d0382c101413607121218030856070042 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 259273911 1250 259272661 259272667
    0xb040c06170604020901111603030906080708060d02040e060f0403080c0406020709050c07053c0a030e0114070f050c04051303030c0c0c0314012a0c05281e08 69
    0x1801d000095201d00030142c107000c91150020187d04040055010b8508902001140d1600d1850041c00d611280e80180060110078400c010700c0daa0700104140d031090303040340d444d00004c2c024000f240050881400c142c0aa010b4001084006543c20481178080c61281d03440100ca1781c0e650b01402e4072406140203180040c1c00001003048603501c0e9410142e000180050b002d4a48409956683d01d070052071292202114080e507480000000c0d00441c003095222040880f1400c4141e1f030104980355100d54a004003031001c41200409103901c210102c0070021109a010781e034032815811301c0c0707841c3c41c58040121384074428421840c685040070301410f4018448841c4000601d122035905030080c0140040000401c2640c85922010a81c540030160055000c0c1150002d0380100104030703429036502503111006581c02005a055160000960410355121803a1011200b180c5103440750808000390000036403002e06103d41320100b00390007081c03040503100e410f5a8405640b048020100040c842d800900003031018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 259275161 1250 259273911 259273921
    0x50a18020f0409050108061503190311070906090b03010f02070f020d17070803160306030c0501052a011410030b24183405130801090b040c0617 63
    0x240c01400054084078012400c0a4481d450101110402d9010480315800441401402008840b90b604410f0003034014101c1615542c2c1c404800d40702c49031008040040c0c420750004a04030070700164000c0e1508a5003888107940d03502e5080007900c00061000d102e9480c050400541c13252a2003220302c0d09500c01d00e02034401680b50200701d1011104201599000900481442c0d443d0a20008100c85442516003540700d0800701000741107998a504018181880c102c000d01c0481c0c1040720900c116031003442c201d551001581003070401c0c40301d03158440380c0340440c0c1e00e601c0f001d988064021405010701034044c605569500718440b10400c400e484043d00b903031400c201207900703001d50860504040c4c000422000d102030418010982211100e41e0206520320300c4802c0c8a810039040e40314800482c01040c000a4040b0800213085171020000c903003409000000442a00000315404400000c2c55400b000308003001c87e505244031801002c403011101020b42140208881d4010610070005103404441c0386505e80d58 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 259276411 1250 259275161 259275209
    0x51002030c1315110a051209041404050a0203010c080f0402041109060310030b0a06180e070302030a060e011811010f0e0409050a020f090618100510030c0207050a 71
    0x10180611107420300810800000031003080c40b04000f0503140700704011000744414010510007003a0541869078202d1640240450030018242d407010780c1c1c0d00b80c125a140c18102c0010010040750710641040c10003003081005104000c00c41c004d5990080d8024040b41000c44801c4030710510031500d010b880821900800d0160920340d0110f800c1c0c1050038a0a85801d540ea03000544507041100d2559507840100020b004203c4c3c4111002e820000c0c1200a003c500e003001c6441c4802200d44000d08040c650b5050041d0800300108003074401981c018080d0b4011200340d05001000c0c02c1c100d202080c3c2c0c0d40c00c2828000003203ca51386080460364001581c0a90070903d4001184e82111900c4960100011140304c1720725562a40310b04401036109000822842341184180051480d91180e160320407482601000410344402000d0300302d03041011141801c0da6034a085504058980380c11107600540a481d080c4030713486c4c0650150035004190f40071504030f641d8400130440d00765624003034080700e100e00045a03966656 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 259277661 1250 259276411 259276417
    0x1e030801120302010213180b06040506090603090a0828020d120e0c090703060f050406050616080d021201050103050609060307090b210114072a0303020c0d0818010504051002 76
    0x1200f0b2001518100540003052120b0100d50030030080c000994456903030031a500c1c800c403052280150783d01030900d40340000040311406068041400b803040080040c0400d2070502461130f03e6503002c503002c3d0302c40c2500ca1100c803e0503080190340a4005a911300d810721140001507800e500390056890281c0403100b520440c001d042e800b041c500c0302e4401d40d030800500b540c40e42d4650344109010303a00041c05514044296810394110fa1049005a01d0075078180115111032040780e004240c05001405801003078034100145114000f9600800752001c43c000f82081d400205840c102c88099030203016540b074020400070f8020095558980c55031200000304070030030b051b80108138441801400400b01130401240c0d40c0241d005101c10b0526130b5560258900c0e00c1d050044a030303811419a1510710308424000c460404011041d05121540c01c09401040040500c6501143c1090101c0f2080c0c1302c02d180e8903040030700107110580301c8038010800c8418800c4441d00c1403249030f110f41d82040040203561100700440c00254 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 259278911 1250 259277661 259277663
    0x181326031b07061a1005120c1e04120209010608070c02040c0908100f0c0c0c0909020d02040905070614070804030210090815060f010509030a0b0601030b19031e03080112 74
    0x4818410360000c0755061040c07060100ba44071132000c9900390f420400841620a160003800d10905000d150300130410b581c46241c1c40f84a417582170750f60b0580515841c0d4400c54248901040803030006001c5894469000c108050a1007074402c0c0355240d0300c0f80000c0d00d0181e02119104002503600344104003500d059082200c80b15058144000b172561500d00c007a060813115901540815212680c500701c90110b403050f103a156a0514203c00924455625044c07014120310483c450b0304c0d1034400c44402c1d542d40d085500e00c1541d00a00c10802009649040c80e2204668072911002c121030309480b40780303803003400100e80600350301205c80d41c40e050860f030801540b80480c5208504000717101c2c2d03000ca038290040041c2c1c3c1601c80400c1c400c00c42442e29100708001d030302a0451003030410201340120011034500140703e07540242c0c03001009441da90348100480040074004115a449003085030a8040c65200c194101c050344d003d00ca010300b007075a40443e820551448680d00800040b44c25004000b05c24501c08802d08603 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 259280161 1250 259278911 259278961
    0x7052b0f0f0c2301050f07080f0103060f02040b0a0e120c220209090702070305070510080403120e031306120207111005190905011206030503030a0b18132603 69
    0xb030503c00329142c07500ba8600c00540b02c140c3d900d200703010361807106d04400c40d40302c5076924100d050f0780740c24503c01f56170b0f5506110003040182c552802024660054040e00d02072f00154403004d440d0311b0514801010030180400703680c05a00010200c0e001180b01080f10326400401500d01580301c242800461440361080d81e0074071516500340610242c42d550840f016008d500907034003c211036070071030810390f0500805601042c45902098403514886810448440e4843e41509002018038a84030029021340b00b08641c000c4c85010006800c00f005110344160001e503803d9544a502034103420803540100e100fa580050000c04d01100003503071300d182c540322083d103c549914041e824001c1c1d01d02110076010100360f0b0f01012134614401440a545d0007014809a00d5940c4414403003140b85803952502c81c40040c1610305000e071180030790001904c91603864140480c2050242007a441d062050020440d0000c4081394422145400c40c160141c084181070f040d07141c1c481e4558903544480d0030304200100302401c02408 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 259281411 1250 259280161 259280183
    0x1021020301090c05120c130c1b0308090f0c0303120613020c0106181a15040503070b1201050d120c1403030403090303030507020102120112060207052b0f0f0c 69
    0x16242070040ca04980c0c800e00b1043c00389801d080c10008030900303462800200d940180109002c90303407590b5103028001c01d920000100030108050454924400c0380d4000590341b1010740800415620903000d43c031901d00101598001d00c404d048079a1240c250080043e81a0300a21146010110b040c1201d0381101c1c000b030221a040801e201d601c41aa04610f14654032655074034410003104441c4803806940c595030000400a22203034002c0f00c88610014404c0a001d807841445e40a041880301c0b00303c070041d140080448214580e2903404524651140b0070700429080c1c10000042c40d070810764100c04690398094180c02c00441c048000312400900b0714800d803142e03039104048550302c1c1810300c011400b81d0b000c0d95408628608505014041d5036001d8040b800710380c03040140f0402d11400208083c150750726045a255241c0280c1070001c043d000d101c0024040340100c1d11420030500e005c0050000d01851003a9059256064aa0a0f15480c1c0a80300e407401094866485421903032040c84d100300c10034491060002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 259282661 1250 259281411 259281413
    0x90705030607030902040b04020405010c06110f070b0919020105030411010c060f1505011407020103020309010b09071e17070c06060308031501140a020a08030a0603060504030816081021 81
    0x2141600030782e00400402d9a0321101c005500706800350707156030203096038158682850580002d01a50184402900d1283d403442d41001c048510030469502030325030a4025114001810031132b0340c42c1b0050b10b098000f4422886103140b040341090481c88400d8050b1502801c603a20760322483c0d902074203020360b1810822081309540000d011445081d07404800d23404002100c101040361034000500729000241071002d4036044143d42010703103003210015942071030056126110030b055603014050203124075600952020030416907551059002c98500c0901103140241180c4c03102c107a41c0e1444052000e1040e0780100c0000d094603000b41c0321150014882c20300090b01c0da6407a03c941420350010303074419941c0d5901014500c140e69000242c50004407400d001246420700c15074000e9a10a40340070014281e040100010304103440e00d0340312200035a0008028041d40c9401e107801800321800b22601004c42c081c01e40d240c0941489152014803e4106c8c400107004242001c4001000040143e90511107e181c400580 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 259283911 1250 259282661 259282663
    0x70f030603020a090207140105090318030309120f10110a030b0f03100b04061406040923010308191806210f02090307051008070509040207080a0f020606030a08030f09070503 76
    0x40c0040014990043c0c4940c6d9603e005142c50b0002d00e900d600c0e5078100f500340001d0600120845800300030100c6520503214041011070b0944c0a11241164000043d00700a201208080b03814102050b040c2c0580781c11181a0307002004450383c025980311044814040d0342c00182c000e070300540100c00002d01748600d204109002920308117032840040206a110500c00030641060700030320000c0d0020501d00300a0301c0080d400b050907401103124015502e511103000300710706200c1214081101c11000d1080d0b00c01d6840741030840050344402c00682d1482603103819020142c2c030918950030795240b4a0a504940d80c945002142c507140710b0810b02901a04440111110f42d400f489940041000c002c400350322550707500109402c0903059031025002c0e5041c6a503c14540da8804001a44041c2a050140c1c84950071030200e4000d02404900400e09940021000c40041e00315920b450202e101f9400c55000355126030074951110b00c5c0c114014159201840030036580b0308400100c9900080820490f400207940e0400030f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 259285161 1250 259283911 259283929
    0x30e030a030b041107020627031b01020c0a0b0a120b0a0e09070801050c0313080d050c03040b0c0a0c0311010b0a0b1902010b010e1201061a0909010815070f03060302 72
    0x225020a81d1002c1c146541e0400780aa40106280030702e400d820320210380c022401c14807845013039901c5060310000701c1c0c0561800c0ca004018080f0060111941501c00d402c0e980641221400b0550144c032901c01200420304c1d00301c0300c86081c2c408200ea150308009020100fa01c20140c17038401c042c16540c0f558000a440e807a010200c40040810a81e695640d05100366102c1c20721040e40c0040c0d05590600040041031461b00003200e401064542113440c200700d203030070f00f4000b074091140c6408416040100f030040d010308207030103180141d009003003950301511003420a100c0d51203221589030210707202000102c00700e4003400c40107140300c2010300041072103850080040c072468541c0d0098003005402050b078841d000e12080301c0c06561311442c0000c101040035000040c0c802080310209501c10381110b01d00101c10002034000c03600604020322803102556010140380c445800c090900d9025401400002818150015809000c0300c0b00810031b40a58907032050440d07100012110300414180c035403200100580702c0340d840d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 259286411 1250 259285161 259285177
    0x30c0501111e010b12010e060610110604080d0506010f021b21010c1107140f010314090616180303030b03030f070f061a0a1701110c010f050906040b0f07030e03 70
    0x900d6040e180c1040700d000d00c0d0200c1040103038540100d0005408001800c01e0300048112b4400c40c0f04040c5a0302120b034081c0301c9012018500401d414401000a28006408074500c0c0b24021301560743c480e401150072400028000b00107901200010b00d0200343c80100880c0f1000c042c1090f281081880001122000140948d4843e0380d92aa0913603007403603102d501406008601c070f001c0c2c011946403119400110183c0409640f15036411500c0900681c002e620911010b0544500700b00035140c8000c44640383c0d00c00715842c20054015159550040c1c1c444e0b01c809001402c8184005456800c681341100103107202008681c0611042244521903c10f840103070030000d100d512100e11551492a001c0300b982da03041e05888003002009020b0807966504034140040d14460b200100f01000c5040c6890702500000d001d0840f004030014810110f43d07419049040d045004810501003910340041703d55981404580250203a60031101258504c0984a145038222030380e482c010490010306407096007580d01600e2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 259287661 1250 259286411 259286413
    0x3070c090501050109080703060b180406090308280203180316200306042a060804050d0f0c11150d09020301050624031b03040318080106030c0501111e 66
    0x8400c0100c601540140c50141c0801c1c64582e0040b03190001d10790f501c010074040104100c0d112110005651541e0804105800c2c0842a6000f181400e061000003420104415030010340c0f14800686208c048a0040113840858040c641000d080910894003d400c003800107402e1110a40c60310300c4001c4104050440183c06005490b801e42c410b2400340701e0443c000310000030b2911042c0d1158134954000c50b01e40d50003070300501e15100140203240620510b9480c22510041900d00f01404220b00f9484407860384603600c220121000558403000982d501100b403061600040e121141603000104107a40034881d194003e00a030552082c080c0c032885c070b26048100820f0340159203181d5117003580707800d01415401c142c0544540c0100c4a003100010840c4062502c19030607210b0020104000954180c040e0780040300207a502500d0741098503000f40059072103041c801000c0807010010031060010300c0f0f518126070303002d0f000c00840391800700107640c80d5855041040382c0e40901e0789641050540700e8642d66131100380030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 259288911 1250 259287661 259287683
    0xa080a08070201050112020f0f010e04020f07021e0f0d06060305010c1e08010e0612120f0703090f181a0d06022205060f1b0111120106170411030705030307 68
    0x761000b400c60748160700142144040344030060241c0c481c254150820001174865901113a211030058450f440c01601c03040e005840081e00304840400d007030242082c0e07031086901024141c99220114140200004034680c040044071504d00c0600e880c4441c010028443c1c1c401052490340c85d1a0182140c1a42002074081680b52542c101340d82e010b013010a2200419042640c6113505100400200c07840007802c2134090000b0034460384500500b00940402013a90550440d655035401c211071042d500000e008802240f0090404620811465802826114000100c4d100c11000030420806440050552000080001c9014580d034a8400300f010403503000c2c0e08050f83d6441c1c000480c40322003084402040041c003110000780300aa80e1502100d500c80c6845492a441c0e5080c044100c1e20796100704c24460b2990300e03001851408072001c6000d0305a29001c1c1841c08038030703170b41e5101c00d81d020b005080442022841110000300001c1c4100c0b08140c03da0009000c8070701c030301d4448021a1460384980c1007940d030744460f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 259290161 1250 259288911 259288921
    0x9030f030c0717060411040f060807090b0415080a020402090d050f06061509030714150301030f0203060703020c0c090907081e0609010c0c031d04060b2d04030609050a080a08 76
    0x1192044480c1c0d10700600400684c45d0685400608900d540d103010b201d941c48004820513040140c114001030000d1509590082e5a1100503100400d0041c582e00c0c0614100351000d03d51002100e0b14008480c4503401401c030786020703942000020341c000e2155944c003102110880b40454000c00c91150740d5059580142524209803041042030104c0da001080300d0002042402001e48001c1005411604003644500e02c4200380c0b00001c0490402c1c0c420025800702c040000814804021182c0444500990568405444884044050707205007180088079a0140c1001e840900f400c2c10361a90042504050341e1044c2c0d00c9181c0c0c10f052400441c80c10001041c1008070a902140034062140c1002d8000000c22007444070b0600501400380186c406820702446c2130350900ea28a059400e80d14128006008019880d10384551900c00d40280010450428101c4283c0c607214180c0d058030f40b194042d00b070036203051a01d0755403034001415400303204890501502201000084450000d42586503c80c1c850558034034007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 259291411 1250 259290161 259290179
    0x6020d0809030a0c0311150c19020106030809130b031911030106050d0305030702010b090a0f0c02010926040b0304060204080d050412060e1c09090c050405030706030209030f030c07 79
    0x940490056001000100405a080301d0040c0d0300d81c2e070505002c04c8859500403018248000c850320544038501f55800c101c00707011580000d019560000c20b02c0c54044d420b103a4120300b01c07021070000030304103402080181000d1409d20b983c00c02d00300b82541d01290701d004030742c046802d021341c5440c031502c000304030a003013010080c082049141e4140160000c1211078a4800019040340c42e840000d01400000004107050300c0c0b02303400101146802600e183c09a043c89030702100107103030340140c0401c01850a03c02a001d10b00c10b000b039a168030307000b100400b04c0041000c1d40e540300400c101640e03201040108000203500303d400740030f144680c0c0641001602c41d480d061200d4189240b0340c40c80b004128041209100400c00d002c0007840b00c0c1d0b009a400210302041c4403171240741909112440c4800c05c022841400015401000700050b034910020500940f0400e4401b5a00b034012401042c2d4180c2110000344040c038402e038040c001c0d0000041c111380f035821000e143c0e5400c503403004800464a8101c04414814171f08 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 259292661 1250 259291411 259291427
    0x5130e07030506011a1201030215040801051e0702010218010e0f0405150f240a0c0203060a0903020106060207031a0a060b07080322020303090d05030f0d0f0609060b041401030f0606020d 81
    0x1702d40b100180382040441c03048000d04030500000348200e911030560034140c40c00b0819900542580d00080009040c003007100c06080000440f12100c00b0346100000d020b50384180251040c0210040351100c40c00da0110054403c00400ca006507000303850803101307820030b075950b004d010f00603800c5240c0905941c0300d4200f031001031f05110080901440d00110302e00380d40c103505141c17090400007503d5584c5c2c40301c9000c00c0c200ca141034903040295040c410a420300402000d142d00c002000c42c481d80081051554940c0103985815440c40081c0101100345007401c1043d9409030b4079a8401c201c441e00240c07103a01c0d000094501e0304508015500300d500070080002c0282c264a21300410a0b41801080a1401960001e5600d100383c20741903008864614050302003000c200f080e180845640c210709034a600c40000b901e4020a000d451a11b4001d0078420002101109803060300c040d00c2014000c40c0ca400d0410201d031091480f218600c81c100341e80d035803018040550612400740a004954050202c10180c01e03002002c0780 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 259293911 1250 259292661 259292699
    0x40611070b1905031b030a050603150c070b04080c01180506010501180504090f120f080f07141c0c0c03031505060414030f01090b041b0b0405130e0703050601 69
    0x4a080000040b20902d90302c00c108070701041c1c60119500c1d500d5441c10052000808000040b1030700c007105000780005036800c01d5209a106400301c1e1140003940440101c4881c042d00d614a00e050200706403030201d0215400c61354418068182a4075040c000050340e402c4800300310310070f1104000408400e00300b00d01400002d0041009103801e0741452258071182090261510038a8481d07951040004100041360aa02d0840d41c3c03c44052a04040c10342c0e0094000c0c10709600c9800040d1000c80007070b9a07a80141006400b569803543d42d10401d00000c0c0c95142c13550b201000d840302407240b6109074904e6070a14064404003941c0d50352040c075611858640541501c00303010260320f50840c4401c040c4040e0f100c50b81560125900d07051404518010100404d0508000006a1105500f029020001c0c4901048024051886014219075090340c031003003440801d1450048003402507042208210b9440e01c2450000810050000020b401c008002006c0c84c10a140d40100d0b040d0304a4001001404a4803010403202 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 259295161 1250 259293911 259293929
    0x1170102030c0f0c010b280f080a030e031e030406030f0216120309200a05010206132607030206070305070203090f15070f0807110a050102150c0c0304061107 69
    0x5800c00c1c9802c0e046900811000351440d1601081c40745034000d09411039140200050541d500381d01110b02c0a02d0b8502d07240f02c0c2c04140c09686040081c80e50030301c61010f000c60f2642005088090380f40d40d4116003090041b00480e916105842c44044200c240581d1242c02c410000c00440e074031450008040e003070b0340940b080b1055052052080922100c6449040c10015500c00f285c840e2100582005a0041c0f01e400310103000004214110300d159916000241c0c03101d4411a000c1004c25929001240c7d030341000c0b0781e0b0003084c8102c1440c5c40c0001d024002107102d5031601900b100c082d90031130070008600c3d402940043d00168400300a0101e80c40c1c1500c40c00f40c00003654030181d072400581c0b074049240300380841526401a1040d2071800380a01700b900a0b10612540001d042103840a58201141c0e240c0000c2c40a4801070000d08541a452414000d4038046a0701a0040d041014080c204101d6035000106450404441003007000c025820900003407003d4690394032207842981a03014140d03c3c01195130407203c50 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 259296411 1250 259295161 259295167
    0xf0a051312080706050403020f0a0c03051c12020306010309020d030e102303060301090804080f0601050108040f0b0a0e0610180203101214010c09030201081014041a030708030301170102 81
    0x4100c5402c100e50065030020070104280c0c80e540f0f0104e1030140b10120804181c041d41e020350341000300d40392092084900030021a0ba006400b101100c040b40e0f1401c5600020402d05580750042da0541c0d00510b502580c141070018020142e074022503a60406500300b10005070070320601130b0480c50b20501e41219526145404c0707821061a1541400c20f0400300760419a11201000040c070750380d800d4100310b5001da4003000041d2101d580c1c2034030564070071819140024a02134400045079551003000705610031600110884104940c585450100340c10140008d1001034a4034082e1283c407500700400b60155128400164a6a10b02030382010504144e003c20303d0b03654010001e00c07041c03004002c2c0b008103036111f0308080d903040c07803031780c5450ce070f006154202d0310006500f40901e2022140d04203549008682c000e88600000c1d41e500500042c04100c6030250304404580c40c50703222464101035001203110020f10714441c0b00b10078540b000900c0c00005510200f0300f54400401446440e03070001185145a000d50000c0d82 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 259297661 1250 259296411 259296413
    0x50c010f0b010203094e0604020d0f06090c0e01141e04050601050717030105010806010302190813050105090102090102150115121b0306030302010e030f041a0f0a051312 74
    0x1440c0d100b800c03c818840c905403001c3c0010b0f2035041b4140d0301e1044a450100c400901a0422609601c41c48140380f1043d00b50710704140385a035400709940e441998020a24409007901d55141c40603041e0b46001601e14070f83e240314510010340c8000011000e880f0009000c04a58074180480ca9114070880d000384c0a00920026a06c1d000140c5d18002c001076003c0340c020900340d0711400101e07124059180003420040341d010301c0c2c01030b1010b403c0046d0f050702c03403e2b0707075894846d602c102c019020781c07158440380034a84030001c42c040c800340d10030700d14145c2000035074405002e8000951611400e4131001d071001c2040d40d50000743c41945603010080e843ca081d40c40030038520781d98502010f20451402d44e05411050200a00343c0c840d0700c84643c2d00c002d05482400038000c0900c04400700003001000c1a01045015610f03209444402d8840003050300c20603035600c0031191629081c030782d040400c0c0d60f45e8483c00d0161082402402c240409460151500382019900c0c1600c9203241154400c080105901070000c2c00c5034804580 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 259298911 1250 259297661 259297663
    0x140408220b130510030b24091504050a05010f2705120303010e070c08041703120a0b010f030213050d05070803041d1006090b0a020c120c041103060102030702011815050c010f0b0102 79
    0x301f20f010b00d1025541d4100d909004219182c400c10408680c051050480401030350040c00181081e10020350740511025110340066514021140000340440c003150102c00d02d1001030100d1060041c0c00c54000b03403805590b140420b000d0040502c0c940403035000400180a040301c00c80040c0d03406080380c82e20400381186900d03484058480c1d03000d0350101c0b100224064042d02000c000f00c800b0820080484009840c0000121000b890b0001d0400e00040c000c01000b00348501c40c0c02540c0a0300c541a804041361880d03c82004400d01e5108011035450240c1c3c1c600048010052001d400144003540801448440d9241c4e200c0742c1c10402000d894101210b007405000c005d522503801b80a480011080c29a2854090001da142c4580c5184040e4801d040c0c603050000104041656040580241c1d8103118400341c03806850414001103480c0760040e4030600c5001c026600c298030403040d201d0328107141151242c80703090001c080c00405810a02061000800845c071903c02d12429108a2022170104142c0000400003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 259300161 1250 259298911 259298929
    0x7020105040501050a181202130b130917183a0f0b0109020a17041a180105070513270f0e060103050a030201140408220b130510030b 58
    0x9410440301040300306280380a80506c191000d041c0c120103e406560316004484840e0130041240a89103030403201d140c8080714090410020700081c184104291100440c074002d01e070fa982d05641591a101089400c50500c80050018074000314024910300c040c4d1040c01031100090000501c4005800c0046010003448581d250761260388046038040000c21b42410703e91540103d0b40644142080000080c140c12142e0082020340d02c0c0d516040b68220203001c900001303560480700545180d0581ca940045421004400b6600107a80044a18802d401810580c00c644040b207034400031610006110341408541c0c0541d000400c0c04039004032070b02800400c10340804091441404540e03850340c3d0784103007882194004901001d200004c07116a580d40303050a55684601d400c0550141d407034041c040181340e0810640c64032554000d600343e0b01e0300340d8684909030f61a084510741d001015020b8004909245904010080841ba40c8580b18074241007008002c1600303501126401490b00c1d0820005d41c5031201d140ca = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 259301411 1250 259300161 259300169
    0x9180919140d18140d020301020d0509070b13180212010303030506012d0305070e040c03091502120c07380c180105130f030b0a11040b030a0f11030108070603050c0702010504 76
    0x45904da0400c54004191012101c001c020341c194000729a0070f03e01c0405a00003442128000c0444c1d10280d0340350005403251045048144204200c413005220349442d440360f00d02103000d442401858030513a0207049016034400c1c3c10450000c0e840390306128166a100050382d200c0e1401c1c3c064045e689000224a132500c040000802013815104d8000440d09402264250000342000d002806070010a030001802010403210441c2c0c03a5500c0456003c2001051099641d44040c0c2182080306449036030341c009040d0009007080b03e21500540c100701284800c0181c0305080140ca0714419400d0701c0f4075500e04203180c802040a100700d50705018103d02c500c0e00c4126920044801e080c0181e071417146514100c001c10f815000480c1409141100004004200e51018410030b462401040a800e1005003881c042c401c0380f140b290740704014400700303d038410f4643c0900000c807582d480001d40014072400380011900241c7c00f500c00e41e00074072301c2003003000e4250189562001019000303905d0a42d0aa0000e48580aa806 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 259302661 1250 259301411 259301429
    0x3060b030114070f120e0c210a030513031a01170a020a170a080f0705070e010b0d0b030c090a050601020f15010303050304151a0a060509180919140d18 66
    0x4c0d00d419282c0180c902c4950088107038410b01509100c1c01c140707035440080084840c01120742041e0b20a020342c03a90740000120007440f0260070100c3c00354404035100d401070580060035120085002000444001440c85051076002e00c2d40055850041c2c0019000710010f20b40d42c10ba08480068030069071903100031b00545454900390500d980300d860b400c5140c4900514004d1034010001143c2c06400c20304409820200e07c1070080b140142d03116a01504162000c2c80340745440c50702400003d000381b4544d04248488640603084401c40940701002032501c90013900c10745e009503a61014400360b540c5c10300c0000c810303440600003081c0030340e4060381083c10801b0510000d03041100c003002040401c84c400780d4030350030601c4092040c48020214000400708640b01c424581c030400071200001350140c0140300ba034100b410000c018110f801a241119881c24000404031165070182c1c1480c880c40c1440d1502e810368403806222a00208000007000c1e80c81d0111382003112043c07000c00585001c0007008620b03101c040e112034407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 259303911 1250 259302661 259302677
    0x40c030b1b031e0702030403030e011407061a0f040b0306040b0403200606090106030b0906010c05030c030f190c0b070c020307181b09180b060d09050703060b03011407 73
    0x1d50000054246081c6424031002060008a40c07902c500800c0c441e010280000b159110000103a03982e11643c807006000c104290426443c0f03600410003108442481c1440390b240c03041d555100170440d98542c031680c03174060b01500e5821007400d044280b4417801c002614200041d0743e51a00003590344100a00c01009004020005000c0621601d42c40d50111040c0300040d184411a541e0240c031003c08880080c026055000002030b2107201c0d0103100c000003005424500c10303448690044503140074981c1c042c0c52500c400c0001010b2050100014005400c43d04142c544070340408070102000d0480b032144600700450360030054086000002100c0d0046164104134814409520109050501c0b03a032004d410541144070f121052211030700901d059220003e45210700050800096441040700e0040c2d0382412099500507203144000d60000036800c01c001e060301c0c00c002c0410b0f402d42c203650380c42c481190907400c0518208204541409000c40c8028110024480d03107568084502c421a001000c08003001180 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 259305161 1250 259303911 259303921
    0xe0f0706140d14070809010c02010c200a1203020a14030105100c050c040f0c030507170a0906020c0703030f0813030e0d0303020c0a060b0109060203040e01150912050d031103040c030b 80
    0x1e50302400705140841c007a15002e20b011302e005031440c4001c40307094029500782241800071a106129101c030544041d04c40415070400050003190b26000c0c0c2d14140203900c5810200c00102d508401c007451380a60310359026940d4000070300003c10a1400500701c0c0d410100500051116a0701d40798401c000070003502d800880c0d48181d00b0522320309520098101c2e0054a40001158400d480303401401040003141c4050006458086048030120303c20283c088000010002241941921740c00c0324107594001c04002d03040500c2c00f1106414410958030850104070000b5201360581d4005030410b60101c28250200d000c0d01503038a0107010301014a414910810049494004050080d410b07140c01c801c1003411582d04600c0d52070480010300c030704403802d40421a00400021600c0c8004210303030075541440c03143c0401c0d900c0d21100c00500402c0140d000f003401408003001c1b803061285450803107414010402001c20200581000d0211500b00e040009030607000c10410022880c1d131240c0c0c40407241d000160440c43e41e0f076 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 259306411 1250 259305161 259305187
    0xb0916081018141b0f03071a091c032d0e010903080d050402040b0406050f0409020d080f070b0a020c0a0b06040f18020414220305070210030e0f070614 66
    0x1826200501c2c0300f008484615801d8000680c9482216440e40c1003810501800100720a0000c0c2c80a400d90540c040780b4207101041014021000d9408402c1d44181458110340018801303610002e46150030002d40c55550301459406800d110300406810010000c03a182440e1301082c051120081c40180101200e403005641d10070400300000b190010031294880026000c2200a40740c141d80591042c2d0610445008a1134140300349007c42e140201110b252001d030005010203005ea0800aa9104036a5640d11020071203030b00003440008113540e02d2035501c48080c50075020240028040342000d82c41800210004580040c2d80202c00d80c000115404e2a5194030000f000382407422256020f05040c41000f4200348101070388081e8141c421502070084c030200317039030a8a11a5041b034110008001003120b8444d80ca030003044000c0c045000b464464076200d1142c0125040c07120031044800020790710300720048407510a118000040f019803003d004101e02e130000c01018905143d80e41060124001042290014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 259307661 1250 259306411 259306451
    0xf041704090e03091201050c09090402040b0d12030501120b04060e07240207080c09010b0c10020f0414011403180c0a0602010608100212010605090316030b09160810 72
    0x1c601402d1014a0702604895140d401c140141c43c01103038802d0070824492818050b81e4490f00c80f005401c5e0900300680308002d1180710162050741c00c166200b15140311038880035000040540290155214200c0e03c83c0b0041c1150710503405018100703440e40340c010004241030f0703040b5046504181b0100e42c816030303004407904040c0c41c4e5111644a01c2c0c50040190401c081d080d44403406440d98003540c110380d599555554580d42072082242e408241c1d500140844440f4034094452140320404840390301c148140080100e9100089042243d00302050400400d01044068416a1030a203400000c00081202c6442070303000c0501000c2c0c1c4400001e0039034950358810020f45500320700c014241076895030b8910703003c0e0088c0a58000c82d00d140c0100d01c44031400604030f000319007041041c29224642a0720701007040780c040d0020000940d042c0104490703030707c03199942c00404000d14001e0b1401c2d0701504041d511540781c00c00c050708030400f9401c03698040204600108450300c074210502c401180c21038180d214901c10304 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 259308911 1250 259307661 259307669
    0x903030d0e0705130b0303040306021b0706090512010207030c060c180902070302060106020609030405010c02060405130f0e0d02060a050c07050f010509060109060b19111b090a050f041704 82
    0x20307103801c4828010762400240c030320899000340d90410800020303861362000d88140341d800700d0b0582c0c0100020030000d80740ea8020700380380512011003142c440c0c0040615061241a030b1000002640483c400d002c00e15042e42d426100b800c105008628201586d070780a40800e4400320060100e954404039068004e0048000384100d10280b240c201038940c9a40d66034000b900b01140c103038018400c280010a40c0d900000d03c0d540a141d1240066003031618180044030302c82419802241c000c40c0500001510340c407a03404990f442e50901002062004103088800704444051b0501c2c9141c2e401001d141508a802040f01c581040d4034040200301917540304a1912544281d0b1401030051085104000d041071041d40201c0c000c04000003a035200fa41e039124500f040c3d40050040f03441e180030402030b50301124000c0340351611400325410180303040c25021074850300300140102214031081030b5250980d03452400c008410f60050240707804100300d06054041d10400740380140028030300c0b102c0c0d03a4038401100104041c0d500030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 259310161 1250 259308911 259308937
    0x111506040b12060a0501060e010203031f1502010c0f1d04150b030c041a120a0c020109350403050705100c02031006060806010c030f0e040f0906051b0909070302090303 73
    0x4180c10842c000d80e02d0754201c4200d01c0f0507207000d0010490a101e00880405420168021070070b5446003804009a03500c40703080c0b140d02055581c0001a50307034102c1da4100c04440680c00014001c85c546070064800354040c0000010042400c03800d5180440417011400c045400762000500c1004040184c0e504600300e401191405a0110400c404011208010015101000c00991681140b18958045401195445880034031908001104045c00d540101000c108510000c00c074145162910078001540c01205501043c01c05440031805104104074015a80d80c000311518240c9142c079015118850303401442e11682949540a007120b01c00d000e001d001540042c10ba49141c001a005040202031600c41d58000c00d0400001401c1c560041500e08101500742c4c51350f8411003800b00c022240300115160700ad030f110b942c81c1220920f900e0030703114500c00107118840014090074052030580c0300342c8103050407441c60795040015410300e40700e150000340c01580740d00300544c88504c072200007420750082030590440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 259311411 1250 259310161 259310179
    0x110c0604090b030f1020030c09010c111908150903040306020c070f080318120606090c07060501030803060316150813020405090105040221120c010237111506040b 71
    0xe06080e8010005d101005100d41b8900b540e81d854284540000c80e94103811500034030031420340d54010752001c05150b2060041054100741c41000440220702c245c2405506200c401042c040350104010612a07100c1c00c0c46600794501e048030105a881c882c60100400464011414003100e10381044801c000c2d104011201d01456119002d440e0780340c00007012900022420700e4030b458217040000721940c07d1003529015055660318001840f9003407401400015201d40100580d001044083c410140610300c01d158051390303030503d01e0030145881214407402c804420348101c200a000174011003242c200b1001d0605403580d980c1c150100c61084403048000e034009083c24200403c110040d40a58426031003103460304080700500d85142c441403c0b040c41c21000e80e00c10b44a60408400c03041c0074044910b001800549802c008268484000b4000d20701f04c514508601d00800440801202c4001c0001251034803144441005468a680e420307051034a08801d58414082a100c0e1620740100e1040340c00900800b40d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 259312661 1250 259311411 259311433
    0x712050a0302010b0103050c0d050c040801150302040e03032505042102010210270807021c0c090203100905060f030d0f080618061c0b04030f110c0604090b030f 70
    0x61034101586045006510b00000c81070198003034400c05000f0303040040d509041016058000d001000050a030000e5000e082c4070006507010240a54214111079820300303000790b45184140000d403550040701c10503c1d00103104002c51410a0078001ea82200e48800e40840c080c0e0300300045c0c0d42c078800c0d070f0807000c5062280a52901120561069a50307041d01c02e07400c461a0f01d04030795001e401c0760007006000c2004039813010f0207010000040d0f800e116082c001c100307a514101669002848074500100304072808000c9007040c0302403101c1021070500500ca9101e082d071851409a200e0f2046d40030600903100f0140d560404202241c0f40c41c1b01c40d0300d41840c00380403141b50302c80f51100945543d60300070b402c20001d4070781c100107942424107440703004000000d90b10381d041d00d8481c1c90804c40c0311043c405c0400b07405c4126010040104031903448550040d03002e512095944081c0c85401840d46e00b1201d9400a168401c50803860a03444000880c3d0403125501c400080283c0c000c0e0000b4285042040c0300640d0b40b046c204048 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 259313911 1250 259312661 259312663
    0x206030a0c020f0105060a050d1a09160b03070e0409080c010e0f10090803011a19080a0c0806031b0301020705010f1505120a030e131d010609090206070212071205 71
    0x44003035080c9808840b50380c80c811840501707030780d82220485e0b0004440d0200f0803141c10900c41000766036124400034120b907180724200e070120b40380803030b1059025840842141111a2010b031030b02d0140c10001c1040d880c41c174110708003a0070707114074841080c00b6554419840007880a008107480b064100c010003840649911048031b82d980c034000c03104a2050151000304404559684076245100e0b0313103c2191403d581c41e10100000b181343e5440922840c0e8010800f445901c000c8040000c121030054881c520f81d4202040000c0448080141c280c09001504003800005c0d40d000440c030741c052000c1c07480c40219135060004240680221000140743c0e42c00c008160b0034105940c0c002c210581d03515181042825a90f00400c00003080c10113404d131083d0000c0128801080c41166030000240d4090701504282006c20b00c07020440d880b4125181443d401c2da08042032000c030a00408008041c030078018045c104140c4c0000e000fa100d00c11000744540056000b601420341d040c082034000384810320070f0345820309c4541051 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 259315161 1250 259313911 259313921
    0x30f010902040501080c0a0308180a0e01030501060501170a05062d030d0201020a050315030a24060b040b09120f0d024606090b010605040f05060a020d050a0c0206030a 73
    0x1c9124500741400440c00c4c04002814681c0004c2c000c6c502d0180d9880c0d0785450102d58002d05188000410300391104100c1d84a24441000410031500c0d640c40a6140d0b0400900716041604001d0400041c0c00c107a4001009241782650061503031440020240c440343c00289204608041c0803454031001182d0300800350b117000d00c03c1515030003130342035440360024054100c0c201d22440098101062090000c9080208202424044403034098100e4400e4040d80d1a43e0104403034003400040640801c09084688100d9406810020810761a406050506021508405005d06e000309402504590050420141c00300030003880b282007201507408801725150700a450b94440030600d6a1030921410081c280514520754480e65000c12003a40781c80f81c0d12250b440b11840701c0c03017025a80d642d200c441d10000b1403420f40c01280208069145e150380ca40c40c0040080204504d40d0026201d10400c0c091040415004a0354182100e032a1801c40e0750b0380043d0900b0754416020084c0a50800030200c1040902c1d40c0d40d03840 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 259316411 1250 259315161 259315163
    0x5070813051f030f05071e020304090504150b010e0f060a0e0a12031404061e1715120303060306040b040203030f040303030207020f090403022e050a0207020a050306010e01150c02030f0109 82
    0x42408510641355481c4150750050360781e100021100340880810154403051030700d841c1110320549203807680e6180b4500c02c1c6c4d03c2c285c0341903d42e40d009041500d6401d1081c4140340795209c0c2070070b008841e6518000020702a8100035182409400300050103031525100308030880e0b203a81d00801c20643c0e02d44464488086103d000c50413404a0040500404500e1120043d07404440d81c9540304004500604010201c98001c0280d24060003540d14081044100b14410300348622001500c1c10200d03141c40c0c04000ca090b4103c1d001c80580d4100708107100c903079100490f050758000d411aa8404094503a88007003461440364200790750070390001003004010142e254004100c4c1600071101d8002c0c50340380c41e0801c024528181c0e0b004001d03034801144100d004108001c801c042e45007250322401c90140800c41a0196034086600da40d22a40c0003500c0001c62810001403c0a4201034004050710b42c1000481420440103004d0040f15500714844c600c040c91083c1c004007000c583c0617003130310850381251a0070703400723040a500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 259317661 1250 259316411 259316417
    0x70605010503120c0a031b080c0c01020d0c030e0603040c050303070b07090f050d150e1f0606030204150c0f081605060a0e0c13061a0403031d0105070813051f 69
    0x4481804880c0a01942d0300900030300054220352415580680310f1540c04041840d980c2c1f8404419004103901c080607109142c192000b901c140350130394000900b0151941840c1050008200360080880e50100307001c4512281541d5860b603c0d152070501080d50121341e070045034103110000c1e03141d003000613069074039010b8855512005081a10361021051420790ba004e000c1e003041080d014940440d8000400d0007011155403800112404100030403400d141070310705d20400c40da608a0000031204001c0c400c1c500180501d20f0210b05040c10624400c01c0c4a14508803401002464014401400311a0030120300041d0f02c18106c80c0e440302c80c0c030b02400c84020105800e841a014210020b01003a030680603400001c0b5601001c1d00c140180d0400300b01d25103205150403075400343d4404010802102042d035007a101c0e02244200c40d2118994070b0700070510845a600d043c00d0350042c2c41c0180090341c0003810794080340d901c1210a43c507209030f1034440341440d4140c0d0051340d004008d100c000444024851008414031001d80d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 259318911 1250 259317661 259317673
    0xf01051015050d0f020c150c18010c0606090c08090c01080103030504060516060509280209010e0a1407090602010c020a0803010302090709031a1501020c090f1b070605010503 76
    0x41021280d210562140501c508400014007808900c00d000404181240d403900044001c4402601d03412a0002d0031190140e500240411108030a000c0117950301203404555a07142445200c481051020000d500318144078805c0300c900304116290300800090b016004042103e1916840010b040318403d0b03130454568010a0501052940704046a6050381c0c3c06898a0380340c1840d0074421105580304130707520350407007070420803980001e0018042c0c0c500442c0420004e14030000341c841c00025644c1c0342c491010000509641c0b010058488403400340c112664215841d260b580c4908000014050740030641d010300c0356090030400b90b10380048044042e1405603000f0005031691f40740036a40c5101042c4054082c0400f400101b0061170120110b41c0d10409031714114604075900d680c0c5a441c411188000842e910640c8200041007001c1000500021024401020140c000801103000000083c1c0329107442820303800004ca070a20016840b0301002119074501d650f4030b545040c0440200401e02445100740256 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 259320161 1250 259318911 259318921
    0x3091501051e0f030309041b0908030711040506040222060f0302090f0d021c03030e060a05070c0b09011523040902100305070201090b16020706050f0a1103040b04080f0105 75
    0x182481180380042d1291904410150400c0041d601d24a0070141e134144010041c108942c2c4440c0038103904402003114250310124240000740031a0490740001515910a205180104140b000000e4000206490020351134451070040b5001e0302c903c0c0000428000445402c5130041c00a0400c003007150200d0381d40c0d1036940070901d0202e0603840b41c1c802240e44805010407007181d6150a91003008010320060403060140840341c00c06a00401130b400a9000c20360302e40d100c0395000c00c10300940350b00500007141040743c2d10702068040c0c5084060170005c1c01f605922000100032030025444420b020643c1001150700955466075000d500d40f61008080c209034000d007004000c4e003002d00980c0003850b80141315643c1d546600800728020440204158119900c408620000c502091841c602604620b001c680d42c0c1b000c031030400781c5400c51660251341001802c2001628083d61034069540e07ca20300d18020280319903d50106113580203d4100380e11940000a00040c0c0c2c040008110711000c80703c0d8000c1c40643d0322 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 259321411 1250 259320161 259320169
    0x90606010e0f0109030212460b070305100801110d0f0b090103030804050c0d06020c0c03072301120f090311120a031d0f0c0a29090d080309150105 64
    0x241900b6001c5121518184014a00301103580315440c85841264010407402400d40d03103100110901840551002000791692000c2240040d40507100525003408503507190b840c8001414010440801c1664800115010400c5d96203d07100501c10b000080c00403209402ca040c89a5100d001c2c5110042d240070800304441016005003017900324003d143c181540c0c6591400c0d02c04281c024002c6519002c1e40788032440030ba441c09403e4850500070f610042e1964120b16840386444104890b82d84240d001d41d10070804000c85840e07003400d0310340d485517203201d03950b1a600503584040d08405544245080590780000042580d000302e14160103991812001407410101c140c40304441101c0c54a0701004010401c080c60080d0004080002d09100481c5040e10104055040030506041c8440e40d03003001510341c040c2c2c40e02072035210107092a40140b81c4c481400018411415403184401c0c5c3c510180461000c22079034655210983c0c4503001b12080e544c030315008019645130480c001c030844c404210003001240d107041c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 259322661 1250 259321411 259321429
    0xc0712030f0f0e0304140a08011401031416150c0605041104290603070e100201050f0c0a1205060d020909030a02010f0b06030f04020f061b06130c0608060d0b090606010e 74
    0xf5030201951800c1d0600c486044c4c4510150202d80c2c0107461503034002000700091250000d04c46441000e282d203941140f8001c29040c2d90711420054986c0400401004d03c2c448044040440f0030f05882085c101c03c0a50042d2600b0042c454041c0c6580d250104000030310041106945c60110110780401a115800d0103602c18111380645000d110b5100c0e4500219504004005640000d024101320160f1440e40000071a0501085001300c010b175181c1c024040601d900d0000590415100c0c130019041c03c240050040001c1e1980c0501c07010203803140c010031110307211045040451174028001514901d0301810641d42ca41c0010b420000541c81e11007480c5024004d8490a802c151000b4102491134071404501c488500001e4800c0e40d002c0342c0300044580c95600e000c0140441081056516010441003031000e007801c400801610b909a0310800885c00540e000510405541f050b00300324070b090b02c520000c282c6040c02d020000b8144000300c01441552000013130f6140c8940303801d9a81c58108540c0a06200c181c5e1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 259323911 1250 259322661 259322681
    0x1107060507021f120f18120806040c0e010311090301060b0c0d0504030c03020906011e020a031b0203060c0a030608030d0204180b130b030a0507060e090912030604050c0712030f0f 78
    0x1c89403a030b444e044944907000310034010300070000480d041030902c4680207040c0c04035208440c018031140030001c0c0685c00001d5036034000b02c101d40c10407c03201c0503c0050009000358808a04150307541541c0e601c180003203410740e5084c08003e0000c01082e40c40c1da030251810342c480d124480881c8500c0c50429602c81c401d0040313a050b2907000407120440343c40c5509000f0303c003c0242680707042c80260a80c0040500b18401d541c1c1c1030a40940c01402c61740c010f0304002e0210700c0c0044101d25a06080c211800150704d0000b0100c0e00004030303941e17155444044c075400303d00400c0e06400030106400001440c0400016a8020300140d440c00104001682c8008030b488007281c0da1406c2058008071000090803d02e80c460303200c95007081000c0c0c02e68010381c2c1a84d40e1581040103641107038002c541e0309104105141407a104072075110114000410204403a94414880703030100038050b034411512100050320140c28401619001c81d03105403800c1c2150621003002c0d014000c070240c4a00307690b00d8005140400b0400d400b40403090 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 259325161 1250 259323911 259323917
    0x4050a0b040f06031d0a1b0f0305030a080915040602040e0f06031f060b03010e1b0f07020913020919200702040c09050d0b01060e040b0306161107060507021f 69
    0x150b00d4050141c1c05490b8104528205010700180404548010300489000503c62900441484088283c8501f03c0003907420480039142d80540c1070000480000841b00704401500301031105035900c21040d482c1010450094555118400600081000d2600a4001d840301c51443c80391542da0050030b89101c0d507080703510541c5503000c90308400880421000015401c10308140110342c0640740d000d02c07125548280d001d0300003c8821030400c107800030320040c0e185150110b100b0045c5011a66000029540101a40a4441c0303501401050140e480c0d44803c2c152542c2c00340c029100ca180c580c3d02c0b254115146030b0044451410140c00c1c00c0c16100c012030704d0410811200e0300b5401c095041d02840010911040610280401c036140414180e5031602c8281c10b00f0f101d0b00e0556020760420b00f006000c02c0449a155002c1ca0510840d003049a40c0855141d500a03148100c0c030200700301d4804105d80301121001c0030781d000e004e50078022950340e612000a04e000d42c02a69030320304003006108104420000c0d04c0e084000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 259326411 1250 259325161 259325189
    0x10c0f0212030f1b010c0f05041401051b0a0b010503030405010c03050d0b030708030c0c041b0c02010309120e01021203010e0f0723120f09060c0f0d1104050a0b04 71
    0x10700d000c440007000c40640008690a000b000d035030b0243c584d801495503440402e0502c1d00780856080900030482c12a0f004d2901c0300d94402c0c54040039006014600031106a0031414581510a903c1402616600c207004440009206002c900302d40c0c5821550105548009080c400410603050000031074084a506a590001c807686940f001c56494000010741c0440d1034a442c1d00c440381d0307a82001760401800401c005565561400548580b8044070b0062441c003c5042030b180340e441100700038044e80101d140b410000035060031480103d00609800030000c2843c00303006508000c2e26480000a18207070000e80803079080ba49103e0060704240801d00c250b00c00c5030780c180700142400c1c0c0c0089885800903094241760740301107104900130442c4580d0104210812002040404403105960703500368101b90000340844a50804070341c0d031619948001c0c0f1000801ca800150b03017801460000880c1c0e4001e42c00d0004000040d45568074003000e900512a16108550502000c1441411a8100e03000c686101420900d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 259327661 1250 259326411 259326413
    0x215060d0501061707060f0e061b030706060305060a1406030601030f05120f120627130203030d0605030d020712021009150c030201060b040605030103080c0c03030a0c11010c0f 77
    0x50000d0034100e003201c0ea95220800003e08050300394441c020070309074401801485090002c014403000020918808000003070814080c2c43d00ea8504544030104620020301000c0707007180b03220f440c501c0741d80700080c00640f61600000c180900032074160b0090400c0b00d000d00c0b5080c03a0b41800c0003a40b43c1541d003107915070804001000010b0302200c00009861007242510396100300a401502290400c0c40c001c00c198200182c072403c4030200c8040701d030340114101c41d8400200e07648130052404440958403840880425401308881c0703d441810f568290b6801001c40b40d8880c02014014003821840c0b190314002c0c070542d01282071103030011a00d441625030100000c1200402502000340107024039003c2404e1041890000c250049001c02120b260030302601e602140d0f160900c5d001742126541d034090380700100d05000911246600104690450750012845034464144400660400300d503c440254140704c002071824002e40c0142c8584149401a83d0806c111500c40005442d4602d5500c801042e40201510480c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 259328911 1250 259327661 259327669
    0x503162102130b0f120102091c210306091d060f130605060409060e060402090a020316051308060f0708010f1a03070207050913050714010806060a03020906030f01080c01021506 77
    0x19030b00c880000d026580400884c0e021400741c0030f0381c0c00c1102107650001007592107804c01c0218840c814080403d030444c003403015154681c1c2c114002c0014003003800180201d815891280d08230b00042e0540031000c000407054072403007076424642c0315510482401138400095a820360009142e01c106146181034200c40416038441d80107010042401c3d500c01d03519a80040416418072a50b06254141d03c0141410306280c010040740d60780c01880e06000c2c0d8010000c101040d83c00250100c64000981003190b11200160301c071075010045600f06280c0c9100f00d608111041c05402c0600d406000300307403030b00c0100340d80b507803500c4000032294028110340041503004104845200300c0151b074400480c0c0305642d4181d840d0740010301400019241d81d502c040300610500240081407001500130480103243c0102d84000c4c0002800307422005043c5c0d4410500414000701309802901250012440103040d55076a00e096222803005803400e0040355141d12550000c20032079400003510740d8600d103507122580c401e84d444000304 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 259330161 1250 259328911 259328921
    0x120506040507021c170f220c1202031c05091201020c0a0807111201020901020111071707140304060c15051005040f020408030f03070f1704031404050316210213 70
    0x130b100700043d000c0c3e080b144089050700e89004030040202e198007401c060300c1c03484803110b6800c04849407240280e10240001c400350540000c075a81480080c03040d440030300019041000401030081d084007014001600147d103d00107003000322041358421074030440b041c180390807800ba41d801070905911203003400003c44c803490040c0010900c90841003c8000f03544d0045071764002c5a41000a0581d004a072050856030207001e0644002c0c910b4103035030b007045603030f44481010440c542100240e00304006008070501035030f032580d58400c4c6007401c02c40fa0f646907a410f006100c40b5092009072410305070400b04499038034090103801d02504d5100846c86620b030610702000010806d0040d41c1c0f4440c1d608000009100f0320510140ca1a034004064007500c81c42e20101c09045102200c442004011601000401d1028010003851f0460380624103010a0304100000402c54401c6130411a49132282c0d03203492111940034907001c0d00ba100311300d048140b003540160a0704044200c42e00025806501c00075506141000340d840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 259331411 1250 259330161 259330213
    0xa06141f0e0a0b0409060506040609020906040e0a0209090106020a0c060c050303190209131a0d051c050403060501080607031415010e03100c050309012009010503060d05060712050604050702 83
    0x107403d0f0390003001500f2104086821102c0640b1142004a14580780c0318000040c005881c0c1035180c09039180000e1098030941c000d00219000950103c2d064a580381e042e2084100064007001d40f40d6190302c00a95101c0390b12400301c54640c180d8101140c4d051145100c40c894503030241c010341c1107448a140c00c1c948e0031107404011200680c01d000a2880355203030036064400c1c2c40000000200c000c00070603081119905445401e0050f4a850303003420000e040000c00149100c400d290f20b600842c100c14007111948540d40c4080e1003141032a001250705540408d0711406810740d03803010088041215135501c00000c044613500c565075091054017020354080e901c2059050340050584d60480071811442040386e001c00407447c005207000c800c00003400b40c01d2040714181d03000c0728610213a000348a040540d0320f20820421504000021010460310f4450f096140038150307001065850900e00307100024103695010b1400200c0e2828600403a0050a051064a000345010740c040d143e4900341040c460190740380048 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 259332661 1250 259331411 259331431
    0x605151b0c0907090e061203090112020415050405120115060e041508010902030f010e060604020702030a0c1710060509010302090c19020c12030a210902030a06141f0e 73
    0x54481d07020340d10786903483d100301d15903184c0419407820a401503800303030301c02041c56010b1410360aa49500900020a440c1000e209290108001d80601c5c0c5c000042d0180ea0301c00c0c2c10301c5048414549076260003a001d882510300c00c0c0c81d1240c040c146030b013886081c1c504100c104100c40301582ca0500c14244a1841683c44c0d440182c03010900c101c48100049a0714441d611444259540d0900c080031481e06204441000c1746030802840041144444680c0320700c0081c00380e920580d40010700104545060020002d0303603800c8140744110594917040180f012079001941c0c01540a80900103000080500c507103400d0b40c40241900d400b981c2181d090043c04140940a114247e90034881c540c0081004100e00010540580c01f80210250b241c00380300c0c000c40112056001c0da041413203442c0e06984d20a000b131113100e146498056049000e8401c0c0401010030b010081e405018040000302400665044070a07445203002044504d980e03000404480c519040c045100080c0f1941000c0003c1d0904003889a0050300c142 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 259333911 1250 259332661 259332673
    0x30102090901030c170607021b1507030215060411180414010b070203060106030e100902131118030303130f0336081204030b090a060e0601090605151b 66
    0x120020701540c9003680104c403c072868034028004c04c49040310840d2102d8106000703045070305001c40040d4645800c5482d0201d140c0154000d10066601c0b50700d80a612030203403807416564403071403e0080d12034180035400801c42d40108003040750740c1481c4c440e885c45541401d101c2d03410302202c0c45480c1c1c144061000741c83c0d4400d807100701002440c2d20020500d802041002040f075900c125a02c180350501d8016444041410320342f00055500c000302003040e0610b09105000041c4005040c80003660f061035480d84102014034140d1002c0c085080d584c01080040c804124415030000d4400070150f43c0c0c07008540c0c10748200200c840c0c8030001501c04012201c1e86110b41070a18414650300d04102e0443c00200c902d070301680a8a40041984000b0718034900a002500e02a00a18a800402601520442c40010a2502c86e40c000036040e02040c00503003142684860180622070351007080598829007800340c81035035444d05138005810328011106103092458812610b04180c0e034000c0075010490255400b42c0d10307001c1c0c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 259335161 1250 259333911 259333927
    0xf11091c060905030a110c030105011d0709080d0309020102010b0d050d05130302090f0a0b01030615050a02070506070c0302090f01030c0b0a0509040f1b090e1f0305010e0601030b250806030102 84
    0x1348081e1000c5041030f1307180034803403483e00802803410302108800350190745402d006220844290640408a061242003040b558407581d070103c1c1c41640b01e0380444201d000b21103400d442268180c11030807115000764002c1c8106c21100c010080151362f80701c002000d6610048200c007040f8042c002404101140c144003040c2c00340d407a0007080d6840422203005003150484020400d4003102403203082d485040a00e41040000d0421950700010000701d10246e007488008a0001049803081104d8000f80c10f001c4c020644a452610300a09020702c40d0004910400040000498591034250344604803034015014441c071030715256808030745520480018007082401c0181c605c0e66201c50080319403400300001c00090300a000002d0070020245108110100700146400b080400d20100c60a50419207210361001c40e100d500b03801d01c48000d401e5000030203650a00c00014840c0c00c0102c1c0040c100e900a0f8841c9170035544102c0080c0c1022a061f8030803003441441d008800c4031521804666074407010190005181002d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 259336411 1250 259335161 259335163
    0x5040b34030c0c0804090914030c0604110a0807150201050702030f030604020d02042111040c080c0d0612050f0615060a080c040b040b090a050d0503040306051e09010f11091c060905 79
    0x86074006e810a035844001c22010084618443c4401c028074001540c103082d0341d43c54a0340c403804040c001400016581c0040c22030b40e510070a10100410150088a0328503541e03061001401b4903c241c004007652910300042c24250005c422101c04030034410890b07155986000812000750019031480301c0682d428040452100000c10000382094a1400c01c86005e0045203082e070001c034025408203001c0c50400d4007424a0641241c41650002da003042001d4031112091206030080119603c10504400340c01da00d10207003c0c1c0483c0c0d42d8211100e0ac42a50802e9881400400106680e003c034580c001c0400c001c00640107114030201c1d078005001c641d1892070f01b551100078086d03940080e00843d00d014000a01d40382603107010840e0384001d01058400081308584c5880d0307940c03607010b13a01c8041d240c181c4500c00030301c1d07200c0004c2c460640e481800721240c24030b0400d0a03040d8001c0410280c580c0300d41c0e00e170003224208110480306413010007000401e4010b0f08040d8104290750810201011603059450b08458070000780 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 259337661 1250 259336411 259336417
    0x3360b0714280905060403020409060207240b0f0d0f03021f0609050618060d03032004061106061f020f030a0e09010b0408060a020f0c0105040b34030c0c08 68
    0x40340380d4880800300b58031070740c042c85000c815072002c0c01c0c00480441006140c560100f6102142d40441c0c0004a0003114144400607200f0704200808420000c1c40b01301407048800015400005103580402c04441c1c00b009105000c030541104580c441c428050010002f010b154108000780e1003441a00c000544150000c3ca00a10b4003d503041c549032600010300940907207125044c0d0000040710a1402d8203034610300e0302c0040c3c0d005040e0900841903203080c00705250080c0c06c60092440303001031149402480d040020115045409507400080c1522075010302c5407000100d660062200501411209996020354490021603a2564007540650004d0341007008082c400340001c0c0b82151500d48000c1490400c00180f004160001420003405200070b200400c000511543d1005074100b005940d5040c190b8122034038029915030250960800d000c00082101d2624054010031005c4003400c0302c50720103d20241042d008030446020070500000e01c0b50030034071903000f808140c9038909250b00f08450f0f075200d0102e154 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 259338911 1250 259337661 259337677
    0x6060906130c020d030e06060d020105091c03050715020a0e24040e10060801080d050a0c020d050a140c091501051606150b0703052d040603360b0714 65
    0x41c00000440304020b815005580c0950002c40240003d80f0304000027402038140d00f500641048000f146040068803000c901580321a540301c020910398025250003020b55102600840e000e0296000506030302d4083d00031b86062401030780f2001100c42154003400b181c110010103a901da80f5212544010441e80180108081e05000008040c1440d00c0101c000720710007a42d100b101080b41010041106920209110b51510001c0c82d00c6595039071941421980301c4400d4802a60007801070940404000d400a607101c00e041c800c0c002015501090250141c41c2e55000145c1900a905000092012110a8543e01c03944805041c903604100c0100d05e56042c0f85910401181c0e0b040d9900c00c40c4600c0d903000d0300182c1c014002c000d0180e20b00111039900401c0c90265070080301e242201e080c0064030226400816164041c040d104140e02d481c0d8031074004024008850000c0102407004a40d01e02c04210500f601d5811031703011203010355041403640ea201c01c0302c0e0000c001c20100a00341e60b040b01000d050f81c0c01410740d5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 259340161 1250 259338911 259338913
    0x40902070b060a0302130f2009090702031804110717031f03020a03080319020f04051306080307032a0309150f1e02030910180e0906060906130c02 64
    0x4440d01d1400e88000745015052500ca4003070340b4020030040c1d9600c000c03401c00e203052410115000c0c80c001e950342c01030080060800d40c440420390310007820384818000341240c071070100c615580c1626034032000e907101c2c82610418a100c1110001c1f000c51418140c00090f4a55900c060341480c014003500c3e800c1104219503103281c03c50400105121405203425900c201012003504d100400750300c0e560000340406034902c0010402c52002c00014a0031405021143d29585000700c15582d40240c0c10131030000d03910074040d403446402010268086164a84104010f803402e00b4025850722060352020b6600103800281c100b007001a9402d640e06507005400769184140c400d840b50100d041c00c1440341510140c800c580d4004200702d20850009003944581e8100d815240c2d104010030090301d00c0012411407040120351038115085180d68030485038040106548140013a8450040544480424000b04000d45002505510a82c0031401314a0800043c64000000a0408000c1c1900a0006064801100102e005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 259341411 1250 259340161 259340167
    0xc1e03010e18060c0d0902041e02030a15050f06090a12081902060f1b0f0309071a0a080703020d06080d0908010515031b01110f030a09150e090901020d02040902 70
    0x5442440702c42c4401581040e010341081e2424011890342405040403c4003440d0f210541031055403201d6000400d407020461705040e81c403801010709000703980240e03000c8034001d10700990048200c0e0400400c00c250307100248050744102c0080208102500165441503102800d1040052003030880e40d030040409205542132500c0d40481c05003280702e28403000003c81590000c4003041a002509005c442c3d03c5140c045802c1400f41e40c404400003503000311510142d08400020521050341c10010b440b0084a06d07800051010011540b200c0c4c42c54003401c01d900d000308030800d003c03550715400f9401400d41110124400291190740d030011a1400e0b00500d64140440c1030518207000950f001e0141d944e01c41110080d180324414035102082d91019800313003d10243d0100b030207020340c680c030808110200060360002c480c10441c500e401280c90740d00030100c48010480401000940108441c0d550846120544400c01100d45030f10600046110080182d20390355820030800412083d02e2003d40041c1c5449000107817 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 259342661 1250 259341411 259341421
    0x30512031b03070221041d041e08040f1a0a051804020a0c0b06010e030a0602092e02070f06080f100e070207050118080c010f020106050409110907090e0c1e03010e 71
    0x4c940c0120781c0c1218130805e0400051201e604c000d1594801c0110440f0207a0555403203040c841c6481101400c0ba1410b01100c0c0b051009004840f03010788240ca501c00c41072401603540304038601c001000d0124890301003a0034481c2c000c096000300051b200d44000402e49184101d1780c2c00010f01260f000411003130104000460240c00d0280c04881c17942d1000e000e00342441209010000240d9909c1030300002004241c00081c002e00076124003205c0d002c05ca803110002480c1d040003d08009010a601d903090b00148502c0a00103502c400751001003040b02c510380c6492100c1c0d101d201101201e030b5002400310403030b148281400103054001482141c41800664040d01c9c0c03440c10480010542003001d03c0386661002c0001e03040c46010b07030218a100e2000300900b840c9510200300441640948581c2d4411039100e4641000c82041c410b00e013107840400d250858468505a442c2d80c010395402c0d03180e0080c03601004820300011500c4101c51700801600c030250103400c0074105100320f821041d41c4260000d80b03915a210302800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 259343911 1250 259342661 259342693
    0x1e0303090b060f010909090f0f0605011a07030507030e06091011010b0a080d0309151401170105070f140403170a260a050a060e0f040302060a06030512031b030702 71
    0x242c0c220b0070450f00710075840840c8000900c00341e8140513503940030b07944080c82c108201c020170184008a9002c901d040e0707210442d041050060100f48182920515034400451003104110100c500c040c4c0d03da143e60b81004459101114042c003080543c0360403417400c000003502e0355111149215043e4040c0e40c0e200303402c0300125001e801c2d22402c40000b07026191002c0c091084100104813042031650030300c0c00092558060400c80740390768109101181052901a8800061203072080e0316060350424041507000222aa8455088031011605070001800380841d080840d48183e880190368124510120705041d125150380e5041c15803600c030003031411000a401b0485d190405900c83c0c00c0072034900d4000d080407400d584103100442c001c1c0312440c1e955550001400001c40c80e1b001d030024100c4a000b090350f900d0042c00c4014000302c20340301503015104d01000540c0700c041e035001d04020f0381d1b445005005007a03a882040985500043e290028450008150020b8002d540700650302c00c0103940c1c01003c2c080c1d00d100c214 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 259345161 1250 259343911 259343933
    0x3020607200102030c060109020903120d06090507050f03070309030e03030a0207050a1221020111040b09131e020313021f140f03010501180509010b040807090c0e09041e030309 77
    0x11410f64009004080d82241d0100300d51b411100503143c0580d45950241c0043c0c103010a45040da1ba4a400c00300e54010f80d6040307a0300ca00c040d14010042003042d6200c140c0706650b1406aa00200c82c844400c10018170280d205c2c0c0c000ba14402d1107828800464442c020010781180c1115a1420050f8072140f400c2002c1e01c0d0030300300680202081c946030000304002d5180d42d540f072050120741c020185e95460f21010041e100350b10410722040c612402d180c503a600c81450b0ba01c5940144001881480320844000003c0013910500305495400d4401b64029841030080740702942000300301088985c0c0d2840c02034050303155025403004d80340f40c0200c11140c0720200c0c00044c00c00c07001100135114000080c445401101d410504990550b6000d09100214000304080b44600c6140d07a0002600a01c240c00002005400300c0c01901c255140301041d5544203403140d401c08121a8184101c0000a002c06250364540c1030400f29980c000340581c1004015401e5607010300c080010100c0100c0020380e4a000c10000d0120075229 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 259346411 1250 259345161 259345223
    0x4080102070c09050601021c020307020301090b0603210a0f03061502060106020d020706090501110109060e010c09050609090c1c140415051605031806010315050106020613060b010903020607 83
    0x4104414107004000230342d201c07604007950111307000d50f0b16442117030f900800c10b075a00540c3c000c0c0244080011407a18510880b004e0710390358024484e00d15880e036800e100104c1c0501c44801059954200050b40703408445502c103000c520002c1c95030f601408110400034458031141c2080e650020200b551600e60001d00e444075003811b03101150441c2d0800c0c0102640600c0210448100746090305030043c0780419640144401280104524540745030080941c10641013220012000e84880318031582d41d80511009104542c960b541c0500c011000894071000784024001c0d4121300c0c1c2c082159191000400d41c1103d4003010140e440e150750304100400c0010228200c0c560300540c0c00144006d007804c170306100d00d402c454400001809000720006102e00d41410800780c4a0780b60308101d9900c0e5959051135510b10134402d024190840c100b10002c43c4107400040d42c640142c80d54400181500ca80382c41d92002003404070000390401c0100300b00000035949082c041c00703001d8016603001000c0120b6244100e42062400c0c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 259347661 1250 259346411 259346429
    0x4031a070f0c080702010815061821100e0111030108010902040b0f010503060111010b030d0c0c090e03030a09020307030c140f0306150904110904050604030f030603080a050a02070b04080102070c 85
    0x9140b400091021065810180d428200007241c0d4446214103008055100e244580120700851000a0711500d020f9802d03140005865400e01c04101c01c50a82a41d8240180161903031310105884042e000141e10080805412100001e21038044490000840d07100703030301c07499043e9100c1060314190300c1c1610400583e402c08032002804101c080c0300203403c0d1f000c000d08842c11b00080d4091083d14540079002042ca90900405540a00c1d010510280a100740d4400540300030140810224001c2d0345071081981c4008290300450555840d00d040c4070117000c0010089070180140b410020010b01d5820390302d005880c12050144050040c0300074000c2c2c09545800c4584039502c00002e008050000b0400c1282c0301d103050b62003245a603035900305064154003001113503402281c0d8a04200a0000200c1c940d80903601c00e42c0c0729074250244d1141141074504501001c0d00101c010401400107501610041c42c1c42e1075140107589946a441103400310740e0b00a58044105a500021b001d4100446580e4160191000003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 259348911 1250 259347661 259347677
    0x6080a090b0f0411060316080a02071e0602040803040b030103050d020606060306191809030801060305040c05101b150f140a15080d020d110a0317070504031a070f 71
    0x7845041e62980050460403600040c40041804d012550505041c038040141900d903880c01d1604041c05c00950104042001880050200781000b416001300c5143c9500700e0700004400d0018030010180d4940b0000807508140e08110000c0c0000c01803000d84010310b00d074042280c52b9031450600905110700c001c2d400046401103020801181c0e034038801c1c0c0b60408801d441c6003070301080034044007070380e1450b80e0008114080c41c582040c1542030382d07411402103030780b00e40d4404400385d0342e460040d000e4072000d5a000300050b0f030612042c4542d00708003100041200c0c1500c1d080303241c10036004001d15050990007003a90302e160140621845100b1a0181800c0f03050201820070090200d4461110500c40c01b4044484940d166040060400401c0740101b01034440007040d0b8042000012001c2c0da00c16405240d203003c0384440c00100424400800c80d8090540c15031144840441c800d0040c0a08200c01403a40041c003000f0301000c80850000c0400d04500307000300c4008500c506200fa0094062000003511074100036200d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 259350161 1250 259348911 259348913
    0x11508070c030f080705070c080303150904030801030b04031b0b1b0405090a0207050c061209011d0307030e0a0b0c060f060a03020312090402040b07081918120807020a0f06080a09 78
    0x103940220f5103e07452801c80c410361a001da0454035441007583c05440c0c4102600082103140c404001940200c140d020b00f0030302c140c01079050000c1d28074100c500ad408240c3e05030040000c02c0070071000c150b001d4820320b06001c0ba0306017401404e10036240c0100950310300451400704a5400b00da060400b00081c2c1d10001c4070308251a240024a0b8140300a03c0141c0c1c40c0d401041110400c41c0403c00458030850080c01280c483c2040303d6a030400c0c030340032a6502625803d001501c0c40f20698003020110030071892010b14502041c40c0c4040e82d0f508462126a07800580090001842031501c1d00980505408540600541e00301001990b01c10782c40030341f0445c0700d03803504402040140d41c00102200d1082200d01005c1e200c0d05028000740c000e018550010060420001e18101085040d80042008104c8081400400c04142800722220032202c11000c0100800300c2080c4012400c3c1b00100c140b40e1f20520310a8500041a8080360800526520910f40361030a00e02c180000d0b604144a2a402000407008104049003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 259351411 1250 259350161 259350167
    0x90f060601081311190e0a060b0301180905070e0106050a0206090c0d150b03010204181404150209030a1505090d020a05070b0928090b011e080903070b011508070c03 72
    0x345000200150f03580700304e2060329155640400c51700114010f15894840e55646035501111046680c02501403415a02007004800c50058a0680d4100c02e40c920070784104982ca1030041120300809d0390343d88910040007030080722880d07240380a041039554040e00c60b0300d201006840e01401406814040d00548124000c503100c55134542106900801e1820540500d14560402404100d08141c1c04d9400000c0126845407821a48000c410f6400e0b420000e45410464050318481c05440007080058080349401c8003000c0c0385c001d0300c1c0c1c4030001010340ba90308000743c0d5408500201d04a03e001e440384c48404000c0e202130240044d841480361400a40041c0d489a500c1940340c03c128014888042c101049000e50382c2c40c0c0e03d41c003400c01070388010340c010404015014000b250860f4407481c801c0c0317414004400a5035105002c10581c03002c099242d070b8a11491031a0075a00703014000c10740c0740d142c4414042031001c00e0000c1e1a460090864161050401d8a0b5220081407408001c1c8601c0511865140d902c0010398 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 259352517 1106 259351411 259351441
    0x1104090825110d3012050702060712060503250b0309030f070309052806020102091c020102032517030f06010305040c0801020c01060e07030b0612041a090f06060108 72
    0xd0001405c0e000c0e50300458001c4016081640030803c0039009200e40101011080808034030151600c0c0841d15103000c42d04110150054007860780c065449640078840078002e0020700910f10302e00103103a40d07500e21a00044400a10000981e1810716100c0c22049010784401419000c889c03000c1c2c03912055041c2040c00c1030185031944a0b00150782070052080310070f8000c0161035502c198007101d820b14184400090268190b0004214070032052820b440140e8203842802c018951b0400141800c20000e16081580f100005080082c030160700c00007080b440c1e0100091070b011400e9070751441d080106405030703403001940f91700104920303d040006420110589d160810010580c3c2c3d80d0840072015940c1142d4044e0300300700300f04411107402490729207142d40240502e800c03515000845c0000702c0304a504541340d41050b0441c000c04103415809111541e04400246081c031041c0c1820f8050b856424 = true := by decide +kernel

theorem cover : BRFrame.Cov 259172661 259352517 := by
  have h0 := BRFrame.cov_init 259172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 259172661 ≤ n) (h2 : n < 259352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
