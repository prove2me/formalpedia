-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4502
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:49:58.486137+00:00
-- url     : https://prove2.me/submissions/5b7e3191-3585-4337-a123-77d903f42044

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 809532374 ≤ n < 809712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 809533624 1250 809532374 809532379
    0x304150201020c0f12121b0a020f1c0c02010804060f050c04080d17060603060d0b07021e0705061903060b07060522052d07030309170f0d11010207060c050405 69
    0x1c0e0500c045060f000560764030441422501c5c2e801c1103442c694100903030b00010201180794400c400c0c07442c003561491000b0001450303542d0251107041c0030322203510318000141d228482c0e9a844d01c40381c0642c80360700c1104c00d0700c150f0b824604007200d62240c0c20400c0141c902c1621203045039203070070b0038000b007908080001d000b2242d1840c10307036042041d49a404d41d40d10340b00d018100f000d42080e00c000703407140c5802d5000716030004000300174002910310b5854032050038500b119910090b03800300d800541d0701079203500c2015200e1891030050400900b0140883c004e4000e800300e6040902d810165010350300d000c1c1c0c0181c00074000c3c580f2456283c0c616810b102000e01f8055441603e0f1450b1400f400300f420840300904200c580e0400001c01c10302c100301e44810710030b5800100700c603146000c5008800c440c001c103000040046003c1d60300d100d209070400b004d1003004501601d0510860313200c0a0f0f1803402900c00305078144070860b103041107243c0070b10540c0c450380617110f4000000e2101d03150102c500019030b00f200250098a005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 809534874 1250 809533624 809533633
    0x203060f0417030f0105010e0d200316030807030e0315040503031e090703140c0402040839010c02150d05070305060102010e03070602280e01021603030c140304150201020c 75
    0xda05180b103038442507400c0000480e900006004c01e5015003010100c2e030030003a00840103081c071a1640120345000e094824120780d1541a00c410502d820814084100450003514420b42d2642c3e40720742c40d82c030a04030300505010908503070031001e0b502403042c2a240b03e40790141241c41e2800d4035005480c0c1e030044512540440c841408002c0f400004800310b88204480e0004040c9a8150f40701d10040f248201da41074105c0c81101740161003600c0c3e0b0b0010307000410444c2d00914590301c1c2c062050803100e506107104203003042c0040e045038001071500740e03484580c3c0080c20401c010343d40e9800030400d441e60940710280c80c403000003541074511006501040c880c0b44642e800b004192546001242610406c00940c0d02c1a4014000c2c0400306e17115500510a891741490314000d40f43c204820b904140d00380d1829030020810f0181c1d59502541c043c00300700b0b803e03180f42e014145240e00310b5070068082c2c03104c504041c0503101c14008103000c01c00c2c00c00444005c3e0100c0603841807842120040207002c0d500c545000040c0c1c0c0103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 809536124 1250 809534874 809534903
    0x20a060806011d030303060918030f090a050121020a050d09080702040b01090f03030e0a03120c05011413060c11010e011a18010b18040507050a030e070e18010204030203060f04 77
    0x4207810b4040c5480200174600e0f50310f07800c0030000121400f030640d01d00c050700b610022101203002c00c002c107070040040c4030154076103054504000e07902e009075201c0350601500da04400c04001c0410b0404680181c21030005031160405502200c3d14010788141400b040d2420500205000c1010041d2454500c00c440034031600074001c0044520380300a200b10a1038442e071702811b00002c1d0195019258505001d0514000c5569070745603141c0340209c00110002041c601741000060000a005612502c41c813800e40a003142040141c0d190f110346100c5002e44113030341d100360510312244111040601500d4a4009100708034051050b1402090642d80c0c0c100d1840e12164403100c10304061000e04150042c000103c07d50b0b80c680003a4010356401041114100d1007011668900d6580f107108143c00340c0010f9640da030711803410100190407540d5400c4c0004040d801a6030820480754075180141c0d001c004909001785184800c0034041c0640600d03040203500d80116020454000c1d02642d0142c420303406611034089216 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 809537374 1250 809536124 809536157
    0x30f090a020f011d0604090606080106231c0f051e1003110d0c03081905070c03080904021b030d0c0903120e011e0815040b03061f03020a06080601 64
    0xd50414001d40091410041c40e03010741c05205940300b14442500b035144407525010020700a680660415280da0346c0d100c806000190748040194003418580c03c040c298007800f0b9143c03034032030f030340051b00c013500701500182103d000812034002c0f03003603000c08490078402c0e080c1c5c2252480142c4404c031541640319500d02c51070706440d041c1244280c054800e00e10f00120041c2561110702c1c1220760744401c183c1040300391844400060901d2070000c0114043e10b03455880380c045080207042400510a03400400800b03000000104400140b003204495001a00380d030745100742c0340407038040e00038a8040c0b844403440405558601d04040000c003103e551a000030000072a1460068660281c42c2c08090007644000004c204e90303a0195081035510307401410000e0040c00c030341400d070800188c0300c8030410028480f45d081c41a80c2d80081c07030399142400d084800384000c80082c004aa6102002801d4800002d480c00c400321541003543e000c10060b5802520300c5070055281c010103000f10006584141c006a41d1126005190307 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 809538624 1250 809537374 809537383
    0xc0201051b0d0b061909090b060f1206190f0905070908150c090603011410050c1002031302040203070503011701020304030903030e0307080d0c06060801020c0c1011010908030f09 78
    0x100c1d007501406040030814120480200340d804509504894200200a5818108070701400049900d0313a03481502401c00322514165002d8408043c011f007006d0028182d100003817000e07521060940021060942c0d900380c0001c2000c140704002a038100309160021520a00420b5030200f9035510a6044c010b43c2ca46010464240e0524421480590461903511100400c4030039040e4201901c01200c41c1415018400500750794801c0c0e0000601000559595149080900446e0080a01810300354100700480c0709441d11780000000076a03c050380040020f00200c140e2081c40410307900508219224a0081c2015240c2c0c4d201303004d5154400844405034100e004140220392040f5816510307020710ba0314540d010b42e6800d002100e802c1d41401281004181101c04100e4640c070b44140350756805c030003441e608100c070894032541c0000180764010000c035107101c0800070300303600c96150640d00b6070303020b18019904441c1e00760302c42c00c03043c1303a5404e1000910603c410135001d54000c68036250502c0954481c0c3c0326032542c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 809539874 1250 809538624 809538661
    0x1f030e0a050a02060d02091507060c0f0816090812090306090118031422050f01020c0d030c140f0307030e03060403090501030b0a0e0a050702010e150a09060b0405040302010c020105 79
    0x7941d020b01480c10060800901800f5007496160740541820b51040c0040e1290301c140841c10a00c902c0852840c00f404014024006032501c0c6050035500341841940050035002c0082a00041c1c80710001c58440c45e0348205411001003030910151140380c1c01c00d00c1c2020240e0300400d400740c400c1c441d01011503c000302c1845401e0f04004145402c80586005339030a4800d0481d040800340c20b0700c41440f185100101d0321462a0401c20014050001141480e0421004043d41b03c1440c0c115031100002e81050344620170500d040a8140c200715140e12039500e400c000018001c03080300000d0140c0d00e03c60340b84600c0040900600c1e482600d03940a2030900e6410700d907495008135006800121807800030003e030b5001e544200050440a403030341d1030312610b8550300c0301c01a800351101d07894aa0f4450800958581c2846200c400b81c0c030440280100c08500002100c2c42e400c05002d201085a82e5104101040300c1d035032000d824950081e005210500d41400d001c0e009280340507101c0095420301002039414040b04d20202071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 809541124 1250 809539874 809539883
    0x91807020106150807181d04030201200706050603010915050603062d0c040b131d071e02010f0501061e0e150f070c030b0a0f05010b070f060b1f030e0a 66
    0x41d40c80810485070b100c02c80e0710138102e00c41b8850001c0b940350b40c240110250030841006043d91420640fa009086a0456035a00304620982c0c1000742c40098030002c40c0c0c00ca9030040c00102daa510760f0000a401000700f0040240040d05441b1000b4a0a100390805481b03200114186e65680d41da140f82d1038200c001c01142800e40c4e46081100b0407102a40040e00e42c0c00030060f40032107003000d4551241d0900ca9102c1c0040121807001c22900700003070444c04105019581c032501742141030742001c440180c04a030b1080180007004100e100ea003001c00780700b54403030051048111b0060109582d240b1002d40011584841050302418440404c064603028150055010b8009025041c500d810b80c1e29203c45500009040104c8120800181003c550081404030145019a480c0c034041c0c1054100c00c3c080b291201d0700340040500f0a00100902030200050300c01c0d10b03401581e020385029542c5400c000400701c030b800030b550041c4804e500e1000044d0050f107a05000c0b20640301040701001d42a44660b90b400c075080b0040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 809542374 1250 809541124 809541137
    0x31107022101021305150c0d0c08091c060f090b0c07030c080d0204050109090c0c11031507021605010806100f050d0603032316021509180702010615 65
    0x10010305064070608000c06854800791480c04071010240d003640c0c000344940c26446901401401585003540d50481d071428030b140080d240103031030b400301c503200c2810703020100a04c2031303c5100d00c050001010484842c0c1c140108084005090048402280c0701074001c252402e82c908042908074200d54490842c00f40e8005130355140c2c0e036079802109c080310741c8110002c804111482c1e0300c400000d4914400341031440f000e200c0150315541080c00041001c0900e03072080507800e05025054200c1e03034000c94241c0c0140d400828241e105049503002c6440c102d2021122003c0040d404200b082c0e9590224038012000b01c1c0c1505c414401c1ea50705d00440d107003201a1180780c2c5c440e5811031180309050140f604880130900e00d0502c03604120314803401c10101c81c80b41d4001d401059641d008030000c048000d51007402c01c5d900c040c0c1a030a10341003481c8020b0700400198003c0c02002d404462900e5118000b0035036440c1000200007516200d111003440c4080c0340c0c00c2c3d544002541c02c0890200d9041d100c1c2540000541096031041c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 809543624 1250 809542374 809542387
    0x31a0609040b03010e06150607080f160510052d0a020c0106080f0616051204030c03120f1a0609030316020d14011b03050907030204050c21160311 64
    0x80019400101510740c016502c02106000c3d4900780a0501c941c60418058450761806100c01c041c003158003522688669010090a0000f8215401741c070b1800d0101200d45444440109003540014400a40980284a00421a108004690030032413054107440a02010000c034270302d940300c4101c0d50307000303d840e04500c1100166040340694050700030380e20924004a18944d0f1407503180d05203d84580001c030303190005010070002a50070606421614403e2034840c0c60300c1070541600c0e040c160090801130420655051500500d0302c5520200c020b01c41181c030030407070490500c1c1460020030801d000c000c0607010a240d002c2003440c0c85801d451000c403000d00914a0900201911b203020090040200c0e84040f801200201082600810340f0b0b104500b68000568407401e80a80780821503114034ce40d0405040c030302003281410020803020212541541d002c00d090711017200c001024014007034000c06280c5030400840c04080e00c010000d005d1000c140d0401c80d0401509000c5056808944144040d002e042028 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 809544874 1250 809543624 809543629
    0xf040e0d020120070318050604060807140a14031008060a0204030611070f1e08070f030e0a0510141b07030c06022b0509120322081e030d0c0f0807031a 66
    0x50340d103040071020008601b03612540020150b400541014001031100c0c0c042080c00d0ba04401c1c803513119000400c0d00390130310510311750003000c0700b003405241205a800400030401c024007030360400d005840b101040c0c401600d010383c070300c40c0290850305c820f580e61820406008510704810f81104c107456008040c220038106191119500c9088149681c00c07441103565448002c246031f400500502c40c4181c5c11401c5d09285810300410698817800302c0e6100d6600340800f08001e075220000514103e0441c1040d111454020f054850340d801403007c40c03d104d001c110012800044003088200039240300c2e4080070304098903441c00f2a40d40c12030340300000210a0001d4000b5040713604064881c0c10b1030182c5400341c03408007140c000c282045590b0b61110583d90001c52510804016a5a00340b81505280c6041400c0303403030903400d00c0d901c0d24140c0c00b0f444100104d503160a4041d400b8002c541d60f00090b40400d110390300c40b107400105150060b000106c0040c40c040d0210394540e20a0040e41240b00803403110300d044505c1d4008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 809546124 1250 809544874 809544887
    0xd090605031009051329150310050c0706060329090a23160306061719020409050a0f050709020301180e0106091d070b0a0801140f040e0d0201200703 65
    0x400c80c01a2030303d4421400180320012a2407502e41e00401a074001d00911650501408007c0e0249003030f209030301d105c01026200000c5458042d951500f010842e0784441a00603154812000b01030b00701d90078a003000c02405002d0744541500900641c015000c090b0060611008880580e104103ca4100095200c081140200084400b0305165030103401107140700005880c0c010040e0001520304400d0608105100035442004c009244006505d02220b41040100c1e03150011817840070f03600383c030301e030104402e6403141d51020521030350100841d04004ac40742010030701070a21050441e0b01e4403030503001213600c40541c000c3d03e04941a10054100840000305503101800c0c4e0340200c00e440e990b0701d280c0029142028010070700781d5a100340c1d1400810041e072040e14144000f50b0403035000410204010460356074004055030454803151505d6007800120340000b07030024040011281e0007070804425250390b8501090454002c41250000c11802050402c4415540c03940400544080e10510003100400d02400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 809547374 1250 809546124 809546131
    0x305090402040e0f160905010e120c0909030d0612020603010e151c110a0b0405122407201c0311070813140d02130b0a06020d09060503100905 62
    0x1400503040907240c0c00d030070044a408075007080082903004144000c1881d178040303418036002140303800f042c0340d41440006440e0720558400030b401214100078650407081705100509480000524240d824100340702e02e903a403508020200004580b07000c40010300740909101114140358040c0926003968a041803510b41d444000f0301d00b8081c19541101750a0320754400050122040c0c100702000851a45428805410007503440f00d01c3c004c00705228180000024074080d5000c036601290456031851320081c5007820040d0030b0f96080c031101c02081c0d440a07e0202000714034400d141c41c3e42c44014410b000b400d09100c1c90b02c9907004041c103401c6414200741c00f5420384440c08031090039081c0492088150b241c0111554400401914100c0c00807459001907c0b0504600004159400000c61540708260015200c0343d110400248900d801c2c1d00e01e0342c507025160f00110120f007001041c280c08540d8600e0041d446009500003c800581c0c007520106100e4003c0302034034001d041c6400151080c1e410046507000420b00070303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 809548624 1250 809547374 809547379
    0x70b09040b0901320d02120f0a030504140d2109170102070308070c120c0c0513060f05030a0f12090f0303090e010617130606051003022113030509 64
    0x1d07000200300b40c80d081c0340c40c0e000b801991010011880640d00d86400c0354004101c2e14041d48007014003400654440300c00964143c0c0458040240c4420240c249103058a101d8034128507014910301e50090540101c0504101c486070360720f2281c100b14070410449950b000c480c0041444c0044c1c0c030040c408a0b01c6c46440100001a800c1c060b50031610380f400c14503130451013483c981c2941c0d0000303000c0302019401280c09400c4041400c00224440d40c565640102003001c51501c020130456150300e0050103e0840000d0013428098214411520072604a402500042c00f8071034002510601c002014240090300c403ca040d00035458403228070866507000c030414104c42807801084030240010940c6e00d13000390944000d600c20303110300300f9842c07800a04946280d0160302000c14050011103c0005c80c40825601d640044c0604a503c45030200d0302d1300030002c21454004030740204000300004c81d029019802002c150b90503140e0888a19041020b0000b400f1040700c8030070100490b44003000009008002500ba0705400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 809549874 1250 809548624 809548631
    0x50a0602060a1a040e0a0618020901030f03020705060d0b04110f0f160210090806010f05011403060307030816020108181c030221070e0904030e060a030b040207060501030b1602070b0904 81
    0x507a030021302905c0e40d03204d4044c0b958000b200820308015407449641c000b2260015141d5601c100c43c0c0009003100b105100180001d002c01040100b050f100740710000207010014402d64035001c1c1d0000d10303001055003003031240c0100c0c5040c841c1103002480c1c405803004402210801441d2200241480040b81c01000c0d24407000e041d41080b010050b0307036601c102c0303125105a0303941c2c020151400600c01c3c5046e20692019540070240403042c840350340d02c9107600750380145081c0055500d403598000320303103480c0c40c90303101034036004000c280b1548047c0031042007000c0034000d03a503040030b540324600c902000510b554080040d03584805187c4100302007031134080003c0001e0742001402c01d0a2840c4000c0c507082c0c33540c02c5009141e4400f003004440380c2c0141744081c01e10415120a4602d1409a801402840100030708501c239000c0400c01c0d480141c031a0700101c0d41c648000c0c009549034010307850581c02501c0c0030b000480c0c00905960000b40c600d18268504000650b0030b50003070030010700d40306d8004550350003c2d4030390750070036113 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 809551124 1250 809549874 809549921
    0x306151b020303030c0c0616020312130203100204060906110a03260f0a06090504020109030b0c16051b06070506061306090218040b04090203120a02010e06100906050a0602060a 77
    0xb000d1001d18440c0394541111903507498282c100d6414008010500b05100310b0406222801c941d000040e00c800b1800c0c0707840010181c031100090440324000c0b0200a505104d071881c0030441100d05d80242c0201d071100e0300d8100049498071410b64461003494500d010550082614801192082051000d0008080c40301c1c00510000c001001985004a81c048034035100d0605101c401100c52190500600184c4400c1041d800c15500003040f01c00c46210191080c5450000701d07940c0c00b150030840d9560440800c0c0c000c0c50040510b041c1d5100c003401e480140b41c4000200c50f003d802d003060070444103440e41c0b20000d0846ca58669042004441c070076404503500560341c1602245c03070146803009240000c43e03400505001a0f00508000560b0044001c42d40214109210580140c50005900a810170003115050301c4001401c0201e004140e840c50201c010320880060241003010000c1c0103058540c3da25041c418203031150240302042d6014450380f8016402440010541143c682c8003203e03519110030f0189042e107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 809552374 1250 809551124 809551129
    0x90d030e0d110a060c0b040204090321060314070513110d020a030902030106170c06070812010e0103050d03020415210c020721051f090b0f01030b070306151b02 70
    0x740000411590032450720403039407103854140e90100041100c3e25140188800c150764030f410903800504028051a204d07000201014002c0d003d50030b0803a90f501d0f002000481c09910000641171a100030748820316081889015024040b901e082503036030107082581825003c1d24580300404295500004060041c0009210f485190004100100c0c160ba03021800401c180101800c40300030354400410000456660001141c000c248101c0c3c117401110302540715001c0c4d0401d4412849510415910000180300208190789030f04800e5040e40e010f0390442c1e10b88843c504046d0200d2080303010300d000c1c1241713103000c140b2410301c40d104003440a440003180806107001c00c030480c4140d88041141c1000760300000014403e080442101d00e00042d84500302c1c0c050703078000c0d88a017600c030700400d801450001d0405881d514050040e030803032810305e0385c001c50034036203071500094002d0309000c213000488800c440e01c0040303000c4070f2003030041c002610f64500410b0a4400b0603030058407032100000003075a60010b0341c0754440259 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 809553624 1250 809552374 809552389
    0x52a030402010f0f112a01030524040603151b020c0105030a0509030c0a0506220b0a0b010c0506010303050711060a080c091801122303030106050322030c0c0515090d030e 74
    0x103081b980c0c0782080307403a9072541d0104403040401a04052624007000203c05a071182c10a07401080000e980b928205040843c1c0a4001604090140d80703501d11001e0b0802ca881e80700203680c60035422010500401c02c41d049840d419200ba10a0004109102080840c10140c0c0055040705003401124508502c03050704900384505410709551941041040021060810888001e004c886403007069071502603644544050030080c240700841076469500025903409804406401d981000840d0042c0d0b07564a40200385500c0000100c810704e1540030031100d141481c5040c0e898416450310742c1402550383c07070158035068110075010341c4d024100e000084660051011594080d1810303c40b000c180080c14105803148a50201405c080741c031300312031904880b0b01e010054905445091511603500c0e00e842940004007800d81002c024521528545030b01099000f01c04902d029205d150b010149665640801c1108455280c01e0b4200c014104024400c0d0310b410a03090031950b203c0c0c01c0c25038250501c00040740c4e44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 809554874 1250 809553624 809553643
    0x151112070804020f0f01080c0c0a08070b0a0605040b0f04091704030302060f01080303100e04050c04060b1308031828061808010c0f030e10052a030402010f0f11 70
    0x4281c0c0388080c0300c1903003080c00601c040b0748002d0300c69941d03203122000002c0c08081c00a0110009200100301005150010300005144c81c0d0800070041d107500c1182441491014161115103602c2c3ca48203001809040038001d1124030f010003090482d41c0c6140300107000c0608810142100d500b00d20700b00704039110041c0405400070f58003a0780148031b20710b003d001d0309c0c441c0e1006030030858241d4824800c0050158420f500309050756441801c080680e1070350b02c0c1052600800402c02940a42045c9005c03074145d030b98002414a00400340c0e29500507903550300c4a0341e141d108000303007800e00b41200c032217903841c134100311a200044280400506e48400b00c2c028400750045c1140d002800080d2402d45001e100c0c4031b00380c0303d040180c202d0200800c108402048040c1c03400b0b40011701308003415200c030401c0d10000011b00c441c80c0c20280c2e41c5030922040c9490784c801c0e4111002e402d004220300d00c401c130740d60420700400c5003528810780d410f8488841e00b2120101c02d4500403042031201d001c00c2000c1e40c0c4400d43c84418041c100703e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 809556124 1250 809554874 809554877
    0x1308030a02071e0206070f110306070314060f0f012102070f14060f150102033709080c0418051b01080603061003080f16050a11060715111207 62
    0x8a40c811450320500031600c03c0c40e0300c51180201c100507000350703603200105c501e840d034800782d856076411042c03400e84410715103007950603850f0041104100009405800c8444006560701c08420281e80b03000400040c1c00c121a111508107600b90741001665000d4038204450082c54038002040c1c0e000d030070a81c000ea034490202140c100030700d25242420440c3d085c4c8481019041c6801600742450800c4005d12961001001038070f0440240d801e00040742d0081c0b0031607440505440c1480010b40d40400c1d903c0e00d04448004280350f080100d90030b11240327885660902c0a4031801070162449800030401c00000e020003054541188104241401c0003440070480302454444450b0302828218003d4005404c244005000600903004030003002003150500c40a4002c1e6a480701d401612411b034044242058003070341c04003031140702480c04004144040000d048112034412515084103180080030300040b4002c2c400014211238502c3c0c1c948666118075085401e4a0f80700301d035807605055080746540d003c2034043e5813074030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 809557374 1250 809556124 809556127
    0x210a0b1509010318080d090609060203040b0402130c140901050918190c20030904090b06191203050c03070602042301020d0c1e0b011503050a0b0d0b1308030a02 70
    0x1115540c16000d10304c9041d02d4218289161111520303450024422208846c0c40155a600144108601c0c2d41c011070069802410841d102c0c9050302d0500c01c0800141e50a0b4810309240f00501c3d40180b260080010341c0c0026650014100020700300c101d034507041003159030b05122041c404030310300d40c54409841c1684000501c1109003030404400400c90f013078034084aa13104a003031010410300b0b16005401c1d402580c414600b2075403007036803082c025425800b41e1110701e5409400d010b102c0c4d0504c000038240174040d01d411a41c641000354008070b00c0f80701594034424603440280760a031110120b4080c90282044104541c20340b490450f480e80c591080364800d4120600ca40c404000e000c0761030410311101005070b5001c0c001049286590f031009007510850103030003001d4901a464400d692000051507203038031399204904100c0c4e5610f90b1840c0c80340c3c1e500c21448600107460400018400d07505401800308552010300100700b800b960313850300400140000c2c1074040780d154031800c04000031410780081d403142c1c51401006 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 809558624 1250 809557374 809557387
    0xc1109190501050f01140d2004170105070206040b1b0a03020c0d09030302060c09030307021003051f1a0c0c0312090f0603100b07031101020310150203210a0b15 70
    0xa904440c010f80040d4003ca0100202034030a907013002c101506005030543c015228404500b0722030240c100c1d881c00b000700604000d110002c1c000d00002510541d80c1030010f000329a9101045c0e14200c4d074003114504010b92000c4041400b041150a41c146c0010501141103101124500700d00080d40c81908400c0000f1f5001a2501e008641801240030414840c689504401e1540c0c030000d56600d409046601490f40c00203030708100303641c10000c481c100341d40904080100c050401001c0d00403c0110784035080014100380b46009002c40c07603103440030b40d0f20000e10078103010418204400560042022201144910050a61070f40e41c104090140301d2084e42c40c0d00e981302c01c614180212440704812050090405100740805030b540d00c40c070314090f54241d070400b40e100c9a00c2d00b82150841903206034842c107544004140301681e1965551101900c00f2030703203200300400c01031100301c0c1d40b4030403801820050b103580b00030350b2035507403095070f009030002082e001c0800d00700f02c1e00c1d0001d500e0f80010204982c41c4200054a0f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 809559874 1250 809558624 809558671
    0x20f030a0f0801050121020307051608030a06050a0305070e070e0301050f011509080a2901060323270c1002070806160f03020f071703071403070203040302010c1109 72
    0x145030242101b0b00e420711955512401080005c04042c0510130351940200001e0000c0e40f18400395503141402d00e0b00d0200d151128100754031580d00580f07060704914200600841c55040008080040301d91044c000c000192802c002e03284220301c040c00031020801c41d071510b40002d54090003000d0103030300446956840355160181d00040248184051000d0016204040001440c04601122450340240e41400d5042c4500f6650a21603e1044005c00d02e01d40c5000101d582c0354554480010302141110030b8541c140c6105d400110760b00d00b00e4805803000c01040d98800c071a81c01410001094003184101c90a01800350001100207441c20714007401a4072151003000031150803c90680c2203503056145564141001d00c0003011000e22014840c145900010665460021041110103160b0012000741c4100c00c216203041d02d95100b503641d680080d500341e180c0070a00d0a40d41c1224040d03d4244c000318900780c0340d9270055031224190f102c01c1e42c0031000540c9100090300c6181c0814883e00b1000c0f10307121030b003291100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 809561124 1250 809559874 809559887
    0x7090f02040e090f1c02070b0c0a050d021b01020c130b031f090b0f09060c1b1c02060601020601140d062a0f020307050601061419020309031b0d0b0403020f030a0f 71
    0x400c40c015152221070000c5d0107802080b001e0940340c81100c0284c0c2d803400c103c8228601110004000c14a1240481d0810881c1e03011800414500c528550030b001c480c200401281c1c0c0d0491414056400304140c0a0b00300d01c4029a031020156007070290550740c448485000030210b10428580c00e000003615624200100250300d50f02c1580403044150203c500d08206c051981d49441c02008030050040028244000600045040c9400d0038280c040f11021041c50381c01d90024688044010094031440c0301180e541e45c00800c00e181030f25070b03103640301c031940c1e642c07004100c520780207164155038850356044503862048102c800001584180c5a0b012500140000024041981000041d007150070034410100090400b00d2214111203281c9042c03c52000601e190f964203200e000c84407518040f40b000b511910640200103490303800c3c1c0450544100c842d62501e0102140400e20b41c1c158400d118040344030005110006442e0418000d00c120340d80c012454400070300c0c0d90b11030344085000c074000c01015642154042c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 809562374 1250 809561124 809561143
    0xc1a1503071802030910090c051f121e09060e0609070b190e1903110d03051e0909010b040f06050909040b071206030b0a0c090807090f02040e090f 64
    0xc000301010351074000102414412124480d261507000400f05840031000c009100c0da1030b5200c0010800c0c0c1d001890000071000c2c0a2003120b0040101101c0c0440e8408281210140c03419030380ca8040b41001c2e0b500d12100106620314a202c00705402c408100e401c2c0d8058410550024031610000501d0000000d1051911000810704041c4c7da228003018002900301d40b041d0f400703006c4505800036120310028001d5400c05504001c41e81c00c0103401403400000c1c170803d281c51b0300f03c0e80120040c403812100351061040303000050b40c016010441c2081810050030080d091f030501180704451003410309010710001084072900b80d00080b9000000308050040c4641c0d05034150040030b030380c246981740007200c4011400c40103000b00060048510700c000513080a0281c46064000e201c4803c08102c0c868880c54004a0f07a203040c1e454503680c0349031102d01c01c1d00d00d01030300c4550301b51112003000f0145a450300e0b0507800a0900c4640712042e0940074000001d00c145203000b40350103040c0d540050300440e010344020340c0ca800c00780b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 809563624 1250 809562374 809562379
    0x31c06060c0807020f100c120305060609090a151d0c280e04150603061401090308031306020a121a0915030f160501180b04060509010c1a15 61
    0x8100d081e8019400c485035035444440703503440d280b80740001020000384410b06504061400500ca080c564042c480360748a5208401d903040340030709801c040b0104e940403900c080c0c20410400100c200c51800c105926441405100003003244440c920b910000090664031082503508010014504403501c2c00b1400c0c0d01405149841d030514864101004400100c6903044002041c0001c2c440202441aa84640c039441c02030018043c000b02d80400441000b124454000001e2603c00e0114030640204086040000169140b0101500f9501e4030490b990000d04664620a506000800015030500182c851a072030341c2c5881d0900d000400803041a500d2440c0d003003000300c80d100416516a0355103610340c0d0308100d40e281841c00709441e00020070300d80000e90340c42d00c002d8400c48010f0b04628030000201c4040e01c070281c2e1283d09940707241601400c641124002c290206605101c02d000641c46040a030505002c145803460320703003440d81c07515550740c60294210208008030204010108544000b485e1560005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 809564874 1250 809563624 809563631
    0xb0c0a06111e090105030114010e0904110f011706060c071203120506040b0d29010b040518040809010c03090b0a11060105011107030f0215030f07030f270221031c 71
    0x3c0000030014401402601d20400b8280c0028030030364801c254000110502038860039003402d05082103c1200c003e0102d59207c0d070410310f4850015480342c1009100041a0140c034041500c1e050104050740e00481d84400042c400d015000905203144010a62064000c1d228051152481c00ca1031042e140c0c0144941d0240c0c1c14003400340c40c80c3c0c13114041c24000540064000400c1006820703c070405282100100610081c10310011039141000d0b402002141c504941c41c000d40d100305018468250011980940b05400c02c0c003081030603501a08018031110301c00d2800d5010715855482c20741c05600705511040c002100e1105c2000c03032040400c0900e024003401d09150444402402c5100e907240b06e5800010800684105500119180c2d065166500c0f0424000c8907144d1815103003c403840d840807542c1c400000d013407200000381c61845121303802561200c40c19503030703a01c00034601d401d1040d8a05a0101d8002d8001e024611001d00c01c00c0d58840d018869002031070341e80401c0c0320405101c1c142025044142d171318 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 809566124 1250 809564874 809564887
    0x12090603060303080a1109100504180c0c060905030f0c0d180803041802160503130909080a05070f15090213060b250609060605091605040b0c0a06111e 66
    0x401c90b01d110380c400030084001c51b14201c40c4002108038000c000e18a0380210304401401203c90308031002e8026507224000a00c100100c03203070310f6400e8031050240d480114200540c1603010440e0360b005050001d0003801100e1402c407000c480300e1642c1d800788440e0580c90b0800384041192030b0340030780fa545050090418401c00c0c2824510b6640c0c49204074801c6001d200700c0c081c8000d5802c039098040d2651141413601014001e500f07801d00b60b4680c1d1066544a0400e800c0310340216030070700346102e03501c41160400300c00d90411021403001d5403185c0c00104d080d544d809440404800150400c42e218075811106040840c04005d10300c103010712901080c103000d0700103007420341c01d00500d0580c9098950669001c10001801c0c9040c16098513455160034005e005242400d0380c1005005450304039a0803210161580141c17950b07240c2d0008014440c0d215442c3c005101048204400a203040250100141b404160b640c80c9582c2c1c2d4a0301e0440300f6039811001181800b00f138180c1490b50614032021880090346036a443d044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 809567374 1250 809566124 809566127
    0x11d0c09011b12090617010609060503040807140d0e18070e0d0c060e1201020901090b0315030102030a050105030607111507032304050c06180d1403040312090603060303 74
    0x103120180c60410035038407038151858841d0402c0a140b15003002c0d401c1c00096200743c004010300968028400407603a801d00301c1d004029074481080c1200c50a42e1500c41d1503080103811200c1c1d03031010700241c990b444140891008262403880706000000104001c21045204000103000c0054092030503209214810030380d00e80c41d0255244c20380c00b40744d903c2c2110205401c180015250ba150090180071150100700104105d80c21204407a079044046840046549043c100e6600780e110300c110250018450030b104011120107100510303003000b0840480740c843c01ca000c1c0402d007280c10441d80c270807090b9200c6004200c44c0c00d06002090704103645180001c1c1d00e00b0300e4540c448d500c0200900e266000c40c2401c0005400750310aa10048090280c03100e060b0240b0581d8000d81c41e07502088c0c03030a903410700404000700d0b16071400b070007161940c460348000a01003019000400c0709840d04600207668010031280071080051050005102075841102c862500d00910038004103801d4082c0c02c00001e1614089041c00420b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 809568624 1250 809567374 809567377
    0x32909090102040f050d06060e04060c0927050a23010504150e0c0703033305030318150409060b040303031503151e0c090602010e06010e18071a03011d0c 67
    0x2c60055404080e0131440d40340c41f0005101075881000b01809140c18001080029080300c2080450341d50b840900c5c81e00c42980c20782281810b041800d01c05e802400484d110900c9070002507109165640c005a07003a4050002040600c50b00b1104c10004441c1e001800185000d20404900d030034181c280d5051982420b0b403082021102034021411928081028000c02d0b20035040815560308071101082004000041200c0c1d8107001440200c40000d01c0c50082030505002050310301c42c0f202290f94042050310759040c408420400444442080700401012528021b58000c107001071a40704499950741d85107040c0101258590078425071401400142000410080d801d0071049103c13040d80010748591880000204a00c6440241481814a08a04055a04215003034200c6649070024400c506401d203030607460301c000740144800b800c1c3c46804141c1107420140380399188103030401141c0320b0750380711400c4c2505c001c2c507100c2c85c41c0507040010045c08482045a00c054441c0d01c40c3c0311403101400c0c48135811103903 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 809569874 1250 809568624 809568629
    0x6130302010509070b043c031e05030a21110306090a1a01141605061b090904241a0a0602010e0c090c04031e0606050d11060307032909090102040f 64
    0x10203201d06010080c2401c00c1149031064071f008141600b01c1c50300045680c41d45140c40195071001c000c8000000f10141d001001301410ba10101551404120310340a5451361007100c00c03808021651522403100c0340c107070710031142401501d080b41602da107898010000b41207801005144006d0800680a900300c3c03002c4142c1c2c80c1d0090900b05900118034000c00e104242c05401c5248843c1071000080030b00b03205020865502608001c040d0341c0712030b64010f46001d0180b00d0b20281d00e401207107040004000c2080d902e20f00d59507580208200c104a411214444191503040142004007803040d2089061840c1c00e400e0f200051205000a00078100d6600b0002d440300003c1c80154043d8201000140c10f40c180c090445003d1a440360b64101101908902d980004440708801c03100c2c10b150500205240c5402c1d80041301d810b07449505082d030351035190107001b920b41015004000b415101e42c5505c460030341801c80020b440440c4900440103d00301c1c0c080100c0c8110240c07622903540d20402003400a289071401013401e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 809571124 1250 809569874 809569889
    0x250504030b011a070515070305010f030c050f121605101e0806010e030f01060524030403270312030501060906050d020915070b1b18010e0d0506130302010509070b04 72
    0x6900c000f0401e1403c03441090710007407480c01075000043d00d03031013580f00d0507000b00f900e0340e01080b2517030722140762030401e1409010140a100c81c8220400080c9000b0300182100c01d000b92100c0a00014034880d18030346480d128244411612900050046080a4401c005015001d142079500e403003028050180031810090703182d0400011000103401039005508608880c4009801c079264400d0395030140e4024203207400b81d02d205240d210f081c0d0030541903100011a01d034001d450001d2031515155016a0719200301004007900c01c80407c3c05206021844540070025070150250007110140c07a84000c046490503080081030288042c810b20a640d0311000b03640192a44810050f5504910340000b1010740c3d03041e8805115082c009140303010443d20450580c01148103864034140200d4660a1400718001c80620048042c03040142822a62040e52500030b41040981391140d00c00d00354503014109541100c12481c24070840140b4000c159091007200d0380041a8000741554505102014140703100354401e840 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 809572374 1250 809571124 809571149
    0x3150c1b0f0203030c0d11010213060507060b1c060f0e071206060b0d1b03050613050a0f0c020c0f01020f0606060f0d05090c0a061b02100203090306250504030b01 71
    0x181009054100400a160003e00712034860f841d4800003981e41da8546150000250b641402800c4c410050098503044040403a1070b030b40140c02c06408840c1a04644820303580162a603000800a0304d0b810b10b480c000080b00841c100140c107103400c0150654a0340040c200c1c14514000040c00d09002c04211401500c0c810407803100381002e10308015005d09000d0b00020f49108002600d520603074091b03808100c140c1440d9081d00000005d45000f54203c030ba0440303c16411070000d1100c11200f00711988001da0000002c8000182a8040780c2c1d41012203450705d01000250380070381402d001501c0c004e6520751040102344014451445010980e644070b03003003c0c1c902d074001d602c00325002c11260080c4e000e0f00d00540409904003c50b26044a14554619150b2442402200f20f03007404105c0c1031140c0d101c0b401c1c1c0706800440c503c00b00c0385a802d000388082c80d1110002140010320482d4115601405004e00803400e0030013502d4444203003141c680c2090100100c40003840000c200400000307554204680c111103400c101c4e030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 809573624 1250 809572374 809572427
    0xf0f05240a031d0c03070b0a0503070e0604031e170a02030702040203092103010e0717240d06020904050109140f060a15080906011a04210c03080403150c 67
    0x54020f403110204034650100d40d111041c2c100080000d00c0c0700003070400c400711641b1a94a10720100c1c148123195034000017460800000e51490301420300e414a011014021030302c1c00d5a00d0311070070842006850400f0f2009400c0d60101d0a00c52040040152800090b54a905e08184007601a61328411322400074026034022001904603903040c4210301e4403000000d40001d4561102691002542c0b0034002c1040d400c10384000304418600c1000c0d03910300854071010f4083caa031164540c060342d05441086a600814030841071f19415210340c60040c0f07126108000158444101008020075144160012506189090040640e4a05400340745400450401c5203520940b1190041410304855802c071820501c41000f036110300ca41d0090740b80c2d104010100c20b031001c50340c0318610321501c054500000003c00100b80000d002d469081200f81408604040c512120344000b541d03405258121a40180d500c2c1c030001c00c04109001d226428124180612281000500c050780c10140030f00d00c00114a841c202c812100d03c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 809574874 1250 809573624 809573627
    0x30709142b0501020408100f02040e060d0203071a070c121211010204030804151806270f03120f0201091e03030209130e010b0603061809160f0f05240a 66
    0x2000141ca4002e802036581d01d449050b0a50b981c9a0a1a060340d11460b0000c1650b01500324400c0e5416600748030307200744090f12146c0820003500b8641a040c0e0f8503010740c2c100014110003681c410410034070000800e603243c007801d0800302c0180c030305c039401404405002e401200010702c40c100030b4a014216414914501903607204664024003440d0401081c1a0000501103140303022001c6154090050b44d40d0858420214000042e5000140c8522800300d814043d01c44030302643d200d036821007141552081c050681da580001800e03008035500a8800c01c40100c07108001940c082440d10306400c0ca800280a294000d80d00c11601c0c18111400b1404640440590070805200f9011200682001010760171440000000c2000600c48598009840e600c0c20b00c281145080c010f003501c0c0310360340c001c1260a083d02c81c92410041400002c0062031070f40640304014a4256400e41010054042084a5031020342000070041054440c0c1e0440d134407a403200586040c0041e8903080d41900140840c0000c4d445c2e800c010b10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 809576124 1250 809574874 809574949
    0x80c12130c080a0c1d04020411131e080f1f0f0c120e010e031c0915091704241b0b0604050a02072303040506030a0203070914 55
    0x14500e03241c0110006a050b030000e88800458001d03102c0c11080c658406203108a041d030013001c1c000c16814240054050301c4c25030301501440c065a6245480c0400a0b04110985021a0862400c0044141c0328141a84120704190701808803840208814006009c103103640b1541d400921090101a1202e5080107020b5040204000c04c1a079003440303106100100948101580311081d001d0a103001d1060b1742c80c49050284803048103051001d540792020303d55849100f0030b440341c1104a80f0741c603a4840700004030010240c0400300e07180040000e14142c00d07e4055141004512100b06401d8203120a1110104528021004001e074040f800790038801140141d9410264004080c04d0400140d003043c01d0000b0102c01500c0f40754111740400955882d9105034080340141200640f40e0210b4290200e04c4c200c4d0401c00b1080080c01d8001c80303003456581c2001030300790781c070440b100300c0c10b26000b00500c50103070341011554000d000780c80304d1440303580c0030900403516110ad054844c191120380120340041020b000803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 809577374 1250 809576124 809576161
    0x70c1b0e0c071709010c0f02040b03060103051509010b09010b03151201020a02010506100c0b0405030c12041508040201140d0f090507030209130b010501030519091b0501080c12 77
    0x4100c8040345407101001400e504024825203980319034900c50492000c2400441c0c11015050315542840385581d110300b13180d005200340c00c9800070360312482d0f65a1550100145402544210b0040080181c50340d202020004040d081581aa0611020071801e0f07036a04070840c10f4481c4403201c42e481c1c0d07640398511103410f2038002d8142e410071030350070300c00089240c190000e05c1c41501035002404035880c0e40c001e22440000203101d0000062922042c03c0010300f10750030860308540a4400c40b070800c4e070b0b600003250800307428841c6449042c000080420415030200d29000400d41e2500f40201c051030245c0000e090f145c0c0d0400c031858107480001c2d02a4032500258004042d0b02080241000003101503d000d0780d817100c2d203002c140d2040d55400001800d6031210421903110300d600035a400f12603440c160065010701809405160505542c0c1100c104482c802d11440001600440b20a881c4d0a00303544803c18a80468110074100b01011041000c805a074004680140c890741c196103145544000b05000c1115404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 809578624 1250 809577374 809577389
    0x8030a0f031a0d050d0327080c070b040e0f0a0902090604054209100b09221401060203090105042606010932070c0213020a11010c08070c1b 61
    0x91a01c209120000410014070086514100820007146d440a00388403585103e1f8050380c41d0b020b0417800028845009002d0005440b400c9071801621038581880030b4201c1c0c1c1040340e034081d01c8001c0240500c109480d15401480c0d800b020050005240c003c201075100060a035070245031508007048440403055220480c0710b01441c0524462122a00f820003403e091010802442010319404a0603107400925140180040d850140c6030324580800720905400c4400c1b00e0354021150100c111040e08044402c1d2101c42d04990006000c07140c0207140d0050320010b030000700455001b4402d454140e42c008046600b550781032426001c800c0f5404440c0e01d400750004403004424090040006500035864202030340c0072a44107403000b6000400715801001c0b8039200010b24a8001400100b003a80c0d006402081c445070000d0034032488800f41c047c0110603030748088021800074544440f8034400580030702c81c146038006240391116650a2400340180803c13030707a1002400320807215020401b980c12000f40c040040000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 809579874 1250 809578624 809578639
    0xc17010b0433081203091b0303071b09020406270609031407030203031b01050c0a0f08060d02030304080c04050a0605030c1c02030a030818211b07120c08030a0f031a 72
    0x340d4400c002e131a042a90707020313850b01c540d005001e005410310800314909000580258203100c0180c90762180881c07110090b100d12401c0304008034900c40540001c0c005808a44c803455001240c40c10950b070011507240010310101c410910501066a1001c11001140e07040303014030343d200310011562410070f03007130b0382c03009505100c00903000d081003d07015800720010200000130825942c2d441c0441d15907200e4080c107280050381c200e82c15010f16008540181c0c11100c05030161401074180d41c042890341d48145c2000409500100c81c910039032805010341540854a4003003030042a00e030202180d950140800e5452144090040c1900c07110007020300001d002e60002e0403655403403c01e041c0940007441c10358200b20f05090903960003807104000900042c0c0d1a842414200c0c0c2c151500d00e900d2171581286100100c482d10f03003001034511180400042c406003502604a603a4034000d481c0c40240e0300702c15031100b4440e810034462038800c1c1742c01505a0840305203d04000c50480c40d030310140d0310081542c00e00154000304 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 809581124 1250 809579874 809579893
    0x1502010b0603070323151504060e0904140a20030304030c050f190902040f050301021306031a030a051e071409131203051f050307031b030c17010b043308 67
    0x880300c110104030711040d03487c0304103101d50b0303512903425120301c0c0141404075a8040d02c1041c80d080040450b0b50050045e0803044c0c0394202030550030700f400300800d41030b100e45074a005125008201c1c4c10052006510803001145014519a40e5401864191040f54031841c01450b80307420030307122000401c0c5006403071060342d128540c40d0808940207400c180030b9800c0c03d640152010986043c14401c40b5040407281408000310307450442c0c210701600041c0b08099161a910700b02d40f420b80c80401241412074406c0d00507040c41e1a100c1c0c1f12450002035010f408506500c9070034200034181000c20300c01014082030310008110303920308001c0c81a103482a0001040c103044404035a050940c194043c44c010006c0040065401004c0403e5140b181000e00500740e00d80c02866082001445034851610084440a940481c0554030b49071408078100c25804200302c0d011035603050714468400c0c410016000c000320303020000c446900e4500d41d0102c0080d8016800c00c03148050111a0858403001140103003c92004c0b20750882 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 809582374 1250 809581124 809581141
    0x110307030c0c0902040e0f04060b030f0c040b0904030801030602090f06041706010b0405030d031a03011409060f01180f0617011505040b010f0507030509030a0b011502010b0603070323 80
    0xa6001c5815501e201e128000400d0082481c0221821242501c00c100644c1e00d0b050300e00004808054012100941d482510b0b40c44c0d92400c1c042030096040036000303480038600d0f103020300c8180d03018200d00301c1c86080c00204210000c3c1d00329103000d05485d00100016154030200011401280c3e49070100daa004c04003140c00601080341030828601d000b403d105440300c90f44e03078074800030050044d40503c96168000300924009184070b5031120541e600824070406082098601103400c661060030340c1c2d4141400b14040000e00f03d0304000c2c0c15000312040c40c44000540c503100007060542c1c000c5030741e9840d254840340600740c6000c176604080007a0154858144000610009a030300030108100b14844444400300d000509103003501c210707007190106864040048080d1041124958800030080701400002d00003809a0345082090903501c5108010020082d41000b00c2c5018207441c0498060440e814049917102c0c0d901c0d610191380c6c11680c2e605011804000100d40908a032021491803500313940501e04204000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 809583624 1250 809582374 809582387
    0x16080322050a03140c010c0c051207030602030114090f040206250b0f011806050a0b03071205100e090c010e090601140c16080d05161401090f1e050606090711030703 72
    0x12651402117400e460030410040d0352880300000d029110011002040146040281c03203484a1b441a80550301344a460365540400c076002a08015101c0c4003a4200c01c816003000c4006a800c82e200e5142114980f80a03400104d8520901a01c0d8101d0b180c42d1800b1915400c11880d600c10300381c6c1c4681076014501d40780c4020313801d082007481044048144601c504202c0c01b0b4900c11601540c8001d0810b030b81503414141d04101ea80c2c800340c204810000801090544021130b441058000da0007912120801072600d02214400343d00a0701060407134000654200d01070b81c020000715000c0d413043e260152156117240c010f89000781541d40e00214a8800942d560a00e039000c1144203040601280615820f921424110703030306c02038140c0c20300100d5001c01c0001001c2ca8010490701605101d4802425921402030100b400d590a4240481d004022101607c0412000d491060741c000210304403800b400c078803910350b43e070390b00ca001c0c3c00b260040180002044210348142c03c3c2402a002510480e544e410141c580207000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 809584874 1250 809583624 809583653
    0x70209040b0403080c0a09092a08070e010305090c040b030f0307140607080103051e01020d06080d171303050309070f06050d24030210020a060c1116080322050a03 71
    0x1000c141c0090b02a409000c06d540040003079aa039100d81c04d0a145079880142004150040c540d0400120b48030200c01026500c400000c00b56600d070703007a060510001d03004622907000a4185030812040182c8480e000488060101c0101d40105101c981c0501080c00e100503509211518040003030494284410003103481c50b24104242141d6841c1e68911048840e0042070000400c242c11403040140420324600303070111400c60010005140048410703a10341268816800f140c6540c0120070380c6050b1039000041a5000f5007120310b0300410f450442031030320b12a0388640004040c481c010020880e500c8042003100301a04031000300440311511800050034036080130080c0681c540c180140710030f031610103011000b407101c0ca03403035040d01003411682081060400000b41c4400c501c5013025103001b092072405100c0b4240529100d4a0902c80c69200b414100030300c484841c0c2c110f404035a41040071040020490300000e07501c60400348070325825415640c03002c22543c00070764000030000000c01803241c1205004507 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 809586124 1250 809584874 809584877
    0xb07110a030204021314191509050607030801090e0106063e0c09160f0c03120c05031e040807110d080a02100608011814030c06090c0109290708070209040b0403 70
    0x9000e46030408100e84201f000d6080300011003100b10410440c22013000c0040c0d4445035007481d8000035101e8000c5040b5401805003600020307044001009014403e100e41c1280d040c068000748101800c11038080c003840032101c9c40340c00840c010301006141ca00965a2129172042400c500c5200c0c800e00d00c02c41d503031035145806003445120150b0204622074030b03030340c50302d0015030a649030150b51a541079000e0b11000700040060701070000000c1d0484403030009100d2504030008985400d038070303400e02c440ca8405012541e004045500a03030f005010204200a054907101d6030701101c10716440700300c080414081e1448500c0102030030740208144105903004101d0052a59604c01c0c1080420b603500000c5081c1c40203428244000d6411700b40400c0403c40c2081030039900f0038241d040702e140c190584042844d080c022640701c240d54204200a04203503900c80c1424000f411540c41804600103c089060b003210416040381c20240d40001e603501c20080518241d8044640062611003145003908200c8078800007190102c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 809587374 1250 809586124 809586149
    0x60d050a05070510051321020607050703050d03020406080604020d02040807060c110d020607030806061e090301150e0c070501060e07030e161401110f0703080c0c01090b07110a0302040213 82
    0x103200c2803060301510b03242c0da07803440c0303590b0368610f400070f6031f211001c4031101640e440c00d0031a101c01c0540c455000030180303c0d2140e030082003014a1402e0150600c603001c030000c400c150040200700300c0a0382c4040d06641228084900503940c41c01912804001d12842d0300450203405000c2000a02c0e0b5004000703100304c10300400b025210102d018080012440d10301500039407051084c007003400824070440341c1c00e9001c8005000c007031a003500030030b9880200402059007600c802001540e18000e060a00455000c0d140c0407002c260800c0c24100880610140109446900740012404006000007500010000c003541213010650b0300304000c000f801340c00b00200c146903900c902c03020301800c0517182d40154102c0d8031101011504c000014011204228002843e008902c0b40c0074400364801c83c1444048000d500c10301d65151f131000364241ca9803e0100200260f410300500000800114040d0011140025404005d00d0017001e4400700040745881550800780d0018800f10b0004c04058003510303090141d031150506038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 809588624 1250 809587374 809587399
    0x1081c0504050904030c0f05030d0b040e03070c0608190c0e0f0f1311090a080d080702060402030703150e120d0f0506060f13150503060a050d1a060d050a050705 70
    0x3562144554071a0940104001c0f0001c3e01092050000980280c8030b91150070f40711406442c1c42e4510b80201034040c103116555149003940d4501441004242070845000c2e50030480d02d0b403142e13003c15049120341001c0c80104030002c0e840ca201c040b900740d10448691020840d4607000c5000030a051210074140f409a08275900303491103032030160101e0001400081a410307410042c0903801018086601c40e280c1058000d202824a46d80e03902110b80140c0001c1e030042c01008a02c2500508280b005010201550003440620000d600c01103249015650086041a0b00c40112000300e00140795203c0e5240711406403e2499401e03411020051841082184041c42950381030701900f02143c0c010b44005a2041040022003600741c00b040241c00110340410107220034030340c0c49210034414070711841c105c0001000041000b0062900c00c1201003d031500341c4000c4001a1a5034680c20300c0101105581000c07592900024019910901c004102d01c2d88070080e1886a0a0340c076226941c1d04c0755000322407191b240c2e03c42c2d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 809589874 1250 809588624 809588627
    0x40209070c170a090b041e0e04030801050d0309050d030c1718041109030a0f06050c0c0a030309051e1b04020903030a030c0509120f0105070509210f0601081c 69
    0x511615034200620358030301680300322001001e503c43c002480034040d07020fa00003001c510a00261000b800c100c68074400b400d81c246040c2804092603040807000d070121170700b4000429401400f660554070281c0780c03240c0c140d601d4142907400c620580e01040d800060704220f141015407000000c031406e4400c00600c22400948005400e244c001d41503c0c07503071580301c0f04200d01140382641003e01c0c855104080c1a00e0311900c1c102190405005e100243c82d80034207604098100000d91050540c4120b40e010107c6c207107080e10110710b0b01da07011078a001d0304154455034140d05000040c800038400014050b000c0c807402c003424802603100c44202d03582070703582d07072854030f8045031400c09000322440030600402640c40d09200c50815030092a00000040404c4014040545103032560010103049840c880300034921048124506801d540000389220200703e0103000040301c54603114041c0f02040c1141c00e6224008805401407860100d00c2c01a1044503c00c180000842034400719403452007032420021642c90705000d010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 809591124 1250 809589874 809589887
    0xa06050a09140a0e0a030c1a0906071b0206040603020c0c0907031a03010c020c0120101407030b010815180c091504122d060204080d030e12030615030a0504020907 71
    0x224071542d400885c28031001078410280113074540d20030008a10310300c00c41500c80840c640d045074034007180da004905100c01150403001007441400c2d42000c020900000c2e034040343e1680514441c400034150042406005180140134203580780401070300700704062408002c000d0142a1003c054946070b00901034200713050506008541100351143c00401c40181980011140003a955240b40b0044240c85807603240c1c014240942544440c9100380420080341c0e80703003072481204014000c5428140742c000d06070b5050740c00a0300c89034031031100c000100c1c203891020b001c07403035500b41c0b00d06001d00d82001e0ba0401071078003422405880d00300d034203448402d40b40102140507c078600c07903401441040d08507012320200044000074400c05001440c401a540013070880a03100d09c1c400d0030201120501d40124040c010301c9400c210090415803186014000c05200504480d2a00414143c00400c3c2100000060781501c0d17030f40100f440800406070155030381c80c0141424008007010b8030201d2145030144003003103d0601c18036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 809592374 1250 809591124 809591141
    0xd0e0a0206041401021908040914060d140a1a0a0605010c0f02101707080403180506120c040b0c01050108060c0a2c040903030608280b0a06050a09140a 66
    0x6001c18a0a41880c406441820008590768110701c5122266034500210a152410491250a40544450900080c40c00f6514201761440003004100300300300b810382c0d03100702c144e05c801d421505400010b00a003956a00303020801c03901508070244020b030b0001d0030b003800302d805110b442c4000080040d1900c800046030008a09200a4121159030401c180540b03080344e4680c4404d0320b01c0c100490f0300482c507803581044050444030800450343e40710801c018503400000c4c0344e0120455440c6c448180c6c0c00d0400281c903500604c903c410360281c0540000c2d1002c1c11070011a030181203407041064071101034015044c080c0900340100003281c051300021030030601d464815103005940d0381e01c5807078141e0074201c0f010510000c10b001d100000d1000c012942c4440e01c0d1880f69a0405000b60b4012400e43e0500000500d4000140789140c2040800c0d0f00c201c03c408000035802403216401a4001c5490301c4800b010405401c20307800c919448903a400340003458030318580c040090104106481019550f41ea0b140310201c81691 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 809593624 1250 809592374 809592379
    0x20702060307120f060b0a0e040509070b2104140f03040302090f09151806090c010f0f050d1a0112060e01050105070303020f0c0706090f0303120b040b13020d0e0a02 72
    0x30700100318802d018442a02c4229880380380021074504c0707000d4201c00e0f43c1083d445590b02d450009048290b50b0346c4a024103980450654091009040c40396419a8400795031251220401c4003087c0e800905045d40704552085c800d070183c020703060074a803c0103030f42ca840c003850341c11591142e1000c0200311304012003614112500144410f8169072035860540d0000001003003130800b8003804020b14120f20800b507856008820404440d80404404000903184c14002381111401e54400103188010360303801060700308655164a041d04048105241c180c8540c028018803860301e509111121300086c0e1081c0601b01400c0c0260784100c078105495135a03508590b86030046880400c4040014090365005a0041216600c030b403070014504588081200c120b80c00041203007c00d500600c1c0c0411009a000009001412045840c422514510b64000c0d114405540d11100700e15200e03000300040d0781e40c5500c400c0c0300c0f80010742041021039660030007030029840071003d0000c1500e080803074111010005a2840b415502 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 809594874 1250 809593624 809593627
    0xf1d060d02070201020c0a06030209121216033c0804050709021309020c060f1e01030b0c0c0d020f0d030e0606090a0204031502180d21140a081902070206 67
    0x1008200a5071140400b80c4c15449400960442625085010310080c0026070300140c64035020b600304100d514207aa030000d66a44210080422203501d0411075000f545003100070088218145016a00014841d2812543e400424038052035803e191032402c0c000621007049080361151042c003035882d41416240178000d41e00143c5c09110282c00d0303600802c05030325140041c43d800c956880e001c101b87d038001d604501898201105000480c5516182c4a0b0046401ca8105044600c14081000c90701c205202c0a0311a035402c102082c10003400300120365014940c035042c1e071000303c08020040c0d9102d110b080e02d01001e100f60752001d000742c0e129110350420400c0b000094417a688400c02045180d02000c1d040300c100c0d6508000010000d02c28003462040300c42200d001586030070100142040b108000003c0d00c0c088d402c503c0740e00001807602c051030480c0c1402d9010940e03c201116200304c1cae031030b46960700682290200050300c0d40c01c50b40140005103d0f118000e2009101c14042040c001a4003880348020742040d070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 809596124 1250 809594874 809594887
    0xf08060609220302070e0702010522080f0c0a030f080106020d0815060c0a05151003080a0e040513050601080a050c12030c0109060506040e070e0604021602040c0f1d06 73
    0x8180180903000440b080c00e02564094108092560518050003140503901c0003408000384040b44800b1075210036140001c2105241080d04580000c00d01d0400b0340190070401c0380c84007000840d2082e589428401c90841e40c0703ca100482c069920304d05008142c0210781d03034001910205104943c040d060b0744190340034110109002805845564024052060114050443d1900d40c4c0751a000b60003614021070040421a42c3ea041050a151113010401d00391030420f02081320600001d80d0b0303407044030381c891204c88d503071850366000704e801c000d42e0910258000d00b82414844180180c940d01c50209020b507044e40c0a80c0da840384450b55592004c3d00007813080d007009185424503e00b407405400f403101f060050741d24000e4100c40150849030b0848040355916901c900340041c1e41401e204400c001c8401d41c0003801e10380d003020041410008010942407044d03400160f54403900040300368003842c0d00e50242091040071011030000d08201c060460520000e012858550035035051070441301001d61001d080d0516101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 809597374 1250 809596124 809596129
    0x120181f0c020a0503030a0f080c040311010c02030115090c030c1106060d14100c140a08010b0d0207050a050f0d1b020108130b1005010e0a060801120f05071e0f080606 73
    0x1020801c1070b40e100800400014250328240b00404030403c0540d6039012000049070007038050311004d001d0300d00e188018402400051040d45c1380c0c05480342c090038060000311661001a01425100050010100011000103a120000d40241c0d075004016101405961400a011900d40380c018070b40ca240c81e4094408030b211410724100b20b49255004420003003001204424aa150041c40c036000d9810680c2da84442c04c0c2c070b941c0600703200c4c1d003e03e04070b095a103811002000140303440e5041c0126090054005171520b8002c44590440b2962607100e0187d444141941c02e0283c3c5030160b543c0301c0d41c0d440c0500e8407007000f000d124402d000400400c0004500701ca0800703400455641d28002c00c40000504402210800b0a810003030300362280b0008852203030006e050900042c0340320b04e000f4449008503404101400110b4100120a040d0360704c0b859103c55020860070401584008600068518000d00a0114021401e880068807500c0149020440d4542c0c0f02002d40400449216003030154124201040561 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 809598624 1250 809597374 809597387
    0x280c0e010f0815010201090506090a021e01120b0a090c050408010501170a200d120215091504060f1401032001080f100306050903040503060a0e1903020120181f 70
    0x5a2045c4000600c044840d51998038104007500d0300062039210f540d4090461419030b41ea451205c429125407007805000380d0004e0249901c217201495890b0b01c582600c0031684401d003042c0000c0c0702c45070061000b95000c490140841c2c0c4103000e418000c0d42400004a0341d1242c000310402d4a08400c0b00900b40700c1120f031980d1032060034042d80300604101d40c038901409540c4520141012501035100c046800b25041000303840c02a5041075000021448004c01880300408a0450799403410002d00c21f0042c0d5030303807a04500803c4000e044103400e61600010359146460708080f42d041c0c0b4411003802d080032100f00040c10703906449221070350005000030009465919050507040d0000d40d001840c82c40d042d00d0395511020b4030803c0380d00304255030005c85e003000989020001940c2114484408000b02200c05807140c0d10362840d415854001210101300b94101071003544400da00003c0681151007504101d282451a0f91220711200004802110720075600e245c422000481c0e0041110462500c032040c84080e204c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 809599874 1250 809598624 809598661
    0x90c010c03050d15170c060a1d1203090112200702010e04110903010b0109081b0109080d090501140a17100905040f0303060e1003030305280c0e010f08 66
    0x40000500115002035083d0081d410031011805499100500340284170002d00e80d081da10f006543d01400c540d000c2d545920089481c0d13001c3d2850400c04188010080e44141402080100d800c4401a404140c0006010001d4105800240d03500c3e0b50700c4440d112102c05480c0c00304c12181d0b49501010801c2030000d041802052002e1060600c20140755091000508851420008000340c0e040091490380385d280c28403c021211009083c0b01001c5130034020102e6503032500d940300c494080d034404040c0301c0f940c0c051071040c401844540c04032503004650400c01052030308540700b11404203074541c00201d90300020405841015041d9a20325107030386281d0b401c50645000c050081c640340c085144001c90051300314028184a00c0c000c0030003840700d61203441e0003402c6070040c0c2e000b580b0242070f5806216581c0054061301d01140c1c1c00d4038012030680c0303c0d04204201007500745160225034005007085501007005422000001c1d4450b150402110b1404005440e4807490301d0303000000074a2100001c12500d4210103c5c0c45 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 809601124 1250 809599874 809599877
    0x111210d0906090501050f07110312040609140f060106050304320708010203041407030533071814100c0f0506041a0604020a0806040504141002180405090c010c03 71
    0x300c0080030748615046680f0b1110640f45030b5110700800c0f040d041c4a045550f0001a94074002c15031801c0b080c9600d46a0040702c0f4500c0311200760710041000d01c03c55070898007609401c5841116107c11902e1041c0d0354443ca4241005c190044e2800000d202d4003400c01c1d01d20079508988c024086400803c0d000d4180c600035008070000b1000c4041f201d0f126502001401d000c3c142003030005949040070b0800c01051800030100c60003035801903005000288020560365a054208881e20b8000c3c1c2c00c01c14100c43d13162540054003000303603074074040100b100d502511926280052120251459071580d0700410031241c8129401e0b0420352000785095402e10611071005041d0040e84000b03406003d0b40e0311503080040640303044d503007034034180c036404130070400d840c80301c3e4209608880c118640750244030040c0421034020049841280e540e4001400c0c81a8000c2950002c4610400d80c0c400e5410b41000c400250480c001c00b0040c00c008220b031030b4180c28544605405441d412000304100b10058004680e03100d2601d100b00c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 809602374 1250 809601124 809601131
    0x30b01030225050f0d09090e0a05150c19030c110705090714190906020d03060f170c0a090c230304061113080d110c01080a0507110312060111210d 64
    0x60341440620506070541419a200b1600783e19215090303040d5130070148518419005a0041400644005001d4030a001200e40303418250307803230150033071b840c1c0036040506000c3c016110344125025419404001402d0160b1503151406d00131500b80ca0f91240d25020388d030740060003903002c901124042e204001d20886070b800d03010700c1d10001031003c40f03040440c80c51100206010701002d100058050010307014184540c0350401c001071034825450b42003002031051480f9440e800c4007aa139803404c24402c00e0300300c91001c1c2526041d06da80f425070400402c100c14a5400103180b183d449071114004000c5814500b010a4400c4e0440e280c41d200c5600502d40e0345c6003403081c020100180e4844401c0784050740000c20240c3c0240c80024211800903240292102602c5440c1e0001e003280011a0381180c1303c10307007080e00d40d0800201c40d600d1180684486519810502c1684070107d5081220b480c00c0204a1017503400b83c0c0d820f090034404000c1c90381d40b2002042450000c07840c003584e00046850403809007140c00d03500000071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 809603624 1250 809602374 809602393
    0x30524060706090b010e060d0c0b0a050403140615030723040605030d0e10030e0d0309030201020c070f0311030f03071101031b030e07060206160806040902041407030b0103022505 78
    0x42085500003601103856240c2c01c0c0040200c1b104c4280301d180d11440c141c4106e07038000c3c507a0f52510040b00050040704004d08c80483c5101d0428450000c3d10040c42c0d0120030942d20365401420309907070300310440361070107400810306a111240c100030582501310f411101080d8034003426a540b16141203100056590400e503510f03000620303960f040015918940300d50303c54103280701d064410300c20f40351080c0400109050070b21049801c840301c000355818141d05a46400a01c4118601c5c040740648201e01c0d8112552180b2200800c84090403805203049900c039030401308a04c2010414580c4030f00e01070000d048290001c0c041c9001081250348000380f801c0d01450001045070000928000d8809907a0592001943d500c8004a1900d010000a0f000c0d11807800104042d1818004141c009005914010100000b10f408242c3c02d40fa00d80007440700300d40c028024000601e02400204c2c2c0d51008483c9100082c1c00d0151010311940a03100716244010b000907911140c20036030b85040768424207840c04403820f10072940c0c41f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 809604874 1250 809603624 809603633
    0x9042a050d091e031206140d0201030603050d05090f040c051e0d1b0809010614010c0512030408090108011a04030231020a180e010e1008011104060f0305240607 70
    0xd544010f506810403d1107110030304005000034500007080c031410346004020705c42c0440115020a98032800c4035501c80495462004230060542036000030700340c0c8900400d90801c1a08000a031143c80c8007030791803840201451040100342d6219001e45408101d0410801d0409811020072405041d088071010380340225600480f4205c40740001c030024803071960402c0203000f43d400381aa86d00418800700038080181001802101401c84407542d80c14807951950311001c01800b84240246a0307000b07401541c81e45460708103083e560b400500840d00140d000000415507071410751030080c100c401c0e4841581813906650074000b080c001441008648070650001d00c002421074100090030101c0b1030000350f00c0301c00b0b448003e480925100840c4859103104a410301403003000c01e210b181199018203070102a6110134a0860070350407103400139440c2e9400c11071031b034101000c41c900030001c8a5043da541e001940085000b00c0c04c44000341c80b994150f03110382040c2d10440e03516014030101104000c0545280c09541d559 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 809606124 1250 809604874 809604893
    0x5061308070e06090f0601090501261602011b1d0114180a09060501140d06260c010503070507110a0f120510140f090705090c09042a050d09 61
    0x2000c0a0300b03440c503003000802c0c1410b0f0b00f2160005000321442481d030401400280a040f228010581040241c40007207a50451001145c1d020204c001c00102242c104003070516180e0200d8070500d0f02540c20000c1c001400d500040b5600c2104046035900b0349903d82d00300d0040b40121680d250281005030442403900001c90300e000600810810020102c004c403c2c42090000344036051b4408400319140c41e10812080e60803111009824440440d4183d517107800044e0000144800e41041145041115807445000c541a8655503007001520446202650740c8004650038442264071500150041c01040001504076484145c080e900801d902c3e0129140da414038080c400e07980c07000c8840780102e10410705000081c0a0702110510046041c40880450103480007402d0f0080c1c00e00040c00d41c45400244030300340520290001d45401441e0701c90a0504e03200310130454111100881c0303e2403a2200c0c0c00c10701c0d0300c5034504000c030b0b680c41441c41011501044065a00f60460500345465a031141d8890000030304140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 809607374 1250 809606124 809606129
    0x1902030a0f082703091816030f02280305060d111009091b0e193c14090108100b2419080f0a090f050d1d0303130506130807 54
    0x70b00940d01c56858400f0046c0e04d0340d0403061449103120a00501500c200c10038002001002d0908010590081040d9910b00a2140001d04140f030004034101590b00c511341e1007400c40d003041c0da58040c001c07030b204c10082202e04480e00340000c040481c04404d0601c60700782581c505000c0c0c05a8200020307501e503950503590070b41d003580c12000c80c0c0300d9036035445103030050b00810300782400b080c1500c650580b0f02161780a40d0103048240250761000f003003100414080e41c014000d01900c9690504c1900002910031b05075903030301015000e036882c1e4103c9180e854a0070b08109a40718102c801d010004c3c5108094070076260004c107840849030b604503071103004290a0780e0511043c2c00494024070300e007583e00c400c101010850750480e03d43e800104200c4200b4080c03c0541034490b1354000c0c205903000900303050945400f4022010f6440c0003405402244e107090b8059810103040011016000c43e100d50300e1861808050300e9100d068a6124206900e50042c485030800001501c500c40d240030500180a03190070003a0700d0400740b917 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 809608624 1250 809607374 809607451
    0x5042a0e1f0e191503230102160c06030e0604060c0323041b03030f050307031e1d010b060301231e10090b070615090906021902030a0f08 60
    0x100c144945902d0f980032102c80340c07814803020002c246100f120840d0301e1a551101801010a021403c007175407144009894640400c24001c6544400000304030700680148601500d5001b40003400103040c50003070180d400619180000307003120340d845544180090000d102d036007003050b03038560303218003104441d00000342e428400c11034440140c5428907240d0004602c1600c070700c900101c1d40c541040021380041d85803a522140d410f060380c4903565840114010b14034610320703041c042140100601258802ea010300b1040740748041031441280200c844500340d03558181d41d0b9420200800042010030303c1c2c62400c2105002c40204001b556949100250840303080e5104002c1204685e9030540161034400085100003206060205c0c20f01c1c508401040c0394002c07003901400c0e1a071114030000c403580d0103045540180804050422990b170290802e02c000750032400400e24418101c0b00b0180003c0e000105079840c89107982d03181003140c17081d84000c607a03042e0080c3c1020012900003507100b1452408174a8050341712101d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 809609874 1250 809608624 809608649
    0x70b0307210615120e010c0207270c050d0f0507050711030c0603041a01060e0a030605180d05040e011a0301060c08130311031e0309010309030905031005042a0e1f 71
    0x6007441c0800c840e400170034030010368500f43c50160000d4001c1048400c44203040425204000541584201c4e00c8103181a0401300303240c40d444031080b6802c507014004090701504200310b4081c01d81d520008a80e020f84000000c203000303118000018204100003019207101038251804282c900000c20b40ca070b003003501c049840c60214140c40c5200410404994010003040c61700707208119454011070311181c52404003030030a584680c009000e400c4100c20340319000c90381c41c0440e42e15050790705c801400742d0801c0c081c2a0040303a10388000100a405410950400340b1440c19180ca182d00c0c14605a42d5180c91460032aa1540705207d0015a00340c2007111500860054190b6500003040e101018140410721030360094090040c510302d802c0040010944214010a090026280c01c4c6e50a05482a4440343d020541c10301c950b038680400c41106030402c5005921420b650a20403039403c45a5603452403a0903072641400481c4002c20200f01455010b6800084914100301c162103400030080d00340840d5005200702c17146 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 809611124 1250 809609874 809609897
    0x50a14010e0a290301210f020a0b040602120c031b16080a12170403030b030708010203160305012106090c090903090e0c12060d0203030c1e070b0307210615 68
    0x140d00d44010004a01000703c2c0d851503041c580600725005115200c0405020000001000c1104202c50b0701d0759540c005000341040da50703c000c0c400c20795026015000060190940314221880094183c0d0f00000004001e5800c0c00740e10500301e5104005045040103d00c208001007079032076240403040000d002c041003e08481c13401400c1c2410f882c03c2356140c0104000a0403034958800c950b103901c6a42165040c50041140058480080c0c43c03d00740707401c00c0c91254400818888503c00203003501000d121f09450138000350380d030f5104500340680310f0169090380c20f030043d4201c400a030243c5d00c040e060511540c01202601c1d12180d08004451071401c04402003070f16002c0034054030708004c10456002104001d02880c005403028913007178030704d4003a10841c0518184c804001c21964180203840105521904840b4200c1d8050502c3e1042d2001200c44620b60250600c08218500101c2c210b0303128452170340b5002c000e904030b6203c410082c6420754003010060380d908000706500200841686030303042650350b207816519 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 809612374 1250 809611124 809611169
    0x2070506060d021309231005090f0307031211070501140a110711030a060c08010f061d010c020117070905011404060206040b2d090610050a14010e0a 65
    0x40940303070a2044008250400042c0e42d02413481c824514084d002244001d1203103080340d180210990300855082c40c1c0f0103003100300d250000300c00050b40d003541810b00481c0c95030464a51070708040340c1d5084041c0c20800055003c02d0140304070040f00410110b001800e00c1b400b88143d038081e0001d00040341c0700d035111148050300303980701d01c689034105e2144201009a000c5503201d01016210b4880c0c0181180141d412100807650107104130303903106412545c103003d82c800d810030050030a1070034000c013240b051081c100481c40b00d104059030200b5903469920a00c2d01c0046000640e082005070750100d0400c0b0543d0b021406801405020034003031007003030312100e088038144000074001c04040c607000e01d41031005010400566a0010b030203600305070082c14a12290f1130780c0d42034100c03224480c000d0317801d0540b03d9400001c915031251a9140b203403224205590b8291540445c00080303c0d070902c14a5841507070f00030180900005110b00758001a01418040880100740300891988070795070f4083c52004110702c90040307410703 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 809613624 1250 809612374 809612383
    0x30810050901030606030b0a0e1c140c07060f030209030c2b11030111070809010305060a0e0c03070e0612011512060e0417030c0d090804081009120c0b0406020f1c020705 74
    0x3140f00c4014807440002e1417155070b03251100042e80c1c409403141644050500d00500c0b201028841c880c0cbd00b01d0b81e030780307546051070380d5021103100d003c2c0029000c04551310782900c20303c280e800e0500003c0207070042d41c80c0342040000209410080309244244940b0405400d144442c0c003140d01841001e0300000904100c0416003100c14a403081d01140c2810010b1b0000a10070000316000340b1000d0800044a855580116282c000b540d000080c0d83c0c2d4040c4244100742d00307820301440c450903459485020b60a0120148106030085210000310320300300900502139900c1030006003010b542d50b0714000c00320142070304420b810350703100b43e114030b0403500500280018420a1b40e8400b40f4080e40b4501d0a24504054036094500d00c03401141c0c0340600c0c0c3c1d980c805400c20200c0d800311801010414100c820220450440c1e03c010310024104072001c07a111114021401d014070080b481c12a0060141a115a950340b90301e00a940005a050380400040001100075184888080e0315071102500040e26009a49000e41c5003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 809614874 1250 809613624 809613631
    0xd0f0c0222020a2703051c03090206040b04050f040b060d0905010f150806010b031905060411120a140105240405030d1107081c031a04020d0b03060a020412030810050901030606030b 79
    0x2d030034002c581030000c01c80001f02c1038007500d403c1042c0629030814401c00c170010411160000c1d80004002000940349450300041c00643d01c2c101c40f500d140301d0001040208650f004803581d0f0700601c2c10f01a40340c8030980d0780e000041040c0a0000492030350101c51000d01201d10f1100b424807030b500188018025604104107aa0140404900701031540c00c1c1040e110800d00480c90006074000d8031140080c280340c4a41c2c00000109100403601c64503244080c1165401c1e20381195944611483c0c8488044180707852051641202c40141880390610312030034860540d0b0712503440001d28140704220008850310100281e40000d9860740d5282507502c880d032440380c14540f05074009000750380880e0300b05150149410f80700e000900c42d8140010304003007039105280c03406442c560340e641c0544041540a20342d4241c2d0411000c2201c110f05954582c0d0b030320582c020403406940210a00c030040700e905103000078050000c0030b030084000c0d8401d202d850b95450010320000400d8004544040d03e0756030410070089a040265003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 809616124 1250 809614874 809614937
    0x150f0609110316020f0706170702120a1b08030106020a05060a060509060f0d0b2d040506130203030408060a0f0b040902102604140d0f0c0222020a 64
    0x90241c0800d590909804083c10f40c04042c2201a04410703824001c02c4180361480120007901c2c0e00682d0740700e001d0000d02c903140042d851440d910000600321407010880903481200ba4a0785801d103000120211019000441041880c05500d070407400412603d001860007001190300402001d01c00e45011400c000025029058040c14660180b24076070701c106060354800c0b070943e81007446403d008005032440381d502c0005040b010802090024548901003d01c00200c1540900310300c55680020154207030400b100c001d001600401d0200d0b0604100c2d003081c002c4540020304490406032204880350400800340c90040c4c07050741d22401e40b0360f5002a030050140d550000c46041100440e01d03004680106825080301082101e12020f01c0e00544008103404418140802540601d181c00d24149425500b8000600203500c46c0501641c145445800702100841c4030341c0e100b203001900d5509002c4242001703411150283c2c84441c00c814a00d55901c0545105daa050303991100500300400100d140c0448401e0380c41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 809617374 1250 809616124 809616131
    0x20c0114030f06040b040e0a03090b12010b0a021f0f18030512040203161215020406090b090301020909070804120503070c030e1c080d050907050d0605070309150f0609 73
    0x102900d40400580e81d0000030026000301e107584401c00280203254500714150f02c0f602e011401d1000380d00005084038018407c2d12201041a11600d0020840c01580341d0800040e0b41c40c0c4c014844441c08101512840c801c0e03004030f07074407206c0e00c01c2012484400e0074440e464440d5130700c0e08400404c04900a0560348404000c3c104030070202c60320000c00c68401c000c1c440d124032400c07a010500b152410045c0d8200c11003201041940e05843d801340c44a10754041e0819600a10000302e4500032000302d10072202101c9080d00c811400602d4a410705a4641028480c0742d4155401e00c0040f805459980030b280c4550103956400003145401e207440c264110342e40f049182042001d00411540c40d400030a030154103600b60402400d049110300003c0c43c0508016094040c0320f4444440c04d04020440c00901509025400700780310556900d50000c1d66909144541903004201c60640700100344940d02190300b1078614a804140340d2040c1d160b040b4010b0319109480f12840d0343d80b0040902c45010310464000d0000a0004e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 809618624 1250 809617374 809617397
    0xc010f0b01050a050a120e0109060f0c0c0b10030b0f041505090c133b060f07050307020102090919061406221d101d180106050d0f03020c01 61
    0x2d02d280a00c025800501400003134030340300d06000c0d044400440907040340c107200341da82c2c040350a4044c00103040300304d4455080180c0c09443d503d00303008034902030b0040d035507100e14a011912416041440a41590441c0200a00202c0466503034140d5611820007406403060a05082c5000700102200c4000d2109061821050042c0c90401084026488400b112609103d00300000020010800480052141706e044140c031002540c030180000071942c01040018060545111655103a000807602c00003d0300b0050001030559001e00301654001c481d500c001810301003070001140001d4419600c10209408212000d2000341c1c050003800c01411040c40455005100d64012904500604118840c0c0c1c061103100c1c00c43c009944507104008015540f20105174100914801c1040ca00544034002c8524601e0390114400101d8807500c0c142150b00c2c0c003030680c0c9a4a040812480041c90615060389540b030300c1d00004c041c0d94010490700e060303000c0c480701000f60105280c0032345030480c000c480a0500101e002e92 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 809619874 1250 809618624 809618627
    0xf060f031609020d0605060c010609060807060509060a0e040e062d060625060212130f1128080c03240411060708070c05060c070303031d120c010f0b01 66
    0x100003101c407070340b0380540c8074005402480080c02c0190040c50b0080d0012400c0d942c824015007009048070500c2208001e404c4d22506451740310300003401040d001c18420016000e960600d00020006c8083d20328240d44909229400103040c0d40d03061a18503c0c541c030035010b006006000c0c5a005e044898500142c9041d01040e80d01d003481c51034000c0c0340c280304440105141e0340305108100780f4406040302211032800071140b8030b8610025003000311401146a0454002142004c0040030f401d034043d003014502c020203416a59104810481400560300b000240303400f614070108954034050400040040000382900300300040f890442101500340c4264060140c20b10401004080384440b094104800305050741d850070102c03107010180d600c1c40d410000000d50300e01840018005800900e00c038480350558a69144100aa50300555140e6030240d04000720400000740607900825150745410045489111201600350424000060309290520300207290070083e1802e108021301c01c41c44840400c03035040c2e440300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 809621124 1250 809619874 809619913
    0x40b0c09010903020f0301020c1c0e03011a0d05010f1a2b0b07140423010807081f0b0310060908030a020a03030f1806021806090906040c0c0b0f060f03 66
    0x2020303020b064219174038280313502c0c20340444d40303008640001c486030310310884131000d110f1100c0983c6000107405828829039529040c0100c855506104502c6104440040c0030001200c1740d810003180d8a65a41d0418183c0b424640165038909400c801c40501800344c0e0f0041c840c0c105c40000b0706282103011020341e2698114039000e001291604803150303c045650b04002903900c0426882d200c0ea00c100d000c0303000140008015501d1501f2003112100202520f00c15005441800c1c050354500003040424001891030501e5680360100720714102c030002c40007503071146802c240e0342c41540c94041020109000740b00303080d00072106000a00e000401946498401103000351200d0202100408141c0c5495a9a0313000182e90020b80e000e040d1940c0102d00444a0b240100007503001004008100c109012004240d00d030000541d804040064440000c0d542c41c0030400c0024000705649500340b185290114003c506010481c51040301c400301c010300141004810820124011030348284280c0c0006040c10300310b01c0300c88 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 809622374 1250 809621124 809621129
    0x426070f060b0d14030d0c0305130206090a030f081806030112110a0803120403090522021e1917091e030c0a080306041107020109140a03060203070503040b0c090109 72
    0x1c00091a0464100000d9015607002c8000c0c0403901c90328800301400070084020102440b5841c0200401000b40c441542a5581140d898071044402100740c03016047c0380004103c0700c80d00405e1031005076125070701c140d176017004090159010080460007840c0000700203204106160700b119070500303661502c1a5241001d815600040100070f580e0050700c02a00c60707001c0b09001d46185001d40e070310f6410324a0307091312400342118160f000441d80a0009020b007007040120703002800c000d0300c6031302140c1c128079058040d5015144110140300780400c101c64450150025101c45070000790280c61003590a40000e043c00130001d09601c02c640801c00348160f1709400074441c032680c00c043c150710b0040d030040220f603402d5000300560310080d8020905028204907c500041d8840e580807a4204421810155848d00d18098100c009010603000cbe1070902c40b001c2407038480340c80f038103008083c603807003036103da40d1078007a6041a1030755004150b0220030700c0200074400c4512035000c0b82c070301003880c1000c0c0182d000030480d00891 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 809623624 1250 809622374 809622383
    0x2060412031e0905010c02071a041a040b07030903060e06010f030b10090c0c05012012090a0c03062f03150301020c07262a010210050426070f 62
    0x445004411a07420850000320300b4500300104062026410114081e2012503c1100180a281e00204264100000c09000d00d5a251451820a424102056185a40c407403103512100c00a100010341c150b06c45005010345886692451031070741c551700c0d010090ba6140f08655149410800060041c0300c01d20307206a00722a0041e109070603c3e103034490003040d00491500900b00c40c5041600d50740040d604084455209445400200908914103003004d2042e00c1c00c089560810604000c80e00304d24500304038154202c01d01000741d88420358940c1d81c0c11490701c7c0c2988100c2c0d8450721072044101c0d041c030208003503d1080344103200c02019401c4e01c0f030000c5144401800b2540518202c01d076100140c9096040c1e88800c840340c8100e800103911504c1c0e0f640c02884c03041c08801809100c00410081042c0400e40c40f0648944840081c8c9030304100b150f03040340d07140768400181184100c61841c2000241d40c003509020782e00991400b8540c1111039000700c100b00d10000c2034004040100100310004a0080780782c051282c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 809624874 1250 809623624 809623631
    0x1120b0c180f0d050d030516080c030406200309011a0108090a020103020c101107022103030a050c0c060f06040b15041203210b0315040f030f2303160206041203 70
    0xb48400200c2800d524500904075124404210046a0b0507901141c0641c0c8180864219078241d2801103509a00490384400e5a1009001050000d016600144d440080b000a54440e00c2c0b003640c0080182d03007044900f959640c0d1500400c10039146007825042200e0320030700e000b1599241c200141a0750f1801c1e554001d04041e8002000480c1c00c0091001c0211001e42c40002d00c1003500c0c0603003602441d00b2030141030744988104020410800f9103d81584401040322020350308640e0743d2131084006180c02481980100030810909081d410188440c51149105241d880395604104042c002260287c800303d50062480c2003522400c62911000e50b401c0307414522002c68400118a02194403124076050980e81c21100d40030403040352000d400c03040310900282d00721680040000c04420078410207803000f40850340305040040200f4803c3d102c4d10b019441a017008014900070004a1001da901d40340d0b150520a800b0060108080f001800620070188920007060345003084d0325078140c0d5002003134603001403680c0e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 809626124 1250 809624874 809624899
    0xa0b030f040c0f080f0607030207020a0306020a0207091410080303070507140f07080303041104050103020f0d020f0a061812030207151205100617070f051303050601120b0c18 76
    0x401900b0b0040e01e046030415080d950303145402d43d9921000002410540280d00005909a100b072094a4616170020040c0d03507002d103141c0301c1100030340c4035150800450045071808107910040e8013980c610154103111040052800a0200c2071318120343d0000e481e290420400d210926901205172444150804c0c0644806010803000d40d02e04400c095000314540290040051030200120246200c1c0e40280c15903d1107030304640420045880c24003000307500040c0301d02c0c0e025241c00c2010b016031500d03201a00c4402c1582004000684103820340e4080c0b400142040810602450000360307000c014810a51446c00c00701950313602075210801400740070716080c540441410802e12510140c002036001d0182000507003807941b6600e07640003480c021280424404020740440c0d0111018a500c1101c04c0c0c1d03a440c02036905071004031202e900400e100c0c6020403180ca0040b000c42e1007481600e0080c40100402d9040c0302d46458210080c000041201c140220140f2503101d02c030800342c035600e4100c031085985952080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 809627374 1250 809626124 809626133
    0x9060901021c05190f09030312020702090921120406091502070803012d0b090f030f0d020c061608130b030a0c1d0303071b320a0b030f04 60
    0x419030406103145039101503209100c03d8114004020400000000c2c40520000c4034083d10685803600a00b00012101c100400119100f91403c2080d810501805031a008042d00080d07683c10003a0b550000b01d80112109004000402c4500449060484401350408514801404025900a00c050302036038035071410b081000303c0100180c0600c0b80b6514215204c0f034203030410716220f030800d0007060303d000340602043c07003d40e128400c0d040e901a400040b50102c0b50070902c81500c0c41d0005500c5603003180d0701e01c441c0242c82c3da0030300145030b6011001008210102c48048004e14241d013116100703025074020000105010800655003200c51340100001c1c2c0c1d21007541409140d1440181e120388170f0a98040113011124603641c1020920445c5595190540c0d016420302111501813280410307455441040601c0006002014491078603003442c980075225556010035008030642d95100b5080040422210300c06003156180c1c0b0741d0304050640344540020b0604402440306c5c400505072541407400040003e0070030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 809628624 1250 809627374 809627383
    0x501090c1218051501060f0e0306190e0123060a1d0705070218040308060a0807091808070302070f08150a090501061e0f090b011b080702090117010b1002030906090102 73
    0x399440380841c4c288003e0000840c031000428004d1800040b00e2100755603100d480342d54030070580c0b00000d02401d400c0d110f00078058411448071a219210a0300d4031242d420000081c81440c2c4214845000c0384400c0140201510388a80f000b8005841805811010f014400d07190b05031001800902e40040c1c881c0c0c41e0660241c1e031a001c0c2e940300941c0145200e008440000c1000c03841b6014030700c6904e0700c103010b44030a001c0101d444054090049a035014200400c00486540c11a45111002c0c0d0f15240442d80107448030300044e481290700350090b1340901000c210007443c1e281644014102e00300604440b80c0b03c0306c1c0084800034090100b20459890320a21820300a0030340c420801010039084240710941c11a0911504047e00e205410b9040701c1040300060003002402003c0d01190141d440d07015807159040043d00301200688250f1701e8100a003c7c600050f12040c08442c00b07000000c88480d40c40baa040e240070300b5901c114803036900441c081c006903130000e6000001d4036060101265407a40703030b8000c140100d180c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 809629874 1250 809628624 809628671
    0xc0d0f0203160f2321040305030c010e060a09021509040b0901060306050103180507060f0c0512090406120209040b1f03120207080a03140d021603020c040501090c12 72
    0x70b00c00715100034000c0002803120409840d100d50384c1110000c9500e0401500e50b19181807054160b00a2107014000c0d40c841c5401504030301d0141d00c40790802c1e80b292a100d1550708003821440c4640c1d1f45411451005004201140e8000011041841929030980c0030500884030366207414004400800c095206a0725908038000c4000d016001c0002e960391440c00074041c00a0303208150109140030440100c140b20341190b00e00d62a00b19009102c01440d1210840700383c00c40310305d03240820001e07200c0040040c1062142c9104144615096600c41074841c040004880d22035001c04198514841c2900043c5c903584c114587c40350700000b803130720f10742d0328650384402940109071030b10ba0752407144d4804000c00014003403206500f05943d007212601d5440350320459403100c080d0701c09408212280c00d034540b120904002407182d05601e000150420100818241e00c04240380703400c40243e0040ba41440080c1854480d0030300410460f0024802499118000360200340031142c20004582c0f69251992282d4030496601d08 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 809631124 1250 809629874 809629897
    0x909060709210f0b04150614090703110408010603030e01090602100b040b041e0608010b311802010f080106120207022403090c030d050f09031e01020c10020c0d0f0203 73
    0x30b9142c094500001c134100112002c03100407415800c2d01b0003550b11485038000740c0d580b00914001c840300340e20800c440c0c10703001001c200406444d064201d14801c1800b011f04001e240c9d00001084050451901800c5a00e04205081c10040800d0301008860703400201c03501e60309444840091851218000b2402510013555071640060030080c8002c40c40010101189245444140c01c1004070f072500d0100d420b0310025584154840c0d5110300e21407012000404000100254801205040020042d000e081d01c0300c0c41c5a048014086400c10f030103651f0003480c03001e0701694500c2d02a140307606011000e8a4048021a52414181d001c58650119190750000d4002c0204900e98100311580000c00c0c3d0907242d208541860346402125004906804d00182c20101c5901c2511070605045211950280c0c032380100401d50b5061040c1c545403000303000d050004150302c81065001607920f5a244002600e010071080009103201d104102449002c000490011108645440e040301d4149840c242203196000b034100e50030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 809632374 1250 809631124 809631143
    0x617060d15060f08070b0a020c1c0501050109020702130b010f11030408070e09070b070c06080a14150102150c0f030921040e01090c0c12110a11090906070921 69
    0x198500959220f202152010310448110316180d0030803085c41d0151018030700143c3e0184a41707001914081d081703401c000c3e0190320358502404d407a4617041d09584081c0d2008103100d500281c0c1400394100981b8014941d807501105119076618100001c0810190410b05810840007858084c0c20102c1401110020007410007100e1415494020104600714251141503403071069800001e40a1132550580300361a4001d8002c209641c80c000054601040007800c0c01c0d4015625171800c450b10030441c160318002e007110500010b00314010380029190416016482104401100800c10450401803c03156200c10b00760105031241c880105a51500d08030f41d0313580c14444c0b14803401140184024001c1e004582c1e030541c91548503607032041c034101211802a4040c000801c9000908042074403100c109407250168600b40c00041104805c1c5802c20030303118000c4803070102100e80c24846103807030302040e0b82044000d8081d00d664102168041e0007412a44a001c2403020b048154105c241b032a8100c809583d50021402c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 809633624 1250 809632374 809632379
    0xf0904050a05070809070605030703110c162607031502040f1403120306031009020109080102070c0807060908150604320108011e0515040204120c0617060d1506 70
    0x80003402e003c42d05100015001e038009030344640d0000c1c00208503034072900d846103103031111481240541030282c000a00000100000c0c400b540c4c00304401406c1a80501041d84a2800c103690b040d003d2100082104940c0d4140a00c1d0414200100359501100c1d13002c40d4501603084e11307200b0f42c03020380607a502041601301c401c80d00254100022025801650003241995886005c40c08a0f481d1400241c96a5406030b120048520010070700ea4040c003000790050600d00c0081756940801c0d401daa0007040e080750859040303e001c209002c010458140500642d040483e1140e003010b52256403110602001d991128a03480407800c2912180c2c4501d21242400c8800c601800001402d241720440721502c1a40c0c024a001c00060f49550610034103c1408180211480116070881801d000c0e02c0c0240c544402d14101801c0c10401e6601c900c001c0009240702c03215008100624140081000c8c43d81d80b0403030510000d000c0041541e00811503250740608210ba4101c1c2c0b101c00d0742004a03044440006980403a480e04201 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 809634874 1250 809633624 809633641
    0x406081012140d0206040f0228061d04020901020309211c1805150706111908090615090a0e0a05060612160603020a0203070f0605010518040510020f090405 68
    0x29058803444007012960743c0c1184100490782c400c01110040c04440038186024010b24244290000a900042c0703810600c404d000859a10390310b0a44c0104042213200c191050000b600e8600b1080584003144c0840c184081000082c7d100c2c4038002c04d040c4142e50142d068038a400e042c0c9044844820280200e5140d10100c024100012011482074408941482c45200031800201e070041c09941d005409070091300700304034600003035801c1750b08221f4102e616034200b0124100103201400084540307403c800e4180150001c00b42141c0310241903500e55401071000c0000003940103a18031903005055940000f9030b0f41d0b034142880105503820305241c00d400760603c420700388500003034103600507070003141d00c001070b074100410a55407603005070315446100b090002e0420500d80640d014201d00010303401170300d01e0481942ea03401c501248100085071910395800050226003002d580c2e54140341070403003034808141480c1d202d2541d10309008035031540d5950005000140c14620a0941e8141e12002d8800d1005083c80c094 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 809636124 1250 809634874 809634893
    0xf1202131a01120515060a11060c0327190312020d060e0601030b01020c061e1b330406020409020f04050411090a06180302120c040b040c050406081012 66
    0x1810b40014108803181d41080701a1107980d002e01204074086224a5801050200c2e0760003460201e0103010b510002100c444400740300e8544124080302065a59103000b00100c03000001c8a40c0c0726031480f0242014407c0404c00042d64a44420b06589204214009103000c8680940c81c0b90786800303c0f4000718103104032450b03030380086041d5924411108181d80d20600110201c0d00440c041c0790041c0d000e018007050700d00b00380000341190002003404910344034001c03a119140398020001c40364882d001103400b40140c8828482c0c004104c0703580440034a02d405020f040103550104c510f0901040005102007010050342e64121002481c4411055417158060003101e05507800c54400c00c1d00071410405a00a03090441007268507030b043c020002d42c0c01d1402c1010445010700364401032003010402c1080400940d4503a000c10480751156002480405511801d001c1607842c0401c0c01801542010301c00c000d0560400203444c2917480701d10b81601d00d031703a4031110122000002e9014004000d01a139072181444074220 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 809637374 1250 809636124 809636171
    0x90b151f030504031112180f060a021609060303050301171005180709060614070303090501050c0c010b0a060906030f090f03030c08010608010305070b070219080d02070b040f120213 79
    0x125514003260380395202d06c3c0ca40340006808041c011042110b07568101d03044074441c4442d0006481059805c1b0f040700400d5541d48172541010142e4840410800e081000c180e14002600c6086014070400d8030b5907a01034100d0006001d003044680702c1203100c0e080d0000821111a2482c00c01c04140032a0624002d800141031072201c10748458041c0400200b168032450150000b20380085d42c2c0d868403007008802ca02c405030441d2008a0070107031910805030204000740281030042034141c0703540e541c40c0483d0064508507200344402a001f0004000c042094a40049500c3c0c11038209080100e4420100340c889001441102401130180120051800a1540c1544440102d800395100c1ca03200741d0b03c07020b0079101d881c3d0034400140a50300070341051100034404000342880e01c0c800741c03442540812000f26024503590720f8002c00792941c05820a180792030b90401981b401060300c00c076428035241c1000311444245125003e40022001180b2003c02107441c0d0135100510045115000c00c0310021320840d5003541101c16 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 809638624 1250 809637374 809637377
    0x706060314071703071b0e07031407030e06041b0803040b030403020601061812240b040c17014505060f06120402060408010606051b01090b151f03050403 67
    0x1ca40c04904070f20304103507500e24020b80400a5041c0100b030342e51900002400101d03d105210025000100d01d040d80030200e01840d02c0d505c1c0421b508280b602901c1440c040140703000d00305420301c5400304601d80007288050708a60403503400800480c29001050f14240c45a004031005d00c40014002100500d001c00f0714021740c440d60a13100166603404048503446004046e0810700f0710040c01c1000051041155000d10900c13170107440710600e04010b60064100580d44c1d80600064a0300e0707071b0711503901d86803040920301c0034642021901402400007150191105024640d10005030b0180ca401c00031542e44800740000c00002c0d12107004220300c030160381907003481803140c141500308000b003083c51400101a0041200142c6128142900800514030180c005482a81c126a0401001c03038507031002c3c06088081d15644c0c80c0c0940d01c2c0d0442400c01540c590703414520b0442d91400440d200054113506e507058100c461440a4003c981c1d201c00001ca901c8540c2030103051141d080b9200c0200c15405070070441c0b00e24080d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 809639874 1250 809638624 809638633
    0x607050109110a05090c03040c050a06050a0f02071409090a0803100e071b1e1b0302090a0204320301020301121b03110d0f0b0a02130b0408060a020c030706060314 71
    0x310b09000c2c8100e41c0e401110740c820310505c001440815548041c50b1310038041c540714151507a540001c50344012a42d003001000510004030700c00e0403500303c0c200c80003c901c188014402e240c0761034004007000b11020381c441d104025a0010810708032040100c95031091b0040c01c05652030500924084080d0342034840c3c900c52418503c0001c40c50f42c06181c0310441900c003c410100032181b00c0d0346004101c3c3c2900b4524410b0b00540740200e000c18003405128084210f4a401c04585601f940100054030030010111352440d4010001072000a140300380410038842210809003090910030301a0348000b80c844055601507101100004551035000801000c0700e00980031106201c3c0d04042c12a20412a8000138010a00781d02c505a0503080c840c154521181c0207e034422003003020703651b900b4031801d001e544603803410382c0101d13101006140c0c00c043e4900800305520624502850f00c00884d4484d5001031240d292254080f03500541e4081c02c2c82107030300c01341d48510304020154503840d00000c0ca48802d0303840e6496100c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 809641124 1250 809639874 809639903
    0x60b0315061f05030a05060126010812090a2106050f1006020a0b181006090c0e0109151d0d050708060c0a1b02012d031b2c0607050109 59
    0x8216201e0050104a60f00c01e031840d52040d91140c068136015007800c1c10000c0698400840070050300201510000504000a0a5242082843c94030002c1400c440000d60100040e9809a450222003002c40b440240d0780c0f0038050141010581641201c0e10141081e400c01e010010803029148003d882041d42900742c03181d0640f03610080341e403050146030081400c00d030080428800018801d41e0a443d40c0070b041280c040014514141d01603803815408030b84e00c0d680721400c0d40905500070080c0507144130207282290007a4135003040351481000c0b001d0500e051011084007100d0105900400c214841405001d0840e025040e10341690f458200d441504d0b400d001e0b032004112280b01c0340301205c6040b01e0968451750b10601c030042122425680351400c0781400020b1061700e421981c1c19501d05114445584140010940550043d0940342c0700f4030170b0505407208414a1044a82082e2070071804545a40815101040c1010007404070028088042c1d001001280420410105402c51170f8100d02c101d0b0240d2500c507 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 809642374 1250 809641124 809641159
    0x1020d150b0d050a0204172a09040b0903091e010306090513060b0622031a0c04150e0402040b040609050306010807030f03123e090d060b031506 63
    0x88501940d14001e00402c5000a0079480b0b820150304002c0c0050014034060741c0c2e42c110032104900d600c100d0007a8000c11001d072080301350164620800031940c980d07010701556400000340c1040340180010860500b4801081e20407800300250b610030303080906400744d01e6804c5000540b031000d296000c60f0000742454004110f0586078091140540a0b4080c1111600d60680d91440030f444168030050701b00c0c20920400644903a825446c041710398240418000c0e0a055041403603003a03829012442c4010020020302000c0c0001c1021181200c1107415841c94540a408044501c411038000d5283c4c014004180882c10b00c40160090080b510252500e03d0116034440a054451500b48a07502182c1c004a6080001c10920b41c030400703003148a40b401d8a4050910ba840400300e50540f03819441c2004084a0b00c0242d06008031182e5020402480300c18051208841c1c1c1c0d0380a109146055000c1c03a5542c07c44410040e1541000750701c52402019a544401615007410100300304507001c1c0c3c4514a21a140408030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 809643624 1250 809642374 809642411
    0x307091409070302011e211407020d0206060f011b060f062414040b0a0801140d02030c01114b0307062d052505160614040501020d 57
    0x16031381a11440502d280b088007503044c1e040001314000a1250042c2c07032940a40620030328140c00e0205640014070720411850700e01c0a00b00003030400c1c041d03500015544401c07d07000100103a001d001242c2a02c0c88030002001260040c40d00b08110f0b07204c0000100c10010040f194101d49a03120400f40c0403c4841c1d070f51441c4020310170740c0c00303071251b422485003680b90391461003205102a45802c000c1002d01d019600c400700e0081d54030090303021000400c64001030007109814101070308807140442d00c0045120300c9800007510303000d1448001d41030060f461000705080c0c00a12404402005001e00c1e81c01e403503030301403420940c1d00d611f071104034020302181d8052420320041760103d42610708040045040506698485000701201d41c0d0700960350304400c4001e401d940c110002d09111030015000858039007400202081d4071000f01048000d4a42e64400300108640e010040d1040480e4400034038102261034144000204015043c4400e0011141c04103c18001c054009001d1000c00d004108090301c030140030840039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 809644874 1250 809643624 809643629
    0xc0f1401050915190e1207030207090908030a0902120a0b01031b0e010608040c0906061808070b120a0f060b0304141507180806070c050c091b03090c030709140907 71
    0x81c8000d4000c07401c0003c0e40d800301108038902d07400001700301e00d0000506207464028107503100c0c050b0000035540201503060044500a001c000f00038050000a43e407040301c0c901004046c6101d50350350f1502c03402555601d00342000c4680122003928005e4401e400e0000400800340001d407001105c004403025102814035040040b00c03100112a922a4203024007101c4d400380180041e15140c6985ca4003040401c01e80c45100002c10b0703035848025040c6103000b01410406103d0f803045c0d134240c01103102008020704d1101154031410240e034401c50280d582d541407400410810400c094618070302880441c0c41038241004500640c0122000d8603035011281080c1d9075450525980000782c8690004107406a00920940344107480a0f10a05241b41c2c8a602051a01300e00701c545000103900d09021409111007402181c482c01c509881d204d0a91401c8030100303030f24101104003042e80601c0000014051074050146440c000002001d40320b0440d6204800f00c00b42c411040001c448050074000300da0704400c0007640c4001c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 809646124 1250 809644874 809644903
    0x206061207030b0705040506271905010e1c0606240207060c020303070510230405070521010c26041106031909050d18030b06040203070c0f14010509 65
    0x1201d41190360301001000060040781c1030010601021030182e03540070180c180c441e144440c48224009102441680b060b030310801a008201016100c18140c00e07070f14801e81510420700303080c80c099081e4000700b01448200455060110850401501000705580000085940c070124955143d4514450820350f54a014040c402590102404000d624010140c0b0340b403107400202903d08001d166140e4034201611103640b0790003559522402115440542940da498040103540301d003543c50b040d42c40c195940c0e198000c0911605070052112400111441c4a40b10040310b00000d00201502c403c029190385c2c456400309920710a81d401640011541c554400c1c49207400000d280e885811403c24003031240e0000d48000c00808408071038696159290003400035491041c801000e41002043c4020700c07209070102030300d400369601003040005c900c1c2401240c1d04000111070050792505c5640056810201186006240c01c0c084a041400e000343c3e1050210000300080086c40b140da00e55060030349032101c01d8130140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 809647374 1250 809646124 809646133
    0x90306111e180904031103210a020a200a0f1101030f0203150904080c0d08041205030702030d020d090605071215080312040515040803150402070809060c0a0c1502060612 74
    0x42e00c40c5403102c1c480f9000780c041d052404004031500e000f1401c560004485d19411318804042d0140009415043c0c3e034089800070f821400d02140c148000d01429072040c01408624014800c80c4202e002408901710059011980c0c4400501d02c2c078142c8110002c05105602103450b08000b90030804581c000c6034810545e0095100c1c0500c0c58604001c14444c1c050410780f0550800e03c00f810b0800c80c10006103001d44850348819040c2d02c1d182c580422651400003644040200920034071a0894000040d01d00b925406400942c0350030f10076110344000c0c1075162016001c2e82c240006d00c01d4075904616116480b690b038074014012100104405050600d003441401d00a510811860410b695002036886e0082c3c0700d8820745090056140c40c40d0016403042da010b80c1c82c008000144030b6140d4004020842c448425542982008800d031117450a034003480001c1c0b800742000080f0003c03410340501c2100c4075180e00201c1d00400030b85410700d10340c00c0c001e01454000036128500c0480d41d60719201c21030082e512000c0c4002d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 809648624 1250 809647374 809647417
    0x601060f1d100c0f08030a0b120a17030c070c0f090e0715031805010903020616020c012124050420040b0c10020307030203100512120307090306111e 65
    0x12501441074a105588510702944813800040d080c80080d400b48055840c00320f01d02e0814401c004c006d04940000403010350060000b80c0001d0128507903150801c100a2101ea181e40d10507000760207910508034020440c0203694400316900441d1800c0b042a610b0000c420002007903010800c540d84c51460141d0b104501d00120400036082c425008220401c83c510090100364280d559085d017581c846000c21009604001c040014006d09602130444e08c03101d5100800c6d000038000b0001e00780c000c0d10007180c01384078240096410359089981040710f01d60440c45449107414464007800e400315180340103240c0300b541070038030a0b0701d4403910400302e60200c041058014909071901d111803141d50b1042e40710084a0085281e2030b2801074591001c3e40c403580e03040c1c80143e030382c0c0741101e20401c442129402c10340c03007040700a6001040081c0081d00034581011480035076940d845001046d100046c00d9840181458108421300c035140301c8140180c110900312800c00b5000c12083c03000c48149000342c001d0f00106c900c4c42800b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 809649874 1250 809648624 809648627
    0x4205030109230c06120103110303040b030112020a120c060201050c1e09010e03061e07210510150c06050a050402101b0807120908030921030405030601060f1d10 70
    0x10b90082030807072000c442c1c8402c0404041401038001078480569100b07560010010b101c4810f050850014040380a10300d0300d4203218690300e142c00103003e080301c4001038500341c1045448511881b0041c20b082462090140d0f014503003100d000d015409100b0044d400c2c8000305441e008146c0035500c40f501d01424603188103001100c141c81a410203652076040102c0cac16501100707620244030329070003100010700300d40010203011522100002c02506240801120002c3c0051000184840c101c40e284004c00215003511850be040c0c044242c07035082490001c0d805d0907000800368009410561482c4581c0c8188011354850302071004170f0360211000b075000754920213246089445030107403070050390b0010010724100b1440d80b6442140e4001107021205001e24800c005149504903a2460040544d04011494080d0380320101c0c2851250300c01c80f44050194443c00903500d07070306005580c003a00005d002c46d4865a1754060040c40c6401015403100484e0804280b0031340c0740e558503151180c012010301441244e03890106c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 809651124 1250 809649874 809649923
    0x2030c0f10111002040807090c1b031b0503040b130f0501050730050a11010b22110a020109020a0b0f0f0307050d140108012d4205030109 60
    0x4403510a0054040501c60b0310f616101034805040110010004a4180500340c01220207105010702030100c40f000100b00105400401d100596051900d8185107181d0843c1e030f250030508282c020864000414003007681d07007004018020500c040740400806665078408100b00700d0f4607004050000300c0402040b000b040d880581001e50000e480011800c219602c109907038105d40519508000600004600190540c406036044030401514020010508400c00040940b0420328040d10642200c1981d1a680145a8044695045003251980d5120b030100c07030090082ca15120220b10911207010080f030f5a95040050b60a0450b0f221070052619941c032004090f1034100401d0781e010054108100580c10b0038038000c80421003511000c00209504048585094070a00b010b00910780302c0205400c454401c00600e42d112040d0300f0500011189440301308805290b10648012a010b00c540c01c103024080c2c045d0840012030407107035007446402c44d02c40c020035003a901c05410281c03c0000c0350170203039401c0c41c01c0b03103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 809652374 1250 809651124 809651147
    0x240412080412030c03030c0e09010501030e0c13050f0919062a0c050111070c09050408040e0f160c0f0303150f080c090601020d090b0d0f02120402030c0f10 68
    0x10303826818180d031441210b006980c00642180010604e403442d80030182c144c0a140c2014080742001d0903000200030100310800014811141095164060144003400501c02c40c1810301000d03000d03141840c00c070400380c0060300003580d00034062991080040c25141e40800c02e0f4000406100c1076611040f200d44850740a801c2c0e80c3c43c80006003600401c05590702a0452001300c3c00304007034495904102e200d041c5103084442e804011854000200044400140c2c903210b1030042e1a40000005841c0c1c40d981410030440c000c5400c1000032040c050188a8014007030f901441c410a50071030080f20400701030758129000c2d40b071000c0003401d401801e2040c20010303000750001e9150340a035010f00040c29542c0c4006103242030310b541c004c0c55240c0003940c0c980c680c1c0c241022445c0d8000c80031f000074a185e262903c0c0091034810284240301c0300110110310712402d05600d130440786010310254015504c0d0204150708092096042e1000c922174070070610000c4480c10000f00ca1180c50742c0040041081c45183d281c00c0e1401401c86 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 809653624 1250 809652374 809652383
    0x50a060206040515100e2701050c04060c1506060c050c03010b09040f03031b030609060806040c150203040324050a0e06013605090d02032802010f0f020306240412 71
    0x180d40106da81101d129045200308210941d4590024410318446184502c45c4924152641420308201000040504941c212a400d1420103401041400d1000b804c12507083c4200105080410014003142e010100c1203c050040f070a48074107942174000c00d42294004102e480e0000a00c000007404141d4584040000030b000303003004201a21605044480200c440c070800b004a59940002c1c000d03050716115a8019088d545c0c0108114200740d19101c0e40d0401a11030136513000c402c0101070850620904c152070080d9803001206d0704280d121032004441f44152124071111070701c2c1000103110140207024840d040130464002e400030741d00f00340148214900c21700340c41d02051444d080c544030341c402856581144006000f8000740e0703810701c40c042d641031580038104a01194000d00c16006100454a4105c15010003601414034035860540c0980c05000070703079441c40c507980c501041c0c08039150030b41c1c0003940315480446800c0c2892001e01c1908491080e940101040c3c4a41802b0500000c1d1086801151007800f9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 809654874 1250 809653624 809653651
    0x1200d200105010b18031b04020703111218060a12050604140c0306040c0c03091412060403020607030f0905100f060302122407020c24040e01050a060206040515 70
    0x6000c40e050940d08282d202900038040000c550348244100c039040492200c0403409010007032100d0800c00c0c910b9040d0582144202d900190303040c20903004210300780044002038151139013401403001991282d081000032000080244015040600d0001e00700c0e00b42c2c11040d190240140707002090340009010061a80b50080e40c0c80004541e098100c0451902c10210000069078a2a1040c14002031310302041c2c070700c81881640341c808030003e41c2100aa20541b000344055060b8549101c00280344229840d550744200c0c060301d002d02051541c08905188100c200761014803919980c940e0714803c55400c82806000380e00310390500244045550043c040c03034002c10b0000300740715849400068220040c9014842c030365111008021403810356548840007404100890340c180c1c1b525500194903041c01894140c4506008100e00ba4501c40a92136107400da58221070041d2030f65100d001e01c00c3c1c0300c1b80a0040e00d01c598401d48000030b00910009015100d00d40c8000901301c4c8820312042c190f03a556000d4030102c1c0c0c1a91 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 809656124 1250 809654874 809654927
    0x5011e050403120c051c0204090b040209281701050402090619172112100311100309080a03060518161103120c0414030c0a051302220501200d 62
    0x102c0f02a100c0306c1d11403030100143c1da079281003021012601c00c25801c0d030150740140042215a941d008101d000496000c045601c1e61040d002240e203200d880f41c00640d494003d0881820041d2015800680b00700d100b51001c40c41078961000b000340500c94940e8000361410b0340d110074000c03c0c140304170403000241803000721900496200300c000060440000e00350125200810403205a403800390201d0b4100001c1e00b40d40c40044c0c00c54640d402c40d050640c1100d13000f250045140410b0074071036440741900325001200945ca82810040c0100500000c1c407a5510800e050380c0480c404041450226002e460a240fa1540050040c0d0040d40c16611003002c4042c280400d2081c120078000841c0da0b28825200995026a12030401e079170308000380030401c1142e0080d4080d0822141c02d8603042d02810035160221180041e1a0300b041c0e205000e445900c13940407000745d070245c511008105040c035000581d202601d40d0b020604144007400001e0340748010404590384803d14010f115030280b03004e03602e030300c1c1c00c3c0903144548035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 809657374 1250 809656124 809656147
    0x90c071106040611060a0e03070303051509040c090f021204020f0102030d02030a020a03050c0910140c0f0309040e03130e06130203070906110c0114130e0405011e050403120c05 77
    0x400650040f404a540c0b803006402c1507405001c140d034050850b0208100e080d030700800d00c80c1d40303014120004041c550380b00302141e5400d40c0c4440c0044500001401014180741518200c0405401c9114100300c0508003c031020303102e001e0f4006d80c0c2454009844c40022030b5665020009101c001c40811419400300b0030400303c1101c003600066114210340800541d030740d000798000504a43d802060701b0607402c414000f0b02c1d11640d0740700e8280052895483d14400c20001c16070111a103106010003410588250201403558100100142c600c4c040c04690402c0848603141c002138480c414981440a611030b031100034840d8058400c121904424080c041c03040389080d80507003c08992080d1000c2002c6901c590041102d554400540c0740c4200300140079000c0c0040345400601a049524120140c51074003040c2c40112030075a1030001e000b410203985802540c2043e0500710b0081041c900c242d405284645000e6000e45007a009043c0111f42c5075a4900d980c10004410800800b10744d41c8180030008100085031007807 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 809658624 1250 809657374 809657377
    0x50f16061404030504151e030c0323010806130b071b0b040f1104270609020d12030f060e0705070516140117070c2013021b070302090c071106 62
    0x81e8401c0c2c56055499040c02968050561b0326a84d1404000a8500c034542e102c407501ca280c00030300020708002c104200b64180580140040320003c4803681c03c80704405c0040c8440144440c1200c610700d00340c800710f4541d000c201c2c02800302024041c3c08400b071400071640340e034443c0a10b6500d481d9000d08092a4003001da40b184220541540c06440010103040000140207400081750594041100d040001e160510303016046c034a480c103030b2024030b1000c001c400b805014a581142134042e0f4000c02660b0040403170b00c1c01041c03403818850010002840d01a540c103103030900c4c0c0705900c20360340c1c0880c2040f225a61014100c03243c2d80602000c0325540211b407070705c01500c070161038180050701d0a00100380400201000042010402510420300101c5090034017442941108025500390713048841411045c1c441420403010070005450180c00c910400d00002401901d540035003000360400b1504860580c002c0203555071000305010281d4440c0c030007000710310101e020100038060fa5200d0112144801026400607109 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 809659874 1250 809658624 809658631
    0x9031e020a1d0604050412030c020f060a0507080703062909040504051b0d1e021f020102090a054207060e0f070305061b04090f1b050f160614 62
    0x203203104080a02c06480040d000710740e100c3e505803010002482d26486404802e0700c1900107106142e1740d212500c000078030a1102c601900886030480c0d0950620844100003400100c542d0f1000401440203e0f5086100f80104000c541c0d500380c0401c5541c910b00b00690a140c01c48109454070001045a28059192070280e1413085004401070410134103080c030803ca00384886903546211b19022000311740051440381304084100c0110751108240a002d00c08113400c0508680311120782c44502100600c000c0d4150010300b02e070340c8160b0b01456110350314014081900908008660110140c1038401c00c00c1d4041221800d09070003141c007003490b881100d1242c841076072080c00d041c1d030840c0c0c4524221000c01c800b0400c580a0800381c6000300b103c1c5146880f10340d02c6280c003a0110b50003050346400d1032050100c01e8142c178041c0050b003404108071540390300c400001385810f0f1154481c40c40f095030b1142a150040060fa42c10b03400c11100185040d080454048007a44400011120140d617524507044411044a80510 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 809661124 1250 809659874 809659889
    0xf06040207140c10090305100507020102130f03051006061706010e0d0f020f06040321090905070f120e0318041113180b0d140a210306090c09031e020a 66
    0x3c0c50100380e0910880c2d205840d001c2c8240400c60104000007500001e03400b414001c0c60314001402c3c2c031030b00000ca02900c980551180046c031070600c0410240707a040c0142e42140d1250080700e039050304c3c402c03201040c0c40040c4105404a1488480ca01c503540000c0303102c3d41d0294051602d03440c112141d00008900d51040d003800e031a0058400481d50440c05c0c550004848400f0842d030a6050a1840d80e402c0703241c1e42202100700c03035503000b0300c0c05400390750080341010081c0c1004001072200f8a0300d0304000700b41c60044031040002030821000d080d0442064882c0901c031121003c040d516102c095801000900c490400480d006641c61048010b006204005082400c1d403010142d0302c500c0c50b10000b0428610088a500c0d161860035598010543d50b50000503006640721004042a0050307040a03400c05030301c1d80000e024046030a0141e00414070441c40600114440c0e14100400d0340c44004c0d0b4070072600141341c0a004980d40a0b000d202150300d00d62021050301c1c0307000001020807080e40c0442c0b82000035174001c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 809662374 1250 809661124 809661133
    0xe0403120f0c020111041203050706110708071203060501440105130c080708130506071e0809070308030c2b0524130609021b010b01050708030f0604020714 68
    0x250b0441e03080c0030b000310b21520101014200341c20202d80406011070799200606101d0006401c20811400d50001c0701181d25180f40135884108500f800369880e840024110307400074040700f4862000e8007038440d5000b0344406a40e00d40289941580704000c800c2d61071807072021240360314082c0e07071400c501b05458640b034202d000c400304141d40b41005200e020f079000300b80440c4403810607412072009039010746c07210380c81070f0580f03400665600c4604030844007d8540c0b00290090168070200b0810641001e0300c401c40e103150800043d10004512021511040300362101c4080d600a490b003080842c2d076100c040d40e004160300c103c140c035244030505c1058003440b17071381000800041c5110b0004496200c61081e558854216070003204604c21410495150f800c3b80d20715503200d070f11213200c184819805a0301202c080e0030f52100855a0304070030300c841103070344d0845007180d0303050b41c20040400314079403284050f038a00384d9000c11020b045440d41312525034000c03130040c4010f8001d6400c1c4000c1e00450815220300412032658800390 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 809663624 1250 809662374 809662391
    0x2c0a05010216031106161412040c06080105060f0711030c030604030c061401080a120207090c080f1e13110a06051308030a1211041a130503010507090e0403120f 70
    0x908050302c0318041c4072180c1c10170420048940d00020801d1007641092a00a89482810820350403a0040102078031400c035004042000b04481008030f003099a10940340d07121580e03a02c001700140c90cc0343e6204500107030f00612050780020710320706400d1502c8100505585c480192900481c0c5080c00032102600041d61032161802400840d12580400900902d40d10340781d0b60420900030758964001d41c00400c18410404020003052082c4100b0b006403054980500902d8a09880144040001d90702c0362944580e41d008078050b842d1250f040113089401c6409214183c4c0c4500c84a606003072000300a56102c4d141a11030714450341c6100006014084c9901c40030784404081d1503504003a451a08043d545500401072032600c190484540300b0315940c0c1c40c10100c0c140c010215100b0713503800f40c0d50059803002c0031071000c00f41ca0302c0440040e00b240c580c1001d02c00285075980081509980d426141c14012440c0620b00740f1692058a81c40e507401070080c00c0c040c081002c1c102181d070071504107102019041e960b40300038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 809664874 1250 809663624 809663627
    0x70807030e0a0e0c0a0909050702010903030f0203060f060d200304030e010c0203031b01021e0909070302040609090e2113060804080a2a0503070b0105042c0a0501021603 74
    0x20700303600c00141c41c025500d41c10001440510079016061541004001c500003505a00c508003690113080042014485800d00d03000281c00303000e0240084011900300304000124503124030980b07204040090003003d80744d00c0c03d018041603511445122800c2030300e941c1c84007010002d6071000c2c00e8100107400001d981e4605418018626280c201c641030400c80070820000142e68000290b034216003042c548032419420b4002400d009110340000c071203003880420700032506142c04401502c81d80d04165001d03e059a40c0c40130403401c0340700e80c1c001d40c1c0200750400c2c0700b44031811b070320b0f840300d0005483d450844159a040180c1e00141904005c8200c120103000030700c59407805040440b032401080d50b03040074407060400b41c1c0ca011142c000c81005074200012210000500d008011016410490100183d01080d446003041500d0b548081c00540d01c40d10300b04000500c0d410248501034101000104001c4490203a8440045404540c40c90001c58072403044400c000ca1420f1004040c441c10f003440418081225240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 809666124 1250 809664874 809664887
    0x10903020d0e09070206010308160f0809090f01080a030521040b010302100e1305060a18020304210c0303090c0b040801090b010501050c030a0311040e0412020609010204140609120307080703 83
    0xb07845010b01c0145081c04811500040c1daa410760350300c40c02c655142c0208903c4007211104503000035000a004a01e00018444c50f00e0040c131180d10240c501e2001c07546e520544042c50074007803144800546c8130b181510302007885680981501c0d08100d00b1030103000111a00c10317815100a807402d840101483c0010002c40c80e018085200d2000103081c40418810308000240c01c000c0c040744000b13003031921480020402e503a40000703c40908001c1120320090900a00e803000290811102100c8002d1816906865031940c40c0382949120030a07030351003504000325a01200a860003220441d411a000c82c800316400f182a0003078409401e25000000700c421281c10b02030203480c03047e0b00c00d42c14081c0402190000e1035000c0b084401082c440e00700800c4100031410b8100e52840b0310750100c40c10344800c03820700081040c1c6c08404507031544290b0848404e41c80310390340a8200d200d64450459105110b400128240c05d060024117504d54000300704000c40c0ba00080e2843c155803007604119003030200000e80000b090340041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 809667374 1250 809666124 809666147
    0xf1b03120315081c0503040809040204060c06151a0d060f120201320304031106070504061e09150207050406080d020d180b03040f05150912070b0a0b0a08010903020d 72
    0x104003014260307068a200310300e44da01e140d00308540000000c0911009208175550000d01420441d88c50380e0310740d8020034600018504031112403e0031041c07030100c44103c0740e0b80141c480380480101400403030f14603400035034889090403001c070b51102c0300007a62010092a80380204210366450304000200d01c00100501d80c0030001341d0808881c002c1c2d180c240c00301444071111300f2401d5440a6034984807030a080c1e40d04180035130300304041d10400040140d101ea004010384211120741d1a1b03590b03060030f01c682c8814084050740446000800f5079000700800d0f602000102034001c2d00d401541c0075507480307101241c25a5201d40141002e984218540c88035550304000c541d50800652415a9014a90100c0920500c14920030407103e40350110114040c0300c18281480b080d075502000310b81d00c4004420310039525140450300d401d2580218140d051070300303c800003190f0140380d11020500056444d003032940b00500d0310031070054000a82c1d08021520003000d10510000c540070b600100802581240010072008242 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 809668624 1250 809667374 809667389
    0xb090609070609140d0f0510140901020a2f0307050d090b0c070e070e18190905030909101206150f0308032e06110c0306040f1b03120315 60
    0x22000c0294020002851401c05005c40303507501601c0990804500003034032540090068043c40c0c2a4038203001d12640402d080c00601e1100640c159507907030a0508038010000c100c00440c2e840c5042d501400391703a070008494600907201d444003052507111803601d140c00000c821905035020203228461240c0001240f03000700350f05403050b1b290884c020842ca485d40403a210303c01e00d050101000c0f58900780940c10314944018090800e1030000d0100d171034505180030903a00c05860061007035258074008124000c3e40c0b00e03150044025880c1205000600a0030365009010803082c0d01d4065001c02d80c0300c03100c0b65020003a400741c400450b035080ea040c0414100540303540034658541c144101000020290740030f80c0c0d409482031980c030407944854100c0c005078030802c0c0f43c1c101803901628808149a5048803d00e038034406c0440860b00010304400c141030f66030b00e080d070b0094a41e100c41080200000c100081c0c02040001202c501d17186550360740d44809c6080e401a0740d01e00403030384034200c440e030030125008000010101b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 809669874 1250 809668624 809668637
    0x1502060a0f021b1f1503030c2d14070f1205150702070806060607121101061e060801051e060a03020708030f01080f010c0e01050a030e0703350901030504050a0b0906090706 75
    0x8504d4948015030705d4440113044c841c40020b407409101c95003000c000f80e211652004002c0e0941c9a0261040740b003015800c07156458258a084212100010180e040e40d40404d40100c045080643e00024910700400840d078a10070401c280e41e0100e81c440001303000f000140c00603c2c00d94200701c0b11a00303006000f400c450250205012100c08510030708051584545039091596510b500d24114501501003900416846000008104a2403d0680c1904102c401c6680c0340002c590300d440400041050041c00030381c06d0441c522020610740361010042c001c1600a0400600c2e24101d40c0e14811280c0040381d40d11912403ca500400010505004080008a851008111503210075402810317100c03240000320b041000128003110300c0f81c0a948240711041100c81250305c110b41c2d9240002d1009588648120b01c41e64500c0e0260f1112041c00c03280c3d0454007400321440c01d08035040c00440007401c006100784c40520482c0c030b0307401c00b080390000b83d5409510300381d000e402a0301c0d081c4050b034034280c050741c4000100000e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 809671124 1250 809669874 809669891
    0x20304020f0f030a2102010f1104060e182706060a03061d06010e01240503010326072a2108040e01140a1502060a0f021b1f 54
    0x169050070400840040301e1914403600c0d4000424940035610030000c002441403040503661008604c48881020329070350092003040c200054420503030300e400c450380282c0c080a000500500c0e0140c00a010800b034050b00c5002c2001c0400c900c0440f20400755000e0100351810440e00106401c404d040301030700c5000c07100910300c0d030030308002082d141c1c452031001800c1a0b40d20900100c540305041e002003000f043d40d0003107824950b15060b0440b00c1031420701c200da0b00c801c12108058500d01c0d00102d88900850561160303400d5a1a540f10100320241510a64140701c410841e0910703011302c03078000b400106000e0403c60180c44007401607000c82d810419a07003100d80a20100c00c01c6402e102c00c0d1842400034941d22150141c041a203428002130046401408004003600b0002c90f001c41c40700c4c1c101c0003508040f030390301c025266202e801c20024207214906100680000b40090303c2e440e01608031504550041600610b031a2800764615020000c1ca074400c50940c103c00c01d074004103040134400854507021010200701001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 809672374 1250 809671124 809671129
    0x6151318150605030d02010b0415030317091f1b0e1318020306160e010c080301090c0c06020c030703030b0f0f0108101a09181b090303070615080f0102030402 69
    0x210000300c0200142604401e40d14641510340000c00204400341c215040340c2046240a4064017101e10803600a40c9407488010f40d01784842d0384c034003c0325090340f100030b9071940d0b007441038008580082c140c81d20f5104521250315400203d0751604030203014888000388116220000c0803001d41c40401d03010070411707043c0e000d05d190340da0012000220f40310010b00080c0740403452001c6640103031040c006581405041c08222411207682890b11010720b1030b65071503091000d058019918406071420246c42601d01b4001401004400d60140341810624100390081203000e82e10403090b0784c00586200c010360000b041084c00c00d80c0501401c20440c10031140703110081e4003000801d4042e1480070442c0e0400c09003802082c0219200d440c090302803c1c031244c940c801c0c1c5114000451444e17000300d110034061040c002c111f0741d0b4600c039000c09900035a0101e203200301c402c0c44801b4a4001c0d03001044101d81c940070070801a00003c0c0517204400c6100c0603045400781072442e00c0f006e00d040c001580c40714502c5034010030410005a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 809673624 1250 809672374 809672411
    0x4150801183801110307030504030204111e0406120e0c090c120411010807030c020628140402010e03160b03100e07030e0c030c060426061513 62
    0x15903008400081c01d82d80c06100d000041c2903900d4665000000482030900d0302c4801c2c00c400b0300003000b80ca51007010984c0084a80c0e503407013030505c00b070000740d014041840146016040101940c020594550a009291544913102c942c944014001440c1c00a0100411900401d80d449486600361082191064040f80d8580301d040000d60640319444060019410b02c40034401e5400d007050a030b034082d07030616180c50f021450106403120780e0b0110f0358040c0011850742c440e00903090000e110b5800b41480b62030701c0302681072401c20a00c4880704500031030351103504402c4a01c00c440c130107081b03032005041904150002620a10440c24450b009420142a411030624454150b108650b80784179188d03502d5561380b00d2082c1c4c00900d600143d070b1160142050110207541508404c4d91000703480705540c000c0b40244201540d44c0000e070102c2e50400750620013006000256545510b19480458a400c50444511405402c049048840b0724000e0703020741c0c0b50350071400e12201420800c00e50400401144c00c101c51001d40a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 809674874 1250 809673624 809673659
    0xf0b010c0b1b0408191e150905011112040210030203091213120501150e061302072102061b1c0c0e041e110414061b100204150801 57
    0x2d01c010380241e142940c003110101c800800c243c3c400e981c0d0482003285007440501d00742500381c5001340002100310079500c1207409495200e0b480184041000009180100a000207040c03e8419550700c030b8103500203500c2d410050030803d410511202e21403800c2c0c030410840c160302c0003080c801c051041c0100000f20300001403965814100003102c80d11680c4c50002c4008007800d5403c12065603034010441c10802c0815000b8a005198981e8901c283ca0b0b15000c40320040d8808440d41d40e80316010781d0600c20f0001c0580c0c000c010440c014090504448100140824850101c00c035404c0164840810401a1501d00d403500f00f5040803004680e02c1c01c0111040e00d000c1000c1203105e2400c080e0b440c0301c0c40210303034003d4990319070001000e4001d010020009142e0060100d891062044080c1840075051400c4c964201720381c20b80d041100c2c0c15a00c1d690a00c14420145c0218104189120210f64103248403402080354044002d440c480260350381e82804a01400f94074030150710000e012401005209418601504c00030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 809676124 1250 809674874 809674891
    0x6090d09050108040f1703150d03080c130e090f2401051c0b0f090c01030915020715020c01050a0b04090506070809011116050c0d200a08030d0f0b010c0b 67
    0x30584c5480c100300f503002208150051000e841310546596080419000d50710507039503040125038901e080c80c203000c03204500c82401000940c80c000010003510301c1c0c902a00001d02c482c0c3c0c104a0850326100c030510290170503220038685074012417640c80710201c1008559001c89240303241074400524000800215001800384034425140040094001391034690750340e030b0340340d0802e0446490703042003a500f10710010151151b0f20b580c090204100302e5540a401145805588400c0a9000a80300c01c001c0e002500194001c503510302011100362241140c0b8009403800e841442e00002d40c50801c034922808490700d51102900031410a00c0110215001080042c1d00055030300304241c0d1aa26441064010720b0424000380f81c090000c11034042c42c4031070705480d00c869407061080b9060702000b10300b00400c046030202e00411008207100039400684100c100c484130740c5409001c45c03949c1910345404604540241c1c007800141a66110030701d4520756103029007901d51400f03003032000b07100013241c540c5500c1c000005c100e8103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 809677374 1250 809676124 809676137
    0x301150f090b13050a0903020c010c050712080f0c0303060117010608130c090624030e03040b1312060b040b0109050609121501060f0e010315050f15040f030506090d090501 75
    0x2c0c83d110503a416006051a0340b00b000646000c0740e05200810342d00c00142c005200300c01d485005540034050745d00d20103400400500035646040b4045070103940010301102c00c2d040c00e0201d40018441100605404900980a0354032843c02c01d0005003080c000c40e0801190080f640010003480c0d401004240e08400c10340c1c0007611901140c24403031140c01040d40f10f06401e81ca0500d0000380410312318403400500019241007031000742d0f124000c4050703d4400140004940040004108202954008150210b00c14030746003500366942000c2c00802d0240e5000b5100d035030300d4800c0e24031140f4281c0310b08100f42609007058080d00e400c010100b01103028034210316020300c4404620513003a1104010020601e55035904d054640d40e16210020300c2450011842c0000c40c01307036445002e166010b4062000b944807003484010310140b80c0401c01001e003500850890300304401c048002c420447c9000100040c0103030310a4013040c145145412454078200400e00412034014001c0782d00b000f5804222042103070800d03e03064 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 809678624 1250 809677374 809677391
    0xd0507051e03070c02030609070314070806180a05190303140403020c1210020325110307080f1903151e1a0c06071206080d080103080a26060301150f09 66
    0x1381e604c007003266000380d854881d4404001c00d00000040d82030549104c2c031180b42c0c0e2303e80811203266880003140540d61a540001e40094505166854900f2141c1c4104040b19022001c6480f01400c0c905100310707104e40c501f4806998414160180140141401030010b4440e40b807400da10000e4507203111448451041020403a40015880c0c2048401404008500215503e0410340c4404207400d10341c2140c80420710880c529404030301d000b444006501c0c1148000707580361840640da0b00c400c4d40d01100090a10322030601c0320800b0001c071441d08480214040d00e001a40c0c960305140c1b21001841c40d4002840302203207081c0311808811122807002120b051101c14901c4211194404035a802204440b403000e22455040111941d4480070840b072810059504103c1c10b51982c1c001038580400d128402d022809420042000410880086c8103880c0356190020f400307100b10050409c0c06080032100c0d1f01d070310700380c80900002d440c0038400c4500114011015044051810094004103281c41c0714580d002c0d5950b4482 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 809679874 1250 809678624 809678627
    0x1502030a0e13020c03030903070219080d0309151505040510140f04020712031b050f0a1119080d060803090109030602160b01091e0b03070e10030b0c0d0507051e0307 72
    0x40e600c5060166040c0c5c1d849203800d8607099500c0d009007100340c1c880c0042083e2481007590b110400015180443c015020003600b40381c00380c01903e5408811030f01d44203040040e9018241d80d2240d0000355032103801c1c900005291004120995001410001c100502180d0400600e40c1690070f4212050302a41d91640b2081d01d8030014000b406641000340052001e01d101d031088580c543e0045580c10340c0c85600701c800203400c0b0412141f40c040c801001803085000c10034206214001c0140d088044c00c1c040c03c0b04c40710105030814a8845021940c01ca48180010801d41400c071150300408014124650095040016a00008013103000307034070015188950003d240348810131a00c48041899812854011603541d50350044002003401c1004002c003259410103131210164940145c803c1400c005005080d03945c00c0800840301c400303001e0400c82d810341407000c000002402c400c074090b00c01d0302d04400c00b98444a58105240a030f902c01440c0c2c104114040010030212481c001841a10404400e0030644a6603183c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 809681124 1250 809679874 809679877
    0xc1f0219080415051c0515010e03072c1509010501050a030e071d0a0b0915120a03030204031a040302031e0c0a062f0d200c01061502030a0e1302 63
    0x80290b084000c0380c0302d055420f802800400503003801081642d10117498881000c2101d605071aa06440c800c1621501590f42c402d40c4129000c0e100142600d840c01d641c0c900501c00007602e80045005074952000e40010040c3d803000d038542c440c0c1600b140369054013140d400280d0a800501990b818480d000c12130040c964440d42c801c104240c200011116655180c0c0000300100314180080c06c0d144802d03000080c2d80c503555003d07a0f041c0f0301000d804c1e0320554076126503d011413482d0100441c0c200c108200b013180310080130480d01c0e171380c24066200180c0c3d40d03066040c589048030440d1111130b2035000c1c540c02e00000980c0081155240e041f00c0e201100c0d803100c0c0e2400304070039201d80b0007100d205100d21812074062185a82c000b10091010b80c00c000c424a030441c841c12a410204402c01c101b40c28140b2006004100d230380c1202400c8950310700c69010340446030140795802e800040b20b980071a9594081403281c0002480c41030112140fa0008605101882c40004c020825400d10540601210003041085400310340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 809682374 1250 809681124 809681129
    0x30605331c0b091c030b01020c040f14040b06091303080a09320606030d02151003021513090506091503120d021215092a07050c1f02190804 61
    0x161880c0c018141180e4096544007000d60704650500d111283c040c18500038410392020346e1068000d05031524100d010007004020170781140e5000340e01c803a81211700307030181f0000307038803d81c810000c0303500c6401c0c00018842c0300ea00003002071540302d503191859400319400038405948040c90881c081040211440c6c194040e0300445010301070039054200c840c00b03656100140900300e01c0c5000885510703566000800d03550364282e51003c070140e0850596041450742c100000e03903204006403607a05141da942e6000c07614410514843c0c058101c00071800c080140a204408401019030b60800d00160500f0740010381c4121015044010380e1002c60f004252544043c09010348401c8010305450b1109407008444010350300100080320a403000400064040c984452100300030140500302858513508c11541c0c00940814000b0388814484203103c40304c401a8100c01803440c01e20a0002d085651a030703d0520480320f03030141040c0c0445480480c0c24070030680c0001d42403101d03451a005070082001d40c1c145660039100d145c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 809683624 1250 809682374 809682383
    0x803040b0304050304180902010228022e09080c0103060317070c15020705152a0a06090311010c09270b10200a150c030213030605331c 59
    0x100102e86d4440c1e800002000d000b83c00b60380140f1944d580e1000d400001070303400000f2046090700d0b20f001d0305011110007044244d10402d5002900349484130050303001c080c0c0d080f90004208100620034100c2c2400a02c103404000c1c00c007402040c1c06c503940c010718405800240000b800000c5403210503c900307004030038000c044d0000090080e1108200081d240c003404e02610b402418222001400391051720300302d840000316400700803039441c1070000711400c103164400040d91030701c205200762020071500d2065010182c445d8803004058280c1440890a64410001d59420b0024001e410070060b82c000c948245a18610360f86107082c0c1d0390800400009001da00da090fa0024a15981040c0007500400e0550400c549255a030449501d045405584c8131004400202414806201b1500032903541d0000e41c000c845504001d42060000311000c03040703043c503500a58100e43ca40080c4543c1c0200c0002d10111014205804043d0355101949580d440e81003402540c024010b440102c03400da40000082c03040745d81d02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 809684874 1250 809683624 809683649
    0x70b0f0d0c1701031506080a02030d0302031003170a0e0906150309101503020f0306150f0d0b160305060a0e01050904080702060f07020411180118080d11160803040b0304050304 77
    0x580c00c28903c9980e00646501d811454150b000c2006140003032340d074088a60013002400c0390303c0c0349402100690405002c1444096140304080009441c100c018842400c2d003280d51511a210058000c00ba4264030356a540102042010f000054884a042141e455801c108072583e94581690aa20300312542320341c894400c0c9010300e000000021480348100303d0b07000710741941d0b0000800d0102741d00c5040c1030700c11f941004070020440c5281c6c1440703000c8007210307000103004a040387c80030786521040200407a040c1d01110841c4031340041035500f40c031445410042c1076030b4031f964043c2480c0e00b4840c04d42044c000c0910502150001408101c180740032910f0080c0c0c064885512942c030120300740f25581080302c2c12072069040040690407031903403070300341c3d0480300e0310754055a0020b100317500565915074004030500640d0b2221001141c6142c003005444000480d6944e0a0514469a00d5a9040c03009038449071100c07100480341000000340c0082070b10140c07102c2c003401e155651554505145944150760015054490 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 809686124 1250 809684874 809684879
    0x50405060a0c09080304060c020a050109050916090b210702030427060914071b080304031d06040807030c09111905120f06010e090420010306030209041202070b0f0d0c1701 75
    0xf400302a108c111740c400d6a4001400c0e880e070700195864551390050a4005c0c44241c0080c06004040d118448001d2050400c00340c026220554500558094008040d403200b80403100030403003d040c0d0415a0003080d502c081c60030582058204001400343d00c0749103403801e01d00c7c11841451822507200100400c1141030800000550b0300003440450360481344600421000c0c171300c070130740700301644c0051a00c1342d8803001702407542e43d0350340d01581c035010300d8a2010211480c003a103046490303d909c0010300280c20020003c211442c61490064825a150340010b40e4090411000358010240f100640306224142c03130842c0c0c0311022004040300c3d00d00a029000c1c0d5129902d81c1404800840e0130101da014100030307a0307000401e929842c18020108000d031001426155440401038040c2d00300845003401440501d008903046603250000380080c80123682c01d940380e20103d1041d2131420b8040040d00001d202c600f000d281814201c0e41d131110302d03003e98494100160f45444203840c05500c81c0c150042d981c042c01145a10658 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 809687374 1250 809686124 809686127
    0x50a0509180907032303120a09020909030c010f02090f210d0f08160f0f05070f0c081501030f1b0e090c040609020c07031b03140604020f04050405060a0c0908030406 72
    0x180640b10a85440340041d03081c5179416000c06680d203800e04444004c2d0b28041501d03074032040c0d5a100814111005544004940040e52101c0b1903078042c01d604802107480c0c40e400401c0508550883c1e5203a403405104014450503500d8509250743d03c40c8045035004070359112001c0410048618000200341030044008419215810030034100700c1405c1652054070030f540302811840709110100078800401c803011111007219201e28040b0b001c0340f800b464141c0c1403200664464911007860300085074805040c80081c0b2180b08100040b914021070f081c6440306651540c0c68080d8100d00101004c0c0200050740b0001107490340902d220350040100c80c0c0300180c20703d41a01003544034842c0511850ec500d082c1400080e03200030700d00a5a5001ca442d4019040315442d41c0d031000c9428020901444070803800000020100d12040781d000d01064281000d0b144500d481e1041000c440113071800e040c0b285241c0b4050001158001030125484000b0300d10014900408000581e070040703481c0d1200400e0320000601041c6035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 809688624 1250 809687374 809687383
    0x5030a061b05030c07140c030703030201060305152703091e09180d0c1403030708010e061e0603041103120a0306140904080a0e060d051e0403050a05091809 68
    0x1140c01c0c50900d1400801c41c50803205407105441d81d0302c00076420301034100842d0000002c80c0310551704d401180d03030380a014404070b4144591584240c01507551949c041041c00018861a000e18405114000706860040c0d0719040101c0304050b1044840316940d06009240820000c07500010401014500400f0086501d00b4416140c0c0c2c908600600800d0042020800391503420410408440050310703844044c001d045401e51840307407040d5001c1e0003001c0000e0120f2420b1004500400711580c4481d010740c105200d8031500580501018001d03200c0008841d0f0026078001d0400d4800d03030444c0c0d05e950b01d40703640c102003d00308e0a1b401d40c6585030007490005c0709000d403000028811000192410700c0070580d00c1c91030701c200340803040000381c0000182000400143c844401402e078400c040c00c00c45046005807010980d1a000714441000b95580c0b00c0912640c0156040041c0005060400b105102d03c2c042c3da009101b4000e84002d00d046c0600410302c804a0340c1c840904118840684400c1021460b01c1d81015548 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 809689874 1250 809688624 809688641
    0x1415071b030b16110601090903090302040603080306010f1e0f0e041104061d0906060f130b0310090227180c120f0103030509090a2c0f15060d020a05030a06 68
    0x40348400c1c0c3d50034141030f000f01c129405405111001d011542c0c030b0724040308060124080d040f010040f5105020006980b54030132500914014040303182c07a4a410b00000d070105c0003045034103050140000c001580e846a0b1200d0b01605030f698a8900e403038029a40043d01c030340a170761640a5209051000c04004115540080d004640d072554030301426001a0808035841521098410f4001c030304c620010b40d180c140305000b8100c0e6404621680c0c900070f1500700102c0c0f0030341030340c003c004000000010b00440c2d40d800301102000e07002440f41107141840701c080d0303503484a003010300c0c0d003002e9218444158001d5480260280c8107a900110ac5081c600d00940004800d600500b50480d07d00711203808546200e00300400c2300e0503a68503854180c0391000400c2000399004000340700300c090644030340d41c800c5001e581e00c0c1c991031640101c1c07010384448414880602d060241e400c21440380303907008078500380d0f015049040154001905035401110070b05c1c0c500120b06c80c0710554101e20340500c10449040100800c3c1e6200084 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 809691124 1250 809689874 809689891
    0x71b020402070b100b2106060720100906051b010f09060204240c03031e06060206090714030d0e030c090c03040c090203010e0a0e0a050d110105011415071b030b 70
    0x1401d84890300089280281b010f40702c801c01707082c201e403050301144c003289540081b8010240c40c00c1003560782e60448084050f1044841d103041d100a6071804d814800c40700c08be504c4250601b01d8070380703040c1000103105010310a424a44401e403400703c41c00c004021340c410f03100045910307030038400c031402414120040d601510558100400001910000140540071498032204d00c1d5180b0420001c182c0341240030704021015500607012148100140e150b8500c1000028080f0390050074580c0f5242c031656080405030b60103000c4a102078880941c5941d0701080007200c456a0381403980302c040044001c01e107880c989410b00d80c1c008040c030040c041f0541c180405940720714031a5000380302c000c0c1c4544002040c1c0c0000c2c4621020100208003041d4880e50580001816001da0303800c455120f61315484442c6025a000005c4020076045146042200e00a010722070140198040351071881c25050081192143c255284402225000c81c54404106004204451041a44190b5600300e6203a003400104104203513901d80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 809692374 1250 809691124 809691151
    0x80a050a020c0f0303090904150213060e0109081e01091b0f060203070305030103030c05030c060c03160206090c100513180b0d020f0609060702090c04030308060d0b071b020402070b 79
    0x103843e107440c0300c0aa8941201802440c2442280c4043c40313122003014000b00e03a401c00328050765112070b0481c405049002413681400003e2860a000039040d4000c441d00715040040412051010b12400629036450580404400a0f61051040040d005044044000307064850540000340c1e600e508155207425203034051441d07100195100c0042e03940303110785e000040104e4418001040840c0c056030070000414005d00c256854840807654050a2400848070307400704200102c140110002c070781e50040c00c0a242400100254109020303120794582414030001e00c030303503850f00c40703e0a9280f0038030903500b401c4103000900d103240d500d40041e0010030520482641a140c41c00c02042c1080c40d20107071390b2802940181080048901030b00030b000d03441d409103039490303000070081102000584403601c40620660101d01c0c41901d5034118a0000c01d10308010f41003511400c407050130000071948500200c2d0f0000c0860410b040203078560744010559004618010354494408502030060152551101e07110b8440040e841 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 809693624 1250 809692374 809692393
    0x6150807020a0c061d04050a0c030f0614060703051303050f010f0b090703240f030c0f0308180121020307030c02030408030a0e0612090f151306090f080a050a02 70
    0x100c0c0d5955500e400900380f100c1200f0108043e60050a44010f005400d00e88440103098500104065503001e030b801c0c02003039989500043c0d03d15031510a0a0300c05245c0b40c0140809403428501003c269016403d46105010000c0c030a82010301900894404c5034452031082c41e92a40d0703050598444044000b0f100302542003541c034101c3c4113980d01c28484801002020b400d4141c8400500320000c004a142504e07284007550051204d03440305180c1d40c001170120070301c1c0b01c12072419450b00c0024049683d102e0082c2e4003c00d0428800515150141c0350314a0004100f042003607003000041f141c0d00702800170011035403602d0600480310010f80d0001c511689258030300744140c00c0d40f110b04980da07100b180b046620301d4000f48501c03001c882c40340d5503039060241c1c01050f250400788840c01d9000141800e44100303141307900050118000c0740d0144001c0c40300001c0320b81100d2031468a90058170140241e203400a16050703440b5200c004118440f403411009170f4000303603465120100d000d006440d42d40642c141002500c00e40091 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 809694874 1250 809693624 809693627
    0x6070f02060603071a2a01091a070c0f0f0606150216051c170307020a020102120f07060b0105120c09010e0a0302130506060d0c170f041205090f030106150807 69
    0x12a03081743d11400c00d0404215001c08501c0c55a0460a091a04889030b5001d04040c21520040c00e100408294000908940340d0b26108410040208510a01c2c002c0303030041081d01c64006403604d40e10340d0040071441d1004010700d0208803c0d8100c0c1d0300141449d00e040404981c4039901c880c40092200340d6000c603010703d180410100d02c01c58041c030509602243c0050346001c6c1252284c2091105441048420303015100580704c0d4042d030304202c4107a401a805108610190341c2e040100a2009412510540c604070403d501041e9a202c2c15201410068403104d040d090781e440b440c100c902d00d200b9030b0190f41c064248011011503a03801500c419001660640410045151141c043ca04883d4000c2148002840800160015040041449030f002009120350300700e50310f060080610852090f170310585001603c90666010703031f0700503003545000c4031003000700030010f88404482080c03481141022500c5122203400108140346900495415500f0607800140001c0300100801c403d10240d1150f040c82d60b00c03081d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 809696124 1250 809694874 809694883
    0x170a0804120c170c10170f04020907091a07030e03100b04050603012a0c02100305040c0e090c04050910020d050105030706050a091401090506070308090d020f0c060306060c06070f02060603 82
    0x1c3c10006070059101c0744001d280040c034450401c401402c2280c05142c0e00b003c00c50650380308a9582c51108000f00c10041180340c074403a080e42c4802941005280300f4200700600003a442103001d0300200c4100080c07076100340340c080c0c1c007000e1207880020300700c40326144030542010240103843c3d9114042e0b1b04050101e12075180c103000300b1168408440c0c403ca0000014101104201161410202880010341c400c8000d611070445007024800213460100340c0c2d013858a08042040015403150041312103000610900c01d10103c1c100c0b41035801100c0109032a203412420504144001c180c1e81440e510001d4502414485500201e040314011030135110051b80d07030b14080e180740c8180c2290100040310342500748034801c22141d10000071441803501c0c1069a4a0f070000c80c0320760340508800e8000c59048010483c1d0460100007424601100c2c0c4003420b242d01c00309030026642c0765408060343c42102d0201c006049912907905540f2040b0010040391082e0400c9a00901158105180a0014001d070000502607080008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 809697374 1250 809696124 809696159
    0x7030e150903220807080d020f011127040c0e09150109051c021305011e03050607031d0706080915040803040f020105120a06060f110601170a0804120c 66
    0x4015501d0104100d03e08490720340f50900c010f018500c11000800d50080800914015061030001407540c031113058030291034004c1d02c4400c0c0803507130304007402407038035412180560380305840c02e15800400e129101158021840c0c800b071002c1d041032501690150182e408218505444c10556801d40c00f51180d408111540803441c1180b4007043e0004000c0009050601000f0002c3d81e0303a41c85650742202e01c0d07001403201d681001410151507120001070144807002d284048610000318190802c042c695996183c880350300401c0c0c001490380e02d51103c10800e000b44801c2218071303546810780b28890744510019049071000d5480302030300d1150a0054117003a5120000360300458000140c130b821617440c0e81d01d0b900d050a074440b080341000014007034030300c00f20000008607008040104003c90140c1c00d10390010b2a03016410800410001014440d03d030b03101d404542d003410b43d4504031b0000c10718015410403a1420b035400c0401810004001000201404145880e101c0c082c8288251400541d40b0f1150a0b6458441c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 809698624 1250 809697374 809697391
    0x30c060702240f06100210020706050117030313020105131a03090705090114040908071a06040c020d0912020f120d08010b07051f180c031e0b0705160b07030e15 70
    0x50001c6911490321114240c880e41702481180c400310050041c1c0d0059800c400c3d81111403544810050000800c21102584002d01100c01503055250030044081c2c2551100c1000e0705101c1c1c0011020103030010b00740510040c00392185800c0c5841a4040c00380c00e01e900444100100e4029140d0100322440c155400c035040302d512078880c01240360000204002042640e0302181c1c829010001c034800500d40755070004614151240c44429440c0a0050100303a685a0000404541202c810403a01580245a82080c0d03a4004d041080910803440440c14100b011805158828000c20600307040071000140c0c1005a2940d0741c521f52142d03030340e80c00b906c501d0045130030040041e006200614140d8583c09581424485840804224008192001104141264020303a4545402402403080c0280340d00491881084d640705202c2c00ea9641d15400030741c10380501001c080000000392001d0030000d02d8441c00c5000e4101c0040c01440c2400c04000d0b004040c00d104400060242984089002c045401300e50300c03442c000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 809699874 1250 809698624 809698651
    0x31b0309041a0d061a09190506030c0a0e0a0e030309030a3b0a03060606030b0405010b0c0601120f050d0305010e060415294308030603030c06070224 65
    0x844d03407020007a15428168aa4070400407003120700a9507a040614010100c40c0082144040c603100e019003036400c0103050b00e000794005000d14500d502c0721901d004c12242c05c01c040e0080340c0c48004e02c5002824456680841b00d11001c402d0011045001c0010454007820f03441e4a4a110800c0c01e84403480e40340d20352651103165144a44c103662076040310ba0f02c40c40902c01850321456a460355a42c80448040b60080400030b0f546510718041400c162007803a000d00240034020b81060748000000d40d540d0f10500840c4004802286508108207107035901c0c0c2012a484002d5410a24000748000c000346400d00c560031240300150042200d60401b0300ca8000c0d00c0c004100c8900b00d05040907a40b8007091240014180340703080c801442c424041115001d0060011100c105504103c40c1542c0c0098551490f0030b40b92440005243c2540c2100c0c0c4842d00310b141960100003142c80340e603240c00007070440c000c11164100b0f6008a404200503d036011458020360800540000e1840c0c0310032006c00940e460454114504100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 809701124 1250 809699874 809699899
    0x30e060f070c2a0603021c060503030a0327060209040c052703191208010f0b0301050f2b12020309030712061104060504030c0504090f03030e031b0309041a 68
    0x21000410352011403665200410a800c900c0c0c40300f54041c65502c0307840002d5010a00709648620254121420713400607900b44034190030440001d40b0391042c1c6141c1c100745640c9985800700398000d0440d81071300781c1c44881200c0b18074002d418000065030040c82080d228034506401c070001140201c081d52a100c0840002d0058004005081001d203100c642401d0303403502c01d150700030258a035048600d210b500d2190075103007240c407100c0b40060311404041c0c01200e0081e06004007885400d40c02d2082e281101e17800c8900841d108840b00c0030881d44440389850059049603981488014454601e401c0e508a1080100100301004140102d071680505410f03140e16400000d4200b00004541c00b4901c180e5008510009441c2803040c2901c150b584164042d5001c00c4c00818200140410038402c8001000c0581d424401d140c00c0c1c0e500d00d0008024076400a040c19500c40e1050003a01003041507410341420a8401f000f00d0384172800b160741da6040001d001e403155080c02815210310808801e600320420f005002c032000b554 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 809702374 1250 809701124 809701133
    0x7050705010305010b1b1c02030702032e020d1506051309060515091216060e01030c121805060c040e06040c09030b0c160804030213060803030a1d0607030e060f070c 72
    0x482c0c4104189280c860b2980080600385805003442c1f402d12117800440e580c0384a072041c1806d0804180180c090400c8a01e81e5040b80000700c2145001100d0f44040160350f01d6076640450001c02020310549074206240c0c5c0003090054010004140c01e0550140410010b50744118074420b0324894003c00ea0001090407500c2d007941d80500180282e114001c0c2283c409031485800107182100398840311500041c03840c03040241c203402200f25074042c8403e01e001d12403072108000141000311030b0106a182c00f5070305c5504600000200200114081c0d0080a403a500c1c2000b544614858005018584029a40d000480c0441c505882811000d620300d4681c0907106245840740d00032f000004010007440c0314100000c020400c010046040d0346440f4130035150700c580c00d50040c440c0159000b14030303591041c50041c06002c40c030750001c00e807944460700d217002045540300b1342c44600c520705114640ac0f0301440348400348a4101d0b05500840812800c060490b00b03ccd44c0e0300401102c10398400e440340300205001881050104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 809703624 1250 809702374 809702407
    0xb101406090604030b090606120604050a030c0812090615121b0a0b030a02040e07030515090c0c01020c0d0e1503010b03060f0603040308040c12020102060f101a07050705010305010b 79
    0x40341c00802e06400c0503526110008401c0040705c00041e03a41094082210526024000c9160001c0320f200500c20b0340b41650701c0b50f80c2d8207500742d400342c28014031118400800044900725074807456199454231722810400d0b2034554402c1d0541d40c100b503940c4400c00280e000c1c00d003000c080c0a090031030401414610359696014100c400001d0f441900a4041ea20104081e400c102c000c50240c9071007100141d9452a24400c201070400141054003058148070034008194810102f0300c201c0c03a03044400c2e4842d030300e5840c0c4d038240d90302c60140c884450b54004540309400090201d0b00d458400d09a85038114221100307010071640c894030030f2030206402e0040c001030245003601806564051009081c06103960607220004d4503d40044600b200010009000c0004010000300c80400034030403070815078070300000343d40003030346441004011300364014107103002400e0b40460100c04402007860fa0f0a422150885c102c6a80b2103512070002a541c501c501c3c440028a54400e02c15513048130607107403007079003040011118000c18 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 809704874 1250 809703624 809703637
    0x2030d0c030213080a050c04060e061525050d05070b0a0207020406032a080c180a140403050c0106060516150e01020307090306061703030f0901140709030b101406 71
    0xc0590900844511140d0603d20703801920b0f040c030040400d0480703494a030703140118101000380078504144040028900c443c2d88a500700e6803c0b51038180b1a0b2601c040c0000b640101607201c902e011801004440d01100c0c0c81d000031035140a40161621720502e014150307401c0c440c03180c004150705803540000f61800201e130701034031000b0310040000c1001980c0b40c684810081d4422140c1c1c00c075400c44420414010361b406400801010020701030140a8428000a030061034172422000e000701600f0001003090440d54071400303c038500c81c80ca005c09810541001407090701700b00485500b9620f001004035641d4003420aa03003ea0291220010101e022907a459504c104030100404240f0740301e0001c101c80007803c0c0047d512031641c60f9901c1402c0c1c3d00d503041c45401d07955503500445001c0a0108402001c45002c01140e9014050002001d5141c4880c10a28010481007082038a0320b01c0e900d0501600c0ca07404184071046030302985d210001619094503206600406200e100c0c1440e060b03011055045c240100503040c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 809706124 1250 809704874 809704877
    0xe090c04090507050a1b05030d0b01110a051c0e030c0112090b1602010b0901050904060209191203120e071a0d0e1507020607080c030a0f1b09120302030d0c 68
    0x10980d40d0200780041d00d9003900e154000c900003159a004490703004803140400c000c401220720340f02080e80c80f0a03403244600055000301d03940314000040f159018038599565510520111440c501c80ea04081da140c2d0004100001c429a0384840241420711612103942e507030034001c0250030040090001546d40d590312548400145440d0f641120100340329950b194802ca007140d40c480d40304140103500078211200c01c000070380715074203c02c014440d03602e88036200d65100b40c0c41030300103030303240c65403000500304c250b9040004402c001c40d80b402041c00b01c0341c02010000144030f0303103500c003c98007210256816148000c118a40d21f0340250b00c200410050004406030440b03241e02e4007441e001d0300710752640596070500181d000d180d021480040000030940e02c500e0f8000b00c144003414050900e007c0007040a580505015014071003c00171408400e00f07980001020b13090700303008000c070b1b55624012107103d0b05040740e1400455003510f000250402e07030041d4070200c40e0340355000d5850600e070004140b00900e00c0c1e640900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 809707374 1250 809706124 809706127
    0xd09081c03110703020c01020c01030207170702060f0c240105030a02010f05250b07030e03040621050f180f031617041806092d1113030b0a0c0e090c 65
    0xd000c200c202c0c000c2c06154000da0241010002c510006407510225402040c10544108002c201052500d42400c402e0b011079481e41d42d55800c43c1c00026114000c0707000700c200f43e40c0c00003448a08420005400104080001c03100110107443c0c1c04601100d00b400d116158054011003d040015885801400010201420b010342841206680b8400242041c180c0d460000321007441c140601101d81000d41d4403092a00e410301c640a040d20402e40c03240140d208400500444140a00030b1030501c20440c1c51181080000300901c0c5080020300b14080d40c1550034070076500e65041c3c040e0170700c04041106280c5100740e1005502d0f03c1c0504d07001480328260b55a00342c65481658900c001c0ca9580080207000420708488900d07644280713003044070222115a80003605582c40d2807144500000c0c0d0340795407000003200000300e088003491201607070081e10700420b02c7c1c03a2001c0700003181940012440342000550f03000700d90507101039840d5503030902116030b40302070302003c568018401d4946182c1507014503803003a041e00708103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 809708624 1250 809707374 809707391
    0xb0921040b040b0706091205070b101401110f10020301031b05030304140a090207060b0324131a010303050a0f030908040b16050a08071205090a210804080f0d09081c03 73
    0x55001c01c50410310440042c0000850300c050100e030481240d04100c040240030005498140700733040c03000c14010040c0c180156054040d680071800d20900960400500c10341d0821b410f80305542d002036000f408200e4043c8521030003401c0d00a08000d00d681a100050000e626090038240c166844030f1642d0803031a4002948003001c2890840d6002511980c0d00c1343e20302240209a1404150910002c0ca010183c50f8010515160352000d000080350307082007200003410007003959400e000b000b12402080b10368a0f8403c400000041543c054024200205141d03a4a000250743c10f400301c0c00d40340c1c8504042c0c41140b00b40000d00010210030028480d99666400c2410000350701d42e11070341413a420204c00d8404000200c1c018051260700d24019003007102c80c2ca03210345041c80c80400214181f449004500302060f04550380d1b004d40c04200c0d084141560401003064456075205101544c07480d9134000609140100b24803203060f1800b645481040d600c00d100903001d09000e241d4042c15068500320700008041c1ca61020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 809709874 1250 809708624 809708633
    0x102210606070c0f0f0821070c030f110909010c1e180906030b010509060d03030b04200c070503060610030b01051b010b180915040507030b0921040b040b070609 70
    0x940f401000c2c400d00c0c40154500d050700b6800d0700c1c845a0b12a00454220700c84440200e03c0c2204c40040040c080c3d83c5981c4c8580e6a81054188003d9540000f4000040c04000c0c04c180140300c864050a54030072a02e00324160b5a503924142a0340000c0e40e114003003548007541d921000400072090100104034905402c02007480b0319034000902c141d50001800039902e071424001c0c00103030f004141c050141512040d05505080d40880c02011140c4030150805642d07440c00c1d03000f5580e40d00310b804150a80e900f003000d20307100303400301c0580c036404400504032a204e1780c41c00107014200411500c0c4200e10082c001860014404001d401a000451005040050812460420102c8503291941000150300000707050a495801d1245201c0c1c41100d10054054050403c405407000058400360800d804211410549462500700d1408210b900014251f010410420490100c0003030b00d5492038501100c15245158140c522a00604c0ac2c0d005600d20050100420302040e0380032000cc5c1200341c0309180001c0e841c00c85848 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 809711124 1250 809709874 809709893
    0x50102040b030103060c0c02060d050a06050301060602150a05040b070809161d0609240a2402070b0a020a032a1104060b0f031302030f0d0f0f02010221060607 69
    0x7110400300c0c0080014410701c2031520900303040c4106401c0c40203107001160001645401f4003c0c188009a0300c0d640010f4800030b85030010300080070081c009001e4103444035000f035100c03c0200c0020001501d1580010086140c03406840d010715005008030410b9150190b08540b2000c004040140612640c1e100040303c0020b07001803c0101407050001e2180c40304c2c000003446450b4041d210b144500300c1c0c1e105011100d8800307400550890306080c1d0076140b00d12000041000d6081340c1d8080d040e40e101461005030084d03800d4124552441301e43c4d090360411502e4402a0070315019501d0b0f8503006030301510113000041c0c01403c0340360170300b031003200100c48642c1d0718050740d031a90401c2d03003007226244079104007165942442d006d03103c05001c3c40c003000b03401d02580c090298650300000300001241c4040700811019500d041c03201a803034240c40010b80303100ca56101c00c0a0000c02d071544c10000050007210303282c44014418070a545256030300508103400080035007110003002c0c10144c809a80079404121a1002031201c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 809712230 1106 809711124 809711129
    0x12050a1202031006110a021e150703020312071b050a14070503120f09180906250804051e0c03060901090308070f030902090c18010306210204020705010204 68
    0x320305d0340c500b00103440065000301d031b45410078160041c1c42d1101c148204007a940d900c3c410340c0d0342d800b07240248102074001c1d0040c0c00c14440384242013240c1c640c154200020340380c500d900020b202c484444031211401c04407481d9021045d840e0410103280c8000588442070070107004050301e86000f10b0b0b190344412030744a0500000103045070007070380e03e4010340f69030f02006407d000c22181e84176002045008281d44003038140c0316180010b00303481440c3d5500750407000704000f2407011341845207041d00d00d4403015004a0300d034043c041da801c0c2e10345000c00c2000f03c051403d000811031040c81205140c100080906048500d904141c181070200ba084000150055154079240318012030b0b04004400400d41000d00039401003412042c0310a00300a0005001c194400b0800100b01c11040ca0040d41190350171300c6001c444401c002500a080c60b00d0b0321307500b0b8036140060b0000d03107003201660711340342242c3c07141c2c = true := by decide +kernel

theorem cover : BRFrame.Cov 809532374 809712230 := by
  have h0 := BRFrame.cov_init 809532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 809532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 809532374 ≤ n) (h2 : n < 809712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
