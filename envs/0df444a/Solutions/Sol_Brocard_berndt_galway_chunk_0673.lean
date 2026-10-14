-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0673
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:04:02.35695+00:00
-- url     : https://prove2.me/submissions/c59e99c6-c493-4b0a-87ae-80b4900deaf7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 120863309 ≤ n < 121043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 120864559 1250 120863309 120863333
    0x305090d08191b020d1404030609020316081006050a060207030f06091a010302041a090112140105010906081608030901050d140406020306030106080a0c06051b010f0c08091603 77
    0x502c0d18410742810440074032600501801100c0703040020a48003a003500207041a0001c0090000d01c401c9945a0b14000009030498045a8000e1800174106600c0c1c800282031120400404001c030030108400300d00c0e01004121711303180e130400c01020000c00b0b944006010180e28507216620160300800300400104038003008111880d0721800300003684210030f90b610090300d2003140c5001b4400b42c42d0700051086080c28400c042440c10b080d82c4040f0a014075100080b20a00c050040c6080150f2283e603040421402001d40312b041450b070350080c0300940e15040d43c00300808440c40344110a10410b080c5002d80c620b5204c444040c3c0b8000b501031441d00c04100015600c4d58466140c503103c0c1c0c0d984d081d00d0405484003003000c0740250f11501c009039032810400101b509450554110703060b903070013200c100400144031480325400c4031154140107885001d60f00000541151818007007119500f0510007800e021650781c0b0168500c3c056403102149034880100040d42c03130b811800f0410400c1c0044100f417011600c1c4c0300503e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 120865809 1250 120864559 120864571
    0x2060f1b2817130306060605030708070305040b060609030c03030705011a060a090e060f030a0309050f0613050d0c030b0405030301080106060905061e0c010f02030a06080607020604030e150c0d020d0305090d08 91
    0xd00b10f110381c1c95441808a415641c00f400000e4004000e1008282d848040141c000d101e9103410320003410300392554610380101515281c484d840002d0381040761b440070700016007444130040030b59485080d01d0a24034043e101c080d070705243c00ca60040000700a442d106041d41c414403200da66545560342812071100c0c00400160909a029161184000d0140d6003007003084001c900c40da40d280319107440c00c414040d9880710307080703018452002449103c3c2e0002410003810100d41701119880d10a80e12420f0140b0516101e800241080d02c9010810041c0000080118102d13144440200011030703940030115000803041c0111580060708000c04200036424080e0403a8060600306101d01c3e00c41003c1055003115901014041c410350084100120390143d403081030020310304000a0501c5151809000b074854400420080510003101540c4400703032a50010344045082d200b0806541d00451307030320389a5401c14040301d54014402c0311103075507200d07229009030381c004c80c43c207002403040c114400029101ca0b0401489 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 120867059 1250 120865809 120865837
    0x3050105090d1d061209100e0d0509090c09100c110103140708041b12031403040b22020a0303030506041a13020f0c160501021005011202060f1b2817 65
    0x85c180103800d40096180903c14900c0107146940a001160041c0c034030580841a003038000c400783c40610ba81150407590203000403074000321541d039500d001220b14020a40002d8014400400b043c0c291500702e42e810a890303000c0c1e918190000ca0050044040d2005e401c081c8440200800204504602034103900750402d2003404d03000d90480c04a0741c6000e090700258001449804c04001d00700516800050907000468001e83c42c0c2c0ca14540703038903100032900003d08250313800462a4190fa11400350030b10780009a950041800d802d80e6a40c1c02c00401a2600b6640a44290b1408218000c2d1140b1030b1000309912a01802140d10305c400005d8030002500441288880c043d410041594404c10502803c62101058444882e40c01e091000085c070b041480100c16032101d00d040b00501980d117014001c0711038150704807809642c0b5002e500c01070190b80912aa4201950759018480c0200100817074102080306406203000b8901c00c2c024094010007554102c09041c61152482034411140b161000701494665000e03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 120868309 1250 120867059 120867067
    0x11190f0b07060f0c02011a03012703050403051f050105040516030e03040306060b07050f150103060f1811100f0c11040902060703030212100b0a0e010e060f030103050105090d1d06 78
    0x43c0c1e000fa13854091080c00141d564040200c0c00c0c00e0415001c4050351020340007040910200441d00c0340855400703040e00c0c82a4610050002058400c5040f10003460307000c01640ca000c085c01106400d11000c60083c00340030b50500c4008640c1e42880c4c8a114030906a0182013400c0e480301c0e50080e03000b01f007510711085450004100220120b841401498028100306980d00e5031a08142041390800c044121001100e03008101c00840421012002e0b0341526084200018011206482c00c00248801c01c1c3c80c1e00d08070007801410081c8012070200744c0380d20f10b0948290844110300c100449000d80c00000310760109504c2503211000c5242105400d06807030005e0030007c1c1250340341d000100f241c0c016000480000c0d8001440311052280345103c16041000e140307860308003e040040f44400c600800c450b45040001001802c0d029a10980000c0c00014010785616600d41e01043d00f040c00d031b4001d0205507101e41c20000850131842000500a58016041d5114044000760780c2d010010602074a5120750300c40001c0c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 120869559 1250 120868309 120868331
    0x605040c020a02030c06040815060406030c080c03010c03060609120204060503010207140708070303090b0a0e1207050a050303030c0f160206032508160f110a11190f0b0706 75
    0x4812154600ca140e002040c0d02280d5104161402e000c0404480c02280c0600080141d031000049003516000d0b075034904101640d5500c0402c00611031580041c00e840308420780010100800320b041403030702c00240c000340b161112100c01942514918400c000000d02a4602040083e20401090801510090000c83d0880e03490001a0aa0b0440903080d1000c04001480443d0880c00300f00c0440105400360140074400e25644020701040e105105424003100700241c5920600c1c402c5a06070304811000700508040010034015039600c400901956014a02244012500c0c2c900001568821410840c0c40c0b4a00990300d50000c44c6a081f5a041d051100c00901d03039800107a0b41c800140d4891080c890303244455a040d42c180c50814490320000000380700d4010705002a108000464001983d80c1d410602c290300b00102c811a20004000384a0350180590040743d4200a0182e224540400c003c4503442074241d5076240328855045c182c80342c00c90031404143d0030415506400b010b80704587c01103c000607606242 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 120870809 1250 120869559 120869561
    0x170d060b0a03021b070302090601050d0b04091b14060304030c1b0e0411040e0c040c0c0203150702060601020f030406120b040203090109050601080c012304030f0606050a150206041203060504 83
    0x6050200110341c02141d8804d007210801d04860100e0f81c040c0c000c01e0020700c0c540210b00c4800c0d0142409042080002e910540c4000b90341125100e840040c208029415503801c00c030260010206441e8480d546d021400110700c0b580018864000c940104420301c0d58450780d50699031411036010450b41d4038072403547c40030038283c1005580024400c040260109282a00c3c1c10b41c4040036104085110300c2c030340592151022400600a5140c140c19600082c601c141c42109850105003200025814410203490488140c140c101087c0120042c1c1c00b1226541c80304001aa141c40c2d150300314594941c410321007044000c0c4107070360300c41c1d40c4006032200140180030540414142d900071500c680242c0c0d1030b00701c403504008080008034010300b2130501420b000f026110008150200c4001800c000803c840c5070b84640c00c10b007100321002540d02082c1060f01ea80580b038910050116441514450140d2100c0068440042d01d0310b8662413605d50302404140c1c0c0e8a0fa00d1040400600407103c0406560311400704260301c403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 120872059 1250 120870809 120870817
    0xf0b0607030f142b090b0a060f050a0303080711280c0914240402030c0910030b060915090916020d02070f0902030a060f0f05090c1e0a021903030903120603170d060b 72
    0x4010b03c0230407854140806442540a0382e4806405100c0d55041080842e5002501300c0e0070010918010312a82030703070101b02d80381007032003120306c840300320940c2564013050304500320304143d10302c901c555085003680d540449044400300b59594094003c8a80007410f5440c04034407140110651601e1310406580d594041012600212824500c0880008a4000300e207060625540d420046203401c2c0030140900300410114000c160005001d0002d81c549190070300028004d980d941c00029000c100340e0b00c4d0051036041409849012100913001d46041c04a030b1a01c086140001d0352014204150303130525040607403000394801406003403001e83d204800300701c3c1382800c1c000d18020640d494000d40000e06100800813200c002410803030740c411003000038107201346550544002c5401c0928a99486030260041a07081201124004040c283e0f03212490703040640603480f44401600a0f82d9072815400c0d15002d0108841c8103000c083c2208020190390302040c1c00c1c01d0010000d24100440100320345a40344001065504 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 120873309 1250 120872059 120872071
    0x1b05010f0f180312020609010e0309100201020c0a0605040c0605030f0606030405010b0909060702070816060c0f08070503030f010e040b06040b0d0b0925030c090f0b0607030f142b090b 80
    0x290140f810313030300141e0422040360081110b0008000c22095002400da480c07160001076405088000007008a441c000c0d41542d80c0e010f07805068a14041551801c0e10040c481240c080340d103448484008201e4a2064080c0e921a00b00410159215254003041020340e030401001107419640350b00700703000e20ba01d0700281d86003d00c2c0302030010b003480c0c205004080c3c104003080e0461003007030b800341401e15000b1007103020100441d2503504240300320f00780c11304019000c401c0042000d481048001500d0f010031a0000c0110f120320302c1ea404d001256604c0b000420f003030701400d4a000d80300d5a07241c4003080c618500390b80a038920f40350040c14200c83e001160f6903840035080403910303800305400050840308501c2420401d014610b980b03610401d092401c6079900d03107546409002c0d05e107034182e5826402500c80416031000100340c5c5d004000980310296490010141890303000004001120680300080b455680c0080d40c410500c1551604410b00b03003650294a4070304a1610004003c0e12811944046448001102d010744 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 120874559 1250 120873309 120873323
    0xf0c0c0d030c120e0a060507020c03070308090103110403030c12051e04050411090a0303140d021602010216080a0f020612090f06070203030c030f060310020a020102071b05010f0f1803 80
    0x41000000e441c2c0c044030001c1480312404e294112900700380201e0f510849590014002681e601c60080481c50301100c80c0195030140305214001c000e105202028100d240c1c4240d909120307100c100301d140c43e01401548401404200007844900c005007200413095584c2602d8a4454207150680c02e4010194100c4400165420800502440f4600381809900003140d040001c80345407030300d113001107120740300a0f1102404200c6031000503103a0110190444120780140d035400d549a20b6022003c0c605251107103022805841900d20030034003201c00d0306030380342159203183c0a455038403d591100e25400d0900c26049074030030010400758051421080a843c001c054480c0100702066840010510b020340281200c410b651061040082c015421402c03250300941c0102c40c400143c40d6035004c24544480c1e1880803c0d028000b00e44000c0c600c2d4154003400a1a000d04411207421818444901031800c50740105030010302c0c1c103004c0e40f010301e0240003d000140c00c0391404004ad50030803900720304840c01c0c1d42c008031006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 120875809 1250 120874559 120874571
    0x20c0f070f030b060a080307030c2423060604090c09030c080d090803090303031501111005101413020306011e020a020405061804140304180b0a0b0c060f0c0c0d03 71
    0x2103c460440994070040c00d407044207401e4180211341e81d9a00482c0d10040400c201c1d0140c1908002c61101ca00c3c2c030680060ba00504480030b04070b9404098040030b400202d441c04924010b40b110750b0b030014103600810010f0622482c190030300081c80081c0203244104018451410400400141c402c1c0410000b48500c0c009043c040d1001140142094502d60081420358020312001001c1e0360040206c0e900318144941101c0c01414010050302c0942c1d0a403119034030390050240c0002812000e801162040c0c00403003080510640f03031841c50b0a545240105660040485030610a02101c240d0045070031890504100c4000710b2000780010400c681503e454005030807103454603045040a00600380c10000442d11a40e01c1074003030b41d006443d0440100003400b982098082c0341e002d0642401140c01038054840b81014034101c2100b04006410000c0c0800c1c0144240040010804c0740f01b81030b103003040082c002819154840741c100900ea40d01c041c0045c000c8400c02c00041080001c2007000c00c1e456212a10b004c240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 120877059 1250 120875809 120875813
    0x8070312050403031707140c0f0705031207060203060120010605090105010801030203060a05221a130803010b030712021809010806010807090203040809091003060609020f0d020c0f070f03 82
    0x141411010a500c14007000b8442400080c1d0081000c03007908003d0b0307101d08030036074901000f00d03241d0107c40b0b14104c400d500080ca0f02c4035030401041d24958031402501301e03010f080c4e6910a0565444004036040c601002c01e124440000b5400d400031034200c50140b40c0035003100e0004010301135a117034030000d15115039074501c410881e9050007002d40340145400d0a20300b0b620340c550340100b5111a0010010051581c0d10130000d040840c84260942e0984507025001400034043e280028881c0b443d01c484052000001c000641c07000c072614454081ea50748540c0c01411f607440c02203503a140c1d80000c1c0066061080240d22a9400c00c1d65101034802c4030005c42e0418100c3c4210000e002c0031031010780000d03550360084001801480381c0055100120361604000581c1eaa40300d090806080c059045031650018442050011900681502e101580e0080d0003c00c1890b41d54500c0700201e10a0303040c444640c403818805c4240720582c50303002d03000024032501038a08003007111a04504080c0290001c0c0071000c40c003039082c01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 120878309 1250 120877059 120877073
    0xc0720010f0e041116030816050702011803080301090f050a020304020303070b0c0f03100501260c1606020705010c141303230706030515040915020328050a0e01050708041b050a080703 80
    0x18000106a8000d0f50701103008c1001041407045d072a01034140401c0001089a070b01120b0403c0008641103400240c40756140c0012101508040b071081945500b4a400300e0840d42d901d100b241d02540e070040065191040d80e903120300115400800c5d40c901004107000e084030200915009520481603000d083c0d050700d00745400034240b4407510244240c080d011200940580183c804042e40001c0103080842c2c07200c01d0b4230b81e080f44030181014020950f138008580901003041c1500b02c0004c05445495200c131000401076140703183d0054100010b20740003041c02c02c002042c5c02d8141100380e84c2000340046420400c07580303a5440c001160740101e000a81d920200084643c2c0000000c0318032604490500a014140d190001841d081d503000c5841c0d198000007003000aa00080e1460141076941c0740c1202e52020000755100030803040380e812900a00f031a000c40030140c1c042c0705680c0306603025200c508250702c454441e0759007000b65030f4060300c004100352008661036441d111250000c0206100074041d036425031602171 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 120879559 1250 120878309 120878311
    0x2030705030402011d10051b0106080f06011a03040816050303131502040605030c0c010b091e0c030126010e01110306100212180301090b0c0720010f0e0411160308 71
    0x7a54802640319403000c0d80d0381700c00c0c83c540e900006e89000c0d5140c40070811000714000448090f981c99610b09000010b00c0c84003c2003030807038003c900c0181c170900c1c2c0e80c400f001a40c4070703d0310002640000c820000507000803401c2e0081c0c940c0010084007507085400c20360302c06181d98030640c0c8250040a00c05031100070019418180d01c50042506010742c00c3c6880c01c28081d145000240c92102020000f0540b14a0048254441c072805800100341542500740701081420070f610130803a520200340400001003844109504403412210f40f40d146840c49164002031300803203880006804065502d804028131401d00902446540203a00780c0f4265403818502c00b004010030000b0035030390554010300b088645007030210090710501c5a402c4154098007101c070000900400c041e00c0000e11518040060150071a00d0074003420302c0d14440d0200780550f4807540a0192854200000140091003940b42c00c04107621560680003da00c0284c404921040200112000d9800c081c4000300f50906411140f4280342c0d00985031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 120880809 1250 120879559 120879587
    0x19051e0712050f1209150709090c050f03010e1b04150e03011404080708071505090d0e0319050f010c0503090607090f0b0307020f0607020c0310060b03040f14010203070503040201 78
    0x840d19064104208140340d01805115130a0822101c1c00159149010300400500b588050340f008418a460358000d00108041d0044c101d04501e842031b05001d40d0300030421100750301c06164105081d1ba20308254030444c40c00080c61034420116641011b6541d50000020308042d00c80c1d030300c48406040c11100010849003001c44800e1084e030400040840030300081400f40d070020b030403580380c4c0c1c0e54804505002080d4403030400b0040c000a81c10340c803265001240c0c0e010724081c1e2515410780c0e0740c2520f94142201c00c1c030800900c650f0305400142d4103126000c210420f2218913481082504d00b9075046503122421580c03510a40c201240300003007004002d99007400038550140d207a08010b043c0a0401c1103059601d42c06001c2e55003a03140010200e030f8841d00030080c9005108444007100d10628051074000d454442000340ca50091013031065108205085000b0b003000d594204c00c507581569036549035240c40c00500b103000c0d18282c0400c213003170404070801e000075440360b01c80d5200c5035506d01f010310006044c200f9503101 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 120882059 1250 120880809 120880817
    0x30c06140415050f070c0e04030f03090b150a030b1003061103010f06050702011124010b0903120d0b060d05060f0405070503060d020f060705060103050f07080319051e0712 75
    0x41071003402d6448102001c1d5504916126446800c0068200d1840c450014040c0070040e1303c0900040004d0300d00103052060340f182e0b9a007000c101401e0001e406031481800b000700445141c40c0000c0045018410300741244000070300c0c4000048e541d0700d9a000d98441680c0d0b031540360507540d20600500c078440c05001c0070300c80384a0265242d503160607a07401e0003440314050b040030010001402015a0721580d07007060380c1d600e80c0007516404841000d01c000400303000f61404c43c4c0349a802c00000f8500c41500c080c0c424405010300a055002d00f03699800640313a00c0402e0940442d581c0702426084e0ba21100098180c0c41045080010700b81400e004102c20842c0d110003491040741080100301e980350340401175a0f0010810b964202078030480e80300090415108a16081d04482c01007041c805100c00003410741e040324004d1041d0740c0440440b07038000381c50754818000d0100342d0b4420024400784030b81c2c4005161002850780781141c14a900f400180f9401010a5000802010081035210038003118500d844a85e01942c18 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 120883309 1250 120882059 120882067
    0x902091207050d0803070513240e01090506031807082a010c02040b04060305030c0a110f010f11030408010203012303060f0a0c050d0f06061409130f02090a030c0614 72
    0x1000032109020f1010042208001201080805025100380c6011040c800c9182c4c400d40d480340313200801150b10704081d0740101581c180c0d10350154000d56001140f018181e41d00c5030300c0d86c2444140916544090401021110400c2130b400c424001030080001402c5400048c040c0d401900e0820600001c401110a400325201c0c440682039a8210b034403000030585c10361b404129000b41c03400041c0140001c0e800944640030006101c0b403802c2c8081b65510803203119100000d101c2c082101070041810f452441310703020400c240450094107004406455000b000041140e02d0b140e114040c0e07900f0390f002a4001515030703100c4500010324600220051182040a800400c80c518015031b9102c003400b0b014006407122991b03040c03500d10080c420000c450001804800501100c6c401301e0b012001040c641c460751001500f90004024082344d1a401c90700c0380c540003000b012038402c0502507440100081420035040e60360800c60202c0d02c4e140c04802100a5000b04a000c5000d40307020303000f42c1401c88000a0060542c8104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 120884559 1250 120883309 120883319
    0x30709050108060f090a0b01060905040f02040305030d020c03072406090213060f03021204080711030f0d1b051509010506040204050102030d0902061e090307090203060d0b0415060902091207 83
    0x2e03401d5131120f0204040b404d19143c00d01000e081000511015000582820010410341e410204603811600c05650401024222040b020202d0142e8000140300703800410250084e8101038010380b030b040c00f030301080e24601340c1700380c0d10b070301c10300464081801407441c0c080c00c845041e403c0c9128000003021440020361030f0450b104641107441c0010300a0b8005e02c0000c1c2d651a000320b1007a4151103001c3d10f000c101002906003410900c0f081d4201d07840413248a04601100c4455040200c2d01d04680b4840c0c5008126131100d214040e100e40540c1002e19802814461201c03000c24405c000303000e0b900a4007111907ca6040c01e80c107082c02d6903001450280540d00402c010402c60760700004541c092a07040a000402000505c00111540318000e07009686808090650b10a000044000d0034442022400c4800c0d003940c3d590300f107099000854806a00812a20005010a6082c40410fa1003449014014040b14007854000c003254403c0e0401c020560b0b002c591f4105509040340302007511030f00e01004200c0c0c60310304 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 120885809 1250 120884559 120884563
    0x7030f0b030604020d21020a02191211060708160c060e0d0605180d2006060d060207060605120307051501321005070201032d091104090c0302030709050108 68
    0x50701c000c1c043c405d082e165030240314140c40c05178088200c520709100c03a00f90240c0000d58070146900140d1040d00000ba080c501c6071155080c6030f01303c4400704142c0d524105262174221204030000707003894100307000300003400000701d9000080c8080c40599000c2c800c203a000c1e08001e40030083c280c001400f0302805100940c640d9855070004000660300010200346940d0b1402d4a400003d600014400c0c031303100300180a80e143e900096003a09542c20010103240f590003103004559a01c10030b035451500110017411140105902c0e8004000d9507024180c08607015541c0e0b070106640080545c86d5030015040402e01d44200481800804004001e1004c1c2c0401541040140c0c3c00c1203400600694009610202904074481011010300b40a807004008003c50325401401030704503403240a0490010b450890450403060001d40a1901200000f8210800d0b500c0650b4403402003e2800e41500d040705008460240d99840d80210800700d849030140b110000d15510505107024280c2d0401402d0600303010041c0108000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 120887059 1250 120885809 120885811
    0xa060b04120501090c030809010807080f0103060c0c050706030e070e0c030f09070e041a0903070f0303050606120405070302100206040305031605040b0d1d0703050307020d06021b0607030f0b0306 85
    0x90292402a01d010900d00b50740140601800104080d0140c03d0000c01e00690802800c5800002e0300c0b402c415955004044403c2481124010100c3d00320740010b01c0410820b40c411b400711516410701c900c407846640c481c545010141d910000001ea00c910984204034002d000100050110164001040c00c1841d410425800014880001684c20b00006020528100100f0005100c446076440c1a4140f50800b1b00f1240341c2200110b070414080008a048030100100b00c444280e0400c450050032003855804030080d29014205079404281804081d110320640c0020701d006a100358000c0900703514500c144440900040b01d41d00035900030200304000309170480201c9900a80c022000141d01c0da00b45030548460140d50050901500c002c1a00800008544d105105421000e0441c002d20584030303852650300c0c0703154000140290820f011607030050030904901425a031080c2c030007504001c108d1074a010810300701082c410103917002c89d007030200e91034052107507070f0301000e004100784030300748059010036074420b8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 120888309 1250 120887059 120887069
    0x100801110703050711040908070503090118031203110c01150302040c09120b0c040902030406050402010305010803130b0d180503040e0f1605030402040b040c0e1c11060a090e011d0a060b04 82
    0x17400003280d0741c05076a15404444000e900811064139840d403800c0c01c50796074005091150200e120711000d142d03a40118010502280e41c00300901b1030882d069001180070300420703150150528000d000900e200d00d028003c08404218507200325980c20318500411040c0d640226a240900c0345401c000e004d8120b00d024004441600100d9107502034841074403000c1076210300e80c8840112480441800308000c5e00b608030b0b80c0601d000341e07014000c1d81d80765032160303450780b07e00301e607054071111508020050016044050041c0215944000400c086989028640c5d070700d403840d044501c0d400004092242c0150f030f820710f0f03400006802141d0070510744030301644820035000f250309040c8030020000074210756440d0010451000054818807504621020280080b580c0150741441520402c0e00f058a0440b40c1e039030703003051a401003c00d416943c00e1009100ca1640301c0c01202c3c0411540700c0c80802c400f1484009940242059000b40a442011000641200c5c4019040c5120f03c1c0c01c0007010091602c2007001c0d03c050301c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 120889559 1250 120888309 120888323
    0x1710050c0301051c020d060e0609060114100207050310061a0301060504060302070f021f0314040203071509080d050d0b0f0a0e150414091504030f051608031008011107030507 76
    0x1c0c0071310013115040a42100e00941c082c1c101c803031090800800c0d41000e0005403803602154002d840700c2e032616841303110900407074001496071018240c04d440c100004112a48003801540c0030140c41d400480c0c06c001d1140b01c205104c0d0b44030001040014030740309000d00c4100d000400e00c1e0071941804130040c407a20981c8688400c241c1c01041740010b10044600856039580e00904c8205006081200b4200c540c41808040380441d00d001c03080c0c48000700c00000940b14540c0100030300b01d07480c10210400001042c240d507910400c000440049041e00c2e0170082c1040103000398607050303141d06041c0f00100644046841e05401030b070307441c594903c0030340711492080e090b60914401c660041c3d0340d580500c8204004039001c240d005042210005a00580c41c1216001d070940c8070564000e504925001c011821b0161402400240188440c0602d01e02c41c0c0050f0442101e010b224092407106515050700b80e400944450010b802041801c1142c0d4a00b4420801c0104207a50a2821303d52551005442405500c202505103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 120890809 1250 120889559 120889579
    0xd0825080d0c0504240906020c010801120f05030a17070507030804110103020c0304090f0f0204050a09020d0b12060601020c0307081e0304030602030f011d0c07150906061710050c030105 81
    0x40f40154280c5014200380f001520000469440b03131003980319140390400100344050004204284003107003460900f001170310f800d40d080e440e26000d000d450411282c26a6038001000c6a1030009000f84010840d03e6840e0f0707640492210001402c22110394094401c0080c4a001c0001e0000a500075072000d52064004040148200300e0301c0041c0c000e44644405d4103842e020000300418044040c2c0d001c44d4100c001d2070f00c100116590510b40008034400c60203980d9016a9040c4100000c0005400402548001c8a0701141d0f4001c1000410243c00c0c0700d160030710707940d04583c00300305665a04001400348500c04074014005503103444100d80c7c0314008a01e41840503034012031742d04112541002158000c69009004554919010035498001c071030a024545030070007040c0000002c6402642c0280c0943c035000030440c9040d149507188480748181e50f030002652a111480c03240030410a10440c0020911112040ca042109084050030500368110544c0b281c1e103000203010712500c210317060781d05445040e1950482 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 120892059 1250 120890809 120890831
    0xc090d0b01060302040e060603010f030b04050a0f0f02031903090504091a0403020609060703090209010e250201021b01020c06040b060a0b0c070f05040b100e040b0d0825080d 76
    0x4120440180a01005600000303a040d070541c000c2040f07640d50300040c074481c2ca43c02c0c2080400c1c403003807044120014040303005201248030824901d411510030401c407400d401045c1d0381c185810721003060aa400901c060550819802d00f0300c417000d1b40414100301c2c900809440d5402030102d902e2402418003d40c1e036000044104010401450742903a00c1c4075114085142c030386070007565581e01319031003403250041c0408107103040d019006588a81ea8020030a081030b0703003000300510341d41000030b101c0004152042c12600091700d12410040640c400f5900150b0f50b000b42003112007001c104424103141aa104000e24540c0310008a0510b4006134010410025601c0f560300240e8010001c2c2c000444403280021040000100014460210b0304a02d030a418103d83c1c0d0001c00040b154036981042e00850650124100c0c24400c0d06103091101000f40000380355160389011441d003d07071115048407140c0e400580c0079030b4141e10241e13510306540c00600c507038040c1c02190f48050550060141d07480c2201d483d1040264 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 120893309 1250 120892059 120892069
    0x19080105131401150b0c07030501020d09060b0105040e15010e1f08060d15020f0c0607021609050903161e050105043003090312050f0a05010608091209060c0304060503100503030702090c09 82
    0x7c021600b00300255141c0485c48004001010120411560341d8070b0708643c401e555015806960464000d81c0c0110319030b9a8045c03054000c8011500503504000d03403a030386204e507641c510103001c03620380221071042001000d040019100450107054140708003100b1030b8035000038100c400c03200d0b90f0801c0b0308400340e2206001500c1205601503441000b8441c080d0f5001c02028a07400075858a800041c07030002d2000d595504040800c5078019107035515690001c100000b2100c00d19400700294520602142c1454002c400b042c010302c4442c150204d82c141d45450a010038006440000009640f800d001d0b013910822004034490300010080b01201416240d615890525010700e02002c1124810fa03c240720324640f000c0780d00c0402d14110b41c020301d0305141000101d241c5105881861140074080000c081c0d18409000c8203040b42c2051402c191302150400c009884004148040c00051115454480d220709008007000d0201c0221380205000c1d5205100d800c4c007503611011485d0300301c15480300c0e40c0c1d071b20340140d40854 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 120894559 1250 120893309 120893323
    0xa110f01061511010b061b0106060e060304020907110f0706090902090306160315090504030807030b1c0807050d0c031b0302031c0216030e03070602120919080105131401150b0c 77
    0xda0040d00410484c03a0a80421f082d0103140034407138002c01c1701c0c2d03072501800d440078400405c90b0754110f0b0083c00083c00505140c0c420755001511400c02950004a45c0c01c818136114019241e20320a4200040c104000340d0840e504c10003130002c80c6000d60901e500341002c2584d034507000300420842c0340c0f1146107510542c000d038401036101218200450003142c45040c410b000d0300c4199022000944000001042c080c1f01c9e11400038005001040340c00036407450120802240a100c1d01078680c500308025002c0018030402115050500e40e407202170b81094241809800c8294420102940c5004400d01d400026800f00445050360081d50761a812a807480218034000c0c090541951040503040c0d0882007450380002820150b05811011201002d40705c5c10120b07141c0020540885580c0030a05c202401880c0140b0702e941030000300d03100f844e03140340d85294271030a5520548041b4060346000c48040306001e0450b4952611090500080c001180310200b802412031691041d03038202c0f180419043c940d003805000030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 120895809 1250 120894559 120894581
    0x90b070521041a130509060d020609120105090606150a090504020310051003060504110a0206060f010516140d1d040e33060a1503050702070b0a110f0106151101 70
    0x74042c40d0f0704901d82e0f4031083d80001c00050048012540004071031820b00c00d03842c8100c0c0c024141a180c1c80980d401c6c01448e0f0084004154090010010903150319000d100d281d103c0c241b400d000300301505056044c805400d460100001140c1800c001e40ba450340c1c0c0040d07100007160350686005a9985d035558101c00c010001d6003150f50711501860b100303600d13980d041d0000c10940340b08880c1000a900c101d50041218030990b618900507070400300c00915649400210f900509406040207440d01c2051004a0b0195000c2102100d00c0112100e0210700980e0800410070f001880f81000100040c911615041d84d005000240744100d071141900c504109080c4580202c040e0074080790035480c0c02400c241450603203001c005d45411600d510010b03200d4135200d1008021511080c00542c0c0800709a10201d0162200070312240540c0300d07400c0d0000340d4031800c400502001100d65603851a0500b400151400c2c460b040400140ea0380c10450240110b201c2c0d0f80196103c0703400340c140400e0f21545c0001301405000701c0440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 120897059 1250 120895809 120895829
    0x90a08030a1515020a02060d0603050607050403050d050901170a0f020f07060f020906070f0602070c03080d050601030b0a09200403050705090c16020f12120901090b07052104 76
    0x9101c50741e480ca401140e030050070070700e18038002511503609442d2041e0442640c07005a00c011004009410400e00410183d440e404011030b88030b44035100c0a02d018410b480e51000580001003c2050101c28451250105247c0c6000c5180c40302445c0000c243d8090909401010880880820f0030f014141d4051050180d4049082d916080d1510001c0f42e03070780102000355202400c041000400f503110341708032010028000d08079420000152a5101c88856820b012150741c0ea08001590110303d021105100951140382030300c1d40c41d0390301103840341690b101411244c145400c0030f8050b1070940d07520040b5019601030f80400210384501071003034000d100d0009180421a10001008800c1c40b03000700f034207403c1e0b40041d1540b544680343d403e008100c40c171515070b501c8224030180b46d20b000185003140c6800028100248180c40c0365100d20b007881e0030480d03000300307000041400150101e00d80d40c02410180040c200b02000600b410a00c0d1201c80c2c41c0c0311450411138004105075943c5c1a0170700d0071030503030b0f000d40a9021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 120898309 1250 120897059 120897061
    0xc0c05070608010f0806010e2208070501020d0b0f030607080703022101050118210606030618020a0515120417131805070f03050a060504151502010e15090a0803 70
    0x40c042c000070428040d410105000d5840030400700070004009040b24480c9040380c000f0398a1640340c280341802e610240c1000d601c1c00f200e080c0407a41310340103810300fa0f0041c0c000681d203404180400040301c01c00140d913400f03050a413154840d6550046541c550040300d0703003410f00055883c40004c400a00c03d41d40c4081e180b5109041000c5000b441042040c182c40d02030325402400d011401c0d50491824052140402840d68410020690420410304012580c45a040440c245803244d03128015501401016001c4c500c070074175a8025844c0c8528040001c00c815a64440c1c0240092004081d6225082ea8985000310200201d000c101c003c900110706501c1400440d03813200d0b140c603044502c7d1041e074420601120480a85a050400c00d8813400c1d028030750b19220286015010340096000d4407005201c0400c00760703641c000017140e03191801000034248000618960301c070b05281d0100c007904041d000700c000310380c909005011140320000d220032f55408105007a10b550fa5a40100c10704c0c1115401c8010500807003c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 120899559 1250 120898309 120898319
    0x30e0301020a09230a1509090c0305240109140f06030103080d15050906220c020109020103140c0405120c271303081f09020f12070c050706030c0c0507 66
    0x6007803d0306540010710184084441140b20301e682e4010350400302d42c0401058010030010310700c030540024800090038441c4034560380e20481e8046690500e54000801d031a00104140c008003003000890328403c40a400c00803084043c00200305c040c580c056a143da076001111002c182d030343c0d605400800302d0010982c5999603100d180c0341d030315a00029454100c3c141814121807100b400e0641a40c1a1000507048418503034400d000c00c48201e05003014505030444503c0d82402e8211940500414100c15800124100c00c0c18800101140c01426100d0a4001603005010003021050b0440c2d007202d4040764400740c3d0680810310345041035080355083c2c1d0711032134070500b049c20b502c05040d12042e009a02403614485039124200e04811000320180100020f80e80b5002914460501480c060072500641184c01c02907210340e0200105d901070f40101da40c1d00404105103c0e81d041e00c10b152980140c0c2c918041c0850f401c00e41d1101c2c1c1d10110760003248185516501c000c4590f03131050309884007803900f01c8112581941d0362 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 120900809 1250 120899559 120899567
    0x3030a150906080a1a091002160501050c03011a090d060b01051201061e020a41030414011b1e0f060905010f020f0d0518030a02070501030621030c030e0301020a 70
    0x4100454240090558845c11a48140a92481000004042d01102021007030a000960105011265881c100071040c80426024840e4074800c0040c241d07440e03525410041807050b0300710000c8612401e52401c22072003282352248210303010490341c8143c003c980c0e03504100050703801d07010f005282c402460012000281055010310301a1548031780c8070301d41d40510407422049840b0344c02d00710040d01c403500401003842010720540c0d40f01c602010751940740007400510700300d10390301640307800010840c3d078004201440000110900c1c89600042402d0181c1c007009400694031403c80c0d030b110080c162070541e80305924856540a6003076107459000740c10400c0895113280c01001044205420380c0c4561a005682001c3d560b0761089a6007240c00000490a00c41345401210180100401d03100d9001a51032050000b00c0c810400b4001601540c0c014100c0b50341441c1c00102240d03000d50141d042c96104c44400d50014410b10b4284c0b8140380c040c80c080790540c00798142950040604001ca0341c041d0300c00144849200c0d40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 120902059 1250 120900809 120900823
    0x9090111030a0b0109050607080304031103041502010e060a090308070804030201020d021b060c03070903080c01060503010207051c0c08041509030507060e01080a0515060a0e09040b04030e01020f03030a15090608 92
    0xc241c851072005c6844000340a0140103804004182e02c408001050109000318400c0c03444101e001c02303c0c2c1c40c003502c40a0080541c41030100d46805030b9114a40076000d01401e01c003041c0e000d07095403400c05c552400fa460060011001624203814807109502140a1520030340496169000e5210309550320100c610015114030340c4294040030b02e01890000c5400030341a1000c40b800786003180c0d150358a513820340d2500c13041c5500100c81d43c142036595804c00200c0da01c0a0024003445800349000c1e003035200348240c190002007200c0017060b0800c14842012400035801c9030954056440103845203440c51030548040d00e2081007908040c1003846030000c00940c40c1e61110084030810401e0f45c5524541d03c0300d8050b9001e0b10404d543d0b901801d6500950051b032030a04c3c0d03000d0009511546484510348865801180301d5410607102921426420340c100f005040d00a500e0040701d5400780300500000781804c00460300c0e404043c04e040100d58665084290f841200d4050001501c1a140104840d80e80c5524080d51046 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 120903309 1250 120902059 120902081
    0xc0807120203010e0609070b0a050408070e0105030708010207021c03020118080c07140d0303020f0f0304080901092301080c13090c0f0203070506270a05010c18060e09090111030a 78
    0x30070542c041c4d416103000300303115000d241640018501582070540b034041c107801507011241084418800010441420407420b8001c00000356000d55650600007418244101c079040080305030f004000d03030401a10382151840c8080c10101c4000c03084546407608a02400c2021403000d10030890307140c00c900384080080204221210b103411144825562065084900c1402c1c56a5030702190304480040401e000e50018864013240800c5945000c01c89105000c80750400c0e241601c0c0c500c00850500d03460358004849001a01c0728054003880303d65041180c600d036a10180c8154100807095000c00d201c4100507055a00e000c00070841d2000c0c0310307124400400204100c4000c01c0c0050a0814070200c502d001004569515130070001809240e80c9514045030712042e40b401204404508610040090b0014001e00041d203100d04000f1942c3c0a5004000717100c80380c920101c03414681104420440d07650841320007440a0300981c0c04128964445852500411640c102c00c46910000030400042d4a01944440b83c400303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 120904559 1250 120903309 120903311
    0x6090411030f090c011d10092601060b160f02120a08131403120a0203090a0b0703080c0906040303140d09050a140604170d0b13060306050924040c080712020301 70
    0x40b03003c100444224951642c03030813140a124801c244141401941e03a016000c0360b04000044e569980d030380d50800c0c000420006640d0310074840c00410709c0428000c0c00014002414503500b41030401c0400b09080498010040407068041d00e02d41c219100c520f8040550f50046041e00c181c190581020b03040c81e0302041d85a1459401700c04045103020700414200d45c20000035000f05029010509540819448181c07444154070041c0141e11159850701c44640240410704540c03a140d0381145409018100003404103010340200740030006054590300e041d102129003500d05504c200300390082d03030400b078030418040010450501030b504051020000303070b04121911415480b084c0407244a580d0b0340301c03202580c0081091412492011041411002800c0b11603a0f03101c0000b212a9040005845040c0444500f03132030649070881082032111500c01c1540c4044040050044040c03c1c05070010006003c0c42400302c0c12611101007030610008a00d5031024107040b00031504155100c0c5010380e041081494201d00c44c1d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 120905809 1250 120904559 120904573
    0x6070e040e01090f0212150403121506021b06040b030a0504120f0509151215040b0612010b0f07080708120903090306040305031b030a05070306050a08060606090411030f09 75
    0x1403141441402103c60b0420b2207520400c0c025030810003510b505000441c02482420004410380b240480080e003e644a52a0500010b41e1040650242c41c0440c0301c0c0511f1655104080115a07008201c2c80500322030081c9000e4041d50081c00215503029070740207001c081d10301000f0070041007a580d21850096000d000851211200035008586d140300a0500d140098018807155081742010700700d07860100c1c1c290960714100910340040c91141082164117803409075221340c002c17032103051920070061200310a8400a141680300301f04007941c80018400c503000d813440041c3e110303000c42071407003550186070344043c890355160b01d039040000141d0840940c0402010500011442c0082d00204803864a10050003402d00d5503110384040c2d40a400040000b90b104840c2911200f800e40658001c5119041110001803107041c01f100c010125000c981069018a150b02030506c4401800100d442d030140003118410b94801d054800300303014009128150040413804018403c0001401414078818071b00c0c00c0856002c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 120907059 1250 120905809 120905831
    0x3040906060305010b1e0f04030f03181a030f060307050a0609150302031314010f09050f0607050a02070e07030212010b0912032b0204150207031406010b04060c020a0806070e04 77
    0xd41d00c1b0703550130403600c002c03502c01d0004201001c0000d04049510401443d0520f07980e80c60307204c40c00c16080800c0700000c06480c01d540c007460f04d00c42840c01905600c60345c0602c052030041c13480c03002d00c009040f5484442c0d403480000c129503810018100a4140500b2280358103598140107001002c3c680104074041c05074031b0241d007001c1e11031320075640700741e00550b1458100e844540b503030440c44006e140d20030515500d0b61030003c0400054050f04030400d201d02c0090030b2045e03040f105241009006042001001410001002c80541c00204601515074051860700f481e15000001d038004c1c1f00340040f52275010040800000c02030400701c05001c01307100945e200301c01541c0b00390a6035124441d0151030340031030144134404440751211100300c95035503880e07600051a154881000340e2041280548003001070f403103a0414010041e1344001c000803244070344000c10f01941080e11070b0000c0d0003580602c9042003401c4180c2015503844407041d00041440b803050f52080c1c00d103c400100624450080d00d4081c0e070502c545949 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 120908309 1250 120907059 120907079
    0xf020c0103050712020d06030206221202030715020a0506011410030b060a180506030a020a110706080411031005090d020c1503011a1902010203041a0405070b1b0304090606030501 78
    0x40f01d102c0136580c2c200602c2c41c140041c00250002d0040032000c640d20781d0080300503142c4e0002805031114003908000307405034020901d0410052134100354100703942842c03003000580f000621041030f500f440361150b40c60003245504901d040d039000800381c01441014000640500181c3c0c40007680034094036940c07000c0004020a50549101c4000590050020414440c0700e0f84112000c1d01050940e00740b14034519610000558503800907242d00720041d5000504071758050300052820100905000a04459450320102500440c4002d20240405441e204041038a50701800500f5108200803400c0116003030848030340d680c07000c1007100c0002601c1982c1800b48145061880d40d078044078122421446c6a081c030300600002054505980c08000d8180036600401501c440c00034071151242d40010384902c0d080c100786402c806e01040000c804403840341030001241d4041350f50b800399416002111381c0e402c50b044004602c11001001280540004a0080b41c06592600301c1e904031001a98284240d980700e010800c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 120909559 1250 120908309 120908311
    0x170702010807020303100e060319060b041d070b030a110703230f09150c070e0421020c040b0a120308041a012105070506030403170f0105030a02090603070b0a0f020c010305 75
    0x1400d0800d98a01c00c107c001c6061190561005c0d01405440d04540b03000c00b136842450030040211500c5031248811003690800e40705003a108030000d0f00b0304000302c80c21030505484807568000c080306843c000001900301e55881e0880b6450044480c2480d59454050030001d001901800c0882141c2c0454401c40c41c0c1c1415450942c0d009980c2c1d030540e01c0c07400344039004221111040384d03c0c1d00c428103000d0210b800300480903c11000205070116284a052810b441c102c2e040b012421102402030310745400510421303038001405410f0400658000035000103160024060340d01c4d50340000303144904080c004003055070080701c0340c0c0550b2140c3c00100802a03a5064441703440d60900400840c1451300e0304031403038070605034440340c8010301131400e8411054a90000c0340c0715501c115030607030110b882c0202d0351500c07940800b1540e51140002082e46a02d5050400281c3c607840d01540180c800c10301080441c04030f039001d002080c000c000a4034030503030390031030607001030a0308880c0710340080036015140d400c3c042540240505 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 120910809 1250 120909559 120909571
    0x309010201290f03070504110c060a0c08070c1103060a06030204050604020c1504030c080f190206070509130b030303090d18050d12031b0207050f04140604020a0c170702010807020303 80
    0x118150000034802c2c000c500c50f80121050f8144200000014642c03203510a4015003424200703408d42da400515181841d082c0050900c0043c00c0c0350000b45020254005103403500002c291071700382c408030b5040c1042030007180d55440d80e643c0740c0601c8040c4401c1e10803580c82402100c0c030944080c09a50f50313a40400089000300b8103d51401d0b040584096600c4d0f640c090340690080c86401c0c81841807685845021060b0410021040d00001c005a52031140851150000c080403d91000b45128504400e0003043c5005805d07045004a415868032a030030481c07074005c01890b90014048940701c0c9008214a50342c0d16942c203220010914041c68641c0d41d0088102510a40340050a08004880d90381c0e200c0b620b03240002d141504041d82c0d817150f001145d0160260b0b000303916840e1f00900140f41000d04001610300c081902c14071480c42d042e09030b405d14a100070182c1d03012000f02e0780180c80340074650090310300c0f00e01900000e0440305402101049004100701500a050003079881c5910b56451030300507070b81c81c0320030340710 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 120912059 1250 120910809 120910871
    0xc020901180213060e04140f0c07210807090e070207090b06040506070804030201140403050303072a0302060906072307170310090609050f1306230f0601020109031205040c170309010201 81
    0x7040f4a600c03274000e050a901c29a21b41c48000d05131108000c180d40050f064400203004803092081907130344900204054500d120123400a0f041208019588400e5803094815242e1680d403e8100c82d50344078203031002880068100343e6900f40502e4048050361040c08100d002c1081c00e04015100e0070201c06807000c3d030394448000d500d50f84829030160f4000044159a9060905055030081080f241c040a0004c032446a00140098148020b0301d9083c182c00030404400c2100307030010b0199002c0110301800c0c030b959485030701c3e69031580c8500b01165000030120250081c5100001401007802d151117a440803210304002c00c20107180c035656614240c40059440c802c0184501001c910500c101c00b801200007449030390b0010b03403440c2444d21f20b41010000000380d245800e0500030003401c038180e070490b0340e0b2085003403000700020062541e02508415503040e03503a150a541e0350000f01000340481428002d0140d03904940001c406281e00c032540c90303200c1c42c00039005500b08491995003200920700001500800c2070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 120913309 1250 120912059 120912061
    0x30f09070605040b091906030e0d02030a091205030706050112050c030604151a0406080109061d030703050a020f0a0c03120e06090d05030403061802100c020901180213060e04140f 78
    0x2003184c440e82c2100c503480358800c194003006401c0d022040305401c000d00090303d01152482002e842c050a00f440340a02c0e40540d0003c000c000f608542c010001402d941240143c04141a0981010f601d14044d0700b80003091f01e494240041012415a038100d422240302d81c0403211007030602014180c69070811398004080ea00f40c03100081c1551142d80025018000c68010701d034284480c80e0000c0c003985d00a50103981c890b55a82d00c1c4005002440c02080091541c001e05400780310501c24034981c2e68400e1042c00741c1000404160100c03418801e004142c80c034080541100e07660401c034100313110207012501c81140c10144607103c140300c130b6010f205200a611f00c000d0100c0e0130405548280550030205280864541c00104000320000d0118810b203102c940606600b030360300d5802071060003070405540c80030a003800102285440180c1d9403107502810b55040c0c059108011803503041c04400b0380181540d20070981964003000c83c6e002c0e80840e610013004400c65041c0050612401e591103d0507003a00d010114541d03841c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 120914559 1250 120913309 120913319
    0x12080901080a1e021b010504080703030902010c12020313080d0903060f090503030414070501021903050d090b13050105011514032206060303031103090c0906121002030f0907060504 79
    0xc1d92564000c20780500031070403072503240102d00c50802e10b4082005040d400708034200e0105100e8070300b01c81c40341c4030700080116080980300c05480340100180201059101c03140b0b001164400d209a40c0c5243d070080c0152200303c10b030340f070207034032a00030300e01da810851a400000200400b00060b1400d188100e03844811030541103403101001342c4150300c075900c00b2a4861603603d00240c02000110b10907402400e9005150030f200c0d01c0c0c0c90500240741d10650455000c92104407041803204014411194075081c030a80d501c1c581140c01c000340c40d03e800c01a248100b03010400c091380e0107814010b250f59107c1e00080180385e8842c07010000d120f81c2100c40d4000524140302c1c07030615a0038400215000304290300c0306000303100840c1a922444d898040203c0f841e0fa00c4200070010540c141c0658840201c120344000e040d4607060340c0d540c2d0f036484010080ca2003410740c1804104c0c0c03901c3c0d139541554a40140c10664800000100140d0065801996038010b02940340c000110510b0001c210042a00c80c2951340a1502d03280c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 120915809 1250 120914559 120914567
    0x1a10050d030e061b010209040612020102070b09040609020c030901020f0609030d050417030705190c0809102007170c011e0908150402040f050105151c050907080712080901 75
    0x19845280d04210100101311604040c0d0b51007041c0c040c002400541e03520040b406000549035150f200403841122000c0c00300041c1c1c2c0204204083c0c40c1e0040820f5100d410711400500a042941e00c00f2860b18800209183e0307110700070006002500c4282c08a0324982010421903641c0d100854424085030000d02012803001025044203400c1400303481c5c0b040c5150141468000994800d44102d000b103500011001c840d070a51081c04001e8050905200d007a0501c25142c035102c601c90702100600c1036a44071040c000c510700408000c242d003007404405510380c2850615140c0c4c1c40c0114040c3c0d10b15059400c03105550708400040c44ca080b148103035980c07200f01c000c414030144078aa8010b07401003070101407070300490700c03100c04c0100d1000c0c010310011040d95410715006010480d18003816444205090400501c06501c64990344100742c0000300360582e40308000700040034103000240c20350020a0030501800304021001800100b51121101a40d04050380d9403001602c1c61281140141031403c14010000f00c0d41c02 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 120917059 1250 120915809 120915827
    0x10806070c020409060507050c06010f0509010302060d020c1e011d0c060306030a050a200405070c02120709050c04030b090f15100b0a0906020d260a0209030a1a10050d03 74
    0x30240001c00c0d1348a181d91103000742c0e41e007111010b000407408502079014820800c05240184003404a00c01c100d4140000725180900500010b03000c0d5000245511442c40207a040300d60b82d00800f41a5030000135101804200440020042c180c1c66082035048810131040c00010360013420b00c0340c001d1843d401140103004258000910080d41400780352042c84c04120b052000c4266244603001d5400c00704a00d1340c403407039550540c0a10300d0150345040200180c8a420401c00803030141c04403052207000c41d40c500c0c1c1a240c103d80b500080c800500700000c0c0200783d80410041d005507440394000310f8043ea03800310229500d0141001c80001030b4000c03040b200021650035110743d00301980d0004004d800c0d0312400b041e01590300c0305080d000000c41c4184100301003941442440c03400080d62601c1e402c89241d0b140c0e15081c1d00f03003440c0071a5030149218081113280d00c49604680135010081c094403500f40103030600740c00084090710803849001401000483c0520715403604010380368020080481d1000b262401c0701c0c1501 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 120918309 1250 120917059 120917063
    0x409020f0303030a0c03050109090816061107030905090105091b03090a02040e030a1e050711030a0f0308040c09020f031303120609091103030315090a06050d060c17010806070c 77
    0x40160165202600c1c10b0000314855590003030b011640000007500101200d505030302c44070103a4038010111000901c840c00312004880050300c06040300c107090070104020504824141c0b2460800a101130816406c00d20b0401122022920880c91b40e984030140100e40808540c2000c220f00d403088003404400709034001e540c02c503048000301e44604201e5404203003240c0c1d10200d072000e10347c008034800b0310441e800024074681c000040040000a407101501811070700800700000e040c2038158031000c500761420031a0380201500505d410140700c1c0c203402d002d4480081031f03406499a042010317002c10440024021225411003040c145440c6503594140160202d46a1904504100344107a40004614071402060701074032404800060744022498007405d001d182400080c0242c05c00d1080000c124080460480c250314159107200c11036541c0000034009202d00d40000354800f1100401c4014001c26078080025000e035502d420800c00c14008070102000400d10034212598018400200c0c2c8601c40c04190040314 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 120919559 1250 120918309 120918319
    0x91803050a020f010c0309020405060d0201020309131e1d030301080a030c0218040506090c01020114010e0403090f06050a0905041e1d07080d0212070b04080f040e0a0903030606110303010302040902 86
    0x402c0380f2140b400e44201441c0e000002e07032204242010f6152920582d03400400803103281100d200d4a90000c0d450b800b40b001c451f84540e0b82c0d20350501802100d60800820080c91f0100b0040c0d60101440e204001c01025901c0301003007128040150105200004603410380d4100c000511001505542c00c0344e441c01d03000f001b26040070006024640c2c01c1415100e045c000c0b0f1003103003c1c1006e07140001c000c0380f800381d00c004018110380c14411580c000d040c02e80319450540f210000070b810300b50b486050030b82e807a2001c0d6000600d00851032070000340b4568031070050204150580c1d6100c1c0c2142d620003c001c00c2d50303003152180ba060f242550640c0c0e0b90013155480340507440b0501100380c545080e00c0152030308251880d48080402d030851208004a0780c1d05011809a00d0200d0000a003800c4068841d202601c10080008001d41c0c0000f40310110040300c07000f40d60040074981c12922552400803c1e40010300b08007501103000ca400d150021818500899010700003806801c000c44c02c60713107950200009002e4141d0143e03040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 120920809 1250 120919559 120919573
    0x5070615050d060903030e15041101021207050106030201031a1806010207120b0f010b070b0a090201020a020d030314060603011505030a23010e0115090b130f06020f07091803050a02 79
    0x81e0b203500c2d0409110038012400020205024200602560414407008005400610b6210b0250b21014001ca4100390400304940c1004900301c0142d11308401458100003050000c5008800c00c1815000007055030701c00e80c0c06010310000c2d180b04c14070161860040b95444080d036001241c8800c0b0f070301c00170750303119005104541d41280d5600501c111084440303004c0d15000411002c00250411205840303004024900c0e0051514019840d1520aa10061b2406c1e16441d02c482118080da803080000c200081c0d0014101c90201d030203494007400030490740c0306440c8800c00d03110000380c041c5400002c1d40d040741c56807655202640c1540c0001c42e566030000301420405079841d030303807907207060801c840c1e0076000c80500802041a5050000188040c0c1c81607003c400200300003040c22142c180e0140608040f0f82c20200b00310b844038100d030498507020086410840000c13481010000d417042d800103500503031181010550301c0c001e07101d01504094559903401c600703a1600000014000034410001040480842c1c0705880f10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 120922059 1250 120920809 120920819
    0x207030e0103200310030614090a0f061e09030806041103061912030801050306010911090105070807150b040c08100323060703050105100206070806060c0c0406170d0c0305070615 78
    0x1c90300145c03840318440304060401d100b040190701c60864000c50b60050a403061502e50f40c1c3c030740e41320009140200340c1012500320f4410010305821240724020001039495180c0d142a00344030051a8180080e00002c00210229405d1b00701340c4115204910360010a03840c6a440c1c00900c50b5010805181000e0050003040c00544500f00c0041a40024441c0d0381d141102d52520007003500e03005e8180c01c0740e0043d0b4a84590200c02000308421a01e00c42828240992218054140820a4000c011010704160300140e4041001c00080d0f2101c0c0907100100ca00b040910802d5104a0344110111002a840c5039145802d1002c1080d10301820502c078000c080c03048000c01c4044015003030560a944060200391260010701c4103150183c60703601d0501c1c0910080501e458010b43c02441040c0203018a4000c000010b03e0700d000080c280039070b09604402074003d00486648500304031907402c90915040c0c1600a014030f6000b03961162162481d03458040c2c2e10782d070038658540c588030000d151200300700740803400c24000016 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 120923309 1250 120922059 120922121
    0x40c050f070501060f080f060a0b010c0204020c010e0d1404170f0d030506031908091e06121009090b010905190606020c010306080102030603030d0e0307050303010e150102010207030e0103 82
    0xc0e0040c41840042203407881c1c40c205d032100307a0b080c3d08074845540220880d035011f000c0000308280d0044d012040450b0000d03140005a07030000c0b1143d00039401900014a1000d100c60540002c25980701090845407814580c8104a90842824000d5050f001c0200801c0008031500555203640741c0741c0105803003c801c800d00303d641c54459006442c0001c0303500c032420030055280602008001d0000540c00d9070003003600c0c0d0758600c4039210b008181e0f842004070301081001e480e80c2d5410b00001e060080c060559410106c035401000c0d031800c4829290920f8008400300790f01b000c9d80162154258811851310083c0d080020304005064010680080c102402c040c1d05200f00c0a402030000400482e000350250700007130000181a222150802c9102e80c0c010070902c00180c40020803a48294100900003d4504440154604500c60010054650321021002080e103118002e5900d01401c2030a81a0f00070441c1d907001a8241c0c043d504002d400700b00710250100c400d5000341c029440259044601b044c0b40310480701d56034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 120924559 1250 120923309 120923317
    0x1b03100926090f091b040b04051c0201081b0706020d050a0f050402091b0409020a05041805010803030c030910050708060310110901181205010b0406050d020d02040c050f 74
    0x1846516280250001d40001d08a1010a9002031020a46410000d0010451499000f040795000c1c1c5810b10020b20040300d000d03202d0300d03c03aa1a1038265601d99440141c06980d4115000389846903a082001540c00d034600202e100398a5410307140d00d0380680d550400c14150300c82c10b040d00c0c0c0c2d44c402c04100c0d0707800040181c802040c000c080e8000004080c2042d9551030100c50303017040140e131614a48418440903a5400741d9680e80030f44503550044500d04010f031054180c0c01254400d044007800403510b0313007801d500708000d40b0035603c1040707000314030456013803c40013030b00c3e02031050340d105030001c10129040c0c0000c28019540440107801712441680c400c4000011180201e0756030300002d4240c3d042c4003003840c0c103000b0101003038407240040c04000340701410303030400d4401e41c50003d042c0400e060fa00c078a600d0340f2540900003009000c000300c03100c60190914901900d102540355100d145060804506490099048266150050416080d50540d036091000424a07440c1403424000144880f00d41030796a50014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 120925809 1250 120924559 120924563
    0x5070b1611030910201f0b01110a0b060112020408061602060714090d02090901140603070605040e0601021c090312080114010f0908010f02180a060c06050703150824091b031009 77
    0x11040d5000d00410807040b245180056410271601c40d4019062241c0003a0a50781d080e0050b03203600311038641c030005030b88031f52a0103008680b4600200380002c41d1200842e5252003412405e00411429a0401c81240c444a040ba00840461020921201c07102c4d1824068030385050081c0008400c540b1680000309103003c115a0241183e4542c0d41e040c00f270700600041c540c0c020704c040c2c00504456050500107003081c0601e010710b4036010700090008103240c0c0308000e0400445201d06820100001c1564001c216103032900003907031024210207075480c038240703c0d9210604888048049030103420701c110045581d4000103108108120b1002004200070000303104500000090364001640c50b0354031050310102500e10600c0508c03235400c1d01d00400c01681c01045110710950301c010001181d80d120381c000d40c001c1c00c90349484000502c7d50f00021421200c00108031f91209003c0c1c84103218800920886d2280b03034000c40d8400c081350001c0d00c1d05094015484c810480c243e60040540751000052105130301100c80315801 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 120927059 1250 120925809 120925843
    0x150a080114030a0b0f0907090e030f0d0f0905150708160f02010f0c0203040305120c030306060304050726160819140d020a0210020105100302060a05070b161103091020 73
    0x140400005d0822000d00103100c07d423402e00000e0201903541c2d480b806881030b00d95180c00002040403020310242d1001d2043e51a040c1c00b007000a0003030400c2940c030b084180384001c101701b1240208051a0184580c94820104960031341002445140c003103078403202c1105031605664a405503154524868000d05566241c15401191120303e141041032410b070750440701e52000b4004001a50040c82c01000b2243d0100080e540f1030361340c2d101c3d0700c0c0440c60705d640350f88007040c551b220442401c403024942c15042001200101194501e9103804900702900040340f080c101d041c1d1010705062030103c1e03014103085101c3e0051900c240d03269100800c050610000c46204001030700550309110840c41c2000841104007002c1c4000c010740c0c54040307110015031509000203885a100450003801d003600c1002102c00d007a5000f5800b1006042500714050308140401c20070300811990580103440182c0001507413045400281281605008094191481c038021000407a801d82d040001e0048440100031510300e9059100c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 120928309 1250 120927059 120927061
    0x309050d0e0f01030218100507051c0809010510090507020106120f020114030709060c1e030306050306060d032c0a0b0406030621030e0f0a0b0405150a080114030a0b0f 73
    0x1044102c5020140890600d071042c012402e14007102c00e451801c0e42d000742c0d41401035680020080c0c1d08d5015440004001c0c0c480c0c1d002e44030b00c04c00040c92810b908080c5444907105511104511030903100100c64996955540040c100014039050700256002582030000040792520399042c56007003079410505a40078151030f035081e802c5507406184d06110100080c011415405c14410040169075640b00c3c0d101000905030421052041506140c460398a41c00482071100300240340140c054107091260034402e00a58002070f106041207010300c90b040f03034560307a080d003040c5800101e0804a45040021210495241c0502401d034443c0c00d07114000e080413601c40c1d510b0303910340030b00181942d00300d4118004000303034010705807981002c038487c100039141d160038800200f000035004603810b00d200b400a65400550240b001411039050310080007610003d072441ca41c01d41100e03044214034030901c044034000a100344010000181040d00726a1040c100030103640d80f802d000d4980311440002541c00b000303044a094 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 120929559 1250 120928309 120928337
    0xb0406021c021b010504051203040303150e04020a090605031f141920030703092406090b0603010302010507140f0102070b07020f070e0c0a110307030906091e03060b010309050d 77
    0x702c0d507a00c0e18003d150080c4104c0ca45559040d490b40708074440c0c0c0c40c50002c0400820101800fa8128030880198003505d00c6420b584c60080c28411003090320305900072000fa01020400c48014014041034036005401406841050141341c23002e0f001b9100c600020583c1e4042090602083c02d480a00034280680c2100700102d220010104a891101c008400706414200001c5000c0c000400c5e40d038001c06508000440d01c60905010f42c1292a4002c041d0441e90761152000880d809548030314241d4601140c01c0001313400b1002404060700c0f0a01001c0e0201d0024428900000d000301d22422600c0c5641c1c0030348228040c01882d403802d9030001041200d04940c0b460030003010a6042192030f00c0741d01c07074900800c6028070380002004545c00251090039024070004404800740c0c011600c004049241504507955104e45080040030414580183c100281405100195002c2c0002803aa000d80c82009684941da14550f2340200070501094a54103040c2c07100c0041c00412002d10043c1803813882601e41803401e401c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 120930809 1250 120929559 120929587
    0x5010b120a020313030c02041407050316090b040302040b13060b1c0c08040b090114010902041d042109051f1103070507150c0b01062c09040b0406021c02 67
    0x5000280350740c4103104100c0d0039880c01640c444100c2c0c06050824010b851800418042e00c0011a209a178400303001c140f00719113600200961007440300b181310802c0d14040ca00c0c1129074680e5485000c00700402032001740050f25007588101e82c00d0360010154a101c08050881d1000e0b5007041d0b100c415040b4021986000a00c0700441241d10441c40e800100205c0c0d0310301101808140024101030100040c650014038407c0095001c80c08040340f4141001c030541e5100b085001940c001c0c01003e24204484040d1a4a0041d41406500650380800070040041c462800e00d01108030064001c0c04004d5040c4c8000303043e480e007107202c006815050b0b95840c11860382c00d10140034408842000c0ca5242d00821562010441c0400d4010590703c0c46001210907068030041110740007640200a809040c00600001700d180d0000c9014400780014540b101d641241701684c00c4004040031070890300104103400150004480000c1d840d48988920001030801002c0d10785456034192a009001d441540001c0c003128900b00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 120932059 1250 120930809 120930811
    0x111210020901090e06100804020307051c0c06080f0403080709050a090b01030b061e07050f0607050a021b0108070f0c05120d0f0908070210020102070602160b060a1a07110405010b12 79
    0xc090700b0385004c1c207020317022494004484601d03030100700b0341501060445d501070014a000304001004113562200d0151861416505084e0803942e01141550000b1421301030780d905449100180000099503030b81c0d03141610f9030f103001403402042100c00d94020a4a070b541c4040e41000c0c048809001030400e40003070001d8201e55020340114403800c07050140441c00891001e034205501c8a10886546a03045480e10f14500001071600c0d110a008040802c42e820307074840040d042446d007940c2111100840a0386040210003004c0281d40029000d100007200e5038040e00000f0081032031482c3c014203466907511901d08041c402c04070f01025080c0040c0001030402c05004101d00818410010003c000e03880e5900000e611488034001d0003158545240c2c203840c2e000394140c500e440d8101e1025540d4030103021612901c01202c510448211100c1004200303941032190210b400e40c0c05030308840049000f4a134030410250840340d401c070713141445d080b2882c1007030f02e903030003840e0007002c64501d120303144d0f1846100b650f91158 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 120933309 1250 120932059 120932069
    0x902030a080c010510230f031504170306100c03020c0901180e07050d030f0c0606030609020109091a010e030a02120d08130809010c14030c0705120c0d11121002090109 73
    0xc00d02d0600440c506d0802c003484210030881d5540544000d000494620a0480241c036403502079030341c5003850001507084c11403055104181e220722200b0b5000d0161002c0c081078031a00e4004d8000340703540d070180e0700654100001900900494a0340250760001130b4a0343c03800d802c6402d400100d000d8005070440e060003030003080740395400a40b600c0c0d0f05004c0441e8020520030b50140406c0b8104021401c070701e0098103401c00107900b000d4140034907522410180e01030002c860b1700b01c0c00107022020002c0d51111510134511006100d16488000c0b8004900441d00102414840c9a142c0035442041d401a0354606a411512008a000e811014030150000d401544014085000b00e51003004080004000c0011180140f80909050080502e5410f081e11902105140442c052000084020400d180003071000e003203960883c0d1000300d004800c1d09082d2944042c001c62070701b0190850f5104002241d0b89450320603e1009070144108408080c3c5492800e50020b4003160b42ca9800100078200f541d010b841c1c0c0d03000e80 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 120934559 1250 120933309 120933331
    0x2030c0307061215081605100801120f06020910090e060109151b08070503130609050a0911071b080d0305070f03021602040509012c1207060902030a080c0105 69
    0xa150070b00c040e00d050b0100e59072518159842e0511840e0050300510742000c0d0000c0703412101a00210881c88504180c07034020707140b04071b50b217025420640384501c4459051f1849248a4200d042c00c0b81c0e0b4405024585035000c5814640a00c142c500c07580f111480c41031400c1803660303040a5039203410200c1d9046031019003024100290400c09000720716110f40245960442403800c803002030030982035032032142000200103041440014003d0140074001001d0000369003018440600d1550307491307080d1511080d81c81082d410500740181000903000b2580001d001e10052240c00703241810701e0307594074095624240400340c541071015052040000405c9002510001030508100a050008002c1e120b48009a01b1808141e00090301c4031041910465415070554050700910440c1010f40d00240600300f010810041d548010304809042408a241da80b09a4070100140c00440200d2103c0c0381c2e103034460342098a905032200181ca005880400031036000c5401840b00321740759481010880c1c25240007a0498400d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 120935809 1250 120934559 120934573
    0xa090605090f030a05032a0a0818071206060b0c06011701020a021c05070501090b070f14040603150e09030403060c05130e06030a05151b04030c03020f060409020a030902030c03 77
    0x5007000400c90b0700f4040d0b68201152a5a01c0700c024451f0800003103400e00324100c4c0d00304481550a02080030704485003407078441040c01c0d5a50410994003600749d4540c00126405600100a4009901d4080700035900500020480310b480c1c001040300c580c0205081405035001400400a010300c05000310700d8155031500075840d00c40c40a000941e1391000c0003a0381c601600001d0030501a0740103104032010650b1003002801b0403103030f9081200c903121045501001044000c148000307624454a072542c0301c2c88112402904003410010304070002e0100b01501c20401d08072610204040b1251100351b80b2840c22400195951801d503e4604151520b1110710310610100384285540301102070000ea007540c0000d01007103041e680300740001c1e140c42480034002d88180541c00e036060804400b007807994851601d01c100d80da800c054480040030144105d10003c0c2c40f150389004140010721380000340303c415007402130a140c2403580300d03c03070401268091840003003c6641c0d03640c40c0d0118101440301c05102c440032000b420711 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 120937059 1250 120935809 120935833
    0x5090307031706041b180503070803071104090c0305070602010c08280f02131406070302032d21011509050d0c1a0c070902031303030c0201140a09060509 67
    0x1410100c03003501110300b460368000450039150307070388540140440b020500d00d9035284880c015098209a806011155102082c0851036007400500781e0100d81d0301b18001c40c41c068290700d80906c0038001844c0039a002e82c40c0c112a001240c03058034400051800b480c0600051450200082d00b190034481ca80c000340302e00c0000b000386032804100048030701e0b40000d002e03101c1608860303890f0005080d1070541c00c251500c046010707141080b144500d002500c1c02c608800c0d541010401c00c00006d4040c1a1380140140d000300705400320a443c902624455281c120a0000185116000340b00290417440c08042c0031281d5041c4c1044002c500e002460042445c240e0b0714800905c080802070801003540100c60241b03041030045410000c0f00c0c02904010251460140031340c0001c0007186c0d2035684030b8410b0110343c0c4161031010070004400d10846e40501d100c07046645c0c1000c559542940a48070030820710301907542c0c40a08031445a00d050301144112040000010800381519141c4100d034405404000586d11100141c1d030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 120938309 1250 120937059 120937067
    0x503180405040f02040b01020a14031308060f04030f0203040f17010f0e210405040e01020301081c0f0806040f1b0f0c05030304110d0c03050c090a0504030f050a020f1f0509030703 78
    0x243c00d5030150740c04102c0c044a20700607803030480070900c02010005071f03500300d407000503010000c2c26403428200400c41e520b41e541c14a01e543d13024180c035000c01c18100040450b0020780031302c001d07064802c0f00e401924203107607503500404440c188940c460107505a0141040700c3d24070080c0300e0034151480c0f62808110880c411182d159485c40d1100c0b0a68001d92182c2031040c240004005a030020800100240002c814a9003010b010b03410170b2190b444103100344000c01c0d09003115015000101100ea555071804c9403043c82040f112690b014184540241d540c100a5240504038091310368061034200d4908150840445c0040c080071040c2c00180030002041d82da240092804421607030401c0e04159189203400a08001488030180b4180080280700e100c90300104000d4045911f90803204101c0e01140c69940c1e2070b142d0810f0b503004075401400102032654601c4139901500241c5504009441190740060714142d15500e4181d196642c0c443c0030340880d890303d030b0705122801410f0b800703081c00010350308003c03da9402078 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 120939559 1250 120938309 120938333
    0xf0703050612100e03040b1306090533070204180510020a05030c03040c0803031e01050d03051207021c080f0c16060903050f03071701150e0405040f020904050318040504 74
    0x80e043e0f5444004010aa180c2041a01e01804282214a540300d0b86003000392203684a41c0b2680c4041180008001002d190000c808c2da50440183d0044280500c40c2c50b0401d52160b0349104807404e0003091062001513140c0d0312a0703c40e00300c2d582007071411007a40760a2042c035000082c42030015503801005040181a841400d49401c1098418095203940310b0b4074003c08a080c10390403a00041c800441001a0494100070b0544d250b0030f51404008203076214010700854004100014010440c00c0106000c0303201000000c1d54072210034070646807041030a41030342085c84840000c02c030001d0b0303800707042c8030302640d072240c01a410000c0f400060740390030804c10080b104207080c114041c041d2640c4049040626004004842c2040907043c29940e80f4908101301424201d0300c102140702d030308082e00020900105a010900d900c141903210140d040210200b00400f4242c0144200d542850300429003005884920080d80070312701c08c00203035440e132034510280328900d801800c0726403186092106200c04540304040c15 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 120940809 1250 120939559 120939583
    0x1211060a05120405030706110d0e01020a1b030908030f0c01050f0121030302040308040e07020f0106050109050d060b0d05060613060e0a020c0c03120d0608030421050f01050f0703050612 81
    0x90b002070754550609a086019600002c0c040d039040070403004050110000074040c40e982240100145082c1c8070450b8200e0064100e480e011594000d44061141e03c1a04d00c00301c11442440d202d203000b41c030b4900460440c0c20811030714820060104032070303890840a020300c59102c0e17880c8103502d1407507140518408094941284c800c408051100864003818881c1e01210302031500103d90998942c0c3d038041c5d610100c00100c8183c8014060050070305182071043c001d003012210142d44041c400350515041104800d141242156101c1d500c0002d040c00303440d58904c998400d400f40b0054100380c03921200f03000380281041c04400e034440c9030140500005228021582d0050030034400140c80300e6400000303c0c54000742e40085076251060b854062400d6501c03038020089120110320901c42c0325074540e80b40e50b41c2c1c0240e004803034945031107809940e0024280442100180d001d042101d5090034074490403801c489094906128503080c030420051043d400d4020301d41c00030415100c3c602d4081d00c1108041c3c84800d05000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 120942059 1250 120940809 120940837
    0x4020a0504110c030a02160905150f061c050601080f0118180b0f0a0c0201020408060105060706020f0a050706060f0503030702010809010e03040e0114040e0d050c03131211060a05 78
    0x144201082d050090303415040310302081300d07a0b40141c128040c0d518200b00e00071804044d00c2100102c4c2c508250300811707010301c5111803055102c821100421a40f00702d0344c08906d03084041800642c100741c0400c0c5081000264104c40052941400c4e4001814031800511035030b810000400100007101e21003150241c1468111000a0094816a9a8900030203294800b420400c0c0c1c410a00c101000100d107868041c0d101c181003003001c1c1100c0701060f401d07030040f4400d80407160000c0700100700a00b0202d008180b5203101d07003001450000c1e603601c41001c6030800c16000b00003400100d0324100300906885010050143c01403440d03207061614000a42d00e110307055000b41089500030105200460035000014174556990a0742e49803070b21204000e4401c00300b4451011100e01c44408104581030a00c40c0400446a40c00684080b050188050314550320618100c112031004021444c410f048921270200a403015040c44004944107040020b107003504c030041c09205e9081006004c2c16290072800322008000b078594 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 120943309 1250 120942059 120942071
    0xa0f0e071107090207020d0c06080702010c0e101211030c0d0c03020418090f02040f020c0c0f09010303050304140a0c06020c090f1503121810050c07062115150804020a0504 75
    0x20108101c40501080181450391148c030128006800c142614414081c1e0740c000c01c040000c600d4221002e1002c9520a5001042828a00d160b42d101d1200b0f000050b05101c408a60840c41c2c0306211501c0c6e00c11249030040c0480451440c00c0500d10b401484c0091609142c00d509090500c0e074040d0401603d003400b1303d0200ea481c45418100042c1700c903210006500204200010707841d00f20440065800500950102c0c01007520452080c54814408140e02030040c0156202c0e81c210343c4d083c0c8483c2e20140050b9084c0c0e01466085044000421148100e140301f0408007011615101001c0d01c4d0604052240d403043e00c0020800c0001107440313000650112107031807522005550000403c0c2400c1c0980702c444480030001603e5030700d4254020720801c58020075115030f0080781400e04111a42c2c080c00440e0941c039001002d0400105104e00368046604994142c0301c44080c0030100740400b110f614640710303007101c210040c080150400440399500c0841c0182001c1441d460030b0340c00210108114002c039849250743c0e130 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 120944559 1250 120943309 120943313
    0x602010c08061c02040f1a06190509131505120c220b0d0b2203080a0507140a0c050106051207300b0f060d0203030a1d0a0f0e071107090207 61
    0xa0f010f00c8041c0c01400401400c200168030300c0142803c403085900b8101400c01b06169030030300d41c088405003064100070303114440e92a1400c54aa500401d503440c0e02580300c00d900d85500794540304400c103090a2000ea41605880c0c00c041c42400c00034900b030407485400c01542c00c03541303840e110314440781610242c0c00341d00c4400301001c10100034024000c3c000d81102c5290480810000701c0c3c009a801100e40075064030960000f81d080c811020940c0000600040d0030902080c0031603a01e0304116000f4409042c0100c148440000881c001d401c0058220300041c5102a2041404828402e8030040c3c03105681c50f90300345460790041641e030340181c840e410454098490000001419510508900380503118000380e100d10383c1421010100c01741d442c011000751130b0002c60300c00e24007452a6070350765901901450a184500000740c424110000441803820300d14004170b0100c2d03540c81c0d40c4001814500c5084c00c2d21509101c03c4402c202e50003403500301440290040c0c91600100061014201c0f900c9401c091f9440d00c0714 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 120945809 1250 120944559 120944599
    0x607050c1e1606050306120a030210200a020a0309050913031202041a0c10060609140a0302040c031a060a0804080f07080a0305010905060d080a0f26010f0602010c0806 73
    0x1c0340558000001c1410214000e0340c13001c0110300400341211419284007520121903114514400000c0240c0e007c0070381030481480c690000c1412605070fa80c0240980940d046d02c0146620011200c030068003c0c807410001c02d9002810080130f0301c3c00355040e64461900303c110184140e5911000350131b0002d101319895a1219580445000e800c14008207207031103213091544081a04a555809294009c0702c102d042c0c4040c0307a02c01e4900300d4142d65614580742d032034800c0004540d24107280c1150042001540400941c46034086c1c44107044103540d0001d9508017400c4510400c0b81c1c0c080c80c951056808002100c1e006a00055407504503801034822991030301d600500c88510310890600a0204d6408200303401d400b6003603804103040340c04000082c42150303a132204222000005030002441c1d220103015112145211b180c641303d130400340b82801480380f1341119a013500d08074440d04c2c28540f203505900612038442402216002841c0d40c0c0000d22520794400310140a42800421460281c0d005022012112180b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 120947059 1250 120945809 120945823
    0x20303180a020a031112010b06040506070201180b0c070501020c0906040b1f03060e0903070f110312040306020403030f0206070906030504030c02090f0109050c0c070504090c050603010b07050607050c1e 88
    0x100904003c0020b0703403890640d104040c81600c0602c41c24091400884c40031040c0101515410002c044030321b01b40c2000c0c20030586400040c400d03070402c0004410303a4949803078096400c000c1d011124030240ca07140390f010a2071070506103402080c11074005088a0786a610b070354850344c3e0080c0c8100c2e4080b41c001035460205d81100d440705506044282a02882c0021680540c03001c1d0654030720315080d40f060354450581035924442c00750010609082c004107000400c4070000c03043c1d02004014103452200d075041540d41020b8215801c1900c0703c0d50700140800c01c050b003200c81903c40407600d0000d8100c0346401070b0003500d07510540c8200418140c40318001030030503200b002003810b0746030b0042c800f000908041050b814003003c2401080303041464072010032080c1072010195002c0c145510000c000f014245820f10000d8248140100d802580c036003404540b0741d0300c10001d54040c16124070780c103440701004e08000345040d10207081d038824884100600e00310808041100b00c541080c081c130440440c80c070903d1507494111 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 120948309 1250 120947059 120947063
    0xe03120a200304020f040c020c090702030c1e01050a090b01030b0606090603070806010314090304170a0602041203080114130b0f030d021b03030a020c010804030302070b010303081e0403020303180a 86
    0x211a010012101c0d0400050741c010350003911420740d00107440c0309100484000381d80203005644442c0102c2100c2c50100102d56000000c0d00c1a0380c1801c0901580074a03161039a2206034002070210303070600c0803500900c40e00740d001c040260184800301c52034580c5408950f0600018080103065000038006403604070444103210805407d107a641d181c40100101044030580709240041c0c145070791607000416141c2d056010701c0c4164040c0d0724080c90a032a0725511112955584030b0b81c052030b04800007060240c80600300400c981060020328111034580180303d038205800c03081094407419442e49140d11560000c0c240601c44280008400c0c0d0150700044455250743c52507a07051044510b18900c440d40130480000c200021081c1e95501c00d0014101034481c0540020840183e0015040041a62040400319009070080c01d00601e8020280c41c1c1c05c0030900d00742c01c16000700b040c890a0000d41881d0b002c2600000c403840b0b002c80b126042c90382e4000c0d26844040c041d006658051480310701d4059062240e844119 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 120949559 1250 120948309 120948341
    0x2060a020c060a08090c0d051f0b0a0801060e090604050a080307030b040e010b0f09060d030e011206060201051602031602040b0604051c0515010f030f0c1e0503010b040e03120a 77
    0x640c0f00c100410103001100c5c0b54001c3c3c000ca40d000c0342a414803580c00300015030300c0740152464260409868211420544007041d070140c9402851085841d0701754010041c108400000c59034900f005154142d80d6406041442164022000c010110b44086480c44070745a00c49a0584e5035210020220042c012840205520500d44440c0084c1e609055101d07904920066804111409100080064410f01106d00725003110845c1c4801d00064815040a02c4c0c0b02c805044c8004074900601c0781c5000c84225030032802c0940c2d03440e4240906402c0e5072605841d00b030114401186442120401c4501c8031900310790007030203a0780f2030400d81c2c5140d42c0c41040d10b0161401a04040705500700020302d60003460300c410151018007c1100d042c3c038100366000e045044e1620b90200711a0140385954418084c040214240d66025144401103403000c0710400d511110700300c40d2811609503081c40308050031109408103080c03041745400d5010101c0300d03002c016184040301e01108004903a98620604001d0818015002d10351 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 120950809 1250 120949559 120949567
    0x20d0203270418030216141002030417070302090c04030807260d09060c03060f140414040b04030f020f0706052802070e060402390613020102011407080402060a020c06 73
    0x7007800100000f860030f0082c3d08a40382c5c0c1051100000f5000d0581c00780b0481a5240b445540060800304815100801387e4812246015950b1104840740407000c4101d0b04550003e040420070741ca072829070b090b0400c00346d002580c0f41a1071036850303030083d20841030010041c41d844400c0128442160303680701c003440e6004406c2d070b07943d500d1220074000404c0c4442d8125440c0c0c0c54141c2442d203041c840d20a20045d11108545090400c0c01e08440001003120700c10810b80c02902d8045100c43e101041d071109001d03c0c480d03030054206007442e15000c1d005290141d5004110344c041da1800084180c00174031541100e07a24105240c2d9620002c021400c0d40481c21000785907951141d4a43c141e032980010724004640046800461903215a0304200607445880340045040d41c0540301380414444010001c40c01011082c035411181001740c0405007044022144014000303444a9010f00390b50b020b01440c0c1c0030900e4003c441419141210300503003041c00160010b0302450002c40c4003401c860080015003030008004121b183c407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 120952059 1250 120950809 120950831
    0x1080a05060f10030e1c2007091401060f0305060907031a090c0903060a060e0601031a0301050405060a0c11190f150906060603021804020d060b070b04030f020d02032704 74
    0x703421408148400391091b803850384031020b0300420540d07258001d6a5800d17102c2c80e101c1c2540c6003010207842c24188900a420b00014108500d102d00100c2c4100d55410000f1503150001c06444500e10244d00d8041c275003864102b003425a03030810740991000560a000070b00380c89516003007000701522202203402888403020f0199080710200544a5034504130103d4209655010b0424181c0f69944180c15501402501140c2c244d8000d401c84080c3c40c5505444680f82c20800380001d095450540c0c0c107843c0e503040502840383c0d824680c0114400c1d21041e050514841c0500542644e6411811003413840c03c4010028590401c803035030b180c0c10f0340c0380d401c4003400340c010040c5d1000c80010101c2000c111403003864080001074190003030090b544a0410b0400210480d00001c1c01e01c8040d51040c4200c00603c0c0d55400c001c00c00000d4140681159405001e205906240500c2d01400c0907424542800656001c12440601140d0001c00c841000c04040d00c0c480456200390014154150b0140d1500d91142c2018040300d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 120953309 1250 120952059 120952061
    0x615170901020408031602121f0203180114010501030b04060b0f09041104090e0705100e0f030c030316110a05060a03021309110705070e090c010e0a081516030b01080a05060f1003 78
    0x90613802100c8d000404100304d10a96a2500b402d030742d030b000360b408600d01074824512590103542d000c03207000c960003420a0051605401c440301d012a003200054008010b20165916218100c4c1001c0c05031420440c1c1c0d81001041c54041c0909083c00c1e50042e40050310f000c00c1d0f1181e070840c1c141c401d0121030241e20345803688140d001030040030061266600c6003210000b1541b902a00c4445500313000c0d00c44011141042080c80b0a480c41d00d00515018030485c030307000c082a1401c0000780f804455880e41404030320200d140000700520940b0f60281b054a100d4400d10099890b00221180d18406040050b1384555603140c508134018642c0c800d80e00140b8045441e03000580400c000c0040c68031550a440050340c80e50340001ca0072070305482100c66503000e1100d402803940544115060a24010144140c0b01d0381e41e61580c0c0b40c00680c4601c200008036403070510219051034102c0050840c090f00b030901c510014440001c0000030000e00904120f525070020590a48a000c580c50b0740d42c0003c0c00d500035840e041d20020b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 120954559 1250 120953309 120953347
    0x6090317040b030c270901090e0f030a021015050102060f041403070b0f090a0b060d030201020715060303110102030408070204180212160e01030503030f0717041203061517090102040803 81
    0x5c6000310f000e0b48400120740e0354840c0f6006600c00070040c0744242d00303103075940e0300038403550029811902c503c11142100e08002c001800004199030300a0244902d02c850540540c3d490401400101d00d210005210302e03070f00410321582c01307041e100d0403400d142c1d260706000c032105a00c401180c0341400005100404c2c41380d800440c0b07228140ca0a03490f81103407201c6088a5444ea0880e83c09040f071400000410003900d404044140da40b8007034030001d400d041c015180d100c500c044c001c0c03100c0442e0782d03990001c10130075800802c0c007040c0000e084001c50070f600c1c00e03844142440c440d0a2009104581d00c1103003c51a1001c140307204492500170b0245001c40340102c5c4919611031404010034108240d00c2e000040e003040000101d0f041e07a034004040c1d401c5490300401e2000001000c0c081c1020301101100200b403015803c00c0e060311440c022000d0000c1404400405402c446a50700310035030102a09034007001c1150480d060114800480b034480100d5500c10003594020300581c0c01440d0917000c0024600c00c11140f154081c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 120955809 1250 120954559 120954577
    0x2031906060905090601080412080903070206041d0105060a02030d020d0f0513140a0302030f0702060c240a02030105010e0d03050904060e011703040501021b180127050106090317040b030c 82
    0x20413210b131518001900c80110440f0010241c0340348205800701d0302d02c07803842c154004401d8402c40303082000503400201290000d40102000c1400c00b0303c0f41d00c0f640c012407000c600404040d1003840c40e000c01c0f050000e4491049011075004130b900084d40c0d010000c015800814000060802081719007010710010f05162250442612056402c0050074103e01e40440c003000360070341c95001149004941500c200894011850030780e884603080c4101d000071042484100703000400103544c0d41c054551041c00c0e55035080c0203880214410f01c1440148000c1e6003010180710504d03021114451030f031007540750072581351241a40315a00300d400d00c400021500cbc0847c140c5410386525080013000e2403014840c103652401240b14490041c0d00c41810a101000305040c0c01c2c1341050702501074000c000f2589000300e0004401e0344405005050b10388000c003107408144100400c10025203041c4660b500d014002010000c85002c0503080154041c2d800d165800c036038080394018000040c24940b6494007214404581d00840c040c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 120957059 1250 120955809 120955819
    0x1170d0e150c1b0109060c2918010e1501030f02221a0913020105030405010e06040b04030f09060806131b09081009020603010e0a0b0414010906050612010902031906060905 75
    0x3c402281d0f000321034071003d5071426610007504500c603464039000d106d410140c2c042041410400310502d40c01034500c141c410707170401501000b0300b541c51500c18210303043d00c9403a62040d00059026a01540c011310308604481e00076100c1c04902c0c0b014000941618480d00e44038822107d0415070000808a941007a00e0000460781d103100c4000a17541480b0f2109003c540704032142e10608511030044d801071014541140c010800047c00c81c000d80c903200e10b0010160f034203490315600c180804c0704040d40f0440907c6400020729107822034034640000a44811000f5000500c10750b083c03e511580c00c085a48859410b42040e9070303e28070300049160207040200240508101400703024840a8584485e005a00441e41d0240c050740c0b1f10780c40c0858071445224068048502c4646030882d1204694490103100d0000585a51540495140428003801c44000b40d000070b01901080c04106201c025110840781121401c400141c3c2d00c0c1d5486038400e486103200c12000c0303585c0e442c0c4000404e480360301c0805401501c0c0300b658 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 120958309 1250 120957059 120957103
    0x102431407082d15041b06030b130207030e0603090c030613030807021507140c03030a0605101b0f030212130e0117030a0e0411120f01170d0e150c 64
    0xf4103245104203004100360a1343c4814440803100b00c1100006502c5801034020501c43c090b400d40805001c2c0c082c0e4460400692100309055092602e010024030207003000c0c0b4114600582e41c2d034040e02c030311100f072035035480340d1000700020310071010a00c000c540010008055a04503e000f0580c581e41800008046d0002031218002403011400005c440181403002c540d041515501c0e01021501d150840400c0550b0020601444d02000030400155000d0a01c0303030004120300e420310b0244203000b00074151407801c100c10711011440b951071003c90a44910f400c40c610000c9a589814160b203003822a2141202c00c01002070400b0324007100240240c2600e1454400c4c40060740e907000385040e940c41020440c00755400401004e013401c0d01075010f20708441406000410840ea400324180c1c01500000900b010000c0d12004110400403030701503145c054084040360f02846500e0706060381c1d444c000c4100f01001e006140c40003038007503070381d103103100f081d07a41075a400c29a00c0c10b100440d1511b96458184d84821200100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 120959559 1250 120958309 120958363
    0x9140a0513030c08090a0905180d1e080c040b0a0f021908030610090b04120201080108161206020403020405070c0b072d03061502010243140708 63
    0x7101d00314401e0741682e108180840b56071500802c662244400c0c40d8442e010040005404101d80521886401c04011541343c211b59200c9441c10049110a4038080104bd00c1032441c000550104110406150b4034120708960759001c0c0d0b80003980b00d20307007100102c040c002c00d0320200d050f07000c0c41100318654198242c0d0312a600000a408a11098200003440d50310280005183ca050010000c01000514030f081c2c818999034684040807980150000300003031200350b03600d80540d60082041070040000c80c008011005103043c006001006901038280c482c148a401c40e424040290145c0b0051741c1c00034010085420400310180000034403a40486801d203580c400501c10130300541c211494a07000645074106c3c0c0c02c00100082c0d01444c0c05940e0024191369520124170091050f049400d0807000d80c00059807a61583c40310300010080044000001e42e19880f00401080340c0072203000814220a40358480002910b070070380711720380c5052600e1520b03c0f801c200001c49e03140015091000260803000c55527a24260 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 120960809 1250 120959559 120959581
    0x7030c080606030a0611070f14070605040503060c130b0a0e040f1a040c0201090503040f0602010b030a08160305090d060b01080c0c061b09030607030b030c2205040c09140a05 76
    0x880300c0b01e601d6000040e215012a0700798110741d2150301c00b0400301e40b509003103990b40d003054040c084007540c1400c00d030400c00000c9282080500050520750912034141440d220029a40740e44c020102c0344001c002044800050b00c080684070064494028a03036103a0302d1442d00100448501c0312040c0c4130f5801c150701100da0703220900c5100a6207017100400811a01050280304c00b0700540c06403d4110342d81c60710604040342003413010b04040c01000f04e03551171031840d143c80282910313031400c0b0441c0f0030f40000b040900011500340449100c2d190f03140b94440e0b2819203080076501400b80d05440e0b60441610b01280b420050240e2154000700802d803202d05803503c40d811100740c203000300b4996454980c80540400e60301d401c00342c171807030b004c19100f00801e19007155000403d082c10744c15200b00000c00e807034154403400340c17805001804140d00b0907201d0403c840c0d145002401000400e114508002d9a60404a0140003036444c42101401054000380519000d070507204e6140b00c02112413680c032a1401c00407810300100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 120962059 1250 120960809 120960811
    0x8071211030601111c0503060405011a04032004020406180905151905040c08090c01020604081206030109140a0c12050304150c050d092607120f0203030c07030c0806 72
    0xc5100001c0c103554500c001566483c3e85842040000e10820700702c0c005158421111141040882d40c4180d10380c1080c3c0107120944c2c40607001050400090040f9280c0d40100d48242e0b41145e8020a018404446419200c1407401d0000c20f07031078000c1e00015003c0b07410f03600000e06400040005071890700d00c84c2d036212031004603801901c440100700340340300e5039414501d09402d000142140c0c0c062501c40807982d0320002400c41d500c011984001c64068410018400320a20101c0ba11403030078005010245040c1d42c4129240c4102d42c04880c0c00b5103207402245c80c50310254020010203a00c0311020b800d202c1c480300d0107035640076100b108031044984c1b44000b08800c018500789400c21940100114240390400060f601d402203080d40d05000c00204051140104000300100200820309454020710b1509200000d0740340f01c40312552000700079890117006da400c200010400220346d1050860205100203162031200f41c0f5100002943c180320200f040c2d100c5240101e0f00c002100c0c0302d0002c034244913039030f05043c17626400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 120963309 1250 120962059 120962081
    0x30c0e161d06040506070b0907090e1c02190c15020a0809010e0d0b0c0304020a050402090d170c01050a0b1f080c03060a05040504030c060c180311060c0d080712 70
    0x305981100068481039048428074010041a45082c941c450011500075040450141d4031044c610040c0b044100040c0042805403444580a0001141c3c0481700c641e501c0c051410010020340300084400c1d1244240319401030302080c10407180381c10195041103080740d410b5014020100b0072028003509040d00015940301507540c4001030302d0518040400556403848421095504900b4911b10000080c2c203145d41184030341400915952641000d00601051309500e4118501603841005242c00301d6841c4562210303160b03482150182510b490002003d610b004000c1860703190343c01d110078010009182d0700800c7d1000e00a40c2c250342c0004005110460020b1002e1902c00812412008075400800080055500440c00740030036004599030b50206046a00c115010707000185064504402c02c941d5024113001c039052071410034401d21403007505940302c0940c1c0c84010842c4143d55100d15103a00c0d00d50a079101c0b420348605480640d08181005050004102c40d45000151251540302101d03d092140e050250 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 120964559 1250 120963309 120963317
    0xa0609060f03020d03090b0c10060509011809080d09050a050d26060103110c06060102010507031a040f09060606080103030806030d090608040507090c020a0201170912180307030c0e16 80
    0x42c0b03983c0a10001c2481c0140640401103641000b2034220b0410000740b540800c3c0000520012901c50000303412a00e498001c18402d600100c01040070340000e030b800f16403603039280070300080140841c50940080c0c4901240c104446051038184001c1c014081403100c000c9000e00d040d2006240f018104841c2d642442c03288461544111140450040b8040e0400781c1c0480103040000351241c0c040d811020036001041985120fa003c4030402c542540e080c0941a000301a5040c14000aa0281d10041200ba000040e5600813503132801910408085608a0948550061401c0100ea5251000104103982c00d00003540805c04000108000307080005050ba00c101e41642e402c4048d0707081c04000c90b074070500a0310a0f60a03124030000407071100d1145c401e5a0341d54003590020241c0b0f00031840054004d0950000381c0d03103e60140402c00400303042c00b2501d0385194020307a801aa4a0326454159074040040c00c01851f014414884040300f0800c002c5d0201c402c1e1000c00f468440780381e032900480a80b416808070a00002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 120965809 1250 120964559 120964589
    0x5090607050304050106080304091d010902100c030201060b03040803060306010b0c060402150c060705130902090604090c0c0b16080603010506010e10020703080f030a0c050a0c0807080f0d050a060906 87
    0x80340c400c1001d150060711500000c83c0c11551a40501d15641040c1c00c050486540c90780c481940c058001c1c1e076080000d41c0b03400240241c0507a0b400140340c2d03200b5038811340306101004001c481014400c0d400300000e407011034805c54690910f41081040c41d041240d286000340b26807000801d4503803482d81664501d92a500c024407166035640c0c2030010030884100e41c41c08080090200c40c0c1202c07020b00541d48156600c2d5180d17916030700742c180b400350000096070009144901c10080340d441d44d12401c1c1100c0a403100701e000440d204801400898028042d54805006034000006108583d0054400d034080c0200d0755641d081c3c580c40e560101400c075007040c2c541a020031200342e805055400c00c58803070780e40c105a60045d2018103aaa0f00d500032158400301e040c1d0b21858000040003c818894031540c00b01d000030389011410628190006803140240c05805882c001c000301d032200130407071114102e9504007540020641c031a4400c040100140400b81c400e10744a905000010940c02100c0c41681e0460f40f40340204011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 120967059 1250 120965809 120965821
    0x30f0610090207140a0f1707032c030f0105060109050114090904141006031e0305030c07020301090816060f41070206010e09161e080d05040e0a050906 66
    0x9520011040740c140c103160341001e00310042800030038641c500946c003201942c80180703089004121068082c100c1d07600c0034008500883d50003c2d1107031003031208140124114140c6186d0103100b4810640c100d5143c0b281c1c1e168140150310640000c0d000e984280c0310b1040b816101c80054400c1030720310503c407884000c03d019000403031904e14031154000d80650a4200024000201c0c00c2c1480c100c034480c510038503240e410800800006600404927010094407801c00d030916658020003d12024042c0150000082070000c103540e4217621116000368000c094564442c0d00004081034007640520a54440c3e00d0b000c41120840085d024868400882004003030501500c4a14080e00750080919106e06086103603040102207507410940340940f80ca5001020b181d031400d20700c40c13400310380100301c00c043c2e400441d04220305000b10f14440d4203980141c805100700022a040104944803181d01030005032103842c20316007143c1e411200030320603034906c0c510b201025504d0b104038400392002580c0c6a02d00354001c80c0002d035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 120968309 1250 120967059 120967061
    0x20d06020706060b040f0305060a0b030304121401090c0608090a11130f0504061b030204060c17120a0b0109170c0409080d05040813060f020a0201050a09090e010902030f061009 77
    0x4aa14480c0c2d0001a106885444806081d00b107500070000f25021890180140031041214540c018500c140a00070360000300302080e128084d40c824001e6010040128400308540641c0c017549440c2c1800003013040030458113200f00484014403809000c1032071200400e0b00d012000c01c40c000366541151440300203581c0c0000f84030f00c0c03a4150344c070080c400d43d80700880d00482c4418080e09002c7ca00916000c225240d65004030081c200c1c0441c1400207061041208101300e81c0c02180a550043e008502110400300b91000405540300d01d03200d600c040090304042108408a960181075500020381e640390041d62915150f808107400c96074254995071150035015094074040d0031a810300b038450000d980c20000d480200200380c681c2036408070f82404010511600d010002003007100201040d20300401104100240692036101d692130185c100031000890030b03074540c02641c0c11030090054280410062150140759030080c40c218034100d210340a860130556446070006800390240f007091666065903442c00301060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 120969559 1250 120968309 120968317
    0x3070308330312070614070c0f0b0604110a1107090903050f210f04031209080d0507030b030d0203041d0c0a0c0507050a1410030203010b0901182c0a050103020d0602 72
    0x541d041c0f240d402c01040801008024012a510600001c1285e500c07441030113510900007041e01007042000850781012070810b00d200c5408680020141c0031607100c0d1008200a0400c0e02a2100d2943c0c0c0043e00300000c03648240d090002007810f1040c1c41c070541e240c2140001340c1720380c904040c00081080c0143c51a0309030364001050f40020408411b1480d07042d0010801c03164070304032103024804c0c0b0410204801d26070004040c0050351003c00c010088540c10b681d41c10b8041c0200c151001a40d035545000a8030940286c0c00808011070007011076080400f0a01e00035907942c0a0700a16410040340d040c50340c5034660720700d030a9001d2a01c84641d542084200d5404540ca1117182c50251414800c90340005038903100d00304c0c410058078450108550408a807801d00003040d4980500c442098410401084402141400d40e014407400f440c0401100c01804660904038207542c1110340f17007080000c3c1c11080100300c811a0500c0c143d42d45842c116a40e22400d40408680c1c0034403020390400303841140c1d1400552207900030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 120970809 1250 120969559 120969661
    0xf0609120f0a051b010207060804030f03150b0403020111060708060d0807060c110f0a0b070309050c100206040b1e0705281d030106050a0504020906040b0c03070308 72
    0x3101d0315020400310501d0080c2c407101c140d600da000010f4107050104403a9041003014001e00007410098078011004000510040002e810003291944081e9454882d42040a01c014903c12600006071515000c0d00303d640244400c03808909105009000d0b00004202c29202d003205031100b092030340d155014402c8500c0c4c2144100e5185000700b00d0200001d0040c444c0e030500b200c0076601d0001c4140c0d640e003154074010320003280125541c8540c031880000742c060720f00d09610807440d14000c10102e055141440c9451400100b443e80004d50300c07100c03040c640c0e00058042c070460044c44500c81c81e8a5a20081030404090340140481400714030001d030341c0500903c0180700f042c1310f4102004000c1010f1036036501542c240e04001c000140f00342803200511320b01d25121031008504074001c00c0454170b80400070b80e01c024180f290034001c3d82c01080c0000c0355901e65046d41e00906001c07991994410041ca405078882d13000300c20032801706155001050040b20649c0610700d085524800d40003d80d0a428500f9540001414003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 120972059 1250 120970809 120970813
    0x503030702060a0c151b110d030b0301061d07081e040b1305010c08040b0903040506160218010b0c010c05270406150206010f0603051b0a020a0209040f0308060f060912 73
    0x20013000610361a281c080c207524201c1c8002074254400501d0080c241702c51a90004200c0d0745400d0f00c1401e071010500141201840c20001344610000010902500840e8040e001890702c10a50610448001942e184502c5040ea14a8039694030007011152380c00c0381c610708041002d40e503800140001c1401080b107800400401c41c07580146110350b581803e640050f010200010b41420600013003015000e00d20760045184d2001e9130505007008041a4179010340c00d042c0d11014203140e009025500d0300854610b06825a01c000145580c6901d45d0000030340c461049500a0362808800c01c4885200d4819038403c0e4484040c14045c48070884c000c0d031318001da2518400d070301607500c900002d2103c440148074245050540c004d4000f070341c07415118114000f080c2d40701c4001e1508210810490501d515028111286031f140030603161404540100d141042c00c0100035041010075080c0400c0c803000207501003100348696109600d5503580c0c820300030030641d01e8000030740110f0705200104072803421015044031080c0c0142 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 120973309 1250 120972059 120972077
    0x70b0c0d0212040302011a03010501080a03200f061b2109010e1c081302031e101a130b0105030105042a030b030d0c0305040b030916170114010503030702060a 69
    0x1c0603080150b4142c0701100980c1d900c001d0142c1c00940c1030300313124984030101c000f0461036250a00341921100851001010440b044094440d2054501c07a98843c7c07030901c9080b207804000d0004c1590f51500d0075503d04001c40504407800c201a2102022a5a456a44010403100b03041480c3c207401d0540e4043d06030182952688494a181c8800300042220703000d98071100c042d01242032801405000b40540f41c03910544180001c80c0242c0ca001810611803901e40b2102814582e05601c00c5081c8840b80f4192241141440004807802c00c440755a588991400c03200749241c900305601c054101c1e9142c80e600340c0444d5003880100110b10b441e91150f8410207191040c0765501030748844c0c66036032841c101c0505e030102e07a4a4081c89040e0800304000c0b4a1003005007001c4081981c00d46018001d80180d00c02e84c01c1c0c0300e900000050341500103001075000c038140b02c40c12290030394451111032241084940f4a032140e45c60828003142d041d500082a038100c45024010754a8001e10f50207000c415403181c8034003810f01c02041d0f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 120974559 1250 120973309 120973327
    0x10e01050703150503010603020f010e030f07060203070b0708091e10091b120803040602131e090b0d0c0509040503071401060504050610120e1f02090f06070b0c0d02 72
    0x2008140c0301d40990b54000401c00641000d610206419030005030103a03151500920050f03c400303420804880702400d1010004904400292410302100840400c60181d0b10700003c200f5000405070071014410411460141c0d0b95070f8089070311035421a02c1e40c1c2c0c42d500056030b0310a6052520000311413641e0070f07001e0b502c07801401801c0c0c0342603a040d1502183c2e10309000d14154940340001c081400545261707144441c5800145e1121020703404081c10107403046500144594440b001d40200c24001d220400c4a400c4044454014000c0301c20244103400109050850481640c0782562892903d01c2d03012040c004540d09010501030080e034020411101071004001083c0490100400d41e10401d10010021601c10300304000d100c00d0380d902038041801551080c0d0007485a54005141001c16060101c0001c0d482c0c2d107070399210345016581c0f0350f0140346d40b1000030480403070300340c503002014204019039004841d00f9005040c440103101d0020f02030550040708020811107089600200101c0c0960f03240036040480708 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 120975809 1250 120974559 120974561
    0x5010213060507050c0a03020306070503090304050901080102070b0f070c03120e060c0408070501020d080609040204060b0a050706050906040c3804080c0a0b0a0302090103140126010c05090103050603010e01 90
    0x6904071101040b0041503c0d01001303800c1001d541c5c14041035031084030031841c560212b540c6540146c2583c05001c00800002e005640400c142d41c01000010189511941c0d40c1d00075078002e44c0580e10580728042e070600094440300002203094015600f1b0369501f8185a200c0e06c0440d0035049401041d69220f4130f4500c0340e680030904200c81d6001c0c0041c1c1d880c4580c0c5a117003542c042e240100c90741c0400d042d90442e011760040e064002d051554410000d132180c450f542c0d114030005000b04240e4101f600040000b05d2107099103070348a005001410311440b020481078441e00c02403079880104840c010300e82071041605000001c4090700403500da45104100c2c0d080d000206c1e10045036402e4145501079071850101c0c0c02c10124a0030054415000350030784107040745a04006190f6101e2162401d000e0605400080c210501d0b4880e40c800b0900140303070740c41c0215550b1580e082c820403501103c0c0500c0e24000709a0107101c0c040042c41400300c441d0f926201c852030b0106581c01940500300041c1610703855541c2e59500b036051082 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 120977059 1250 120975809 120975847
    0x90a0e01080f10060605040311010210050c180d051c14040801021305010810140a03060908030601030c050c071e030b04050c04050c0a0207230d0c08010c030c0e010c050102 75
    0x70480240070036503400c1802900d40311802c145030450b181019030401a460300a01200c1c140d80d080a40132a01511810043c0e1170301c02c80a42000005140c1000c1100402c114409004070154540030a071100e15078030100b0520301c181e864042c03ca9040440700301107410101d001c0f220611202d0810300820383d1540d00d04140768216030312005607a50001181c3c0c00c1c0045500d800b07030180c0340c2400d02291a040284184800c005203015503c441a158a4000303e00d941750b2220740015030380841c05200e50700c2ca526100582d030708169115408241864a94544180240141c030103141d120001860042d1500345020001e10259851242e10b48003050040007007500658803d109900078001040c900003c84248011660010951540c030682840300301806075000ca90344040b584211f403e1511072050801c90b402e08456155001e074440b54114003441004150f40280080318201402080446403001003901540c218120075000a0b581030040101580105c004101e6180900001420145050000700100d04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 120978309 1250 120977059 120977069
    0xd0615020a03020c040e030306130f02161a06060f030703060b03090105040b01060e10112503030201230402010503070e040c03090506060d030503010521010903030501050f0907020c0402090a0e01 85
    0x40380c2500824182c0411a6101351802640e08010841d0f50303070407281c1c0781e02010780200c0c401c5c0f00142604050981c0ca401030003a4502c4070b1011950f410380d01405c11210001443e04030348220b0003041307441c90560341407035031403060201030901480c101850082e143c0c0c0303a0ac002d0580050566413000420200380384000746210ba110070000051340e0074642803614443d0301c141e0120041062540340710700b2075114007a00d541e03884442e060032414940020642c3d410305c0c490725000d03000300075480d544034581071403d00c007001107074000d800801050b102411404c24007400c02c0001099180341001040040d4403503401554045040c2c43c285900303405d014005415241d84440035000a0345400c0c00500340301c4d044c0001e98014808603544900034005a070054a02e000c1446400d10942c80442100340520130008000700030190007008100f865800c4c60050700410081c0150303400b9400025100c03e150400c4400240a24040c1d001050b22084040410020f540031302c0340582c00001325140042c0064001d000d0a010701 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 120979559 1250 120978309 120978313
    0xc06090807050f06010302010e0607110d1a01090506010f0e06130b03010f08010e07061808150709050102030903060615210403020f06040c0308030a0e16030212150c0d061502 76
    0x4141420854504400c150b0240f03282d030011001040180e8201380400c100c18410741e8145e4070303a102401c0c4851207000294100780c10419400e510340802601c200303c01c14121040612030302e6640c0f16082071080380c4c000c0700d8003804138031040040c0010030b0061100080e140030081145140802c089600c000a80240d4040366034000040014441d96541c00c1944000e400003200130022034207945601c680d12045441108284580c56083c0070700c4408104900f00585003610494456021a2885085503c1c0454402c0d000980500c00418103600c088219208014010b00500f81d5813035203001c000780c0800b640b070720302d409850400c0b5890303c90700c8070448480e43c0c042806503c511884c3c9401d02a040c80e40e081d0b69100d45400020401000960a40743c0200362a005a03059840340c0c2c038203840000a190583d050034484c41850300380342d0254031a10443d42642e1080e85c420520501c42212690b0b0740c0e1070010307801009901c3c1000a0910010079000d4140001e01c0400403c3e080e5a034515440b01c8541d04010200503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 120980809 1250 120979559 120979567
    0xf02160e181c14090d060b04020417030702010f0504081b120109050c0a0906080304060c1505130c06090b04050618060406090e1012231209031203060102030304120c060908 75
    0xe90380041045403e003189480a0b8940a03820740002d18489143c01c1c020a040c0c1d4901c0444250f841e142e050b500902a14070125940e8074209070160b5981d08110741c12800a404036084c0740301c1c28862420b9a0484030000010100800300c03c0e0704110a200d1800700c15041051111a469114024040c20450740d0240002c0c2070004a00310a00000000300c0e00859125400c1c188200b00d249400800c030780440e070303043c40c0c205031422080c0783c82e0000c0044c1c0042c40d20128103000501c1981e0002001c40380710648100c459000e4240c0d2400181d50001091084d0040d000c02448200319600f00340c402090200000d45601d0124510103002a04c46d4125411a82c0010102e020501010304024542504041144690000c06207000b0700000c2d11412280c0c0207184c2c0c885103045032507544546204212075a801c0040e41d801c60307601c20002420707030040d1899a2003171140e4210242101c0203402103d00030001039020354507654594031038004450440900342c003000442504103020440c9031040a0b000c600c036240c215030f9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 120982059 1250 120980809 120980863
    0x20a0503030c0403140102041d0417070c080c040509030301050409050c040f0e07140f01030f020d0504030201050603151608060619020604020a0801020a1706040f0f05070f02160e18 79
    0x20417182e1118032029a10420040c0000210402c6480c01c20070f50b00382c1303c82d003a40c2d245007884c038500d60740400c60020400440c2d8101040703a9003034041c0c1912041d408891804a08d0400c20081e9401954030031166001000148410705003a0401400d40740940c040390140c01016000c1000c0340d0340640076903455a9920180305c0400c500b071204800802003045c04d070000b03100b8100004c0700001c40c108294185541c901c111480c01c40d075901078aa0040212008101d0303403030b0a06020303001e4442119404e12900070904602841e440401c1c9140c001c2440f24000a07464544181c141d90a030006045558001803e101201c491182d09030300760300c001916809006181464410301840b800c062704440500d0b40148110380883c3c0c0e21000060746a10203280d620055103940c008600103003c9075600c0d8540500b40078441d06203480c2e81d00440d00885840d59500100305010004a8586e0184050f1000d0302d03400314810010710005003602908201104142c0d4000081c10b010703280b0b08136103082c1d100c00d0440d64030130f2004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 120983309 1250 120982059 120982073
    0x5060604060506030c04180b04020d0507021905100c11030415090603090305030a0f02041a13090902090c090f0901170607030c09050d0602070203010203040305041a2503020a0503030c0403 82
    0x41505031041421404c0c205c0142c1d48074021802208020f00a060030000d001c0d11642080000320800b51046548244031017181000c2c01b0111601805803081c42e504c01c1181c3c1030900b800c02d406402402404a81c90100c80e4803019217860020a41040102c00945460107800e01c0200300409428007441c1d048606407901514050903988144285031401500b00086904042129406410000b0028116901207201c1c1e00900481c0c03c80c00550569110142c88102c500380104400c0e500003440c00040c030740e201800c100703a401c02c480080d000000c9002003002c03121074101801c001c0c90300900400043d54070001203175480704240c1c00401d001803150100003840d0b0b014010b40c0e0300300109290910030f90803a888042c0001724103104a0340200d900c0110304051115582c1900c3c00319078018002d568074100707818003c1c03d0b07801901512034203034852410b4814000800003180c0b0b10352102c040405280325400e0410100700c1044400750198081d1201c902d0004030700340015441450041c1c405a00c403411802c03e42 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 120984559 1250 120983309 120983321
    0x1206090106150504210605070201060602060a060b071712103206090a030503040608060307090b0901050103050c090904031d04060317030702030d020304030f270b0a11060405060604 79
    0x42100382c2038001696019511000700e50944180500c8440c190441c140c200e050301000c104041c100919090520622a5041d0420401c030381090b42200c042e074817038150041c11104103204000c552031042140c4000140d10b0546241c00007031000105061041d035400c8880d180b941241c102c0c0d994104107405001c1d2000940341924035014081400f1064840d640c0c1019900c03505d4030f11148900000308001c080b03a500c42d18a04040d581c401e0036203844a54031701d40540a4001682c81c00d200e4050b40384081070454061080c850340b81c500074a142c1c400d901c1c0400543c020a00640510b00126003045500302d00e0700d840807130602492207030b654004074242091804a0407000c03003070070b144124200a03042021031091460403076081031214420b6501d4403014410b82c0303180f081d603040d248254004400c00003855008841070400ea8080d4441c002d01c032126039401d02807080c0144c010001d01603404000d100800e07811000e01644c151078100090041000040381c1d04d0850112411101540300704104086814540121 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 120985809 1250 120984559 120984569
    0xc03020c06040b06040b060c0a0c06020f060a0b0d020d0b01061209050303160e0d0b01080105331c060605040b0105030105030d0305070309120201020a09150c080f091206090106 77
    0x1141003855001a140e2900d1018002030210a5100081105a52142d200f548904801020170355110f115190103500e07040c0b02481503a50030740b91030000a02c035001103020204000e00d0702c003400d2280e075603a206200034000c5903800c030b402401100c507110060301d4000f21403200b03c0c0513020001340da605d0035100030f0000c00385c01d4007942c800303050110000004000000380c3e038100a032100f800c48001c2c0c00703207170072101c0b07041040c10150300412605c00700303007401038011015060b2403882009105daa900c0d5145c0c2038450804c0000544900541c41c2c82c0c0e10500e0a1390895111000014013091603600c8403000001d608646010070740d1520b6440c6410441e40c0792900c92050b01c82020700b0300750f08540c5440c00290301c070360b0003040b41c40505803900005000244070f03500c0040300c20703030002d4800b40100300c04800030b0003500080215408145051004102d148001070700480c0e240b402d40e1034215401e02551280d11a800855006044040500003242c03590b5403d00080401400c1c7d4008040347d18001000500391060743c0d00c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 120987059 1250 120985809 120985811
    0x1020c0f0309060f030604090c0b0a12020a0e0609040e0105070201230609010501120e070b0702031506061b0115030503090a0e3c0906011502070f030b1018050a0c03 72
    0x405042c503250b8100750b4401c2020840c19079120381d2a600450301070084a4001068500e400d24081001d102c400701a00803010503540b140405e51001000c84201c0c4200d2102c9000300d2244403050b61245011b44c0184408035000e48045104143c2a28041c2900e00c15500314015135110b15040e08800c0344446070321100980075018075120308001313000c40c64061040c02070034100b0500c2503003140c3d078601c940c014940b1085070004498019940303101384032454000d484224481d004a81000d40050103038801680581e0004041901d401405500c0c5401d0b181d41a581c4140741d52a20003423181d4246250340c1000450044018660310400001002000c1d9103c0d00580c0c00c501151061204405841c5a40780c3c1e075a0040c849551103000d24422401c0c100b440d601702800b04500ea004002801c11b0214000d412140d054240380303811a164502130341c4880b264001d061070010340300001c01c0814a0380210319001400e43c0388604009464400c1c030302844a04040e00406035442c4c40c140f107a910a54816032100e13440500d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 120988309 1250 120987059 120987067
    0x20c0916030b0607050318040e01090302100c1b1401050f150d020d230106050102030a08041b0f03030507150e0a060b030c0a0e01050913050a06051f030501020c0f03 72
    0x20910005052500980c020940c0c0c0d0640701e551501c2d0344003140c1104d6001001c503903c03000340070241c120407460a0354190159042080854641005004a403201580754000d0084c0d44150b030000b000400648403000108200103080703481120002d008120903d01070b582440c0010b546049079800e50748050454000d250002c0704100c0c1c0c6c070701c1305940410208000c680d0910400100d000103008940d000f10080c00c407101c1d254004090300c143d03c1d6551142d0080e01d0082c01542e545000590b1130380640f01010021802d48400074002611840303030850310b5000ea068484c4c0264480c8103e0741903580c2904220041070303000038400240b00c44003040c0c001c0c3c442180410700980c200e030392035181c0704c0703981410042170161500303032442c09a54144405002110042e142550846d6501d540b00101e9800784915400765084c0c8012442c0135542c01410440c15400070018041c0001941d100c10043c10010030f140700641240c803406c500000005148001540501c0000d070301c81900c170303403c1420070681e091a40340790380c0100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 120989559 1250 120988309 120988321
    0x901061d1f030b010e01021204030f330b0a0605070b07021e010c0e040917070812040807061b0f1805030f030316051206060304060b100906020c09 64
    0x41121a1514041511200900184010854540758901c0818809008a55a0106a0b803503840000380700e0090740c4003191500c0d240016615250315492090b40010100814000b01d18040312000007140304600181110300c110903c0c002c02c08500040310202081a00689544032080c0a8100440c4049951402c0709162500142451151a02c000c0c00e43c0e02101c00160114000c2c05034001d01d107840300c2011120412003001c1402130080b00b1402c00490001c0c80c0c41d610320304051050020b000c0e40882504030305203110748100751540044000b181d00e0300c020881c250340441903140e80c50103540f082030070355242c861524208050b10390141d90aa0410f2655440103078940e07000740840b07544400384c01e00d514180401c0780030b0308450700b0703641250b50588a110786180e000300e000002140320b600e4001c40b0008085c0e094604030352070302c1400c03000c1214192040202d4034900d0143c00550304184181000900302e02c0d141c02003000b00e198902c040c0049418100c0c100700964060141c44c011410403241c0c024285066 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 120990809 1250 120989559 120989567
    0x2121204020a0b041d0c09041e0c031404030509130204030f020a050103090b0a1508120408010605120c04051320090105010e03030d09050c0a0801050105210d270e040b06090106 77
    0x11105c06540541c400010480400b000d40c115282d841d80034106208100c115401c0810b1800a01c500e55411440c084180e10102c0c440d00c00e0140f840c45000c400e1400392102e41b011102a0408004c07243c2c408883c04205102c1c0703a0a10042c4029445514a402e9410382c0d8010444d0b0a1010b46c8814180342c107001c81c0000103592419401e0380107000800008a0400400682038594591b400c000200d00c19685113038107610020000c0d200f221f400e00c000303014071034440091141080000300c0740742c004d81c000304920510349481d0b002507520403420b1608c0e0b8000e081c0c036143c0700c85a2490728100300d6040b0913150b142c00c05041c02c4000380c0c00340100b800d11015007084400420f9403441202c0300b03449020703034030050309040007000d0161404103080101681204e03600d4218482c0205003c0c46400d210741c072030401410440d215021000000303019034001e003010740304d050002d46550452122020b41e110402100c400b030000414502c201411807594010b0062416140000c00c00c403000d050039216001c801c00402405030701c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 120992059 1250 120990809 120990839
    0x51c050a0609060f020a0e030c030106150f030f0603080a0908070b0d05090708010c110f060c1c0f0c050a020c0409080712030212040b0f0703110a0e0102121204020a0b04 74
    0x700c01c1000880300c2e094100403000b0a6450105000d4500001e84100c1a65001e619424026011401e40d05d07400e450b03030209400c0f207580e4451000480c0d03643d14000005402040040c80690380da0601082c0c2e40d0032081810200d4a191300102e480c00350205802000b5580031004101a000c10002401d00c04e05009000d00b940c080c00450025240d1144001045000b0a0120100411908000784860840b01c500070782480000f1480030070b07508c100185402c1044001901d1405100d00e24411072409001e402610031341100903d10842440c0c030f03400e9101c210156481420005e481c680d49203074403124442802820f04030b0401c05c2510880c00c00b040f00010505150844a429030311038522505e07140c0c840d40540c007a0040d0149480e0404041d030401c01440b013900100c500c960000d02012031966a0403c00b42c0890f2581c051941c940c0d00d0610a11010300d000303076484045600140111170803500212002c60b000d0b84004840c0c41c003603124006200842c100845c90340c014004c540070b00c50516060025010001c50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 120993309 1250 120992059 120992063
    0x10b0a030510061d0303190c14030307050711010c021906020d08040c0603050415060305010204060905060307021e0a02031b1002150a05130b04030e0f01090617070201020c0d020601051c050a 83
    0x18060031041195a000c00441382c1f041030b003030300c0d8080b440c1c2d0040d005040a41d551505848203400c0080c03244110744084120791150300d95866150902c4010f480b04540c1e0a511482c860602c0800d05580c40940c0c1e510214041c40014100b819000300d042c004000d05140c1a50803110511580d10b00b8000001c189030305402c103440c52850001000d9a442c181311030703520744000b007000034946400408418420103400800544495440d5a901d20350342d20240301e1940310440748080140c014080c14800c190003805040f400c190054201c911000c4240c00280c1002c100c898150100690000800d0550801a4510720580101c2c006080801c10b9040e2500400074020010b2030303c540d036900002c40460000710310224180c1c122950007031514103403902070190b240d80c0f0243c0348500c44d1074040c3c40e00b0b50320070013116042d5000d80e91480001d0a039500703042c80310100980710405654007401440a5200d04203c2032800075490703801400d0952400301070100000c45007003c0d185015041d02f403400810800212109059 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 120994559 1250 120993309 120993347
    0x408060901240f090e01150303020a0203070b090105030415062c0c0703090e092e0506040b060f250308220b010509090c060408030d1401050d0f0804050405010b0a03051006 75
    0x1210307105c0c074900400313840310702443e04080f411001c4181580081d000b51034a10940480c0e86d030b0f64480c0b05c0301d0194014420b1490016204100040000b918071030400d4007242d02800125481e5100e0400d28040301d00101c403174041d110b841c1c2c2104845000200e101e900144601621407078000749442c014030a64681c06010346003070202020904019042024048100611180328512000d000d440c000c9401c00d010150861404d01d0702089980c5006c1c072410103010030085c042442c040705000c03000c00c15001101d40d81074080e10740e200c0e810120076003490b00300010311030b50307031240581b92081020084050102c040826501030820300800100e420070b410341074480454105082e9990811800e20f01800884031a401c98004100003e00c0e040010180941e28030301c200a10080ba8001c01910b00303204248a116032006e807104680d004614450407010b501d5020718078036072500703840d403000c0340607100284c0c04801c0c0d06600260300c01040b50f261240b41c2c0c00c0034030601c1c000d840c1440c142000341011020200b0312029 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 120995809 1250 120994559 120994571
    0x2090a090c0e1002070816030302010507081909031202070506010812030709061d030a0804050102121305060702010c14060403030e010b090105010e06071b03170a0f05030a020408060901240f09 84
    0x3c24002c11103600144011801c0f1a54480b6100c060780d80402e1034403040b00550308003004509414062090144620713510500081620170200d451805403c4458013941401a12151803042d00e806000411060303006100410180d45025205454240d1005010070f4900041c014020003540c05507040c81110307103d05c0d01c500030000140341c200c410402c21300c1c1c0c550301d48988196a0100300c021005030003210307800d809403822402c2c045890301e00e80c8140c0c5045e200882104e00c040c040e0b0701d48580603080550041c0350004280341141d41d02d0070414484003c148203503211404100c105036040c0684002101401d000740840300c51075010502190040c01a241403007590340b0401110346407441a030329940e421491203a05080f04062040011425000503030b003646030760081c00d8001940b8011038604c039030b00b0f6803901c2c1802e0f0030000c200e486d500302404604080e5001c100008011808000c100d0003104040d000081640c2c0c1e004015030a0804038588058040140d802000701c200da6401010444400104c04608 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 120997059 1250 120995809 120995839
    0x10609061710090e1b03070308040b0c070503160305010b010c050a021201180308061002061b07030903020904150506150409020c070e160f0311030414010f020d02090a090c0e 76
    0x2c48a40d0090704071203180a40d42d240c3d030880000c2541c43d060503104e030071001503d07800c10305890f6035071400702902210040004101c40481c903401001007404c0308065131600b1b912480061305241c0c0c040c0c0030300000c00a4070018000d0100c280715040d02c0700001d0030940118800b6a072115140c00c045040039102c0e5100c030a4000d0000801e40101c80117000d22250001e03c07004030714016010389000c4d2141801040003043e4a402c8e1070000034214016814900504444848075621400580c0207000440030011540300000c0143c0300e80b002c050096103d00c2c8020107401c02d0f4030520b4210b44008101c188a90b8234130000c5c0101d401406c040b103060f14801e030000744e5140d414402140c6446c00303562103c9568904941000000c1d450081515040d0b00c81c1c1d6507294070900031440850959a5070b600641c80e208042010400080d0700e01004c030100740c035460022580b00c40281c0313510200e030041e141201e0103580004030b828052600035007031409030105c480d0410280c12a80002445040e1544506000340500da03a0241 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 120998309 1250 120997059 120997081
    0x1a0a0905010e1504120510050c12090c06030a0f29040c0e031002090111030403050615180c09010905010c08031f0902160606090c0f080c0d060803120106090617 70
    0x403150b8200100c1940c0e01d40d5100c017100a420803d100f0303910342c043c0094260250038540681c60150300c500c4052030402405040c0131030307802c001500300300ca588511005003a050f2604000307188105071400d0b0014070312100138100070039240c1c61850300c000d529103440c5601907640170041400394560191000624500c2107030051341e9030482d5242c180e070b040c4a48041c480e0481040c1d002040b0b001400c0c0d840310aa0140115050340c2c6c0d0140e07001c01001c07504a04000b0b245c1c81e071401030007800b8080042503031520705428002101844001d0b07418a101d01310004030b0031801d50b00032000c3d03c01007a0030f107001400c4100d00e85440209000283c584c80b1096802c485000140f07100301e146038094442138600310b42d2000d051154415030041c3d05005c03070ba02420705e1000140108a4030900d25a210f40d88c0301d510a003c00102c0c2140c40c103a0052a103425040c00707000202c03c41d42e5612a81002d004603000460b510f1001500c0b480d840c080c140d000c0b000b00203c4c00b80074007100e40d00401402010f40c90100c40901394a40c400258 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 120999559 1250 120998309 120998329
    0x13020f01020a1a060d050316020102010b0910030204200d0605030c0117010b1b030d0501090612020d030e030106080f0717030c07090c0c0204090f02040c021207021c1703011a0a0905010e 81
    0x64111f03c00800c6070400c4610100361030701850302c00d800800c15841e0344020302c61a0030040320091040c80d10030343c041000d0304054000c0c4c4907904104d00c100d4411250490303032004503040010101442a591380b001c0c0401d042c1040000c519040908003001005070f504000d405e00103050290f030110501c0811040c0c0228501c4c66651020900783e002c2e29222482610008001c2c0424070410011500741f210003e80103040000c0e5000701500906141c4040c002a1001d23078480503103002003a0590b5076400300003401c08050145225803034048014054944c60040c0401c5400c103104240e8009400402a101c0888400921002101c101080100b030070716401d8000d80318811007020182d0040d0510002c0c000f04580080c010100601c200e5040048921850040f030340e07038207003080c54054000c3c00c20010380036160007500740807107400e04007411501c0700e46d81d0388601c441100040005004c04010006200c01e880703540445412049448005080c25607030b80004060988502c941814003542e5001c0018030380f01c0c81340310 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 121000809 1250 120999559 120999563
    0x114090405040317100303120518030d0b0f09160c0302010f02030a02070302010f090b180106080a030203070302251703191d0105040f0b091813020f01020a1a060d 71
    0x20416480c00f820054010750034810501c0d40c80c810704000030722010400d113030f038402e0302d40640c3c40351030200c0c42c011090000e04000c3d100d00913001041c501031003049803c100800c1e00080d080c030b010800c9406001840b00d50020a107040f40b08620708010042c031100700583c0b00d901702100b0310300009484002e013003d034018041e5400500c001c500010070401a001075400801440f4400d500800480c080442201d00311100c803c0020103403440800810f100205070400102c15451000000070315690f070315000c52921208a400300d015800200340030080c59014428804508001c12802650170b1050746444140c203890300450079031041149044480e0340003001600c0000805092b5049890704820010b8000c80c40407016a800340345072621807450394854016901150344500c84250811300301300c036126554000201d4240c000707699120000c00c0040c9050403a001e4410f007900784141c030b500c50040c481c4409140ea50346040d548152801400102101410516038800721071050680e181c202c0003800844034a03c0c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 121002059 1250 121000809 121000811
    0x4021807030b09060102012c1906090b06090112080d0e0f070302210a08070201020c06030109060806070305150108040c050d0503120a0e0703110607140a1205030c0901140904 76
    0x200310819405034440781209008035540e91141d91680012800e8881c504600b402c0076800c042d0100e154056118044512032400c400d48512012800740c00e0182c14078400709849071a10784045000b84040f02e00640d80003002a62420304560610102000c0c480d02c0e64001000ea020005821a100340c00390b100c20b4003070306940d01390307082d06000500841c0e480d200c5000981c41594203545a00d48805d00d201c40c41054441080685921700707258589030040d0304003040c10307415402220700c06c800e50f64484000318083d000c40d183c001840f500307000802d807800400900f0388040c14a003005100e1500440301c2d60039415902443d00322840c2d0350f9450302040505c03140e80f2064015040b00c480c0300c20441d000c000751141c2034810304540c105580d00204c80096560341c1c50000050f4110460601c003003070b492000450003120103000c4620f000303407070381e94011a0b90002c44110b08641010360620b081121114080e9450582450141d0850900c00c00001007441b6070221181070004ca5561940c040c002e0905940c1c46407c0200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 121003309 1250 121002059 121002061
    0xb04031b0f0305010506040b0936061003030f02030406300516020105090706080112081c0e060603070e130302070503120c0d020a030503070516060903031a0406050612040218 76
    0x14041d1301908064800303c1c440d900301103c40c0020304200c2d00c03c40c03180302507002044081f50721944505506540861622840100081d2424038900c100906402100c0c09018901c0030303891800c0003400601c1c0d00c00030030115001044104481a0b019080c6a1581a8690402142281c500402556060920944090b50300f0001044082d804440c0e106100c0f400d00e400900c00c66a40101154680b120340c01100042080c3d0001405000385289606c01c4080c400c800440c07070702c0c00c00c004101c4010350090049901c1c03900c9252385036100d9428080c2c16003041040d8000e00c1140d007020114a05510001d104e01718045c5800f07800c1d010305200b0080180149800ba0039600880303803501c1038032619403007040c0848440c0314110030103202c2480044c010b469039030036a82d03040c2142c42c1c010048aa0341d0103540510040384044a044000c50341d188601001140b01ea20005100d10860340c0d011000520030494078841d92420a0070400fa88a55044034014100781300e014941d0354a0f840010035015000a41c42c103c000c440b8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 121004559 1250 121003309 121003313
    0xd05010f053403020703090e0c0304020a0e090606060901030207080f090f031203150d0203160f050d1e060618050405150408070609031e0905040509070b04031b0f03 72
    0x6805039014040e000c15030304103410038107242d8501032490294a420031190200540c21107200b0303805004154424078008040d2551038402d100c240c3c2060360351703d040b224008144411864002c4045004010500300310f819860100501034442ca002032405d030244000140801d0a41c0c800d504660040d68440382440c0c954001c03070f0844609400004a660040c09a120741105510300051449903044410450500d1a170b01c03280200740404144107100d400012401d0140d0050f81c2c244002c044542c4d002400d800d505141c0401c0c0d580c0110b59a001038081c8100c9481540480c9580c280844260310103001000505041e15000700102002d6001600f42440c401c3e01c6402e6800640110780254003a4086071400c0000d104204915030050b42d0081c1841010818100000d6032340d0046200740f0b00904101750310382240180c1001032404c80203801c0c00a08140b4050156191030702c2042d82050000c13000740705250a0401521251003030b400044c00383c024450050584942e014000c0003e080f5a03020381c0001d603034034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 121005809 1250 121004559 121004561
    0x3030108010b01020604050a03050d0906050906040615051305100e01060c1101030501060903021c060203090304030501110f04170f0714040c1404170c0a08060f01060203030907050405060d05010f 85
    0x280258405542011851002d9600c0014521b00071a0404007601d211403465609403001d512004411203000d44402102c400301c0c0b92813244902c5622503101410242c942072802c034007101d201120606801c880b05c1020700c655110121180c083d0800042c1c00640d54451000c0c0c6520503140b58403484c42d03900180c1c004580a5849000089418421202d080704045444010740985e4424001d81c0001b90940200b0805864600c000c1c02a088800c0c29000b00d02c61541c5034581a07034404c98003400c042d8070007e03041042150920900b0b21400250700b801d803c060000c1ca28034240e100300e2081c00c01442c010203d1461160b014020544c01260704c034121600c09648002e520111107400148620940c0b60401300e000048c00b41000c044a14015189039150a091880c101e42c2c4280546a0113000e100700581c0401544815047d0030207000c410000701064078041040a1030420144c10000031074200740140b000600b0000390020076100100c60200701a910384010540c040c54941015000d582041c490300e01c040c40c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 121007059 1250 121005809 121005811
    0x9090903090901060503011203050d09050703060e07171209030f0604031e020a0f06020d060b0d14010b07110906060903160501020c06090d060b1c0606060f03180b070504080f0303 78
    0x940b912600e580c1e840f0070a0701c4a0009120b031800442d40074090b40c0c006031007000107029004a004c00094241d1581d101c20385094242e42044030995a14035105540500402c88400146006540441f0320b0045500c00c43d141c100c8900303045806040410303814a6503400f44851901d504c80301c41154103524040c200148075100143c0d60a603050007000907040c4e9188041184803485411010b0039400407140e59480c0e000394450090b0040c1c1c0c940d20280481c459002c0c00050410b20440c500c04228044c1080e07030b100380b0a074181d00c1002907503030030410b20000a00079010a0044001147c00303103c1703640c0d10f102081c0030f84291464590301d0b0127030305020b80d4008820180e00090b564286d007141d290b10700401c28404640308004481d94440c0c5810801d00005030380350840d00c03000801500b08001c10340c00f080c0880c1c0040c80808116142c0e6200c401c2440819031205071110f09080c0f0745000e018480d200e40c0144e070007041d0038178044c01414042c0d000440f00b600500845005069080c102c41d590810921a20b0b01c0c3c0e00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 121008309 1250 121007059 121007077
    0x1091e0b36041802061c020c0102070f0c0806040b0c0a090b0f0a020c120a060e0a050102040b0d050f0606030c070201170907031703070207230d030c03030e01110a0f030209090903 78
    0x407901c100c50039283e144820038440707294040e2170646400c0c8440940c211102c3c503d60160740c80c6030200030303002c9031820a002410143d48941c4600400b01c18500e00a01740c405584c1243c0a1903020341c04200200d0610103881d40c0128a0a0f109075841c103100e50308440b100c101f43c00444c1c503000001002a1400b4210000702040825a801c1d500034045600401c546040008400003030782d440884600b0204107580c1c0518468104501280c000c448695561401d9801980c071007100c183c0049001c4c2400f5030341d400b4140d403101110603000e125240500c000790980c04013070008d1a034000c0105058007164003613003010103c80400c082c0100289031003541580d99110600048501703002060061044280b01c0d026a80101001d130090080d013810410030034070054288200310100c07268076204000750b132580d80c030450459000f80e6aa89803000795090140542d00004041d01443e85000c00d1300a9044044080e06c114445924000070004818102180a17005560381c058ac861114410b100c81d01100000401100c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 121009559 1250 121008309 121008311
    0x3030f03060910260a1407060215100e0c12090f1b0607020405060109030605010303030c08060f030c060a0e041104030512070f1b0905070206010501091e0b3604 70
    0x183c3c50b0b0b00d412a20440d544034800c2000004e01c00300130b2080d0399100305914a481c10741210007a20160b11000303918031044402102c2a0070440d010700482d0780c11300c010308420720032540345070030b80c00d00810300c51500809114402038560003d0104590310190000c99084001000e103280c40c03400d0480c0740d01c0d16003c17044d1040c0d10f42c2c8204002c241201031660070030750040e4002070009080c0241e9401f884054903000b13003840d04000329142c000c00043d0051058502842c000d82d000035406948180c041c00030704010f028a4412039504d181c1d001ca940c4c0000c0c00c00d80e01c9809075811500d481040c90141c450100360100180d02c0703810500b0042180300d140c1c0240040720b01500032036182204400c03440d207652246c0c17800a01001c030600c501e640070408040b89240000441c64981c40c1841e40c480c200e1007141c0003503034002e0041e04840c004005030b40e44040d404001e0700146000c01074120100c0050301c00d48980d88905034040707502280b02100c282c2640c0817071142206d0070080804503140002d003a400c17410414401849a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 121010809 1250 121009559 121009561
    0x6060501120b1305070e0d050a1a0609071107050604171e030a0309050a020402190905010206010b0a110f070312030509070501170a09050f030d0e03030c160303090203030f030609 78
    0x1c04902d0282800e00745000e0030f044040511100302c20007811004002ca001e01c00c1d0810a19400d80b5000855010075001d40003030b09035500c10f40b604101d45620201071401400d61a803d200d265034400c1707901d5810089506084c81980d212114103030a044095000070350129001c078001a13808401440010074008400c181d9508111801d0102d1101aa950b81e40c1c406500504c43d16240720f0080d0b10034001b03d4001c00072580300c01016400034040e64003401944406c05a00700110b100b880c0c100c0c2e854409844240040c0c04a50f0404040038054019145000100592a443c021903103400384a0980302c11201000e8543c9680c0303c0c142994500f42d03400761040000d241c2400036810240c042118001d88005030b440d80000d441c1400e448070200c40107449851010307070310035122002407001c02010b401011000c01468440c1c8605486404903030401e080026260070810070004002d404404070f60400d20a0309400d4242441420100c2c01004401002501403200140868107201250099841104211685a0a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 121012059 1250 121010809 121010837
    0x70e090604030c080a090317180103050402011d011103190210060806160509030f0705010219020913150204260c092404020d0e0d020708070302040903030209040906060501 75
    0x680e51007101c0160010b2810f090300700001d581c140c000c10b00d0b2509443d218082e5034032a1501841c4810940100c0e41c440c100064048400120000580451109080801c0245801d80018080301035000c07aa115500e2190000c80701c0382c0c00340842c580804000011030762070f81b200304902449082c50f4504940940b04403045141100903600900c010307558000007501c0240c4501940b0541c170b0141000520612406100d03007001c9840c1008240d446e0702ca0400140b401d2440c2c04000b90510510139891000c02000d1610080941c4072554421b4000700307a43c8a16100b00a0f80c10407103061110030b580e10668074000a40000c0351030008403000c0c2010403180d203042c41c50801e0400540d89000c1d07008081d07007001901c400a101d0502000b462507600c401c41c02118116284203000904030381c0280b00800200e42d0303075501c1c1c414403403080003100540500c030300080210500342048296152080c0c40024480c1b5100c4154208243c403980596480c540080c0007070180e00103929001d40900030f03502845000841854004036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 121013309 1250 121012059 121012063
    0xd020d050a1404081804060b070302010605040507050c030f160c030b16030501060e040f0209060d05010e06030f060c0c030d1b0f02160b0705071208120a0501050f010302030405150108070e09 83
    0x80240e0703010511324540310001031305204404100218542c01592000002005151803008140d0644a03900000c0c81a00340410441110405403402040190512030507105d42400812902041501c6402d99100d0250440d510000000c0e104018141c0058090003c2000100d82c4494090084a14902c08841a03148102d0840d8424855030f0700003819440c2c10061410f0551012102406100b400f5103031804440124029520580620401c1d643e180c0c0100081c007690081d07280c0040080300130b40112424415641d5482c00050819064414006903005641c5020011105008121041032228150034035412504400c1c41710071034003146680e41801c20700b40c40400c3c0842501c09038006c44c1526418814504020740100030101e503a48101d020120340e0406505910840501c00c094a540e00c0402400025928030b02404803030265041200502466841505440c85110700780780042e1203594a05000b4544289090000e20120200c1d001090b0b03004d01003020030903140202c1c0c2611041d100c003003000b5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 121014559 1250 121013309 121013311
    0x20307020105030a09030e040c11100209030c1509030d03060510020d0801140111030d0b10020604020d02280605130e060604060c1b0617090a030c1104020d020d050a14 73
    0x30700160040002030384840d01d41e40300c0030a150203450426042100003000c070b01117400d00d454032000701d0109112040c0c60340e070411016016800c1a40c003941480f0015010135a19103240410350310902c5580e50010442c6006420368415200c01421600c1c0710020000281c001d03c054010503004940c1c10703d83d901580d00001b0210110140d55460114036841c3c41400140c0001070b1a00604001228403424039107141000504800340403070100103841c420786010040101003072403001c015900020100f002580e00e1500802e1f06e035070140c80142c03000e06407210554481545110b0010802079880010400039400b0029100141300c110715212a43c0e00c1d84101d0ba4140c0e000c4a40c00d6203c08100818484107104581202a03248500340da1701d10703044800e550100000150b001032000071495100303a014407520821058103e10620081c101418140d10020403410f10020098030200a0140e15840c07502c50342c0c1260320342214060115100c5262a1044015000035500c0c900141c1c10095030440d1681009903617 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 121015809 1250 121014559 121014563
    0x10905060d08030a0b0a09060815010303080f070e0301050703050708240d030306050306180706030e060604091104021210080f19110a1e092d02040f0b030a0b01020307 73
    0x340d1500282e40d03403000c1c5900080071006400c0d15100701c0e40310354590300456009444981d2000c034800d810000358920b815000096240016604001000400d0b00181c589030486000201c02000707584196003505c44074510704569030550701c2e00e8100221264150b004900407140742d502c080094032520030100414440003181401200105080055840c041d220401402c0c40303420041085559200000d05145040720840c07a00d15401c070b550110f4010a00a4a025003858181000030501986580da80e40c5002010b203400741ea51040c0702010702031606c11002490f04010410765840c008140c03428200001a9042c5201c2101400049061440480d450031082020001000c044d050300c0600d081c180c900400a440b801909800440075445681d45503014006e0740c0c00b620b25066444a01424203070296000031202d40c034040415103111254142844c03804208072508a1103003000b0010b0000b4806d0b548144c0b1184803400c2e000542e18074004c040d5210302c100c60010800c41d4410401aa142d2040e0000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 121017059 1250 121015809 121015819
    0x10b0406050f010909051506130617010f030807170a050706150b030402061b0105010b071112071e0e0901060503160308071502070f110307081f020a1101140f01090506 73
    0x81801485d900d0380c05141c0c41561604940542014280400c5055100d0404603044a9401009110f17840e002082e2484d0f0702484442d00340c0070341c582040322810250f140801030030428005401414483d40d5401d00f40740c0c00d00c0030281552030f0034004000e040c41d403144c0c07401c4483e5802e02ea8501c40e0311200001c07070012105002c1c845e610b165201d60030044a43e0281ca0703404501851001174400a4034244100e0f801f826101564954852280c1080306070081100b410700d10820403040481d0b01c9480204054040701e109850b03119020448800c120240003180d00070015000c240700401c803844105401000444e1030903410307a401e1381443c40b040620729019002c0a1308100d8100704c81d00001716154502603181c1281034005007031032415075620240c00d00505090752444081a01c50b6a50701d4113016260042296500420841007070300c0354aa0301420400100c2e5449501103407112a00d4010a00c000c0d00c81001c80081101d4120702032280c400010035550403050020150000c21480b0842c45560f00500740200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 121018309 1250 121017059 121017077
    0x607050601061107090c021006080d0215090f0609100e071a0a0c08030709090506012c0111030a0309050601050d08092209080904050702010203160c030215040302010b0406050f01 78
    0x1200f41d6440056081d050b6182c4180031001810701c805108401900c031090340901a043e810f00d6001e42a40c1040e04440d919400c4410704054a54000641482d071f903003000601007803941e42c1801c550070002c0d0710100300300c42d0142074200140d03c40302003151228007004a0301085035601450040c0d0395150507010b460b080e806403070301400d803901542020b01088600f51400c51280025690b4810300d035041034444070701003880c200041c0221800b50054076440a42032a02e0020300703911a50281030780f442030142c10a6034020401022140c0d100d281c0b503640010780c03071007100e81d52841000001d00814081c40c040d1514000c9600119080c58060710808015030081c0412381004421410031840c01d100c0b1140c000c2d200201080c141206030230740980c084040c0030f0401d0303a454a24ac0d01c00c3c8019901c00900b00b40859204204000840c800080a4841e00e4054900384899841d14501a8034000031034409190081c18442004201a0705400001380040e082e0740500040f030f42c60703051007100203401c080180421106c0c9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 121019559 1250 121018309 121018319
    0xf0f01050a0b2b02091f020a020607081201030b0f160801030201120f0c020309010201050a110f0d0b060d0204090c0c0506011505070c0e040302072102060a02010b0a0807060e0607050601 81
    0x50054050b1058804600b003500812410f0040c1100a00321400d4242d030300890f480020b0701d460044846203101640d8178200544903100001c0d100c1c0c04108009100b450081864014404000251070608141400b1803500303503100e0905106442c0126024090503801d0800140030341359408180b040d01445859150341c0ba402d503070065030302000c180415110135691300a98000201907019000c0c0da1600d0340c01640d981c100c81f200090075282c00030000d11034107041000020400f0300c48401c803042003d03444c4940c0d4803041c600c5070400140c5120707131a80394400030201e219140c95072154014021200a940c4c1000315401d001c01c1a03030f840110b40409001d03501b2800041250820641e0750300c60300c00c801d151840c0713040490303903801c407113003080d030300210102038a21080004041c0c0412000c4041d0103041042ca940303034100d0741156540203000000034003034000800c075800050300175009a0240c0c003000f8400310b40701e40c8a850481e1744002c1446000f000421042e400e02c1142020340071500320035007182c041c040981c02c1c0b03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 121020809 1250 121019559 121019579
    0x9110d03020c0904151a150a0c0503030a1d0c010c020f042003041208100909030c06090b0906150a03020409021c0303020310090c020c010305100f0303080f0f01050a 72
    0x540640550007582d9182260380c1d148030565110b28400d02e000b10855010041c0c01d001c64003040c01510780052403450f05200b41c4e582c0000c0c900100c000514903661000c000c80103d0761030400150050551002205120340d4034116000001d0300d00b001d452560408442c1d5282e81daa554000c02643d000c150008106005400d201800c072041c10300c054004224a41281d10780100e50624101000c0412004030904c0100042c00c2d81d416540324903032811021504091620000704140e40c41040751302c0ea964407031381040501075115070354103540183c0200114215414450301c1210221481895030048000040100d207429010041101c4087c011a50350b600b0341e42404018408007070141c2e4041030f00000c03d212001844031302001548250303405a1241000503000b206004d1680000c1d0841c2c0c10400303440c840300e1b030004503140e001500b4030b00820582c0320b030071080d03041d501c07150450b0b4160400c1c0070740072050540011029014244441d141c13245550703909030328030359403500303001c0d096204542403020080b4070300ca = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 121022059 1250 121020809 121020829
    0x7030c050f070e060f0a0303020303010902073206010b0f070f0507080303090f07080a08030703020904090615030507090e030307080a0e06010603140702010c0509010f020304050d030c020909010911 86
    0x1140d0210345001c00071039080c52620307681d40c2c03000c0000d0400070208115410a1054004a0502502d02c003680d1411030b42d01a489000c140201050140d011406009200c4003e1452103000540c28500d14180f80b941d8404150620320b00301d014403441440300004010b81c103030049401f5400300d00d0392982418942d40c2c46100c14104030000340c03030764450b480022074640000d2000318003414a100c01488000441a0030a0500704d056111081c5904a4880030000c5540b0714201c9034480042e00d0016910b06100000800a00e4003000181c41c10f49060400748907000c00c9a422000d4034001c00450b02c6042d0351701012410b0707c21050360f8611680052000c18200e6026900c126003000c0865400718007200d8800c282481d09600364046c0000a8a580ca201500050205d5403900306c030080c4024400706180c8000a042c9104409c0307230703504200603c0030440b11548240300380e601810f0000d040c01c014404504009220121101c41688140c40b58030114255110500c103400320143e000300400a03070f4000d8401c03c040b502c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 121023309 1250 121022059 121022063
    0x2040615180b041e08030307181406071e1703091018020603190e03030a110702090f060d060e0102090306010b120412090312020601140d0201080f0406140c04081006060507030c 77
    0x104442e13010078044020f202940c07052601e0355038840310320174002929240d03100d56070015060503510707518200c0c175864205c00c64000d2900002d40714204d1131042c02d0949107108404c0d01410600300005425444012000250300a48091007111000e000d00c40d102c0c011540740c00101503407443c18803405401800d001d405158000005504060305a94100218040d5429a5841100c40c0c10010800000d0f03042c6210391440001d281120310301304841c5502007142d11401800801544032100d00045440d55061010801594402414400e048840002074081c1d00b06840722486405200000b007641003030042964400302c841078040c0260b03140e40e00c848100c1d2404840c003008003d190580800401c5e18a8250020200c00e82e0040009601d8501408200e62540494034800c46810540da37015030307030285083d40c10061a03005c5440c1c81c0c031285031150007030020340c1105941d0300e02c0f14100101c60111402420031103040e0410b1301c81000b50403643c402144d40c02d01800c0c004c20800d04ca00c801003486007591010b02c1d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 121024559 1250 121023309 121023359
    0x2040509010608120a0f0806130e071701060305010513050a03030c0c060c08070206010b09060702090613141603090309061107081b011b08070f0f02040615180b04 71
    0x980c944031030608000c0c50344c1003180c1d90340c00081c0c40807249911200481c00c0071018581010b140c01c118001480342c0c10095055a5203540b40c40340c2000b2401d062084000a104014080301c0d5071440780b1031180640041d110079121546800006000d080c0c40443c0c500340c451707018010b8002000142d400383c00814041c801c00041240c220704610010f4110310440c1e0550042e920f0707100c0949002c0000a14011058200d800c9030542408003000359103480090303841c410b034121000b110130b50780c0344042681e06042c1c0d0001d640407414070f50b000300c54031403140d0b03d18058148401e0407160341c5900507003981900e030120b0340100014100b644c2000220302c64690610b269001c00199118603581d03007181442d08005502d98891210101508503035503802801000c0504413940305496a5640d070b444881b480c2c0103221001d8040b4a00142c2c000c1000a0844032600c00c40e4020010851152650300c4c1400520450252a0215504403400e86440c9080c0b00004101d0341c81c91442484c050070200c0961000d1401000d0a402c0c2d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 121025809 1250 121024559 121024571
    0xb12041704060801080c030705100e010507080d06031202010b01020309040b061902011d07031208040804090509100e0a1101050a02070803030a0902030d1701140a0e180601140108040204050901 84
    0x351031120010801009036696060aa50424000710b0401405145862103507100703410030017150b10340b00ca02c848040d809040c421103416011740182c90030f04c0741400c01001c0c01d0001401c0c00346003906620005c1624040c84102d9118483c01c1e1040e400c80309a0340358280940c0c018080301e8003d1405401024212002078141418800c642c510070310000201c2c8820700150751601d00c01402e2250707019420380c0404801c0c00070702a691458440c24004001100310f07100b00061440020140207880c82100c0c02003601c030904112528000e9400c0303850b01c3d0030100c6856164104101c6448060700000d2119015400c40e101d540204030b10307401502c041e4040c008100940c01100320010745c0001c00d202440c80380c0c0b9070a60110750300001d8810542804901a520001e00038689803112151401a80403419642101c0080c1c00b0443d10038001180c8801e164040c2da20b600d41032041012600b13000da60850300038031030b5049030781d10b07600c1c0d04201030540144100ca0780002c2260b000a0050302e0b00e60403860700a41000f00000300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 121027059 1250 121025809 121025843
    0x20a0e0414010c05163203090a12080306010309030e0310050f06150a0509030a120f11060106050919030f030f0210020307050d0f0f02040f050f030105010b1204 70
    0xa5021a015218210701545001100e0402c3c0100741e0b20b420f0038a0007078a0f142c0c828003864038001d4005e4016220348001900d80d421071250300f0030307140e512031903075080c2c52220700c0f0a000641d00d520041c4064002c4c0503044001900c890680181140150302801a078103607621000110010825500d00f9410000225480e80890310140311038854040b40c1c030030104181c5020100030a841c0302c040c01c0503010341c602d4421044040300d09401d0360003801440c50450381d030b180d103400064034142950381c000c0c3c41c40b20300f0804003c4990300302c0702240684c0f4491312081400c03122218043d4a55100340300320004100d08002d100b910780703000c01d02113652800840b154198640c070703511003600501031568103c000c2a2000313084071415030104040315040901d81030a40c694a0464801442c030300a1210b43c0a5094685051076050b51054210181c000414401151030710b40c0c845040c00721584500ca0039018010004500c480740c1018018a41640d41b101030b0103207007080402103050080d90090003075808401207640b0341d071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 121028309 1250 121027059 121027079
    0x6030b1c032709050112030801050d05030c070e090c12070b0d060b070302010b01081003020a0e0402240a030609020301030b0408091c03020a02010e0d0f06110d0e0f06090325020a 78
    0x200b48018003219802060801d02100c003220710603004041072915100c403c40000e41c1c4a001c1a064800c15968000d9816080c41c00511b54010710801160714014110045080e035040e80c959480b071070416007181c3e03444011300140191214005070408840d081018280000700a6400400a103000810009403003540c43c40d004c14590007100017100140d445920803401d941e44000d1140d0272413118824501d80c10701d158005a04c504191040c222849035500000741555100c0344800340c00000d01e03c5541c0c004420480f81425a0b201184036008646052408281c001031442500c1c1a00d5000084114540f0707240c40e01c0055400c1840c9142d0700100382e202c04c81270400480d68258039280301c1d80041c0417a0500f48005003100f03008119460103001d1040c040c1c0003099400250520300380e00054000781a0b10241107140c154451218840300480c24069040030100700059110b540c1000358054405584440001355264030642d1541e2900c5907001c4020700310210041c00000341c0c20710007450314071519910f1030106 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 121029559 1250 121028309 121028357
    0x504080316020102070611030a03110f1303050708150f0907080a082109030d0f0b1c060e060106021c021c05030405070f08150411030f1606030b1c03 65
    0x111008100840241c11540c04100c82c90241599003041480700c04601003075a42c07402105801400c0545501d280b01c03040c8401011540141084003070a980c46d540d0740010407440c115407104403020312410000003003c0d000450354021500b80450100c2046e21034040055680300094980060760007603800018842204004c40035041d84929240764644000e40302440c2c00c0050000711204181c1d803182000b10039400402110038245000c40c001586c04411f640400080408401c5207400c40e66a0780700760103000c0d1440e00440d840340708090520100140c610b20700d458000070711412016900c404a0038081d40702d0412061a807070780a01c1211240c1442400100c0140c03548002c0c2008140c1c0003040c8424804140024405407040e0345007411594039110034140c4e9507003a9a542c107402c40000c008a410400484050040c0210050441d92010070803950251140c00d8881582c0d5405003001c1d00040c0d885c02400352000c00c1d02c00800d00b0601e8003000c103241e0000c103c410303000c9007008038044131a6100d00c0c4032640a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 121030809 1250 121029559 121029577
    0x80109050601061101060e0105010c060f051509060f10080703020715051503010b01050405060c010e0a05030c0615030c0904060f0c03021b011103130c0b0c03130b03040213050705040803 81
    0x20a800c1d4074046028010b580002d04059131a41400024061400310240d220304682c030a00c0c03d80d01c0c610b03940c14014000d000b40420130200c1c80c10201404654951903400a401c003070b007100c1c5034095803100342c10401c06910300e41030541c100800c1020803a000d0301900101e40d01220038200986003088954854100701d81144c0304008041d03540b0284805404500c01885031400142c008120100b501c00c0003070041d02541c882c0d18400d0038002520f550224082d04081d03c07504416040b214a6050346c9803d607200e81080008802c10721828000400001320304102c096051406405049080450028802d10703481c000c1060f940da98803021600840f0146201d14140703030031643d034010b031600c0d808103070307403d82c2c840740c14041003260f0516075009410483c450880c3e41042071001e00804200503482d081c0e001d1b01844c0d000401c0540f021810940410010006041020181400000140e15140c003804a400203039400ba400c1000c04103100304000d910360180e500981241455800c159a601409185074404490 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 121032059 1250 121030809 121030813
    0x100606020d0f050309150c0912071403030a09030b07030212100905090706050d02090111060c040f0e0412031a100207091a010f08060a090f0e060108010e0304050d0c08010905 76
    0x440015550702c000341c51001e080c9481c007640b55080000c3c0c610380e103c09146c2c503501110380303620126422035640d10807180340d002c0c060000d030b4095a902c0e007183e80b20212845500b51145141d40b034603511746804022160120704c00d8481c441c4050860b1105401f4080050200050503400c21142004800350701c26940b06084247c20b5108140c1880b0041013500c1d030151950f803542e80594404d01c02d1a810100f92030b64441c6000c1c005842da00e003400102e0710007030302d00400601030141c00b0a00840b004002c000300181e4a903120075010241d41c2e0080f0314010701c2d080703401824001b2101e040840580c400d0b08003020414001d2880c84501e85505c001451810000a07000d015030b00400081011208900070034050007522035107078100001140020300356080303441d011401c1061060004510750b0715a0034400c042d141c448002c028522400440d8001002044d01924180c49041c1c0000b80d050303014041c0c8042440701c2c00c0510308091800c001d011030404110000c541804444801040203882482155000340c02400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 121033309 1250 121032059 121032073
    0x10e040201020c0a08150a060f0e01090b01020a020a0506031b0c100b03070303020c09091006090f1514150c01020a2006010e0420040f051e04050c040e10060602 70
    0x400039103010705900803640540c0c0744d414208040300d07021032009032640c250941000d0b144d0394201c800c0d004040f00e800120000121040100b08240d110303a060707060355400b1000b00000034101c00166610501040c0003503009011300e2089c49170303052080281d40c0080b01e0143c50704035213010103044e0055030001e0035280c08690104406030346079a120b002d180301c80c1c03809601500e846400d64500039112140002c1190080d0b08220100710325400420028042c01504401004910344075140c210140c802d40c07418211607820900036030014405081c01c1011200552440c414040c0c00702d084c404003c5410440155494040c030040d52031800a000034048002903030b0303c0e0341e10740e5108444103085420300900d40b0415840480140840104c0741401500243c01004c0f12400e01da0500d1008042c2020042132074200c3e00348960202080f0300381e0030540c010382c201010b041340d200100e200c40701d0784182210007400300e40c4400c50411090401c1e6103c0c840310441c1c0c0056600b41c180200801d01510b0a0f03500c1280142d0080d8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 121034559 1250 121033309 121033313
    0x20d1109130203040c03020103021c05090c09071803031d1309170f070204200c0d120c020312040302160807051507020f01030510080d0201020417070608070804060f05010e04 76
    0x500d40091103001e0303103021825400c05031104558101640030003810306a000900c11b41555030110a90620000c07140b0601091901c0d05c141910741030510035083c0224448008244143d02070019181341120100c801c1e0030582c5540c508454120000e800c00200e02c0b00c103c0c84d030584c4e03264140328100c051090100820003114515000002079031842c0c01031400c1c1424042602000d6810301156056501158040350704245440344611103080040100a401400500099504004a0402c03407000e61601d62480c00313a10038a03404241d42c0c80309940c10050f002003191015451a4111164206000344101d800c9610441c10800140d00640c04c01880355002e480c08009030300e4003000007140300020644c0e132414040c003580401d0b000c3c5400701446042c540c0356000554400150040b1500a184a40840b2110303854440080d000390700a01845d56044078540c16400410b00010300366049414030354400c2c509591b0113404540d41d15000c0c008032200381d115070503094140c030a07003d0f190180c8040303044114281014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 121035809 1250 121034559 121034569
    0x90f0204080c0303030f150a0b0304060f05011502100911060a0c060506040207020a03020402090f100306030b0114060418110f090907080105030c040c020102070204020706050906010911030601050c01020d1109 91
    0x100b800948203038010010408a0304000c400160040c00400b22179002c5c0d04010300049072001e035900100c0c401c01c5d000c02000140529a0000c00c648441100c0400c580e98803640314030080c0301501c00380401f503401595141c602500f1607101d04c90203809091041041c07a8000000b5800e40e0021106100082503103083c0814003e0f103200d016040306c0100c3d01189007280716800704444c50300074800640301d07a501084904141e02c8800303180d80028402840c42510319564440500200602e01040d51982d10240011400300c040d200306030000e2400400b0340b81031919103842c038400340c032120b40071b03514460311600030015518011018001c09000c192082d038460b54554240b2003d008010140c2b070400c15200010822501c000c510540b00501c03e03100420081d0005070203902a200707a0038020741107480024004188005940b0044c01005000c040e921030342d983c0e0001d003040d182c3d0403078000c403c1c0d0b500700041021507010700010250304c8a1400054108020756003980c048420500c9140c2001500081146141c908 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 121037059 1250 121035809 121035823
    0x305040504090c081b0f061602040524040501030f06051308030108030a0314070e060307050702090115030c0807020616121b03060909030e040207021504060f0201181a04060204090f020408 82
    0x43d408140d81d070890b000740002e44046031800847c1c094980003d440c1d5186980760b20f002841c81e000740c000d00c0349042c41219600c1e180c080c3c510801e112544d004540712540340c9802500d04894110580800000441e2101c800500c0003400c8091025800710340d8000061a1380f02840c024181d1002a54a90300030001c050152908001c403107083c1c0000d40704000000360440611442000166422920790762488007da400d40724141c00a9400b020002c0001416010582a1241c02c0706690303051244420b10700c029034402806655100268000400190101b156040c1603092440c0c00d18003203100c40c061a48030f04c215100900000c0700005421401c036800b075054042c60000f4800c542c400c101444540d00c000301500d40d00c24030944125000620042555151b42014100702941d0055542d202c2d5104805400e03d0103c020f48000b5500b0a0761000e40d0300890341d00200516040311a864181d915110ac41d884032a005104039005d980c240300c08500319100703100d00c400c02000404010703601c6040000040c9009a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 121038309 1250 121037059 121037083
    0x7020601091814030f0f040f0819060e1504030305060906090127022a0c1f08090a05030307020c0f0901260316080d0b09090304120305040504090c08 65
    0x42000c00c010b0030140c4100b040345402d0340204508203000340107500d0900b0751191102170901301101244400c0d60401d110010401c440044560b80702003030750707402d88030b44a8001003503464107000c440c061100818000c1c0c00031a034041459090707401408500d401c1060164090760b0942c0003c2d50381007004040e0a00400c034503001141100e8200c074035032402c0302d642102152070030340c0e01c0c2c0c89040622968040485406031540340380e00c0410740110002000040300c07481d03d031640340002031162005400c0a8105503054418a010003400383c403401c03900d5801507a082c00040c1010720b5612400980c2c50114a041c40514014a103507405000a03240c1c03501000407601070a03a015204606032001005503501c44000601004081c40e52000b640c401c0440080c11805007144d4951021710321000b04c402c112131500148482e050039041002030415240602c007104800701c800417402d6004100a010118240451602c5244645481842c0a07264400f040076039400300b000702c585403a00700083c801c4480034003405052134 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 121039559 1250 121038309 121038311
    0x20d020c010f0b061602010212030f070810030807200a03080a030c030b030a06050c040f03031e0c02090105010e0a0302041b0e010507170714010c0c03020d0905010c02090612060406050702060109 85
    0x24035010000b900b611a6100d170055074201d0021203170440e4024410085070b41402070200361a40350221415003900c00c00c0710030000051070745001514501008020340c05981c3c01c071180d54100482691440b0a40c15071004416100418048440803503071035204a4024601c20110181c640801c2031014054400d00d240100a050030b001051003030352400134900b8280ca42180f40450380341c0f42c01c10900000c0c840ca4101011803510740c0404421302d42c2103442412500441e0b0340c0c1440d1840c3d041c404480c40f1401141c001d50094220004100c03540c482c204030050184000c25900d0040e98960000342120080d04000001e1070940c01e00c408200d400c0106500e4080c001e08006181003015074644191500d0031106484045021647d082404484c00790f1140e0340107204020841045045000741566954000440044c441c0494859409100b070681c142218810b8568000c01243c0342d080120008000340f007540c0210b0060b2001452010030082039004c0c038001d4a00054904010170000d0400d00d050700030402d21 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 121040809 1250 121039559 121039571
    0x12040308030f06061c02041a0c0a030e032a030c06160b0a0f050406050603120a0f05030a020c070e04060f090308040809211e070509071404030204020d020c010f 70
    0x428800000c0380c0e4400c5010b101c4000d00c0d03444000040f21805413900f440d1860b164170000d0710400e11542d00410903101600320803608000400a1512117100b18540b60026412010078480000d002d0400410100c1c4001c0540d00d500346070b00b4007041510000f140c405050a4103204000f45030800340149030b8a000203441aa207000c104803484c460140da80d0b0030003042a60580c0004108400a40c00f241e1454480502801903042c581400380250030251100c40c442d016200314201c10302c85007002c549a540b40f50300c8800071581501e005403010b801c01800070208603002c1010540d960b00511010b0090f0601141003211820281018400ca45c905c9400c050360300d00e408000c002080e08800042da210b41d010040b29515240140441e60030100c0a4007446074a00318450481c6803140454a82c041050b940e080381c1e40c00780415a080d80d0b882c900c1c485d50b038200c001140481c1f0b10511846107416421000c40d252803074140e4030341c0490201c1c2d010030384035a425680401c0c03903095141d0a00a544075403a10071414484 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 121042059 1250 121040809 121040813
    0x102040e0906130308041a0a0204030b060f10030e030f040e0910110702040506012c0f09040f0f0206190207030c090e0c0909070f09050411030d090302040f020d020c010608120403 78
    0x11040a501130140320f0307600002020007109170451250245589207410041c1408500d041c080e400a00003100c18090140008030315080409442d00b03401030040102e00e0b040710700c00c810f500400d01089070400600042080540c3d02c510540140003d14440203100c99a2401000007400d0441507a00d0014590504842d00b43e843c15082c1510340540d01100e000403d51a00001a1a000e6070000700084010103034031211500e889282c190520482c0c161622000c2010060400034811800c64000b0901c0b690b9102c1c08004c035a10b809040300491001d0090303403400b0320118000ca4560381e041c01075070050b80300b4a0207004101224075264002c1804810510a6001110203542c0301c400046206014004010009505120820400000384104002c403461951500406e002404040324155400c40252840302e0690800043c203180c1902c9990b282822030f400c513801c02024041c211b0031060103030307002d0000d00c200340160f1005060214001c000000c0c10f038030300702d481800c01c0080841406100401c3c007003000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 121043165 1106 121042059 121042081
    0x30103113c18100b07150903031e150e01030506070309030320070b011e0909030203090a150210052a0f040e150d030f03020315060a020102040e0906 65
    0x2000ca495013610260b5104440c4c0050504800207003280e80f00c0b040d41d105458092007884c000c1000c58171400702c1d240d05035080350107003501c0b59240204628514140c441303c4c01848803410b40806903155880e825200d0300028181018562903030a54000c1510a60020f140c020450102c08405030780712091030890f400820048507a101e900c00085000c10002c1d4400e40e0f960703255030090341080d0625000704003400960208400303601c4188102080707640e60502d104003a0001c51001a000301201b2802464194120120742491340740c1006c2c4004181d201c0382007070034010b416480301c1003013681c0d0000f00854451490360550010002c82d000c107000e1641501c40e030140d01c00601c00340500740d10b00100440ea1001d000c00401044011a1655809001c2e401441d4410000c00f4040030000106011800c1907101c482c0e90310050358002010302450300840113a5402903040e2000300054a03000a1141c = true := by decide +kernel

theorem cover : BRFrame.Cov 120863309 121043165 := by
  have h0 := BRFrame.cov_init 120863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 120863309 ≤ n) (h2 : n < 121043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
