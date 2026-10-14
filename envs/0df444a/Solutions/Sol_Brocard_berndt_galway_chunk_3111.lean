-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3111
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:41:43.974767+00:00
-- url     : https://prove2.me/submissions/0357621a-8169-48ce-b54d-5a0f9d1c05e3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 559352517 ≤ n < 559532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 559353767 1250 559352517 559352531
    0x40e0f04050f120418060503031e040f060809060f070c0b09010e0307030f0305070215010302040207140619150b030103080c03090d0326040503181302030a06050102190c060c06 77
    0x240301800880c18070300f100409107645500d0314414004040c2d500e4061520185442d02c104000c0d02c0100c104c6101c0428072202085910425044a1144c042c580142174505400f08000c41d6543d0040f42c00c41c0a100604201c42d51030341c3c3c1c20480700b141c0d00c08031201e000103809240c3c03120000d0740e58a022500502e0a80c00841c0c2542503000c0700340356810041c0143d0003d15a00c0c14225041c2d0144251500012039101410328010b503405c0d6810400410b20009004070b03030014107a411300001e045076010050841059500909000c4072013181c0c2c803c0c894002c40e2a51512030240709500c500181e9a0440f01c501c500c56080da07296444100050b08407103402641400200801c1400c0ea49003c3c20145803403180d15403503810045006402d1201c03c0400c2c650054030022810f200100d6000025680001c864460120b54091604041200009454080c0408a0000c4240301010006404c09000d0740c0e02a0708a50301450a040d41021080b00b801d000381007001d80c060107010580c4245503d165490042001003544 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 559355017 1250 559353767 559353793
    0x40b0c0a062d0b06031303020309090c1801050304050d0503070903051f060608061e0d0f060902030f1f0b01090302060d0507030605120606100c020306040c06030f02040e0f0405 77
    0x303511080c2c5035000500303910000d01e9190b0202440d00d450922810001c011001c00600818100c3c80b000d41711005012620b1154006c05208000b1520070001c05415000300e400c00d035420082a81000307042d402d03610050800449154403940a1702c2c441c42d080b00c01050502030048080e6005d030300c098002006c00000c1c007004400b10b0000c000c0410712090002319024181d0034461503100300c515a4001604002d166000d000792680c800d5814968100e0641c592503145055000040c408070302c41c1c100604201182c2031103414403146a0150740f01758000d6040d180c4010340142c0058440c404103280c40c007050403080f050399290081d50b000d0600718034103060503205140c40360001441c41c0c11030000020303010384420401c25070300e0745030103000014802600c0b1662000044106140c586100510f828014006072012100542c481c58820042079005021b84120b820f00341400248035502c0e00070300c000310741428500740c0d1822040c4202c904407107181d00014000e803104500d6290002c0003610903110340c40f0751010385540d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 559356267 1250 559355017 559355021
    0x6010b13030503120f01091b2007030602120709060c0f030302070204050a1d060714090d23010b06030f04110f09070e0f0a060f050c0106030b070c1103010b06040b0c0a06 74
    0x8130ba020065084240780c4414200900241604126810341c00c01489819904108a02c10f40f150218100820140d19541821411106c800c070150040c1c82031b50000014880c495004110031034082c9010274140d50382c1c82007940e0000301d600c00c00c00010340d4501180086041a0006d001003032181c81c0140ca40101a00081c0a980382030324483c1100383c0d00e8040610034040002d00c8085c00403400042d001e03501d0704000180c0b2a1080c0000c440507100e00140d60342d40799803200c88411901da0b0082d041c5011810541200044280c3c601242070698688548481d640c5001400c2d240320380c00030740c180521555503a80700c00307040c8244054541c1200e10206c0f54070f026950040c0041c4a13a9680d9100c403c03800b03124080003a44000f0381c44443c000c1d07003400c10511980d54003007000c5050703145c9400d01c66541c2503c01c0400c0e00505c21030b800a0b01c40c402c0c890600c000150321042c102c40c418021030820789503a003034408060032141202403041d4051001c0204100100b0240d016000030404001621000e0700180c5682c01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 559357517 1250 559356267 559356277
    0x91e120708120a0605010e13150b1207050c0d0311210907060c120c020d050f100f0209091f05040204031415160c0c0305030c010506040c0f0206010b13030503 69
    0x1441580842e80c0d40c03001c00203540c0306510400e001c03020b01c030052030040040d201d8051003081901914506502c410b00710000d81104161840e500a01a440c50307807071244559039086800719038841501d8030081004148a1400d9400c5103c103803001e04551f803040d0360160020090030054010390348041c4000c1c40b5000e41c80441e0000e10342058550f02280c908660b2050400b4002e41040742841400810040840e509200444249210382030110707140500e030000502729204890000c2081c800c100c04910300b008081b1300400700c440f441c6c000380000d40c040700c6c154099016414545800c43c1240000030320100002c0000d1000410301d01e4280e0728241c5075000f0030b0981e4000d420503900c502e0503039202c0512400800a071500c100310021441c841d030400c0d00301111080e441685c0c0c0c0003008101c00e003403028407507010b5819000710b0b4010b007101d40d260700168082d4041c110403a0500e200b01e1409150900340340c01070700c081d8052041d40d40a04510380c201111b185c0181c114208030104043c0d00040400020700400c0244 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 559358767 1250 559357517 559357523
    0xe090a0302010b030a0b010510020111070f0209070c0210080705040906170d110624060415020d050c1e07080109051b04060b18010e10110114091e1207 66
    0x119061181006425038100a007441d0280e80300c0741e4030402003484048204d0640f841103540078468080118200e000d40741c200d1900110210000b001d4040014051080401038070070b90b11120650380c0c0030403d0381c086002c5a806900800280e40790031009101d111055482680c0e03003003081c00c00d6214680807007154640e070840404d606040c25040490903081014004c0d10540b1314159280c0725441e09603548407030000d04010710001d00b190201885c1c10034055074421503140a00403a80b6196262151024040240071603005806410440ca0a4a01c104225120184040300401e4904a1038140c0c03106071141e000b03515064065404040303150750b400c0c0100c282130350188000b003c81e81100c00d25194002d01004070944100d10b0440200134503004c0c082900c0603101a26442010f4800102c0142c65813608900803562140010308810141600014502c0500035540c000700040c4003004804454028150f8862085074481000c1101c044e82c10854100b409411a056502c900d4400c0f044040c2c07600011421 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 559360017 1250 559358767 559358773
    0x7090312110c03030306010c020603040302010603080f04033c110d080c190f020f010302130329011a030c0c0d0f12050f0708090c09090d020c0904080a0c0c0e09 70
    0x403030401c980c10002034508400843c0958558184030001900085006000034024074011000405040c000e501100045801601031176480e03090807082c075003551003404112107500b0f0341c2d050103d0190400001c03015030000e48585018000b6080e02042042600c4034088510003c0c003da2500d140e01c91038424601d203485140d28548a41010407060301b0103d6540d40813000d46c1c0800074210100701c5130b6001c92046ca0301a1100c03411150507000403000303482a08444044d079403810300c00004209803841001c4501780200c01c409440c1c806800603e1080c0700a1007040101d071810411010ba00071101c0055802000c0c0786c0c605840c241604040500b002d0112020783d01240d4165403040341e66400c0110032200c0c401a401c20402c03482c003151500038502010344081c0401c20668001240101c0401032200350340401010b02c001da242c603082c0c05070b80700303d400004001800f543c80c010312142014050907015952000b040c5081805101c0300311120b10320f44400340c4040e10f29820004410a104650f2030003001d0410103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 559361267 1250 559360017 559360037
    0x4170313140c1221030c0d020a17010506040e0f130b0906040b01090603081b160b07060b040203070f0f2604030f091a09030f01060f0f05041e0507090312 67
    0x1c1050141c1da14842c0342c46900000c807040031103040d10410080350700411803c20b0310f9403070b2a01c2000e5140075900242d1051440011010005500050ae1403980c0c05040c0b0301d50381076a02c400a000c0c0300d000740e00c10344801c220340c00041000d50703044100d03407540000c4110350000c0a50003900d499400040035100c10742c03240c000509000902c03441c0d594143c0501806141445034030b02c1e5549064803803250f03110b9105d05803030384030040d03606d90824840064002c1c1a4007d1201854803003c18400c5c2d607006010440b44507141c00c05d4006181041d000340c0b44030741fa068032140c1460800140681e0b51025042c040c0d070800030900403004103100300f401860242c181800d00c142084c83c080c900500b000c1c8441202d00c1c02c1c045402e0342000711101008850400d00703420f0401c1e60311601c00c64042480d00c2c13030b00741c800591542009130105517001040350300d40803503400c9503042801c20390f11028003040328056101e810005000780c211440c1e2403144e0b00460340028651504441095680d200c40181c4444030280c3c9000490f00c1f05 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 559362517 1250 559361267 559361269
    0xd0803090f032a0c0a062c010f050d140705071101080f06130204030b0c03240f0f0d0203011e3b1e0309040c02010504170313140c 57
    0x10000c1c0081840004501e000c40003d00490341d030b1900c40c114240c6582018040140c00710902c24008084000f500c0800440e4468a028005480d038143c0001e50914102040e24504003803030280d00359a0741a11042c0c02c547c0108030444541d481401c81c1408251122800408100e081414600c18441681d81d151603041c0c0d45000c4401c0b084e26410107040240c4c0400f4000140c141604040d0000c1044940d08001000b404030480030b0301803035001403c84003c040c100004400c000000b10702c40c42031000d00705102c98110302410300c0007801c0c030201504a4034441c5030140c50704042ea04181840c8004248141401d45a400130b401d544040e0800c118103004211007a0100041c0d00401c0c41c010640a4420090f0f4086c01e128401e03103000350501c00c000049004540f0300c1c44400d0100b0944400c5420300c881c00c0748250040d5650340d42c00300711064051307450301e2140a0b4161040c800c0c030703010319031000c64207141044000000000341c20141180e440203510510640001d100407441181141001c0003400074608040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 559363767 1250 559362517 559362523
    0x130b0a090605090a2c0103050d08011208030a05041515092007020424030302030903070605030f04121206090b040f0b131515020307050c062508090d080309 68
    0x780c0504203001c81842181680d0380c07001251801d5424400890514140300e0020041101c00501d0f0030350328003d410000f200303110020070300082c1d25140f529640e5a030707643c42082900420900b280945000c03818004039403000030726080207811a0081e210b401080142c0156601128480c031403201c4000b503041c60030404611640101b251001102d20861079000c814101c0c01c100341f10b4008020311130341c1da80092004015403a0105048581013440040072640c1340d01c1d0184d80d0f64040041d861107442490000070f0014850405c5034880c00002d01072509507100c5a4601303c2110800200906008000e0042d0415102e41e10401004184083d8041002c3c0451000d1004070341c3c10407403a48820b400c100000c207407503d441c0100311550321035a10014104c1034040f801482030825030450200c0c090700702401101c10340d00001a0890a02071025540c0c4080c4d104104081449041c8070a189000110f1205031404424240031140e80d000d03200e03003840d0203140c0c800504205200b2104442c80f010100512200f84420 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 559365017 1250 559363767 559363769
    0x1109010206060a1a07020607170301092901050703140a05071e030e091f030b07030507030603020112020a030b0603090106081c0e04050c0c0607050309010e12030a0b06130b0a09 77
    0x3660108812424110302440c0311100813614140303e940040c0700021501d42804a4007490740000c02410030714a881950f1038140c1c000e119148006082166094811190b10b542c00f003409498516244900b079401c0066800c4d4100c02030507010b101c501001a85010b8000340100454641540d60702e50352441c525101280441980c0140c4034a07003112408400260014020710104004885a06640c3d95500c0c1c0a071501030225401241c0d400101000000c0000d01074549000f01c034152014406075450030070460840b100f80c03001030f000584814a00403101003580c0282134002c06490b0218103e00000c012400682c001d440b903082c103a54680041240000c00e00101c00210402202400c44482500000707200c114510091445182e5071004101d20a000904440c900402002616a90310303001001910f150811602a2515401c2150301e203081e40300420b41081c0658100e0305541107031240760740b80c00200340c2e203007406030014810030104c0307255810a0b40b80e000800c0c1c07070800303513aa8220101005140c032881e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 559366267 1250 559365017 559365019
    0x180c06110307050309010c210306031e0c030b0a20030405011b0c081308100605030606240903070803031003211d220b04050106081e06030709110901020606 68
    0x10b01201001400101c1180c0c1440801d18103850350281034246140c5d10381048040d4807000e031803003490540b91605a009102140d01400308030745104500d0811030010505018000d01600d00b4000520014507200c00c52904030100d5400080d0a040d40c41c0c0b201801514515120340c0408088100010810240a40e020a059800040c0c281d07030f04071b2001600300c400c2c07180c0c0100003031004940a08003540c5070b0011801061014201c070a8101240f84a00007000d0b0750103081e00078022000020180d09000d01011000c40f1500c1340a00805002d004d80c0c8a0b54100415099050080f2640007800319000c00c042c50040f01c1c0340c1d80d054620fa02d140303001c80c0140c0076540b0070b4010a0755403055543d4180c005119040803c00341c44855441c80f11a0009000707003103140041d205081c0c40c0c03078280c50115010790000364141010f8074200804d07601e0300002d4a42c210125502c0307814980140a030050f81240385032040d04408082c0c02c403220642c4511545094502c04010303686940004918042950f0b81001000d0300700070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 559367517 1250 559366267 559366273
    0xe0106050a15050d020d090309060e0a0603090503040b07140f0105040210082a040305010b0306060f2707030509011401030506070f021009060b090c040f060f03180c0611 74
    0x11800000c240078810034480c0b0415902484026010307580aa4101e40985081e12021035541c588961403070001c1c039001400342c002803010720780403510381d00502c0034981044000b84902561031402c6000c90242c41f80381c81c221850b0000b0300c800500d08811030f018108152003160403001c0f0b8040400024136202a00f140e110250381048140300158441c1901c038406503042c2c2c038064030a035591051010000030417501e615850340280034022160441100500140e0344560004d00001c810f110400d03650390b005554140d030026404483d08514a082600b900a03018072642110704c5800240000202d07003000ca4a04022a841c0c001300074200402707204000c40c00010002940303080d415511802e6544a0040c021014007140000b041d159034002c02840380c042c0c598400600810304186401c0024103403620055015010401c041a0b04648210544080e00c041b20190307204207203090b0303046849583c1003d0510074540c1d01c3c4d6041844031b50b07481c281101c01d8001d142c0d145225107000070043ca8807460000a05050b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 559368767 1250 559367517 559367519
    0x9051e010f0c02030c03070303110f0111042105060106261512010b0a08100507050703050a05030402010e04050421050901080610110304082515030f06050d030905040e0106 75
    0x303a0031884140074000540341c4800080514804030745404c8140c0b2241e5898800c9442c0001090380c062034058000810f03009031107041200c0e0703000600703a130b40b0003126080a002c284001d000c52541681189000f50000010302c0203640b07a0b80f500c43c00d0100a0300218001500c40e0a046125040e0080940000294110310b090030300d048400c94089415540b000d0388549981c0d100d42d421b4190940102c80072290041c11400b41540d03400d00603903200720b88130461152a043c280040c4c10036000e0810ba8400ca50151111487c2c9142e42404484552000780100d040c00b9070301c18800610703210b40c402e151050703124500381980c50680c4400030318081420003008041007410052080b860368080c022a07045041a14031580c0030944010688981d89a200b01d44007a102c003040c0050a004009107646e803207002060461003210034001c40c440d01240b20300801d8100803110982a620901c03d51211000e091135520000702ca50304da0002400d02c6600c09410350009078407400c18009494130b4400c0002d4080031f40020000701d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 559370017 1250 559368767 559368769
    0x30080c0106140a061205060301020408010231080304090e100e031c020f16080421031103070305040e1015030b130501030b0708070203070c17160b030a0b0f03010c09051e 74
    0x1001031715901105640310000b003803107034a003501510701408440f4002d40d1640224002907803401600604c101c03002c1450340486e500d03070f4020740710441079400f400701452600742445007210160948546800383c0e40700e00240d0702d40c0c01c1241c0c41910f02c1d903210140599500c10400c00030003160220340d261620140d10401481302d044001d902103402030300f4080c5803c030292886062110301030240790300407100118410410304800d111846041c0003140320f610b420000310201c0c0f803d0f039500d000e1040010007007442000103001c01001d010304268014641c04102c0152502c40c0ca251001500c40180300022036159500030480d464001400c200c040c083c00010070403503140d91241100e4039000340144061144080110700312a10a1007212500c58101c50309101155468032503c0314110300c42013201c050701400030003107000c460a9000c001295101103060f030442c0c540d1666100100440c00640340e020a82d07621402c2151002e00070078044a503591110001c04e49002c062080004c1026107540b45010310030441942 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 559371267 1250 559370017 559370027
    0x318060c0a030906061223010207050c09040203010e07091a010e0d03050901022b08180c0f01050d09080d061a0f0d0e031603030c0930080c0106140a06 66
    0x1000c1d1842c6004114400e50381016002070103180c00041341d13003819180400920541207000d0103401e0280c04004090040320031502e00301c0c040d0307038401415074020b611030343d04502d0a9a10a60094001400002c040c548105201d14286403507100600050f21080003109102c04c100012200700e07020708010164024040018402d070400300402001d210707011a032510164400c004c040200f100f4501c1c502003861200111080d41d8811080d61400a1100307400161a032510b0307050403005108240050207005900c0040140302e15004d090507042040034404000084600c0c0500c4500e91b000702003ca598014540a040603503500d0b400810b84015183c0e05016403083d08011506c0109610b01002e868040100f1448080d160321007a00d08148004100e01110421091005c5a80c5101e900c040041c00e00c21130007540c503100288541c880040c03200c1561421840460441e42c06003c0c0440c1c0810030342030942d6401982d03009100580340aa5490101344090f40282800040700b40003150030f540328610740740c2d00a00d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 559372517 1250 559371267 559371277
    0x604060f11040306090804050a090e01050c160f050c030a0b04060b01050901140306010c0c0e09010b011806080a0b060c0706020606010311160606030b150a05040504050c330318060c 79
    0xa26507145805030910546c1ca0940b805030100401e188210740c0d07581001e102400e03031a03101001c82d500c0c100200e8400c004490880d445e2607010070500d0484049a01c444201c65014041500c0790300800182c0d1805982c14840c0716201e45c80b9136410a45810241001401c0311061000d150510008003c28600c580e00402c103180c0304600d00c06c1c1c440c0e40303079a4403004803442402c144004103001c1c0000c40114502e000403061521400140d0000c0018036561801141e408640d850440c11b86200f0203401e201e4148a55680c50f032020200d04045005140b4030003080c0560310286000f07600d900640403d104640d070602c13941e5040ba209203024810020312034240c00d40d0748205013a039110000f62000c032008200e2603400000045401168210f00b502c0c01c1003034103440c014481c00c460312900c0540c02c0416280782a1049500460304007000303103607003401c4074107001d400c020a800842620031002c41c00b9542c00302c84030550101198410b469a12420041c0c0c019030b4025040c10401c1d001d4010004001c0348035000d40a0b21 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 559373767 1250 559372517 559372523
    0x6030606050f090c030406090218250e010c06020f0f040303020f010203090c0d0f05100b0118150c08160303141317131706010302030c03070803030a0906110c0604060f110403 76
    0x183e0300d0325031f45840001010300c41c0d8003e400c800b010311041070141c0d003400907a114030010a40003414442000f40480141c02007a46035010034041000c3c14201d512a040461020f4400c2c0b40041c5032141804545400b80c02200c0c0252803e100010f040c0201603050001101c00030218000b035055041c040b20050711400c050110310302900070354034900d0074840c001c42420400d43c1c1140c00d4178100f00108072a84041c04d070f07810309940452401e08003081c8141c0c0031a4a4070845402e007a0000845003154006c0300d5000c3c03041c000780ca26079001e118090035041001d4180348000d1090328000348800980340a102034240013448400d000c0d41004458002c25548408401d604c1c4800809580d905421004e202a04050750404400c01e90700a400128014000a1a40c1038038003c400b12180b81880c0c3c0c00f010346e81c603103038082c1000c550014000b040190b5190b0b00945240340c4501801701c0e0f075203440c1c040c1c03600c01d8011400c071100e00d900c01c0003400244034480c400c4a0018107501d00034040401d480450105038441c2d84001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 559375017 1250 559373767 559373791
    0x306040b0610030b04021c1b0206041103011d03031005040515090702030c0106230901230301020f0d0b01081b0a0e120109141c09030303020711040204060306030606050f09 75
    0x1110360b1a109520241c25180300400464807465094034038802040e01240d902c01051500d007904003000d1044014a0800c81e099005080359039555907070305049068020741c2070b010341d01c0340416a40801c403503410040010308400210744030300d40b500c0061003014a80e07010500480c90102400000307622001051000342090b40d0311044c3d5124220704a217140300305020f0307151552030311001080f120010000c108410300d4071440031110580c0041044803647c800e1007240c9400200c102009545210500360300760020008000504100604003500d450368030040ca95160640d40d01120480c80d81c00c03140054001e400090702180e0207042c0048001d03c0d04c02c4502246c2071096141c042441c0e0f80e0750380443c0c80089100f81c024000111b00e440c1c40c03140d000b050b41952075540551900340358544d1100340c1c140c00441040c2e40e40003480385161270030b030000e40c08901d0540340030322099140d002c2c07501c0754001880201031540c0c00140c0359103181000422504960007940c46124090404001c0d684d5504469800c1590303c40a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 559376267 1250 559375017 559375039
    0x5250b07081f0b0c1f020903070504020c0c0909030c01060314010c020c0127120f031b0b011202040e010e0c040c020109050309091e130204050a0c17150a0308180306040b06 75
    0x1d10f42c176094000010020314210001140583da86540140030610310640032030701015101c20410042e40a55a0140810b51040300301d2003444c03510140c4c50f82c201140400b540d01d4100640d41c614251071664100b61540c070404200c80d40f48034024031035200b80030004d101506101c041403000a0003e040252020110001c030f03000c60144605005288009004200074111a04800d02e07042254000c8800241d02103040610003850003481d028024004540c4541941e0041c0e0800b43e80c422119008901030340c01c13944d904042d0700c03492801d2140d1500446184028007009045038108401ea9006103100070469041c02c12080001e100003082c0d8002d54811a030b010110b96503030540038440c540250240742c00305003807020b0141d696111054500c1d0b9500030384043c040b950314440408141c1e41c44850500c0040d02e0400c0c1e161640103c150312541080c2000d02c014002d02c0d0110010b081402585c00980b01a0310000f40d42404a4450f402c03904600c805030003401582c905a00c6113400b01c030000300f03543c0c0030b4000841c3e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 559377517 1250 559376267 559376287
    0xd1113020f030106081f090c26041e050a0b0415020c010e100614040e0c0307060903031707020616110f061e01061211040e011e05010509030a0305250b07081f0b 70
    0x4050b83d02c03189107081489c07483c0e00c10b070a01041c080a80381503c06420000380304600c5274040b60b040349003a03044001084400441d07a50702940403001042074500c1904101c0b04184000e90b030004081d09010740b00003250701880c800307402d81801d1199410103401072800500b00b00310b5114100d494a6084d046500150390b0351070501041c1041260328902d60306024501001c0380d002d8210024100340c3c0d029071748080e0121010101a041d0f00415111180903030710100008040e000e6003030400b0b6094000d403a100c20f03001112648a4601003460710300403440d0f00120108200c0b0102c3e90304d100d030b010314041e9024616516002029018034450491030941c0780c0c9aa40b0310714170b000c440040303800810812a0303000296035101400c04802c02100820038982000b80e1000540b50307c101c0545900c503030300034068401001c45681c199001d6000907041e11078041390b40d94901e0b410440030300110680c0d001e0901d2600300d2410b807500418803240140564001310305041420b00c0d16a4964004090350484130413540d9039005a1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 559378767 1250 559377517 559377527
    0x80702190213092004020a0504030213090b1e06040b0a061b080d0605010e040e03040504021b0a0515090d020a0b0c0c070303030e0c030105060d1113020f030106081f090c 74
    0xc1e200d14210341030074004000c00c140203c0b10003810304c5200d0300c0c0e5031000044040006030300c249410880010070510060001d490041c0c2d081d80c0c1c01000000005442c00b0541e160740c030110342203c8561007800f0b55110169155401c40e0f00c0365120071b044a041017450b61100000d8035194090180d14104940320356410300d028a445811040b460300860504c0d1103070359061300500a00300ca8003c86001034105000e852003820180640302119941038050360900341880d0074080250064124001c280d0785108841c610050f0611004842c40c1c0103102502e14a0b059411100c0c401c9070107800d110f1075134890301c00944500d90100c1c211a0440e40030312035a5141d11180003038803807406036080c015200d0040b800001304154040d0721030440d010045058804601e03000040500b240d41c1101c3d2190003140e1104d48500056066030131031045c031001460010301c0440071034000e01b02e07084080e082c8030302c910010051021a40180740340d41e020303008401d50b46103110a66040084040f0910070030400b15160301300c3caa5864050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 559380017 1250 559378767 559378789
    0x80c040c03141501050d0501030b04020f0414010b0a03110301030501140c13060804060f05100602070f050901031101170109050f060402030103020303070f03090510020307060c09150c060b060c030d0506010807021902 94
    0x9180103007c1941c403400c0003014079609480480c400c440d2103034140c1c0d00f03082030701800c0042d40c66040280c40a80c6003030041807156004400447c205a640d00c40e002a001102d00618003850080f400050b41510030b080707101e043e00d4054030741101040c05201e43d02102ca5025912010f88903540703840f034050b46540c40e22101424645540c15181400d1004220198200301c040d00104c42c0319508a0b150190390703450014503000c9500605811140700001403000c0b41c5c01010a025044040c50403420300e14588155182ca54000c0c1c11040d0000c1d00c03101407180140d08060749940080381110214559451580066a02d1181c03403030080844503045400010315001d00408401410060b01c510f00c11a14403a009440345e0146004868084c680990400c0192049080700c5c241d4008400d05d0070654403207882550840c0802900321101500c0b4a0a407282e503c03400040d14801101c800155252464083e0f10010342d20010607441c1000140410001c0a9a0000340050786600c210380c05108040b4900110702d001d001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 559381267 1250 559380017 559380037
    0x7020d060c0c060c050306010806010302090102070506030402130c08070e2704050f07090f05160903140708010c0f0210150504110c0d0e01180602030304030311070c080c040c0314150105 81
    0x580701c102200c00303401c08006c40c07140409a94140c49592403a00640c22405006c8105006903c2802c0901040c01d0000c02150001c0c0010301d83e10300000101b0405099808907800940003411007001e01aa42c0d0f00841d0b800c034885400c607914400a0b1081d10000c90380380340070b1100d00b5003900d21000314003404418804c612410300c041c010365040300d407100301c02000f51001040c13245c1000d00c0d01000550740300b000303039050618a14507a01e81325264550344030791600301206141c0d9450760081c11400542c0030b03000d00c111244c45c1141c2d01d030b61070341d12002c03d0040c0c00c2c1803d0809607000a03007013031540510407603000c6ca050b06030382040750700062001c4000b00106440c046d2514044552058000060842d90080e182c1f0f05085801d030b9503442d001c05c2d03800400c810840c640c072030072016920910200f030009020b5004214a0290720f0400d034202001a100c503040740c07503242e12001d0503400a00000c103c0d41418003c0c061742800300e08060146510140884010244c0100020980c1880c82d0104d15240c0c800c00460352060345c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 559382517 1250 559381267 559381271
    0xf070e0912030a090c0b1b0a172a0607080a0506131a0603010b03090c030d051213150c0f0311120901060e04060204181b2015010e060607020d060c0c06 66
    0x91901401c1c5015449480303050050510080038000900d00003410030382e81c0754000d020600c0360a0509c00160315800581940c644413034280b0f042c01c011410320042183c001d0026000302001d041c13881000c1c0840002a2100d0036050a0604008450b141ca080310f0f20390000480700065101c03030401d01c02500168081e0b106a1040c000400050f5112000c400b40d07010b0003c000541c0c8203002e0100425a8800499000c0f42c0852418020141100c41e4401d50725031000c4001c06640813404996036a0f51000403d410040d001c0e0b98485010a8084e44035844558070a000c0c2420424022200144002c0b8019044801906442c0b440011000c0c8400e4009800901c0390034401400c5090130318259010350854001c0c01c00115040350f06141c442d14502409210140340f01c0300504500a0030342c00c440c1d05a0202c802032085a0790b0036508800c2608020a20300718414281c14009541030070346411074540050030b00c910407407041c080703807000d079880c0e1141c1811150303c0000002ca41d4030600c000d907206440d284029140e14 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 559383767 1250 559382517 559382519
    0x60301020d0c02030c1b10030b0a030c1e061b0227070c0b0606040b1204030905030d180e1018110d09050105060a0e2a0c0f070e0912030a090c 62
    0xb03600080503240019001c13042d2091901c261100d41a8000c9a80105501880742d101e004001406035118000700c0030702401d0424031540b23a846650046129902580e200c45403481280f545e03c0c401c00c01d1401420b043d2405929001c071402102903645503569000e80709040c52880041c404403006038038028820092841d480303a143c059000741001c0c0c9500300554660407500b00007082e628041c002c0714240c400000805080040c00c021a40703107403a0091007141444102400440c05076070410a84450030566900e40740b8100fa0180100304c16007603644140c109007051030034003060103191f50b600030554800c00c1406010b1035502c0c0c0c0c00b4001e01110600018ac0b620001801681c0d9102600580c4107140207500034845a00da09051100c84505446010304404205010440c80e95101f404c1640072400c002c02000c3c1000322001c1555141d0100d0102c080c550701c100402c480d040d40c14003c80c002020307240800c0c182071412144158450090b000002c01c03100700040052380586071270744810030b907a42109040c5085d0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 559385017 1250 559383767 559383791
    0xb030706080103050d030c020304030809031627020f0a0c0309211a1b031e010b120f070c0f151508060c210c0c060702010b1008040f0b060301020d 64
    0x1c8020b00040d1513a00510031005c2c51503001e4000c040810070310307078000e524003480e41d01c6241c000d4002c040082da041c0590218642c074040c510950740702a00034808110140e41003152042c40f48507078800c001003501c0c0144100f0b14501d1020050300e4511070f4900b0047d00300e5205150846a500c42a000040080c0c8107100401401240b03200b01300c0050303c121003601c000d040d82400d480c0140400c46400c09041030701d0341112a000441006141c100780c28803012100c1100a00450320001c100340c00c900d00444e4007054510140e8507034032480d0b420025100c12000076040000c8024103500d80e2000c007606941040403943d040024180780c500070300b0600b21040015220303034600c848441c40680324800644c0b00c2d11010544e012800c500300d40071400d2440110700c0e00286211050744800c00200041b03604913060004040482051100c10302c5400c0b503500006d245042ca4080000300c06814001204200101c401c010001f040941102d0b61140c0000320701300c01e50303035800000e0301900c1082c44030000c15013820026410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 559386267 1250 559385017 559385027
    0x1b031e07030b0a090c230904111003150825240207050d051e060105060d0e0705100f090f0b0a0804050f010c020a02030f0f121c020423240c010b030706 66
    0x3c10b420300855505080c6d149420480c89030b0069034007801c03004940320800700781d1804008131aa00d480505001c82c040310802e11a03441141c00ea800480300360400c20050394016140140c0c12801840407110384c04850520f980f01c00030301a2590340000000c0d8100060710564020040b040c0200401840c125a1342c4a41c41c1c091f4807881000e07990300100e11f00102c2c1540411012400905803000544103d00309402c0906040142a004460400c0740c0203510b80810b045d11036041e0100c03c401e9a4461240b03125580c40000c0c0308040a81c40000e00d82d403003800c20b2164080d080c0031110042c0192a00002c40d440354208181415090040c4100540ca411407400c0015008600c0709452030080302aa003a4042160780780da00d66114800003005504006021807501345840050aa5050b02044099502591a50a00490740305401c08840703903050000102d00e50081c55a018a101c2007551071501e1070050041407440030701070b14400304040300d001c02d511052075000d5011850f0078400400703c612a582d142000f80c2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 559387517 1250 559386267 559386299
    0x705030421020301050f06030606010e04110a0f12090f3207080724030c02070803030106030b0a050d03120506010c06020d0608011401060806010804020d051b031e07030b0a090c 77
    0x3c001d5081c400042c01d2040d600f40070a02c034500140c044c060954860004440140c0c0c0000d00359401507617024070350180b42e03046c1e0280250310300c00e03150810462903800b0042c0c50901d40b50024000304d803d1081640000c0d840400c110b06a9071f0121981c0490281110300030351483c030402c4201901038100c1c10b9040c1c21000003500104841e640c0040d01c030750350340303525a90072801000c003840c03c0144a1110040c046c0e620035402207485402a1050750001c3c0e40740c1480c40e0440e03100fa404000041e07160060303c8558501041a8001401c04a8200042c1102c03668007406808040c994945003d6540c80002d031030b0390180f02164003580e4000703030440d59038a207010590000c202501403004503600c0e20811200e0340400c1500203050b038283c1d49410746a40d845400464401c1c20007042280c01201135546035002034820802400351a01c013225a0b058100c00100740f62603e03542d88450903113404250420a00d240020400314142c0e600501a0591540c500c140b403000350000d103500030701c4080481800030302495442900da03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 559388767 1250 559387517 559387519
    0x80906071a1509011205031b06010f05060903061b0408010c080108010f020418020304060f05130506060a140108040204150303081b0a12020702030f0106081e030a0203040b070503042102 81
    0x100342a00e400250b00c40304607000b030324650080c2d1403000511251108140c1071010700c2c8500c0c2103c0c40c241d04103d00301206580078003502d040754000307001408061180702155002d824140c2d4a28141010034000035540d4501408400f18a400980407901085225084402400301d40000b88008481c0280040041409210f81c2003a9481c0c0070800a0000650003100d0071104030500b01050050001303596002584050411070b1a140d5400001081d810140140c0b84961848521210340b0a030318102641400d10042002d48210540c440034480c1c00d007070280e80a641d400a20305446196a20300c0440c004114543c842815401301480000801d0380c006400c0e4850a00c41c8460081c0100c506011069802040340901c081122000c0c08485100d0036400780c0764481c0020f08440c0f0382000455003508640240c0c00001490b0001c2d01000c01ca0b01030600c200c00122180b100652400e8030102000b900d9004900400c1c0e0300c500c000903620301303028040051340e02804465081a008102d50054a022410460030407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 559390017 1250 559388767 559388813
    0x60e09031e07050705190f152d2003181c0302031c0f060b19050310050607030c06020c03130909030c14010204030503070605041b03050d080408090607 66
    0x5111045000d030a50b00040d03440802044500e08100820003d122501c0c0d14100d524100c0b1000920000c91000c0302004010107801e280e4817041001d801404100d0f01800741070b00301c454007481402400c0030008880c4441d602e00e055440c540070a08070005c4000c071514900c55511010a00d9a05600d295540410a420460300548815039941604120b03400c1008080c1c0960024000c010807031020010b00d03036001d80a602d0000d210b141541c080c400301c80e07c60b040002d0114020490840074810852902d583c9046030070140d0546c60000c80350039030581c0e2801824007800000c94100101402041440a0140c9c00181035407140d4014043c40da0b00e8000210701054074903036141c0018414a00d1060780035054266440c00d0b210001a12450b51103800511801550740d1300304800000300e02d09001070201f00388183c00200b81d80c02c090400304100e10701c006880d0b80400c03d0010400028000140f443c0c10a012030924240560301d500303020300c0f5409420455a003281d8001a0720081006071441340c08181d04e4036400b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 559391267 1250 559390017 559390057
    0x30c080d210209121507110601061815020109060c140414040219080f0a110a0305100f03050c0f123301030308040b070513030809130207030819110304080904060e0903 73
    0x1088801111002c00c4001c1fa800200051200c0c1d8410300302051081404c007852241c1c25034500003c2c0051000c1d0b017003203005035981c00044007000b08901907941e01000d1440c1c80480b002c0120ba412001d44181c1c03091084d03c2a845103a00e03010303121a0107640c004c041e41062107070845607994001e4a0244111a4100035008150004031040300c20302c1541e400740000c88100c3e0070a00c003900142c00800001e4a6140b02d21503400e400241c42038a0280700b4041d5110300c0141002d0801c07641800940c4d20b089800c117103d00c1001c945044007030000218a045030304828914011801c90b10301400025610300c60311140c4582c0300d0000f009250304a03080900580c0f181c806040c0036510600101d400340034020b0000940302c0c4643d030420204200030041c16054500070b041044050040d00300808aa205010850203c0c0c0002c080010300b0310164402e40f00d00340d0b190300a01088000c20f489030000c4c48018002041e081c03001c10ac500c0d07aa22964000000743c41c1d111501d50702400c00d400c2c402c5d629000500c54104899100b01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 559392517 1250 559391267 559391281
    0x207050a14011407080709080601080c01030f0606020d050f09130e0f0109030801062006070e12010221190908090a0f030f140f03030709030c080d2102091215 69
    0x220303c42c074004100b103028119460303000e0120f0b461a03010b07003444208842180c4c0407070545418000180248520300c001e10320384141e5400035060311030f81101801c2e224900101040b107070727401191401d80250701c0e241450345da000c040715400c07260040040198110f4844100c10700040b010f540440074891147e0101d5503562048058142a600d00844c000c0000d2100001007005902441c24601c8494241c03029803824010782100503e0404c01700c450900042040e1142c00313460415401400c8201006402503103485050410341c0d402d46004500300e512a2800d00005103100401182102511000103041c88886001d041011a40d00010000380c421010210006003641820000707500301c03540003101c00c20480c0d680d150725140d00e0103044100c0c0503014004207521109800d100840c032806a586803418018154105441188120303000041198002004684002c0e049041c0c08038080348805100c40000501c40d024019006a503007464000b14502c400e210381c441e01090b90802c850012145003010365a4007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 559393767 1250 559392517 559392521
    0xc0105060414101710020c0105100e0403051207200606010e04060815090a020a0b0c01060b03071e0905030123070801180e1203071d03120423040207050a1401 69
    0x30342c00810480c0750280410213039143c0000401031110000079103600500e043e25031001c1e40e02c00c0360040043d0750364908200d032198144000d0070141454410030101c900e0030359000340103845518410546c13194040c000541d52889041903800d415500c5101e54a41180c88507082d075158415a031041c089020111417080070b0400c0c0c17142c0d40444030400c0040060400002890580040217000130380c00e40161124040940c42c1c80160100034260003240c40d0b583da510b80101421182c1a41201d900d02c2810414000350580c0100042080c003c0341c0e417966201340103901c081d01d00c9244c0c0d500186d0036509200341c0801006010a0f58609840c5180001000d9500c24100300d9441c0c030f090180301c41c904001e500e1241065075a62080781000031100440c3c6245841c00c1c0c0616a5800484019000410507401021b0394851101001c140c840250014103035000003404a4505000b01e00812004201c030071103101c0b6460000181159440007d481103594a0480c1401519041011029104040c084400000c814814 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 559395017 1250 559393767 559393771
    0x7170307084005030f210114010807021c020a0312090b191e0e0c010c030e040c1803060603030f081e0a09300503060a060f05040306020c0105060414 65
    0x2c03811498000c44400440c07204040c881d07800031200014042600c001420410040c8410300184400a0300c0e00c180c41c1518040e4011900307022408507544004004404c81c0b10300b22400c810003420000031907901c01c0001c074542002d046170b110381d1954a03003c2c0c101880c1c000c117910701017034029a04d03c5000400034403540b083d101415030041403800a080015846880c09225000f1880b41030300210320048000d01000100c3c0100f0301600229540b075030642c00001c03003001060844642070034450170004450318080c186a81c1c1000700c034080c0c1d44941e401201c03144940c0c036070100c030b40040904410a80e12410000300800443c0400c0f0f01040c040041c3c2e40340d0600408410b03101c1d0b05544005440300d05641c0c600b84105401402030081107880c0c403403420000d40c100158020480070603070252100da0181498400880108850301d041c0b02040090011640303403880c1001c01c1c3c51981c20020140c00854008545034403480e80042d10341840172805041180064026070302905048074144541e602c0030356130303c200c8442 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 559396267 1250 559395017 559395061
    0x6140c070504110f07060606030506040e10020906040504110c1615050f04031a100b07030e0402071a040804060206010f0b09010c030302161109070509030a0303110717030708 76
    0x300540421203464143c00c22400c2481c118001d5051030590107a142e8190448042106c0707054844000b44015076042c03045e280e003d14219804c0c460204212070f06500c5840f815000c100d5281c00296140141e150401100c00802010707208000108000401a04130b401c104d104007030a004100300c1c10003041100019006590300824080d0720610b000b00141e80a500401002046403818480000401c460051408444144080d21581440c2c07440400020041d241c00c01e202c295010700c500000300e40d001d1302189100c402998010f988040c0c0d81090054003810030301000c0307984610700401082040381d00c041d200316581a003c0391503d981b035040960800906001d0300740348100602a00f01c80d0740c4981081c07a0300c24081e040061401c0c068020f08110804007440c01c1e00d807007214008418050424410300c0c5c1e4070100510f00503080c100d000000a8640308552000303800c241d101c0f112200c2d1003044004941d19030342e000c030007081260811510781c0c0b01c03034000b219503c2c04182140c00041d4042d035501400448070320 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 559397517 1250 559396267 559396273
    0x9030506011e0317130618030f06110703110d030515190e070c110406030c0e041103061806060d1214160602040302100c080304110d150606140c 63
    0xc00c04402981c291052407a40c1140e0344815000000300399035a42500701c1d51101008980e44045c0c0c51011611030360181e1050042218032140f0901c0c0d01065400170b400d50754051800d920f0304c811030824a000e44807a04040a031404005442d02c10541c1003030440d0650030000c01a12240005248158201d44044481694500c04100d80d11420314122074444455142c80c42c1401c00251a1001890b503205d0440300c00e03001c01e40c0a01814140308011010740001c050440d000d00c049815030b5036007441100239204a00c0155003d1000c6402c004140400700011000031b81114030038900110380da034210b000d07401c2c6002c40e40140c4000c5103581c20046030307800d0501d0300f021074143d0410b40d42008032549110045900004103090100860424201d103100c1c074094060680962550f055004110040b50b0a02c3c0c0e910a01002d24421400203880c0410b503a800381d08119410421260310b80441d8162410f140002c042281c0140884031014a0f03a20500a480300c90740c070f9401110014801905c41d00c981d800019080d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 559398767 1250 559397517 559397519
    0x151b020112091e0c0801140c04060f0909090f020f010201050735010e010e0c03070912020d0602030f0106110a03050d05180a0302010e2109010f03110a02070305010c0903050601 77
    0x1241c03a081105540c0c4038100b00301034001101c40d4a200c010040c801201c02c161020802c0081c0d501c02d029240f0914031800b12881d01b0b080c29522440140b0403403240f4400d0048032040c01c039210707000320100c2c070040a8602d4180408402441c1c50901c07030340d80354001ca11943c458441350805510500c43c0340d1041c51036880e4099865590200e4503405031a80c3c105603006103d4400003240a41c140146a0090030a003030315801d5035061071514915440c0052400044400600030402c40507800303a4900b01710340c00c22030301c40c1c000d818a00106440515900300601240c4c000414030894582d1240380d42d040b0b0741d5941c0d92403070ba400302d070100944601075541c0c0036001450a002c00d00502950b5071040e0380010211582e003020100c05034045090a506d268140d0141c0d5413801c04034846030007408060491248801180401103415010038021301a1008039410051503d80041c501c42c0a540440c48400f403c25107281c0341c0c110000000d64075501070004940d203500b440c0008101d2800390850005030307644036018000c0d613 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 559400017 1250 559398767 559398797
    0x91b06051b0304170114070305060607060c020c060a020a0510060b09120f0d0507030201060b090d030e03010914010b24040e0a1103011715190905120301151b0201 71
    0x800560780303482480340010440010a0708580a140891185540c00806e240a600302000c900d05802400e100500d030520b010402e290792911300301c0744075079440f100c001290409024102e00e0855020062504100005440c2000f950002500714081e8450401c80305255030100080d400d0380c29074400c0c025074010500100b0201e242106035481250f940400f00c8103405444d00c1da40c0d140140510044020501c00145a4180356080c05004003400c448042c0a140c1070310500401c4c2030390080c80c809403c12011300b4007050981d40c01e420000285811034016144506040050350003411400d480c5840b4114480c0e07903959410440404541c07220792442e0390707402c05140090051404600814260038156503081d03800c06030f940c4a0145001c0c01590003818040043c3e419494a40b0505a40704070483c03c50404108003c8140c0340d01d10006002070340003080c03015a9241492a0000c0c05c60240e00700003012002054100100c4900142c94850750b8400c440810442c5000c102e001500e940640021000d000b40380c1c003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 559401267 1250 559400017 559400047
    0x50114042a1401030b06070c08060114030a03030207060b0306010f06031a030a08090a030609051509011e1a030307050c010e060703050904110d02120106020d2c061b01091b0605 77
    0x6442c00606002c64210008800a0710079440490211800ca240107014800a0743c10000180503108103400d8900c1810080c00180e918004540e00900300b41d00040c2500408c40207401084510030301400f103510650311040c030030318001c0480c01060b000900e0820561043c182c80300d003000600d480a4003034040740701941c6814001e90700440c0510340250a0013000000070b4110700c5038009190082000c0d00d0081c030900e0342c005030311202410345031003607041c44012a02164201d80012211100c80c0340025004240403081d1020094400900d506000204030355051042c0803609000c031000907a140c4441921050802440380140c88003e0005501801181405e0070140e0044140c0d40340c0807802800e04070001600416039110386113801000c000100100081901041600110021414200c010400ba0321101810301d140e050500714124200c8410011515501d00b11420000100c42280388014007542640c00707070101c001c2c110352032260340d102401c43d103141c031040c00140c4240780e551a1038030386402e0020310 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 559402517 1250 559401267 559401299
    0x20d0c0c030b0a063b01062f0307050c030f0601060f1202130306020705210a030b0d021801060f03050f150f1002010b150a050a0503090109050114042a 66
    0x242c0a41d18100801c250005940c01c4660110005e080c440d2042c204607041030724183e014065482c0c003443c0c0018811507402622011244190f01050b2100b22100c640c40007414440d044100e540f404006401400c2c0980480d800c0160700c01602100c113101e204500300c0c0c0e9101c4007449640c0000300400201c00781c1c01d02c1070040d00c04151030000d0250400c910b0808404000140e98000c5410560004014040050900c80d94400d128841c0448501e901094030f009000d12400c80c2160030190340340c1da00d441990300d2040d0455403c1d000f50800004412100e804080781d482801003030f0108000c2040b003a4080d111340034141c42902200000400c85c0c441c91001040340300956021035225003581803880c8103464000b2400c415650744c1d070011400c8404c03541800030390401000c440c00950401c00018843c0d540007001c03105002002e00c0c003182d42e55181e100b180d0060a0721800144a5420031803409070001244007058000c0d4001c564910400c4940c8802c14042c0705114010b40000900007400c002d032103500b0880705 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 559403767 1250 559402517 559402531
    0xc14030f0a050d140f010e060409030203250b01090c02100905070501030c1101050906150102030405090402101106010603020702130209180703060e090607090e070e041503020d060903020d0c0c030b 86
    0x12884c0510381101c032041c11800c0f0f910624a2080100411040341071b4806503410403c199000c02001e5500e4800075106d101d002c6281141008501e56020b0300d501c114041c14500d60000d12410403940c4468140c0c000c0d0200c401c401e4010301c140c11013110034007074922400542544c01001012020f1820005402400500201030140019150030305082c00c0c00303008843c85100d009019141c94a080f044180c00381c078245c4905411940180400d200c00d4855401c0603804c9501151400074240300804101d83d41000f0540210241c044e840c00001d040b80c140c1c006c0c0146ca8800c0b01d169144032061750003803049008030700c00d10764001185d0003400c1d50040d0b44642c040d00060503183c0421810389550714540880d0050700c41507080d0303105004100c820355024038072034082e20310541081d00034100006c00400ca110ac88140741d1007117a07550305101c50148010700380c2c4025680500200944d40d07250802c20000d000c00310b41500513005491880907800d00c107a94465070640d218400110395411900e5102c0c8c400002071202d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 559405017 1250 559403767 559403771
    0xa080a0c050d02030a06260703060506060c0a080418050f04020f0102030c010e06011511030a081306060b0a08010e0c0f071b030506070f050414060a0207150c14030f0a050d 75
    0x1031110900b81d00003148102d000400114001d450b00302c0c180b52040084110301603030300c440e50300c103545e411004c11070340201d90300124041115200e190000e0103d01c0782c28010043c6c1d00c20007918030100581d240140040b00c1038002910f502810451905040e540b0441d490302c0b030510800006001498501c501010003001803048030b041220030305080e802c40314481220381c495803101004010711034000b07240d182005624901002c1c8812459040e0341d581c0203688469050000c0c0c2c000051281002c007640b5090396400100030300c25540e0722002100d61b136004444840000b8140000810340410503a5030701d020701c20300c900107880c0011201c402145904030303210840d20200002840c40380303140c40000b640051405500941018208801c0140a41000112840500100380020000b100b02d0400c103403034210040c1ea2880c3e40e0110210108d0a000c0550000c83d44041c0e0000300340103060f806030541d20b250b4444c5014081e44042d05000556a02640c44c45c0d0b00b01410410446c3c10992040006c1c080d0b10b0140540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 559406267 1250 559405017 559405027
    0xc0201180302040531030f0807052109011505090106030209040e01020403060c020f1c050a200d0207060815010513031a1510020a080c07050613090507050a080a0c05 72
    0x4060300d00503a4034005d14040040c102c054144404c09040c0504006803064034044602d6501600208242800ca0140400c11002542c901c2c052821281441a40c409507500c0e02c403402d540010282c0140e0300c8614543ca411051120014640e02d60801d42c0c000178004400343e0b103040c40880c00303944020700c40d541080e2184511600040c0034000350018602c0b410003c02e44a6901000a1a0107810040c5100301c0e40083d100030011040e03100c401d007098040e4035180341e84010b5414240c03480c2110031a40480c214620102c00310540d80400c90070303503880880c0d0035244016940c220407140351034107550200580c40310014291566000700c005082d41c400c9010500c440da40d59880c3c0040b80b009840141c0559605081089811a00c0c49a98510184101c8450181e66140e0000940d41c01c18100c00405040001840013042c080401061008001c0100280e50f1072010229030904480d1354402c4c5122a82070030003045145004400f9a10f002e1103690351100c6503601d061012010f0110791014009001007004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 559407517 1250 559406267 559406269
    0x15030c070f08071707080a0c020409140705010f030218042406051e030f160509030f070f170318060906040b070c09051e1f0f030b06040902010c0201180302 68
    0x341d0300381e40c0610050390b1148080d09000072440350210801c01c1424040004d040011402000e03140c0010a41c64000e01c818190b10109000700071a40010f0010507120148004039800058404183d5a003030303030790030741c44410b0b0401682a8014440c140d001505408a42c2c3c03000c0c02d26501441e07030240c58080d0313001e0391040c2c10070841507a051604560700003000001d41888060851803d00c6400f10b0500036689075103400b4200d41c500c00806000030301420800988080c084d0b12440956843e0320008003525008178500c0c841698609a0344540d09007015804130005004a00c0c0400041c1e004111000c1d601c0d10108102c00142051244111359011001f0f10966100761501c2c0040e101410980b0300569840119080802d620035250f4030100c20f05003004100300d1251440c440810901e081501c0d80384403620707080601c444080c9410b4100200c21111500000c0c90140c25040d00e013140e020b400c01018644840b810702c030a8802607140039008c104c403482160010351203015640304c5150881516201c051b00d0358 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 559408767 1250 559407517 559407533
    0x2704141003260f040812090a052101020d020406080f060d0b040c030506010906051c0c14040b120309100903030906051b0a030509190e0c032205161415030c07 69
    0x207200f43c80030000450184090207081014061a003540c450840c01d19010a000034482c04550040c503005910401c03c46050303040c01c42c16441c0c1c0e260048000e40d00c80440801da44001d4020744203c10004000d80040351a511014020078005c120181c0f1a03184142192141e031000070010f40105c400494080300040800d03c20f02805001e86030010300824824908010010146036032038007409102110710b003042c0046d032103201342e0044070324000c800c441424078440094003c1543da005960800c40075905101c0c01d0001000034903e6440c01c91302c500c3d541c40b045808075004d40841c0001000b15020030014002d079030040018040c00c5000041d8003090006c00f4143e203082c50300841040740440d030003090300b410718540300c07411040ba25168803e01340c00e00d00d07210689807034500c06051400145030010100310358a1b0060b00b442c1051006d00303803610200207546080341d500e05a284e07003015650030b900008624101081080c406140c40200200480021004008030590001e060400100f07400c11818001460741 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 559410017 1250 559408767 559408777
    0xd08030a0606110d0e01080a0908030a15080708030f180d030e040c0509090610050c1f180201050304063b010501050301021903020f270414100326 64
    0x800c0c00440c5007803a10700c0103005030816025075465a0003112040762800e6216044012005007442d20004035110101000010100d05402a204060000800c2400880385d00451034400203031810703201150761254480d440720414010400150000c001c078440720200c04016002c0404104000b1100040350700004950030094441180456002440c80d51189020310403440e14544a080c40341c600686540050000d8600821007840ba070181802d041c0500e101c0d01c107541038841c40700f04460103994001022010b94840701e14400800d420140b0810301030011210a401442d412f8640604546640da98107000d001960f00c04400280300140350800d0313400c00182c4040f5480403e0100000500072420307a800e403001600302e00d020340e004104428a42d0340128a004144083d032030016141c401300c40407503025102c3d40300550202213000783c03014103650400362a40c480b508211002c10013607e030218800000070b02110000c0311140c1040c01000418105403010b06100d01a0b400070111448807001e1512640107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 559411267 1250 559410017 559410031
    0x17070b0a0c0b0c1303390513061502030309010b0a320a140f0301090308060d0503040e0c0a030c0206070e1507050303090c090f010b1c0b0a081f02040807030f020d0803 73
    0x6484050003005941040340c450f034180720102c10000c122141c07002c1c0c846501610609010705aa44101040205c01d88e2081000d0012400701680611400e030ac000d41c1c0760415a69085113510b8490701030032926058040d103044442d0a200d4190608000640c00209061001e455007403507214400c600c6282d4945200502408822103109441c410b90000d0040061201c00164002c0e0324004801010907041006d02d588075108640b00071103018030345000d80c20743c080c0e90b2003111a840c11800b448601d900481c0174016040c542d07a0104220010303048100c0e500d02007959410302280101d243c0c1c03c107d05011003600d42142d05003a80034601545a07841ca4550f900469510225800805d11004c1d149004500742d500030200101c090750950500d02101001d1003800d0300b4030010000a2402d12041e03506821840f100c1200610541c40c155a601205840e1440300103018501004d41d26a00e00e9a5081d2090f1404e80d0074040007440034a0450742c98002c20000b00100340e920140034250040002d0a00005501c0380b00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 559412517 1250 559411267 559411283
    0xf010512040c0923040f020a0e151e0a0504021e040308070506070f0509010c0201030b032e09030c080c070b07050106050a090e06040321020417070b0a0c0b0c1303 71
    0x100d0164250304460480c1c3c0700400640309290a042c03426203a030304d419040394114081d00e10041c031910010302c2140090340110310b581e100504005010f00c41c580c140c00c43c45021303a0940305228502c640e100106049a80701c81d8030825080040c04281041d5020b421030006130740010381840b4030f88000c9080f54100c0d43c03048804200c001464000c1020900c41150050140d0800300130300102588094802d0143c00002810040c01440795025a1300ca41c10070b440000f00a815104500c5880548800e4050103880c1ea00c0380a0003602d10700c10071640c6100c0c0300d0b0001d405544680d0002c0042d40e43d114103a00000c0c0300c1c07243e4419070b9400b0451000130401462106d125100001c0d8041c42c06041c0040341c00c80307600901c286072501c0c42d00303606400040b4845a0040c0d1500e020f41d0891306014810300700f80c400c03100004940e4030120700400c0c01841602c82102e1003610008540000d42d07600c0e600000d5119121079103000a640d0920382d4001490100b20a801c03000c5214114180340c2101c10810b0750205035807080d20006 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 559413767 1250 559412517 559412519
    0xb0414010617150705030a020d1407030507080609060a0915090c0c05010e0a02011704061d0312012c070e04020a031e0510170f030a0309020307080a050c0f010512040c 73
    0x80100103501c40689031141c43d03007152400c68009012800000e1a2050713107500080d6003c1054041d500c4041da070021220341d11141e04003414020014182144c208000c201654046000c52426040492180c50002d18481c00706003000002e0018015424100b0027001d001040072801c171f0400e0280b010a88a1039607001d5004066061250948014100f07400668116001c0c00000d0703684031117041100d2001088002460300c0d6454190010007540894560001285120514500f00400208000e178a220080040703030b620340c4c901c480d00103c0810104c0032424020209800046002c01b0290300c8030040c02c2038102c0c0040e10000ca0141e070300405040000a6540c03074401c0120303c2102411140c1d00c200f03e4101711501d000c240103007400d080ea01170700c01c0c0c0c0c44104441b14100c000422a1345d1032038190009994441242100c054058003905000f288240200039010900203c001040505160408000c0a5610304a42401540344000701d140741046001c1081c1ca0301c0601c500b442c140a60302c02c00e1401d1420b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 559415017 1250 559413767 559413809
    0x90c1b120a0230090d120518040b033316142704112701020a080921010203100905060f0a090c030912050703031104120b04140106 57
    0x1016000c00f01c0351140035105084520700c1014018400002d004042c85561a6078640c0040d0605020f03a0000b00410340e1114900c00c01d5038084007800041c0452030540c0c00c2203415204100540f05d02004803605513112070145888854003070a01030103030540d84c200700d00e103440340b4140c01070006c400c465143c0400302c032010100103e5445628002151003030b40205080001d00c006e0384040030401c3c803150008070010b0821104658580d48980d21208180251a946886203961714400310625072400c1d61200040c0280151035001241c6049075a501164081c1b0f0000d0807010030644682e03011001ba000c84101c1c0d084003401909100a5024a0004d800000036520b404080d50580b01d0080003e8092880c044807040c030ba840301030481060340e010210104031000500c000f00c0003007840220103040b01c0342e1804040807468000d001000c00a0081e5810b01c41c00c1d503441541491172259200c4c2131039041c02a0044804143d140d868035420500c580001249411414601800e5401a401594080c4852401c030307441 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 559416267 1250 559415017 559415023
    0x20c0703110112050f06100e040e011b03020a0818010209120a0b090c0604031403160b07121e05090a05010f1a1203120403050909070302091905090c1b120a02 69
    0x8844444400384024030703011096100218004c1c0402c0c1c0201c041600c030207d00b60181340d0404a40602500030014900f80e50380b624081c000440f581d4a0284681c0300105400380300b4021124034652507101c00a590302e40e1010202205c45c040c0c4c0c080d04c01c0d54240043d40e103907500d000b1f494828403400c000401941d8124200358581c1d1501402c52800c0f9400b40d40101c1b16501d4100a480480b0340100150402c402c8200d030090852180c409101c52002407107044004101e1880d090501506150b07071050745030b0203440d10301c6c030864101e4006a900c2c006401c0d0062100c40c842d4001c030785d10005032000da0b0040340141d9034550958a00c540c0c100050303a11207a40a03100711200c001c100d401c0d0422548558842031800740c00307071644681484000e650195100003818103003c0c4003210b0321203101804460061421040080007900240029031150040c07021340c2440305030301d0741003509031100100000c5040d2136401420364036a0100000c945c10888800154210850610460035800c01440384c40c1e640b12810b000080c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 559417517 1250 559416267 559416287
    0xe1003030f110a0c081e1b19060917011104120302030702130f1a09161b1109090a030f051c14011707061d04020d0e0a03030b03010b22020c07031101 65
    0x2c036401c02c983c2d1b210800c3d1000a9800403c0c1440503901e41c4180c0c603000420000b0403003600881003a40d00c6c800c0001c1095010281108641c010690021070001aa400b1400e07a0b00c800140034070301c0c206100600084d954400560709080c0b0030b0046034600b0220790f02003980012094107010000ea40e07a016080040340d2030180e14015000b12070804040421030b00001c0c1200c10141c5808152401e206154040714006c1c0711040500d02818112011a51580303021107a10500c01e910743d02901a00f400700c1c1c11018001544500160b142e01e41e081750341100441198650001800d16800440011000403001e0980c80740352808404c520025960358140141750803c03051600358081c0c030f54807200c1c04000540e403007403012100300c404244242c051b43c650380008020340111007602040502d06051540c00d050002042d440c10b0f44252801c7c032900c1d411130308260883c2c051003102a009443e211111802c50224602c1d51281c4224001c01410402150301491030104160012100d407035404a40401c15a00001c40c22 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 559418767 1250 559417517 559417543
    0x12070e01021b0612060319050607020d0903030203190e1009050a0e04120f12051302030d020619051e010b0d0b031207020609041b180e1003030f110a0c08 67
    0x19100505070000c940720707100c0d20314a04088000d000c017180c0b040c0c0c0d091250100700b90512058203141c2d0054144a40c64241c150f504030b0140c07064420444041d4060162401200c1d0150080c40c1441191a9082c401c2c4915503001800c02c00301d04000741d00b50750381c0e444680b01309020baa514098542410b0501221103000c3d000707240304000d0001040f0000c0d00d03500c40c1241008031450300c0e54850388032000c00e940c1c12401c41c03500702d02141054100044650340200b4400c007607000314201d80c2c0d0410889004d984034181901c00304201010741c540d074161914a81c001c2d580140344452a072203660704403601c900440d00280c120781d00c021000640014580418001d0003011042200601440c00103004205080d01c10f1013030081c001e070000304090b03c96a540354071207a800c0300102c42011410031001b02c01000c1940200b080d07040c25813540b40100e040031380c2d00d0040e4030548080e00d0105003203086807815102807034141042c0b001c0046007880200f55120500c0b00074030086c030030005c500d90a410b146c5000d09010981c8955 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 559420017 1250 559418767 559418803
    0xb18030c0a18090c09050601020607030507050301120213060914070e010e150d060305100c020a050d080c0d0c0804020a150c0201030f09170c060f0f0106050a0512070e0102 75
    0x480041d944040c0400111038540741141110442032102601404440802502c0c0071a0600d0010307484c15144c000714864142613007a10300a65583c5019011610b040c1e98023000690180014086031100014401c202030004140ba11014a05403030b01064401030b40080c640c580d11500d03012001641c01e441a81c0000c0d40e410320015200c41280001c0a200f4202c0c0c20500c07074064101c020300106550b4085492401d0f20b0a01404125200d0614942d5444c40c14034100e01d2503e17005810070350905c003280c0340ca01e1590100240c02080c0b10394908681c0b42070050521010b42404012142c45144c0a20601e45c4240540d202d144181c5000e0041104148607035100d800030b80c02c040020b860103580300005003041542406c0000d10700389180c0c0c411000341070203480202202c0c2640600040003803070b0000340c00c000200c3d0003181c1256641351008c5402138001d0300c0a501c0c00c410b0740c005006550094002d021481100e01d840e608190040ea00954070349010340b8901d0105400041002c035650781409608000c0c4148180 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 559421267 1250 559420017 559420033
    0x80c1501050d0f061e140108060601030b0d2603100f06091d071115010f0b0906030a0b0f1507061a0d0602130504092d030c030302030402010e09010b1803 67
    0x10420100c0d01c2c020000c0000d56100c82c1c0b040400e82c0801700e4000d04043c050100704088880302e0303440f0700d030780207001305038152140760001512980301e4010303032451210152021061510950340d02200940302c4080743c14030320341f4840f00c010190800c0090352041c0d0304411a003100c03921302451851017484581140d4100b01f04204280320841103141420220713071121480280380c0d41c5810b0111614038031400e4020b030b0741c0240310100b2100440c8150490507203505400d000425550785c100e20316144950b130041604454248005401280654000088040e02800022150502c14001080c0813922118048056000704d0600c042c0300c050721895041c1d490401300e8200c025101000281d42d650007840c000e1040b50000703110715604158400800003401e02400a000e4100c56181440c10380e0034041252000d071095040610690f09000190045180c164075000400821600d00328007a50008006a05002c80c12038501120384503c86414002d0071078200d016200c0d07880c00d1b0071581540e105180035100b540b08200e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 559422517 1250 559421267 559421273
    0x4091704090f05040309030b0601090905190e0f070509100503100c180302091f17060405190308010b1809091c0224040c080f07240806040b0a03080c1501050d 69
    0x1b2802c01a6900405990395035562030340100d800c83c4040e04520030880c01c10080c00485c1048203507400034000ca101082c04000d5510441c0380c0c0d2035205020465503980000c504002600b40807030200e40003a0b0740b02c03083c0d806d903881e030010a181c46194242c41c01030030303034030b6403005011a480300190307030768400401183c8540d0380b568000504030303000a0070308a10090ba040443d1540c07044400f02c42d00900000c1c2c8a11005030001031030301d80300c3e00c085506a90f24003a9205c0c0911054104103801ca00c250705455080d00c59007080030317800c00c40e0008084900e8200d0100d40301e00c041e41e20003404900c0f5920f208024400300c041e920580181e003000b4883c420543d0b014142c441e840320105030004440810f6450083d0150382e031800e0901b200e034850343c404040707801141d440c81c0d6100d1000c03480c28140c0e58001c2401502c90300c0c100d092102261081c3d842000120001c1c0410310301e18098000e100d40803c0280a007c400b500c170b8807201896440380701c160256074070a42907038601103144010329004020840b10340700509501e031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 559423767 1250 559422517 559422527
    0xf09040c03110d0b0412020f0703030813020d0501020c01062405030105100c0212210301051311190309120302071709030a0b0106030212090712030e04091704090f050403 74
    0x1000050038101d445002c1c0042e91611a02005002d410403107883c000c0c102414a40452503035010190700600441c1200780210300d0029003001102c3e49a541d40e41c20f595006442d141035010446c00f02c1e84a00740100e03c40c0840d8090020744a28000200001800ca02d4480751010b03001000359004440710840000d4441c146d0403a09880c110b410540e40c1c483c040b082440101c2d80b09220680081d8006044901c42030922000500c1c50040b651115012a044071444030400d003d01003485060742c801c246608107440e92031250062540c845000140c1c42c10b100c07507449060f8049400e5003007080001c3d902c0c0310010a006490100b05106259418110f05d00f0040b42c545510341d0010300304031021064005070301d000d551030400600b48026000f44006901e56140d000c010081d40c400700f0001e40041c81403021510720200461144112507405c40c403c0d0707005a4a9500b65034407010000002d9000750743c0c040410108450b402a49480c5d00c40c1318200d030382c2e1801d046682d421130b544600d000003600c0c81c0c14104000a5041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 559425017 1250 559423767 559423769
    0x90501120b040e03040f08010e031611121209040b040203060d1412030103030e090906361608060703020a0503010302060903030903010f02040501030b0f2107080d0c020f09040c 77
    0x12400105001e403881000c00c0c090b098549030200740d0b110001c0c00040c00c2d050114280241e0310150024421100c03171484103a07490180f00000420324808402640009201c10f070701401c010000341c1280440c0c090005200c3c105107001083c803421080000350843c09180903c9040c002c0c4100704e80071819400c000d030101d40310360303404a401412515408000b010390384c001c0000c3d083c1589805603490f0f40350b0312480c0c0201a148000e0382603005a1817500480c0f414440411600e05c145c11400d04820181c10140ca007880749403605000740a16041c840042c00c0500041c00b01d0b0b461207058414101c1000c1c5045982458818020100d1040602c14030040800980c0841181c0c1102c0e01140e4890b1511361160000c0c1c00e40c4110034940364550f1030b068015940705159000340049030b10980f401c202d1425039a040c08603005980a1040d0b00c9201d14031554015468030b0361030011501c4210441c1c6050b40c441c2e68103840c12a1401a10010074421511103045140c800280c11468a05440b0000d043c10140c0c2c4484d800c10341 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 559426267 1250 559425017 559425047
    0x4110a0302030615030709140d1713050306010b03100608010e0c1b100e010b180a18020d03020601080706030c1709160b03011404090803040f240203070807090501 71
    0x410f940c1d607506020389840d0b4003000e820a560b41080e07600600381030924890601030000e4540314005900d4240c40940581ea00303c440081e0302d01100030700c003269610004c0b02924591503160003060b261030800c1514082c0c680780c41d0b8199a0b003040c045003007042900350300c03042c10040e5000041c05100002803a1a40103858282c0403034440b07010450f01c02a01503000303c212214800c1c921080703240c07182500120030f07007a41900208145512042800301245510a114003001e0710480440d40b00f42c4c0980c840f044c15468845503511140e10b55000074440100b500701600107a01050040c40700610038003216008103c03a00f0304010503000d01c100604025490484800350030024000620501411f21210200f1010180003802c001d4982c525a0080c0e082030203500b00c4002024042e10540c18988100d01100d078000c02040e0a50f0b031141d4a45d042040149412500428450410300301d040745825a42c0c940100703040c0c05a02ca280c03544005040f03007c002e012608120b2014000c205590b00680c2c4c2d1000a80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 559427517 1250 559426267 559426271
    0x6030c15030c040e090c0a0f050109060c170412030908010b181008030409090302010b06040b0f0307021005070905030105071e03020c01110f12250e0111060f1504110a03 74
    0xc0d454080c10407030b0040d90301c0042004000b0040018410006c01d40907415601214074040703454580c4e00317125620085028190100365101c0040c010f01c0c2c00344204c04d80c4148a200000c81004000140c91450b81042d80204180c1c43e42e0079015023096004010000600400d400030404040484002214080c121940140c041e650501041c0c3e0424001c0c00d1002500301c400440c0d82e00ca0f0f0703d0500c08000c0c501c1c4402500107510b0500f080400d464203c080300c1c12190389003c02801c040450760012455840941004250300c103850b50810010b04502540c0d2003910f481e150314903442e10345000c3c5425030314005e04400400c54400b0700d40d101140360444001500c0542e2600503112003517240d100f8014171110b1140114400b0100d0f500d007000240800904080000100642c0705032030301c900d500b4901d1260307503d01945d10030344040250800e10402c0390422842c01450315500c5661520700650400ba81654410711030101c1408220346001d0141880030010030548040244054029050065020b98101e03441015 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 559428767 1250 559427517 559427521
    0x1703030f0c0702012006010504060e0903040b130f0f090c02010207150f0b1f0201200a1805060c0a05010b15121e090c030129151c020403020906030c1503 67
    0xa4450705c8429540031285109202610b00800301540d222002d1150a103c0c0e400d00001003403120b030420015028000320341c002d500f02810222200315640048016882d00200090300140303601588640200400221107584010381c207281e150800c0e00c440200b01c034107682c0104048800118200754500604c03408810002d02c00c600d004128000d0314400d1525a031140030448100980d11400c1903082c05a00150001c2224010300c862060460890701c2604411b400103019028405014240c00340d842c0f00d10018400d001a1140d0000e807a0b07401110400200e50b101a500b0002c0200c24880d01080300b100b101d410140340b0b82c1030707120190b42c840e18408070031002041010464201c010b51030b101c01032001c0d00c40d6081c14a0000e1102d40d6654000b6282c40c403030340c02d10301101c1d03604003480e04900340702820408203440104190244070030032416066464002408000107844060b80003a4201d240c10703510005660fa511394010403a032000003500192080e00113102c0444140c0d190300000100d9410031102503226 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 559430017 1250 559428767 559428769
    0x4020c0318040f02040e0f06120a080a18080c030d05130311040f020f030a050f040314160804060c0213020309071a13061e0c030905060708070c06091703030f0c0702 72
    0x58648000007943c0d45001040c081640721200e421580b1610b06422030a032203903100410802d8040380d2103942159a00314100907070115840400074803020080b03041080310200000407001920708158030030800c07608800c0121060386000e0000062040c624a00306003058820a000b139400030071848000d101c400300804518441c4c036280c211010f882c4199100315280d210050300d00e8103e80c01103074440c64491614000401c2000401c1c04103010b01e03055600c6150300f03c03421040680035881101050f10005040d10b502c07002410b072800801c06080c0b16551110101ca0300d1060082810788032000d101c4481c0140100300c0c1945000480c2400c031040100d450b06180001c042c155424450141c44441205103910b021607480d810441541003241040c0014400c00d000440890300e0351103120000300010380d030003000c2280d03207032a41c0035040c003c0c00b0301c003260710f4550180d9170f1501d04046540080d000c141c02407001c210214402100640826100700510701c0e40c50254440149010024541c101082c3c1c085142415 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 559431267 1250 559430017 559430021
    0x8180c130e0a0c0f060f020c1002010b030715020c0d11010302030c1b0601050901240f05090d0b0106020708120a0c0c080a050c0306090c01090e0604021306080a0b04020c031804 77
    0x159428401c10b44445031200e09204105085501488403202000a800540141b00703450811800c051035024216581ca10010841150780d80c0400904542d01d41d04100c2440e074042c40540014400c1c800e1170080f42d400780304040d007411a1806002e01c40c4500e46200d40200d00050700c0001a280309180043e52966800106070040c003518030b4064210b0100e5100d10200000051a035050b10401c0b40c40360385c2680c0e00d8003689091001110500d0300e61b40340c080d000000502841a50050a0310b40c00c0080c10a450780010542d0004982c43c180c80d00407004004000154051004c400a08812000b400520075400020171b10791044016860401c008529200180481149244094000007081c0c8541c8010303414510755030048541e0051003402204046161008000394108440c0010303110100c09034603003d042c0300c030340d07600404040d0815020414005c00d065601c0160010380695114544142002500e94040b119040d49150155204214002c455480001941c14000c0e03e843e9002c141c080310008280 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 559432517 1250 559431267 559431281
    0x30703021c03180b0a0207091112040201111504061a060a1227050d03060f05130902040513290a09030c1506050114090114130f03110108180c13 63
    0x890f192507402050302d1004000400350f41099a00710303001c03e62640d80220880d808241c3c1c20500030010080b1503000341c0e00500203640140141010f10992085841481c104003401c0c118803107031b64066082100300860b41c40741c80d0080c0800d80000b480c0c0465a008a02c0c2841011841010700403000c0c030141c80203941e80c003e420301d200c10060898020128014082500c00c0000c81103600d13000382c14413802c07564400c1c46103508035044020548484c514140a06c2000400c40540c0301c4495110b100510168803903001d05070092001d800d030103c510038035081003400c094242000d01180d44403648041400340d5141152500402e440302c00040e8038000e85030503940740000010061144d000513400c268541895480b840468401703884001036124040c60f1100148246641c00c0c0c0851010101509a00c007000c01802c5141c170300d6000c003900c0350344644001c1300d080182d50044074128042e0310030350140d5a01c651b07415009021010700c0140310915242c2c20340c9500550f1010b0380242505c1c2c12040304040107030410382d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 559433767 1250 559432517 559432547
    0x51209031905160e0103060e160b0a02190b0609150102030a0305220302070503070f0f1a0d09062901090302090a060e0a0b0117130b060a170a0203010b030703021c03 72
    0x19a0040d90386152040c01c2c4c20900c0180c4040e846c00c8001503000401241008891840000440c101e41c20000c040344a900f041070b0b884c04512540300482c10100c2c100003030100a41c01945172076100d1030300b03104000222000506c0001603555801456045076000000d50341508228240400c4c0b513514801c0154003444a40190f11104130689960000d26030040344e8182503038810740580304101d4603100102030810a03403141d1303550520906410481c51040341ca050720881d07208d40b8941e141c0003079030407075400341c4100307800c1551280d40e20100c0c04043c2c0320280410000c41000052650400700000010b45803140c2440060301400303038100003030300d03811640d0712401c05090030707080b102c8990800c0c0700c1c080d000b040d1080b1103e010482201c900c21000301900165441000591154109031505669640c440500509403541100c150f1101240c81c208030300341c40c00f02c100300200030000c100140c0109400e5075031803252103000380c10040d4140056140c15103070011545080403000d003003050920741290110440c4244c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 559435017 1250 559433767 559433803
    0x90e0f15030d171b0d05100305070e09100603120804051009060b030c01180b0a0e06120402040b04021303060203060a0f0807061806050306120a120903051209031905 72
    0x81d050060f00f000940d001030403080070501d11551502c03042078029034118410002c950b024071098420b40780540046c3c1d03010a03540c0c0c000b00d6841d07581c0e640034a801901d8009050100d07846d0300700300c0c050300200840e0351041c2841d903050044900d1500c070203031070403c902c0c0c10400308203251002605001003046800c5840044000400070030200c1d05082d401021090f44e500c1c402e0140c4803000c6503540c8645422924940e100400c584090715016107500a5888961103400f8402444922a0155280405030088521305c075041d20440c030b0103204110880c5d04400700705110364414081403403181c12800d5100f0907a0b4ac02100182d49031540400070f00488540e510940b256140c021010401c64800704422088440e56107802d203101104d00344400c2c420380c290148100045007400003980724036040340d81d11907078040c0009442c90000b103038490b82440214405441d02080c1701d00700070800c204042141040100303030500c085003040705200009403240d484141c0340182d111a144a0407d0180038401c049110b200c031101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 559436267 1250 559435017 559435033
    0x4200a230913020414040201021c090504020f0a0e040e0d0302070303090501050c19050306152d030907120b060f061b0a0c080105060a0512030c0105090114010501090e0f1503 76
    0x3001d48260441408901682c203101c4410140c581c0d81050074086c45d4140c0142084d091680c1042c00100304080342c20f410042d03070890000321500c8a2000b4080c011154401e1603070f4201e00344028103502d03254460b0038015464486024903080020540300d4205200d40380150750b840860038100c01400988901414a502c0d00050260300403c01e4000c180c41045820900042c0381c0c0c2403c00d59913404103c500b170303030840d08414502d0036100c00b41c0001d100c40750810984107484141002841d007900040111414a1100001071128038034041007443c000308000e0065212140303a0381d50750440380801800250248074030705121003d035a6484c00360380e540703900380c400216000340121003d69a46211901503c0d5010034100114a407503042c09254802c210140c114100c0300e1414061141e656180869144540401d20043d12a8a001c0c0502401020448004103103040c40c480c0d008000c640683c012030500c110881708004d80311542820302d600200c0712015003130564555401e5012007500c24034560789070003030303580c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 559437517 1250 559436267 559436281
    0x7320912120309120301030510050c0d09031805060c0705100908030f03100f06020c0907030f1d010f0b030d0f12061e0e060105070f06060806040b04200a2309 69
    0x140d8400c03041003080302c00185013010043c416210031300001e410754000c211007020b490a0b03070700615000100201070516003d03003075114004640b1106401c4000445400103001c010610344042c40260500300d440b41d280404582c0712640c0c03881d882c841d91b030013050111b41418079240140b0f40e07a4001c100d141c3c262640c800c1d2032802c0010742d41c0100c400040491000300003003050821490f0352001e4401580042c980840380c502000300000005059004140c0c48e81040d0103644218060010007030740c0300910650600096041c81c1c00d6403070060492019500e0184240541d40d00010044182103880c01c0c0f4030580c041c840401c039a0a1908200001c0c2107062440001d0750340000031100c421101c41e65030701c8040c3c039152003600205050540302180011000d200201c0801c84610407088418031074180069816075403100d0a0038000111400c2d91039400010401003441840d902c00c14800240e40c00110b0f040d9140710020340c1c060280d0240c881d55885202c41e003100c0182101068041000c020404103071031400c0c603 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 559438767 1250 559437517 559437553
    0x60f0406020d02011a100810031b030312051006080c0c03040b0405130606210204150e18040c1716030c080f0c1c020102071d07320912 59
    0x3001c00c00540ca450742110420001907000b21905000408541071014080000c95030301c7c1303025011614401c0051000400295617210300b068490200c00700800b06895030601521024840b2040144103061404002d40c100c44c01e0407841c01d8896904042c011601c520084c0042ca0160b01c200220901c00040d0110b800c0814002600c2214812181c8829a982e0541200180c03130452040300081072440000c100301c0d00003640030350311035111205d006040c41d03910a10718290b40c02401030700020800c1d05102c1869403c00b650420b802400003004850300b4100b46d59209800846449070100c05951205051031942051000b041065080c0c620704e2041c98403070408a80e180210301c912515403160303020002c9001004070b004860500010001d40200044400b5030070f0064100034101d045019198002c00d0304144040c540341c0d46150401400418a007c2c00042c12520510b02c004045070906009820544621842c000301c04201000d500d80b9010303940086000b2414041c00030f00180552000310b12010104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 559440017 1250 559438767 559438783
    0x7050a0c030609110315010504020f12270304060f08040c0905090c0a081506060706020f0d0b130e061303020f0d12051501120533010305150a050906060f040602 70
    0x3900c0d5002050b04130010140d40300c0e09051303150000103130a07004210600c4c1076400f030010a07400c2c140c80b43c51701055181850601c001102e544201188049907901c10109041c010072101806c84011841c00e402d21a000d40b107248981002030420120394005403c1051a203105802407444000c244182c3c14080791194544090120481c090b41c40c81f903000541c5c60000421551409410420590a4a651061158990240c1419201c0507000c12108104075440c80090006401907400011034440202c104200c20407412401e1000c030f4203049030002d1404000c40c010307411603102c1c800f4120340c0e0b100d0300c0c0036400c00070f010481d00b03040d00510214200741c48e0400c2c0d01015199014070200290765425210411064065651500241114498000340e0845902c0160000202e014009580000c0b0b500183d18460f4880913074000c07500c0f41c06122640d40c25019150b00001c610706203414060009011600340d45c018810984112000d40111341c031500d6180c00c44141e0883c005d4920343e80c54580744065918190 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 559441267 1250 559440017 559440023
    0x80418150f030219080f030309010b0301140106081b0316022b140d020307090e0a0b0916030204050409080304054b070305010507090608160507050a0c030609 69
    0x1403200800c049401140890107072801900500d00c154116020700401c2c02074480140c000e0610400081107404040002104c074802010045549181100889081d6264015124000c0c1e06141e242d400e03d009072121141943c00c03915000c1c0e9256918441840d11182056040507942c0d400418401c005406081504045a0070f40840d100b40810b402c3e003c2040d9080680c8030001401e0702c0034000c1141c801d10500000d24851407201c0d050482103400541241d10035113501011444800c02002202d00a001045e0700400000c2c08001032010341c00880c0160a004040f0010030f120034090200e442d01031390503a0007a00014008024418980c41c103808a584150350546451113480ba05022039003400400c140d100641c4c505022882402e1a103c0c800f02304010b5410000a082d0b10500d0706040c0100889002980603c0c00401d042c10300b03e2002c0c00d080000d801020800c140710040102d107903058085401d1082c414038116948440b20f0900038240380d002d11004210012200c00041488150b401c00742e81030f40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 559442517 1250 559441267 559441271
    0x602040501110316030c051608031e0a09090e01020f070c05031e0307060b041103041203050c07031704030921050c010813030e0f03160e151507030309080418 69
    0x40b21000840e582d000e0500b00461001498401c4000a07204900e2030744014440c104543d0105a0150b0923100e0841c00d40019825600200300c00010707031600450030b044000b00408003850b01c08036540003070030b4a009000b2107045d180c13194541991520250b040f00c9504c964030341d005441d12098a40844070a015200c0e1a200c2d12030b485400303d4049a0702040f181c2e82c3c1c0920000e510f030000950f0782c400500040003219901c1950b4041da41c01580302c45008501c201c0c815984504043d4607668090215a80506203590000c01808142c0000c0c0d001048842c00030b60840311041c041d665450111200318107500424440d04810004460f250940007441d480399100da000d031030f1480800001101d81520464140303800c410300440120203e40110042c0350349080c054a16060005c00a001c24603100c3c015074081003c0c2440c070001c001d10205810816040400c00e600002866070000000b80400e82d08281320340c10003000200f01c0700701402039119460303641c0d0060340c0984440d500e61400d205048110b200388240c0b8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 559443767 1250 559442517 559442537
    0x12020f30030c070623030f04031809060303050705070f0b091912030f0f030507080f1e070906090b0903120a02010e1005061e060315010e090f090f0a081605030d090602040501 76
    0x100702542528441c80700c7c0389401e01d5039910381e14100d901400842840c5561b030071320540840e00a045d806004040c3d4002d03255560b440040d03103820341c07514080d9807021a040d19200400e1007040c0600c01240d15412003100c45541c2325048441443d4003092070761102d0402329045420300d08054004044502d04c1c1c5c1a600c0c2c40d242240102d4042d4107540c0102c40c41000540b0200021b404018614601ca070000c2c0c000243c0c1140343c0c0b203066500b48055081c0c43c250003242c15541c04005a603442502403001e001c07045840750a001668001c203940b070078103461818417001c0c0411488801403007540020b240d21044e07001c880314007241c00240c0009190550f00f441c0960108001440f2040b94094071003121040641141d2540e52107c070011009070403006101c0c1006401e094541e150f0707940d00c90321400b1341c0e003c104003901801c100c0041ea03e0400885500b001e44d030002d00c294004502880140c0700550112400308200c04030318582181903100c0e100e43d4124003440c28511006001d0075501a0040d22002e2720707580f03804 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 559445017 1250 559443767 559443827
    0x2b0326060a08070e01030807050102070c0e060f030703150c020a1704031109061012150308030703061703040515280206100302091302061312020f30030c0706 69
    0x5402e98012910011381c501d00410008803100c006119140c09200014242522a81c900d2484001035211010907601102030211900e40202c0c030b5440d81501710300170a800ba142d0381c1c55102e5401041407080c9659598001010f18030f00030300188a40c56071244216a001d211130700c1040b0560001e0100703540031172100c03074035400509110100c9405000c00410310716031030465500c00c884d1007912041d51500d03240c035200503c040c6034918910310007851041c7c500940760700c4c1000001b02250020b40c000aa450380008001c541201c000c812a8103992056030000585c580c3e482c480741c032a1158007500a010310414901c4940f001c4503e046030b0480d8125070a4030241c1c0c0380c042d0701c031140541900029600800c0d42010540c50441c3d05022120b9501c054102030501945204c041c022040913400028840c1c00b8407428000c6103407a441c8100c1e2000101c5800f100c000b05801d5200360306e0084c466015000814084000100c0c2c0100301355016240b0010032030700d01507200e4100408840c24151040d21090340c08090701c00c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 559446267 1250 559445017 559445023
    0xd020f09070315122609041e140103170304030c080f0703020f030a0f03020c0705060a0c050723010c02030c060a0c0506010e090d1821030e2b0326060a08 67
    0x3c82c13500101c0406509010041700074034680380e80c0c022040650b0810404e040b41c1c89030b00072290f030362408880c1d049a0803850aa4030042e198490200000b8491010041c0700040c1ea200c00400c0e280140d80c003854580c0c1c0e0b01d20b0162490b966120018044420118070078948104c030400070300485110354207540e1b0540102c041c01d940c81c0250b03007100340424811401400c81c54442d6010700b0821110a0846103102da84e000411100d5001d0000c0100213803c040300d400a2040c00c10a15001307018036010f13000c03160b003801420203508100c220b10741d0402801114410a40d5020010100b03020802448e0715904e114580d409000710041010450b1540070300c80000440c03c0032800428440d6485401900c4219401001101d5070b503080c1a84032906403003048003245620031162414807d101100c0c13103d0007038165007000740210300100300483c4201d800002000d81030310b5500082444040d40d1507941d07111903a91405403405c0000240c415450030448030b09512400021206500494050719503520042d120541551 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 559447517 1250 559446267 559446299
    0x18010204030501050f160309170d110a0201060e0c160210030b040501081b06070209010335090406090902032d030f04061107120b07170a0605010318050c0d020f09070315 74
    0xa609661288100903c12460040540c0307040b2b640000341e2042000901525908405084801030b90f4640d410301c0030342140040d103034100c0d0800c144642801c00c0d03400c0700755051600d444001e0217280c0c000c000748020381c001c1c1c07c40054600c0040c001c2c0255a12103640f00d998070980e1007090208020f002c0860420b042010842d01f62a40240031103c8a80c2580c031841001d500200070320207800300803407840d086200b51860204c1440341e14002d00343d40da00720000b00030030707240d103900080012444c2c41e1040740140d40004607041c00102007841071001212800a4104c0c151201c2c462040c4c6000000350076a441811780018030035a00b40f6215440303d1040d047c1141e545143c03600811080d54540e0702c0c0f0002054102200550000552500d146914000602807a020030247c8805200d19110751042c050346d0b8041c010081104485c1003900030515054840f2942e9900342c00d01280140303110341e00003095440c0c08c211408044130181c22001d96092182c03000b0000d101411401c40d081d4109034021a001c801541010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 559448767 1250 559447517 559447523
    0x105030f07090f291c020d1101050705060c0408150f04110a050d06050109050705030907062f0606031516050313060e060711030f0a080603150702160f0e18010204030501050f160309 79
    0x9480740f00555100c0c01c40008823000700e410300c20140110400624100701c0380d846040f07030300040c680b07481c5002942c62400440040d100030b82560f400410104440340340d0304d1540903030001b08100b8904174103000b00d001c0342c42c40e4009035004940e2140345800e0141c0c1c0d82245040303a099030800c01203070395580001c41f600d02003680d085070540c1140c0e40400070b0501c184a6801824101d5641b5500c40d00382c0901c8000180400e001e407106a04254200152442d040c014690100d000b01c450341d2035071a00c00c10040a62010203607600a12202102113040700101c1c1034240c440315032000c003c014004d02e5500f0166220001c03669040090307050200007500e240e020041d540443c0c40546842d040c03001c3d100c2e00b52441c6800511060301403042081086401c441c900d0000c0c0640241d40241010f1403404606400c1e5900d07580014a10500b03420b4100800c501e50302d4441d600ca5071710380703440d20414410040d650285c4510b42c00580300f503007400c0900c002440b04480c500c1c0180039190590100780c070008019815a98048409 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 559450017 1250 559448767 559448779
    0x11010506010903081c233105030405030a03020609070906050a0b03060111060a201303030e0105040815060f0904030210110403050a080a02060105030f07090f291c02 72
    0x4000040c14000031702180300c0545007018024448001c0ca104880e6940c00c1c4004d0280801d02a0185030000b0710040d13041104404415049001c4044200344c13050000c038014584084000b901040c00f01c14815038001d440f000307013600c0c0c060b401c5043c000e566041c280c030009540c0c0140c80f000581303912a0b208141c121031000d41006c124500d08802442c803504001e0445041c442d00c6180450410028002d152103109a04400100118003031403150b0324003190341d1442d241440402c0141407a108181400d400c680d030502e40354074030400c03440040f6914007841d0300001c3d50340310702000703201c4500c603014400340701e542e080d1040340070144540204030311114150b4010380503800095070b100310134155400c4030b034181c007840e00840d1625a07250340d024039000c0c0e960700c01e9039000004620300b400a0b5040c0240360041c10101c3c01840698044401262501ca0030701c00d5480e1650b4460210600040e00c1d0454140d00303e200d0041018903031400640c0b09d948034009400d0f4840c0740415010710b8121038000c1d0840ba0241c010b014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 559451267 1250 559450017 559450019
    0x3111c0b06220e160e0114010c0f05060114150d02160b040506010501020d0302071119050612040605010e010305030d0b0f090c09011419050f070203120d0c08160f140d0c110105060109 80
    0x1c00c07802d0047c01036180307042218411000300401c40c811051118144100010000b42d0b00d02031000041d10f0f9001486440741d4a80d188058400916105a4029074800000140d403440000b2a00442802d01c4400406135046401003006003c00415810304840c1c080e000d0342c814011143c402c4040707100f4020300030702d210521010301c252410400c01844041044180b4002c03003d4603180051019000001a82d40e64205032080004000240c05824010606035a18550950440d5a11912805441d17a000405941c030310207581705540f542c1d00e5100010380900b0b10102400d150001070481e6000b9081640444c036050410080c0d002c09804650103070445400c0110581c18102c012a1315901201207008005014046100980d90034440c99255a00105c0080d0b520b2440490b0340c810b1310240f034800070912034810100700104481003031440c801c00061401d11204240c0318400e0310140d01d1002c00789024080450109080f400c035911011a411035a1603e240003812240741e1403d80701c0171108035000500340e1030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 559452517 1250 559451267 559451279
    0xf18101509090b030f010626030a1704060207060f0c08390706020f04060915090e1305010615020118020609040e031605010603111c0b06220e160e01 65
    0x440307030f41c5460000302518007000c120b0030f10500f034400a800514411002c0c1803400e082e02103407080c032070145a104001e14140007010f00c0c054000300c46d040710000380f8074087d800542041300c183d0441e40c0e504d91142c000c22082c082194814010200c1c002038401042d9480041030b00030b40d415850036640c10400390000e24411107030b1110368180c43c41200e111442e0a05100541c0012002d001400d064000501030076119031800c2c0f00280659440c1d4480509484844003040802d540088a038007580d026503074a4020346c40300450041e240281c05030190a551901e10089078101107045d6140c510740d6168024043c840c040c100416640d4800703940258801010000c1d0f100f01d04045d001000b1402240c000c2c0ea041070207001d042400d411039440304466a0350340f241c0034002c01107858081c0d07080106c1921884030104001d159000341400011002c0c050b40d100b48005511a9101c0444003401803200c0661141d40701c21504140103000c0740e0203049010b02542d2240031b0788407200c0d02070004441d50380c90059143e920380a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 559453767 1250 559452517 559452521
    0xc0e250f030f0f051b0408030a0c230106060305011706060d2d030207090506090a0902041b051b03030601020604080a0c0c030b07170615090f1810150909 67
    0x1121503800d0545031081c801c054107541c4950401c2d01c494040c00300e018680070f1840d03208150004001c1d00d0010303040c041440102000400d07107104001500b41040002001d040014034a0188402800c1046002100160701d22040d04000125500c0e03441c21f00180e62507031700c0020300004468500304964410000030710b241c0381100030595603d015540360300c0003524002c2a0105c4130320025001c00345003412030141040542c104001401881488010041401c1c60000502c05000240c0070944180d1540d510b4001d40d9169400503072802c204c140701c00c8410414010141c240d030400d01d1a010841d0920b0100000400c001c0304891064005074054045681c2d9540c5809140d0480c011500070007600740c1894002451112400c800f450141031234140520703110a004080c081050220000342011100380081500c541c1c1c6192111102501280d0300c8018840106207044c40141c19164044003d884560010f0030448685009800d40140172001c1500c03000020300c13a200c60451040081d070005c40c100700b00c03d203617 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 559455017 1250 559453767 559453787
    0x4111504080c090c04030b090607181d04170417150c030601050c0c040617011506020c01110c0409060e1207030903060216151a090402060d0203071107030c0e25 70
    0x500f5141d0b081940b03984400707c203014100d414000560095060000a60300003808035240d00381c64660500702420001c1c0c0e00c50910112056a0241c4000300c00700782080f1490300c08540400348020301545980c1c0d200b001d0306200307204c40000c07001406500d035690703210400f44c2c0d0050301c10684c6268140c036544030b20700115410352143c0e419412502845081003001d80d141c0c010103004080b1074030903c0c94940d85840301421182c0070701c2c1024140704071107020814140c0200c0d0780200002d003401c010254503418414241003c05c5100034582c0300345083d603984200030b180d50003883c034541144201d980342c001d0768a040020344a01407020780440c2503100c0410024010f03400500c44130030162303400a5504025034580e002c00c8910001e0807482c039100d180e0410203410751038a1a04800086900c0812030810750003050491086000682c0304540020014440c24012842c10004004810440d40b01c05c0d5071f402c0000c09084203000e405419548500400c44070b01d1424a2024001c1c40b038401801021405401a00e203403642d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 559456267 1250 559455017 559455031
    0x6010c08040b091e01090302041d01060803030f0c0c1c030905010c080a0f0c0c1b031203050103032015090c0d0c050306090102190e0f060304111504080c09 68
    0x140018a2000a40303100241000300903a444458a030110001001070040280e2488101c80c1807081010f0840da0f844030182c1c04681d01510000b0341544100c80d11006a0492100b9000560030300c000010b160780000003d43c0f04200c08008220300385c4400c4441c40b6244507072510b40c482d983c480c4c00b0681842820410950001c103840c24005041045030b070382c0d0390035100c4102d059004980f4020401c00020401d000702c41040c45028000c02c03619036900c0e000380180c0c0720010080c04188020303a903a101000071888002c09182c01503c1c920b031505020070014090311003400201c0c0055840700304010860582c0340500110300c42d01000e0a403e1004201803103800e8802025100e440c4036005e640001b44e12080000c600d05406803204c00c1c43e1030300301018145032900c00383c4122041c0e803040116202c210751443c203c182c148124a4082c01107007000c00090811340012206c3d035800360000051208000c900c08549031500e0b0142c03121a042c0c48a51081c5d0f5170b6020fa8819141c0c3d40d000b15112030200d240105180e80c0c001c0e1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 559457517 1250 559456267 559456277
    0x60602070b03070c2f010f1b0206160f1a0c09060a021015090e06011d1506030a06050301230718030807060605011d03030f0c010b090a0b0111160e0601 66
    0x207419200e0b40c2d00050041c0000d020600d80d44008140344042c01c4400030390b05e40c00c1c244000d42020070000104045840c5c08169a0138002d0017104046540f213508440e060180c0b81d40e15a030510080c03d12400c030350740101c0100c8403000350180c03c07640c03491150341680c42103445403072250504840030244450b6a003c039404200b1030150b1001c80c0481503452103040c0028141580844c0a18202000203040b0748032000942c001d03502800040003034040046107290308030155c0710400070546a1381d0a1980c49031011102036130240000c41000400d038401e41c4003a088075030480c024000c2c00881030744aa14289008044001b0b461f104000031442030082c2e80780c0315610010310f6030401040e1f894a07070040707907002400700315003241d1507050070001d03903034043c0c40c6002c1d0200003d92100c03c0101d03040001d5692003103000b5415400c4002c40d00300c409120a501031380300c070031001c4d0a5003501d1070b201030b0315030051032024045400300ea48140c181400c181d0004100d850120408441c116441c00c0c2002e0004158008110b40c0c1044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 559458767 1250 559457517 559457537
    0x60c0d05060f0909030a020706030b060307050f070b1302090105010c23070e04050a060b0a081018020d060c0f021b0f0f03030a020d02190506040f0309090207030804020f010201060602070b0307 84
    0x1480d0fa000f82480780c5034000c083c0d91110b400d40720090504034280d00500402d4100481900e840e943d01003169040b4001d030409541e111121000d082241c020f20501400c01902941000346290b040b04810254505c00c42d20540207030380703883c0150340001c5203d10103020121518001404003040b01400c5400060322801c0307542c415501c04241444030320844048840d0303044500448100f1101e80141c11182104444501805042a103030781d81da040900352040a071501c07201104249201100c40400d11900948210540e204904001e8090406100c0110010fa45444c0011807984040782140244000c02d58107a20801c850b81000b8048e2940d00816501040b00d8120104075582007008080495a98001c0e0020741c00e010b8002e8208050040c0b250504001c5481d0080040c82c0428159070099110032200380300e907c04e081c1250900981d410600e01c6c2072000400c9018541c12074500c511403442103490041d6840e20100490a0340c00900c2004050b9011038401d0020070540c0740615070103d89803030846864 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 559460017 1250 559458767 559458769
    0x6140a08100f080c040b042013094b020319090c0608010816060809011b17010b0405060304120c12030504031710060c030c050d090512060c0d05060f 65
    0x2041a8085182c42d8801e01810004d41490f0160828404040b41c0c10081c1e06003104d140a441c1c02105691100403034001149009800c2c54061000642002310082000c0d5040c01e004071482403141c601c3c00f0b00002c00d10002240e0220900c655a50315192001503003400d299056928040e400140c0780c41200580e0581008011465107d05642d03240a80d5480c10014503220000d022204103030844041a0050820082428045503070b8001321102c0380713807000450307864034285801400d0700b041c8540050f02101c4080c0c54141d02c0200300100c4102c01c150070f40d580e66138902c041100d200324818036810403000d10004000c2240700350b44615140c210f06060501c0c0c0714658032100303004114805032020940c0d8030144420306078044030082a0003a803140240c9182804161490318803410312900040000c2c100d042c10806110307000140710305900c034080301c50100c500e1401500407007503030041e04d01a00980c0b4001e05440c0000a40c1400341c030074040c855207407070320420140e405003c00a103080e8000000c51202d40031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 559461267 1250 559460017 559460039
    0x4060306090b04210512091606050414041b0804030203120f01170303090703061e02030108100b100e010f110307051c050c0c06031008120702010906140a0810 69
    0x31a40304022000d664546450311000e515800d46030a41c518084c52071407640303107070003504a0354005140100c50340d642d44c2e401c07031079454030006013100e400c4810000130001e401504103002e0400d8544c403110f044400d006610910003150700000b5036140381c84000a00700035950081c0030f0b458006000344107482c40c1280c0c03e0380e003039021407060b01d030b42862944610040141445502c1d80c400080c60420140d461803d18010007070b41ea03075290001402c150740e0f84280c01900210190071109007030444405540701d60b035900159841d10001000c8084460901d001041d0360b03c1c05d0034614514140f503489440da9204998011140000c2c03400991062005101d120414071000b0800750010a110310300030519500744861180900e5019165032061003024000d0403c0b0140200b0800720650b8155180340d1242e0302c2502c65200f048495005040d00d009403030a001d22840154001d00b00c0c01d0017031b200c5510f0300307645003002c031100801e0200c20488003100348a4468014480d4a8140d0421010120000e01e42d4a460410700 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 559462517 1250 559461267 559461281
    0x70218151e0433090507092904051002030c07080f0703110301090c090e1e0709050c12010e100b030c04090b030a020604060210060e060d1e0f032705060f0904060306 72
    0x8201403100c1810131020b00c3c6409800d0b404481460515002071070010b5080d0071104820000c000b160b1034840c516003401c0440141c0b00240b00040c0455401100340f40c0281d200c2d800302111031070324001c0101c041038090340090b10440d01c44156000b48602c070701c0c5444034451400d2030b1450300d9065407515503141c04180b8102080d130281c051004c0010b6200c1950810038a09481c02e80901d2900d085002c40d10440200802d545040340c610b240041256520650110320070f01c143c0750341c0e00d80100c12000100302015240c903601e205903510131001c40e440d502c4200340e003420b00040f1284200042c04200510a910362500142140c000c09403c440640c0003d600090481d007145e000752005070700010015032056458004d200081102101c501c41e141020700110340c94001c040006403038448007420036400360300c0c524407038610b068200c00f2000010030145801891000410507a1000b82c1c4150203806003403491054000c00c85000801d00381c545250b580e59020a9045400040e80c8165a1000000070030440d001c0e10b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 559463767 1250 559462517 559462601
    0xf02091f1e03020c100c050d02070203240910090b0402040908070f03110c0402210606131220030703020108130506090705040e0a0f0305070206070218151e04 69
    0x26071505580342c2204e10b0300b804074485003040f5080000c207580303054009086440c0801d4011f409a2b540340d007400440d02e000c814078490044200d8998440841400254260340501800e8042e607440d1a03d5018184c1031300c16009001d455107408030302103001460543d001c003051910940f00c65050a1941d00c2e03d80410858900690229001ca03080c802100f205001c210420a404c03281103003807189082c400c80c001194030500e068007a05034800700310269a04810b60b9460105000b0020716140c80358140d000f00d6591000c112010507813000014600142400c0803503810034041c004200c131606d56001190f500002503c800d10324146c5614080210f0400c0c8446480383c103004000f0040289024140000c640710211090510381141403800001145200303400c1440e600340c40c14503160202400061114814144001d5110622611035260701d03c00c4c1d101a8416a008203908803440700100601100b906926400c5410000c6c08008402c00e249c640d0021112000414000075054210180d1030242c040c144942 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 559465017 1250 559463767 559463771
    0x101e120b06030105090f06010b090109050607080408070b0301051f050c030403030e030c041116062a0806120316080d0c050c12090a140112020f0d0f02091f1e03 70
    0x20101e0305090042e80d03080002c4100401c0c810f100304191544850b0103010700e00121400283c0e4030426842404100040c040042200d44d5a40341f17490400c455600c0352150094a00800000188042640c81528129a000341007803090358130784070140a03030780000070481c4140700701030200d041d010340100064000b451003a121021101004c208061074400030455142c46282084a8080301c840c400c001d0354500407164031600e00594280c508000500f120011081110400200403071170b602c0c0750f00e55540106410748030071810303846941c180050101e0070320814038030785d108004184800c0b0362541d0510810f03004100b45400e28108114160039144041c000500107000030030309004100c810f0115070110704102e42000e181a0030030003c10408081f1b84210300440a031380c03645180e91f901031803143c0f503001d52141085584090413a03141d4080e800c0580e4003e1700903e400500c894440b000d100716980400b0040506050382c01c544500d218104010314018100407850003251000002c030a11080345800c507440c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 559466267 1250 559465017 559465021
    0xe100512011509092f090c090d1121030306150405040e071a070f02060307020a05010e0f10060f0b0c0f0607050d0b01080609070f09171e06101e120b 65
    0x5117200201c09802400f52403406140c2400c0c10040a110566510241c03822801c903070311003045e0300d40307130080c44181b80d04035070400c0700c540030889001c4200702c10300800c507031900f03042d41450003811110742c5440c05141294420404951031f4580003012003000500251054909501c9074041001c2e02c3d550416550a40c2c80b00e42c090022024140742c42000c00c0d04c07e4449400c1c44d0302612500c1c02d0200000c07019014410002c08100084c3c4203000070012a03400100074880f41610308200ca9030f48000c00c5000319036029160048074012000d0084004580811014204c414109144074106e90320455080c0454482d00030500400c82c010f01580b449100c1036162180c403200d0803a00312007078928200950b030400c80741c0000c100e10b682e01c500303500d90080014030300b0f000c504000500c20780d24050300d03400c08049080c00401412a6040c0040c0400c51304110b007d1403c03490090004d000e95810007520b05540c0c2c041105030901440e00d82910701c010131807503100725220041e640c400c4007461508001c2d05842c01040081 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 559467517 1250 559466267 559466273
    0xc0f110406030f0501230c030f060607050610050306010515041703160c060806060715050a150308040306060f0807030f05030f0a1d0a052211040e040303060e10051201150909 76
    0x1100b010b210346e5605a20b141d031402a05401c43c80c40b00400000418500c1701c0411041d0f190f0380c013a16003056100d000c0700c9440c20800d241054800c014803c95119124000c00400c0034240000d10401d0342c10768010703150500b4101113020041c0e80c100101d8810740c1c401400820342c0d13110440341e02e61000e40241e4803030100034100700c0003c00300300c8010015070168070b081003084001041c2400c9910320480b0741310300054503112442820060400c0380d105001d40b022218022007070007480d10040088078441d0208002d00c0f0380d1201108202819885401002d4108103410004504060a050000fa1040007624600300f2040b11070622504040030407400079000400752003040760030008039440c03d141190f00d10091840d00001849582c3c041080ac8090050000d2000711403e40742c014110020841aa55803141d480c0c000c50040701200319801d6000070300308140024001070380017007540034803591044010518140001d0154612034003600324800d40d07030740204600202c00d11105401500030014082410000c1d81 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 559468767 1250 559467517 559467551
    0xf0619030e01090827150901080906010302011b061506050901020d1d130b040c0503100603060501020616021510050a0b040b030a090201050705010c030f0c0c0f110406030f0501 77
    0x40d540300701580c58040c050010a8143c03017034036a00d030580021040390800c8200c09101e8018011052508808200e20320ba10f40407066010701a410003c0c0e07540e1480d559444075042c0c1e034000070f00c03010b800710341980ca5442040c20101c0c1c4550105e40039050200c2c034954411f6019444980c590b010900061000c54039220701c1da410711250b0100d0f0500e1500e180e0350f04040741d42030100703081a02c4036032103001c4001d002e03000d1004940055510520040c001c00410300d004402030038540c421100000e2152141001040c04c6019118803400e64006078001e0104d555031400004000000140344025841a6a600e561100410041c944518100024a00f46a15180c01e0141009003500615541402800180000750b010400e6035801214001c01054111050005840c18420490007a203154240501c03450743c0b903051381001a0f0b80741d0b1407204100b0215005803c4540707088050b4000e20071109070300f041c404510304040d581d040c108010000150255a9134940c21000e440500898099464000480b03d0308504c4d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 559470017 1250 559468767 559468781
    0x70306140603011e0e01060306060e0106031503080a0e0a0909150e03090d150908180a0603020a020d030c14210a0c0909020309120409020309010b190e060f061903 71
    0x2503009000041d203405800b00c41c40c4101c1130110810f5076940303442c1c2c0400c500750400f40040d60803000810007503464042c7d1290003e424000d10011a04004034080c4540d40003a0302d10840303810022584c00d08001020403030b07400d40b0510386107500038000030020840300102e00c10350300803511421400707003000301c020001d00640d8145a448074294109101d01c05107074450b03074400900c0d564084074502c0b10310030380d40901c0300404d58210054041c6401184a4031216035230036965514100448440e02e43c9035443c0000c0301680f06007100e600040e004803114045d43c074025000348003e0381317540c10065a40d40c15407030007901d139401c14488681701e8400d0100110501c01800916034024002940a2060104185015020340314a21541c13550650001c0001d020b55020311849111662516880741d5807540c40007200040d40041c1c85c0d49901d5407920054446a10700003130150725082460880c140c540b440d001c0079403004100144002d07045051030041c2c0225603100300090140058070000c0c41151040040300604941c40b03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 559471267 1250 559470017 559470019
    0x8070f03030513090608010e011401081e0a05060f010906080313030209100b220503010b03030708030901020f19080601030b090c130b03040813170727110405030d0806240c0703061406 80
    0x200e840107024074040071800c05102411040c072030326468260209375141c40507018010307100c1d001e0038040c00f2031004044c4820f41242e0701d49209208180c0c481d8410350702c034825280c904292102202081005040060030f0940c01481203004403111980c80180703403070690203603004507450042c1d6412401681c0d075500865001d40000e130001c200c0c002c0c050317001c079580b0321030300340054125040480020400c10b401d404880c010a43e8020b1152a460103469110500c1007601c0c1460108444000191655110b8402c0c0d415203140100705c40d040703440301d10390302d40136070300206010701e80900341040841c0500c0c2c200c0003140203510503003005a82c2c40301c0610703d94505c1c246410101d41c01ea611814165807000018804080d200d1050303c9210b808403541e0414401a0501c141110050a1801868510302200d005c0c2c011184143c080d20390001010301d040300c00240c12603180c0e42c044100258010013804480010000100c4064030514058089401b103103041c1c010b500440340c071a141c00d5200c8070800305800240c2c01c000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 559472517 1250 559471267 559471301
    0x30619050640090501080c09150f0405010b090a0b0403030e06130302190305070603020717030403020c090114030c0f09070804110a1e08070f03030513090608010e01 72
    0x818500061403038030441c08000c5100c00e0b100e802c0ca402c940b030701c480706403091001c03661004840d40b00155030050450502c26290031610b4080001004600072800c0e0056002c0207001502d0341c2c4d03076aa0b02c40d41000c299181c8940115849513184c415490341d200c0c580c013800c03084003c143c0301c0c071800c03081004540d01c0d50011041c902c0e00380b10800010b0303004a14186102012034145884508100415070030550540c0007079400800d5001e0b0b04444481500d00e403040e6401501030310b00362520b4020543c1684600c2000900703503504001c0fa08210501c01014680040c400d1042c0d800140142d400940083c1080e040084040c55001e104005803a042200980d40603041e100f90b190729103504001200e03243c00910090601020b00009000c0280d0312403030b01441c43d00184021440c544400d2102910322100f00c40702d4100c0000500800e11217000119139048425403858903529904683d0101c94a030011035801c010300c48070810119140c001ea000346005000000000142d0064046409003036a911200409140c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 559473767 1250 559472517 559472519
    0x501061d1f050102060c0c0a080d0504020f0a0617090c1207080105010501032a1101110405010e0303040e011a04051806131a01030e030c0604060e060106080f0a1e090602030619 77
    0x42d07004035925612045a46d02d650311206850215800d200d01c00000504046001520003940562940998007807402907911154601c0e65409001e081d140b503014107400b040455014817803001e141400c141e841440b407801d440501d1001004a080e042c5006402c1156070000d0000b031141c580248162801080c0c00d01e0103001d0400d01c1000108220405a4214050344030701b0030700501c09008851103512007620000820101c0d5540e15601c035281c1143c010240040d0b50b111015400c1e28000042e9801d41e40010603a24003a445c2004146614080700e0349401c046100b0b200000b42551b400002c1d00d503400040345039124a2822a040210413011120070100d080d00e440e80002107042e21031121000c50b070b03081c00d002800d0028801071a1031402145804022485544100b10410105400818490f09018200e0782c440e40c94000c00c2e00d810108403840991040281c0004e0014642e50704548071420a201079101e14001c081044400e5030040c2ca016a4155000020300000382002c48851184c10440f00d13980700c582d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 559475017 1250 559473767 559473769
    0xb0d12080a1b0507050309090a02220302030c092a07120305151014040807030b060909031905070f0501061701021e0310050a030f02040b0f011b0501061d1f05 69
    0x400b00400c440420814007250b03800070040c040007102d40d1800010b02d080c04a140150000000c4c2d444150000265005010451a85940d50b07000c1003d680c0d0080c041c050342000301060042081004040181d0352030f11a4250806220b10081500250381c800119076403000c860920300e0144049144900c2018613000c10080000d69420035002010801c4270300c0f030001040248101e542c00c40101c0340840c40f80e0001000503500b000058080301703d0f841413403a940ca03951403000b088903050007210800b02d59001000040480c55054180c04801f14540c01c02070b05003802070701c41b014008418101111282e5613404280015410601c0704246441301c00000d41c541642003e640c2e082d02c50070300c4452050310010010442c07a503040d0302200050a40580ba25401c960790782400c486035081c1000a174001d9240c86035002050510003a4920462010303100c00a01c0100d01c070311814080b0740420b0540e41d555986502007820b111a1003e00300380c6a81032842a400c0c01c101d1060748540300049504811001502810032036 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 559476267 1250 559475017 559475051
    0x60804020105160305040503030c0f010c0504180504080409050a020c061f06110a06090b0a0b040b09040803182a04020a14031003020d0f061401180b01030b0d12080a 72
    0x207401d483d074409030203601189815100303401a078100ca0f9050001041c00900d007540010301240310000b600c028811031008503001e0352144200d0081f01c090921105150305003a80b01d802554005208402c5145010343d2429030408881c0c083c8c58500d9440c2e0001400340004500b0403409401400c403140300c4666032041c0b21840c400c1400c1d44903241c1030003039031190381c0d089440500c88000580d4005100303100e0081c181c0b030600a0301c0340489a00c00380c0c500d0904000c4c2035003000c1c490b80450b074501400c0301c0503503221502c50410303e80000345180d00c0307078508101c51059940c05100b601407008000700c08030504c00f070345034407400f802c486c4090710b83c011072041c00004134842c0e00c038042c42d400b88000500725036252030701040c1604a10060300f01035017080340a400c50041120401101c50000d0080300200460010f800710036061880a129008000540c804d400300d16244e10340c07140b1300340f4105042c001241d41222000c210680242a4140d8a4030340000c4d01c1108103401c5400380d41d00400d040c0013001000d8003001d041907 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 559477517 1250 559476267 559476277
    0x4052805062d090c040609140a03060e10111809060a050906010c050a0503030106090801020a0c170705011a090f0103050a03180b0d0f240b0c01180302030a0207060804020105 76
    0x40049500702c4001070b04058001008210140640452603500c0c110380c40c9005540702c0c0c4500380008250900c0090715000000340b100c4003010051941d150b503031460321018050002044050458007a25000011700c00da035119041350344a01416903904c822071441d040c4400240c22091901400d0101304014072035403028000c905840f001c8a000880d91280c000488080012500007031a030300c2802c5501e42404000000755040358040d6a644900c6c50300d4010003070a0f4020001c1a00c0401e0107040c40c500041c58456100e5281190400f0700b41c1000185e8a481c0d0a40300d41600c4400703409044940a0001d06210030803503405200c4040303075429545540e68aaaa1700001440601004040943d44285220b402c0c1c02000402d80445440d454400d46010880184010681c580e216450241851a14400d4034500d00701e4404041400c6803550dd0040701e418a6480700c401c292a5558850b17801d0140d40e10710012090960099000355124400300001900d002c0c2d040e081501400314200405c80143e0384102150303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 559478767 1250 559477517 559477549
    0xd02150a05070903140610060c030804031220070b06010503090a1104021b1f1109090907090203070c1a0c0307050a020a02033309030304080c0c0405280506 68
    0x94199a101d0040380c100d400b9800080c90741485c0c5170031139a54175000903094026240070348222001580c036502035902c00403100c80140403520580009010034000d0103154200007884002049183c1000b0502d840c50680c44100310f04000d002c64520140103491045951104080c00c0c12442d5080100560f584d425031080001c150f1840c0070340049040d25142c040c0d0389008800c2c000c81041c03400e11030b031481c0c0f10103040a900101c10740c074406004061540f07000f80381810403088080362618403107400f8441d80a034020100f00c1da51040c0240002d00e10890301c0218412101913a506501c2400340c900810366444400612006090708018442500f42100842c0e40011f0715041903645c0d949800c405a041044041c0f010398180507203500710790887c03450851240700705102102185083c030101031401c0120800d0b2445c280310f074024800200042e01c600b00410b07010980b40c0450b5101d28000e000030782600c3c0100c440c502050015001d03100041001d1100da10505140341c1d003480341d443e05501062907c4100310000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 559480017 1250 559478767 559478771
    0x5010f050a031203060e0103060c02061e010603150807060e1302180f0414010303030617010e072706080a03090503031602040b04020d06090930030903050412140d02150a 74
    0x1e07030f90150003544500c00800d06100720107055030f92400c03c40010901e5610020240c0600ba00103035440440c6480e000600d800b00030b411030b590742402d80840003400c0300a040030358000407050220b1980c40c02c0190000070000ca80c2c5510074810750380306022408022880071802180180100c0303000c001102d808402e903440a4515814105000c1d0009001d00221048100c070030300f0701c1001105050341030f0000e00503545800c103914020b548012a050032151403290788800c5411540050051191018480522003d10383c02032946082c0a183c640448a8a0f4010034442c1c4c002d040ca9000c01d50404800c0c001000100d0281d81031420103a4050241c15644a00074132482c3c1e22100052107568690550724840300c02101040801d4031010404021306840809036000030303031000028486a0b0308040d80e114810554038401031075050a0058000d0200c3c000d04909104d803d02000c44c42c007500c202c0c0460f8135802200200b800c40e0044a89a09101505080c2001c542083d03041c0b07080041c2400e80345401c00041540 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 559481267 1250 559480017 559480043
    0x209010302041d0103022d0603070201110409050609100608070e2803150213170307020409050a0b090609071e08060c0d0c2a0606030c08030d05010f050a03 68
    0x128001c2c8201c0e0800c00010301400141512007055894160682e8030a450b4680707001004000c4a51078000001d441c80704000b600550040d0b418004007a41d0881030074000801d41c40d485e400b42600940154100030155a611004c0200c145066601076800035958650f204105042a00c0204403020060110080c001051244100c50702c95522400f0803058140c4800c0d001c8a482c210000d102800348010780e442c0c8651084500380c424103100300c1b02220010700c0f60344840c52034200c442d403907148250107075109800284130f03801c090788440c092100c040303102e500901900c800c60728007282601c0014000044660243c2d0801003000e2000482d10700b5900c264000100300e189802821050b050107800c941c400380111028010348140e01d8014242d90000c004c41400220404c010480709448429401015451142c00c0120355880700c516403020a0b005440105a00b500c80e10786c0c43c9102040d0340805143e52001681650081d094400c0c00e0242c4107541c041c0c074200b850400020b100c91018000540882c0074000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 559482517 1250 559481267 559481269
    0x603090a030e01031112040312020f0406030501360f050f0610022a044d09010e06120f070207050d08030a230106020309011e0903140a05060f0702150412030209 70
    0x101d200f000b6040d0400039903980d2f42c00c0034180d005810038410100402d04280000c170f5a00c0b44a001c540d80c5110910304014942d00d90400302c8181a4110340242d04e681c0e40b06540c1d10142068002c0030312407040c040d802d90603070504200303101604502c91596002c5400103e020440325500311246d9013070501c3c0308040020650038200150051012510089050030300040020326100e40c0003450b003c132852407120809080c482c58624061100015a5011070042040800b8a03580120410000d070300003d8640740c04c1410640843c056400d0540d04003103410044810084421ba0410644025103010360340c2d0082c03000c2e2641c039020311b80006400720800380c0c0c854000050f502520908500075a02c038000030304280d42d54141c003070745030391140c0001400110a110308070126101d4a5401449001035a11404400e1a40d1a00d104410049000710034601480708000049101002b00e14001c1c24108101d6650341000d16001e4030701035914102c4098840d0600400010a0b04c0802420b00c1c07488904016a136028154 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 559483767 1250 559482517 559482527
    0x130e0c160605040210050418020d140901092109090b040207051608010f05060d1401110a09050a060c0f08210f090705010503060d080f04050603090a030e010311120403 73
    0x4003668030200c0030342441009004180e005280100d0080d11460103c4c0104081140d4612039405000b07001464070080240b251050390003404948800300c1e00044000ca001d90a13100805c0c107070f4068985039150581d05092106108010381d00148000e096401d40b182600054800e44140c45040390507940c079140c2d01c2d110344540d0100c4918030703401415105100c010400c0c10744240114003c113001586485000003100340f1038441e07079004d00e20090214282d013401c1da5407451042c0510301482c40075502c400c6030703c00169912020b069000131a80b01e00c14440d00b0301080c004c500940b58030000400185024490120700f00c011018640380c4c2003400c450b52120341c02c00c405101c80c14003040300c90362545542040000303c221404180110045810f07a000c0385d2703542e401103406000c20740f01300b580700d20f840d0155000100d02c0401030202d201041001070425940740c0000d18560000c0702c11030a0f0340c0040ca080420542d00824002c44d0042c2420201700c0d443e015174010302c40e03001d0728043c200f80c4025040440c0a0501030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 559485017 1250 559483767 559483777
    0x507051c110910123c110d0209180105061210050a1401020c1801090e0c031009021201140408090d021905031e061506072114130e0c 58
    0x10f8001000d0107041c01000308000105aa4480c8079864682075096800400e03640030401d031002c0705601216010400c1d0318102e156190014080075544445000c0700361540000350a0a070b0b140007005031208070040611101b68100c80c20603280144a000520039030f6244803d64021a40c83c40c0c01003aa40d540041981c0c0c82c80c0f940d001580d002c1400d04e4002410350300202145444070742039098a0004800307009114078058207201484001c80c100c8010700094045074840f200a81e078807022201c8041041300400d007003005814181001a40320f4181c501507040402c4201c00b4000c001d4020840000b070201851407040c000b0344010300141000801510700d60703860f081c10662079002003400742014819440a40c80003618844c060007402903041007020a064282010005000140603201310b582c1c00209120072451070040d203502035010300144c0c1c049090010a02d80070502c502180c207003507581001c003801c21085850350512001c82080214030010200708907600700d031400d41104041d07444d002d01c042c0550183c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 559486267 1250 559485017 559485019
    0x83403080f0d18120311090904050a0302010c0f050306130b04140f1e060d0314040603020d060e01060e01080603010b130b0f0d0803040b070516150507051c1109 70
    0x22a10890201e544401400c2c1400c004408000e0030084550420301d21804070405801250f1060011030041c0c000d41201003030750000620750f441c0505c1c10000483c1e500e000c1c4c4081e901d41d1300c104034000400d03809101e000d01a0b800b5041002c0d101c081b28030010b00768400141034601076500440141620f07010340e0052b01a24000400a021201041151a9441c0703412a00b04507540c80d420045800d451015980c520b584501107034012050380e540d03040c00030344446910218104208040000e0030300d50782c0c1016101038549560007507a00d41c40da90140b0250f172140d40240307100b84050070040101540164220107513010a00b40042a035a40c43c2c0068010a0a8100c0c9500250200c4001c1c1c902c407d107900401705a04212440c03103d4100c04d01c24048a582d50000c01403414904101250100d00d545e12901e0707002c04246800c91804074030810708044c4150703c0204882c0c807010000000dd00140d03500825901406918109043c244280000100c81c095607114146250382d51980d09200d014810031a080028 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 559487517 1250 559486267 559486283
    0x112020d060e030a0e010305070504060302130302061605010507091d0916081f050105060909090c0303070602041d16031a04061403210702011d0904110a083403 70
    0x50141e0304242c513584000c18010015103820556086580a4800e607401402c07180c1d00d4a083c14280b110550095004101800c5800b4004100200681c0c880004002c000d41440014000e500036241c042d00703403180074050b2800e0107002482400482808201e0841840780b890681e0302e9030310345160150510401500844c0390352955107020488500004264240d1480005030540751040645a07400b114428061254047c90801c10000640b03041c098807a0000c1501c0b058800300500d0307000084ca0b650080030221189030300801d003000041003c5180905080d08010420910315040055102c1025918021402e1507134954071540f02941040f40701600c0b1101400c2041160345901c1c1c007115070446c211909209108a0100704418010120343c200c41c00080c00040f428285035600640304002d01d420128042050302c0003d0032269500e0300e0300b90049000d41d0081402074280c80c1840340c1c09500e50055001903206d0412500400340060b004c00e01680480180c440030b6414648403003409180e5170002d88014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 559488767 1250 559487517 559487531
    0x130f0e0f07050d20040f0902030c030403051318050103060b030307150c1103030f0414030705070626130201020106080c030c0913080403151505130b01110106030506061201140112020d06 81
    0x5026a0000d0040d01c10402c1901b1980da80e5a9031035040c1c0c0f100b1104025840421700100d00001d005001405041803804078030006c05031201507140b01d207041c50011401c001c5c2c0f50303c010414000383e07100350021000c0540285141c0740345500c0705500500d48180e242245940d075280c02c070b11140f0985030341c2d00384554203007031380c1e502c1c1884000004c404005540a80c5c00941d901c2a41990806c00811a143c8a40c000c0c0500f44940c50881c06864403072143c1c403107180900001604811504421800611031803000d4000414118107000090848400f60040601a48a01d07803094181d81c00180d0501426401c482d541d00d142c0e20548155800c05509000a103040004100841001710265000c00484a200b504229030411062581056103281c8030f1541c1008501c001084d40c840b164105000551041c10100e0714441c044451500f15407440d0710030395064002501703200c9540b4004c0c51114482c1c0317080000388080300d0142c4014044450610a2a6108090b00b021204640b1403885d0020102e40001081220f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 559490017 1250 559488767 559488821
    0x111306060c050d020a0309090c09091b17060a05090c0c030a090311100c0809151318020403051f111314010201110910030e0102130f0e0f07050d 63
    0x81c00080350807222406034410318002141300148443e00d85815580302c510607454400488c00030802007440408000018902040800c42d500a8106116000c400c048940d18012001080003208150000d2000704c54028888070340e0701c8480c880181d036021a0607007941d40326102c48000314404c1d60600e14181c04013264126040e9004110703c008c890198860210004c11101080465031581802002142420303103030a0200300144064000c008000d4000c481081e50240d12040c503801c0100c10000700007140038140100d840e00c04805201400001c2c1c19414241542c2e02e09071280e000fa144d5031014880310007001d00c086c2c1c954000002091090b000155243d80f40c01c071340c13420107490b4000c0c48804130000402044651051061003024100e64402d2814010501304000c0e0600343c0e29007881c101600c0d10f10003e2100001c1c40201582081d40214003050f40c60009a4448003045501c521510646035041102407111036405643c800d2092601c1035542002c444020000c00280a00401128900b0004049 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 559491267 1250 559490017 559490027
    0x10f2a11090109180b271f0608070605030c070807060501090605010c111c08030f010807080d0507030e01051204030c05250e0601050415091e060c11130606 68
    0x80341409503081c500582e2691200000d03949551204001490318580c44400304499401040c1c1207889441504603540180c510445007000c80704156a40ba00a0003220f0072020104291621b1541c00c448180701080c40c0c030035869118204d5200d2141440300010000d40c840b552a402c8070b450a910441464441c034041c180356004150901a04808615052005c04c65600802e51207070781c2584842c00c0b0074091405821300c9907060220801901e85a4881d003100002000c01028505c0b825401004081030b40c034106049240c646940c0c802c1b01580c001045a1040c0395021742141c0c0b0803a01030a00c0010b003594280121030500c91980380c001240c9092081c08100b640c000e402c031405c0b0303001d1000c0b600300980340203a101c403101c0d42c05140103005409600401001904001c00d603400300301410400d0074541c1e503d000b50600b1241404600c0062403011052046513900340d00315045000403510711013407604181010300060000107025092030b000c04184403d90303440e045181c00c250b07520101449002d07518240946 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 559492517 1250 559491267 559491293
    0xf2d06050105060421020103020f0703022a0901090c0e06120901050c0c071a07050115031401091707060f0c030f0b0316120302100c051b0c010f2a 64
    0x485038108030001900349890404c1c0d0b0152611900c017410055281003074034881000801c001c905042d02404101c841074095809005440d020740c014200c030005588a8065403819440814215002c116413140c03552035500c80c1c0c9055900f4810300107051950044265064409c03c1c9140d5032002d80080c150281000b840030140c010a0701000a004a45689040d0301c8280144a0f14003415404184200140d110980020020408800d00a403411005458050075544850141b00c45200400070800c1000007a402076102e0068400003041a004599030744000240b0307900c5580341c064030103e03150041c46596480102024100e0000b001561540c0401402510580030308031090b0f481d00c9101c0340c40d8140801c01400d2000000b20b00c030182401c0102c01048882c010100760110300c9004903034180c0d141d2503c250a000b075016120030343c40b000030340c40403118112035807110b41040e0007520050030b55980005020044000078140f04603001641e0b0058504405a46141110074024000380e4041c019404c802c0d132 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 559493767 1250 559492517 559492523
    0x30a140115021608250f120210030c050904050414010912020d0c020a05011b0b010e040221210f040f0501110d08010506090f0405160305060103180f2d 66
    0x2a48419521240041101281c800c0d038102d0341104401c04c50142c078550b0f40d0a80c248240010b204403a0300d840c404c074105541900500207d0300f040d400d070819458421980d4494114030302d0f0500c04a482200f0040c640e0062241c814055521000441e04000c003040c2034004020810000700000300301400c0c00c2101c4881e8034582c401500607000425031035031051a0540c006e54000d091402d05516210046800b95038040a80c014900d21000c800009010400d0b40f40c000c0003070064104031414603004001420070ba6200b6000f000c944984244190341d80400c0c0c445001e40c4c403169444803030b990300b510a03489210b003c0e200c1c44840000a0003040141c0d110b45220280c404c203a8803100c8801c0340074400c2ea41d445000075008081506e070301c01040a031410000400c081000501810568543d020100d07081e10707419101d04800199110158000a91500c2050740c4114240b0741840a0540340c041001c045200004c09000e1011840980c2c1c244200d52507540401e081601b5584ea0701d01c00303100480c4102c60041011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 559495017 1250 559493767 559493773
    0x714070504110f0301150903020d0f0209010504060321120c02010518061902090f12011d030a140d020705070803040806010603110d0b0d060c09050f0409030c0206030a14011502 77
    0x20050041850040d92030030f2800c441d683d85580d092459005601d958051900308100440307d010005031587c00e04d072120329204503510850500d1920400141c50070580019010714600903041010a4008084c107a084482c0c50803485843d6000d4001c645070081c20b074070184414109603041d8127240e415400b140c481d014545030700001107142d00a0f640c480c001556006d02003194a0103154599400e68000c0c41c3d4064002d142b9414100e0700303400703d10b02030b202c0700400d24143d6541d408086101450500b1580d4040c88030003840c58220245005441101494490790300740401080b580a0058581e04840703000d6002001c50f1111540c0319640c0c2e07960352003400344034424021440001906800fa0085207010b9032102400f40c01c20703150500c081c001b0070b241d184180c0e01000358500000882ca0700d21450300100300d2569101c2501d4104020f00108850b015207a9000328602401c0d4004264804000c610701541212007035920f03101d0801b89005403110100d0550300b22481d0000090000320b64024002e00390307881e029 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 559496267 1250 559495017 559495031
    0x2011d03070507050d0c030b2a120702460c2303151312081008060c1b070312030c0f020f10020c01020c06040609020307080a030c0f02060714070504 65
    0x180000505882c00c010429569407906000250f4860a23403030f440308060071100c88145039990803552601c4041c0c40e0f40c2c1d401c14001110301401c0106412254403180c01d000418142640200030b036500c50420b80200c81d60000002c88049048117103003010300312121060000003003641401c058441c41050b01c1480c4d51503625803450550701d007102141e18401040200500a41da100d10034060324480c0082241103c004544072042c00076455200014442c0c20943d1f070501c4600e01034034a04080c038410f40001d281a8004801c0000c188140e40440c0c204800500349009008140386c90b00e4074001007908000e1407a1140c3c5410784005070700d0350140802c40e59650340c1d800040790580d81640c540c0c130394440c07034211504421508a10500150024000e05c1050700005140c40030350500d45040c4441540c040390803035182c502e1041035150411440002d00600400340c801c2c000d0560700130b00141041880140346078907031030341c5034195602c1100307840d000d070380015102c4440f842480d145600d40a060103403074030613450164 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 559497517 1250 559496267 559496269
    0x18120615051e210609010507201207061103090a031805010206061905030a050c03070b1c0c03150b0325021005060f060c030706200702040b0102011d0307050705 70
    0x511a00d01a4006105020a0941c0140200c10116102e400d0000072400d115680541007003005900c11a01075000007002c0c1400d41d2300030a0741240288140e04040c1003121084030000c085103c00c1103058480e4242d98500362441d00780058414170385100514140071040083c400d40108905017018481d595101404030744100301d842610007400f60500592250303001441a00b1302a5503420001403c1017055411039845001a1510401d807100320740700d410400c180f42d110f0800b0007840016103204000306090201c180503c01c01c5408482424003000c1e266841d00c0207550203a4030002074181ca0b999a5841c82c3d03160a4103000035802980c0084040f9010055240741c0038901d049440c46150756405000740344010707400305c40a840302421031544280c0006075180d03666075400040030b441410101950325552507007050800c540c14410340006071f081540f101c0c01d00400381c2c1c007101c40c1660304840c0020030403080d20040b40141903045411030901500005410049000400b5044041c81841180c180d180c40d10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 559498767 1250 559497517 559497529
    0x9150708070e011b0809150a030b0f090112020607031815021509071406190c050f06010f050105031e250c080304061808070303090c060f0f1812061505 66
    0x4207004a1a944559400001803407401c02032540d000011300c401042c4018804001465121012100c02700c0d941e0345040e41e8a0400400ca001010390450b1000074075890107203200c0543d01c1000300207100c0e40e00050040101070194a402c00c055840c1002c100c0120b031602d4001008661203990f443c0036200f45c251503071a545440020510501c60300b0044c2c1007c904d0020441d0f01d0902d0074660b103a0048041c01940452050400b6111130020156a00b503c9038110b802c000342001c0080d607014009821100061083d074560500c3c2000701c1d1828a0403507901e46d10b084c2da40b412160503003000500201c0e500b090242d0482e41010403092034511181450001a80301010f46546040b00c1d03004105030020301c0001d01140792a4400354403809072000304100050942d46140c1a540071002c11000b283d5210101405d002c1800c1501014111038100840045172010300509140c060903410000c0083c0d00e4450b800944d40d0070408001014010180702c2c514000303240c004042d05404110014100e41a00001294507046c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 559500017 1250 559498767 559498787
    0x300803062206061403100510020708010e070e0c0a020607080c0706093c020f0604050904031110050f0a09020a0f090609051b0706200403060903090806060a0e09150708070e01 76
    0x108444046c030306c1c113010701810f100d0350070140c401e42c011903a0005d0088003c0c05040e904105c00409000181d0918010f04002a0301603d07005c14030006100c844042d0f03400082064203c401030410b680d041d5100741c608141881107450040c00c0600300040e01b810000c501c0841d4201e41c401c0d000d402404440a0503258a400c8a01185140320141e0b03010900503052060035101d010801a20841c50180c40d00c1c00302e41e03001d0082e101100015081519003440440070f00603540b030349150030000c0c04182001d10180116201c041c020144050742d80c00104210758034680c06400515500025260040e5034190030340c02440c50b0300c90303103800d14184030015024200d42084411021818102c0c50f04090240c2c4038470740105803d00c0c642c400c0312100c0b143d0540d0760724000c02502c01184600d0010800100910b0000e02104013a88101000e601070303000d000207a0303501403c0b00d0503203c60f024007080b503544e00d540040c508440c050a170720080044805000350950b0205046200d00095226024007003001001141e0003800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 559501267 1250 559500017 559500031
    0xf120621060421200a05030313120c020d02060c0a150b0103061e03080c0709020f0703301e0507030c2d031d011401300803062206061403 60
    0x39010084001201d00d100d007240c9000007904440d0262100d031b8038980f56034801ea58001040003540d076090100070022038501e0000301586400c01540c0410740c04500c60306840031000b407103150003245003503909104001c05013a903138102081c800920f443c00c0451004000b1440b00303274000303810705a011402640d140f40400394010f40c1130f02c480c081407a540b40c0c1300f0302d03800141d0380c000e19004e0304c031000407440391a001404002e00c0d41c200d00c607078800141c42c001d401400703a826030f444030085400d0f5a0072801254034018250103880d00c0007180c0c2168004255969010380b00d0310801c501e1038103051050242c0c0c107900c6914100c6081c0c4502c4002c038401408003200c0d0b103030120711050001d550001103100c9841380c2c015010300000c0803400e4000c0301804c0354090a4418200415644c110034600401c444901d180c4490303161102811204850210101e1a42d2140352014010304070110000105002d0745170104a8405401c0c2c00030484801500241c4410290801d80308640000d010140f00c501c101d1400002c407805441 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 559502517 1250 559501267 559501277
    0x80307020609030715020c0918060c0a050702031f110313120905130e100e0703020f0105040513020703080c1614030f0c010204090f020f120621060421 66
    0x1955400c0241941c07101d0107254040c01008800030707031240c0b080310300c21001020345c025007480707203d903000e000000f4030040a05540070501906410300d0800407400b02d0300301e0524060309564000e0418280c40512030050003d4041c82484001c00800c40100c09070400f0003250002800707480e19522902c0154002901c110a04c0d031140b03000500000c820500101d4948405d041c000d803000e903200000f44c00c008183d0a24543d1540f200119254148188072124951011500030000d500302601c040e0382e6502e041c00f00030f0040f4890f1000c08002da0051b400c1d0b03001084010001200b045c150702c1c05030042e4110708c0c802c4001c00d400c0004100c000000b2400e481c000a000d050710013044030243c40d400328901c4074804006d10f41c00104240e004090f014401016480ea0941c0003594543c54500e00300101c0d203501005034001c0d8418080780080000c81411500320380390050100d082500c0c1c0d00006020200b01c100916160040e20904a1708010b0101d1014807460140105d45080c004800c054840c20042000d1900010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 559503767 1250 559502517 559502527
    0x203100606050a11010b09040f2f060c10051602070815040b04060f050c12090a0b180c030706090302130621061805010902030f0f030f0d021318060f0803 67
    0x6210700d004c8005014480004900d04142070302080010b042910152416078002c94603006121903944030480131145d03000c1c620882280801808008483c2c40c600d240706400000d081e204440003040344824080c461030303082085080421200900705020713500c000144c0500c80380010041408209011780c002c400007505030a54843c0d813140b407943c0c001031040b900d5903907955000360885224407410344941c0034000071690b030b403803680340301d44103050000d2001c20b0a0b400089028006145110a240c00c101c105d0446041c445580d401d1500f4076014403201030705031048000028049a0080120084a0084d06e003041c2c1040510912000c1d80e07510301500c22004043c227444001c0c41c5403407070b501200c18007520001031490341035084048401203980f82920960744400203042035103010f000341600d2001c11401040340c0300203d801c1a0f01c80c001c00010030346108011407504d03503482c903580489058080748000c01c44003984868071641e0b400b805018010002d0b2424002003203038241c4447c010b0a481c1c0741e00065046c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 559505017 1250 559503767 559503787
    0x61106011404020c1006080c120d0c170f030f0606031308090604091406010212030919032f07060201020702060306091312050d29010c03141204020310060605 69
    0x509850342049400030f030b00700855240d4500c1444105e00c0180904c2c0003103102d61500600d246444050500d00d88036031159812a0640c8600240070420f1701c1e4a4101090b140f10107040c041020380001c08024803a0400107280c44e10100b101c8001d502c00c581c0a00283c0094690310240030303042c0005c40ea85405031403003200e21804a9140c202400104d20001d000c03518181d00d400500041c0c1d099415102c1102191600707000c0d01d5038052044148a281d080c41c528294a071001c401552000440c0c913070801e26007130201540a01d480b82c0d0541002c040c0300e61290b14141000600c05200c41c05030b0540c51014003911001044440c418020bc9901c42d40040000b0306503200e040400c00300c6840948003551003600702124800094011014466201c156125a40c9450440c00c90307000351038040031003a409516801030741c4521400308103103140c010f00a10342800070850602e42515100c502c03c00b00740d101036020039880780780d1350540c480301c6c030940c4203400755468861126041801da4116010300c0002c44d40c00e000230001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 559506267 1250 559505017 559505039
    0x3053102010818010f020c0111030c07170f0c1507180303030b040f091214040f0303050304020102010b040f060501120c020d08041a040c0303030b0a0509060607050709060b030105010906110601 84
    0x209a80906a40d221440d50a0f0396084810a0341441500b61300030030020240c4000b03108a900c41503030a03140f1448c61a04a100a00740c2c8504400241210003002040c140c3d00303005400d60b8003200415040980c1d602c1c40012950760b40b0b0801c890074020000d00000078805500c0341c0781036084e1082d00000b03044000d0031607500b074020b04803010b00c07181c100d5034808200384101d5490058682440c0141c01540c54080c1e180401001c0740c6440c8854484a40104010000708084e070007440c0450f501890507079202d4446100407030141c00c07681e40c060307070060400800f0f01070010960b001d002244e90980b204503280c1c0b0111000342c1500c1109440402603085800d01501b07050207650340560091080c0ca011200380344200114810000070380b026104250400814010160584903018442104440c6112401d1070301c0c0014400010042101e4000c03640400c82c001003140400a4001074602403a05000f00d40d12164000b000d40c209100d50740c0002e041060005040b4000d203101c1844a000d84080c02c03035a802c03c114062 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 559507517 1250 559506267 559506271
    0x603060f2a050a030e19080c0f0c0f090c120a0c030f050402060301450c1701061202160b0403081e0c030c07150c0e10020a1511040303030531020108 65
    0x415000d4450042c03206d01080301e140740c80030f108000c0680c0310b9603e0402c2d10700e070040c05400134121354819000c904050703680d040c054a00c000300715400b441c1e5548041c1c2008481c02904020389812020300248004407426420102030550f0340c1d80c0400820f4903011030034007661000d80f0040d410540400040c420004008207010041503807002c3d00c414415201d410b40c0c1203446809816860741c140003980c2209501c9401011113142e094a041c188498a01111441090b010300c200c1007440403045ca034811400698064641903456014141124500340c02d0030500d25108980c1180003500c20000110040c140a07502e580c42800746101017869541c44001c0f03101640094038002402d0428840000040c40e25014108070004400740400d0101d00c0b20b078040d04034248d5012403885090300e80c07a060561680010280f4259170441c4000249840100c40c5c01c00078030740c58044025810001802000303058254103c140201c44828426890810340d8804840480082010030461880d5110740d102540c41081195 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 559508767 1250 559507517 559507541
    0x40c0c020d1106160609050c01091d06031204080c03100504080313050313090912111f0e0604050619090b0103030f090e1501030501082803030603060f2a050a03 70
    0xf901d00400c420704010700c8002d4802c204c51245d1110004820040180083c1c4001d08080c2000c4001c0c5003440d00488100e040003142c40d914122040003d1007036641000940c81e018003400c2007683c2d40380c50302e03022500d03041c440e08018081d100304014196800d407070b803040512964004034403e045490301000c000180d104510f00b03498511007445074440484042044000074411981e0002c1c00703da66103052480407088100090a00000746040050f00c0e00100d8800d1500c01ca50740030071000c541c070030000c000410701110720711241d2068200700000c1000004086000d4010351070040d40c08030511440109964500d2401007441e940d00c0010400240128146c070280c21860030114211501d0b15202c054508080f81d20100d4800c40100102941d601445054058003020000e03200d032103066903003241c00148902244c00018000c04460b01418802d81c02a030207141d02200134020005c008600700098000f072013a10101902c020f055011107107681c40307090342c103064a0b02c0e01e41c1072049802041e802480468900 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 559510017 1250 559508767 559508779
    0x2040308040f06030506030105090c0d020316031202070807030c090504032106051806100e0102120d0b040f0c080f060303040f0b07232d0f0705040c0c020d11 69
    0x40001800c110180000c0c1c403800302607010315450081c000702907420103003031107011b40d140105006e8618130214030b00107802c1c3c0c19155402c80c0c18039032000c07900d81407050340c818078044200e01c804400c12010703071800b21500712943e017103620441d16003a030140c48807018800107000c100481020030031780d071064110540c071901034209140c00030b0924401c196181050328660110aa441d0000c3c481d0b46000e014020300082d0410450080b0728201002c42c0c1005650035203401401220040c0c0b41c0c10342c3c4200310102601c100d9017401625580c0b8905948054400b81141620860802024006d00c888c00e00c0364440c45490340c0d0340d5001940307410a8012910348080e21241e090301007080080740000da645000c1d03009014005400da036070f00300c60501103401c01d4a4002c01c1c0505034002e80344c08810340d001071451140050300031004044903400304401003000510107080403d002d411a095110000407501c50102c40080e981807101000c40d200c2280d64580018000350301605001005000c078503228100300141c04083c1c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 559511267 1250 559510017 559510019
    0x601091a0d050c270105040e0c06040e010f1502030307032004030503031e0103150209031006330f03090c09090b01031103030412081305060a0216170a12030204 70
    0x41001c450603014140c5890b8842821021075080403001d684004c01890350350280c90f80350a8826424040600c80c8130303c1251550091040c402c0c00780702030003090400a0074140e8950b62441c5124420f9824402c45510395000c50001607407901101940e4042405980030b1450355880707500a80c000e04c0400c040724010401e410301280b80d041c01c00028070243d8040c20046803246484800315444000742c0000c01085105180100300068909240fa403100c880303c4c101684a050801c003081c50b0080c012403426056050142c0010700000c40706114a0300c805203280e101080c0c0c0c030006240c4002c8120421400003c0084540c1001c2c90320030303844514440d224500c84903040d5501c03400c4405845007048162200c880700340c010010040342c0e40c85c181c50f558043c2d0145040274503000628485840d10100909004000145045511a0303800e070500900001400b16031034a07541c1c41d000751b459640c854248890310710b00c0000300c1c0e403604080d584010704600030001c203025105591060052821301100c45c0901da003c0c44 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 559512517 1250 559511267 559511269
    0xd09030b100f060e040b12070b070809041103010602060a0903140d0e0f01060f0f0e010504050c07021809100b033d0b01031b1d01020703020312031e01080601091a 71
    0x60b09000506499580304010a0b062040104403882082075030302c241030aa8440e0004000403d003a401c0380c5084c25484d440f500300c1d04103c0c403984680401183c0c0946400d0301e140010310300c00c0c043d6060303502c9a800c80d4515624448030f80c08841c0704002c094041403c2c501c1c02c11b460468000101841e103c2964040350101c0c0d8401d00c3d07480c2100a41c010b0130984d440724020301c035001840f40714030b00030b20151708122079607032600c410140c020206000d410b000d1500c070800a1039610004045481080d03002c2e284049580f542d610a81d90700000387d0701c0d40198000da2000612280e20fa00031041203010090103400b500f0080107200c1410041c008100503403049409400d201d142e07440c2401640e00300d00000114a900c180400102100c0c503400c0e07100d800900e036500c02c040013688580b80c1c401c00103d8001c080700190301d0500523854601c096000a6051140c1d0304100540344191010f94040c2424074541100403114040c2c5051143c4240035000070b03540a400100700080b42c54200c0d0300802c8902454182588100c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 559513767 1250 559512517 559512539
    0x70314090f060912031603020408030c0706090506131403151005100306060e010e190b0d0510510212180112060b0714010c020d09030b10 60
    0x5a011400390440860401d0840040c00000d51280c105400303002c000c081304084241030f00024003500e000d046003034144541c40d4069030445020b40190421640c882002400d03030340d55010f49000390030000c0c42c2a00c0016043c1400f01c180c1d40c0c50003020880c0f490b82d5040003441038450b40020300d015810b201b409003402c002113001440c40d001e4006e1a0701c003030000c1d003050248a8200790404071401054500700040010f640d20003041c00d0154024640041d001d00840006901190080c4e00c03214841a41d42c0d0000700203c55400400120794190818422951250022429040540700d0040d070440c6000e0a104007880d04155440d122462910900c102074200102c03100c909507840100c03a41c40400f000000310550104032180c01018000c2004e45441d5181041070030b00000110800c1c180701a100b0504203100c0d850704024080d00e0410340658644050342442400401140200e000741e500e45501040300c43d00c0845d0b0300e8008a099140e0501c1907203541c0c1c0b81d034003000c002001040d06642403c03010074504008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 559515017 1250 559513767 559513771
    0x3010315051608010b03180d020102090f060f030609090109050303130506060d050c01030915050903120f01300210020610060903020a15050f0a1d040b0a0e070314 71
    0x15031002480108510202401c03a0809003482e010b8403100c00c0e00d00c40640d481002207040d80d546028168403501c2d15520b180303041c01c412120420340c5c007800d9444409580d0544c0a04101e02c011610300403503c100f07109105084c0700384c0041c05070040d42040003030424100340d001140c02a10000001410f601075440d0a411500142c8000340020000f031800800c2c01010080c7ca900303c3d0048900013802549a922952b407103c003600e0250505484400c0d40c014070880101e481d192100c102c50a109501d1f19040d84da49a03401440c908071580350500c040384036144468203803030580e800645410f4400307440b8240b0340b10b550000482d11144440001c201401a00c84030040030401c03545800804d11402c243c01e4000b290b1850750045010003d400c1e01c10000760750b44540300d0088511500c0d001c244402c0000003140d46116145410401d09800160540d06070341c8280346c0707014400c0c038010b1036403180403070340820003a54041480700d6400040e4000500c40c41400c4c0500c03c0c1c12011500b000101e40a60061400c072482007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 559516267 1250 559515017 559515023
    0x90f090203061503131211011506080f0112020d060906090f050f010207031205061804080a18060e120309120106050f1804140c210f010b060a0c021302030103 69
    0x7000380036060a069200100070301c0c01d100700702e043d46007440800d91070302091440901041a00303030340410200c0c0205d0400d41c04640d418001c0c80504d01b201103510890340741e846904006290361000469141d00b10040f40d051301c014244014503900150200040d10382112001e03030f0302c141d442100d1800078a080c4a031940c420701c1840c4821640d42d05040c401e080941c00c81c0d40e03038001c0c2d00400201000980c014010044061010b80000e0380780c480f05c010071408650341d103802e151000d144041c8810701c0203600c00b4000d5050107560748600c1010210740a20044030174440c05000c03441500314204903160103010211148034540440c0d0038064844009510901d92105050583c2d5403114107100038101240c0d80034001e081900c041e00c901c0c190300068408502c000344013400c02d01c40b010404201c1c00041c01140d482e000c00401c0d544004d20700030401d040300080420490828880c1c001810141d0070180104242c1d040001c1a250500005c04003d84090500ca24100d9000210504c681031100340791019501941c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 559517517 1250 559516267 559516271
    0x110604121e0c0312021c02031e091c03060e07051b03190e03010902090408070501090f0309060f08010510030f02041a0705061e15030a02090703150504061401030c090f09 74
    0x20b45824003800c500d030b0391508080c401d401040b420071800e0b0382c03003000409003241c0c034401030b620360711101002c10b003802111490788050000c500b0f111807110b0000e12910b44401050130001c65001085054084070814411400401c1c0014006401d560168010300303600e510040800081c41351005d2413604640c40075040100f54005002002e013125071216005074202d40650082211a440c0d40002d400000010030040030801b0000380c5800f004402c0d0042080640d2080040134501403a25011b0300400c0c103401a031001a10112503400c0003403060458074100c81024043c16810f00c0307140c104034003400181c0303c803120700341d004c100c0040e086131400b6009891100316004c590703d03402c051074034038140031010340311004401d40d196950045616103055107801c01d44001a6100740f030135510102e07090169144c0081c0d8408000e008202e0350a4050f0401c03d5641d0b420001610940e0300e5208001c00c8984a000c2d04c211035200d81070480095020b684aa408071205081c905840395403801c444641d40000d07040342010907 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 559518767 1250 559517517 559517537
    0xc17030a060801020414120f01060b0711031b2b060e010b01050717070f08130306050115020c100509030604050c040507050901120b040605101d01110604121e 69
    0x552407140300060000d1800a516080c1350031503085404000c03031107052164251070031845200b41e007009040b84d8059401c000740000c0740e44150949071a0040c00302540c03800c000ca1854002403401040c00304024510051000504034101c0c01e10001001c1c4d03044150351048046025400c0031002002201c07200c0c4198400304010751070005050030341d9520104d550500c40284030010014060209403841c8111015a0780d03210780890a100108000f494000b6000481c00900d0106160080580e142624060003040c00544d136601d806104e002c00b0811501e00580102c07059103c1c038901002e0b4440c4500142c40c0507403d0400342c200180c2040001c2e20201c0d855806000703208070700e00f054051650b02440d80d007042403c0158000c00a05002c2010882d107140039580da070700401c6035960b5804240503010140c03141040103110710000e0600b0390400220038203000c04683c5020303a50b01c42c204070300440303218801401c030944642c1e444040c100c00090174607080c400101040b0035802e01c00c00c0034402181d580d41d0380fa1416 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 559520017 1250 559518767 559518781
    0x7021506041811041b0f1116080145080717030702010e07030b010b0306040f020a0207050f0d0f0201120f0912080a0504051906090803040503071a0702070303050304030c1703 76
    0x321140074680205540715400c2c5e4000a0b00001c8218504855041c1622220b603c2e0013803a0418042d00c00e0345c80e1083ca1002c012a50a10542c409020700c000400c040d5401c0082c0c41c50280c1c8074910036000841070600080b03098061030811300c160b444d00d200e00006420200d1a994146202600a0185a80c00e41c04810080d08960900414501074000406010b545065407140c280c030001c140a00000076070000041445626036a021820020301c5240c04c5480c0e001d5854000e40721455885844d20a2410a1142c0c0192505609208203c0c2c1d01c009062507141540c0c0c01550700990041d40e030042d0680c2c1c1c0419040007400d40c00b0722120305102d200420301e101c0d00950060702001e03010700383c1010366181604100c006400010401c0c0544207184606100300c00070315082d009403040c10b00051052402005100c10064000080d142582c40ba49001c980d80200c6800e1203a6400b048031b64400691001c4800c00209000d1002550054003901d4080805152916081e0240b801e64185050300c0030f001040041d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 559521267 1250 559520017 559520021
    0x2130302131b1403060108090a0b07021c0e0f101209150609020c070e101806060f0f0203161401051614072003070f0e010501090605030702150604181104 67
    0x910400c0c00c00d01080303c0c81010480c00c034000200954140f020410204000b4a0100256a9106d9000c0e5101886e0310384804000d4a40840020300828000d00036260110315001d1400702c0381c50b800103058448a40c2e8081c00304551010046840000e10440f41e1140624003010300441c0081401041403003080808070700740d40102c4010740c0c00000b070207105204000501a02103060801c031802d030f00741c00c00342e42c840c140d6409005041e0380c48241d0060421030386d052400060b81003502100c01580314001d40701850300c030644100c81071030184c00050700300700124944160464003500f80c150042400c03010003207010008500b1030b0010740741d0b00a4845509070710790910341c2c0070b881d082e2090010100c00d4108041c5030740d822683d040402c9440c608245022000000c1c0d21704000101c018100c0070100003400d82d039014411181c41003030045500081e44905c1c0840e0081c026821240949110341c0100034802c0c600c94650208240500300b00d0344181c4481d0b191a041d088120175100c2c0c42e0203403005084c1c4c030104c0000c10003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 559522517 1250 559521267 559521311
    0x30303070207180b4509010e0601120b0a0605040c08040c0b1303060f090f201f0c03030b0306010b1b06040206190302040e1303170c09040213030213 65
    0x340300c2c107106005400361101e44100030500601080e0030303602c5103220084206240f1044002120880740c074103045c8600856102140034a000000802406003c4d050031a10f40303200740a02901c805070f920b5558001000d1109503030340400c1c5802d000a200c0c0d154400242a00c15400d81240040c0103070080c08144044203018500400b0b040307102602c1c041c01002c49507542012880040c181d1035540320f001019400340d41004101c41e5001000d0a400d00b0149860900003159400086042c0070a8000c40d046c0c0c28a4400c2c0c002d07001200136980c1000a29000440708100c0e030500031410107131241d41c0d03041207450420645020749003201049032500d0601e06055211010184580241d0380106c0c10302c80541c50300340071110340203044041e545a05045030000d4001e4429a44000c6d86104500100040c2da2907010041988a10071340d035020405c041c0c4020500c03214425500411002c5040210040c82c0c9895802000c813011940f040705030003940c03600002e02070716841d10303a2568140c40c0d4a160001c10304004c1c1c03e003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 559523767 1250 559522517 559522559
    0x20f060a020403110a060f1413120b09010b0607140c030a05010209030d09030803220b010b0403030e01030e07060e0310020f03040c05120601050402030a091e021009030f0803070e030303070207 84
    0x5551700e1801c40003d10340a0201102c50502035003031914890300300d4040450340740b0315200c10307038214903582d80d286c0c0c100d00740c990b00003502c0c25400303080400c84440043c0075400703004000506c00c5082a40c1c68035a041809109600d40080e441000301d11442ca0f00d0034040b01c05a00e02030b600042e2141c0d6504240340c104040c100440e000c01040341c0b001d00010710160196074208905e07001c00301602c540700d03400c5540e1034a901c1c0b01410f00c41c40e00000084029080000300305403846079846d070b40003103000c40064003991044d00041095402054050040d68441c1041c1401107034010115050300035005103410803680150300c0d00c1c01d04200003080106001480085100a00d8143c9068001f07101500c116500c68106000f040e12070340d0004003003070504c0840c0d0025620180c10601c11258400b5031802d019008200b10412030060f250380c03401240850240154500b1a9040003040c0940460707681c650302c050707000600e03901c18000e00302041f42d1b850b00c080014500c511240d4001344081130170500c0c2c000902164945131 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 559525017 1250 559523767 559523779
    0x1b05070512030f0f0d1508030a02190f2402070f1e1a060a09050705090f031218120604230105071b0f05061504050906010b0f0307020f060a02040311 65
    0x6283d485401030450b211104d13040031240e251108281074801800d803a0340c59003885d240904012609050120007060004100c0d000c486404a840555078141d4150b64000b0f84034001840c407a50200b9488036440641030794041710bc1034030711a00840b0100703c0e04503c00075036281c1035030b000c1d0b1801c104d005c104400185050044413960602556a041002d080101504000e402c84038003080b200c0d00d9021071280a88440701040c0f003280340032000144650840d403805031289190300c15841150402041c0020403640300001a40f50040e92011000c0380520f056034960040c10010381c55900500502c14903004d540b10b011440c2500b00c6200c09c1ca0105141000840d107281d00d004280540141c008501c45d01540d10120b80041d08056030912400c1042000340180103405034004202c40c041c00681c528290107800c50f402c104d55222808203030350300c4209003c0d00200c141c5c100095240c965051000c0c55100c02d0302c4c4100c441541505540b2801c05600381c950740c20607a0082803c0c4204452134409403080d0f0020307611 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 559526267 1250 559525017 559525027
    0x10503060405071a04030f030806030613080a180b04030b060102060c13180921020106080f030301050d140f0d090806060108190612050a0309050a0e0402101b0507051203 74
    0x100d544900c003503c242d10a21200b41301407240d0b00921015200107640241d0001081d070003a05020701403040844289119002d84400103820340004004284070703a03045900181000100c40080d40c0d210000065403004445030040040c0c081c110900038005540700b89c144040606003100068a40080074245883c140c0f02405060f401041002c01542203a80c1071701100c055440d10912140244a030003006051100301129007685a6400c00598130107080c40c0c0d000700041541e48511984800b01c0a00d0044113802c100b004200a18250500e0081580120811054660200344051030800c801c030a051041d0004003c0029003030308450800005c04041000d0801c6180c1381c00000c0164500909080b60110191b84007a040a0164804400b41410501113140200d260418075542d404404080300001e64204000c0b0f820f0501e42009000c54080250b6061640c5070f0ba802c2091000314922401300304010001c1e40c0314171805460822094500550140400352b0070300040c0030300d049035008040150342c42005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 559527517 1250 559526267 559526273
    0x501090b0d09020f061201030302060603030c060a0b180a0605010e060304260c0a15060b1e0c03073305010810050402030a021f0809010c0c0b06040f05010f0501080105030604 76
    0x1c88001c900c0311100015004014070009900d031a81c03920031504034002190184603610000d044a040c1c2c2e0203a02102c0050344c5003c02c2607aa48501c40d07441c440c5801000c0460304660840d000440035a000401d0211107086200c480c8402880031566190000d444020400c41942c03c00c0001403e0603054660601e145050b032504881c90003000480145541801c075585884511744060701c01140d0580e0a80d11030481d18103000d40c007100c8100c20141c0303482c9006400100090f9000c1190100c0d48608101001041a4948445150010000303841103010400094000a10720540e01c003502005041c660480040310401a078284040e08290048910300401070005a40c0010810a940301c00c40b800b14003940d6500c00b003800c1c102c4030403000f0b400807204d5845601d14102070f809200300f41e8650781c80500340e90ba0b80381040d0136141c081c0c440a003c40c0b0140c01c0303100400c0c40c00000c20350109016202140000e030400d04041203503026030100e076118400100a220355a8040180d900402c0210024000b070700303040e1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 559528767 1250 559527517 559527539
    0x6070810140607031815080a02192007090603060b09060325080a05010c0f0e1c0837032703021509060a0c02030c100c0203041208090406050109 63
    0x18030341071060001050f0030381054810f08900c48040048010b0304503d664440500d030a01004242280120340101d00103103104c4101c0c07090704c20031603070a00ca03091022400d040c190f03442c00c41d1a40d8400c01c0040d14180070070002c0108102030090010100000c1d540b45182404012a0540106075118030305443c10b01640e554005410708403140003620b8000b007810b40e2031200041250551042085020b42c1110009000065000007a004241d03120350301a0003280204443e001c60038450158818000b40d000c04248942c02c2084a24a02c143ca40c1460720080140c0c0c0c43d0112041120358004800c00042a150070041000045640d82103003000d010950b440c00c058500344d944280ca5220802c01014440140340c03003000350380114a4501c0100b519810002c02c100c2e00d6440c01c8587c6503c0c1c5042c80400d40100d440041213500c00c0001001a0519007120030090000d007840d0f1844c0e808610040c04040303590403c40d0b00f0070303441030720607900c103592100e129042c801551403603840315052200715941088049008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 559530017 1250 559528767 559528799
    0x108130b040f02330a0c0f0c061e0507110d0b0f0115050c03180a030209070503010801110a020606010804020a2c060405040c03060903120e0d03060e070e1e040e06070810 74
    0x107040351076100c407000c00e41166211100c6d079000d0103a11845a480051051080d03c0c601641e0720fa80d074035541082140040301d5000da40740c02c5c0f480080c40401c00074020492200c68140c041c100105441d850f5903440c1c5454120081c00d844007280c0d200002c004120508803581806c1705440c0600b405800c0c43c040b01c0c0c2c090740b2030040080c80665092880c107148415965100c00d680910b500421143d00750500300c4d80103000382c20134001c00c00c03258640484040c81c80560b1040e16441030040c0c0c02001e03581c1d50400112980b8070007034004c9820100790030011a241e58000c1c0074202c080d000303001080101d214240824240d00c4040d03c03c50240f8600010301000ca80d1140c85a030689030171a4000c03410100c10301c1e08413401071407091400349207860200102807012002c00c4070b0400d030306595030038048592228034011000d4070964000000c201d4012000c80c143c18619800e036104104032001c8808810343c107000c1400c2d40c004100b10b512941100c0c2c10420300d584c00008070343d00a640070300d140c0c20031401d002d0075006d45094 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 559531267 1250 559530017 559530109
    0x130c020c0f0d1719050406030b01080408040303270b091c020312031503060c180f130c09080d05070b0106091208030c13090f0b09150108130b040f02 65
    0x410242c0032203e02480c2e007181c400340740d0004400801014190300505541150250000090504007001c41700e40c0b1801a10f070149411050040c500341c90f40d60242c1d194010ac0d01e0104c0227a0544151111070307004049102c000740710250181d5a22500401003000d54900c0c540f00c203c078060384206034805614009070030099460314980440e6a070f01d40000c142500d07140003124503814880d1070100182d58030704078040c00f806016066100714003a07041040105e00d6103014101c6401240c200c05030440000390781c000720181400e42c185446840e403590b40c4e0508080b101d055100204800140120130404600c0c0380d603004000a1078581d0f8114140321126440340b00d841005000004040003041940300d00d9011160340070302268115840e96602c041c5240079080813025030f40758900e481d24001c6182410007100d0701c50204c946422000c444210015644140040e0100c28011903140d007460000303c860b15402c0c0190302504c2242605100d03441006160384182e1350003089003002d103858a40607282080c003100f500300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 559532374 1107 559531267 559531283
    0xc040e0a021615020c010203040f0b06030d050304060b0a05120601090e070302010c02100c020603090c0a0b0702060d0b0f0d1112010c05040b03040c0302130c020c0f0d 73
    0x54920a80900c00c1c1209440300003d035800081440d50003a010300509019010708503d0032604200e4080b210800094200824801c402200c241e01c072204800505c1608241c0b1802016400040d100404268a4001c208125603e05080f00040e22024044011204440805a40e201c20030700c03400401d50315100707410800c0f2602180c06000d594040c0c40d040d80c041c065a0034040c8565040215504011b07100c0140c90043e92400015401085032600030001d43c00080e00b0044050115480b21544400070440140140c5480c4190b03a03600c01c1f6420009280d40019000c0303801c940d02444060780c010340c0e15031110100038010550045030034042d108000d0b959007042d016802c80d00714a011001142003404200000b01c0307610019684544a1401085810703940d40c0450907030320101070b0b824002e07a00c03680d8102031950f0400004c0c100b06000c0714814490710100c0041030390301a0030800a41049 = true := by decide +kernel

theorem cover : BRFrame.Cov 559352517 559532374 := by
  have h0 := BRFrame.cov_init 559352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 559352517 ≤ n) (h2 : n < 559532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
