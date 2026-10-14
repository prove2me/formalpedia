-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0017
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:22:41.21938+00:00
-- url     : https://prove2.me/submissions/c92d26ac-5719-4d90-a5dd-659a8995aefa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 2877705 ≤ n < 3057561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 2878955 1250 2877705 2877713
    0xd06021201080c03030702010e0d0507090507020309010207140d0803090f032b06050a060309060e01090503190801180e030c0f0d0e010503090a1403040b040602010203040b010b070c031e 81
    0x301594004440c00c0c61140d41440d4415241c9030388410b09a00980c810002440540c0c2c0000348680804400c0300c540c00d10750840d20382107041461f1940001e161500382418001e4158000c800b4241110080c0e00b15507813181c0e105241c000300b80c0100c0f246500024140c2c004008629820020b41d400000102100c0042c4032220302c0714515803284601d640c0044441034880600840a100d4101106100005000490a00703000840c900d40b207100c0c44090690319064081000216000a4050000f01008000460a6041003522940840c810140009040601040c83c80c080c050702070503039400d5805401843d0108581c64010710707a21512041c0b511041c014540003900c10030883c914940200098600c80d099441c010700007081c408000740c1882003d00805c00c4401c0e0000c2d4581c05590060f01c0f8854100e20384200c03070f0452049801c40345030103000090104285030150003c0d0700a03407044c031417a4100c3ea81c550040c04140181c6000400c20007555104201144001c01d8502e90078030901c0203541207100760303a030b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 2880205 1250 2878955 2878957
    0x10080d05030402010909050613020904060f0e160801080703080703090801050a06090b0307030312051017060906060405060609010c060612061a01020111070f080403020907080a050106020f07060c020d0602 89
    0x564800050380c00030800c811564006403040c02850491400d10950510070005115241000c0d10038a4180c3d0216000c1020703950f0b900440010b0000e240c0381c001444d20f03a218085030440c229040070340303005480310045030980310b043c20504031082507000d08010380c150790741c140c0030354070148099040020311180411100400c0c8036030f034001c0481100000e1664507004401082c2c071860b01c800d0348241c00406040001c02d40101401014420a80d40000c4661310460162840c01454110700d004d1021540d162034070000000308240100300030401c07a01c0c182c1d01c840070032040e65001c41d1038a030407034000e0081b12946c3d40110709414045110700c070302041c81c80d240c00f400e0040d1041341c0d205858483d1555840341c000c03054022041c0e00d2560a00c02801f000c19030201903c4a1300c54005c0040c2080c584010b00000d01c800181500d0103140c5c000d01e684103604040d1001001c0401c1944c0c00c414091034400000740c81c40c00014142d000c030340340f031001d001020300e083c60669030307811002c20030390b04107034200308420014013a44 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 2881455 1250 2880205 2880223
    0x6070809070e090303040309050103060f0303050c070801020304051e010603020a06050a12020d0b0915150307020102040302040c050301060f020c0307061206050301060b1314090103020d020103090506070905100305010f09051008 99
    0xf00850303c0b071409040040420400f40d00460505103421018401240d40b21807400589425040c0135030b9030b90007404000e260184aa2141d00b003544044140000c20402154a00d0350000300742c0c0804084034822061822500d545c80006e40c0140a40d80410600d0300500240000071680e040074140410241c11769000d0b82d001107440c403901580e81d0400c480600c2c21034402500b10f4100e285070349040018501040c0d2140d46150b4481c400e08010001404e9641700350110f60140d07a01500a100c110b00c0380902400581081c0180300201c1c840148115034140700042c070302000f0342d0003401444c0003490440262504221411907603274540d10b0314804500f5440074000c00c00280040c000e81903984040034005c00364560290001c1c2c9076a1248440d0100c29504c103071025065a4044170040b8601d8881d10043e00203010780603008116016110401c401c041d0846074a41c00c582d030070b44403130701e407070100140480403a4001d0250542200d1200c00901c800c81850b88401e80c0024840c951030900d50b2a85c0026242100749 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 2882705 1250 2881455 2881471
    0x2070b01061e02031303021c05030d0203010302090601030e0c060306040e07030c0603050606030403020a020f0409060905010506010e0301230403140403050303011e081903050405150405090f010806070809070e 91
    0x1101e080000c2252070002c0c8440700660348003031820100040540a500902840064425031500046192843c00b5002c0f0000544c1e100c0308490365080102e140b0b6000c2c2d00244806c3e032003544003c0004140c0c1d402030046003960f01030754020b801c0d0307101180d0421100fa0000341c81c0d10b412039907480c800c800d1742c2d50801543c0c0285000ba02e10b035170381d107280c61001800d0b20710040146014600a0050000003600043c0b5052016411104440b07908407001c0454001c0c242c146014004a0912212400703100c010760140f030188600781c0c2c90704110031109040c98240c9020400101c02c20804d02170441d145131482c048550410f2207031802440c0c1e0460640740c0e40e01034015030403d40752a00000010007006c1101c1200c1074035600e8045a8201c1d0a15288009031690311480102e49034110314145e860405104400302e80160000820f20300101052151114164001c0e00800780031310f1501c40443c003202c510300e101e9412100b81200410407641c805004580300580070b00f20b52003d1082010102e0001e000300526445019a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 2883955 1250 2882705 2882717
    0x91b0403051608010903120c020c09040311120f0d051003080705030310120201050703031a04021603020c0f0d02100302070503070f02090a050114010302070f050f0d11030a0f030c0302070b0106 84
    0x1d05aa56401482a50f2204001340e1400c254000081d4100c4c03071042418010000000c0ca185424005070300b4a648070404a071f0181810040108054114072541c0c81c222011044810001c1c2c0d0584480b0588282c01c52000c500302c0501065500380f1881e040107501000c510400490340740c1c0d03603403170120b95003110b01c007150607400100070489100e072441c08580007018005819048242e007900003a0051244c00d01c003504268845c03080c18908000b65003020810000604215650013042e06610000100090200c0040c00342c014030000760b203014001001d1058009007112082c0d41c00354204480c55010020307113024180c0a01040c00410800e00140403240e010f0314001d40543d20610401020a0004007180341482c509001804450be203450a100070a0080c01c005a450302d481c2002404a12004401041441810700030b08a402c80840d034040310b0f0942c0d498684182c0748007445203445c1c0c00360440b0030000501c1240e000c0a124031a80200807054480c3c02c0c0145451120303190108208400d800003c04611 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 2885205 1250 2883955 2883973
    0x50103030905030607021b040203060d0c090e010c02010209030709022506020403030905030a05060105040509030405030303090708010606050c0a060510030b040b0106080705040f05060c070e09060405010b06040803030402091b040305 101
    0x10f0a0004580c8040c8074030240c0700d000708a911500e01452100f2007980183e5000c000503142e0f440d861800c0780400e42080a810515540b042c804002d0044044449515406c180c410340d5a68014001e9034006130000b00a007000500303100001c0000e402c4101c150703c10300c1c840c102c10280300500c4901100c0c21400307600c3c056038071400d41c140500a1001a40010302a034040d407228000705102007000703030558804560206140d1101d400340c601d03500854114551600000050201c22400010380d9400c889403080240055641c84006844d640510320002d4869000205071742c0025105501283c1d000107111480a07409480c0e450b9010512800c0f541100c1010086c030041c45181e4000000941c0300031507103011840e10b030605d96220301040c218414a4011781001c185141c1025062083c08082e28004192408a02e04144050b43e070b084c00342c0e0180c80c15440c00d5914080d80c1000000c4405980355400150b28503200c590030310018010003800140c05810804402613203041d85402070005501800c010a6566 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 2886455 1250 2885205 2885209
    0x10b0a020610050d060504111003090501060501050901050d0b061303030507020a05040e030d020705030c030c0d0f02070320030a0206040f06080604050105090c0f160b04032006150604030204050103030905 89
    0x192002e4408010a800500e08202c2c90340e031549101c840a03840000810292947c4c940102c08003e800f403881d9024210703002495030300f50306500442d50240214000d0112a40c0d80b00103480324804c1c01301c22030028008100c940f80c2d00034541c0101d4103c910103400c4038640095607031307041041c1041c4d4004400180c000610b560661034a5020350002d010111010040700801400459403031003508003050b01d4a401280d0802402010f02c20784e002c2014120603240c4d0350300c0602401d42c450540c1d08410700410300344820b0364001071000840c803090b20741c0110b9540f941807035142070b100d442d10410b12165051003031a401c2001178841c0c83c080c0c00108080c000c20304604c0c4c1400f0300903116400044c0000d000760320701001000f02e42d60b03d15241d031704400e559601d540d40d40c5003914026090310460042c1c24610100700407610407c4400300703189200354020b54511802e280690100ca410500c60703805040b490b40a1404104543c03450f484156441000518151400b03540f98003090580d4400d80c000d401003424070034104824 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 2887705 1250 2886455 2886463
    0x30408030a050601020c030304090c0c080d02070510090209012607060207060905150a0503190501030812070804020306010501050c010f0f020301140a030c09090602071e02030705030c06070b0403020c0603010b0a02 93
    0x4001d09002401e28030346c40e04003080d5280998840d111110751036203000c0030200c2c041c1c241e40348041e4001c141103030350b0204116851b020794030008007101c45106095070194841110300c070703000520354005d150440e10b034607124040c42c10b1119043c12090350111051804000c00b010032003000200342a4001d01851454010003074050380300340d031159001e4070b40240c00110810394482100d158840d641081601c0e034581ca80b00702e41d450f80402886030454508000401805001e074050860381016900022941d039802d0390480f88604281e0700250942c0c045401806658058804cc0c031032148103100005446003010360020640c0e4400415035002e650000c010b20002881508007180c0010070b0303c26003c050328580e1204080c4040d0300c41c070040140e85032190740801c0011f8045846440d00186a0000040020740340304500500c22001c070720034442d0b01e500103610b06002c5141c8601c0c0700300500d2641400e0490b00c0d4000701c120018011021406014500d0a15a8801c000b46000e401c0c6000400e80700d042806018ac94 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 2888955 1250 2887705 2887711
    0xf0d0501050f09120409020c0a1209080c010c0f0b0901020904020a030b0f04020a05040b0903011b02010c090905060607020d05010906050117010c0e060301050f01030e0304140306130209070f09030206030408030a05 93
    0x1283c115501000035130310364800f00c0d0210f645540005940d03d40100c0701c1400d02007034070f00c01480300d06100c40150700a80c2c00a2910180c0e0040000c4c0c0e9003e10742c0d98010b40302c2041c880001401c2559225100000c0b5072143c031503d40c0452502c0005d441c100c980000601240e2000c4000b00100b039544450812508042c2e9500340c0942e01958110324001c002480a0402c3c000c610501c80d0324030002134440b06645086d000201829400a031001e001030380310704040d02030428203410f4030019100c1003000501403c14055107000d07010140c0b40b0791510050b0380078001464541d20302070f91150340302c107004400501e80d803183c5402801e46a030a54101140005503034259041140820100059020092403603540c40003203d0461b03200322a201d250311050303401030f005800741015010b114000420005800d920503005085084800c03010394100740c4d00c510b24160741607100f03135010b03401481c01e0340001c48a5020306c80e564000290740c20b2210141e5074039400121968002ca400f10303a2514040b00740090070a0700d010701e5030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 2890205 1250 2888955 2888971
    0x40e0a020903150705070501020301090f0e010b100c140304030506010302030d0503060f10020a15020a090608010b09090402031002040303051308060403020606010f050d02070602040e010806010f030b060f0d0501050f 94
    0x71a0090040c00280c0d510b100e500f560b209a000d10001c40c0381c0c0c1d801031089a60303c03640000259205d40c0c0d140302410044c0045603075100340310300301080000c1c018011710864040907002401000e042028020445070626030340700440740144201d0512000c2d030002c2001c0c00c025071081004241541c1548189400d1002c4004130405200c000e100f84600f95a50032401190f030303607042e16003650810200408900d816060315001c0c0040d08030104641008021b90014114a006c584070041410303a50f880c102c8600800340300e14842c060302480030040c83d1600a89040c2c03c030340000c4c03c5400c1d44081040410490b070095200f280032440c00103529072143c01d201c08100050158801921a600e05074030040c0d16190f00410680c1000010440c2c024041d0052041d6004071001d940d0454030390005103807002c000c1d4414003c2000c846c461030000a50000700041c0c0c10305856070210000c000c145103903078000c2d0410020b0a03071680000e0700300848281d503d4107080501501c0c0503000214841c189489036007602e0201070a401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 2891455 1250 2890205 2890207
    0x10c020d080904060f030b0105010509040b09090a0506090307030207090f11040e0403030f05090606011202040f03080403060518190203070e0408090a0605040b0703180305030406020a030801050301050601090519090f02040e0a02 99
    0x1700f1f00c5442110b044a10a0034600e0392411084000b40003004801006a4020810010700c01454000600841d03503620640450302c0c3d5841d1921055500c0c051010001e0043e4840303d41070001000b00d8001c42140300f2055404115516652055001c84d007082d040201580301c1030b03041105141e070500a00740140c0c9205001c00c0942002888680c6804000306014180400280c05132200003140c1d0407100104403c07203d000d84180c5a240c03082c816170040c40140c80b000d00b0034021a50402c2403400c0301c290214581d004100382520342d441030054070481c50050340e0500a10a002036541003841c4114410ba200e4810076a441c0400c00c204040c89030b141d00000100a400d000c00d112500c440421100110f801d81442c3c01d00d003d040106120310291508010a00d0101040c000b8000360000384c2d010100b0321076160802160f80715802e03d8221001110014000750040500308454280340d013030703030311644248103038841000e890780c1c0c0395800d54403401ea40300c88443d80020304102e100c40045445411408160043d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 2892705 1250 2891455 2891459
    0x50309071e030602090a05120304031a131b08100204090f06050102030306040f020d14040507060e01020a02060c100911010e03011e05100e0a02040e0708070914010c020d080904060f 79
    0x7662540d00380002010303142d00103a440d41e90b6991664080003001c0c01405503842c000c0c80300519849400600c41182d1202c89031000d5107000394011364039849040708555407507980d80b40e40c42d0011028003400100b0f1100c00350280c0441c502c3d40511141e454030b0104200903950300d240090420889903440010480f0500e0324409001d160b9000c4200d94000170121408103001c1da1503030061000780b14411241440600d00148010203801d66040280308601900a807410641d5400c4156040701c01892030500581010000c0401850228007600300f41d440001100d03400030034125020103e6448050030741d9140440e4941c0802c540c2e000c006032031980c8041c0c0091000c0c9000510800608058400c12030620b51284005585690f00c0000400201480d620034400350904803600300007075200713001c0c155100ba04400003c1c882409504680e01076903241d6240c0c0000d03443c142a4910703100610b5030950400402012150241e501d41c00400000c901070117013241d41d40307092400c0004031140b49e0311860034602d0005013 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 2893955 1250 2892705 2892749
    0x1a01080618030a08071409060309060a11070506070302070c090507090f15020604080901020102130906050301060506030c0702010c020f060409020315010e06070303050c0d06080a0302010b06031303030e030c03030705030907 97
    0x60b4205c3e600381065424198a1011043c0c60b0113220205030b04000080100b01c0d1b040c90000d0214051800044100448840c90114440740c0c0700b5200c0c054800d500c144007040300c0310710950041202078060b00a0703014494035440e400b0107a0340c05035500c50001e00c200b5414016410918510001880ca541560407070070b40503200651200ca0051002e0170b0101e0104803440503034000e40464110040d504911400c2c19200c82c0c001008243c00d004440c083d43c41c140c0f012501c3c0c14000200c3e4027601995070524100000d560044911800c0e11904030f1304903074038850030407494032044080c001401c5090400743c3c8a1601e0301800c445074000000150401200c3c08810419442c4c071002c803034000c1e81600d00400c80343c2e15000025518424100c001c2911480e122000540c00c01c0410070f0302c1081e00c00d82c000e008d40f1031441c0c208030540c0020707500c01c09001c001d000058006070282d408068000710344c1c03050340c2c1803103207154540e07045400803180d9501050001003041078a40051040754081c05c02d92001442940307030010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 2895205 1250 2893955 2893967
    0x60f0306050a030b040614060d0809150408060106020d050301030b0402090a06050901080f010b0301091707030509150901020c010c080409020703020a020d0f020102060702030a1205060409020a03050c0a050f0603040f1a01080618030a 101
    0x9c01030460080000d501005844580d01c060481d160044182e595039a0b815500365100303400d104900045c000d10030703101c19152003075088038100c070380001d800300881c2c8a5400304000010040c1440420643d03e4400040c01d440311020304d80204220409400c110b12a601a0f9080d85c1e0108540c0307109034900729000e80081c130030400c2c101103101d5052a0a44599003442c082d1580c1c07144814007540001405c071032a5501d642c01004000c0c594007a0700b070320340b064004001540c1c1d15202c0240100790380814041801111490340c00b1b88511170080c411140704240d5a000b05040c0e1307201d42000d46038802c3c0c104926040d940c04100d0b5a410041d90302c015031500c61142001800040c4a0306074481c85519a008500250783c1c5401401006030000c02201c611a66860801e540d403410400c0c0e18003681c000b02e800100781c03500701d91920981e28054800c0e859a9500d66807405202e1419600329846900103034070034020002d0240540c040c05a80004105504102d09411445842400c1e10000c0364002c00c2001203041d4068 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 2896455 1250 2895205 2895229
    0x114060309120a0c050a0804050a0b0a080403030e031e040801050105060703020309040911120706020607030605010c060b04090807300203181c050105100807050901060f0306050a030b04061406 84
    0xc20002d40368603410100300c1d0351301c09502c1c014055204120b0040e0900104800403c22074030708076000340310903945640c120b800340644074000001c20030307400009010034000c5d00401c21503162a13064070301d403d01902210006402ca03401d0311218034000f2800f4000030100344944c034094801102c14504103002aa4000d503644a45000c080c056600c400880c400c00811214a042c0200e0007040240014449600b0654650a5100300001442040c0114a006001b8031804013a01c106039102902d088040d01c500000e0043c0440d46a04507588209940100701208041c0c200341e88241c0074042e07d034040c2504c4143d40d074010000440880c141016180c00b10350000121005045d00034068102c4c65079420000b4081c80c4503810048441101c142040100101135200b68802c56040300c0702c080081c0c60722080c036650070460260030b0b00204440018004a401000c040c81c1008080c540455000c1c0c40c1c2020516648150b8011118140e90006000411603540039030b410101100d02c82c002e8501c0c2c104000741080020b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 2897705 1250 2896455 2896483
    0x40906120b070302091f03051017030d05150607030c06050106080f060d0203070b0f0903011406030307031101020c0a0c030201021009050d0c0201050c07030309030b010b07080a0305060103020d0e01050114060309 92
    0x260805261b100e00f650503d03104562540b00c000700c81000300180182408a45c8081c036518014000f0a0117034420356844d040c41c005000039821b050900c0b400000928001d041c540b000480400f0240700c6035244030041803c1d1744240c0c7c45440358030362440e01030180c841c10782141d001d002c400750801c1005e11030b046185070b11001c11102c0184054482c00440d00346001c1d5000524103010004806c80c114800307a0080c0b080c3e6606500070005140c030000c8a21140c0e00030307120239516410400c0403078082840749101c0e60500c0040d0000504d410001c0101c6031030200100002c40794000c00d600100203560f014032203861950400707503050160b20039507034481d6140d01d010710041050003980120704041d64401d5056907603911000d400c4501264507811f018000c03580d07600c41143d00007102c00000c5446404a030940b050583d00074030300c9003071903c1900b06a019001c000e00042c100360f408c1c04694007000c180d0080d4000100324900015255040442208180390210680d03030183d64100b041c040728142c0083c40c0d44031002c803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 2898955 1250 2897705 2897707
    0x2010e0105070209040605090d03060305100902031903030518030310050108070c0209010e0f060d08043c05010f030209090a050a09020904030801060e040504020d1202031b03040906120b070302 84
    0x1805005031002d00502101a4002c0600d0080104001c901d61066018010b008220f5054008048088054a9075408000e000d81c0022881d01d6040e01c0c15088205494030003019181081028421011029203000782500060344070070500c0b03054102d040d0800040b02c00040510314500d4032019202014403140b1440e410030200740009514148104001e000300340c1c0c0200114840d5a46e80d00300400104103880c0003401c0814403000c2100c900c1e1445201412640c080ca9060a240c0741204048054040c1e1031413031074111f65031400b541902070074045c107241450618141c101150031304000411444c500094803003418030404c21040789586600c88036500100510002c01e1607a26030210101501e1200c00003500b021800041c4000c02d0340104805d8140c81d1966181c10070490218100403e641060714003940143c800c00103900402c0c12011142058007050048a25001c0c001e034144010143d80a80700c5804e40021034103020110460041000402c561030000d440008180c40303102100c2d10252802080c10b0b8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 2900205 1250 2898955 2898977
    0x10608160f090b040609050307080304030201090b0a02011806020307020f030301060903140102070501020f0703030f0203010b07060207050c030706030605030c0d0816050705060304110103051f0603150306060b040608070305010509040201 103
    0x40310700044000f802c1c610301003540701c07552034101524020442c01140d00c2409150004100d40b503000044d00c044a405954400105180811801e4260300203d4080215502e4000c8489116290030305440d0151281c60010b0340d903d02600001c0c101000815a01001d810403c0108180c5910070907042c1500c0c0c100c00e000c511a56464065030081c403c2c8000140b840d40003150113400801c4200245c401140284c0342803107285036400c10101280310900941c01d2500d401c2c010307200401d038a82e010b4078440d4810f10071140203070500c0b4000b92a2000c01c0e88160000390316240280500e007818024125603550035110890b10103400d80e81c102c41c0b400368150032000c0e000728240c59002d108080001c403004190203003003c1d58a042a017000e04110035042c0c122800302e410800841c00701c0030700a281031031861100c01e500c1c08150408500701c001d00880301c1c100d968204903610110205202e403151100400c503104400d6510392601c90080d0003c10028006402e040c6424010840390f164603080a85c01a42407a01c8070b1491 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 2901455 1250 2900205 2900207
    0x402090316080102030f0109020703020a200901080102030a110306060a030c02070e07120b030a050c060306040204030203030d0903080612070b03040204090803180f0d12020903010605030d030203040b010608160f 92
    0x5401a0702060101d00e107900000e10064194021030041d0550300c09003505030f80b92040e070300c2a4841e01000400682c000d00d0410007003030008c0300b038003030b0751a01d41c0f650403e102c80c0c100003030b000d44020b0300218104d0354000144012150310703104140d40ca41c0342042d451b05520741100000c6060040c0804602030503100c15800310410310074000200036001e2582c40758a14148180e0051260a0362482c0c80b40e018076010340c1c2c0320f107490001400e01800f544a001050f150a02c5418020140c00181a240e0410740034000400141d900f030028042c41c160107030380020700041900b8010001c04000c2d20f038500450b01c40301001d10f0804042a410140c071514071400c8c0c0e8986540c070100e0018200e80001405816000c020300c114406826030620714502d8410485522410344001030ba112000d0002c200d01040a00c0d4512110511503009842e070742200078000a0b400740d481d40440e081044104800c0d000903030000c2000108000004100d024007680d141c4917150380340c00c0080352003072602480c10205105039168000e0301a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 2902705 1250 2901455 2901463
    0x60409020105031503031b01020a0e01082401030b03030c0307020306070e06030c0306030c04061401020d02060702031206040e03041e1d0604050414071701060902090901061d030d05030402030606030d0e04020903 92
    0x10351281280421187c80d1001028000e400a900400018044031a50445580b154038914040c20b1a51115030340c0c010b4056810300c4130709901400c541070644481002225507800e00240c08004d408002075aa107054503c101810464014140d0051004003442991152210f00c1602d42c84094800099070780c1d25020002850074040c01001c81c0c0c82414039401040c40d00d00c00900a038070344000e03021a0640b4400380c0b4182d8458500300d65580c0140d2040c818000300703040c0203190680201c40070307000180300307011141e8107403c5512039000782c208640c0314401c08440c211446510b134020300c040700405001d5000c015085400403401b910329841107440724041010300041180e00c11020418108544030985d42e081c402c86422a0244220b485529000001440c000b0f00d0007101d00000000744801c04583c20040c058035900b14840b00c4049000410751b221425442c1000003111140c100e40300c541d100c0c5010f01c1010720342200106102e004e50807862100f00115080521440d50341c00849015031284e400e0000700340380c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 2903955 1250 2902705 2902717
    0x303071710050604030c0501021c1e05090603070905090106090303020a080306180403020c011103090a05010c1410090c0b0a020604021c060501090203040b07020a05060c030406020f07051506040902010503150303 92
    0xf000b0000a0000204402d024501c022a0002c0c1c082d500b00588100b0020f481e008511119808245102049401400e0300d9146420070782c518204141021a44004176206400498030f03500032504c5900c0c240418907180b006903004100510b0300061032403c6540080d102d0011000091003c4400f00102d00300d40e896200243c0754074900710340ca40044c602402c00a40e648c6032105014003080e5180d10909010740c0c003100301e491704030015140303c25040c940001107036014146d10094511070310b000440814464144051001040c2c1840003207031684d16410720034840e04c0c9652002c680c0704c500b003042c2e100964000c40d4050303000750111807520040060305074019a5407154000140b98610303100000c00c1210b820384c040e500035802581d24030910343c0c40c0d0744182d940d9208c201c0082c3c1564000d400280c80c1c12610001107a0152081d103000d0306000b400802e012840c0c01a44c0704540e250000740315400c0c9085107106055128a0849050215466540020300396100280060306140b81d00c0d0b40c003031a00d46041003254a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 2905205 1250 2903955 2903959
    0x305120d0207050a05060406060f0503030702060c01021314011b03020d030b01030f0c0203040f050a0803030406090203070e0708040213020915070203190c030501060603060501050a03020304030207080d020d020f030307171005 98
    0x4c510303180c80c9015511040c084a0499a141c6002804113140c050b0302140402c0c0c90b0f0140085107048126020480941c00c0201d9005056400300101203111003071080c090020821605020450541540003602d44250610020b864540500c60360011a50006840e684403429090000301c0311444801200a03248810505418504203411210080d9001006104a13046c2d01c64002c1540c0c1c4030810032070805024460001950b01c140040340100d01141d1081103840e1000301150840c07580c5031000280d4007412503181021482ea81d041005606110240342101940d0040c11407400060310300140c080c01c51421035100711400401c0040454030108002c0310003000100700c0010318149441c000720b8080c02030104403019400c000e000a0501c1c024040c030b4080d20f205171241824a100044114000c0d04014410740c00c52150510001d40550248110710420206038040c1c0105109244041d01d4401600680748042d4010070400c000c90380c0c40780041d00c0c162481006030290b03840b60400410580d015800052b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 2906455 1250 2905205 2905213
    0x20d060608070e0a09030507150608010f09030e090103030206011404020c15010513060e0109050c070f0809010207080712080a1202030702010c0306051e0603060402040306020304050d020c0a0305120d020705 90
    0x20400c0100080c1040484881c140310070352560350b81403500251761a00d01d000300480d40900c0410f00007030070500ca24080c4003006800080059807402c046080d909410f040180d544e41e41d892007414103921140b840201d080a031056941c551559a0007999400b05100d05000444004102080c681e942d0b01258400c804a808550f5600c6000546d1711451800b881001d20800c0410f0340c40c241ca002c503000c4d00c1c04480031505107010507845c0c2a01203001e03100003000c0700031030942000200001154240420409070003041d815403201c043c0c3c0c0029280480035040310581d640850340800183e00c40c00304540c9100d44c810b00b074545070b4648840c15108624004501c44450740040300700504e0b41c1d415072000400304090b41d01481602c3e80c4009110044950805540c1c4829400040d030300d4901384a0015500702c003010307100628250b9681c444100700d81042e20215566000400c00380c501940c10000b000410104a40d0a4a0149550b07507040d90360420200c2c4c03c1c1e07400e101184003101401e03168103584407207400100362 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 2907705 1250 2906455 2906459
    0xa12021203040b070e0108040b0c07080702130506090c040f03080a0905030604030804030906050c0613030e06040b030105030708010606122004080102031602011b030902060d090f03020d020606010905010804020d0606 94
    0x144103544011031300c4e1070019020b0b00311100258811070300140680d8004400c0405e603200c0c806a44102d80c4a44401c0d9807613a0208071200060b200d480084061581009002030302c0d041000800207449406400b070749405605000c288181c00112490f40c0c1165030001503035550316002c003401d4860400a42c816940f5018100c104405d140d00308160b140b01714070942e902c00c1c003540c23948406d54041c024102c882c5c5142c3d10100009128907070340ca41107000d9902a051414200b00105c0c0003451076030098000c124001404801045981010440f0740c02611904009100480c14050002d00c029119010ba00c1c005c0c0d141c04844101d28920030342d07900c0c44400d103681760350340300d4482d80c10354040d500c2034907050307002d280051400780070303030310600c12030011000740340d01c803008a4140c50703045000c0d0540c040160ba005800b00468002c00b6414030a558403113114000010111115080190405168052980540d00f000040100b40d03030740a100d04d401d0703440c2401c10401646890001c682070310f48011004104c14500000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 2908955 1250 2907705 2907713
    0x3130209010806070314010e07050a030906050702030c011104030201080c030a020702030312061002060f06040c090503010e0706080703020327030d0e1e07030206030408090105070507030804050103050106030e0a1202120304 97
    0x855031041c0c01d07903141800249180036035246c14106c01d00c00da00314460b004001c58440f500c10740c01000d944005107030100c0e4554554a8103002c4901c19100c038000741e2302c00641040743d80d40c2805101c030f0310321902ca40e241c2414510740010f4030208004080c10966800000018101c211a42c1916586034014041380d4403108908895100000705640980c4502c1d10300960040d120310025440340f041000032044c1d0040c1d11060188000740901841113014000d0650010a150711700348691503411081500400c5207600e07141c4042c209410151450003054010401c11000341207181405148040001414109e43c04c1410100d095008100c49d05e00443d003088101c2440c484001050542d0341c08141c1c48510440200505a942c0c04c8544030017500001306100003000308240c103014000d81c00c010705155180c504c5554850b810020150030440b0410000f09040c00156818851039003d042141800c100c80b000c13101300fa9542d14060f00740244000c0c4109010301c010341c03003808028502500e80c1ca0316910f90409143c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 2910205 1250 2908955 2908963
    0x50403050403020f090403020d0305090c04050c0702040507110715090803070c14010314060904020d050303070302030405060f01031a04030905060705030405030f060f01060c020a0e0403050306040605060a0e06031302090108 97
    0x21003644101c1a00d41c50010b80d10b0840085c44c017640d8503070003c0c541480c00c20400d030081c1100030500e11260081c603100300c883c3d440c1c0d4050306214084000300c2c542d64003602e104110445034064403207410403020180c3e180e1480e00010750131040c0c2e00c01041484540100040c01caa584e003182c0c00c41d003098000410002d080201c0d288412080e2056a590500e0780e900343c0c0011803c07140d0b80c1d071000c451307038015802142140c1000c80c1c895410a0010f0650054507080c2d8540302d103550f0060340c0710800654000204009d0090910140e0341241407081d44c1080f5500d962540c9115807080c48400050f5030b411004181010702a101d03482c01000c0c0031385000c3d103529030303420708949030341003807280c1d41c081d00071a8010103c40c0e0340480c406102e0fa04024a14510ba420f041040300c0901c081c078001c81e0072621240004c00c00e803080b241c4c920f100380c1c03003a0340701a0b0768a412828402510015401310703000321028002548031302d400c440e006e04041025a079154490b5a1020071954072102c001010307400c01c0100001041e00c94001c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 2911455 1250 2910205 2910209
    0x603030706020c01020c0c03010b0307030303020c0309060316021009020105040302091801050109091403091f0302090d0b0402030d09050901090b060d0f020a02070b13030b06060c010608072d05060318010504030504 93
    0x21040e01e2905007d2802c2c14203803170070466020740c141c00040c01400041d00903030140660300f41c01401c13642407042d14000300d50294420b86a40070207030010039455200365030401c925961f0b600c14690501c00e048640d40060300601903400000c0c480d1102000081c41c032300306542649072001110b0300904c042e59481d1808000bc1c600c4c8003055130f0010809004002e41c140000c00c9542000c4054181141210003180008103140144100020150200041440c650b85e2840d0f1200300341c00780c1e0301c06205007014410035150454510a210500c03c18840400c45036542645080c1105c1c0c28000101e0a520300400046062050000e2041c0d031610348004051140c01036070240504581d55001c94075002d032154640141d5008140000403520030340b150a0000980c1d1518a6411150240ca500d04006c92540460700b540c503940c0000400340e010507001c203d6072484411111050b117a400c1c0c010a08001c4e90403c01500b503050084038012200040420f444071603005819403030040315030082007a07092070703d4001e0541c0d2141c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 2912705 1250 2911455 2911477
    0xa020901031209080c090a02130306050c030a0b01020d080a0203100509040c0305010b06070807081c0519060504090507120212030c010c030606050405180601121508060f130b0603030706020c0102 85
    0x500d501056244d80040d801503500d03c000e0000d2121354400c41d01c0d002035484010980b038000034001c80040043c1c60b030700400c1d02840291600b65283d18200c607400e000c440e0803a200e107046602c04919031810a800a01c802c0d0080b588120150350780c0d03600003a00c40050001e501803504030740440100700c1440300102c42913064900c110000d212400d90041001594040d81c203000d840881c0401c690400211804001e20821880600042415144290041c101d910485003815402d02100788641800068170840c2d020b00000c0b5010803440019440f0303181e460410b0301030811481c1000c0000425035032109806510441c962040b259a4241c4070440783c0a0041c9220075000b007420020301280140c011015502901c030b018080c540c0308580c05000a80e0184060030b0079040c041c04c2060442c01603140e01a06111a403014214038020f4a0004c0007440d02c10010080e034806801142881b80880c04410b041100716000710588801f6101c0c200001e0540c40f504100030407a0344002082810920190003500a13140e00d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 2913955 1250 2912705 2912717
    0x2090909070815041a040303090b060303040b1c0b060a0c050606030706050f030a09060c030204030308010518040201050304050f0102040608061c080d020d0b09010602010b120102120105120a0209010312 88
    0x2801004595441050150020b540c0020000c520301d0307522000c0255100e03005041c00713000003218500310013040c44199416400652244940c000b0b101403008003e4000d002900294541460403010031158001c5520801d0f20b80c075a0001070a06100d00d030401e06c106100140b207541c0d204a2810050082c0050303480c00c0b542405030200040c07682c90045071510841c0c1550b02d6803440c2412428421040e6480101000c00d29035030713108084082000b47c8a6407629040640b00165150300354140984400d605900140c401c0c0610300401401b0300b021200035401c2035080c20a01c0d10b03071b100d42c079000d0306200020f03035a0041580701180000d5a660b202a100d4002e8400380d0b941c42c010040882002550001407101805010040252085000c442e9000b0301191785442c00010708800d001001564126080e486a40141c0d182da424014510342131400b12594603555008524200603c0500031a10405115684c4034080c01c200455916030140041c0241603401031000140f580c403440c041c02c904142400c07040c00140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 2915205 1250 2913955 2913961
    0x503060a02070c0905090606060706090b010f0612060b0a030504020d080309060f1e0115020307210e010c150203060103020f030a0e0c031603020d080f0409060302030c0402040302090403081803040306020909 90
    0x1841748902038020032016040030754813901844829070001c0c0088859541d5401c0da180807482c0c0740c00c005d010341080d202c00021249800c400810020f051380946e00a203152035400c1291040401c101d40452290b4100420240e45900003c0d000817132010010300707603003400010800300b198042145071040309007051440715621001380d8010714016010610b40241c24110040c031034001c0284800400f034900d4811245401390ba6914440c0003200c80805d040c8101c00c03042c038160119082440760050150a185c100031014082c0c940032951008220b64004840d400030106406901c29011203044001e0104185c4c4d49050400341440109852400f94505014400c1c400c01a4074004c074461010404402e198861a030940d002c01000b01800402101c01420070400c031700d01e04942070b000c1c2005101c19000010800e1950041c10708000418400c0752042d4070400c02400142c0e250264250010b4061502502c540e071a60b42c006c0345a24081644400c1c0d1101080000070003031650000c00b0b1285041c3d410201d661 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 2916455 1250 2915205 2915219
    0x602070b090f0904050f0307030203070501050708130b06010306030c06020f070e0603070504020d0e0a03021606030c081311030709020714060601050f070302030904050c030406050916090c020102040503060a02070c 93
    0x40640c000c80c582c00700c02d8020042841c58118040b5800c14015800c1c0d4000310340b0981014a15032016008a02607000425200c050050a10907240d0003101420310720aa868034401041400460170001000880e114020800d00e0340b180d07000c107000c0d5501200f1a101c45441e40340180d41c0e1502d89901c00340a21032042d001c00c0710380360318400314000d0f040a401010039a08010810020350003107888030000701d0f6107d1140c40d890340108018001e15009130040c003c5201a102c0003010140e913500600203141c1400054840c6960005100d6440540340784040796015007403811000c2c0380c800b9560b2981c1442003090100d80020142c0c0180f40301440303500c074041c044641100346615810115100d90108000340700c1c02250884a0008241c128401e10650b032800d41d5101c002402c9070001d03079a1407400c5001004000400496104039038000311041c00400c0c49030b0400d100016802018044c1c6c10704140c0716165010204d000750146c4014210040590f445c500c2e103c0c1b190340003034111140030b40f40d0b00c3c1c070980300240c06 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 2917705 1250 2916455 2916457
    0x90b01090501080f1c0c0201022104080706020109050307030c03020a15020c0c0102070e01030807020a09050705090f0103090c0611010f0e01050627070806060903030a1205070e0a090c02010e07060201060602070b 92
    0x4070156040c5d03014030740030102d000d840c0d400620300b013641980181c400c03101e58403065501040181d240700940039121400c0080540c60702c69250802000d6a00d8141e0010201c0e10010a43c1d4001da4036291512400505140482c10100010340c01448403103810350f1221001d074607401030421101a00e00312800300e01c22000480e583e945034402c0741c034150070720001440070441020040c28170702d0001e01038500c2696104503410880f1012588000000c401041402080c03800008500b480d0000746810700544c2c81d245c4910509251901c00c00040c0140c0342c0f259241326900707400c14224034400c03039003c00c00e9110307001c05d4501802c0210b0790786100d0090302d041800c214200440300c0c074000740c06e0502c616003a9a100c40548800c1d80103002e1a9010000780010382290390200f006007a41c140aa13160005c1c201c491000b20107907a406083c0c0001e0103011031514400e52164404c0d2005c031a103d80012131000707034540080c0e0040c0210710030324503107000300710340450595015003160040341d03402e03800ca4000d0b56541c0848051 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 2918955 1250 2917705 2917723
    0x507080702011107020a090b01030207081801020c01050f0306010e22090506060102010c080106030506010311030702010902010905040b01020a0303090606050409030f0210020301050105182b020a050607020907080406090b01090501080f 102
    0x303c1351b2002c005015106c103a034442968890103050044c60400d00e41c407901d4940d00700300d00d6041c0c0a00440040d080b00d590600c0300c101000c40a0034014202041d041c40804580802043e01c6c0c100806203102441e16512218910b504881001c1100c5402c141c0c03413502405070803106010380d540d210b54000f164940d40705100d41044011180d4580600b6403c0000440141c440901150304042d102c44014116403154030045008000329000080c2c881820f00c0050f00b07904d01a408030384070300c1c5456030030310141e42c001c124003c48950620340041e5003070551502100070041c7d42c1215800c549002c900b9410990012301036240d5038025003c91340009600b80c2c100c4241d00c0240501c0b40020402d100c07010b0308803044225812407880c0140340d10b5400008003080c900d100b0420000b10401da034181121815802c0620352100034150070f5030803501d03040f0103401003804010f01801400400055030001402d0000340d500030440142e00c05207541c06540d5442911014000078019030007980540c0d10841d20080340046c04003c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 2920205 1250 2918955 2918959
    0xc060f03040308040c0803040f0509070306030c0b09040e030417060a05040c05060f0c010c03020a0905030705060a081003060501030506040c12030804060c090f090f05010515040b07020105070204050708070201110702 94
    0x4596030700e40d9000c403850040908111000b500400000c280214240041d03c0540080d0340c40400a0703240c94100708442e48041c1040051602d03065050000c40c007860070860a50f519442980d85e9a843e0b1804580102804400c101c00c07400049400f060400f00c00041090340d5103d00200e4010b0b07112051030350101d4406a5004144408a000421180c10454007824080fa092400340d030909420060050960300c01d00810b50010b5400103240c4480c5411241400c0039000030707030081600609040205146100b0200d014040c401c0b0b02c800910030303805080f0113101840e80b190003070050f540d4910300729036510401e89041320380c40b400d000d01041400c024a1500390054140da44c0d417002d502c0b640c40c0d040040254400700c0e800c0122240c40803509184ca041040000c15a81800040c410103040d05d050880d041078004074401d11901c41d5015130800c1c00000e50f401d03903c030280025278406040c40140d49501c29003038000e412078200801c01c0161500180854420f0142d60000d010300f004c07001019901d0321541000035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 2921455 1250 2920205 2920207
    0xb040b012a0317100501110a0c0506030405030405030d050301090b0d03020309011404050d14010c03110301090e100617011506021506040e0604050303070906020d0903020103050702010603020603090705030c060f 92
    0x1507402948400c08010700e4068209503074940e00032400f031030345440102c840c42002020b21008002c1c650b803215196891891074000743c0f098400640da0750440039400d200b0b070b0f44036505c0070000c40c0900ca424801c60b801007000a08030b820002d106180500355410034811500c00302c0c40e00c0541110b0b42002d03001d0b4045070ba4140d0140d49080348030401914440c070002c1c11303181d0b145400e000105040d03d0b8054401d000d0b134001c115048040e49481040ea00396122a44001c0416041904840f625603140b0181c905480c4031480118510092051542c40c04510503411220241421310001d80840582491103003008100000e00a00c00c403c035440c082c1c1b440510500340140d11541d40d8040310317464188003503004a0003c00200e0b02c00403407100f8500c0c0000070340b006c0d0380c00e410010a2000041e000700c140c0303000340147d001510740303a00100e0010300080803500c00a41499290000540142d100b90b000c00040d41d40200401c1d168101081515603480350b0740140d40c000c1c4a90350202c1c0081c642081600e5442441104107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 2922705 1250 2921455 2921507
    0x2010806060a09030605090f0c0301020405010906120207050d0804050c03010509030a0e0609040603060c11060702030a080702011b030c030b030105040209010302041515030203040c14150903030903010e010b040b01 93
    0x40070742503000d00c400e04100b01407441e0100004509016081c05064000001c0c141d5906110b12217003409469221035200303030f01c10482044542d0300218000202c8499040040c8188aa6005140a48140c0800620700e024185490000e560400c285030300075400381085800c5080c540d0140b500301c0d1015107104100e58030034010720101038402d4201188942028110f1803c001554002c141a240250000c5804a480390200e160543d0300c07126441884034000001c00f50b0b82440c10000c1e440c6d00c11070203d1030400045000140d8605c0c000d420003120421035071030380d07005600030850003001044416450000607061514010003450140038481c041c94005011202691035a820040200000c050f00303440c40c201100001003130b540303860b00c40c0e400d01d800da100980d4915146c0b5200c0303400002c035080411001518241003c4d10717240d4010099011582c0e0003c29664008040040c5ca54010000b0b519070540c20000c02102100c0706400080c40240107403418013611003100c005548480c0e070760800c181c2c41c041c52480 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 2923955 1250 2922705 2922709
    0xc091403011a040e030c0102130e0c040609030803072609070b040f1205070308030103030c06060b04060813110d03110106120302030a0309060209090103050d08010803031909110306040b010609050402040302010806 93
    0x801c20031321001c0c600302d03458001078442c4a400da80103034845030341d030081142007000491b40d000d4410742d0141006078528034003414118082e00201c81804042d03c9032802200007a030203400740707501280462030541d40080c004070511482510040031a0030340030b1400f5240740060142064002e540a507424403039180202d074108040008103131030700302c4203071864801e40c0e01c0000030a0704e610081d40039501035520f802d8402b0840c186103007a80c20b248d001c0e00c13684030104000c2100981c0808115080400c90724207035946d14060820b00039810b041050311354889200b9140100701a08410501300808a14000703200e859a100c0c0f01120ac10000480a40540c00812044441c184a940080c96861055000604000ca00c20101c0c0183d48260012102e580c00f840c0c1c1d21040d59000400280100a9140198658640300d000c40d88075555407185e0720742c8603803a03102500410440452004442401400300c41a51401382099081407500380b1950000c1109048003150ba0704117030085a00b0380e6010707128116140c4074181 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 2925205 1250 2923955 2923961
    0x1023040203070b030106050403050705010c020a030b090a05070602010c020c040506061207180303032307090b070201050c06040503030714030907030b09010b040908030601020d030207020901030303021c0c091403011a04 95
    0x100481e407502401d4804551a044840954040e02e56076803040e88650862500ca80f52000d56004241401644c0c140700c00103a44800ca01010350f540a10010030385d44550815520f40191650000c0540c014080701140302036056102c6050342d1030035401c480394100464103203c100c400c140c940c681c0011080040b61626008104d0040d0001010318020203c0d1031448850b00c0e008001e40c0007100060785a089900d412100d54111100c1e01d1410300c2c0003000e07410300141c0580495814814403080a60104454040d6801102074585014001d002d0314400d141c1071a0103622907004580e00e60204d41c104a00b001d204580710240d0744982c00070401000c1e000d0840d05d0301c0d060003000510701092592642e070703800c0250700d540c040e0071398841c85500826100d00f88a400a41070004003184002018130600c0603030096683c801c811030450303400d070400681d113502e41c1d10007060b880050958901070900740b403008600aa80300340b000d03003204d521352038074001d0400b1501010300b40e817800c5040c65180107000d888003285250581c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 2926455 1250 2925205 2925211
    0x606040614060a030e10050408040f0605030609040303230a0204030605010b030411010806040e0d02100506010c020f04020307030204050a0311030105070806130506030f10060801051501020a03050a030603080403141023 95
    0x20440d04000046e51030314040d07130002c86044800180204040040000083d104406010141080740c11071400101045140750300600c0607040540341c0b048005c1d0709801041c0081c03490410610031034107280c81500d0002075030052104880c0d16107081d000103001c80c102400d49008a40c0095807010168984004440303006000e403955a0255483ca03804441e80c00402c040070500c60250040c0501032442c2e102201210001010103040c030a602204070010f80d00d00c1000000340c0001c860050300d035200d41608500030b0050343c000e5130700319076a41c0010060100d034000d852441b80044009010554922404640f00700302510090b400c6078a101c181e05583c26527800c041d90019024040720501d168040c240c80c5040c42c0b240c0103102c41e41d50f5000600c00c49400780110f40d4032040c8105108041c0040c040000d540b01d0a10501400300314000c1b40d051982d512940100340210b4216080e980c860344c076410110103040f103910107020307035128110b01901d005026001c1c42c05582d03103d54601751204030041d00280000001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 2927705 1250 2926455 2926481
    0xf050c01020d06030614060102010516031d0723180112050f0102130e011401020601030b07140a03050f0a0b0a05061b0a0b0103030207060306030809060706020c0f0606040614060a03 79
    0xa000002c5044018410140203500402011a43c9440e100400502d0400034154a0459044c58100131b8949411190760601e82111310b000199640d420410061140d19188400860b0250a41c0013070070811002040c1d000e600022105080324a52004028000c40d00c0300c0c0081c4052410f200401500300460282400140140b09442c5401c0101003640d089a0100a0100310b41314100400d102c0083d034400d5403800743c840fa030b15090140c00c0c00e100203951a44140300c01030409400900103a1140e2060308801c0309484049442502c50801c030802602402084503400043d5407060005084803866025110340007a0280003c0c0d161401e0000b03008156011860000e030300b048025a550114ad400c01020034000d00501b15400c03e0b506500d4020305010b0664010002c042c107019081c070204980340202c2d42d1543d01140c4a654411103850040041e000d040b801c03064034050800b800074880c1000c52903074414501100e040000310345449024126540182c040b030b030085000d20008600900a40c80003444402c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 2928955 1250 2927705 2927707
    0xc01050f07050601180f060503030d0b0a0f030b070f21050603030906040905010801140c0a081504020a02010506040c09030b040b0709030c030c050f01050c060f0c0d0c02011a010201020405010f050c0102 88
    0x4a4507560f00d000400c3c1d0051680940f813650304000b000c280d10030405074000c0d516050090030702c1d0000096030380c09800744d0540c8080c1c0d5000703540200d6842902d071800801144d004811042c0d520f0805941d214412030708840864000480c02c04024450107440c8400442002040039420b40c10015a008242c0102000d805210408c1500e10a99400e0041c00003003103941000300b441e60620420a00b52021200c1844092040c1420322480c00b003240f040c2e4241d6a40fa00d0801250703034508a442c408008088103250f080340c0b00050200401d45d064005504c559003d032420700c41c00d019a030044448035013900c40030340307044c00101c003207400200300f1111907411030300c03515102000b01d0302ca4607007110b8481c8681c82290400d44c0000200b203941840000e40c41d11a009080042c200380c603602030541c446030000c042c49a06128400010031107210301003a100442000c100403c01d506c1c43c584064000c0c68400f403400817142c07040828a00799071050084a003940c3c9d0681d1400b0301d9548080094425820850224000c0c0d50 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 2930205 1250 2928955 2928967
    0x60609020c03040311030a0b1306090609050105040201081506041703070210020303090606060906070201080702010f150302010206090f0d0809010908030403030f150803030c09010203160b0402030d0305090c01050f 93
    0x5490001c1d0a08408800c0510342e9a407441c6480001d038202a07015501030307044405000e002c16910890a0f900c030704c011a00d10721540603840c1030802407044000c002c0c602d919083c120400c1c00815440203100794401e8807004003c0e00c581590000c010101c00030194000010007060080d012105030440d008400c01003103908000d0f15900152210507210703d0720006900110030445a950200b00542e00700c1e03026500a031034400742001040300c41c130407210060305210006012518451003503000c600c5e52307050044c08108098800d21a28282c2c00244405ea00512804000c6080b002d070210350141c042c1c1c4007100900403203055a8041d290711400038038030501c0d03550714071f00400820300c590000c600c12846542d0008500010741c05910845222003410304070341c90501d50901c081c034000421284c0006444100989460392500100c0c6948521020305000e81c401030f00c50002c0091014003680294402c50a50700d01043c60b07802142210307011030703001050780e00a807580a103950144005084941c0705042482c6401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 2931455 1250 2930205 2930219
    0xd0c051207050303042f060918090102030106020d03050c0706090206070501150f0b120705090406030204060e0106020607020307050705100309140f010b0303040501080103110f03060a0506010e0d0206030703090606 93
    0x900701c11001da0311600000304100402840205404407007174101c0a040600220400016015241c065100d00605000804076000c0d0386450b0503405260b046d444c0c004103490007000c00d5010390028450480980304804203588054000e014040c03092141a1082c1e04152031902e41101600000c1001e980202c420001207000c83d0b42130260110307130f07294243e018800526059507000021502e5125143e010f506004034080c3c200a007505075040840303460010385494650300050011b08050b40002d40c000c0c80c0040c0002d540281c402c0d024102d031210340a5500030780d502901680c8a04c121a40101a40c11154043c81685801841030241c40002c0c500003c2d400d2142d81c500d00d00000c84182444554020300c55041c1c0300c00d090007040c400c040281d02950800d403921001810804060000a082000030307052040f042d1103403200400358440c01400c40740340c0d0400003440780c0200025a21140001c0b02c2c0400100035080002c1e04507850340c0d014114620f0366031203100c120014201c00784c08843d02516194001146 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 2932705 1250 2931455 2931457
    0xa0314040605010e15060307080703020d060303030b0a05090105060403030503041104020c0114180709020f0d0c0c0303050903070b0a0b0f03120901020f070e060d030c060903050405100207080d0c0512 87
    0xa14414100000c0d80d5040c14004032070251300604c2502000c02c05041603a0644500c2c0540344c1145140c11304030a140c4500e001980071f4000c005580203d5494840b0000c03c3c154560021141d0b08000c0d22104495a2507009011020509004094001400304010400a07104100540d8854003401d07c9038007000814002400341d078450b054490040c0e4440703a0035200d28110f40103154010b4240c5c500e40c0320790072510b01c0c4a602c4030014407400d0550b503400b281e07502140050004891a10000030001c0081201c1a07001070030382e94492405400181c40c000004080103000400c8801c500e41000c0c43c0301c0070366290120306000e8003200ca0015040408035041032083d0701e041000c3c1c0400ac8944c191a500e42c0c1c40600020b140900c0034042003050b500c280000c004200362904241d4100d4000d50303400744044000c4c2015204001c1d000307001810145402c044109056000b409081502d42c2212214541d5140c0700040707a803602c207030140d6000c0360807503015164003031f00600a0650701c600c0b81c420b8a0100c800346000240e5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 2933955 1250 2932705 2932711
    0x20304210b04080a0f030b0109150207080703050607020d0201020906030402101107090f0b0d0f0f0512040e07030606050c07180e0f0a050618070501080a020c0109050703060e0102040b0706020a0314 86
    0x200f040c0403654407500d5401480d001c081d00b50303d180800c94402e40b00002041428244183e080602c4000b43c4000d83c01e10a200c4407014000140031190842d5503417500c0b0b42d8400c42101e1a44c0180903008a60000c0c51040c02195110280103002d113045860301d400f0080300c5102c8403821428800c0c10292516100800d00151005050040340059101d2400194000350340440c03110038424400750035400001402c0d145145281c903080300c51403a00212918000d8600007045c0c40c600601d01e404a00050742c00d0184400b0703413203484640c1d028020150303510700545182c0501c103541503450b000b5403010300455080e085a027003892b00403507020840d2000314050301d040902c3c2d00c4620450390002c04068003844820040769030007000515120f01050b410448141e29022180a100e04001004011940804903038058604d95001c04c0020003480b011850810703a107109c5480200c13080ba0801d96024280001882514225108441d00a1500c00d181d81e03084000d51040a50105042c0c0d54146044000c000b4051148 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 2935205 1250 2933955 2933963
    0xd0b060903010c020c03060705070c0911090604030c03051002070302060a050606040f0b070b01080f030d0c03020403120203030402150301050a0303030b1314090f010504020d0f02030f0d0c110303030601020304210b04 94
    0xc0c00c1c0385c04d0410b060030300300018030080c24440104000340004000c40d00e00c200b1582918400a4032910f410808103031845013885003580408041404000c0c440b001d00e100080380c0c8544100c40054004000440a82c00b9240d006000b5810000000e94170501981009900c0140200301c2c9140640301c442c9000c0c090f6880c2c0215100710b50102d030304003c01c131071181c0c1c0d0383c050081c0c7d90080c4000b890000310a5980c0c4901100b015955484003e50303890f4900030f40655010b90307031000c0300345c0e420281445d000390740f600200c906a205400c41a41444441642030031a8183e82d030240841e0449411610260040d240c0303500502e400042424002c10040843d01c5280380c2d0a404100300300503404cac5607224600c2d18158828005c2d5691400b414440140d40e140f000d1101c3c603a01c01c8289030207685900000b82002401421900755009611720b903500140e0100e07050740d17140c1c41100398007965080e2078103050b540e000440da5075000da441040305100000d80ca40801259441c03c0008006880c100e9846000c2214240c800700d07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 2936455 1250 2935205 2935213
    0x609070602010609020903071509080a03080601020d0804020108011505040b03010f080f060c090f030309041103070201060f0305060402010507082203020406090903080c16020303070503030604060b0f0d0b060903010c02 95
    0x400300a5080c040c0d04001c116024055080144420009031180c11500c10860007107501d41080d14018040e003005001002c010050f694a051030741000341c1203d408030b5070603005002e41c807030b104042401005070500490301a034403010544c0c00c1403618569034080c08142d806101050000084440015004602034442070b0408000189054442483c0815001d104002e50700716400b009582404241a00c0c0c40038401c0b07460181c144000000303c0e0543c0310707c0200c540c20909100c1e40c0c2c9003e1004000441c05010b49900800c640d0b981c808480c00a141d407400000c1040c0c11420110300550702c55000f03003040764080d01c6c1903454685810300c0050203008002410001410000042096185c54807038100284122441030050355050b550081851000400c86400c180004c600c801c106012130811380100f69000d01107996518690911a5503508211910303807045003012004a004c004520a0340c0d402030581703990300d08110b0641c92000c0a454000010754004006104104080c0d4090243c0e202e101c80707a0300030b8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 2937705 1250 2936455 2936459
    0x5010b0f0102030c100506040902030f010501050f030109030503060402030703151706010e010b070f031404030f0c05010509030a03030209010c021c03080702010507020316060204050409050d090e040807030806030708060907 97
    0x401580c500354212981950000d01480e883c2050100704041c014001c5880000d0796580c200004008050360300c5c01170340521900074029034204055110506032101100da8180340c0d100302c010582031300d44000d0010000703241071020901c00d040c1074015507045065810301090b2604000080d00c0050319551044240c07868100343d40446640900c140d13405012a10035401d00c2d50b0400409031030b10b00c42c5a00003090200c10403044000d051148200c107042114148200380c5c5d881c0d8a0072f00c00d810b205c1d0803009850015032000e0002c0c0542c0a00c00319455643d020340901840560350301e041c0c0082d0010f074401070600001c080040010790314990003011000c00120840f1100c0602e06008001c80401002002568500703402d001020360000213440c0c462200c28907003000110940740c42406405070350700c2250064100b81104e402c10030701013000c606500055440802ca0340e42c40c445020300c42c40a41e40034046070401c100c06000300b407040c00c50541c00000982110b085655501c007103440d10600701c3da403c1264200c5141 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 2938955 1250 2937705 2937709
    0x303040b0a022104050f06090307050c060403030905011409040501090507020d0c02130e0709050109020703020d03050601080a020702030c0d11030d08010302060a0806030a0602040609180e0d050c010b06030405010b 93
    0x10031504910a80c0301142032414102000c0305646800c0790340f0707081e400e0000000301001001c10001182e80804c40c1034914500341000308564940052104a03610f00842c03440a12904000041e602166050364650701401d02d01401074a00300191943c1d442c50000800c0901c2d00b907281c0c0e0203864000c0c1914440001c0d01d291000009042241c0e45544004103c0c001c0d110700b001d0f175203032070306400070003a80b01000402d0b1600340c141034034113061980010030490500d1f00016060175258058412180250207444420011110403421290304032004d6020842c080c002c6006115181c2c0a002c450b44003034100c409801e040ba0000b1004007960208031900765207040b400d07440d0300741441820140e001d0f42c100300744154110340c001001405080c901c1d00c1001050380c0050344c5a03130308101100c070144d01300000b15922a12594000c1c030f40e621500a80b4102e0344192403c00080c0c12500c20040b40048020203446000800c00048506600103245030806648074403c0c0807040c1d1300e0070000c5001d6441000001b444104e0311007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 2940205 1250 2938955 2938973
    0x30408040515070203120d02040305060103050f01060b0307080c0904060302181b070201140702030a0b010312030605010903051b030c1801030b0c190309020102030d0204030308070201060503030901050a0305060a080f030304 97
    0x80b404005092050b07000580300000d48103203841b000e190481e1254000c100840003401341d5440500301e4850755000105010700455005488428500203009058440070306058600c803c0e61320400062190f000103850056400c0582080480100301184003943e0b81c00003003010111503212100b200130034051280706908041164000081010282e00f00f50b83ca400180425200a040850b0b0586c00034403001195001c0c03181d0508944d101c440703c0944d584900b00780800c1641801e0010101f0720380300c0080303078560148031200100da902a008021034800c103000f105410041048080e051300c03841c101601941d56200c060b290f11007201030f0440c0c881d07140d420400b0403080080d01071190240c041084915080e50022070b050501032500b000f244448091004034518460080490409032010402001b0564041f08060254036160f009015080c0c0380d4042545030700c56691090701140081100303009040c000c0d00844d1340018000c007400311081d51082242e08126041001d041d054100108210400540d00c07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 2941455 1250 2940205 2940229
    0x16020f011803050c07050a030803041208040803011e0812070c05040c0915050d0207030c03021b0303030a0e010b0a080102120f040809040e0102220609050103052502120304080405 78
    0x50000d2008090310084014150301d0301c00081c0820400041c911403185082015030f0003002d02034454100c0580e02e0a100d800381c0c0058408582c03004200c0519000a17100310b01040c025900018000c2c6180d2808003161500804600301c07103007072603250000248842042c45031028480c24030001a0365080b06241190700031b01d20741c20440c0f1a40c03070000c02410560303001c40040103584d001c02041c0d0000e40c00050689043c0102000030300b14a00000344401010303407007168010560720a4007140e481c08080481c0c1041d01c3d0700341c58040c0e0582d0040c000190548102d8000c4170400c86400000102c00400d000414003100300b0b038000c1c00141e0740001c1d031145101c400a00c0b04e94040c881c4103541c903007410b0680e6a40468800e01c00356521544d00c4001ba01c00c455420350441355080201d42000384201d440100b00380890444e4402e501c086140e483c0001015406070054510074984d000032405d49046500f50494440380c442c00710811485020b00a40e55a1041300081d4003c034002d40200b51030700d1411080000000d005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 2942705 1250 2941455 2941483
    0x5040608070b04060e0109180b040501080d0806040510081c020f0303040503040308031e0a0e07050d0b040b1b030408030f0106090503030306040f0e0a0b0402040b090112030e0301020d051602 83
    0x19400402c41c01624200351020b0b9005840d1002c062030303c20b00101c903954100c2c0c00c84c60520001c8415001e407144c29038841d1110f10010784041c031450b0f81e6848400c0c0c8a150024410011540c0c01d00021070310b14243d4480c075804922650401d415035107a01c00c80d480c000c9041c94240f90351441250b10080d403901088602c10801c0304100031403031481c09544054803800703640700007048d012000c00811450540c9840d0501c8070203070307004120a6807034001c501d200500313902002d44030503000d051004070342c2e0300704400345a01c8160032005000c510f4403203980301c1a0700710005001e83e030014081c10020907c000098000d6004501584600e6143d040000c2d80700740c00c1038107a00120900074581010411500e0100990394461070480300000c40403038090101e009004407600c126a6401240c144000b0809007035002c0c2c1c00b8600075241041006404003e100d5034640071b0080d010302d402507540d6480007900c1401101703541d0314081c001604000c80a8402c00940c0d03000d540f000c1161401d48000728495904100030421031480c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 2943955 1250 2942705 2942713
    0x309100506010504090c09050d03030c08060109050d08030a09020301050c040e060901060c060c140c070801050109090b0610050903030d0603030f0206040c05270a0209190e13110d08030105040608 85
    0xc18400030f03146108900c5010441031301c074060001924011001c40f0300600c005018001e08001504e401801044a48003110105403040d0100e25194860504141950700c09402c2028001f400d40b0b99099980000b02001202c0307403506288001030700d0a0084038011407074110100d07143ca04056100c4c2140c04c005041e01d000e80741d210700400044c0c1d0301550f005a01c0b90040c000044806103000110391380365507007107000c0718454006400d1240d000d00082d0300007240d80720002002140d0320b882c5420192184800003030200d08842011844a1505051481c3d4029460400c103140001c40004a82140c001c04020348103140d8642c810002c0c507030410301c07205002c021440907180d24501a42c0c0c1310406805809480e02414400d0fa20040c624075a0750184031495003040c3e008900c0c9081c0341400041d42c42401000d000d81c00d449002300d600448094001d050740d8100741b840ca40c6079038580808000c000c500005441038450441106450b80700c04401642040c01500703010707074135810311003400305488003a8426075031680 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 2945205 1250 2943955 2943961
    0x2130b0a020606010509010c0b10180b100f0207030b0f07030506010203090d060c09030203060103080a090f0608070507030504030b040c0302010f09080a0b0702010617060105040b060c0307020d021201020f03091005 93
    0x3078082840c640c0102c0909000381c4841e4104c0048441718107102000301320b0340c4100d0500014481600540040766102c40c480401181c440801d10180c03188502e55a810100ca0b01d0804900c80c0a10b10700caa0b40c400c00c1c412130700d4081c0da80c0c5442c00d0312142a1002070240c1c50f01001e00840d81e50500645501400c280010b502d000d41e440c003c03846a1201010240103030355582c5030130341e00a00c6014018001c6800078119480c658490501d0316003136100c20180c2c0c0208980c007800203072006846142e101100c1c919196000540e680354000c0d640360340010340403020494100800301c0040c05190f10140100d008038200e081c07075403d40c4000361400d0318404855051111444040200240001c0c4010400d6800007000c1e10540351844c05a01418454015030381041a11001038030a0000080d414120788003101c060180080410034012107101d540d11441440e0010030409015043c0a01074a444600c0941051403494140e00c043d400c90b003181034440d4003010008144400d800c0c04000300e40003045100e030704111a007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 2946455 1250 2945205 2945207
    0xb100501080402040b0111030c010203060a12020105030703050c090604030501020a08010b0c03040909050c0405010320060316110c090a02130506040e0127060b04030203060703060605030a020904090606030602130b0a 94
    0x10700100000e100340d440d40b0020109900c42e042c00d084211182003100d4aa8590440003800303504111007160040680000000d030200c03c84051030025070701a1100d919685514104502805000704580042c15041000c240d140d01c80c02c00503c015405600010307291035140784002d04140040c2d0203c0c600c4481444107881c20480032040b1403c0719a204000540c3c9074088c42c20500b03125078080382c0d540c0245090000014458880c083c40b00c100d0040442080d0b1565550400c1440d001c01d4641104010821042d011070364061a8810318500380c50084a1400307990100249440808a80b02e0160700c0d00414184e48102044d11100003400080341c03800e04007424882c81d02c00710b1034144a03013804290b0414103100a8030140e01a4080c1c0e40f8469014000c640c1c6543c103001c5680d0051104034020321802c0e0003d955180309100f040150760300ca5598a145868118955002c2d42003003402c568469076450f20007000403010710917440110b12454016854030f4041b40880c4d01ca4880740c0c80300308821400c2001140071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 2947705 1250 2946455 2946467
    0xa0b0a1406030709090204060e0a090b0106030207030906080c090d140c03011404060b120102040f05010f0203030601231b0609010608030309060402090a06030213091e020604050d060b0d0f0b100501 86
    0x5240d40010015000d9240d000280248c42c150f88428403100c40d900c00c3c050303c041c40e41c10400f80700c0e004041105490341d8440382241280f144000140000710300203018444544200e241070b8000c16500c40c001e0409040c840080c06030f110f2008202c3d5444010a0003100d0108148000010107500300e00800076060207210300310812200600003002a99188062105039460311079211200c40418021500c0e251181c2084200703205034000d05011406020a8601c0b076031000045901c030b0041070359224041850b01707034084403035a0b990000001482081c0704840185080394146014500744030000d0000e410700b4a0991f0844110740c0054400750010000c0208003940000c84a8125505031040d5000d0341d543c003450001040560002540700c2c51341040c0480040898000081c103601030900c13501d8481e440d43c4c4000c8034045034000250001020f0000708200e290090803100314038020b203c081070403403140000841045211101302c8040e40e9092102045c45610760f280d179408081c09140d042040d00342400a440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 2948955 1250 2947705 2947709
    0x80d050403060b0604030807060506150702100c05010e0102210c04030506070503040c03020d0305070606050a080a0605060a03060e07030302070605030114100c0b010f0519051503070c050a0b0a14060307 88
    0x148640f1420744070070039260f1604440c02075070011401c0340c84031003074603294000d480300380ca4030b5110745051007000951100c40c00491392410b600400c0081d10516064040d40c01105000381541c06540e034031051040740600780002c000e40410701c04c45e03c05040000904109034080a17246042e45c200c1030105100003a000203030182c02203a641000b41e180e549918111039458819000290403240c800d80480401d904a00540a524425401844410f4449040c4501803100b44150540c9500200f03041c0003046190380030940280001d424042100c0d101e40316242a070340d080c840c480c02c99000c5002007051583c1800240080d001604c1c00c03900d1549060f651000a4a006104070321600c603040d46500024060034410b14559480840b1002c203603590360020b00310a00341c0c8100da000d000020341400c84105111140c07815500c0040600410001b00c52951140e5007000342200c06001110740c029010542c1007111034211072146400405038076110106078159814910440b1440da100070500c90315560104010741 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 2950205 1250 2948955 2948963
    0x1b080a0207030c0f050c0301020703110f0d09050418020904030206040201080f01120201110f0d02010b10020304120813080105010801020a031406030d08090309120102070201030b010203040f03020907090305010c09050307080d050403 101
    0x44c1c580503044c0141405c0d0a500d007242e16610011f940410075800c05401700010280909071807840c20140d58483d02d446510200400103001000c1c2401a89003650200c0207851041c1a2500c811100354041009000169400e5026034401c204000c115039208403040d81c88034640340030f0348035545008080200d00d82c100c00001e052002040450800402c100440c24003c5200000c03640c417041070038000b90007800c5400c40d20340079403844204566400e000104070360846460104a80183d0000e803a203d1190308595130ba440811000440081e900a09000d20b5000c0c10400b0001a44d41e925800090222000c0010303441a102000b01084001e940201e4480500019810080a00d0703440e1a0b61605512600745003076802180442c0d8141c5000c0d0541c064039190f8800c3e00d0810900081d1001a650381c05103119041061840000900050400e0030050b03822400740e081007004603440756940c9080d500340117000400130315035403002c1141d486c0401005004003105000341c018445000c03c0108907104d5404090 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 2951455 1250 2950205 2950223
    0x30304060b0d05150f09070605040510020c0a0e012301050304020405040201030b040e06010302040e0303010803071101020304030b0a140106050a050a0e0a030209011503060b09060a03090203101b080a0207030c 91
    0x400c192555040000810340c040701352450380300c001c2c07402d801048040d0380c82503070508918005804120005540b2003914100d407240c2d41003901d031408001c04c4c03814203c078000c1140101400d581a03600d524000c80003070b2810010f005030560500e4100140c2c2c01e0000140718230040109021000c41e40c1044c00c903900150180c501194554460006030064400340000355040707071901103420824400841c00c4d5058030320884040c0840c201c010605c954a000038080d1802d40e0308100306400026107859154521030714107005483c10b1076070365180c419034080120384441107075885d8400142101c010600311809806903040260602c0b0002070018101e0084100e003005011005032016100e985200c0c0c1c0303c004641c0101100490f603190410242c02c41074140d02d2501290400c2c038085540074811054850008002d030070705061060050085000e44658131082c0d0f09401050044140c00c80c2d64000c6803002d0362158841481c9690790f40c07005188103401015004e025206205d8900000d501074a0003013280d170450518 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 2952705 1250 2951455 2951471
    0x20102090a050108100b030106090602061006020d08101503020304060b010305010f0501030207050106030b15010906090305030f2206050a020d0c1502070305040801020705010b01030c020604020109060f02070504021303020f010c0503030406 104
    0x444178007030035004090b022802100014016610441540683d1641c3d42540d85035104c00c40c6840c3c07240039900034440944c00840401c0b001e644140511036111600000648505560709001a0030789400281c00c0d001a07000002c000c1448254050039218007800e2804212941c904030441008070b801e03005503030406400182590500c1405d4000c00302840e045003007c1010700f40001d141001c50861100e42d400b041c03002800181c0e581c080c140c0c4808494214016501e0030700070100360100c035445030803e402d0445411442c0c0a20304501901500601419200d4a956016074540646401d071329009250421884024403000138142000c01050000681360241c2c5800981c50255610700498110b0403456102207142018840e05401101802001783c034104000c20f4900c90480c0c680d83c1c112406404104040340030410507200d01c80c9101c0119a500c103540907075131210001001d0303034082074424440400c40d4209006516066440c05010a02420450700c0b10070b050303031082d840c2e0000038005094a5650021 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 2953955 1250 2952705 2952721
    0x50703020d050f04020901080303040305070825030f03150503070911070b0709050a050405060d2612090606060301080a0b060303130815090303070903140a06090c1401020102090a050108 81
    0x1901d00016007060107001d2460020780c11a001402250140d1064850000010300c03a100407048901454041d603415140c6a4280c03556203d82c0d001d0803584c80b1a00d80100041c2d0f41071104071540d601e036803023962002e030504082d00e002400d584091741c6400c5d800c2c4860802300040c1d54001407000c11242e9000011409404801c1d2220550003409000340c06160440e00300450302d60f01c02c00c0b1009071441102d4414000f500c400c00d100403903030f08903080381e04a0308400b500008a0075107110300940924004d02c9030505804030b0300300715007034000108200c80f001004003801403030101842095030000041d6650b50956141c126559550740400b10083c0044c040d0102107552030724140100d42c0440e122003d45003045a5940c11700d903540c0d9282e81c1c515895290707400400c0c0c0019011003100d004100503548c0d502c529046445668110440502c0300800c1d11804107210000741c2e1030f008000347c1500940c625502e4901e000e01407601c0400b03c0c070105045901c1045940141d5580c0a210001d5820a1a082d00956a0520 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 2955205 1250 2953955 2953957
    0x6110304090507120606020102160303020d0b04020f070311010e061902040801111801020115090b0609030d0309020102070e01030206040303030b01110a050c0316080a0f021504080a020a050904051005070302 90
    0x241c0406814041042000307a0020300090180c00010300800c105640c41c0003c900300d004031107805044099241c4140e011038481d801401d00e0070f450f1200010f042d100a000a0f00701ea129124002c1c45120120b6540141074010141030380002e48100240034501840d01c19648a11004207105608607401c2040c644440d030680c1a0b8001c0d11500c0f00801499162000003640c640000d80100c00504e00c1c0d4100720884e51040c06603900203078071213510141043c14000d440001e8824641020f400c4003042c4007208080c0e408200d10a4045890303100010042c419000090400c1e6842e0420350003501d001004100607103860301260304990300740c98001000c980302c2004076030391000020595194864040100c090260100f20200c101e0012030445d041054291140c62142156100380c0483e0b4002d00000380108001c003085131660b501c0203080b00d00c81205864410107982254000710301660266160100b141481040d04003d09811a00344100385850347d51560f888455030300c000711040e11032010901581c0650 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 2956455 1250 2955205 2955209
    0x1e040b040f05030d180212031903021e12010806070c05060601120e0604030215070903020105090f030102070206070b0a0501060503130f0c080304090b09010501030c08010b07080f0a02011a060a020706110304 90
    0x8050010b600e0b035003031842500350b178005d0a03441040781007240403907140000308840003a2000c00d01c40e00c011400b00010380c001d4015000300403807101204154000e0410010003040800051041800302c0d504014201d440e1060082900c0d060101444950001c1600024003580c0405c09107085194828038101c02c90140ca0803116144186c8140d50030700081640100701d088100103c50404e074082c0e03898107000c40b0f04501521000c0d0208508102e20ba980d03090200c020380941c88060009440c208450b40407410b644d0018030140c0b2480b000109015440542e401040c1c01000740380391560950a017443c0c3c118802e0400340c401010424004903034000c1123010b081c040c008082030030503070341c59560344e01805d80a03041c01d2035040d00c611110000031a0035130181c030650110a4142c0d81d002266800c0100c00031296000480c161600d16050022a089260f54402031503d007403254004180100f18050155070003036a0250030f80700e00e0061080300c00045d400180310044984618204000051b5038100c181144615 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 2957705 1250 2956455 2956477
    0x408030421020c0103050a1518150609080106060206010501051801031b030903031103010608190219030e0c040603020f040c051c0506030f0703080306010c05150109051e040b040f0503 80
    0x1c0000c1d145158020509090300f2400b030700d0a11032580c415684004951005082a0110a29130f8060125071343d140e50f16086030100c038800140e1084000800c003146041980b0480016205000922104038203009a000528040c00104241e505200c0040c0c0a802220074949000c906441c040803280e100c2c1d0840010040c203407000d034958101c81c120050240c510301d001600482e05000114821358580d40071a4121910f99590415503107800d460314484282501d02c02e0b100320f409000ea069584c0e95003000c900f800e6032644001400f82c0540307409904001715030a8030b0384541c1c60f00c0c90400260302c0d0044908046142110002a418185030040d40d9502644c0301e1002c002c82124030003400d4000a90001d030244008030b08903007255a0340140655100c1460100408c090418008222107500451402ca02140b140d815503082420340001200201000d0703100225068407401803003e1410030049c1c0101c0e081c49026490450f141948403030a001a02810040446a4424240c1c0910a0034003e440380342c681 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 2958955 1250 2957705 2957753
    0x6090a1e050403030e010c0507020f01030504050a0c0b0304030f0f140c0304030c0905040b01081204030f020a0306050a150501020304030519020a05130b010806040504021c080f0a0903060e01020405010804080304 92
    0x9030500030005d051320307903010006602e020740d0b245407180190203407407000d07600402c0d05009000340300044024240c0900203e85500c10001280005024484201e015240f14400203850b403500d070030000c0691a4843c090028070035a0b2400803d03142d4441202c80941c17407000141551205103405813441e40c0301e954006017012800b02000304642d10150480d502941c02002c0030404c990725048003a0721400c45420100e043c0000300300c01c000081c0f0000410307402a000400c0044010740d40d40780c04003998012510244225561040580c07104021340010010b00000c2c4015400d00d030441d0f1790150b90305094120302050120f221003020847d40d030441400c02605001c1d06400501c0e92000d46140a8030303503045c5080c04152144002500c070308bc035101d0b045c81541c0052960328854178001c1d02038502084501e0580b00c0c0f901c1080400041e00b107040003480600c0041d901d40c000d2500c1d5083c031070122a5218140c1555074010441040182ea01c441c41c039401c503400403e0745a50340c07601c0c50014010740644040d0702c0004a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 2960205 1250 2958955 2958961
    0x3080403120908040801050c040e0f0c04030803040b0601030501062303090102070f050607020712020904020405040501090206040f05150307090b0a0504030501230a090302030414030f1504030f030506090a1e05 91
    0x10f6503101030011100054024012500c0b240400100c600541c043c06a403800300800244002901c00800d82e08060150702d0286071540382e490b50351841d0f0003144c0c00e8401607078410501c00e007540e05100715801000189400003180c04806040500c148110240e03078a41c10780030000c641203c4003941224070070380d4003000c00040c241c91071422545581c03084400f2809800ba0240002d100c580802c0021400e03607004080008940c0c0e60f42c2000018007000e0310985076590b8416440707005031140030050000e0705160080405180c0f07050f0411030b0010155400311360344a002d20501540c40d400c40c1c1120180e41d420032426803104400325080711180207a501c0900f9a40c00d100c801e015000ba44588030340c0d078a4481a400c8065516501c003041529000700c00100168010041003104d13189c1d40340e210048150040c1658010104d002845160038118200607103564201d100740800c046d0001e0303845450741101d0800780114500100099480c1c00010039032819039403903d07041008080d6070917407800da44120900801c1241 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 2961455 1250 2960205 2960213
    0xa0c03030b0a080d021c02150a0b090907050a0b13050108040f080708090f060a0f0509040b041401050405090703030905090601030e03030901060303110307110f0402040302060703020a03030c0305070507030804031209 94
    0x4504d12406005809078025481d07601d40d00101c48900200c0704d4004016124462600c90032142c2c000300035904143d82e40250310540d5603180210746c040c0303180c0c10041261034204003c02660b2212980300c2c0042000c100041207120101800720800c896090030440419503503801c1c501c01003011140300501b8a003002030450100400c04014100384a010307102107404030030410602ca080e108004840011802490485000600c2007004200c0d4001c0688081100920135000c41c0588010807248000700e0186c0c0014021802e29100d01c940c003d01c1030004184440c6035071006415030001c0e0044e20b00175407902001410380c0c0d000750414600600d811049990300e1a08682d0f50b802400300b40800c034009042e101d003a106800000003a180101c1e0031103423002107160840100003601d0315190301543c20940074000000581d035003e01902ca0b060182e0081c007040c1030980b4004084540c0030215000741807a1030140515994040d0a5801499150400701181e44640c20140c0e0760400c407440443d03c0341d0400b85100100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 2962705 1250 2961455 2961463
    0x408030403020616080f151008040203010b040506060301060807031104060f020606010302030c160204090b04050a030e030a0305030103020d020d0b010b0706060801060b0304020d0305070b07030204140307030203030a0c03030b0a08 100
    0xd28020303401e072807281e00d074060360610141c2805a0ba01c005184940801d10042918502c680c018000b20740c0111050b401c1004101c05400b8103104d2000300d0074400400080d03050a0044040d041d1040ba0204140d20301f520020b24a400107000b800100000c550000740818080e0b80700c81412840009403540320fa0341c89000604401c00001080010b000d148045882d40d40a402524050200d000e03915082c10840385d0038a54455500d101130341d21a032245003010200e03070590702a602650040019000380302046c200a80014800c14030240643c1c00164018042580082540e06581d41111807180444030b500009203680b0220300054001e1490400000700c0405000041c00c0f940d01c80c15040c00990303962598242203460600c83e42d00749200070800280189840390303c51409034441c0c01c2c0241490010345411003d50000c4844001003640010b00740510390350300c100404241001c8001300750311419603021a44900a010300c0f00d05103c01e0407582d00c200350180e0010b41110768080c1c25507544503070f00c100080d03407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 2963955 1250 2962705 2962711
    0xf060b030702010e06040b0610020c10110d0f02060106050d0209100801080c040209030703080a05040902030903040311090402010c060e01060506030c030f1b0307120608010905010c02060901090f0209040317040803 93
    0x9980383c80c100207200100805c20b41d05c0b454200c0006444c40c0e51b15020702c500218442d104804601030740ca002c04c4171380d5a104101ca80300300700303584507014803201d4021a032900b0f00403121441071150940302d03142410b80c0011441d05442152900580355401c045050000e0b0040d051002d5000a03941e41a4100c1c2e5808940d060480b000c034011500f000c0300507020702003240301380900141c058221000c02e00c04245c01c00b0062101941a14003189003d1303480687d0800c81e00180c58050064000150810600051500725021820100c58151882c1026400038007040000203000740010f4031120032840c03414003035014800802e005002c5690380d25245030200082e610407075030390445240704004212058801e1101c4c105000210704440d20b50303244d41ca0296501144544880c01c515203541002c84c80107400c3c050000042d100b40004184000c1e620780c042e0400d1402801d00d0140c0c1c5c0350900010109004440c94805590150303000c1c1c11546a07402e0481d0a6a080052440344d030b400386061004002c001d01c02184 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 2965205 1250 2963955 2963957
    0x30c060605060c0303010b0306010203070f0302070810020a021e01060503070602010522020105040b0d0219080a050702030a020706030f0e030708070606050108060906060a020a02090a0e01050f0c0406050d0f060b0307 94
    0x40035503160020001107000780c0c95405519071041c0014003c944484005542280c4140101e9050440e19a40e4138a00101c181302100145c0000d5010031000c8030130891490f0707030386c800481582018200c00000355500f030400d400405840e2007241e02980382d00c003948190054540902a120f001d610303500060301a18064030040c0250440d1001a02001c3e0700e100e4584101c5e40c141d480c649803900e030201d0b84102d5005840e5003000c040d0308000c040c00801d00e01d81c080c4003000080c0c442c865540f030911425070071600018501c20954008000c81e83c00c003035010807424141d95146c1000103219010701a00e10003407003540c003044414880012500309101105e0f019210342e41c0304120030b00255443d1801120461401c5d110a030b08024448085070340ca24005000c1c2c962180c1501c121015004180c0001b003450109542d14507140d95182e120707000740007003030141c0c5034002500c13064000d25040c40410494240300314814070b410801c0104071184291043e03041110841c4040c101405156120000e11a15a0007512064 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 2966455 1250 2965205 2965211
    0x15030106060e1e0609130b041b1205010f1206060807080106051504080709051503010507050306010e040603050307030c080c0303190b0301050609060402090a080102031905070801030503030a0c0912030c06 89
    0x141841003071020101e14035001030300b26030424007604107203c001c46c3c0004003251155141c00c0c03800d056841d64802c1c407005c15100e000d103004801c2120340190800400304400c4012500b0710005103d41d40d4414034000480f01001e01039520f10901d418070b00000c08003a0000602c5000d4580c00003484041504414103850007290f0740c480d01d0298801c16541e5107d00d10500764150040d04003001900700c40d601042e440005107c1d43c43c100d0440344002801c5401c100c40d064041000402400039950740031644452100c41580c0801c2900d086440302c0d0343d40c0c081c05100030208042c00030100b04014444040e24220000c05046a8907418503100c04000542007103144140203260036a043c2c401d1505009040c014080540884540d456903024080030354030182d50660011401e05000880403000d100440c81401540140224040740d0368290050300c6020307140301c040000344001031002c16001300803650000c0380607800082c868103884042c0e600300e2042e4040c0c0b0480401c0c2078200700f403641002c820310303280340309400070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 2967705 1250 2966455 2966479
    0x6040e01060e0603011401050f0c1015091808030601020304030203060103030203030103031403010506030a0902061c060509090c090a0c03091401050702060108010c09050108040503040504020705100b010309030509010815030106060e 101
    0xc00f07500c2c002441200400764201031001c5455018400415241000108680c171340100241c0c034610b45040039010001441d07640807600903a10380c00b041c030409800b00700c4091048a041082c004180c18103598050700311a0000085411603000304101c4000310360250545020750b0390f0f4100a51690001d101c2580800c00c10b00014103184882400c0340c3c184c0d040280f00d1801e64031008410001400300000481c0c00030b07410010300c0da0a0101c1202021241d0706031801140a40c10101486030100d40640310b01c0103035112003440303d19555a21540c40c0c0c005680480050f002c00f2401003200500701040c000781616000301c6222114007010340100d803041340e083e000c950250342da61800c03a00302c51000d1001700c0002c42013a4180515031080030a01d42040c041d00803039003041d4517400050304a81c4062001c880355488000c501980e18454013807009504801d003010070005c0c1c0b441d20007405a00c60b50a2641c10040240c000580d084491000c90030380700d10280081040b50b441c0c00024042040702003480d4810100340e420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 2968955 1250 2967705 2967709
    0x3010312030c0c03080703060905090d02010e03070803010608041104020d0e0c090601020d0c03020102130909030f0e01080402040509010905060406060f0e06150901050409090302030711090421020a0206040e01060e 93
    0x70701c03104504650344034150f03120a81c404036064100901003104068407400001541d4040340602030041203850041c01030303a480410060f08684400c951341d941500180401d00c00b2035001d005490448010341404221640c84d4644445050003600025610910105224a0701a01030717012030b00080910044a50798802d40c0104000400111082401030340025a043d1460703214070201100580300780001742c141001d403920924410b5054100d941d2841d6520981c2013450f0b4007164140c5004810b042040c40c01c0b4950303000030500e460041019010b540c6a1010a88100003588a03200304d03508003003a00d81d1414186882c001500c1c403486549801100c8405c003080c001100d00c1140d0180c44014480704a801c10781003403580769004085a42e0500000340400a41c041060084100319842507001d541d0b03e130407628000140b40b8600e04010302400000d02007100040d50740041000f08100d44501c1c4010004500d0b04a1402c1d115400082d0040404140041c0740d454816000c0d040c1c076500e0301d84545001050307017 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 2970205 1250 2968955 2968961
    0x4030c05060c06010603020c03090915010816020604020d02010c02060a17060105090102030d090c030507090c09060309022103040504020f07110d020d0b04170301080d09060201020a05180d02090108030301031203 92
    0x20090302e40350011001003180d240030745e009003007401c2c21401b0f5a0800c1903890009035104030458003c030031070400c400742e51050b691004650354004201c44444004400c1850b00a5884000410090040005071800000d40e805050202e000c0d642c010b00a5035281000e0300c00a09000d196000703008600130110110781e142d0b004009544d40d4040c103034010760030011f068030a03001425040e0419540481d6130040407011610502421024141d00e03400400c003110b0407007004081e83e21580c050800c00d0310f00105103005a4885524040060b038561040ea1041580c07642c0e5402c6100300e40c0081e0f0b002d88001420403801c040788c406081524007070400310500200038000d004840e4035810000b50300c054416000800550622602c2c3d0300039000b4001400309007038844000d03070550b0080e08508601d0340400941014140c0c040d4001010301001d01c001d50034946011005007850103181d03100b5450301001c05041060f501e0700101c404030b09400500d07044042d42e441a03031580300e83c420300041d9801d2925004041c0082d0280c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 2971455 1250 2970205 2970217
    0x6050901051e1203040602060711010501060c0f0507050a0801090203060f040c0e0705040801090807120c12030209190906050108010f0e011404090501060311010e01020604150c02070806010303030204030c0506 91
    0x40c0c05880c420b0040e5940200d0024000b06043e0b0141100c0b001222000e0204064009410281c006109034281030102402c065015110900390b80c1c100700c01400803035803016407807401d25846002ca03075141101b0b151090030108160400341e0400000b850014800c10150000800f4038025010380303626480341845403244000855010307000304d6a00004004814210300902e5004125141c410b003460b803501c2007039007919140681035540c03602c0410440140b009500300814142034070304000c00c090a2035540d000d2007001c80c000a00c20300d64003041441581d166188a01d141c40050000c141c102a20340c0721070760041c012409858001010b00b000072520a002c9041c1405862004807241031580ca407070194001c81041c4036810303402548841040002a80034080c52001c1e600c2205840c0c48460b0360400100780e0380c032041015045600500604c000b0807407510a1884d50030000002003004000081c081e46000b803264407400d01c0d03100701e100000c14141d00d0343c054000d50303100d1000d994030b0f01d94602c00c2100c103008030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 2972705 1250 2971455 2971459
    0x30c0305010e04030c0c210b0106050a02060411010905120703060e070b04050603100b07060605040b0612010e040201110307051b060702030c04200d020315030f1c0203130603020d0605090105 83
    0x80003c1000320340100d21205000344981c40d080d4182d9120b4041000c1c2c40c41a51300c86000071103080f034400030003004100d2a03000d0f10785803404d5030904040180003540c4820141000e8900f1601e440c0c0041320303034800c10362400030b07090103802e0b03048420340e41d41a569030340305510098603460324101c02c515211a01150032006c4035208100700e42040d04000400c0b6440d40060211415400c00510009490b29074002900b0500c6c001c1600185052500b0103100c2030f03842a41c41948a00810800b10346901100780c60681500d1000307035450342558407440143d6010110707802d1003681384004079041c3c0810400144455080100c41c600c098a046400d0a0103240d00650700001e40c107406c0500308814506140d4030031011030700e0414800c0d5542c21180300d03034081580550b070829211a0000300300101c111790b00207000e00011058005150580100300300ca615035550035550840a8544039000040c580708000f95006d08000d0b001c40300009944140140081d480030250412160618400140500e0f200c42114126000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 2973955 1250 2972705 2972729
    0xb0c0f011404060507020c0405070c0c0b0a1709010e0319030e03070206040b03070306090606020a0506060a0803031b070606090b1201050f010b07030207030506010303080f010b041202010503090a060509060106030c030501 96
    0xe9641c580b0090540101705000310321a60b0400c00e4680d80e14011130380284e81c10340b542c0da013505442c10840041816030708801da0b02c0c041003202c0750001d54400c22201c08031901c0c03024518580c031081c68480c05000b1885480d14648400308000f00e03081180c0c0b400340311020300f0340c80c10000040b10681882d242d0061010180d44050f0521003003110400f40801143d100c901841c001445940780e1a50000310ac1c9590820401644014055000c001e020400e80360000421600d250500d807400c880e9590700c0c0720040c20083e500440100e07082c40b0036089010358056590100c4140405500c0344401001441e01e402200e1140c10403100000b40400d040c0318103809000d0301c50718803216a00300254002e096001003021400c51040300c8002003c6101072026501071482903039190040d0800c0c14401e6034402061b0007a02420004000401c910364510310202a504c2c2e0a0a00a03140d40c5d84018241c2410704480e4080c182178145001c0041040021079494107035041ea403420480b0036038000046003110024010341d441c40350 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 2975205 1250 2973955 2973961
    0x70806040305090d05010b0901030303061505090a050103020703120212040b0114010905040b01050c100b040501050303040609050108040309080118020405090304060905091b04230d030e090603010f060b0c0f0114 92
    0x4000c01c05074140d070b000700008208080c051000c034915648c240c0c000e90019a41d080180030008a0301d00406801e0200e2412500f000c45000003d1000340480c441d041c140759002a41307104150203400c210b0740b404c80b0709030115200c210464010300c40c9902103600321419444100040342c07030b9030040b03003c480150060f0b41e0481513600300004c2c080200f14041519052000a200d00007440904001e5588a440c0001e40403030743c0c842c60410f203c1a2072040c2c0040d07200e42c00174072046c0886948541104221242403030134803295180c0b400c003601da048690304400340c65401c003000402180343c0300440c0b101881c8240c404119544d00d4410b490348a0045010784400110ba2a004200380d00d0701e080c60940100e0880e07004620700300c0c040c260b910301e540309900103811206045500118107079410454808950103032500c204014140d03134000c0c4500e8944040601c00d890100100700c0b207440945c021202c20703a09901c03c108550b12685800c503242c01842c4440d101e0700c16503154140340c08040c0130b403002e42e180701c54a50403592 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 2976455 1250 2975205 2975209
    0x80105060a0e16020c040213050a050f06070305090406030206120910020301120f060e0a0317010b03010b04050d03030b040606031a03030c07170c0d0b04030305070e030d0c02030a0501050109020c07080604030509 92
    0x218141c1c01e4030f000c522500019028680d41d81c401400200700100400c120140b81800b0301103040406d0b40244c2c0b04201301e00d0030110585034542201c00303450f07042c40d082e5601d85040300058004d041c25000a500300038081400c0300854106500a402600801d003110412100c4400c20816071000740a00118032503a0300003100001d01c4c0c001da42011520882c0c01080c0b140300d42d03044034a420340008080c4c0004180c02404100c40e01c0a03051180900840350f85145150f05106140c41103228078031a041c0181e01d48101401850721039400407034481e0000f8002c0c0012950f07400002d000e066500b0361921010070342c19521420340b40010440b00d1951124000e0700c0c6c081d280c90b01040005601580d464854042c440c000070079591494500b10700d00784030b00e14010040c101414001c045803030040c408411721000c4064264240c1d030005804096440d140b4142c0c1502d095840440c3c10801002c000810030340c281400414008003035009444c80b0b4042000316992030396503400440d911501518083d01080041081040d54 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 2977705 1250 2976455 2976481
    0x50103020a02070b031017010b060301030f1a0c0405040b0103180f0c030b091509011a0609010903050609010509011401030f02041a10020607110106050105030109020304050c090907080105060a0e 85
    0x84610b0041c0d9140079602c101300203a6034411070703000d031200402c1001401401e0b44041c868100c06c0105008008040180c0301049003848107003c0542500a07040d90710b001c22942884589003506000c4001a01741800040c1d480c00340c12a0103800e1040c2d0400d00c007480154400d108544200042d0391081e60080750b140c0f142d00420304000d80580f02c16009110110210346440950f82c0074143c1d030002400e500a001352044d424200281c492103841e41003107001c4c001568100803103072140e0303422905d482e503820100b0016110b0b400560710003002801140c04100f9002c8040d80002c0c42075204174000e020603050301c403c111010344240001170034404000320340d00240c200b035401454031014100c40840d09400c2100069408010311000e40d00592000d810842042d40c404884403080f00b542000b840441d040400281050005001e0800e807180d0110010341441070030070040c02c00c040e01414070b42590400220281d25403400340241140e5600b00000329003d8284000752404807101d49051303203801c0e04c0c0e64628003da = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 2978955 1250 2977705 2977717
    0xa0302070b090d050318190b07060b060c010608011a011115040203100501030f0c0503010203010b0a11010207020d030809070b040608070e030c090c070b0a060806060108040501090b0a0507080a09050705010302 91
    0xc00b16a0f50340000080040004060310401c07450140d106140d44401c00c94035490407066003260b03501903c8200112000003007565481741d44180302082c0042940702188440c0a00b111141d100c0d82040c100244082d419803080203911042c140d10f08142d074102c8010750f400c001e2510902040d604c001007a801c104040c1c4041500248010103489840100203090b83c190b603402e810a0707e4080c005900307102041a02107a100040c00284c009609641c5460400d901c04e00039400301c00e0a00080702d50400e0041000e60440da0020380c01800c0320104682401c0040c001001107541c030405105064010951002001c181c5d804c684280d9640e62080c3e03a05182260962606105550140300704440c814075542c41a9131180301e908890100303901c0e4016420b100115480213401c3e000703103030720f460b006014100000c100729a2282c401e08266110713071110305d4481e005280548025000345801e0041c8140400301d9004140100815541d865140c0c44d208500c00c1101c43e0950001d00c141c0c00808100499400f03600a026 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 2980205 1250 2978955 2978959
    0x30f0f070c0203010207030801091b02060601050a0302040902120601080c070b04080a0c060606030f0b040504020d02040e0703060516030605030c090106080c0408030408010204090509070612090c05030d0809070501020a0302070b09 100
    0x10801581c0c1d4080f90998104000840c04500c0341c200601c88400b25115265001c034400103485000c5007041f001a4484070301070800e41c10041c0002c0c4d0952010b00a404440040c40d0100c011540c0b503c0440d0704c800b4400c420b5440d180007610b04ad000c02e400e03030b03e1101a0340043d50008a00710302610703117a40c0d150099003d00814001d01030300010306e0011403c3c51180c18001c10250b14003050001c000070101088800d903403452449946080d0910025840d01c4103000440c660503200000e04d003000c00c003143e18140c407907400148954100703400c01c030f40c0380981c5145e40040b0515803801e02c442500c6000b00340d140c049514046400540440c0104209485007000e0750b0400800030700c06140a450344030844c1941d0143d081044580c0d0000303020003d02050b8403425900400d900003601c1d1250070042c1c001c050750100c411452109031100c03030301018031680100c080001c2c0030043c101d500c0080c00c031320060f140740022100180203000f14100018154000300e020801c484d40b5034042c101703460030002a01269006081025 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 2981455 1250 2980205 2980217
    0x904090609020603070801060206010609030506180a0b1003020a050d11010c0201090503010e0604020901090506030a060b010207050405010e06030f0105070507022b050a050105090a02010504030b07030906110a02070b030f0f07 98
    0x3405070303c440e0001d500505a0340c2e10400c00b507060106c060f00d0168187d001c14208500700d6020030218001091003504880c03028605602410303100704c258546008000e000e0401800e28040c0885ca850383c1a046080b02e00c29a4074804c00c560301c00403c801071b1518400544151441340d1450910740c450940d02102a2050400500c8d03207445201003821204003680d1044540d20241c1880258504086260700414a440703040c0240e151801c007003620b0b40301c00c02c80200b1064503003402da0802d81c024401d580c060a4041e02c20412903a68071302c00400c80300256044c6009000b24000e05030114418002c51f840340c6203c0d1655403603e103460342400b9490501a542800e0b503c1901803e10f0131f055000c1406034100e00480040c1141003143c1003180c21180058808034030782d07102258200040c0d82010948080760741101c0301002560b030f1581c068000d0300d070051009241916100440110907010340c01740c00e000200d40d080314202c0382c44408841d0144021384800501c0500b01c00080c03444840081201d92000f80b80c0703000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 2982705 1250 2981455 2981471
    0xa0b031b030108010605010210090201020705010f03020d0f020304061a012c0301020f07050f06040c030201080c120115030609090206070b0402010507080a0504140102060415020f04081c08060904050309040906 91
    0x48046420a0f08081d50994451804100d01d40c0d040003d06007226804d60204044000c80d40082c8d0340795407502c1213505000c8441c08200304c8074003c1c2c0c16143e00002c0c1c44014401c004003646010029401224100d803a149402d581410301040c0020701040c10f14107858510045800030401200700042001c0e0003000c52451036012450380307082c00940845808020b07125161170755484c0640c10210a1001c014042c0e000c4c408201c0401e001c0104403048940a007004005902e50240001140c4648425070480300040c00000400f02d07400700c60200031950551301040000e0f20340300401e040c0e810040010b9031203001030100f00041501900b002d9082441410b05510308800c03641c0b541003603080301c1c00c143d010400200741004480d041902c0100c45507001d2020b0800d03890959100015540c408000001140e40803490b621020f054108680140002004a032103070b19840240c64075402c401d00c5036100191a08003c1070850818801060003143d0000c0070790304150710f2609110080040300c00c00d031075540c2c0707440c45 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 2983955 1250 2982705 2982751
    0x3091a0d02040308180312030609040804030219060801090b090c0c0703050604060603020f0103050c0304030c03020f070906090e0c031009050102040b030a05040201090e0c090415050a0602070e0702010204050a0b03 93
    0x400046124003841d80d125018410410302a001442e0914000c1d0428002015000301987c00c503a80904100d07a9080c0d152200d04003051039008540000f501b0020b0700000c840c1c2c0050205c5c204049503896910640f1503070300c07050ba11094900d0400c10582004502c00803404c03484c5118060300b2500784000031511410b580b0780702e0600e030900948003643d07401e03540c000920a50401784400300c4181404c0c02c09001600b811041e0505a210040002c0c0401c081e0200760800c040c401e02c4072021391010301007103446a035203914406008280c0f500c10246050700d0058000c1302d054000c90074420f4294020301501c50b48000403140c2020f8508103400b1502958200f002058020034030003d907014180343c039000175091400e403001402104450b04001444c0d44a00b00b003201d10080300303003120300d80c40058401251181c1b0100100c0400111508034a50041d51804e001c030300c01c2e6000880d0001c541382c9500c0410b081e1280081a8200d200718090325821801d490400d004246607a001560052103404008101c010f8180b9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 2985205 1250 2983955 2983957
    0x203030d05010b04080f0307030e010503100902030c0c010f06030206070311010e0d030b0306070206060915030106030204050702010e06150907030c05090d03030c0f03020306030c01080601020a14010507081303091a0d02 95
    0x40000c400c1c0004c0f606002c011020004002c107040342000030352038905546c0340509500d03e40b0103050b0410900100086150361140b070b1080c02003135818001d64480c1032000c0a601c45801c840c0c0c00c103040758602044510340405a00501003220b4001d44620328000c2180c604582007600044550155900d84a0124011104110108100b821644c00181406480081505150300501500115400802400742c1c9039503270b01040d604541040185000340b1007140c0864090b00c12544085d60003440d000030030000503010f4021b80c0d414102042960b01c0c9980b01d0806500080720281071a400c807a410000605a90095020303200c86013207400c1042c00c20081a0000b00a072001c880d0440000342c450030076851850700101591407100d050304055040d032804a020903079408070740c0070700c0d41040030b100003041117039000b40882c484003508076215030301c81d02c00c00705000c1c00f0701401d8510a0024036108001848400ea00040008403541560b4201c0c00034600782186058502c5800308c142d081e0403c116074001204588 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 2986455 1250 2985205 2985209
    0x6030a050f0a0204050106050a0801140415030606030b09030304110904140d030e0606030109020102150406110f040e0f06030a06050702031306020105090609010204050904060c0507061103060316060c030c0203030d0501 95
    0xc0040c0030502c0c1500c184801d8580607801034080c068140030102005030800c45c032506443c00400820308401a038000034025004032201d00303a07490b29031440402407284542000060783c0c0070324030300c0d4007a4444c54043c90783c0748402c0790080d18503001e1006e080b545103414042a60004c0c0680003c00c020146117540500341003407024502e02080d612800c454400c0c1c007e02480b0361000c812802007141080c107400103500c50786600d003e000f040300c000700041d027005681d9014080400d004031085440b80009405407415502901945182e83c5030400020000400e50b81c080d44034550103000b41c101505240d0b80d04001d0300c07014101c40f003940030520001509280d03078001130f001046640e0010410f401c03d00c0707682e8280307074028140903c941d004200070321003070710350307802983e042a800000000c21a20303250044840b80200b80d0018021424501140000c05103003002d540103040840581d0090040303601c801c0d010941500c09d51002c107010108201c003090046000c800c28600184c25680341c280700c00d0b00001160426 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 2987705 1250 2986455 2986483
    0x206030f09010908040b18040e1009060e06010b040303020705030102040b122505040e15011e02010e070e07120b0a05010509011809060f060305010605040e0603010b0d0501020a0e04090206030106030506030a05 91
    0x4100000111a01c550858140b80e00340c502700400c5c1040002141c80320075004121400350346a200340c2040000c9948100403000600040c2d07041c55071140440c3c0b00950040c4019001441032030301c0400c182c54113108580c2201d411012044c50f180c1c42c120700f6000400c2c001e00000c100341e01041d8032305803107889031111050910309135905036596060202c1c1030709080018050002074181c450309420203982060300409d028810305110040c001c01c140b8201d0151070701424480b070501820000081c00b5046480c0d580c094102e80d1200000c6000414104c0c0850303094074111030b800a40c0d50010005c135405680184103009040c0740078500d122548807409000400741d803000913860b0383c8080070810300301c1404c14400507060628082c8090b500d480b04c002c1c158051402201d56035040340c8040341380d60390309500507055900054070800503280103080050003500000f00030000b040128001107094a003e2054035080c035030051681d41581d091100c120300030840249211380610a05000c100420320401607a0003034100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 2988955 1250 2987705 2987707
    0x2010b031506130203010b0708031f06030f050702010c020706050306040212100305010605011b021009080d02010515040b01020a150b0904150b0103020304020d020f03070b0c06180304030206030f09010908040b 91
    0x845001e021100b14200200000c3c24030610060001c1d800c8001280c03c001d0300504043c1e102c0d1120b01d0302850b8004144030000030003008041c005480e54064000d95540401c60104006035500d03103400340e00340c032800f80c1d0600040c0c110600a104450041002d160482c2020f040141441100032076185080c01c20364000445d443c0031f507410020800d0034001c04024002c00e2030004031103510070030021071101a089000303218030720a4810010349445101c81c140248982412214507914031a4003030300a180545920050070300030100c40700705040c9030103400034621040c2e0051041d2a03460303d4240310000494400107085441740c0140c2403a50340d000c1000c7c042c50044181c030141c0c000782a4548112561586202d05150051003000050380c1d60180314110b0540554a400d510034020b00002d040070840d4011400452000c206003070650400100b05201d08801040a00b485819400c06a6a801584002544414200300080907100d2212025030030003000400810082a981d65008081e08039400020b000c5d80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 2990205 1250 2988955 2988961
    0x71b150302070b011a0304140a020405040303020a110d05180f0d0c0e01050121091406011403100203090d12020906040909031701050f04180204050c040e01150507020d020102010b0315 80
    0x5400c2e00f075006100d00b1001041d800300e10f6810000c1c60000800151511140c41d92400c40045c1c18030151001540c010001c1000d8902854046c00940101c544200090001c0308882d540c0040083d280e129440243c907042e041c404c2c1005009c0d0088180b10070140c00400d080140c402580300c0350441008584105034481046d42488884007886405900c007504002c0d4206083c031f041d040403a10070380081350a1401151843c4c3c0c900741105440c9145070342000b01d10540000103a000a50f00003044801d00131025500100841d4401030240d010030b4074100c8042e001b01c44414280ca000d68610114001e030703a4400740c10030110074009141d42c4c00c141d1148503504e40b40d00f00703c000c040d44a00112031140000c400f440c0a5410b00010404d101e00b0300c0c1050303014955450a03102401c00100c418240ca07680208184010301c2c122059010761380091080b00c89001d80d41c0c3c00403c2c010a281c4880b01903041c0c0703a4895041002c07540822580300740d10f0740181c0c159540c07400000c0d4140c905200901011a20610b5095141 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 2991455 1250 2990205 2990213
    0x70809060901050c0a0503041b03080c07050607020303160212060403050901031803020d080705090306011401020111030403020604020f01050f13050a0b0f030a0207060213060201090b0a05010506071b15030207 91
    0x40001010709610781d24202c1000308071503405041c1d554490701031a004c6c2d12541d407803a00401400c0d81c11060b5542c800d20101c0002000184401405224060020361384260b50b0307002880740500800d81e00a40c0358100788000c80c0301d0766031074880032042d50009240c0c18050300384050b414140042035038107800064001070624601d5803d4080e60015407000155400541155100291038802204a00003040f980300085848148180251644444020243d542da0b50b0b4603112240e0749848286094059401d00e02165070a48082040c2d0b803140741c058020701131654490f420802040c0802c0314807411302c0b5040c0142c143e10046803002d0b181c08000c100c800c6c014907040c0400c01940d00300035840320724a801c0c00c0240e00210b000f1f000a40381c00c890420303005600c0d40c0e40d900d044000381c05200d10038040c41c19081d01c0045c0880e0305412a024840c022120058140c41e042d40c5072007554024050349400c0441048440e00045202e465414595100c13a03130021000d031650200d4404038040301e940b42c0080d030080b40c0d000c148 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 2992705 1250 2991455 2991463
    0x6070c030203060c0406080f060109080304080f1e1207050307060e0105150303030108030405060309070b030903040608100302010c0312150605040501020609190f06020705010606030e01050609010509060f040e0303070809 96
    0x310345050034039418981b61684c02800320b0002821941848540c202046060340140698400b910110381542c0c2c403a07440b113181d1355a41c0c001441c4c01001e4410307076940409024034a036a80c03904010441c003a0142030201250300580e5032225404440502c0200290000324119100350b110070030b00000086114103201001c215201ca68010041c400e0700200010000500c0000c00c960849900b550102d03244e1352080c00f10781c00c000d0594003400b07582800008115419801100500035640b241c3c4a500b01a21680c040f87d10103a55130100901181e405491000441d0140810401045102e81c0210342c2f00c60707035010b4904041140e40003401192002c0740a0280f582c040c4135180e40000244000d00c10064085002007034440080c0001c2c0045103103100c0b81013406613036011503001d1070700000284404c66980100800400a06401580551802d030204500d850b0000b860b5040300c000030b04440c2d46468020400c010000180c3c905c50380309076a00039401a2010900156210714617548445030035140c01d402580c20 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 2993955 1250 2992705 2992711
    0x31305010b01030c02070501030b010e04020706020322120305040602090a03030306060212030f1602030708040e04030906080402010e150715020702091003050d0507030e06070c050a0501020c0a030204020a0c0206070c03020306 98
    0x603d410071240144031a40091524111402446c0100d2000d0107540103032030303005100c1034082c0c02900005d94401403040540046000c0c420303101c040740e0007508200c004100c1040700080180300e0030f60b601500c00024485d81055403c40d0045200525102c0080000381d55080160720446c0821345a90080044a070103101c0c691a402400040620310300d403408078080e20b5240201041a1009036070b03844c1d1070300d0340b08005441106511603c4243e40d00c1d1901d40071151007600302c400301c0c0019507110700482e51521910410303020300d5042e1240c0040800010402c00d943c440381c80d1615a01400344562000300398860318034041000c0d001c41c01a600c280c1030060201c0440010070703101c00c5a02d00d060401c0041e50005e0600c0341511a0306d801621404a490110b81846602100b154003e20100f03011b404c0c4444503c0d80380c202c940440b0368003002c560b207000598440b850080340e6039000824501c00c01c01b5081580003030013000c88514010f060512142d0024410350410b040a40354004840014011070400704111a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 2995205 1250 2993955 2993957
    0x503010f0b19030b04020409060b03060708190207050606010c150204030305090a0f06050d020706020d0509030d0c031104060c050c03070303080405070605031501030f1d1b0a060504030807080f031305010b01 90
    0x90b0103420350304c0350101c00e00c0190009016a83e46e192070b0f41030011340d034030204214000030207541c0542080440280030f0003090300c12400c0005007c0103a1a468014400c469540d688100606803641e0f03000c00560750844662001d41d0f14205000030720183c3d90481c80100007951082d00c48503200c5210348240500c0741c52a4110a1400000c2034040c00620703000340946400101800025a03145014600000a402241c2c00410554100400e10011240101c00380800c4800c06000b04540642c0090403015100307500c0714110000410401448464414580c02c607a0300d010382c003101c04842040c80070030319018a990098000400b40c0060004202041c000742006186600c0c009055040409102800d83c2c4c1d818201c1e0b05060703130398185000340112900540c03065032a040c40344d100c2c41000403c0c07070b4883d10308845203042c1c642c4584202c20f06240c54130600c3c0c00e44049550703040c1411b0856580750659400030b40256814070b0f0500c8284c86552499004600c690302c40c150b00c0104a03030600e4191b09690042e0394441c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 2996455 1250 2995205 2995249
    0x3020a09050d02030c0d03050f0301030809040e0d09060c0204091202070501140304030203030601080429060315040803010504090516060201020901030e03090f040f060801090602040302100807090608100503010f0b 93
    0x6400740e5000174510468180450b100022401545010303201b911411004c24500c42005c0300001c01c1c054410080c1600030300584040c0720543c0d0500415880303440105c0c11501190304800284025841010780803c2c0a1020b0300008070980382e40c440840700c041c000381000042c1d0103d9020b01070307560f00c00007002c0c2076400c41c05041d0440c10940d5010f034032808001e141c42e04000d002c100290911121000c203010190028007116011400380b0f0140d404035030300300e40301c600a103d56240c1c420340b100005d698511075a00410f045055909041c2048043d00c803034901500d0034031032041d2400c04c1c3c030f41100b60b1030020500f40d000180c1c0d075950400090151100c03000203064940051010314460748074001c0c007072820031040300c0c001141c01076804003078001d1009130030000c1c1d03c2d03280c21540c3c1b04100300c03580280700b900d00880b511100c1d40c500200031100d06600725211400038440381001c01809029899598100c880782030000701043d10f03070001c01e0071650101035042c40241c03500203101d6a8102882d401203c0309852081c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 2997705 1250 2996455 2996479
    0xf0503010f0b070602070210020a030e030703020d060504020a030212060a060905090303040f0303061a0c010b040501060512060103270c050301110f090307030b1006110105040f0209041401020a03020a0905 89
    0x1001d05041070380709900381c962001440380c0c01c1145540c111030340030b03900400b01c1d1044240540003d541d01b082c00341c103e0100d028099091024a0f0003c0d0038011203a005100b0901000e2031350b2640042c21000d4812070308004060804001070b90385890010042503568020425407418118500941d04d481d4083e07510240340c001404001d5001204030380e0f00ca9000520030019071150300d021401080c1aa001421849420344c160903041011801401d500010304020b000042e490803c00c012640c2c28805c5101142040017040c40384802055007079445281410005414081440304076842d5038040000c04280490389030100420224a1711000036000a400030441e8502c001510052807003044041c480c86540844c4201e4143c8e005c00144000e10b43c08080c006050408407035044842d4568001c0c0000700c1c81e50061000c980205200f030501c95904040750b1003403011603400b400444500030b8010f80762050019a1381c56181400d00040010310706540e001a603030b040c1d5070401858410b454101074810043e220700d0b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 2998955 1250 2997705 2997719
    0x803150103051501050313080409020403061406030309120708030301090f0e0c09181e01020702030609030a09030605060d05010507020601060905030601030b0106080910060303050a0905010e03060403080601020309030105100302010f050301 104
    0xa400050080c05c3c81603990b00c40c42c0228001103c08400180000f40c0080c001c0780311100707270b0081d00032280306400c20f01543c0400c910382c2c680224105c9000340c0680c4284601c110500c0c2c00740c510040740c201c0c03406a45c2c1d41525001110705640c001d03006608042d40b10282407c1026040c428501c0d02d00c2164007810094442000003400050042d111403840f955440701158039032001d114181104450780107201819101c560500d010790040c05041e4424025000061b480d00c04c040210380349202e80c0d03601d606056040d540c0ba130004017005050304c0d0b0051181d101d4140040c1c424070170f20b0700600e41500208000e41c5850b8005110004540090340207400030340c01080025081400c440c1510300c0c81c2000e20450362450034162030000d030fa2010030300b41c40c2003940010078540c100b8010240300c6090303594805401e4440e401516a00c8a40c492940c02d40d00c88400580400e1042c041d40303801040510503a46031540c0b410009003990000e890006003010000c108204640c1c225400808103d102d0030000d09662415032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 3000205 1250 2998955 2998981
    0x5130b030c090a0e010e070602060709060915030906050403090305060901020403030c081e07080d060506030103030e0d020f0d0b01080d0305070f0c0f02060c010509011508030d0b06040e0103080315010305 89
    0x480d09000b602c0c24000304006101d81e4000d0700d180c0c00d0640c020803024461040352130395a00d841c42440050300820000c121610301c55100c10081d44c04545541e0050391412010b01c80314042e2514040c2010303078500203400081c0d1503000d040d0099000355034230a0710604505100e400e20401405480c12a03204000c03c000080d0042040207086801403031094441c580344814a884449030030701450f266100261042c01c006684002d010701c40004401000002d46032000d001f030742c0c40203000280104194169a43e1a40b41c5410344083c03182c4040c040c031160390000c4012403100c000c107640480700b0030030000040c4041d650802101c0180f007a2440c080c4400e0511046c090000c016030410023003007207000c48024041c064941424101c050340900450b9a440d02e96a8882c000d05054032042c0407542403000b803c903086d0342110030b981513514a1000e14608900ca03043d000007401d440c540c40b60404420700000401c1c280301d040d268002e41c02403031000d03607038038080034140320000d951901c1c03c0c1410328050a112076014000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 3001455 1250 3000205 3000223
    0x50d020906030111120f090604080708070302150a020703031103040305040e0901090206030403080105100905060d0c0306090207050c10030e030a03021b0601081605031b0f0109080607080105130b03 86
    0xd52020015116039012034098003540707280403130456001468040c0c140300c0c0f00110b4803c00c44425103850300e44410680c05d0f11040d007a100642102402d00405001c10b85040051205c0340c0710707004442c9605030059a103890b032082101e00b643c1c46070740410040181074243c05050300c0c01c0400c40a9038950318241d6000b82040c096400343c6403900241000182803440309500008030301d0307001050076403a0b18281c50003e0910300c0c01d004841c0a44c1071a0a49203909010722010b109999000301514200940010800014040d07002200c0402d900e40900060501c40342c03000f000700d140180d01508007042c4403010b002c0e402c0d2847c441081014581080c1d181c04000c003100340c55500429180c0543d48840d10454101c02e0105201d44400038000c00300006000c01c070008804c60aa442060008101d039554010151102031951408042c82c0d00d5242c5080389103016054800c5044050500e520519161407070146404011514080451210030060201d450902da10200c03030042071406008001d40000440c0e1035260341 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 3002705 1250 3001455 3001459
    0x80f03040314030403050601090203061f0206060108090703020901080105040c151704020d0204050f01060206070c03020303061912060e0c04020405010c020d080d11040510030507080c070501090803070c03021501050d02 95
    0x80031001001002c2802103400542d00241207030300035616072500400962090b940c06110780420b402c03404407242008012151400c0c0303038000e00710641e5003000545030180d0040541801d030055610100060317648482c03286c082d1005e080002201d190901c0c4c1944450900c2e00189841d15003182d070840320319804201000d40001000710300515403118030110358410305c00f103c000c1d07106080004005983d5450300c40c040c102c2c4c500743d00300c403000e40b03030907a00741c4041e000400050300680003000000c1c49410844200713070314150f1111040031015030318100c1980711540d0380001c8820f641c407851005048007040000c8400900100d40c11840c191034000003070002084840020b004003c20f6464a00303001e00b6005440990081c500d080c800110260a2440b1951180c001da520071035202070a940d046200348209403050200e900d5000a548070740c48034110a4104000488096486441900000352480d014502400341c03a19030200d11031440c5000303803e00c3c240070309092210403c000104550740c2c807a02040003407901 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 3003955 1250 3002705 3002723
    0x60c080a03020c0115060c021003110403060207020a05030f0d020111120106030b010e04020d060801060b030105060403080304080d0c03050403021005040305040909110301050405070612020c0a080306040f0603050d0306080f030403 100
    0x103e6091030140c207001c0e060150a400f034000011b8003070307080700704000c03039920807161035000c91984c803000d4080b920070b59401c0d0b5440c641400140f00144559000344100c500003400807806540c0d07280002e1804408820a5206d500310b05004242e032034090240d01801900d80c0130460801700c0310500d803840404140300342d508040c0c45202c4628180d0080101c0c0c010100050004e42d5600a200c0c09400600120b100e041d016604e09100015010042800e43e4140d03680105000e1030301e4a180c072071f1107494001500550b441c0104008000e814407207803103000c0c032652507502d011800380342c142030103420407008800025030b10f400e0800304800a0707406400c840c00d07038140340d0000803050400e00303101e41c00c200480241501903190405100c00e100d0300281070f00445107640c2d100075010880c4601c920030780c0101e90111500b984005184030005804802444c2d001d007000d400041c0b4849035161082c140c0e4401d030320a88158001544c1c2c2c00c881989406400d0186c408000281301000c807407255141d8900c9a44400380607070710 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 3005205 1250 3003955 3003967
    0x5010f0804030e09070801060f0206040f03080903040902070c0302040c050a09150e090915060d030215040f02030303040c03230703080904060308030106030b0103140106120b03010e0d030e010501060c080a0302 91
    0xc00f40ba0010024440644894040e00d01014060440070003800b039035020454040320010500c0c4000380c0a0302c191392140713040100751659901a640716001415204090105000c08a0116103600c05001d000d40901d11003c4030358035500603c42207039210b0b18008100b18042002414040d002100f02041703600d11040781001c000e015500301c034980c080005207640002c03580300340b01415100065a147c1c2000e0309203200301684074042006591014004000c0240c0c001d50740e440041940044070960260040d0f05980c031040c0c0c50f0380041e044d607004880855508000d020280203101c510300c030030700b00c042c01c2d000c60001415003283c0d856a501218440105908400500c1a600e611160031035801590701c000c14a4880d61034950190140111000341b90000345003034192103071030700c106030460304890203a2a51a5822200b59509018111402d007881d0150348401c1082c8600c04100080382d141c1070036a034005104684c0f010030500b91036060380144104828480c5101c003007072190048422103c0301e4140140d440f5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 3006455 1250 3005205 3005207
    0x90209150402090d080304060c0c0308010b0f040314150f01290c0706020708060609010e0f06040b12010b01080a0504080313030207050901030b0f070206010f05100c0501021305100201050105010f080403 88
    0x4841c07448084e8001004084039000c0001000203940250300ca41c109000054180c007003140c40966004024002400d1b09004000c00c0c00740800070b00f003034820385805600c0c3c00e8072078a506444d6050307500410102e07800406101c04401100b2002900021014019640c95141c6685500449001c8001d18030580428603564072401c042c5d0101c854034030386141540c0c0f03c2c0307030b5610001e034464485214030310380b5015401c00640c89103003082402c3d059420213409070041c0c3e160850b16034800c0740001c2c11030303404c80d5132078400c10143e81c0d8103615864036406c442c0000c01c0f000c04060004180c03150207007a151001d8148400e102c0000c502806882c0e102a040307003d04200802814200d16242142d440507800c280001f00120522030b980b02014442c408050081e20700b5126490f0881e0b42d503a00b40f00f86040d0002154050251780741c458184510048180345c04021100344e030301c1d09801c9a001c59110314900f02880410440760406501101964440b4002002158905070010780494042030042c0c08100120b00003030101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 3007705 1250 3006455 3006457
    0x102030f0c0304180b030607020a050d03050c0706060b0c0106080a020a0b030408120403030603020f030309030601051311040f0503010608030f0a080a0f020a02010e010509010c020703060c050909040c18090209150402 94
    0x30084d4844001004000715600001030584d42d21150090040e40c1c001408280005101c0941d103604c0001410f00103e0301c0b104400400b000781020b440100b040240d0b0000c5129401010301420511000e140e855140040403801c4510f1740d4040020358000c0403030040944c1d107003030709101140d00c0f188180b030742ca503140d1400c04136500c6440c0081c4071051200080c841032540c55070140042e00e00c2501c880b015004c1800400d40d41c2c2c040d00441c0da92640c01350780180841d0400302d61100124441c00004940e11103030001506240d0070981008040300811300d82007080c0c0c5424019200101588009940f0f02400d003641214544603c256030b2050210200104481c0f00b6258059400c0745030343c450440d16000c200c10000d0103042e2004140c610f541c2040049440c11300306200d00049010240c0061115034074550341ca401030f2801d8045042484400d000c041c0075902c1742a2100c0c45035200c1d00d0b03070364507032404d01c1c2c2421455072030340024040c0145080a40d00043e107914407000e03000010490003000400c1020b0000380071f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 3008955 1250 3007705 3007709
    0x170a151d0105100902040b0901030e0f0109050a050c090405031801020a0b04120e060405010c020d0503040e0f0403170106050301050f0f03030a050c06060402030c030402060a090b041203020f010b0102030f0c0304 92
    0x8103586031500c0c014040d50662045001d00c1040700d03c0083c440c0e03201c01e2034050b17000301d004007144580c0810812180358000e60220840c000c0080590355020007108100e0300b1115001815a01c0e604a0040102006400d0080c0c60584004071090140c41c209919619900d00030150007603407140000c01680c0c4943c1c020041496a264001301c02c01071450f051401140c144482c1c003142000c24200804400c4c035280900555060f00d60607034034a50452450340810121900c80710301929180400c00000c640d2100d00040c075841540d101da40186281001d1800408502c282020060000c8200005002040d84503044904490040b40c040c10848a1304d4001007149000c41c054039498072000a0f05442e854016011f001c0d00341e002d60564080780d50740010300c42688811240007035440001c0000a006103070035030240c00c8801180c5082c10509890350040c60459020f50030103e0340600c2d2a61503020542d0401442018200b010024085500243c5c0045c0d40d0f030003855425a084007010408501c0401c080060300c0c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 3010205 1250 3008955 3008981
    0x207050d0803061e030709020a020f0f0d0e0a0306050702010204030b0c04060e010f17010e010f05030106030c0b030c070807050619090b04030305070302090301050a0204050103140f040f170307030e010501170a15 92
    0x1402d951f103103051802035019100c00c0c0050302601031030814852000c0fa0440d00241c8a40150035041942c80e01251802e442010484d8000d020300d0b0048042412441194410310341c0740c00043e6120b00711300385002c10001c01480940c80040800051082036406865445030000a0a050310280f01110056800c100000c24016606101200000710b00d0000101a0b04a56031500041001919001814241c0e0800d000241c0010b4010307808100c083c0304035004652002d007a000c101e00707001080d40c51030050350007004141c0d0b203a480801844603508a07a0388104481c01d28100820000e0f0f0250341e05101250010f001030b0906644400140c40d0b2800381d0121820614020020800c070701c1c201e4035070030007900700e40101800203240940598500c00c0600440e4018404000010b021365910341da881300355107170f030030b0102c90316800c110a13a000039284902540c0629610340f0082840d00945030141d084540503881090410300010381c10000c0070012501d0f0300420341291000004000d0b001c1041e0180c880070581c42 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 3011455 1250 3010205 3010213
    0x6020a0c0f06060f0803040e0f06030304080303070305010302090105060a0806010c05030c010c050301030b0106050306130f0f050a02190e0d0201030504020d0203060c030414010204030309050402070201210c0207050d0803061e03 99
    0x1c040202c2030f8003400c1a50050b140c0b10300b4007078852a006a580c0a10b0003000c809032a64000701d00031100e0503400c4d40d03104800030704891030207480b6045182903810954030000401e48440c010b204615021040343e02410303090f11150300b001d996560007050781e0f6004c2c0080c0d050180c400081400c0c060184112082d41030200700034441916000700c010441d5209100a0b24005604000415028444c10071240104401000c85000742414230b040c03001441e0160a84001030380d107101c01c60124480340206441110542700042e2601401d400509555507415101800c101141d1056252544c4241c1700000d030359020300c1c001819a441c0d03c08136800f07c08044001e581882403200708104030022400840c40303140f140f0140d101c81001d404a403030a034000c0307000003404151041024405800d251340601801401450100039261054040c403180c083c0182400c180981c07980009030704907404000da64010030094444440030341c465155110341d0b01010340780c0d501c075030740d8a0300200542007800b0070500c106070014165 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 3012705 1250 3011455 3011483
    0x914150412110406050d02090a0603050601060903060b01080103020a060507050307140616020105010b0306040c030b040e010209040b01050306090402040c0203040b030c071103030310090f021605030306010e0603100306020a0c 98
    0x240c4040704040c1000c0302d42000c044644030450905010306411220040c000c0310704a1490b03400c00000100050501489a580e854000041602000b04600914007502d403030000d10f0441c1411410345104103143ca050103e03403001040161a11481d0804a44184ca0281e445122919080c2e00f584600b4074080c0c03424507041d035440d4606401242c414050303500d41d13000c08100108241c050f820f0314024420000c1c8484184009485070400380c1000e50801050301e800105850000001811a0381074680c2107490380d40420070070a54100741c4a030500e405001d007001d505600d0880300203249010000c00003070140340c8071000d03419418001c109480280c00103c0c4003e071240f4104901c0c01a179001040141c0b101e201c203030300301036040c217011088a02030b001070070601e070403582007000c481c1c0904210b850204c10305070308100400c200074200c0c1405482d24031600c0078503070328202800010b2241c1c180d01c2c441d03403080c0010400d00601d4540441300c00e01301ea5001c1000340c0c0300c000203441034541d00d0002001900f401c1c3d8842c1a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 3013955 1250 3012705 3012719
    0x2070503130f08070303030c110f0a060c030b030a02130b0604030b0609060d080703180b0406030501030c0603060b0d0908090402180405070807090608060f04020c03030108061609141504 81
    0x15000301040222252041591500d1400c01d082003840383c000f5a41000c0400d02c040f80c445d403c0010a011282040036140b90f20280031841d2140740504108960413441c40d800030440c0c14042c902c0603184601e401d00580c501d2030002a01d92605803402442215040b02082500302a41c0200600c01e00041001c0d444956070304014410090032900705e8495004400011414075085070302d9801c00e03800101450500c80c0c0c503070301680c0718008040c0c3d100780000750f0f0800080e045c018400400c050300c0e50740d070082034be545540752500d5140e4494028030240342c14900c05220302c002c1d440a8442c1d0750100700740450f0317100303040c1000444d40c030504a6860300540001038845d0140810030400f880c00c41c1c01c0d241001039030388000089980d40b0042d00c0c04800154216410800300c0e01c54140980c01c604004d051303042404001d800a4100c0e486061260a00e400c007000400a4a00c14400203170b00254507508081c003a800c00300000c2c103080350750041c0000790a0b030340780c001130365210140d6070009404c01141071603566480e612 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 3015205 1250 3013955 3013957
    0x3150405070b12010611011103040213060b0f09030114060306040803150a03060605010f0201140114030304050402030f0403020601060c08121f030302030322020904060b01050c0105010f03030e06071104020310030602070503 97
    0x941003c54020401c052002d0300510231000705821240120f030554036544d08000c248558898040f50968a5035030101d8071074940310007044020381d8800da00d0f603601a403a0030315083d9281d6448158508070207004101d0103840c0441d01c681e01a030700616143d070365911054035a07126011010f600303400000141000c0104030702540231000b0385000341c8484a00201e81130089090701d28041d0015500f00305074004001c1000107055180c0140c800905880c1020b4560b0049003ca8208695580d0502001000c0c00103064051280a002d0704040c6051000b0602d41d81300d203d043e00c51081003a003181850030003e03645d4640d400701c4043d507020030403013100800e80d2414029525003080c0c50204c60340e030b40f50300080a00038807207000b0750305035038080d000214543d01c42e12000001c11542c40d03c941401400c02401c008050280701b0303c1c0c0078040701810f5001d42c50031800c00401d14070320042d1180c05060104544804140304424003080603404075000b503a01e83c3c42e44170140c0c00301881c1d4001051940007003950004c00c90044 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 3016455 1250 3015205 3015209
    0x11010207031421090a060f12051504060509010e0c070f02030d0305010305010606051e0d060308070803010e01050402090303120c04090e030909060613060302070305190807020f0c03150405070b1201 86
    0x1183c000c0340e48000d44507050701840b40302505540300c0800841002620302801c4c1100542d10541404040c3c000d8000f06802070381c80898040340e08100d200c0c0d10340503d240621a03c006481c050b00d941c0c0c010b6041c1100c070728070720030042c003007000321400419070000f0400b041208000c104d60240503508141035003c0043c0c0030f00703404c0c0011242c550a1140100e40795202c0c2059032904500c3c01500c0c032180711070aa80d425141c1c01840341c1c010640d165039010000c640304400800c1d200d485004426580c1d03143c004500d88824040c2c00c610f114500400107084955400810b550342c040e07050740301c800c0070727102c4215020491007690b00c80c8054138101040118403075004000740a072842c013a6000300d05c6585240c10800c0e24800c007407540c1d030012590348051146034800d41c003419521f44241407003442d101c03414817100c54560b0301a18000020380c43d0700801070461f5042c081c0b50000c007041c10040c034105400500003a00d5035100d4554400750030801e4002024000100203020080484028480d590804560081c811030824 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 3017705 1250 3016455 3016483
    0x305010b010806040516050705030405060708040e0109061202041505040507030207030305090601080d080a02040f0f0303030f09050d11120307030b0a12031202090102031306020106140603040c03110102070314 91
    0x52002a0a81c01c050099a10a52207082c4031003092401300010384154221003001d840c9d500c82800040b419441300d00041448500407220300c0d807200c1c540001d0744036540050b0414000c450030020100642d00300001c2d0340d03000a60480c0c01103030044234540995803959155014540c014104002c4c0141290558000d101d000d001e55000d028541c0c03051103459540e4028031030703400356078082c1011800003446410034a42104419a0161a041da642a2007000041c960000c10304110040f10030010103826105401c1c905281c45810300c03042d5025260103488103810b1002a05104400f41c03090344810042c448100c050702132841c4a03840c1d00b080c82c0010300505141c081c0c1ca0160071046004961620803120150f50302b6450b83d50494014449240740e006900b268070200c0c15071000f07001c48020550b40801e44006482c95a0000911a1030321000741e80824010a000c0d00a02c010030034400452440c02214095941021585e8041184480100d10f4a0082d40c8041c00040c07640780d03110b805200c0412071007023406003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 3018955 1250 3017705 3017717
    0x30d060f14010e1327230c030a020603060105040b0304050c0a0501050c0304060f050721090603020906120601050f0304060c080f160804020307080d0509040c0f0801060806040f060305010b01 83
    0x1850066030142d030f00405440e4400041d500d02400d15102e0b40059202800c640740384400b07043c0800f1100c050344005071046403a100d19603286640749101c1101e031341c1d03c00d541500a00110300780e03c0200340c482030800c002078001c00c0b0000c0020321a90007003013150001c140010416580e03140a060654803901503103031040c483c01d60f1f0313000000e039503204000380ca06180c2620065443e10b46025000ea43e12403011001a060000621110021644502c1501e49041c02e000d900a201d514680c0001c1030301c0b885412950031f1500c10f12000d03d1070f89a090948101d8800740c0700119140d2214001a00e03103010344d030625141b00d04000100820810150440106460607890780740064032a8040420715103000c0b200c0500c0301580f074030302d0240e00e03200300d0185800c10300190607142140e803176101d41410580041e0400011400006424005007001e10034903481c044140b9100c0d01c0c1c9192440018401c0d03034103100c0d810402c4405000b0070084c0e80c0e181d009071142c1100047c10000540d40b8a07126000c0d000500145000c154 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 3020205 1250 3018955 3018989
    0x90b030106090606050313020114190201140705040e13050307080d050705040311040203071101020c07080c0301150b030a0608150703050a05010501021905070305010608061008010c0801090c02030d060f 88
    0x82c480c041d09041e40c4807034403514150760351060040100b0080884c1a0b04028000c194042c40f541c10708000c2a18494190340c004d4801128480a03003500c0b018002034020514403800c00c601140d1200a54040d40d4840c0c55880b20307525015288400c0c00c1104101501d0b030b0100040600421500900405440e65a001c051003c2c5c1ea40c24800d44050040344005004e035122140c188403a4a415402558000307950300b80090840c1310101410301b2a0001c443c110141e5201d198180b02025042010000070f000440007070045524641e001d103801901445000041c44e008000325102d240c8581010b0040c00c0c140048807020480181d41c1c441896003a40d04c0e02c0441c1c03808012a00e0b5a080b40035240c140c46d03043c0c004000000c420810514101c610100c103032458020040c0c040f0019a00b03020310401416a82d009010328241951915a191050307409082c9a03850125424130351900075413200d0443c1d01e44000010850a03c0c48141d04621458111034451894410080307204088019010f0590b10303c1321445212039 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 3021455 1250 3020205 3020219
    0x20706020c0a060f02031b24220203030d0c030501050108011d01030209070e03060901090209090304060207030206031e07020d020111090603010b030603030708030a0e060f01050906010309030203040f090b030106 92
    0x56610705115400c500c45502c1404694050320345000c561545204803480c040e650316400590500f101c6401322560050700d02040101c0c07403084008080c10b81c85607000c4845c148100f0400b8050341165148d0b13641000805400b056503401c0c01955582c1c207001d9018407280700c0e401c10050041101340241404288583c001080340c2404051501892007101a0b00740c07541d00315020008160802041d01c0e0411000ca9085201c03a20240001401035601100104280842e84108415075400802040c403540c0f0901003008025800107a01089a8068620503585d480c0c00034040c100380c030110480240c4005600601c1a810b5000506648006455000b0440c8100c00680c81c45284142da095541c0001c041c0018080d1b01c1a1174019500000300404407407a10005654130b258a400455645245555071001d07503720700710034840c4950210501e01603011944c14100000d052040103450f0904143e0307940d03079140c2058002c00031200500a0000d000602c5665900d0410107030000c0083c2c80c0c0a542031800018103d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 3022705 1250 3021455 3021463
    0x5041b02030307031e1d0d050f030708130609050a020f0105040b0405060d020904050424020301060c060213030212070302030f010509030403120c020405070504090515030c040c03060806070207030302070602 90
    0x4025030302561850300d60f003004070050085071004000d40324441c021020b000b03e8501c00d030003020b0041d0116203403914107120840c1c286042c4200900070b014080041d55401303401c0500b200c0c0d000d034190030032816940f944003580142d00c0c0365407401021245011900c80a00200180c10041c3c039100702c40a400002e035403401140d43d4003641c450b050408105100034001c2d403410034042c000c1d481a0380801824203541c880050207680040d1001c0d542985030940d580c0000750000401407003030880900561555242250041503a400700c10040c100f164003140c01c40c01c04010901d0b003001545c00070309641994011920183c1c403003540d4401284284150340e011a007413401070146610821182000d5401d01d8a59190084413840e40c02d1610304221504404d040165680d10803a8081c00880c4d172500d407070358101500c1004841000c1c2403200c00310100d48102e0341d190390000d403191041500303980106a207451508180c025005a407c44c052500564003000702c4168001001000c40f4001c5d402c030385445a84010690715 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 3023955 1250 3022705 3022751
    0x50c040902060d0903050d0501030b1f050109030b0601030b030a05010209120106030c030305090111030406081602010203060a03171e03040318030510020a090b1b07080c010c06050402010507020306100504 89
    0x4190b003404025201c034815488410700034001d0500c5803030030030844945c038100c034800d810072a1510f00200034041129040c1002a030081c0210309800545420900007801e50750303480c44010507142c03d4400080c9903901c03d40041c40d01c1a005401c680040b1120319102e1b0107900013000141c0515500898501c0441050164008403074100e5044030b00310b401c5031001c9031036504c144102c40c14030402903c250b40e0458200b000700300401d02270b9696901f41c1425040501c5040502c5020400c5a00500500265640e40040f01c8216503202c641982900003011000d1010700510030a840d0303140071403a4030034610302c0927001184158465a22000ca4503240074070010415828040540564061000200500101d60042111400c1c90500300401d581d00e201e50101c5521a020b400c20381d01c505545070104803010002c0201038842900030b04404882240001c0185002c0b0704090505512480440c055900880850300c41c03607009400d444540c03501d480300d014181043d22410380180d18040681030858003450078a22 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 3025205 1250 3023955 3023959
    0x703050a0b060f0702030c09010f050a06050c0606010c03020111040902070b010504020403030f0e01020c0a03030c02030d05040812071103060c030103050c010f0e04020d2a03060801020a050a12090618050c040902 92
    0x1081c6000b45164508031307041094200d130144100031220025580e540c8c0300d14002c14082c1c076525801c1d41460300344403039030442d076101209108044c062540c0000020411562085013817800401800e81d40c2012405401807424116084000103404580b100740c540003030040038040c20100d440c81c0da881c0140403c03445188009000542085101402140724076003502d0310044c14412500c0c4502171200040004c4c42c0c40c1d00840224802540410031030a042c07140424540407030501070300300f40c40d00ca51141c84401054a446400c840085c0741000c100110044210110000d03044860501d448020550640d0003800103403818440c50342210700c0c5600c60500c40030304001941e00c0c0302100d013814041c0006904030444961466440d00314031110000c2901101c0c0585007020400d20b40418015005400c98400b900050026401006080300040d0044120b400f000c0462a1422481d20101061401014a900700404090800d8031901c00403044007008486180208140c502540901c01008215001e14000035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 3026455 1250 3025205 3025207
    0x6030a03021504030e0901090b040b03070f0b070503070507060206010305100203060102100b060705011109130b06090d1703010f03020405010501081015030204180606080612070b0904020d020a03050703050a0b06 92
    0x11008421402c4060700913209081c11001d00701203000255810200342c1207000c85075610400414a1b240c1400b0ba9400d481c015006440da4030700300321010340c0d000f03500d005d16019054005844000c01c4420130454240c55040001e60704150b840e000002d4440c9401e201c1500d0328800c04060041c41c00c0140b0880f805210141c000300088030100021a001e0003907003516550100043c460040860801e0003001030341040301402c545e5450111b000c0007032034844040c000c0100d600d402c40308100c50312200110f400b0020308652810030840303d03141050200c042c7c4520300620701008400002c180010b400d000041d02e2003110107110036a00e440044407201d004990702da903030801e407890820145205a0000340c00183c00d1030098a81900c80c1c0300c01451640724400040c45a50320070b401c0256950015043c0e81142c001c50b0f020b6840072400440c03940c1d6070807a02400c045420005040c808075034a69040b6042e00c0b401041c255102c100540c4090001d1000310340741e202003400d05001039441d00c81d0707100b40c0d00b000030020300607 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 3027705 1250 3026455 3026473
    0x30c03070602071e080307032703030207030807020402090a060801050301050705090904030c1511040503010e010513030f0314010605030702010b040203070207030803040204021303050319050a0504120c0b031005040506030a0302 99
    0x1003100781003083c15410700e000210030200d0705490510080c035003103000e40c4440c600052700204c9141e4001c444480050840b0140c00140002a40420303500c0449401980b4951100180e0000400074850a188154071142010001400d03e801004e000c2c12105c048001b00304030f40d01d1800c1601c041c85900c031140e0b07200009200140001e401040400800c81c059061007602c600842a083c1c1200e00081944851034408102001a46002d000b02482140024020710150400e08850841001407280080c1400860704c2251803451003a0302481d07080b22065400342c0c49594684024181d644252080001542400d400c07094070b0800b07008490040c40035900408000317196854a0f070058001070000c03644140c080100341d111400136032400010390b01400166503038002040b042410481c11451003014400240112800150804152003c48003022141071919889117003c001001075070b0130140c44d140010061001460500d040141520010742e4100480c1e10350000301903541241079401001607205d8480 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 3028955 1250 3027705 3027719
    0x60a0e030a0c020d0f05060a020d0b030102040f03080d0b0405070804020906030604030909020703030209090106020d02160b0403060504150c0306060212030903030a0b0d050f01020307030f1b05031906080606030c0307060207 97
    0x76042042d40640380718405d42ea03081d5a5581043e10603640d0840064000c2206102d11048c0c0c469980440e1044000f18941840e0481c4091010f03101c0c40003814030b2401040c03100024209030800e8400800041c020042e6240c010f00140280005a0b4264021144100020041d05002030480d00854141e111f4206052030308001e03101a43c07005030b0840800d902800960590b4980301411400381500da00074180501600500920702034400301484044464000d0820914004000311002d0f0391300711601007032075500ea08051070b1210101d4002c485440c9001c03402d940b0607038143d00000c02e80d0711942c01e4404050031095400c42500042ea004c0307056800400204d0241481c1c0d0b40b2651407480c028001e802419100d480760f6052051070946608a650000204404290b00d4820b040c0400017800e020030038070702041d10b42401140503891203424003100001186540b4210820500303400980c560034405035880720040764490360240d0340240240f0030072242c010245030124605042d034003182c0c010100e644c9003c2c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 3030205 1250 3028955 3028969
    0x90604020a02010608060103080403031e05030601120603020303280201020703120b04090b09012007050a0b09011e090c060e090a0b0a050a0b0c07051c0303020d14010602060a0e030a0c02 81
    0x8a20701950342e18807001035560020b0028500039800b0b80c002c9500c3d1403031814064440340c10a0856840c2d00c201004e02c1d24541c0c5c00c038055070f422000c02e28180e290b80c04101c02540080140c0d420195051001161a00000f89000039103d28840444122098444d00d01c4080e8241d0142e4070740203000c07400b419040000d00c2c1c05a804000c0902000b400801c0c5041a40c9454040e040190703603c010f43d07519030041d20311208292800c16a031400b01201c0074589052511202d0312074501c0d68008007801c0c02c0308003181505900750003056240c04050174036040c90110f001c00100601100d030b030480d03c641b401003000801c5806491001c100070005409031000ea500d0403005401448000e000c43c2c1e1040c40c100010034280c550b50304200140c00ac9049142d03a40454003100d80c9802601c1d8041c9219241c208060300f25a540c00302010a4254541009610b55094880541c00380809054014020014000001e40183d000950720b00403030650070204106081d08050740d03128403840c81075034086201e52241400600303202c2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 3031455 1250 3030205 3030217
    0x1050f0409150908030f0702070e0a020a170903040303080604090c050d060609020d090209130c06050904020702040c09050a0e010803031302130e010e0706090305100b010903050106030b070e03030909060402 90
    0x41c076010781d000c0b01a00704903510a401070b1083c036004801c00521100011140740c00c800a1700003003600c42d24011105041690040c80d000c2c00d40d4003c160312151a01807104081c0e0015110700700c0d6010328000c035856076250014401540003404403408290326041503c2038056944d040700f40540114184004c5c070100441210044031180e03607541b4001001003e42c8041c00c0705002c441c0011505003044d0042210b5508090303e2111010100e0000c080060741070f05195044235603c2c145242c0b10800c0303000180003801441d03c065000b60401c03c4a02c40345030f02c66001c8054410403543d1450b0780d42c54107502c8210080902480c4200d600c00c0000c100410f4510383c90074100f9100a021a281402402c00d60b01605c1c40700c1040c850580d1200c50490302c0071400c1c00504040e1590b0314000d40e404c1d1440e10f61564552100180c210030543c1c402e40544180d00c5080540c02468110b402444220356030300d440c07002610100c580030002540240030f40200e14010088600c80d01d001440521541c43d11401c10009502003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 3032705 1250 3031455 3031463
    0x6080304150c080409050f0603010b0108040303200403060501060908030403030c06110412050a02010e010e030c0d0201020a080304110906060406050d110c01090503040312020d080c03070513080c0103110301050f0409 94
    0xc10152400070785500f00a0010b421000300200d01c030b0901c1d5840c8100c00c40c1c0500190b00c242d0514405405d40d981c00800700307034400d4240c90049598031018041e2691105105143c2010140c00a00441880820b810150403a80799507134040625690300016904d9005070b00004000458480420300802c0c0b05420042d070045038a085103181560700e1444181b45600b60300c0440315500403c650405640e0080c1659941c0d203002e081c10207828822000190710781010b101d2651040d13010414030800e59101b04290703208107510042c0d00c0da80e400d0a0030008154038090550502c50b8500800049940c10200b003600c048403241e44030030f82051204217103c00034000319213481d02c01100601581028036800d00406041030b000300003556440d410760400540021000e605c000c02c1d54400e64505c00d103654004501907200002800701d9480742c655130700c101d55a124600c040854448041c1c2c010407100804242c5041c0d0000980301017103008454105001580803d12915610210880801d405400d003504080c1d082841 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 3033955 1250 3032705 3032717
    0x4030f060f050702010e010b04021c050901020904020a020304090c021c03050a09020604120c090603020307030f060908030a06080c15030601031e020c0303010315020403050601030f060213060e040f0608030415 91
    0x44200034a0842c0c200b10303070240040c0e440b0b4500781c01d1003000788a901c40048003079400f54a00300c105d00c242c0808280200080d095142e9440c005410134600f0340c16101441001170041d5170710000c3d0b610095a0342c01900464200520301902c07045c540340005a42c0b42c2c040c000c04500c0510b004080d400b5401400000d004101c09611a0889401640ca000c01080544481225003080c0c400328100172100d9503150b008920060716140c3d0134030140c1e400042d20f4084941c00311a00e40000c7c901d01e40100600319a1000501c0150084140134640d800d07500400180c81140c4c0480e1045400c1108002d011100020003190300d0604002090300e41d4800c1c0c01200c0001002910b00550015906802040760b100c0b114440c400c1c0c001100500400550181d070004a42008000398201030440d2a4542c5813281884020820001c0b01508410000c1580644003840c0c100390420196076a00c0304050300d46da0500b5180f5100d1858007608010806c0c00d44964416110020f00440c149400d05200b2070207050614038003024454 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 3035205 1250 3033955 3033971
    0x3050f2211120604140f07080a0204020906040b04030b0f0601020a0c030b060d0b0109060e010807060516030e030609070305010506010c03020601120c0e01090c03060e0411010e0a05040903050c0c0a080304030f06 92
    0x8003c02070300703000d42e10a4078480d800945003007440d400d1901204001c40560050030040140480c001100030403e03404440040c2d039a100180064140e104503130005030411400f0800005004403250881c4c418103660b03081106603030b2800012a00c0e864846001000c908074120140f02099501e90078950060025242075041101a2104640e48030f00345c0c011002d16882c1d000c00e100c07407201003184c18010300c280390007400060b04044002e0070138090581044035940ca80ea6280b02414031034181c0c07400380d08025065642c02d00702a06c426450341d24500051340c456081101294107540f00b0301c1e5118120b600f50707000c1c2081c0e900f0650b00400d540b00e96202510020800200499149104003500b4024142c04100080d203480d4040050107903101680282c42d1040c98404110116101e180303000710202c02460140d5002e0010400984c0b20f030055080150030a29088140b02015080001810b03075103000000c50b818003a00408018820105018440c03250300309200400000d41c0d0110380230016445900d012030084 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 3036455 1250 3035205 3035239
    0x30e010e01020d0b0609031507020106180e0d080c04170a0503120405070605042102030f0601080705040509060403020a080c031e0301090f0c0e010507060209060a03050f2211 76
    0x140d5044000d004a95001070410340400320340c03140c0b10484109403142801d0040800000c0d45501c00c00f0105030900012000044880340f0070f500080281c801c00314080e00c00c1203108006e20003000d0880d100301040c4a580302c966401d9010b008405d00ca8000b03004154901420000f80070000700280c1c00850841c03080d02d01442c0003c41c240080c2c0407000106054000c0c40c501400c02d1403810708240d01c160103001c41000180101200072841840c061050012205004030510201785800c08081c03101010b0b0145600200d1600300101e4240c0484008940a20440c0c0b01d0280443d180c4005031001405030303100700c0904000605100140108501245c240c9003801414403100c03945c81e1318008031004400d0000014401005144a002400d5000b400200700c00c0a41c0d441c090891100c4182c1c090502401003008030070050603404650403c600a09001d888402d0303124050b0140c0b0040e00c1045d4518030500c00140c9011521140e032410502180c494400070780c684d00c44102c1d80c451064000d0300300550400454a80c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 3037705 1250 3036455 3036461
    0x215010306020304021003090308040b13020306180c03010209030c0d0c0b0a02030406080702060402030c060d060b040b04090b0d0c0506090a0905070c0507050114090423090f06060603010b0706050601030e01 90
    0x2907008000c05a568a032510400c43c00a40b4900c3d4a41070515090701c99000c0303903001034241c1e03000e90b0050884c807a61b126281c03404e481c0300399000d000350f240c8140020010062445480c40d40e48110403811149110200c80416082c4d006800031650140d2203444500000d10f0806031005500c2d0040341c6420f016502c41910703445650180c8526000341e80005001c0144a41c8407680681c00341c0c41d0710282c0300c282850f80c0000e40300c10b40001c0d820b100306408034140b81814080d42c810b07030080002e0704506580e107a07a000400501d400a1044540e130603d42084000a82411518858503684c03040341c840f8003a04050030020720b85c0080c03100c1c0d904a00102804109424a0f2081d00c1c00703500e00741c03140b02d138403070300b602d01140381ca2003d811241c10401c00a089000c01010070007900d2480f13404580228840039124200ca041007030701581d110044407a081440034080340810540305084405003662010b544650601c8180c4c4002e100e1034a210800304483d00c0816103c1c0d0000350001d40c145000315141100131031890039 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 3038955 1250 3037705 3037709
    0xa020a03060f03060207030f0302070b04020d110d0303050f070f020304061809180611040f140d05011103090607020c0a03020103020702010309020901090b091006020307020d050f030301090608010e0703020604050d03021501 97
    0x20315030011b804024903820000e040750b200983d14041d482c26807281c1e00e000c0c003404094802401707072441992400c01c204610384960781c51700e8040c2c14104242c0e15420018003402c000d50b504020f4000510109100301c5c41811401501c01582d0001d61400380740040c100c62683c400450b02010802c880c80101e682c0d042e82c001c0c00c7c600c036034504813414201050300381401162180500c0c1100031204000401c280e456002550084800085801594030342c1e070b801007051400420070081c06275107080052041c402c0071101a601408122007118215581e5403030990fa07a20242c070322180d00042c8030f14100010344c866001010320500c180340c007181010440e40441d00e41c030402e81201095940720070031031341d10b410035802455011200000002c8514070345807010303499205080019000350001721460003484010081c01c0c07007140d840300440c2d54135a5101c8045e0020b004a008112040d401c0240c00344200800003a40000c2c1c0c1c3e0010f0a20f49031a01c2c000410500c4540b05e8001c80a40c020400340c3e03141484207036130541c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 3040205 1250 3038955 3038963
    0x109030e0111150a020d06030b0903041505030105011d0402070506190c05031902090d1a06040b030c030c01180f120302010605030304030c03230604050c040b030706080a020a03060f03 80
    0x144105400c0000d014400b0b02c6001e041d15520035107003400701400a0041d503411500394100180c0e5203420107440310241546803c080d104040407011300800c1c040c00001003080f00c044503c22888001c100401702c0d4503100030700c00c1c180003600c8241c13402955181050641c0880a00400c010719065031592070506000045a080c1c0c044280604410650040c5000e082001100342c6403282c950b14082d42c2d800c000d928900c0c9000320003580451450380d20317212000d4010100c1d400403541c8540d000e9183c0c0f0780f20081c1080340c415020720b0404420001900b0006940c452071a40140a01414100d410044900c10300c4418800e01c410041940010340034000c0c200d01020702036029a00860300c03801d04029082d03800c01d03032106020354010001080801d154a02e420706903035105507043c2e200440b603246030b400900d2002c0046041c0c041d0390140410400c0c00261806c8411081d5000c0c058010800201503da031820f100790000304004900280e0f001c089680106440c1095003400103110351039201c40704000e001500121 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 3041455 1250 3040205 3040217
    0x1b020609070902070503030f04030306030c0e0a14010602060610031b0207051005040602070b0703090b031302040c03020a020a0201080603011104080a0b060904030f0e0301061e090506060304050604030c03050903010903 95
    0x104031640103024000181c200c2040640c5071070103a0340d64950313910000704418105c03644000800c1c02c2500ca9004103004581200f5480c2d0b002d03864030b128401014003911400c000e43c0c60a005410207802200989040b04c4107500501529910340003032009500030300340e1280801d65600000340d000442d0011500104d000d0360700501078103080c02c042c41600c920f070600e02014810107100030400b040d0f0001d40c1c20141da0b14051a1502c2765400c0c9401d41d5589019000308400390400310400c80f104141d0066000761318003c450600003000d0242040d012131080759400e0b00182c01c26a0b101e009940101c152a0300810301070000120520742c0b0880328259002500201200d402c07113004c1c60140099400600e81040e011641c4203040c1c00c280d940030f0a600c0b206016002806903007109002d0980e02035203e18010003031074210103062020780002c201150b030540100902c0e0380c5880c000c01d0031802e002007680e12941c0e1240c0100300e03d882e5500e0a0390648510101203003040301c00c0003101101d45082c00381c144464802d80b0780b8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 3042705 1250 3041455 3041461
    0x60602011103040c0b0d020c1e010b010306060f03020f07020a06050c0d0e010903060504050102190e0a0b070809060306030304030501020c070e01080606030601090f0e030c06010306140408030c030a1b0206 89
    0x80c2500c81414404402690510901012450403245102190703104200f43d42c2c1e8201000303244000e4010100c4003000c40c011060074031000112805201107040e9030384000c01c402a421001503040b9407a0340030f1440000c0c844002c1090f018000c0e8020300505451201c05801c0459690020300356000642111001550200319081c4c4104200622040c5000c1d6040902000c4031000000700f14140d244400b4000d03a45039030100303060180a40c11652000540491209020f45030407006d480718100c0d8403058050203005c40c00190405a40065885065100440500e80075040c000c00169820242c100c0303515000800c000400507900b44010101c100200000d8001c2c0c516004e00d102030071405900007501900700004114881d900443c4140c1910303401100014280b5001e15000d00815284150b40000d00c00001c06207015100001d04a048a01c51001030080c1c3d012969175001039042514010040300052001c516a0048000a1503020b00c003c00005104542e4007416038120104400c00740c0960050414 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 3043955 1250 3042705 3042707
    0x1020c0a0b060d03020604060b0d0f0302070e010801110313080408030a090801060b09030d03050702010e0304060908010506030a03050a050702010c0c0e04020301050906060307060c02060d060602030c010501150903020d14010204090606 102
    0x10740350348054221084148008503450194031130a0003040100311540d0341a48500d51307a01c05d46c00c1000c650304000e4030407070b203030741894042c4d50750005002e41074900307207007000001c0c0e0b090701401410050b030a42c40d02241076440340c56503141c5801c00e2a004998500d0709200201d1312140c1000605140455680c420b40c030a85080041400c5070a10382001c144240200001041501d0000e8880704850481c035000405070350f00c5100b02d005040c3c801c50b241c090300000038005200c55000f420380e800e903000c0070003c100c10744541c800c140e9281290b4000030080b62090082441c02e6009001600358640103046c04030700c0c0917640d55400c1402e095504400100001d0030107101c00d5007402d208071a44194250010b1102d0b05041002a6807032142e4440c410403c012441c460301191100d034241c501c201481c40040c04403d440700302c065241d410150041c500d80d031800780001014080c00c906901d642800f0380310510444d046409110151a12481c2511501d46d101100d50030030324244002c2004001d0118001201810210 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 3045205 1250 3043955 3043973
    0x905010c02061009060302060906090301110a02010b01111b1201060803070303020c06070207030206040918050105040c060f090b030c0309160b030a0605061806091804060902010f050c0c01030c0309020301020c0a 92
    0x1120a46521702402400142c403550104c4011900c122100390b02c2d600c280c1d00103805007081c85c03440220220301086480b0700313580540144a42c00826210801c200036034080013039640b215078522000c0c45942504000050800c009801411281000089811911001314a2030365128660880000e40d0000d00c01404c9407081c000389421980038405406e9580c996000101140181d00509800d959100134142c0c48900301950340c001d5541c000000c2c0218900750501000001080c441c40c00400c1880503070400d6213220f04d00020980f2400c0f2500781c2035441f0707070034044050f030401040005103105821419a03640149094030f0004d1070185103295403440e049030813400f50703940c60380054014107090003100c40c00b45008110041c0d01800b41e07030700b07030311080b10100040310107180400c010003144514041c00140070494001c0303a00207000b030b01c501241001c81c0c4811961361050000020172034011462807000c1d507219411040380f50f001403074046241d00d0241c0001303003264003100c21107403243c0c420f012490812001d41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 3046455 1250 3045205 3045209
    0x1080606010809030a121805010f020c12030f150a030f0b01060e030115050d0206090904050703051507020a060902060d020a03050f0901060302030a1e150203040308151c060905010c020610 82
    0x43c007850400e80c401a01a03c1152403100200b0920713140c101d21680700c482030000704007060f0000002e00c406010707809598003c0d400303036407030f6482c0e4090241503008581822086900074440f8441d81e40310342c0d0740d01d0701d000c441200a560903a072140b0308500c0000440e410f65608400d80d4014151040d007035241c00006000c6403100b00c1c0c4c6902a90500f800c0c54043d60703d1541c01001c45e54143c0b550b0000d904944001502c510500d02844d5100000500303220030300100080d02d0701a68400e03c101c52003103034480b0303c0c1d50a1603c21640540142e201c4050480051050b03000804560b10141c002030030800514403080a9030000395503880081c2c0d640003003020307808500030901d0b00000d0000c001c0040740d0840d00482d8a805a02d000900500c2c105401e144101582e60031040c001034008001241c0c00040c17480d054043e52081d141500011410004160410344030b2480001c0920000d0078200000c1700c801c003465400c800c05c2003d40310203680e08030070400314202307004401170320b61194007030000e510b00141d4072643d0164603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 3047705 1250 3046455 3046471
    0x8031201080705030709020c0304050301020a020304060e010c021309020102010605130903020601050d0803070809030403080706090b06090903030711010b0a0806060310110301140d050a060204170102030606090103020306011205010806060108 105
    0x140d181000f107514046024825030b901c0800150396819000a01442d40c46650b0041c1d425600c000340341303030505074041b018105175150341c0e4130030071589040070044075a00c072070030300180d4800c0d02e009420034100082d50116400f00d1040c000800c0d0580e803107000401d040b0030780c580118600d403039098803002c040d41030042c1805894202c5030019102c14544912495000090a420900c0059004181086d40070070135207004542c8044125a941c0e00c52420b1000780a09032007c80c1c0d03080800c4042001d07440d109204a00c1401c5c0e11004500f181d80340c240440e0ba081010315864250f55841c254a8800e40340d1440400107414071000501c80d600b030800515290031421100742c48600e1401d24040b181007400d90840741110b04020046170280f901400044904900c0c0000074801d00c00c0728030990810076140c0240c002c4032503000c0940e6005070100c540c2800e034441105c1b4540c5c088c13803c20448403150300907805503130070880600d05030440d1b0f0f6189076031404440e005c1e041003072070358403150400c0700c0366034441e400030b80c40b81007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 3048955 1250 3047705 3047713
    0x170405030706031b08040c030f0302150601030c0c0209060406030b0103060501060f0c05060402012a1b0803040e060907050f03070c050c100f0c0302010f14040510050118150e010803120108 82
    0x11070701c448802c181030980703004c00c208040b004141400b00440f8401c1c0955004403000030400401d1401941d41d5000b4200301f00f0080c11080024241e600901c1021001c144584492031484059400c01c0312011005100d02d07440366452101201043e40c84e02e0b00c6005e1849050005150350418a0184c900d0381d080480780c007045441c0407084005038000c26000e0304141e0a007460710210101e10b5188a80c0006004061030032200c00b2949403d1189800c8404145298200b800c2c1d5401d0700c411040e80c403481980924100708501700c0c081036480c00d00280d46548a420351402d035040c85214960600e480e8801c1d10a140040c104d902d9100c180a01800304040a50040300d040000022800001e0a03122601c22500309010700c4503541d40c1032500039080a200c40c450108100300c05269a1403007002640d00f41c90644c0c04c0c1c419480528542c0845101e090f058a050221001d100b51180702000302510021820980f00c019007000000c41610280c401c40c003804400300910f0b04c030007920119500369030059000d002a90304c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 3050205 1250 3048955 3048971
    0x603030304081606060b03040302061501020705030a0305030a02090307030c091103060f040506030c0a06030603110603011a07081303080307030f05060901090b04060e1e0108010c020d0e040917040503070603 90
    0x2c80404580e405070248141c107288000302c4c2042802045141d0146148480000170802050f602048442c0301c0c1a0074011040d0b244900c0c801280d17a079501e8001d541e019446004058040381c0144c024641c004200300015250a038200c002ca414280c00750320441e80d06c00440c3c0c06000148980c080c05040613608020705085142c54070004601000b25044c81c5d0081c0d50b1034003c224503407801d10005207200006000104180d42e1903030010010b00712444260360f0308040f41c440c090300b13141150803641241d10403002074880b0401e00d4407518060b44411001c6071000000c0019032850f07441d161040c0011030003040b0003034a91600718000750544801c501c040600c54509001c0182945c5d50100c02415034041000c001000b0000e2008a0020036590f003004100c001e0500c200111a21050541c0c00c42020203108020a81d9a0361f0090b803d8a1411440c3e030050b820031034008507420308c50800c500c01024001e10108078a001750301c1e90409840290100c01d0212800181889141000c2120340001c000c28541000000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 3051455 1250 3050205 3050213
    0x10203090c04111e0a1d030604031b06060810050105040c020706031104050301020f0910110604020603040201090b160501270602030406090519020307060e090604050415091401050603030304 83
    0xc0c1e90511941c4103a03660000307070480082a20981c0e942000c00c10b80301c00e103208104280a40354000c2540c0c4800268903a0031110078012400c0d4504600c00c01074000c0c0000e880b02d65081d182c0082a00404d444d00d55000191004030720540501802415400041c0a400401d21080f4041d82c005812050040c1e00f0864026160380d4000b41d10307803c6401e686000104514520305048a510035548016410b60010407082c0448095a00800c46c3c04d808031a05203024841510070742d03010301140c54503103507038008900203005410000011079005105141803410151100319070b0303440d60048070841407402c600050900400c8402d20882c40308003040303034031052840c2004100640c05400608000c4c003094000c0003207420445160040b41c5050341c0081905c0400c3c4412500c035410441419080e4401d2144440000308980290080c00b803040026201c40082c0c1e1350038003031001416000d00101c5102d51036103600d84040109220300b04502d403183c4500b1a00d1500d52403001c1c05d540000c1c0440b4401d4108006000005e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 3052705 1250 3051455 3051463
    0x9030201050d0b04060801060608010e0604060503070e0a020d020703080405061b0d02070212010903050a090b090a030210020f0d0c0302070e060604030f06150303080103120207061407050106030f0302150901020309 93
    0x2c41540d021500d2001d22003c075016040d03d5010300d400750b09018000c2441c9401c890282d0690344481c6255245d0395502c010081a01c910788913203501500302140905c51141070450003644400212405480c004000d48a80103d921440c0b060f4001807200b000e200070070400b4480715070044074000180c5440200030700c800c2d80324850341c1d10001940b580041d10404540b183e001d44e08513048401d000700083c1d941814040c0c050340c8001d00790000103d40c2c1c072011550420280c1a02e40410b4082d042080d05411a4244003882e40d168880c0800d40c843c4400981c10213008221010090410390344121002c0220300d0041d241c0440340e0000a400f5140f9030400c509a150f280a843c116604102c003600c0103500d03070402500030110040c000c010b0111000c030100600d034210603610b04803481400710b4514402c40c844202d80f00c003490301900d00010070204070240420303000340103031000390f01a0000040d06642c079960758074100304601e411000358000c100038503c2e903880d0071800c5a0000200c0c0c0290b2842c41c3c026a540e807a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 3053955 1250 3052705 3052717
    0x50403080604090c090504060608060a06030305040302010e06090a14190503060708070c080c0105040c050d0209010302060c01060807090b040606020609060601081504050a0608010b0301060303090b03060328050106060903020105 99
    0xc90fa035251040c14401c28800400c001c0089000400540c2860304008000d004140603803403080c4250070204034000414850141165019952941411f0842d030044030303c601c5004101c1d50044041c04414070503603880001c01c004040d1001d400140c0041c01d07043c07180c0c0003130a64103608542c0511000304031548010541d25882441c525020290f540c49540595a43e504940b01501000700811114402c040551001e80503602800d0050b945958034010401c215011003002034101c07000718010001811b018002d064481088000840c0301501c03201d150307242c0742d0140d01c854541a15038000704060304162066070003070310880c03002e40a945001c800c1103548440141405040156401c00621000862007a801d00058001c10a0005007805011040a42203501940d0f540c0c3d40b0300390b00041c05180511500046031350507100c03111801c0c07805c103251b08103400c0182041c0e0180a1030480100c0004859042901b0780c40f10b9000ca003413062682460b03403c4078200e80012061101035202840541c0e001070035208 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 3055205 1250 3053955 3053959
    0x1009050901090c0507051c02120403240209060705070e0c03060108011418070206090f0304080c010c0203010906022205010c021c0f020a081506040203060105040618030206130602100504030806 84
    0x700c2c50000d0f01d0482d0540324656001d003890040e44400e07001d091161034043c2c2d0310352541d422200b001d55041e90005017481588401884007010b1000808400904003501c3e660310106000182001c400c403001c034030146d010b408101c80c103810a00050101288540c006c58101902d0703584a401c0d850708200291034200180180d8440c00305528141a02c0d80d6000a005204600d510000045040026000e540d615083e148001039004054030b4064034240042030320101c1e60351000a05103500860010f4490003114802039815549071480e403000300c1d9082c0010301c0c2c509280381904149443c0f442c40d03022038200503040f8904020048000d4000360781c400700120f90307121140b840310584000e6440c0c6003148024070200250080782c80c2d0000901e0240108880c0c00e809404640b0301038640e60102004101d1000311401342c081401800709000d407502c1815200600781c110102c095130641c0704e80005900341c00200441c500380700d03c2141440f1103507051240240c044a140c07418003403800c10f5500a0001c4000403d802c2c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 3056455 1250 3055205 3055211
    0x3010b070c03020402040303030507020606012c03010207060e0c0a090e030406030203220501050a0605040e0d080c0f0c0706030e0312010e0901060308180306060105030708010b090d0203030d050105100905090109 92
    0x500c55841000741c001c5070700610441d601c595a18010b07000d03110854138000076025000008040b940901040c4490300c940c0881d460340b48011030074800010201002064041d0f40c280a80800612940300e003182080040005043e4180648100600c0004a400c84084182000924602008008217646c00d4803c94240503031295100d06041040b00800245028144404c01000d81803080651006e8040c8000241c1808070b2500c90341070009076150050760080340d0344907039009031202c2e2040b507080c0d800610000540c0e14201c1c1c240740000640d0040c22041d1816000302c80c0401869030944100d40b04522508042c50810030301030b0084007040c105103d507000781c2c0d01e41400501c00d4002940500040d5a02001c542e03100c4c14001554484400341100f03841c024418100400d00b10740c003c0041c1c0e032144907031f6a034a0070640c4c01e060800f02c2c40e030414000180c1282c0260b103542e00680d810f1000e000140c0046c0c000050540c904420020345413500e134441c0080c8a6032403070038445911100e19141c15184001804 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 3057561 1106 3056455 3056467
    0x30f020f03010306110405090c0c0d081302010c0203010e0d201911010c0807050102070501050105040615050c03070f0803010f150905090702070e070207090f060b03010b 74
    0x18415030801030004000184d241d42080b14108403a07110345041550b03400c0440c8884d034054807402e6000201040b11000e42d2802c000070404140c40d03280291031400c080c0c0030f41103a106a0000a070400c41d89403042420754400350400510328544108442d1054000ca00c0182180d4682c8a205801c00005081c1c1110840008400e19a100c8144540341a0303905a40d605a1112403d0b801c0342c1445800d020700c1e400300c0c09075030181c10344c14080c00c009a520601807500c01d08580301604502e104910300742051180565015001e20020428100075981c0c0519101d800d2460180c0c0000505040303003083c049003003140c0da1019604a1380340145d1030441607102d03848a0707140d0031000c141351300042101c4000c2005241220503207410444a006541c20191a681c0702c24440f10200c3e104005640042000c1201c00070620805000101c401c10800540c0d042100102036071006210f8000b03410703808180 = true := by decide +kernel

theorem cover : BRFrame.Cov 2877705 3057561 := by
  have h0 := BRFrame.cov_init 2877705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2877705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 2877705 ≤ n) (h2 : n < 3057561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
