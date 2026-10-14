-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2979
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:18:35.077209+00:00
-- url     : https://prove2.me/submissions/47e03c97-ff95-4d5f-9bf7-54bdca4eca33

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 535611510 ≤ n < 535791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 535612760 1250 535611510 535611551
    0xd022404020307060807020c03010914070812120c070c0f030c090c0e12010b0a03110a06110a0303090c052106010f0e0a2c070602161d15040906 63
    0xa400050224140310140c1c42c000384000a580b61820001c1c12622100c0050b442d00104140c9280e05608040340780c02007200c0040840b4041d8180004ca07105540c0342e40c669612004a07529003038403544140081407400b0713809080f40d60800d420141e280d15112039621001040103082d0440503060588900420400c502500200018200c800007081a00c42d411001820806a00d803241c1c03240c1903190004000c95000e5000f05841e040003420501c0351543c0b031801c901400008070145100e11400e490004556004004200e90010030390007924000c0e000b41c0e815002001100004d50384582030304c0d004a100e8a034044a086810107110200041d102c8800099180c500c05800030546481019400c00200e8001981c0d503030440042000452190350f84030429421108000b0b03001142004000c2d82c13040f9407000301e8081e003500d0705903081d11545808440807492020040c071034a0a218088000a04d4500050980f250006a8404407017010a030040000d070a40345d092100303503607565070740030050b80341404903034034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 535614010 1250 535612760 535612813
    0x170c030d05090601150e0f120f011a0d2112020c100608031309020d020c01110705011b050a03020c01140a0c0905041a1903061b030c0c21020309030d02 66
    0x200d100f4503141035002015a0078024486001c0c01448a1f41c4034039a41c0c0f2000141604070071812508007480100c02a4003800e8042618024074054048215040c01c100c2140c01d8000e03001250750001c0b9007140c01083c07510f00c081616100f007112101651010580070f00003041501c50140052220f03128040801c1c08541055202100c00d50041040010410400070000b04855840b80010380310910074030f00c10041c0c86202009142946401a07a000114800340542111800b40000b0017401280e540203505541d0540c01d0000030031401c0c40580c1c01c45110350000d0511102120000c540c070720300c90743c0c0d164842d102603c18564440c2c445040c030295a500000c0440146402c88040c0110007010702c00001d1030000303600d4a0300440010212103156600e440d040001543c1c0b04a04026030003e2111a0811455404c2c42400013030822080f01d914034800c0a4000c040c40d0440507201e00710184c82800720044480e0181401540000d1080700107a50b424001e01005261039006004030342d500041010302005180c65 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 535615260 1250 535614010 535614029
    0xf0209090d080a020702060d0207030906090e04050337020606010323010504020f04030b040b1501030b030c04240b19020f0a0f0201030b06070c03021005070f170c030d05090601 77
    0x7020728665008600a81003a8420b0300182e88400a00200d00d2901c140002d85048900000d05281019840900c5c0782c12640b031071351241c140a848226403183e506050b00c001e019a481400740202c0d8200401c2c409c42d025003009081c1d0b542c508000d00c02165146128030340da000d600894200070310765816028003040c000346042144d21400240000845004040c01400c1c015070703020980c040c50001c0c00003101c0281d604000001524030f043d2400c0c42d08a44c003150035003026101100000c410354081c0c00b42c202524002406010251001024000204180c0d6440500012095138041e101c09056210101412100c03030046c2c0e84090343c417601d05520082110310300456000c1d20032030b030302a03502050010000c0c0d071100682103a0141400100c0161404680c1141c1c01040059064108000d01e520102264403e444081440c0e003506419a10303401242d10151a0031004542100002c0c056410802240700820321242040043d4081c03034034507001241c1c4902c429503128140aa284ca00304010340c0140440c20 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 535616510 1250 535615260 535615273
    0x7030c031d0a0b100803030a0608160305060402010e063711250f06030f0c020303100e1e040f030801050a050a060302090102011b0e1903020d02061602030a0f020909 72
    0x4000341d0b2059600c00240c2000e51900c041400b5010b56440a0b008005000441c0c1d00c07401d1100c40040200010304c030380280c5101e01440c400400000c44c80180031070340c003c2c016100d5a40d030740e001581e46c1603405610b0b42d0300080c200403003090b1110440c00c00a04c52002814011808010350003020300c02c8080a41c40d06004a02c0d5404002800006844c3d0444c00d17814005408c1d4840200c41c03000c0007005421402402e0b0141102282e02c030751540c8a1000e10f90500010711112850980c1030b81c50784410303952a51a00900360040c454a145501d803560031080d8004a1590307407001100060780c000059404031800f1310f440c00e44005141d40042070b00c0c050542115400d40b660710302400a400d6621f54400d13102070540200713411026078003e602120036100c00c980341180303995400000404403000441c1851003807803840760705015550200b05007000d85e0740c0038082c60340344041ca808000d007980000801110440101c01c441005031418800b03183c010380309040c1180e0560a80c81086440391008142080940c03008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 535617760 1250 535616510 535616561
    0xa06030b0f0d050604020d0507084207110c030105070302031e15301f050c0a2f0303100b07050c041104050a0305030904060b1219060e07030c03 63
    0x13103415900300b94126580000401c0c1d40c1303810b9090619640c0103003160300907240c0882c5000742c0000d11002031607141010b8510755154110100708101d030b090a0841c5411801c0002e50030078050000c03581420b661000300c645000064001900b5103600300c031000d00290b0003000340885600c0e082525000001120317145e814a00e4901142044002c821201c54843d510040c121101e442c076008480d27a52a4914600402c1020715510f02981c6540d180308a018890113a1071100c1401828030440d40a45c640803841481d09500c1c0d03408940100511a801c0c0d1210180c840c101c0c90f2407a01d540c80c20303410300007101440c0c803894183c4a900c00c034611030303008040601c020406000001c0c4c000c602c042d82e551003101c00241000c14041c42004a010725003115403c40103092021041c03140000180c0044001110301348111611410141403a018040c003280407150b1010104010409080b804816550218030003c0c4440d51140200ca262400791840c1c00440d5550b0440400c0c1030781030043c0e000c946154401c0c0d40010078036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 535619010 1250 535617760 535617763
    0x910020a0308070e0f04050702150109110405130b030304080d020d03060b12190e01050103060c090602030307320c010f11040b0d0f0903080f0a05040804050f01020c0a06030b0f0d05 79
    0x140f014080100e02103140b00e069480070710122420001078000c001e54a0300b00c002a503141820081c0e0f41d6403842e400d00000c3e48969500504c60070314001c01e5854200351420040c007850f40070601e1450480790300c5130307003030395007038408102910040c40441c0042010011030440071381480458002d00b0101b43c01c01c2c10078060340c1d050100b01e410100c40405207000300d60329150600311ba00b1103d2429043c8500708a600c88000f80150072241c1628010901000a115a6801550800b0840c468000503800074400a99030340d0180c04c4c1050318030211750300b031220006c908480d040384800c2e0f120202040000420b08584a92092091080c08001c1d10020808003e010000d03442c03034019031085103a40c81001942000c4106142c01801641028071400c3c8100d82903450080d001c0c40013280c11050110b5001c0c002030902080e03004c1e0500031a00041c0b1141307050305020501101401000743c0d1419485960405261a2980d10781000146007540c0c0028500e100700007045081000e94818a200700c0b090040200440c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 535620260 1250 535619010 535619027
    0x10080705011d0a0f0f03051203280e03030c0406021b030c06070f06110405030f0313060e030f0a0b060f0103091208040c0b0307080f090f0a23070b0910020a03 69
    0x8580c0500c414070700b00840010b20a00440e0002076100140300000610845040c1d04003007505e12550640705030400c5181c26600c0d5020850789001041500d01c102c568120b601c0d01070340d0140300c5440d13010680e0009400c09a15543c029035041a09010000f03081001e0b65043c000c5051408100785504d100107141c1c40081e580311501010035108101c0040c0036010480b1401500321700b41e038404828041049900300e0010203800c64030400c0d0103400ba4541164042c00003104852081e81c03d601d0300016036007454000c83c0d01e4446001c94a406205841e000707880c0700c00400689518500c00c01c0c0b00840361400f02c050003450101c1500450605040c4215400020050451200c81c103c041c80c1801450b555420031002c4c54503030340d00030309050307000000340000958410800c92003240c40d02e0700a99143c0324442d006a0b01c1000c81741c50703d5a40c0100b1841c5000030800c409803440c0c032142100000203503c0c0c0d824240c0c180b500f280d00081c040f1100054032500f80c14400d0064a000c1e500303001070035201046440141c207400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 535621510 1250 535620260 535620287
    0x201020c04110d0609060503010b101d1c1b0b0918071b050f06010515030402090421110d02011e090f0611030a050105030c18060a1208031008070501 65
    0x1620b80022084288000042e150009000c4609000d0b240d900c0300d88000501035402503600a50a00c502140035051920a10010307450564505e07005080701c40d8202144102d038020f2a50101c04440c050110300300c55807046020324081e0910306e01d1840b01082c11809020140d1114182c800240100d00031591214048402d078098041021070030b60710b01200b22824084a03444404030500304150303900740100040da014540300004219005130340c0741d0007044210700c810840e02c08810713010000680141400c1c1542904140b15030420150304441060b001c40020000305440300003803e62000f2050524200800304811200340020051150b8500000c0740103002002c0f0314135032a4403801e101c41041f0601d2603142c100c58108104104406c0d864014407480c1c0c0c0f050300c0d5014060f0801c400443c0618000c03510401c2c1001c000d0845a48004801120344102c0c0000d0600f5845202094001100921060400e01180c0309859842da245810006117042c104560445901c40e8070243c0140b00c41d0745c100c8241c55005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 535622760 1250 535621510 535621519
    0x40e010c0f03230108030c06091603023a150908311409061801051005070f03050714030c0a240608010506040c030b06030106030519060806220201020c 66
    0x1185881c20440b0041d44202107000d606690f48000100803602002400261501ea01910001d444a0070540da646906c40290444183c1080c0200010f1906409d2800011a95112450712020031074005450403140042e42040c2d05400e00000104022400035500c4603a40d030300d00700702d2441c1e01d4039003d500d4000c0f0100800700c1441220041a800c41400710101076810380040d42c1c4607a81c0381c07910110302c0c0d0320844110303010b600301d00081f90152504070b41402240a00400c0b0007078aa1034541000300214204130f1703080c1400410803407000801d05004003000301c580a5103500b90340e22080e01c0c205041802c4036000645030b070424400000383d02c00c007282d5050103540100c1e0311442c1141e01028120b00644103008a502e292400e500001c2c65032064105901c1a4001c0b0f43c10050082540c8055081d2803001c43c0e500d40c4060308200503c645800f075881650065081540080c0000e4040e01c0c100841d40035401030411035201c1c9040150358001740c13019103048070160003843d810104590010b50350b00c1c0f00b03140d5035205 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 535624010 1250 535622760 535622771
    0x24041a1801050a0213060c050a030e0d1a0f01050a140f060d2306031b0d08090303040303020a150c050d0902030127020307090216060c1814040e010c0f03 67
    0x4040045001001000600000708298100361a0f1071000794080d8410b036007aa551110001006401285c6001c1b42a410002400303010030f09603822110242d40c001c803035034018441104540854010b920300b10912800390a1056242000c008817505800c050384494401c03001074500340040c0c0446c0303018050300300e03081d07412000180750072002600301c1c045c0c0342c11200154500321074070000c0c5456000200358150113552800c015154001032503100e04440c9010100c1c0401c501207291303181800e030746001075140107810070707418840d060000070308562080d401640140d00409402082c003000c43c0c0720103585101c0100c1007080c8610042d01404a02500c401d001180d0f944001d404150348003900030100104405040410354079481c0c0d000302c5088800c0800764024802c1042c00300c3c440825200303c6104505440340600b01040d6a62420081c2c1284404030040001b19403081400c0c9042c10b0548001d04001003402591079950018031045407482444074503541e0401403041082e60304000ca2001c2203c1515000c2030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 535625260 1250 535624010 535624021
    0x1241206021c090503090109090515010c052e06060e090103110a0b0408030a0809010204050904080a03090c090203041b030206030c0912030307020a03021005010807231224041a 77
    0xc100340070b50904004103051480c40d4040000120040c51500402d885100d017640c0c0707031043c2d01e08030740c011548100150350070f0315403080544c0121600c103003c078840c80c00c9076121300960b8034100d82c00c0a44102441d14103003040e01e5054418050041901500c16490002454100c80c2d00103400300c0700600c40035190f01c0b01e5041601054440c0d0080074007034503100244a540d42e41d40c0081341d50341e92000740b035040062540303400306032214810300807101101c000504107202a21203444040840d449039031720030306040d03890040d01c00203900c240007403006242c0c1c03000050700d0303280509100d031404020011070114820188014001030707075581c050765040704080b0440c80d207800d410b83c04100118413091070b11809100100030030010650007d0050400c0f4483d50030303214420340d180050411340f1b6081c0581d603001d4107c0401440300385142e5039031051415030b200c03103480040720346004203603501d881c00250040354000520001c0d02d0030508a000094900090a02000d85007585500322250304003501800c5084d0602d01068 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 535626510 1250 535625260 535625287
    0x11d100b0904150e0105040b010804053403030c0c0501020d0f0815090903030a0608031c2a021e15040623070503090606090408090d1b080124120602 65
    0x2100028080fa0524901d034980b40070589020091107550b200c4d40c100304100b2001c2d48500c82a6000390340c01002440c9501c1d01c20015441c0203c00c0050106135030140d039171102c2e81c207612540440254000c1e25206103080040c10f2411403e207040e000641550700a02c2d02c8080e5a501c401c8100000300d8925244140391034503030b0168140c0c0130600e001c982c0000508141316003d80b011009502811a1300341c01c0088541c4d45200e640c4034068035588482c0880784540707119401c2030941080c0440122410512814068115280f400e407920a44060040c0e01480c0400400814124101c441d0049100100985202a5a900b03007209004000400b03694941e641a0301581c880c1080482e0125500400001d40ca81900020503940044a04202c0e900c164004500103051500b64180125005606a80b508801e03400303001c044404018119100403001d500440e8460080c40740c2c90141c41100000704040303442200e09004004c0d01e401100d012000ca550400c100c00f40c101801040716403101004d6100c0600c44c001c1c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 535627760 1250 535626510 535626521
    0x40903050904020c16050d0510180c03050102090906010302040f0b0c03040807150f030b01080f1b030a0b010e0a0b04030b0405011b17090c130e070302060c06011d100b0904 75
    0x5540143c00410f88404000e40454a07844e01794119001d03541d03081d0303140100403505040c1031003d02540c2010107401038032903c542000040482149195003400c0e4103642d5420800c0303250303009440700e0f54003192a00103445c06e218001c3d00030800f46000e6050600b000950ba5400041d4848c07469414000078080205850034019500107088480607150030fa50b8818044100c555400300c01030010702c0212110320300f14043d200707052011006035580c10884c0d80d8600082946c6e00050b0421800351982c4e001e0030504000c184c0113601c0341c03404ea80045405850311001500c4190368401c254401c514a0000b80614650001030b0350480c4c1e04100002c03200d4985003846401000d60541c2051742101a401e4110003540004041458214803034031895941d48605c201515205101e510a51102004510194110341504002024800c0c1d03800da5060070b941c4d50006085a0220300700040395002007004118200380c00001082e400f02d0200c80ca0803900d0b011240c0b103040d030030600408074001030100b24641240c6132035118 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 535629010 1250 535627760 535627777
    0x306040b0d06060f2117030702010e0d0225050d0803180d0c200a1e090501180509030403120f17191d0c0d0609170307020d0302031504090305 62
    0xc01c0030b65140d03139200402e00968010000c00c0030205001d080c020380c01128221240d41c2000c040d602c4007017400200302c895840504660110340d2106040004030a09100708480c0001c070740c00502811100740e80000b2810400781e1050600c40b0443ca080145488910380e020315258000c559550303035541c0800404003421940c450511520a907000a040d071a004040101414000c45c040440419100518030095190410f85034108240c401c04000010440c00c401c001106ca410800c5905a00c070f0040404440d400da0140d4408944c2d201c2c451200c46442c4a51500004aa0040d61030f207404d64551a140c94401c484a03820400060000076405102c1c030004e2040d040b10328240c50940c100306448412505034091203481052410303032981410440c044801446207205005001c41401d21410824200e50510f019503485868101100c00103420542000f1400f6046d0440b90b16410b0040c0002d190030b480300300340414544100f0034800e0b09030081040340002c039030445d07001c6016001842d013120640680040e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 535630260 1250 535629010 535629023
    0xf0d0c06050c0f070c091d0c0d02010306091410150504031103030d020c01091103210705100e0d021510120221071d010f150e0d08030103020915060306040b0d 69
    0x40003001c0102c580c1543c0211000c1700c02c184001d203187d07103040d10118600091002154440500c421140c1402e004c12140c15005041c0019000c0c0c0e01e0085600f40c0c2d03445040101129040701c2044046c031030040c5030714003428080b010a520403207001c80184c018441c1d400090400741c210000e10409550400c02c44094440c8001c00755280c1c2e403041034a070b018101544003200c0343c0d6030483c000002c41c00d00003180c00400070200e0580b0612400d11144180780e42c082001540c20380541c1c00181140010313406a00b240060b204000d11f6180f410f6040241060f129010310841c02404000303012000010790340a20544a1030310100345810306502c002111003031121212101e420064942c1050803002040d918100c5c0d0740e09011066515040350004003010003401822580c40c0f05480c14000885200c1941f010750b810b074103010154200311070000d450080f000300116200360000006004604103551060b0b0004114211080c000820f440000c580740001171081c0d02950b6901030500c2e040d0f070b80c0071b24202903580048 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 535631510 1250 535630260 535630267
    0x903070306050a0b030c101d041505120303011a0d0f060906330f2001020301210c06120902180901060b0f0706150801021b0f0d0c06050c0f 61
    0xa005000342004a58203c80180390224500701c0b0b0030042845074030f8403c01031020004080303016050f14400300f00321088a4078401e420100140ea240c070f100d18410800226900d00400303180604003c3d0b030707411341000c950740c0340c10510041044494071403c43c031107540c100d06150b840d42c1544100304000e2444540e9030f100c16090030341c0003448030b10381d600000a64103010710241c11034446040d055003005400701518482c0040c0903041c0030840c0b203620300410f0390059251038072008281400040340703050541007105103650f000004024160407421141d08140f080e80040003d1005916012031034203591080c80301740403a8030403441ca042d4180e03210f031840550080002060000d01c40280d10007010854819565620f4042c000c1a000e1103401560360b82d42c4610f00b80380c42d0601c50340d6410040c0801074104030350310206c0ca401003803c1c0c40a0003c1c0401d03011341590341c040822040d00c40380c1f40c101080e070854469000500781c08401c1e540841c03142800764000d0307800700301c90320703800318045651291442c0d907110b000c00413 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 535632760 1250 535631510 535631513
    0x606071a0a0b030c0a09020705011b0503060a0609152f010b0a0504062409120303050402040b0603101a16050d0f080f0106111509161205060f0a0209030703 68
    0x90200d1030040050a2003005a04440d006050351020302c10280d030341c40842020104500b210a800500c5054803900021030110030740281c400b101c01039144201e0104074048204982420084c074500014141c03807a110403007910307150f40c6c014481d6401c058401007013051020203644a0b000c6000c441c2804100345414482c50035415400e00800544090602c64500c3c05030000e843e01c0c181c06100107035441d1059499a104488215460307003003180840005100d020100010420035905d003e44002e07000c1d440101d224030b0648101b000722481030303142034412541441401103030719a80d5100d105540340c0c2c3e1000342c1401c0586c1c3c0a01654090508040d56140d0780703c0d000e4007089000708e54131480f82001d80300c40c0701545810405813003145c012101c00300040341035001000401c1c0b08100300c00c0306d0284031054800030400c0031060402d206046441e0b0031540e124620500421419140400041038450411010501c41e9500d1030f440d20317000b03001600f0a40304000407c95403101c1e981240c109200c01030031202c2080e940d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 535634010 1250 535632760 535632803
    0x509031827090304081011250c170f0f0d03020c0703020303030408070b0c07030c0f110d212606150a02010501090506040b0a030305030c0706060b090f0102160b03060607 74
    0x900036450725020751901c2c0c5000d40b100307028190070010350321840c0303081100c2d100405140c1d10444100035448281050303500d0110380f1508403000a018ac20a9580b131211ba0400d0740d6280040e942c0721544550b0041c081031218103000701c1d00c2c3c58a4501c2c0d00c0d02503a86c50203c3d508034508021038001941c107000000500c81001001001025101c2c81810f401038142c0d10b4141400d0140118040030340414101101c0d200001ca22036a03010710740788200d2010040080302d102007005030416000840700b00c0003c40801c880040ea0400c200b804d000e05240c00089038103004880c000020142e540b00c0c0b00400030002080440d604c00b443c0c0003001c00e400741903e499003411070b0f000b400b8040038070400c0051840d00c00030036a107081c107006110304c0b120060320340b01c242455643c0413121948000d04401050750140284800128240586d2008110581300300392078180e09010003e031f40d010010380380c0c1550701c081d0b405807072040402e52190440f64034081c40c60f120307a58440440e0040c450362400820030740744800c5c860200d401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 535635260 1250 535634010 535634017
    0x5010f090c0806010b030613020c01150503010f0c0909051b0a0f0e010e0907080c040b18040f050906010b0d020d1b020d08151504051207060305090318270903 69
    0x40e0108100282e036101240c1e11244280242028040c00300001001400c000c900c6030301a80c030760349005180c0700301170f00c03844d084542e000e8005040c4004000100047d03d806d004010468160300740c1040716020311031014010008500c1080074003501ca200050050f01d2101c17036049902458483e081d5111a080030080500c0c2c82e05815901103014607824031003035441940c0e0b0210010028200c0c807402d8489075004d0700e50b920001e040d071291640403c00480c92420050142c4010380303801514410f030410601c00c02c004e80c1c400190903179aa900c0d003c100709120600080482c115401c0c2240340d0360b48d107000c00b5000040d1042c0700142c80707001d060041030181c0c000c0407666000c90345035513825540c9031642003000300c44545060b202c01c1c40507014005c0c4041c0350b1510403040e034064841021540e181a07610350120f42c0300e0f4805200c0d00d10513004060304000090f050301405502403049400b8601d8500103925102410300d007041024007481111100049030038120f058a1051181c0c201e0704d1032140f4141141079a00d50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 535636510 1250 535635260 535635263
    0x803060405222d230601030b070c020f120312180a020d170412020f010e0a090b01110106060201061e0614030a09050708030309011104050934030b011b030906050309010905010f09 78
    0xf15044e0b503c424402245840c1a80e500074100506501e9080e81140d500c0c0c0d10340e0341030342d0002e030f4602c203128907035501000091205004405152510403c0744182040440140301c81c204170b10200300404200701c00708500440590417542100c114410f41807001c0146606407004495400000d00452030008034580020413502c202c403c005079030035042c0119910010381364000e0300085140024086481143c0083c1182d00061401c0a8008100f482042c00d640e5a640202d0140c1d540305400d0111140d0800ea8924082490403400d000601e002001840d48410040700070301c46e94084007007000ac03e00f0742c100885154104045989141d151115540c0360b17842601d800059603e0014151403994501050303c0482e00010601545940d9024480740d00c04044c0000d86900101d00300e00f208103094101854100d004103641c00514603054400140a0038131040002c000c002c002e24103400003903800000e080035035130645031131501d94403580d05043c05070402d800000e1041d420607030940321120b11580712840302ca = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 535637760 1250 535636510 535636553
    0x61306110408010c2312010e070e0409080c0705030708060406053402100b4606080106050408031602030313030308150a03031209020f04090803060405222d 68
    0xd60210081405c030b118030300f80c1403000c549242c010445a003200c0300048c2d012106040c4460070941440000d4110342d8011021aa04100807402042c405010001800900360580051983c03a00b851a19a03440800a0000f04040e80380e500083c540b407501c8540300c480c80020790105540241001c04242080301d030819040c014460598980c01e000f44902660000c0b141c05001122280c1900b4203140001000410910318043d400c80d0b0000d907a459800100c14a00e241881c440c49141804c00051002d00c041e0720490421009000c140050b0102100712502420038041195603058030303102180c21806880c802005100c0380340d00000915030012a40c521506100440c401000316080802007800e1050101070b00107490010704010401690740f20030301d0350380001c0c10306022402e1000000c042d164250b00c11920880d011041c07080c681014090310f5001010052414175108240700c421961008865028011071105000c070904410804050b43c900300d01c4504144242030701d030503c1c11a0000c50901c90070345 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 535639010 1250 535637760 535637807
    0xf0f02090a0f0f050709050f0d021203030a0506010206220c05030f160b250c0b0a0e12010b09150612010b030402011e0c02010c080c0f0618061306110408010c 69
    0x1e904080c070607584035170415102c18040074208002d00c01e007403061800b80e54201c2c5c16140003c0260703441c0600701d03054400040007181c0d0383c40e001740248184ca4000d0200b40c1558800000d001c200813010105503041c2c1e41e00341412010100d03030304212804280303a074410340e014025003590901d1408040340300710302c4490b01c1e260000503550f54000f07800541304d10070034000152140146803a0b5440b0408920350030300e0203040d40c008200d480f021003207801d5116140701c1d00860101c2d0f040c840141000203442c520f203009030008010351004c4401150f903062000f0408010000742c0b02c51041c150307460a00b40c0c0c000c02d150590341c2e02e056840e2203043c40e41e0307030064cd0f003640410205404080d90703045580075520004201e0346c0d5402c4d0a200fa500565000103100d1049911002c2407111803010780c4100081000b0b40303400801403559041c181c485c038025180c5802441034a40140b8200151601c100c1e044800e0294000e600040a070b800c440d0100c1d450085810039003841d400c003101c1c010001c0d0310a0400c4012058a11340b07018 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 535640260 1250 535639010 535639031
    0x6080414031e25020d17040f14040f14060f18040b06011407080904051e09060714120c030705072a0f060e0415080106061e080705070f0f02090a0f 64
    0x10009621003000754001040040c2d803000440c840c0c441e1031006401e2801b03078101a01d814100300c25400a8008200070600d20b1203a180301d2416000d07030420300324034400800401d403120b541900c1052000780f109004502c0c03800c4418064407158040200805d210003408005c0c241450000d1000304241d42c0745001134046402c2034481035508045418942c1e0080480d0301d411000030600014010007420341c4401041148036a040d80c40701144107105407140005401c95182c5044060201d070180800345040c00390501418a4540018180319044084c50014544070303655444211254480c501c0c004010a21240e02e5201c032140342c0e4044c44102242c582000c1100762143c40e003c0b10b151461203000005021110310039480e09180c2d00015100f070818130101196170312681c0072801e45540e80d1011001403e0307001c104c2c5a02031083c1a00c4008950391800d1600c50030a280c0c003e260340500780d005032a40101030903050400c40f44441500005078040d000300403903c1c1c00c0302d054004043c40112040014241021241b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 535641510 1250 535640260 535640317
    0x1817060c09030a0b040c090c030c110304050607030c060f0903021b0910061209120e040b0f031509030403120806040e0106151d0a0f0602120406080414031e 68
    0x68070740c5000b4005150302102615089100b001c0900182d5642070007034400300f529043d82c051031108a090340c5010070700542e000b800600114510240440541081c0801d20031070307851008645002d03800d49003408002185040160040898280c11140d151606800e002050780129010ba28484005180f401142100042c840341c0041103400e103840c044007800500c400c602401d611500508000c0000541c0a429520150035444542803103011850100c00d040251030305008070244000d041d210008407950746004a5541c0c181303449814401c82c84480010800b030810415100250b4110350320b81c0c1800f51400000e0605003003911154040c90802031450b1641c501400b65000702e56901092140c0070302012070455a400030345040130300e003034a18140e54215969802508000d4507002080d5030001c0d24000e0081d14190080c0706511800b6410311007000b00c80e0f0443c0c82160303c01d800c032059840807891414658254481e81281c0741c50386c60b401401c8200307000c2c0a805062254000030045015800208008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 535642760 1250 535641510 535641517
    0x30501150e04020f010f0e03100501080d09080d0c05240f0a09030e04180209091c180614040b1612050414042d09060f020f191817060c 59
    0x41d4115001004c0315030654403d02e0382c1c00d41c0308054a88480301c1c0411500080c10b00d0a04001880d01d2034459005000a40080c00102d00f9829103081c100d42e81d52800d103050380c441d224a0110402e1207030301e100b89010300a05004174860101c20707408400002100d0403000b002034509941c7c040e0014519000a50008103070b2051108494060701c44001c0710529a0800000e80501c0710720018214000740c181380143c0f6035101140c0a04500300c0034040c203c403494040c10317801c481903140c0e800304420440001d10b055584d200000c2038074000c4c44c2815244010a50b0020a88aa0707802011401030006907081d2988188007001c281510803240209404062002224a80980d001d02401b20041248000847c50640d0191400c00000c186001104a81d80507001038205000040d64110340c44603112800c002491180e011210f40074001141024040411180540540c0d102c40c005902103044c4c1c0d0201d20b0007035464a01e00c1c81e04031804103101e9219944404400c02881c0070690a10540c03000c01c2140c043c00c8103a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 535644010 1250 535642760 535642763
    0x40305070e010b0c060f15100203041a070308070c170c0105090c1005040e1e0f0a05060108012601060f080703050601050a03020625120906180620100204030501150e04 73
    0x108000d44400011b80c3c181a8054480e00d213904035481c0c410040e494110440c4c0c05c05100b41c010315180d07458580c12031400c0d050a8010918180d0400c080e5000a03044040b80e0380013656403401100c040d100d4a0940682d207401c80304d800c03841c1004550401c0c48601504000e200340d04407810354108051a00034007000c02d02c85003034103001c07410031b1106000c21003110040070307842581440107100c0781020f8100040c1c1040260b0300300c641d4948103010001c1000c401d0180315040a802c0c608504250701d0160400189500304205103402154080b44c005103440c250012006001684150840c2c44e559032030301d517a68042448200c6050240c1d0000180c1c80c50b00402000850b500940542d160690390383c0807000004d8009840610191a0b081c0c0c2000314a41440c0610b408100380c4424100b07509001d006800315841e0403461407032040c580c40c00e10400da4003641000001444c90000920060040b2906042c13204801540160301d101181c0042844015048004030f1031420920381005520340d1410000c26008960 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 535645260 1250 535644010 535644013
    0xf1a2223011103030c090d060f05010e0f06010509010c02012c040c020c151b0a030339030203090c190603050106023f03100905061e04090215040305070e010b0c 70
    0xa00020000f07000b4406c0342030003401c14641108a9856100301c0f01c003100c2c0447d4180c1e88074014800710300e03d0768005e81c003c40c001205050502e0f00e0000200b191203581001410095111507050441e4015403a03038001d486070800c040c41d40f14480c102d40c000352a5006540303100d24105110b85e01458000b00d0221511100030380308220b5064801076003110703a884000d10000c07010380301001c1c41800e10188540044284241d4000c91f44c25081c8114410070b69030441451400c030402040c2e60000c281c145100120b801c05814090307180d507200907031941051400b04c15903030403807100c03440342d10038460021508007a0348458a08100c281d80b903001c1203941e10b5506d45041251500c00c0144901d070464403e002c042c1481d54481d8040a00c00848241041e0300240c400c81000400c4100a0100021034000c1d640c3c087e6060368105014030410310541c00364524813035258060f682d900344040c00c0d07442d4070010115501c44650450b80d174541c2e80c900a6511051403069601036031810002154200c461030031201d0b21440c000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 535646510 1250 535645260 535645267
    0x807020c12150c0f0307020309040f050903030f1f0303031410030803181006061205071805061606180302210406052206180f1a2223011103 61
    0x2c500389184800607099159681082c04074129400100000b10320404455002d592507181d5a000c1c0410380d00e1544d240091103090404000046c040002500e510c410a802070b442c0ca9104e43c10101118041a0120041503401c418040141a055003120000b0700e0612103000c070a81d16942208407060b5140002040a0400c03c0441d20401030b00500900c079031522130a40b421110011020f0044412980c080380116080300c012601c0144c5e03500c11542d020341e0f6420b12001e6207090480b6810002040d02a00c2d1003580c1c00b25841c0108450004041d10140c1e0151041003040a1100781c06040c00068504030014418502c801c2c1fa68a00c02280317650404040d032440c4e08150400d04156441d4000789840c800d04101e5a42d03071803042d01000e0145c00205800c0d00c40881240e8494440107a40b8415000122005032100c420001c4c3c600000103807508555280d19203449000310385001c032844003000c0482e0700c40300c00f100c804a003802c0805980b0182c290400b0942c0c80c5c5807442c00042d500c0d0303510703502001004c1c0c0091 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 535647760 1250 535646510 535646533
    0x4140108091219030225061a03070504020c0c130b120307030e0105160c060f11060c04090221091e0c01020c120309060c010b100207180c03021204030807020c12 70
    0x403a40f00711803200c9080250801e540480303000188a43c80006468240800f1035031001d01255208250304c140c8254000c061400205011a03611085d40c8115401141d0000760318100d09018401c009808400a00f5460003c1888090501522030414a54824076105541220060b000030440c1c4002e541070300e5031a294040100156055040340d80c1108140c58015030b69400a000034050760081c0807151103001e01001301d06002011045260072400083c0c0c800710a2180700300040059a04940c00c412015a54000c4090032400f000318240180c42103501d034000b40514548082003000640a4000150031200c1c1800b1040d0b40d108891034403640560043c85403403c0c0c0781081e1001c03100070f1480304112482e00310b0400c042285a844040b084c0300b04d9540c0c0b55000359502d486980c0d5001c4480328030003001514141030541d5440c5032381d001200d00710b5680f0240b0103031803806901614441410421040c50628140c10060201c2c1d008603100320050248001e40d03c005e01e0644105002c4005c440000d20307059104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 535649010 1250 535647760 535647787
    0x3010617041e05101a03030717091f032d09170a0806090c0301080d0f200a050105060a08071403010e06131a1504090c0308041401080912 60
    0x2070410303200c5070142140200480310002c004148284100010b0500030306030b008100880c1c841d610703071801011030f0400c081015613000050b68045604034101c2d03054401d01c124a584075100b202541a0807407030104000d0a48901c1d040e0007018424152001d0207400c1c6004c174000c00d02c03e09404030038412420400d4160f5202c0a42d44007050040c880e040c24240c40443c0e84a4121540002d07001c5000518a001005841e08000414942040403002441d00750f5042c50740301c1d82c9801e80b01c1642010004170064640065100755803640f0303100544114240c580c3d50701000107171182d89012050350700e0343c200710118000341005240103007100c0c200c401400d100e0382020001010404500c100582c590b4a420070340c507004c00c06001c000c2c00742e8400d1040305001d6025107001c9805440c29460343e023042e600c80007044036181c42452000750b030080032100040d0165040c0740c0451000415000648421000305001c0b41541c0c1c41030040b10b4420090700d41c400380380c0da1025095583d2003610344960701c0200501c60b2003648210f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 535650260 1250 535649010 535649057
    0x2030613060e01090536121303020f0a03051c020715050d0c08011401112d0d080903030610021905030a020712200d0b090106090e0105090c1c0512090f06030106 70
    0xc144003030340c41c01d161045501c0c0b01f81d00002610101c000401c002003045240071040100c00b040145d41880b4014035640364251295001c0c6a0b210303100b00450032001c1503610900031180a0f012101c15803610b0102110300520607000304100e961034600d4506200c08e1980100000345c1214120505c241c1190340ca000111240c1e807070a418056184201000e4902602c064560060141c1224091040440c645000c8501e0031048242420a1280c02c030240b000b40e0801100f00e82c1d00c007c0a890480031690010740482c50300e01a102c0320785000900807031910070040f000c4020203082c8035070390071505a140c980ca0540b2220b00b249200030001050001e4001561034401d440c0c800382c250060135500340500076200c814808404691500160f551403a0501400d2014803c1d18002050200200705900d00489442c0c1c0c0e6884c07052070288a0602e140c545a6140c103800003180304c41c1c0d030140959121901c400340050b046d400c501c1d03650348103481ea5400b00945043c40e4003038a0490382d0503a030307412030300e007125265580071013 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 535651510 1250 535650260 535650361
    0x315040c0e090c0a180b0a0320070b070e030303070309052e0506040209030d02030c060a060e070804050f0d0903020f04020a0807180509010b07021206150402030613060e010905 77
    0x2a180f08040102d41c5c070904079200034546500c041c2d80d5041400c4000301241ea010400e03c41440003203458002c0040c1c00000d42c1c2030340303030f00040c0056262200d1b202610a0030030401156454030001040040195150704072086292050049450a103039a004a00c004c40040e8190781c4030100440c400c20552110f82c1100d90841000b070401460701c00071801007400d0807058412400564400280c038070900c031003044032650007441031100700310450400700542181c01c0007800301d00412a4800c0410305102081c059000c6000c14141110780d0b440820101410198072880141e02c1a0428410f900803420b20b4021a4075031915a661100b09070b58000e4156085071081e24424060604070501241544071048017a0183c8404540d040e00e415180c410031848624084610843e070b00201b00b804070214402c44c180030f48180494016071070ba030750300000c108240d0b81101e50001203403c0180006000c2e04800d0b2a6060758a26001032040307130f44201c0840b001074408948400404441207802a200072217540149501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 535652760 1250 535651510 535651517
    0xc03160c0f030507060833010905091006091e17071a0c101104050f0f090403050702121507050a0c0605010602070602010609060b0f0c0307080315040c0e090c0a 70
    0xa46580003201c41d10351a030411100303640f01c2e900600c4a40e40110400758050442c11661008003040c124886515400c440c443c40c0460042e950030806a000d401050060017010700b4441841c40d2403c1d4082801c0d84070b1040b000441e01210001c0760368250100d90014925000c2122001546800547c2007400b803101000f002c54082d002c00850344010b0502075044115144441d69291700d01c0c50040c07401c0501100201d40f000d483c0614083d8901c0010042d5021a002107801c0f0000e1245100890300c84499641101e602c112010104410036800001800c0001e0080e5036040600d8920f403030807070b03070307520200c10080950280d11300107508148510014680d034501031615141400c113076641e09059800070381028000d6001725800b8083e03194244100401090845c500b030000b546030030a0840315200b07a910802a5200006014a44140c20001c464140343c1c4a80752994070320704244d01c1840385440c800000e10443c201003c080c800c0d4401c0c0b815405c1d101c00208044d0b0a0303282e015500542c0d611800c46613060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 535654010 1250 535652760 535652783
    0x2100f050f0c0f041707151110050a020d0e013204080318011503051c140711030d02030325210b040c0216060504080307060f02070f260c0316 62
    0x16a042000420114006c00400b403c000142c0c40f2407815014100400c00803c008a00c03407140082d0b5980d03c2040d40f60002100d80b60604684041c0c4a011070208900c0e003846410f0000d040154001200045c42054a00d0380342e51a44c0c2104000d03000340080290181140d01003008151600000c503040208102020080025841d0240c01e4906152003400c030354600c100b04000340300c0103001d084d061201c0c0c0c01c2c1500c0340210b01d42d40903040045494414561740d40100360f6508216030754414281c1c0000060494041d070420182c000c0d0340c3c1e8803c4a100f141c18072003080300d884080c09503400f050307041c9150715000c285914903031003220f0220051048030101c944a0310018001d071664403d04c248445a940500200050580b44400800d16036004804000c0108020007520801105035070240c1d80c40b043c0400c6400c42d00903280041d01488201908500040e6200707070401a0312212486980800b0840b0001000c6403031200c91a40101c840c21070340c0750820054020150702d00912205154030602c0c0c035184 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 535655260 1250 535654010 535654019
    0x60c071104060f081606050a050403060b0f0301060f0f0906030809010305060112060b090405090312061203131202012601171f1413030f0503070e040c02100f050f0c0f04 74
    0x210303041240d100c010240c05c0300181111400315503503003030054652410030925000303000300000e100784210f00c006000c0b19a10640540c860383c8908070b480b2080d40040080c441e0716214490b41c03400d41c0d100d102d000561002000c001642c0020340c010b4071b089942000040342030003a500b00540207440e008090a0400180d041004080341480c480d10001c1e0800160071500e0fa88035106000855034090008a00c40c0d000707000313800d039a40780c25407015032004068840b143c6140a100007580b0394040c0d0141040008903080307010034007600000d0a1440c9074001d903200f504c20100c04249150101c904648000c504600200500c46010714564441c0e00320319800459001d00d5024202e0281c005455807602400c5840c2d04001c600002c48516154004c5400c40d4140e160b00b01580d00a49a440d8480c000010300c84040001030249018100464034aa0050300030710000c2e00b829402911681c0b5400904445450b000507107000040300d200f920b03c1032046da030400c1c1003501c44e042c11403803581051174022840d102c00c100105 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 535656510 1250 535655260 535655279
    0xc150b0f040903050405030c06030408040b0f0c0a050606090c1801140f070c030c1a03160c051603210c061521120c081c0e07170c0102060c07110406 65
    0x203402c0d40a5510b8640f070b04d0034603042600385016100c45501c140000d00c20b200203d080c04044504889030711150f90356400c0100003001c280e00540c5a00012405202400340a02c034010a80a01c6000101c0700c8003000e55507603400702c3c120300032081c8841c0d070150700080100030341d4043c6800c0c3c0e8080001440d001e01b041c41c00f4038800203560102400719000021a041003040040c489040d10103032008c8480c403c5080d00c00e200e095410302008264140910600022002540c00751402c1d220568000090301c146c2c8658500030f55403907d0b2840304580361b8541040681c0700c06490b02d0f54021211309a52040b0700080d207619020040c00b80c0000c0f1001d86e0448000010b600f80c2c60384441828000080082c40d9080c015040200310303108401c2c0c82c071080c44070951085000070710030f2040341c0d00c03003000002e8649418000c0c0c0d007840c0280300c6040400c00f60b1041200120b1907003400d52030120715140c46400c407103000c1050001241c13120000d42d9044150782c42408000c0000b01e52180c14030075884c01074400903280e9616150340c1d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 535657760 1250 535656510 535656521
    0x513030e19050d0309140d02010507080f1c020c0d0e010f050d020c010203182503080d090204020a05090f1008070c060e061005120c060f0903010b130b09070c150b0f04 73
    0xf10041015070b07008104c042c40ea46c850b40702240e030858106c001424250000b0301144180040240b98180004005100b44480c400340e406005160400000b5055260034100007980302e50591f40c114850b841c5034100f064414003098400c2c0b84180d40720680301089072426901c079000700c444000d05a03024024850000002d00c00345104d064140440440d542a000c002c608052000180b4184822446001045038a400b49120102d9600081d01c1c0c0d075401010100a009000c4d82ca4002e600600009a44032025802005420f506004654021688132807a0405c021000249148404070310b00600164090b0300464103002c255008200220302030000d60302560800c1400c6400302c0c10320808413018021410710034036151304840d805004128a100c000c1c005026402800d0441c8100308c000240310700941c03400c5d046010341004c05841c200710b10111582440150048030560340c02803400c48001003243c0e100d692a59002e582051800c1901e10350418000e024221048843d60010b0346018105840c1e03e661165 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 535659010 1250 535657760 535657763
    0x301020c191a010807060807051b010f0f270507030c1203030f0515040e070506280804170a031407020f060a150b0a021207050106090513030e19050d 65
    0x904401030824a41020503500003280b011084110b070005100240000407900151a030504041c0d082d0b80d140c44007100d10f07201d6949000451003141c5298122010150400c110500742e0301018844c9106038a000f17021203500f40043c05404c4c00c0303440c0ca0030159502c3c0f039a14030b4150041040e28040c1342c513074503a4800140d955201d80760044042e440e0342e040c15414861900320030146441842182043c0d06607500e000b00c00c11410344996a0748007501000340c0108a0340b0000c044c041c01841c0c690809003e40d074850004402c4520b00051f0518281501901c0341900030310079a40300450400d03450501c55492601c2c1c1005540074241580c1d002d1500f402030600d4406442034420768018181d100e00303120350038101a409800b41c45158148203070410b00c07400b244030300000e803050012000e403110541c440484c9407840c1080030041c000c0b00051058180b003010b40291007602d4448205110f02c1c3c81c0e5440a18144040c010094001a18580b6a01c224a0008642030141071408100010561110300068098646400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 535660260 1250 535659010 535659043
    0x12020a050d0317180a240f050a0f0c02060723030c070204060603050105030a0204050a06120f0c0506040f18061a0d110702061b01020d1118040501050a05010e0301020c 73
    0xd0f03400350481d2910380c00e548190030000884001ca106901183e6501da00c103402443c01d110401139003400c8007200c2012011806640c000e002e04580316072064028007040d01c0f11090541030030401218a0800e000314400fa10469009003200d648000d81180c9400c0e0160f081d02c420394407031100b903503030201010195015032010022240e8910891042200300e488950000c2d06240c14440100120703540402e02025182c2c040d9800315055496540300c200402c6140c1082061a1080e034241c81030000414070b080745184a000d10b9400e032501d132000c000c1d82d070041d4810507004402080e01401801210041c00d00c06000c550390204030700d520340b06024990031404a050100c0030f00450304228000460155031002c201801150f4034005c0c00e6004941940700d1350459244040300030544600c3c8030000d504690104402580811a04507031210340c01c4140d0100102e114030700846d80a8542a1809114040c100e0340e0050040c01c0d118036210066840d0680051300742d606544c03d110240103031505106034002101c40b0744 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 535661510 1250 535660260 535660277
    0x90901090230070303020304090905030c0706020607020d02060112060b040b0d080d0c1b080a02160602030304150515040b0607080c06090d2610151e170112020a050d03 73
    0x2e0700c008440da003441000d810b60050100704003107a00402201e0548850070800301d26801d507402e1461943c030460401002e140328040380010110b501091090262815030b00382c072004600300c841283d8810007070007240d048500500781d41c40001c0095008813136a400c06017022034809800c074005104030481200c281c03050314000a01031b001c0c81e4144160035900100d4204102a2500e800c54038401a00514000304a45c2d0300041002955000f040010451801305403080f40e11912210001e4036074000755002c88103641007014400c0e08004600506201c3d101d00d0900c3d2951050410410000c0d010b080c42054010b5420040240410078190050022400e10401880306048c0100c002d494030781d2030205c1c10304010302c0804a00504030140d02c00400c07408140e90005a50b12614030545260344280d1003070320401c486c1105d00d580c1c580c1200500c800c0003032003c01e0b40b542c1c80c40c102c802e0314500755402007511030a4a4000612901d00825400a507141c0040d00b440c69481c5c035180070038040700d2681d100381d000c140c504 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 535662760 1250 535661510 535661569
    0x103020103060f08120c0f030a020c04050601140d09080c03040906051003180b04020402091c020424030312110406120501050d020a1512181115090909010902 69
    0x18000d4100030003515500d0083c0328070f0400e031245c403175480070750551050000040c054900700041102c1c803071600000c0240d03580c401914001a54540b076030800c49021f40d0801c00050341e1036008054113480b40315560481c518000b41889010003c0034003500c21944c3d0107003801141c061000400207403002d095a81d6000904904102c20042d151601e10844810541080d11401440319248075441136268040080c3c80240c0701c6100107006030083c0c040705500400120380851108020001ca41c28950080d101041030028079004004c80f152402c12620310114552001c0001038031032040400405080800025840d0708034510840329030155200d080002c196050303110724201140b25050040008031006034603001c4c180d010135a20021449040e24140f42144805401c0340541d010312101080c00c5010003c0f818000b00d240b4000228180c10f039000d40104980c206103082002c43e500261075115607442c04c1442038010018500790080035140c00b95210300980700180c5526610076804902511144900c2944 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 535664010 1250 535662760 535662767
    0x6010f0611031306050a11012c010b1c0204090f080a020f0102090f090a0f06150e030303131b030b0a062103080109021b160e0907080d08041505090601030201 69
    0x200210001650400c0120460314224090003800f140c1c0b490030061b440f02490f1605590910b42811341d02081e500b0004e10006800075030a0321483d8110b4100300b0340441031004000d80c22102240495a0130151268150b1140c54140c1c0d80008007601c004e10200b8008015610202c00307110f0f1141c201d62400001c2203501180703405020304902c0070b8103070f002141003c003c000043c8902d80e03004903180c02001e161021552001c15900080c0c0302406840040c852a560764000510180510608074002041030090f100e10f0307c5c000c411240654520850a55040c1c69a10760742c200340069040d01c003a02085e4a0000006808007900e5845510000b400040c070511309908a01d0003090b05c01d0011030758804412031070000703401a5402d410b550030880300503110300ea29050605a07030040440e0806a00c2603402401141c402250b00a00303680c140b40800c0616140d0468465440b8450301448200380c000e2100e41d100c261103445200d50040c040e0080c412000415400d2000716070003550381d201580c01c25801403055581 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 535665260 1250 535664010 535664027
    0x20705100510081513060b030316050c0109060801090507090e0906011505030402180903090612060a0506130306051f030f03020607180909050705102d0f050c01060806010f06 76
    0xa00502418200c2c2e44c0500440c2003000040102c001d02c803442111a040c0585903015500c078100180c110f0307070703504040b40107490440d000e1803040720302d841503e01d114030740d503c90a2980100c80c0d0b83d46403450141d003001c2c1c0042c06403600400c52000c000305080c000400049120b502c0d80034810b04000b411503035042c10803600e1054029415403082c0a801c105010040e110a94103071409c2c000340303040b14801c0e120240102d0462081107221030b80114040742d84000c15640b1601540141400c407005e055071a03541007408643d0051520303d11800c60b800750200081211504441d52090f0900c1d0a4030361034056816594030454141c0040e151a403004030258209501080f41540206a13803c100c9072004000340401d2440365140103503e00a038440407800c08108040200700e01610009145101c080c60021340100710700019503080d00040811403a06115681504040c41200318691b111180c10307082c3c07407060310a58401d106018066690745400a4010b50501c01b0501900c409001101c0c442d00e010303c0104a400c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 535666510 1250 535665260 535665269
    0x611030f040519080a030906090b0c040905010806130209040501062301020c121908090d1128090c0c21030b040228090b0d0504140a0f08090301020705100510 69
    0x4640c00d4007002050100b42a90700554240c0380200740f00c047c0b450118043c0072003140c0240140c80b40f800340f040d10014500a842502ca104004000b1030ba41e44041980d5400c2c00c0d21003980200c0640358901c05402d010054680c1705004000100e000c90b035445c282e48400c1e0341c1406003a4001032110f070710310143d0b074144014000e000c401c9603540700302e107000c110060701c40c6c00c5480c062500c40007020499042022a070150380c3d48140040c01c11002d0321300d50401d07050042440042600ca00e11003295054a04e64001c901c85086105440d00000e6130b040a912030700900820203034105014160003201e00240041400501c6800c0011580b001d031000384030090180c600042415100300d0060004803203107440c10014400c2d905188001502d8200d05500c2079940103260f03000301460b034200140015130482c858102d94061440b91004199003426800c5080d103401108100902c00300b21032038610b021400e40350203041e101c40000d000520700350035075235400d251003a846d41c04503c960302c90040001821105240c10002e2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 535667760 1250 535666510 535666543
    0x30e090f06090604020306010201060305010906151d01150c0f031814060702060717030906010f090c050a03050a11070c030b1b0a08090c0a0b0d0c030605010207030f0611030f0405 78
    0x2810080d0002d001068000d29280c000c0e58044001034085e071007500085e0045402000801442c1c03650700740900600451369000103544100800017071108c180d2081c0c3c0381c060603101d1210a50f0f90800010300c4040c40c0300800c1400704004002070701e0200c2e1b55090006c1c0f40f0382c441d450b800803003030078144c1c60751702000750798028403050300ca00001d403405845410850f0742844d03046850079a40d024038506586161142c00b000d4142ea48081f04000f400440019180d0695111503104000644d40c1c1c288801581d500d4000c1d800019030500010708514042c0e0801c9800210340040400d100c41e00406143e01c941003800705560040a502d010420b20045444580d0080c1455070f41040c542c10b100b085244900c580030891080085030400280b07200420b10000d041303120f0003010b9221840d07840c02240a6070700001002d141a91900c0718280d92940240316180c111401030700604009843c540310003500200c02d41c802d4401c5134503940d01c0c0b95a035003140c00440c41881e0701409400c5504140c2001c2d40703400304c20031402424 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 535669010 1250 535667760 535667791
    0x31e0a0317060307030b130f14010506042901020a02151e130605070f0b07030b040506010c0507380a1805030615043b06060a151407030e09 61
    0xa40f804140b100c103403074001e00008042d032903490518100261064000d000c651001c002c0d1010000e0020807410300062010003413019407a92420030040354080030801e42d039911080303421805015040c1c48420700791814016105d4035142070700480c12801d1004500c00e0300b200c001a1031004110503c0c0c0da001c000c500418400e0401007a202188a001e00034040d80061100100d2642c0401c407118004001807944011030b442e5a040024000d8050014040300321b11950402c00000e032294440c4010502090b0400020301c09103241c001d1050340c4080c0015400280b000d2042031a541e003e00310700c000d80e861a03840c1181c2d0344d81c002550040001c000c6504981d180720101001700302c4c3d035900083c0d007900501d03005031080b024a0510000341c020019050810809a80d07482103071018140e6003090501c01e101210004c10000c2a0a05561102e00c11106c0d0350703100c508036405200c0c40485540b03541071200380b400d10601c1061030030031602945e0003401080b4000b0344000a050610b06043c002143c2009440421059 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 535670260 1250 535669010 535669021
    0x61c0b0a120b041b09020a09060806040203131e0f0b010317040807050f060c0613020112020f031302060c0a352b020f070c06080108030f09031e0a0317 66
    0x8a615000c0d001900c0c6000f0750042810401c00c4e040c1800080c035204104554036172103803034041c1c0341c2040d0384540030104038088005485400c00e80201c034032844214204400b1044c031030392200c000f042d500c5c04030401a80030f0360000c00090002c40c0304080e030500075000c00146603d949805c0303000205640c0d1603420014240810440901c00080c0c0030140c580464100030001822000b04085005050802e43c1d9823040d00300f0b00c142c0d190300100c02004903000703a0b11558000031752050741d0181c0c4280d1010042c400c008000180303100d5000c1d22400220b910043c401451f142140300003a25081c1100310580b499441076a81c0502801a821107030181c0c0664517040c404525041c00420b86401070278001d1040e41802002d0901d04101380a121203185034500302192941d40c050598429a00704080881e6000800000480d107507019088480c1222504801586400744241c0c0707203415030f086010302540511401c1002d4060380c02c00c40c0591030b1244010010511411f00c0d040041c0071440306420800c2c3c0320b210106124 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 535671510 1250 535670260 535670273
    0x11090108010b0102031206010210050a05150109150509040b030a03021c02010c17060307030c06110c0d1115091e18042102190507030c08010501140906061c0b0a12 71
    0x140304d40380b103c2101d07900c7c0e0f0f1818010307400c103101901080026460001000700300d01e044c2d4440c0d8001d00601d2040d5001e0600b1350019a011402d5005501c00e2608511405490500c180000c0c0a94040038002040d40c120041c0440d19114000c6c0c41200560040784d41c00c40c942110760302d00180420701e48024405400c8045d0007500241078580c103d2900341110b00092a107840070810400155800240e1142c020fa8801c3d0090000100300381d40d0b001801420369203441864a40c032600200754010242802d2034030b0174400c00800300540c81c20300701c41440500c6490056500d51180080e1090585041015101c019041025551401c948039860030043d005020202c0c07094203407180c5000008274401552424110300383d2410f101144010400d6800d400c050b020841c0100c3e60348100d902c81c0c08007000c95a220b0344060300f40c40d000d01402303c604d86c070031450007103519282154680004014185500d0500c5030251030b1400d9580c0c0c6c1400612079101c8000d4072490401c04c860000504400e050301d410002d4070754548 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 535672760 1250 535671510 535671517
    0xb1909020a0909030e130605010207061d010804020111101d0d1e0c060e030c06180d0f1119050c0303090303031f05090103050105010f09020414040c180311090108010b010203 76
    0x30082c1c5a60301c1503041054010350702c0d5031203100004c02c00d1a40150190070400941000c1c0101401801060400140c29001d40702c0d001550b00200e6a9990054003c0011211014020b2050741008026244048000414841c0c04180600e0880100b03c40b0b0040c0d40350840708521840100440d80445981b81d882c0e68030100c11680742241c1649020b1050900d601128100c14156002d800a81b4045821007041000002084003211010988649660302d031885c1d5000d514500b9603039040e030880f240f000d0920344540c280a00b54503480c10001d40041034590043d1900d1442c4900602009d0602c0c0720320705211003001140702e5814210300952405040b9000720303480c3d0001900c15000d805400c2c40c5078415840b68400f02d005858083e0001c641582d40f030030964040c100c00c0c42280810603420101054600c1680200e9054aa00a68240c008800c07002800000c1a50803d100100038049000e04640c40407181d28600840c01011202c002c0103030203042020261341030384056100da1410300707c000c285e41c010051703 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 535674010 1250 535672760 535672769
    0x40308090f04020d020f0714010c140f040b0406020a050c060a09090f0b03030f12071d060c101b031a090103140f0a062f030c250b1909020a 61
    0xc4480001c950125001e4001d40f00e01c282514001b1848000c10a21035025200701405011404d44540c8000c1e8290b080743c0d010b5010800194144c0302590b61040b15400030803d0111203501039142643d00d018803411074205401c56070060b04a880c006052280802c8035008425017241d41c14a800541c3d0409442d100301489001600c0e610392841c400034041561020b00801c9015007900d50701e594a0110004960041c2151500d44d0601c0b80440d0b2010b11403209901507074440c0b541e106405124004000140e0809440c1c003500744100e49948260000318010310190800c400340019074843d100a0240a0718400b10400010204550100c80300303035030f01c850f4130341140c0d0400c041c01c010070802c24400d824841d030b5441c07180f454403032451004100815503000e80c0b20541c9805d803481e0240c10788003001444942c900f0048101440030320100d490034503000d0062504101021511000b607030010305940c6a862450419910364041500700302c040220f8501c0d5015240c0d01c030300200030111840c3d0006664000d030703000b03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 535675260 1250 535674010 535674019
    0xa1a0415090b0a0b03040c0e130302070b0702280807060305090c010c0213020f031006080601020604021c0f0803070212041a090d0b09060106091d06120a0b070207060f0504030809 78
    0x2441c40c0e915800f89400140020701241a40c0e89058201200e0402c42d0344038115981244000140192400e0f103c80526590b040d40540310302860500140c40581000741e09030ba201031401e00303c10071062605050754140c0026044985414608200c05003003e034660300010905041600304034050a010032001598082401c12490060890012030b090440382050022054400520345120513a44006948148890074100344030301d894941c00c640c00242035a101c2e02603406440440c00501d80ba80c0e50f0025520945900300300c003030958407043f4054041d6001035030001400000e00c08016410700002652081044525141c24540288603401940c0c550383e681a200c0040f07064181507071801c46010609801000540307142c01c0488031240c45070000e10a61021400c01c040000340404c48040c0b000c03004c01011002c001903a5888288000c0180f4600380c0c03942ea000f90800440098140a4100d0040c103041c0d000b032031090700303010000d84008040f07010031003884814441040081c0c3d10000f01c55115100784c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 535676510 1250 535675260 535675271
    0x5100b0a110c0105070c0312030615080a18150b060f18030c0a050d0f2609090105031b0f04020d0c090e2211131107030e040905120304050a0204050a1a041509 69
    0x304200c000380702b1500000c02080c40e043d01e601c0c4450b403003940c8034000c7c286c801040141d2110302c0f10540c42c50700c1e131b000018107049048505421403000c5a00400d483c0d1000b4101710314080d04030b14001c002c0e90202c0484c0009103402550ba1049003000c0103d40d00c420001e41e4045072043c24500003440d41c80d8190801042412036800050070040c40e258400ca0510002c0801a181a0050403600142c1c01081031180110101c1000050600c3c5c00230f55140300d215241d04000142c440c810030300c81a00d1041494a400035000c124181c0b0004180c810f00100c0e440c02d41c0c440c07000310300341511501103000250070342e0100da0610108024603c80c2d480c41031600f5601941d180c1400d140c2c0b10200f00181854485642504d28000c0524840c210340c8004041c4688a40c2d6070f4050b075210300b420001101c191b40805480b50b40b0000b85000348000d81e00081d600070380540700302c410403040396000606a5804884200310181c85000881c1d00d503c064207003071081c03a001ca4041c8500c01586440340004503d03403007140340260325031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 535677760 1250 535676510 535676543
    0xb0a05220212040b0403030f06051311070c030b010e0f0105010203030a02090f03060711010b0402031909030903150f0507053109091b0b040e010905100b0a110c0105070c03 75
    0xaa040b110712010120036500d5525090524020010045806402103410404460700203146482460252031005150003800a044c0c0c043c1001000100810307000e40031304002d507001003034100c0d003c0c000851107011554040d6041c42e141015150303000d040c240c40301d02ca03100140001c0c0c2c1c001c0192548002e88840041e2a54200800909545900110340790103006050070300c442107500103124035140749042c00030300007000202d09000880c0f1080740c1400484080c51140000748032150041900b150180c900300c0c200640725110104508800c05440204654941103800320a0715030050304c0d40490142007040c14564142d0005c0c0b07000102158400a5000da00b42141c90784c10619030007405840201010008882a403501d928109041001810a850110000200400464112030a892101076420000e0340f030890981301420000d40200c0440c641c015000c9907244107400a006240600e50300c03100e1108000050354100215101400d0400a04000b6900403e00020680044a83c00f48003541d6040300ca = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 535679010 1250 535677760 535677829
    0x30402060405100f03060503070b1209011e06030c050a03020f0d17070326010f0311010c20090106090518060d020405090d08060102030a1d190f090b0a05 67
    0x190380200e0b5200044403512a82c0a92200c129444248151001c201c1d040e100d070202340d501d150034451500c4026081050302182c05000400301c2d0004240750001c282c008142c1c50f00e0100c8200c085d410442c00d980c07401c040003405050f80c1c0b04002000c080d5100501d690668020450b074541040741c040c010a010901c0c041000b4200550710f00112a1801003501c448003072500404482d6401130141500b0940c2185600c8040f02042ea60f040751140b104080c0041d10350341e521807000d068000b0541c1400400c16450b008591302004080005044000344e08240070748104024034a0b40c185c211808218202da801e02c0a52582405861302d2080215640200c3d03407403e001540c000c502000080d0020b051070300b408040c25000401800302c2c0203989600f00c0b659141d500481ea2401500d07060320004015034070b90341e00f40d040c110b4140320055000d0708119900207041300d20b00301d09801d54070070402d42c02c620400b00030145087c403501c400ba042c203d4051041c1440e000010b40c80008100880e00403081d1644886a41c096 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 535680260 1250 535679010 535679017
    0x10b030103410f0f030307120b06040906090e010c05220911091c030207030210050c06010e01050a09090c09050c040f030b061002030a0903030e0109091a030c1008070503040206 77
    0x1002c4032001c90280d004409010005040360350004a441500600400c60b140400c000140c0d000003401503003542d94148084680d5000340107952110303a81c44003032500581316140248041d001c0d070320b0f001c184146401c4011080360303d80f06428600343d140c045854503190380b200450314100c0080c0d408000b44071010309141800c102e240d10400100b894442c00d1000e00c20a10040c281e4000d044491101d8a50b6040180c507500c001550020f00681100d0300030700062604081c010700c09481407800300c1c200b949000980d4545582030304032100c02004140104840e2800042c0385010f407490980138403c451507940d0340407404505005429040380c4920025450f000c1440c10341e402807001460240c0c1c2a9078a04090b400c62200741c0d03006000d011091244c0107118000400c072044030015580c0c071800b0500c1c0d03880031680c80c182d00100504210008400281000d0b4034021000003e0900c0c5000e5090500e03801054030307280701524114024042100c01c0c0000c581c11402d0369603c00b100b81030141c1c1da0341c3c4030700c0041c2c558030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 535681510 1250 535680260 535680323
    0x181003061527140c0906030705040302030a0b0a0b060909150f1801050a0b070210030c02100e160e0903041e03021503100b040521010b04052a03010b030103 68
    0x20700100300628000c070b103041658081c14038210200a481c45071480001400c00480d0030b5428035208020016181c1002801140c0c401128504107003426200c0e4002420404400b400b0785204140308203120644000c0e00c100920560100d400c03e150081050110303490900080c5141068148200c00502980307951080e89250b00300103142044c175019100004070b43c54420300885000318440311002c114103c40804440e1303d103030003e01e55144030040384012809003080340981d000310b00820404440318042c0e4007c0d070360088108800f5100e0000c036032040001e212803a50180010210340401d010003440d020084800381c5031480d24604041e44031124069413100241c1c00290002d120020b00e52088103c60051070183c0c8010050400150b03441e840c260312802180100350344003415550701142c10036010001c1640c1d035504800030803007110000005040791000c036650100c1d16401103514140040e00320600500c400c001001c42e0442d4103005042085010500004001121000c1581588400b0251266004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 535682760 1250 535681510 535681529
    0x1b020d050a02300106050a050d06110301231936050108060610020d18030602030703020301031b140607061407030e0f01020c0c011809020d09021810030615 68
    0x405242a58801d100442800318015101943c0f50b880484018000c034411160b00134030400f80241000f080290300c01507403030304036145036690038486600e544c2c44001c0d60080c544060352007003401e0040e2800e8000087c21245a1141525036150002e8500c0700c92361030161768000541c11555020f0315030780642000c000b000c0c2d40051706000010b55180b40300da008903058640383d5007651b9140d140c80c418410340c104201d10b01000b507000b032206600c04500c0f5070900c121907150381e95103003102070707036519400d040340c0c0309a13445000240c0010060050090010400c01602e501d28813154109290050301d507000c1d80e0b034a40c1e0718884c040000d2103800b40286c41d0050488418961184070f00307410080300240040c00d1a41c00803009000340300d0320300c004850601c00d40300900c452384003070000e82c2055401100c810044c0c1b1000c08001448420100d40b40b40c0e07510191250101340d15002441880f14010089106405404401c0a088140800c191060007200703140840b540440f001c9400c500103415100c2c20b407500e4000003401c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 535684010 1250 535682760 535682779
    0xf0e360109080a0915020a08090109170d140304050d030b0112021209162303070e07030f060e070c11010203220f090623031204090207060c1b020d050a02 67
    0x5000c040402402e0020460b200c3e0385135242d58140d02c1300d0f0440c03040c0d19100503030845030358000440c00c4e100c001c01c00244140352000811f038942001c0350500790320000484240e841002d8541009406ca800703030321000307902c0a009007503280654990355528240c07100c20041644540da0024643d00548095241c48226541591652065140c18022000071622130905204030b041d8102c0a810100d001d07020b03070300050f1903469020842c6031202d10043d41c103d401030305407045000000b4441401407400f80140141e98003c503650004842e2141542c0882d04010b0301c3d502420144114590052048a05142d201007628808010703680142e0540c003030703061585840300910f0003607035034626101282c905940c00c0595504030329888002e500126449030142c0c1407981d401608222207140f00300e032811603403017004040f40d00008442c00c0d042145d030800da002140040c0c003c9011001c02c100e6004600b200001494401c0c103a062041d4161800680b500c40680290f541c1942c85050050a12483e007506030050001c4d0303103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 535685260 1250 535684010 535684013
    0x715121409010b0603090a06180503070b0106030606090b0a03180611040302031902090f040c080102040b090414040308070315050306131208060105030403080705160c0f0e360109 78
    0x101003001c0307416070329035460325409a04034500702c02968040c28000000b417881c034143d40d96107401800e500f00b0ba41c08a044401d0503900243c01007005115003481906400c0355549065405415110150044414007038a6076007400f944030f130302099035a5411303580f5020a10040c108200e41444807541400b030145410001e46416002d04000103000b00d1b4800c1c0d0840394a808008891007075500c20100003503000c0394800200328030400d004d1046070003070b010346d600c1080903948420440c00c80c2e00c99409100e80c0c03040450b2107505407500e48a00b00281c41e0b001030300d03c00e03490583c0c0c00800302d000040141c0309144c0d0300c400c0881410180f19101c3c02400c009402c40d801414040303500f100e5440c422804561981d50505082141e030310420300c042c080c54068450a0039a00c2d0381d6420340c1c01c604010800383c20000c041c400b1260011242242c0d1a54a00903000c01c14a10305040a122444245800003003c2c105010107000480ca0503903605000c602524910341921006080d0002494200c0d1000038070940c2400304000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 535686510 1250 535685260 535685291
    0x19180c032108090303010312050c0715080702012309010209090f041415071b05150907080106120615120308010e06010f0c0b07030b0303040810050711071512 69
    0x4525108510641c0001c0091401214070b00c80032a8008074a800c117000420000704044020b50b030741030303440c1813040c18468407150162820f621075100c08401c0000c0e07070030340f8161034100308400e4000301a84002d0000140080d003030a8a40040103014101d09a20340000386000c0b82035054454825004042804078104902c03d810074503000d450a5820003103c2000d0f0403211400950340c180d8006060415600750f543d10415a1043c452035100d1550124200114000070004d02c0500940415080031410504108041c1460841e840e040f04140d03a24011040c400054800328100c001c40c1d1020b00420101c80d034405068071414244d201e01441d0f50410700700300c1055003140c1114143c0f0170503a8400c0c1c0c0749e40d60f4001101e942505581c9080031643c9900c0c5071010440e003c544551000c0d41c1d04010032090000340c080392542c1d100c2d902210b682d0f00702900d03403c00f00c100ca0261b590401450b2903d05001e0400c1e000f626240d1500744210004161807801c40300c0d1050080018a104540e000d00c00c00124010041d9003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 535687760 1250 535686510 535686533
    0xe1c0515090106050319030507140102070605160917031216110105040201051206040b030601090c020601080105150607060e01020a0309030f0c03082205010515120619180c03 76
    0x540440c4100060303068105118000454500500805940880b4203441e814a5446d4030160300b040402c0152802150041401e017243c81459800140e44520909000040b610064081e00007007451030f822440d80d07030303006464606454114002c4000007940503102131031031091310040c582e0b5a01000c1085408103802030100a4200c8035103981c01c0306400c00000a00322181190b001b404a1307000c0c401c0031848800080000d81c8031502800000e0581050301c0020b19004090b400104520788450041800c0d0f6414000c0c03c2c010b2905130001d0105081800320348261030300702c00c4c115004a80c003198007001e009198000024498035107000b195a01c45400c0c0c002d001d4032405200760082000002d01840ea1442090b0007401a6090365030403595840f800c401d9003080781c0c18240c00301c0d100b006c6c55034480815000e116443c040c04800c0d510701440c00d80d0303909000c1403083c03d46614142c0c1d00010100300d024256100401108603540304000398a24403991002c081c26078a40b00a408188c000c00e0200070880300b010350 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 535689010 1250 535687760 535687783
    0x3060f180a0501080d0c0b07050d0905061603140f0c07030c0c031121060a0f06090612020a06020f06070c020d0515010e0a2f041802040f091406010e1c05 67
    0x1945e46010124006440b00e2108140041488003000009031413144210082c1044108561000c12100c1c1c0c1600c0b524039001054860402d00307a06107840ca01071681500c07030050310460b035145000075031400922031b80080400601c0600c1c03e400000d04c4030209885401d00410580c0c4c08040d154a080d101c0c00d16100300600401042c0c01501662200e2030240c030f100d02a6000001d084000f0301c1c0e82e42d600d80c1800301601005200d01903450700c80c40c012400c006103024560141400d20704008920295004101c206070540c0c6c805002d5400441e02401c014002160050303203c2154103102c010640d40340701181c01103a0035503010745540614045822455648015035048501d00603803105561a840c1003c81202c26446501c413816109000c0b051404201056524482690303a160b81c2c1090b079943c07001201780300040b0081c03503403a6000405020040d82c8612000103040c00da0410020803080c00d0a0441540005d4299410b003d50040141010703030b1070f0240301210705080b0407106045402480c0c00d50707642807100301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 535690260 1250 535689010 535689013
    0x80a03020118120e060d060e090d140f130306050a0b12010e030406030519020a020d02060903070c0915090e030a2604080f0f2b1103060f180a050108 65
    0x282d030140180b07500200a10760b500503d54800142c41a9010395405906034000d80d040074080c09800e011008070300c03880340200403082202e100c0d40740203101241040c1000204900740204400015007480c24032003039400103c0b10800301590b5071840c2149000a0761982e000605483c280700810200010366004901c9001c0d0650700e0905118007031565034207036084003d40543e07960017400f04200c0f1510270341103140c101c09100916040300548080ca60182ea00a039164800341c0e100c23288a4100907030400a0907407000041d0055820078115640b0007541c81154414160101c0d110224128060301030300c5644020040580100b1601030aa1a800d4498005007000c0e80440e107004514005207021201c480402c000700c152000b00c40d9201d83d00c4400343d0304401c0b04000c10b044180b03c4910701041c00380040150304007004005a41401500b12815a80c0e058180002c0f59810310210f2940c520f40c000a80342c1101381180c0400b02c0c80c4180010814003955140149166100340050040e0102c403684418180d410381ea0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 535691510 1250 535690260 535690271
    0x40e070c03174204090201050405040e0c10090f050f04150303260f070c14031c0b030f150a090b0109060f121104051e0a05010501030c022b0c02030601080a030201 71
    0x41c504100341d03042c42e5201d6421210740f0040301c014586540305510007071050504505064030341001c1021140045802040342d17008400142d03840c41e0082021007000524544804080d0a000c0c0c3c06030340034040e1060034001c115540780300300199a943c000301c4142e40402000c0114640d281001003170032094060201c0e11380c04401d800400790004800030f80c03043d004d40007152660345590800f2100d80b035804005440c0310b007941c109908425014401021201c90801c0c3c0039540841d8050b090302201d021103c214400d80c081540d5414041003c200b400c0c2c020b000b41000545a40c46021000140240300c02c010022480300c400462100c80070f034880010f44a104442400068032240700c03105200d009440070340b09844800341700b18180740c9030b04101c0c1d00a186000311100420005600010910180c5801c0511511000188000c0d40d01d48601c49008403288002c000c0401541d001c04401d503c4441520a440c80072400517501c90300510504c80e6031603014045541c50742c1e64400300d40d154000342d0380450045d401c04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 535692760 1250 535691510 535691581
    0x4241b1401020a09090c0c0507170a1416060f17040302010b0604060c06050a0c09210807080702120c132c0a060b042a03110301120314040e070c0317 65
    0x702d060311f0407a640040107140702410940356000c500b00c000b0a652840c0710b00a0000005501004020801c0003c1d10080081d00c58582c1c503408400b0b4240c00c42e00030004481d944d141c96035800b0741100140b1404000345030490315503007801c0740034001010802d6045140050300040312030f80090b41d11040e81c01070b00200280d4032050846419034101c000e080000440001060010506490744690700b1900b0705120b04400b001c9558400850b00038000c00d445050021440788107509052a502515035200c0c00500300c00d42c00540010503521424414041d80355960818204e10300c964040c05041d0b441d100032121071007841c2c010300341c0c0e1042104812a141070904100c0c0740641070030301403002012000d641650300c25005004504c404402109244101038403070034a100c5504c00c04004601a144501200031300e0383e064100030744038080d628509600400704000070060b1068075496a500103411b40703840b9528055070b003030071201503180706a050202c2d40c140d018480e8209108916440165403001b2500011000c2c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 535694010 1250 535692760 535692767
    0xc0203120c071703210411040c050a030b010201150305010e100603081828151805120307060509060601120213060509041107060204241b1401020a09090c 67
    0x1180380480c010b81c00001c0c10320080340d40100300ca0300b400b10181200e0824240000350940610300b40c0c810001c3c1d500388424130040c0041070841540c0311030f059409200030150b64038000c09a2140b401c40d0b0080680d5900140e000707a20030740207070200b268221718501080d0b4507410124020b14030501e0f07402c0e0b00c4c803c1110f10388844846008078011603030003075049030401c0d9888a107040784408808146501000c0c81040700b40d42c0142d10003400c2c404510a130f0400f01c1908000c04c2c2d041c500254800442030001101e40d03040405100a2a08243d0780240c500b68150003082940c2032079405840b44c0108124244001c0001031000002d40074401c00003660380e25041046403100c5801ca1003150114031901215910500080c3c0c00750004100c120805440017480d0504c145080d940e40d0440d00003200c1984d00014100103034110b180003528041c05141d01490352032090030010309509601e011480046038a40700402c144440004400200301000b80250f40d10f04607040300030242c0d0054000d01d00341600d00300103503500511 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 535695260 1250 535694010 535694017
    0x50c0418120c080f131502120715020903030d1a01211a030d0302120c04050a030b04030c0803070c0b0a110d0504020d0602161e0f060c1e0c020312 64
    0x4000728000408801c100e81122610b4003035905407940c800800c000c03400c1c0c602001c001d00c00450b10310389000f04a410315170680e0100c050403483c2e50440d03221040c1410040190401c5408856000c1d9004d1140c100403100c07140a4022003400544c9400301003a141c90803402034000d44150304a80380d044c24034a41910041d00c0c143c07107110403415131010114610003681066849203101050005000500d25100d50000340703050f04c000400c134000703600862070316008a40c03164044d401580308401d20f400c090034240494260401c03444042c0c40880141c02240a0500903600000080e400407103071681ca181008016280034a0600d00711469101040002c84001c124820400c030100115906807a142411036250094417010f401668441d00991841000540d980300800c0100780c40c8c5844800c440c11400c01c50008a03580e1040074228110208810011340d0000c000e40706180d000c840040d0032000d2503401c5481080d4060b24040164000c80c44201c0701d038114541c010844e00c214103c0750a440b01c40802d941c00d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 535696510 1250 535695260 535695263
    0x1005272814030d120e121c0f060503030f0304080405130b030f010504120e0f0301050a0b09010803161e02030d091a04051005031b0f0715020a0e010503090f0703050c0418 74
    0x3042c504d078240c49410320740c03c02c2c0c1e1800d21185c12503040351812015044181c0c000c03030b141000416211407070f108a440d41d025000e10082c0302c000c20012030340740402298581c45080281c103848000000003d0402140c20150f401410010301460a1924401070784001082d001d40d005201e4403410104840f00c40d0140101803099912110300d441c44035520100355404403142c6c100d1540806030100a05207502d0900c5031910901917040c01280380001202407045210043c1c0241d1456042048880c40038486428908504d5070300080c07600203803042003094a0640301d4158000d5042c01004050207403240e0000c0c410040d1a00e03210303c1d403a00e91117040b90840d240300700e20800746c01814a40b404504d860040c8003440c1d0044840c1802c40d0606800181440958030107405681c04403c0480c040e400d100010b0006444499035440c2140381141868000c0d0456100e0210329042000010000303138400f0b014003048140040d158100e9981c3c1c2c0c0c5a11340702d6204c021602c0f21070701592511034200c000003546442e031003845 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 535697760 1250 535696510 535696517
    0x3060e01050607030c080306040b090405010912020d020703230f070801050c04030f060b01140d0606180e16261e040b010605070f0f0803061005272814030d 68
    0x41c01d503543c81d1b003901c0d003004001c183e01940d215907459007074031543c1402e0310681c8030342c000141e01d0034140b600c4810386040605080840d0310034240700c0c108a800007100380071703a508010000c0f50103420b0107540d600300252101682c9240100c0e4540d03426044001181010740d00b000c0c0c000e10007580c0b56103002074113004510003d04440d2250b00b01c0030105080e81e01540f801c040600d0709901c3c500c100c0681e4112503005001013004256100e0707080205a50040c0c0707800490403003c02170010303145000c0f20901c29039405032040c6000b4680516146185008409920311112001030300d071144420040c0002030321a0444265503c0d055481700d00c0d03040325045202c5442039600c0300c2c50041507400c140c4100c9141e006600220f031404007007241140030411000e6500c1c840d0340728040c450b03503a280038010720030200e0f0003604810610034248079803c2c00c01d0701c07440c0c90442c0508074403941406d022030b54005010320060f4920800106c000411401c070f04c810031040d02e4262000003650800e410000720030315070f035200d1103800031001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 535699010 1250 535697760 535697777
    0xa081207111f110403020d0c09060b03040b0420041b090b09060a0c03030902090c0a02010b0a030b071803080c0a0c080c0922021f090e3d030303060e0105060703 70
    0x241280c0e54002d22403001c030343c05084d0606480f94045411b0420040040d520310605802c200101d00d000c0c02104003522204890350f04504083d070354000304600c0644010450250803100d20340a15034241c1900700308100510a1080b10403510b528041030710380003025000601789001c08178800040908540913120007034801850004c8038113080381d00060f958811000c1540b100d4803000581e03074062055014140000c03440d0354460300030401908503150403080b2405030100ca80200041454043c29a80c4101c450900004c911110220b00700325117429040148201404920b54a00b5540010907550042c403c4c0c881303845032a203800c03802e0341c2c0d848031404c00c1c0d030300815040000f01c400c4407503036155520302414203c00710b0206955000503500701c50400400601c2e0f009410345c07829280d029201c47d0040a22011009041c240f889042e80c00b83d102444814007449a801c10f607090304c41880e411041401c140d950007006035180e03d00100034004a01c5050030140d416400880c03e03240a070120307040c869142d1030303501d80d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 535700260 1250 535699010 535699063
    0x3070f060c020a1a0f01090e0c060904290f121b0a050306191b0912021212031f0602030d0f152702030106120504050a08120711 56
    0x1802a00c00e001c1e0031800349003550300014520996000302c0c4141d4214070f07110380c64116051800d007007050307021204079424803880c084c0b03e01c004149164000005d894003680c4041200124010b80081030b141c10180c0380c0d840540c070703003000b9641c1b080c50158421200090202c498208120803080046441d12454004602c48070b045400c20403c01100e02020708494a155503a400190070101e0440e00d02100d012801c200c00c440c0d500600c00c00403940b10100b8103099841051400070150a0785000315410014410340500035546d0b080480c000c90342ca20b600f02c1c1c11619102c07400104e660019200400c0d2280001031425040044074050400d81c2c981c0c1d8015800d00d002880d542c0080d010011603d0600c0381c4e940607078a4100211003051300903010840a0451000c440e43e4490690341c240107020102e81d205000500046901010800c0754881040021400340c0300e80c01c01da414040000e1000308a131400160364090240480c40462003080f46441e4410310080030100c186c0c031002a4900c1440038801400f0020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 535701510 1250 535700260 535700273
    0x27120206060306160e0607030f0305072c06040f0303120b0a1526090106030c050901030309030b04060609020a0e090a06060207090903020316080c0d030c090509040213050c04140303070f 81
    0x1c3c0480766914001c445d500501c0c01103085507000450542c0040c05401c0301d07207100e079058010550080181d103000c000c000c003011403035076944212040c1d400e10101002440c0296654200a40700a45144401c4040580d9a840c000c0d0aa28505a0100d155410040808980d18040038054111060600d9045145900500881c0c1c1513265241aa03003403400d4100114080504400d04c6100b044d54400010700d060841c105181000070607880765200310b000c0001400080d52000345082102e9000d0b085100786e844510304000609400c0d00000300b071506c04205000b030164004030038a05c2d41000d44440c500754507135030004010368006010b8080547d0007041c1c100310340000e41e84980391840c06032040d41c2c00d06007060300704413001c8044901510310300800324070020704800c14050540f49100d00e0404000c030014284000e80300c0e87c40b45c403500d8400c00c0c10380002030035500c0f40e4030a0520102900c600f04903e10f8030241505040d0054090390040c0c036541150a161401e00100f201d4040d80c2003040c0058031289995400c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 535702760 1250 535701510 535701541
    0x61110140609130c061d09191d1c03060806090d050d02120903043f0602041e030c09090803040803180a05030d050a111206030127120206060306 63
    0x3c2d90040b0056407040c003003902904040040c01042d514840104400d1421100a804801d0358910810054091000c4100710711103036039040c0e100303101c0422005405081c8403200c040300e0342c0303c01c85c43c01030b4690000300003816200c0706640505d40d101040001d40b541c12140d61510202c40881690b4031520030010480c0c0103a02030075425110101c0541350401981d1701440c00c060613a1a04915031010074113108280c0345070081c540c0c100890803071101840b4a001c509087c0902607118905803c05000200c007448411740407203000e400c5503407100842c6140c1e804000400c110510098400c3c142c105000301c2c0e204800c1c0100c100c0305810891060542d2030f107855445d40c81d803028080303e02401c1909170301000641c00f407106a0407503000d00040c603140e41e000c480381c0e4107840c030092003024264034000c1c0064180c5143c000395042e0001200800300309507114030109005203900c90340d910003000361500e0980103d82100201000074403d440409402c402d240b02a69501c0b015201203a05410100c00a0191b042d0b403c000e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 535704010 1250 535702760 535702771
    0x15080c1c09111302030603240403180902040b0c07210b0606040801090f0b070306030803420111150c030411060a0507050f150a0b040b0307061110140609 67
    0x54031500c1201200040d03070100c1c0300d1500c2850342d40100421205142c188423404030800e5050103c0c052110088a030f1441e510020402014081d98001c40c01c4508140360004014268081c811940c50392102c04000300e50300314600803181071084c034502080700b21010150903055014000a0050220700c0d0f5941c6c180210000d00349a00300a0500000030004800d0081c06600740c041c005510500c80c50741454848100001e0194040c9410a04100f000448680031030360700c0351003001288000e846c04610402d080c1d202008031200301c00952001c82079610074101c407001c01482622112403400000b104030f5140e00025003c10001c540d1140042c07a00c0070020011540180714114007281b41d82c0840004015421020480b4005040840d1035002c07c01d08010704919801307a80014070040f4aa4505848240c030010300d4112120b440c1c424800d00c680351a04000500200181503401603a1240401412100320f00700e161094440c02140c5209071802d88200e1114020300401c5282964070315081c0482800090103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 535705260 1250 535704010 535704023
    0x110910080f16090b04090b1006090b0a090b0901030b0907180e010807140a0b07030c230a0204021e0418060e0709030219030221010507050a020604060b0303040f15080c1c09 75
    0x24050000b007087d00141e100b030750002034183c4602e00b0900014183c80542d04a04d0345071008005032802c05401844100850f00d100701a90740d244070240c0120003a00f8011b144940100280c014010059005803400f0301801944103204001035440e40d5400240400b84120142c0382c0110f50300380204038084428201c0500084c0070035006940ea91842800fa43c01000c0a82c0001c1960103844100000002c56034103600c8150151520b0b80c4104078000d4403400305d0391000313110302d070b00145140a5a103c4101525542c98a40d81d007900c46959100c070511002840b003490603250302e4150b02103100d0184c0c40103903019810300d07510003008030700719420311080d03142d00a000070034001c110300008016070761150001c41d40490915109840107030a05c280303084d100042d200e40244942407004004041c0d0003c0d120741d000341c000a000c0340740d1100c0300c0420705500c2241c1290000450141e80441c1160303503a01c0034590b507245a07848810b541e81307440d01c8074841d000d0810808d200601064125000d154280c20131545940147e0303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 535706510 1250 535705260 535705271
    0xb0907022803110303240603063f1c02062502070b04091406040606271d010e0702060c070b0901110c0a150e0703030804110910080f16090b04 62
    0x2103606240d500119541c001b404181d00340e84507040c03080d5540c001c1411054030401d0441c1000340001f110b41000c0c0582e4441800200110f0700c41ca4412004d00e413149244c0c45030300303001002d03c00c43c0a0f1540b0299540c2c100c12161041c40c51802440003c40511800c21400d0540880030076140f0a100120b203110544110320612601007a0008070400400041c003135148001070005105001100e5060000c14040c4968640b420030480300e50440c04038070b02c4e44401e5040210042e40702c0365030600c0c0681c030b802205100704090358440300c0d01201d1040c0c0e4140c1d84507000000e0580e40b42c00c0100ea079010211180d401d08607041c011000002d0140800c02c2d045102100041000000d043d803810050304424819052a4407000805080c0240b20385120401c0c51441401d000d121450845141e80310411720008040140f4040020280013445408244102005000700804e0500c03c620303035441e44581c0100341040c010003c0708440e9120008102e44880d52440c44003115070310300420170004000d0180300c2a00540c070740e0b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 535707760 1250 535706510 535706537
    0xa0504061b1707050d180b0c0304030c031b090b06120a3b0703020d29010902041a09030a02040b030a0b010306020c0607020a030203030f070c0203030a030b0907022803 73
    0x25811660040e508807054580f01030741000c503e032800880c840c40c180728101d00302c840d41400b4064020243c41d02030402e82d60b0b4455241444d4554421035001070500240001c020082158403c008143e850006504440042d15600c0c0c090444910b0b00c506070348a80300300141c1040c5041690040d40c4403100b400d001030038800c80d1044102001032101c80c1d0a0085482d8480f1000d9090032013886c5000d52040d00030b044c0070307041d0b80c04990703a10350041d405840321291039401c0c4425200700c560500000702407880404030356521460754000e900f06d03001d0600a1003002c005900003003a15800c0e076610b0742c1c0090040192052513000d01000300f440d9612150103008982d040808900266850341c001c501c078210060fa28074800350305a0810314060001011900540c0034400030a07400030649402c401035405c10f04480c0c8035148180c9141111750b07002500b600020030000c400580543c0181c0c41490203442ea00d8455a540c0412030b21000b0140007084001c101d800030402400441c05c1c00383c000c1d4428208202828000e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 535709010 1250 535707760 535707773
    0x6020619050402180a1416051b01110c0a050601150518032109030d09030f240903051905041d06120105130c08070303081801060f1805010b0a0504061b 66
    0x3142e03241c400d1600d1b162400402c90081134056400450120490a82600103034010541c2c46548072100b260703420040100700c5c0e15003e6025001c5034505c2104140e8408860550070740344c2c051100191824004c410002845456800111009200c103135140e92602000b036440c2400302070340c40510368040c810361011210421156110a0008540e183e000d13031038600881c105031400300f00e10046000c0250501040001840300d4a014030184e40c40a003c0e083c3c011194500a90321080c00003c01c0c14500302a4243c1c24190050000c00d1213402a01484c9a14030780c810060315940b0451140c280c401c070102800d5504035402142c05900200e00415030761444d85a6003900d42910000d0b0f41020440091000804c20000f89903502002881808098240645151006400603500a006060f0750031440c4044070f90781c03c02e5200d10060003905106031661512107484e425a8400b11000105291902d00041640d00c41142522042141691a0f0340b0f0f29081c034000301c501d0706070211050380074080703c1030141c0003448 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 535710260 1250 535709010 535709059
    0x5070303060e01120c08010902330a0302071e12180306050c211320040f0b0118050607020d020a03060c03022a07140a0b0310060906020619050402 64
    0x16485108613101c0342e81030800c240f0005a10000e850380c5021140001615030110035950454a808100300003c0300a403106030001d880c10a500c0c85000004038030400c10f41650150494502a25100703c00340050700d05215118602c10f0b010b041c44001402e005001d6101e1002d11a40c0840d0454801c151541d81e0750b500142e49007030b81d102d940018040750ba5011101011010080310380c850f24070781074900b17190465010b560f03c60140a0021000d0343c00700c0c8807445070311500618002c1c0c09001005038191513103c6500074529030394a180025000c4005103040340403942c2c020241d400040c111403420540e5400c00561801d00c3d00d040381c00090a06002000c925180309a5244811075140541d698151200402d8152401d80c030039642c0000003e06080d10600000341481650f1617285000182001d60000408580c07440d44900d5448000100f04204d04243c44c810008403030b0075888006e501c0e074840c2c00c00d81e118081201d641f10040c070302c80561740448420360440358100340060f10f08441c0c10600c6070311144441 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 535711510 1250 535710260 535710269
    0x31f0305030d1b08011401090e0f15010e0a1701060f060e01080c070f060e0f0f07050a050406210609140102033103053709080601120305070303060e01 66
    0x10070200309030295100310f0007004458a80c0d1403916450806492003d00228010f000741c150340c1110440a88050b40112903c1024200c1080c00c62841e181500400281e084111200c404200680702c2a10855008102094503c04001c0400e4042810500b40c3c41d01d1030b5815203002059074035000005a41038100c2150030280c6502d5859410004540001418031803002d402010762003400c201810104080300b00b8494483e6201c600480c1201e10f035010149441005e00b840d08a0b400781e2510550400000a01c910494030151a2080e02607039070001c000484565104650810b941424042409610480c1c0d000d003c6100b010009134040e200e032100c0700320a02c1c01c80780305200d81d400005e102c1c0e101c1e40c04155101341e11441e59400420704d05034441008107042e50400505100c1d007c06e01c801c0c5007040e03229241d000e1072424102c00d0955040c0349141c1c0c44007505a0f0750404142082d80200350504046a4181607800d00301c201e481c0ca800e5a5400c4445900c021b17010740805594100214210b03550030907417402130 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 535712760 1250 535711510 535711513
    0x20d0c061b1206050f130504020f04150504050a0b011b0515100512010b062b050a020715050709050d02010201140f0108010605090603070303230d02030a06090b01090b031f0305 77
    0x2d10740c40d01c190048680641007248030b4510700e02000c0d0507940d0800141d81204440d040407900c0d13152440030600301000e0303800c81ca81c4603082c00605c00011209a601c58102d400480d818407468590000240c01c0380c0300008424001040350f010050f00a0001010325a0644560101e44034500c07001c1c18113140031019644050581104001003000e45027000c48d8481c00b0503810020001804003d001031828866120511891008000f12500d2401801c880750030a041d0300009002600e40000680000d500542044981d11907034000d2020001c3d507449400e2045c1c106444105c819814801004030b2488841d004904564940300803040c0c1848044800c0d00401c4409415105075040800b41400d6903005c0d00028000d03080c010400c20141d034006280710842c2c1c4c060030134259803610309050381d401d038000280c1000e050343d0006400b5030b02c0640343e0040d0311540e501d95040160326181d4600c0819107812901c0c05000580c0f107201484103000b21001143c100301c4090b082410704100109442c42e001c410340c41075525 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 535714010 1250 535712760 535712777
    0x3021906150e07092106110c01060b070c090f0902040c0801032a0b0a02010b06120a11030609071101230115020309151615051b0a020d0c061b 62
    0x1c1144071a040000781c0315030740740d0040da45441400140340c1078840c8110071840c5e0034450140759800d00f00c1e40d21a6020b030800c000344001442140c0f851056409601c503554107610303103240010011950400e0720314240d0b21410b50152285005041000b40108002c00c43c4100d0b0f40712030b548011b03030300c510600070940025114642c0c0c944c1b440c1011040c0002404985c2e0061403441c4003040c52542d021041070964218018143c1c6a01031804100d0040c807210000c1500540001119003008407841c1c141485901d01b400305110300540b4050410030742c0000d07a5500d80044c0000041f404140c05803001c01c1c0042c0c00700c400001d180b107085c400c401100d0180400038000c088003c00501c18100161442400260700303000842c901010345020a000d4000c100c1603141000001c0745d01010304480074035040044d5000240c42034a02030700c403041801480281c8800303010020314103400e038103080f221081c0c0301c03200c1013134014088a403001d01080e200035070101c0702290541da45088281030301085c400048002c08183e46c4a042 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 535715260 1250 535714010 535714031
    0x318060b042904050c0d11040e01080a080304020d0f050601060c21020c120a0602030c0a260105041d0a080901081315091104060b0c3703021906 63
    0x200c500c0c1040c82c2c2c00d440d000c0034021412a4862400c614400020341e000540d90f580d800e40b640450264881d000607480c10810356140814480c0040c2040e90800000301c541c6036a2581640c0e034880c041e03000185000c2040c40001c0152410601541c0e0f40d40c019201c03035050b4030065031030030300b030a17001d07008540414005840030b018820388101648941d0b50154042c1e13511100c0b02e402954441c082c05035184a081c1e0340b80703030001c804818048610b500354441e42c255240d0910448461442d046aa0f0100020702c0d541303148200c098005210400240040f00c1c186c00300d03402d00c3c050001504403c1c420151003550100d90b10101c0c00100b0040d580c0600030104070383c0340d1414100042403000c9c003810b0042111355003000000800d031325140c1c6540003040180001240c4100e4981490b0b058108034102da4040e241c6000083c0c0c2d014291700804581c81a0419600c2034543c0c0421440342d5216424440c500104a065990301c2080074000c28003c1406801200c51181e0805840c5007002d51b241d0003210b406071039000b001e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 535716510 1250 535715260 535715269
    0x1060807090c030e28080d05011a070b22080414011116260f070303020708031206100e060315090709060e0f01140c0303090f0703031e0318060b 63
    0x284602e914042c412508620107107a60f6010300c02d1103194240410740700d041302120070348081d00310340d03404036005d0386030040d442100001b80000d100d4881180c061012890001400d141203c0d54144d202020310340c1515040c0300c0c0a40d19280024004540d1045445180070842c0304020300001c04560f861500c4441340d04000400501c2c01da12024000d0303100740030100400791a48000403c0e9002070083c446081d11010540700d014045600d40b0380b00b805841c145ca0800d00340811250180c034065002c9489060b076800b0910350701d02c200074862124101150100700c640c41e2903090304c07690040d40c2c42d00450303040a0300001862944155004a01250000010307040390510340c40c04d0340d00c011030342090f825080c5081d9024140ca40141e01c154815461400c00c2d20041c1c0c0101d080307280801c01d4400c4151100d0380b100b10346660740d01c02d50780340c0703001e1103401c0700035802480000307468007601d625584a25003c0f13200e6034072040a0081c0348004042c992612101a0b1140c1400000c01c00346000b00340219060f001d103018407 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 535717760 1250 535716510 535716521
    0x62b0b01050403080d050a090204050411031510050603061816030c0c030c0f0c0f08010b12010c0e0915041505090703090206033c07090b09010c060e0c030106080709 72
    0x850511109000c01c002064181d01940d8030b00c104108085a00d599440042d0001d05d05048029403140ca000180402d002107020f081c80150819011242142e0682d06941c3c100c5400b111100c02142091106120504004010b10380091014010911011030000461580c0c5d40444010103200c074005500e1190760303410b0058243d161058241030b0b6004203aa14014580c400d0004043c000251000c0c40750104603480c000c0100410a080b00a1117064940c00054041c00340c24180c00d10815100d554804c03d840180b00302d0000552903110304104110b10403c0c080c514400403c5603003c011007124814450304d0324081c0b81d00c10720660a85c0f1581c942058200410454003600b001e0406291580310710050312844110303038004101d400c3c4c0021001c54000142d001165056039003c40801400c1e04e40701e00260084128003641c2c80352200c61010340c8410080e5001c0c083c010320ba40c0001d648241900100e00140d12501c40c1039491820749021001250100303083d200d095100008944c4500b84c01c203c105101d2140d0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 535719010 1250 535717760 535717781
    0x1030b210607090f090b030a06050901061a030c0a08090f1b011205070c080c030408070f0e22031d060a0c0302060610021b0d0f050109110409120e062b 66
    0x30603250804131003961800c0d09010b009400760743c0d407800304000d0350104200c40603258484014800c030315000280303901809035031280c03501d03116400e5130b6a100f2000c1c2006880c495591012000d08002002d001118040400740c01c2c000c1e40d0041c00080f902110003449081c080f0083e030240d030140e5481ca4800100160000e40c043d03201d89141c082841b184661107504030301001c0e0001c1c0c865031201e030b181d000a0700314412503202d801144030700f403800200904080404401c48000228079038890391544200109000069140d40c8883c1e00703100c00800090091128410100301c205004494104000205401e544440303016008964025a88800c00d0360401c170003a8400815610750b0307080310036560301960356815030f070511000381c1c40c0c0c40800038152100100e035800140c005043c980310a0030750401900900c00100c040d964403441c80c25002c0d107420710b03008003035826521881620b11110401c808541080541905d280e000204000c01c9064044070051085403122010008540c40586940c1c5002c89001c000d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 535720260 1250 535719010 535719017
    0x406080a090201020a0f02270a0b0901080a200607081308011803051b07120507150516060b120114150303190c050a03110c011d01050901030b210607 65
    0x7a00d40050b64007059400049500542c9900261007507c0010304e0f0210044018443c50b251428078891680070a110f9802444665020880d5030904014003443c00024041c0d030505a001141c6000090410b05c9a1480c90300521001d400d140104000254240d0020314103031004480414001d0550031000041c070300400d9240000c10006010038644612102c0c151030250a00401081010f804407186501080d520040d90650b07000984401803559848983d400c2074500f48035410700070079080305892400c031485507152901403c100e000d403031210300d44818402c202c1f0b00d00e444101e100d40a4880880c0161a94035440c00030502d0f84950301c10202080009110994510b04102d14415549000c800c031010368a500c0084402011410010f40302c0ba04140c1e002031880c4501840c40703042c194840c261030a03080c500b000b692042d00d818401185c0d0192200e20b40358141d0902541c034203642d8020341c000c0001610605001c01c0c0c1c02440c4c40040d4043d0f6005005840f2202c0a0600c900c4000080c412698090507908 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 535721510 1250 535720260 535720271
    0x42103110610050607050a05010507270509010b070503130605040801111204020d02011421280234120c0305190c061a03010f020c0a1101050405150406080a 68
    0x120b820300450381e10b105450040740002003130018040e040c828050b225802000a0001d410301007001002c008170320300e2f070502c450300c000005114100d00d03201071400c8400081107510346900303100450380c15503c1654102c0b181d01c82000b40d180c40c401c41d0715030780008241d152291501c892502f0b510328251203003c441c0c403032a054104075884010b0290400070f50059010f40303078121003521520046c1c40038564071010a1021801103980d42140c4440462143d4030002e801591500392240c080c05c0c641c1c00400400c00701c0700c00c071205800d07071420b620354054500c0b44210104440d031740d00311040c400a160b11030901c030202250540c96110a100046142d6040d03000f8500e4050410015501c0003041c501503902000260900c00c40244005481810041180d5030040020400100d49040321300d900c110b982c84030f44c000e500380101445510f41901c280c9140002080140242e005143d460b5401c0502c3c10384028103100d13090202141e00d445040c025650804c1d50030340545c2c0d40d404c04101800a8000400c142019030414 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 535722760 1250 535721510 535721521
    0x6101a0c0307062d0c09051e04050c090607030201020702040605031f0903022103041110051b0a0f0c06020624060c01270c090204080c090c0421031106 66
    0x1c11984101e40207900014003981e0154030f801401041c440d00c01c4064206480120245400d078014180e01d200c5840301c11001e5501c01c144a460020f80d24581c0b04500e910912240c942800c2c1c010a42c81603803c0b40c4a86460b20340c100060054001c01d400750f00603940441c4c2030342141000d1042002038041200101003213403002403907006a45051186500d015101d400050416008214450701810070121440680315110509220703030b0011039043d40d080c40f41a03409070490a0085400001d282c035030f41c03a80d2903c803000d2011485060b00c0e50041465100b00c0e01d00d440400c80c07042104140501c6070304140012881d00c04004e03d4803602070580c00e42c82050410080c030303800066501e5100c0c00700a441e070701d480c0c5451080007030040007100800788088898170811a140001c081c000c98446204030790300d0b0405900c0e05541c5080b40034178061036500d90f0000d01c1c0060113107130003a54298401c01218040d440e01e608c414844c00b8000d0b40881c02c1d6080b0031003001d61420550040d056005040d040d030002d02042c9441c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 535724010 1250 535722760 535722763
    0x11401170c030417090d2d0b1f030203070602010207030f02010e0d0807021e0705011b02030706030b0a090f14071b0825050a02100809060118060806101a0c 68
    0xf6100421406000c2d0034030641e544240300b901c6940e035004107400d4400d20a810701302d804142040007401c40e4000501011420300541c2c41c0000790030303045010003015603a9420440149032501001d00140005480c00000598082182402421540d8000340e283c03002854058501800412071209590404240c0740001c200098150500111454183e600341c41e4070509a04110081c401582000200e050454000c40001225022100c0c2a80c1d411100590b0100042d800b01c4010380003945a04110010000140f00c0c1e080461400c10003445030009903034034041daa044070801113207060300640311404a044407007807401d207592000c040c0c200544038100760070803010a107105001c02401c0050118248450511203c500c04105800302c140303100303171005c50900a07034600c80103904078410308001240c5e00c0e0080c800c41c03071607004514003401865581d081455101d0403010200d0780d00c3d0b0b150354600d030018950400300200381c050551403030b251f80f042c1d04205494000e42c0c50b605e944149a041000842d440034030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 535725260 1250 535724010 535724017
    0x712030804081c02031314190602030a1b0c02041b0c14100c11060a060807120302100615090e15061b010203040c090e01090c060c030e0405011401170c 66
    0x51280301e869039000440007215103c03035044811035a1038404070402982c1c850400032003d070316024102c0641c194640e5241c3c00e540c1d0840040d0035074003041c100b0400340016540e07009140c01550110300031501ca10003010480300c8140c1c2220703070000140503d44207000d42c140751003001c22660210084a40c60300c1802c201612503000b810009100180200c00c3c5502040c00b4811042c06100b5598140038180d030740302c401402612003d01041700740c0a00400b06842c07030340c030f842034034222000d90016054542c0750002e640301641d076101c41902540074450780e49844001510a940150124050402c40d404207000c00400c80f4405412060b5141c030f6400034490110000c26a514080c2d200b16500390b078070982d44541c08491030440f1a488400d600200c14801000310421050050300d084600401c240e0b400b80341e15500340c90b992500900008201c050502055110381641070f0020300070700780b02d0184024030000c6000c40c0c009921846924110a1500c40c5942e0310060308511003101742c9070040300f810003602d00c030094071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 535726510 1250 535725260 535725263
    0x18040216201509091b0d020711030304032402090402030f0915072a0204051512071d071107180c05071703060109150201050103022b02041104090504060e0712030804 72
    0x1c10403000560768264174407a80003250b052000c690f0722401c0100e2040040c0d00510720843e540740441c00381702010304002090364110b0790030030300c050020180c10b403040080036070045000d6141c82d001c02001c03a00d51114002140102505414000380d03250140c890b078240032040004c51030385003408050007429580aa4180904040c101a5010010106c2c14000f5031a80c140d41c020340180c1410100550038140c0710701c1c4014a042a00c4c801c121642203080349807a08910300541c2c00c003500c17584610790400521030707115600c603980d4117020000005190419140c10403990140b62611440c50035426042494004e643c40c000440c28501e003000340035941e0071882640141058000d1401000044050380316240030b030000c0c15110301c0000310100040c00203000c0c00c000d000c1030740a07000c281920015450343c135402590a08510030300c0380c50140720f40c4c20072020301040c40c100c4543c04014000415041c2e51703441280d00685c480e030750000c1d1101410144505185040c2d100a00c0d02400860350408641c00042e000c2d4490b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 535727760 1250 535726510 535726519
    0x2a1606030c0816030b0409050f1606022e0f06030c170709111b240408031303030e0d091a0c030a08040807060c02030901021606020318040216201509 65
    0x5544010100d00504244241540c050f040c045441c060001c0460710b040c4002c4602c0c00e940d01e0340c034000410388078859244280310050744105080c00d0f24280700c0c081c1c0160140c903001d093709100b0062036400c0c252010802d8801403107a6684042041103030340307401b41005107050704583c0e001c0e01c031b0980216102d00c117a2045160b180e444079500704070310804a040f903e0a600e00e40424400c42c000707402a03aa503061007090030303c000c950850482d030010542c3c1d542c28841d59200c0c100b00d145a5030541c004a800c1001c000880030305449810b0000c44280905c00303100d402c58155a02199607241c501070401c0d403e80f00c0180310440808101d65803601d5004411514845114208924940c0703075032809040b14880c400c40688102e1601502c02407041e1302100600c22404241e00f00c3d5044010b21000040001e0300303214540150f4401c2103200b403a9840524590781116000304010305004200410003c0c0304002c140840318600c03941d58000500125107901c0071507060a9482c05e00e102600210303a02a8803a58481c103104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 535729010 1250 535727760 535727791
    0x19030606022e0203090303040302101505011116060e010206060a0503060f1902040b030a0f1a120a0b0c250308130521030604060e0f0109022a1606030c08 67
    0x300d0280e01003038041202d194108540c0c80c6056401c1d0354980c0c1040c0d030200c0c010b000d0300500002c4050140502d52400e42d00000e841a21442c040c01913a500b25010900000e60040d0045c81c007074810707100008001070000e6261400c524414500090030400000d282034483c500c004030500241e10b0010f40145d0040148249040680341d003031009017040109040202280d000140124001d26482c01a5003d0360b6270100a01c03841d51007003100c07030a40390101c10030425854412200c0c421446c120400c014041180e00544520a90075118010098800c641d090b140c00400184001c1d48014020b0066a50001500c0000d0900c0d5907a4020a0b044000e0400b180d002c04814032a410300070103000300c11148240130682c2010350640c1c061180550400c031001845540707040c0c0300240e51113440b10300038030401e150a0b01c0120b980c24013010340000e4100f22400c41c208030403454400301910701c949540c290103081c031004003064011600c0f401501003540d00130b80300300b505120103a0580e0750010180b83d003181e42409071028 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 535730260 1250 535729010 535729063
    0x3011203030c200a0204180b040312090209011203080705070314091201020304030c02191805130507380a121b09031a041a150a0b1903060602 62
    0x3121818503a800d21004103180b018070703d0000014102031080c1c4251020300c00301c228420009400b41d0b014401410341d90344203001030300003489201411659001303010005401201c40d0085209024240c000801da07003007000a9400740b41d042408141d000b41c142c03a046184ca491950020a54110380b402180404d201240411850b51250101c0500c2040c100085490740707031600380100742c400740c0c84040c0d00411504050040f0810f521b485007082d074203480190700f10460b508081c00002c2c10010b1124652606201e001380002e0007e00c0000d0080005a42211140401d00c00321607000700244000110100d0310b4070310380d200003864070948004150358100208a00007103511000940000d40d41044c04120b15200302070181e0b00700039140300340c83c0200382024070681600002c00490105131400780c105103154080f064080000b500e200e50061048801a42c0000d00c0f001044445015402c00350108502180310190f169044a607960822154070b024440e040c503066002c0c0d00da01402800b1884102200701c03506 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 535731510 1250 535730260 535730267
    0x9090108190f260d06060f0906080c040302210c01020304031a1003081909090e0c1c2906030a0c17030c1002090a060509061c09020d0804081203011203030c 68
    0x43d0600c200c49403803005407401d44002c410740c010601400c44074a020404a450362040e255154070310b1750b50301c901d030156040032030a403041807004010031a00d1208100110040c1ca841d0380880484071b040814070000c50440c0903640c2840c03100920390741154414042003000c24401c0120040c4250030103400104d548031a10411109001a00064141c1c800002e4581102c9003018103800e00c903015036106521070b0b40702c1d10054299800c01d000d50340c6562201d400c0c0d40c10781c0360840c9411300010031040c419544660a54840701001032141280c0000084040203508050001081d283e014000303d0241c115807203076035500843c074070040c044c064044820380356074901c0b12420012212030700070345000c644203050004010000fa5014480c07072802850f5a0321300043d80b5000d10161005000010b10f030500303043c4000c0440702c0c5140280b000b880102c1d00d524404026880d55031221103810300801c0419503540c1483c0c030300fa01c1c00e04002000245884100010072160a400b80641c034100d5045c90082080040e181d000c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 535732760 1250 535731510 535731533
    0x30601020307060e070501020f24060d0606060302090103050a090507060e0a030c0e062e210903032403020609130e060a061503020c0d2106030809090108190f 69
    0x180144c0c40d0125400080d0800180c2d40b040704d40903030031134496004202d54541c4483c000e26919030218000a800e0751500040c4982039032021f405088030301c24007840c0d21464252069a031144011a0340002c3d050410f50749070142d917034450080c02e0240600303a0503984076035550b941481400e007000f03038a2014002c2541c840300704100a50b000890b62040503103034075a01c48a06001e50b90304e03210b04039141202100c6034900f801c21445400200c0d15420307020901d407064902c041c8070722002400c152801d0b910b0240b901701d441003942c034070f0081e5400501000d041c40e4608003820b01e9481b4a902105440382080140e85000031140800020381c0c451268840b044030f000050316969201e058180922010007854400550141c070844003a0a4100c114541d004400e604074403450f0801c02080d0842c404041a4a000b030005812041c0c900410701c8003940711140c4a01210300a0300122005600080c00398501c1c5400d507101409070a00f900a0300e001a0440606107140b4443d4100401c2c5c050340910080030312444a009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 535734010 1250 535732760 535732763
    0x50915090a05040201051c0605090915040b040501021b0c0a08010203130303240e091501030201050405012706120501050616170f120117060105060f0c0c0418020102070e0f04020105030601020307 85
    0x8441f000101b020048040d04181c000d4500809503440000d00000e00000c03e80d08000f04668a41519102d0341c5a80c2150000208142c0d40d035034080010100c440c20740341251000a140300f0140c145c1e0181101042400d604645c044e485aa0051040c00320780c3c070451555246036503041c240000c8081140311844170042ca00b8000c115012212400000c0c900b9003c01011700c1007443d40300f42c50450850340c04a0710b01450a01001e0700180c1d00b80310502c1154015600c0703400021040400004c4240110b0116200d000141c00410000d035201c855107017100018004c60f03000d04000c60381981040c80c01c1e11460160106844050406815a06900305800181c000c40d02510004407109035030300d130043c820100601c000e2041c01c80021121a1180740b40341d0106200c0d06071040144001c1c5011544001075429410040c090030301e0303016840003054240e55030b218030702186403402c480715480b0750240000790070945240d00500741e070884c003010803044600d0691025031041c4d09003031181e10382c0c6650300100c1c51802250030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 535735260 1250 535734010 535734037
    0x20191506080619020a0801030204020d0905011d15090303062101020f090907030902030d0e0411030f01030b0105010804050c04110708130311010c0c360204050915090a0504020105 78
    0x50105044502240280c0f0401c05045100f007011030001404003288074480d18440002d06940040c401494250001d00c032448001c1c102140381c0586841d040d00310340611071a515443e012204000410000b802480c400d1800c643e01082245008480d4a40300d20000702403511505c510500c000c070218584a030aa010f0300654000c54455507100820390b610f0340000401b521440140000415003032090052a098550140c00b8080506030041d00303503192260f00c1101d551064840e20320050913528070000e10320442645654619651540c1854038010f08103030003c5041103044010480810b1001980006e4007005540004510f0286601003086006000c0300400b1000b0004080070303c0d03000c60310640140c82c00f4980e012546c0b1580710041d94031600c003a4000300501d201e030303c040000808114002000519041404409001e84044192180c4014000d50070a541c04107041c8400d0800c031400c564084100d8088003100b05031800001d142100040261008588402c0001c1c1103922450a44100490001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 535736510 1250 535735260 535735271
    0x5040f0605030a110408190804080a03050d0b010f27051513090b0d14070801050708041202060408030f0703090503130911090609060d020c150601201915 67
    0x8001d00d01e9000762226042c03541000340c02c450020003502241d00325501c040c002c0184000003440d01c508900303c6d0030150364500c018440082c81d0302c010300000d16068441d0341c4035030303540201c21600d004544242d120a41044003482d90b401e409a0006c482a80c0342e100c504112051450900c5d409a017941160040c1e074100104010040340f00d4881c0c80a0040344050f041407a90294541042c00c04407000f045216501c03c000c085401d02103418001003d94003500041078035a050f4031017080078203544068442e200080d8050003080140034000946001c1d54007180b010f842e507814a500d0b1042c240c000a029441c05031780c050041803499000f98000c0d80d001b80e102c02569200c0c0c1410034212801a01c6224650a1500701034011000c0c1c107100d42280c0519000a102500b8031050030240300e40e5030007512034031580e103074200002c12191a040041c1051602e60541c0406a4500a40014a889031080e20104182c008403048402c0c0305001c5409071a254030500e4540e514000d90800450010b00806420803082c03520 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 535737760 1250 535736510 535736519
    0x170c0d0b01030b1f05010f020c100c0b0a020c060f090c0d03022109060f03060307120809040605030607120515040f1410030b15040e06090a020108150a120305040f 71
    0x88480504030380c06420443e54a5030341c40013060f81c3c008203d02503403d410503042c06211030341c0581d41030380c00d0b01024411642d00810540200705100b0200c00180049038000012000b0010f409075030b154406002c100c20750038641c0c082070a0760748144c0945000400b030304a20000c5d40e10b8a0400c40325442c24801001d410f009a514240039496015681c20700400702c0041d403043c0d15110814084440081018202030710b030516203400b040081d00301403c01c50b45401140310014040c07508e040b0001405016694495484a107403040200300d8602c2c2e40964000c0d0005d000300194907400c00d02210240b0080200400e00d95075080c011081d2200c0079122a602c46c0c03500300007501803c850b40c001000f08031244078442850300c3e4106281640910703032000900303820807000010901c1a00003203510140001910200d14900211192424038408843c414296841450444199a40500b46541040140c9c00c41001d1955141c089400c05d900e50240910f10015860200700b010302c0340c001c481c0107160038100241ca0320f864 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 535739010 1250 535737760 535737773
    0x91409060d022e020f060402130e07061710050609040b060d092a0e1f0f0303020c090606030105060a1b0b1f050411090f030109140106030b10030c170c0d 67
    0xa00480141c4103400020003070959000017000d120840c041001046103668650800010000b650001c018a507240c5104900e500c00400070580074001c1e5031181070500c4090700c65018181001044928007003040c01c010841900c2c1c036003c941102c1426100460004200c0010034410f108047c60100003500d0900840103000c407a1200e1070480c021440d2a00903c04001d855240e0f0340c0c034901482c0000c0000c0c4000c1414000c40c04000c517198494184000e500c0d694070a20110f4800c6e09620540141c2c010000f000e02d1803400d900b486a0042040382e005065504200101c0c00364003403103c411080c041d0108403090380c03d601d012a005a41e81c043c80c46501032800c20856900740e100c1d41b200410031079881001040c3c40c60300e070045501d05441141d04a0400c3d4a8004100402010180680e01135583d40e90000226400030590701d980401d0400102d01c1034078500c0d003c0080c1400510311180704503100c0f02400001d4148030b44604803034002c44104400089500b08904110b00c18492503032001502c030b040c8041154 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 535740260 1250 535739010 535739059
    0x3060c0c0f010b01140304170a050309010509011a0d08090415060212071a04110a06031b0e060d051806041109060103091a0a020706110c010c091409060d02 68
    0x840081c0c90310030201d0741c009802d9540030050320703021890320310114603001d80e0360028550081c02111960307108041c0031005010795200c00c079500f001600001c100040008240101900420008020060a4071005141040c60415141c1030b10415403e19908240103500c0c0603190303d1500207004000490230803a010304440c8051107040c016001d0820707400102401ca00a07074001c2c0b83c00103518150305e544806060342d0184024011540300083d039401c0981a2505040f85001d426540c40c009404d80481884002c3c040c4400d52003810810103000744050b588580c0151034994520101c040340c40d8407080d54000c400146a1843d80081c8140c0082109114400340c3e400301170700f4140c07910071040d101c0788011000d840c3c3d000e4020b0700d451140120050812006005e40b9407066040b0b500504200081c1e45400541b011001044129840440d04c08200c0c4030030302c07a44d1101000d60400082e80b500e001a0309444140340f204403840303030355014006050707910356504500d211540144410b808020390000c1515592 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 535741510 1250 535740260 535740277
    0x1c050a0603030807020316120c12090608010b040305030d0c02070b0a02030a030f05010806190e0d090f05092401020307120c0605010b03060109090e0106090c050417150a0c020c03060c 80
    0x2c880c040410700550021040780d00300e004510020300002c0d61a15904002340544480c4810060a08042e201081ca1424500d042442c0755030340c0015289084001447c100040c0c05c11841c001040008100107200001200c081c1c540c80f00c000300f02c10341c850b0340c01e0f4107003005076018a60800c0300261400e00c00d17901100031701c032110301600e0420805c000215904119102405101030950091010500c0f000b80c8080b43c41d51000a180c01280818601c010300c0d0901d8021401c072030101e10340c5441400800440707200c1c0c4018000c01c0d00c20f5140c0c2c4c0351032100c070203c0d407130440b40c40c03010900b42c2c00300c00446904c02d000312107065070403510345007003c4015071004103000050307841070303030060316000020030051386140441e070003100140d48002c15a410302240740004d114004600035599a60300000800359014000c050190a10b901d0310b030f880301d1804205100c2c40301000d1301c249271a080f44d86013107a802004c002d01500021a80340c0020b09031034082c0b0591605400e260380c154540701e103004000041011000030203010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 535742760 1250 535741510 535741517
    0x2030408010f05100905040213060801020405014a152715091801060201230601020d050304082214030105041205071e0605180f0c061c050a060303 64
    0x2c0c036100000040700c00640310401c44490b00e5004014240d000c1e0040c42d0000d0000380507081500da0102808100c0d08580c1c44002c00c2c4c0d402141c00c0000f90703000300d03101104001040020b0702007000c0d10702a124411040d0305402c50480d903410105c1919104442680d103004018162410081d030a2401c0011a000b600d691865807040100050b004281450443c81d000c0e00a0a143e002129448030707090036420001c0d001e40c000300c1540c481013001178030b1070510b8002c21807038000140d01c50340040101c204004080015281000e880b0a02401d43da0010b0810f00c520440c0c034186459440d51f160912440c41486004081c2d1040a403062201c1c1000100c01030440b508203041b0381d042101341c000d041c26120115805000400403099402109002d0b10003030110a1140c16030807121a036841c002a0541d800c20026111259a0000c10030381c104502e007030048425149000b00448a08d5208490351114030440d641e0141e40d0105000e07200910100b601c01c948402c1c5201840b20b4036015443c03200a046611099001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 535744010 1250 535742760 535742771
    0x80103170703020715020c0d0609050601050910050603041e121112183111070b0a0911041409071a0409020c150a1a0a05031e070b0a0203040801 63
    0x1030001012101d1807545034002d40402481c0004030354900054907400390a50152482121b0f507a6030300340c004d01c8018410320002074100c100e414240d142210503045180103403115428082e030894200c0d0a102141d0342110714543ea95210300d440c0f00b824459541c00e6200841c6280ca14040180b040454004143c4030783c3c0300b0400307000c1c0d502a5a503c0003200035011020004010603d4070190444288417040e0018101148061244124040c500e030b001e8030441503810f41d0000c102a06956005403281f10184030011400c040b03c80d03d0300e0031181c5001d001000550350f42c0d80704d903082003100007241600160040081080040701403105c4088441141e039154140918400801c004150304144500c901803c2d680c01c0c1001d0401c00454025400104051100e100e480c1c004982100742d1108503110b0110a000410081c1c0d10381d4004003c020100000d81c070030041030b142803180f40c600048400c944040001c041018505041c030403424000190000031068400040b15102660000000c0c8102c540c0540204030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 535745260 1250 535744010 535744043
    0x31e0603060c0405010c020d02030d0207090e03040b030105101e020102040e0c0712051608130914011a0706022107020d0807020a02090703020d050403030c090803040f03081b0d080103 80
    0x8840304210b40c01008030800340000d201c0e6501c13030383e180c0c06510720260080c90500c81580010b450803001e0440300c03005074450340013404200c00b140038100030018038a0065040a0900d98943c14a02050003401c0c01090f0fa850107040e003d10400034544a0000c040d011540052480c00003030207984140030740e08181c0140d8010412200210048404058010218486046030542c0847d10340c0d200300c00850007241c0040203e000308121400802091303100b1038001c0c001d0340c40e001c0c010003500c500c82c4500c0c42504c40031004105505100e002500c3c001900c00245035503001c2032030071078001d0140c1005800b0f01c0c0c94190340b003146260a034244c3d80c011015a021a14185080e01044071b80c02400ca44a800582060300c4070f00c01402c000030502e401580078200942041829000c7d2802c071345084900b41c000903250804240c005e60441a4100600142c5025514082c2801c140045810107407100500710900000c801040802c0e1907003c00d21090320805596500b044900018446035082c001510a0098100b2051 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 535746510 1250 535745260 535745263
    0x61a010806060d020a050708161205030412030e030408160e010f06050715230a050a0606050405101b0b0402040606112a0a060c0b07020d12020c030f031e0603 69
    0x2446034038010100340c83c0c42c8526a40b800130b07401440b54002804002e02820380000d00a401030020705030000102200b0061a0814003003007003074081024140802002400040307604622076401c40c0c80306090201d01d0141c8908400e00e148603070790290803180620f0040040540b01003c0c602d00301d450441910000f40d80f1607243daa041100c0d13200f081c0210381d081107140d0000d0b0b00d0011100840303000784400a24407084030100c3c45600041079681c005215000b00300005503001e071080c01c2c3c001510f0441040064149040684644202c4c01401d00c1904110844103030540300b080d0141409000c1300090020007007515110f1242d440a8134124411400c254010500702c0c80750007411310b501001c0000f00803006e400759105090141c560900c0403040742d450315036034803902c91251940041800b5a24280c4a510341d0070b00700d40b01d6002521034000c6401c0302c104440007541c02080c00c400e20307602d40401030752041c00075405461441703030380811003100b0404420003889003400100d1803100d0b0000c0b801141507554440405 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 535747760 1250 535746510 535746527
    0xe22020c06010b190e0f040501350c0d0215040b070c09200c0a0507170f01060f1502070509070c0201021c1b0501061707170c060403060b010c060603061a01 68
    0x1812003050305489040028400c1c05c8544106102500c5401001c0d034540200c0c082e03d070260403600300c00c60480161500407600c0f00840138501040e1342d010500480107a06107880300313100ca5003a031180341908146e10a5594180a03404008034284901e946c2e241c0d904c03000d042a0304442010780b44c00016400000d8150641c0c0100480e0043c01c2101c44200506000081c146400c81007034040948200001680003400400c281805000c0e904491135a04049025580c0381c00170242d00007800340d0518004000b041060705a41042e103030113804c11005200503620481c075000a60340042e40c040100390a01c140113400840b001040ca000380d00b6074034a24910051103803003c800b200e00c100021404000020380c1061005c002078450320840011070801e64400300804a08a40d0199840e907401418017007000f540f2207180d42003401043d4000d006001000400101f00380114400540841d803900d41601d21607228607a060051a44107030b0800045450b4200003000304001b098056130301000030490b0000d58041d0060 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 535749010 1250 535747760 535747777
    0x322080708070608180f2a04060b0a0c140607090306110c0a02040c0e181807030b0a090215072102120d15030209040b040302120306030606010e22020c06010b 69
    0x20007003551038640302a1039505d11003106203031602407000101c1e002d040901c0a468455480340c40c2507410650302c4017128100b0010010345200d140303010410450000310000340c0d0703502d004d103050208000c00ca6042030000c0b0301d901d074811480c5d80110010021001c0c0c20a00720001d4074020203003000700c1e8a5984101060384100c0010400c20351003c1000001480c05401c8468012110320703240c40c51520043c003140d014090441c07904950001c2c0070401036811105002c040715602c2c0400100042e51840c0c40309060214041c221911041c0c80b0405101036490300000440c92071428582d40340c1e144402c1c2002c0341c4100c0c144550003100d00c000c034a410410740c800514600314420000c0d4182c07a10641310102e6005007001d0840020b0030250003400005a540ca0311117510980c080e22808415145c685402402c29114500021070714005105001039500c0004181e9030100003802c1580c0c0501126000840640c0b00c9540902c02e524504100e600c03a0100d42c019042c0c4e0709030b02003100c202c1e90301c402c0d80ba201c074000c81c102c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 535750260 1250 535749010 535749017
    0xa1e0f11070506044d0901051507110901030305070b07090f2304110c1011090f010c080c0a02041a180a0e10091214030601030c0203220807080706 64
    0xf003000302d200109100c0e9202e510100440350081c1486081c2c28200e503110941440c64135134178240041400d00b501da1a030040c1c00b110f04540d198180000100358685003003c0c00c00805004c1460340800080320805d4050580007400d920842d80d5900e001801d42e80450340032603411211002007541540180b04560945440d44620760102e402c041240001d4060010800038014504034800e2154680384110703407074010800e540750360b2031085885542c98900c0340320140f8105460120500c40703000112090b00c6420200316800103001480c0001210030f48240b010103405400300041c41008413070300183d0340c06c02602c2500c050180302c680700d403984604c0c00c25413035480d000700141c0c682041021000030b0b01540300d0840213000a1180c81c030880240b1309401e100301d1400450340c5540c66400d0042c0404600364450303892500c0c1501102c401c042c04e696000103820241415100d00c54404054003e0007944d4451706040e00c0c0503d4001c4080c01d130415003065100f980b4a41c00303140404503c0041c08580c410a840311600c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 535751510 1250 535750260 535750273
    0x10c080a09032705031c0f0f0512150a080a1112190503030f010801020306010c020613090e010c03242309041110030209180a1e0f110705 60
    0x80c5020040d2110103011410480c40d0000c000d01e6012181c01c5141c0d002c00c1148807003100d401d100a061501da00f007800400e0340110b02a507a803900781d01c60482c2c0803000140c9490000e03107006d800e082d501d5001340e0035482078220001d0f04021120350052140b0b00d45c182c0c220b40f10000d25a640300750399200e810502c0c0261442c5100c03040c81500d4205090082c04072001842190300ca1050404101110038120b04212882c3e0000400d1107146540e0500c0c0c64050140103008600c0d5060802c0042d0140221100081c0141c0300450342a1542080580000013000818012b20041c1215130400707008200300410032000c00e2802100c042c051a503414004100315400f03003207000701800c00340941d03060054114800c04080d451502910306031198000307240694440c10745d2218602106080007402c10503600c2241c1010320502a15400780d03a07010300c10540e020f001c18070303180984a0503941d0010301600c0d41280c0781c140381810609a8a02c0075441081503c1c8048020070400328103040b60039152003010405821a403001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 535752760 1250 535751510 535751521
    0x100903051605030f0708070201021506010e091902040308131e031403041a0307170c2203020303070308010303030b060f040501110f1009030806060316050a03061809060e010c08 77
    0x1c10501c020381d01603402c8030305082000c00c0340103060f880b1305e10860703e20402003031080c11540c0410079400303050901c0c0b0500105d46003001c0000c1c4507441e54040f1031b03ca0f054010204008100701c060303002200c403400c00150b50f51034903030a200360705500204011882d072180480000724907aa8860359402a01c6550140e9019482c540324114210440c1074112401d00082000081070f031480c08148104c80b03002020300d92a440c02c050068450700702c9620000809028a0411100700602411500c100080d40c82030007000c0e4142c84240340f40b1405420080d0144000034001040c5034010040c64102c070704c01d0780d0522104400c0d01c03e100c180e00642010080d040e5041c0414452980a90b0080f0b4034020340f10b048070902e10008070a03070720b072014030050001c41d140d5984400c420b240d8801c6000c0e500c010261001441c505115840c4604421808100010803001141845001e4420707000140141203054034514804809422100100405001250040d2420641559070a018000e00c502c6581d580c440d100d095984 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 535754010 1250 535752760 535752787
    0x140f03160501060e0f010305010507030e061801090b0f09062401050a0c30080f010915090203040309090501060c241107440901120c0206070210090305 66
    0x440c0800ca030a55215a0b0116840722043e0320607104911441420f20079505d142411030841340003038101c404050504102c503030f89401c001546904209030a1200c0340c0d41241460107030042414030002440480503000b070010880d2000500d600520309501940c030551210401c840d244181d00080e844140c00d18241400590701400243c02d91030f5160400345001c0f28241d40b60340184000b60317500c0b103c07030824840541d5004081001c2540a207c0341c10511441c2c100940c110750800d03014450100700e103460790505c61040d60000b41080050000c643c06540303034205032401405011040c015000740501d81400068640d10070303080a40d601d9004a10303c07140c0b8907810000c209041c3c07130003880380080d611810058070b6511040010101c030f40c01608034800000040e01c0606041c01c0090708105400d081c0300702203d0038620165824810040400610b5689410900584e0180500031450300f160385407a011a428a4001c207141d481411142d0079502c40c00038189a1ba000c0350300802c0c0203000141e051100303a107410307103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 535755260 1250 535754010 535754047
    0x305040c0e070c0c15080a090c0b030c04031b1232010207051504020a0e06130e0a020f0a140d06091707060b040519090c090c0507140f03 60
    0x30119803418035225041003110200603110080000d10a0320071034103001c3d1207501d03040a454045449580c51101a400601d44a4080c118010480c0d45020380c000f00a600c206c0c40740101781026034a80c403840d22103440c522a8000f44070545000e2160342240c11007c1213603c4c040142c44540c846414000c4240d00c5540f100003400102100e548082c42c1080700c85140e030400071001021180005d60344800601d01681030400381441000d85c03518a009000041c0d44021060040c0e4218030103034284c076914480026000e244c41501c5010702407030700e242c00d92043c001003005034041d4026121045821a00b80034040c1c00003880c0b00301071600c80c06011200280c40e0072220f0046c40c3d4015003020803840c07155281d248003101004011a610f080002e24002000340314000c030f60043d102160104100d1a00d1020f034105c1d0002032002610b460741d00e10803801080444550b00001d845081010010320080280103060b650150740d0950308509044030960305a4000518240d85510b5000590b040803218038000a0811 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 535756510 1250 535755260 535755263
    0x3121817090130060509060a0b0c012705012003070e010e090a0506090901110a0302280503150409020a05010c0c030803070c0201030c0201140402130b03010608011a100f030504 77
    0x480b0300502e800c01281010342071010780f4210303d0741003480c0b91034420070840d001d6510041c004c81141e0204032017070344c407a41800d088034442c0301e10304d07a101400301d6590700400c071208021121440c4e41c404040d250400e04403641046208200800c000b000d000403100ca0240d01980380da030220401c000143c003891040043c5103441c0e43c1810601403181b070714070006104880c11201e9020b1240c2d550f081210130324011005c581c004034044003c002511400c1c1c0400010700c21001e88105040c1c000940d04401212608400b1000203400740c03003112140e003c4001031081d8402c1e202c0418500c0b0b0081c1342621480c041c810500380640c014040c2c0403030b618100042d205003040781d606850080880c5c0c00080455003040045201c3d01c456a240002e61b03030184009411580d00c035a682e000c6a2400351010030340301080710710513045601100c2000007c80807440e500301501200c00d04c56015400c01d440060004415001007403c2050140000b0410f0304060500070115405003200300060b6201100740c900744c1c001c0d80110f0304135 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 535757760 1250 535756510 535756517
    0xa090803120402100203091314070f0507060203270c0102060c090906121203070903050601060c030807140c070e190c051204020a0e04050303100e0c180d0c03031218170901 75
    0x80c1071b1002480713071800e007110901c0311270300c51400c518464401c200050703005007541031094100f0f216810050403030203040300082040c0d500101041242d244120b03442e188840743c510404001c13800762090b80c0c1340d8500c0c2920300e001d4410400031a8130820150300391410300c1d8014108080d90742e01d0300f040040300c002c9018015800d02a00c208a9401e0004000940c490803030b41c0c0b42c000a01d031861408a20300f20050707125004201c0d140c16210006075004031b840c0d80000d900e151204046400030b01d40003591040c031382e41c1c0313802d0710501400051081300001070a100d201c4902c111140181c0d5804460f050351140d0a89200040c030400680302c2c41241d4521564100c1e0018041191081d02c8410141e01c00030281c0b026612944003200708000503415124140c0a4090001d1540b030740d0500c9079aa084501030100d4000114841d1060b22040e501e445500b4081d4a03041040e04490301ea40342000f504c0700354902c5124900608201a40201c8050072000d080155800307198100001080c0d00b4854040d04050001c1703042 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 535759010 1250 535757760 535757767
    0x1050d0305030c1614280605090708030d1d010b0105090d1401090b061003090507062601090e070e0f0103020120010c0203090111010504020f04020c070906030501020a090803120402100203 82
    0x5001e90301031204164850000c05d0101c41d26225901d142164050607030203000101043c0c00720140c804a00e43e5500717507000030007080a17250b0100850030003456408c50400c51002080e040c0c039025042d080302d5034005034124031450a150520311a070a0300c49042c24903004c610200855411401d0004030110902d000e02e0951000020300d002040c00d556a546c400e503403c5185005114a610700700c661013070380c581541803c04c1030b91201d5507540c1d1500300c0c51081005000401c20990603a42849110309140c030a91412481c1540c0c41d100400003c240c3c1c84804100c52050500100362580c03411080c60083c0041000f04205a103140d004449260205185030f030440d000011040c2c44401c24010103d0a110b1600603540b80c4102e000010300320341c070340b4100d0301d00d0340e0501081c480035803a209000248058240e801690300c0c41d00307050042c9442c5055002d0001640fa100340002401410b5000d007140007010345d150b5510990b103c2c4403035600c2c010440418201c1a1400111300107140145080c0150a001d0043c0ca04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 535760260 1250 535759010 535759027
    0xd05010b0118031211100c120609140f0606090303040305241b0703050405040e06061c020f0402070c08060405060a3602040b180405100608150a0b0904050109050c040501050d0305030c 80
    0x43c7c408401e06640400c0c490306180800110901030f02c4082c1130b080d08104180700d000e0748010801e450103030030408504d4814020442988594044442003c001360071a95129a00d1405aa0350210038500b01600824040b0100748901c9004040f8000c5070f5910f280400c1c00400e407949480307907006510480501104000c00140d40d1240e01030b1b2040040303040048c10940c81d0520a00040310100c0326440c903188416002c0c000180d88121030310380b548030207403001a260740c1640b80030307044245550000c4080d4400c0800304001c00c031001403034510030018400706215213208241e440440c80300400b81c0e454200200d00150504010070152421028001400800c0d0903040c8004a5440035143c1c591240c0c4035444410070081c01020400c03500481c14507041085550314005540341ca5480301c600d1104402c1c284804504c2d6100240c00030340d803003100246072666500b000c1c03074814000c01700d0300c00c110790314010346614808a01c0c0078403402e8100d0728007505908161141d036504541980c0002c040c1741e800a03040c0314003103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 535761510 1250 535760260 535760293
    0x30810030204141b0c120906070c170c0306040309050607020a0b0f07060b030f03040b280f08060406150c03050d060f1805041509050a020d05010b0118031211 69
    0x28024102d41c03030030201c24100740f65848220384c03115901c0450070004102040c400f8000003085d484d07001c0d903036144d0303900c40050600003070b440c1c4034030352001e40310100220740803480c0b10000702d801d80c0004c001e00449000d0005042810307124182210003030041a950001006941080c8004040c44ca10060484004903181d00d686e00c25a0400d0340108003041c8040f580100b00011486403c2d1145000c4008062032003450f41ca4a40e80d11641c010620142030200711400c050601910524468800d00c604043c548031440000b403a006906102c500002e1506001c40da0b142810312820007680c240128400601e00c8032401540c0c6a8010781c411400c022041040e038006c0c45107441400060420524402402c925144032502c110403030b07800b0340000d03518000c01d000014800c10f02d048884041d8640101d400d000c1c50601c035050281e0040040d4100040070140720800c078041d4004049190700341c0b00c2024801c010380c001d4102c8400750000a040c2104880e81030f01c05030040b1074002014250307000319027920440a0044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 535762760 1250 535761510 535761521
    0x6100e04020c2b02011a04180803070c06140603060c03270d08390403061802041d1e0715020105040c15020c090601140c0606090919030810030204 64
    0x1a034a1120010f03003021034840084005003840d683d200901110a80d0100706042c50210309142e4451a130b100950844e158402c1405864a81c20124047d1246014407010341410304441c0c085903051b02c0c0c071715090b1804401140c00d42c00b4440107401450990b6841c0c808081e25480608814440700d690b1a814428031044050700c100385490b1405403240a07100b0340060120600034100004a15520101e00702821801c508505082c8015441e0780148508001482240c492900041d042c2c81c10004110b050940b1070007034a504a20a83d400c10040d245031a515a00149102e041e0304c003034210904004100402418072112488800191003d40d6900c14412203418107442030440580d440324104400c0c080d038005800018413005c0759110000c050803500030340703603d10b591606218034100d101080c0181d1080b2100740c8000040e60006036501c8141c00d019603200011100d00f4450340365440061012403020540300c14001c10180603040f00200d039501070703920080003803a20400c1e0102100c0003015170381d1070041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 535764010 1250 535762760 535762783
    0x305010209030609191101030f1404050d140409020d060f0e071803080306040c2708060a1a1e0301050f0a0b1f030b010e0310140a0506100e04020c 64
    0x180c1e10752141c0189400c20f8070043c070f02e554580083c900700301c0c018a00c42d01591a20743c4040341240022941006030b008190411450354060b181c1000000000b8070000340341e001300d003c1c000701d4041244002d800c440f1b08a42001ca00c030005004d0104000c440c1260f0040c2514070102800891119100c04a5032a0901c640c0e11401404c500700040c400840d40100701c0300410800c09006403034840c259155084544806401240515030313031188200c01910078040e100e03e090b000302e5030780c012006256150a03100d94600480800b40990004a8090409441440309484418003040801c000450030080030380c42200d1003240850307000e00045150754080c4a080d120344140c010700c1b8200e0038482045011100944003941c0078004000d85960b101e201241c0a44849442e440d000c92046070110040b0381c4c44030581000790b01849103010b0f4586107221030704020794034000e12602c01140e58800b8140c00c00c0e24800e6401540104c075114242c0c0c10b4034424083c85440340c01c003903c05071038003c0058050b898054102d0b107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 535765260 1250 535764010 535764013
    0x204020d05010f080303010e0c031911090109080601080d1110050a06031104021c02090a120803043302030c1b011a010201270f20100f050706051008070305 68
    0x140103541c594800c80700075202c441300440c290360400744807a9280c03501911084804102100084d81109030000440242d69520810702800408d04a01c1840e41c000c101c1030307804181403440100b086600018514101c4a0348802000310300140751041c0c50401d500c3c40002c10b030380241c040320061801a070081500a08201d100060303111310b503051141d08103600d10b030ba45100d07a0042084c2ca0b80341100c00c1c2d21050329030301c0020050741c4102c0100000c00b41079103503205140d1854000302c490284030900c0050f61066004900e11006408403071191422202c1a80e60801e20298558031078804035025400f950340300f2a0480d80c14a01002c485c004068950b1801c904042c41e074603184420001400039006402d590005e000070301041d0f004102d506611030000080300501100e000b105003c0c0841d01c511071004e07a0700501c0c4030a003400c908c4803190381c51501f070a8060082c405000301440082c03080c6c5490304ca07104156601c906009060359100082c000180103202c0814401502085d52541408282c004511510 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 535766510 1250 535765260 535765271
    0x5150d140f0f031804020307020a02130e0f010b1801031509060f050114030c091306021e0c060906011d040b060a09110702090f0411010807031b0804110d110f030a0204020d 75
    0x2c030b0485a142c19044d620b8044da0060051000254000520440d265811a105810301d104117007108020628040f03155100d100b809056000404103500403083c840d01502c1c3c10505400500b13900b0107240c07080c4001442801c201108000040580e4003080d055445030300f011856100c80c051840664030203070850401c0c400420b16022440c5402c001180d088041a1075860052514080c0002d181010300300192440d030700042d60030b0304031a1898290703642c4d2103d10901911000c0c01b9010030342d900b104a03000c400301e00c203110021981030320039480e40c508a40780c1c0000001595030366503100501d0703a000d021035811001c01100400c046031396000f00014240103002040d202c01d950300411910300c0d409030a00480040d0041808046070041c18041c03005c0781e003800e10716403e4079090001c50003081241d203180240c0004014041c1d220f07a11100e001d006a0003540800e00f040600c00800c01c98400d5090000c282a00321281e002d00e03420f0500c1030029070741004041e25035548840d004a01aa4004107128000030b9582 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 535767760 1250 535766510 535766527
    0x30204050405042f01022e0212060a060306030b040201050c0a0209040605070e12070902071b0305030a0f03020307081b1e0316050a0e01180b070f030305150d140f0f03 73
    0x2650300c40c2e01113020003410802e681c52800042c0d02c52002c40c071000141002403201c111100c0e030591007603000c12221581155603000100007010003041c25a20320744940d410200008903d0301c64018502a01d410890606050316668011348680e80600103011490107107100d40b4015070380e074091041c0b0450042d44003244901d0983c2005095400c0114003d00c20407000c4100300195030001140c1c130565091000050b61b4007240d05000c0c466451a515040015905034008010003c1c04000f51a000001e515000174540103000c040d4280d000880b40d1100180d0381d040022a030315140c00d0f0701c6010042d100d003118940306001090703904d42e6046c42f0940e0b007440400014800f08135900750300450380b1400ca1402c0350401d001084001c0c8008540c140c854100120440c881c070030b40c000c84441100402070f4081703080d0b46a00e075117811270801c141e59105030003207464240054500a0a100314a90380e120041030000c448605030b40c0e4104480444800401c5481880461805038070108181014170000000554031624203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 535769010 1250 535767760 535767803
    0x40b030a1b0c140f060f040314030a06090b040908160212010903020a05070f030503040905070203040521011d0a14010f0c32042c010603090b10080d0f03020405040504 73
    0x201c00703882c0150740542071112001302c2c0880d515401c0501c2c5040b1041d2a01c07182011620106c03800b082c0d02d803d901c00001d10890040aa02001c103e40c8410401d0011203400001c1204032020b800018017036072000c20625002a071242100283d140c401031a801455600e00119400c41d5035a0034201c015a0000c460b020a00c4400c200800042610b50b801c2060707541113071341d03042d1240038070300c0b50500030b80e04d5001154040740248242d03405804041c11381c44100105503e01c2104150000c0ba216540d407a2071581c18003202240c00880442c09440300401c580707076555546607800c9404240b040641e559610f1803881c040114000c09800000359524503602070038138a03020400d01b002034650440c065a00b4a02c02c9030355003040c1901c0403600700e40503036581c00000e110341c0301d00070710040a0000050405000481c3d01398240c2d1201c2509030285508842665a02000341c010310800d00504210f41c0c04500c51806d8140b1810300a145158289809800c00740e894010500342c03801136030200c40307408a40c00c4a2040600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 535770260 1250 535769010 535769033
    0x1a09040e01110702130603020312180306010305032506050f0f1f03110f040f15050613090b0111070303030b0906010216051c0b010902130806070203040b030a1b0c 71
    0x100c02001081c0304411440c41c248160080280500c000707004528260b03400d984800011a0040d058400e1b140b25180498695844040c2c3c2008001565508088600340059058103a07580b000c001e40c40e01d2082c40d00407000808041c80e000d0090078443e0910f0024099000c0c150003190940c107134800c9d6040c58044080072a070000d050100404001080368514218131003644100e0f43c00600980c8040802400f01e54464042d001498119041a056050707050040d84110a0040e01e07143d4016960b0b00d8004010152040b102c002e005010301c10014407580c891a84a0702540038141001f4040903c00c13150181440515442980400d540365085605403d00800c00d40e813109091020740703802e0b9403084a020703075115140130b0180501107941d500761000c0461039400c000c1a8000c40058031075a542c1b00c400d0041d521941c0318500b40720000c0b60000700e8003400140c5501a96654001e5411701d824003811950580008000448690300da00116040403000c03d6107011103451540c6140303807460f0174103110b0740411 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 535771510 1250 535770260 535770281
    0x603180f28030e0405060103020c03030f0402041b1d0a03120806040c0302070f11011202040905252c0916090b0913091b0605031605091003090c1a0904 66
    0x39281501c0d03a0000b640b100c4520003070641200c0001d600d8803090300490080c041c02e51400e01c2d901c000000c3c071011030410041c8900c01c1c2d00c01c0b107051010101540d0403e028000340f914a001041c2d6104060980e11310510902e80c04030740252110205543d41d48940b404500040210300c04940800d0601c01c1e81e040c1406940b045c0015801c003940f80651507552080d112481480180040c0700094a0a02c2c43e1700c45d02940c421a1101d29041d900d0b40c0d00c50b0b2440006020540c0c0304030b0442e4050000c1070390010161003800c001d035682e44880740301c607030f01e1040b100703a4100356948100328508099080340b4070343c0d40d050694042d594030a500da4500c111560007408007641c2e0303005085210014400140907035900240380d140600c000b080840c0008151a101004010110030b05482c038107a824041096540900a5031242d044009520101d81001c08160b0b414881c0090241d0401d810f05840d016590182e080302141a03c0f88460070301985d0755804005840e80b9612118022010000f82103619243c940031382c01c40345 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 535772760 1250 535771510 535771573
    0x3050d0b04110a080603160f091407020703020d0f02030d05040e06190513060306020a081909120c0201050c01050a02030a0b03011824020708130603090506060603180f 73
    0x2000c080301160503004460303070fa81c200105000043c056032024482900c5864498a09644284d1030b059514241c450341d0142149503464800e10004014860030054010310007a000307000f005055400344500d4403101c10303090325039540082610005890801191622a400c0d540e03071910b8034141020318408800c0074042074811170100003610000c44c4405071100469100310760542000c0c11a07001940544076903480a00218404660f01464582000241e8448c2c20f4440c40440c20924214241003124100381002e040f22146911540316280945a42c03000117005060003070420400b03040e45c0c1c1c02d54808650300b0b12203e80100a01542413801d00442c030201c10210024046040c56207140c24110022000160241300307034920a2031450080031180340d01c41c24a070400d542e1101c1c94100310119501c00c1200b061107202040380010038900c81c1c45222010b5a20001909a54030b9950030403d403a0400703070413407591000300304210080c070001704260b946044a69001c4d06449c40c4c5011420615043ca06a2016a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 535774010 1250 535772760 535772771
    0xb0306070f18120b0f0c0f03060d0303110c0f0706020d0509041104081005041104020903060f0c040f080708010c0f090b0705070b04180f0c0507020103020903120703050d0b04 76
    0x419401ca0644625649030b458142002d030306840d241030060000d90300c0160f941030400c48103004e01c100d001c1d101d0310640704801d480401d0f8603107a5098105200300c8411040503401800030540790310b041d0a80c081b04601a20740414600c8020200100550106481052a5205140b800240b07441480320f4402085c0300c0c0090100340d03204000142182c891807802d20710aa50f54450b00120042e401c042c0c2d00501005001c03205034003418507142000300400d480644681c0c00001c20451240b8060088502c46d40000e4090045911012144c44225201070080d0001034002d11000c40c0c2c0140c08100031008000c0300000782001450440c1450131503c400391040100000c124203813030b0f00c540001050048070030102181e660755907a802d0884c288900c40e00058000c83c000a80043e88400c4943c0780141703e2160041085402d42d9412214101d07100100034a012840c1403103490090742c000e80c0a0421604081c098600300300c0f402c41c0c0c0080552102d5011404140046880d2031100607501c6401c6601c1800d903820400d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 535775260 1250 535774010 535774021
    0x60102120a1808010c181521110a0e130c0c0311070e0c04170d0207061d030a0302240c041a1605011b03020f03010b0a021203190b0306 59
    0x4040c4607071010201885102c00c0d881e21802e204030348480040c502079000700900c10521900030704c004020302d5224030181480f0008280d600d0401082c402400080d1030b90300102441c11030b42080303480700001070721030a50380b0750090040324540802400c0f41c19041d51045070303c5101c0e208221140401d030301e9010f4824506a050801903802000d03140c481ca0701800d200026988403020185014501e0300302d03800800f01001030211041c800780c0078005031440d81d00300c50000052101002e6030380c0c2442c500000160f004840c03c00c1203d0142c40c080c107019100103408803c408500011070310344486140103c7c016807042101d90442d50360342c444061001c40140441c41c507400e05013101d181038001c500482c040f8582551511500c2d0004c042101c40c0d080720030300008074003216401c180380280034022008503c1d001d180d01c0440c0c1c0030310034405c80e0412529507164a00310307401c1c8030441d0000d030030254080d802d520401060300d09004442e03001e1031207031511414003803400c0044013800003921032060046000c1d502c941c080c00f4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 535776510 1250 535775260 535775293
    0x240601170420060f0d0606080702030304150518030324090103050601140d1b050405090106211103030d022802060f060f3706021005041a0109020304030206060102 71
    0xc1d00468285070a503059141c140005403103224504c00c03151118030006000c1c01529443e0030000c2211107544510005e81d45480c8141c0e100d00c030840c0c1c028101d503586070704131346030060769444a600301d0304c02008035500c08001207001c0d00e107600c00d035110456000b0048074000c2803550b4422201ca82c990603950303506194550381d00c50341d0303442040c000c00c0d812801c0306485111585548040c20421500014080051300c1c41503c2c00c540760429001d2a8002d5051030300103011254140150070456020308444c0c5281402030b00c42c03500d0000c0699044402d50740c60250070405036001c0002d0030594924203401a41c400c007030a09400440d0301e1441031101c1003200c0f040c6089054000c40c6503030f440011101c04159560700c09000a00c4038000700c0d6041e41c0944040f0007506031010301800601d4000c15900944010180520840040e41042c2324a40042e4010b01c0c181c480c240843c3c004a81280c0714040106030b1552400002030340341c009803c400001c95012003001705066041200035080b850a00181c0030356081200101e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 535777760 1250 535776510 535776533
    0xa181b08072102040314010c020726010608011e0f0615051b0f0307110a12020d110904030e010e0f09010b370216060914032406011704 59
    0x410b22100d01120681e220800071407034805180c141e03085641d6a160b180000381d403404201c80c9540c81d840c101102200c03900000d090000d840c800d00c02080c40644024484a0702e20092400035650b540b11840060005024000c00e000120256840d41d22b00300f200300440708503101035414041c62424654100010790034440d00102003490307450040d545420803180702d00703004400c810031005446801000180c1250100c050084a44110113180410101038100b1030b042000b8020301994410048218005140c08040703040c42600c52030307810fa1400d46044c006854400111019000b0440410003e483d030340c1c1c444034010f2003110071280303040d601c00844041082c6c00414052a440d608000400c0510321003030404621031604c9800f8000e006450f456804500103441079074450141c4a103400200400305c01c904200c8c141c540d44e6440703105e01842c008446000c03211040c441034050051b4113a48000c1c404103604402c00009a092050884c244040010076202c0d0b200d100d40842c0c1c0d070650512001030a0354508 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 535779010 1250 535777760 535777771
    0x80c04060e0616054b0f060103031806110c120f0102040308070221060c251202070b07021c0203070b0c060f070318020409030e0a181b08 60
    0x1d03154450121011841a10a00c400c2034000411509030100700f1100098280d4410380a043c0700c03800241244990f46840407072904031101d00c408410700c1c1150317010078000030424002c00b01110505c81c241024142030001c02e03041500003c00e0503480c0300c00c5442c901121002812a0301d0000800001c0388034503a1205a1100e5141c400e1604000c04007950401700040390744103070040000c644d6a942e82c41c3c0f8070f42c07542c0241c400300d0290740104581540b174030500c1c0e280340b02009003501410007a5a6100c810f980d550250020139600c02803000f0f002d2000351030740340c6038030001e1141240683e19000828043d02c2c01c00ca82d44400c3c240c01c2c04001580040c0c83d201446a0f44100c8155000b14007246031001034100101904403d03240e140101300d80d070541d8030000303071705008605001805e0013f440310b0000b1420f03640a40a14a0340700d18800e6600014241584140c225500034588501181446800101c0000c2c041d80100c41801228103240d40b00b850364400d26040340e40c49080b1a01c240c110b03e1001e050400c00802 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 535780260 1250 535779010 535779017
    0x90a0b040302070f170106080604030f03020f070606030f030e0a060c080c0114100906060e2d0907030212010b091807030e0a0602032d0105040c050d0501080c10080c0406 74
    0xc03030101402081040040c01e010b8040082c0360303449103000740220213441084000d40d0308180380080e07052008100c2c240101d07019994844525100390303080d0003942c8050091035154000f00301c6600072880910540018622980c980c83d1410103904006000404c00c04c2c00500c50000746504000d1542c02c00101400c0d66809000b850b210f4500c0c405960041c0207185080e40f10010b440e040060840e6490350400554500706003c06c080b42c2c0b1a00704950000d030302c1941e950417411810f480442c044c0c600300703408420705120511258000d003c002040e0a0707041540e41301d000c0b031380218800c4c484041100100b40541510004203007072000a1000450030440c0f40648101d0b64440400b0500301d5100e504119080e0325504110382d801c400501c4c12900079842258000344421501d000039244a4032508515884ca03150444011542d0a0408101c000c10802e00400c1c140141008805541c04e040e0041c10300901c2004042c2148521100c144000441003118101c2080040810002405820016a816541c0515 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 535781510 1250 535780260 535780283
    0xe0f030706120b010e040507020d0f090524070501060e1512031204020102150108030406030b0306060a0302100e120a050c09091005070908010e0d030b01020115050d06020403080a09060f0503090a 85
    0xf00141c82040481e49125081410001006a05500042c4c0d03900b000c40d141c2d488240e010000b82d401c5892071306500551750300c0041c031103401000512110800344ad800440740319914101c1c1c0ea0303482c2401c481d4982c0c003801a00040f0010000308152450300074041c1107040d260313440d1260f0345040c40c2d91288200480403aa44003803401042c1503910800120b406a15900d10b0440c1035611a508a50703250064800e8100203030030801084468140425280c0c002c12019116038160b5080d6401c2154850400c03109400300005450402e0715566161821080c200c5104c1c0641a2130b200c40c2400e60405800710f103901c0c01401100180040c41100285d0080390880494000481d074458180482d840e0940e82d20925166080285145d00b007032000c200030310080400d403030800919030301000680c20f070386440d5807002102c002102d00b04118100101c00062561040e10010b00c0c01c0d4884c2c0e035540c2160004072021b4000348031174109001c41e5811002110079882c05041c030500310714044800035900c10030030034024002d4031481c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 535782760 1250 535781510 535781531
    0x30209040503090d031d120607111011070c1508010e130807030f0908070f0620010c110105130807080a0c080301080d14030c0906180409030e0f03070612 67
    0x2c1c030541d03400d01c000608400886041c1d04000b130600102503c00017011040b000e140982d460880080c01055900c940504166642c00b50309a83c2d4140002d85030440340144080c80a10700b4840c0308090620446910a51b15800d072420401400e04054115100480300c8001d8494056007104605045510402c1d460390303140e58202c269407800c9101c040c001d008000100b2640c08040c0c106080c24011581686d07007180055507840141da071a8000c0c4100340c0c00320040501440440c1c800ca103001c079050b415010204540714101d00c01801c48080400c2440007071486496929002c3d021300499420850301c80241400c40c5060300e072b200c2c140c410102d0040000200140646903070740181422100181c010310103545942c0d44d0701c462a100e111106e85040014081d040e1241c01d400b40c081620702958200c480d04d1304040c0058140100c0340c1c4059a0b03184130070b0220342d00011540d0b0b00d01031456090303c29a1224889440385040c02805039034180d00314441e03000f07007005001060703004046840401d00c000b4040b6411851 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 535784010 1250 535782760 535782763
    0x1110310120317070504080105060a06051b0705030709061d060f0105033409090e0c0d020a090f02090924012001110703021c0f050d0e010f0603030f090b040302090405 73
    0x221907030030030034001e52004c00c011303d50090060411a20305200034030250351400d0400c01036007941d006200100e20144104032000031512004046401d0320802c450580352100002881c102c0254008804103440b5481444081c0c0c150210500480010001641d10300300240001e0010b60b001700d10341d04200d00800005c0d0007085481c00000c80c0740300410284220118404004003a0b05102016004100300002c0000e6000b0340e8456400c110701c81002070300ca0800f00d0400c2010140d06003200380d80c13020601d5804140c041443c4901c3c000a0205940180d84020304000c1c001c480100800f210304100c01040200403130400c0e4a06201e080f40c09281c200e00500c40c01c0c400c18481010112540ea1035032170403524584c5c5012000041107814003030f408442000d850840c4002d101c482d0b0944510000d054a160301c43c3d514042c1c0040c107c03440c1e0f4840d000c249a00910100380c2150100f4010f02ea100b6204c100800c2416041640080700e90045c1c0fa01d6858141005032169103481580320083c050280000081c0034800d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 535785260 1250 535784010 535784027
    0xf030612060e0f280807050d0305040501140705030f0a06080d0909060b030603030f0705100207050c0a0b0406090b0708090612071202130311010201092102011103101203 74
    0x440080925824a0a0038210700070004641c1d0550329200f06144995a00d400107070208100d524407400650801800341c0c110101103810340112468601030101c07500081c410300200c054100785a5001696107400d040a030f095030740c400307001c5a0007610304091102c0c9a6210045a0b40820f0548c8518010303164414428000c0c280740d0b025440034015152912031140d40030600ca0b003200c44000090090a44400c070854a61009031000c6a1550040051440480000d00509240e80c058003c2e039010600c0c030803008060740d03c100801c64480d00b0400c4400b9a516000d101c410142581c21244c505140c24880c0141c4545114000c1b24400980070550030f041150101c225440100054030060b01c03002c00d1141a050301106640b05008540c0c40302d00c46a0882c018402d03540c8085200300d54051041c61a150781c403a034140b03a055607046540f54510040400c925820030810b402e004103a18280030142c0000900711500c04041c00d0386082d0810070701c40c4801d0102500c605440701a04586094513140c5019a013010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 535786510 1250 535785260 535785269
    0xb0f03040b060312040b0409050604061508090c0a030c0611010b03031e0f0406030c0909140a0b1315050f01020a0c0e0702070e0c0403170a0212031b0403050d17010806070f0306 77
    0x1000040c0460030044a401a0044640c42303003040c030542d182c1c40c0c100420744229004943d03100c903502d40c4410f40e0620942d003140e04805c0000544e907030f1011510110300b038440c26400984030440070715020080d0750362141d000360f03078049a00300800c80403e00f200080e40364403070900c0022054038074011074100c4610074400c0b10400301c0c0010700641e48030340d6900054068664002c5980202d511102c0028440c2e4180c0100300c282e01040b401450155a041d585030024405207004540082030220030500204007031058030045c401e40c91221000600d0402001540a10260b02074119040124500d000621b0440709030256901c04c00070302000d0f51419022482c0080603408400fa08600c2030511494840d40001001968007801808040c030001d21280d0016110f2461040c005a104400c3c440082441002864000c1d4a8807a001c14010080160541c0ca402c26081a2019001864000600c82c1c000b4201300030b80b12000040801580f42c004440d8880c8001000c24044c0702d2812406000d00b48a40e000c2c07005403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 535787760 1250 535786510 535786543
    0x60f180406090210230d0207060e010609060906120f0f021807120c050a0804021906080a06080601152f2d0d050705030c03160c0b0f03040b0603 63
    0x925041c00c003440034055114040e070107400c1c4030034241c03001803203402081c0360044140c43c0d424010808505048143d402801407050a603401c1c01004e000500500802000910402c000710301e540c00d280e1080111202540041e030040e00c0c000e010050b04145900416406401a42d0344510344042d080c480405c1002000096000c0d0740c43d440c482c03403260b2001696000b21380658034690001403901440088499600d006004a2403c1c420701004921410059a10510151601001259a8000303031807a0040f9000980070913800d00400521101031300c9080c00400001c00180069490302c503c40d1306c1508d01c01103040401101c02c55451840b00300104e41c0342d407c40700a00404010b1441c1d0a242d8a80c0180310019600e001c0c00715a620742d8030a0550032020b901010409019009030808050b602c0d540600d000310b51a02040c00340761850302c01400608555080c1d42420302c0c000c09030b440c006085003490b07040300381500310030320040c0e051181c0001500c0d8002c1c2d1140794204141c44000000307160807098409401036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 535789010 1250 535787760 535787809
    0x90f0402180d0b09070e0705070b0403090b0c0309090c12061009080d050403051509120705070317130803071104020708091e0a06020106080607050708040b0f0711030102030f060f 78
    0x100601c840125204000c400b007917500c801e0f102d500d10031280e2800d0b5a80350009100740001000b19001c10066500140309041c17040e4615900e00c4410788a030080c0212050396000420100005c0c18885002507100700f4554000346013000b00d02c0d000750f030200060407040c01520300e1617503031103c0743c002c0c0004e90181800034100e520b92150300300300408503402800308580c0307070140c07070b126814480f41c054000380142000406455440b0f14103c4546a50704440070565507441042000070124480c5c2c4510f444059013801000c0d41c8950b6406d10240458003540027035495402000080c01143c4e80041580e4107881c201c4002d40e81d00e11506140f05203024009050368030080780c040e8041d207444452089012140300f03455411442e0b513184e50690880301b081c4902d10700c5802150008030f107184030300c2c010328620307114180150825465984a031610b801000c21004000c000147d000300380881043c82c1b00c20140128020741c91460f0443c040300c108480900305500406045840c04165529020300f04d580f40c00520f8900341 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 535790260 1250 535789010 535789013
    0x601090c2a0201030f0b10030209010224070813030e010f0c1a0a1b020303060f2106091e1c03240e090105040b070c030c0c0e09060c090f0402180d 64
    0x181e68000348080b40030070300c2c01940904041e40790142c0303940030700f0041421000c1c00540310160085d510008229045015940c6100c122040454881d02c11415103100114035140c104005007182d90003070010a945807108240000096201402d070141500030710300521035047c1d4240c160b0344407500a2004002c40401a0100c1030440c41c100294801c27440303072100348460b110160a505a40e0030300f402c1e040042e00100300164007402c10803a030003089130000d455225418454485e2114840c4458800c1d8000c0c0c0050062100c0c2c544108103400e64008112101c500f1480400b9009507541c024940a80c00c8c02c68459100421500a030b1114401041d814420040d4645030402c0b1441d002560188050440c9184041058551b05101c0e10380b09640c811810a856161080c0076a400d6000351011402c000c0404c03540c00000d000c10400000170980c0c400e81d040c480c10580c1c501410440700400030400c04d501071004c60103d640703100d80704001500550300103036203402c406007401240c0d926020386a001001c070b908600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 535791366 1106 535790260 535790327
    0xa031b0f031104120803010317280c060e0307023a0516060806010e0f0105040b0f04150531050f120a0501021306050c0601090c 56
    0x80c03c00e9500c81001200103a80203045801410220041042040c05426600151140b050060401e217005408061401c01e00e074080090300f01748419003001900508142104c0c0d0382180c0103000d0b01d140c3e0350500d40e0703e40c0041700880c0541109038042c2540745100c0030054050081001e600c03440110f56024803012199518140d585000740301464440328521284440203010f19111041d062405c800003401070b1801c02c01d0780327010380c644241943d91681c2c084d04032070030358501d20782d800d44800302100c11170f0340c2c0c5c0141d030004541040c0c0581c41c48545604803000d88085a0803880340c92280e040802c051441c510300c400c9401c0441c60030380c0709200900c0e201c05010780750180600468074419608103000e00c2d01245d2103050f98039075070019891b8040b44540c00c400002e441e203820001d141104083c4941c0d5551014810a94002e40d541400f440701da120b420403104103e015900d10758010010740305170 = true := by decide +kernel

theorem cover : BRFrame.Cov 535611510 535791366 := by
  have h0 := BRFrame.cov_init 535611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 535611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 535611510 ≤ n) (h2 : n < 535791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
