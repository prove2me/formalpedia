-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1183
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:38:46.223351+00:00
-- url     : https://prove2.me/submissions/4113e71d-85e5-4b61-8178-4e302137746c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 212589928 ≤ n < 212769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 212591178 1250 212589928 212589931
    0x60d05040b07090501111b0607020409050c010201060e010b040e04020409140d0210140c03060307030b070f030b0607150504062d050a020c0604030f03060e010303030504150b030a080313020621 84
    0x1c3c46d2030b41000c001902c1c215601c03000200041c500c8602c2c441c8101280c2c90380020740d54501e0300100f05001005076800c00d02c3c0c4566482504a00550800e10049507004500c0c4100b41295510a0028609894030b40b240d1904000500101e80c041c0d100d82c0010301140100d131041041c50101006043c4440306510040d28080074440c0094166050460514480e00350f10640c9600c085003162080c0e5035900c400009080c850140c1000300303044000c8040c88210b940c00940142002407035101044034401e00c038204201805802d2000300014100c1882e03030480e01c499040503410030302c01d000101750034501000000010b0300019003400650030301104034080c002c41c0e01400750041c4010000b1458000741000d0a900c1c0d5a0040001c0c091100c4144c408080601c00e034041c400405141d5104400b40d610b070f2400501800080d181a2001c8030b1550505418507801d00c075014641c00c0003801491000c113155514030300c94000a200c29680c10700c0e480703201e0141c0c40e11001019000c8502d011420688903910801c070341d6020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 212592428 1250 212591178 212591189
    0xc0201140f070914030d1b0203030f1b070b030118060302040c0507060b0a030218040f0605010f05030f070b3013261e0c1e010e0606060414060d05040b0709 68
    0x40c0340c0c901c07074075505e01182d141003044903441e2150014060b0602100910031900000303400d8072000a0500c01b5143c520701030645141c2c500460892861001c420b81d90702c40003801205951001000100040071046901003030b0a44501c40110310651b40c0e0300018115000e0142c41800f01d03100050307000400415105601c103402007103e40410300c900f181c001c550200280d4482194500ca1000400c05100c0705d500700003d20b5a221100340091f41c1c44418034407101280b842241d0292041d0240c0120b00d48005c540101a80d01c02c041f081c1c2410340b0301491a46402245810410440d260752951a0071880f600696104100380c01345a2901b07051441e00c0340100c11030424054400304030070407042540316484129290380f00ca149810020050068461172948180030130344020b4442d1402400304e201c55000c00341e900c0214940200000a00001103d4903044200d500c20b82c003501c2000300340021450303c0c03a040c051400180c107641c14040d03400e030240c080740c40c00d680a8401c61004c40811060541c032800002c05400c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 212593678 1250 212592428 212592449
    0x100606260405030a080c070507120b1311040b04020705100225050316060f1e0c03060506030103170906040f0311010302070308060d05121c0507030903120c0201140f0709 74
    0x75003a11069101d001d10740c101c00c00c10040340b02141e03022102c18250f80c0c040d40c00c84161001d0699440881050000020003220321412000020711140341c1031466007d0142c0188a284100700e08000300030080600c00d00d541e0b4419401d214580c0841c00401c00e00050b40d840040c0141d59010000c1e02c032868203031400d01c980ea500d102ea05130300d000480100c2131721404c0980c2c0c40d51784225111858110003410401c0e4219250b145400d007606071306800003201002c4840360080c10001803120340b0b42241034030024080c0d160031104c100010030000741c03010303200100042000c00e014100350102e0300003112a0700039403004c852042042c07824404d008080c082d11fa0f0740402420118504005a600a0812000188058400d03803481c00c0540500ca070a1100d0040030003210003890350744142800100b4100c0740740c0200c0f00a189020300080030750380241b0510000c603130140c0310504c107800b512000c030000e000710005290855498440d01c020001d444403580c4c0c000c00f603420b008149480c003000000c080c0f021aa200314180c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 212594928 1250 212593678 212593681
    0x131a04050109060507030909090807020f1c0f0f0b090a0c0e13020603060d02060406031515080c0f04091119031401170a02060304050d08090a05060c0c10060626 70
    0x10782c0c2003101001107544a092480d03c0e840c03542001e440100840d48042c05460400c80b10100300460100240810340c030031210550400c000209010800107681c140e408580304600004010131624a00c1d000790602c40c0e000c1d1000032480369070b4031100c103009542440351a4092100c80301000700712450803001e000c4c2c0381d40108880c600052410701d2075441e1040a40035440010214001d502d5608160050035005003503035540303541d48d010040042c07508000d1854188440d0701d01103040903203170700d86010020070382d5240c010305d071a95a00c03c41c0d642c0c890010800512002c000000e12640c0c540610402c0e41c00c1c040300c1170307101c1900c0c50b4020505c1c1045414001003628100000100b8408c013600103056840120081c40203403802c6171414603000c030b14413004c0e6105a02000f003000300301000030986800b104682e0398403004d4a4003900c0c1942da8080c06001003103038021200040710080404041c3c03810b83c101204035041c08814000a10803a603050b0000c40024100c800d00e14030310486002100350040c8504010702c042e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 212596178 1250 212594928 212594939
    0x3020c0d05030405010e070e010f08010b0d0204110712020a150c020a1209120b0114031c050310031e0320120f1b1506012d05040b131a04 60
    0x85600364800641805000302c04034040c041c00354010700c03002e544401100c0c40c0c983c49283c01c0d14000001d20400c5407107e1652000301d102c3d4010301a0442c00c030800b40c0412444035241e400c000160058a00400203d0303003e20120001c10b08540074000d4190305070300603120f81134050520743c0d049207041c91000045820492000a034a5002030005044c1d40c00409a46450042007030031186c00e42c1136407003802c0c21001c550001d4103018148840a040b00e48541c01902070f09c108200303054903020f41044418021882841c4041341034040e03801951311440c20902030340c58503126540c000000d0300351040300100c160704602c0e003410940c1100036684d00801c61a244006000342103c401e84d00c0d200b010701218241000b14095205228600a954246c070791460648064012040707415900d910601882e03070300926440201354107500074014801e00604405541241007001c180d078500c00c5400c06110010030008200000f140960000035040b13158884800b031842600d00020322041189410302013041d0344003000100030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 212597428 1250 212596178 212596183
    0x90c0c0c090c04080f030c0c01020705090109050a020409111201091503151103010b0a02150c070803040c0803030a09060e0c0105040315291c0503041703210f0703020c 73
    0x1068011500035425540e401c421403100d000b264403042c15403140307542c017000741c40010014200b0300ea84d007400c58411550000c0126600e1150703100d84c0e900054110014441260240c105961291401e200945000e0351064141d00321000c40a4800d12400040b640e00b000790204040c0d94014902c4080c01c0c84507000c00040b030901a80c0c10300c0002c00181c1e2130780b00e118501020350041c0c008420640782c02130312981c2d03580d84242a6172220301c8000050254001410354500192501e50040e2092070324a41042e803103079034101040e40050302c2903640a5200d000014201410402148240300103840894201c1d05490441c0c16184e40b0318404000d41c00c813080c41e07500d99902401b03440441ea0411816501810300d8090400140b000b039010320003141607040c0013001583c058484400040c0242c4000c101c0f00c58282102c0700c0385e4100280189580c01c04c00c000c005009a060001002407a00800d803440d02460503903624051420780460028600c4001c2000010110f0114055200c0410300f010b61600303194142c0700380c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 212598678 1250 212597428 212597443
    0x120b0604050f03011503080408060f070c0204020f270f06071101030203070c080703051e130b090f040e010906050f100603091a070201050f06010c030203030105040216080f09090c0c 79
    0x103000d890501c0122181c1e90f403d4012400190621500f40b02054903400c1c1444030740d000b4020b001013846088041002d84d503206146601c10942e660310384002540710340c20000a94440c4500b81d5a03510280040c2c00941c00c0945000b480c0c94103410801007100e258030500400b90803020095103d50b4050200402086211121076400380342441e0060703681e5608038045d20160300940c0060032819000c40d5140415400c00300070840f101d604002d42d200d54605450080300c034441d1094034401919041c600f040f4500c0c2001c040c0800031001041c40b5011403000c4042011103291036203400c00c5a441c0c001000c203002c0c0900c9601e401c09404d00e10311002d854400710114100307040e8850003082656130a03851081c040038000e401c0d400d100b04100c0b0000d504007098002c0c041c1c402621a020309102a9002c60150340c000c05030f1049090f455005075045a06e0482000001d4208a21a00d4a80401199600000c800600401c841c2100c0b09030140c03a001c9410a0141c3c48400a182c01040030301000040c00169000461706e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 212599928 1250 212598678 212598689
    0x60f0603030e1201141f050d0305070f05070801020f0d0e0601050a1809060f05040b060f01120e120708030103120e0612070314010f1d1612090203060412120b0604 71
    0x501d403c9441440500418018402c2d82038040c00c50b05200c2c02a2030711078401d10050500e4011940c85455404200b404110031000502140f02081581c1c00190504018486c440c00344050b00c0b0055902d4200b9826a07111900d05284640c1c002000d076080e02c0140300d80d000d40d4900302d004000d20341c10b02002c940685030a02401112100700342c03e07110541003940040d84000e81c0000140604095140c07050064401594206d07040200b500014185050031107604046c500145e40741a140e07030011034020001e11050100703410a00400401d044000764480c028035031188a40c240c81d50320b42c954101034000448030220801040050550441c0f150b0301c3d282030341c1038a0f881c0020f10300702d07071603161b000d40040c40c9207800403013012002400043c0940d5410401d03800c40c0c1c40110300644401030b0a182400040080f1040d003030804a41c2442681244076101c580001e20071005d000a018105400080c40c200040324112814140c16125030180c42d400381d0380c00d00344a540541881406110000200d045c051130181d07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 212601178 1250 212599928 212599939
    0x6051005010905010c0602090a061d100e0f030a050d09080d09030c1403010b090108010f0b090903040603050c0c06010e01150c0b06010f030908041202040b09090c0d06020421060f0603030e 82
    0x5c2d44207010084d03045894400340109081001603465401420301914242000381e00301c03040c500c0744441d04142c1c281021503c0d03641d640c5007810841c48100400b101001c4811a054421402c01c0000030340c2c2008003540400081d101d018170300e0f1410600900d0f00c01801103110400c02101d130100001001106414207031a5242da8018100c10600003003401407541c0300c552070388482200c00025900c0d0b4107520603107450007181c80c18009040000b0500100714800d40c0c41c010140e10421081058502c00d50041e0f40040d900c004840c504106900100e162a0782030b007080b0021741440b001007089075a1551003400c40003080c00c0100c44058261100b1603105002071070030703060006510f81100a60300c264000304070540e211038038a445945075400e1201c1c42401c514202d000714542140010b003803421110080c4503054080042040e42d40d00424000d211494000807034a260f0288004203c119101c240b14101804601d400f0791207410601301802610707007802015041c035145c90400d1000c80d40c407003660b4440c1401030741c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 212602428 1250 212601178 212601197
    0x5030f0312220c0603050108010216020603090f1b041a1f0e0a0905040209011205060c0a0201110706090b0f070909050c040305010908030f0a020a09091817070605100501090501 77
    0x1400751200b400e4030350044202c10011400020803407125060020390381e443d41c0c10032a580e21200e4080c01c138800c2c004034600e000c110000010040c070340040190341c884200020384060b10524580c0d9443d1030801d144600d5411400400e08072641030600c00c2a561540c0038148400f80c045040110380c1c0001e120221031610440b0b26a8a0541c078028800e9241540028214030481561400003500a05056504034410320034180001090b01511586c100f00f107800802402d4a5240c214582d00540e1220a0440c19035403246207000306120108094820280a544049105070103441d03c0d0503001070080003101c00c4000001070001d09927020007210103854078040c000a943e103800c803031003d10340659030000f0300542c201200c9800708081070020b9030040c80c10501405080d100c2006000983c06120460310024500c1501000030310b030f45070040c00040411000f020074808a0f40c071000d091152241529000300c4000940300f08019983c8100356101c1e6181d80802100c5080c4000284008010302c10035040010462 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 212603678 1250 212602428 212602441
    0x106081504140916090506010e060c07030f0b0103060e011e0902120709021317030f0a05191d040203010f03030810090203070806100819021b0a0f02090105030f0312 72
    0x24044014102c82c0c6204480e107140c0061002e40c2c4410b0405091051000000001142d8005000e001d01650058451000480c800310a1100301d0304104102849442000000004203811030010158a03026030382d01e926541c150708014040c1c85440f002c84425070300d003104000810503070000349000c912504070003040c1c42403140000381e603c00070b2081007075990040790000030740341070940c0c02071564100680c4c00040482d9901c40601001c1507080005c822030700100680e90a4021030002024000f0840c01d080b42032420134506807104c01c4169440c240842d2101c4030701c1d0030309001181c00c2840e00c002105e05610f591706010000d44125003134400101403214500c08220801100c18030f110190554000031500c0e440d1042d40100206010740c0c90f10700800e680100038039400d20441690b4401d050725651403200c640c890f11008001c1d0321159071505c902183d6041603045030000d0090700d1903a400f68a41d50141131241c010400054010307440a480f9500c005048a2040c1020043d1a024061010030b01125500c09 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 212604928 1250 212603678 212603681
    0x140619140a050909030702030609030a02100b2b1e02060405040e013207030603050c01110c0d0c09060e1b03040501020d050702030d0606030e0a080c0a0206120f0c030106081504 77
    0x3904220f50040780c2400300310961000001500450303000b00c1c100c48030741e00c4080d0000d49a2007040003810040e080b030250301c11442d105811004240300e0140c240c004001480704030810150f005018490300460f0000c40e5403e1040003c8800c9901000641c0c0348000c003110f500041e120312491103103d005a0b11a01c4030f5580d0702d82035104a1340803014050442c401681d40f180000808030520700c01c8034401c103030008034042130b01c24407440c815641c0c85801401e038038400d14010750742c40401580301300391427140041c1c1410030744540d030318a0030035403194020340052400c05080c0d106450103a000405810034400401c240190340045140a551f0381041003683c03134590b428241c0c00392090b81e0902217114241410311525560000050890100f084010054aa200c0100718162003071851180040d81c0a8030601000c1405500200100718581e000c54514000796030106800c0d40141c2c09140321a600f00d41045020111901c84a0344800e4003094549598181319020385400d01c05013040b40c144001c000e891010391907a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 212606178 1250 212604928 212604949
    0x10b04060f03150b0907110703050d0210050c0702090402011d09181507140a09081b10090501020a03050904020c060c1c2304031206030614061914 64
    0x5001030003015114081e1070403100e207a10080315031402e03180341d0030300c848181e100700c40201e0300080c4005510703103a60000f01c4220842c01c41c45441070148030800000204100144222090b8940140c40841c4400710603604440000707020000c00201040100010b82e1070002d9140d01c00d50909112840c8202061040d5840c803000056a4200a510051188408406404541d20442003049031002091100860000320068840101244100d15500707205400440a40510380c00c1d4a8071581c410760b2413601618100070402401c1c0c3d01c41c0e143e910010303141030000051800001e0b60034050191442c203030000b0364074a4005400313010401e0200b04c0c40c1c40d0369920340480f0300319000070080790142c1c00c04c10844406a030140a101644144880300b41c007a045190090310b0036029100c010b0400c205402000c10075048005004400300000f07502c511045d490b5902c0703400040c60080c00c0000c0d0182c06032480250150020341854420502c0510240901c2c1d0007044000a840c5104080b0000141d10408680714555 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 212607428 1250 212606178 212606201
    0x21206361608061f12140f180604020616020306040609031107030804050108040c05090403020706030b0a08060604020901090302090f1e090c01030b0a08070b070c0603022104020d080a0302030f01080c1c0501 90
    0xc1c003c00000281c046c00d21680110484480320314543c6600416028001c58000d058032603402aa00090140c6411409003501507440480f441e01d034003455001a05000085404840e416030f5420460b040c181c1c4080e003410070800020091504e1821515281207a0280748034290401c448a000181000352038488200141400b074504070880c205403a020f92540003d024150019250030024a210318142140500300c80300340c800b81615488580038800a507121044450510101400000060f16203c13a000d00c1001d40d028507450340d0510b40048440c4000d401d02e1000c0301945541803060702c01e4080f5031841c2c4405d007400c0000e0030745501e4003c540180303000c1c2d0086485005401002403208414001030410728440e0107a20b8070360f62a00030035800c900541b0380410b00b411000e0f6003050001d840d0300c0910b40281c0000d001000c0c1e00a036940308503540e402000d00c40e00081c3c020060040d01d100780c40c4914054036441010b00300f551000800b103507025501416918450045030301110a0120070b6100e000d181d503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 212608678 1250 212607428 212607431
    0x1c0c1e0807060b010e0415032d0b15090103020a0618031b0315060b0a1202040801050c0a022e020a0905040204030f0213021206361608061f12 62
    0x259040050050403540f000c24040343d0015403e00d010b240c90710400c4002524440060106800c544a103007004142400c088a281060508411185c60b140b040101851103505881c4542c6080c02950301e04400d107030201c5018503031600040c401a034499041c94181c0d0b0003886c04100a10301880d02000c0c0301d40503031003c3e0104400341140401c05840035400c6c01681c0c041c400d0003100f280c40d0900902260324074450840c42c1d030410710091304114480e032a58140405036420141c245621070340e140f0708503a026942d519010b40c0c001040490030340c042c4866003983c820607100c40100c201c14800c2000b80c1606005501e581035001a00302d2500d401108042c01504020307100315104c50710b910704201405000e80c400e80c031610400301582e0b4801414003c0703030001181c201c2014041d4039507009109080301030002d0f143d1641042d1004211200401550305009440883c400303c69042c064080c080c1c032002080e42a0410400c03c00f00802d944403012280140f03043c01a055003d08403003002190490301c140c0b21111744070f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 212609928 1250 212608678 212608687
    0x17150405100e070521060c0f0c1204180b0901030b06120609060103020a0e090a0210030207051501050901050303090619110609030c0601060801151101021b0f1c0c1e08 73
    0xc00b000030b9a04140c5a040d50460300150030300c3c0340103032000007821138481c9a500c45000500c5651584000c0c00c1c820b0040c3c0055400d100c90100e459081c003070090300078040c0c40c40c00304003040320206d580040302c80f240c2e1000007080030315110300c045020380c5414040908840901c1d004901e294031503100c0c40300d010002c002500d900e402c1010030fa0380c139440c0c01c0c401030388a90f0802c0c4c00450080c1d9580321590059244d0402419046402d900740300e41401c6525080e41030580c2401000003180c81401203950400070302c6c00c940f42a6040008100030b0040c1030300000d0183d030080c440341e00184c0300d034005c9812032100d0410400c09611040c80481c2c12031600120181503002d80024005d040d440080a01403140003141030f900e6a0b178840ca01141c11442c240b05000d00c1e084040e03a045001801283c481611003c103200151601600303501e00b075411000c0c070030060110345c041d0700c55550541b000d128011016545a81041810a181c01d0080a0041500340505100c0f8075a5280383c5500c28403070705071000d139440116140c89 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 212611178 1250 212609928 212609951
    0x50d1d100201021b0706091e03140607110105060f040b0a0b0a1214040b0604021b010606020f01060906060c0b0709090f05010608060118090c0c020a0f030c1715040510 73
    0x2c3e400440c000f90310340000801104d507503c0003161031400d40c0c0041da01d0740c041910f00b1244a8440e0300201d900d00320b45010f102d010012440d03102d05100b0b1850100014501400e120310020701005030000090380b940d00d04404d20106990b000d1003008076090485d000302d40c00700c0308400641e120000b54010351a19100040c000e41041e0400c2c8505001e0307170398a104015110000c80f180030304010817140207121001100008500d4a4075502409031813004c501c0942c441131400d500142144c00d45d401c41e0700541d0014540d80304c1d52800340a148003078021960144001e520342140541001d640e0f0100401440c803000004103103900c259000380090400308000d0025890042050380104400e00806c0300145001c8001012940030301c1c16011000603121a2542140ca042c0620300100000e00c418020401503a15802c0540d44002e0040082d040c0c4042107000649580303090365100300154030200500602c600b0300400110045a000e0300440161130465460343d42e032501c3c0b401c0c41907801447c04441e2908981c0c214 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 212612428 1250 212611178 212611181
    0x150127140f06010909020306010f0309081605060a0c11060109180b0c0403021011060c030a1e0e0706090f0b0a090306050f06030c030a08070215070218061903050d1d100201 75
    0x2d49401e032103054042e034445144c401a0b00c0220f4040d40450b20810100100034407950264402c28000e90481d410301180000365030f0402111001940c1550210061000c000c940344100f03c45054035087c0001c0500740290003503192401449400c03051036440910004849030b001c007001889611010300102d504d01060800410b401038001070380240c0c00707400700e60310a90240f840d0050601c078030f1009082d617580e0b910544901d40c2c0028502e0321080c1d194030780701500b1844080300101055013101e01241151211152500d041032030750100080080c622400c00c025954440800305480c202544030340d0f1068041015039040c82280d2000306031f0303890082004034800d107100c800e9005170411026210080b40207030416a40e13a091002c0a00807203801c2000100514144c40c0d502d100940081600f420180c03603800280004841c24031912424219104000c510714056981d0811000410041e8160310300351b031141a521200415600c0900c50028107120780b40341c0309041e0751010703940203181c2d8428175100c0ca0003d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 212613678 1250 212612428 212612431
    0x100e27010e070e01080601053403030504050d030b0604061101140406021902030406051204051c0804060605090f010603020a0216121703010305120f1201060908150127140f 75
    0x40042c0308001e100100b507100710317191030060f0300503945c0c1030500d50400030000f18040302d00c003000d040340000a0211000c80b101c43e01d880800d4002c1e20f00142a15050030000d0500d2402180041018500a0076601c0da03130322002600c0c19a00c42d494030b8007940740385c1c4050b1801846690304244010800c54200401c02c4150303001415840e82c0101c400301d039410502c5044c0c0e540d010701d00800e00030034803d00c05001e10840c070503d403135840b034041e108039241d1315a1600c42c0c1851039020642c120000d094501040f0510400740070303000040c00c040d01c2c0c0c0104d500c1c040382c1c0d481c0260010b006000c2015000a807441c00140f003040000c4000e440a00c0b5040702e6540d9400880080f882403008491107011030b801c250300c101280082d06c1c12a608107015100c7c80311400040401c0c0d51045121580d8480c0078881c58003800d440c803081da40078240b2600e85244286c10030000a2900c80d50514184020741c0b140d0040c8403020052148e012070804916081525008112040300601200814a039011056004210f1203800c080e5005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 212614928 1250 212613678 212613691
    0xc0302030d0e0102030a0c0c05060a0e0907050903031204020102210c0f0f0304030605100b0403113f0307170d0501060207060c080310050d051b100e27010e 68
    0x441d0700d40700120040e240145010059405a0414400e80c00d01c940203100400034030740b15005410040e81c440002480940003c0c400800185270070300c01000c03904000300f44942102030790510b03508100743d000c00a13540b84144042400140d4155000c101164000c001c003694401c0f50108402e8900804828a28141c04c626180d031401c1c030503106d202482d41e1020a810000b80701d4040a10724003030640e25400b000d020050300d40054903012640000d4030000110140000d107104140f80181803401208100c03c015000f188500d6244030101008641544a081c541d4103000d2064120040e0720501051030840c001d9040240c00d41c60701300041030992800c0c000401480140407010001c070390f01c95504a0ba202058002c0c8404904003a0354100441c842c84051540b0aa96000c00c4505c2038a13640800c070f411403490002c59030b0340d00001001c140341c01c001200c618218401d44003c00703030100d0440d00400a441d14803040c0d000d413500801d00c166140d0f240c20f20040380541e801c3c0221907941d591015110f40e50085406 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 212616178 1250 212614928 212614933
    0x20f031503061810050c190f02062202040b01030b040e0f060708010b0a080c070c0305010902030607110307020105090402071e1b060815040608240609040c06050a0306080a0c030203 79
    0x1000c00110300c40f68000001c40900800e01600d080e03401a00400d40540005000b80c3c0511041c0c1034043d4403144450000c40d50b9030b4240c09403070141c0c806481c11002406c02c8204000b85054103007178500400300b03840d085404903400300b01c510501006070300412040d0b10658100307043c96081268050700044043c42e240b4400c00f1100144d44100046441d02828000d10081020810104141c00c1c41502041d4012000410181ca050450366031104015840d90007240d10342d441e000c0c0c1b0429460103001d140c1e405012401d06d03090b1075107038100540e20f0f03104042c0000d05202d40450982c2d4640c90760b40c10b8070501076100c2c4065580307154052a60360451400501150000410800c141c18418190400000c89100f42c840f03801c151281d81c00300501c00c0c11303032600640003560303000c00082d082001c01c41031124100040452203012014403075400850001094180200d084d50107000c005004600417a01720788407031a01680300c07048840202d0190102c0d80c04800b20f442807182c00c0c0244102e261510040324801c404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 212617428 1250 212616178 212616181
    0xe060901030f1503021302030103020d02011d031c1b0321020409090807150b060301060f0203091306180b0603010306020306061c1b03090309030b07030e030d0c03060f080a06020d020f03150306 84
    0x34a047e4402404004d420143d44110180103500920320302240405c02c800b0311032601000008203113441e080f4050301d07407400861840c02c800103401601520740c500100110600054242d140a0b144d00046402c0c404d010700d042c002d0700b11180c0c2c0303a0b054501900c07044400740940040d44c2000c003d90b8100080644805c5030b01c80e1603410842c00d9204100480901501c80cad425603107001020740340f40200c1a4240b00b54082000218800da0321580603005507a140c0400080039030420380030154042121900750152841c0c030041072110f690b1074050b00e0450b03078003a6015030b41e0359442c804590305005200d501c2c43c101c100c2400041c40d160958222100f020b40d4600701d15200001a41c04606981e5a108054042075401d502803001c00c01c40d18a0036030115032400c01217244038001d090185181c0c0101521201e041d91086220303007181e03040c05200000e215840380030020f1420000069101e04000400801c03050340054501e4035074605d50103030b5030300e00c1d450310b140e40d22864100c1030740c680c4003c203003602c1c3e100e40900390 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 212618678 1250 212617428 212617459
    0xc092603070f1118150402160b04061d1c05070c0801050601031a0d0209060f0618150408030d05060118030b04170309100e0106050307030f050d02010203070e060901030f150302 77
    0x80c108101c09003a02c1c1c0220941c0301c00071240c10354405c2142c907a0304550200620740780130300c08403041d140035403268200540600d402d0070800d0441d2080400d91802c0e1041300038600e40103500003504e015003111044811603060055105a8851241d0702000305a86140200003030851019800350b4400c40b82a20241301c00d15816038641407030340d40324a00c55400020392a12034054144200300300c0d071141006d40304c6000741450100003402a00070b08040007031022808034622280c02c101c000820f880e8454018142810300701021aa1203008810001040540c0d403000a41c440c0e101d40f100e40d40a070b10300c40220500030349a05060f9004241114240d508002242d0b29145080da0b00d01180d00c90248980038080012500c1015009054122403641d119074881c0340c00324035030b9000e0119030015445030025840018542c9040340c14445104403003810f41e48103004000c11903401001c4400c0c100e0048442d5a034480c02075005800a0084181030500c0314905031000c1580c00041d0b107400c096900031200000070400c101c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 212619928 1250 212618678 212618689
    0x619030f1b0503160827071a040603060e041112101103010e060f0f010e0409080406030b13090c030f08120702010606111f020903031e19030c092603070f11 68
    0x40d551303100c01d40c1c8001c100544440188080385c44c051404025220f9a81e034400d101d072030b202c40040400d148c0b9180090104805078040c40f41000904004203100102c0c0307040c0c4c075865240b0380c0c80c207800c0d40600d854054100007410248055140e69983c242d04001c010030000b6500300d00e41090154080da007004001040c0ea91034000395108050000511ba02088a80100110703044043d10041d10b80142c0c40c3c1c416100083d00c4640904043c02d42c0760303400521540304008000720811004180140b86103011058004101401946005c0d241c004000d00c5645080d450403403028882d00d90020320b1007000e402480400703541900110b00300e440541d19600c00140e00c05005032a0780d41066500d1103000707078440000350b80806801518a9030401004da074100724103422102420103581601900c144d5001070740c1080b90f18980403955a0111518007000711118a04001e46030410900a103c6540e102a5600440d291600d5550750411518010b40c0c0c0c40d59450325140d45074a03070b50b2070121204010031600c1400c030b00340b1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 212621178 1250 212619928 212619931
    0x70503030105040b1815130e0309040b3a02041d0609070b16050c0d0303060e010e04050d030504080d06060504030209010b0c06070f030207081204050105060619030f1b05031608 77
    0xa404a5500c02c0c2c40722180643e403d0b08507103002da004030200442c40358400c694803032048c1c0d203490320b000f55a84031303000d00410045480d148649440360f1095200c050090241c10b103200c21030404070200e5510890030240e072070855020004029840350421214102140c2640400725560030300d0002c40b016911810880c0c4d0300d640280c001e2080b10070007484455028001c2c281d07000314403405407041d0344401d0804008110101c81081c0c081d40843c0e100c001c10000040c110090b5801006146080025410190349040d181d03188006a80b00309616040450140300c021400c40300810061002003003201d942c0e0501810303d8000d48030607440381c5494000068a089100119040d002480014002a0340d89c2141603d030b46103000081d404040d42170028074001780c1c02c58001c100c07075031104180302054039081c03421a0a517040200a58090041440040f040f0810b00c5240000c440590402103203030703114136a008005101445888008100080c48c01e8501904440254001c0d401c200343d907281000c0300d00098800c0f510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 212622428 1250 212621178 212621209
    0x30309010509190b0f041809030c02040b120102031305010f02040510050c0a06050a0e010e0706052b0504080a170708060907120c0306080f01060321020a050102070503030105040b 78
    0x40002c000a481c0c810400c3c6103059102d8020740141ea03d4055903500f40d040030540b240807101c001418000c080c40d1341500340c2604569a401e00500207503560040114990a10080c0a2a00e07031011021641e940041c640a080d80b81d0000c40d183c1c40d144403904045c803a4040d059a140d442e00d04a4032150035140225406c2d140090003295802c004400100d41990040303605881501860347d9040000da294024036000e03061110000c07811f40201070000e801c46844e2810149150b1000e50200010b40d081010f403000b140b900c0584444854072200f500c00d8120351511014a140e15100400040040041c0500300700b0010350b8581009a11054030800d80c010b05541c02e001251245002070103518060400039400880c07490280c2e20302081d1148041030790703000840b86012903240c1500f4090984200041c0d03100ad8090f40003030081c4ea01e940c440300400010b48444641c4072a0761185136002c03500030030142e01d13040d900c0f0000315503444d09402c100d901c0e9002800713400e00c50750400060307503a140b42c03c1005040c0042e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 212623678 1250 212622428 212622437
    0x91207140909190212010203100e011211010e040e010612030e030610090b010e0d050a0b15011b08040b07080301030501060608070806040506120a0609060f05040f060906110301030503130503030901 86
    0x1002e00700d0f0f401d05150001ca900000007803010441100078000741d801040c860507628007450829225002c2040141c12400400d601d030100000407850520746403021840a0070a465015014004540905454103140b030f41c96090050024034001d400045401c414002e0342d405140154020805848002c1035588480c5000340c0502442800310b9a132044030003203014142000943d41180c041444505400e600b5110354000358600c0301800881c66826621100c14804004080312a20020f080742c1400c19414910960b00a802400c0103480821140035081001b1040e448982e146011402e4ac2d009007c00ca84175424a200090b6032030040c42050700130103941d02c44036903035500c1c402840000c00c8003d00c6107a00c0b440f80814400740d80018030045000d6405074801150003182801e01d101a41c000e10b40f282800c5141c9002c10012030f40c1000c440c0e11241e4842000b003821001d5041c038501034002070800c01c000150000c0000104100040203284411300005103111540c0e0300c0c01010388900903c280701d40841e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 212624928 1250 212623678 212623693
    0x718060518190228020d02031e0702121204030606090209010509240309151302030706080406060e1006020c09012102010306170a1407060f0f05091207140909 69
    0x41803515900041e8034010301c2d0050078001400301c5064000c9080d4891045402c01c841c1c4c0d561007603030611a403200200940010b42c40c100d80d0900d08004c0544031007034400400c0e40410600110f5451544002c03800021804403903d43d074080780d000501e54000d01c41100c03800d01d054000100d10405d8002c0da03510f850140c41e118105520301c010711000500c1d29a52074480740c0c096440f81d003c00042800365001d41340a10041110f5140741510b5090007101030000e1440d445030b4606103006941c0018201c082c0e0784546450100b5498a14028014081c1034008007a034080c00c00422090720300e480d8105003100c0195080703500f00740155003841801202070060456035450101c00803062841c0a00d8152000d10602d40010015078850070700c1c0d8000301040214141d0f03003084609105100ea106c011040d4008002c0c0944881c07440c00f100070701880e1805d0108010710629038656082e076800b59050b07410320740d409003184600824400700c0036140c010a001c1d01d01c10f4200d0c88101ca0090820140141c410150200102000b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 212626178 1250 212624928 212624941
    0x6220204062d1401030e1009060b0a0b0903060109020c07030c0e0712051b0a0207090f09060b2e030e06250905010c0f05070b0d020c0712052d0718060518 67
    0x1030300500006d905144614058003c10b0001d5202d071281c80340c00760030001405802c0d182004400c0c8171039400001c0300d01c0103011191069602117a15811601c420000580d0f07070303c01c0c0034650f00b04a41b551000c0c0c4014491107000a983c150518802d10941d1656078041e41025010702c504100c0788140d07600050810842c8103840c0030090340000344407040890044564107652007071403030155001c5120625516480c0e11803402040098001c2081b0340c0f070b0031100440c0000b1034940c1c802c1000350540c81d48012103100c01a5048070b078003d41c00396038480e18000680d80c203480c00e102a8101e5011400112251341514441046020b00c2290000c0c15210705a452804020054903864155012014240c1d958058a000092424034120051103030003820a005070705c40100700002400c00e03403a5031060b41d070300c2d00084078507000a6001c07076500d91100000d03081016034029621081039562801d08040e44d10b1080100c0400e041c200f0002103c0b0007000300030103001c0240c40701d0a0118001ca0f010140d003004444402103642c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 212627428 1250 212626178 212626181
    0x1803080705040803040f080c03010e0604030521240108090a0f080d0204080a0c0b04050d0209040501090b0901020702041802090f13120504080115030506220204062d140103 75
    0x40048091a0482c245a00c444116066030702c2503211014001c00004204280c1c902401203d070301c500308800810401c0d6003103a00a80302d00d00208020304008000a61022507602d0a0b038264040555080c510560320b03119094444048404004032458803030f84c00e00070130543c442c1111602c070303250b1000500a00a619500c5a524544c0e1290841d11303108140a9401010200d01c040d00081820a000744524011400e000d903803051160018a260382d820481403080342c481caa01322001d20f41c103035949040e81d07640341002401030405100050000c94081c0034081c0f9560150003a0400a0080b541001002c56171022800b4564844d0300007500541c0010004a1005600340d05643c480059004052179264640d07844050003000110a00815008502400822000d21034082207000c0d2844884c64981944c5600340d0740c82d0014201010307501c0800c1c0e18036106217000802c1352119409001401019281c6203a134050340710126008000c0b0103c0e009244803114400b9074641140e0080e8404c0900c1c801c403000460 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 212628678 1250 212627428 212627431
    0x9070f12060f051f0e100510020109050d200a050c040c020f0312190b130e0c0604090f0b090c0306010e01050910030e120f190c08030c04050310180308 66
    0x40703600b9640d90026032440c000f400303420f11802d007011024802d0f1680582d001013000107600b00252014446080140e00540414698191441252001e54100d8125022809030403400d000030950300440152407a8242c001c0100c4c1004407104180720b070313900001c400240d507034000900041c0c07071a40910060095400d0075030107205800e1051050310580b2500304940d51840d408000580441d510b00820800311203581c600300090007008010601000e42541e0000701c500503081070a100c401d954140d56018044200034000c0e001c0d001610f01c43e242c9030354080c55801001c0d481d84d20303506a41849c070380c0115498800e01603880ba42000800d1030079034591030011180200402d520505000341001480700c5075603800d52050031820641d401007098095050300c107050401c03c03140c040c0d0051041c05000c402418102c1661002300c00191000100c00601c9802c40c1c030001d52801c05070849100006200e54540004000d01c20360300d041c0e00f25800d00d5054001441203a0305019095841840301020000181c8501d400a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 212629928 1250 212628678 212628683
    0x303110a0518190b0a031a0d02012109030c060606020c0a09050c04031a0601090812040902130911040f24080a14090d021002071109070c1509030809070f12 68
    0x203c414919640d20b10b40d4106642e0005107801e28003042e109003550389401401705e00202000c0c44590344100c44007045c4d44d10640c0100074184040069114a002402d88090400a07a00e00782030240501d0b900300a042401120f10907140f55007014400b0070103500000c2c12150420024003600e002503d40000c0800500380a81030340b0960300100400008030f061005076811203541e4040350082810b080001400c41c8003240e001c200f081c1c0019060b03075110034400301503c044400302d40300941d40700b41141d090400d080315500004001860001c0f03094130807503914090300c26580c400c140310f46455101c1c90303048142030295036101001c03c4d1103a00d5214143c42003c0c0a0b8100a805501140c0c00f01ca00c2154445440c003191901156480003400019542d81004078090902c00324004616104003611118a000316000303280c0e0140c40441d002c1030186124450052466030083c201180c0c24201c81c00820141c803c106060b00007400c0140420904040403590f1422510310b0030002c040d10b071034503084607002c503c0e5283c00e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 212631178 1250 212629928 212629939
    0x15080703080703110607030f050603060601080c0c1606020105191a3313051518030708060c0a0305011d0a0b19140102060f07080103230d03090303110a0518 68
    0xc04004c04040000ca03000311b0403a10045460400e114103241250348c028040752080d40114148256070b41c000d001035400c40c3d000d0030411350752080c860803a441c14840030150000150b010b0700005015506600c05070140021b00040010301d04a203551030b040d10040c440c00e042c401d400c01500305151402d41d080034400c01105a602c0341c800c40825a08004443c40cdc2541101c42074000388000310345000b4aa03d101904003103c9510a50102080c405264006d00e000c10003c09c503111841c2070f1b140e0701000845d004103140c00031901249801618900941c00414024004c80d041c00004540181c108131100507590412010030001e03a51503105a02418001c54526005098080c01070785810451841d80050034174808608549448200020300e081c0000b0f004451014140092100c542c1d0300044950440780c02110414010400b40e090703080051343c07880c00211a205414240e002c0c560503400c00b51099000362003c0001d85690900015548103d2101070b0014004101d0301c01007540c0302025a1020304098070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 212632428 1250 212631178 212631197
    0x4030801260f0a0303050106090b04050402030703090803070509010e0105032518060905030613200328030e030105070504061404030c0605030103061104060c110d2415080703080703 79
    0x30603420601c800c0b0400c80d598000800010500d90140a024010090751400002080c5400c180c06964004c1e0b0091520a940000c08a92600e100b03030072072140d142d0031800f0140d690900842c00750040c0d0044950302e020503c0c801800c04258080c40580b44107201400041d41c41101017840048003580c800f280806010311070700c510300c1550588140300054542174a48046a500301b0702010700d0080000d1410010502d0380b8001c00c00101c80012299201d00b000703c6c8540b000602000281c1409400380100410841003940014448900c0103180f00b1b19000e9140c2540200c041003d1500340c4100315001d00114104002c200050780c03245071001200d080f16150a4105500d0b560384940a4000d80c0c84003000400100052040c00400d2040d442c0c1c40d09a5110716203060f1925030050806001d03045c0241c0140305540c20190262180059941042c1c1d100d4a42407030050054408442040c440c200071300344910b001c1e11080c60204805410060300d09041c010075030145181e40d043d00d2580700720402c4042100600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 212633678 1250 212632428 212632499
    0xc09110315120f07060201050a02071e08040302130203010e090c0306071407020d0605011503090308160c050105042102011401051c0b0106030b0f010c0209010306050c07020a0b0a030c020604030801 86
    0x4800100555501a01004c2d02c0c00703c0007800d640d07003c0e0180b46e00c988104140800107200030041840421142c0b80ca80a20409040080e030900460388003a4005003804e10002087d103141d401581610035541c503a00d007a8031403c06456076901c1900343d0070f80540c800400306250f24003603400c850285400c448041d1030700880d039004c100b0884900300e003101c045d03403a80b005000a699109194584210a05d4208041e00460314000d0030ba00001d80551148401090700881179442460350701d0440741c11000078000c50516251101c00401d0b0445801614000f0900e1802110700c1802200d8503041c402a05038016420b00c001c00c48952541e441040b80542c3d068250400100100e074400c1c02842144c41c0010310100b81400d0000360b13410390001504101c8013038081070060360b940c040c3c6410f40ba04a10001240c0da10800c03881101e20a0304400703540f0030440c080005a0184090080c442155103641c20311800407000001c0c2c0e62094140c400a010680300401400302080000041c0c001070501c001d4801c1203238802 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 212634928 1250 212633678 212633683
    0x90c0206070806130b0402071b060219201903020a1a0d05061903051513080d05090c040212060f03010204050109030b040510060b0a0306350c040501120c0911031512 72
    0x1020880d88441410a005070300d00090080f0b01c01488140053304846018001540507100c200e030b40100070301a000a00c00402d60000b1158114000141400d80f03554071100c0c3c050041903562000320300c03818080c500861003000d003152000803040700005190405421030140b90180c040182440d4002008043c3c144815400381c25490055004402070001e01c0160b048610135a01d0082c5500d85203098950900d00140c07400085035203901d952a0001460385928030b03482d08108861030055402400828400085060411954000d24003101d4080d04982c2c950f080c9400c3c0e0249110b00d50105070100000c101052403040b10541c010b1149040c1c45d48024a00c40c1d420449440360858450668003045103410141c0500c82c0b4406010400c0750700301c0024016920002d240304040c001c01780071081c0003000c410f119040000b0342c4040e4000f08280320a6842d42202d102130720b12080150399015501d0400240c2130254858050404819020649950750f02c1c078bd00c140d501c0c07180d80740c43c0d007102145443c02c4015005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 212636178 1250 212634928 212634937
    0x7170111040312020d030203060d110a080d030b010806040e031c020f040603020301151e0c0f0501111905190e3d0e030a02010f140c010204090c0206070806130b0402 72
    0xc0c10b041010540c083d1002840e0050507001d58082c94810010702140f6038500030b04101e42540311048005000c05d003404290f820484d58002da40302d110740b0004144480e01070b04592407020f400c0c1d07180f80789640c40038100000d03504400f45000298104100e45c105010306052030500c1c0c500c01c118054640740d40e51141c90201da000d42c1c80030300000e40c0403005004042244140403804090383ca0481c2080e4148110384a0700d003003600400050140c45179100c810030a10030140640150000000c0011001e1528600181d60102503034100c0c0b50083c00e01d4840c0c8a005201b90b41c43d8841400d00c0112848135020182c9010780c0505030940c0c000515694041d91402d0a0180d011594039100d44601d00160044005800001414480305000610b2407403c140c1e20001041e91010303809290844070480c035007009485602c900c00420315030190004c0c540c00400c005400400c00c03500c44410411000f07800302d1080341c54540c1510340200207003522011a0007460103081403807035289403020001c1c080103403070001001c9920 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 212637428 1250 212636178 212636183
    0x40b0f1509060f0406171e010501030e010e0f0a0c0b0c030f090f0405090d031503021e18010602030310062f010204080a0c0302031b03060f0405011407020a06060b0a02071701110403 79
    0x40b0490b240c0310721b08028015070008121004a80ba801d40ea4412501581d01402401c1c10180d55641443c19000c094001c02492030141b8155640303107020300712594a0341c5c401c440648012060000c00178008402802703c0d401342d0040b401560403c12442100e40031640004151279110540c5500000199a9489210b01652440000b000f403031280060241c155054008441815450b40c401040961a01d1241441c1240400703609081e5a0751800010f0803c6085240184003908800c000b181ca190000000e50040f071a0030944840107944502c22030b0003078991049211a860000c034686203040400442d8110401c804001504168441d448945024403001003600d044105010401c1941001d12541200010f615a06007400e8440e2003c45e55814014208a488001140019042c000700394130440502c140c20181d08603c1c246440c2c025580c69036081d0603241c482c9001d0f000628070604e8012581205499000703807611070302c0d0a400c80340e4401c5112500354555202e100e0f5190040000000744050f51 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 212638678 1250 212637428 212637437
    0xc020703140f060a020901020a030e130203040f03080604060f0b0703020f0d02010b041a010c0813050306011203021b1309170a0302130911090409050118060b040b0f1509060f0406 78
    0x2c014040910b0108003a201d030110314810000d10016982c0031880c4a403454040c18060150007041020031000c041020322500303064401b10600c0300b007111034140c1c410498000c0d0b0310249182c54402c104000c94449114038038a101c5140810010442c2ca20301030072280b030007401511048c0c01e981b002e032410018104038000050b50740c1c0318012a54038041c0705060368140034290000c90034848900180000d404075002615030000810316180034036503000078002416001c0c00390703122540e4405581495a08145044000d80500c400c034801020a0150a4140080003080e2050b108810260b0400903c20710005076044034a0070b0401206411507001005807480d20340e00140d455196000000703841132141c12100c0c2c9039042011440e60401980d081d10104441142c0014040c002c602e01580100041400446090300520b480d00c2071044951010440308025607040c804070841c0700400c101010205011039001c3c0c02d01d07402c21202c25a48004e02a0324901600c03027480e0529403220b90741d01e40c0280d031001d40000c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 212639928 1250 212638678 212638693
    0x2121b0a171b21060a0e033109091514191a0310051614030a0c0c05060103050715050703021b040204170307120809060103060c02070314 60
    0x38100540c4a1008100c000e20a2000c0c45107400c40686640300071481c214a148020080540c80d40c1d404a48200740070031151102c1a8030307100041c0d5480d0501110321034800c601e4038059800011001c011500000401001556040d190724021210004a0b008084080150b0300340400c0c001340c00e104105149024698030529a1280c801003420b48818860b0300480b807190704144264500ea000d5501640c011504012804220705682da082500350294410b03458031406240c1d00b1361541c50f41c030850190701c080d1244090103500003001c2d92041e214030422080c040003040043c0009009034041c1e5601c11407842d1140008640d615100d00e0800cac20b0b007050303030650417611082254152000080c1d0109910b8240b050500440c1d4401039254102c800408086600b0f440c00300301541d445904680283c4510708822503050b50120040390350f40c12a11044030016400e02e600d510550040310a1441030403d100108401d070300b0341d51100d0142c00300f201752109511504030040009107001c1c1070412010304002c02002d46 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 212641178 1250 212639928 212639983
    0x40905060f100e070507032a140607050702040504020a0906170f0a030804032609010e060a0908031b1c09030e120709020c030c0709060806010e19090212 67
    0x41c240301600c00848420004010041841d040070f0a81d40300045052007900d94680741001c0d51032101e80018034960380d4030350740d014412071100d060040e4502c1c000e05040c0b40c030260036a0301e02d6550f0011384c1d252000c50420300c01a070041c40c2ca504055030261001e031001880e0f99a85064006076640e54024410350b82d0b143c21080001c1500300310018051003980010010451562009414141e010f04003034104204844066025043c01108403442d002c07104041d0707a54034103e4080d07802000c8480d00320600c0e008030800700e1122205805404034407a044078100740b464469110305612518208400c0200d603030b0a00c1039627001141400101c88002042c2004183c03030f849d070b1034014810920802c031795200d600380c20440344002900050940903a0010940140c1c0d40c101d94011300c2c6180101c0701130300c0d1580305168000c102408150401030071111b00320b0464203940d80b103098950b13400c4130331104501c6036010f40461070b10304c43c0140c2090103240d00141154128041f0040d069080140c6021007201c420504e00510702d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 212642428 1250 212641178 212641201
    0x40c0201150b04030318030b0c0a0507170408121315111f05060306130b0603070f0f06080121060b010311030a060509010b13030b0c0c03072a03020d020904030e04090506 74
    0x6d40500c0340c00b102640c0c0c1942d45443c071040015241c0c0760001408141004907174098400c490342c0741d4214868511074a24844440c0b05a482406264078038011101c5e406a400300c814103072810f0351468501104101d0034107210b460417000c40800503040004010030390800a5050207e661240c941000000c103032098501c0d0f9006032000506240d000f40d20150402900051368045007402d2030b401500d00e01c10351500b0001038940744081e0420301515018000015030f0845007510801155407988810a241e0381c2d03960310302404028404820b00741094201c01000244842d8000c90000c001410001084000304000040c01d40081314180c01c3e1a41d10003003030006140940c01c0e14010603c0711f0301d0a103052400289100c280c00907201c020f041c000c1c5c0d01c02040d82c10754454103403540300c44d2110899407200168201200c40c107440d0702c1500f141190b4850700309103500d03511500c0419260080c0c2440384800555080c001c5521005005400b000b002041d03480d1103585501600041d640190300800c01828601650803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 212643678 1250 212642428 212642447
    0x30203011401080705091908100f15050102100e01060e04150e030a09050609030a0b040b0a0c050301060537030e010b060c0712050a050a0c08101406040c0201150b040303 74
    0x60503c000341d000c200d207040e4808115000b00000340c2e42c442c130440e10a0501d040140840c0c00001c120301802c0414910001654044000c00800e00c605100e10311610781d40101c1c03075006028117401604480205051002c50350049005144210000940250b0b00e03092211001c6041c0e07800c4441010307060908038400d1060041c0d11032820508051817600d00700d04030107882c0a4032403180078041c030760118a5104540d0103100d18814aa007065809c1d1241ca0706250184003400c1c101c80f20700381103240034082956503104400380c0f81a520075803a068030340b9210480c2c0c81d0100c8a20b048004150348280d8800c907030b074181d4144000d480f82250720b01240c00c04078070210500b541e18911041e80110814400400e18210000b100d602700c0e09601618641200c80f0b040c4035051140c10f450207400c9204461042c8200606c0005040480c0c42c20030540316482814495001912070410410703440d034007188085012132030940d120280c00d1805000000d4580c1c0070b0f04d1706840082203076001c040a40c10100c2c080040c10303040f8041c2d5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 212644928 1250 212643678 212643719
    0x5060c0a0e0409081914041a0408010204030812130308060616050a03050c07090908090d02150c070501120c080103060e030403020a0b030603060603120d1806050a0504050c01020106050d0b060a1503020301 89
    0x9079a296883d0500c1210340034501c248140090f403402c0303814121200c181109c1c0a08011b5000703568458407810081d071a984001418001034248000103501c4a81001c80030070311a0b40b56071414005e44411080000341e81158684401c4c107c0500110400114200508448a4840e882d0705881d80c06119103581400710313035031120000d2410401090001184441120000740b01210f03041d042c0c000340c0c004200958881074030390192010002d45441d504900143e206e084480036a00c0d501d02c5010000c8080a8413410140c503401b0039424001400010b805800032107201020f41c0450742803c1d501d40001350316003422381c012070003100d00001b4070040c0c1c10140b1140c1e07030141055008241d03a03034140d02d9420700e5200b507004940d82071307075180c4142480c44032080c43c000f280b5400c888144000d08108604800804068800702e60714030981104c2820b650060241100710380000780080c14405007a01c4680481c1d00080015501c24946000401c602c8800c4a2800034024250b400507107a605080001c01c055920400c003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 212646178 1250 212644928 212644937
    0x301060303080612010b03191205070818122a0d080304060c090504090b07080703050903040e060d0b090f070f181a03061608010b0705060c0a0e04090819 67
    0x500101c0d8002908a41044080c0c622203031110100c82e64600500d506041ea95050144803680c1100c42d0340000d5a004450040c0c0c43e643c440101c1c80b1050718184281e640042103c0c50034803030146c0442c0030f080b10380a54813014081c070310214094861a41415002c103000c1c00c0000300d00c0d607030804082c01020f03004581e01003034900c84011402d0340c4a140441c000103100034059030700d23030307081900051081c20140018200540148048070701803400011003007044030f0304000a03404000040c809442070107204c0c050310310b41d8042d40c54075041c00300500c00e60000800c07060308507540a0400000600d01c04800307200c1c80c00c0c40050000d14150f9998241005081d0744080d02044403c0d03002c3c000030038204004180b10300c9280e400903200798000202090b241c030003401c15505018010810554031400314010300b000c0541d6450410603a2540b510b29110300904e00060075617400000002c5c02005410000c1580c12248c4c2403121540d414280040e0030381c4c22410301111511004580c1d020708a194000003051a50107092 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 212647428 1250 212646178 212646191
    0x203070f09150f050622120b0f070201050105100309030507150509060f04021008070e1f0306060518010507170c21070b1603090c080705120f03030a020d02191701050301 74
    0x945901a000044440000c00c10182c0d46d05a16801140010a0366099040e4800a14100568070084c100d80c1080003500036000900360f14410300c1100d0503510010402024040442411030040040b00021801d004041040c400418528168003500c41d050705400f140b01d28003024040d080400290980b10100101414000180d45484260000d0995454110030a0b82e680c001182c4444c0b802503210303000401d40c11101d240050520300825030604e1510140071240c0d03107080072680780c8903002211120002c0081c2e1144290b200c2c4008001190203103900c81d105554400a4215603070040c004241075600c42c8000340d0400241121540a455400d8102400c0c03da098882945070107000380710081511481011b40e070140e01a9000f00c4019410005041800b074880d83d400c1e99801442c069070380b00380c8502004941c552000203594003c650010080c50440d00d40d4594140603402c0b00800c80340d02a020b01244001c86140400400c007c0700c10365803486000680004d680e41c0c0a010b07007016002e40d05042 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 212648678 1250 212647428 212647439
    0x70506070c0902030606040321080c0a0507061a03031c05131208180304120b0603012c030d020c0a142805100903051903051506070203070f09150f 64
    0x7840800c82c0c402c864003582e641e85480001e0721328841ca41005111411241c02c01c0554009a4400400000d05455090060700e440003490300c40e0007072554181c0090401c00c180000905d164100c103a6401d1501d45106460b502d80d00000c0c215041060740702c0404428203084407124105000f840e41002c0500c00d004034801494864100110390987d5a00c180280c20300402c210000c481c1c00d0070320343c810700010399071119103948035595190881c00e4280c8031140148045521440d040c460700c0040380803000c1d4100311004c075101c4000100d00c2030304c08a5040c0002d0200f100600741d24001048084c00040180c404283c040ca400d40c1804802210462550f0204003c1d045400303a0250b00245030188000e2020340c00b9191a16914003182001d001040e5420261f0205c00c158005016100303c4081500c06038040c00380c003400310304a600841f00300071a5014480d02c045182001001842d1550014042d01c520036220100a90310407a0340d0711401546a541100c44420b50503805400c0140c0755517501c00320054a0710 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 212649928 1250 212648678 212648693
    0xa1e050a05040b0a021e0c040506030d020a030c2609010807030c0f0e040204030804150807020114040b06040f1104050114070210050c0a0c030305070606080c010804060f0212010f050307050607 84
    0x107000d06030001c10b0014685650b5802040140318006540d0003861b040300305404000c1d00d4a01010300e1501881c1071601158452a01145210440304564000c02c2c86d600592822101c0e100001419905003900100d4403404c4c40e1f108000c40f0611107180c22007590b1340154400104035000040422040600c1d19106e40c03180e036440103000400da101c500c0c00100c50402c510000d00240f040394801440b030b290010f40003461130590040d840320241d45031036035001d95603a00002e038280c3d8000c000800c003240e20b5800141c001100c0c0308079260401b00140c800a8514030f610701e060301311020084090351a00c0003050400c659a0701004422200c07000c107001c00c1c2040040e0f8082a20040345140f90414804042581000c945c0b0801085000b1a0080b918400081c4d072414013401907801280280c07000303801d02c000801c980e0000200224114810780d01c1c90070710b6950b0784800004040070101c1092540d02044001145181a1070980c040c1c054298440380091400c02054600f00c2544d004070300409080c003e040124803074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 212651178 1250 212649928 212649937
    0x708060102060408090f0415080c01090b071518060504020a09060b030609220f0204050a0c05030402090703320f0105011409030c0a030311060109060810020d110a1e050a05 75
    0x14113a0b4031514201c00280001c00f1011815411a18210b280c0442d0f002d8400188100c0d45d001050b00c90a91842004407003c010a010b43d00501200b005040d00064002d84c0d8610070114640000a0071406002c60300b88101d09400155405070302c440a03c015880e00113954030007400340c18003c00410f8505081d40189000040415114006000002c0c503030b03403111040c0510320620491540c110f0812894600302441e0302e5902070740110319180000304c81191034410b0f207071503201d42c1c0c03503140c10340c0d403203a08200381014010460010161076450a0002407902d516200c05a1018030f09041c6409007400e203038043d4040144180c003000c11100040125980045940710a280031200041c3c0c2d82840001084c83c215441d4a5180c012001c62400000d00da84503000700305d10820702054400a990742d80b81002905e40340d01801e08940c00523125625501d90070340c01811003c044140102d0180003441591f003040d00322100c4400401c1c002c0c1ca18903a8003440c02490941a08142400c1e4100500301c0c2c802881c0303024 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 212652428 1250 212651178 212651183
    0xe091908090303031918030c060504060e1b0906031902090a1506120b0901061b1112010b010206160807050307110d11010b01030216020603070507050a0606030b07080601020604 77
    0x40100200303200804085510086026048942e0390411100194000607500d04003425686031080c0700c1d83d84400900302a108541603529194003001548425000b803001810445905580b000e2034000181c040c03040c1034044d80e441c0760640c891401d1f1428008410b80c010280340c482c3d005403150b001c21100e044160302040b60190b41088103559021016070041c500810180600c1c1e042c990001140c5a003e650807050952707800c0d050103030700d5200b01400301850080c02100301080c0e8061042400e0904002901c8040d0701412899071703154400310101d0b21003481000c0514591f51603980c2420156010402c080e00715012502d0600720305040540280f6848016003514100301002010801491058100c80601d1840009403098074040a501400c25144002080880e5081444102482d80a03200fa62a40c0344450b003000c1d00c0c0c1d0038039400c01c402c9070320080200e0141b003005e02004012417002c00085001074404e21001502504605007030344010030040c640c1e010400440d0402c5104c1e68046005904940d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 212653678 1250 212652428 212652463
    0x406020901050d0504060b0109060809060a02031024090b030405030901030b040204051e040507020f120901180e040501152402210301030b010906151107180905070e09 73
    0x80030036004030b0303140c811600c085599900f81014130040c0000c0f580700310104034003629a40042c654500060321703a40021140070300540c00c10300000310003c005800a640c4203080c10580c1028680b1808071a041400300003100400c020805103400c10360790440c0700c03180a046140da046085243c60398902d0b54a100e680c43c001d04142c1c6a010045080d1280d0b01581c000e81002420303180707400f0311268000c1299200404003441a81000d000ca88503a00224020300c490400c1d20250900d2a8803205e003010740d5210090050411011058816503008801d40b0b01c0b025203407445c0c00c01c2c034a0a0508000d1f080d81c40f10562800504010001008004c46a40040d10340008201030b840402ca046030003030307050400350781500600031b802988860251008900a5050360303c00c22001c18666218942c0d24221041030003100d011203401d09074114614041c006072490a04a032003201d407440d80340d21040054101c0c5040c040d10945c0c40301c03c804d0801100380310030300160402c07000c440c0320391805440b401e036104014000d011011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 212654928 1250 212653678 212653687
    0x30a02030d06081903210606030207060b0f0a0303110a1406091605010f0e0a080111120109090503030c18030d05040e07080402090604150e070e03070f03022b150507180e040602 77
    0x801c403803190070079482d0b8020b00401c5a88d6036400050081d501040e021221289090700e002d0f07280c5000d1036040803440025145840d25400c680d01519503e01e10b00400119205034103c4100040c1d0002c082c0b280302c000c0d007019000b6801d03c0180d440c038112004e40c100110b980c0f5040140090f9a014034020610807a80ca0310713003044c50310780700811000c2d41244c00046155003044249a00910604010210b0782158407501100f680d88001c00d07030442c1c4840c04020100d8008101140200e62200c002e058034840305151061048000c4c00081d00e030010144203000030650202d01000070f00a03a038441940300d009402c11103400c3c07815500040314401c005004610655031110701a00e07108151000c0340c00f52842d01a040400e080c0313820003420048a03a21103612038460780d00081000441c4009030000c4a80c003030b1402c600408050300d122035900c084010714800c4460802c000010800404001100008100307000a060801c003c008110306113070b100c6269460f610b182d04114000561075002d5101d40c02010041e05d4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 212656178 1250 212654928 212654957
    0x4050c09220c0f0512060103030e0a211202010519200d020405030712030f0c0215070f0c080705010c0605090a0b0114040f110d091103030a02030d06081903 68
    0x52410349440020029441a000401c0044014819054072100c5441d000f00903501c00070032800b04081081e103840c60700090010400240034501040102d00000c00382244240c0b41c0c4041d540844580c96081c049242c01c2e400700042c450012542101c6000310302c000c0c40540f5103900411110480014070f500c0640d6281d072400d826801160354a0044c80c1e800d808035a0316403416600c04081e40080c002c01c0c4c403a01800c1000200804040040c9085c0c90b0b243d10380441e44c2000c3c1c602500c01010440781660401c40b18501407030302c984202e0007013541501c5030300c1030382000c02131b07081c09545998075030000f402640c4588010701940ea0030101a0072801c0c2c3c0b100c0081000e9942c04080c0e0300b0900036001c007e01c0300440000100c0c0901000e0b0403075900c140240c50070000040795014420594140d540c0c10425400100032411132100036810110721140a5034a00c0c070440741d51804603146600144014005810214466003c62218003501000300904001012032031201c1180c0d01102e8070320300300102449229102c0d644e4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 212657428 1250 212656178 212656201
    0x10180302190606090c212310030c030506190b031002070606090c0f0206070905010e0f0109030209090307020f0a030201020619060306021611120303011203020c09130b090604050c09 79
    0xb4000141e4280b081c2184164051b000000410b201d901142007604603407038441040c8200704951405e18050300c2c0da5540311380703102c3c00d404000c2c00710300f44a40641008001b08042c035544000442c4103d00400961030820188480c40e6401c00342602c2c1a8207040425035503a80001d4005c40e03c0380c14010050b0307102030618041c0020b120315030100702d040d400c14046491007900400390138030040c42a029a0301c9a5070b443c1e01282c1250790740c05404c2c04620048409600d900300450341c12403401d03060526855081d100d40008520100448181146500015200c400c50030b240361164ac4031042a00d000300802c0c11070740080d40310413001f480c4441c900e4030040c0d121880102038101100650300404115138070102c1420210362503100044c2940c001d80024240101800e00800308003841c20000003944c00c503400c03d403102200b842c0c01c00303040e01144501c00d02006c407540c6010b03015014012642507114088038030b260070341001000515898083c1c20540070440814804604100c1c210402c8604030b50aa035100841d24 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 212658678 1250 212657428 212657441
    0xf030d0e0613051e090703050907060f020a0c03080c0f070305030d240b040e011e0605090a030605010f05030601053a060c0801050906040605030309150408030a02101803021906 77
    0xe90064801140f58a0354441400f42d040403541500c002d85c0075515000c0560075100280e98400865000400420000307108000d544c01160203441650310010311900c400c000f40040e40c005403074250000680c06600300080100c1620504804080d200440c61510f403c0d072039015400c0302c2c40c0d0301c580b210303021710100b030000101e4070b1803410440bc03543c912070f25481c5005aa400c6800741144080c0508008a0b60b0100000340358900c1f25081001d0b02c6c0f01c0c1c01c29508a0b0140c0040c4283d0b03030080d5000902000107030305400740c9406410704103081481549840b04151528030181d22803401000e41185000c0c01e1f46149189220f8005021203002c400b161345403528034160034400e00585518a80040044031503401400c0e981200c0b42100d81c0b241c42d880301c1d4100401c6030094402e095169008100c1c00d401030808414000096401c41103060900e552030500c1400c50344500c15010058011202001c1040f09038070510a00c6003010204d0141d14880740c0d0003a595020b40f0403418080b54501889208002c2c031038110384c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 212659928 1250 212658678 212658689
    0x212010b060d0b03100603080a0320070f020325140f060a0e0f01210f060f0303080a1401030809040f1e090506130c0b030702010b06180f030d0e0613 65
    0xd607690150261010003c00301800711912901130b1300c00e003038480c3d40240102801da903000258245000c8120800350014020490040c03031048818181d0a420b00c8440040d08886000d40d4003101480749520425080040c5000c00403000b601e4000d0b00b01d0200e00e5500c0400941e804040b480103514680e86c0058200741c00c00e40381c00d80c410000104620302e19405182d80400e98420343d01420003004020040d030700c1c200201103264044018078200a0300e00c805411614815505040019203103460b041c0c8210684500d40080d0b0200d0f201328148101d0300c907284110881c42003401080c4416505566a0b08403d1045107501c41c412030703c0b000103089510340c40d80302c0519aa101030400c0145110850003601401c0c1c000300540d400e004040010b500146094140100554010150804581401c150101c503030030152000c000c40d0350328100106103855102c010b054003007120035501d98507540481008012490041424002d40010401d411419003200f03030721441050490300c03543c85800c2c0c002100410185684103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 212661178 1250 212659928 212659939
    0x6340314011805132f121c0203070c09020d021209210f0a1b080703021018050606040b010302070501020d06140d11060f0f0a0207150311070212010b 65
    0x240040455140b0402c0c0c0c08101c1e00f40f10f9540da500c014504030b04070410141c0060303401004240c001e5a5400759412540e01d022401c0c20400104002c00c00c030208181071901141c0c00b50030001e4103004010325250b64840b00748010341c50300c0ca4907541c107810610103118103000e80c2c1e0086288011840c594040c0c4a1405003106001c4452402050407550347e910302c810541c00c9072041c00710301820781e48201111b1916050b074020614014901c101120b40c8098100c1d03101c0390800035100300300080c542c000100491070003640100311044051102204a1303511180e0303503048506801411001603800b24a01d98011402c80b400110a01c1c1007006802900c242d94006050b540b00103500c007044d40c950342c44a0706603204003503507801103c00c40c41030140d1015080005803122044800a4849140030001071840040e40300d81541080c400050011464108040030390158001040074003015400c1c400080c5003014904e014000402c01440f012020f00c18070030083d00400001340c4007152417201350010756501201412 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 212662428 1250 212661178 212661181
    0xc060a17040f02010e030a0201090b03100b0a0e030606010807020d0e060c1002040305100504050a080313060609050603161404111905070b090a0c18090506070c020306340314 76
    0x300407400c600c0c0504101d0105d9154120b07500c884c24001225460709506840360030490341403202d00106600010b0103e512403600c02c001241104907980502840c0074140c41e880c100d52004010141042c0700188001e04014201040014041d80054917454030843c0d400d001c0d0300c1c248403d020410502c602c1019103510311400407002c5001c0c0955004001302c070b004000340c0d410941002d4554050b07550681d0042c1140c1e200d160740500cc174035000c0080d0341010502c440010386105a80c0e49406a4200c1c2c0d00090f4401d03660307410002c80303080c10300c0051100c540d240b500c0c02c0b15078140041d5522078880740fa0307242e02403503039031041d00641c4901d80c1c1103600c4d41c4c0f601443c0d00729140402c3c5000780300d9480712004813500f02200c000b00d207110100003604804c49502101102082e4103207003007040c150a6504d04010000e4a41e488880440e07010300206005804944d01d01c4c210344401c1c01858a0800042d1806210307600c80074498180400e04001044507640e16040102d81c1c01843d0811000f60002d400100300001d410780 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 212663678 1250 212662428 212662433
    0xc110102070b13180203010b07030819050a0e0f1c0f0c020406090b0102100b0d03050703030216050106140108040b150a1a030601030c0315050906030f030d050a05060a06020c060a1704 80
    0x3c01041113810300c0400140300c00c0c01c5150501640004c1c070501c005c10405106600001c0d0061602c40e030300c5081000e1a41c00d071039127418040b080d184141c41100400380e42c0c0d03003646c001402c1845101180c0e403541c0000d204503102c1c0440205000c4100da8441c08001d040700481c210144240c02e000000e40c5c0091051100c2501d80c90702c0c000518589822a0152080c2000c0441400b407a028194000b00d00500c0d8640031211030302c050380d02c0c0d0b100c01c000700c08140d82041041c1154400e4202c85c00070f5030090f00001505401e05ca03035500700342c444c101c4403418440441c04210005071100020350303012007806040748100030881c2c082010b1440d240c201201c131030600034004040c1c00c3e12502540c46860260703014005020049015412140348280b56100640c01c010140418103107441091340200010b411103544401d05000d140c01c5070044500110151f4448d0280800b5504d240140c50f0009800c8503036461840c9061406503451040e106028000c41010a081129170b0003800040c04419203070141044916051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 212664928 1250 212663678 212663707
    0xc271a0c100e010605011b1203020702030d0306150309020603041112030406020a0b01060c03050d050705091003060326040e100e04050607020106080606031e01020d061e06020105070c110102070b 85
    0x1042d480300035610b0041c0000303a944c811018021070044003044034003844116101c418038a001d081d6507105040c0c082003180c0051300c00700003042ca0041e1a941c006055070a01070600c403403118420b485401c050408003c48050ba850346c080707030740081d4849818150a1400d0010600194180a11542c6e5020100700040c58980106184042130f01ca0340c000b66440e030326113009490030035510b5005070014005110107040d0409580c002500400c042c01e2a41c20a0348100024240d02907584040001a84989d03042040003d081d540ba140103801a04201c0803d8003940f841e00e0b180180d12403c003001200c03030007160021288044c0f08001d42140422140140303024102540d44200a460410044d03203840320024841d403020441078091080140070304030101c0511528500f09841780d8407142a95420040341e400c01d0f41504c1941d008010300c030841c0c5503004101842c01c0c040e509030f61081c4156410001000081c541c40300862000640c40b80303408104144080c0102e280c500c242e00411240b0b0000200c1c120715401c0c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 212666178 1250 212664928 212664941
    0x60c03040608010602150f04050a0602030c04080601080d05070308040309030213050601020f0d020706050715050f2e03080d02130603051f080a0201030c120504060c271a0c10 76
    0x141e00d82d10a2642d848008903079035400050300411b80413003000450900032043c0d0b0040d401c140518101e5180280320385441c4c041b43c0c8241c40251300c1080c006820840460240429401007640e00d024000d0b06d1841000646079214003c0001c0c1049140c1c00004e0030507000d032502760007075074010380458007100041500400070a010780d1500c0c09807044400d280d04a04002035089a030105d0750380134041d9a0300c0c044082d90150804901114803c1c111030240180c194244582481080b0003d100c1c078040c1041c0071405c00c440c0745030000407044003083c400d01364408d184070805000c480d0312107140c3d940c17500345075003c400a01615824078504a10303040e001580c1d07581030700300a00440c0d84550035030070100b112140240d8005d503441120030303981010102d0800343d8002e61028000d1889810041c059000e403c06c2802140c1003218104e030441d076148035040c00643d00c00e29060301c802e16a0100070340110000314040741641c0c20300c21a000300e1060002c2c0001800c1c41c03003d40d5441c9050508a80c14011740703811a4018004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 212667428 1250 212666178 212666189
    0x2090405010b0c101d01050a06060e01020303040c050f010504080102070302150c180418120c1703090316110303070c150c0339080307030f1a06070c05060c0304 70
    0xd200021410b081c0050440d501c0c190424002d1444120b4100c481000d420300000c030040015104000510007102801064420609070307100203007640c1001005040300d008a684541194414420400001e80d11b0842030255601103c0c1070000340c01010040b10540b0550f00041d000e54000706022080540000d100c0c408000c00004580c010340c1c41d0000b03402c65002e00058440c00c1c04502070f013814070313003495440f21880c0010b4144140541c0042d8843c60480d080c047c40c120001041c02a0700d805002410405980c54218003441074034500344001b00544d02c1c080c2080048800d11236034803002c1007110780c2c006000300f03110140680c0e0300d907201424060394600300c80c480d0007014401400065501c921441c00140d44940c036403a4080f010802080c2c020700c0e204010307504120241528903414141c5801c06204411501c1044bc80d0f03541d180c0382400a0a907900b0802c6c0486c0d1604207442d0341c4001d42c8511040d0410303070041c0e591584520700d1b41002004189154012504080f000407409910f520100040040c0c54 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 212668678 1250 212667428 212667431
    0x603050c0f2802011503020105090604050301022701090302010903140a0510022a0624030601140f040e190819020106030c0e070509090a2003010f0501090b0318070b0706020904 77
    0x442c0d0603030070703400c1e10768150b91181d401e0795000382400191302400c05040810b101a02c0e0700d0919803610042802c990000c0c464403040700003604c00d5590080f0f280c0d180703500e0310001e10705212054990750002c1e0840e007041c0401003000601d04100088814100008144513421138104c0c0e0469a81c045080001e50010080c3d0b042c50132444410326208c2444401c1004051040380100725036541c40841240c180d00c44a150300012940d0740c030464071a5010005280a003c0030080071b054002a00100000e0030000c0410034022803c00e216502d08000203d8900b61007050092070311001d28062510162500c65140310007207641c606084240001c1c0c1c15801402500e1103200b14800641d100c00e03d1a2101c0c004550b00c0c2d0024004100480c01410102c503045d41000700c401c00819010107040003222410410410111008408001000800031520003840100b03000e00344840d6a80c14a00d01000502c4011301055411420030503100f10741c2401c02548004010949140d030311800145401e2000c1e42c492490340384100e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 212669928 1250 212668678 212668747
    0x1205011e06020f03041401020f0d05091215041101110f06040c1e050105070309090f0b0405070903110607051504050708120c03090904020f0d1109010602030f03010603050c0f 76
    0x250000407040883c1034a03200560070f04d032030918031214020500d01c0040c114000d10008000108040081c4013100180b074489a884004070000c0c440c03003003c0341001104a0b8003480f1001503400c035000510790000d41254010904038004001a1410010124003101c14440c2940045800401140460140d0321400a80310215610582806051034030448030014841010081040358040c4000b03000480c03280c1004110305aa4011301c1c0b08589044640d801035545542030ba80c40c1c0d162900c0b8481d4801010705000b552541180c0300c1301000c80c4400480c43c0200400034050080c04403c01c40e084d0070508400c4640414981890000d45401d240d21441c00b5511582c0b0001d41e01c2c0303420005513035003056104029030500401004100c102e4502400c145d1700700a8002c03c03003001da20340c03002132000c070b500450f0301ca4611490b250901010380e005901900454005025080285c0d1518045904480d0035140110301910b031007141420b6441554121001d054000403e0103501d6441141024003940c0741031400e050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 212671178 1250 212669928 212669939
    0x9010506090601170910060b03040c0e01060e061e04170106050102010c080403030f0f0c02010606090e010e060907121a0111060108060a020a030b120f061807090b011205011e 76
    0x4070809a40a40c08541883d10400280795100420341c0e02c4810f5404484688905c1c08071001250369981044412030f80020820082c0a03d0041d0040204400d5900c14510341c0b500e030b0002c01e117900000721144514000034112082007004d054507001c080810710764641d15a554000142a0270750095842890b5081c00800640c030741c010f11a01c007414006440d105295a0385550840c0144940700d501040c0355650b81003400c0d96501880344048555803600000f070700c1d504011003d48500b080703500c070000800300140140034020042d1403180e0029000c0e58070480c1d503100c4440c02e6401030140f80005410500c3d105078200c0c50203290000300d20800f02a00c40000c000c80700c62156461700b00034090681140d2004011a0304040303598020b0409410034507000030f100d031020000030161003070301500100300e60040d521164a084244011a08100c03014084640480300185041c1c803001c440c801d14405642e1713010702c0d0085900940450340342001c0300208000d65038680c40c9005080402c41d000c490412540d40d00443c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 212672428 1250 212671178 212671189
    0x12010f03030c0201121508070518011401030905070830030f040b090a0b10080601060801031e060b043608090f01140d0e100603022808030406020609010506 68
    0x9407074042d81c815644400640065412021200c5072540080d07490582c00841200d02400c00054a208005044921b1a0070304109000c81481511040103c4d210010840390901000704078078064203080125406d0171a0404a007000119400486c089c02020802c07002c1d00e0003004203012451420750382004a1841e49441007140c082240d01d46140702004010801060891282035800341e80b440c200c0f1000649030b0fa80b9980d00e80183e6000038944e02500303091083c00d80501003980503000303500e041d4071a0340c5140c03512300d0100500310000c07040140c11441c420603c010341e040912440e8010b07000303118660007a0109844281c981c01e441c0c2c07210018094130120b0740e0951900b840d0454006000d80d04104d007020400c1030f58203280006a05000e25141140d500290700c4018200510710300c0000aaa8113410700400c5c00c002c0d4000349000f00c18036089080c00143d441282c0000700c00074001041403600008600b05413a02526000411284004103000a08030303070024040d44108424402440551908401d212 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 212673678 1250 212672428 212672459
    0x1140c030307031a0d0308040203070503010519090305090a0b07030f0f12020c0a0609050d0e06090a0905090c0301060803090f09010e0412020a0210081510080105040f021903021201 79
    0x46a60410004039074228840d0304000b16001c110001c40c0c420340d80b9240014107880010104070082101e940410080d0f10302030040c00c000707040a4000380020710704580034441680d40d400400456560b542186810305200d5001e50340c041c01d010307000c281001d494071050b0586411800c82100056020400681c1e034034452585202041110303203071240401015041d00002e9040645480e11910907510030b0008100d090140c002140d005102604031601d01450041030600d06200d01e60144d1010004001141c1f5407102020403117040304000160364440c0d201d424205800b81807030340c0d410342c02c0c1503010585000100090825950850f50449908844400c0c4484241d00744034070204501042c0c00140411803100d460200d611541c41622071441c3e49500007a440e100c1418410000b88802c82000910718900464654924040740c4091391084140c000a01c86541402010b0240d80c844203000b8084015406035040980f402c10008080030354080024000c2d00010000c9111001c50030000074110b00380e01e0b485 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 212674928 1250 212673678 212673697
    0x71b06020d03240f051002010506011205040f02090c270604030609050a0803090703032a06180204140603060c040f0509070504051c060e0c030712050f0312060114 71
    0x10305a500041c90300303400901e20a229000b096580140f002d0078002080d100c0d102070000c03c0c0001510a0415050256595201c05204103581c50701040c030003140e802c5580405401203040f8003040310307512890070310300c600c0900100a4002020700c05001070f0508840c0900740103141a2140c901501440054007200c03000e82100b160030020411051010038101d40210103101d000d00121003d03500c0c0e41c0d507903a80543c03007260b507201241c000120030300401d40e0240802e840d5144100400c0d4440d60180348207134a414607a03c00518442e551040d02d4004035221400e0588503400400800041d4a048440405002c013294410f201c0d01410001940100c5048180d0302034032070303409541d00668200400d004101c44090b00c1d0f482880400c1c4000180c5584d440d1003108025402038031442c061b40c19140680648450790411491078110111480c000d490000b043c07002c6a01c102c00071082e00300f103403c1850800701d40108515040c000060300314120344c1d010341c100c4d0141c10300f1398078010701005c45114540d0501643e030340e8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 212676178 1250 212674928 212674933
    0x50f1302060d110f0a0513050604050f090601140c0109020316080604030503190e0a051204140d0f0f05071e03230708010204060e1f0507081b01060605071b0602 70
    0x200c805032180b0340c0000000a00d854006141c044028032086940d009408018002400091084444144507c0f948020642962400c0c1824100000036081009500e2014058150f6800080850784295451403200c100d0b0700003c3e0303030748402e41c010704d001e0203813008240c1c000d20030040da280340b007288004441c0855000d0340152400b900c071983c0481d02a40f001d0310038040e04c043c024082c006a82d41b88030b02c400c014180d070001c00f0650303440e207415403c28010303003140401c01c0d400b48000c0000000249000400c4c1c101201d0001e607501040c980309508111405000d0003103900b6018076420810700080510580b058524615424611000710082c44051800028015818040c1c48152026000c030140381004a0f00c080e00c0c0c0041d02c03000c500742240c0160307020800045102c5900ea0319801d003410450441450390945a00d50218080050130701d11a506000f48641d10000b071038011107071184219118060244000d1200e1f6603600002011a04031510a94041082c101e02c9600482c0c4400c01d0021585203401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 212677428 1250 212676178 212676187
    0x30f0b0319290a0f140601050a030b061608031009020f160809120102130503280f0804030303060501140306010801030b0c0424020708030301030803060405061c0303050f130206 77
    0x3a010104200c0070300780c5a84851042c4064000b0445603101881001c400303c0006001c079a9a03a48002c0da50b942807000b4126143d0780c01e000e200c1c1d910108a680242e014180807810740c540c440814114850f00d003030615a081000902800c21041c440114000c25200c00c81800c07080e103940250040344100300038031621031030403c140017502c0c1855103c1000c0b0ba024a000c44c2c1808410340205088240d05d00d81d00e1707441d9600190840010b11090030040c0905401d038003c041081e2900241c00000041004040081c01c145001c0410080070701c40c455816940a9440c503242d9641c0e00d00a0041c6c001806031030b01050b480b40d2600104204803043e24812a4141d4602100e41d1030350300d85200681000d001901488000c010106443d00380384050417a2014500c0c0c20407c01d450500002c0c1440c01c243c000d0700840e0000c100400c0440c0c1c0c0030050fa0f0304400c00b19000641c1e80c84020004841c80344010101c45981c902d02842414560075502182c4513020190602c3e030150f40380e440c000201c1c4811240203502c50340900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 212678678 1250 212677428 212677433
    0x1605031204050f0d060e060103030311121b0c070e04050705090f0f07030b0a0815060306190c050d2d02091c08120903030403030f020306060301140f10030f0b0319 71
    0x10600c0400c0600584007104004460305c403101a9009203504000691280f001042007542c1031143c00314000742141011700f4110640010011004050030440704030290320350303034400f04604d035003250702200040007110001030f503420801892403c2143e080c0e540d40140040010b50b4204100e41e144a81481d80c8001142c0c1d49080240d026088003400c0c0e4810542d039101074a415841d51940342c009021a10010082c400203c0414088100d009044c1c81c0a0340280f028800c0303008108110304101004050f000c01c0c0041090001c0721217000d044801c1c0c00c075505000070684030012181019240c1d0f43c40c100060160b8800140000c1030b803017401c585c1c42e0000303980e141550005642803064810706114060302c501d0180f80c4154210b000ca0f0586600d00c05800c0001400209034141c4994809020100015415840c08000080c03060005214841c0100d84450203924282d803001000b1261410003480806c1a0f0085e480080007070140c0001515030340c0c5050044116450001840f02c90301800003004d01901c6810b9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 212679928 1250 212678678 212678689
    0x40603110907021e07170d05070b0405030706111b0a03050921010518060708070e060d09051b040c110c06070c09090813060c0b010608090f030309160503120405 70
    0x4142c00c0440c024011020314a0b160001c2c0c036462005000c0041440b40c0c245070940d40c2c402403c850158013a4003000c1000701d902d401105540146800954564241c1d0307032070400e1405d510500d01e00411303d6282c40120208501d540b000303000c004064802c2c941d107036824111031603900c004807071014012403018050f4084515003002ea401c968610f004c055070800503545641400d48034150f4400021201004140c0480501009a10352040440c0303030001c898208400e01a0104100c0141103029140c0000d80f40005025070f009040c141c1c0c4d07c00101c03140c04803071401908203800022602c034401d50602440441c0148500d41e40603d101d20b0001a195413a1000e080040c90307841104115110b2201c00c40000d40c000e454071a8996503400703003440582e90068403189403102251900403070280100d507030080021035680081c050558000b400c00611a88401103210318029005003c2000c5200c000708102e021360001c140a080340343d00580cae2a100c1a01e8108054a454007004407030090402484100304c5850f22 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 212681178 1250 212679928 212679931
    0x901030b0c0403060207050c0118182a020a02131118030c030319180b2a0109030e090f06010c12050d02040b03041406071b0606320406031109 62
    0x1d041240b0b0b180d030300c0d03031604d0503a081420241c800790440100d5202658120042c0300c2c100700615084030225040a001c500b4040d400015228005d503180001d0300040480b00c440441d8500000d02c0884801c03010310000d68613201010205d000e20311103603400090600714000c033081c40c9400a20301d0f041a11a0b401c8100c11502c0d101260303850b104d58180c002c02502c1c103000400320407901811202d0348201910b80074240a00d017208844541a84a00070400751801e00141c400014800708444280c0781411190f201d003c5d040e4140e10500d502c0c0400600c01c041d0003400c1c40c0c00207042510003454550340c00c54140700120084600b18085030920a400740003500c48401c080b00b498031420014100003051603140d089812503000716665442c00018481884103004100003403001c1e10008081c0703440e0981c0000c10f294807134102c042d03200b40c914080c5010000f8a41000024101c1c8100043c110711101d000c00410b004107500c1c0b000001c07000034403142030741080d028482c241c9401401004002309401c003407101c01c660 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 212682428 1250 212681178 212681191
    0x12020c07050f0a0b030702030d0b03030a05070803060a03150209130c0206060d030c08030f150a0503030a03090c030204020c0a0309120b010b220f0801180c211502071403090901030b 79
    0x202800b007800d0a2031340c09140511016401107441c2c0d00d0103c000021150340c030740401d00c280d0040c00340756a2168000126401c0c01e5118a8a40d1a0384401d130108208500c2034000a1408542001d120342042e240d60260030700ca41c040300c0b0207000071401c180e40c0f000c07101e465240c4401030f002034000801c1c0e42480c4180000b010b10034602115558031a80f03964009030000c3c2c0303103083c400112000740201c0e6040c111181e42500d80433245140041e10300400240d0381d215094502c004e15403034038995024040c0112801000f503801a00565482c0f181c0020707180c0b5450043c800308c011949058001c203880d001d48080003025070b0311810840351a400c0070030b0702005030894250440f00b90b00b13028504888280b4507a41900604810941078115420240b44070300351140d811380044885052500300c2d001c514025011307412207049146121050020703c02001c0369000c100c0020340310580310b9807991044103583d0f005212207030140c1b1300c2e0303924810012001034492041400e020760003d03034100103002095910100c16007018 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 212683678 1250 212682428 212682439
    0x1e010c17040818190e07110114070807090305010e030403022409040513061401030203061e0c131a04031b060f030f1506030608121309020a030b0d05060712020c07050f 73
    0xb02d004c80c0c600c1d62264036044020603104100031b01280c190451100142040039400a10001c103024220810500c130080200301001024004204480c0c09500340308040c54000c4000d000301d006110b400303940ca5200b44403c0b40200302607030702d00c1942d101c5180b061a03040c00e00400781b0b203060421802c0101900c0054100c00d0b440b410702211400041d800e10909036107203d07192032090690301d036004240c144040203103008044d9400380d011040e0802424a1a680408070000d095111440c081d14640310180c1c0d50000200c440090b0310140e19108268042c008480c0300700f1a01020721040a15030354213504610480004c00c1541c00c0380031050f40244c0260700640c0c4105400940d120155800301c1c1c1400f038591082012980d28101800000740512440080f003040190a070300d850b01c03410000320030303141d20312071a02d01c00d41c003140385100c0d64841d80190300400da00508030200ca403a9810081d0300c4e8902926007101091b0444840d0452031114000e441010b10300274040d0040501d020b061000d56011040e0490340700 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 212684928 1250 212683678 212683699
    0x61006050702061903020d0c1205150a0501050f070b090a05070602070b07060e011b0309150c0206060108040312020a260c04150905120102070506070e0d03050901021e010c17040818 79
    0x2042140b040008440c010380d5030355a07410300c050281044400152117041c112010541c002f40646a507282c4c0001c0710002e03e00300e0781c6d81002185040007030207124001400e4244180a101c01580000345244e036050180701507480c1d003961840c080c2c1c0e4940d40344c03013410490b500c1401f2201c041817656028015005501002141d61050710b0740d50036214803030340c4220f0f01107641c070401030040c0721019554000700d00340140104114110b440011317560b820010001410011031000280400d031048044101d4028007e500755119000400080e002ca5078048513424000ea000208403e840c0070340b03a403180a1020002c42500d0309041041c0758014101c4102d80c1018891851400a0785455024508400c880c6071000140c5600e4146495803c10001401c1001003011807007150f0029660940120440c075498240a562000143c00503802e240590600c1d041e0020a108040b80142041d00421002d0700f0544d62241c00d1000c00b4292030000d44182da010300501000e00000004130800084070240c080001d0051148 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 212686178 1250 212684928 212684947
    0x10060f180e1c030e07080124120f030215010e06040e03031b13050a03080304060e030a1e09080307050615061612170109020405090a0c08070c0305041706100605070206190302 76
    0x405c00c0e1580f090b12160b640d01e400b0381440c0c0d501d106075907550440c034551070401481c0c2501c0344022682d15002070b040748030805c82281014000c00510300c5285c030f0110100e4240d0ba490b80e102d05000003c075900c5004608080b512080c0c0780c0044105d038850704510341403024401c5212004030a076007001d54043c051440b03145c0e000c100d654400101000440c401d008440e600c1c81d241c9003100a0341d05a8030300f00c1c0e150740f0522401c0c81141e000380c40849000080c20804208005030f0034101d450038000c1d48000750030b00000610100340040440c5c02849a0000003445111050041c1844060b01c11420003034000c0c03405241d19800201008101e0460380500d10b00140039410208802000540c01c1c1d101c1030005900140030412030501089203a80b000c00443c0070001c15044034800b0300360b2500106607008106155405c0005c15015100b40c6010308000c02c6c9400c03580d0840b000c1d09548030307800d40752064041501d00001030381c1c901c01c104a492071a800b62000f81000d80081405500c505070035140d4050540038881d5408 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 212687428 1250 212686178 212686183
    0x3120f0c1a09030c030f0408071a07060b040902060c01141b0a03020f130f0e070f05040905090a060f0204030309150c12030f090b0103020907080606090d030210060f180e1c030e 77
    0x4100b26401c8956101e280200482c0b82961650015122b403001c112102480c860b40320580f100c05070001d50204113005901d0004000b807144110095100801044603050300c04154046144030007100e210184a45841c005025880003103103045404000400506002601c0380e00502404400c800c9000c0c201134041c5125401a04c9903048890442e000e030b04108401849100c0080e0082c6182c10b2401401809035030040c4140f045004290309288c480c000b09001c0c00741000044242a0020420000c652414140c440a584140b20640000d0070801000c61070b130304000d00d083e01000e03003511000002c9030f050f524007002c60007125181c0305050365801d110440740c03840c4c01031a4055102d40405031266040d03204000d01e4036005413034481008120402c1003455224041220044a01210300d4454040e040c90100d113040001800c4141c014103044000911041641a560580e452000a8014440400d503e8011159030800200c1e80c1c0e40980035038107800c8504082043e28843c170b4907001c2080c404100d030862 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 212688678 1250 212687428 212687437
    0x307090e0303040317010b27091f0503030301052b050715031109010207060503100b070609060608060906010608040215130e13030c081305090103120f0c1a09030c03 72
    0xc406410001c100002c143e8080240c081440701c00d0104400355040144841c1c660090f40c050305a8441e02d1130100154102e0b031034403034001e00802044c0c1c1815251914040d20b00034100a00001c202080d84408111440e003c802d03203060707034009040c5548040860302d0010514440580416203400b58140c05da011480034440c100241c0000c01399040c1c00c1c00c900a0050450f2110703200c1c440102c5e010301c11040140c2c4c0c04500541117880524190f916520703046038000e400001d035400f100e9202c200003407844c02c11810fa081100d27000c1c00760208111995481015607102c0e00212000740543d04001d0050189a0042000580082c0041d044404079018000d14000d0707644540020207000d104407c0030826a140340000b550701481031052005502103a50f0007811101207460024415407001c44c03400041d2004141c280000e0400501c611150759480c00c01c285040e003101419000518400c40e10003403180030740060709107180d000070740c603100d5120040d64801481016205240c035000400032300c0c0b8860010005403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 212689928 1250 212688678 212688701
    0x1209170d0e060a020c0c090f04140309030a1a010b07030c080c070515031006260a0902030706081605031512012c0c030f030a0507050114010b09040b0d0809010c02030709 74
    0x140e80703070301704800c0600d086285c080c183d20400c01c4c02e080040308141c20040c41e81069010f02c400e44c4060108a455007903015241646425205031641c07202405071626480c0e49440030802d0700005a41c81c1c0a41c00e015210700d810250100b20685038040010302c0031b0000704003550030002901d408071f44030f20010320007041c00070752074801000100034407202d015601d6040000305841e003404104818088070000e500301841d00201c104010340d000080c483c910580010000942c01400d95203003540712540600604801d940d0302c1808600c01c29440c0c0c0c42402441241c1c0111081105071400f100383c0001c100c0550b1311901641015500c84c10340d00d40501e040d0351a0351000103188074502d482419540040d14084075403070500d02c01e5200103200c4060000102c1110088801072800a40d2100c0b6420040d0151440c1c201340c3d80c100c5400000080d0340d0f440c007006000040800c031810f2020000c50400c00c00301c1c0d4841d001c060090181080401d82c20743c000c03691040b10520140030303200d9082e038400a038004c0340d10b0040324 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 212691178 1250 212689928 212689931
    0xf060a0201150f0503010c110d0e0d050d08100f0f0302041a120709140c071b180501091802091f0e090a050c03071212050f0d0b011209170d0e060a 64
    0xd02caa49000e0003000080c0760942381c012154225a0821955078061014038420321620360046806500e412400b03a4503d40c02001b00c802200f80c0c1480103101100865041e950a404080302003464507140c0c01e21422030f1410b20949803420704507001c000007040381074030700c0008816140901c020fa0f1541c01d180d000140070702000c2c06a070b61518240600362520300c94400b100454010401c000e108041042e200740c181c116006030f01c0350f4000c0e52007010740d4140350416101b03c42403044028141405400c000c1c1030b035221080a1200d000000b4624523a15400c1000a40c0f0090314000036140c0285900d101264008941c01804a5650f03048071003011842070700c6807001c54000700000400d00c070003000700c100c00910641c002c02915103060b03100141410b12001c01030644030340340760700c002d011f10403020780f4404c1c1c19620703640355500d00040484004045c289030280c00725118440001913403140d84144ca03030f16900200f5024113401f000c85001c82e00d5200361202a9910394032080240d400b4020031041c4d1141f0301c000c50 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 212692428 1250 212691178 212691209
    0x20f0903060a1a03280201020109051c030605010806010206190b060a02100c09082802090717060103052701020415021005090a08090d0f06050c12010807050f060a020115 74
    0x39440a08010351503d02031741c0f001200d00c4841c50b4554010105482507030144959989620040b4050000100050907131b201e6448141d803403205805250b07004c0b4111383ca04004640e580c0e0015288078000f19105405608100000f400401c401e070254050350480400c0007481489100c00100b03035810052820005912140c000940381d240382c0b058a0034515181024001d681c80d00403045e42c1c500280760310030800e49100002440207202815090083c0c0c0d8000c050b80c03003600d8960001003e00300310102100340b850350070010030507950103482401e02035204900c06440d590000c640c940342200621941040307966003004000b403e507801140c0140f42c00507031350250044081aa1081095450103080311155810505222000414000c100e40500c101a00c804070000c0d82800c010000c449a000090001b0b030a0408008480300840c004003070310340b85200802c2c6140d80301d0010796500c10290094130f0b002080419102c4070361030030401900504407a440080b41c90b1003029061440c0074116403010b03810041c1c0e400c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 212693678 1250 212692428 212692451
    0xa060c2916020f0a020f10020309091302100f081f0b0a0f12060b07110f0405010e06040c020102120609060607050d080601030b0603040b06040e010f091a070206090c0103020f0903060a 80
    0x1090301c4030f03001401c2c0181043d40460f000110b00340d00d1414407a00c04d100c4284000015402401600c41c0550300400c0d11801d468402c03c4411805a8040124841d008103454603900d20302800c0410946141c9a07030b04101d655070140b001501038070a00d0000406080180000b07144c1444000800340e01503650380701c0c07501058444020b0b04166022400d200c0b0707541840000d102180c045030030303916400e4000401148541c01e0034007242c0320305415080b15030090b0030f14002040c00364107021240e004120070f5608100c0d418003504228200d0203400007035030307120354020080342943ca0300010454200100a00702407508040e561903600e030502c5c000441000c00c1200c03040100541e0103210b523800c5400d007951400c1c550304e0300e540c030100b181c000108600c1c400c41d5a800038842002d000d40c440c801040b40c18008104648050416640c8001100c2c107554080500e840000c0c0c1640c4081780c0c803802150300c10700401c0f9000340c844c010b501a4104a6101803030f0b1500b4030610398103903010440d00d40180d803040000100c0700c4030b00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 212694928 1250 212693678 212693683
    0x42301051507030503070915020a05070518041115070c03020a090504150c02161409060607031d0f04090b0601020d1e0c0f0206040609080c0a060c291602 67
    0x590095100780d84a004505505084000325410a645803408a0b40c942d5800020b441c4c124258009400141c029080613480075000074044240e2400ba070300319850780740c0c0d607020008401011850030041018120101d400074031349120005446200421928281f03150114200c006e410840065429007401d500030020b500380b0f0350a040141c480e000d42809545407070789400761303988148500101055564440304030090310900810040d15010303520000e6445d5101010064044460101c41c444d40140000c18080c4c54418111003246d039068030386c2031681091000c51f45010140c9065a60000f265448040107a9250b124502c2c07800d0bc2034030020702e2400e01c0d600092620a000314074100303001940940c131a103c02c102064400100c070610702420198014a0301580410315070390002d400110100700410f060381c0140c550300903955032104841e140903100e8208100021076100301d04c04500d14400314400f00c0d40c40c42c142034007140011081c04800440c11861010b0040480e828108881c91070300030020b06506 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 212696178 1250 212694928 212694931
    0x12150904151a061204030e12010c0e0301061202060d0609060603050901050703060e1614030a05010302100c170904020c060a020d0c02162d0807091413080c0102090423 73
    0x10070b019003000711584408250b16210381c1e22181c510090810024080501c2200308600303004026200e40001c031040680c80303000e4031a4008083c080b0322a01030b0300c883c5080500c607190499103042c5440c0241da20b16000e10110f036200442007804680c42c0c1001080e0041d190082100400080d5000106460402451401c56001070040300030036041440810203045002c034201d1b0001c160580c4c0407401010702030261030246004140b4083c200c1e000c010080f1301c07045a44024100d9009071094601400c846030100c3d008142214024021100319031400d803800d5600019003104640a04010b2900d01901d50991a003102110019070040e000100c640c2004c0ca22b010b00d01d601ca00900041c1040e80700c03007958150b212064020501040c0000d2510310302c015042c2070604140041401551441d41c5501c41a070f11400c00f4020340c0f0040d810300d50300440304507210001503c1003214480da03080040440c4e590012903840020941042e41d002d10064103d0f64892083c0b0078207009100b40080c070b41d50b0399580306151050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 212697428 1250 212696178 212696201
    0x803041e05060a02030a0e011b0906090e1302040e03070c1a0406120e1504030806010206011a16030e040c1d12030d0902040617030705211215090415 65
    0x514440000006800242c0540c10048450001d41c42c0c1e03070f40c030a41d00014030054002840c0e80d82070078000386005a01840c1114a07030525a2404e0403282c6a0700103a82c03074605c1740324907003913211000006207501c2100703250200e400e8402030002c564111074682c1d0600c1c0d5000300d03800362260a030201081216041c000304001e19160403c03640c0d418a4640700c800385c03080690590382c03400e958440f60a01400042845140c44a04a10800c0d65203418a41402424408202c1d0781c140035104030800880d0721501071308848130f000d080781e412601d880c0b41d1090060317511052040480912101880e100155078450041c540a12059641e0445911010501c134100e84110400640240503480d03540e81c0d6540e01000329200e08240e001e02140c40c440d1480403400410b03259020050841c0340c8814803000355001700060021a0264040f64a40740f182601034031400b03102c1484840019007000714040c9054000c449079400b010340441d013080920404003040321070100301d40c01ca940c000d84445e124013504e038030b1285500100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 212698678 1250 212697428 212697473
    0xf050c030106090e0706080a090204090b040308060a120f1a0c0a020c090105010206012d15030f0605130f060816030c0803030123120d050a030e03030f010b0c0709020403080304 77
    0x9070312a03c0d03c4d1036085d1402074008104c0c42d00001405008144c00010f10158058000c100b89501400c080303c91805c260b4045002071401c001250541c50a800340e48281c0d0496031040042c003140da942c1c065041205801100c2102c68900034105640c802d04002d48540c200c0c108040c0d454140706002424201d200b81010300c01c0c0c5240005004a90380000d042d07055800b8041040b819000385118030410480e4510484c0301c08546000c080343c00c04041861000c417003150307103051001d4000c2c8000f0b1070036a20a8000c0702d400000341580c106810009030040005015058000181e182d00e03600850704048076009003140c2c040c50004200100580701d0289030040c1031361000307107055506010b0303c00403403611006000c46840c1d903940c844000f96102c0a14450b10040c0e0340444844030b0451001802c40e4000300c0c00d50021900e400d4004180043c007100f12032040000441c000c6c0e540c2c0c2072007080107060300000a060001c0c031880c540402c0c8000d49100810145005000094a0385400c2c44e000d640c94210288205855 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 212699928 1250 212698678 212698691
    0x8030304081e040e07090303030b3118050703170c07030206090111010c030f05090a0503121b0d1a0f0f0d050c0409200105090108040b06010207030f050c03010609 71
    0x1140c0d1002d0b0303401041c0c0881040c06000c070406201c541802250480900b0b2031040b0248081550010710701d0007101d100b62400d2024403481810010344c1074081c01c0794400003401c04004203032421282c510201c020405a400541d640c00400c0046008113496412180369100c00c00c00c0c001d10003407410510304032444240c101d103440068040325882c0da0662000034000c64001c0340c012120380c0100302c0050451070351030003004041c540c0c00b0002c010b00212000b41c85901c0c40c15000c40e0300728401003800710101303800000a42c80c01c0700e18200081000001854000b1850442e0100c0c4184000603000b0721030750407030901c041100308141b100340003030309000001c8a00c1200d9142020502d5103802246024000301254450801c2185082c420b00700f2482c0c0195a90003441c0c5800741d0100701c070710115084030035150302800301c0040301c001c010341e110300c1601100340c003082d129000500001c10074811281c2c804418030680d260f0540c0c03035880c108020403502085400c1c0e00146a0015039050074032800e4020942020300b032188 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 212701178 1250 212699928 212699933
    0x90c05210417030406021b011a03010b0609220617070905060901050112060803221a03011e120c05090f0106051c1e050403090b13050918060a0e0708030304 68
    0x10109040c0c1100c000442c04030000d000d218441d4165074030340d150f14112040901c1d4004900d030080c018002d00c064154007561800780d00e42014411030921010160005180400c89800c00c0074560301040d5410703046004240010b0b400e1581e010b0100104143e580f03c40304014130807501e6090482c031b40c0022045501d4075017000995580e130704c001c0341110000e00f092404400340c8075030741d00a00400d4002031102e00c80002e620080100e43c1365060f07800329501c0f882c9210240c0340e02c50008000c4c0c42d8410f81c10044810300040c40846221682c0450210348000ca0348011a91224106542e0003040030642c0d215000b132108015904008100030b6021403003129002d610340c1010000b070300c00c2c02000c1c01d01207041c843c04042c2c4070005103a48040007403905204a90308040070b604844010b0503007164100e00150243c0d1000404902c05402d9a69505103015084800c03410841807050b124401810245144980c44081e5000e010a024640c022008504007290719520304181501d03100d615400003103580d1042040001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 212702428 1250 212701178 212701193
    0x703171308071a1008011a130b01050c010f0b040e0105040312020d0b1c1101020706020a030c1703130204051509011707050604180f0e0a0b04020109090c052104 70
    0xca40ea444a6480d4a401242c1828416240301a803861050501a000d000c0a03d4005940c20101c660380b90080c042d040e19280f0080e0b0300f9107050f888a4110151811440000c030301034004060300841898910305040311900142d0070340b48001300c1002007650fa44040750b86400c182c0942c2c080882e0f07420090241c1c6c1040c1e44c0061103400400c0100910a90200d502e07810400b454100040e5100c004111500c4190140072003c90b0035448102241c0c64220144030743c006500105448040341e01c0f40e0003600020400d6203080d1240b4420001c1218a030304102c07090307442e40071240044c47c05950088040d1304030720080c1c4107101c115080a0200541807a06401c16a0555901c02045054a20b0b0f040e43c441180d46100e50b01d403030904aa001381c0e500620105020400c0c4109070000031000800440c01c1c001010601d004408541d400c420708030310340e00b0113040708c400300e15015119034000348103151640f01c45a60700b0251046070089a0300100084002441d502444030300f11b04000101c1c0241541c4003107080c1a65003c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 212703678 1250 212702428 212702461
    0x509060108040f060f060303085b0617010e01230a05220b0609011e090302061b01060b160f080903030d0b01200303150a03021203070317 60
    0x405159103589803000308000b50304890300b01c40c1111811b00141d0780724640903001e4601200c42c042c02c4410900c0858200081d03180640050b6108500310301801c81c10101c036002c68801040c0c45880446081c81c001204050340500390061040c0d0380c071820443c0f820f400484103004103a200d42e1240c040c0d07400602181000070b0051020442200003401d0206c8000049148550703154402c0340d01c00f102d24810410301c0055203103140a0001d080e410007440070b1034000c00c07c09018400300c040c00203016605428500c0e8820010810364003c9061030750040b40e41e68005115907009419a1641c403440800310004084240030307a602525040700381a0030404602c880001c0f0a0b0b9204003c2d01700022258a18107000014045980400014050342d030303190086505540031f400c408006c180064840d80d540c09041802c0b0110704400d10201020794a10340f100c8002c0c9032600c04001186610401c41800000160343c0e4085c00301443c1841c0001c1d640b25121400c000d4200714038187c036a0300316402d400070000301040d401d0018 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 212704928 1250 212703678 212703683
    0x30507021515010c06050c09030d020d05250c0f1703090303090402160605010b040510020a0c0e070516050c040506180705070f0b070e03010c05070203070b070302120412020a050906010804 82
    0x24121800c07602c0c0120346216420401400720740c07401003400286040c40c80101020002542200e00c0105280022659440304400c81000140e00f400700480c2888990510b06401482c1464050b4141d419111310907417224503440040d1400c00c1c0d800c01c00c2015006104140345002d5080618241240c1401191f04c0b44100f0400303d1056a00251540103c10200c47c0702003901d8005a0801c890b68440c0900b403020f80c024064140b08240f00428032100030720000340a8401d40d84580341041051424034008003001000d0040014004240110a0900500c0d9445000c2d24068002400540380c05001e00088a00c0500058015040f08000203a0100c100c0c140c25044040351602660358440d038149080b542100c414028408ac50a900340041958401c85000312400120020840d400e030031a4286d400d441900c10094140e003244030300b080080201d00288c001c0c1c9000340143d80840b1a41958003c903940035400250310100740108000c103509150407494003600d0107032160416410280000380c04000020b000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 212706178 1250 212704928 212704951
    0xb04060203070207080d021014010617070504050618210a031103190305060117060a03140c060c0a140a1509060902091003021c0c05010f111c0305070215 67
    0x200310640d01c00c01a07213005001c2078090300c10030243c4490094403000800c40f86414641840d00c80e0101590b00d02c5000e04070f41541d21601e203c8100d140200414941c024044428084207000014170758884c94000c0ca48540899204041d5210b0350041040c50152081d89680540b078032613a40038109400107690071724581504106880d003032045c85040c50b510856030b0190a001e42c00440c0c00c1c4194040c1c010314080c040076240c801c0d10741139001c4038541c004401c0ba0500e6009030783c49010008140003180001040b211312040d10340700c0090341d001c070300554030848c0ca480b22a400000d154083c484000c85128003213407c1c1e009020b0003c0c40c0c0c0c03103024001314504590b80000382c0c1e842c0ea6004100e1584d2109a0f81940604200c0340303031419044000e8010490304c002e9000c1d02d0b60b44182415100990388a42c409640511440219407d0000440d80680d50080c1e107021303c105942401d001640410010960800d2074203805600c0403040c1c0000c01341c0d04094909001d540c0720301030b52540034014070404c65020110856 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 212707428 1250 212706178 212706181
    0x3010312051b10020304201e011803050d0f031505040e0c03010e03030709080307080711011112030103110402032509030b0c0307140f04050f040e19120207030b04060203 74
    0x480c41c0e4081200c0100b22080c8101c40c0070300864409074014610a5028900181008080400400a0305034000055500c8800c18501c0d59110500742880381b26407a040c5898a48164049411080c8401d01e4100703a0309640208116486158408240380720080a8a014009102034003402401380d1880e0042e54400c5031640240c18182074100f06994800100900a01000310609101c070b0f1a81e10540b501400909617030004101e00c2d20000c12101a40e610810b070b245082580e0f1150340b5080c020041d100c3c1048140e21852180c40010003501058603011001c40e036030303949940707498440d002c1101c00e2503000c0d0340180b0411259850f00800b0301080084400004403906040400300c0340c415054000030800c00c025014130240044000c0034610549084d119070b10005403e01c80ca1003140140c0c4402c4030807440810042c4000d042c22a005100c0410103000481c0317505407444900c0c20f181c10382c50545001e28404a4410501141c03006030b0042c100c031400a02044e41c00c41d11900b410b898028005044141c0010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 212708678 1250 212707428 212707447
    0xb041211130f050103020a0501020a0b0a0203101206020d050f010e070c240b09070311030714070c0b090a1e0b03090a0506100305060114060304060b030c270a020301031205 75
    0x4041140341c0d004031010841400810140d0004107820b000580c0a10a04a80401d0f15400001d4221030306402c54070094107542d40c0340c0400c02030360008010444070300010800140100a4560020300c49201c0d140140c0c586000c410301e4000c03940300401e104444030305a401000264041c002158002805180845502845e4200000d01c0199556031402401d080b00701c01016140581c06600284030450f43c407281611002822801c0d28110008062014001c1020840b0b61b8054100484910401901c0302d00340a12910307103507880d000a0f8001401740350005102140c525200d11782c84041d0120040b0500841c00b03c0401940d5000c0501810b03c0303250f000008941000c50410541040340d5002c012610340f0b00d4456070183c0d442040d440111740d01c2c4660340c0042003030480012681d40c090030182079241142e480b40c407040003800800040c15011b0045102d1030105454101c000811b0313003050740c00d1406010500520104c010b100408000409105000500002d20444203081140405281c0243c4400059 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 212709928 1250 212708678 212708689
    0xe01110a02060d020d1a030304060c0c030606060306050102010f0c0f2006100302010824091f1502120301031211030f031f1401120c1808160b041211 65
    0x8400182d40024007040c8000340488603001410403501e61241440400f003040e030b107400c1400c006a111513040d0814803041c09050310a88031401014041d011820744180e0301d840d03c0c81104c407141c200c5000a0740341c0200344102d580901404624205140c0300700010455044010301421940ca4200104110010120b0705c60300404107004010300094145d414905140a010000c034031244404c9001c54001030018465038607640c5e800c00722030b6840c01c2d00d030918900300301080441000245000d00005810494003490000080b0b01c8004c0c0c031040d031400b030240080001c06498003030350844103d60f03a601080148006481455000d01480190810025217144d030035426085005401644815103008402c011188016005000840c08403614240300c5075118980c0300420610b20000d00c0c00f1519561f909040c0030010b60109070f0341c82c20b0703203440d00c0045600000001010110b0b4080f98042d03002248840c880c0c480c110b0a100144025240703039150510f01a04426142a4540007a04000160b213908905841d034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 212711178 1250 212709928 212709943
    0x608070210020f070c09060911070807080313060513031e0509040c030204031a01050414060f120c0409050309040c030b0916020102040f18050f0601122a0504080114070e0111 76
    0x2e01c00d8004e4031b4803020303001c00a2203a8807a0b44000790600c203000d0001a061403c03505085e0b0000130091030451313640ca68010341c0c2e20140a0382000c0c84d403d440030300451603520440b4042c50300e00ba09c11251400310304000f000c0d440d03e082446610641c084090001c01c1c0c0003404c40e106140180c0d030100b0302c4210300b142503000740110b5002401c51700004424141020790840c405040c0c4e0011070701005980c0400d080c15415a0084602903000f4051644020541c0b83c0043e0f40000c840c041c204448160344100085001d8440200040fa400d602c041a042c44038030381406403243c41401380c5000c2201a0030900040c0d0942c1700900402c0255882610b0340000500c00e4044a0142260092003084280d48084c200b95958441010394905403800d400b081c01d80302d0140702c8a02441e0140d5520044481c840303210002048080c00c03084040141540301c0c907103000d9195085803184003644980c1d4071280b4102015003903540c800881c018403a2080d08000c81650029441091200d003071030810741c580401c00c9041d01c0c0090 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 212712428 1250 212711178 212711183
    0xa15120522081b19020d0f1202012a0215101e03110a05030303071214090303040c08010915050915241512072106030b010608070210020f07 61
    0x4007a1060140144400100070000f1a0700c0c214250714154480c0303079240e00c01030100280440250703820002501c0d100384001c81841c00351401c807014000c17503919001503066110407000540d458507012a2a68401c003001c042c10201e8000680400554100c001d4403501140a54403400075180c0219024445180014000c0c003403000002c11415007070444800760221a2008441801c0d0f043c501d60181e080c81e84801040714809002503085803030304c0c2c409030380403201c1c413a4240c8015940c0c540c4bc01c40d80ca451841501403224035016655a040a082ca1032000e003550b00100c110740c0c103100360b50340002c3c40e104544451200000c0005216101c078000d80d810b020990301d10201c003081400900c140b1500320204c4010107141d030150015160b04000521818542c00442d0502c0c291061001c010490ba0b1b4801e61584086240b8184078034020301c12000a90b85541082101100c1e51801c042c010000e4050000b400f60045041005039403401d0351000b940c0713008201c0081443d80d0003065100559003130310161448a039 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 212713678 1250 212712428 212712481
    0x2030a080a050d0c170a15060e01020c13050703110f0702040b010512090c0909010605030a110a0503060a0e010c030212160905031002030411040203010f06230304060b0a151205 77
    0x40d0742c8100420488440340a5204505481c0104586812510580d4400c5912203007c0d0390051900c2419a80c014221080a055015003180580503a031408455804555200ba00060a041c0244020219028406110790058081141e00e500c40e1040060f00d10740f40d811100891081718404c01220035002d03c211b0011000c40c00000e0108072000420404441281078514000130380e644502c090984003075100326501508520243e5000c00c40580081002d45405441d96903840d82da0b0022074074140080b10001d03049a5911840003140030207005564030300d19240380550a045142c0d0007041040c0000d421749000c00088550299401d01452442002300300003429240c155a50000503400b943c030031101103401280710024592149424420380e416103a079911203540141c10f02c0002e441200c08200c0c01280b83e0fa41070020054407085100a500c0385204100c00b0030258445428080b5060071904680f24dc500703202526141903a00030590508400624000700d9035446040794440c3d00015945a4001c04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 212714928 1250 212713678 212713691
    0xc0711040203070206090111040f0e04080c25060e06030c070203010905061503060a0501030807020d03030e0a0809010f02011a240a170f040f080a030f091b0b030402030a080a050d 78
    0x80d4002c0f4800c0e100d038510706e0091080440c8038101c0c1605200b54052100b100280603c140410010200e0666116100b13341301403030414241c94441c54407100d4003400b40c0051154640203588011203c00e03600a0102e41085042100c40b4000255a0300000b0201d0f1080c840100740311040d50783c00d4004450f0303070f90042c040d22964100741c0340001c00a140c1d040e00d14001c0c421000840c0c1102c8503031145034100c030b0300900c51740e080000c9a03003001000c00c07500c54154201030702c0e10b541d030012880a000c41d20707405115021881c2d540144078005030522a00c0e541c00825645424500081ca1201704014582035000321030848a03200300d401048003540e008a2000011000405d21741c0c4801d401162207401c2d01c1d003020f204001035680404400240b1011200182900d2040d1801800566614080e0040c0b4146083c00700d801c002135001039089450780001960b0345c154a6070428202c0a100c3d0841002e0321089401c03070724514094001c65a00c1c0301c171510007401c3c1640003450140d064071490548489182c580780c28801d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 212716178 1250 212714928 212714941
    0x1d010c02190803041707080607030207030512090d080a0203060d060209030f010f0504051504050d080709030f0f1104020f1606060f080307050606011d010f1e0201051510080c0711040203 81
    0x100c0e001170003600051a2501c180c070369080780005a00d021034480314007c155955920708110041c2d080703c4011014400144000760702c6400c4021407510492903d001400c0700400501c0040800102410210040344100103014041d228222205183c0d0741240b070150f65145150042451f16001c1020315600e0b518168000c8503490043d00803034011400380f070840726201e14a00c5c84100500c4280c41c000d025500840c81051070b14092160198064101d04100300c10380d9894464410390b028108040b1101110401c0303540410011a003440c00702c85056508500f481c02440544801d4800c207006620380302030b11a0b64008200c90784d00204003400c3c8026200c2c030072a664441859a0790044a42102c15000e100e00082c15075201b0100b80e10098000f40340002c00080150042d500744401803141010802e01c154010b01c03112080d4104a0080841e5000184514220a54114200f011400320f807080445204041d00c065009950b5900b00344000304250780d0300d01c02e103000720386a12030000060300f15001004000300e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 212717428 1250 212716178 212716183
    0x406051e0625140c01021b0604090f050a1a010c06090501020c120a0e060f0301170c1e12120a081003120e03100506150f13120c061d010c021908 63
    0x4982d22445681c003401c3c1686460b207403900d0002e071240d40143c1c008101000f501c181c0310044014600064401e600c2d26442e55084c3c000d07680307030105001c4000c0d1100c042c000d441d40e0340e1103091580b100443c0c0403902541210002042d54001d200040c100944071301482050203c05e604464800b10213608a401d070000302c10403818940c0100d00c050340410340700c1c070504203141403a504a5404842041b41c0c070746940c3c00c04030050040c0c0c00300002003500b0310070303201042100c2e00c9240d001000d0480405903010031010303040c2008100c903030402070012241c2041095042d110582015109400c20340d040030b2040d503948029020b0000a03aa101407c500901503603600c1d19a0805505030880e9019030681c1c0c14020441000700c1175500030358603203402c240c00b130811003021104000640202c900b800e0301c091800443c50300b0030300c0f140d805030481c410400841804908100c00e01d0342a03001000d403810400a11301420982c00c460301d00d04050f26041c401e41c0c4603d58215a2890001c4003050040c0c80c4074440342d5201d40c0030300e5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 212718678 1250 212717428 212717497
    0x619030804060525051e01291011030313032102040f09020c060402040504020111070e070f0e0a0b0a0e040906020a0f110c19050301090b071209080f1b0607020d02010b0406051e06 78
    0x80c01a0640300221271220310035804401c0c0c8107180d9005501d50b841d109120000b07000b6a400950400400354203a203001e0a101650641320b244010000d0713191414020083d8416009501001c8403510400c0080d9a099011410550107601100d000580b07560398001a900c100718072200d100d003401000004552400d8181446015000c0340d0b640d0b110405480c1c0d0203803000001c0c0130303085901c00c0100c1400c00c2010030080090036681e0042c500f60700c40107900000b140c280c030310580e0121125600030070030400683c0d0141e880405900240b034a0183d40100e20506d940720f41002800a001c0d034000e24003040c000c150305602c8401448003070001c1101e0012801c1c01c442c013520036120b400c0010804c101240f907041550080c0c3c40c003a43c114000c180781001c018400c11880c0c1c0020352603400701d140184003200c1b20405010301c43c07080a00350090240607030035a40c0282102d40b9010451321907490441d0500c042c3e2604c1d00e070000340625228402c2041e803040400558540524443c02210b240d281e0400324541d46081c0525 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 212719928 1250 212718678 212718761
    0x1090b0403080723070b090309060d02071109010e0a0c0e06030702010b0108010f2303190f0b24060a0c0213060501180305060619030804060525051e01 66
    0x2d080f880c8043c00c80d110440200f0094059075005d00c00b64020408003520705400c50b41c42400c43c4d1904010b107002c10541d40201c20301031240c0b1750200c0c141d4203200d1015880d00d42000111800c80d80c660418141c0c459401018000d03110302952154214800c42c00351400d5840700f0002030040341c90380341c481e40080c00380c034040d43c2e5a800202130100005400411942001c1a43d9002d02000c0400d074480c40d40d06d0b4200c0700004010b0381403042090743c524500361561071442240c00385019900303240050134000d0311070301c000d40410030704c040c1c002d14180d06c1140808181e442003811039800f1ba640d9172000b011140c40c901e03100082e6101401c2d41c0d08441c4511690b00180c00ca48003a00d54104200d4040c000e03000650251001030500d40044000032081d283c01609003803075104121005d0b03c66a12503c0342c402a8019801c82d40c0418000980c80d0641c90706401550389010b0011030309808412655207841d114208681c00428401900c81c09035100301d000c3d040000c2c458809502e840b0100a45d8804a4401c2c1c40301656 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 212721178 1250 212719928 212719937
    0x27030206030c031e0402090613091502030f1f060f0507230c0607020603070c03090801050f060109090b030703030327060f0c050c0a15020c160303261801090b04030807 73
    0x24042c04041486080d05c51030f002029600355a4460702400030f0800d407001c4907e08155500403981c00a20340a403050604560040016142e10f08001e854032000d8024000c80060f074003031003090310080030102e00501500c0140c500414460382103d0300390790380c2c0038050340141503a10641a8110751948070764000b190032010822104201c5002003070284520a9800203074203d201003000403840c500582940905620916166070416501c0b562603084590a40f400e401001040c0280300c120b680c4400c040010302654802080245da600c800a996a07004d0303c4010203050b11903801c40c061125060315813094004502a1f941309820624050000704161300000421074648900d08000034420003c3d036a907607200d44002c2109000301d4640321641d40d01c40c1c2c05d010405400304406007450105010101c4846520f520000382c03c0d0a51601415849003441c942040c0501181c070821200003840030260040e50610301c0c1400e52040c080326901402c007450000d02503003081c40501c000c142c1c0c4078420f20b10030040c0c2c1e0749 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 212722428 1250 212721178 212721211
    0x40218060c210406092603033c19021e09030d0c0c060507020411040311010f020f07060c0c08060c070605060d0c090b010905040507091802030727030206030c03 70
    0x46000d50086015040000e070b0917001c248000b81001c0e1a54200880380e0144078501d004039181145035600c12120003071040d01c60003662031048800d560701a024400083c00d890340300b0504814006400c001803070301c04056141600d45581062a0741250801e03026001402a107001c80b070150080c136400754a0340b6000303114000503800d01ca4403540d0098241644040ca0840d8640b52501c119103035006100300341e0b44250386500c0051000760381030083c0015407040800012610008002403c4c411500c840801503400010252041c001c0c04507030f0106603076880c00c02c40f40091013810305030500c1c0010342020500f0b10610040c0228500084050100c561080c00140500e0382d40c1020b04c026820000340081600340c29981c20711135a0041d81060780e0072101803511b200d00380c1e40c03580000e094500aa80c42000314400103824000580c0c0c1c0daa01c00700c10403003094150724608103414001c000703c203402e02e43c3e4031030031001661901c10000322704d00c0001150010f00701a140e0505c40d102006591040d1440e040080d0500e6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 212723678 1250 212722428 212722483
    0xa0807060c03081b0702090a02090a030b0402041404030f0c0c0806010e01050907020307210c060903031a0a14101101060b04060314071713020301050c09030f0714040218060c 76
    0x11480f074400c0300c078102d01c4c5041501e2907082c42022a00a030034038211503004c1c00042c3d1541c49080c0e120001f5809141031078214185801413001712512a0309105107068843c0810000c00e8201c035020f40780b05114907103804901007505103000080740e04d03040701e151401040c3c00050034031150b030401e0f030680fa8100c0f000f20254031550410382e540d00c83d020000b403076062101c107807c03108414011082524081420300c0842941c8603540c41040f50042441100800da4840d0b03030209502101004400341c0c6020307036140b0041c40c10103001e0801a80c00034492441841040b014902080c0b040020b10f508005c154000d002c3d09889444151f1150868001e860009240900c01c0c0c13000403032409094025001d94481044039480392881114058008084501c1000000c08600c0144c509114851003a8082d0503405d44130060001054144801c048241e25968011034045c4059403540c100e0001c4508119030041c3e44080d1100d810140c10b04260503680c2c0080089207c9584d201c0201e1225010000340d00c40300c480c074201e003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 212724928 1250 212723678 212723701
    0x602071106040e01150908150a060909020d0605040204021b0d0e0103020f0a030b1207120605090c01170601030f0e03120f0c0912070308070804090506030705100302090a0807060c0308 80
    0x144600380e407100e403400040210078059100da4903179030368038507044002903102e4101c01c1c913059041443c40d130812030314030411041042034842c000142207059020b0040c504e0580010724003601029001e42001c0e691008182103540d10f50489151094404a90b442482c0d95416142c0700e8822201d46c1d00400d209036180030341c0f5840b9108030740020b030740c40032181e0500020481c120010402c00c0b83c00c1e40c20915007402103441046c20044000100203101c0c802202000c80d14005041d200041c0c00051130354030003204021182e80003550100080010780c1d076200642e580200490107450001502804e0501c1d08000681c0900c0c08030040460600000034030b1419290081e40300000c1c0d0084440c80440a0705100304d41d00b5180088404158900c5901111107291310307a1100c504540c00718104440c0303194001810030101405015a903031200f0124042e14019140c08007140c145401080c5020401d030340003c2c0059142e4401025401405544007201c2000303864543c00b07081c1c07034019601600425000000a1000c0e03100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 212726178 1250 212724928 212724937
    0x30507030227032505030106080a030207051c0f030504050f010f1413030506070c150203060105030a1d0706110114090706050a1205070f090803070f0b0a060e040602071106 75
    0x810030182d00300d400c0b0741900b22202070110b0681e5418041c1c0d01c2140a003003862901006000304040488070043e251208050031146107078440d00311600544800c1011980204800d000c40c0d2065502900c480b02e040e14140822803c0c40c8020001280ca4012100b407681c45000390080e0343c820b075420000e440365a801541c28800c40d106803400110510a0351403529541c4000d40801901c6030301821003507031240d83d002c0c1454030417038404000940281c100c10501145100d07042c181d0000c07440451075801d100c0c00080c05c5100080c41100c90756100c5c20b6041030050b5129043c42206010416188425262400204100e400702c0e5508450360820042d48800c0184e58100350040c20350000800400f807400300107030781581056010a081c01100303410414981003a000301403045050342da80081204030210060000412500b12003142c3c0d00600000300040c40c200f090302c0b02e00703811100d00c0c0190783d16410b051000d0f180c250080315105908005110800c1840d80141c00f1041c801c01600707074032442007018010540038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 212727428 1250 212726178 212726197
    0xc080a0e0714060906070f0512031506030601121a040509010b0f040b03010e0d020610360f1103040c08030307050a0309033b01080106020304030602031306060f060305070302 76
    0xc4804000b4140a1405880a128042c00003414440d01030001186504030031000d4802d2102008148104442840012940166000002d09504010740e40e4074071030074003d0768940a1800040400e500ea8050000e4450000c400c00d000d010080d9060a8002524440b400690060741801e0118541d4401801440c10110000d08450343c0320705107034204409041d684140a406558035500203482d6801400700502c40092a002070401d407c080c1e034242402c1c600f5a110082000c3d03075512003855103480c0308110f0f81c6052031744042c0035494088042807009041f00c10250090714507021070704500407203c40c05184214003035044a02001d07a03030100c550701ca1000320340c0d02c400a582006080480307400f95011081d15030081c80c0194040d5415207200001c04000c45000842c1c4020a4065001c201d51000c1c04610b00c60038680015076501d00726001c1d41d07a01450000601c150340100014031120100c0f039000c50f0064104106000300c5035100013403e04407544c0d00a100009041000250b82d090003802110320000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 212728678 1250 212727428 212727433
    0xd20030601050f13020d0605060c07060f0201020403030f050d0e01050709060207050603310803040809120c060306040f0e1002040e09070e0103060b130c0519080105090c0f1902010c080a0e 82
    0x21300c80900000c3d480304962248140e0340d030401240a441d120080c008480c502c0d0010102c0038104140030b400900110700304404c5a004000500000340c4c05139001c6a910120704140f034547c0c00f590306041c0a408250800022507180070704209403640d00900c0542211415002c0d03807442ea45030418003c462000b2198106180029141e20f60816660040080540c0c54004009182d0406559030700341c0390702c00d48081e1450040415026100e10b010504106000e103004010716078400424007244640c00010601e6200d01d40c3ca90302c5e142c0345100c54010385211984001039400e00007820018500035005130050350004200000020340c043e0b80020300380c060b00c07480a41c1c51626880c584e5581c020303000e65106590051100d00180d090100ea074090804400100c5c0c8815845501caa846400624900d10b041c500b00300d4120010080d13a103c010019801047d480102c66941101c4101800c080c4191050006000142c1d281c40b0072541e810342c4003400c40b80700d6035100c51481d150010b1580075544075801c5884c1d00e8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 212729928 1250 212728678 212728699
    0x60b0a0905160806010203211b0c06040b0903070b0f01030311070e1b120f190b01120902010315060c05070e070203090f030c0604180e0d050412020d20030601050f 71
    0x2c50240e10030715030010052045030f2030400b00383c9100310b102281c400300003195080c40040c4944001c4078030103081e620010a00040c05d003036000d41d2450307a548020340040d01c0070101f1004600402d02c10300445501980006420a1900b8212140c00141c5004d200c00e40000d440002404040800803c0020840d81d8620f03014189440358109212100341c0a012001c41e0300c42048544145070030309414620494030494804171525042e18401300c812041b0a0864001d03141108003155a80c001c800540d0b110080940099001914401070b0700074034450b482e00f030140c481e000c80058140d41c041e80d6240102e1140040d1002c6e00d55a1309240000402610300f100940c0061041d407980b405c003a0900d50802038010110b640450404010a2180c0d02c9600502281d001040d881c0c85200140d020319900f41480324000c2040c6221407800400f203020314010421040c1c0b41d44411015581c034a2041c8403401c1d044001c400300040f5440100404120301d0381d042e8042c1c0514800000c045c501411201301009000c2c02e0002d48 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 212731178 1250 212729928 212729971
    0xa0302070314030c120901051c0e0111090d060504080f040312110a081c060e070302070606051c0807141b01180501080106053402090a1104030b070318060b0a0905 71
    0x5a42015206d941000300500c103079000b6881c00100310040809810000800594090700c050954035454454084107204010f488800c0d12151122280d90703821100c0020300e070700c4a01c2d1005461143d1320302440030500200d004418004840710050612001d0349801c0383c0200342190b860789038043c079400603040320740c24421084003080c1c1003041504407820400014500d83c407404541866441a40c42c140001d42c0441d401e020070142d0311406001c0c1400b01c2d1340090600c1c000c00a100302d03801184004103100030104000c4e04008981180c030840c4102c003802ea85895250345015500d10000e004280e0000e101c1182540105641190400540d601a922010980c0c205002500c007a8041e409090881c01c1c904c0c0d0910441d0040b14031440701c07004d405c1a1110b1000b0314010031029100141090b40303800e143c900e034a06081d000f2000c58045941c4000b0540040e6552030040d402468030310403d958001e101a0480100010340e4000d04885800b1110340301c200782c81d0600300742118000c880001c2c01d083d0350404d411702e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 212732428 1250 212731178 212731213
    0x901030b06120a050c100306080303161b0609021507120f0917031b0609030d111b0d080702010c36090c02010606031a0108040606080a0302070314030c 66
    0x601c0a80500050464801c070060607190692000c41078600b40c100d2140349806203400009007480d088149803d02520342000492903d910001d0014038031808044202c1a180c0c2c0101480c440c106400c20b80802d0251660400e400500b40300c1c2c1c1c0c12803080600c0343d500e01e419402801903422182d00285c10540c110100401035900420b584001c0e818096040b00c00943e100e1480c00f650103d00c09100990780b40c59002414400c0b00d01c00c5040d4090356004541002145d100000540b1401c000000000c1400303c040c40c144005446911000041e050788440c00300055040001c00880e0f485556032488802c0e03a504004031308a4a81841074000919003da0f03445500c000350040e61108546c402074a2030740c4400700364040c4401c62580c0720318142c035152210020b0700354082c03180700020801030806100751456050f0b404003102140c10b41a05000e4803001050030302449602c018060300d205000c4a11000e05420083c2d9a9000c521084075181e00018401c000e5140c00300541e0044a49000140381001160752003d2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 212733678 1250 212732428 212732431
    0x4080c0411030a05100f03030201090605010509040b0c13090e01020c0c01020325061803171003020604060315210c24080403020c0a12020316140f0a080105010e061201050103020901030b 81
    0x5031714501c00c100c04203d01076002403a100443c03280c1c00021300c6020314030b0200107580050303100350b00ca00c888004100110300b041d101190f010700060001c0b569024100006e1103070648640140441c50300e00b8030300b9418980b05500031304041060724111030090700000300490762441541d14bc20f0f907046025404034044856001201d280c90300c59800890401201c1943c413601c0c800322241078001818a00e01c40064003905000c4680041c0314079280007880e421a004030b1040d120f544103000405a80b500c3c2c0c03c503010a0030401901400043c01000c00800380d01c2110031002200308401c0d2804000f42d000000c07074500c458003c001c0551460402017041254010547d421703400248140d055024040c031071a031950b40c003803d81020700680211f081030060310f4010b03d0700d8500740c1044404a011400da081c01010038502c24903907034800c116503020300c0c500d0100100700c0302d5805901a071015070170301002160540c90122018400e01c07066580008a042400340c2d0707820307101c0070322010390400e0000d40140086010120b07c02d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 212734928 1250 212733678 212733691
    0xa150611010b040203040c2303030304020607061b020102040f060219060e070b0d0504210806090619031101140a0c15021b0601080615010801050f010c08030c04080c0411030a05 77
    0x101090b00c2000300e01641c2c4115805c82c0c18428010f02401512141a01844c0707a00030845440c0b03c5205d403d01190303880c4000382003c0d2040c2c1c0045090000c22801c3d810509040000804448a941007148040d010f5003043c01002c18081c181e40021a4203031000032003940110360078807032200d80744964480704028500e56020101c00e010710800070600c1c105440050a03100c451407400125031401e41409213080c4291220b071142240c1146404544a62191410b138011104481e0340e0004d0b1660800120076459221011a0321031a81c0b88c000700740061010f01640c120401e0725442c404030b09561412084c1c0c0704180c2800d0204071180523900205606101084410810340001440d02004080b0f107a0340415041802075a0fa0182d40140002038050100c0d640200000030303a0003803807200c040081c4c0040c5d0140112409003e400510a04680c4900701410049403c88001c03070350380c1804181d45009502502428419114410a2800b0390038140304902148070681012425070701e8410440015040103810b6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 212736178 1250 212734928 212734931
    0x4030b090c06041401261807080a03050c07050102070806010e0c04030c1e05010905030d1d0405130302060702060705220b041e0504050603120d06031b030b0a15061101 73
    0x40d0710a03612400300900140c25800411030100101c04001058403000038141c0d512901440e50310400d0000c200e4030960024030018820300c1c5801d1031000c852500301d482c2e00c5101c862040e030380ca10050681207802003408009840c01d541c030340f0340c1741c000590356142e0b2072060712110360042c0010000700c4080c13038140381c01ca414035a0032847c0a6498569442d151525080343c0700d100c03151480304802e031084041c0d000042a083c280241d2092a001c002030300d440060b9204001c0c4490901c0311062082d0352250110302d030ba4001e2041200b4109450341035a034104416048025101e204085030003180001030051080070103a4429140801c4015030122100505101d00c05e601618071000c90300b994035001800144c40e08080001da1010710401c9484105c09039488940594980f105104058402081e54415015110016a030382c1d0f00011401c4000c090303903400075001e54100b4507000500b14410415108a038001d8070741207036a88402e120042142c0d21a6900d41880d00304240800605004200c000c400c000542c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 212737428 1250 212736178 212736193
    0x7030e060d0b03070905010608060904030906030b01030b120d090902070506160203160b07020c01050705030a082701020a11012306060403052b09030b0408160204020c10051302030304030b09 83
    0x3ca0302e03042c8a07401040d520364880f4014052241d10254050b4021702c211100510350030f0544014007116800d01402c020561140041c090b240d000360400084290301900004440149480d000d071548104111000011400200003400340c0e414000c1e141b110380c02070080e0200b07444e0701807110700f801d0385222400c0030b5000512800b0400c42c80e200c054014680160182002845c00840090401d11040307030350750510a092241c000807071b00000a540c074034410342c2400211900ca210000d4413111005000d14202d108030000400d2918041d00070f0701d00c038020358481b00788001d40104000e00744c610b591042260316070200f0202c1410f4541d80321b9650031103000341c002850b2035204d0312500d04040300001300a03240c90440c40c0c0386800201d422406100b81d82103150600103141541d84a40802201420180040c0ca011641140007103d100c0c204401d0b03039000f48110340e10310101d045552503846100d00c841c45245000001202e01d052941074101040d801000755180904542d502841139101402800d07141c400d008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 212738678 1250 212737428 212737451
    0x5072a09020a09030c06020f06041407080d02030d050705030603030d1d01021b060906010b0f0310230a050418030809010204030c0e0f0c0915070318060507140307030e060d 75
    0x802840e100030300f50fa4844040e404c43c20f054a4128082d8091000c66102883c1840400c0001c581d087c1c0103607103c04c580040c0d03111103100c1840d10000b50800700150142100c488001d680010041c6a101940358040c44140e541c1181915140811207941d030b05a0001c21032109000050350000291740322201040d07000301c848210183c2281c11041d06807030b000c015490034001d40700302000017036407181c45180205803541c1030860020960203080d803e14008507000c004201c0604600d4040009040ba190000c90341d10210103459111301c404002940c029001100041142e0915015803040302104070425514200300e9035086401d000c006000002da958280310110002e83d6000c13907500205100078410500f03007420742140314406805820020416030410600f00541ca401c00440c404548101c4269150a400c4c202690701d002420302c02940c0114a61002c182250051701400f0054000d1440311454005030300c02d60780e02d102d07a000150110742d100c60b9201e501d280c9030009001107000d02c600401c006450741d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 212739928 1250 212738678 212738681
    0x3060e01080f0105010e0c0412030c1a0109051003110126040503070218011202060a03200d0c0206190e03070b010617090c01080402040507020c06040b04090c05072a09 73
    0x781c1001a85401005542184503000d001c0c181c090000d00c03002100e02d080108000140d4403640c49800b00291000109070245400f9005c2d04034043d411542c5880030345000b10817022851000d0107544009031034000402d00c8020b2500803141a250301c14502d10303080d141c61005403288030141c4071100e244c0c0410706a40209054410245010f82e20860081d41c80302054810441024247c4510104448580c030040115001000383d900320140c0540d40c0e255511855007003140640f1040030028002c2c0b000c00c548100c0660040c0007458a540a41d10401100000c0001240c5410095441c050180700c0103852046c509441d9102034030346000310085a103080348541d07881d1fa5558091b440400417400340b0f00c0c0c2020450700c821102d80e010115501a00b401c00c1440006806c0a901030b20190003299240001640103008100b4012503900040c07129481da555072030200e20a500500410207520300b02070894900d18010b109039070103d64002e0070300324502019049944182642050f026002e0014100001c811459 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 212741178 1250 212739928 212739931
    0x20f04080f0703060c0804110d0602090405040c080f010606140c030c0a03050a03050f0103031d03070f030b04200102030d0b040204030209070302090907021207021c081908010603090f02010f03060e 86
    0x80e6406010b80e54035500f80401102c10380309100081c0080345013000009400140031040b010702c116170151b500400b9080440090140007a010740007481d2a080c0414001c1c59104003084400b81d50468050703144c0114014241d4240d4484c00010071a03509013264000f640c3c1c4041c14440c10101c042300d0520b00e0340355120380f91411211055021450000e814801d15a050107410381c48101680000b215514569004004800c07905010100c069021803504a60b5401e110310001094940108041d060300d82c200302c200a541594100c3d20449a0002d05103462500f804448002005130051410540001c0342d800c00f8140d510340003507000381d08000110050351040c00e0203018207150303940140c07034103120f07000e102c1c16881c041d04401c255842488800a4503207036800300c620b40399041d603600c2c4594145054110041000c564020400c0402284c2c00320800301d000210342000c800c070b994030041a66515003e800711038980c0c0c0c020388410035204940340594007a00d09038241051618002590741e81d038200030541c9090 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 212742428 1250 212741178 212741203
    0xc05150c030a05010f18090c1e090f090515190c05180a0e010b0702060405030d0e090a0605090a0207081204061a09060f040e070803030406090605090c010210020f0408 73
    0x200070040c0088290948a40303400b400504a1088586041201c000c22403680680d405801a81f121801c0080004000b04000100800320f503520400c010040c41080540c1039018030614140390003090300f40c80615000b0b010040c0d4001003d490030110000c0344c0301c1e40d4600140741300c00145007001082440001813182c10100b890940c2c4540c1c842090030440013040f00c41011413480b51024510034003003901c510060504407401d031034601e551440c1c90310128095010b55070102c1e0340340c010b8180016100b600891000046101101d0300c040b0740c0c0d21a54200212200c80c000e064100131000300042c2611029402025540d0103051002d007856010440a9002481100d08603030042d1943c51088040c00c0c45034903550401c40840714441070340750010201f00e5a1321350400c1a480b45444500d031400b4000244102405000210203880e03407480c0604000000d001d41c05402c95000d0314020010f01400000701d035000300e108050b8007408541d03801c0c50042d0065040038200040201c01080005240b4104010105503840c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 212743678 1250 212742428 212742451
    0x90209010b0c0f0327010206040b0606090a23090610020304050105070201090512101a0303071209050307032604030b060d020a170a050f0a0503120a1413020f011b030c0515 75
    0x43d102d101c68030760017569081450540d03200078244000a84e80c2c00201d07078414415103446403184070b5000002d001c414070303902400f080e201460380b111010180110100d5014820b80d0343c0b03511611003400b842449400ca041c114010b80003480188400d61081d00100040e9005140c04550300d900c9038001204011024044e400e950702034a0f012250b1800c6001d641c4141401050400e00081d000020a4481c490313000010600d0391340011000c0e0300f0740904400c5024003005030455000d591245068800030740070b102c0e480c2c3c400fa07800c66000c04201e9008221010380e1b6000003145580d072070b0001489100c0401d07070000c9900144044021401010304200c180360b00c0c5408004005240250824600344034901c203488403e50000e4900e03801090300007048400002910102504036901c841c10031008090700103403000040c1501080c4032220080d0855400e1881c000c0310b013200300c1c3c0c0d501d000646008210380e00c80d41c150b040d078880400100b4010000e504001d0300072400e603904c0000e041c0c419010040100d80f400303000b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 212744928 1250 212743678 212743717
    0x215070201081503120309010204080f0d0201060509070c020d050a170918010f06120b10030903080618011a07050f03040e09120409052e05030c0103090209010b0c0f03 73
    0x641e400b0000039000180809042c1d121003091022907180d1110904d00c3c01c400ca000004501e0042c1e095045400401a6000703070707044100314190180d12055043c1c00c0800560070440040340714a031004c442402040d041e1540080c07200282e0074000290040340d1305640034050282110b01080007640d2080b807004000100607681c0441e0070030019882c130031021100300030402000612000f80c5100040050b19003d0400d01a036601c0d158804000d085042601600800d055031846e46041d01504aaa216071298a64118a6680200788030780c02c000004800d0806445000400103401c5d000350f01303000c50345444280c51400c0c0064854900d00010b0170740000c5958400113040100c01c030054101604180c3c800007030092500d102c40340f80c0c00c80c09540159103046954201080c003400c030018801c00c521144105040f180183c2891031124007103e48101c80c040d0003807464821032580300c0d00c00c401d14540c0c0207001c10310716401c0c00f500d15000e0b00448070180c0b01d8410311707001103051001000500120708180000c3d0081 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 212746178 1250 212744928 212744933
    0x1d0a0c1e05041805062809060b130b1305010e04020d2901020307033c0305071b050307060906020f0301270e0303040b0c1b060105090903070b0103060c03020403021507 73
    0x70390100b4842c2a200346000113200d910b56030400760300182104215010106c04a90814030741d0200e5a52100c401075250203c00181e00d04081e0190407030070414508620071726540c02e0f51220381d124104071364440142e0303440140102d600800840c2c02e000f402500050811106030050030440d889a01c00c10040c0014901d25901e542c00801c42980e028001e20207141400b10590300688034245031022200b020ba21a031140d00003400c1c0401c000900c20000c1c0c000541802201c002400401c030a41c0d9000024035505600c441c85c00c1c8541c81440030950109c004c500d44940c1c0c0c0c60301d10041250340400c4890507000c1140101046640002d54042c080b19100070040c0c6440b596050001441d03103004005160030400c00300a6000084140c90b03005800455914007035075140c00a1280d0711403400300c0b00d640500c41c1020039203880300140d1981610010340c1d4003c0c3d0b40c0c80d8948400d80d28000d1309070080400003141d0060001541640050710021003504016003010340340e900081815034803007800382903000c0203e210b006 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 212747428 1250 212746178 212746199
    0x40b090f01021207080f07150911010e030706200a032604020108010306020d09021302040f0803090a031e0c0e190b0604121a0405161d0a0c1e0504 64
    0x201040c0900041c030b0401d060207802c3c80503004013807015240b54404900e0041c41e81c2800c0c112521564441ca014003044005070b1402c0042450039010748608040d0040031035254064101080303140d03801001883c041d868034104503149141c031340000c2d604014890316908210300810860981610941b561526110702e40c68001500c8031220b02c814282284d0014440540d8004009a06481c0c000c40056a151298040c407805001040c20007034000c0c010340003203e41240c041d0701070410341c0c00c140e00b00c180071a41c550030076559003d6029100e5028a58400030000079031111000ca0b07004014500c03110704100161140e150140c1240c1c013540d4400c1d4084d0800c01c008500280c1b21516401c403180421030743c0e82a401040c41c600442c05a0f9441da18801c4812082c01010b81100d002c8101401002c070403450709251213619800031903000984011000c40105201d101e490036000b14040080c11850207980b614200c030081d043c410780240a008440e05d14070300452040b58590003149094071a00d5646150840740c61 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 212748678 1250 212747428 212747449
    0x20a020907080610140703110336030708030a030e12030a0f0612050705100c0605090c0a050d032c061b070902160807022e02010c080103021809070902040b09 69
    0x4100b00c005c0081c8142c012200c3d082d42c0301c094140ca04401c001d00d9500c80d2615501c03c240302207113a00003108201c0216801281200d03909050781038003820702d68250082c103030340b1180c030700074481aa0402d02800600910075808000c1d0a14140700b1100c01048880c81218030783d00c20780d80405600c1d203c1022800d909020300540780104101c00f03d6a1600d1066124603881d0030b10750098a206500d510444e030b011a108804102e8460740100d802c00c0241000c88040c2c1c4da0700242310b10a03005641c1d02e20001030515004552000041c0c058556030319440d808454003510b03132541c0000040d00400100d0903080e81d200e000192091481460421002510720f840d118500310302d0340c1c815480580100842d42d6aa0a007038800c84900740e0104d2103546800440c4001a908050714030104030f0145400a1114003180f00c0381b9503812011160020480b079501c07542d0454036030400740006504503404130741c0440c2d203160350308038194058260403e65285584a0f2040c02c01da81c80f5901c0215000404662031070980360220190 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 212749928 1250 212748678 212748709
    0xf021e1f0e10020102091c02040b01030902060708070305070b0c0304020a0807050a1a0405061c0605040b1e0f0301020c07170a170307090902030a0f0f0c1b03020a0209070806 76
    0x514503004030180082004000c201d400c1d028003030b81900072108074000d4041e14001d4400034030301d44031008040d1100c40402c00c0c0c408143d2049061040d131000550080c400c1001042e0007078103151401c1c00c0e58545200c10f1740200e2084003000010801c140c003041440c040304d4020290314030101d990b41018010850740d416075400c0300142d6006013800708201e6841c0036004040b5408920300d1003101501d000c05418034050340d407250b5005500080c5c180c08081c900c0142e641c000050746c04c2000303110f45920038041105c0c1710082c0320b0b8200d15001142045021050b04411558000500c144101010303400400c1c2a03030040ca660b191603601200b000d00000d101d40700303030755030382114100200b110303180a4580f401d50b501c2e10381450040b4135002000c00e041610500880015090200041d0b60701e040087c43c078401008108501d8141030b180114141e4070160130300400e0081e0300307a40d40d503850801c0e100c0100700b01c0d410040320441c15841411004401030300c41c80e244034490469601ca48000e464000140029495005207a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 212751178 1250 212749928 212749969
    0x8030906061e0123121f05030307080306031e01051008060f0a0c0219080d0b0105090906040515030a050d0f110d05030a0f14180a050601050d0f021e 65
    0x444140c0a218080c44031041000d203030008501d107204024600a43ca201c1d140c0c80b400c0c0780081c1c4070062241c8803030300c81d015013104010500106d01c03592005106078414018154550410003000000c82c00c0300001e9074002c0c8009050f45c2d9500c140316800c044002e8a500c25412603511001001440d2000c090a00e00030200000a012103103092400109050310043c21080c2d155074400b540b29980c0e00c200f1908000700f0715a405800c503502030b42410400d039084250040840e0307040080c08402c1d544500190b855111002e05002d100392a07000400c8042e000040104820407002e004001c580e59041102d1001103010740003600892149480050412112440c0d45003413001501c0072a0802e980024283d03603c462510700035849071a40b462a40c09090101030045009007000a03c0c8150300549608900911518150f400000c0141c030380c03261500246035000c1e0180e0070181c0100000e04008102d03d0860b445056500346840317860380012018044801543d120304002100f800342800c0c4001e60350203031012480c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 212752428 1250 212751178 212751199
    0x609050607051c09060b030a0f02100c03020a200402070b100e1308070305131d0106021b040f0213060f030f110a0f0207050a0b090301140106020a121b0803090606 71
    0x1800d4400401e1600c0d0400f50540e51151a02400059444104100c200034113a43c3c60340783c242441c1c2030b507088481050703120303507110390f841c0340c105018801a2040e40da041e0041c220011480c0c84030520202180c030f02c0260a001020030445581d075910040c0300c114450a00c0071507038140f6240006844150760400c0d000d03800032000f88020951501503890740254000c1d8400c0d035460043c0350855041c0a6107100111541c1825000b0400544900030000e0b40019014036029582e40d50750202da40303504001d0104c1c00d04031054514409820160090041240c482001520304a1000883c0002c200079601600000317100c500c210340c41680c14007607660500da280c0018410701101005100041c42075800754002e114120b0004801c5500078083c910051400418035080590f841049164940c44440c40c0c038821b5107056101034025070222465030580d001e41d8001d021040b107581d500400c0f01c21141c184818032000c2401440d0340b280250b81c42d40068801e100103516800c140c048289809000340010b03110711000306 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 212753678 1250 212752428 212752447
    0x306050d030512070c0606030606230109060c140303040507061b0302030906030402120f0607180e04030507050f16090606020a0308070e0a170c03240a09110904060905060705 76
    0x2c1c165050703180b040399904015103400c034064031010301c5c8100c014181c3d0300384400081805540c3e401f84040702d19411501880300351014030040d0510807080c4150201d0324415050100c0c034802d1544420f030a101e070080e8070b194001810841c3c40c54000b15002c03111648688024007407c2d90125402c00e402c0c0040440c66041565581c003e07481c1c1c05080403c6004a03000300004080d035640c00d2040314922417280c15144015516042207071944011100c05010030010514000b11103039407030b410800c42e1404030040d20942c54503a0126240e51200c070081c0c4041c821640c0807001071000744144041154140d0794058005c0c40c10100310306803415588600c00f550000c62403c004a50840301e250f40c02403071460f003042d015a0001c002510203c0c0d50f000034580304088860003501d03250009002c002002c086086482c1010f4407200c0100c0540a205521446281d04000c50940c0d0100d03003028003070354411114000040071340e8000c111140c000b141c090b1422521410300505210003401002c1d042100d9190840c034201290 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 212754928 1250 212753678 212753687
    0x32802030c0d030b060d1803020c060903060f06030a39180e01060b0d1e050c0d02090402120411130608072d060504090c050a0e011115070507030306050d03 68
    0xb0b80480c080c5030300c0e0f44c02c41c05141d03210411180d0b2400c1048081041442c90892800011070b80b81c0d00b240075103d940d044011625003081030700d03156200100180410350380e46800003044840a000142c0510a441001c4000f03140e84950040d000d94603d80c01c01c054030440d4a00c14a5100078500407480302c0c00d040c091114902011200004c810400c2010680304071682a8900402682d4442c1c0c08030b040c0400c040c0803039202e40d0440c000602100d02e04900d20b00c044440303002268000d80703800d01501c10801c4060743c0305c0200c0d00500a0681c00810060414841d10100c020a00c000c07202200c4460036640418020b140c40303d40d281000b145410104902420210076959902c50307070081080260102c0e2000070004510004031401c10030803960b00442540d00d01c2d0242440e041402000c034140d0030a807803010b5030351240d400d4402960315969a0420700d00418010740704040041c15203200750007038544205019455202550080b022a9541591100c4a060050454403d134210328410300c1007d0f003140209511 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 212756178 1250 212754928 212754943
    0xc030a031a12281a060102100501061d030d050a261003060e010509060c071b14011b0201120515041406040b0a08070303052a031305040b0d080309030c032802030c 71
    0xf034000d00702c0c551180b90040c8e01d410103114400240c076040400214040360310110b1086080035050680022110301c0c01090b4850f258511400c0c0010401c2c062291001c1c41508907246c6140080308035001c15500804082c40d46d001124a59402503540c8810410806503205800c4889803002c000c00150401c00410f42d2145405808100030840100d814403c0c4509144098103d00110485d8425641d80c1c89105190758400240c59022074050802106030849401408030113550580d541b48007590700707814001c0140720207006e0401c0030b6455850410140c0302c9105040c00440b4603190840c1d0362a1150401c8151100004a0750240358000c004002c080000101101640e9241c20001e07150b1000700160400341d910b00d03002201900483e120401200d00100041002024007030000b00e0981d107481c1400f080e10081d8a983d03800034100c01d0041e001c0b50342d0a000d5600080c0d940c05407403030b0010004a81b880d42e00800b4510412151200010081c2c0c0c0c4024070700c2a00c0b41d841d0001d5030805038046141c2da00e603903a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 212757428 1250 212756178 212756213
    0x6071b050703120e030f0105060307060206071e0504050424090603020f150c12030609010605091e0121051005090c070602070f0c1e050102030c030a031a1228 69
    0x9070340c0f00b4011034044c10030075030700707110107402c842c29088000c60144c0030b0b01302aa441030080c012072001041320f030710100d8480d01c03442690b200c000341c10300e148003c56005011b441140040000030701c03000ca040e42da00d0180b06582a10041907104410300b01000940030303c2a41c2c851850b0500e071080420046c1c403810310000c8402c4c4111003046c004a200440c9202074841c803d0040d201e8003896000c040010141030180d0701650081c0d8801c04580c2e21090250303014070070829159403107040c07102e200408016400c0d000700c680e40c06242454400ca43e09403050a101800c0c24035014040d10780e02001102103424000c0300c0200421200e010b881d0a0180307402034207100f002405407500e80c0004800013842518608003c1c03180c3d0000195003629a209030801c99055504501d801240316000c000800e9807001083d5151030303034410065841c02800c000e0580041c40402c101c182450303504120741e06941d0b5921000b4981e00181009030503c0030160010000e8a0f94019001054210700e0913100b0205560700c145510409 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 212758678 1250 212757428 212757443
    0xf0313050405100302060408480a0e1005040b0f090408070c0f030b040201020d0e061b0f01020703020706080702010c1d01050702040504060f1808030408032706071b050703 75
    0x88481e100a0b40301000f5400c042e41240c4006000150b2250010b03001400700f00150b00b00c0580039018440c50040a40c08002256030700b0744540340c2980c1c01c3d1304528240100703402880003011503034074130524482410445d0040340d60890898100302d1802e041c01481c0740c0d40011902d40008002c4800041c2c000b800162014085040101c1c4c03003010004900c8409002e801c0140d02d00f03102e203541c1d190000e0f08410854003203005000d2801d40c210b009005a01c0004030321b600a1800b401c0003001c1c42507441400c0c1c500c5c0803107540d01c1030100120600c042880205051402603000c0c10341981004005050304802a00c88021685000c00d1706032165407002007000040503600466103501d0500004071014080d50301c010b5401842e10b0284000c010943e4000703000203902000510180550b10407552480c84e694101420003c420000100000e8400c802103038006441419000755400c250850030b40d844000024401540c010300c00d004880c0d801072601c0f2580d11207141370320096013070355a440351201c44902c001071090 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 212759928 1250 212758678 212758681
    0xf0201151a0c1f0609050f0402060a02010f1d0120030a0906060b0d0b03010e0d0c020609010c081c0501050d0807060b04060b0c07030b070503100e06030a06050106110f0313050405 78
    0xa00101c044969010280089030043c0111012205071111503003403040c0407924100d8001194001801002d00c2004841180c00c810b41e10b030703000d0060300d601151650085540c0d543d41c6081c01541c6114192041c03441408456500e1411700d90b850854a00851048035100500d40c072543c2c56410108690740414001404114000c952034028003509043c4c01081d0030510220708000c462141e0303480500c0d0f00404500038050f2070454523202c0e46441c440c07441d18001403103610306000907040c40d6004009082040c5080c0b0146105511a6026a000300b012218103402c0e014603a18180f429015060140c1812620807240790b040b0ba81c0c212042c0b0403850010200d0f921003034400c1403944d42c0c0d40127000611040445540e10b040003040182c5803411400110756070500c040100b6541ca1041c3c0550780b140e04201545000c590421840344407030400100030940c940309851840b0005209409117030f00070082c91305d17415400001504a5801c0500d01c05401045a000340130410849070480d4100c03080f1001610002160b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 212761178 1250 212759928 212759969
    0x1002070f0f03090b0a0e010207140a061803020a0e04030809010b0f0d11040c030902011106010e010e0a0204050d080909160f1812050a03080703110a0e011116060f020115 74
    0x9400311392109503044000f040030500c180e005080e105020000342c2c260b60b516501c81c05215185501c5c0007045401980b00b81003840700a0103403c056190a004150548060703550394001006e00310300c2d8000c95042080502400205600003c0c041e810041071002448140b8481d00825804046003040c01c1c46403d0704160101070014242a202c103081000d0700c14051616034030302c0a0080c02c00464100d000460381002101e8100f8045075040c1661604006000d05905e0401480d180c44c3c2d0140407401516400c000019143c0c0e1b8001c5082c1c100d600c1612519102d8981004000c0c0c203190090141783e003a10861030603c81c5030390001140140d0380980c280010100050901f1a6110416403c03442d8100034028010061140c005414103106200741c0d100c001d0f96603981001c405486610106800e046810700100101d603004403400403003444103141420800c0c000c41026842c02e140709480c2d404903591740360180143c9a000c0d60f4155507501d10f0000340952032080c82203041c460744c684140d00074a10304441c507490 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 212762428 1250 212761178 212761187
    0x20a031106010e161101240b120a0b12031305040b0d11063f18070e042a08120721090305160608060a051f11070305010506031002070f0f03 61
    0x117050080c0c0000c00002c1c204011214034981032201c081140b805850b400900820a40c0032150300c13800c0c6028010282d2104519030014103d10442140d204903452000c51419a0400c060010701d001020f0b81003204c1e20b42405d00c022120004200303402111840c40240208040952612482c602550b1041e0396101d51240b440f0443e0030354104800014811072110500701a892030300481d40100d1142c41c5182d2161403498402250040400035079800c2030500b0003004c56001800c0f81e00030300815444030000450fa101c507203078600c16240e01c41440304169080c45081e40070040c054400381200c089515008250b00c41b1040c46000c852100030107010320f0071b50003c06100c3e8039072000460703000b0200c40c4240820416800980c82d20f00a85000495641c0050400e10b4010b450b502115000340010881c1241520448040940d9080b5101403112003c02c49054110802224000f14000c0c000055141044010982080b42c0300030900703000f07030050005102041e92901c884270241c2c0d01004030a078005e46440c0a46 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 212763678 1250 212762428 212762447
    0x2a12050c1902060c2415091305030d020f1e18130b0607050307061416080a0b0307060903050c090417030403030e0a141c0f03020a030e060403020a031106010e16 70
    0x10480c1c0500e1171a0600600002100301c0095603c5002c1c051581d108440c0c0c4004002d01c0300800c1c0d01c42c0580010401c1184108908084980a003042c1e0b0300d02081d07000f0013070a80c1d10100c0019aa04800151000c141c1c070000d022841100000800c00c2c544203a1001d200c06414440710058411000680700c1d07004031585038081046a80050100c40d15450217007005da4903900500800d0710880d05002c640340781720340c2c1e21960074403403401003544003101228200e049410f030304010000050996141019641a50100a0310000b0b00c0140d03502c2c111282585051800c0c5000340610500602180061000056181041c0d00e00d416416032070b16140d03078031420304030040c08040001800c1d0b4080c5e84840414480310001c03481c010400c030005c03a020590310640c2245a903180061f0344c400075212842ca04000c034460b4006040241c00b40c60003184085d200140a8141502588c0850144e8001144031b02095089500301c80614014400b8207c00c0d858000c0c1c0769040800201084040e41084242c0c022050180d00c440 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 212764928 1250 212763678 212763697
    0x9091204090e1f0203061309050d030b01022b030c05090f013002190806010c02040b060c07180612030912031b0b0708090c031203072a12050c190206 65
    0x1c1040820103d6480300a5106a46050103165a0440d82030303240e141d4042d0f50840c5602ca002003032041c1300306004074010111180d070a811400349019070034107002d00b5909070a1000122441005088800e20041c049403c907504004c18030905008103641a9149001c2449000080c2402640241c035110108000208140c045001d00f0f1415940c450f0460203602508070b418140c01014410312072036a003036880b001c0841e01c0b940026216890303040141081c0d001501c030020302400c014144203030202000d0810046030402a10100c1c00c0c180c11280e04000e002c1d0a000b4900940402000344a580b4028500c0b2801d0142d1407618124000301d50405106103c640ea0742000c0140000c1b001d0014036016400f007009441c00d84c0010145e4000c11002da0300818107090b005c0004005040c00c085c081e8450300e8640006000074288601c6060198070b0341040720147c0c1e0403030800300340d03071071035401c3d515000510003d40300351401007080500c5003a000043c0024140006410184420716442061001444610800c13400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 212766178 1250 212764928 212764963
    0xf1309080f0c0703031706090a0e0f0a06050a0b0604120605060d1205030609010509090d0806130504050706110105191e0204090213080f030f0d090b010308070209091204090e 76
    0x741201c0442c0424040b003901e02ca1b5a8440e1a20704012100440403002c1da6a5039101d104180440d000c001513600c19058038001009854004403402d80b0345050000024003510038a882d02c081100030910391180c5200044110f43c040c4c00c1c22b04004080f40b130070701215801041d47d0344c0c5901281a580e81c10140220260340682c5103c100d8234070400041032904140d81c9603001c1c10031940040780c60b14004201501c6056140024030300c038059180101d40c4903801500060304040d41e085c004400007400d0091a216a029600400002d45400c170010f041112802c02d580d40c90b4135201c1400560800180000c0c41c40501000c04070356100744801500c1d60340203400c1c0038401e02e40300140000d800c514503000307031680c1c80300c83d0906940103030354080d696110b4405480d010110380041140203039001034400a00894503080da000030f80040d01daa24031014620a0b003055800c50008500c850840c13402005003540045000050300e00c1030140404007806003d1030240c0403107180c0f2484901103400c400c108040600103450341 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 212767428 1250 212766178 212766187
    0x30c0a170a1a0102071a070c090e0a05100207050c1002100c030c02010f0204030b01061404030803010b07171207050a030225050f060709091802030a150b0f1309080f 72
    0x100007803900320058501010490004000c1e50b00100340390303040313850184041c141ba4583c01c1660801d50700100080303642005103c1d002c29810014031030710518140c10401002928101e0034228a020251444c020f5420700401188000036004542c40031141c10594240d04081c9940405a0078450100700c802da0192030300060f02e182070f84c113402c00b00b0390140e1600200540b801c6034140320160710542c000541103442034001080010700c10340c05032000044182c59141825160360750201310340d10a074001c0c0c4481c000421a51b05001c600740c400c070300345014460705078505804e81218620501c001080070040c48030101d0604491400fa030101c1c1c8038000030b8141d041e8500d081c6050451508030940f070965481c0300d003482c41210901c1c0000d502b0b00074001c41d251005418a822a081c1c0076200c54003512541034091705026005860400ca071b0100d00b0b00c5401600d44070362200b41e03841c00f10f40c02142c1c01c61003050300104031020707500c90940058801c3c3c0d00d81c6000c1480281420000b00360f2107107103070000c1481030004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 212768678 1250 212767428 212767441
    0x40501090b090703020105031503030c0d09030b07080f07030b0f2e02060106081305150109090605090105070522051002061f0f05010c06290307090908030c0a17 70
    0x14008501240719038501c903541c0e00d4881d10207035100664000280407403000c001092078040c0c140740000503003d0040c2260300c0d004003890141c0c149541881904046511101305004004011083d1584540540f0b005e0141d807070600d1030140c0b814009000703181403503910580c2d000551540030004640700f601514510445440c01807040c80300600f0008000590b4a030b144040e4801d10105007641200c685548049132a15000d81c08611100c403200211041e03c1102c94401031520300100e5a0300034001ea600c000340c1b45810f407c0c07207019500e00824000f0982d150004104001380c228003518403901ca9242d004456000c0c0309018141b41c8490340155500c1a84580341112142d400140d05114045541c1481c0e0300c082d040341c5500d03429902d4018607102c500b1340581408554401c0380800c50301405404c0100c1c0d107001810031045179030404040c860b81e8410031125000e59080801444005180710750341001a102d00c3e4881c841c081c000500640344482c8002a00402c0902c68103403000c10040484840d43c0e5420700700d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 212769784 1106 212768678 212768681
    0x21008071701031202010b010905101b05010f06060215150f03100e03040f0b120c030c04080615010809150105150f0c01090201030615090905060406030506040501 71
    0x100031076100c000c4241100c600840c000c0c05403144414080c40b0003030940303500c0d0483d98140204940104920385400000740480c4100f03180400c084000001c891a140040c1c1001420a42c00c11140080e0300059034005030031200640c0032201542c008550600350520100d480b450859100b0f02200c5190421088900c40b03a10001d0507601c1c3c05181c40529011103100707496440c0c0035400410b040c051540c0e40204200505a203282541c282441c060507628994801480200000c002001050042c07003943d040c0c801900340c10003510940c0c80d041154100040e413410490303001030008004182e5602c80440d5200081d200d8200464940e800c00003404020a18903840082207102003113100c6110440e00003404100e6050400480c809100b80001015074240340c0244041019080c030104540750007030020380c01c4420009001c941c40d69040000381c01072031f003a8005001409003d08100070028103 = true := by decide +kernel

theorem cover : BRFrame.Cov 212589928 212769784 := by
  have h0 := BRFrame.cov_init 212589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 212589928 ≤ n) (h2 : n < 212769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
