-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1662
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:06:51.423748+00:00
-- url     : https://prove2.me/submissions/89d37f7a-0bea-4d32-b771-630a37c3cf82

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 298741007 ≤ n < 298920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 298742257 1250 298741007 298741057
    0x303050405010608011104030b10050a06020f1002120a0b01020c0d0803180d050319060b0d090204051014120a0f1b0807031a0711070803070228030206070503 69
    0x90a0446040d01c8551038841c0c0807850402c10f011b40980c40d003605035a00d050608648980300c0080c406042e07502e0f00088000005055141c100d0088010a101d4002c1d104405408180b07034100f001c00c0c0be2000c1d03035078410810a4402d2842010381034100280c280006000002600141e1034468009080c0c0d070711484c40c003440b00410000d04003d40c0300c1e40d942072012903807000007091b5613a21341c12492000c000c9802800081c20350072130f965280080c1742d8141004a4a560740c0ca4150010344d00c11030b003000049848031194400d50425003d5660010003141c20301c0703001403910701c40e074464291200c2018031400001405e04002c14081124010311508150010004411464803842c56028036950001c800d40310f5000154034403010601104aa0b004a1851403624680f40c2c6581e106000130300c52428014164100c024010042046401a2203148000d642d81c03200c900401403c001072001c005034070b80c4400204040000c0425000e0112039055880c1c940b90500c0346044c90442c0039010b66480206003110b50342c4a5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 298743507 1250 298742257 298742261
    0x30a0506100621470a03030f080a2007060b01020f071215050108010606020f0105090d0f1b0510110f0a0f0c17120702030703021f06090f05060f01020f0d03050a02070206070303 77
    0x113920b2402521502c6500c4201c2401000c211318030014010612403420000890f008414107a48205c04582c002000d800101070800a00d07410544101d403100701185030001c10540c1d20640340f820909000415860441c6185c2664899040c0500c02c45668480c5941701000345448031038800200f00c503800d100c2c42d0b8694070814002c1c461845008014071500c007044000000600c142d5015803545070242c003805141401c151015441c0c00404802c03c950a106010040c1c95803481002e8a407294001d8a080b0703c600788000265000004911346406041041c4514270041004403585450f4a00300b00f078140b0000d400c1512400603961000c0c14484d0940d02101507201503100070000941c0e0040c1d00070558540c4401240e680c01010401805170703005004038003074070030018808103210050306400b1824980380d8800d00c0a0720386100f03c22508644903403d1190a1030802e803506841602803004045405180c0451699540e850f000c00d424141d803607010958030303600c0c0c1d0100e0390b0440d000b07026a82d40f0a0710b4035000380 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 298744757 1250 298743507 298743611
    0x90203130c120b040b07050c01152c2a040e06010917150a0f0f0905210a0f020a0602070305071a07021b04020702030a0506100621 57
    0xa000300001c1d41c085450204081001c49468102e29085050f13940ea07590480900c3c0050401021701038140110b18081200b401039030524501c0956081d003152810ba180524510001e655038000c00a228118120810f11411107511116994500d4031a8000c0c104040c001d901c0c449030485030b004001004640401100794a5001e0070080e680d0030b07555559803a003402c031003040f1802d20f013494104070103400d40b0b00526404641c02034030070400045d80c0100202013204584083d242c0182c00e0703849040c64814440240500980d85800c070500700340c41d02914011580d1440340c3c0050030140003807440c3e414017061003003120a4a00794080802c44d654102414042e004ad0004641112002c0d440b00c01140310314014040325000382410f40041540d0045c9924101c0d010150761060f0f0f8000e81c1c01e1014001681d0100400400280601e02500c4075007006181c40c0d130090b42c5904450148080980502d5204044c5a04102c501003c0c420000358102741c440d18202110f01c41408984d01000c80021a007141e8030745500039 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 298746007 1250 298744757 298744763
    0x4060807020c0d030903080d0f18260a0804030903060218041508030301060c02010c060f02041e05030d111042170708030703050a200c04110409020313 66
    0x82c00c900d4840704002240314015030040c0080e1905e01d04000190507440644a01d40c81d1550200b8042404401c074022500724820a1107032010819a1006101c3c4d0240c5031000d800b11030042408441e02c0351540e606620401d03c0f210100a840400034007454490320640000d944d104200355030f43e03030312803006242d111a0111660b110b1441c02c5200950000d107000c02100f1200035801550231a880c15405540000c1042003e9051264240100000030210f00ca1900f072100340b0880161282d040645a8150403078120800d0241400808103001c40e40d000607aa0358648030610700310103217170300f032421450425100315905a034803410080c00066806401404d003681003812341075184050f50b04003440720071000a40c141951821802ca0030f122024800307040c3d0b608800c030901180c07042c0e03540d140d58500c0c55010890075000500f0209840302d5280d8000d0616092154900c19100c4400103070b101251540f042041580c415a41d80c1490001c0c0c8000c0310a40d0000c001c100011500c07031802400c0b20303007500b074910022 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 298747257 1250 298746007 298746013
    0x4020f0603040c03140601090e15011703072f0a080304141f08040302190c0e06060c07080c01030b0906060d0902280801050705120c0a030f05010311030c090112030518060406080702 79
    0x345600c02780011b61211042501c00400c00c540c0d10703213118501040080c6e01d44008a0000308807600102d075903540c4a013401c803c41c020b00c050620008007811880c107001c003815481011642400c0040e48800010340c0c0503500070003d44c18070382840d80001841701102c007411296803550208443c5103a90080c075224030030741c042c1e02910801c00700c000303201041442103100200003440000082c001c4c150b548200c0e640c13108004e82061320b0b10f04002d51044c41c11103a5031003107285500000e0304424559040c000c03810707020000d440381c110904000001684c0c60140105a5481580d200c4481041d0768802c00d070074295202d0018905441415103071514003a41aa000700c5103158207100209071898801d4003190208850b640a0314042e448036142d0020561103501080201501c8100ea030020780d1641c40b07a240294803036038144d440f00704808103040c100380000202510428400c40100444514032104400a035810700e449503a68000181d0b0500d4480718485040d0898804100411500d401000c028001c20940e021 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 298748507 1250 298747257 298747271
    0x9020907030b0d0b13020d0b160504050f04090c0b0301081e0d0c0209040309030c240908071a040e040803091902010207150302160c050f060304020f0603040c0314060109 74
    0x203600740d8101c42c0b520340d0041c01c400900c03004603140001041e000402c40c3c44e4004540e80c1c0780c0001d0410079200d0005d0310400212004c0c01540d48019880b1038003840300b4282641030501c0d01d00043c142c0c04061034494001c5807510907440070010024010b10103054405419501d03540c440600540c1d80701d0741c85480503d4004a4a00700742c011000036a100c5d80d0600755100324440c109a0300380701046202030300c2107080c461240c80c0840080c0a1000420180c0f80c03c2a100b03c5200c440010900450310b50307240d400c14041e62800070301c074035580401e03800240e0740300b03d01d0903074140f541d804c1d000c00900c126408100401c60b42c009000400c01460300550103000a6421140c0040b00c56803829680074440c40c000340541d0140404005006d041c24019182d5070b50b6060050a2840600d01d041c5059900d04046a200030481030501c040d151076100c0402002e002d03102c050440c070b440c0c0c0c00709000400030b194092256002000150401c84014440c0b00a198401c09895044d110440d58541d83e000a008007003c03541810b031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 298749757 1250 298748507 298748521
    0x60408180f1801141c02040b130504050c1f201612020f101d0109090c120501081f240b030402090601030203060618032d01060906060507030806190306090209 69
    0x40c1720942d10303004c06102400c4203d6003004002c2c000c0b0340016801c05602c035100305960080b4803a051084e405400601180f03a2000104040040f0340d00a02c40b0f0300104100140040b50b00418504901504484505c040144100d45510b003208010a10700d0400c4070396800308400307200103100c40c1a64400d45100002c400e102042008000000300d0010020b041d2904004c102ca000501e005a88401810a02000e035103904000d41a184e40101c1c410103d6448203503e56050214414240102600c01c050b017030004070301c030600e203401e85008000c030321258407020740300481c1990742314000b0100d00700d03a40800034660318450608181c00032030b02680700785074140008004c1c1d406402102c0c858100107000c1c900e0203854007034081090300c8030310b2940d80512403180c000008880091b0030364000c1d02080c2d010564400e0702d9095600303545450f040504840d0504400700101908002607a1b0320381d6042c1001c001c1070340d031240402c0200040180403001c012807408000184a26680031a001c00d00a498001d03869840a07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 298751007 1250 298749757 298749769
    0x706111903121109030705030d080406021c020f030411100903111203040f210308041b0312031508010e060c0a030b03071404140c0d0903050c03030a06080f060408180f180114 76
    0x749e0300100b01102c00180c0020751036402801c0301d51041d100019010424040241260405411b88010b0b84000052109200f0070701b1024181c6801210040c2c190520f0800007454040c480c0b02c0101061201c1e404c00880e5524030900c5500303400701c0000c413501e480d0307141c02d0490860920301c43d00c50003120310b006540040c40360b503d03100d02094251b102c4a0050702c1e641d54281500d01941911401150308200100c0015100d4510305c540e8081668045011000d40d844022009000e601840c0f860b0325000713000080503404902075521003216040c032500c0c1da108a4042d00640100c4540681c103000f01180400c0c84101c06001309170110703041d1030801050320502c01020b41000140e501e07101c800c0701030003a0b0300b0001c01c1d608910941c906c01d242c201d060041c40500070340346800c203498003404a5114078041c0401c440070094510580c9020000340010f003440d07116034080e403140c94000000011503203403004e00742e02c8104140301c0526000e011003011043c41d000c8011440d00a00403880c0c2c156007a40c4e840d0345481c1c11 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 298752257 1250 298751007 298751023
    0x212070f0f1a03090a1203050117070e0a0207050717060109110a2a08030406060e161d01140325020102040302030705130914010905070611190312110903070503 70
    0x1150100c0c1d030800b03000c01d9100681000300500018880c0340e404e100090b154000351100311040b80c402003032950604d401d031907801120400400860f881150304100180e2440d01c0a500300781c1000d0016540c8416040c828103000d241d4100306010204282002d13050364000a040341210b642035804c100805002e03044203070610070300342004001990801d840e0480420350400d0748007004103003c5110003103520364950031641c100310f90580f607440d91a90100000904003240d580d0201c00f0303080341040c003561140090150040000030178090798141c52404920b0b4060001e0802e409000604c094480c5002420030002228490000f4290000c5c00b200581d054014001d50382030320740c001c0103800da00e401c0805109007486c40e05082503a094035959090301040c1141c5d07080c03c0103203107400081079503515404c00902d041042e034018800c202200c00c501d40d0f0b0131000f26059a0746416084201007010040c20102c034041007440e005e40e0303102d1804488005c0a50908014090154180c0c26a017030550740d101003507261982 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 298753507 1250 298752257 298752269
    0xe0907050307020c090a1e020c010b03070f0608060402130b0d0c021b1201021b0703050f03040501120b0d060f090203010506030a211101062c040804120f0212070f0f 72
    0x4500a00150343c5400345c9501c1d4041c0400310001103c0c4802e610518044000156607100c1c5a80040e1607510f41c07100b0300030101c1c41c1e00180c0003441c0d080e107000400554090a4802c6408010180010503119551901140c940400340450300d800c2a49032007150031070f503002c501a070001c64036000c1420340e00f90003c1058844040c000e002c0e502e00b010300c0e5003400f0220001300f1810304195400c01c40050600c0394104000c2c10440144020320121703046d403902c5d502d01407030003603190810703401480100540c3c1e0b80240d82d00c100e2240d030351001c030b10846200045070066044020042a035410900e0105210125a00002c2000d000310b0003442140c41d0a01807546803080342c1c0019111203061400d40860107000c81c440b0b840d246007807400c0358940e9481411903007121020303080b01703100c80c490100c1c81400708480002c3e80d0411681c0d15484045040c647d444078081d1090f8440c1924805024211a0501891b80303078135101d00c0d402901d045900710940c902d07641c80da4442c1c0101d0030030880701c0318042620711500400c6001d80341 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 298754757 1250 298753507 298753513
    0xa03060603180302031905041208030402010906030608060a02180d2405090c04090215160c060f091a040902120601140708090d140a03030c12140103110d0804060e090705030702 77
    0x9400000951030104010610b000d000040000190301c5274555591000c090040c80000e4690130f151000600d02d8101e42d00400405081280601125002003a41904036400041c01a034803102d41d1a020f142802c00c039402c0f43d11440381d54214051080a0b03210025070104840d50307120f065040620401116419a02c0e0216907010380007486250034554043c0c0916400100589100600b8812404035944003000c26515007800380403800c10081c101c4a0000500364501b42580c035a070b13101600074411074091080d10602c0b503083c460300c00c400d1340aa04990180c4130a040c19947d42c08503440051403880d00380d4031180002d681c1c5903c03040c22142c0700e003540c1480e548055441c1c03078444100104280030000074416a01800b910110300d100c60020044144410b1080d1808503a00c5400e4802402c2401c1c2c280c03c5c009214203019486025400000c0b00505603071780201c603a00032503441c1c4040b841c1c3c00d400c1440107000c0c0b04000380100300c250b0080070785000b19204881240b0340783c2d50b1203000c4403180402d4801d480542c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 298756007 1250 298754757 298754767
    0x7030503090913080a020102070309210b18030703050909010e0408041401030609091a180a03030e0307050304061205010f03120f0e041d1614060d09080a0306060318030203 75
    0x894000540b64100b104440ca4114240d41901c5940080d03001005400240c0c1d030015a0303c00b09500840e01c00001c003010702203d501d0400203e16070396004128500140400e10f5000040d9405299281c901c12407204403003101e4803040d082ca000340c038076800300203ca446103190000000301d8015070b40c1d115114691080c02c00e800c240c07920106c46864002e005015051545076040469680002e1180c010650300450b100c00301140c551810172035800024200380d04406010500b03401043c1c0c000f400c100219407515001400420440b02d03503040d40145800104140000180001c80c1680314051100d00c00d40c0c21020001c590f030324090005151316038440281012403401260527114003c0004002c8048241448002a0780b410005402c9030b000e818034006480701c018640845a030200281c4601000c28a09141c1c244d040100c2c59030a01242030140388500b01c001005101c0d401c4540141d50380030303400031071251174150141018002e484140640740001c2c0c60311078200041e0170a140c00d4103069416401542c502 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 298757257 1250 298756007 298756009
    0x304050a240c0c120609060c0201090b0c0c0124080615011209150906020a030b01020604050601030f080705070801050f06060a080a0c05040f0e0403080c03041109040309090c020a140703050309 84
    0x1002c403101c4181d54a00c1c2000000401680300584000d80c18411040025108164a4050216480b0300e482404681c5449898400180c1155035140c001e04624040303a1608445010070b0702510038401000050364071143c104030425800b020250958800c94161070080d078032445001c140795200702840d800030703135900241c01000036a540b06000d424060300b65000c0c241114140c0c0801d030303061100225541c039400900c215801ea4944102e400d01030092003d44441d040a0b25407644d00c1a042c000a00302601d0804d03079108000d01d0310102d0b580c480e802800e58901aa4030b04880c1d008160484e004480e01c5804000103c291801b4011120400b04c0c80d03c07a09030303a072507120b0f0060081004044071414814100408100e41401d0780e00c40c0c1c01045002d01180300d61505140007014290007500e0b24480280a01c180b00004502c40000c0c2d4070383e80c0075503d408403551642000c5980d069107038020782c5024038000c10011100e40c0400c82c3d41d4018010580b03102c41024851a9956442340c501c4040c0c40f580040c0200c02c81 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 298758507 1250 298757257 298757267
    0xe011b020603071407030e0109050d0b0c0a05071205031e04021e1210091703060a031202010f1b27050d020f101809090803060d0c0e01080304050a24 65
    0x18030b007860403842c400313031403030b4045120380c00f040044e00807813010582c2c88031960b07000c1520400303040b06581514510b8415074661301d00b2a4042d1654080c0c4101040c103003a01ca216030305840809030002080482005284005000707540242c80e50050b4061221040034504440c00341c05000c0c543c0034181c042030a61001c158901ca99540741c459038009018400c0800400e010000c0566012220354006060822442c3c01c1030700da80c40c81d400b980030000500422040da500d42d1105000c40740c2003c1c50010a400c1008103d004003070f40032440c0881827420b000030324100c0000c403402c03035003410545410442902900c2c406200d00050000c100700600c4650045c08035040003002c2040451000c2c1048911000040000d02d000c045c280b10140024443c900203500d0720b03103110710f1342d00034000c178541080000140d440d000ca10703110080259000305000249078042001000c4050010040c496020f034441d6100c0c140581c499200b07110b03591143c13039400004a80001d00c50454207291078041c00361010486098400d0720 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 298759757 1250 298758507 298758511
    0x90708070f11120c060a05010b0a12060308121501181a040e0a0e071203050304030c0809130204080c0406080d110a06020c0313090b300a050c010e011b020603 69
    0x1040381000d10b500300c01c182040a0020980d00318500d0f40c443c40500e01291074100010100d101050420004011940e4918126a081941483c0080d58048221340d034134050221039000a00003240050301060101a0204c3c01d4051640f40c429250b0510100c8011603108034070039030007604107a030000c4c100500d41402e4100c15040012149032801d007035035102c84504540c2c0403202d05000e1754441201200300300c400c2c8048405000031490540d4560460f403802052404020710003828001114401818048441c1c1951407540000b420300d81d516083c4103250340690014446c203005845290000700452806020311003d860001c0010098254520303012107955400d01a0700100b40078200c601d001061150006110800e03015005640d0340c0850b0f002e03813000d000d00f580300580342441c0007603501135541c40a003503240c088902d0f0b0440c0e0b0340c96030a401c9241d91403030084010800348199811007041080c00321f500074461800b40c0703031058880040401074424907a00703030005034041c0c1c00c0d007110b00052400101035a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 298761007 1250 298759757 298759787
    0x30f060915030a060603050601060203040e01180207020607030c051b030604060b19030309050a05041a0d0c080d03060e010e1006080403120527071401030b0301023609070807 76
    0x190303000e24001c0401d0070a250514183c079103540b24002481032050410104e40100103901c0203528081c80c04029441415041c05030703c12142140304014400583d94059900898004241550701c1640d85005001040302040c2140c15019a908844e8070a05070301c11140005000b03405400b2071740c1e4603074a00004100c60b100f000e80c04017010f00810f5128282c000d40b100914031a454412046007420204421100d0750b5000034480c505200a120701d801c0400114048160281c1c0c7c140394035038083c60815151012900034001030300c10214494a082e0f40740c0c11038400c450030030002e0161a6242d00c821818408100ca419045403c1c5c250704001d035610854181e50300a0091412400c491444400402514815a01f858110803c03411040c9540502c0302c0e074400c03a0554034001c003202460311545c0300c500008900311a0503d40c4c2c40b22810340c03a403800c1d0100c2c0c40d0035130496201c0608040c1402082a500b84c081e5190840c060620041080d905004031201c0c011120303601e030300042d0b90b140d250032140440c1c0caa03d12 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 298762257 1250 298761007 298761031
    0xa020717010609090f031d0d0605040317090d030b060c0d12141503010b040b0102060c0d09080d021c110d090204090203060906090c0415090e070e0c0717030f0609 71
    0x1d64207110b84108004c5610488501041c294142002068142d0381014052000010030419405a035102d500301510741e402400032074641d07640d08081c1d880c803810558403c41135000108000e000031000c100103900481c0ca880c10480c100c20b41c0240109402082120691984504141e0009600840881072050001030001c51001c00035501544425030560703415184034034540c5503280d10b142c00e002c3c01c0003c4100792010440e00e43c010b00003d580d0f0300f0151455142a40000e450080c10505410003030407a504050001d41d20110303885000000d50060803c4406c9011a0304080300e0107006000d110505100454200d0070701410310300010040800c440308a0748981da601c00740006807030621245104543d6035014003111300d81094114104001000d55511442c90240e0f04a40c0c9010100e2400a0f6100e00000050800900d00703001d10380002c9401800108402e10104600203184200405000d84113580d21f03480b840100c44003084d140010f45200720196a0f5400103001828101d541c260311270038142131 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 298763507 1250 298762257 298762259
    0x1505060708160507030501091208040b0105010e210f2506120207060c020a060605060408100b180c04050a0905010509130201050f0f0c0105060108010515070f1502030910020a0207170106 81
    0x503e526001e0f00381d1049595944440e00310090001003a0050203070291403e0550340d40c07401d550f580f003502005000e0079060085040e03001003952604107112400c0c1641c000d0b201c0f000c030481000103540b85119424a491481800e940c009040500314403c031421202900280345241440400ea03480c664500071120025030a0000d00007044082c014025007100c250060602000107007012800e90301260012406403008100800050030000b5005206145040c2d00145001140e000500501c01e007455242c40400d50380280007550030000000c10407641c0468051a91694032144102514000d11480c7c2d480700d0240c00041480c810f003110368032540d1051400b43d18007001130003001401d030003031300c640b8258035404102c00506c8007007489260b400402c24248481d0641c5004005104c0041401d42400900008681a0200200b0440c65912a0b5008400d12500813807940e1800c000d42003180d00d400305100300c29601820411503c2140e80b807509076030107044000d0510408a40d140784179003c01e00a5035817148 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 298764757 1250 298763507 298763513
    0xa0305030a0b2d010e12070302040504021804080a0806090112140a0819090b090a0501050f040e1311010306080c041505060a0f080c12060d0302030702100203030a150506070816 77
    0x210a224665034003040103d0480c0f02800107203c1400200b034140a41e41120068184e90000140c88003202e40c1190089000c4e911403000c9412000c10761001a2001c00e02d000740030070043c482d40034028000e0265a461815a108410080c40c4802803040c03044503041d0000c908042154416003804c0045407008a0302544060f070340d003003525440340007803401010000f402c1040c50369106d03442500414600309004d05001041c00000c842d03690901c55641881000520146001202c40944000703001aa802088500d84828603160b01c14152000700c0362441196051010f40d8000d1254000b5506100010083c400500c030a0000401603407052150580c030b908000100c0f50340d1500202030401c6280d0f520402d52007030480103032100e5000341c03000304d1003042440000400c4003044036041e803104044511001d00c45080c1401e034254400d1940c003079000801c400300c24450707d40010040d4040c00050000700020050707060856a91282806150b6001c10100440d50104015001030440c85920b50440d074075040c3e55917 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 298766007 1250 298764757 298764799
    0x209090c03060a0330030c020708120406051b030c010b010318030801030b150d0f03030e0d0e0118090524010c031d0102280b01090b010c0201030905010209040e010603140a0305030a0b 80
    0x4160100001d0b00c035024403c46030342c1402711500810620300184404101d02030307102d0042c000d50040e0009c0110104101c4440b15405400300315002e541c1c03081d030b5510a400c00300103020b004400c04180c00b09003000402005030f080d030035051340e210360140e551007890303400e40c2d50705001608003416810b4264103005403840b40d07540b400000c4048034441c070000c0381910400d150150644610004100720740d000010383d40141c81d00014000900c500c02d103400c221109225520b000c3c000e4032504800300f01807400f0100b1500a1031000e0030310101c1ca482e080c859028642c00b00459050b100c0000060000d04070300008000c24180044e201e51552050044d100080180c2c0350800c0410300700360b410b8219500d04645131003030042103148a40034240c0362005210030583c9800207480e04903142030082c101a07035034a2910610400b94140d52130800c0060003070100700000f460107400b03454580001e4030b0141060042c003c0300040001c0f5404c0c6654107448042c2146e588030381b034000500410b8612500400342c0220314014001c10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 298767257 1250 298766007 298766093
    0x10e0d0b1803040b0c0c060405010c08030405030706060602060a0608010c0212090d0f0b1923091c050702090c0702310c08011d0709090b040e100209090c03060a03 71
    0x503c216103d960307a17420140f611521014907806040c040009003c56640b2003642c00c200c94202c1001031703a0352950f1801e50b186210f44000a4141858111701040341c40e40424264010084454280413844d11010340600701d43c0b450719030b0703000f503803200c0e01280c031084030a4043c203040340380240340500e58003858803803007000015000c04507440c0405400308440340141960115810682040410070b40c00121403800c0080c0c20b0039007115030102090000746200404200c4080003031118405041042e10a03080a06250007044080b4070400003074000401d4161848240d540c40c9800074109018290300e224485040040302c10110640c0400c1d201080d40c580003402042c2d4000c00c1942d540010f0740c0f41c04002e0100914030880f5902c446080c1050201881e44201c0b04410380f4054000050030481042c0000c00900300e801c03a5a00e54000c07400d0100e03090b00e4070b034040d052620040d6108003c0350741e905031260080c48112070144e809400900140040f80700f2036184840c4042000034525000c1d03c0d05a120f1030402c070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 298768507 1250 298767257 298767269
    0x9010806010e09030f1215030d0f0906030b060d0b0a0308040b090f01110622021206090f0a1a150d0f02030106080c1e030313080c0906010e0d0b180304 66
    0x1100004102d041c210700907899000c0c0300800914100503002040c1d1000e403207200a50508110100041056200e03810701001c64081c000301103032400001003070f002d44100c0184c104d0001080b646000000c00d903019010707800414000505d0b2600e0040c22450803001801e11102d01900011407400100000311040003c00140000701e45003030712400b09008102210940000090401040a0030101c885500042103904001040800c461916143c00e0b1031130f4620601ca0b01a5011012101c200c01d0303d4400f1806900440a06003595110307161442d03400e99513140d00030011714080480e480303100008190803401d82c020300d111442007aa000c5820004010b02800c42095800601c3e4034038007800c5240920030100240708070005000400e40d81c07400a0b640e000002100d420107020803102c07031010340e03003841224091552003035501c0308281c035206119900c2c0c4c4950f55643c002c4690001046856026011840d004100200488012402030740d804038509809881e5491903c0300c90021200598140050005850 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 298769757 1250 298768507 298768513
    0x219020102071509020607170c12190e06070321050114090105040b0f0f060d050c0304171306050c0a060c0e130e0604140f06040f140601140d03030209090108 69
    0xd079401d0041c2400c484108645543c1d1078642c1040c0140c90352010740700700980001410081030f1742e07215081c1c524071510205c040140502c0e0b1003c50780e141010054401801000c0700d255140017604e6040c0e070400944503040b580701c00e0600ca00742c0001e101e03000069045012620304c5110064036071560007540c90a80141040395194800a4010b0400c7c188090050508540a00c0035040f4440840c540680380200d0328002ca048142c06102519590120355180088000130050362820082e0324040b9001500c0850b807900104441e140b414402c003017503131102e100744000000042c0c608041541d041d0710030f000c07850039409640d42c1d81c0007040181c4030300c0b03291070003585410000344940010003121030200441002114980341c1c900391201d4000a6007540560b00c45d20551201d061044001d20700946030805010038401c041c1003008015a4416030321400b48144d04110042c0e402680d0f0b0f940720307042400303501130500c2c0c680482412482d180d400314202a000307007001842c020201c40412044a0700341c20880440c0c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 298771007 1250 298769757 298769767
    0xf1d030a200d080c012f0d0b090a060f1202010e06250302060108010e010908071e150f0f0506030c151c0e0d0f02030307081008030a0c0b150a0314010219020102 70
    0x1940031b0181c10318402c0384030419003620640d91b44101c056100300c40c4010010f20301041600304c40c05264000500c8800003400b0000c030f454a0743c00d0380082e2100d8000c1034249201e54000151200e12808000b00d02c0d07a050710b40c2004918039006100c01070308501c011242d4100d05829520400b80d29a050f401a0f034025805880c2d9581800b0005094900301c108640b41a850506060013003441d40e400c0e038864950001c1c48080c524078083c4001c1a0391404c46019000040c10004040c80103115800301c0000c160411080c030800b00c18030029422503508031015a00b540010340310b200e1a02d4021044006107444c201c0d40c5040100703098186041c84030f20282e02c21240c1da1100380d1004c4c14810401d00b12820740624160103091a80403000b5124000a4207040c20f001c88580800c0602e0038001506000d8100d01c5c0440ba206c04001a0007080140c4034203040d80c4c0381d55410081200c001c40742c442040361003005003850564500e195214001401c0d0b00851448035542440800c00c141e001d682c0001c0f4289180c1d001684907 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 298772257 1250 298771007 298771027
    0x1a0d06050f011d16140a0f031a09180709090c030204060e01030818010903080703020c040617030f0c120c0f0c04200304050115060f1d030a200d08 64
    0x14007030603003010300040ca45070a00303000e040390800b20030b521641c034040c00c240da03804a02055a0502c560742181d4510302010a82a103455800300b83e031340300c2c017074160b0781448448140c03030410800490610640742c012491000007030131503805160f9a011154001c080b107890070b543e40c4968040b240e000c44103d40c058241003003002546403074001c00000e0320203401040310039451030356910341354807805000461010300314070301c40816070203540024001c54111034641d548011529000b5151140e61103014450351078a000881c8411001185161030b00b000d10081d80f6015007402d1840340340d0001c58841259120f002c480584e41c01203003001e011600400f07402044080000424a814651802c42a900561070a00600800075030071103c40c09400d54820b0381030fa6a2200d0429502400c8003c42a88a80d9080d202c0000ca40c1c0c1d101061820f020032940d50301800744000a000c04000383c0d00141e155055000c0405040414010320490b2181103001d8003a40d000b1642a001c40c01c1c010b1200c40584043c40c0c049210f40d41 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 298773507 1250 298772257 298772281
    0x303020915160218011d0a0612150c0e03030d0e0a020a031a0c07030e09060f030105071d0a0b07020609060409050a0b01030e0c090f090a05010e070302151c1a0d0605 72
    0x2800503860b40c0e131200e44d81420603c41007403130904240c0d04041c4840010810140e0a5030101c4003400004030060840034047c10989044d103003860403c0700c001c1c544522030700c01500c0381d2002e00d101c02000340a0761800c0c0248140030090010301d920070005001701e040c04001a130310452032200451007a100d420b07507222800081c1e03208050003440c44075180342c10805c083c00280c0c0300440d0f1101d1401103550301103d44a9a000c90301203001c81038001e40561031300b0180b05400b600049140181d60000c2025010540b11800740405030741700d0310800003002ea050181a00614150300500a90795000d0301240c182682e916110381580d800790b4000083d955500c1d4000929681406113283c0c1c0c1d00710038020440c181c42180800c000110042600840d60005070218407900d10602880c4440c50b00b03d4000c0c41100444206240c0b83c07001440101d1248030341c014146111340d248030568009120208621565a5001d0900f202810801c801342510b007800e2062144507a58441c00b40202501035940041c1340c0c5006018491 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 298774757 1250 298773507 298773529
    0x503010605011d06070c0b0703080103120203130308030601050702030a030302090a0909022202090a1d07090e01090b0303090a0e0609060a0807120203010605100f03050703021603030209151602 84
    0x8100800b140d0f054600008801c820031a1a005481c45507036807903141450b2200b0800d035004a091007034006803030420b05500100f130b50706980c05080750458100000c2d2090b680c03031040b807441c5a00303e0154602000030030030344001345a00c0903041c142149404410750019084c140c210320107c01082d40030603048010300b0b1052031100944001c20041000380402d400041070704609900d41071207090b865024210700c81c910f4041d039400b51000340403d1221901d421000c034181d619030f9420901130310307a03d00207a10503100d050707440100c3c3d1400b5400c01e0180d080603030b8403000c0c001440c4141d406100801c40341c00c00380c03501c00d200c01c000d0400f144117110600300501006020403020780100e00ca464500424031610704d000c10000115501003000410443d110300c01300f4054886079200d00c1d840100c4420030a20b480d0840005040100355070790811240d5507904042d4228001d4680903160f8010101e03559001038001d40c001c2540035001488400a480d00c0300c200310b0540c3c00700740d225901e0224205040d01314100703c15060 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 298776007 1250 298774757 298774759
    0x6080316060f1107080901030b0402130603180f02010c030903020a06050429040501030b13020d0b0909160510030e12041a031308250609020f01030c02060c030702010e030706060503010605 82
    0x842040f06144070003880c1d00590801900740200000c0c05c0200f68020f500c600c10f00c5070040c109644070b820008500080b002c02d0300c03444000c2824541801c80710765440e50503a0015074850492031860110740c004480d1040d8100d03003201401401180840580e0f1041ca040c001400f895071115074907401c01c1c0c604400c1c0c00040c401c540661155091111070540610107440a0300c07400c0c41c00141d44c0300305200062081c1600e040402c1100d03c000303030040e103401c425003000b101a603090301c86001944900788017980da40b00002d0314000c8692251003e100300c1c5801c200060301002c4e1858045580407110040c0350614485038030351811110006010001c0f105e00038482c2000c0c100c0c8900d6241145020901841d80c050301400042001c000002c0c0c014040603c4090303032800c084d0740000310700f0f00d104911b880390041c1480038007688652407030300e040c0303485610034080e49a0112056000e0f0590303840340030880006400c0948500c0c19035490320880c0444131010809802c0c66409a440410b1103841d085c245400c5443c070f50002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 298777257 1250 298776007 298776011
    0x6110307020907030b061303080c070e010b03040803041110020106030203060109110f070807080703020709050c0301030f0f06180302030d0c02010b03030f1305100806151903050a06080316060f 84
    0x41405039403541c4485511014a00b0041703204401c01c000500d80d80303c1c03401c40c04412a40d150000c410b06c04084040e061840100040f81d8003a6103d002c000690039007441440394180c410000640040c0174400559003007071250180d180c09801c40000245100d06103c0c02c480140c2d51a141007040d0314041003081c2c01810110810403100c2507202080a5510486100c101e40d840f00190704001c0141c500109e032051030300140115220480da140003501c0d4500c0384184080e4070700b00404545056089011241201c0e400f19090407182c5103a0f85402a04900d040c0c19500e0f50780d100f00f0300e0401d10042c0303090005139129078055695221000d0f05401203500840b07500c0b046a24040c09108180c0b07000040f281c44030f4601140341c0d1140c9814407181c00f80c90300e035000385802248921242c0015504100b00c1801980210303480d0b410400c200c00c1040f42030040d4078014000101803011038840e030380660322054010300703041c1c0046401501c1b003414919540c810700c0c54188038210340e8085024466203200d514640b0181c2002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 298778507 1250 298777257 298777267
    0x4030e0f0105040e04050a06060b030109060b0a0f0c111504051f0906110f070905190506060307030b0307050402040806060a0614030402100e090a0e15101a040e10061103 74
    0x2e0150240d4042d0b100011065404641405820842d000c0f0041e03210005004240d15005680c07602c4d0001e104008005041070004521070030740700142c501c600b215a84840945940301421180361070704c10015121041e480d00000c02c40d0311203c1132410300c2c11980241c10340d161720702810300522202e2202c00d00300c1c6000c0044500a080d50010003001100c501b0f10b88030002040015502c1d040220740303252603485100d540070000b45540c0d190000ea104113000c1e001c80c6100a08070f178110064401c11102c09901070020400205e1f00c5000e58003440503101c02804a804860311070b00402d080341e0142e040741303040e0f82c4220300f08405440c1c031680000c05440030b80b034064110350800d241040c1d140005030000340300340b6640f95240000ca10440000c44981c41c010403d82903800c00f0007512005054120120a10340500b2429410100700c11207114052000ca83c02101d245140c038141c078841c1020620030400704981008005440d002c1100d200c1d0041c9052000c41000c1441c1038000b60410b242d03c0d40384a203540082c81 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 298779757 1250 298778507 298778509
    0x5100b0f040501050a110102070c14100e0405090109021e041107030c030507031101050f091b031b0a05310501120b0403111204090501090501051003110f04080604030e0f 74
    0x801d440480d502801c1503038072290070380c0040c0c910480040a10003150b00c08101c00080c400f400403100103e820102c499501e00d83c0040034400068480000e42021074007809080c1802d09182e4002580000b00e00d00018005125a0002c1c10b608031240044122200f408105215071519110310401303c0043c01c0d4452800d0842c0c1d601030546505418040d00740100490018181801181c0090101403090020401c070314201d050301910000503036000e0344030310618803082c440c00716000a100720104003d0041030000030b50742c842e0341d58400c81e81210b03030800010200064070351070310001c80b00c0d15030002d400101103a468070984561908090180f100c16030901f401000104c2825851615490300301d00d94400e140c0d40c908084c0c42a4400040311840780c4100c00e4190403240707044014006550080c8020b2040b40da0b41d030640d0081e60400e0007004d80c8400e06c8140030085900a0b4083c290b00d204800802c0c2c03e01261418000050b0066400203180c0d0300400c081100b010b41c2301e044600000c004590b04c2c9805402c402c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 298781007 1250 298779757 298779787
    0x2030703080a0207020a030606080d0e010e181b0c030a0f03050103020d0f020f060c0a1a160c050106050a06120509070e0c0d091205071e0203060a0519090605100b 71
    0xe0074000b8040e500007195000d40d03c0360b601082c0507540000090203400c1e40e034a65155075400006100300010708145034001d296124803038540982400524820b40200e510013151155903014210300c00050400707810b0410920b12001515007241100043c5486030007080340903052030202c616103402c041c44c203401400140d0300c80680c20900e5400050356541e00d012803001c241e1203801e10a500ea4030890100b9452081c10000441110f0507101d01a81380030307240300d50b400740c25200e07003681c65801c120109102c0e032183c14400c2e000d00b4111740c014030000c01d000b5524004900961182e4105100040702d404041080a565004076034000b00180000c00d240d40c5090014907015002034100c1e044030390b0001d001c0d000c50340c868100840b0039810441e031118402c01e4079001b51007540944003ca0b58074400f003900100490001a00c0c1c0c4110340c014005c0c10742c964440d42000c005040003010780c40300000c10030500c00d03100010711516034003910070280010641085000782502c6012680312402c2c0040401c4262a5151a1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 298782257 1250 298781007 298781011
    0x90612050402031f0507031a03071703130e060108090303060307061d06031015020a0b060d0614040f0c09020901140702040b0d050d080c0a08180f0a0b090d0203070308 73
    0x88400010640c4a5200090800301d0000080990050340c05181e901c41002e40e11480c01036650303440030021021210480142c005040035540da050300100010450300c59000710340081d114421041d2443c004140300c2002c00c45260780c2100c034240440c0300400890f5604030002c00e4110f82c03450b0046003180340800029540b0760103070040d41c1c04c00400112a10040c2003070404445240700040883e5202e160152035080c81524a00c03038102e40310469144020998008a00e005d041c1e80c00814022a0b56030744e106000700195a42c1080741d0f80c90380c8040b810040920840c007140100c0c841c4596a400ca0b034036040c02c00840380305420502c5468810410186a607030024550044680c0520034103480342054000140101031407203605800c480440e84620402c034000c10075000c1d07242103480700b00907902ea10000620341e000d50000807021400b0b200125491000c00541c52142c070441504880f004160391b00c0300c0307041640310a011503034500c0c1c07070080c400c0c1c640f0b051014201181c2035100a5040250680b0000d00020300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 298783507 1250 298782257 298782287
    0x61e2a0a020a170c1f02040b2803060e010b03090c0405011e0501020c0f2b0f06060e06060426010c020a170a09181b1e11060114060c0a050c010207060906 67
    0x7282c00c400c0c0480d1064054078008c00350441d04581b980ea44540509000c0d986840d21000d02c42d0071803180075018000d214000c161030034103090242e40e03801d102180080d07501c040e10100039441880580201542c0d917000d01d07406820342070661600820604905c46455003d9042103041d0340043e080381000f03499840b1804400c8004a032110840e039000b4050320a1005843d002500451091441406000301c0148441d182841240c04011007640e41c40c00025030202520030301c0c0c1c0041c041000b045809410014140303003c044800d81400c424020504608580100d00d0b00e10140c3c0185030300c030050201c40745c51050348101c944120b510740321104000910402e030368014842078184200301d040240c560b5a001d507681041c181d20301c541c84030340b00c0b00140101803204440750541c04400c520340c0005109030f04c0b680490043c14002c00443e428412480160035003c09010341055060101c0d00c103c107420030004401ca8001c801901c240c407203040009091034060341107034080c4000c52000300203c690201c0c0105892079 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 298784757 1250 298783507 298783543
    0x9120e011704260403020301050c1b03130303031e06091517030714160807030b01080f0c0405060f06040e040506070f0c02010c1703100503061e2a0a020a170c 69
    0x200d4035107940303d405a41c00180d0550310300410015101141c0000f40700306500c08046600407081c580c2c41c690343c0c1c8aa003005250041c1a4136042001034080d4029001c03d01d02c40580f500680c4c029084442110580e52003881066141c0c14224601d40c3c0301e40d4800090b000b9500c04103c120000304045a91f44201500104510011b0f02c0f58140900c0c00d01100c00c10501d0901c001c040075648940003a901c01c0d1a000503140c4950305400011001d900080c0c030301c0406000c00203001c05c1e40040f4100b00080c5001400a42c01075221140c41e802592020000c0010707202c442c0030101c0341d0802c3d040c950b00c1c6c503100070164414401042c1c5c942040a4000d03500c040d10a6091074414040f0b0a11b2403d004c502c4801004003010207004400c0c40380b1882080d0303a10301500d0041d41162004d60714441415444c1c5800c07170810320702c0b29a6001182a0b091a280c0c4140301142c117030b0f40d5440c1407606600c03840b01e5a00640804005800c608400001c204d81200108154004c2e84096800d2490804080c6d440c3c20880c0c10000c9100c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 298786007 1250 298784757 298784813
    0xe0a0b161a01060309111c030c0302070b04081513020114090f0918060f07123209010c090f091a1c02010e030111030f070309120e011704 60
    0x300c1c4841c0e05030301c0000c03003a94000030340d6503583c0094060484080100c800d4000018607400c941444042250300e50400000b440d0651041e071016240365a45240070703411070050801c0400d04801380b100420041100f6402007171804164202c4c081052000380950051520051140c00981e80c060040300b5411581002107a64269003000280610742c2039014036080300700f50b02080343c00f645514401c11514404400d403029980c642e0300c1e01d224264220b90031008140ca41d40034951114207588002c00d003400c1003d0701e4550b200f03440300c0d5041c008000a048203622a01c4420060707040c03002e001e00d0141540354140144030a082c40705c5c0081c0c41d4418020482c03201d41c0c071003946500c545d00356206404104085c0108503102c2510b41c90f59002403c0c10801e9011600d503044400e5582014072855000c038805003d04c50941d200c6d980416440d85002c0c5c0080200341e07c0f0b0403084d000c10030340d008001b50a800358070707520100020b250026000955030418160003028000800000c1407050707080750003074465281100100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 298787257 1250 298786007 298786013
    0x3090b2a130501051305042a11030f090a0e0108010e0708160b03090a020d050303090111090f010c0507082b02010c020c06090103320c0301030c050f220506010e0a0b16 73
    0x910322903804194414200654203403c1d4640160f0001562043c000c0a040b80340c500307102750703460302c0d6800d204816940108108152214140090009480c00a2844090958075a10300b0110a130a800040899541780110009004101300020040c041d40c030107007003814601046c20300c5070020751040301d400310000000220003a40c1808004030055000309035602069050038180e990b60070842d89403107158a04400c034444810044187c170400e003801031143c5118002c050046030070403140d4000b140c03c0e201d400c41c08a0142014407011382d0128010800f01e20954115a00c0d85818800780707007400c156450004416059640072030413140c4050241ca00655424501d40100e004200100c2c6203240903441d4030341c80c8600b0800c2400300c0d40d45201200b120540e42c458954401c2244400e00c4003c0c1020b4000c1410402400c000d45802c0c12960000e24100307100220703040c00b101044280103076049490381c5408021540d82c00802079000040d05554580e9818100003802c0168441d404280d01c8020042c5190420 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 298788507 1250 298787257 298787287
    0x50d03050903010f150f1811091008040605150303030f0606040f0608100f05090703050a02070b0106031e0c091703040b0a120b040b0a03020402090103090b2a13050105 73
    0x250700c0140081205101914450700104105007030441211000d2074002280c4040d0041603091b0b862080c2c9200700d900140f880c030402008400c1104000300c409000d440030303568806003031f00300b118080c3c2c4170fa091500c1c0900c0c0c07800450320011700b41203289443d1500d00d00c103a2030000a40754070010b49003908005841e03c00000798a40195400340724090704140340855016404940c9a0096403d009641c40050310754401d0070503400180140740d0402440d0000600e0544250402600f2146949006182401c26103548011040982080380882e0b219241c2c0403c04800e041c1e541c079040b8820300304114035080f44034020710040c414415a00b406002205099200d8024001c88000f80f80c984080742c1d6070b0628a40103060100011201c1c0015460307d80042c04505080c06400961500206012641c0d4256070800c4020340145551074105981d80120b0000501c0007003406025040340034440c8100b03040e4400300311190590301c0c0e44078011501404244210607806081c0340980f402403d085440e06141d078140b0f80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 298789757 1250 298788507 298788517
    0x103060503160f08012d0b06161a06060415020c1e030712050607050d0f050f0a0e010204290c0601060c0201090b091008060d050f0c1f09050d0305 64
    0xa8140101100070b090751401081039000c42e42075080c03682e00d041c0d5443e8400c4c01c030340c41c02e4484607040000c0c40c0b15440d01504803510f40d0f1805c141410020b11014248041245500326814440107040301c1e032010710900542043c849840030840c03005140515021f400b20303641d80298480c070000d200d041461035130242d00034056603c2d8900f003d04580d000c0d1340280c200388820101034821601a0040c5070b0003040c0b2080c03101442e8131264110000b05801d485880c07084503940e00c60b501c61000141e9941100b2090b0450740201805800c102001310040d0500401031001c41d41034048800c0e49031301c108020800c00022000c000301c0b0780707040030600d0f41000499501100303d2040591f0746119006400010070416000b8660703800d45d900030707626501020780f10140d481c00c52140c2e50360140e102c45882178540c01f02e80b04104c0c680d0b0000c07025041500d200700c140d403034928000150801013001d41040c03030121450305280c403040100c1c1010241c1200320b11030480c2e018207006102d002e003c1c01022406030b42c00c1814040c2003190 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 298791007 1250 298789757 298789759
    0xc0615030204020c07090e0f0d08070306030609030804030801060903020d0b041406130c090903051b030409090302030d0f060608040602070206040f03110a0b030702030d0e1c050d060509010e040f0201030605 90
    0x59543c07a00180895110a024040c0441c4249040b00c2c1c20b03000000008c0300d00313407245944008c103440c803a441e806a8210100500d10300405403100004030000d80b240c0113088916109445541e69400d2600d809007200300141c00060800c4121401000541d03111442d0f920440e4114002d20303eaa19a42000700e20071405440342d00c8548501424407884043c684040d100356030181c0e1a40358401e403114030103c2a1500b4003006030029000b07000c54110003181c1008644095450790490b464580d40d050113901351502980140d02581020501400741d400a00440c11a0200c0ca001044000c1c10000060190070001e0070241050744e004c10040215140d42c400c450143c0148592202c40640e03d01d40310040710b24640249010f0b60200a00060f03100b180400e480c02048550051428288071a240d0f500900004011f0490b83c420490302800081444c400980d88081c2c1c0d0b5107030380d6503041481035081550b60300d501030344c00b034422480100100702e1410b40103a08070760302c40800c05d00c6030030b03a0004801400c5290065 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 298792257 1250 298791007 298791011
    0x150603130c030503070b09010504080a030b01020a0507080309010210091e1a010b070201030c090e060126010b0702030712111c050616020f1c0810090f0f0b100c0615030204 75
    0x20003803060010103040315910075503062005030b0714081c80902760303030054030300500400043c051610306030300907003141a440f0b0042c412030307241038800d4948a2428445030f010790104d42000070400441d5034140300342030b0030310000d4105120703001c0c01d56a0108954091401005c046000c84400000c00c4124a0004642580c081d0700140c1075844603064021548510f00c1240070074641000054003030700441e0380c0307021a05266103035181669284015a0290001d800360702d203042808181031200c040c0000b070b8178003814540e081305854118078414945410010341100b014014555a203400088848210b452480310130366080c1407005100003a9907140c0980304006265000d45000c10401b81c0c0e001600b800b03130034002c1c0d0807a2100031070113049540351010310b00e103400c50003d1207082c006e005018580158029520000742c01c1c81135920b010a00c1201e500d0356002c4040c9480b001c41c1c4138500320500442c450300c001107488005404451502422025041c80001d00c00b5844800401c10754041c000d0b040011a000740c03007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 298793507 1250 298792257 298792259
    0x51e0a0917010f05010905061e0f0415050f18060d0c03150c08011d0a020a1806090806180a1b05040c03020c010c020708030a30150501020303150603130c 67
    0x1c1e10b000c0c00b501101051110710b03150001031042030a010b9140102400317000b02244556103800c00c1081000800c509070001000340f42c145a076115845a202400b0500320f4109100d411700301089071083c0c07005212032044081001b000d41403051202400e0f0012012141d0f01280015440c1600390b5503890750010344000d0203048160b4504145030051000e40126680740003050f03172190094000b10500307800c0c03500d4a1980e48001600c0d000d02d035009204035115418105003c5011100849006800c0d4100e00c0010309a00001c0244540400a03a5040344202400d03036560744003600300c0c1d6910101c400c1d010340342e80c0c051140541e141840c02c48540191801030001d000300b840d041c5003d0044d42c405540341490350f20345513070418007074070205070a010745800070082c0d032503d000f00d4030071111403450081c1050407001c000800d61f0b403104140d0401030b9000c0004070200e1003100c181c900c00c441000a600c2181950401c10030400c42074080c0524585030403003143c0031a2a600e404081282030304070030b88000c10903850440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 298794757 1250 298793507 298793549
    0xa0306020c06062d041d060c0a030e010b150a0c0606080f0705030106080a260a03050610020604020a0603020a11070611060a020703081303030b090c0a030c051e0a09 72
    0x5800e52061400303981c18408049006084000481501100151900c0e0002890040c0c50160080303c2120a100d510544040172904040d040c0b83c82656010944000018030b1003902b070b0540141a0340e42d1900000704502c510b000081441c80c03807110440507420b2800203200343d08a01811660410315004a420098261100d01072507540b20126400c2d58070380320b40c0d14006400d00d014014013041d152401c0152207682e40941d108424020403030000000d4100d000c0d0840000907001c0060315a86034250340104481c24210140203120324440a08000c540080e02000050784680a2401c1165054500180d0f107000c81981122505222810810b07032b402420800102c40303034031441c4c2c070003000340c22019101071303890340020726040344100200240462074110000b0040c3d024481183c80503800303402c0c00f04103070464000081d107054084031b40d1403170300f0310104d01d4100c80d980c54490b1041c0030256040c06481c0410140d00456004000c00040070b0403078002986080c007500c0f61000800424110307803960707181a6902 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 298796007 1250 298794757 298794763
    0x402031c030e150415110d020a0302040e012103210e03090a0e0907150509030115090c090b0d18150c030b01090b0d0f2004050f0405240a0306020c 64
    0xd0820740e07075204034502002c0c01c1c442140000d0103075500030b038045c503900410001000609011006d14400c03502c14001c030400e499081c0001c100040850b6401030340c4601f0212500e1410300180c0040c0f08100f07180320081710300d04410035040c264030b0301801c10502e01c2c0200803c0c19540e031601d10f0b03840b1b220381c18040f03407a40711840080905103030034080b11012019522000e803000c007000d046550f000b441e4400001080355241c000301080c400c0d0407524090f864900154042401d481c945c0c40496000030140c0800c010f005900c1c0714011000a032450101c4a00345010142d24441c091100d01c0b1814941d186940c189a0000c9540c030105150b000070302c0e406541c00704aa1800510b6583c24000111b42088080310b19584180d4400c42035038038824503035003030a00c0054100c004114040d03c8500303542d41c2c4c00c8000c04824500046031018820018115076990500c0c050003980c5444000b4640030398101424002081d40d100d00040710160808000044109000001481e10308941d002800080c40041e0303603d4111404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 298797257 1250 298796007 298796021
    0x60f0a1802040e091c110a141c05090d0611070204090b040b0108010902151e0d02041706010f1719030f0314100635040506010e040206040e0402031c03 66
    0x78200c0e8101d6451811554944200040603000502048502103220340034200d02483c1804078000c40d01f01e5000b07551001511040b04010100e1544082200d00c45010400c03513000c1c903e1000d280160a00c800000850300c0d0404880008011545420040003956804825900c1007900100188195081d60401c00c815003070984003601c8183c03601001244422050081600345503000c0d1000090419441c9118500d0304003d000c500e50740380000c0c04400c48825403011780075031400c0c44030041c2c0d61850f1a00700061000005509596600200010044180301900040441d4056101c010982d083c1c915200e08040492141c80f41c0041101404818194041c0f054403015145031001c1040d842c074030001e11400f010840350203640f0709855409101c0a48540340c1c14100d00500d0b017040801642c60301c03000014003400c41000c0d00d0041d641041109000f03040021a0040c400e0900b00c2015013019004603e41e4401c81c0640c01c03071100000c01080c11900e0400804e4240c0c01090182a000071606400801034208 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 298798507 1250 298797257 298797269
    0xf06010e040219060206040f02030109120e0a1d010504020c0703060203010608100602211803060f10050a060e0d03050d0504120e0f01020c0d08090a030c060318020306060f0a180204 79
    0x100303600c800400080368503c4007924030f250000c00389540d4980e02c0c00c0364075104180403a09552101a0300c07002a413607980514510f0716503101c0e80c1c0f0851a102c18010111595440302040d10805038955074440c1c00200120b05441c82950050b03070f50140c5c5c000c5146000e0188e4002400e0f04c0c070010000503103075405000540103550040014440981d1504100e135110a50401000760248140c989080500303018002d2400c002c01c45d1021800701c900390006410041c048800c4441091181c04105060303040c40c14541c080d24040f5014010107041c00c0009000c000d2060016004040309a800030516010b281076854000140d41e0900551a2524026503414900c0c201040403900040b0800c01a1610131024a4070340010383c020302214074040200401c42e040f0f00030a0380c40f114104124641038444982d00d80166009144545089107030040050486005003241c0041480307042c2224010f0740c0c0481c84c543c00c09412140e030400d0898040c0042c0c9400e03043e50200000050801034840500740c15000b030411108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 298799757 1250 298798507 298798519
    0x6030a202704052a090405011506020102030603070e07120203070203160609170906090d08040902072121021318061e05060406080933070f050306010e030f06010e0402 73
    0x40b4280f061581c4041440c203018480003001308503200b0b08104a0301340e0300c11b00980020400ca08002010b511440b00c40c2c00c40c00050b500082040000c0c00c04000000041c8440010a406807600340350040c522000d0b40800c0009a4002000c80c1a0078030070000d49508101e440c6100c0c070000e103c0e140000007081800070407220410f0b248448a50f0705018002e0b95503094010b0107007071070100c1030310420541691174201214101000c3c400400c0c4181e06c2e2001d4803480c0d1280f540c03500ca10042090002d0300f042c05111070420407101c10318482c2031b00c4d522210591442040b8a0142c0c46c0c050002e0302d108440051740001c200c04080213a0300d480c00c5050b80207941200d10540900700300440d12020101c0b40101e0340034040d00204200010040710b4895520140d000d801c5074203913001c0350740e211618840c4118014503920401000c05005101c0e1104410013600b1903180d00380003140c070300e400b01d0141c003500000b00007905111041d0800c000d240c80500040c500700401f5810345101d0341c1c56046100340c0803020ba4082c0c0c041c030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 298801007 1250 298799757 298799773
    0x4080903010c0f120c1b03030906050114090a02041505090325060f0c05030405010e150309010f0f0e0601060f0507021201020c0105010f080604080f040308030708090606030a20270405 80
    0x2404c0e510841c0715034040e0740e5412410b002d84240145240707000348012000c140d80d0320b4444c000300f0308a1003624040c0003558061040000124100004540301600103180c0c5841008100311803910480306d46c8020b02c090414a464200001c0024140081c021416240e00100446a100c28005100402c1a25480e8131105840c28075510100c3d12416056802401503104010030f001640c00780140b010b0006000303103085c1910704032500865144c0c00c15100c0d07a003169183d200007a05a0a0b03801505000211150304100c64510101c5441e903410041c4218030034003d0040c000054903100f141103602c01386c0c0150210114481010055000754010042c14103135500e0f0100101d950040040d44034102c03007014004081d81e40310b94807121407540c060010b40c40040b500300070000001d030410001e10320900c01d5840c1c0595924019003410300b4080000c02c070620980000c4454000150007824214030042c02072540580c100039140461190311070b080c4c03800400c1c0f01401c150b103407804504c2e801b40d1140e8030400641d0094 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 298802257 1250 298801007 298801037
    0x30c11010b0f09090712140d0e1315080109030e030c0604060207060e0a18020a270b0315040501270213050402092101090c14010206010e04080903010c0f 67
    0x98081158255100342c410360100520316080c0901a0884010000c1d0354515903a103904504a584000045591400501209141c18001d2103540007421081c00c040ca500300b0b607240003130120a15407042d6010280c1c6c1d1101c01214800840c3c10101034003000c002004040c00501f03000d040740c1c0c0c84910f02407092180c0c0043c1401800e103441a1f0303080722020b0b001001d000d801c110080e501d041030b20a07000e0304182c0100e4009200d288140480d52480b000080c0140d4a1111200080c1004144030040d4004400055014241440c0348440c0c0300316408a85281d44035182c2c0142d00c80d1040c106e0143d0b503442802c000001c03481d80071300d00d0480e02c0b001c00c80040c2c60000080c014284140c5c02a003101a4006008400030000c5080a0700100031064005115080c40d5900449140c5421040c182090042e90354441e90b0081103103554150010b01100c6030b1400350350504800007036407600140602c42440011001040400c4000d4040e14001f950080081c400f05a03840300041120403e210b5490000b4080e60814440e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 298803507 1250 298802257 298802261
    0xf0206210a0911060c0a0b0406050f09010902060a0f020304090509070602070608160804020f0a0906050109140f0f01090b0f070b0c03091b03100e07050f180f0a0609020703030c1101 79
    0x400f070703102200103001d4124104000f503982050700440018050a03140c840041d000711100e502c00c91054800144a06244e0001918288010501409a1701d4844d074000940d0320002076401d19032030391401c0701400706510012030039405035901142403e4200310600640007404140001a00d10550858805c030b9070b070b200c0c100c0b03060030250ba99903010200000c0c0f510645108030440c0d07034890b0001c0c058120801170700021a1103c84550300010b14955940001c1c01170707690103919000100496600144808200e000140500e04100955231042000601c25940b070390040100d84010710741014500d8941e940581320700c40a501c07031981129140140e00c0050882c12040301039a0094480d135004100201c0310750f0f9440040303410321414a0f45031003000200309200720b95003c0c0400c280d030424080d1041514107001c0c803c1e00c035000d50034540310310310804080e9000c1160b141484c3e40441441e40d028150740700e0b6144440140016000740c081e0318000207400c0700341350301900000c10408003580c5003920044800c1d00142 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 298804757 1250 298803507 298803521
    0x81209010f180515070506160912081c0b03030d06062c0d03020f030c2d030a1805100324050d0213020405041506021c0c0305070f0206210a 61
    0x500c0b020100002d0000c0d003003021002c0c007400107440311546040c08544a2901c0d2140880e000b004e440c0000507403518856004281030020b1580d00c15201e501655940d902a850040340c0c14510380c03101c483d800b202501c14a4000c4089200081d09a0350380d184146118005030175940907510114000a64858400030740303c10065103a202c0c031040408005449007000300d01445140103408500c20341c07a800c2c14061080c0020030b2441101d800402a21003c0700d00d54004405408060030748208104c030402c2d0b849000700450314103050600d8811141014456030040320081d5030049030700010790030711000c001c60700345c0d01c6090340100303081d141200c040340302c2048036504445004041c5c000c130700303101c903840142021101c042122801c001c000d030034507840d400400e00300d5000310503a0b03807a055288810009140c040c881c0d0312031a000c014407240043d0b1070500c0684000a00b02c8000d0800c20005102000d0200200340e54005982c000d11080e6a07220345c2e180242c641da03145140c0c0c10010100008039242044900c80c404c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 298806007 1250 298804757 298804787
    0x6010c0314030615031303120e060402210304030605070219030504061409040f090213020307080402060304080d050c09030d020106080706080405070e0702010f0e060709030813081209010f 82
    0x781e1228240801000ca500094500f42d0807000b02c5010581c00c00c481030113103108054442d05e40f42900e101b4140103002454a88501c81a41c0c508001c20001070b81c0819900e41c45601550640707258002c803071024800b051045122580341c000400c000c003c005140d0040b074003d0081e982144c24125101894140401800d60020045a8100001c1042c1c0c1d004904201c240c0d03410090190a020800c03011070107a0b0440c03008100641d6070b4901c00011890045c2000752203409003201141113117000100039055030700240c40079114490201c001400c00030075804960204001c00b80c04d103c642002c60701d41030107400903982d60344240039040203040080d105118031812500d0260080100901d081c906443c000300c084d006951350700510602042000b00d040701e050054020b03031300005400a00580800442d540003403415643e420000a0000c142d40c094202c0060300d80061203640ea5990251680c2c0080103181c3c041062070080700c803210741003100b400107400d807a80e0a0b00c0303e402907540c02c0000c80d0740d048403803031340 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 298807257 1250 298806007 298806017
    0x5030f041707021f02060f091b130f0b0a08030f0d020a02010b12070303030b0f0906040e240109050a0605011e0201110403211128021c0b06010c03 64
    0x2502003450342070a00380c0410000882490449140c000c1901c0c010703002c0c03d0301952814805000c1d0034a60420880da400140184a90128180244071315142c40c004114941c408041d030701c0314550350b03554100c103c0e042011130000b000304005a060321400340071038940162080307540440008103000088111044200b006100d90714103c01010f410009404c02050001190f40e00d40054903140c64800360050451540c200070700c800303440d614000b4299111507041d02c4c00340311064511801501d0325011079401c00d004560104940078082586803038001310300c0312451000c2c603030903a8807002d400d50820079050347c2001c81d051103e03650b0490b410302034030030520899000030038003e0410070030700c0f85904030791403480c1d81e200100f1023a0014410703005070f4004e9001694214900c40480941564018000d103420b4107504083d8614000c10324019119100320480c20344030b401000100180000c0d0301e6440040560080c0011800e603040f48a41c0e0071071860368000c941c080703c550003003922503014075038588a4590582da0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 298808507 1250 298807257 298807261
    0x9050109090209010509100323010c020303250e040f0905070611010e0705030c010c030c08040e0109140c030a0e1c05030403080a140105120c12011b0302030411120703060507030605040c05030f 84
    0x54903c00f01595001c02c09c009130704002c06201000280140106020154019603c03810003600268500c005024411000300c02c010883c600c998100081c2c04d03003136400315800915418014041d202511a01000400134002c2074170208000c0c2c0c100744c180308484401c40007081500e210140850b034400240c0142c031341c554802c501d00789843d880784511001c06442454000d0720803980380c0d1202c3c1c07a03130015004482440c04200040c030182666218110110044905a612900384405921701e02e00c00a0b0281958540f500f00e8500d10b030204004042040c8040c003170507500088102d200a0141d002564210005a04500811082800c070b003e4400c031243c00a03231254841e46400304000c0012440b29a00403e80118500c80002c2c0d51503400c08001d20401d00300109a2040b4400301101c06107121078480b003418818400e00c0046100c12403610040d202c291a04c101103081c00440506c0e2404030350006154030308010800552036070603000701c802c0761805d590910403041c0f032000a03110341c00115401d0034141d01d2000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 298809757 1250 298808507 298808513
    0x318051b21010911030d1d0a0b04030507061412060603191401060801090c0504051201021608070203060c0307081302040b0d080310090203062206090501090902090105091003 76
    0x310315600300100401c0300384078100e400c07401041038510118481c400d0b503492035403000380003070380c014858440000c6001d0800100428009800c6030040a62030745280003030072541c00c0580302c2030b03c1d0002401d28849241d45442d542d1801d03035a9408036006940000302c208500d000d003410410252900040c604095050585d41c05090001c0c58200400c1c40b904100703080c442c140009624410036103505402c400e07100c580c1d81010000303004000d048c2d000d004a58908a4502d039a0355203c1e00383c43c2502c40c100c464800281c0c0c14035802d406800343c002d00c41800a11001041c0070000d4502c001c0215500c2070f03003610241d80c0c8202c03034101e03140000c4840c40c0200d1400030000d440b407859070021440103071009000048091180e000300d41c42120024040300d0340d280020074042d0810000740c00300010701040c4410351461504401089401803d141505422980c41c040504030104c0c0d900842d003e001012010046982c0d154444405462841e906a0043c040000089082e040c40c8602902c03c4c40031329040d0703540600d10741e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 298811007 1250 298809757 298809793
    0x30c0715110d0f120606021c11190203011b02060a0606050a0903020402030603010e120d05090a02180403120f23060901050f0112051003140303040b0412050c0a03080106031805 77
    0x90900c2003040b00992000e08003e00a10985c0d01400140c2e00501e000c400408602c1181400502d5800c10300c401303074052400301440081c0454800d04d001444179280081480800e02400b01d814041d4102c03144007440070171f031660015043e4800e00100c501807000742e0f1f48540039101c5209502d02e04000580c0c142041c80503042603002150003801c0070300001090418280c400381008124268407490a60002c0c40c9000c82d40240202c5404c0721841001e4030318480b29a0010308464800c01c90302010031454800902818020b0f4600e00c85030082410901c0920034a1880c0c600a06c0a05800a50070a0241201c0324040940f0001413003103002412540c42039003094200b01182c004c03c10b070141003281c42003c80450003030074040c490084201040c0841001e007145000c00d80ca00c0b15180e03482c80d0341e00520401002c11140a0300680007034200001726081110031000b181c40344100e207035020b03013849040d43c1102051b900032081ca041300c0941d1742c208030f5002c400d0440b9820b1b07030000300050a6940048000500c100f241 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 298812257 1250 298811007 298811027
    0x3010b031e010b03060a0b0c1c1e0e01031a01120218041d0706020307050d05031e0f0406200717040f0807180506090a0903050903030c0715110d 63
    0x21007110844002080c014020112090b000206162804000d0107554141005000040d00d82d038810682002100e014840d6120701c2c00b0740340c1031102001003a40b1f41842c0105050620201c880d02000d0840e04c0ca0740010340700204801e0800d00013894450009449840f100388414414416980e5880050f1100c01942c0a500141c0d03847c1480444110701000b1552184603984001144101144d400304c00300340101c0c01c15401d944035000b5500b0401079031000172000f060095903140c1c00e0801d143c59842e1000349c00490300c0040407643d91414020300748007515840400603440340b44148018441007034201c00310714495121001890320017200703110303810026200d5250810b4065020418a00f803554440b5080529030b034035442480c441c1c111030001e2011410308003c190940680034028041414100041001000010701041c4803076922100101010300c22000c8491984d4003c00301ca440300c52058000792288a50300c500a030383c402da2024a82654021100c4d49001c809a1000d000114a60a8169414100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 298813507 1250 298812257 298812271
    0x6112404170c07140a0605120703020f090a08030705010f0b010f0507062c07050402040e04080c07030503130f150203070308220609050d09051c150603060c08010b0c0303010b03 77
    0x20522049074002c02c100b205900a000741c03c4e16042025030502403000040c1d15800c0310702008801c0040c2c0c0c03007036070103001c20903001419440e005940e60f5910385144140d018000c1c5241c0d02c08002d580000b29200000050000340d4040d80c001c0020000c61010380d81202c6003085414040baa001d002100114001d90180440c203002c5c0c0c0012501c0000980c4c0707442029400c1107880c980101030707180302420741e0342000f40e503000c0c01c0181c40451505040c2030f00b418411000030001440c411340000d40031400c07501440320310003e6510004482e155030460403107440c0c072046070195110071101e041001902122840c051000008039402a51030400b054070121030070f2500402803c031614401c2c5a00d2502d8184d42203002c451030003030400091605041c80c045041904c69000c02041041803202400540c0d0baa141e01262551429140d8581466900d4514420480d20101c560780c10301d400300000500c078040c2c101e0000c8085560742d0500700e80c0c840c1c1c0002405e024801c3c0030031640d030050005100e03507a0800c000b107401010f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 298814757 1250 298813507 298813553
    0x906010e010e09040302070303090e28200d0b0102010612062408060f0106020c0a0512120301030606030b090a03170c0910021515030a260406112404 65
    0x5981021070302d01d040c2501c1c205c3c0180d2160f4003c00c00c0c180e02c446000f014000071040c12882d800c0019495501944014258010a0300c410301118081da0541c0420401020f00c1808001109030410400f4140c103c108418803241c14185108110740c070600c02c1d0400da0b064440b41c1c00880100c0c0d00c403240101818550741034610580701a240101200901c3d21004001c000d00400300f0f0300d0203c1400c108414185d01c04003d40d84a00210070090ba5850031220030b482055540302c40d483c4000e41081c1ca00b684058052009100020022003442071a03000102620700481c3c0e5030040ba243d0b074104980d6900304920240005045108805091401d554284e400403900002182441864000218241d01c490341140240e0300c4501c1c12147c01e05000815503100e6241c4401011201c07840c00426240d0140c81303001090350361680c001210003000120f090b0440180200419107890311800c0142150908016803a128403032031101c1800c00209107004a803e4005520100c0662965903c83c00441c01c61001140341b40c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 298816007 1250 298814757 298814777
    0xb09040207080c0c01030f0605030d0f02010b061b0601050303280903080f0c0d051e0c010f0606090e0a06031113090623060a0e061905031203010617060906010e01 71
    0x81d8204041d03c5200310300c4000e0316131004408005003c6500c200e01c5034040078188401085203a82c042440300803130f61746091080100058030001c90050061226160780100041964082d0503501984a10b07180c41840444000d80d0b280c01c20581c0e21700030307100300200e0107400b05010001e100a004106220307100c80e061600c0800c4e201d60b101c04103900314070b000030041280841c00a045001c10490628500f440303081481c039203818420398240e03035414800001c12070303400082e0036a034174102503000b4408040c4038402042040d0700c84400070040d034940e21030b6000c00b02111000ca10342904510132202102e600009650030002540c0030300070f03170421030320200781701c1c0b81d03039220325000f08251740101140101c104150002100307400801212107000036103200d00880c046c0c0b40520220064500c00d581040c42294170f480ca515110b00850b40c2103650340c200031703054094007c802c0303024883e000c065030517a086510307203107408201100c990b98001c1046403a694065070400c08518254000e40d0341540303901d4103243c034521071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 298817257 1250 298816007 298816013
    0xd030210060306021c0c1b02030c030d0c0b0a0c120b0315040804061103090a12050a140c040605121f09140601150813171207090f090905070b09040207 66
    0x4610381d91040d5031080c0c0024041c0da00c0040e8042e1099500500c020802051100000081c0304100818031720042501e100c050100390749d0100071241400600a00311811240c0c8050700503c0084003039811101e4407118004544540310902441550f40c24955441c280f0901025001019040e040031960705401003609488824513003104143c0701e1402002d03055601d40c549a0020140c82c00301d80c0005c80e58205000405480c0d840508030307400c0b81c1840c44018a50101c3d8105942481c4144100034201e41400d003680106102c04982803e140e241251b0800c506680d90041c418038404c20241c0c6260340e0001d83e540000108500900008910070300c00c00070300c440d0281d83d01e001143c21444100002d5100c1e600401c403040040312482400f031001e2074001c9440c2400b940075040004514001000080041c40f0240124000000e07a080502c558861009500b8804005400c0716142c0c01ba24120180b000004603c0e614203009041c0415407000040800d10f00d03011001070103822132158035510a40070080b035408 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 298818507 1250 298817257 298817261
    0x6070507081b0a050d031112100b0a08060405070c052a060414030106050613150e060703081b0336060408120a09020a09020d0e0706050a11030c0604020d030210 70
    0x5400d0507800141950f100341d080c40c526054121103410105418400c0042c04940d50100b60740c628100f0720890903090b01c45520b601e4005c64160810b0503c02d0002c10250340c0e10390f02510080c02140c05503820009500c1c2c0311800c82d00c0b007030000c0001e00540c1c89100d16610110880301001c190311b80c1c058480ca401c0000b000000c83e9540141d0107155024400b40c0006200d05e800c0c45414020b2404481c540c0c80e0000b124102e4068614500c01c41c09006507020020035054010a244c5141c202d00400c0c0e1640c0d2440c0e840c0141c0714090036114980e80441c0c10502e44580d405e000112801880c80640d115602d8214146086900c12a10507420484981d41d1801c400c2a030200040c9024500c1143d000e512940e1030821a1440500141000115401c00b0342000250b02e4050403042520040f00e03001d60388982c07001d0b005015000b800c044021a204071500090f84681c098041e00580440d03030f8420750a02212035400717139280903080d06066141c001c040403500500d45151801740d031031b05c24016148103000c0314881400b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 298819757 1250 298818507 298818547
    0x316021f02180d030f181e2637030809060a11030a2f0a0e0d0c12030c12090609240503130b040f06050f090607050708 52
    0xc402500070900101c21544501aa820748100790703041d80b419501510020f03c440035445d0344034107020701301c0d88510305041002080030107007450452219011080a0340009502c58912035808960a42d440300030350341ca03100e884495285602402004809042e40780d00c1e4448104400d2040e080c01000d05a41d011403100e800e21001900079110b100d11840d0220701c00b41400344c0200280f10480c640f50b9000203055149003547d8109001c2600090607003201c1c01c0301407410860840e1103000d030245040b40510341044400400c4085540d0362445d11081190b01480305070542c50b440141100d00c411400c0c426203039000c142343c10030b42c000d1404d1040c09400382c94010f004800f20500c04001490301c4800d2100340c1d00000c1050061555260021009a020364a001c107105600310960800a00001250550301e80c50a080c007544e0b080a04c0c0003040c1090310300100c0306079014404a07004c0b4107010000e180080381d0014240f04249a80281030142c0d2082003c59080e80941c408540034401402000303104900030f00001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 298821007 1250 298819757 298819813
    0xc0a06020d0e03030106080103080a050d02120603070f0b04090209030a02060a0306030b060d03080f0403020c10020703060b09070906030207050102070c03080903060a150302130e0d05120615031602 86
    0x10303907030360780d4503101000e403600350b040c07140280d00c1000100191075022107450304607500f0140d80d544074805844101c03050721898440000840c00850f40b900c18a141000b003c0c0951001c4044510840c1c0d100d440d001031840d82c1c4a56440c000c0c003400104007010300f94009105455008040c1d518100c0c665002961310340004c6952000656201d0040c4200624001b01d185c100b8001c990000c9010901c1e5002414024002c01d4141802800340108003058020400c400138903900070314200740c504050b90300a5031070655210689a25003440007a00e51401c0c0707400d52a025429035611069160b050070170580195104c8202180d20399800c1214402241800089101444c8180b510304e0f5244a00010145481e00141c0520405442c000e44a580903016414580c00c82e1b40c103440340a442d04100c03240304014905803507001c07a01c0c06121602c00160364001c1c010602180049903040305611041c05221300031440c002001c030b845600b00041b594071004100d0401d01150a40b0440c0c000f0010310107103802c1c4600c0135200f4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 298822257 1250 298821007 298821011
    0x705191505010506090f04090302100c180b09010203040e070c081209060906091f020d02030c090a1a071106210603280609080d02041508070507170309030c0a06 70
    0x249601240d1402034030b0040100b290940d003008459030001d020640a041c080d031007140d035406030408060090103000a840701484082090074086032003c4d0804050180c4201c000c9015030010440121000903035903404011b03401142014200000c0046510014100105009440310311900103121100100140b0400030503004450030a409003525000c000f401039941e68000368204a158100000c01600c80009126407840d403e1003e10ba540003403150141600d0306600010401007010b005000502c100281a203955a81c2c0d992281c60701400d10aa081c2c150054508002c05000700300e0301200a840c0784802400386143c450400d8040010010044a4007900c40080f81000341528060003105208032660134582c5003503200031036501c4200d0346200c00900040c2d80d84040000e118441080c0e40400c3c01c090411075071192210503143d000900f141c113107070014450100050b034a41c490000e8071040d84c2d0209440c004003a1260302d40305590801001c178081c3e88414010600b44032420001020164040e10340 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 298823507 1250 298822257 298822283
    0x13050a0503120a0b03100b011206030b150a14010e0117070807031a22182a051c1103010c0306240f0302030406060f0602100b0f0d08070519 61
    0x200c111090003000f120701d076440c03c1c007010341c50307180420084840700142e00300040100d40b510041c1c0b001c01a00e001004018a003e401004110002e03101a016038241c0d111083c0703110b003504c00c01400c00380c40c0c040c104401c051840c1c5900390354003842e08a00440b07414140000c0c1500800118840e042e000c80b900000640050180035a45070540b00d4103050102d031030500d117985402d280105400381900d1401581c51110001116042215a0311100011080200a08a1800c90300f003481c0080075a010019000700e1016040550381c4943d40d90200701c6402500c5413002c926600300900800301c11b0002a201c16150b102100740c1da640c207100322811260381d514000343d000c0c20301e183d4081801c044004c5031b280041840d130201c0c0c81d40c1c1140c000c1039442030603e40980d503651a0710300318020f8925a44440d440305c03043c54011036100d8001c0303002000301d4100c0b141040250408401c102d440125400d01c103800c504103444000c0494081c40042c50054007840880740d900c800025450a070400444040d10340000c000700d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 298824757 1250 298823507 298823527
    0xc04140708010506041a09040f020c15060a030f031110020a030c030e030307080f0430020f0a0c0504021b1204180504022d0d110102011d1513050a0503 66
    0x1101c103001d044107a0760b003418113040c8400e514500c4113451031003140c00004100040140e480fa045240070180301d220554507007240c1c2c801e866590074080c8030301c0c0d0000b0f04000050310508080c02c00c0401ca82d009100d00c41f5181c01c1d41c40c00c0d200c030110003003059020700500320060b030000c84c91700051491000e00d0f076000070f000d111824000c0890310131410f401d140350001c0082c00112076122040175000f02e0120840702441c1ca541c5081501600721554015400e0b0380300080002c2104005601c010001d40c40d0252109a60000e03ca6034480540001c02000c41811003800c0c84123041540c0500500030b003142e40041c04010078100b0509c0c082c05034030140c8856070001800d22041c40e024a40480c00d03502c045c2c042c4180c0c10240d0002e02601c000c0c9070305c031000000302c03c1e5854001c4203002222203040805010b6495031915400c0241c04030380000300ca03a0240d070801c2e20007040c480303001c20540c2600340998007800300260907519508a52002814240c2d03144114450701c00419400d0109001d10b0f4460402190740b0700e0003007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 298826007 1250 298824757 298824767
    0xc2607150e1e100819020913050910061401080109020a0201020408070b03042108070e0a05090f090f0c060712020a0206030a0c0f11100506012f0f120409090201020c041407 75
    0x4090f41c81000200030500c081e0304421390b64000d860000e800017685803e40340011900107003020458070b00350b070f0030807044c00a04a00881c4d42c0e81c0070410803109000d81c903112002c0014040d011002d95000946002c0104030201c3e056000c0c4c410340801e44000740c9010364410120349007000a801280c6503510000602040101c8218003c00b18038400b0541ca19410740c0d1280509084c0d8014003010900903801041d100c19a07800348503801600c40144007405c00e00341125004420801103801404511400c5090801500002039010f100e000c001c227100e05e00700e05540d80e00c0c1388169040c1c1c0d0105501c00d201c0c10f42e005a0311280618810300c0e1a0800081140c60404010000607440032040c0034852a42a002207100e0b0108060344540000d44001c286038481000407a0300401c2c5082d114410420404288040c0e08055803516480e41038004451865100f841c540b500e51010009218075000100030401141c5116000107601d40e005005658081c0d03910360114055419021081603d80c01c40e104201c0580c4d000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 298827257 1250 298826007 298826029
    0x303051b1819030b0117010213091d0f0a0f0203010b030a0f0c0e0f01060804210203040602060a0b1c060f1e05070206010e010b0f13030c2607150e1e 65
    0x10074078524682d4a113440703080e80c10f003060107001c1245a1050304860181025011611a20b120100034051140c0c0c4000107002050040700f40c14a1001c000032440100f007001402050f426028000340081441940d82d285540c100c1d018104d07055529000c60152581d01031200c071200601500410140c030005251460f05074440d030300000e00e07030200d01040c0401509015802030540c1c0603030806150366161400e1842141442e0700c0c1d072414160b02a81d11030720307041c1e011000c4c104a8080b0707021107907541c42d106508000d5880311005940c20400c88002c0e4510702808130b081c1c6d00250b000782c200040ea81552007031081594403c41919048a10710000d13401040054402c5a611030800c0c0b024048a504101861000b01818450092182d00204d000c1420340e44880440d465203034040795228a43d956450440d80d12041d46c4280c0041014000c1d9400c072183c020306407031380d69101010150902c6410440d0700c0f0f5510b0b10702d000c405c0400101412540041d01c80c139110403407a60108414100c0070300a201000022900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 298828507 1250 298827257 298827289
    0x501090c0e092107020a06050a090f1406070311060c0405091e06040b18100e06090103030f08070909150807050607050c09070c021509090a090f0303051b18 68
    0x502000b003026804103440207442c01c6002080f0400c4402d0a0b82c0c14207000e072110181d032000161000140f0076130040d00820054009484013044d05603141002c4090680d42c1c8280b035403070608290b80352074a00d003001c02004154400c0c01e0000302d24034044145450301108940189046000103003e10480c9422424a6441540c0c02241d02d80d40174030304400c0f80018000b8140500a64640032100f040f5599807400c544d070400a4034000259240003480003604071003d22801c58180352040100f041800c040035901e0580b905500c40083e0b82440003002c82e101c032001400c180400c03000020204c1d01468901034a030044480c0703424068544e06009401e810b15641c2d62100d440f802081086800094000c2855201683c0c2111440c031a80c0c1c0c0c05201f620400e605100c000e40c042160040c0304040c0300208040c101c01c210564024107265952403002040314109038000c0c11504190500c9000079119410903580801805003c0b1030110449003008540d421071f4101c040e0400290031415081d003402d040000101c0d00f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 298829757 1250 298828507 298828529
    0x110604030b0c1e0723070801112802030316050f1603031103071d0a0b030906040519080d05150310020915070c0509090307020a0909020f030f0d2303040501090c 70
    0x2941d80b29180340c06039250541e401505e0720001144441c0500010b0700410780e510003400f420004a0308000b095201203001c0c5c40e03200d49103007103a10f07035a0070704c0c8032000050103a00110716607110b201034007110041069982d02000030410032102041c0e0b50001070300c02d500c02d1400700008018146800b038265400c0c0c2c0e60413848641c3c02c0c410003072560383c001c040f01c1201e140020000c82200e400c01c08071340101050740004c90000000401d01104000000d210751150380a030080d580103501207130f81004600d150042c081c0c0780510a204e820740f40340c000c0c0d020540003502410b0b20340a02480d240441d00b031941440d0030030401d0794046031029083c02c24035010b290004284543c41e240040c5640c690010740b21a00403640203964180004110000070002c85030320396001090312040560b51036212014201d0310324220b0240ea200911440e40d803c00160b1039090040c401d020708500848180100c8030500d60444462620310b81e2900008002900340c000e40c0601d004000200d0180f01a00740041c080140d50b121b164020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 298831007 1250 298829757 298829767
    0x602010e0d0912020d06090b1609060f113a090f0e07052104020a0b12041106090406080f241302010309050d1205060609010c110604030b0c1e 62
    0x20364880400c00c03d94140c0620300c0300c4650280045000c080713001800070074591074001604d040c000321809552040510307440f49003c04103460f00444180c403c51203a8408581c0f04080d0b0080507000310030406030080400102c541248003140300e884460944048088690f03590b05c845415100d202c8520007070300c0c00c03a080c2000301e50701c1d04182559150480c0f01303403107a50708034401240d0b03620310a000f158400405081e4140481c4401802224002000d840480c070451041100264000e8680242c8004100c2081107422a82c3c1c0c0b40c6540044035034014403140d10410401100c11655150b20442015065410040038040c1c00942d0080c540950b09822034180f42e4550860000b00d1000c801d801d500040d0080281300c540b03c50720043c1c000e454055001040c90040d440c00102a6502000c02040c0c0e10b4440403c1c0729684400050210a205d0101610300180c0a00e070f004000c0b0340341032111100d58401501448c6059982d40310142c4035002560100c11120b00001e590b84400582410813a081d944904020310300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 298832257 1250 298831007 298831033
    0x40c21180b0405010204180b0a051e0411250605061507030f0207150e0102010501061d06071104230109050115030b010306030203030406030b1203030103050307080304080415090602010e 81
    0x18100c040310003400e205261002408102c001e40568004000c101c40d0001c003103018204070000381ca202000c4600a01110a000410346800740e01c552248044424000041c1c10a2050001621900716901c200729000c1109150482502c11003803110f0711049036402c0080f20502d4600103440b0043c082030311642e845075542e201c0e41980c204850321142d140c145401d000106a05c1a801c0401d40c2c0d200b000340880c46071031121110340100c85400720f0b16099008006903038031141d0582d1000c850020100858144038941d9050b400c03e10000c00c4507138003907114031810b0014003001400303075940503034242d0404564841c21001e888022140502400041074184035560529140300e0f0420b44050f8403030101030b15803840a10b0783c2d0203588a44083c40e006030a80c0c1c1d5035a10f030b40b40500a0300c05070754001e0040e1070301c0700020129032001c0203480c140c075880005113161000540710909aa00060400e07100c440d0708220000c0d07900ea41c100351100309401c40c2c803100c018501c0e00001900b103584000009005400043c3c1480c4a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 298833507 1250 298832257 298832291
    0xf0209010203030609150316031202061009090305090607050a020108073e071e1d060103022212170702012f0313151e0c060209040c21 59
    0x1c400da0a4405002907a1000d040c130221400500009030503004000c42c849426086008c0e400c1617a0054140001d040c80841040b40d1b41d0004070340c10011070005410a020000d41034020f1001280a45051824903080d0400140b031a400340c501100c1d503500200313050045580084000d40d0041c81d60400e1030382c0c1c030b9040c9428204c0c02c2c02c0d0b07015401003070b0104500108000507040e2403c54500400225260b068407402030909090101481c0c0c50284a101c00009042001403074056aa9001c0919800540c8604c8010b401a410940400038000d20112086500801800500d001042000d07101020030400341012628501c00d049110401c01003082401d0240c0d80085040720b00d28001160251b500074200c9581e454410209405015030000041c00e100154035001071174165003140410100e500004903060b9001d0304003841903400b0800f96026401d00600a10030012414018440907180c01c0c000c000007011500180300d04404a103000b44035026001440c1600840003a5026041066550846d90048 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 298834757 1250 298833507 298833511
    0x3110a140d02120d02010506041b050d02160f050d0f05090f1003020c03070b011d071b020102010f020304200609130203090a0209190e190206070c0e0a0b040f020901020303 75
    0x100400081c40d0940840d00d400c00c0248048990b00c0c150341da10301c0d42c100024081c04040e55103a114604000004590000d64058003402d000c0e076482e06440d10030008000f001139005244444892580c04003800c01040700b9500d06403070144142d000d04032440c815007001c1d001d0480c044043c020404c0501c61501c60b500c480c2c11000d61440115100080b0005860741180030344070b1129550f8183c0004155141049012040389040ea0060010781020000c05491700f022540101c43d50400110096585401c004802c2040d8507900d006100100308901341d04400030581e8001d0f5021154609810401c00604c0c46480300403da060044450764507140c4000300150b000420302c400542d003103a0000200d4008c1c18204241055143e01130650310092622440c40500d1031000f0514503e001d0404201000b1124045092405441048c00c0722001440070340134095940c00c4450110354010b2440c20108800b10940f003100e119080718000845d0691540040c0f00545280c00c4120007d2801072100708002e03a00403050325 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 298836007 1250 298834757 298834759
    0x30105100c050724030506030105071e17042001140f0f0c070f081b01140a121a0102010e0708070515070c08011a09061003020f04180603110a14 63
    0x5800d4411810441c0c1040d5980d0300c610501c0c0d00d90300104e003800312040c102c00d00500c096201004a50340344030070300d420303074a0460703420000515021ba003c2012164201d80c00d1107034401d191841041001700344901c0b0084003a2002c0d201c00c6402ca00084c0780035070070441000c0182003031900c40704401c1c0c0140b10b0510780c06620020110807101007213413a0040c1442003540c0da1a500e10046840f0303250755050ba64241a403d00a00ca028001d10707146c0c41c6403a080710285a55240103940301e2802c1160007804d0306160b0001440b40080084141883c00d141985000c3d0071405c6a4101760a82104001000a421902d51480c2441c0340c4e0456041000442c402041210480300309a0720720f204a04020a00d0129124482009002010682020078907820540c00202d23038000302c4002106610b00340080209001085850035400310390000601e81c40c0340306e07802030720b408801c2818803400c1a0300e070368075403107000401c02d41d500b40181d480c01d0400500c0035200c0011100f00c0305448450301c3d603043c6001c1d0b60303903000300d02d0105e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 298837257 1250 298836007 298836017
    0x1031101020f0a060b030c0114041206020910110d1403060d06060f0e0f0105090f0604110408010e030904050a0e0703060b010e0402030106170105010519080411030303070f021203010510 81
    0x11464590003406407001c04000041520400321036498094000c1014101e514028440c00f240d500d641c5d4001c0907200421046104410300b03143ca04500c1e858005804002102ca0a40900040a071600c90742140913203042e058035900c1c0301858130f01003145030032407440c1d0010410401c1c4043c08148142402140d40150003542c21000382001410f0100152820b90b21800c01000d40e00d01c006582d400b88072441e07025182d258078184140cad0707031641040882003080d900000e102c9107800c0421740c01e1905074001070400c0c1041e2112800e10b566141e500d401c543c2100411303204c54000240030a030740e107040c0c0315007070f8450741044040000b4844040c00c1075540201d400010300d2148d45201c601c203583c0c001c0c03407a00d56610004009542ea580c441100420158541501d05074040000002003030b0382d8001c0e01600c06141d1400d90022482038a9001100c5455000c0d105a490301c07030413509002c4544052000b94410103072511103c0794a01070040080c40e0900311716032414441d00600040c401039590800007034005e2810310380 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 298838507 1250 298837257 298837283
    0x30111032e0b0403140105070203130905041b0b0903011b02060c0c010f0f0e0d0903020622030c0816080a0c050607030e0a0f05040b09040b0f0c0c150105040e0d080103 73
    0x84450038181c190082e0300654400309000081041c2c004040d00502d100000901503622040d00c144d03540c2c0510881d4010138580101e091101000703030f178842a8810b0243e01c585c0b4040f07500202c01121400260408010030100141655490030240180e4030084610040700c00400d45241d002911840e000d0701d1141c003c0d000140f4201d00000035007042218140e4880100424000c42d40910010420200400c81c0c60140a49142d41140200c07460380840740c01508107480d0804a61000c440c09040c04e482f2014162170000220100e60f6400c103000c0903101d0400100607500301e600c0e0002484400741e00c0030f402030348030101c5080014414904c010884070305450168885425140540e01ca04aa1a80d40d030880d21100001035154610500c10040340d00550782000303400012401d12100d0201100d01808a40807900403800b5041c2440740c040c1c0c401001d10300c4500b44441520a5420030086440e60454884a807006000c1c41c41c1c2441070300b101d52580002842c004070011000740c06582c051002921511506039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 298839757 1250 298838507 298838581
    0x90402100c020d06020c0105060f01030e0d080705042c06030607050a051303051c03050a0b0303030c1806160b010b07050c1212040f080717070e062103070203011103 72
    0x4440018242d021358103544805480710043e0081c0307003c85450b40301d440403264500350b95000b4800c0c03001011901001d480c07004440030051301d000d10701030200e004001d41008005000310a81545c010000d20418007034520381c0c5d21946000c050f22000c0c1c03401f48290058030501c07100540007400c1312103001182c28520f89610288000c00e080100561000d40305004115041c03400c580040e0040d401000c0c0342d20704014580f100842c88044403c052030482e050343c0200b0106060b00001e8001c0c0801c5c1e0040c4100124501c3e540021170004e411806107003001107801c4690800300050303410100d002d0810141d002e4200449919841d80c0d550f200c207141c030300034200d0814521619905100c1c8061104010007180e0b034880d60b8084003500c6c0c0c480c500c03901000303005102000c204100035042e51912081c40c000106203480c10198186680c0b500508029804440a0700324082c00c80442d6001c01d2400441025640324451030042c103085d5100b0005150003480108100410f8400c48040201d0b4015541c641d201c001c281c0755 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 298841007 1250 298839757 298839769
    0x90a0f020412030503070210152106141005010305071d12030a02030904060f03031e03020d05040f0b0708012403090b0903031e04020d03051c0615020c090402100c02 72
    0x1030410035002909040b0107092642000c0110300a168903804c40721002380089080044400e40d6040c0758003a2542075080010707000c060340701490021501802500da18542c2d855604466175075207080304c1c1501c82e500300040c1c901d0003c000b00040400f13080c02d200d81d1503d07210041c00d06034455454005440300c10007411003a00c2c1c0e064000510760720b442c100d80d038a04000c0b40103986d81d0482a00c0350f10450800c40c0106a0040c03d0103024100c0740e25031039800100040c0300408105660034031520040681c00d00c011048544035010340da004030701403244085d00980600704601528030040c060010b02149000410440c400c0024140c81d680e048904525010f000c46803c0340030782800000603260715224420301c0040c0302d0100042d40510245d100c0c150300e00071140a001d1101f801124080d600640031951030010074024002402c00c00c082c1a0103801c10717050038078030070304850564124500000d65413a0031070fa4242c04014001004104464490340e03858541e00054407034100c900380c03004001c20141c08000710b440c0c130 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 298842257 1250 298841007 298841009
    0xf05060304050c130b0406080106291318060905071413030b04060e390a0e0403120b040902030a06021e0d0902100305040201200f030d0506040501060e090a0f0204 71
    0x130310701003200d42d03944100406000b094080510686c40c0c1040041c0c40f0405104d02c50840720500865440540009400c9089031820b07a84242034400c01c000000c002d0095130703e000c010b484010a8040c0810020600c8022605075401a03407260741b0b4442808103898100c0702002e0401000400c00741c0e1802c07050014140a00c01b5800200148455818481001030f070307402c07a1f41c503880301d402210a1603442049141d10317448140160300001c0078111400529007440c20b6030100d110790140c2401d54881e41c511408400c0e0008980079000241c643e42039500b00001c80c014281c461004940c14060b12449400007521100c40b084010b1003a179000401d40c0f451698107011004812403030107041e441d40c080d1300d642009483e130302c0000ca1140c4800c00c80f1865990281c41450300031601a5140c50400c0c0485c80050805201006a40241d102d0651440610403040008109070f40000d0004181c5040c07071002c6c04103a81060b0850300030701c415800050000e40f0340c500c20550118503c0804600b06400d2000c1c00300078491 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 298843507 1250 298842257 298842259
    0x2060c070807140303030c072d030807030c02071401050c071214010506060a09030b04020a0509070e030c06030c07030f0909020d06080606010905100507080c030a0e1203040f05060304050c 82
    0x80d002000401400101c2c4440c21111031582440301214080c0805031a03110458011403903050601c040c3d80419400c9211a401d0313481d5607840d15180320001c452007040b0b10880004c80c0007c1c00c020400424542c0f60040514800c07942c001000b07001d08003101e01c803011240c22002c80c100728021902c285101e10421214000b0180c400c180c408964a9040000340c14010030252107843d0300300804a52207050110464424940c5a50b52500d52800c680d0354000c004000b510603644581d000001245036554840c843d030061900d078840c00c801c040c0080c10b060400c3d07041c0420b85e20613a4140100440244510704403003085a051030013400800340d4190a403407944a5402c41070300c0d584041250744a803c1154040c100391540b602c11640180d50706001101c105c221801841e820000c65511400c055000c0d034040e03d030091007115000d0501000c2030126146801c035085100005c0c108184580d81c0341408018003540d407025070b0107985402c1c20100000402c80f81c0c0c1c46001e004000000000f018081d042c05402c000c418 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 298844757 1250 298843507 298843513
    0x6060a02012903120406080a0e0a0501060b210f0402010c020118060503100512070b0a03020909090a02010e011404060c032f010c0306061d0604171b1c0f02060c 70
    0x2190300329010440003002c807080c06449102c9040105000050646040b100581e86a0b85a0350740c6c10354030386c05413200407508181c0340b1031030005e00700182081c06101c01620b444986192155500307140c070742e2802c003888080c550448080c410f10002070310301c6207030a5101e030702800d00038001030300e6200488104c0079200f0203131440040c0c88000b048807039200009501032031120a09241c0591604108860b5103d08440107482d544102c0c0301308416405c14002d441250714600f0010300b0140420b0224580d0f890855801a450300078951060466130004040700d8181020b00c1d000143c0034010001d01214400c1d0b0040000340702c02d40350300320100340c403692040c0f40a0040c854407919800c203070003103115081089100b040c60f075420a4284d5420300d12910880e0116542d0f076a5040d903406082c030751485c03903241004a0580102c810480441c2112004189614486031365006001c0d401d0000703030005050020301d42d041d11904142d0182040080305000c1c108449810251000c41044940b0005d81244940320785041640 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 298846007 1250 298844757 298844801
    0x5090c0f0315030606090603061b0c010207060e06100f0317091518060a0926070305030715140a020d270203060112030512070c05010f090318030b06060a0201 69
    0x9002c031800c03080e540c502502255403a84500e001c00c40f60f03040c1203c11079019403101d4001190454100d080034006003000460300d14041911443c242660310500e010f03134045403210340600c65480200203c036440b000b035605200e081410701641c020201000d21028000c0c4440c0201c031491160b20504a030407800380146900340c039894585006050b6081044d0364610100044e044034420704041c030480c0c80303141d183e0b0b80c0c55501509015444c006281803051500d11038522643c00799a14200f048400051030060009680f21511849d05042146030000d40d004d1813402c090b42420b110072300c0740d0740c40c3d000b01c100c510150300e0340b0034202d003400280750740103200c00701d0010b40340c440c180e40b6010450107001038001d5055400d00e80e02c60b8003008224a00c40c00090001e00d040000c020000d10000b580c54010446113000124820340b80c5a0500b50b030110040140310940e40c150315000c01d9084001d0b4100310a0300c1012102c0b03d499511444140c00f0700a0045019480c001140c4000318402e40c4034240d110308004280d4012 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 298847257 1250 298846007 298846021
    0x60507140c220b19031a0127110307031407020304030503040504050a02071502090a0e06031009020a0b070602040f05040b033313050c0d1106070204020c0d03200901020705090c0f03 79
    0x110085102c00d4851390007101c9460412070b100d00c0b01c3e0381a158074410074560904c441c84840d0707240e020523107221426550780c1481c0d0f105c424010019401960b1355a03001c21182420301c140b02e140c001c040c0440096620070401040003c0d004002e903002c962040742c000525555100d903000203440750038070007000500040091014102c00b0750140c00c503200c042e40c185038410303161001d0072900c01066821030b0b850303030103040890085000c9130013807805144083e103016212a6140000b24490300018411940d040d004a402c1c00000010201c0030000c00040b00d041c03007100a0b000200340c070707000040050003420311200c04101e0014110054480041d106000c440c4040c540079203207a40076080b80c0000c407a83c2c0100000d1400381d290203c1c01482e01904820780c4c5003003ca8070390401184c2c1d80000001c98000b50203002925040d082481001c035006425200401c10812005100c5520381c20b207858804001e109005d20061070345c1c0081c0c40d00c20b4400542c1c07070f102c4036101c080c502c20060280c0c10f441e4113544000403c005403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 298848507 1250 298847257 298847299
    0x90905010c020615010503040b06010c1202010204030204050609010303120507021606050d050106110319180e06030d0306180b041103010b0d11041d0a0902030106060507140c220b 78
    0x5401c801e0ba094034090340b01d4880b004560f58540d030545000a0b810b10100307010503140014070390401c0e81414010781e0310585a852900d07902034038070300e000943d501040800a5003030901405610110482c0c0005082d811684d0203071085448031a08000c143d07071800041d40703a82c02006001d45e20900b442c44015281c0c0d0310300c00104554040030300c6c04940ea0402c00005400e900610101941a1800024608040b8854400b032540090701448504020100310048103c50010b42140094841c42d400f0b080c0700e2404100781458400d1500c1d0070300406103010020032070a820151410b8102032030300004100ca940d0100040c0142003030b13801d50210340a0020000503015015001080600c03500401404058083d030b00701201c5004510520a48040c2c2821846004d503901c50400d13401104200001120400c580110f800c40304542c00040204600141c46414407591844c481d007d049124010046904c044012400c0050302c849130042d00d1208403040d180c194013a421020b95400054030341ca02080c40e00c1d1480399 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 298849757 1250 298848507 298848521
    0x3110307050711090115030e0f1c02100204090501080c090420061b0102130801020a0e0d06090c030b070e04020c1902010909050c030a14161101060504050a0b03070f2d09090501 77
    0x10900d00004040389403000303d02e800285150000ae40050380031200c0d1300035442c2c0c540b48002c0c214050802c0e80d400c1440782d0300c09440500b1030704c01e0024166040c07440040c900700703142d00b2052080c0301c00020400041c01d0007182d6442d01c9003900c114002c804211002c10000c2c01441903c0350104103413010982030010550161800a01e80354520008030341e5141640d00300c0c8907150604000800b440716400d9035042021101032468481c2c01700261500c00c0751600090003e0341c2d001115042415800d000805510991514079004129170852601c1c01d0f09900325514070749083d210410120b624808001c1da80540165001440500001d0041e072034103140140d600c0e4000c0b0f88140e0380314900341007034a0401302010003a1007061030900d41c441c0c45a0300d40c0107a0b47e01994006400d515900ca2001040036141c502501d4052400c440c1d001c0390681c150400c2500301241034209080d400c020710000c11008088007020550282000c4a1070f14980c40000400c10b08040c580000e0580c6017040780000801c003055000e49 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 298851007 1250 298849757 298849799
    0x20c07050301180506100b07060c0c0f0b0a060605160618051005011e03030503190f230c070b0c07020d0c0b0903060906101806050a030c090b01031103070507110901 72
    0xd02d159480c451b1003450083c050003186d00b400820311100c000194164880003005400c0d00b07154112880030780c0d40e0310003140354948c11074820608202f40034201400e8010743c405840036040c42030402c1c0590800da40324200b00c84001d0041611065201c00c0c3c410345607041c40459801400781d92034130795801100c0001c2e110a100d0003c0e41801e02d05200008900e4004003800e40b5803561340c040c69134817900c940302e0248c240c1c8030702110910b40d40d1540b0842d10030144958514100c41c4c2455890030b440d1113800e448041c3c002030002e402c00000300440e0000038a5101ca0325400000380c0c2d82c103500c903c002d0000c220448425580140459400e40d40801c040a2007405051120012030880c4c14544c3c41150305900c601041c1e5295102480d00ca02c1400414003e00c04000360001c00315000030030307030713526000903d84904580c0700360307007012841c0420b20500605009020300c0c04404c1c01e0074000130894400034411032100600310001c001c4042496401c005029116039481d103002130208540e075845401c812a4544540658 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 298852257 1250 298851007 298851013
    0x150f0f0e22110424092c010609050f030712020904030905190312030c020613020d15050106020d02030304110d050f010e2a06040302040c1715150913020c070503011805 73
    0x540444901d950300b2600c040619910481c4142c0b5202140024031015105007018952480b18141e41b0686010068020a06941d400369043c1c901024040311442c01e00d500c60207904180c905200322565103810061141d41910510541d07500c505044403040500d412090340140458492220091001c40000a407800b400880d043e0031003035501076084440021001c400350f00020b00107034000c11414a00100c082c0042c10080548195a58018541d402101c100c0b07500c0d65200010700a103070741040f06604400752400150310b1401c154440c841ca080d0010091803292285501d5841085414080180038900b9200244007090131000e84c07030340712142d48840545100e8582900a68030500010140424002030311451600d4110780a02c0043c00c0540010010301801580c0c0701f8640811591003031285000c100c15040c5031403520100300c00d41f82c01c5040070a07220070500400e00342c0d40d0340400d5080c0014084400694a43c0690f07034150610103903510141c0d040d4030b0b000c03c030400b104042a0001d100c1d440748040d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 298853507 1250 298852257 298852289
    0x905010318060c050702030a0b04030f0801060e1e030109051509030711060702011106040506040c0b030f070c0309080304090e06070302160605130c150f0f0e221104 72
    0x110210780041e60030000d149184000310000c1016540f002404043c1c0740340152900c20725402107807405030f0449040fa4244a40703400c0009241d406800f802801d907152609010315450414010006800e000d500c92199189800c0c1a5186207128241d1a0003040a0b000344040c0308603081071519a60741d0401c00c462452030200140c0c4c1402c02100712001036500600800d01520000c02703004080d08580000ca045c8640300183c91040182040150b00c52481000206014601485c2c4180d80ca000ca40c080e00000310300b4814019400d10072090541d00948030f01d4540702406060404030742c103040c1540490b01c10700001802080400b1950003143d4030800801c202c034181d031500707a8110b00b2846003000081e40b40c00c400400c00e0008146401040d0020f038003030b10580c82c2034003588842041030510390120740943e40c1050b480d0001ca81003107200012400c0d5041880c035000f543c95000e0800394100d001c80d0b10604e80149001c518624201c1da801140c83e564204010b407141d070201a4005501900803a400b407032140b00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 298854757 1250 298853507 298853509
    0xb10150f020d0e010207061206030203030f0c0111070b040201050c07230a0e01030506010b16060c080a0b01020c091603062402120f070b0411040504060209010e060f040312111009030905 81
    0xf0382c44018074410b0340208019071620100700e480007080300c100030031b0a46820b0004003685c0c0030004bc014070350328000851342c0d0340c0300301500340e00b19020200c192601d41c0d030510038075020841c0200896070054081c24415601c8920000c05403c1c11802d402400040c2a90602504800100118131708000400c2c3c1e9074084484d1908609000c0c4902444001e20540c01400144040c01410001e0522184200fa412074150400e0359046e003136411229102c0005102c52007000440503030750150214100702800036190f001c0c240404038601140007440c0c0e4000e98400007000a0350f5100e6440300c802030555141c1c070501e04020b080c0170465020280e032003200502c502001c00d907140044800310703a40c07260a1540c2a240001580d43c2c02000e0100070400e827050403180940e110b0b40c1c0ca41d406406d1040303100b410016500c0c050f00f00054205c0c08489022030085205014001e028000102103030141c0c0e4000321280810f0800d01000c68400e8070207455a01e25020301f05000c41d4410f10341e0041094284240c0310001610703101c0e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 298856007 1250 298854757 298854767
    0x50102100204151b061802130b0315060d140d080907080601150c051501180e0c09150612011d04050a02010c020a050a1e050d02030303040b10150f020d 66
    0x3019030203032101e0540b03d8a030164010000d44400ba481401c1c25500058143c0781c1400b150080e5025100c5003c000100504510b0043d5000705c01d90031180c3d0800034501a00d000c25a14005500007030580b0401074040703111030361402902151994000b0081000303003503c07140d980e16510500074034008282118041a29040c0214101303041c1d4811070018812a03107041c00c034450644412641e80b0030b03c000c131050b000210340309128090040e038029600b49402d5150608000c04024034808000d0a1840d0031a69502440b0201e40c0c80d0592034211029849602c5441c81c155440400300301003544000300066242c00b03401803821050483c1c41040103450315403445008150800b0084500401c560000440b03c0700641c0544041c0414a0024100c950650349600c00316642080a8004400d6030710080310220144120030312510150030184c45200080b000c80d80829a01d000c0a4001400b40d0190000140c4640ca1540154014400003881c051021141d54010380b8003501002c8240c014051080301c02c15081c090 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 298857257 1250 298856007 298856009
    0x203190e030d080a090c080109031d03100b0f04050103150c08010530030301092a080103020603090307060f0c02010e070332030a02030405010f030e0d03051302090a06050102100204 79
    0x350241c003a5070303441c100440312244001c06034144c8580c1d17841802e0200d070703c44805201420402e4000a0060001d082c0030381550714036107d98001c0207104092003179a0310045550200207040000103d21102c00c0000582040c1c1b03a142c1f101d80003440d1500000c144244421481790140301d40e41c023004600000074086a50602c24094140c000042c11203400498001c81a41c20040b4008110304c58621058980035045520aa100b10300355030b1a00710301601c2c0c900c40e80550303609100440d00f000c002c0107021005024a401444082d114410202c0010750820f0b09100f21b840d01a8060400c000403040260700c0e40003021050b01400041d803801042012401c07002a03e282541c4d001042a0003445618130b404801707002c0101c0c00200038602401c0d10a101c0300402c041c001c8070030303213401840d1103500300710004115030385081422003098240030192030780c84404180305032030000d14a00401e060f95000050071032480d444100035005051a0304118942e12140d010301f00b0b640090b0300741c9485582e201000c109900607 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 298858507 1250 298857257 298857259
    0x309150c03040c03150212010b04060212090f100203040306020427090b0c1e0f030106170c1801090302060d050103030e100504050d050c0d060e010f140a0902060c07060203190e 77
    0x3d0114240003082084c002c1c02110481a40d001d0702d00500c402280c402c246080e400042d82040104050058a80520402a2014080e28074605104c0a02d000075203542e020484e060042c2c1d420107080e14442d200f40111000b45403c01f109640d523907640c91441d07440c0007500501086801300480b00c000710440b9401007000264105043c1c8042e40c4512600208a6200781d000c00c25041004c3c68000310030711454003610b01c4001a4411548a602d0140d02410b002680b00c0c03000c00140d02401080b079501204420360304040304004030340c0007000700130005070b81c0f0030056000698051404102ca062007400c94101c14182c1e8031a0b82c070502805191014880000d0000420030042803003404144982c1c1046656000414041d404907001400c0c11400b07e500c041566600343c0e070f07541c1c8440c203080781301d03009000355007071402905020007503800842c1d4071210002c80540f456550079210031251065503511401d4072032800c441c42c242d13040d04d40d40c0c20001e5502d030700800071281079a401280d000c3c03425004803001064024 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 298859757 1250 298858507 298858523
    0x121c02150106021e0c13020306041b0801030f0602092206060f0c0803090a140703050f0d0504090b1212040801110705060412140301031119060e0d060b060309150c0304 73
    0x681c4449400c41c0320380e4407001d40021700c581c10080d619070b643c2440c004044811240f00595a04100c0280025a02c0440110030b038050b045051401042c0d10178203044c11a0781040201c1ba8006041c54550041d03c1140706c4a680b203c0d4015989407908807200b503485103000c180f4001c004403aa150400ea4a44901c00600b00c00318251088482c0800c1104000b150b000c241c0f40103072410701b00399940b400040a510703204030700683c0c0103080038404c029042250390540000c140040c064884030010003840c1d44900d00401c503049481740214a02c0341c4560089014050403401038603681c612060808903190082e1040409641c01e118500c40c03517000b080e003150ba0050b040b0340a014965a0764075402c8159450f5103a150400400901520358800d11074081c501075440340754500c036a01060410002d004000c114005034031410751b4420000181c100e40c21001c0b0080c140e90340004403085c0e042c490020001e4102c1d8541000001080280b00c7c0c001241c0d04540100c441500340150b110581144420700003160003c00c0c481c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 298861007 1250 298859757 298859773
    0x160f140901030216060606230f1b01150905240a1e0b03130614090d0e010e090a0f0507090617040f05030c0601060201051f0e06121c0215010602 63
    0x1500c60f400070319180b4000240f80143c0d00450355007800f1104282d00210018071661120316020410305a21811041841001418003907006580c0582e441070103901031f1250010070300288243d01c290054022401e680100c03c6d1166980e109103400b8000032140c080c9a800012034014010302c0c404e49008500501400401580741411102e42d51806101c84100302c3c24104040018030440d2400203520800000340082c4030542a0328008081e101030115000c80400c407002088085c8600141c448000266850003a214641400045c0c580401109040713800070085001c12024015540054840745454001042039685000044030500e003240151030000d9811074421554544002c1c0c22908140107008105203110965207441c0346500c03c05000403141c120500400c6080c1d02840303000d9010122075600400c1400c03440303101e00c055045004003600d41483d000440e00c2e50310340c00c0710591841045c8085a6000d482c840a408404461400c4400184100014590320600f1134600c2030490b2800d40041c42c60b5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 298862257 1250 298861007 298861009
    0x1404031116030b04140118051c0813120e030a0c051507050d030213050a060e0f060c0c0111010212040b01150c0803010b21010f0e01080105090309010c0614160f1409 72
    0x3c0740c01c0311175000281d03481c2c2102007406222a186128110311680051500c02d0715000100014254084501d060100380401c001040000340641486141d10094210442c4241c02046d2051846485420340501c1900300e400104403250803400187d4a00721545400c081004040c03486610561070020f220341c2010568000031030107a0003405415041c030100448640e160004260184011340c8200d00003141020950b4440c240001c50080e1000140c840301d04d01901e000d9066a40c034822010581080201c24160f00d040c907080d8150713598001009140081410309052880d8000000c1c020800180701c2c450500c00d2060003500701c20a030a40c04030840e801c40e8600404a101e0b03811503541440c00e20301090480e100f420191140a01801030aa10065407600b880b075035201990381600310f500c440e850401880181c00d000015102c6484e02441c2c0021206400d02e802e80103031050450301da410110351414485074410411160100340d04a981d8030820045070501202c0380c544469003030300580c0b0100b003075401c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 298863507 1250 298862257 298862273
    0x1090603081b1f020304060f050106050a0e03100f090201021b010f03180b0f22020d0b1e0c1b0d0804020105090a0b160c05060307020607030504061404031116030b04 72
    0x8003003998010f5902c01041a00356642c41d842c4841d03100c0805a0000800041028500c00c00c0f1141402d12800c0002d503041240c05009840366a07140410b0014030101f4001d299010410304200c000d50b0041800855100f548120140103070207400c90150041031440c041d001c60301c0514001c070100594a0020418100c0415001132602d05802c1e00b41d05980400900424440340c40c69014162841d0401058545030000541600210047d00102c4101d0340c0c440d40540e0310101c00240140e0040103413011030310341d0f41d0102d40700c486e03010100015103190300400c490f01c44880702a0000704030503224808022403200030152140d03060450349007c651410f000c00c025501c140c0140104640c05022103507802c1d140c0c81c200a0076042506020345205070f9451000400c5404d00b8500000c01d825076405042d8144000041e40b500801050801015a64000074042c0166a080403010000700c00f09040300f410a420005c0401d0041c0302c80540c644683d19403099403901c16894001106d0300985039021035100c40d920560 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 298864757 1250 298863507 298863547
    0xd080f040f0506090c10050f030c09030c030706020a050d050309060403080601020c03070f031103060708160c020d031d060309031b1507080f220204020705250801050109060308 77
    0x2061109201d2540008004102d264050070b1420010900c19500d0405c1001000100b859071040040034400c6081e44021402503e801501c480d2003503840f80e8900c0c0100f450042d2041c480307545849034000025001d900403c0011245000e081a620b450500361002d5550344400d81d50012180d114000040111b84282200343d0031020520540c0c908038402d00000e4900152904100c194807540f08040082101d441d1540541400031707805440c491030540f40151595800800100c00c4044601030a15001e220320980300909600415100c26440303107050080103140b00c82c14506041a40400b26045071900743d05a0744100c07403890080d45442c45200b0207407060300721041a5001e41c818001d85040781d484400000303101d4009a51001d5030b628064034075a0801d40301809c6000ca0317180504516004231100040c1c25800d5406450150b50f0324418500b080c0b030403108244c0c100d00311014004041e20364035a51405c07011245064004e10059032244040c00c111807103444002e003003520801c1110007400504000c04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 298866007 1250 298864757 298864763
    0x30b030705091005040e0f07060c030c060903030203060112060b0906070201051207020c1503090c060318150105010914181012080a030501150906031e0618050105030d080f04 76
    0xd030056541c0000c500112400c0d90209201030f0a50000e1045061a108845110110300c1c0182900b00442804680f1102c15006040070030401d50454030505015120720003c20303920141c2042901e171141001402504295600c60004e0040041800c0d8064140a0b8000381c0d82c0d016031191402d4900350800003583e001040c22810700009225007615101c11114040c4101c0740340c1c001d007042c015110208100005264900b0040c1c98007882480007a2600103045003c0030402c3d6550355894032803040d851074403200400403d0f0340d4410030100a1150442c0382c4504d040304c0d002c1c2c80b0280380546030500b0007802e501c0d0a003030540003242942c94180c2c900714000229001000000b0241c00c2c2a1183d0342030040a1445400b03444501c40010401c510603450b03c00c0d140141101140a66500300540c40141040c410703200b42e400300b503101d590f1201010100b03140d82d0850207200200b003003a95030381c58504107070360301405900b0143e610304000003620341004035003100a100543d40700c4e0b0856031040c0c94242c405c0d00140c015 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 298867257 1250 298866007 298866013
    0x60806011404121e0807120e06070c081e03090409080405090406021c0605031e19050a150204060801031b1a09120f030f030912131401030b0a030201030b03 68
    0x1014009224900800251105045a4034032900505040f07501500301300c00b04c03c0f003d03019440030b004103a5105c10382c0c3c0f0b8103910082407100c19400c602c084481045650a0603402030000404904004254181d1011a5071850580380041c8005020340340810074000e503503006400401c004101c6103000c0e0301c01201941304020a41c02c3c203460f42d0204a0a072000c4408403503a5500050305203400112001c6e80c0c81039030b0040004c0c000c0f43d0420340400d845800c90b046008090803021341c0105019400e00282c038000d41204d0b658130104203c0e0914554071140d10a044d141001c030f42c0480100c0c2031060007114255032040e00c84000a91031650341d50041c4c01c4000c51560362200701d401c046110300f500307990214040b0b0300407841c43d2203403604010455032140e0b11311000160750108510309400407010040d511078002d50344005441e030386c44e000d150307041944242082c1031f410800100740c581e185200c0b5610090b20388865a408481c080d5400650854100c6140103174030800030581000158440e0f0030000030081c018040d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 298868507 1250 298867257 298867277
    0x313050f0d060c09080c060a09050d03170a02040501030522020607060e07060302090310060f210203030c0607120903020309060a02190606151b321c050307020706080601 74
    0x190790100e030320044904000a1103d00c003040017903c00c0100c076030041001c551703040c50600c9045000e0101803091003010700070103000724048107150003101c0640602d03c004220716810f140c408002c9001394402c0c05014003207881c080100b101c0744944615000c6084488c0b07402e6030302202c11340804c1051f811074802115070648030a551407040c4818030020000380159140582c40325007140c00c1504007021680f009130a945032050070801203002d0034518080b54100b101d0300b40d45070a041814459280e64810181d0507103c00501c0c0d00d03c0f140001115803003880300c0d554203031207070491140800c156115420060010b901c28030040b1001d160007002800d00d03c0d1540112079940d200400101c0d804205814203491450b0344842c10030110011050181c001371452070000030001c5141860920341304030354005400301440344072202001c2c0318040c20f038400028114010160941305c3c1a0780d651007065040346400e04e005642079441c160301407000e403809113a03590050301145080c65012507400000811640c1000300b5011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 298869757 1250 298868507 298868513
    0xa03030302220905060901240f050d0207050d1407050a02190302041e05011d0408090a0803310e0a1517150f2715010801020712020313050f0d 62
    0xd000c0b0002c0000c41d1010405103090401c110a0b680305078850b482c020821048884004000748040a21446070700b40000419011201250240604041d040032203100052000c18080d00056039039404c02c4613030302d21400c808074a000c04007501031880001c00941c000d41c01d00c0c0052038050000c0c403030080800212004190740340c00060696103101d0044020304c0100f0350011581000f801050301610319904d2004001c5c94842003a080080000c201410703211012884100c19a00c0c03805000c000c007043d0049070345071203840210300e2030000551500b1641c3c549440d030321252080c680230000e04841000f01e504003140e481110b10400b0b0072916031845403c03121544041241e5800c03210a141989102c0c0080454050401c0b110490550150050740e139540c0030780412444040342c07010300010a040c904140e20501074090800d1400a101008001701101e07500041145001503020f41340e410f009507030050005c0303915241640c9900c6110001c4040d81c074011400d01850611841e072060904000c0d25500380e100b100e407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 298871007 1250 298869757 298869817
    0x90d0303050702010507020304050d35220e010302041a040e160f03080307051309062c0c18060d0c03021207020f0d030c020118210305060a03030302 65
    0x5001280030941d01c006022240b5424424641c0c0301c00c0d00d000030741c609828074000a08106030b4040041c00c5241c8581a00c10443e1031a1f46900e0420001e0400000c1a100324140401074002e00b01e10400c6c1c140e65030028000506500c07400c000c42d0494500440300342d086030203000140c095039201060698882d080c00d442511284200f0a01a04201c0600010145d02d00094200a190b072700209001000a07401d0010403c8841165085660343c24a9940c1d80d100244002c4001000e610000095140c000c00061498400800100f01ea58030000c5500ca0320a100d482d00701444162095501c020381070100303a190b04c0c0300c006003003000c0000410a03410510383c44e00c000c0c1901d66090f00078001940214554101c4101c3c0580d10350400103078000781c00002a0610144c0e035592039800f000f4205a1901c00c2a6031450003980688803014541c80c1100c80b00602d401c0c00d03200c000e450340101d00b6a501881000000911070b1056a02034407004003076070910313031a43c1c400720080d400180b41152484800448403c11030032403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 298872257 1250 298871007 298871029
    0x60405090118120315050907111c020616033b10150e011206022104050703030f05041d060427120e060d0510050a06030501211709040209 60
    0xd8410b0050030005443e00a0a0715104074210071084c10144040c006075940386a0940e1040b1240340400d03a0400003c00c0c146040f40703003101446102034181a03800c400d41d02140c0144610501c000c4072840280e00c5008500312111114150039140d542c80e28601c140d0003d220380c021603c1100402e40c01403640c20160750501d440745e200300758156550b806031500c400f20040d5010080c540c482046900750b150048410104541c03003001029594002691885004040b41808408c03500824100203032030145401e96484a1502040d00860381411a54251350b1081c0b0442d8191116007040c8500c40c0802509841400d101401c5142d0064880801d070700604500076050528004c8020482d41291550501034030300402600104104003880f1544600c2d0748800301100c0080d0049013002429548403005446540000e0b0003486d4015a50800011b40720b500d40c00050595a06039511900100d031840c6c0394640c00003900f0b0042101b480b100156840c0d06000c00507100203200600054035105803400010115881 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 298873507 1250 298872257 298872263
    0x110703020a11040f020c06060a050f01080708190216021926030f0327030a17090703050d031d03070c031e051903170f0c07050a020a03030f17040b060405090118 70
    0x1f01c003044014a41807242100410003550004054581c0e080003e00c45580205000140000e01002c0358102c010070702c1c030111b04036403400300f151a6100110311021000015205910811400f400e044038400d003480000b007143c580304020050000b8207104081c0d000c0550502c2072641c0401d010040c2003944000041d4460580944c0d1406814580826000380c40010342508000b94424042a42a180c00c0003058540e64240c10710024203507180c0325820301e80f0440740c2005109004d81c0c091022200c3d00764000d2010400c08504c65440300845940ca82d07030328041d64001906a8050410802c049280e0003286d6044007e8440400d40b0211561911850011180b0310305502c01c0f0701143c004140751340160350b4941c4d4142520580e52a0030001c01e0318290740006400a102c04c14000340c2e0200f0400e080041606041e4050f000e5100381e43c3e41c0c10b024040005030001d140100e0760101c0180303087d000c900f6011b4480d0b584411159000c1e11004140700c003d1a0092100e41c1c1590b8480b8000740103c2c4441a2007401c40c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 298874757 1250 298873507 298873513
    0x815060a090c0507031d0301470603130c0b0301060801051c060519060914010e04030f210f0b030c0103020705070b07080f0307050904110703020a11040f020c 69
    0x1810014000c4001840c1d101422a0b0310305109980c040341e101c4201e650454261070510300b0346500303494904a95410008465140d8686098608804904c00b60304003141c2c0c800040e882c400f0400010209410303500910301d02e109104a552402c2481d104000e1138105001440d200069005651141c0c3c030015183c00003640004040300410100d81d0044480d2701600702078804101511003508000991812040000d00060300c850004000782020400b50310006444d52062000c55070759540f03800100260f0b5120111050081c002140c008032910f00140102d0f415526a00b24100c072080441c1c4000080c80c0702005414860341c009070311041ca008410048049140001d00c035079018041502d0304204404c2641418018400e46d0081040446c00398221840e84048a0b9100c007940b410601900c01ca06400c00010b42c0171041c03022590f0702c0f20290031a075a042c0c5080002d0500e0001281c0140503035030b07004006034008003420340011000c0f0307503581c102c5d0000340010804108802e8003034140d030042120401168 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 298876007 1250 298874757 298874761
    0x1512070e030d0e0d02120f070f050405070306060c080f0906030c0307030509061014131503050d03060f0b0a0e030303090d021203010605160c0e0a050103060e120405010c03090815 78
    0x1290600202c0eaa10089003488000c0e2051900820b11480c0b00000180c03050640b90361040842c0c0b420321580c0c12848840c001d6842164440e14911150b400b02d019a50007545010001448180240700c0d040c256030064840b9038080740a603075a40c44541c00702849052010040c41710000302e0b00ca4802450080051001d103585901c1d120800401300c81e00140994082c2d070182051000701101c0542000070b90b6074580348290049210408540034510741c02c00003580d5032504503580140500700c281c0b41c06aa1294040d10500c1c0c0814800318140d034180d000382d00c191140e0100410040e10000014021910303203080095043c40ba4500180c00c6400460340c1002d2a0000040d00843c542c0c1400b02041c05a450340000341994108203009101f4003440078849101c1c50120310140500c600e00c0000c40c01810300705d50080030340c0780c00c005013000303088284002c990450401c42c40038818a80414983c00081451240c1e5042c94904001101c0f0b6404111041c1c0600c4808030700800c1c079400c20300448120300f00b2600c0d44500c40c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 298877257 1250 298876007 298876009
    0x4050402130e15010509120f100203040c1e12030201090b01182301030f0203070b04060203040e090c090c180d060903020606060421080f1801030b040e07051512070e 72
    0x50b040c000c050864080c40b9001c0302c1420b0380c100d0300361141840c065a00b14181007001c00424a020340e41180202c00f44100b00ea0b41210103260340007144034902c1010303586072007036890300324080704000a01c1d00608002002000d022240b0f446000c0d04416001e40300108103c0c6440d215900424020381011a05450900f101d41c1c1030701403805031a0300c1d807000c0c0180018906580165420355881800010320b810802c00090056581c20803170f180141100c0350841d03030755540e582d4001c0c0d03031ba43c01803040c070003410340220004803030307450101d44031100c80720151206013190385d8103a0804203980301041d45004440c40c8000350040d91906150b01c0c211354414040001c00c0051820301030b1030030100801c100d102d0b020421060110707101c8014546404010348400401c1c4054500e00200603014980081c0030951000c1510300214080700c8413055201c0d003e803010030200151701c00303200c160f848006100100c0d6100f0007040003141440c20004401c1c44441403624242260480380ca0414034050359484000340700a0318103100b0b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 298878507 1250 298877257 298877279
    0xd0813170a090510050702090402060705010905060f0103051507021f181a0c0403050a080913020a0309110a0f06050306060c0d0203040914040b060d021206010f0812030c04050607080405040213 84
    0x203004c1c0541085428082c07a503000a0450000400082c047d0001003200d00030440250803034509603070310034184e500c1407800d01d0b07021400e08024802038505104d881907003220009c05880701e9008074141e5010340410200b4108001070180f9540b234191007569251980c8000c110240000042d1a00c2030001230074088960840040720500502003207480c4004000400c006030300020880070682c0d000000769110b5001c00c000984039140708107001d030240d000280d500c100f10f903d5031000068910803420b00041c40a600c003440359406590243ea005000c072100c081c8a0580100013640e48240010305151070b00c00e042031b49a040a1525901f400580d201181c14412210b007409500304031224840d404c20641f0341078458050200000c0c0010340141d641c803192806545070182500c064118450444202c0d507034503142e0f900401601d20400700d07140035416078104080d445400300d034055850101c442d420207080c1020040c1c07950050204990742a010080001c50781c841d40040c0101d40c0c00700c15456074261608990581c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 298879757 1250 298878507 298878529
    0x30c03070c080105090c15070209010e010305190b15030a0c031a130c231206011509080d0e01021516350c070501020d090210020d0813170a0905 63
    0x1403a41418100103c1100001b01040c5a0408880c114800f2202c0600c60f0000e03c564400079402480030170020070408030b81403020341200c1c803480407281c0540302090746019050702c07504010803016104011490020804180c40788100c03008041d250f52410a58501c807a0340d01a500031507000c40c20320680900c00b070419000545c4031400a608000700c400c66501d4030146041da01902c0c842c4170104040031106881c05100400c00d080c0907000189005040030740c1641c903402480346002d01c4901d6040b03021407500c41d0007810104c0d00450000c2040e03080d11030040c1c03001c0305140c41540c114410855999025403600076118007802959500c5820000441e00c01042d66441040307241c0014081040104120443d080401d06406410551000741d2200d030514091391042c0d034805007445d030020503c00404440c5501011415208a411000c000d2042c00140e84601044020f01c01003070b513000002e00b4114011828030401c40c131460349940040055031785002d244e0002074108000a00801080c00b182c140400350203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 298881007 1250 298879757 298879769
    0x905060105040f0b0d0b180f061e041d0709090201090509090606041a0409080d0b0a030201050a030f021306081e2806030b0403080a1802090a150503030c03070c 70
    0x50710302424591403c080350143e01c40c0b00520400010b007808045003d500a850f5104002d0841050b1803802e0940a54102e09907225015025030001081c020319040c010341300500c407010340d4500584044d104010051040e444007110018001400044500c402c1c001007001d02424140000c04500c20700005042010030740210703005601c498180401920300013002c41d0f0160040310003044a00016805101d04415510800c1d00700c2d00f0030000300f0030003201501501e2152000c06040040b202c40404025100307500b0311020340030a4041040e0800c00d442a00100b2900800c040098900b6154204040e0803941c1e0b503109100044901083c0300d5100400003400e500c001d080e0046044905040c2c441d0902461503180d0107140100d00c07580008a0344642d0080401907810603100741e61440c0a00f00500042401c81b001e02c656454080340301d68080c4012040c01007607801610440c4a969081c100c50000c0000e000b60040085460b540002c0c55a402c00041c150003012002543d05d0b48a10300c1c0003034042e041074001d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 298882257 1250 298881007 298881017
    0x90c06080708250e032a03030a09030209040c0b0f22030309060c05070801050903071a040309090902210f01140f07051c0c090f120b04240e010609050601 67
    0x88445004001d03a02c200201088960000c036240700f11054840d03501080009425008013210208002e005118882113902801410454040444205601da210f030b0b00340d035008205201d00510160620001fa1a80280304541c0440c05548454000b8900d0700400c03420030780880e0010725100c08402d088044030390400b05c05071804107a400c6a801030400b80e414021781041107181d00200b4140b050800c020001082c90707270003c01c1107003000100d00e03840740e0003140180e0300100e00001c00002d01d0051559a0710841d0181d80f104886030810031104050018910140e0f0303c894812600b41015041282c1c40d140703224060024000a22542142403d41d5000d201e000b9a820f05a020800810407001441e0740c051054580b0b5a603582d1049802c0203240180900ea000980c41e048401c090950408441800e8640d0440c10300c0005665180c140c0c20707442141d2009146082c46800f040005980d800e100e0150b02c260754021301030246100e02c0104890398180300b40156034694208000d03451075449101e800003001c0c80e013 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 298883507 1250 298882257 298882261
    0xa030e01110601180b0d05011b0c03090b0d0f050f0a05090c010c0b0903300f07051801090812071505060117060301060b0a1d120d03020d0f090c06080708 67
    0x105458000512680d50286101e800d407568929035607100c16050a0000d0810321400c440f1b00300f07a8002c00ca0104654120b02d00f50740c070403200d18080e40079561032b950315540720140f072403c0040f4807840b43c205541d050762407038a51440100c05241800780744e00c10301d0000d44c030903084e20348008035002391000600306120300d0b0000200325500e030340c1c041c902100943e00b001c100b50f200c0e01c030464a41d1445c4a020380724541e1200012a0202c80c0345100703803118800c0c04045d4030381c0a80e145c581040c081004191001400316108000c001200c00d4641c50050040c481410b140030302c203a41c0c4d9601802c04421140c0384000d13400008048040081c0e041903016071034443c3c0400c1200780b03007170b00c00030300081a81d41e0703103c00e240c0d00310f00010108c4c4d6003500803001400f0300c8005503448845032230000e01042040903d4003541f08000b0581d1103d0300f0110a00c0108802010081981e1098203200390002e500480303c0207805611969402c03038204c2d00b40107070341340c8511034040c0a103058a000700c000c0520300e01034202400c0000c1481 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 298884757 1250 298883507 298883537
    0x10b040c0e04020f0705071d0603010b0901120521040810020406020304181e05060f0102060c0a0c03030204050303030c070b13020d02090a0e12040920070825050a030e01 74
    0x110702840c0c0c0c04181e800590701d129020300101a400780f4000149140328440c00818042009a544030b004502106102d05580300c2078201400d0f01c6000a600f500015001d0041001d8611044007118040c040c00a0302c05840f0610341200900d031854001c06000c003c00501005400d03020003244140c031121480860400d400c000c0029101c1c4114440c508007412258982c56001100b40c7c81091503400064428186204040200300034020403200d880c4600d40800c1d0f40300b001e50021844600c50107400c0e6403145054a10581a900302000103c16020142d0070302c0040f03040c2d10b04000550050105000d0701d41c650407545005440f98800900d64280684020104c0c40162550544103584d02e50407540c0d880250f40b1039440c840102100010f07000603200349100c1e43d40c80001c0000920940d0321000060040007840a06455000400012003000c45020000200803910110144c802003058110303030b05600182000100301d25810050594003a004112058100350300f00c2d07618441e0481c282082100040801c1e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 298886007 1250 298884757 298884767
    0xc030106030c05010503060a08190201140c0a06050702150415050108030a050301060f03140f2205150403091805010e1008100e031b011508150a0e0304090908030603010b040c 76
    0xf220301e074180074010002c16116620180410042c0c402e5504503a40010860600626a140028140d01041089081010b118100c0c2c08841c00309201d00e0003000c5000b082d1b0340d40b0008010082c250021405003807041e28180e075100781c4150180b405104e045450713181d480a034100b12078069103c074801e1b6004102c01d414803a0440281d03030440701b0301d00784207041c461700c540142c0181c1545e0b20000305050103201001000c20f10300300458090000711007084a4024294081c0300d10510743d8001030016827004c040b000010b00e10704c143c10703401807003803600ca55250fa6843c80e4218000604400303586a075116801400801440d021a9902480c1c1c800c1081c840d40c42c1c81102a12400722111107030300d15071504608034041304208201c46400b07288846640c0c8400c4003074a854020480204000c0c0720700140034001400031030001d6682442e40e806110450580c540700802c8000b07181721550f0308102c0c001400006101001c91082d500c03081d0040301c5841d600d18003541050308541071498400d101e64a8002040f51040e0300c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 298887257 1250 298886007 298886009
    0xb040e0303040c030816060e010e0f0105071d0d0b0106020d1701030201050a050304060e03131d0c220801090b0604051305030d200408030c060c030c070f080d1d0c030106030c 76
    0x800d42d101d030b840b001152006c03400b442400380504185d09000801e0800d00055014402e0146064141d94178081d00080c25802c0e101c0540c0c1d03050010b450004444d1500d000036200c10301c03281c0700131f05030404030200c1d55071817141c140260711480140c0c00071100c10300031a8100030006e0000e0382c40b5142213159810355002900c54056a2004410031801000180401c03100e68040d007607001d44041125151030b00011004000700c1d41e80515950345103c06121810000030b100700b280980303845407400703060000507041c50103440079140465440c2c0c0c1020200195031300c0300780b1420504031f0142d80410010300c3d15400344010b44502403d4020015110f1066801040000c42a111066111140442c0001151480407042d100980c20240c02407400103000420a20020007090504000c0042c1c8480b80d46070541e17205140411159510b2000b4104100400210380c015541d41d140e115502c0c80342844240180b0404450b0001d062003039803000401e01d095444030401060980c0c8408500a001c45415980c400ca148006 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 298888507 1250 298887257 298887263
    0xf0b07031422060f03020f0d091523090d08071b080d020426030d110d021303051c05070204050606270405060d030807120609020703030b040e0303040c03 67
    0x1c9042070400d05541d070440703005000740c09001044018a40302c0705000d944510034100890a00030000026900034000c0d1b4400c00006003035941481c004a1030417020340398a02c01207078035100c095000c8c42856028800c801003803003000a4034062001c0307007540500c4280050451207240d072050800720444c40e8441241940b2078854513005114a210004066582c001220002c250342c402040d540a0591a035014004403601d001105036441d00f00d200c0208213807402840008103800030402d8000c0920150407500001d8200c00003a485c0600c1c00069208a0b000340103003510001f120001041800000c1203030100c1189003005640080003e114040c1c158030406a000340225228000982c06907210000d031141c0352005204520040700c444000c00a500c014039a03184280d151a01040303060030102c04040c086607040d00e400c00c007901c4591040c0d402d000002c001441c6c1c25142c400101e100c66060001d025204c4c4a6100841c0c01c401380000c00007034404c11058000300b940107000b000045074912034145d0407290 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 298889757 1250 298888507 298888517
    0x30703031a04020a080604050609010b0301060c0c050a0303031e0b010504030f1707050d020118030f0302030604060f0b09031b060912010b0904030c0b07210e0a020a03050a020108010f0b0703 83
    0x20010200c51614140d60100b0340c0144041240740c100c40d08038400030310840c800c44041065554000400c0041c800c05c0c0522101c9400600041c0aa14091243d4403541030081340311014065850002940041146d0000c50020f9101d0240c150803542031100d140074000c0303a42042c0010340b030703e10008010b03015a102c00303000310009240420510441d40c04031702000840e49000d950b11401f80c21b01d10340c1c1e681507074208001903191204615148d01c0300e81c00e81c0d0320303d94140e40d444074100720000c04901a400103003140d03070300680d80c40000414080c0c070314a0380000e00110307400b2a1034285100400d42414461041200180100140032400d036840d6001c50f22034200450b006100d070041c4101507030040106100e030342c0d0443d40c285c0c00d20003859007100003022002e104400301c42060303a03880b00c12107020004000440508505600ba2466806ca075000386910710084012507000c04880c3d0001071907210a5401941d494000b01100c20540d40e0140815000d80034107080d440c2044d00e00421071156110744540034003001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 298891007 1250 298889757 298889771
    0x6040f21021002070f05030a03022203030c0209092b030c0305060a0504020307170f04060b01110c01140d0218040e0a030c021e030f060105120d02060612010608062a030903070303 78
    0x400010740421320706030070100302ea480743c0c2600c60250080d800041c03451011b15080f41045541c00c40d944cbd8100035640c2c9aa2042505005a4244054000c2c09010382c40d250080102d00c0703215071000c480380c086401392045040d902a41480c8068101da00703000c0031500b05410402000349680340c01004070100c40c01901d0040c0e60741e503a1503007240c2d2404100004581c029001082c4400403210301303552070046005071020031150708614010365070021080000d003101d800c06444800c1943c000c8a42076044441094250703c2c1640225440e000c03603221400e5405211043c1d1703c40c04140c10207101d1040c0c0400102c00404101c01544c81c0a03241242c4840003c0c42050301004501c2c10035141c60000c541e004014045581a88505012580f100024040c0c1c5001e4444400c0c5400303510000a02250b5518054001d481140c82c3e0390b0600040c2113400c58030394810764039881d00281d00030082008521070b0203503086040e55000a0140301e2200106204048000b010900503c1841c050103c01c07102c1c0f6641c58100003a00f4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 298892257 1250 298891007 298891013
    0x100305071a0903030a09061b0b04060518100603060b0a081005060a050a06170604060b18040912090602100615051e030c04030b06191e0806040f2102100207 68
    0x203100b0740c1e4905800d8000460b0b06140c880e040000c0a0075610310b0b440e40d400d41c907080080a0400c100782480a000d8100304030216002c9411a1721007604400800b604000e03a0a13545038642c83c0c80c6000618029450340c501c82001805034910400b945d40701d003250541c000528221210781d0703484d0210380c124100f82ea13440c0407a02c2955115007a0700141005001300041950792000034120140000280400c00462400034080380741501c02c14042c0c403110f600c01c80c10201c100c2e20307604605104400040d00701d07070b450000b00c01048040c1311400184d1034654840c9209800d21030024240000c9001c03c4058a007801800d0007100054407400b01e00b002c0302c0c07030190b88480c50710307080148200480041c0d090080300081070100c80c0e003180c00200103481c0603210405254031344000340000d0f14213039801e0b822280c90449081c00f401e054040e0b000111511003000c0b80301c2030785071000981802d00507601110001c010759104030402160b1021803449403011489072201c4021a00041c1d101d40c060201c00850a0b0700051120030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 298893507 1250 298892257 298892309
    0x711010e060703060905070e03071e090509030c1213030b042f03070b0903071202210c010305090c0a05010509062503020f160e0c09030a050c0910030507 67
    0x1000ca0044200c4080307060028014006007150302401034001d04200008001501864014030680030150007022040e00d0000f05410790404030603054006004080d0000b03c0880c00d008881c045c8644101555a509040079a10715280e48041500f81c0c01509100808900305a0200d0301c0c1142c4e04980160740c990742e14131b00090302c040264049100400ca030300f07a40364191005500021040380a03011602c0c050703141c0440282134002d40c185190301d03a000310000c0c01200d0707c3c42d0203443c245201034101e0b981c3c60401c44402035170440050000340d0561084941c0b820b50742c0e040c040c66400ac91040c001c0c0c00400030b1040071851030380c01c5005607414001e0001d00ea0030b1540b5100d01f102c900040184072305001c08403404203190301c5003144400f607005110301160380c0c5141070b0200c1d40000b0030503004062041545041343c568145107008008617030310b1409000a2040707403414880740d0405442034001e0181c01007080200900e06030080d1480d003c40d03004600500024a0001d41c05003610100c889207041d8009003460024 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 298894757 1250 298893507 298893521
    0x40c030e01020307020105060f060913022503030507030c08010b070b060310091a09060c12040206041a0a03110a1407080c0d0903030206160503221707061103040b071101 74
    0x6010740c80001000200b59041d40594007508045401740c1076001207004101c114010401c00c650300000d070500b00380400034254024108102c4130400700100d0030080c40b00c68150368000c602074010980360701c20041c04540c981708101031110181000304895042c0b0840d2a410b02846c4001440300171000007040071a507041010401c410000130090003c0c117420314001e49400054140d0301400d1400f00085003405034080740d128480c01113070480e182801c0a0700401061400f025001303a80000007000042801715031108030070030000c00b0359201590360745031200003400c41d030b00a0207640d0404c10074021400381d15408203442030b941e048040c0e015250000c60408092500c24103041c594680f09452a07108041d0304240110112402034003a20183d50700c0305005012468810011800120f0820002e650f04201c030100104c2546001c5c800a00340c8040c1d941d1540c1200441e92855181d503011804608000041c01101414441e40b2041c5081d810241e40b0280f520402034000c0090045070703d28003124132401d501a02c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 298896007 1250 298894757 298894781
    0x30c290301090606030501080a020d020919020d0e0c0d1e02041503060b18070f05070f050f010e010b03010b030a0803090a0f030c020405180d0f1b14070f0b0405040c03 73
    0x180d0381e595030240000240101d1044102103410100005466040443d4040300302da0083d101080340741c0150b003041050a8007c203018850040341400304070840300da2001d4564a01d0250f0001452542140310354944004005401c0c894503820408800007801030300c40a0380c201d240d801d150382000803480010081c02407800b80c441420355104001003800029001f14410300300035200641d108511111543d020101200c0400c046201030f010440070901c54001000902e01a281d0515158540c3c1c2d01c0320308100350080714400b40e1f07445481c007440d103260038400c0c80c0258004078000c008111610001c60348550346004064107072070002c00042c014071414407c180c10b0300c1c1e206203004444d540500d0007070516809813a05074001ea181c0700004209407003040280440c0000100103181800b40744030304503074070700d00c84070208100130042e428846600034034802c0d00f8109105814100300e01e06400152490004103921242c0f000489820402c2811641c408903003e40c0c006482c08200820100e505a000d4401c9260301c0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 298897257 1250 298896007 298896089
    0x604060b0d05040201080c04081b0609120105010305060a09050c0d080705120304030e150304060c03020c0703051e011404260a0e030c010203030c0912010b1c0303060f030c 75
    0x403058950745500180c071807407007600ca80703050b40c6810000d440d290003140505c3c0e58590180d8032001089080300e0843c0f00041c40240030618001d44100801c1d00c031180d0030100311003607440b135006004110013031007869070107469400704100c84025178890641d50030909490074041d940451001040c411040211000c1c50b80203070032585406502008a00250300c201e4080e00000c602403003400241c58021810920034840c0e0314a1030070360f191521280b00404485220b0014151308014181d0401c10070720a101c006d40c010405403001060400c240051402100340c3c14015907d825140c0d10690300f80d4803901d40042d082505c8050b842e42c4640d821605400400c01e0f12a58800416110501395021360413a40314a01a41556544000200103983c2c0f400140c500e1403492300c0c144145016418610400701840440800200f0300428060110318480f0702c012505101c08028403051007855010300400008198040d82080c0702031a607103596849030014001d441e2140c0345801004550190091490100d001d031001e1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 298898507 1250 298897257 298897267
    0x12071e08010c0908070909030903060525050d1109010819060308280305061c0c09050103060b010906021203042a080106080f03040e06060c1e03040e16170604060b 71
    0x2c082c056078078503c00c13121248240103000c00c020f80c4a000e200301c3c407a4151502e54060741540e45680140c81c008080c0b2038441c103440c40c1034090800305400c0c0da40c02c080340d0f100c880d560030740141d0703a50030f40307050180c2000040b60070802c041090740e00c00b89190703100048003501e8801e80c40c56420900900f8a41d4405020300c0380208000c4910a0313090003070044030602c590040c0d43c042e0003010580a903941220a503500c400c00031240305426481d03480782885144915180d484494646408074202c40080c1c00c01da404036501d0140c0c102e556003007138601001e402d10f40010080341428071881e81180c40010401404e0301d041820f01c05c1040e1b0102500240c85084200b0480650744031070500d8000d000f135100d25036030341c45212003d4600140c0407045806441c058054038400f90307a013109002c5c007640143c05801003803040076015a14003501e41c141049001c10360006d180e8952500c001c003102000040d004113590b00070b0122400c0c9031500082e00c039001d030002c0044803502c0d585480000380207140651010709142e9001507 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 298899757 1250 298898507 298898531
    0x7020f040905120a1805100212180a1211120a030e040209040c0c151a04020a26160306060c030e1207030327080a080705070504091b0512071e0801 64
    0x2062081003031107085d80402c42c0e0311401c01c601d103090340d411040540c001c1050360315a80c541c000240094014003842c0100101c4880100e12948400c1d8070030310f82542313201a00020003400e05c0002e045200704a5440c0101815840d0680d01e52000391001000d1089940a07039506854a8054440480c0700400412020401c020040c040c001d03a840308807860300c40500d128800c03074094441d461078045c50f11601e541c0341d60b0090078440254441d610b02400c1c050210400c151020810341c956000840a440c80b40d030300d040c12940541c15507400020b09040c0741c285003040c81070721b600c8070144482640501d09140c0e0b0409042c0424070600d90001d00350254000c016010003419003020341809640048510b80010800e01ca0504021114030700821148c0d07040203c03800f0105507044094610140108240d40c9481d50b030740002000c40c0c280070380071101d24146d0242c8034000c1c3c01041d400001000d00342c17908105481c0c000d905945132885400391070141e652001d8a2840740e00b41c94141c1d80640100d9008200105002c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 298901007 1250 298899757 298899767
    0x7060603170c0607050a1709070f0b0a0e090c030406180b090f060f0c070f11090403030605010e090c190201020915091e0a1505161203060b07020f040905120a 69
    0x442c00180c511908010600307185c45a012161481c080d42d03906030007042c001040039080346000d41260010b104002c00415100e4614114030700401c1e80700c200d5a07484d0480c00e40600f2500c1ea44c5507a03032007a404001004001500f15049075485944007030001a1440c43c3c3d10320301203c0c50041da000c1c1c802c2c400b590401c2002100044c010703071488064800c4030010364800680070040c1104403080040500203011382c00014910303c48481c100d62007039680c240480740342008500c01e08030840c0c00b600065103c0c04d0400c01540c0000c1c0070f8040c208252006851890300c40c201e0780312445048008488003044200c100d0301c1c64800c0d4152099030304002c21107118900b850740162441e40050005e203101c0d0388940c2c000d0b03503142a444403c0b50754840c00303090b40341e85a1500ba210380c254100000d0b6007080c440c0c20080342d441240300c10b028004540c070581c503413450300b00b600c00000c0842d9174a401c01c10a00c0f41c10806040980d8907500c4400d87d1320402c035404500c294091404504101c10015000b012030000302c1e840410b0398001c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 298902257 1250 298901007 298901017
    0xd090506010f1403121b1501060f031b0e0301060305070909020f3c09040b1b07030c0807060b0d06020304030807050304021807091505040503100b0108010b0706060317 73
    0x2200e0391901d016150110b0b5048545034020207545540030702200610807008802401d09403188070007546c04e00500140c0c9031f007000e8505413002c20600c1c0100060003081e8010720080c0c0e59160500d004c001003628180300040140d4000d002c1c1d414800055901c1020307903001d40110018560040a4581040d910340424001d0248000704034451094054100002e041c151a0107008004840300d940700c0d030700d20540d081c0302d09964036003000000380300b0f480074841074a403100024080d07032084880410a14003000003c1c00140021180209000d04002035000300740e00c0307180d40c80c00e00c0c1c00201c130542d2800b8034a407030001817410044568112400071421400d000d802c0e402385200f02c1c069129084c1d00c1d61454401c41c1c4910080350020360140e040780c117120302c3c1842c856502d548131045040c8905d240b605c4150041555000c05a0040050b034001014000c0341801c0c04a0010902e0046050019120324030019060780c07414010943c0746280800c0f24014030565800c028000e41c3c211084622000101e00070f9046a881 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 298903507 1250 298902257 298902269
    0x7120e091321020a05100e0a0f0510090305070501051015030e010b121506030705090f150301110a0e030d050417120d0603020f0a0b18030f01050f0919030f030b060d09050601 76
    0x1404800d1b81c0183c81d540280c1c900220094080c00440310305654a0744400b00c903503025503840c89001c0850074440d495200c3d01c1c8503179000303854882d11242e061810300d0035100000c0c1070b065000e800140030440d01c4180c100080c0300720001d0a01040c4100d200c6c00d024014841c04012540c0f203009d1404081c0080d00120326880003e800c402d002d0702540c2c0c0c040034565160641d100f00e5030840801c000051841c0700c1c6d070740201d4001c944c03c49040540c40c02600028203546120340c0da46908280061303281111500100c0a6190000a6003e802083e50030f00016080f03006503c1541c204040140e22040d0b940e13003d12a40341044c0712058441d84690045001c5401070001c1d000c101c0c01b80410064079010b030300d045600641207544004241d8542582e003113044a443c481d0710011905403023180144510b490007030241e03d01c584001711030940c3c00c3c98002882ca14001180c2c0b04c8140e9801c1b02c04c180c501003503001071910840003680c100840c0c8040c00001041c100d120301c000c414a581d14003541d6100300000412294101c0b60 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 298904757 1250 298903507 298903513
    0x18040c080711030f0d020f09030a08090f0406080a081e040902040918020d1e14011517150705040b0a1d1203090f04020f0a020307120e091321020a05 65
    0x100108090f981c1d1240381c18140c043d1005002032034141003150010300c410101c90902a082c0821080400e2400355018000c0b00c0704000802c00c0c2041c0c0c14070504000e11020219024042c00b46043e074183c1d102c041450b80a0a42c1c10001000030403000302d1400c1c0030880302c0b01020790b035075070b542c075400030000390010300031a00080e042c9254100d450400c0440d00650b0740d00104070001c610120707621038030000a822180719240420412041c049017506008107400c511580002c80d11200d1040c0f0a8000301c1d503900014005a848030f6060f18403031000500c40c4542400303800d0b110040c1c507008010b4a09000740c1d803081002c000005021404103602407038503040030a45a1805851401d46820003000c410104513107800d80e403061000c031149142c5290040c00f410805040146000b11031500910180d02104044026900000d016401c0091078030100421540a1808100c1e042c034840014003007201c050000d44401050a0103034060000070041c00c4840003500c0064440105402c90203926034055007004d66442c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 298906007 1250 298904757 298904777
    0xc0703050d0e0d0203150a0618020c0c010903150c120504050c3313170a0c060c0c260601080c0108090708030316030902060313021309150218040c0807 66
    0x2040c1510070544203640180a48454084c802006001b008020809680740b07803900c0e80000c1040322244405094000300c0c502503910270380210403a240142c41c16080703040141c403480c20404240c000c020a418645c400c000420280c104840464116041e010100c90084c03510062004100340068500c440702e0f002c3d21054080e40054032b540c2540313034000034545812610202b1030b180c22401c5200900040704120441d860242c1c442200b040700d20101d03a0010b2290b0301442c0810306000c3c044d4591030041440d41740400c03a0504595800c0c100c0807062050102003024141003e800350910001c81e444e200395074080302d086e9a50380c9a150742e10501c09002601069640340400d58110f4046014030a170707180400214a5a00c51000e007008078540455079008060b038403070b24940141d07114002103000c1d603004004012584141d0040013489810940c54001d013034603168000c00005d190344050480c210409500503207805079040071f0f01c410b01952803840d600919100b402c60150b9009001d03d8020101e9594040d401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 298907257 1250 298906007 298906009
    0x140f030c0705011515050d0615030e060c090d1101050d0906050a060602030c03220f1829011d030303040506150a030b0f040327050312040e01090504080c0703050d0e 72
    0x4c0d07200d80202903010f070710480c0700140c10b40240020182002c0031800025182e40c0e40074062000f01c00d144021001075121800013104e80010040660400507401c641c074601100040040c1290075602c50060800c0b004d42c3e0800802d030300a6042d42d000d100400c2c03092198014615101e4001c060869605240d6840c080c00441c0303040c07000054032094040e1200a501e042c00d2094900a0442c81c410440451501c8880c0030990703003c0248081e0087c0645100754a11038060325800007038031085503810940d1486600c155050041c0c0200802e41144282045076550b0204094064103c40c0d0741811601840300205100400c8000910340d0f1058a02c407441c200081020f80802064015610001c2d040f000300c1e2020950000e65065a507810920a003001c2500c40980300d46107502d0012400041d40c0118001d000304101e040034041c101400340b000d40c085203482c1c20006070303080540c41030141c2c0090719070342c20018040200d810111461846c981049413029903a0740f0b001c03941d8842e64010a000100b03003103045119 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 298908507 1250 298907257 298907291
    0x315070f0822060902130216060b041107030309020109050111031b0123040204050c0306033c0c010e01030522050c19030303061a0703030c02010906150f080303010e010501140f030c070501 82
    0x2601c003142403445040c60103465000243c00d2b440801c580c065035800103000100702ca00001c0c28294400d0305c002c0703138a81d040d0001501c40d0443d40c0c00541070120070420306c00003032070100440c0e102c41d254014540f890158600c04500415220f041004045802c10140600e01c441350071152181d4402c40c1c084c000c69840c203442007828001070322a50f4040d8000e6021600462000421012200c2c840e01560310322401840505105800e000794941300350000e03594203c56503171111180000500a09044c441030900e101d043c1c0d0b813001c40c4103c010344031003222511000c000003442985800c000060840c500c05031805d03100300d03013500544400c40c0400c0c03070700c000003580d00e42060f10b0b08640d040c0c1c06001410318450b524260301034284680301d0021950303504001703400904a84070b1846c10010340c201c119140740c1060340070722138680f440e000074229620501c010011181e4640580d41590000e2a009554190110010045002d01d001601030303080c1c003000700441d00368440b024045031409078000303129160030a144001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 298909757 1250 298908507 298908517
    0xc050307030c1505070614010501021005040201050d091502070305131d01060e011e020606031603020907050a020f060109050a0606050a090b1b0105150315070f08220609021302 77
    0x1034200048080100f044200c0018100c1c1c00241016490410b80d645c460003201c0b00000504840519000140695641084000c245c84190780003000b0358106900040c01c1c40c007961411101da03903200c1c2000c500704042c4039051400c03e21082010754a8110a290241084d048051107104040485100256201081101c81101c01d441c003683c844903401c048085800c0209820418140401d0807180c2c40d180c8004d83c0d80200d8420030354040c04403404c0c40410181401e0580e0494010b02c0007609007880580c3d5003000d140e422180038180039540325483d0105034203101e4880700b01d10560180304000160800d064005034842c403011a410440c650326448203030740c035004e12038451002880c00389052041064040041c0710900d00507144111481c5224882400c0d59400c1720700c035202001d00280812242000c02c41b48140c2c8129809900301450f0000c401000603c12900c10802c0020300700c0800c00582c0400c0440c0307020109801d2142c41c032b02e80ca0a080b00640000c0301c04034080c40d00000210100140c51003554 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 298911007 1250 298909757 298909763
    0x3060c030c0a032d060806061815010e09010608010612020c06072d030209040f18030c060f051501110609071403010f060303080108010506030304240221070c05030703 73
    0x40d050000310b0304220014141400440c2d5468055441c01024504941d03103aa0b8040c440c1a02086017810100100c0c20301201610403801055801220403448400d03501290b4406058010300004007003042c012200165494000e60700020040c0000c81c26682c8400b4850603030b0030945969000c810022121800c0b8419801d40380c816400020109403294407680050504030007803072014034504040160070700b5400340d81200701c01195000030081218102801510250f02001500f00039451030300c92641d0225050356002001c110000d44007600b04151540b09030b03410b4000341c000304240d20744146508000d1401f10030340c134003082c5c0e2180f2001150200161081c0700704d18617009031558618101071300240304101030000354155200c08000c0300c2c20a8900c91540114000c0d501c4186951410180c5821a6000791001e0301907041040706101000005070308501030204e80000501d1040c103168100e0400d000d401180110841e0300006520310080f480103000707418013503901c8400b520750700c400301540c6240a01c0f0003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 298912257 1250 298911007 298911031
    0x120e07032a08060c0a111204060f030e0109030804021c050a03030b03010f33170303010510080106050307080405010b090109050613051302060c10020a02010906180201120c11031803060c03 82
    0x80300402e205004840e051b154450880340c03140301807450351001c2d4015401180005134601080b410310f0390701d030085102440401008000c05000780e1030003484880d0041000e8001c9541070104018814442000341046030405c007941d12440503440c0c001c0150060a034128880d40c207020045000c1c4480744520040c601d1560480c1c2d88020a41e110171390080070140c0c054050400307600c0005440007880c0400500307803210101541e606e40c1010104046d589004201000f0801c19000500000350428120b0341c0204c03540c00c2003805d5550b03510703200e805071542d4054150400994800058039102940210b401814112a885000180604090122001250480e000034907050350f038405410080d0050020001a0058812107014946101c00f40d0340004003c8005030f5403000c0d104240f010501c1202c190200f41101820b4141403500006c143c0740d055111001440e60341c1e050201c4260281c48140c1c542c01802c0c0549e038072203a42c190322085082c90004514024020b890028214000302c1c0122849141c0c42039203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 298913507 1250 298912257 298912267
    0x1109090402120c04060e0402010206130809010309080c19030305090a0302060c030a180b0a110f03070f02010f0f0905061608070c2306090c04020406120e07032a08060c 73
    0x700110140304250700c041038003d0b084400380540702c50007414080c10042c2030610341d40c2080d10009144c680003c009d00161a6080603820004215030100e8450785030034a4040380451060034016a1803180340e400722414807600c130380d54481e24810301201d0385990180d1800c111607541c0c0801d281e190340a00fa030003030042c2c014100080390b00e0801c0c0d024540103298400001020a03403000c01031559620311405a032102800e07020006820118004e8070402950103a20038180600d440d5901c182c2c1c00050404014458001240640c65100354002c403109101e9240a0010030300c0f5065140080c607020801791818003c0c1e00004165910300503441041301c000340da8042e0165141c0004644490081c0c00848900081190144841141007404580c2c0011400504102c0c100818503030324000c050140c4070b01490041c4400c0001d20f0700104401c21100701e0400101d084500350f00380504100150300300400c0c20031a00b840480081000e946841c0b051500d18480d03c22949030305a4513034400c012030711410b07080000c04c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 298914757 1250 298913507 298913509
    0x9030c0103050c0705030307050418150b07051c030c1806020a0807060608061608150906041d12090112021e0901030b03100e0d1106270a080d1109090402 67
    0x3202c19030001c0c0e041c2c110b41c18140299107460855100303491042c0060004241440311001442444503943c0300d25100b000100380c80030708048e100b0424815481460340200e0100284201440300c1320b4001c0169948404803200303440080d000b40840001040010043c0050490011005252a080d10125002001d4880495442024603072001504031101030301d82d18000340450f010040c6c0d600500091a540c0e001c1c80045000401d440030042000d204a500a081c001c02ca413154560950081410b90340420850344443c00b0016800c007024118050b403283c01c6400500300c5a09001d44a800d109036030741412141200700c40d1050340288000c400080c43c04e125100c0c0c54090100041000070705c107040100c0c0d10101040024204049002c1c2d80c0c0701d182e12003560506605041c80045004541130804910304900c205031a40d4505005101c1c14101f00035095507128028607581c1d080c008040c20b000c55110001c641340032079203078110381c6115054a00705065854000903540c2030390950f041c003808110441d942e0b60 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 298916007 1250 298914757 298914761
    0x1050f09060a0203070819030e06040b0105100309240e0622060609020a11010c030228090825050a05030d18051305150114160206041d070801050609030c0103 69
    0x40c0c0b40952100300892000160700f1806440d900614982441c00401100f101809580050201c5001608031108000000d0081c4607220305454099030b480c05a903100c180c042e002001c03000e101406d2510800c031503804090b481d0b4001c052038800b01405221511340d0300525a0703114815107030507602107420300b08603038890b540010b070882c083c1c010440411015940c950240403640040c0716040054909542c0041e00c1409000d00d20403440180307011490011001190010b070241c64040000d40102092102115445030a5800140816106540c07000710443d510440d4600382003075441c0a40c1c400b8000140c18906291a1421500064003400700c280c1c0c5580111080070541e80000c0c8603100d51320f400308082e20b03414008010890b2207400060350741004000c01c4140341c00412400c0c104503030405411f90741c94114040e5040d01c0000312541112010781c0c40010002d01030b9801c0707000385040024062903415012110503016029a03210b1807526600c1c0d01c00d0203020b1003203001c110307003650120034203c5c8554840c3d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 298917257 1250 298916007 298916017
    0x10303080c12090c041a0f01051605010e160f0317070309092c0303010620010219030c0e03071a0d020715020705190218060d02090103061a01050f0906 66
    0x86403120740750402c100301c0c2c60512032043d1801c4955602c0b82c0301e10042401c20340708520042400b08503284290180e54005110382124404540c104503001c03501c0c44190b41204000581c055005009121003d92080d0056a9003007101c07942e9409000c1040001d08030b0740484c10b10341902d42262001c183c009c0c3c0c010001105900c0750108030100401c03004000f843c840c0f24401e142c5550070000e44008202d03014a070740c03021100c003298059400d030010401045425000303480303207810001030010040c0c0b00c0d074412030803402800b90f18422803612000c1c2c410f0601c00c40c0c0c50b90200c16980d05c03e44404410318900e00c01e02d030743d41100c0e0151100300000000640c141d0001d040280400740100d513009440c1080980d280304a1000c844100640d5540100d8104104001030220f01d95542d0305160300c1400f035080ea00010003868100600c8220207004802046031902d034651003074100d64015182407a9565a85002001050041d507180002809524030880d598464000c0b148003600380ca00e11810801d000040100503480 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 298918507 1250 298917257 298917271
    0x1e0906050d0201051c1b030f0605030c0f060d020715050108010911040509120705010f0e030a0c1b05061b0607020a03020715020312040b19020a022a19051c02010801030308 75
    0x2005140410f440d07502d001e04c8400c18144400c0e4000c5d0354a07086c1c080d003075a6a64141c180000c0c1801d40c1400f03a5140001d881181000484056800345c2c51400801c40d03501c141d10607603c802e40009039107014032030b51049948541c0042c00040011b40e81e02c001e41801c0320100100245103408001502c03815150603008160000c6c440000d944010180084080c003580c8003103011121a510de000c03843c1221403a228000c04100c40710095490840c11042c000d1032040010002401c02c0c005078201580f01c40b4a0401101034031000e00340310758581f40200c00380d0703070142106020b107600d109210001e180c0354804140741402580c10b40003040c40d1400e10b200581159680b202e0402148024000c10b01c40c1e0303580e000464060b5000301c0505d8554107002d07100000700c440b40f0340c0854000707004004502005500080700440600e80951056182000e41101c0070380c02d802c04419030f800004107200302180607001900c1001c80b501213904080c0d01d044415080b6500c3c00100307020380410b10b103400401c0480e0140f07602a601002e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 298919757 1250 298918507 298918537
    0x30606150904020a020c10170a09030207050904030203121b040b0d0e0102120f07080106050d02030a0608013611100c0602280809210f041e0906050d020105 68
    0x41d00360702050498026800120050340000e0a105035030501b4410b200ea0020036162121000042002e554a21a409440400e0099407a0003107030625209001d408094000145081c500303040904000b0342c4c03600403034420030800320440c01160264240040c1510b6001d2a644100e08080c41c00f129001d09030080c21140c50032507140c44c02c05600712000c0c4020040301c2d1117500c4034001e505004046240750100249210700b40010707000103000b116008010f54811074110500540c0d296107900350b1038040d01050b44062165820070b0021548003a10300e040000c86c965044106c2c201e00101842c0007441e504100c0050824241d400c00c0c8505801c01088070003446825092800c86c640987d62044102c0e4440c00b0000c00d07460f2200d0601403081c0f50744442c404446010301c0d0881d42410446282c0d9114200c0d10611021151001e400d0b102e80c0b6090320958648500e010841600c2d59510f5032251440c52a00311510315040d4080404203580d0500d00c41e00b01507030b0000e008480f65651603401581c1c990300020060075250 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 298920863 1106 298919757 298919767
    0x40b070c0f05130203180f0d11030708070f03021e0606010e010f1205150a0b091002070303080a0504020609040f060501080a061d0a060e0906010f06080603060615 71
    0x2491a0030b005035a40c1b41c15041a12000c0c0c4920204801c0c041c000b1031600d1210007148540e4002c1054641d90f01c51051124690745034801d050b4001c1c0b00c008203110302808502c40c00c11114440c0d100b0b00443d045403540300740c02d00703001c02c000010252030350012041090f40d590280c0300c0d10801500303080048020000704409480d200102030a5030426581e0000240b0a501c1090301712810800502a01d12041e1540204000c540c091901c843c096003031030790001516440011070104594060ba02c20700c15803910100380340a020058400c0e40e01a800380001e06090b41c451140c0b0442c8400c0b11400110310340b400c8005001c0b0b03203004000800e00e0340303011010800116012480e84500a07000740d001c207290b2361121050000e0403541c0024021442d0401007010920380000d080341030312005000031590301e945110403a40c0d490101c130b110780c05400c1940842c0300740c10710308044603400b80c05500d454205 = true := by decide +kernel

theorem cover : BRFrame.Cov 298741007 298920863 := by
  have h0 := BRFrame.cov_init 298741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 298741007 ≤ n) (h2 : n < 298920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
