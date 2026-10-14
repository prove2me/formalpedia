-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3090
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:38:06.996777+00:00
-- url     : https://prove2.me/submissions/d681d487-b321-4e7d-9b19-a51dbf0af59b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 555575539 ≤ n < 555755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 555576789 1250 555575539 555575569
    0x180f030a02032512120b1512010b03090a0f0f020913150c050d090201031b02010603050124060f05040b0d06051e060d0b0d0c030308071d060301090f0906050f090c 71
    0x211100100390301c5800780b840c050745d8280d800f18500c2d000c8400190301c020510b0b11481c00c2c460000e070720300100020404050061140a11842c25450140b40903900c2e08854800200032a280b1313407600c42002a085000004982c000d085104a460b22080428030b0040151080d117911480380e107481c0d2051001c0c001d07540b090070507581d030030300b05034040d9818800791224013012410b25031144141401503201c200c4e440f1480c0d10a0380007003086451401d0040c01c4810f04001180740b568401d21502c50801d0743c40240c001c42d199450720024842c1e403c00d0444180c003554020082d00f03640060080500740650704504243d0b0390440340d01d102d61010456a01090415404040d081007003071190001a800d2603000111001c80546241502c5209603110210203c90f50011000300e030b004018000c00550110703080202095480a171200004c807140040d510307010510070914111f8540751000341c10015500004800da07072140090040d41411111004005030843e48126180310b00c2c0300c100154030301122181d0901d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 555578039 1250 555576789 555576803
    0x71b0933030b0a0219020d200303040230070312032003090f0618010c1803080d1b1707030603022211041202010e01030903020303180f030a020325 64
    0x5481d40d0b42e18014250020502c4031030a5080c448828201c000b80c0c010b44260030320307034081c14440203201d401402e45040b00314000000f02e00d042802800c50000400c50703030015012201030501c05007100f241080c41e0403d140c0075503c0c1440b6500031014a0780000c0640030f480c0316500c2d04406400c90002101103802d00501c5440f150361044c03203035105445180007540c1144000c400e844d0104070407540207203480d90030344c4e01c0c0c0b00b49200c0040002484000703100748a090020761416242c504600030700c599840c460340c000a880514002859002c0610741d43c488200c0f924031000803c0848000403005e011f445606803000320407104240040d041718483d1103100250b95000b00f00040802c91520280f4a4000035080000361541ea084681c14088584010708000c02c0130f1148021441c0041c400180050350039060107041c541400c11071400a500401529441880e02d100b265011701c20348049494000f0418480a143c00001071450206502000901040c07032100c1a2032400e2040f010011070244150501401d40c5c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 555579289 1250 555578039 555578141
    0x51801060329041a061b070b030912030a140f090c0105131a0d090b0114030d09031b030204060605180d05070308030c0706060909150b15071b09 63
    0x903d4a81e1001c0b02c6a8800d0003498811041400460155400036000b01c40c040d4012611250159003003148034003821411083d01e0640c14a001c480d51740d0f9007034a1022420341000301c0000c07040c503220390042a410191031480840e608014001c20441041528402040c2c0130354a920009035020380100c0714800c040c035a111400c180303003148020704221200300e442203140040041914542d807502401541c14081c001c0c11000e545400705072842ca210800f1454080d400c440c80c801c6680390002c0124003100d40107a01800208060424103100031143c2d00001e5126141c00c1001c030b9007d80c014040d1445400c0504042c034801041d00030080310039507807a030041840d130000c0402e20002d104031002e15080500062034904100c0d003079031110103582003500071075505a0f031500b4680078000d0550312000c00354403200d802c005c105c0020001c80c15404140ba5041207962000440a041100d003a4800b51000d071f40304559580a502e907c3c3c00409407902142c81c05000451043c0f80c0010410080c00c00c10000500c0e840604d2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 555580539 1250 555579289 555579371
    0x4050d03020a05040503071d0114010804080702011709030d27330213050603040c060318050102030a050711150a0504080f0703090905011a04031b0518010603 69
    0xa0740c0440c4002d4104401408009041e8030b0401c4a07202521520046200c2c1d04a003440e256884070050780b01d04000d1030002100442d80e41c0140341c0316045504038425954402072400165410300d40040a240440590700401c81d90107004030181001c6050307607100340030094028202c501c96242c1c1d40680c148010700d410a0000107000c500b02225052418078100c4400200d01404821000f14043d100000395000146030b003511031a070780c0c01c601501c01141d0071810350130607444218401c4158040e003000d0560b00c0c0c0e10408488001c2445417042c9030301400a55491070000756241c042c007402e60308400070400070f1665842003880840c00c090018203134000b2140c41c2d079a102450007e0079010b0403d031010360003001800c2c075a003405001012501d0003525407203c41e601d08060682182c805920841030f6800052509101000e1f150465003140d41011071962840001c69011486c1a000e42c4400d07031055017680808290520180203904039483d9032001c00904c04c141c0000d15030401c88035454181c41c92401080e00c1e0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 555581789 1250 555580539 555580541
    0x100c0203030f130b090d020607050403030e040f1d0c1e09070c020f0607030806030c010e0102030d05060402160c180902010e010c051c0e0a0503071202060f070b010e04120804050d03 79
    0x15104091036415000d48000b0f031910044d02c5820b640a841c50341101148040c4541c04210041d0060a10b1500b03d181c0352844e2402031072841c01800ea940300e5a100c0c00c4e100b100074042d4212a2810ce003094016055100d495001603a034102030304014001d55003c0e511007940e44040e11709400f4018003a0418205543e07000c1c0481d030320285440d089a2045d0100e80000303442d110500a441900e10a40f0ae80c03609040c14030825180140481d02c1a040010b010701d1a000c69a001c0141d0f0780c0300d07800160119840c0c0b90000001c01034019082075460124016500c08144102d03068a8411503424418809585602201007815a40c81e0340d006400308010114141c0c3e40c0d4480c00511804901810a960b00c2c091001e076036000404000034003400244014a01c100e062404200e000020f210482c002c1138030354070380701d410403c0344032140c8040e00c102c1003c91150608841441110312490313101c40315921542e104c503414104410b06440945483e042d0020000740240110f41c8c960190b80c004000f0700704500303a02c400310 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 555583039 1250 555581789 555581791
    0x1d0403020304030803042d0302030f09040e124501020102130303270e0c03130804030b0406050105030303060a051003061205030a030509030f09010c0f0f14100c0203030f 74
    0x8003184420000080403e4030100690300803482103814100e8002e001d41d2a02d20045010034400c0010900752031040041c2d000000c5074902c103030b808a00380d203c1007002c002600800a5a1280c405402901d000c030718812400802042c884112011005015400401184040314500070131503c0c20002c1907050030702c201424612011100500c000f501e4101e8800144c01e48210325881100424100f00300c864092028241503005094505c02080380d4600e4480ba401d00981c014144400d10030703000000c40d20f421080c00210300c0c001d4110f1038039940c43c0e68a1612911404c1d0440d000e8030400e14240001c00d80780f8000c02100d00540d402000c0780e0300642844204001003080754200810b06959842c000b81c14000c00d522a0714560103480619180c101e6568003405980d0700802400464104000c0c241e003103c507510507074648031003e18000c10260554502481101c2510601400d07490010360b2034010000003450414880ca4000c003035400400c00c0f4a801400e44103c5440c500c050707007081c8000b869031000600380c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 555584289 1250 555583039 555583043
    0x9050f19020d0f08070c150f021e15090f011a03100b01030b040f0917031308130b0c1e0d0f14040e0c0a170105090705180402030726011d04 61
    0x1440100c900d6132a20b0350796010720300895524410100402035130a46004c0326442c101c0a01f842840d02c0c008810003902d98441e56282100c030030b00515403021480741044803171440700e44c43c00131118505100d260742d581e034101501c0c080115801c06084100d4178001d040c00001c1780d20b014005248403452689440041d1040c2034120381015910714002d4031503541d80c001e100b0b0051420100042c000c03098100241584024141c106c002042081801030800780d040c00320050b43c2e04040b03601c2e00c030154003601840c1c030642503220103007202002c6139484529201103020800c0721000304107d041d41a6000401d0780f50360102c040d22001c80c0f5002040910980240c900031240c441c0800303014649030320303403d030032000040c06e070ba107141c0520012418111458003c8450038199000440e1a901980b408000070f00b500c0c00140342008004020400c84403043c0301200c0742e004403d00420541d123a160488008090b40500400f0000710b40f42c2c07000e81d03906010000c2049040e1b90780303220a014500038092401c4d0b4904000303403003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 555585539 1250 555584289 555584303
    0x9120a030b010e10030b01030b04060b0f0711040603030306060f03060b030c09060d02070309030209100312030e030915031b120705130305060c03060901060528020c03070909050f19020d 81
    0x8120056074404c0071820f100700c070b41e450000c2d80c141a400010304603039903149118003030b619201c4140300e00d10080701a6280c0000540da440c0c1d03a0550341c604541d50422406000d90402d081107004000c0542542100041d2003ca41e1404007405103010110180e40700b905c41e1038042c0030304101051100440c5001010400405400c81741303400d825010070350485c2d12411095000a0304c1090500031841c2940c1210b030099141c0519504590948c0c4078511001000003ca10500d965040c02414880051090b1500074000a040070200e20f032111409a040c0e2080318488191720a03c5006040d0114040588880314900031a152150780ca013241614164070581882200c40c3c001880000010010440c0314890544460f400d5180c1c00c100040c08038140341038121030140f0909000d00d640f440c0310602d40c114030015105091603900141039051f414001c0c3e650034990035020303602001c100c05151350041d01a03107214100b20380300851444c10302600c4401000c180c180c861010783d1b1a4025150046c000500c140c0541c1d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 555586789 1250 555585539 555585557
    0x3181005040f1403120a14030a09081308100903021507020a0516090f020c03160c0909030e120d090b0703170411190518040512120f09120a030b01 64
    0x9801c000b07207001c6920150858106000e800b056080500c0f810740383c2d502c2c00c0074090a101d10410041c201c1001904207030385460002c0005200815550080e003a801d40045d0782c944d6030003500c403d800311200540038020301845144541458060588180da0032150950b014007500407803c82c10700c040910141906007180324500d15280441e006026a40801001d4800b0b041007501e441d4020064582484c0c011030500c1c030510001030340d550007004a6194501068607035082108503d403070313003010610303410031041a0300d440c14500070150403541c03110510b00c01b15407c10308603400354840c0750b89012041038200052110041005407400f45006000c1581c4242070030045414072000702c001c030b1042180c0a07920103404400b4111300f820300c0c1901c0f02404a0700301035070007418144400f00d00f8912403095580380e4a002400001d0500500744480c0d401030311101c6d1002d988480350340e51020380c2c07003065540340c21000f5500045900000e0000701d408006624039a000d0030306c0003454090b0010300e1103608450600100f00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 555588039 1250 555586789 555586799
    0x111515060a020615010212123412021e0a02030405031f05090c090c0a02070801020301090516032c010b0315071202090f040510030f080702010e030318100504 69
    0xa006038034003503030050a0500c4c01c0b80309407880e071203021380160554000035204640c16241800b01c4040301c0c100e00c9060550344842c2d620b4a4519039520003c2140c62203000d00800620043c10400e091507841d66800c0c480200e8502190103d11410000b8010448055242070000041001914080c407880c0152030625649001090801240f501060982424084000842040d03440b0351a00070741680c00820035880311001240310790b4800742582c840d0740705c042110500c5900c200700c14405450503070001d54503960748251000144c141030700d40c0c5901030301150620301014468481e070496849a02030070808a4403180008844e5201c05845201e15500c40302902820b45040101d00401c2403a9007000c04203207004140140404516a1358801c000c0c010440c01440347d45003c42c66040c0c0504a6000405850341c031005130f014121940f0090034002580308400c03d1243d09005009050300070f807501030302c0c100c0e04010182c41e84205254403100703103a0f1490b03400135814540481d40e203001c01810542d240079110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 555589289 1250 555588039 555588049
    0x6161b08031c020307090611101a03010b120601051e091509010501030905331e010e042303091c06140f0a050a11040b09030d111515 58
    0x40c0e0030003501544002075046100d0000b15440d409082e40c40b20442c1907040030f0702c0c0140200d4841c0701d19010803050100d411420fa905200d001401c0a52202c1000815074500928007450440c210180c4030394a49040008142425041c41600f080c41c0300191140b6804c0500700a5403070361040344100d6440707c407800000745441e089035041c012090b00c0828807003600c4c40c404100802c1030503041a8101414968520b00050300000c03810340308900c020208198202c4628402506084074030400e258a80440070b1007000e00c96221800321901d42c12801032840d0381c9807030240c1444c01e0144c030b00601807849006510f2001c0862000d0072030071900c540030750f8513190101d40001d082800d1041081e80d411316042028003002914400d0711241d81844030804981c0c600038404040440c4014105580c1a46650020b1a40c042d10b0741b003510034035030088009032180e480d4010504950402148a0b00900c40c4030880c06149000f03169117020400700030020400101d0000c03004600c66400740c03a00c0d6054002d084490300b66078803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 555590539 1250 555589289 555589343
    0xd110c0d030305060906030106050a170a020301050403050c0f0c010c0f03031e0e06010e07020604020d0c0506030103080403120e1c02010504180c2c040b03150106120e0102090616 78
    0xa5900841c00b13040113420403e40c3c00016103940d2190f89480e030100542d03142c0c02c241c0b83c1203030b42822110b441c44038042440f03030a211084900075850f520303082c10001015003010180420640c80801c84d803006119a0045940315012581640411140c041d184000390b0441d2511134540e200c0d02e004140724058400c40c1ca003c034045000229801c2e100c140f2002d82410800206005040349540c0c071031345042843d0007035140c120280c4041e008642c65051401807100320660000202400740849659613036a050030b030000e03006800111a01ca8280000d91420317441000b40742049407009128000c108424007030a1051000803604a050040510000800f03020300d01303604008480980002c2105520044000c1c401c42101c2d000d0041c42c1c0a80d4840350060904d00d241540c04103081e81c000611120b09000031303103000f1050451031064003036100081005030340201c0c000a40f11500350184280c0002c030b90341c1c0e4203074050b540302241c010301e00740b1072007040400205a800c0300900900c140401818069041aa1418 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 555591789 1250 555590539 555590543
    0x1807031e060c0e100903020d1103070e070c140609060a021806070c0f0503070e0f15120a02010e010509032508070803090901120807020d05010f0c0201051005040e0d110c0d 75
    0x410f0301c1d500c000e040500c0c0c1d038561458640b818a01142c10341c0c1c0003500b0030940d0b0300040c0204950401800b001c4e1802c2000c100a001104045180303803900303200040c51702070703031100485071b000142895800700480041d0850140c1039100c06003010340d60380c0c004000290005003d044840e05040f0f444511516003200900c2030303500030040d80d001282010018541c24000d0343c00315010340d000140070081d1000e076901d101e401117403440b0b1014803501c6140150300c000710301c00c2810754042e40392240640440d0700064a40076140c1300ba25843c0d4a131455000540307540c014004115015000f0b560141000d011520160100c0380418a104000c65181c14240b0f1505c511500309481540c0000360018051034440031060050039001c08145008025546184c0a4010321070002e004500b220081c000b00502034000c00c140704007084080100c0424420024007901054540c2070380c03000060400714160816004640780410b50000500900e81060012611080a045a400320340506900a0f040c0c1d41c6455030b00c14018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 555593039 1250 555591789 555591797
    0x602071a040f1503090204141503070b0a03180516090e0744010605040e0a0809010f02160321020d21060806010605121807031e060c 58
    0x90822456000345248960959021101440200700d03601e100160001600c03480e000561404202c86001c1c0d000d440c40d204000c4d4040d0402d81290110050b1210b190300c82c200d0740082d01c83c80b0700040141612801203000c3c00350034480401c031604005000c0d80101408002c144010818034280e034494500307258648041420021040c1c10400108000740512184000e20340c01402903c2c2c54404522002c101003100800b865240703107845009444582c94444100a0b070309400c104071840d40051034000c0c2844c0c01181d100354a040c5113a4101600018180c0000d5441280d040c41c00b1040001560285c3c4498006000c52090f00762010020003020031020056200d401d040194281002c0704002005507a05ea50302158005425542081d9001110340e03000c100079610211400300e8075407c4009000d40d81c1242020703210700c200004026901000402c09400500b100c640c0546511a1810000321013079010006030f4010076091010558640620030007030307640311081d01103034095038840741513460030300c0d4080201e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 555594289 1250 555593039 555593053
    0x203150403120b01080601110f0d030605032a0d020a03050a03020c0108090313170a0c03050606011b08041a090d0b040b07230d180501020703090b1c0f0f060602 70
    0x503400400a01e08038a5251083c0491021080000c0022070002c040a04100224203841c1544c40c05000d1100341030640b006682e20341850100150140c9168482c4034020310503c03040c06410304003413208800c04004c4100455541d904201082402c4840c114142e0b40031403240741c0000042c40030425205164420b030041c4c0151032848002401031039009052040c60b800401603503213499503c6080109980c0c902c203078401c05081c4d0000844c03030481210002010309120000101c10301100082c00e41c440ca00c240d039401c00815204800356107220070520024600300341030000b03100713002d400c1002c804501801c5d600e0504240080000900f11a80c01c00c050743c0c848102400d000500807800c07501a4081407504144980e20000c2c450001e00340000304605403141c101041c10004500d07076400c0650300c1450810340305005015820402d000394803058046020a8255100141911300c14081d5084119407903807030f5442c5800c021807803014120a01400c0d1110f03a80351007444001200388038403006003646074010030384 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 555595539 1250 555594289 555594293
    0x8070c08031606050f060102030a0c060e07080f120903031b1002030406090c05040b1c021f18050f09060603070e0406080325050604080a0314191d03030a1802031504 72
    0x219000504402c80d001017030410040b250340c000084589000091a201c460311040b8100b8000802c400410520203000345800080c15000020388841035001c84c1d13056980d580f80b034040c03014052003020344c0740c0d0b015003082c84040861045010151110480c0c4029180c0542c0880102801c0368002c41301101c101d580c404910061090554848018000c1501c0c10040090100000fa882e0310008141401d10340d413480d0310070210744500ea02d190ba840e4840806107200d11000101070903d4001e41e40e1683c0c8007242103c0080d061034180e1901c910154058582180d9485120502c5840e0748020310310018001c0f4084070b03418030f40381d5129440003852424041d41c0c4800c503030000c00404900c1c81080054504c980c0e040c0402140c0041000b5030010b92190150f0360700d002c01c920550142ca94107038000602d4039080200044ac0c00704548a1024a02e11001000321a1112140d084120307483c503041502ea40c002d000256048010354402c5460a01c400d282401b0518643e00007458110515003110802082c030040c081 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 555596789 1250 555595539 555595541
    0x303090b060d02241b06010314030708030f18070b03090c1e100c0c080a0b0601021b0f03070b0403050c1c12050d06080d0206090616020a08070c08031606 67
    0x50082000c80e0100d01102c40c07074000440e8140e490088195440c0b41034003542000c81c00004585c08101845982d03000490080c02031071b105d14092200740c03a441c0a00080d03000401d400701c01c960b94251312040b654250f49580350180d901e6903000f000c0601e505842c4141c0400c0032810408003000b080580c214545c1c905d040d002c642d0505240011f058000e0001c05556400140200c2c200f0f00c0311801a903441d41e1400380500126140300c00844050020490b015010030502004a801210386020b0050880c00c0d03155140120391351442c8510221180c80c10121001c4e0b14135101000c0b00054800500302d0b901a602c440240c452548640d10881e2503910030b82e16903030300b4104501242150b1444209107480d000880d12001003440700305c50f0f810104100054900e00490207030b80044060f18078081117652070104000b019503a0b080a0b10034040602c10070000a07801503101185200c03810b1a540504417001d031550700c41c003c680042c00121410404482d010030600300820151030300425000d041c404198890070608 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 555598039 1250 555596789 555596791
    0x40818031515120709090f0c0905090d210c140c1b03010b090703020f0706061206050a061a0702041b020732010528050a080108010903020c010c0503160303090b 70
    0x2501407510b00f03022102e407820100d0014121020100701280c600ca081c0f80000f40701c504240024100030744d0f0140880c54160646c41070f807240800d01c04a40700e501d028002552013038038181005205041a0940b5103800034a50030400c108250342c01d0030b5501340c0140140055a82002144040540c0201c51200341c182c00c074046d010521206400030054502030101151254000a0690003819000a220003001c00c0800c2200d035802e4000d00b08100c810340721400c00e0010100740300255802420b00c0c001c02c0c0021484d1264504440011000b880380009100c1c1001240d04107480c140d0740196034071028003c0800c8100c5040c02c0e619181c0c09032103040c0c10b040300d0511111200480c010380c03040704404200d902840303d045256605090804645032100300b0940342d001c8460710201d010900c5458980e4200c60740020103407a140c0304603161403109030b80f41d0107224201c40404a001d401030b40140025243c0f940110441c102c00d0b8000c100b524513010740000003ca541401c1681140000d80d00c268180c14001c0f000901 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 555599289 1250 555598039 555598081
    0x20d02180a0b040b030907030602070c03021e0a060e06120106020c0a08010501080309060d0f0c02240f0a0b12070609050111030c060109020c21030f01080a0b0408180315 74
    0x784811414481140003502a50180312a81c0b0740010105410074000c1003880000e582c4400305550302c0300c1503e02b0040c2c004240c0300c12809014083c09d003e1071804852688041030ba0301401658800d45450012502c60344020010358000504019640d211240d0b42000c2d0b000c0c0001c0e03002014040f100760140911952542d0007054564034120051010a40200403030f48801ea007196a15107a0110300600002040d00b61131031a0840d01c2c4c80c1841c001c1e540c020504c0d008290028403044501c450049280040402c1118810f030a1030041000680001d07040d8080f0320385c400701810440c0000880e00c842864594290000c42c0483e028010402031581c0c0081345010130500000550304141202544a642e00418050707030751513a4001c036a10b90360503000c00402c20b20840000e500c1c100c91280d001c80301c0d01c9030300c1030351441c443c034174182c00102e01c00c1000140038060301d52222320f507442d5030b5894840d40c02940004094001c452031000c0c103520680c2d030400840f00204101e0b5082501410101c83c80d4401900306c500c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 555600539 1250 555599289 555599299
    0xa025211011404050f060909070206091603020102151b040f03020405360313060804020a050a030c061407020904110316150804060212010308070605060109140f13020d0218 75
    0x81c03190581410020f44003202c0301954801e07503480248000582c03900501c1a819006044041040200d9500250042c0111202000c0d80c16403140400304901039030050002a015078007044d0505442189131250300d90241003244c04105030030f00c25060110541c816881402a104d2002e41881545003501c1141d030008030a803480d642e00101c0c1605004a0881003040103032000501020054040c42403003101d0705419040900248241c41e4040070341124000d4070140c1c02030110038804500e5050480484003500d4100c0d42c0140300500e4040e0131030b101e80703001101c12900c280c144003c40050b00d845000d00c0c01584164821125040540141407801004100d10340b00080c40040c00c126003000c944419408032502c0c41e085e10706950ba402d20390040e00c40c50a4040c40040108000428001d41001410b803461043d102032209881d0403004651030996805010b809405490040095250410440e5260b80c005000100400079600c11142281c0102c1030044042e0740001d012101b40c01c0dc0a44c0c10000402158 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 555601789 1250 555600539 555600557
    0x6060609030b15011103030108070e060a081e0c090c030711070608270f0703121d040209030c031b040606051c0518060106020709050a02521101 63
    0x44031591844003414101c440c22048401d85400c3c2d109100800350b101c0a441107c1c0d9035691031910310f90711881c034881c2d8100c610607080800c40700d19284016074125020440101288000400ca41d00c02c0401280c03c86160f1003510010440b984903a04074a102d00c1e0b01c0728019882c0d1618440250042003610407400854208032010f000450f088047c51340c10069014251503112000b91040001428105d03900c2c034180301c0c0700303626030340c20300300241d00310550340b1030b40c800740c00d40752100d2040d00c1c405000b0050250f0400b0060708202c150510354050080854020115680206614007290405111542a6448030342800800645007080e002d000d005202c14544589010002c04141e60800b10003004114120b403590003288150480303030802001a0210000c0d01c046580d00c03207020b903880195110780070100341040006100200e852098529400700724040c0d82c0c0301e100603425412080c0200320100098005a940e40c5868011141c810070148010990b40b180d8030344a0a0082d003813a8107a030b25074104100c100c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 555603039 1250 555601789 555601793
    0x3391c03180611041a03071e090509060d0836030601090b0a0807060314011a070b09120f071109010501090b0a03110d09170f0406120204030606060c0606060903 70
    0x72141c40464102e41c0004076903103245100e800ca07100d00da0107007041c03141c81440c0c004122050001140500c0d80f40e184d103464280c0d42d080c40307546280030000d000c1c0403c1c2c00c00001c2080781400d0040b5544498010046211500243d44d032600710b400010300441c07030140080d0081049920b141da840141c00050a4904901c034826001a5549605000e02000d1f140c1f1800e00680c0c1c0d4482c1480140030740071141c00da40d080c580b00e100c000c0c010a83c0b0050440e060003a20000120901100b0144600d44082c80d0210300c1c101c039039180e02600e2030002e85210503c0c407031806d0a10075201324002418403081c6259800f580e5000034200068202d02d25a29240715549440040005030380141d0038604031490b00e89469215400781c20160011b02c80800020420580050b000559000079031040300620b100d800003c103241e030045006800d1340614160248520000c00c8203008040c01500c51440001c1299001f52825469980f07410a5402a500c0000400e4140000404100c1e50303000e2400640207038a0310b417031010715607 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 555604289 1250 555603039 555603071
    0xf070f030e10090c030803010e10050616030f0905040e0f0114061f14072d020616140d0c05071505040501050a050d14070210050903391c03 61
    0xb02400494103660b8210000c20419505002001103030004221500c075a035600481701c4c0c41e142150920100949440d02040174074019099031241410f400d00d41c8260f00e61580c0596a441ca0301c1e0810301030102007900024141d59070300609412a501401500500701340524180c00c0d10100c0040c102151048420003110f92a1000b03010103072009200030040c40c0031002d40a8800840c0190414442c1c440012041c042c011030b084da40d4503008529044e000c1c0940022140d0908144858000b0347c0000c0030410f600c802c400f01c0c000950401c0c0100b844801d041c1e04d40403074a1030080c091420801248000340c0f08001d01c001440448014815a200082580d5100f80d000340701c1e00c10b0b0700074507040c024040b44080031680b0800645402d81e048080c20042d08010000c1903004c00380407642c0f00c00600c1a0040940d040c446402181d000d6000d0000450610040703c44040b01d8403c016145504103800e0000e00807050041d4420f0281e045032000540259600c0900080014039802039100c2031508207110f075030a0030342d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 555605539 1250 555604289 555604303
    0x30c1401020f0c0603430c02131e021218060702030301031b0801020c07030606090207080d0e010e160501030c0503061011030903030403060204050a0911040902070602120f070f030e 79
    0x20407076000f940d079660040c4032010b908036a0545d108107036003e980c0b01c9501d4003200c850340710a2040105807040300b0640f202207401007c101d900070b4110100340c518010700e0340e158021030801000420919a8014110340b550101c0e08060720524403804090144140e20340c1480c840501c140051001d000c26103010341c0040e6681c03106200c01400c0c1c0004651004800c412000002c001c2c1000f14001c0d91b03540448211183d0311070300f500083d18514070300300e070005070104d051084a401a40c001d443c00e003000301031000d4000800c1e51292102081d502d5880300024a0800d00030f404801070313500000c0d20602d040c0b8000504071511800e1715030900c0010070512800c0d5071074035851013a030b00c40d0385000d074070030801c0306c01d01800d41c000c0003611a054400441d01008201e50303a006070080c1c807800c1e50000301c0160b88074006d2059401c081203580300c202c1c00700828054009190020503046008240161409203c0c000440000108440c4201c903200f40c1c009104003c0c0d8018030170b012030300c030710f26060286031900d00c4d0f86c54a43d01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 555606789 1250 555605539 555605563
    0x80615070b13060b0a03080c0106060306120201030f09050303040318050901030b0a0c02070803040609230604170c09100e07030b101d030709240b0f0f090a030c1401020f 74
    0x7444428040c20003000313030010006a500900710096130340d582d00d002e09007900581d24200303055003000c9020600c80e21a204540844d00302192240c0b03a80100c0d0010740c003d0504482c004074280e1122000404110200010342c00344c1d00c269200c0000d0810100210002080e03604070710320418840c001040031491044681d074201054000003e010603d006c0c0580c0313415060341c032440380f0b40008240003a0143c3c01401120464485012407010640200b240140209400c6c01403584264288022700210051080c0030080030540170445100e25068000161500002c803044c41810181400600c401e5291524041d084285400d085c07000c208254009a5007124000011040100268142035103034484660045103080240a403401161a0085840607159040c0f0203401c0403031001821070150400e054900c04c0380d8900440d0f03030800d4100309228215605c01d0615403640082800309007203642c0d84100b407030020741c0b06100010b515403410040ac001c911828100505540015504c10090b400205688007000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 555608039 1250 555606789 555606811
    0x913020c030f0f070203070608100504110f0a110a11040f05130b060609221103191e180203010605040b0d0231090317070215190903080615070b 63
    0x600c0c409101440f50081e014040d50510035103400003070280c0c008a00794040c1c458041c035011400c0e01d0b401800103580e140001003181423010880f0901080304000505031004031880c1141000b1414034800d40b80800d840f2080c3c5204c002a040c1010514183c07080f00d228130300341102402640f41030701108000700c61f611000f8120003204070000340700e541c0704002c81e99214002406a83c07640403c010401c90182407003403084c002d034038141c18065680410800d0301d120b0111070340c1c2c1d0240300d41202180349c090400030840b4054002220601800503c3d60302890300850a1003810404404050042509440740340c1c0c84640218a0803080c2c01c1c50362182c108c1c03100c030346806035140e00d034100e541901c040b0103080d1440480c00c491074850740038207052515040a040755000b0303a02d80c2d180caa01c4a569410b07900c000d40316540541e10821082510b1080c0c11036403a03110424070040340c0d0341c030955921001a00e1360100c2c00c6001076410020840344d03207001c01d00c1c0480f0b03880555038070741040c40c039603280e4143c0b03c8090140404a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 555609289 1250 555608039 555608047
    0x10609110319060f120c14100c0f08030108100f020910081b0301030b040c050102010c050d0903090e010b0c0601080a0c1e08011103090105091506190306060b0913020c030f 75
    0x4509400520040c9841410240242c2c1d54045501820031080341c06c0741e600c0740e07200c800100c2d85007401c0b0180141d0f9000705549040314014005440b1044040310486a64807220191004502880042e41c02010120040c00a4942036007061040303500d454080c41030180b0501c03180c24151640000710085081504000280b40c84013100d00582d90340c1e0394600c00300e00c00000004410018ac0c0981d040c02284144141c00b003c5450f41d0040e800d8902101d480400100c090000e4854001d440d000150154000c3c145003504540340c001842101d2400d820400e10740c000040c80d11680b43c0100034160061a981019100900c40c0b41c2e6007400300c1105210300400c800c990a6030b600c0c01c00261340744400805100e0020400114400032000807508200c3e400b00f019440c0000103488124007240201c8400004217000200b81d0361101040510190690840c014001e000c802000051092140c40041c181c0032340d05944a558034000c00c56561065030010481d0750050201e00800c04000054840b48a0191829625 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 555610539 1250 555609289 555609331
    0x60f1618090f0605090c0301031e0f02091006022e0b130e0106062007030201050a030e0f01050103020a1509050904080d0515010305090a0c0506031e180106091103 71
    0x980316003221590074a84100341c10a028103070300610443d40180c56064450313036810b030b810110340424071000d8020b40c0300c40036641000c1100400880307824495516406514040d80210b60003d40403550070011029030300c070511140c3d4041100d5800b084282010740d826114811030728108550141c0030010b55a22844584455960a4203480700c021001a007040651034411045e8040c100034807035580422206000c900302d10480440500c0d1015440008001c0503103075030700454590780311044800415a8800420a0544085c0219016540480d002044650450041000000b002e80c04040c0e0310424583e038181e42508001c0d524200c410840352404655150b0074940824400e0943d0700c16207929001c03c000c03142c004140e80c0b00301d0a9080c0e0301003085940381c01040380e4820301d00c40003a2519403011010400c5203414001903a0010011a0f10005031010450030040064180e9510041c08000d0b061100300391402d1081100414410030284414000c201604045210241442c01a0034000c9140750b1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 555611789 1250 555610539 555610577
    0x17010207150203150d0f030e0906030d0e0609180406060806040302060f150a03030f030b1512040c270b0d031d18130201020c09070e060d2a02060f16 65
    0x2404201910740d1110481e41d2801b81100c0c600100d084011500140c07180c600c0e030502030095132062801600504025040440503500a07503244c0c1c02035030100040111640c0f0f52690403c50081da400e8800400d46418549002c209440590300252119485042004046540000c0300c5800200d00d070054402622000d429802580c1a20300c11034014209100c00800c059100c00c1e8001c082d00c2e6580c081180c050b06a04010740d4446c0d001072001c501006103e10f4000042e20048a900710340b00d20b810000d86039940c1702d001000b000420004649450828070088030f84090b0240902525007201c02c040508502d40e8003600d00d0b0010080540144840f4031301c0b80c3c4d0360715445c120b024042580044010185009080720540c0100201c0890050042e600300442500389100014041c040c9600ea0700304040c1c0e030100780061500000b0348408800d41302c90030701610610024820322038941208480038029000304011b85003142c0030f000b00080c505010b040110f41c56014483d0410410103140118400003404600c0e9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 555613039 1250 555611789 555611821
    0x91306053006270f190506070c020108011401031d0a150e12030c0c30030c1909090501090c0e0f10030e0a02040525020304120312090501090b0117010207150203 70
    0xc003003441075070140d0100d1804407517000703030741407141045030f209503500701c1d0850b04580c2c82c41c0028081a003100040c402604064004032032082e042c50300141050300c068401c3c0c0301c4c0000500310301c095048560404240a200610840d0300d0406420a024126119000d950740d09503400d02440c01581c048040303203480c50800b0480310400c2800c000c030350000c030022503107801c50b81c4804040c00c6100802c8000010400020094a00c5241d4070703c0742500300500e00c40141821290019110208015000c0202d4814101d1154030301070074101c14000383e50352081d503000c1c0c611402008403610400ca0000b0460f81503641c43c15034000b98810740f41c0441d4500b40082220318004210703000943c0719041a04124030003106003000b07110400305420071244d03140041026a200d00ca180a8120030b00368240500700401d00800010080e04600080015200a079880d518212900200d04842681100004001e0000100700070400d50524000845c940481e03a600d03811103100004101c10b42c1500840003600c4444c202c1264 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 555614289 1250 555613039 555613063
    0x70308010b0f04152f06091902040c180e010e0a09020d02010c06180303141312140d0f0c021e0706030b030316080d0f05070509130605300627 62
    0x160661814440c4c1d8030a02092039000e00b2121b00c11000050400400095450501074140381504035041580d001e10002d40300b494082820322500442c0e9401070920f0844032002800020503040041d41429000c078860340c8090600a170050400105c600541d0b0b421500c007000c154242002810b01040d0710f081d4019105002145140c00c107464044e000b49905504000c14004800740c0e4443c1a03a82d10501c1c480e9414004400b07070000f00b41c1500c032141c01b800b0754011002c6c080c2d000d51050503c042400e030107003901d0044440300003294690760b40007041901006a480d02246000308025200012841c1c682e80d11540c2c400c20040607290007400c2c1a0707440604c01c90b62000f01440350b0b550221a03034141203909502181d00c4000e03841c9000c030a00080782d445e02c210342c081d0b8015550701d8942415141008140541d0300081030f000750ba03403040010207540746171900c03070485200407188503179088070001d1030a900403410080d00507170015030030003084844009807400612040c0742200a0084d5a0b0041440c1c00c5000c03c2c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 555615539 1250 555614289 555614327
    0x2030f033405040303020601170d0c0503090d0c17010e0319110a060b13020a0203040e060103021911010e031c0e030d140f130f020405061206010308070308010b0f0415 73
    0x201003500d50b0000041c01036030300035021201c003030366140090007581c222100d407110617800a08100100318450b201509910b40603c04803810b029030b020004440c045170803c100ca120000c2a400c0110498000d0304001200280c4020400c1c140310040b0b007600d9105900d9078060b8821b2812407070708824041c10240080e045090210780c00825180780801c010000302c000c541c071030100380300000c000305d8050080750403100b030030f80c09107040c18036150600d0f812080242000d8103064017407000c8440100070700c032148010961030351000c40400c1c0c452034071401c403681c1002c0c1e01400c1d08100030304054121145120b1101030341c00540000c860180c02441070440c051084010f031828188012401c482000d4800c4501644442c041403901391140c08401002440c111802801006440a124050b00d080c0c0d200030b41c000030140c401800c11120041c16418218260800c4071111400318180d02415440076a42e400b500303550149601d0320000f02c0755020076024921603403018200d402c458640c0d41d03200b00c401c56522003600070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 555616789 1250 555615539 555615631
    0x21c170103050c011b11010c030c0b070201050402120a0506040f06021e030402011e0807122c060609010b121009090f02040b09100302060903030f0a0c050c0102030f03 73
    0x1800507196001d43c9101c50006050668400c140d0240b24040c84401d5400400d0102c6001e2240043d6200701c40d1503015000d0104084050010841400403d48030707a07020b03400003a6070300d020301c1001900da1600451851030740c8910507444c0040d40016076507030410341021803800890003528110000c1e1283c40f8242d0408003440030700544684005000d54012032013601c1c0e00c107000781c03c407944008000304409440e0015000501007a821401070100250a035100e00d00801d500c40c90701a64400007604a0300c40c501440c1a036602c171301c20308007840483e400c500200d0340e03000c003940350806500700c601440d03110400350640341c0081900c2ca50082d20b101d00134160b091050000da850350800b004050803040003603000c1e905207041c52200d490495069032184003040c03c4440b800707081d42c0900055800c2000702c00d030148000c00419511a813104042d08051842da501c90141c03401ca450041e04015825400505550044c04841881501d00c0140d940c0650442110b0760074030418001d50356030181030012400c0c03a8111070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 555618039 1250 555616789 555616793
    0x5091908060405060c071707020f04060605121b03010509150a0311040e0c01090909052805070605040b0a05090120011d070f0b031e010923040201021c170103 69
    0x119000b80302d14000d4080d03c0ca190f564403030400e5984a00320b4001c103074421645981d001e5110b0040a400c00e00c0c0084c0034440c41241100100381110301640203480810004140c0c640c8041c5481c59140c0d2014154400140180110580602c180810702401e40f0405200000074143c4944510502d42100700400100f5415528101110f03400844800c440c01141420001c01d445040010805000b060603965000751f14500711041c0001c0c09503080441d014051001d6004680c1c03504110f540c5600c030705001c1c030400f401031885e2603860105a94007040c10310034144070030880310316900c2c1518106000e504000d07030f4481100300102c031881010100341c41290481282c03a00ca00c981544035103469240c1414001b9600d1440f030020355544140d200704814407070824018406550038101440d041401515801507002042214801c0c00009801c000c0296658400c81c0c01c03038080d054403141000900450a40040c280f40c0c0001b0740b28641150000c144100c6082003180d511711070707045540180101f03804103031956164 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 555619289 1250 555618039 555618043
    0xc010e1f031d0d020c0f01140c0d031514090c0d0219030f0b24090604180c0503070e0405100513060906050604050d060e120f120f130305091908 63
    0x80d2080d84004164109812141c88009590014094030750020304a21a21724208005040d00c02c2140341000412400c0300301c5940fa03240508036040244000e001005070b50170004003200c03514800520751030000b020410088e4074080300101c5242c42070300c280346280d440d64040504c1e03100307515281640900c0001c0c1460201384105628075950a40d540520005e002e035402d04c02038070150b04505900a42d03404e1225100003d00e064051408203500400b41052504400206203401560008003040564141c00c036000e400f5100b008207112640c10f08504506103640010a1998210181c174082c0d0b643c0d6021959a03900350800d00300030140100781844200248141c0e00c050110340c800d207540541400c4000c21280f0703090701070300e042e54030103484018201026103502d4003800342c0000c00c5085006e6025001c00b9504280c0041014140d0070052960f2803000ba50700710f156040083c001e01c8080c01d104240084200c0100c280206980c04d464119210000040003546001105842881480d21f51038001000a00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 555620539 1250 555619289 555619301
    0xc160b07020405010e010807050402030406090501140703150605091201110d0b093403090b07030204140a0b0f0f0f1206030f0a0803060108130219090b0607050c010e1f03 74
    0x401d640c14002c130790342d1300d41101c4503480a0003011456000000f00744580d041c81d03405143c0c4180100d00215960903aa01d030a401c6610031000c0c200401d4882c070420941030b801d8002e403403440b041100c8448203180780007c01810390003100d50091242004000b0340d90005002d41046000c0140036803400e07500c0030740c801004010b1000c40d0341c0324003d40c1e0500c001110702d401509440d04680c0b0b425140d00350442449102d8403510082d600300c80604d5510800f8230007060250013041e203e20031580b001a5540e05110048043e01a0603c9003841005001c0307061004a1014054840000c6208600c90710750403082000c2046024000000c040304001240c0409200c0d141641c56019500c20f406030340b400d120240c280c640301c54180340c014042c80c2c810004904154410305a0642c0600352010401101515030b00098540051030f0008100540900080c0211002c170701c80c44000d1003040b0750062030103e50359a1580c17101c0c04130300c5180c180250700944400c1e6407281c41d04400c0902285102803c102400d00014005080e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 555621789 1250 555620539 555620543
    0xf0601020d0203070c0e19090f020f04150605030a0b0d1b0b040b0702090606040305060f07020c031f0506030a0f0305040306060501091202211005180607080c0c160b07 73
    0xc207000006803528004011600c03000d410110f410b95040c24404001c039200e2024248050403c01c0a0798091003c401e071042c141d03642d03c1034052100e51001d900420060700e42c04000c1910562400340c241c0e6003040d040f22103070100c43c01e80c10195242d40d1904035510080004002c0d44c1c2e0401d90100d40c040c07c00c44e07003007040e00550b151741c481c80e6a600d8440da2401c07858003a501031003900b0007080003070380c000d45401c0d0022940840d00070101e9140c96241d554050900c5c5050f2400c202029002d170902c0400e0b07805104803101c03444294000c00d481d4880300c240c44085690310100c06510b03503840c00450050344081c0003074981c44d034201c144401c850703406240c000c140e503100e40710541c0d0700c91810b800810340f50f201d480d00401f1211010401d0811030040d07000c020901150071009840b201344d01d10b00c41040f4105018602c0f03d5030602c40009403500e054003030781001c485002c40c100b00640000007000102500086540d400c2082e0b000a075464011218600b45003000080c2466202442c0110000e01040d10b01d0003403403114 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 555623039 1250 555621789 555621793
    0x30605011a070303020c01020f0a05070c0b030c070b151504090507030204030c060503130615050103060e06181005090f090c0d030203030a0c03140a02042607030f020103140f060102 79
    0x203a60342800c9540c0c5121050740c00501c400c10001500402e100c1c1d006440c922072684001840c0c01e18040229400703a01060000c40883e81c049121030501104000c0900244150b825007442c601c0d201c1e0003c0105d204192004251000072000301d242c2810b00303014010714a01c00b418851078001c56050400c07640d081840784d404810700b4100024a002d10130b001b80c400f140d6200c42107906950030044103841c03a0700b00030500c101c2400703910111008207085005410824948120201d0624105400103050350016081203040f00664020b05c542c0ba20350403c2403030008020310a5400d1501c4010854400035051303800b02e42d2102c0c1d010188120705491840e0b09002d601028211246255644280840340382000700c05001340c1c02c10f2000596012042e0408110a4214940000c410100007010400c1c03000c140d0f02d81c039070030b03078045010300089a07400700c5010780c0e0514101d031081e6010015540703651a0341c0b9000051011340d204c0b0f03c4a0459001e42c0202644003015503481c207881c5800a61040071342030480703150f4014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 555624289 1250 555623039 555623041
    0x14010209030d0905183303010c0306030b010509041e0803100e061806030a06060801050402040518060114011e02162903040f080a02060118020a0c02010e12010e030301030605 76
    0x50280d8074030003c668020b02186411640107446117000900284921203042c2d210503e440c8141000da40c3d000d080c4550f002ea202d640c0308600506003120a000500014107241c44014400f185212400c181154030407110301c150f80e9900c3ca000881c0422810300090300c1884180440304105012014510074003003012903200c125943c1d00310321480d010948185070001c002d44590004102c0035940507070b00080281c101e03402004103640301d030201e4440c0d42c010301c000c1c0d41d11418482149018081e043c0c21604004004000e0384003400100c2d1500c00c184906001e21040d801e002d28203074051565414076109031400d06240c0c0300020406500d4140d000c00004902c00351600104201c64508414018002c42c543c01c0c000c1c14113500c0700cac140313141c0c0054015070300880026440d50014445078000c01d210440d5038007405d800c0d45051281145007c1c0d09114480d043e00500814000a9009140611040c0c091900a000010301c40100e0b00c0110b0b8a6841c02c002c0d42441d0051480c4500040118103e0388220420002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 555625539 1250 555624289 555624313
    0x40e1f06030b16051b0f190b0c1e03040314031326070204051003050d091e0b0702040b0d0b0115080a020406021207170d0b040b0d05060703181401020903 67
    0x14a10310366029022510902842541858904004a00310316803c2146ea4a001c000115880c160b901901d81e071225112100b49800c0103456209183c010b211800418200001050b02045011040b11001c0041c2000700c005410b052040c200403003100b5442d8080d0380c0d02c0c101782c11113060305818040305031100a1030644c00c01440291801e00038080c10704140d0181480c2d1241c0c00c00010b480094000306001c2e907890404800308809010130029840907444e645102c62814681c03680082c040c000d1110410440101013141d2154207003282d02003541142c00180300c00c200d90000d06032590540001e00748000c4500041040d020003c41d40b108102c498544002c95903e52400340142e1046024080044e001120f013140b80741240b0001e070440502c07030307600300d500a19114130b6078000380c200d454018415612602c42010310300b054032803200b031000107903000d10340029152226595110050480010190f9501e03100080c03040324081000c2d41c60740700c0915100c207102080410301079003100c98140d210340225072070259 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 555626789 1250 555625539 555625561
    0x10f080103110d080c0312160e221515120e030d0e0a080c010902010e03011505061803030c070501090b1c270f050609011505040e1f06030b 61
    0x1049aa2200708040b0660004050048200461004a071091014014803034400c00a00c090084081510400f0400d480e1015440740d81040140c90101400b540020440d2207480d480b080c811508e003141060002485080e040c0d1004140904c13484031940002c840208202030066202c82060b41c5564030141352001110ba072204580030010103101340e520820080b1280c0d02c0c0c6803c601c04200c6080190340740700c54103458844145d440440d8107036840e55a120b80404640c0c1040c0c105040701001d6000700500031840c02c00d9050032071107001d01c1c0c0c800c03e00031809141d002d0380b400300e944104201505a0f900d03844000a06940c6899901855000c030b00d5045002c18426100c40036111594100314400c00c1c48800d15a410b0001c2c00341c801d01d4040743d601040d0034000c030080466281d10341482aa0400c04d03d2007581491410701002800c10005a4104101c440700b5072200150301055840807030300050440300d205c0c7c000789001c810300070b4013410481020f0144108115680003004580c01001010a244c0c0d403084900c1d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 555628039 1250 555626789 555626791
    0x415020c0304052b0b100e090c01140d09030806040506060f04030602030c07080309030c0609030301080703020118091803120c12150b0d0902270117030f070c05010f08 73
    0x64207a0080c0400c014920b41900b050340120010845610f48060400084165400821065a401c070341c5000f03010884190b00340c0748004103081010b941e480d003085410300340c580b00742038541410000c0000012050441d00c02c01c03245050035007030381081481803624026284c0a0200c50780c0380319914002c000750450800c001103980c0ca0300b065114500e03082c110742c2c89800035000034000f910100c02c14042d000009003004000c50256808000031515107050064103480c1c2000284610b4003601b09100400083da4006416425681d0900340120000e588092024082110360700c00003810b42005c09540f150900d1002c0051100d02a07540d4403100c800300d0703040c0b40c160b407410b48014001826201040c02c070701040e90f120390b20719002c0100240c80d00b41c1c2c0d140c19211035009014039000540e60354040000714505080100300c0301c81009401c0c1842030b508200ac460b681014800d103407000110b0420017065030000e2080707071100c10480b0f890701e45501d103908109810150ba4050540812400b544072541240a44002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 555629289 1250 555628039 555628057
    0x7180806040b0c0a050408030a0503041b03110f1207030c0510180e04051e010609140402060405100c0c03080d242105071706100e07081308070b041502 66
    0x100600f515603040c5040580e001491501c00c01c9014040451071020900003040390703011582c0e402c2d440341041d041940806010008071460301428010400000344014001c9000c90740841d4801506c00010f000710381c0d07119408413241c406004d4040044100b145038814007098074010b5400f2941454002e50554040380702442c0d8510704181400e0400403064510794243d80305101d0b80941e20701040020607884000c01c40300f20344100d651226014403014080748544544807140c542e4030006803d0540100300c20784600c0c041d160181d42010f031720030240ca018000c2100040c0c1d10040240c10701d030385c6e8100700c01c1e10f411400008002c181030070100c49007481c0142018101500041c01034080030301d01343d83c00990304020100c01c02031701c030405100030216809011040043c0b6290b0000f4004019010302c081c20040000d04403004185c8501d414410341c0e401941c8107a0042903801c1680f130581b03840c42001c0c50900340b040003e081520008841040111024495004900c42d020000710008810034000a900600080c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 555630539 1250 555629289 555629303
    0x3030702071d0f040309030812070f020106030b0f1b0301080a060f1a1009090c120b060f07030305040816032c0d061d0111040e01060203310e0718080604 67
    0x200e007400c583d0b0862035400602c40d051011016540c1c1d56039034800c2d0858202d085054401208102d0710582008941c1c284004a10003000864256603a4004003840940b004100b10101400121802c2c40506031991a200003038102d0b0316980e4801e8100d641325242c0904039031483c00c00355415030f010000d026910481c1000c441c5281449400424021022441441d000801c104100002404105841003011424142d03640032103007001000c0c0345064540144107a40100401c0210051440103a01500e101035450301d4007141c142c0302d508000585010780d2206210581d82003010310101900020740406c14a5010a40480303100c400540c0080600094006900440000c201c0302c009041e560100e40090710b10a5034236150400451050700b110034054201140e40400503041c04a52100c580060040c00244019403421140e8a00c0354a480018a064215040005030030000790b00c002e03200a029003c190200100c0740781c10b6400074403001c4080315503801c14581540102d03013544081141032041e0b0300421 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 555631789 1250 555630539 555630541
    0x30912091305190501090603021f080c160b07030507081003050c0607020a030c08031e0f090103020c0a0510061806081e191b0602010507140f0403020d0503030702071d 73
    0x50030070241500804080c1c60300780000e80d02030070301d600d03210700390180c0840f0350006801811803050106c91039001b5050190501141424800d0a41c8004000c0e44142c40303039000c0d0b8548408840403000c40060380402807500c450341040069a07071741644404c1c0303d86065034840d000c9d525022442011a1030741e000c081c00d25005483d601201d4240507005100d210700c003419807c5500d950b038448081d04849030300320540b41d07000084c041d4604190200c820720541d0b00740c1c031120314149003d0401001c034030130768070407034141074000c01c0c03400350b1541c14080200480c0d0814162403003c2c0740c0e0408c0000903c6030740941e441940f0034191260075000d01d489082c00f0b544a100090850314007808040d100d15900f144210b070b00741b181d201c125402030624807441550f079100c0d0500c0704040c2000762024444000c0da0b0010011a8544010050f0256000e100c0100c03814110341c1e400c0d521030311095240c0d00d074403a0ba00065040384010303401070104800000210310480d115400c0c3d81100340c9501424a007841141c1c0702d5400190410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 555633039 1250 555631789 555631819
    0x120201020a200d03182f0102031303021309050318010906020d020c0405040c0515030601023a050c120409150308220317030411010203040602030f16051203091209 71
    0x30b0b000c81406175502c83c0c0c10010341160350301c1ca407103000300c000c40560f1880e8040c030303010401a00f04c00e05c1c0f4102c0c10900107541407800b440c03d00389001c503a900c4043e101e21464202e5440710100c1e0ba0024289030f0700841907a1340c03680e0300000486860ba034510b00d40d000407450380001814a1002c1208081006981d01901c0b42c20781e140c003003102514020f08140c8070b800c000031001845a850900c0000016602c100f490303181e10b0404006410000c200e040030300c2500c101103107031040e0000c141503007080f0012003619130480320481d0b400311080d0007042281c016602c076401d8844046800e6001610450352080c005100b4408100540240500c9604c00107101010a1001d002d00c0d04640141c24090301c110405507526a645c0d0711010800ca045c10f5460080080010521044c00810740504c9080f41c420700065203070502e020300080d82c1b07104a0714809038504000c02c2840b8600128840c50704d1164028085940311000309441c0e047d264420385044105108003002c4d10010840c00d0240e515805e002449120401414 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 555634289 1250 555633039 555633041
    0x32306032104091a09091608011a0d03021c0903050f01020903060c18060f04180b03120a03060e09010518010b2d090901050601110109150903020307120201020a200d03 73
    0x80d55142d00181c4944e511000d043d203c0b40300c2107208220340c0d8010405040184921a604030305500044181d03410115002c00d80420030100143c2c0d42d01c1a0340d0808110000c3c14100e0906014914800c101c001040440f20300702c4d400b080c0507013074a01030000e403400107903070420160803481200c1003160941c00000020f012100704201410302a03105443c400c030103409460004a0b41d9102c0090b01c00c0401011800748000c8140c07404401030003400d0300c4208520050078000a98514001140071007240c000241164a20b100381c11000080081000101890800d4541d1a01a010403160803103080d802441450700040140109050ad1801a00505e00c04558241107c0381e16024111551030089000012000d03846440040b4801d1a51400011310382c140300c0001004d2101c115030030b4102d130781000381210211380303a001608441c4000040000300101a07260907070450003007400c041c2050404041c3e821400341c0640040c10025160368580100324001e152501c02130303100600010036031341701e41504e260290003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 555635539 1250 555634289 555634301
    0x1021608060105060702060c0607020714010f020c09060625060b152d1306080a09020f0409052e2315060c030406050c15040b040f020103230603210409 66
    0x11308010310f0301c0d564500551401c49c090b02c4030030059010003020000c5501c207a02c0b0024850003440c200d100203643c1c410081d03461512004552141092002103205680c0b114101c402005100c1140c0102e031801e1005014502c1e0241c105885160600705c84e00c145203811641e8041128082081d0781c00c0814450502d40b0660b10706400c201c011984100c1086588140300192510711000c160011100382458001030072000b0162441d00e40303a086c0444000141c0d0381c038200c000c0100040c0c0b00040d8030000d50900e03601d44040302002d60071000821260181840d06040e6030390101c0b195080c1481945141c0f411400c80601091824003400500c2002c601e5018203011170010400d0014820341c01c0208071500d0900b075511076030003035010580008242d500c0f000c06104e00b070030207500408080900d00d4503844005800e900108020960045d40d240241168003035402400d00d00f01c01e00c015400447d1881405078000c030141c40042c8284120007640500e80300907541c1c10000c1020850305420640f900c4030280150072 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 555636789 1250 555635539 555635543
    0xc060d09080d050103111201020f04031506050901030f0c080a02100305060103090206030a020a02062406030a150f0306051303021c020a08070b012904141f0905010216080601050607 79
    0x1810804201d0b040d40901400e4084e501a0024603982120041000001900c1c00c1400c541030340140580b040350001107086c2c40c1200d801c81165104480c03d012400300800c01500002ea02100c43e800200910600c41081c2d1138180c800d0040c2c1c40d0b0726440d4510940d9407200300c0002076100c102c1c0817005400d140321b5044960403500c1810081448800e650000c2c0f43c1d5041200e19070450303580415000020f550410a450b0014424540200042c3c2c42c0c2d81d02640c5060f0500d0102e008001c00404100b80c0c5460f9807180b4151518100182c0e1220b40760303a80e108030382c0d4040c80151005410600800c0140304e50031892411103925400805448101420b138445c042e000c00c840c101035005a40d000c0d0b001c01c00841c020301480d48102820200c0d58109000c078044427610b4850320080072189011201d41d1100c00e000c840981e40c052003200201c6614400046000481c406c50f001071502ca840b4044055400041d400b069920036001d483e00401c003118449090b141c2c0c2d105040c443d03400400100981c1c101400140901c2d8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 555638039 1250 555636789 555636803
    0x30509040b04050108060604140c0f072f010909050f061e0612181c0302090d05011e053301181d0f01140103110d1503060e0c060d09 58
    0x881c240010301150400da1003208a03800c5101001010f140c90b1043c010f00344118080d801041c144541c0072052400761103105014a040000c1d0030003400014104c80c80c000c1c2040312941c009060711852000b0003001400740d20301095100310041782c065186d0191718410b4046906142d1150346910800809000e4100d41c8062142450342a2505071107841c0101303900500b4200707038016410305101c204a8044c84c020b01c0c202640042d6180c104806600701ca07202462041d01c1c01503101d4404c00d0000c1c50b41c0540f0800100603610300f25000c0e450007243c440c2d044500070719400412080e0780d0141c0139039600011110802d0480070314046102440981c11840440c54010f141403000121809482d008506954014100107031450341550030504000121641c003000c941100c00e07555142004504020b10501802814542c8500e240c0072403442c0e58095800301011403405021b040f0000000d42c0c0840000d01068680504203940740802c603030002003076910301002804661902680d000c118008120040c0200d03100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 555639289 1250 555638039 555638051
    0x30402040c05040f0b04080709020f07110a1206050f0703020406090306090614011d011a07060b1306060906021e0d0503070c0b0a0509010b0d0b0106180b04061812080703050904 77
    0x214621303281e808090500308541c0e9a81d2414050102d1419a4503403150a85078010050703104584c682405641c045d9a214080310b070b411541c1800240c2c0c2a81507048540e0100c1c000320b2103018010142c04ca0307401144130b050000703e0b684402400320164402c0b4050b0304045a2454010070000d10281c1c0b000c800d5170300950700000d01000d1360702002c2c5440e17002c3c1c2c00720540044040c044000b0702010b81c1c1040c010704945002c084030300c42c001c0070016640644c00014010680c6c1e595900b005450310b9400790002c4680070b0b0301b0001d150712204050944082c6009100045c452826440500c0d00f003d0205048103800e040100110b480880341110f2940c40100100200081e424800c1d002a0121400b1409426035441c04140b03031611800040c00c6408500300d0a10450b040c00c0c1e0200400c11101c1241d05441d501e1030201c0c1c52025591a118901c40707a640100c0065a0000e400100160301c280c1c521040c1606010f03445000c0d9a45400c410116409680903102d080304005050010b40210b00528003200040d00101e82 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 555640539 1250 555639289 555639299
    0x71701020c03030702010e151e0613050c19260c04030f050607080a020313110103150306150501090305100f0b030d0f110f1207050f0d2c06030402040c0504 68
    0x11a0400d130b40307000c050b0391207030000c00c03a01d035042c0280d0f014000315200301c0d4114541020080100c60070314180050590f01140402c0260301d50f03190f1f100d0101c010010601650070418505c0c0516445560382440b00400141c1c010301c0c1ca031141c1c1494940700c07030580c0021480c10021011000c0164040c04640049004006c0080081d00d80c506210090340948080c1000340740141c40602040c00040c4a11441c902c108108031502881d07147c804840358112a010040694201c0140c0052007000e03d0340d1406c0900a500004002c0070b50041c0c0301c0c12002c80c02c01c0031102d640f20010f41d50078445000080090b04003001e140c00c68203003a8803044c90314241c45d0b80410000c0008012030706015850301c0000009130750b5910380b1031300742d080710b503e0182c00c408400411564030504e1036551600245100c0b15104c1300c0c0014200144202041500108000340041d94004030052402510030100c41012140c40b84d5610070005040c440d80007041d81d00d0b04050b0070146555207540c01c0000030708400701140c4c01d200c818080400c0e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 555641789 1250 555640539 555640543
    0x12919030b0904030822021f180b090f030a080d09020105070b07021c09061b150c1110050136060807031103030307051c020f0f180f03071701020c 64
    0x3000302c4c00390b01c8041850424009289985155041102c0303034820496034000140c542c04500800128181018a03680541d0301d0200c80c0051100b8003600300c001c03018000724002070607400419240d03400f114080004258041410f840b03842c1c10401410068090000e0910b810840c0c0281045c6441490803e140c5403503640c0f400075150007582c0020040e804001d407001030b950f8500441880d540c2c54280140c0b450310f0900020301652880c4a12681c40e4094464001081049120300040004034501400351132004030006021002e07914800c0c05603c101131042c10014218030445050307502034010b890042d0b040d003080103035125420200d0f5610303400140d0503804444041c0710398006420000041c00a85156003400c80c010080c40c16164400d400410900800c250080c045072203110310040c04040c42e504103014040280103000c10001c013500001880b0705400505c0700180010f261014000c2e4500c6200000d0002d4505480000e68040c0c5c08a41c0500903d00d0380f042000041c903144d4005803511600456a42c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 555643039 1250 555641789 555641791
    0x1805010801031e0206190305060a23040f02070503030702060c120609090c04151401091401030b030a1e140d0903170d0e0c010917030a030218040212012919030b09 71
    0x174086c521011500d0000992502a01e034101c0c0e4100c88003c0501c0c24400b01c25292a09841c0308040c001080011006036101d60b044064006e180355030454580c401c509016880b07500454281006004210000e01000080b8003035440c030441810120425903542030074084200006054000e07903100740349500d202555240900d541007050140035003001460805c04d030110714440221a4148a0b07800ba041c0140360344c00b40004162002440c01082052206020034109250240c003e0301c2404020075081c0303000903150905502c18030039440ca40c0540300d2510b00301c2d1a0340e01c0004003400101c040c641003002c10709100b1f903400d06400305010381d0700e010008400326040714040c01e855220f503003081000d42d8107580c1180e40c20000700b190307440c4c0385004820b20084648911480110702d080c103a011903203c6083c015407400f41c0f03c90202400455503489050b040101042c2c00744145031312000c5031041000403c0c0c0c414050006d8090360426241840c0c4069590400141d8517801c1c030003016070fa18421942951885112 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 555644289 1250 555643039 555643057
    0x2041809030306080f0303040209060a051503160c1a150402070309090c0e010f14040b0318010c030b0a0b0d0e1c030c211508010e0304061805010801031e0206 69
    0x40c0c4200514019054440303a5004e50340603086007054109440000c003c580e4881d504890308265555250001150300389150803032138006010303116400b0701c4111540198003a4905501980144a446a0880d16031124410040c81440a019240443c810030301589400940460b4004085003504002c1022600400c03021340025003804820401481c00784103d20050b130403071402150505100f0004ae082046414180c800c00c02e5400e101e9a0380d00f0b10005440107010500b031035550701c0c00c0c2061002d14008100464590651030f01d200000b025009205e060142d04000d0908100b0502e418641c03002034110145400c003981d1188481d8070b5004c01440f07940780b018020025800c007489900c1c8010300311080d0786403640034840c050703a001a5403000b4010721540500030b00000701c0c8921016130a131b00408580da00401181d030030305071450244080070000e0802d903130b0140d0340c428207034044400740790f8514403d00c200303404120780c20014404121400c150849039641081e05074090406036000c55020340c00400340e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 555645539 1250 555644289 555644291
    0x5030f0a020f0a05030705121603230114060105090a1a0703081008030301050607060e120406020d08010b0a2a0308040209150f101b0615081204050d0303020418 70
    0x4a04602c0c02241d1003001c500c0076a00d061005040201280e9201c00741d00400f4481d0302e060200c0c07074441904000040341d582c004506c90000720b60b01d10780402840754020100c071001c265030380240995201445410b000e1a1480b0003d08140c441d0001500d81303503c40e42e00c03103800012400010545101820424800013a0304c00f6880d950300e49410700408492014200b8000a480c0070010480e200700003040d0790642d07004a605640c2c805d03032807a000000b480750000000d0140100515a0410b41c02c14001c2c1080301c400340c00340c0d03814560fa03e00072140e07100c0902411103d054144001407041d407184241201d000071041d0540004025200910005210000200c0015034110204000c600f040500300340c201c05128140d445241f04c0d00001040305410300c2c002d6014185400e07038200c026114200d5450b402c102042803000c1c03d01c5506106010300f0309106190340300e8400c1c10000031090800140c1c01500000a4581070501c0d08000c10001101030080c002e42c10580c01344030106418001c00c041820f21280114 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 555646789 1250 555645539 555645553
    0x70e19090c050306130c180e0d172d0702030c19030e0406080307031409100804050f060402010203220f060e0f010320030a0e0a0506010602060f0601050409020a0905030f 74
    0x82010304c1c00900034180c00350111403a25404c00580c2840099084d0343c1d48007086c041000b0b2400f0704400502075455555034900c6540c4020860780c2c0c12400728015800115444155a81c6141c41001017032280c0084640001810350160007002a0750360b00c40c0c11000501c1038070318286280703038014901071a041030500301e40740020403c407c00d41c00003070700c000b1003800b81c80030721090386005103c580341d0183c2c0c81c1c0a014070143c60920f9445010400440c0c051680041c0407030f0040c6404100180484d104a600f1a8140720722114240000030004400307204581c168001e42c50004100342081e07029030355104008069841640109821813112a8040600a0f680c0c0348085a464201080222456004454141803401072006c90740030f28138074a440071402c08454280d981d107418440d0300040c000400103c0650140300c1e034000c200940807480a040361125400c5034902d89513544602621003054401e28003090003007104010602d0140c020f040340c9156402c05038101782e5180d02213424203115180c050310a4001030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 555648039 1250 555646789 555646799
    0x8060d0206031b04032003012703030e0102030109021305030601050d0311010603060c0e0321030a090311010216050d050f0a12090539030c090603210a030506060903070e19090c 77
    0x11b5083d1010000300d00911140c2240007102e408012841640030b060f014020f4901305160194000d070120b045950001c56580d80c0d6100d170030000b500440041891926146400282440d001a0751816141c00600428200300d850b641500c903a9000510300c2d000795258940000451120711800c0403020b150786843c2e403140c28650070103040400301905c807910301c000c0320482c207110341c8581c0903a85d010140d0b000c00940f448250505803411007052030030001542c00007800c0036461070020741c26a03860f40f04508841c0761401424080d5000c0c081d80807915003903c0c05010720003d40d407082ca046400c40c00c080340001101255915000c1c140400000100c45601801d003244480f60356038581848030410200340c0c0701c2801e407030302d00107510341c50b00b90f03c41c83c03041c11304c503010840640c2d05200c25121702289410002c440010000c5480c03440e00110601d03004603242a0000d00c117814000c048031000c031001005407101e0341c20146003800c00e0a014000d0520400c1c1c103940744078031144d14801d4011303440c05103400b82c507064501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 555649289 1250 555648039 555648083
    0x16060608010218010c0c06080612030f040302150c0d050d06030803041a07021501030b09011104090b01090b040e040213110d09051603020306070f03020f0a0e010f08060d0206031b0403 80
    0x5640c1d41d04002110341c050006c40c0c001c0422034195011403501113150703142c0b44001045004c03141039840c1036000c00600b505100c00c5501c01030048910949203000f40d1110082c0750280c1c1e0040002d80680d5401041001200302d200340700804e02742c40c0007140091590740703d8403029000c0d04100d40884081e17000d4801d88940260f03102016034880c00038030041698495034102082481c4040c407004040c0c1003000c01141001c04207401030600c1843c40c0e1b0f4a651255520b040600141c02c1050b00107001c1443c088011a0300b0601c1c1080364140c42410014030074944899090001000342c000300e0b00c40190380e500110114081280c02031922100094012654500e503041039400c003040707000d1800c0305042000c0200016100810341940c449241e0400300ca0600b800c0e00c003500a0710501d5150703214610005032511030260442c1d09010144400e03610461201d01540042d10700d0030068402135030141c1121040001031402c0001142e0103032181c00c084850a440300c98403141a001a00201c800e0200701d178600246900f8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 555650539 1250 555649289 555649327
    0x40c0b0f030a0b1207090b040b091009060e241212070c050306010303210615050d18080906093d030216021e09090714040e07050402160606080102 64
    0x1c1120304081110003131000f583c1e45e012610554846a03116440f80c982036685070b009144e020b5000e00709141500d040f84240d00704206500584108030319005020a40d20401050540300750a4000458078000380750540c1011a14805203090b03201d030400308510002e034000d0050507100c0b404802003a866041a1400b0390a8100940000c0c2c000e601c00300040020940c409d000c00c100034482c00d90561501c0e682c0c540d400c054038482d04444980c4000500c8004030070f41c400300610b885135001c0d00401118840051440741c80c000703204060010a82807004c1561850a4001002903600042190170054420b00c0b541211450340004214040d140034041203044035070444800440d265890214607010301801525a040c0b40d580002c0d024030301e980c10507240810004440030f42c10070002c0201c46607140c00b841d50ae0f5100c0e0680555142000c080078041520304060141f50b5100c1a4200604501e034142810701000750041d5203801c04180d0420040004901284200409800342d800003590340c102001004550b032031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 555651789 1250 555650539 555650561
    0x3040807090216030e12031c0e0c0916020309030f01020a03050f010e040f0804120c0503070506120c030a1811040b012618151501020a05100203040c0b0f030a 69
    0x2c0100b200c85522004404400c050607071505003e0441c90902000c50004600340c501500c01d4803001692016204c071088503240040701d100028031040c880c803d410f60311100c803001d84603000304846021840c0c24465125481da40c00c810f00c100c90919041d600042d2034001120206c00269500003014040940c2c9030007000d903c2603040c1c01c80b55545d490110060881d000040015110404580c207800400c01341c04112001424400444007210b5480d0410360880c160300c0c803540b8824410500d000501e41441402d8403e04080030b0a402c1e01ca60762201e501c00740351b02c0141043e600f02d40d101184182d1035100000071207480c2c040c284a421404021060000b21003140c0b0109040c014420032a80f102c841e48410348410384400800c080c615140c0924010b02c41d2022074200c0300600488001605100f26901800c0c403e12410401d602d02005d940c0059844a0300c100c4054003c0c0c01020b012916801180c0042da00a4882c09124a0081d03885100c0100b540004090302c0c500344c0300000344210000c1900a2402c160 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 555653039 1250 555651789 555651791
    0x209010906080303041b090207032118110f15031605090a09091112010c0201110702030705120c18061011061605090d030e01020d1106010e0916080304080709 69
    0x1e07080c0320281e640c901008100401481507a40001004450400b030ba41c000c03c2003860554440445140141c5122100105001030080b038524815000d011405000a00d21111000058603945038a40c280914801030b02a50844e42402c5030200340d45a2643d07040c040410303200d0154a03810101c4215102108407c000c004000c4244200304242e030b40c4180120440c0c202a90004040800f4602801a40041d988031a84000710180c9403113100419080040c21100c02c3e0300801c0a0003080c030704001140035442d00650542c0c0065414400d81c00e003580c43c9002c00e2003100440c2e50200450001a6800c440104110440080c41c010300c0503604041d20000300180316400c002010500307a080302940c0340e00041100038803140d0f0b0b0620301c00082c0100c00303c510108000d440202200c4039801c014144500d4140450300522406c404030380984d02c2480c0c2e42c40c1d4200c8141c00303000c450346031491402d28000050181c4c5404d0240602c00c0d102035011450b0341e00200075000c09103480700d20780740b006420034090ba13110300592 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 555654289 1250 555653039 555653051
    0x90108010c05040b1b011109030106090501231c0309030605090a03020d0806011110021e030c04030f080904020c0609060c0a0921020a14090a06030f0f021c030503010302090109 77
    0x2042d044400d55060f21030000c6856120f40c1c40038800c4084100d00c1107011129443c04003802540003c0c0401890300240c1540244560f55551b2a030000b190b10922858118002c901060001381c044803951302e000f8134000748503c0c0301005005e003040034402d81c08030031404500c01c148100204020b5004481d841717008080034207441255500d004e505c13001808691001c00c070729840041c905a020b03025042c031442c1c01a08850b0409012004000254424122504c000f985590000005102c41003101d00c2040c0441103582001c0c6180d80700e007640b040041040301c4032803040c880000799880300d1019140d0075000304000d10441c10002c440a04054000d0107580d00c8440030015980d0290b0801e101c0000c94418501c0390346e680c0b904000b0780500c2101c0e503c000b5806126450000f039040c3c140007003c4051803046554030000e8683c080444c0480713286110052090014804031004121980041640180041c1c01140c1d24061104c0486031400c4800701140441c2c4084010b1065007000c038601400340c5030101c420082 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 555655539 1250 555654289 555654311
    0xf01031101110322080a0c0f080712080904020d05150a06050f18030a050d110c01090f062607020a030810120f030c051204051806100c051c080609010801 67
    0x1607116282090f401d001309000603081c0400d00201c0400200011025104007000c2445c24510a1f03841c0e10680217060b84200e004114004007098220489400b2503d450b50041565200c1e4403079003002012030340c415800d0200403240102030040b02d100c0c5011800c503003540e00c0c545040003450386564126108010080c44001040b88080c012203040d2504000a0802c03488190002031800c2c4542c1d9009090f4040c1c59401c50034190000e0048034000c00034829502c902a541d0011034141c0035030300c40c945411801810030010607019840c0002c03402c00c4c0c8904985000743c0010721000c0c2000c142c41c1440142e00c944115428541c2c402d410070741040c031024118851030314100000e4078001c06c03114041c014030500340b41ca00405010b51600300701c49500000b50b030100441904100256001803080700c0c090b520b648550720390900789608440c07040c100206844d102c629105812035004c0c0900320122980d01c20b4102d64560140750b4042041841c3c1141d49241e42840c0520034896407000680c020071160b030410000400c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 555656789 1250 555655539 555655543
    0x6042a03110d050c1507031d0303030703020a1b0b071706060318250e0601030c120c020106030206131d070503040f030c1a041403180f12060f0103110111 67
    0x44001c4500c01802c2909081c002d00f000141c0c1d107619400303403c4840c0c84520080c2c2e4409020014041d1301c0752076100030240850f0f0884036450b0101c5506800400008224038025070140101703404520b4034025203c0b016a50321801d21101605031881c100540030008582d0388024600c00d05d6030305c09c050070654141070f00420100d02010f4114040d03200044080020b21004105080d170300d0003000400039000c1c01ca4403800e03442181d00d01641d2059100200010659400b9001d42d1101c0422540c80006109030900810010044800301808654a900000000d07954210103800380914220b0b89551741481d00040004030058901001080700c0c05104210700c690f00001a030b60322a81001c4494007000303152404640781c2042c0d400042486107101820101c905800d042c02c0d100d03074458070324040850203029805139640250500d20600101d1030b07030b80c4289407c06104003000303004054a20428000b0783c50300355043c40c50483e1241c49000308800100144800742507000c0c42c0c1c10080c2030000301001c801c0c0d80d8079 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 555658039 1250 555656789 555656813
    0x7080304121b090e0706031103040303110c030706140907060903080702040213030501020c010e0705030c0111030c12030a0b040504030c060e1606031401080d080f090f06042a03 77
    0x2188140340300c0551414000c07030351040c0014a20b00103405038129202c00000000384910016104648148003012401500070720a55180c0580700d010b60f070444c4e40d2a41c0440183c52101c84030142d0a0742408141a800020400f421006126210200304180c80b60080b0050950041060080e0747c000c1408128175500018184143c1e90010f460300d80d42c5100e4004500684900310349400903c05800000050160640c0a40056490072000f80865948600b1465440609000d95581a003020070b170314000b507000c1c1034065244140607098a05003112601242e05186503041c90000e0520000100140c500309445003030415041180c04000c4c6041548005040d1441e0100080a06a80e5804c000440100304000d0703516420f10030300311140c140c03540401000f50001e0100340050411400022036801004910b00d50f14443c155280340280d50f0b41d07040140d030094064030034042e0740540034035600c01203814070181d44200d0285280f10035400c04c8240d4a982881d01c4003000c10b00e1002d000c01840050107143d4a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 555659289 1250 555658039 555658049
    0x20040f0903081b1218150106120b06340b0702070b19080403020a0c140a0830040314072c0a0f060e0f0f09071a210a060305010b0307080304 61
    0x700710b0381d070145c1126490045001801c0d044c440c0241d2501d00307201c0c030320249040e1103450b580c4450b464402c0041c030058400d801041c9512450601264154130310b81100d000d50101090114036483c1040102c405101c3c00441c01518040711140401408030340403c0000c00510003c1c000390314100d245450744200040d00a9043c0070005244086000e042c4200035018203642c010005c01c07a45943c41407030742070041048407040e0180c40600000039100e0400306152007440700302241c01c11006581d007000031a40400c04682c102c01c4006010100102d101140740b1440c150748007008010303842c1060603041c01c40c224444180c0840a4020310101d04a046402840d04001c0030788012508010304107240c03000c0d200c6a00001c072010390348010011643e8030b01003214001d0086580c0307900c19480b00c40c546500c0d50102e0017030010b07486c403000c02015800010001814103800c042104200302103088000f180658007540c044d510941c5400051051010030700c64020388900803802840c03814a00b4a0042d12409140b00f4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 555660539 1250 555659289 555659317
    0x70f0b3403150509150f030106080a06090f1502090102010b0d12080a0f020a0c111c17040909030201020904060e10030803100b30010302010c20040f0903081b 69
    0x44200010142c03440940500030080c02c200003440c1c1010000c003034206072080c041c03080460b03443e0408682418890002550000c1020f4400d0540356254500030f0305504100703d40a60300180c110b008076000c41e99403180c9001424001d6901c181140c002803e546440d030040d48a42d800326000d600240b00400c40700d229400c0e5007028001940e511845000911106414101280c00012148542584000394800322807046480e0102c80c0b21100510064104c00580b105004000c1103076000401c8803089080c19400044d0700c0c0600d4203031604200001d43e8540d9000b100941e40126640b8418581809050064102045810900c3c03600a078450b0410250307100241844a0000204101d005446e03000805030441ca488181e8403107100c0e08131020800e64022801c60059000900b5144034020515036040381d805940d901d41150141d16802d0140240c115091a44401000c40708142d440307030300034045502051500003030010690b040140802c1c1c00107041400417441500d08045041c0607a0507a043c010340148 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 555661789 1250 555660539 555660551
    0x11806080618100807090501150c05010905150f33060403020405250302090d02010e011701091d0303060d030305040f080d061d10140303070f0b3403 65
    0x2080c01044840c158120062229041044624490b001c0c50700b104e4041040315400c5545038644403c0380c1007030051929855601c460410b809108d4051050701500410001400102070707503c980c906048220380c0001c1001c80d2007041161411000181e50150741c0d00c0b207141c0700c82d1800c05190100300840d4444e0132888a02030540a4644660040c3c0f8042c0d603001e4002c0000f41004082813080301c10900560314850a4090707107e4210313220b4000e844140703102508004c80080d0039401940c20340501017800381040701210401c2c4101d13401001d21402030a95250010703128031003800c0111406445180007800741d0080080c1b110544482d076095543d10340501e00016140c846292407810060070f0f2a002c2c001003400b185c0320003100c0c2c041d80480c0482d84240700049102c2c28001c145070392021700302c1d4000d03403252103403008010034440740100c4040400c008003a00d240501650320403a80303510544090364024012000c00400d0136003030341e1190340d00c14110050940b010100f11019640d54801e0f0f00b200c20583c07a05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 555663039 1250 555661789 555661801
    0x16030b010903230f030d110403031b03121404020301060f06020705130e0d0e090109050402030604033204050a090501180c0c0602030702060a0605060f2710081501180608 74
    0x1242c501005511094a08890706000d9285d50f0350002c1d580450160b117000c40701164044100220340484e83c0c5516403080043d000c41c80e10860021000f000c4e000d0100752200e0b00310700c03a820300c2860403072060f0b00403440003802d20303005050071a12107410040006c511000140301e60307174001941c002181c90855070b111100c49124010400783c47c00795451092031140c0010400700030382090310307060213160664040c1a581c0c0c0c0c45107000d00ba180107036006501900b01038041703030110744210640586003044400507680382400c441e427450507412944000b541400c01180a00c41898000b00610041c40300b5081404154181708000b0b02c0e45403030340407400c946035541480c14de0a5000307503000c0803001c2d00300000b15180d203001103000c0e40b0703008125030038900780385000808a07242c80e003081a10408441c1e002864104236031240050002c203a90b0800d003040d1001400b403024a580d13415000c17200e031744c2e40750759030650f030b040c40e034258840b26070050f102d20306010b6001034517015200600d481c207007110524900700056803101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 555664289 1250 555663039 555663083
    0xa1a090907030c0b070318031515030c0f0513020327010b04020301030f0213060b0913090803091c03090314160b013816021302030702010516030b010903 67
    0x281c2c001031158206503400101810b4100180107500d0003522000481c0701240036180b00f8140a001c02851821284000c481c21126a0300c91180042001190903100b40c4946503102c0d035074065400142004140035080c07125003024144101100d4096078190308600b0280c02c8004c5204918241d2141c040d00c8080060703680c0425041200a001c02610865070b80d42c4900304103204210500003a400b40781d40d0340046801008900c100f008031071340140000e00701500310382049500d0301001d9154041316100e144600c0820f594000442c007807031640c13000b00801d946c5400c02501691f12600c9800906150411040c0803036080611000211001d10215944d0b04180c2c01c4030301c4420205002070f16811700e0100109001e41e2034108401c844c000c21034810300c104c8a03e07071400c000b03407008442c1c0f120392581800000302c03c0d180c0b00c80d002c0030688000c04007010002c860800701c04076001290f0342c90040c2e44890900145d13940600040f98150750915040c00010720010028210301c0a52000400103800c84001015000203 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 555665539 1250 555664289 555664303
    0x10c0c0f030c02030a2103110711060d0609050108010c090f18020703050417070302010905040b0a140f03031314150712030209120105061e03100903030b0603070f080a1a0909 76
    0x44424250a1440000462a150010b4062950200c2d140c151701d08c000c503085d88280da2100350b104184c411a1a528000e00030980c00c901c01d413010b003c5d00c40d00c02150041141c02080d0103041102c000068844a091001300102c501da80003141c600d6200c207091144100210307003801107146008015a80c0d01291a0841d51481513038001814106045466000d81c8000700f94441101e0017640c0e80c003041034030340041008480201d5003581e4424410001009104408828442c0074140100401149014a40400c0c116449628440091181c424051160b060b052404000100f01030f00e071034918a800322030344626071099000240203038980d0303048021841d210341c044601042001d080d005c0c0401580d03004601078241511610b10550b07100a064840c10b5a508407180c050b00300900400ca00329040e5040700052000350000d50816450314080740281e100d110003940141c80396501d88904080c040c400400554000e000c290546041ca001e6a10182c50360050101181d0112441581e40e01c0c1d10000910b4889 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 555666789 1250 555665539 555665543
    0xa0804021804050c010206011502070512011506050c0d09061d040608030418200415020c04090812060306042f180627070309111809010c0c0f030c02030a 67
    0x1c080d00704420000045010f001e8048282c0032217180b80d0300d40081070201c0145012450060f4003404040150b480d040103650381d910114000003c25420564100040c1d5450b6040700e008505c2c0081d402100080401c1a0039100c0964600390010300c2c207118009003141c6400c0790700c070013400d9070b4082c42005903140e5029400902e05481180e03901e560b20031040354101c4090700100d00c92443c2110781444174a21129640000300c0d03840010b45414105a8108101c18810031424114441c4008401075911948640401e4600600c2d18544515040c21441c1d901d0700001d2445000f60401403d000024114040c50310007018144c4075005485000300380716000c2112045c60036403185881d0391017200980e4407100700340140000c0e51940710b0080b5040070060001c00c04807500e651444000e002030342d92842540f0013007030a0312898403003400031014800a1200000b112150042c0d0b0789020900101900911403095000e603c0d041095481001d030b00c0b1120740403030008024003801a84443c00c800c541d81403005500c01d036 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 555668039 1250 555666789 555666829
    0x30221040501050702010b18070804050708030403150506190306020c0a050a0c0801141003060f091202010c0207060e0609040203060d120e1009080c0409060b060a051309060501050a080402 82
    0x49024140780340a86010b0382c001015529091440c1030b0ba00b40020384803404000303111000c5882d1100541103481041c002c000b500c0a00500e2401b01e4040c03414001080154003411009544181c80001d403411503401400061081800e0400041c4580410054408130780d0004401611450441c0c01182081c02506d4010400d01030f10001030708014035008202d00f90362001d0001c2206480d1019681e28009060b100d1200c942c00d500c4007003000a80c150400e50b45080c0300500869240481c6d51080500300f581d101c1a000745c0d44900b110111641c1c10003200006140c1480d0140c0c242503003c0120303005200340c0a03003078080c07600000082c005e6124484a510000e0744407032140c0d0120f40f41e200044c2003c003107641e058400e48079014000b602c540714641100c1541c698002070144561060100002003005400407076206440707100306821540c50001070000c3c05110784135075035901c0c1c0c03210b20404c10b01c002d6040112124030b8450284a41c0e41e0000a80d451a510f0b402d002d4501d868500000300903200740e0600d1240b1b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 555669289 1250 555668039 555668041
    0x207090f051014130903030912110606041a040b1801080a03081f120512040602010f050a110306010507141614040b030d0e0402040e0f0126060601030221 67
    0xa0304041d030080384103203144000d0040003601c5241e00c0d2503054848003000d510440507034040c0c0080d505a40143c041a01c81e050001e154400c540e18654058900e10208000ca0a000040444841c0c00c1c464144e0060080703804002400640250011884403a00c015026070703611940240c0e2511101a4001c6d24503a0107050090b07585d4403c0560356800810b07208400003000407000c1800c0d0b107010b070701c00d9545443c00307003c0075529130a040c140b50b42044441002e8401d441004150300c0c81800003001040904016400491001c1c0030444680642d2009491164000d1820341c212501303850801c00e0701c0e0081c1d401d1038400d0340c0d61014108101c070000300588284150040b03840e552000b04039900f1420443d01000080169080794004200c100e03280103584a4141d08040e6140402e04d125a4a107042d00d5001000117080030340701c2d082c1e002294011206400b071510324600501441b04807032689503502000c0100005403003540c1400b5034407410007502c90b03414036401290082c08040c05401c2e1800308003072a2404122 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 555670539 1250 555669289 555669311
    0x90f0e070f081606200a0b1911031b0c10021809010e04020a03151e0c1b030e04150503060f0f130506040b04020307050a0e0604060b1c0c020709 63
    0x807218a501ca000c045124450318000052403064180e401c5400341e40350a101c51848001078201350144419a400314020041d010001500001e9954014100c254094009903500d1551a08640300d9903034001c96000248100a02c1400f400084d21040c0107105d03441e13032101e8801340114600000c0303502e41d1248500100b072500d1140180c400900394103100700c90102859076507582c1c100b03c5440035103020390050809801800802e040354088a40c103410100c0005404034076000074002c1982141801c1e401980f10505481c3c155440241c8000d00e50700312614400300301c01580c000c1e10900d00848418051501d4000d000c500c10081124440100405030554905190500241c800228115200408200c0190220b5400f000d01d140200c1481d502000800756a240ca496501c07400c440113100303d0b0325102d070500c0420580c2721002090700421507144070516a05110040000f568440d80007500300c0d2109214400d81c10510107007a09007503c4007400080c54000c0124202e00b070607025048442c0c400c2c100040d0900e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 555671789 1250 555670539 555670559
    0x60f0e040c0509061f021905150c031e07020a02150c06010807060905040510080106030507030314120c40090e030301050603100909030804050d02060709090f0e07 71
    0x80300e9032081d034001e58241e40b120100401d00c03100751452900f04a28103000f4090340c0d03910b0312003803101e40940121800342101d0645640d01c500c01100841d119003040603001c4900340c1300340030140c0003085020000d045182c05807500486040848054a191804102003048035000b806507010490700541410703200c017203a00000a281d0b111030300d41c0240e0310810740001000900420b91200341c514583d02c4240d07403460700d0108406801d014001103042580030000060706030b003d02c2280021031041c0e0103089103500d1801c000d0f1002c5096001454104010032601175030241543c82c2d554083e100c1103450303407550f00c19a03004145450000c0c0b50780ca01c40d80601e00502c2c0c10b803c0c50280310702510010801c00010748885841d026501174544440c0598010b00041c807051810101440e8008400300700e001000b83d0701d0800c00c1c1035440c00701055000c40d81200a01050000a00807e8000f02e568002801207003040788000741034070b44502c11464040d0365a40d001428806c182c00090030101c11740200c1e400d868454802c44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 555673039 1250 555671789 555671791
    0x190309021c0209090604080a050f04051903030912080306040f14040c17030c0d03200a091d1003060f0b0a1805180a021e04020d06180207170706060f0e 66
    0x42c3c0300b0404100001d01c05680081d0f494400c2e6400b6003c40d041ca070900301c0648158100020340700c034410040c0000b103880e40769452101030f000c0084c19a89482c602d182400351803030140307812403408200760004600210302d00030100c9030041c40a440006182c482c14603c40020402920501680c403040010b002c01c0c40300f4000c060341034400701c0d00808451140300c500c00e980c0348110390340c1a8031900b00a41c040c1a050296100c90703031002150780c5051616545e040c0f1981c0d40d07441740b0114400300e9044001440700c3c04118522510340e2050000c484c04c45d06001070302c000040101d100003400c0c3c0d80c898048045040d4250130001c013192000e40455202da884010700c040704403042014813401458900011030580445200e40440c11070390300175044900340b030340a00c0b000111081241d410102412054002078480344001d0141c0342e49d1490010b0b02500708481417122101e800071401c100c5006014032800300d50010480103400107444840c80d5560b920385070500242c080e40c1d0028004035403041e000120000340020311 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 555674289 1250 555673039 555673043
    0x150f12091a040b130201200f031b190f020f01050f0f09130203060a0308090114040801091203020903150a06320a0e0720010509030901020f030a05190309021c 69
    0xf09a5580342407201c0b80b040045500030b030004904041e4407036404940b501c4803c403c140c0034252215010801c002c0e919581c02502c0d10040c90504420322440c0c0780c000c2c411143c40709c00288403054020304d1a181c0503100964084040c3c0304d603c1005c170f900226801007040392280b00d0181180c40c0c98221500e01980c0135000310a64500139000455980890740d050305c202e900c1071900501080081d801c5440d403003050f80102c2c49a40c1480510302c444006180e120000e440141081301c0041405001071a01505900380ea420300402d02d401070280d00d0792664042001d005000f1015401075a50f691140d441c000740045da030121040c91581c82001408010612410500c900c10009920481c920b00043c0b002c1e042c95841000084442d2001241140f441081e290790304041c580145521014118400d6007117400995620a0b9603100107131503991542c047c0000360009030401c0113542040c0040d4000b070954404d241034000c0d058240c401301c9807928040e82c003401d000c540182145001d14202034100c500403d41081c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 555675539 1250 555674289 555674303
    0xd030902010e040209150c01020d02030115170f010501050705010b0a0834030f0521130e0c0a0e06190e0414130b1003080d020a0306150f12091a04 64
    0x180c0820b90400e4000c803a54000044d02a40c22446484039003d407a030448610300d40c0d41d540800890010206030b0001e1406044030300702e81d9101e5103078030034060100b0f0015034000d55543d115104111f8501c0d044868141141d40038240b040d5a90300394504980106458145603a004504000c0821805000224400c0030700e40e004030701422202d440303c0990039008100c010225070204120030310000743d0038002c41c180d451198007128103034141020a03104601d202c4002e6400319102185030a03d080c0500c0c01f040c0201030700d0004001d00e040c45003040800c0e06c207803c840818003420100e504141c0d21900120b90140c9841c4505400c00c4078005c00013800c0c640711080c0c1c94440d0f4185903142942c403000d41900c900504c0245a40320141203070741d5400410010040c140415140c1046002001c03807100c00040c084821003544c0180d450790f02c00d501a04603800e40d04007001d95101700d40c41410a80d0000c0040c0500c1415040007462028100442c0020b003015810041820703500d075019030001340b459030006010710712400b5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 555676789 1250 555675539 555675557
    0x402220b070803070c11130504110d020d080f0712050c07050604053001140603060901060305060c031f0602010c0905010201020a0c0b0a020f07050f0615060a1b050d03090201 76
    0x10806040c0c0510107000e4414a41080411001030141d0145010184112481096036202c00001000c00c03d081c000f802c40a42c0307890400040040307a1400034808030084a0b04842c07030140b50041a5400100b440061012100060b5203654092503c00d442c035160341300d000f0020b07036050b0f0301d00100290480d0310b07034800c54482e800c008221490544162416030708050201d415030082601c40000040361820040602840300354030500701503081c094440c03020310403d68001103003882c1c02898905100145a8151640b42120070700c001003000c01c07825040320011030110f40b02d0301e44d0710f4150350110484440e51180140e0010000700c81c1e0701074004540440180d03c68004a5075503100581c00d03441105207050000303654030503110005401080554104a0180c00142088030018000046502c469010f40d0b0300da01c00030318140f01e084104095640200c903448401c0084043e48003007201fa0103034602a4050100242500d90b99180d81646550a41d0b004411140c01001102d006802070050040c183c2c0000d255003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 555678039 1250 555676789 555676799
    0x2107030b01050a06082e270b1503180610150f0203040603110706090c17010207050d0c210f020c0913110112050a020316030c0806041505040222 63
    0x2d140f001107035981d448901c0d49995912140c8004003030411080c0c2034440e50510584d14a0b103030001c40014000310041106602070071103452500c04412080010114103081000d10360740c4660400c201a0442110072039103d441e1199016607a184805041d0b0081c4140001c01c200035003214002400c90314201e0403d111140005000c50b003196102c0c00a002503801000300f000028820360054400c8012030b04000c0c10040d46949001c10745140f04400c0d82c1c032040410003440a010b0032506158513110041c000c505e010001d946241d1a000d2112881041c0028074600e0320170300c0300400300070315224540e9904095a182841d0080e141e0400b000141c0014802c03400c2d00c2e0081e050012006024940010401c45004407543d11691240e0075501e54030b04000d00801007414036a9a802030ba402201d03003400258a900e030610400100313086c0305401008050070704142c002007640028005420450690300071802c07450350364070300c0ba4043e06c03075004c960080e10004034408440141d24003051082203e0004000045d034031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 555679289 1250 555678039 555678049
    0x3070c061b0c110301090602030a091103060118050406061d071e1202070813080304142b0302011803180e010602070b0a020c0a03060c02060609090703030305062107030b0105 76
    0x905002000c03910202ca07140c0030540005000410910050010860070216030751039040e03030010b0714840b15080d06c5030700080800103080948056030109800800c2650f02d015000c40380d0100180c881406135944074049014440f00b0b80005001d03000c00c07180380b1080003400400340401502120088002107050800d0b00d82292148a4140400c0080c2d03a1868140400011a0000e601c00300003213900c520200001c1c0464001161030900030940072002d151a249040001031520480c4100c4500c182d043c0e5200c1444206002e041407141c510038448030150100501d0280c0c01428440084285028030505110400d542300e131000310303010555440300000301d0740c46000ca41071032800e003c0c04d00960004c4034148801400308018140350301340c0c0d1046402c0303008030902244000450750400e03200300d034170344010a0105804000709508030009840350803072032600c2c40c81c007600c41d41b6a0000908244d1640042152a952038042c011804403d021440c20100380903070355a60340a603880304403004603d074400040c20f4600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 555680539 1250 555679289 555679331
    0x51c020d0e1605040b030c0103050901060e0103030503070201050c090d03030207170f1c0605100c03030603080f0a0206061009050d080904150e0c07020618061201080c121903200303070c06 82
    0x102038000c01f04114450010740203042c000704494199940d03900c0005151192400c200d000394081d80320103a0702d040982000303003036940040c98100c0c1850100996103854898030030703200c4000d41514005896884520f4441704e844016064120300b00c4000c207035070100d4485c0500604000205c05040314106000c07007492030a450061180c6540440d000d12203004031801020300c028a18802e1500080603601c0c6d9665050302d0300409000a01c2076008640c481101c1e404005080d08441c044a0b14659500803810081881d074141c050b07580101d0500c0b00d81e20411039240d00303a0718040001032007032007114090b206015200c0100d1007181000f00501020800c00e03440701e4203c5100c50740280040307103040307155120140b180e01c10801561700850200880c0c00400c40b50208103010b001c00001502d4030f02e20380801c00501450b6200440556000700b1050806191118028002140d06042c0400e150b110303078540c0c0f103009403113103a01c0f0715600000040155165204040c0620070788104010003062020240613800342e14 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 555681789 1250 555680539 555680561
    0x509010f03050f0a0504021507060f0c0c11270a14011505030f180a0f0605070f05070b06030705031e0706090b09011d03030403050a020a08010c051c020d0e160504 71
    0x7103180c0418200c0e804c0303410480e0b000d800078100d600d0740210055030240c1c59021000036103403580d4803069042d81e000c080c0503018103982e07940b42024856156440d00480b0101c41c02c007551013803d4400c0401c1600c0b50310031407058206c0700c10f001489a40391602568014184c29484611031003000d400100360360065800c981c80c0c2580302d03914682995a001106020b050300900751501e0620010103483e0b9050b01000038200d414444c40d00b1510140c3ca9203841d609a82c009800f00b400d01800080502091f035009007540c0c1c0380b541007800b180f03040d1110b1003c80e05180b03440d08070540501440c481c01215098001c01008a0208902240c0003196240d4048942d01014001d682c0380140c00c000441c0ca0b0740c4903920107441c501c16401a880101c02000002e45142e2090380b04031455001503442d88103518100090a00070044480240401d001000f030081042c410000060380c005088035035420300c180c8643c1958495049904100001100003c0047d40d603400794401000030b40c0d1702d40011030503050500507000c201d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 555683039 1250 555681789 555681811
    0xc030d020c210a1b030816050106090c0e21061305160b04050f040f0e01060611190b040f0213050108010f0c080a380111030406020712051c0509010f0305 67
    0x4280e81e1345031040107400c0409103d1054107908007001180d0035100901e035070b0040c03000d0841204060700e04242503608030340c03080610b10318002ca4889407a802036041e200c1080201c592001030388544101c640c183c0c0d0600f09054543c41a102006000400c10464050381030080f0110b4003c0c0d542c1800440d1204200e000f007000011041c0010807081c10701f50b210f5440302c40001d0003c0788091410b0780200460303515a00c020b0310350307455400400500c3d406c030390691003038261200504001c8240100c400030208802c2000ae000c0010100020184a02c441802100d20350051111241c0c0701303943e140902800c000c2c0070301001e0303500c3c0107640001d203070552040e4a000242d6403200c5425136942d51200009020140c010b800382c024050b10546441c001c111722210f158103440d0740c0940038050400040a1482520341e14040794000c1000388a4184c00248980c100c580c0c49a032043c0d00c00707051030041c0c2003101c038040b072809c0c030343c000300c41c88400542003801340c0352001c000c0c0c3e608086003071480310032070035540c0503100c501d046 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 555684289 1250 555683039 555683053
    0xa0302031b12070605070e03120d0b0a030803061005072f0102150408030c07290c0c0c130219020106080c011409040f0b030a0803040605010b070210030e0c030d020c21 73
    0x143e0150803007641b0107110701700040c1018110f00400d0a107000c04c0030a8116080c0003640801030704451280c8485500c0941b030b40c07804241550b907101110f100140040703105d50002c02462960354880d40840380c0181c0e00402d0703813a0050200ca8100b080321010040440c150041c042d50076825480011411041701c02000c10004507211600d54190b1907101900a14410300c00708407200125100d800c1800c500c02ca6105c00c0f40c3c0034014180740c3d824418020745580c4484100304a8421030404c0020313040b02004040302c60040200c0380c0060000248030b03406046140000d0440b0742c4200c00e030194007510031200184255200740380d00e00c004442d000413012101c1e0018100344901d00c994101030384400c00040618500041c183d10f4080000d14103508038204544030030000041004005490280c0d030b004003035910610342000c945030700055610090385620000c242c1d4601c420010280100070303a01c0c0c0e40e00050141c65490019180c000d445241000c90180202d00740c09083c00540030003a04100701e50300f00400351440c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 555685539 1250 555684289 555684293
    0xe10141206030f0a0f060c020109030512090c1230042706150906090b16060b0910080615010806010f030e030a080613140c0d0603050a0302031b1207 65
    0x315000150045030107100d183c401d41038000003040900d084038082e031094052048280307069015124500640411a4101402c11001a4215007500c40311003c805a01c0c0f41940c9514000d8542410b0099255004259101e03141c440040425503900350081c000c07284502c0f501d0311416101c0210941490741d041030007040104000c040c014070023007900d41c1004c1560740d05610002407009849294200444124170507000d21001600700c080b10780188214101003032560b283c080140305900504108800c00c060380069171041280c654088064404c00400200c40d508258441c0703402d220240c02100714501c14240410001c01c9024402481440140e40f0204150384807001110301d03648289080e8145a12521510740204c0d0900107040d4901081e43c85440501c0e1110030444e00900f401209014a4a466034060720f10894011050b0720020b041c600130340d00c0d024040090010405907001505070300070034141004140c0c0c040002c2101000020545c41011b4288030b085464428051142c0c0303540ca02044a000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 555686789 1250 555685539 555685567
    0x40c05060d11130e011401140f09100806150c100b12030403030c02130203040c30050703020103060f0e01090b0f030a0c0602100b0f1509030a030e1014 66
    0x1c8012129403000c60050070310040d442003500800b061081a489603a402c0c410400e9409005004104030480d43c03080c6c122013000a0446074030241c04400320b442c0000c00403003c42d501400c8030f0782548040d040c0800760805900040c45028241c403a10321a6142403841c44950600d241654541402c6e440503083e9540b0003007601c402018100d00454200ae44290074074003900041c4041c1000310b00a445011404e1254810030003d100f480022009440c81130040c030000c01e4001c072070b070010344440389a040d40c091050320422600b0110403400010300c0300052001d0f000c0140204411049a100b031303d0911455880320100c11800240703008404803410701c03400401c181d00c842d40007031110325400361650840040c800c1c0480d08240c2502000c2d00c03100211a001c12036941d0420403400d06c4074940310100b21414942001600d1130202c8284a4866280c0301e00c452600016001114444a80101220300c01e150610300504900500c51300c962040d264082403a021034012048580386102a0581c80c0c80c002c51011001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 555688039 1250 555686789 555686797
    0x7030b0f0607060920090705070f0f020a090903050c010c051c1503081206031606020a080c0f06012907030e04090606030c06020a0c08010e070608151302071505040c0506 74
    0x284103d601c6062200100e200451802e89441c50101c04401146616050004900019005d002048820001e040214005048046c1c0c0030ba80072a000c0d0103a450b9000045138110036410805060307280507801030400d600700c4c0091143c0c12040000303009214030440c0564079400b50121020f501c038000350f94040c81c1900340d8003000c40d40700a04e044980e00d584076144c0c10300b540c0143e003c10035403c6154051002c00d00e01080740a18502890404224290420700003d40700d481c0300c0740c02842c0d10804114142c5200c030600005880c0302c1c0020032581190307901c8188039440051050b00c1c800d5511500301d0120800e0040d030843e0403c80e0151500c2e20300ba20410700b03000c01485504000e9400541d540703000f000180158805c4402809968001c00880322603040202d01a12140c1c82413443e42e14100780e5020032100802c3c040b048540c40d0234040010342e10f40e1040300410900e01c1416612020500718201c3c0721141c1d80c040c245036070041040349283c41c04080b040045507020b44d80038101d51007240c001c101900d0500010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 555689289 1250 555688039 555688043
    0x19031a1807090203060924010f0c33050702030a0509031009030905040f0e1c050d0e0a150b030c0618060d0b0306060619050702010e0603070807020607030b0f0607 71
    0x4084619000c0035003420480d081d0000b0000d15000010f102151070584406a0440180c4030030101c003507030500f40948030a110b0b441c280c2c14000414112200140074241590101c4c2e0804022440c00300c51184c19080650f0052801e0480e101c0c0a0b15882400040c0c49228401e01c3d09400540ca050b01d03010080e201d640085c40c3d62981131141c0c260143c1c0110b854011405458440e445110482e0f04200400094501c140240c3c4c0e5960316010ba07220303008500290248511264182480c8902440101101d19205186030b9059240c00d120300e96100200004000c140c40c1e0048900701e5400c3c20b400b002c902510005441c00c0c1e07269005040c021094506040103042c0014800d07194140c0c20946808680341d41c00c02d454516445079150000ea17514102071180d941d009000711410381c5415000c0340c503002e0003113001880d5405c020001c5640e20031a40150000c40010ba00104441e44038a0000d07402005c243d02150081e00500441011070f0f0304d1130090107131100011f40100100c031950418014048660000780d01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 555690539 1250 555689289 555689311
    0x71d0403080a0b0f13060602060601020f060109050601050708040308071208010608071107080d021b0d0b1504110301030f0302010608120915040915030605010b070f080904200919031a 80
    0x1241241e0390b2803e05c002c1d602503d9101c00719900e40741c00d02c040d0800310020303c1c042c159005525064100403011500c0c50669032070580c00030303031038440f180126881d015408008150b04170018001c000e104410000d4030b081881480b001042c44080c580031150001c01303224800100c0c2c80d11b00420741d201e02450904511190580850350100d40e50358046150420380b5800b4400760f04145445103203546207026400310068161050f80107900070381d407402200e4000400e108150406000100c40d0380d5250740007400851075202c80a91296107a0a12007800b0280c2c0b00c040f07016619003000080c0e0404040b4484140318907548460381000c142c0024080e04899914800c15851404c1101103403405452260041112001c480310103041d06510303080c011600180c01624500e241400144001350700c84800e6400035901200c0709454903e82404940a0902440c51002c2c10380c40300c0c0e0f484441d240a401626405034200c50300d00f0742d403907140c4404c1e443c01c401c4d00000c0d04211090314078840c12005080d03070641190760300903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 555691789 1250 555690539 555690559
    0x2403030f030e030d0605090a05010602030a080a060e072601050105040522050103050703030f0504050603010b210103080c010c0509030c0f03071e062705040c120e071d0403080a0b 78
    0x2111500f103600c0f168204808540d2844280a44d00300a42859401500302c42d00300300c10f506048001e960380c0920600725042010071000503641000b127400140082c04041c6081c0510f00702160701500c41042c40d03110418480c42d1040d400c090412401300913040381c1040e100c1a10741410300c01803000e45852090302c440708140180381004100494800d0700e000314011300c041c0c150907095250003441d2031000c0c40031408102c010b110034002c984d156002c4034111450503080c1aa201000500810b940c28000c000c03292105100c000042031100d894002e2109003207250007000043c0803820b050b9030b140140e1001941540c00070044800c0c50030148002d5a0510b4000c085405a03591800f01001c1c0e400580042440b41c0c82601040055540008080c0c140c42c1400082031000c07101640001580460f07803181501c1241c0b200c00122416000c0e08459000d80c10002d02031040c0c14059035416541c1c07001380f150b04070043c0f1098034811501d007091603c600a903030555510405440e0300f101500035200180400d46d00001e202 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 555693039 1250 555691789 555691811
    0x3020c0307081e030103030801061209200307050a0311040e0c09190b0405040206030601180b0c0c0909010204050d0605060a1d0f0105090112030503090703060e0a062403030f03 77
    0x8081c041c16442219102e41ea10b0818441a0f00715844201c0c0100940041c0010700009400c038070004d056686519080b00060082c6d00b80a0140c00c180c00c010f4142c0c1c0040900303003900201804003d003619401e90440790342c5c0d50351f141401240c3d06148809400301c500148484a40c2c500b41d0052240000040103c8104a0310940010b0072440c0a5070482401156002c03c3e82c80c03013009004a000105084074100306914140c3c0100341580300046c00c1d00e0410a50415043c0204280344122000d000e851032440e886d000d50308407090340c07131940c07116051242d100c420024118010500884040e82d0f00075160100018282d0384607400b9003c05481c8a038041082c4202107645007a04541d484003185404842240b401c000e8616030b110107040c4c1060f8014070b0080c0040c008440c01a80c4810284e40c18680650380760303621082ca90504100e0f0300024542410902d10146411001640060b458010081000b41e82150200e59440e000700141d00404070340015400c0001c01d00520840001882504011a140040b4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 555694289 1250 555693039 555693043
    0xd2c0603070503070909060f140307083309030403030f11060408070209090d02030319060b070311070b03060109060f051c0507030b030a08160203100603230a0213050703020c 76
    0x100c41c01c500055000c8104401c1d141e002840c5002040118030400032241860305251030754048d030003061030b21601d54986d070595480401003034008008040a960500c0b40d00b0014075a425030046c1000c3d048000d40c06070560511140368030307034021304403035004500e410703e0350340d0545a000502d080b542c00d1201002031104440001d0106501c994890080595501c190703104021041d50003800b521416070044070f80c148269000001c4079045010544110490351210316002d003d011160004a0b20560128421082541000c0e0801d60034403d107064400d00e039244d440b5003801c0d010842d00780380001d038910000c004050040750751410840355490a1850b003040b185180840c5400c04030b42c44c2e4810342e14030400c0030f04d9600d031142040000c000c5002d09211005910303500c003e4002c07144400d103d1002582d9840855804215045070f40f584080309224040d900d0405425010040e164185c1070036078980840c4084001040150105500a21000179076642c840c0710801840000c0018042c035500308031045140d00c2c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 555695539 1250 555694289 555694291
    0x210605090106090f050f071101060503030c062a0327010e0a030e04140105060904180516061103031f090e03040801060504050103020319050c060c010b09010501020d2c0603 75
    0x35000465060301d840c15800480b0a0504211007030b42c5803205000480442207800c1c1d820603442c0c9031505000403041107180c01495194801d40d030612001880b5001020081162881008039144d0406249038509140401c100c0965502c80401c40070400038030183c03108140c1501103c40340002030058000d8040250031141c07034405121090740a02c05100405500050403803500c9001d0328180105032310b14011074400b400600505100b4030020501840c030b0b8586078040800d03a620002c00020b20a150700b04942c032000826800b01c0900c66070080814200c0c0202c06040d00214a44015855a92101c285080c42c0b245411402c4036a84c2840c800141140341d40501e802611111024640c2c582ca0711285d1421070324250312a90047d4101ba0040015035401700d07550b045110342013000552034196142c0319060409420f0080d030b000f54042200008140c2c158440141408203480d240c40c541d881d0001a40e503403011a0b8050001084842c03042405614070701c803001c2400300c8240320030105004400146403070b00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 555696789 1250 555695539 555695551
    0xc070605030c1608091912060b030c03160e0609060f0d060b121f0501030c05013b090702010b1c1703070201140705040b1818181005010f210605 63
    0x200200791404d1a00d40850107568450705861000400c0b4a4500c004000511598010b46019507a02805509da10b050240614502c40141650ba8104001388050741c800c1642c0038072521881040b0000e106030402039503160050320003c02ca000c09000120400c68001400c0008559441d11240c502c000c46e190784d03101d48003500c0e040c3d028203286008180c0004000401c140d00005043c2014010400300e9050803540040d21420b20341680c0c91f01c084607804240c480c444665194098485241089061005d480020720040480744095076440d840c0c1c0c102e080c0ca4005c800d055000e440b1901d0520300601e80000313070301c80d10f11640d4546240c80f80e0314004d0981e0b40003107548001503510303280204088450200c540e5400503640c1081d074142400c000b0f81c103405024010717801d5040e2002d0310040555940e5003000c003480d403025001041c803603d8441d284081028400359104082e10808003000b00c030022500071107042e12481ea20a1080f0b902c3e05084041b0340c1e04685124404080509404020603010300070240306103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 555698039 1250 555696789 555696803
    0x2a150c120c180a0b0f0a051b01020a0e010f080f1305060a02030601110316060b0a0816081002120f070302130915062604080904090b010e01050301020c070605030c16 72
    0x119040002801000b1101c01c40d520900000b401030007521510303000c0d2424042424544d64580070b13800f07002e568a00c1b59014080c05942601c5081d00039802c15001804208c410381d5800814040c500019500c1070002454000454409070005088000b084105603000e100c180400c00e90b100c95840707060404800344ca8400800303400008200541d42c20900060b5081003071001145054082c9a034800300c4080c942c002040c550f150100303010b1135540c21561038083c114180c01d641c041c410349020180010458410700d4098013842201c1c04008140d4802c0e180c0c103c5442d40c0d04007050350b903807000c000d05410041004042c99400d000500b40f0700d007045542c00c0035000f072400c009696003030f48070000303c00340c1e060740000100440101c0700c000b92091006a120410030400e801201a00c2d00d16051020740160480701d078000e49004c440c0f509100c014003895040b038a09101075002d998a030707c2450300341c1c41826203007002a80400e40411085100c0c2d030040da40551002412030508003600f6400c4d40702403040c10240c3e208 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 555699289 1250 555698039 555698047
    0xc0516172101030b010509010303051204050109080a0315060807050409021309050f0702060c030c1b0f1b120102280513062007050a12262a150c120c 65
    0x8502c4c503982e24050901214034a10f59803455500034000d110b15001500400c0c2c13103034040303800c0200c2500a19440b9a220040a440301801c5200030020010407101c9a000e01c543c00000072210b001d000d400d0300982140e80c0305850306050054090280d4849581c40885e01e04a400c0050f4030944c0c1d02c15203004181c2c4485140740c6041214009180c400081c100d1ba600e01c0040090001f1281800100c8140c007900b030755054000b00c0d006441c181480b52170001c0300268020b07a41c45010141c40c90040800410040303c0c031300640c000ea10103203801c070f00031604070701c8452400d903804c100e501500811480d80d130703da903180c000c0c0380903038070780600610201030341c00503020480d282c5c8048141d09403500301310600e003c0c400050843c14a00400150140a144900207840c0494804c40d4203003c0180034100703036441e50300c5242001440d907224951055000c19524914040a480c110200e00603180a064022071028014810725110003010411030a01a0800390080342c100700d90008441d01c242e0240c410001c00e8015526 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 555700539 1250 555699289 555699293
    0x9081204061b050301052d0907020309010207060e0a03110d0611070b0a1802010806060d02070f02090c040e0105101709071811071104090c031101030c051617210103 72
    0xb9603400c80c111a8203129040c4018055925400b408103c0d003c0000c03220311800041e00c0b101c07100800340c130210b00d0304003a81500b0000c8080c1c0010092886260030b03401c46a2095a8802c100c500c1c00c0300107206503202451010810204503401c0d1211801180140580f51411030b942e00e04046520200c1000000c010100320303902032280303600d46039903c8020740300c041c0041d858061b0703000f4000c003c14000030306010400c40803441540355442660404902d2107011940e0b81d0303036424441c0000d6540c1310700b01d1065551500040111000005581c1140c0051540e840740383d003400204000102211001e00c1001101403101024400340303036102d400f03103c030007000d00012410101d007440b01d03444c005c07650140e049c200305003500c500e17101100300d030441500039410980c1130107072100080240042c1c800280c45080080c00c0401841241090b600c40e14a003601d04010001d840002a901c50040440c132090886491041030046000c0c0f804c0242c5000401b00b09500e003c43d440500040c0001d510000c464111200e03005200b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 555701789 1250 555700539 555700571
    0x604030c030228030c0303060b040b1c0e030a0e030a080d020307080709080c0d020d060c020607020f0a020d140f01151a0903031b0102120414010c0810090908120406 72
    0x82c5119182010074160303103840c00c5610032480c0f044401010401d90084c0b02c814540302c3d52090010700803a55910b40e680303545203410890340e04810320b24100840c044940c0710b46d14109118098031114800c02560400c014003800740c60224001000c9601805413950311000100640002d00401760720200040c0c032400c4c41180200501d0740106010280101000b007440319000000350b8030518030301180d200d5108415032022410144003070302d00070400c5082c000707908402600402d0f0326200c0c9045900300c8480250380558075503141042c1c5800b039084070080b9a0003010a90840054a03540520803c440848980c804402e00b101c104912400d4100c00340d980074007030425244090704d220001303144500c0c2002c0001001035141d03c14a00d10781e0003942c141090222490007074050b01c080f1480e00908003110703d400d0601c9401100c1001810085500e01a4134402e498041c21085020b81c0b40d071140165954100304ea02d400810b004002550004030902000e00c02078443c1c0c200074402d620401c000300c0c500c0b40018843c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 555703039 1250 555701789 555701803
    0x4110703020f0f250902180102060a05010506040303080a0e06090c0a06050f040b030711010e06061f0815010207030203010501150921121202160c0503070311060705010e0604030c0302 80
    0x1100c140c0202c40b450352a030900103010981054040034580c9609480a0640310019a031792282404900100d808142c44c1c64441158101d0312082c0c0913681e0320303515881d4030300880780f0902866071720480034041440842c0c8038001135030b44031070540d50004140c1d41910a09241080413616403d103a07010f000c1a02c40f80c00d0040400d0020401030a0036400c04070f02401d82c1040c2c1c003440c00b13100c101c7e040120004036424410a5513405108482000b0000520311803e546d40341c00088071094005c551000c203503d082818840f40c503424541c16940c0002c99241c09601c9100e1450b5104d001e41107108400300071015903020320905000340a05010000125090f00000d083c88400c0d82c091089847c440d1144a540c06100c1c020f11180c1da03003c4078101404880c800c0907554290104c81c880703080340c03004c2030802c1590f04101052489a00910360610080c1d912010103544031400c2c00010405156118030560605101016055082c882e01c0041a603122400300c56207041003c031402d0b000900b0440300071003415014071183c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 555704289 1250 555703039 555703063
    0x7230d050a0c1703070f03020a150608010c0e010c02040515060a03020711012a020d08030109051005040501062007030f0308040308091209060a02103611090907050411070302 76
    0x4003ca64107420002c5031280a01500500310804160502080610a01940d083d5503413081c01d9a0851141c1140d500c01059140202211586002c80c8460715038040e00c184d600e4650140e450350880380c0d4035801e10020708805001726001501542c581c0045542e034501030107048489550041e1584080c0c104200410000c0a034503050095610f4000650103079502a84081008484000c80181c6548007041d1114250000640754a60101c0003294285958106a000d1a40b0b89040c940035a02c410800040307807001e01c1908045464009084070403401140d40000c2c18040744280c4003900c1e90f80d200e120342260004d900f14002801d401c100720030543c1000803a0b800c11000801002c01e807041458a101a10a540c0c0c00c03481100d02044940d013181c420841c01101c0307036000b001030065661013a250350074104a40c03a01c05098013005035201401d03040034072070001d05400614070402082090188003080202800c002c407103000d00701c1c1c007140c0780e2910f0103024030f0150700b00d00c0c1603594a507504000342411141c40340 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 555705539 1250 555704289 555704309
    0x7021305100e070c02030a0c060f03060608060f030106120f03080108070303090302041107021801060f052a03040801230f190f0e0a080d050f070207230d050a0c 70
    0x600c0410304490007588162411018400e50a031550741d010356040c040040025030501c80e001c1c42c2000c00010a403264204c80703454071a0845280c0342c050a40944050740a5000008c1411000030b009240001d03c1c207d003000090000240580c6a0b00388200d40000382009071350b00c0c10350f0384d05001050750000301503004007082c1c40a81052419568000c1010070f0310701c00070b031007291100c06c0341800b21510003c450721264024210241d540d58003800c0d6094241c24811a404114208000d4a040b03000389d0072a00740d1503125510302c0d0707a0340000380101801042e626017640144024840030170008024840c08404451a071107040b000d400014145612010040003000d140349000217005805950070824444401440d001044000c0c45446913002020b40240b25407240c45403401c4001031010360001044440c0910409000035aa00d480c195940101a682c0f000160f2086600f0062004125100700a115003e8083c0411111400c0041d400161080301a07483d030708400644003c0051100710b000041100340340c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 555706789 1250 555705539 555705541
    0x60604030c030303201b100c0e10021f0b030c0a03021c080d29010305040c030f1b1404050f07051602270412021908180a0602010207021305 61
    0x1451822018007807000030140741e01c030a1070070124408210700c1180c540789031205d5611a41d6009000b074405d6000049040c29018911000b03120480368010707502005584c0e12814443e440c01c5e014080d25414407a0700310214045e085481c3c0c15045841c1c0c3c2e50300c104600e054085070f1103241e40c00300b50800100c241100d2081a00355010401622964542c510038046c04110380c81012190130111900d02c035084110750300b280b800220341e90003101103d003c03031900c1c030b40407000e0401c2040b500154216182510041c0880c0201002040090100504c00348030070b21071042407003101712580301c1118404903504012074903d6110f40b12185410309106e07881e071004428940100f1800d2100000e04140325400440c0304c088010410502552208000c44007103220802900c1d91080c1e43c01541300c50035074240c508907000d031405550b035a0007920010311400a4980d00000c00c04049c400d59801032541d112400c41c1e8031880c000313001003ca03541c0b203240001c000c000076000943c1c0d81e802403041165450105c1d1145d02d141c5d203048 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 555708039 1250 555706789 555706793
    0x120501150e0414070c0b0f0f280501060e130627140403111501081b12060703020315030a0f03050f13120309060f1e12050a020c0606060403 61
    0x4040140c04860600300780101000c2180810050050030b001095145040c2d000e03c0001640810b6036041d160044203594801e446880542004100658806000c0307001e00001c0364092030110900040c03000c0f180e4000085140c04204001a00e03402d90056002c11611840c44821741440441400c0010304076a04100c0d03103081070215000408001c2042c501c0b516080c0903000601c420740e200d8a42c001c94500e48400038030f02403a004080c039820304100041406104120314038031080e240640d0503205194043c05942e4400d4019544002e0900003040d400301d543c0280952500d01800824003c449a40d80035907a4903141d018640d074120050140b9001354001c480382800318185c04500ca5800f40d040c0741c52584c584001180c0c00c241c1c0614a203142241271003803400209242c40404155001c2e10944840400c1a920700040c3d58004442c0001d90100300003414181c154a04200c03140d00a81300c031304200480018080c210001c03140c0446d01301d1201075000602d0b5001800070010240d1052040380e0300d17445c1504bd6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 555709289 1250 555708039 555708059
    0xc0302070b13080712020a080706090902031302062101140d08072a0905150616060e01140a140c070605091c030506040b040509150c1b0a03120501 64
    0x351061070005180400c0b100c01d808503100500c002443c1800499502640340e1189410069101c04124450a1061800a5a40c0b03010840300100d5029803210001e2610b0402c11001031b42c0005c140e81562100e00c50314200580e1007101a005100c02d109000c940c00400040d00031480c00b0681081201202c40c010141d4640d95400d00a410254420060b41e100d0540e407a08100c00e955201040c0700300c40541080c00380d14000b00880400b180c00340700091003161201c01c601c40071700c100401d1668000d1010002410540480021403400074800c800c00900309482601703060840b1140d00314804951505802e20008614074000c444124204800c000e5a50400d50310103651841a88801084d0648500000382c51100500480c40080b442010b036014484080700c0003401040d00319440c5100e0b602d000e0b64102103041c07910a0610421480000b029811040c84c2d078900c806400a0200100040800c5000315a40704006221080384e50303000148042e142c1407170007801c400c14840380c49490310b261500401442c019 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 555710539 1250 555709289 555709303
    0x30f1903111c09050a020d0317071707181e1406040608071107080303040f0b0a0504080d0902040f1107050d08130204090206190905100513030206031003050111190c0302 74
    0x703642c4002501203151900c80d00701201c500f0061b5001600403019001e250300000c1401c1c0c1d9070f1500760f0400f519666010103685800c61443c1c0001365601e108005200c41e400b03039500c1c01206030b088942c4030b000c5581e0326070b140b0111080340501d41c41d0360b82c1810410201d60803550380382113503e040702c400c0c0c10300c0c0c20300000034400c0764000c041e03d04000b8103102c00e03401c801e0144a5440a4500740040e60350302d02d007504189442510041088a0a80e80000080c03040300e01445014040c0794040350061030072444100c8103024140c050001e030303405a680e8ac07900c10f01c01014400c62000141e00100c0e40d40700c04060a209050580d4042b2460034403490508010005c1460440b90008507411140010b510070b0a00200c1d610b030042901d094040220941c11203c0103403c0031a1404a070b03012520086900f292180484480c001c268175a00801044102400140381000203035a2140365104c4541c1910342c0c903140c0d9420349a440008800b801c00000e1200950040c40a481089042c6420000801c5403140c0c2c0c001c2d62801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 555711789 1250 555710539 555710587
    0x9041512020d0c0305030301060c1104050702070e090f0601080f0d02060c0405060703030608191205070317090c0607151d060601030504061d01060815160e03030f190311 74
    0x21004842e0302003154a03044034015503006002c990300ea68440d24090400707020044140c401507505a072030300c1d0307505d880e0081c14802d0780f06a01410509250004007406108060320418140c001c4000e43d8007450b0081101d02c2c0203080c01d40c001e1150028505400341041440102d1100315007000f410010086109811601210000d07a0380076540e5080e07040842c010b103071942180300d03640560320076808101652411400c2842c0241100c580c14005500b0a035201c0c03240c440020041000d0b070604415800383c00c8803c551065015082c1c1e5078160070400040d80c4c1e40d010140446400744ea500d0340708031031851842021703001d07162aa10007030140c030754610310369854100818160415450780005000c006141c3c01c03d0212402070780341603850342c14a4400c60b01a140502411843d0b114450303507280c4500f45004618000d080c03c0184c0c8690100d40c43c03003102c80c102d22561441c1c051004100d00d03100855500020800c0b0f460a00d8401c102103020003000303003690100c00d07220451520071312400814080c0c0303404c8007102003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 555713039 1250 555711789 555711799
    0x9030901050f09031005071e0306120b040f05120c0c2b0611041503180206030402100e0d060f0c020a0c0501030b010e03030d0501031505090606130f0509030904151202 73
    0xa0000c0c000900d4205d03a0903014480900709030501901b65048124600170f4100d0502c0ba41e45083c024200300c0071145e0b20310402144020304504080440c202d42030080d0454019890b07090b0a00300c0784c0342e05141a02030505100c00d40400215202020b905125500d4440c008030b84000c039007030001060346120010725111200911007000030000700803c0d507100c59160402c0c040280d49640c1da403403006a0307a1016611200c00700707060041030407103529660150030b446a8010312207421503d80d5000d028030030680c4a441402d2041010b144030995650703c41f18205103200381c10204400c0d200380c0e007140c00d8400061001c010740d402660301ca000201004080070581d9428031780040e0b9070004030700407246903610303111a542600002484085664942e0050740c180c1e0300170050001c0800c4040520800c8880440b160112904001c010a03014a4150444d81080c1e000800214108818080203401c440c0182d4000506070310000305000107050600036402014182c6811100035850103520201c48501004020b10134 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 555714289 1250 555713039 555713047
    0x50a0225050603151f02010e0a0803040f050a0b0f071706090a150515030f130c1802071a01050306070c05071206060317040f0506192001090302100509030901050f 71
    0x4010612212405a0030007456411410043c14007078010100c17030f4108000550810045030b040400c0060101d5160340d1003044c40b803540e91940c4400000500700402201d081c02108043c0c00414500a5158092034007680d00d181641416400680a0700e002003400034003155070003c100c0705a07100050254001854580440c0c4102040505842c0750a550401d0303038040300980f850460303c240c04010310311070681403041c42040c0d01c0b5410b400d017040c04074440060201c102c9141c140001c8824030801c00d00441401d50250805003107640e4800e180e074101418182482e4450010070031840c0402c08503400c1a01e0342072a106402d01500d038141c9501c0c0b24041d940e0b41c4c1213812065030810010b5840a00190f4122900640d040707544140031803584d00901c1103042c2803005e070801203407030718014007118240b454610a11400d82500c00055901209107c2813030494001401e6108148000780140007820b8407a03806814400074508203001101d00191410045901c1405640201e9070401c00b02c1d500c403810400a02c0d15 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 555715539 1250 555714289 555714301
    0x7030305060a0512061f0b0711010203120103080c2b080c040b040f090b18060120060a020717031605070c08030a050705151009020711040606050a0225050603 69
    0x5025a6004613048030415084000d5407502084041c082c1d51501d016040f0340610701c006046000d414003605510000400000380010031001800d422000d041c01960700382144045091742d1403074242d100b550300303250026a00b400d0420a01100500003d6410109070305d0380024450b410880c4442c0105051003440b101088403902d80000343d030000d2003100360315681c507601ea101c0001030344aa0300c17441890500b0190340c40042d05e00b130400c0d20f0b41c00c0041100301005079a02d03001198040036103140003990b1301c20b940f48030103801418080301d80700300c80b540809030ba15182843c01d908400294000f91a1440092091010300c0400c2000805c07411302c10700d4010303120341d058100700b07821160350750141e1258840000c6000c0c3d050740003006040c0c507501460a450091981e220131080c049030131500061480b1803e8800d1041e680746a000e8042c2d1130203031204210750024070010074202d45c40390700910007081000c203c1d02d89882c3d04000d00034174080740c0c011542a004003811b0504881302c19000b441e101d0b110200009030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 555716789 1250 555715539 555715549
    0x4180c080109110c0a05010c09060c0b28061509050405010506040902071a040f11030a1a100302030118060608150604050c07021804060606090608011802040b0307050c1b01050703030506 81
    0x50007428040d070349500c1d12840c0c60780c000d052341d500700e0021954561001179051f0140e120000100d411500c480c01c60343c2ea0700034440301c44a1901c200d90b8180b91150500c2c0300680341f4820039014214103808074141d10394104014121551940c00f03d03210f10f003040c0040c000741d25008152000c0b0741c001c80d00540c56901902c0d100c10154440d002031305411480320204401e0000001484560b54040d055540700400c80310145a180d030b07202e501c080c25002c6180814140030400100043e400101804102140c0c1d032640d0000382911810340e80c4c1c08244540c51191000e0113042e104810003481444010100040e600030203500800c2c00400c0c0074410b5070f60f00000b480740c4003202c0443e8103140c0c0c01040031903082c4c64528400c0908000380c0b002d85e400c0e07182400205000d80500c004009660160316000616840e1240c0c0b1015100b0300e030100c081040d0240000910340c0c01c914003440c09004141c5429454a0340c2c0b05115241110003003200120070240c1515540d6641c1280880d2045a01885e01140a6542c000421 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 555718039 1250 555716789 555716797
    0x80a08091804060b040501050603060607020d0206040f06020114060102030705280b07050a0314060a050603040501060b0c0601090c05040e0c0c010603050624040606080c130f0b04180c08010911 84
    0x4101c40501c0c104000c0000e598440e221100301124204800d91700c0f44140035081c0421561113030051000c00c010307005803401d030045050351403000b400d1916094541d03401d405100300b183e00510250303440e280d00c0f001041e0300c031071083e500c800203100a60070298191511581c44183c54645070f1f54808401d0b1140c0b181d40104002e1042c00d4100c80810704070f04225400802650000c0404800280b4104e8a8010000a09500d0380514401011744075454200810042e80b5400a80215840d40da140350004800401002800303600441d103024000d80d40c07501c20f2050583d001e92050008022041109000301c0d84501e01487c0c004c5004090380c1d8844070300b0600c0a00414107030300042c0041c8030301c0b001c201d41010500440494094002c4076440840c880380e0a000648415004450114081e40001011080c100018040060202288003500c0c2d60712aa4070990b42c60680001105010004003070001c2e806d002c00780c41e148200d0702410480d550300c0e000000c001c0c03072040c055110a1522011030003094004402a1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 555719289 1250 555718039 555718069
    0x15130306021209010510080309010e180f01050111060c040e07170a0f0b060c150903070f120801081914012904060e09301c050c04080a0809 61
    0x45580d11002604542402000c580490303d40d801d0038000343c0b000d8410012107088800b198020341c2855540401941e0281e48080d010b504640d10f2080443c0c00b82c0c14403c524040d0400c0072080903154141400142140e440451000066001005002000400700b00b1a41100c0b0b4041c2d00e4015900d5003541129441084140303101401c034800706102c2101900c2d4000c000c6645e440400b00010210358003402824040e2403941c85203a000154002c801020100959030300050745820399207004a40d50b18140589140b610940300c1c2550540001821a0811407503809406000c0050844040d82d0003600e00e016107040005020f6244820440d0b1652401d40010325030200100f440307060260010f110229862502e18407511a41c10040c0009000d0b061780c2401d4001e181d0076019141407011503892455014504440c50745145607490107800130050900900ba500004e500080103141036000302070245c540c050514220b000007004100000c0320005080c000b01e65002c00d6143d01d5110701800621480715040301 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 555720539 1250 555719289 555719291
    0x7090317071506092405060d140c1908090d0c020a330c05032710082a1608040b030c0c0f01090201170a090203011a011b0215130306 58
    0x580d902d04a00d5000f000945450f181c0400c01003501e40041c0c56050f041450088140520400034030460030010300601c0c2100400902283d0704682e1119100701c00c8003141d50b0209000049064011500149045064503000345000c81301030034160740c0107450720600c4e5980740600615441640c215103031032480c07100a240c428811040701c400400303000a40b4085400043c00201920041e03035805000e81a03039504550032200950401d0059290b03800003605d8034260780000b940034045070085036900ca5403015440503944d0b031907074242001000707151810b00101d2440d00380422070800001444a60095602c1850440300110340d21140b410510003910030740d04165190f4a0002c100202800c1d907400811411031180100e464210481da5542e00701c400c4000020b0004100e400c4a07450903a070150ba00e50000c000c0708000842c1c050a500085c21900c1420280d078041d184115a04210360300803002e5051007200b81040b0601c1d40d042e50004200c4000300d01184a10307600851b0030900c000014071482d02469001e40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 555721789 1250 555720539 555720563
    0x501030902010e1c0c0509040c050607060207060510030201120525051b0a0308070201060803041403162c1e100308030f041709030c0f15181002060709031707 69
    0x180d11820b804c02c1841668407000030100000c040c10046409442990025402c0106904090400c200c0390b110100130703070701d440d000e1010101003141480340d18000d0280810a1101134654400074196414808051600c0c515180800482820803001380020b01000303484107003540d101407000e8465000b480c50001082120145d9280204400101101028080c0c1c98804207a07845e0310040303007a14200d010b4008103400c103210401c65060300b2105c4055543e0b0040035160003a40408031354803440da41e80c1c8a1b10b4400d40243d04050440f20840d240c1c1d1600702c441040390003a10b05110ba100141013191444c1c00505080800500022515510b04000e554003150603541c90070203006108940d08165015101064000c1034440601c42c00b00c01c03104804000703005058460400740c10860582c0540100c0c54012a020707505e03c210030310040c01001c00038282a40900b00340b210a040c8006c41e00151161740640d400542400b05040e040340442c4216944490b00c85030301d881c941120170780b5000b0000c00806ea00f501c61 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 555723039 1250 555721789 555721819
    0x3150306020d061a0c1b220c0e0a060207050d06200307170f040209040c08010e1b1c060b03070b0a030c080603120a0305130210050a03050606130501030902010e 70
    0x80c104004586009070403001c4109030b09090512071242009004032a8401c91b40401d10303160300c01c600b8440d00b0300100003610b44000b9076020302c1420581070140c0041c0c0c2d1b071000a0b0b00c20b19044010391504d840246ca040104a060000107981d588060040a110b8031600410a080085c0380e081555400075500020f142048040c1100364147c106442c2079000c9003690380b18800b8002d1641d0f00300c0c41445205141e090720b440315000e000c4109005070068a80c402c4e0640041450700f400d02841240d01c0f071000c01400c0507920a48048806191190628440c070000e81002080d55070b401c40302c1001c0c0da0801800140400210002032804803d036110000600c004102411803d8041d4406860004d240e1035a0815981d08010543c072821521034142030403005020710368600d88280e00040d4044c1101d45091820101c0d500018442c04c030070340840002400010790741c0d00465040c056241c100c8811360f42641014802c00c003c0001d00054010f06041550301c00c9498250b80c400c91503100c101c0740103007803c51459424 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 555724289 1250 555723039 555723041
    0x504020127091107080a05120619050402070203010e070605041d010e04030f0e090103230607021e01091401021908060d0204180c0305071a0705060604051009020a050315010507030e0103150306020d 86
    0x100d08c00310b01d004001402414500114a140b0705e0030f10000d03031a00c0c281810407000790401803043c2c0c1c01d5903a4001c802c039116006c0180fa8007400207610f8403a01c035403030503000049210b00030315102d0841505034010481c82e010391102c560015030604028001903100c4100b114400e4041406550200400000200340300020001c4286540550300301c410444917006071582c2c4001c01d4400b80010ba00502000d041410721103003c8072070b102c09400109003800c0603155940c50601002d00c089069500080c080103600061480b4007000c412801d104070903240c014005201346100c243c001e80a0f98542c002e12a801540e0030480c5411540441c0252071541c60342091740c1e680c0414001c24005401d0100300049640114041d645415072140c020005039172070034240800b900b8064000003a5829003180401c130880540043d0107446401e40e18543c40345400d00418407201100d625503410720004004103400710f907003e1480401d040c0203080204040e030b1b440140c2801e54145500c09441a84045100c1c0c02c0c00400f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 555725539 1250 555724289 555724297
    0x60306012c12240604020d050901050601020d093f121d13020a0c140a030807091d0c09030d0c170405100c05100501090504020127091107080a05 63
    0x2007a1007107504a210121100e0741c58400500010103039a00d83c02418500e4407403d2071951040010b0409418a5480c107004401d8400503611403c869444000b040025681000042001055490b05441c0149041182251640c541c0e480c1062002250310000030000c00f010883c09031000450b503104c1d03078042406d1031200e260241034507000140d20034442603001d6800058403804614000e000d080150725400c1c02034000d600c038030400000d08c2540c9000c100414010420940701d158036401421042c0a03d00d40204248030040980c0203102c5441024007066101411100105440e00f08040440d26070880c0c0c021140a4000400c6c2d042c0324907000043e00d07030361010540143d5407283c20311180ea15200e0070f200e00e85004270700507541c00254103002c4014240c03140b5408201180203400707440d10b6000d2010700b0000e4800c26001103560580b00c45c244400c65030b1185085e00308000782401e40304030744c007040103d014852940c0320f0403980d69140c104000e201d4480004944400313a00400c030640d1483c00d21805020342c4c00c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 555726789 1250 555725539 555725627
    0x207111008090607031e0207020315010e041502161214040602100b0609240702150c10051006030c0504050405040501200405090403030c03020c2a0f030c06030601 71
    0x5002c0440c2c0301034083d00400801034a0011001d2094400c06c01c5100250081c0c101031b6030511031250311411004040703607a14042e0a8cc201015003514290824140140c80a604621a1441080081c2900340524210038540342d20450f00014804940d4040b148000301008014a50340001800502c5d283c0014280b12000c541ca40305012000045007041441c2c01a6440140c0018445d121100c680c0e85d2002146181400100c1407400e1104940104468000309540340740d02030000031354555815030070007400040c508050000c4c85185401c160b1185014414414141416100c8429055983c0503905507000b900d00948100602d103428100113020348421101d00c80542940e41c5104402903804007114140d5401130010781eaa9116a507003100201201c0c60000c007003503800e00145907030520078032802143c4c0c0030300c19150300ca8019450040c0c2401206060b40c622942d428016181c0c035880201d20203030403010858a0649030707500e03100169141c01048603115000c1d02800301190304c114580c0907600403c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 555728039 1250 555726789 555726793
    0x2010509060d0614030c0d050a030f050f0706090b09210c030403060911090c040317130b13081018080d0e030d05070207050109180915090302012009090109020711100809 74
    0x200b220602407c1720003e000a0813030f8208511a81c00f081c01034540804810300d80c6441c502e8000c50704458203054102d590304649454844040400f4800442052508880c2440140545064896200441001c041c0407400c6111003c00d0340610083c0c11320a5500440d0050302c1803000e90351618012001c01410a0524464015580440c60b4141103a094400f41c03584100240a8a038405d1023203d0300b500402e842c02c0010b4051a07003c60f62200e403101900042e201da20035042c0250401c00e4090a0514011800f01428582000c0c070b510070041030f1006a0541d040f100c410f5a442d002c181e0400544a945d04e401468480010200c81740086c65218500c04c41c9a9170030b850026480d00c00440d203210840c031501d034480d50a4050321344501483e40c0715000281c40f903075074217100d821803034140401d0b6420182e0980150b503403500c00d40e031500d0861440300c441043c40401145881c1b0170000007201038406002d610070156000c00d81008011f07910b104800032440c02400c00c0070748045103c000b002c1da10202c0d404003442c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 555729289 1250 555728039 555728053
    0x501080d050f03072a080703031103060a030201050906160818010c0b01030308180d02030a03050105040b0a180209060d0203070e040c0e01050c071701061e0e0402010509060d061403 79
    0x2461281c01592a2032849491192039915095001c40714442d891000c1e00d40d4903c1881c0300500a8a03010415a0561140800303070345030900c0307007405011107844200320309403901c040041080c4c1341c1c0c4d59480c0c2341c00c1d01d0342400c285446126603401b0030028003c1881201c0030b00c0070b002e031160502c03100c00050035490a200b003283c1004031030070004441c0407010640040020601c00010700000f401405255404025801464003d13803061009500c1c01260a91840250701300003024086140c2c140215400b50800742c034140502c00f0940003140240c880e45c445c00c2c06241040c4118858000560102c0300c80c01e100070702c00b517110649401e410009600070350300f110105100180d52208c0782041d00540344091718584510f910303400c0c44401500c0c90340c401c1811040b07600400304040382c2202800c002040760007401e0000110642131181d910605d806100701c41c905500c42d118200002e140030500554020780c20f1810310b481ea09104046000360290b400c0102c0c01505100d8045014031008054044a9008504580e81 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 555730539 1250 555729289 555729313
    0x4050708100b0117090a061505010e0306240a03150209010801050f0a0605180a290c1b01030209060d090c1e050607021224070e091f0810050108 63
    0x4454a00b420740703011030296440480074880c2038004507440012102565000a81707603459804a85254030400076152400e002800256480180d010f040345003a00140004c2c14000388580c81140780500f0008ca000c2e1500c2030516a4681d904044000c0d84e102490540245180342c24070065000044464000341d901c100000d44c03845c20038001c1c8a580c41c05811a02d101c0d083c0356040381e455010300030080ba100c89820104440f5203401712304c1d4004107402c01c140e855013803000240101c0805039940034920f000061101d0800344a000c03401c10140b980041030303444081d10f01030050b0041d024a02039a5841840801c80700c0102c0101c0c0c10032204035115002900d0402c2e01c1d0106285501d50400181c840168884404d12583c24070a00134100d260006151051403007030a440540340c1085810f0752040c441d0440d44810090704110445a0001421300b407003860000d407000450400c44009000c5c8415041e400006103210b2503d41c0004003030201c0038142e4024122950400c00603000030301c01d41e0800d01c82c600801d94 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 555731789 1250 555730539 555730541
    0x207030f060c170c0a0e0f1203070203010b01050f0a0305093c070803040b0d060314030d05070c0b06101101061e080c01080403080405010b03032710050306190902030405070810 77
    0x44076600300400c1328117020005004460f00440c0d0030310a600700014150712020f50b540c1501e403c20f40a2854011a6606e000388141030940303007078000d010f0512000340001100742e2030300d4083c0c0e1000c000b28a80004d01d9a209594980707800404004400701c09031150100403140c603440f1681e000010320000d007a030440c0e188203540d55954201d106c0c90f00341da0000d010602c80711006000a0810078030b458004110248c403520f48200441c800112240c584d8000a9078014208013030240e95405800742c00c040401316001d0300d0b41000ca800080c58548902601483d180025000d0f005075041491510000c201440e124007110294400c004043d042d0b6080074100001e00039400951481c007503806958041558940c0e0354240e0b86030101900848807035488003ea81c68030f440c1000940a400c103814006d46c40349840300d40741d00d40b0700e50301480f490040303e90800100883da0004112074020105803201201c0344210340313040c065804103410042c00f4500000c240b00c140701d000240141075805800585a0700345690390036030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 555733039 1250 555731789 555731791
    0x70e03010c0e0a140409050f01090b011e03030528030b010207051f0f20160e100b0309030c1b03060c120106030f021918050d0f0b06010207030f060c17 66
    0x41d911010f02d010500c00b2903080c08085a1881c0058070120701882291769150600c24074840201c0c02da91740721959420702c008802ca00c2c0c01010124070030030101010f4000c01040903118080541809400100072140d5991600d2500c00c07034280c034180060078034900360001c2c00341030880d071020300502c01c8142c04549840d20f1b0608416695071040424255112080c040c0ca010080000038402c0c807801a01030341c044070303980014050a00b0300304003400b403140c9403484402814100d6040280008076120030030002c80072560450064686800b0402d0301ca5a0f03150080d461031040e500410340c1402030f481c1c001c246a0314800008882c60040b01a03640340d40d500394480322540180a41d00b5130320201e8400420401d4002c0c0e00000c0031009015000d0329010751214105030680e2882054030015100b569820b03800b515088800d0058002120121045503168581d50510004d07040c02614049050300420540e070700030002e11000f141c1c0049281100109404c1401c028441c8915410108806000c003005443d07201c2001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 555734289 1250 555733039 555733067
    0x150a0b030604060b0118090203070306140603073504170909040f06140906070f0e2805270906040b01030609030306050402160c05060f030c1c05070e03010c 68
    0x400321a82c85440d40000303010007001c0c0a041c0403c405814070051a00e003042d1018041205001d40c2c1d0b41840781c402011207190780d00100007821030980008680d0340d5201125004a03492408440c10002c0c650314446400d1003044040b600d07000041c9514083d4500000d061107980070310300503844c01008404660b4184114603c2c2640300c10703c100001e00044003d0040340c80c4030301842c1d0016114000041581c0c0550081e10301d8140e41d07000100f08000d495115601010091040c600540104403c0c8003040c00c00100c200021803e0514403019480090007095442c02400c0007000f9042603100d080215410050380d42007a21803032034000004a000303000041c4030b40540da0004150000c2d030300c0c5407604070040030f502d40120205074a5560014182d81c0c3d41c00641200c040164507050412620300d809003915603d035200358040d400901c6120364821445c400e495000301d0038184c07282e441400007000c0141ca40b0303070080000414036040c14000c0710b07603101a420131904029002005009040041500d2610341e01c810 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 555735539 1250 555734289 555734293
    0x7050a0e100b030c0d05130212010903080112080904050f0f1e0103030f050d05010b13080721050703060c091d060306060f01020a0f081e04081209130e150a0b03 70
    0x7003082004204002950b0107103d8020349410040f81491010944000307a034040500581080f0320415490700241c0d200d005540c9000070400c0340c50550700500510b00520549142c0f004d04445201804a0b00b000c071010054010810406850f0114a0842110059130314090020344800003910b10a40304508200404800c0d00c40c51090307103599021104518501d540c1d104104043c80055500301803402028040c10710000307c0b9840710040b85121200301203560081645502c00d07402080480401240301c03c500710a0f801240d0150034038108030b884d0440f107a200402551500d803000a07402d078031030b0101d02515540203440c290300c3e01180503801c9004040d80c031245e041e000100402c403940f8080c98010030500060040d20310f8030103075444890102c0c0c1d0508050b929400f001661039080303040501c41c04c0c042d01075040282d0515041181007038ac1c4006071401485900c00001c0c460400385e8035170680c0c002c04035184409014000b070515007103407107002030045243c101c10154046451029280104005c2100140c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 555736789 1250 555735539 555735571
    0x12060a0b120a1118040507180e04020d0c0f0303031d0309040f110a0305091516030c052511031f09080d090b040b061005040b090f100207050a0e 63
    0xc40210052010b800d0030000e80d9101002c20030500c1c28005070400283c00c0080c4d4821070801c034103005c1603c40041808080008000c0b400d8080303c48140d03808107031000b9810b0111a41d45d248003081211102100c090013501c0e1055000850941c007450300c07015684a076409000c030428100804540d02a5114103010170342003400398003640e0500c8c1d80600c2c2c01c42c09030b400110301d07092a43e603104111381c444680000020744802c10401069030400803404032800c05181c90040d0b03d4080c000380c0710540c1040c400f1003010340301c007100c43c04144100262540c90885000a4491000c01d03260408201c4884000700c0301d000780300900514a00d400314140b00030074048020402c000040e007803000002c2213908421228086c1c140b1010791000018820076208621454290301c4500785030500c504080401801684101d540c254a203203250362200a0700e0403070701c100b02103684464100700014510301078440c200e0b4000c1c034181c00c0030461950014545c0c0495800350f40040c0c1071900c407000c110207003000301c8901c14200c110103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 555738039 1250 555736789 555736807
    0x31b120c0e09150702010c090e070801031b050301112d03060d0f0f11090a1a01081512060106031113051207181a1009090e030c0a050312060a0b 63
    0x3200c4142d0203054001519070070910081c0c1c1c0c0e10b0f014000d591110040c0c0d920501108100c0e000303000c01001e440c240b0620005440c010b41d0081800c00140002406d80d21421060040305401c041080c015200040090100d00c3c2801014100c0b500a001000004d034403078a103250009180c0b05d043c019001b48007594502e1076030741000f07103c00145031240032520744d20285102808603045d0510020500e104091100e100082001003244002c000380c8804415482d046c00b86120403160303d0130f048650b10a0800041da0b5982d04c0340c803901c1d000700800b82504829107001d04041035101282c00c034180c604c9070f2001c100c00d200a11008000d0b0041c08458030741ea00b84248203000900c0c1241040080c1302c08071046601c05074840000440040c8014400f65030340351184418211204504044610f0b002d064510051000b05010010020b11071840366840740e6645070041d00b01c501c010b20440e2407544a803401c03103030310301e40d00d241181d031720380c0403803140180c007000c1802142403481c00c0031044088a5072050081d041c08842 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 555739289 1250 555738039 555738059
    0xb06041b20010e0102070c170303060f0a0306050405060412030c020a02040504170c011521020f060d0207080403050706090f0315091a060a0b2b0e07031b120c 69
    0x10152554a078810541d140340505024000c12114070b02810000d40c41381504e142003954007c40e6004550703140250413520607503680010030780b41d1040c030031035a2400041080021401c0e1240700c1e04041e1595090030200024050300051190286200c1d4041e44440561150214100c54110030f9150058220a010a002d032910741c210503081409400e071061000700101592039545c1c4600c8002e08103075155a04503070101d4a00b03440724000c1a400105410310112401a01c2c1d07110103101300244556280050028662922019140b001000d5041103580d070b4503506024079542c03c9444215690301c540e00022a03150320400c0100201e502c0f01c8001012181540d03640c50130700e600c00c00b12040c100e54a45000f0041104802c00a150406010040040f4103125041c845502c0c404d4010112800701000740300020050075102c0e14019941d401c4034540c6440f41c04000006c0d05c40e080e0b02e00380c244500b450101c180040201118402c003288421143d09903030755400c140301000c1e002c0014100ca10100c00c00c111403100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 555740539 1250 555739289 555739307
    0xb01050405011d1002060732130b0d09050f0c09271606020d0206061c0201032307080a050c12060609030d030e0c011b0314250b06041b 59
    0x10401d020781c1ca90080c02c04908200380b840c544c040181d00070030a22401681160b906840c18900440c1004540c401001490301076540700c1c10f50b0a00c0d10001031000756107018507075680240064030540c60362500d4602042010709405a03090ba20f03030140e519040401440010007001040740034000341495a20701ca13940540e00d8a41c02e51074400c000f00ca806070301e64030080c08140c1c401030025103d0040f59041c1100280341281d58560b61040d507000e05d09100d04c41d03480c4c00d20450f00300501e40c11449806068401240030b003685806000001e0010021710312010441c0301c090f40701d07882d40d0b0b40d0b4002c0741d82c89001400a8070025256001d0907603080203110300c41c1401c031003010707480140681080e02d00f11000002c2883e000440a0b0640002c2d9690304030445001d003401805014242481c20510186c2030b0f800d1005141c0c5900401400e2244102c04070800800a00584541140011054507181c800c0c3c0a0407084000d00003040f90ba0210080002c0c4140c0707050320680d0307449400ca03000314500f0a124031091f83c0c400701e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 555741789 1250 555740539 555740567
    0x13090203160b0d0e010902091f050a090c170705040902071e0c090606020a24060312020a020112020301030f020d03020f160f0b3a060b0703080a0b0105040501 69
    0x944060506148070004031900030004404030959400034181482c0846629180a138080d07414841454003682d00c80e41ca150308440030080e1056010603011654003800a5540b020303400c07814400300028107190641c086070480b01c2d940c40d00078018520164100c80d60b0011541c460206406101c02d00100c107031640a0640588140100c0744d1604a0100b801e42200d0501e008907103801d900c080a020401081c0103110040000740001e114006850ba16030380b8248180d6810002c1d04900301f1441307013110807500f20100442d00842070030002e1a0080c0c00940301c3c41801c4045e40801c102c8465407170f44c3e908520890341242d42085503101864a2a400c1044403807091200760110f00c9540b1034008054410701500720310282c041c044c40c072120b2501d4010510800c05034000440f03140b09200d040c8420174a0550141e4012400030190701c103841200c520030036001c0003280840d1581c541903000c10b500f984240204001802500c03245a15501c0000000c240c65030361500500041e000d0108100c507501030a40034a0ba40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 555743039 1250 555741789 555741793
    0x606031b030307020901090e0106150f08040501110f0c0d090605040504020306030a0611040602060a020705152d0105010815031213150c0209090a02100c080c0d020303150901030213090203 82
    0x802e03644c0005900030020381203016420f80c3c0c7d000d554045034092081c080101040c54141d480c44040b20000381540354031001d48803c2c0400d81000400b003044c00c2d400414401c22203501151101d0f40010449890b030407403c10b24034240b0030701c0d001c413a015003e1450781c1e003210300300d5687da4506400c04081c00082d4202500f12501803081c4602d2100042d1940203c3c12000440c14101d5151460100001e1a10401a180505640c4100140c801144000c50f10318481e165181c04046e0b10784410540d007501c0208182c00140d4280b2a50740e0116050010480d103041741c000741e132903d00585030300714042104010030200c640c2c140e100a0340701410741c0c0020064086410f0f80b103115031600f0380c1c030400b585205030242d501c14002090301c0d20407011890035a41054204519400402519000740c8c086100304020a4042c81400350709003180d0b040180c002c041b1800120280252403408006034000ba40e42e40041e0703088564104003800c4400c00d0301340681c0d40341c100e1fa00204a0f0803034200600c1c1d044018454024180e8040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 555744289 1250 555743039 555743047
    0xf030f080a210c09120807231005370e010204120c090c090f14060906071a0105030d140c010921080a02070f140717030d06080606031b0303 61
    0x8a003000c400a076140c01d210401048402400301c0084c50304034190080c13481412a900030001183d9280166010250701c40b00d0902c07800302c40d4841c10035500c5190400e04a9100e90710090b07142913043c2e041030b8060a2100511a64104000c50101d4070001311050310403036845955024100400d55048020f40011a000051510f5181d9100c075880908202d000c0d0b664120081d001c0203142e001e44201e4210306018680030320300c4c9080411a10f00034140384915480c0042d108501c0f00607555803022581003030b1008000b2a03540d074051030310384090701e2444068050215110000905811b012408002c265102c0e0780c0c102d49802e1102c06071030316400c940401e0503d0340d690122140010a49007540e00d40341c49040300b01080140c3c01d07034010414a4000c0c0020f24031030051100300001821014503105895200e22000c580d20b2108400d285480d916910412103080741d0b403007004a120001c401000d0880c244078045c000351313440701c401c995900b400b0303036482c1e030164800300768118000000740b405d407070074038004083d203241c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 555745539 1250 555744289 555744317
    0xd080901030b1f0809071401090621020711030f280c151d04060e0402040c03090c060507230c0d060212010b0a02011a0603071103070b0f100f030f080a 66
    0x4030f0081d5070a4a0128440d2818400540c1c03041104500400582d029641c50b440c0d09000204080c1c414403801c4144100c00500c003083c005468601011064108011901d401003410204440c1007058a070320300034007541d000c4801c2c0030130206d0000c201c41150390744203040c060311090107880940381c800b040d268245e035480d0104090002c0701800c010b6034002e075100031004240320031000300b81000381d1145218500c3c0103030030806818210005580950111000110900314640503005403050010081801160078000704103541c0010141464a000300d000001c0694507201062102c03440180315441c1d640140c140d9041480c1000304103000300c2c0305503070240c203000e10b0080c100741d404c400382c000020072600400c0e481c0c01030754240319a94010650300c900b6132518040308040380702444064000d0040180140120300052010000c0342d0981e50710030508140e514100540040d81081a50007401c4a05410400070390905e03500e0840e829642c0015800e0090005580da00322103502c100a514280000c00200c00c0e5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 555746789 1250 555745539 555745579
    0x23090a08010e06070f090303121116120216050d020607140706081915050906030312010f1e030b150a120f06052410140a1d0d080901030b 60
    0x3007444402001003240d400d10301006001000b83d04e175600b0030040409020408268001500b500c2a4100c0c440001c400000003250305984c420041050459081407840038100300c0055960858403455600b41d400c0c502e07044095208006403445550742c4421141207480241c942744008109041c403a28141c0082c0d14000c42450601007503034060380119002100300b0000c0a20002d580d4010851300008004120300400d504d8090400e9000d140d00400c0e024000504a40f400c1080320359a100071124040c1c1580c4d0b404619400d5001800344080f20300304841c1c021a41b005299610701641e6001c0e0644150755a0303480d5120b0114400440c083e403140701c400300011808099014840e01d280100714034440108641401c1c0d00b47c0342c01a0203032111500130015583d41f51038a104a407070413001101c01c5162858a02400c5800700c1e00c0e245091a804000260407800325000799101c03081c00b8086510140c1d2480c3c1108018108140b143d020f06460b20800002c20558840d030700041c11140c00030455a46501c040c2d000603 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 555748039 1250 555746789 555746801
    0x30b150d0920090a050f0703150b0f032d070c1a04080903011121180304080706170615090d0b0117190f021228020f0123090a0801 57
    0x44018020314000d000c5905203070f40d049501c0034600c1c000740712a0510b400f014548071001030900c0100740d642d41490b001290719551010082084801480c2c0744d60500850180c0380d40250780782c1d040d03035422800c07000901c20043c090b005a8070b0704030390000c520354840300296002c180070102100c020081e181c000118a1001d030669001e2801751603025120501c5009040c01c603040c00e101f085501130280664096032046500b400c0d881d0841102c206c036940c81e01080c5a030881140c1d541c07011a800041804a410040000d44c5411514543c0c0d4134200c0c00001003130384019500640d030854002c0301c2d8019a42818070088010003944002a040c21010000303a180e180a9440070b81000284071702100011205200400c000301c049116a0140440e0660715a2403a01c0103104001c0240100805910202c2940c400e001d01044041984400b8a055400c8092070350007140c2c0d298203e101d030b00c0203501d001c01c0394440c0344030f1301043d116000c1c1e540884008103490350301ca03000208101d41c00301a03a5804100380d00300f80914 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 555749289 1250 555748039 555748073
    0x303040b0d02040914060f120d030f15120506130b06010804050a020301090303061d09030306190f060f14030603100b06070f08090a150203091c020303120412030b150d09 74
    0x32508150040200314000d0100d000d22071b00385c400c51491032200102d086440f6271014107002801c01d0030000b0b001c016003060b40c2103d0000600d90f00004052100003642d64859100344140c076540d60340c080c4450381d445140c1c00090881c00c803000005030554003846420b50024051011202078450342c0d80040d00f0355032480d404400182d11078008000d00c1d0103c91140c41d00c0b03a8800101211032034a4100d480d60307808014841031080031104286113140700c20108850250403904251480c407615248060508007100403094009800c4801611200b1800e20a03a40a545d00401900740c14040025400103444503090655211400304201000a586d242030081c1c4548030743c040940ba40f040c00200401024154000018580c05040c02e546050740441104d2900408650040f41d661040e0502a6129410000250184400991001c4000392009218442c5215249903041107140c0d50303089051350121021240c01ca07100c06042094038002c0c2c0040c003c40a000030300040c0e0302d4442d44414a0106480f001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 555750539 1250 555749289 555749321
    0x303010e250e0301050702070303050904090204061802090102060609061807030f29060702010504090203090a15020702130606090b071b03150b0303070f0213090b16021b0303040b0d020409 82
    0x7100e034642028005c0744d90028042c005003103924515107000c1c101d841404036551059179200344100071076907150b101d60301070301a02110b0b9a5100f0000840b00003075002d81070407400741c80341400080a600c0c180c40074600c074550140c28043c0da002038081c070508240001d40400e0905840d00a4510140d20b14440d41c122248031804003060035000ea65144016414810042d014030010404100540d81040868084410340308006035203030350f07a14080b03040441d509002441040c0c00d85610503200801c0d009044118002c0342d0180c02c440902110008030b441c5442504041510740e0420411324005c000038284040c010000d5045002000c0610b40031414a500b00300d0300c05039400e250785005440c62040308c4a42d40254015880d042003074032031a0100c141c070f0a009220b1031800c00064081240c41d04950b440a48c03029009680d070070881700f4851300600c40c85803540188110b10f0800641e51944492082c8044d020b000b0314541401c0010078405a4013460210b03030000d40811001501e0401761150001024403524 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 555751789 1250 555750539 555750557
    0x123c0507021e0102070308060112090f150506090103020f0f1305131a01050d020d030507171801090b070210020708120406120c02070902160b1003230303010e25 70
    0x50b02814500c011a5050503a88188041000644c0004649400c800c09090110740b00c10603520700c502400c00f66800070015240140712108124103c4600e0f5025444000103000c00d98801c0b0600c04003000c01d1002a612582c0e460b20b13800142080d580314402c000c0080d00007064545042209003c0c1c0740b043e206070f2180440000302505010401c942d01c1d48200034624a01c20350b5150200141021a02c1c000191141c07181d001c070002014000c07421118072030360120303100d615004442d1500d401c6403c040b1585650f50a5211501107961041300001300b07946a030001c442c00d00c180c82e003c4c00000a065900c0304190302c101040483c01c058204542c000607521544095078030341c248a801042041345e442e1444116081650342c51840d41c000c100c20041d2241240300584488400c00c403845c4000d00e0041c00303400d452456041c4218468541500401c0c1c1e4095083d100844000201d490040301505808000541007032005224070520039001907006020500d20300205a845503210500703042c0300c500c49000c00d01c888 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 555753039 1250 555751789 555751813
    0x5150102010c091a0d27030207050111120d020f041205010605040b0906090c0f300103030503040f1a07021c08060a0b1c0204080706123c050702 63
    0x10003400701d040b450386081d00a41d440d2030403203155048030140a12442e00c010414007088051584151446205a0700c0d502280d00703003c3c420000410541c2d82500180500c08020503a9401100e1184014007044010f0155110798101186540c01554022025640802089402c80140c4014001900302d040340010604860b03d08603084507415840386008900f005081c070499955080c00070303070010b41503076480065a01e1409074080b62007000e0782c1e8012100041000c130b030610441c111601c01840c2520704520240e0030041d02c0100c6140034840100000d104100080c00500169500941e07140308100c1541440d01e110100c46021404840560050b03000700804840720b903602e071603652201014103180d011400e10b4000704186032002d0107076031142ca50003d0084c1c84c08040c005641e11211401070304644598484820355105c142c83d1143c1e4001070150507889611181c1d500c6070110300d0b00081e04445400c100c0e500c26050002d020713018029002e1002111050302c403641c2c00703070394401c030181c3e80a07000c880080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 555754289 1250 555753039 555753041
    0x120d0b0a081c0314040f08070309090c050d271205040e0103060506180919050c030601030b0405061605090409030516140d1b2312030727061d040515010201 68
    0x29400c5540d04414140500000c030349800318903240c0c1038018140302d0781c0d08098181660784104e154486e0061520f0041d00b0b93340700364020050901021020001c1c0701c00c1c1c0f006840c3c041048103001c4884107010050445000055984604d075140c10100d051081c20aa40e03800405400c032026441612019250000c0000c1c0b4038000d140301d50b20341840f40b040c0006080c2103100030754944800c01c040c046c1d40c181d00201c8042c040d0800416131280402400c0714a2503071289040b108699098804841c28031903140840c3d0038805007066030301d00210300d07551140ad0111000400c80a07107031300241a024080d040205000b0060484000100079010b20b40c98045035036200390951600600c42411410800350020441c49a002c403100d8280807034000325040c22000c0341a40b442c81c10700d4030048180640c4560003031220f40031b00741e1001d1842208961101c040e0201448507100c0e081e5580455142540e038400d03014802c19004190040101c500c010301d443c6a02c003840302003421914103a440c820310050401031003145e1f680c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 555755395 1106 555754289 555754301
    0x60513053a020f0109080d0302070606081009140307030504180b0306091c0e0907031a03030a0c06050703110712020307120c0203070602120d0b0a081c03 67
    0x4038804614100311580c22406a04100740d034020704e6004240e941c085075640c00180585000c603a00441c002d5100e03441c21105241c0d101c4021420481c1007049070100300c084040019800c9860912441240c800c408130780b040d50003000b1080000b60b0010a840840340c482c2216040d581c0581c2419010700b5280800d1074042c401c45e000c100202c840022101c1504070b4504903910b0300558404211084010848096000085c0e030012030101d41c03090788001101002003290322000c001c0c490001e41154460048400010071880c104403d104003441440d0b04601079040410900000c80c605054500074020003412000340c2509003102c05001380106d40103c2e034080113039601403940311005008454064801c1c1d0281c400c2402c042601400001d0a031944408031441c0c50915030a04031f040045c210b41001c0303e401409200000615807420446106c0d220b103008003481400310100e4004040f0f0708 = true := by decide +kernel

theorem cover : BRFrame.Cov 555575539 555755395 := by
  have h0 := BRFrame.cov_init 555575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 555575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 555575539 ≤ n) (h2 : n < 555755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
