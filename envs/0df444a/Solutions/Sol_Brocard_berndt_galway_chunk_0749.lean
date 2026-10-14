-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0749
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:34:32.137532+00:00
-- url     : https://prove2.me/submissions/54fc6e9c-542b-4611-941a-78517db78207

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 134532374 ≤ n < 134712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 134533624 1250 134532374 134532427
    0x70306020a05042303070812070615050a03060507030c03020c03120a060b0408010504050d09030201020601060507030216080a020a08030a0f0c060b0312130906030b07080405070e0a1a0f060708 84
    0x5014040c09921900c82d40400444c00c130f04440515448400882d1078030200d050304080450113001e0440080d899811441500d07040c4600302c3c510a9032840066240309140c0d1050b1001603a6009001d035190b0315004600c101ca20b50b0900b07510342080303600b040c3e0340ca100f00140050304401c98808910b0100054121000601d6010141900c8540701d020341c034000e24064a08507018031480c990030103c140242e41c0c1a04036901600589240d80c41c114090701d00350b0042e03000318210700901c1001c80800c4211840350300648020801422000c07181d20520201010b5908000d0740c0394010721450f0299544041041e02e050518509502c40e0b500c0c5141107c003602004880ca5454080c85e41991070118150020703101440541c2c1003200e000e0390f51301c8443c1c21291640000f4051400031000165030074000d9140301d402920400440c1d050541d42c034014038440d0400e0700c4d002c14082d1100e41549d200c01c0741803207105090004036010070f081090040094064400d00000800c4407d0204201c41805440c1045101e203003543c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 134534874 1250 134533624 134533649
    0x30f080c032a0c0f1516050d0f05010303081603050118021b0f0a1506050d14030c01050f0714120103060e0a061a0a14090604050912070807060e0d02070306020a0504 72
    0x2801c3c6003a40314900c0c3c1400c0460391050b034000000d810881442c2a0240c03010a21056100c00c805104954650062040ca101070342c4400c180307489070000b440346038002e50103965a0401c0f820414040c00e02a007184000c0e00405051400600000040386108001c0d450303503043c01a56a00146800c0003891300c20720010a01e40224148146c640c0000316111412500c04d04548020300201e4609204440c0c01d405400e4005038800c00c4c0100151640c44262a03c802c600c2c101d03818408012050fa080d540100c45165480001900b404482038000208151a050420855080941c0300c410060007500501c0040c221a40720b200030103280c80e040c03210886a64100005100100c2c580d141440048601c200c0a409081800000216007200c02d04205074208001c100104507120041004060305002d0561802c501034119024580c0c01c00c0300c02008458441d280c0b80b61508014282803045a02400c05458645c01040501050f65800b00e40c8100b969481400141c852070120400c44560146801c442c07080c111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 134536124 1250 134534874 134534887
    0x1090507170a210311120105130207150606030b060915090d12020c0f01030902060304030c1110020c030106090501150810090527010b0d0b0613090b04030f080c032a 72
    0x3000c0ca0f00801c0980c15407000d026200640c0840f500920605180410101c075040040c007440c60f01d80f01f5104015500040581092440e8035a200d00c020300c0c0040c1c03030350300e42c0e140810041c040d01800780480716039040b2881814022002d022031302c000c1c2c183c0208488d40303100041c00780180d0b581030540010b240c1c20510a980054000f90065960403400e00d0546c0300d0341c1d010a08031215840b0f800f801c80b4a5030b0103018282180c44a54003500c00c050002e500b04c61b03004984100c3c640da034803101c61038400b4006a5000740a200800b03414107003114840e030000d000103410000107000071060081080ca0b000860700d0548502d54841c08580d04800281d0451148282030406012641d80781814810403520040c0c028403240301d0001c041c2d4221854580c045807c100b95442c100c0114a1041d07000740d02000161110046c8044880c0f840e0464000880c12030b000c0200405001c02d05511000c0c00e00c0080d070a080c5a030580c103000003901c225001c010121075002e0341403100301c1e03942006401c0c50040ac4018000103500da60 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 134537374 1250 134536124 134536163
    0x90204151214250e060603072106030506090c0414040209040210030b04060b03190b0307090213051305040b010f050108060607060e0a0302010515030c1522080c040b0301090507170a 79
    0x408510864684040044c04113141b07181c20700441c0d01422850f1101b80b60416110311302e031281038003c215118025900e0b10000007040d401c1c46a02d110301c000c10007405003982108104402c41d20300e400d000e445080103804210040e143d011184c1c0c1c100743c049030701260308003140c04210054140007603140d030030a040030750000d12000410042d600440c007004031388228102c203001e45000c490f0b048580544c036500c002000c00920310707654020410504802c1d91001c0b00c60f10f0301c010440c3c9403140041e4400895969040005100000b48214094015803410500061910b0002403000034003a00e15031140394001070b000c2c10000d45a000c00c2050120b103080c1c65496002d0704004e40240400c68420916000030903200d9440d00d00400d00c150580c41c000d00c1c0703002c524100e145000c07054024280e442d00115220130f4100c4080d00842c1100c0c02403011740c004108011556051200ba108901001c074060382c100030307024002403000b1620b0702c02d48510150b000f031500d4040280d41d252000342400600015002481c43e420382c0f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 134538624 1250 134537374 134537443
    0x19030f0303020307110309031b0d06050c07020a0501090f090f02070605130209060a180905070506041503060e1911040510110c010f0c0b060604090c03090204151214 72
    0x80c81c40f521400301d000384100000f6220720444507e1a45604001400782050320902400310031184054020403103200b45c0d036220021140c2c180c9800300e000c0740201da10350441c54044401d8002e03000c20700e08441c405140100c0507011b8200343c0205801103441d810403450704845581078408243e0040024071080c10003507852060504446400d0b80511a8000040c12070304019800d00100c400040003100320081003001d541c028514400100d03418058642c0004140e45c8031800340000e4201003c0c100000c504034100903048130a40e80c003540c080d00521080199050400580b01c40f14281c207800802e005025134400030040c401c0c1c3d041103521071185914161700960199407a0f0408180000700c401031480003005590030200da070000d40014040103004400958499400b58020b480a40a00e04141d107500524044d6080650100d0010780d455002c0402c1d4074250003a22951036007800201c180d103060480740c4121520b46800540810880d0703810100480c1c04100b103558921000c07241203081c10311a561031100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 134539874 1250 134538624 134538631
    0x2031314040509031602041d0d11010510120204020d0b190e0a0911010528080f0a05040203071403031c1407030209060307030504050307021f11160519030f03030203 72
    0x20790b203824009194180c0c000102c1e4451041a002c0c034401908036800c0002a1000c1c44400242075000b00410b09040c808100c0c01c540c1401c1074607115013400d0801c20541c00c40310002c1c03900c02d01c09403502040016681c1c2000e0001c120f42c0540c2c0243c1c4c3c8020f000c440c44058440380401c0e076007011b0440340460301c074020541f048003079413001524001c0c00d03100c0c20ba20300107403882410050003003000c00b80c207500c0641c090030040c284103120346000e03905110340650f0030070038102c2c0080240100d0000802c1210300c82c50072030803503407000120b00c04010605094003c00d070b948140c0c2c02840155460070b0980c25a42e6010070070b6400d40e00b4a2590040001d0a042c1d200c8050316108038080c00300c0c0f5902e4041028203000b802a81c4405c040901000d0955a483d0781c2100034200140007581d19005c10003101000d6101d10a14002904018031079108c070040d4402c0007000325076412034030030444e004075415012481203031911500301c13001151144a80102a42e260178081301c15440189034051004c0d4160800d0b1301078000e54170 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 134541124 1250 134539874 134539879
    0x20705100c1103040506041e080118060501080d23090913020a060206041106030408070b0a1a06040302030a060515030307050a0204050c19030504080912070f05030304061b0302031314 80
    0x9030710300c514103030b203a407402103004080c1e0100f4203000c1480340003808254003045001543c24407942a81d217450884c00c41c1d448039000000c8224088501d000e1103102d025103401811007500404420b01182001440103c1000551030345282c585034000d0b24961040540e0703000f80c4000c0010400341002555030035420080c1c7e10882c002c85c6003400004981d400410362501c00c4d6003000c940300380740708602c0c1080090b50000340120383c07243c001d20451002c48c846400c0340b84668014040040c0d00711030020b083c40c8104085203c0e81c4100d204200c01e1005803804070324205061303404000400c40c1d4441012800c41c00c0b40010070355805100120303100050140001c1c100140e14000c0e2410070458480740f0000405100e0f074a0340c106c101c0340000c440110b1030712030390100d940540156042400d241c041800910310345441c07500408546c0c0300d80824081d000d42c2800a00050030202c0085151500e0814040c4c0140c0628580803500105c180c11007080c0340c02801280c200b096070101c0301c46420b440c3c440c80c1c0b0007408410001d60 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 134542374 1250 134541124 134541137
    0x102071512060e0106021903090b0a0e0a090209010203070b0a09020d080d060906050a060f090e1503070803030702060714040b040b0a030e0d1d040e030d060806070e180604020705100c 80
    0x140e0400b8610800f070581701a94050510001c900010042042d46840704070200802041c0004912803810050103c5021a6440e1210011410200909400e4030741140311214410081c01e5426078001040750495548000c016400303a8031203015030018400800c010f504900c50034040b6007004200802022000381c060020444a601c8094000460f01035000305034000381418000d02c041030240182064503031407850801c400b0754541d10988031820058a1242c0b4018602420420314a4240700344070140c031804004509610300750b00c0c002c0d610718003d4240c1060041c040089514824900308460180c01d00c181440d549682d10341e8821626808210301d94002031030b000007070040d0480403c3d841824002c03544c81c48002c4420403001d050341d800707441e280d5070300507a6030300010b0301c0b110184041d00701d4003082d040004069240c0f01600d410701034020403031f80411411459218107903403035406441541c089292010705c15510704020034000d00c01c1500280652107410141504000180c00c001141d840070b5a400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 134543624 1250 134542374 134542379
    0xf091e0507151709030d0603030e0112022104050f01110d0507050a0c03030e03091309030315030c0b09060f0c06070f09060203090405060414010e04060b0901060206040f02010207151206 81
    0x5581044807124420004840240034000650f00d41242500916684181c0c0e20303204a031080c40c812100325900880111704c0d0140568020768011a2801e10040c000d4010740c5040002ca019030f0740c1d0103850b89000007450012010805201e410804948202040700c000c000c8c0042c10030703100070240c012410340e4043e2414030b4001920640700e8000d944c1c42c00441d4444590352041603500b0b801406007070709848042d00c400d200088150303a0300c5280c5c841d0080e80c21130028500c40e403400c0c002c0589060280810a403100c0c6e2004000003101c0ca5608400c60b80c0750220b0945131501000001c01d14460f20048200d060b40100f451844030402060050090310241c68003006840968070640c0c4000c0184928000740c0c1042c05003028a090941040b81c1c0141c00170000140d00c2ca802003940040a000c0c1c0008000c2a401005c01c020000d142c0308101d2244c1e0200d03500d8040f503240403c001e54031320340100021b00100e03910384400110f9008001d1003001e0000003c0c9221840724402c00208141c4010040c001501c0c00d18800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 134544874 1250 134543624 134543639
    0xf060105040b03060f01110d030207051207020a090c0207030b09031c0506010914030f0a0c060906030b09040210030b091918030f0807020f03030106091d06130f091e0507 74
    0x46400301c0b5002c614160466880d001000240561042e040b4140451800c902d10440c0041c89811014405901d005848075540d04041d403a01d855a154200048130820001c009079039a4601c43c03040b102d004002007800c0d403a6241c200c6c207148555100605254060090051b942d40200c0585072400c02e00381d00041035070040f964401a40c0c4203035440341c0400c868400c24403407034148013051889610301504407054041450b41061601801a5040d508030620003400d00c041c950012080e4010301c04ca01e414441901c42d84001281d418024100a20800703c1c2200081020b02a410001040200030300445035460000c0e1001e404054643c0703601030641c41d0440b9841310405e481003614900f5016941c040d80200e90b1103058402c494050100c90a5200d508150811038004000850182c234460b80d402880d60310f0311a06d081d03114000c030304450307014000c1010402162148403a80b0280000c04d5404241046201113140003413079400400303000f04e050415140c140101c40c261b40c1242c00e00c00d07400c444101e070740c50300ca = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 134546124 1250 134544874 134544877
    0x90702012012060d0c15050715050106020d020c01021507110a0308070e06041d071107091a31020904090f020109050306090c0d141501050a080304050906060c030708030109050f060105 80
    0x4c0003405800003d005000d410450584c003000400c1509000385880308980303891441d809010841104c041c0c0314401407001c0c50341401032000c03000c814001041c0400912001030340f1050400940c0c100c3d410114002124a44030708104100300c0e4100d0142ca502e00d516007001031698000300c6035080070484c0c10b00840d5107804d050080300c080710203d00004019884c0c2d044070186010001d4216401c021251a01242c0c0800501900700204480e070800a0381d07841c00c1099205a204030211b8912641100b021000000740ca1762b086021b00c40d0038106840c44044e0454540c0c020b010312030300940c01515100600781045603c54074028514003d80300c2404a550b50310030036948032030448012190f038003d00045291814407440e201e42444c071072074104804101c9508030b01d00d40600b5035005a40d01e0287c40040245080981690f00a0038004000d14909414803002c500d800e640585024021040021052092603003801591226603028480765034950b03481c83c05102420741900c24a04102c840004581c21750300440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 134547374 1250 134546124 134546149
    0x1d0106030501060216030b13080f0d11030606070b1008150f09010213150504050409060f05091b150f0406020607020d0e090426191b050c09070201201206 67
    0x84050500c5da0039581d406c641580d003e8080c03203007000d2840ca410001079101019000c60440c1e0442c0350b840d000110840c1069504004000074040700c10018003905444160454441c1900701442103860340380e184000d541b1201507406060a806501844406445005e40c00341c02000c0b511002810b07500e130b0100341800c0b48108541d044403902e00e80010401102074040d448000c043e5800c242d41019a42e8002c00c041e5a50400c089401d141d0721030403411020550701c546500540483d0052000c12520440120720548001441e442101c08911064032124074200b1549103003801110a915207070b0b1090080d6440e01c0070b96418026002d90040e00711960b00c214805e035040580180303409047d031140d4660b21829605042581c1c0480100000d103940040c0d034000404440701d00c00c40d4405014100700b4010040a100031a0f0b100b1030207002c151038089030000440703e403e28402c440b072044a13222088140d00400e1003206c940301e6980070581c085825401d090261100b000e0800800710203030b482604002c0540b2070300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 134548624 1250 134547374 134547403
    0x51215010b03070f0f05040b1b06070822020d12090807120b01050913050703050c01090b0c030d180f0b0f01291b150108070e01030510151d01060305010602 68
    0x32044c0002580c0b064001081516290038250b107000c0c0c0703c520000c01c0358400d00545102c00441d032515640c0550802600b03a108034185010340460428031410592841c0c800b41d40e0315412240301c0342d4000c4d5071b50107045215966120036200400c0c001c6400c050140d16041c81004140c0c09100c2d000242c0500300b02c9940651684150307410351a80c00c0c0010810714400c0500b48004410103100c0d8040010001c0000714091030244000b001d18210b2040010841e803001d0300400050725040c043c03000385440000070703550440541c51000c00e4451001c1c20b400200007588101500c801b5005031f4210a1120b44d241650180034004c007400c1d4203030b807207000681070500701500101c2c0340c2504041615204141c907000d40b08420070038050f03005c6142c0308048103280c640b807443d040ca008540303400104140034041040d203004224280c01c081e4950325646842d9110720704405100e604a88a1180c5403011804940c240058042605081222691504000202d08090155201082c6000b0001c90b105000154041c00310500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 134549874 1250 134548624 134548637
    0x5030a050a0308040309050907030506030d0309150903050f0a081f051f030f060e060a0905070507240501080a02010306170d050c100204031b09090b0a09020109051215010b0307 77
    0x1d80d503040740c88410040c8140c080000c2a4004241981c92509141c040c3c0f446a0b070129660601c903041505010281c48004145460f05031954000303100e440061101d501314540005440019050540d01889051202403143e4000910314000c03c0d00624445d02500402e103100c4502c00001c0c00c00c0309000594004d1542c0b00040d8811010100440d0f2021000444d0750b1501003054201e140303202040d6811038000c0c0703a264003c41c0800244c1d06040c55058006c21600d141070140b41084080985680304065002c2c0040c50801e1042e88200c41c2c070241d2140b080b1071502c0820081d1f03540c0081c140c0312010180200e000a0400c5800107a040c500350107031024590700d90241c20907100302442903803160301002c11180c0b17500030413881006505451004e8402180101808490350090b041220040c0c50346402001d00c175441c040c0d082004c1003541803410b52200580303100244529207800180d80010b1180e0040b544000121640903a241d00807500e1103911020300325a03880790742c88a21020b8035000480350080001c00c0d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 134551124 1250 134549874 134549893
    0x12040b010504180b0a1104060201090201020f06040c050108090307080423032107020a050a06080103051c08070c14010518011d06070c1b060801180905120a1b060506030705030a05 78
    0x442c00013207410644298001801d803046000b818100c7d0000d0380040c001d42d5542c902c40040d940c05000c480190100d2001414152605540356201d0103c035014060420100000240d01d107031003001202c1420360000080d40d00d46583d800c0140d03100314503003070144100c844001c800c11241000260201c8078032800400706c003103219503151040940c03c000010303a4494488030001440d9200d9401a8004d0075265036802d4041d0f05509000d89414190460002c07400440f0f16281e00003940a4580354225141e80f8000c01030000c103080c0b00510100000002102c0d503c3c1900f80402c80c0740c4000e074030400c04039480081c45480750001c3e1658484860950741941500a0710010328254490545082014401c5050356650708141c4a0b401d00100182c1080000c544180300600c500c1f07400315980f48011080c50418400e203a116a151a06c446402201c03031032244004c43c0c10980340c0e005003d007091008448005546460860a20381c02400d41610264001d014586001c070706418003103254181d072500400102801003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 134552374 1250 134551124 134551133
    0xf071409130f0207060203040809100203120730090c0609030c051c050a1202011508030702010f050c0f0c3606062107020706111b0604030812040b01050418 68
    0x50ba085034040c916420803038800010070030703c069405076026480b140e807a070201a09003c4074841920b04002951301c20f20502e900c40810341d0fa140c1e84450640390982641020150320b403d0000ca084032001c840303442082418440f4215441040782174050624643c5840d9905002d4079250200c0c0806800410121030600c200e04060080780105031000c1d03810a072004541d00d58a041c13550b10041100c1d45c8071030580301c540d0643d090181000e400c106c004504a80c1d45002e426a50368410044028148500580d2003180c030381c00b800c1030302d40e40c0e90142e044d41c100c00d00202001b034507061460070851158145000c0032401c07015054050686243d600300d05c00be034440c445441e0b50055402012a0790141e02041281d2030b983c8800c001110900c04014514181e00b00464081e0414905030030503002c000d4000d80b0310714030900009041c021841c1c0303403050903c08011100440d4041c49075070009400a4000101480c1c40c00045a04c00d02c214012800c071202a6200c0c02080190703490025040301c1c000715034083d0300214 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 134553624 1250 134552374 134552381
    0x3070c0b0615120c04082a0405060d03183b0f04030c060204050607060f23070f020712050604032c10170c0a092709031103030f07140913 60
    0x81e040000c5414540e40d02541c5161100d45100318160f544400003442d4401c47c3c02407646080c4204131024441494001e001c00c44800c000100501002807096640c3d800e288042040c00c00761105440c0828145090480c0c002c0042010184c0e40905d500107c40030042e20312001881e002d41c00081512660703464589048489a03040101602e00d00c0c0c1c200000580b660b10b1000030120700d44101d0740440d4481c582c2c40c0040071519800d4000b00e01c0b444002203848481002407800e5070010b000d041c40100c003101c12130100d26041c0c45030414501c52080031540c405114000502600c40c0e4481d585100042100da00081c03481c40511001c1081105580d11207507081c50b0400da9061441d101d880c199501d6240550900700301c200680d00c031100e121000a40700e0b244d03a444141310020340b02c1c8558225000340444050021a901103d84464266540040400b01441102080210241101201e841e41080560350072061010750704000850101c03005800d0880c080415545024002445580f10303015440080003c1c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 134554874 1250 134553624 134553631
    0x609170307020d290f010f080a0c05150f0304050a05010e070602060103030c11130b0405060d02010c060504050f0a030215070c23100606030b090a0e0604200603070c0b061512 76
    0x22140300c084c0140c1d03041040c146640c400e243e06401c5958035403410031644400c1d10f0320381140f103091f0010031407100402c001455032000c4071000d40305002e6400c3d50184622a0340608400c402c0e40c41d40001c20310003800707000682507825500860080100640276456175584905d18803031900076810040040021034042c1d5809014940aa0001d1048825904c0007550001e02c000707441040550b260320000d82810107106545d13200d101a541003924031441e8001030684440340000421160301d640000381080010b10030130301c0115001045443c182001d00c2e010b5101c480010302c8070030050844001900340c07803058148060003900302c90703400d06404001c940600b4150b10b610110031148120704411704c3d02103161040c00b008203216034000502c0c0350294104008610b000c3e000c15940c50a2121110070100d010589036006544001d031040c030b001c54100742c81a4407824403002135200b60040104518960441751065065201d46001012a0798410408c41200d80541c04003201d43d4052020307000c10707110303d22000d42 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 134556124 1250 134554874 134554913
    0x601030209190f0908070317011a0d02040f031505100e060f0d0c060309030207150e010804050a0807060c08071d120f01050703021201081c0f0e03070609170307020d 72
    0x241d00d020794200c10280c41c0191303802c440c903d40002d10340b000e059000041d2040c2d816010700858140d4508241c4804005008404403002c8400192440100a16038122402046c1511030009900d80d2410046098103658254010b407030704045c005055403c61100110075101e80c3c4401c40c49a40b2050240704020311059610b64100c1070b2034002c403000c540c0040d4040c004090716540466a0560707860020b050192640c00710700012600c0c3e000c070301c1440d005041ca00c04007000303190402590752141015890304078640400741140400044035010312541d508214041e0340152983c40060304c510200301c0c1c062070706d204000002c074040362448003189054030b00c001c41484140c0444080d0180300d0110f50071500c0a549100200e640000d41c4010f80708822521801481c44001030003120f48135440e2017440b0001e00d4001010030480e0341842001d903020702040d200c4600c0c040d0481d100d41380c6800d005030001c0041e0245c1100c41d04107010003925964000101c860180c4d000e080c50741d843c20180d0f5200d52100d0807041850 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 134557374 1250 134556124 134556131
    0x8040b07050309130b0f030a0215131e030309060815040203090f010203150a05120709021b100507090902070215030417030702060f0c030717041502040605070c0503060103020919 78
    0xc801e40d45400090203644c119180002d00e0b140c07002d04100181a0b6150454000d802040329400036a441c01210a000000015604d80e15410300414160b070b000f540c0c01c0003107096412031440b000202501c0050702135912035100d00341d80c280c4600d03041c1d81004080329804101d01e2000815001d5040c243c0246800070128004c444501e01e1400399203003680c0007152010454200c04600708040d2030005005802032005455030b850600313041000d15110f80050141e0b54569800042038cc045184100700c440c088040102941e07424803062401401030402621044005003000bd0045a40b0a50380f084ae10500e90023001c0000c4401c40150709003068100820a60382c040812090040502400004612928850303010704181d26101004420059024100c006590018030030030070704d543c204400288648100d2310021907592a49401c200341603400da60284000d00220300010883d8025019120880c420030000906644640926503074000902c8065030002c011004500790010241046221054940011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 134558624 1250 134557374 134557387
    0x31603060506040905151215041a040f17250c12080304060c050a090e130606091401081902010f0302041d09060f01030c06110f06010b09011101050408040b070503 71
    0x1029600280d0144081544070010042c00c0006c541107640640400c46000c500c3e541240710700c6558501740340c02041900c0c5500081818170004d80c0551210702045a84050790340703443d2034150540a104a81150000c048481001d0206840c00513298040c80015143d041c41e000b1611f00040c50841d881d054620707601121010402c00c200c0140040040d01034403a2070340d28286031601c40e0440c0c0d8410a64020850140034444c00268407290103000c482a80b42184416112005005401400b0720310040c00d29280c40c0303000420303a60365000721000d988030076050030550380c0c3c035246d998035151440400d52001070506d80440043d80a0b1403154000c03049482c006003040d49400ca0501c88212141d24006060055400c10010302d000704856603101c00d940c4080714440d450359403410040e406d5801403609000e810440700a4203001048101c00b024100c804a40903541d41c0d020406480c0d00c5541c01c1c600185000b9503401450300140034240c019503103c0d1129147c00e01e0b040d084142a0003520b4100e40d68041001305 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 134559874 1250 134558624 134558629
    0x120a030605060705032718190c0206070f02070b0706050714070501060f1d010302010f03090c0e1008070f0e100506031513091707031806090f1a0316030605 68
    0x18040f41c034071410045559041c0c1d0284140c0c1e03100c90403c0c0c01d5010010f901d01001a4807800006c03040600b071081d50980c03589414142804c1d03818840a0410707a54a040c48034028030b03900042031405280140c54101044518030001ca8850b44c0ca80104403030500c04100c22400140c440e4021503100d411381c60f1807066070706180c3e403522180c2d00424007603071940e440e86000d010201c040d601d81c400900003400075460414440000f58818581480084e06000d0b280d00c6142c2010700a0b08404145503011945502d0184c441c1e28024100c0c0007600c5003520502c1c2c1c50300204007000001400c800f52034081401c4070600b0329280034580d881000604030700150055520005498440a02a41c020460342c1d40e0400d56210074070612800400c1491a0f005641c1031000f000042545280c00b00340c511020b440d0503980b41c05900701a074203540b603009a8800c1d114511000120264000789400969152581e0941d40c5030341e139509000403c84d00c981c02e503111442040803a040e0450b024450502804606000c40c04c0f4703594200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 134561124 1250 134559874 134559877
    0x20d0203120706050f0103030c0b0a0605040204081c020f150603100c0509100207060e060d02070206030708011503050103020f0603061f0201020a030e01090c051c02030d0c03030e010e120a03060506 86
    0x1100746521101141190401415008042d4480f4020904100035891070f10020f100d02c0c00c141010f080d072002000411005041604503a010300809801555216640d0403200da031050703514123500c011035041441c010f40170f101080341c40c9078004903c0241200508030041d00f400b050050540755152003050001681800e01c0c0c040c0c0c07a1070384020f844050301c03010303000c2c24095400e411842c250b04541000f8024050b5540241c484038802c00305440fa07a40301c408061284009105158001e94460b6010042003111603022049070306903400700301c4449404590b9007069066032000c0c0002503200b429420502220b04003034000d1a44070100425005860018808154420700c6000c1c0c0040185d40000700144031541600404100c0c01c0390704003c000100c01a110b20068603400d004130361080142010480440120524511442c2d400071300741c0303401d44110f541c00380141c2038000301180424248550f8094802061050f0701760201c640740908141c01d601d00d010807090b4041180c1da014595244030200c1c1070b445540 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 134562374 1250 134561124 134561143
    0xc04260604060e160e07050c0703050f0706020d0309051c02010912030e071715070504091109090903030601120209060d051303031506091406040b0a09090b040207031b020d0203 77
    0x3000000c4000c42041024100084000003903088084050104200c5d044100e685500000c941790081d10741c00c4494159042460381c1d80b0141c404d20482483c600d6181000c101381e022941e4640031074048805c43c5030160252100900c001d801c07a00154441c15454401d1480b103141c0034002d10001071440d0650341c0c2c2c3c444210300c44d94120006a0b440e841110034803010491080a00041c000c40030f0860f4030061080e0780e60503508680c162200e075440100e03002a00a81c2650090a014030080c407920013800805903441e000044064420b85140c80070036031055020044a000d1041070350388000740001a5105006980401e400300c2d00144108a1400b200d04944140d50107080030034250400c12005050003001d40e44101c0c5007248009503040100100c0350001861000c4072035600000e00707544030200004800c1d000d02c1d03000d0a2100b03c00111106603079404107820003070700d42e860010011540410300340012800703400320080200c0c43c00f01c0015400006003065180c440d2000341b452150440950200b4240020203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 134563624 1250 134562374 134562383
    0xb15060c0c010905010e0f0d020d020904060b040b01050a080f15030a0b011404020301060f081009180210050309120c010605060406020f1b1c060605060a020703020112050c04260604 79
    0x45150324165a4808403503401040300b403921028500e10382000507c1540014021031003522403464038000c54a403401d071040342c41d80003004040c0c81e190070f0600c280600080752400c0c0c03003a80307001c1030000c4940c0030341c0544110380034540c1c1e400a15600c2c00341480301900302500f00c10150303402640d0001103550801c41451514845d4643c144075514001e040e000e8180c024000713500c510300620052082d1a44403450040501151404441d80c2c0caa20491544541054100e6091241041d03d0418104402c01c107610b0b0080c0f080e65190a00c120f60a000c449502080d15032102540000982d040c02e0402d03e0054091200c105000103541c907941c4d07001840c2a8001c1e4412030160300704004016918405002080e0f079071544005401c2614922000221012080e50614403a11202d800f0781c410702c9140e80c0a807022308400380480b40d480c14413802c003950f074944a01c03049002800c6980e0b4181b1090711402414050301d00d50031024205801c0030741e2401c60400d00000654072041c0c074105003504e40020000713640294000d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 134564874 1250 134563624 134563633
    0x503100608071a0a0522061d0d0c0501050904021b0d120605010e121c200106050604090b030f0307060b18070c1b0f09050a15120b15060c 60
    0x41101c2030342070082d280d0101d080c09115a08203030501403007204a5907035030450301e00941e44180c0030a0f00094100c217103092107118240c2980202d0b0b07881d040b030300c00300c0b10003501259280001511010000c050706511002002c00000400801c00303075000d0030140492000c001e10140c1044068040c1d41c1e400c080c484000240c5501a103070484c05181c11560281030401c0e44101070080310700f0000043c000a0f94404075034000d1681d00c4400503a48000d01018102c0e00701085000505191071030001c0c4000b40340300c84982c0c44102da00700e880500384144158000c032031014000c103007450300e00060b40c0e00520144090507058040c2903c2c0c0c54110400740010118280700703510000b42001003500b400007281a01004002c003420741d030140040306410000651519030b120710020300c4003e074507000540400040e485208250064000468840c400340c0250b80300380c006000811102c083c46200c1601981c40c1d00c1004040c0d01166880c1c00404c450325482948981003564032441441107801145032034cc00b01c00702d40504d422 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 134566124 1250 134564874 134564879
    0x5150109081203040f0303020705030c010b040b040e0717030705030a120b040e1914010f051f0612091a040f02040524090402180c03040c080307150c020705031006 71
    0x30403402a10160078490010454000c00952052003403002410161034034600590010806220350110ba03201903120341034a07154511010010b000e420742c0d515042c07040d410041029014203051003100e9209800200034192103140024401c100640320203440c11901040102038007080e410001440e84031301035030300c044410034002300d804101c60131070389601d10031401c00c1b00c1042e807080700080807100003440526420000d01a031038a5a4514a814a4551706500384081c0c2d070788041895000c0380c480e040221031140742c1c00d030707014007807845070910300810340400c44088902180014590007400c005104a01f006030810380010015284003088408840001844a082c2d0440c1428040c4a030080c00500c0352100e8803801030342400100c1034401485000314100c1e0001004c4d5a50703c804040800050744044c20141440f4600c0748250303000303c40035241c901d0700b40c4001508101c00012249034035007012244407003081803840720f0043c0240d200134208501c034508003c94030b076030f06001483c0d500d0303020076001400070f2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 134567374 1250 134566124 134566127
    0xa080106140703090b09010c05010e10050907050d080d0b0910080d0206010807090213050402121015080a020a0e0a0e0106090902030c0a210e210304050705040b06040306051501 77
    0x4075103040c081420800b0300c11000029044815072080c0c421000180d616000a20012120000c0803a405006582403501003441010041504400d031012000140701a41c3c0b05014180d030f850480c81560303001005214030b00302007100079016041940c801e01e004511014060005910184182d030301e0030b06068440420000344508118800c2c0084680c00a00159850003c03880d407200303a240304000c03140741c000984036468413001c008400544002041152180d8030314034074100081044805c440103a0ad00b05002c26040440325480c644d0958542c1d410b0701d580c0d01c509003100603400c550001801d0103122210340c060b981c3e030080398401400910902007015890407000501340103481d80b0070381c0001c0c070401c00d205021600d1000c6404001103400e042c038180c800303108132000302440c041c50441a80e06c0d0514403201200f0124100b040480ca000500c1e02402600d0800e41c202d2105a800034100c1d808914104203c1c14141c020700701c8118010480d90074540c0c0d07601c540c401d0307410407200440c91002d819034108596 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 134568624 1250 134567374 134567387
    0x5010810050a0b010c020f01020f03040f1401050403050a02010e0a05090910051e0406200301030503130f180c050f070302010207141606120603140604050106090527010f020a080106 79
    0x10007282c1440100850b00c00030b84180d28a05000c0d0150a030013000d03034540d9000300204804190210100c07036030b0766542c41c100c2c0c030040e0b100d0043e0701e85007403000710804241d84684255415250070002400d01d80003a90300648650740399110f000e80040d03888100007055a40c0000c802d1166a4441c00781c0500c0b2680450032045a4006203030140c40c11152198000d584100c003102c590103a88000001000d81c10b804d030004540c0e030113142d030074940700c4008000302c00c022012001d840307405010311106203460b40328400d1100c09410307070244013500b44240c480402c400400f60440f10120341c141c01c20500d440b8000d0401c4801c0d920810065004d81c2d00052400304111411600e240c0901062014050700b120b1441c00c800003c065105110801c0811003005c075911949510180c0103603800740c00c031120000c69900007926000d0031141030b12694070302031001602e8149406028480c041c015414121213a204000d10141440b1140c8112150340c2c540c510122030f0500d10003004d000c2680c2e120a220782d0302d0000002c095 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 134569874 1250 134568624 134568631
    0xa03050a0501060c02010c050a05060c040602070e0609130201090b0328020405030303131e03110c030a03090603020d060b0d0e191203110c06012301050403110405060607060501081005 80
    0x2900c1c0380c00d00400c0410b0f030001140146560900e08081ea0307098904046143c42050318014089000c2d010031701c10b601c4c42d84402401100e166400740d554540c1d5a2180004c3d403035080340d45a803c124858001240707003401c7c06003081300c60301c1410303c0900e46d501c400c011070f5a900119a6560151400345003100d0104928030078a034090a02d02c8158902030078000030a4a03408003420306403c83c542131501c8800c2020a0f040000c0005040780401c1000b40c16007001411401c1502448a00f8021810381c260541804504464002d402d510703110101440c0c031108a00a50002d007000060039500ea2300895040920f400500c070307005810343d010860000c0802440d080070804681e44203030712049000400045d444c59001a80408981400030b900045840b48014a1140c200140c102d8041c038400414420820600071051820142d426004d60b2402001034607148240d01010b02007000150000740d0500d4607030400d5901c608042c0c5000d08026240e61010140c580a0300803075155001242d03004401c14107403044551 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 134571124 1250 134569874 134569891
    0x2d0b1005130504050304030303180b0405010b01110114010303050a030b0301180b090312040b070e030313030302010c0e0105030a05090c030a03080a0c03090803180f150103020a0f08120c01060b0a050a0305 89
    0x40c00c02d07550304d039580e1099200007414540c403204da0071414100c151500c00c0058121484540310300e06440c4c59402800d14942d02d034003140300c0200021044c0d02c14071030203180029502e100a066401d644064403250401c101400406071102c100e040561028040d40f882c4850407040340d015400585418056220028500f900b0399105003e681c1026035220800c1d60480e07000001101035450f440411200c1011442c002a0544800691130441d80c454107500c41c1120300a500800540014400c110b0303604000c084102d00051040c400704440f98080e510258000d41400201c80340c0300c50f441d011034140700d110390050707003c100000c0c00c1103c540e08074043d01280c002e2500c0c0411000c2420303a903401407400050061b004950001041c4600031001b04020700711440350600304c0d01701c140030a130580b448100c2404100d02943c004040040c0c2007600c02e5040c411384038080094038090103158681c81c51508070f540703140d41d203649a981c002181385c50600140f0040a155aa0564400d19580041c00341c030400b0300b0220 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 134572374 1250 134571124 134571131
    0x406080c1e03060106030b03010b09010b180a1409060409050708100608010c050d05070e1306080c040e060601140d14090d090b0a1809020313120c2d0b100513 69
    0x40580d800f14910781901c080b07007000240c3c50b942d20042030052841402854100a48030004107100c020300000d4503405003a01c0411245146503410322903208014420072110401c0a2000c03191890003031900c0b5032001c805000051810a1030301e40c223286c8851580010003542100c0c0e004c1d1951a400c0c09a5006400c464000740885d5046000c02800341c401c10080d542c0060355140070030800c0c0d101d80d90719900c01c040201a066090209041d1a005181922a801c02403144042110440c1024040d1110200702600501b90580d2100b0040d0758101c4803086103108000c3c01c101e004035082c00c921500c0d014810b030070140161071604002d0300e883c16440e03c001d002841103000d0700b003080d50a840210b4024105c1e51406900c9003600d10024102e81743e0300d0300001440790003c0200074103088910403180350382c1d00440745240d91094812080d00d00c00150704020700b04c40c035051900084c5401c070002d0f007500e010f0f803500c00c80c2c0311120584414a5050058440c50054400810100043d00e441c40725454011700100082 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 134573624 1250 134572374 134572429
    0x3071803050616050c0d050408101404170f0a020601050f030303040b04060b120714030706080c03040303050c071415090313050904020f15030f0a0203040201050a110c0406080c 77
    0x1694078030005101a1000300000440f00d45644100300b6240c1c030f074807004c08581442c028200054090b8100f40079500d000c0c41a41800990600c0f64010342040300c1c900c0b10f0500040d200c0b43c0310201c8c410745a803801d1130390f23107010400c40207119144001001c4403d2190f0151009504150401c8241864500440d03c03c1e40180280b00100f414600c685401a5000c1ca000400c2130383d440205088030380b07401407640c5500644800003010646001e1014030050114140c0d0803168031001c066800350310039500c001c0d1030b400c140300240005e0b020381c0c020742d007010000c0111800e0114a40c0d41c3c030304500e1007521a4407150455418031502c44094074080c1c1d04000d04102541c14241e0318802c0100e4069540700e0584103002420204055459042c6100760a100250644c0f10914500e105040d10f13500c1952600c1c168404040000c8100000344242c07400717254165940c0d490440c0d071b1079044880c00300102c2030391070318051191010401c1d9914810080100000000340c01c1e1400c8010411000510390804024a251280040b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 134574874 1250 134573624 134573633
    0x6070c020108361005010e0c0a0503060411042c061e0d230c04090b060f01090b040609180203040b0117010213060504170c0f01300203071803 62
    0x100b550001946082c04680640b00c1220954050000d20401544005240280f0401004601030018990001c000d22251341c0e02c1012010100084806503264501445903100092040b002140c00040c005c0010440300e1908240d85500e034820f5101b0311f14210707030280c066a12031498003490710a821820754a815072070460b02044189191041c1d840c2124409001d500d800d40d65501d003080d02e541c0007021072900007240740c20b4000c00c401c1e0700000d80161056882d4013000b8a054052000b207107900440a280e5900c035035003441440d0302841d600a06020360b0310b00214090402002034001001a42d03a03011013203140c065605115100ea41c0e030301d107025004008001c003055407100c440741114000040c80403016482d0541a00a00030408003a900140100c000150582e101d0301030425600301502880020074000f02441c1d803000c1c01100a81c1019044d111452a1340c09032141e4a0411408054201e011400d00d1070342504680a01c0401029540481400704d035a60009003140303c0809003070903002a40c1103445 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 134576124 1250 134574874 134574887
    0x60e0909070f1206020d110406110d0c0605151302041404061208070201050c0d08040c06020f1002031009050109060e060d03020309091e390702060a05070b0f0906070c0201 75
    0x43d00c050020f0021141003000005d504492090241303810030446242d810604240c0c592144c441c101c00200080c100c0e440d0404003140403402042d140e01c0e0400c1d9003030789130398440140100501b00c3d051130700386080d01e2802d5100e4158014004810190059550b8241241c5010105001142e81d0042d03180401c00d00c10418448178071400a0b82007090b150b140e0045100481d01e40c41034030604122130044040b0940b10a401c800c69600803072084401d4610141c40c1c100c120ba80322206144010b8a0b8004980240d0030001a030055401a280c00960b206054407040c110060780c01c203034090a2000c5e640c180800250015804840d000b06007254080d4912905840095480c003506401c02c2c400d5220030302180d951000b02d1801c04080e580d03488000300c5850201d0086031400b0040103409034039a032688022136425800b1840a040389440c1044606010320780e0203110030390b00151328100034004100601400324000481851051181c0050300801d840d003140c100303081c00e0b0090402e07014001d04406810050ba000304 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 134577374 1250 134576124 134576129
    0x70b180304032f0a08060106090614030a0c0504050402130806100308071106040527180718020d0509100605061204030c020a0e0106030c0905090c1c02040906060e0909070f 75
    0x1101031001040d5101400100810700c9110356000c4c41400d00020f0408010520354121070a41c3c664540880da5240b05846e0240e50380c441101402003000010700920099000002e90203e92500900f069110b0740031400700e23840008038200f880702252040009290030400c1560107000d801c482d41225186a071904010b0007006030080c202c50002940c007089494603003c1d18010b0400a18102585030700084c0c2d014802141e900504814115100080488540d2040784103180c50040c010400c0e07500c3c12105a400c000910304806105030204500203c1c020180501d0b4000c116500140c20011400e66921040360f809070b001a0088006000007070580c0c003050303030b107030740c405e40604240c803030684288000390729003203030f50400c01d0f482c0090000850100d915034041c80b580b482c0b603120000417a88417410040d40d0402100c0050445000b00401070b501c00c60000d082021448140c0050b040c15191b1010318190340780c40c0c1084000030186a1900c1041c0750840310103401000901c09001490f0400d5000b80d01c80d81c850 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 134578624 1250 134577374 134577413
    0x1407050403050c03160612020c0706030606020c1e010302090102010e0d02010605030613030806040906091208220b0103110d1a0a0507050c0703122609010c1e030917070b18030403 78
    0x47d40c40c0c140440c1c80341c0440324041501c81c207035041152148406401441e0500503000144601c00d0041c98908158000e210310b03150340685646503031400c1d00114080e50040761007138110354980d0711500313001c88108000c111008817034001007006414001494904003004006180030b003503031819540402d400001d501d070041000d40740428040f4a508100000e410807540040108510316640c1c0d900e1540304025038020304d500101c0700316003520741c0b15030030162524160141500d942540100300103040b0200885200c0740181001348804441d032100300805440500c0b18007006801d900708404450203104055004c0980c1c00e066041950615002e5615003050100034222143c5021a10f0424010710328080c05580360b0079000c0e44050103440400c1c40305801daa0a2495600307040300e981c0d04502500d112105081031054441c0f40710548907049000d020680003d4400040c180c01e00207445440b04e004010007405900241240d040070940000041030024140c82150418401800020490b5a04c0e601c41c1514 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 134579874 1250 134578624 134578637
    0x70c050411070203060412030e030c07090c0908102712111f09060f02040b0319090609110a050a060c080f090405091b090708010306020d1407050403050c031606 70
    0x60320700c000d050700c40e00c00c01950503c1190200700411000f080034800000459500307000e0603406a070416500c0c050009220301c1030f00804811300440001c0d601c096086884c92400c1e1420990b5a030110f410665042c810244241c0ca41d0705040703c02811500551001140c074940e81d40c0c0c885540c983ea2140c801d50002d1000300501007102041c0254104407924565201305c0d0740f44c05000003000600f008094203901120018200392119152103024400d9a08a0700380034401031455443d50549aa505400c0f06605c1d100e951300e902140c08941d051041c1c03405c00384200c1004515080c55410070151500360f5010078824800140d040c000c00f0707805445101e51540c045136840d2070b12401d052000c6540126410b10390000d14150401c100e40c0e2000503420491000c40052607400d101e02010f1004000701180c144000c285441e00410004846900400e00340241140014001149030044007030650140c0d02080010303070108090007801014448000c0d00c0134110f004000c0302d43c88d903c601c2d80b10149446000e050100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 134581124 1250 134579874 134579891
    0x50d0b040209120f010c0804081614160e01171c0309171210080705040c050d0c02150705040f14030a02210d1112030618040c030c060305060a03110103090212150c070c0504 75
    0x60318000a03841100c1603054404c0c40c498010cd17240041e8991066003a881071010000880702d0458402e40c9030f038494103019160303c2d00030b02801300e059a80c842e040c00806d80c1d100007500c04100c0ba20030325800c0304c1d00e102c4800e0751103074120005c082c0894003400039060038070000301c208415240041d0f400120b410503500403d4000d400c0c030b01a503c0d4000e038814009180c1c00e01e26120340647c2e02094111441d4503c0013a072078140c070b403c5001c80e000d002c2c6009003200c6012480d014801c20034494031000c5042d034020110f0b0004c00490703003c6007424001000190442c13500302c00312010098148a402e00e80802c0d4582445615140502c0f035554010000e090140180000042944ca4940080c0342e036030002034180765401d5082c145451512003007648000c0d10075001000c008904070344240591809610001d000340e0170b081c1541c5500c420b20160070725030380c14580e5414a51006840300c041c40e201c007245200c042c0c102000348204040340718000801441c00410104050400240c00000660030744405950010300354a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 134582374 1250 134581124 134581133
    0x10b0307091e0f0b190806070e060d020a020601080c03010e1506060405100203120a050712050c0c070311090a0902060412290703110307050d0b040209120f010c08040816 74
    0x101c4101601e0116420940c00403000d002030313013026004450130b0343c4441030746130f5268164200303203120f001d21103003a04a00c000c544242d101d4030031144c1c00342001f801c0524191920440300c00f00d078849003080c80541c01a03401085403074814071070030f00020800d070f0082c0030f004040321041391100004909200c0140c1018003241c1543c440b072040e100503190151510940800181c0702a680360000c1d1030204401090900268040c11a40078850003000541c8407041214004002c003005448000c2101030692818080200503010401a4900075070240c0c80340c1e015400ca00d018080700d070300000d000d1410a03051914140050315550200c1d41100e00130284501d030300c2450325003100b0301c10b1003401d60010005040d8081e9820003013807161a00668007910300304002041c5050b81c2071280021034100c0301040041c44103120031f91607504441c0580c8001440180303003100042c00103034665102d012181c095480300c804468081c03001d2144100c44941428000d4151405a84202403881100840c0309921081c000010800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 134583624 1250 134582374 134582411
    0x1052a010b090906010f091a100c0605010b0703020105090f030a0c0302010f02030403030f1404170d0b0901031211011a01030b0105070606170c090f0402040c05120c041502010b030709 80
    0x1c030030040a0326003a003000c2c240340c3d075a004203000320703540b0b442c10040005520384144070303100708041c02600d040d005500501c01c02400c1c907000c030480c0082c001c42c070b401000001c40510405010342a0000340b152140704a040003821150010500d019560000c07001007104400003003079840110341840c145039460841d00e812409040d040150008160000c82031108141d00768021020440c88a107041080507112130060940c45030907074000d00704007014013000e44482903400081a03002240d00c0b02203403803070445010450790300090b881907652400d20541100c0180d807050068403801c09510092102005c5488152605000c0d035641a041c50b0740c400d9075440d076034015001c0c4c80d180c0d41c1002080250560300d1461001008580d44090400d00943c0303030a05040c6050405180540c1d00d040420300f156482d6070074803004200011800040c0142032001e90041c0d500c40090611801013071700f5080d10b031442d0551144407d61449541e00a690610111410b9920b0004045045851030140450413204600864414 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 134584874 1250 134583624 134583641
    0xf03131a040b190e03010c09090e1e100b09010b0a03050a240303080c040f051504170f120c10050a0f020c061005010903050d0503072a1101052a01 64
    0x581404070f03604040c070400c064098440381030f6480300d11510041000301800c855103555500c002c204040024010140c9940c8400e0302010840d04490b40c00c5aa41c440600e42c440b802e074010341d45c0d40449031842d6070506034050140400015203d00a455060008842481c0a482c0b994802c00d071f0380f000041c103176060076001b182000100303440307023161248071000c548802240c0d4001500450a2640401e03c95050041120110303290414500c0410303007084200321403c0c10800e184a003040c401d001c0800c0e000303200060300040f0000280103040303030f282d0560181d0a0494190541605020901c404107030140b01068500c80300c0c10740b400000e4a0fa031021219402031a8280248001d10320101e40780005003000650035029a021040c5800b1140d695001121040c0e01c2c2c1c00000e049030490b48200175000c0c00794000d5500090203052490b02c02109803008105111040c40e00e5205003c2d000c00741d005d002d560075440c5c07440407007031134240e1a05241001260142040682c090411403ca45034440088001c0d80281003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 134586124 1250 134584874 134584889
    0x90312010303020c090709050607060905010917030121030804060209011809060806010821030c160f020f0f030303011502070b03090c01021e0606060702190608090f03131a04 76
    0x1540c49040013561603584200340e034010a0361001003407100b03014038040b0702141d80c0105401c0c504041d582d107110151602d000122060340d03d17445000001031010080203140304011084076101d624042c0044854841039280c02e81900681d0607500100390300150300b580c441c2d005100980d07110041001281c1c001d05c0028110912524400d01060b8504543c0002046070241c104a484603600c600c900ca031105a100000c601c07241000c043c14100301300b64000746621203000580b00d401c00c5841083c000404031003100441c4c007001045030703110440c6010000c0b1282040b0550304507183c43d40d02c50211b66a44018010110088004145031010340d20800c0340c0341c094856808000d44a041824449940e000d02c00545405070145012034107403003110b0000d5181d0005402d0003000141c0310b000600409600400382070f0f810003550030491a900220b900d40701d00412607070741c52a036140760a4203d1410038a21043d080100c0e00200075085004494602000a070340d07199000e02000d02e030f2650100c80c5881035910095 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 134587374 1250 134586124 134586157
    0x309020612180c150412031404080c09011e030b09030409140f0c2106040e030703020d0212040f050f040905060106090501090b0406080a0504060e0a0803040c0b030702060f0903 77
    0x4000b200c2c0303039070101c0c1440900040b070380c040c1d07070312410000300d13605180c0c070250081814081000741002103048006194041d040c1880c10b05060002404198001c1d042543c203036209030b508600390304180d070728140140313500b81c0202c100080703121a0f51510190362101a240580c0100030402001c2c09000300c4004200101007048100704100c043c030200901113411b0503240c0f135981c00250038143c0e010201d98103c0d40419910721301660100d040312000c1000b5040c550044c0e5580e03090102c1070000c10052420b18082c0e0020f00a0a01400c0b0003482c2484099a00c01c2c01903061000304010300c02044651b040c2c4008490784062000c4403400308005000c0c281005d40a0f1151000010304580c101d450081921000e9850200182d102c158075202d038481ca120b4900022031400016110104550146401c94030515012541800c0205207528110b10f084040d1000b0360000140010410340210340030007000c00c030990a055207448a0065194000201405e4910b4040000507910f560144116010400009101c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 134588624 1250 134587374 134587381
    0x9010e010c03110109060f0b03010605180717040302010e07081209060d150b04030620121308040b0a0809070308040605160209100603050f0603071206020705010509060403170c09010309020612 84
    0x7101400400c4c41f001304051174400030080500341809040259030028141c00e150b644003a01d601c0c032031349000f4426010004d2445489120707800c5c21318841d00642c002c1d400442c0d41d814804180b814903a0b02c0e40801283d5005410340c003010490341007030703d5900104a94294031541c400c01044050010300c0807050698008000c0455041c400d0340c040c100340ca00580c1c0c2007000c4207141c140601c00581032055174140c00c2050050604140c0303e031125650115a280749400b120446941f140c00c0b58101380c0002c001c4500c041800300410f540702030256400046003004105243c07544d10303000c1e1a0320590040c0d000b00f01000607100700c14680701482c40704269002d0040c0c0983c1c903110a01c3c038112603140c001e07400080d082201140d5215038000d001e80c007907180180a015a0751410349403074040c52000004443d440e03004d100b5480411020700c9000d00c42d8209401800840c94103240081608a500001c200c1d21442c403410300c20851111000c6c0c5032403582c00e080010b2180541d00000341e040c094988030308a19107024080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 134589874 1250 134588624 134588633
    0xc1308030f0c190c05040e0a05010507080610090e072703030807030f1515140d0c0908060c0a1b060c0309170405030c0621010b03010e01090209010e010c03110109 71
    0x2c0c0b4200000310140c50010380b00c0d400001554901c02d4001d0a0302d440031505020710b207050f52080d484503000c502290000c0c0c103035503103003800e44c0c0c4112410b030085054441005a00d061a82603011000f03954505031158034202070401c4080c580143c000020003a00c0c00d018140e07180d10401c5200d038281209414000540d27285401800711000b100e100000a08002043d0030b04031090048681110345100c0403540c150800c2c0f503141c0c0c5204120219400c00c000b03002c4a1040303074259070050004054040000c11507440c030a10140c038035241680a55090f07030200e420841180a40c40580d1011700581c40c0c1405001c01d204908021000107107400350580d031030407000b1000c40d034143c0d100da0381c1c0070b1080c142000070400c1c0a0100e02c0f036011f58860305825170045071321481039140200040031851061003a80005108081c0c40984250098001c20300c0c0c10000001442000c41880f015401810898000c0d8600320030000020003155500710194144140b03c1660020180034001c5603100906e084000c2188058070b041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 134591124 1250 134589874 134589877
    0x180d05030715060603020c03180109091e14071d06070210031a0f0a060819090f030e03030301121520070c0e040507030b090a05060106050a0206100303080c1308030f 72
    0xb500511545052000981540039000341c034000100c04001d1410280888455040e40c40c81c600610b040240c105004104000700e44140c00c00b820710700190105000300c5100d01e404413080c40d1180300311000b6100c200030303076550302c0b5a0010100c3c5071110014108001d40c00070030044d00030444020f5100751281c80700c0099070b50580c030810921404c1880c1080300340440081c0040410304480c0b483d004081284240404c900030380c0303125084000b200405d49144001e95003c412141542c104071464180014400140b41d40075010502024007100034602c0c0d03500d4104090070064040500500c02d0180041d07069141c0003552103003002480695402c054406880d007104583e0348140e500f02d8502d1890040403410000901e40380744034562041c01403404500f542c031140e5079005d004140c0e40007442866400400078409005803402440756807580b42d2140c01b03e9801070b0608400825105c210400d0352400c201095201d44d1403501700c41d4100c8010754032501070010184401c0550000c0c000c900c030000350b01820320090740 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 134592374 1250 134591124 134591153
    0x3010f0203071e0f18050a1509060513030b150406090b0a080303010e06010c08041e0302120c0d030806030120040603050714220e07030f0608070b180d050307 69
    0x340c0b40a02624844035000c80021003d103803800143d202e2000040c00e9000d40c04010001405100d9140b0703495841000400ca60015009110031080c4880d41000907604104c2d020f001d031070781d41002824407080030a0b1600c800403500c000b80190b81600003149040210071516024805d01410501409440358001e00151140d4107010340100c031414400074854a004c42520b0580f29111104042030f12050011920000c04003400c4d143d2103010480000d000030380c1c8402c409880842c120785030216113940100000da88000641c500c030760300301c1c25240601ea61002d0b031600300c107a4142003016850721101c0102c1d00604540b480215a0040d200d00341c00c2c0420703008090300450708680d03020b100503681c8400844500911510b0b0401050050000fa089400c004c4441964405441c218030302c00faa8442851507140307026101000425559180f07800d0707000e04d602540d00542400e400420603d4580030b0303d2145d5105460245095203502c0c40c42280c940d49400514824a0300310044984441490030070060742da103000f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 134593624 1250 134592374 134592377
    0x40c05090105040207150c051611040b040e032a0a0303021b01020702010206072105190f0608070506090607060203090d0806030c090c030a06051c0203010b0604051507060b03010f020307 81
    0x18603403805008417034081340d01c0000c0c005080502c40c5284058051034409030103022051040a140b41580301c0c408000b01d0082ca10a0200984a4184030842e030310030040c1340c00355003040155010390b0300000461700b201190503540024400790380d050700030030ba42142c0000c0c1140031307840c41034060540c03617005065031005c1c1401c05a0108948034a041c00c0344511306009016811400005030082d00800650404910204c0c2040045902011000403200c1c00c40f0000085212344a03248012240383c4540200c48410010810010303007002a11035682095105c0d041c42650001001d50301c54640c8404d03210815444401503480c1c0c100345820300c0d2160071007581da40009a05000244061034005610006032101814807809511404034000540c0c0c00284a592181e0701c5032000a0185c81d10005e195000c814051000c0d10101944100340c00d44440d01c000d80e210b1981440b043c1700c541c0c4c80c0300e9941d03541d001800c0c0490340d40340c1c00c0c546800500300f50100260305510b0141844410482e0341c00462080b15035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 134594874 1250 134593624 134593639
    0xc0a0909170c0a0b041403070f112409150c0102040611011e09051c09080d051806091302030106120c2d02010e0703150509030a020a0609020612040c05 66
    0x10842049090045142e840c1c603581c8006210000301d850110a182c0040c0030b242ea500c82c1500c1c0003202031940d84560300807074594401c6e103450018003403010441e004410702110604880c180c00b08082c1d410100d140c02c20303081d04000041180803a602e032800030b045041d0024450b0344070922020030074002e4005101d14070114443c84460011550184581c0070000c04002200c02c040f03121500c1c50005202c184000c032414891201410728203c614004801c0c20001c540e2901ea110781448045401e0851202c075050078400705004000030041d0301a5003030400781040c0d69298641a01c4000590b90040300c0041e076135143c0c800800030035002e45c880100c0d00301400c440000d00c01c0c0f0714410022641158484031601d980032040c000684143c030102d82c0156110300b540b001080003408050f1503810641143d00480d44030750504400c00403640e0a0003040e900c5000040a9030810358404030113507e03810500d00080c90300d17075150450000c42d500d11003910381d086400181d148a9280924050400c8003042c00313014400d0300e1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 134596124 1250 134594874 134594903
    0x90901150b0705190204020d090b06040c110a020904050715030c1b08120c090402040806100503010b15030405070906140310290402040314060411030316080a020c0a0909 74
    0x1410440704103650140c001c040c00004d00c02c45501c0c00c400c44104a070300c01e40801214140d164240107800101e1700840b2610707240c0c2009001c100446034405074043c10f014180442094901c004039800c000c5a805a030140740c10f940301e1034450f080c013030550404240c074059224810200b980c0b66004155062203501c03142641781044944440e107401c80f2000070b091140c200302100d510b044c0d1003000341c2c1100c030320002d413424801d400c80040c0a9030416004805154004020002000c0c02c124500d801418280c000f0400c0d4250b00002c80c211510f032051400b0054000404941081010041c0d523000303024025080000d551510a41e8299004030b44400784284a81c0b42c5100d041d48451040e40703a00030380c0c00c411202000c06482c803a00482c1004040710381c071980c2808000301113940d2050f0b0b206841c0c045805044149010f00c0c1c03c6880346080303100c0901a80c428007142d448454200c40c0341041c0341e0051001c50b140c01c001d00c0d00f24a0042088800c40c1c00c8021540c0c0001c90300000c0d0040501076204c0c0056a003140c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 134597374 1250 134596124 134596139
    0x50109262b140711062d12010b120718050a06050706050702070f1413051008060907150809011b031b020c0a150c0c0f030b010512060703180209090115 66
    0x11644040c04d42c0200d507502000b189803950003004100d03503180c00c51000501d0f007801105401c0030440440d408071000520000039101d1000120f01600c0c240740000c0c10701c0304c406c4840c400a03030003c0080040c055444280c280d1141003512050040070010203025500c0d440c0c80b1300a18a402440040341d48504190220b040c4078000300d140782c15074269240011103a4603011303424030088680080e954101700300a0381018506c00900400d441840c0c03030a00610190b10303008000d45031107001800f101c1d0640002c1c1c014842c0e00807070442c40c02580c0161902c2c0c5826241c020f00c1c640140400a41502a1a54101d400e5540c682641010050b808800c1151440505091013662280c203e10442e42d84100c0d483d04c01c0c0000c0c6400001d0344100a9645842181c0c01000c1d40e078840f5018280d00001c40c0e4040c21801001040303030070f640f0503014080a0341c3c441d500205425015a030b4030006052030042c107840e00740c4069a5040ca40401c1031580e0024488090781c10b05080c0c640c000d04001d428075810410070780006c00d801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 134598624 1250 134597374 134597377
    0x203041a1e0403050d0603150207030f0503010b0409150803030a0903180e040b04061103010f0510090b070605060619030f060608060a0605090307030f060c0207050109262b14 76
    0x32918030740c002819540c99600701c0305540409108500d417a558040031020603820381400f14034840c554401695044142806080c3c40c0010100408111007040103011041c0c60300141d40032070b44588004542208590201e0b11114055080980e082c400801007002c035801680003100c0c05800790f25040c80044c01c203064443d50440600460714104080070120340082c1503002001c3d449400b5000002d0401c0c459603606100354000c0c4e010059007200ca01c002c1c0024600803101881e61412030800d03d032850b1802c14404464054844058440c03903032000007801d2500c80f40215141190960810260385240c6070340a030040103031118003800207140050205100e4080e412482c05108001c00c0420354500d0514101c4099105000c96034041c00303108400000140c034030121220180c451007021402c4988ad5900a144c2a042c7d440181008480041000b080d1140b0015000c80204080321201800340701142d60f10300015006050b45e400307240b452000050342c00191046080b210313551004000c2e0040c841e4010035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 134599874 1250 134598624 134598661
    0x105030c18090109020307030311010f15060e030111030703020c0601080109020603061201180308040303050a0c27030804030b06031b03070e090c030a03091a0c1c0908010203041a 78
    0x12101000c88109203411240042e03002c00d02c0c00010815a41960101c0d041c004254800c6010510185455080e030360203000d440c0c0c0e5032150800400604000010012000600748220706c2445001514140f8940b42034001105401003160a66070b43c0c00d20b8000107009501109032991580541c0001255019040c0290608150010700c0142561030f11400c2224145103c085074050303668070a40e500b2081801c051300d0b846103000707480d8012246414207020b42034900c020010355807107242c0416244012381100800307100d00000a01c2c2200d451106050002d00d0010340c0010341500808100002046030b004a09032260505500796140c07801503410a814a401d41d00c11580d168102c0c4000b4021021000c00240e4400302940c00c0b00d0070b00c1c0c481c10100703041010019090b4009904c80d00d0900c03c1c540c42c0e41d05080404d610800091510b9610000c4903280c40e00403100303400024510300040b07882e51103060310350701405164000719960b04007440d012007100d1b9000100341c0b9014a040000300c91203e60080041d5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 134601124 1250 134599874 134599879
    0x50f011410060c02060a20010501030b060a06080613051e240d03091503020403120309050f212208010605090a020c030901080402060f04120209090109080d0b010c080a170105030c 78
    0x60401b00c1d94180c40907460041c924641c900180540381c65108240038103402940100c503480220b003014000d004690010303400400901244006105090312035000c030302851201640002004d032070b20014400c00450021480303d160300300009012840e80c45440c1304611250080030035500d10140c00603c2001c00700008040c0124bc03400008120032500c1a02450100c01c035890300500c1e143d101c0d81d420b05000e0303030038010200107a03407440c149082100410480300d100e100704c0000e109a1844803c168090b1594402e0b0391030060b40890494010046a8042911200094401c1c4071050b00c8003296070007028980700b181c1c4640c07010b20200704180c12034400c64080c41300c0c281c007031450000000300545003410003034070882e0840400c0102540703403000a8080c00c050001d8181c240e90151841c0104452040c001d00550b40766450003100c0d000241a940480b02c1c104544000401e00c4848440144c1e108640510060000300001550481a940c0905500002508460704403650b90700c603400e05550b146800100c98 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 134602374 1250 134601124 134601127
    0x6130608031c0f0906050a0f0e0a020d0606030b090a030f08010f050409023c0f0d0f080405090a020909101a18030f0d021c020a0807050f011410060c0206 67
    0x900c600c0040180c50b01e000700078010400200340d020100444e50180e07001c3d60119643e40030b20903040c2060040b0300c82e0501e403a4007400400da94454041e1503415541d0000d10030000b100804040000310b400c903800450f01b1003984400307031a100c0100d030340316001510220b001a00c642001c040d140c1c061100c05043e900c0c18292204213604080a10006000000003a80d100003900c512030000c50900b07410ba541e440340c6c01400d001080c00214030030301e00d52079560080d2013001d244465998035104c2170a040400303900140e1070544400c1c0c0381030640d8144166000f854010101100b0408080341d10b80040c80110f40550b8240540da88a2640e0388040403640607100140b402985c1d480a103000c1c00014003c150b02e250141da00c0103100f000000e01c2c2003214401001290030208402c3c4420360184000e507400e00c61082e071604000e00360b4200035200c031180100141049000705403802807000401c15008070000c5c40f40200000e842c88031200f80c00b40012036100301c000f107118002044951050407810110fa501400b2903 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 134603624 1250 134602374 134602387
    0x6071106012c0106030219020c0603060f060d0c05041a0304050604030f1101060f05030601060c1a07120c020f0c0406060e0d03031401060503011a04030308061e180613060803 76
    0x2c8051070090582c02d0500c0030001a41c2071a4041074010324001c180580f40160741c0c4442c60b0740311078400d620004003c10754100901e024059101c0804482d8002c01c00c81302c0c4000c1d40002e0001401501881015071021460407443d2208a03800c0001801521a240402c0b07110316445070700f20b09070788401c94000f003041d00074601080010f40140c0c620342907142d00707040014203c0c00c0e61064508407041d641c8442103000c0410003c001c03504040c4041809440c480c41e043c0400002903c0718084c031401180c26002a00101000a2503288500b039200c411060060b02801482c4441c03200075a9002c2d034019081c00d13401405440441e81c078140c80340c1e1046907215103901c048500312004001340301161036410383c20303d42c40d611103504044a1000c0c050280049407141c0e900c0e941480c0015404089150b68964004010402880401d0f0000852640608112080241411420f0080d020308803400c0e01c0540141c1e25a00d4450318a800003c0248030307100036520031101a001c82c007020b0aa80d600e21030801280c0042003034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 134604874 1250 134603624 134603639
    0x405030702040b1528020106031205030402010516060f0605010e0a05040e1507020312090703151a0a0f0e0a02130302090403170a0209040b0a030215070606150305090607110601 77
    0x600f1000400400c0d15a00180d609044503981d40501458161402201a05201d080800d0401a40c2c9a840e200070400c02d400c5688042d218081054010b041c400080001411a8412421980c4d045007500da500151101450300d0009000c0e01c294001c6158100000400d0b00d510560880841ca00024a1040d12524010500004100700c544500860044022410515000428450003064140c1c01075a0340d0561506c20002d040c000790002c4050b80041e00100040740402d04c2051090700346120008085108203040c440408203000b03290f80020410500041d00a2244091001c858a000701001d080d620b50000c00120300c24040c81e032130384222000052015044c00d80fa00e9034030510038200045031280c080803031004100200c4442e81e616800203054203150425003d0012010000c1e500d4090550550740020b102c5043c06203600c1d414600815020140303d41900010000d00c9202a0038044500d1114005c01411040350750344414407640c00410388161165032881030020810014224503401d003110f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 134606124 1250 134604874 134604881
    0x7090b0325051c05040b1609170312010b09060706020d020c010e0d090e0402030717030d0f0515030105191a040e0304050910140d03050c061503010606030c02060c0d11031305010f0203040503070204 86
    0x1f103000420400c0744003c40c40e01181c3e03078250b4655201c07000440d102c0045800448190740c050304600444041402485c0c040c0c1c5503c0161804140e11090268540030701d0341c0b0310b0000780664202928a136007001c61030100c911012552140311407803941c4886400b82c9500c580602240242c400940550000004008041710441e4005000115806603440e01d6001d0303001c201510710300701114180701c2d80c4a09000e0848903e046510714003070250000d202c0ca1402900c8d5010f640f01a0880c010195214542e12078000164a103030012180300402c10400e00c895400c2e50740c0c1d2900079000d150302501680001c903000300c0242200d0011074841005a081e0324158206109421305154030403001c2c800c01744000b01a140c000c1c0011032042030811441000c1c80e40d054105402d41c1e0642d4000d10034145413030504070080d41e000c142c0711f500c441c60748587d59a40a503111884001c011040c040c049260002c0240b1000151070080c0089840c043c030300a102d203c444030801b900303e220a44000741264410000d000040c00c0c580c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 134607374 1250 134606124 134606161
    0x6020a080d0902060c01020d060501031b0807140724060b0d0b0105040b0a0806040b1e0603040804030602130602011b090302120f2d0607090b0325051c05040b 69
    0x71404200c0d81c3d000c20010b0700b1005030409142d4012071111418103551150000500092170117204d08124400c8500840f21900301e498100480c110024a500d4000d40c5440c40100581100301d594050707134203044410480c400b112050700002d13014408022401c9000c0c0806551145000c986005001841c840080800045840c14088148030021780030852102a10040700e440d1100103217032070f01c4000c03c01220441d01d601c912888104048203003c071900808a042640143d600550f40d44481c140300301c490065500041c1078a00020300f4607030041590042130201d0700e60390000d0105030100e0455907541000c1c540311000081d14840100050f16110340e00030b0404c40b08070140c5c2d44404640000c1030400030400301c0481480550304143c05c400d0901c1c0b4015001d68011405800c081c2006400185100350780e1203030380303218180440401e00d00c0c081d903000061110294102ca83c80381c4041c0d071020786241c20104460034500f14445581c1c41103002c0e80500f91140c0d600c66041c914075541d03400480903011914 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 134608624 1250 134607374 134607397
    0x715030b0a0914130b0a0f0b0a030c0f060201020304080d0207020418230c0306061002030d0e0d11010c0e0111031309020421080a1d0316030b070906020a08 68
    0x6100341500d81c1c6429403108041c0101a6001c600580a5001180003035805042c0343d8203100020f0001020401c40c5005d2070b0010110040403d241081c00107220150281a81c180e0348001c44071000020442204203110840d4100c3c0741d4400380958400e03080c1c3c205d010480d00034203004000c00410801c402e05500030000340388001c00000d04006603082503400304041550850f40000866031064400700408007a02c1c11045002c0103040d007a0360440865110000982464010341d004040801000e0091058030f0090710b50180c00c104004c0c0302040980c0c0c0300424800c10020418402c100b03810310406018840076613065443d03841d41c0900312401160002e400c15210b99450009015840b014800000160000c01c6441005038840d4144400000181400c0c2c0c02e1104d40010a103c0034000b0720403000343c8000e05950300301802a1a05440070814a5170340c1c528856150146046442c2c01d511078844484c1aa4052a40002a580c0352041516100003d029800140e404202e088000900c280d00811071703a1003c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 134609874 1250 134608624 134608631
    0x605070504090c030510050d020112020304031103030c04030b0606160311160e01051f090303050c010209120f0f010b010e151210090e0c0906060c010e06100603050108030408071503 79
    0x2204056000c4030503c1c00c00e440040d4940050000c982c90311008203002e08402c031209560300305194000307440c424411410094141d00800040d080c54081c401e40c1d400c0e081c2071030a4039035a281c103100e0089203601c07a020464440d01007202194180c01c0c01400d40c1d0a54104d501262284689910290345410304440501c202d481514494a8215480d42046005001b070841c1208194144410403011880c2c0308000aa10054514103241c200e0f40031508804807605070070800d6403523089044c142e000e48141050140c002c84100c99030b59200e0400680080529030010a0714411100c180c1d6080c08e981c024460540040c0a846492145240231002203c100385215401c901d440081320781040c400d48215121880d003840e256003000310f100c6c28010f0301070b415040301c041e009100d1114000b5829280103001180070f502e0201f894000070f42c09500802060354090b040350280d01d021401c0c87c1400840303020341400281000000106071100000f40c50554000c68090000d85040110107224002400885800c054070f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 134611124 1250 134609874 134609879
    0x91208071103010612110301090809190308030106080612010e0d03020c0106170a031d060a0f0e09040b010503070f050609090403091806060f0516020127080a020f01080907030605070504 81
    0x1400d2040b030b0014080d14003060700300016402d01140101000300c101f8001d905060040740040c81410840d802508102c4108101d8414a4151250891203410040185a0000011541980240403180314004c200d801c5440c94914045113800c1c4c2d65000140e840c0d541c0000752035040340f030007034000d08007600030400001104c4c0d550303101c05483c0021075101d440d819040200ba02c0c0506501c982d66038840d03058400307810343d903103240c00101e0303130b0340c070442420800b0002e4420410020520554410006400c014200303065400c2c40e0409480604c0d0a05c2490320038465884009072440c00520154200c680c000c0070a800e150100c8180003000c0d800902c114204000c81d03602140034140c851400780c03000c8011500203503507410b101014041002c101851005c0c0541400f0156040000d14120903034140e0a1030b04020b005401803244090407035034000d50145880407032001c1072031a40002e85a1900b4000c4903080035009440005541c800820b50300d0039142d40004100380302061094004503000303003491800501c0c1c00e5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 134612374 1250 134611124 134611129
    0x50603060112020d02120907080601030b0a060b0d1b03180f05010b03100504030e0a0503030a20030a020f121c1a041d0105090c10080c0f040b070606060912080711 71
    0x4d201010301003002d076000c6451040c40c101d401c81c5030341c049620350003071880500f81240141d0b9024148801050f0340034041c002514014990403800051180000e542d844038140c030780c00400341c0700040c216100d686680220402051080c06200180f480b00c032860740d4881e130140c40e0a030700411030a00130740c6d003903480d4401521107490810503602d45061060000a890400f40b800030311200c024204144507601a000611180e5000b0045034038220141c204400c138400070700c0420040321051511811540004a00c0c011903640100d0044050080e003001e544c1c8041c00b002890815005d9041c44c5d405007450a0801c3c80401620b9014034000c0705d00894a82d0641c15410008041d40c40e510341020f0154800884015038139402d00900b038211803104060400c0c201850046000039009500c0041000480e0f008160044608000c4509100c8004640d0f07503610307142c0759025241d0740800004c903141d91425600103001442035507a4002d0351b00c99111921551340c1d40e203e9030b00d0fa4100f0030041d0f0301c0c0c0c4203c800d4105242d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 134613624 1250 134612374 134612377
    0x120406081b030606040918050106062f030f0a05040e070c1208040201050910180902030f0106050a12090204020d0509070f08030c030405041104081002030a18020a05060306011202 78
    0x208825500c004092424585040510400803034000e03511000340300340082a681c1005407411703109032000000c1d01103842500e02908840c0322401804a5190a0011601542c801e00c420184c0400d03070b040042c8840c3c010980040100034181c0c0a400703420a00814041860950080c11200b145103401410542c0380c0822400c4a20255a41c00220701e0300380c525800c0045078525859105143e0030f10842a1826030000380ca50711807024413610070500c2e06180c007441e500076121700c4507a8020802007001180c6a00c21032000b98419500080b51928210000a0070352142c0308603002055199100d558a013840c001c03440103480d1903a02207900c16000c0c801052481c60300e03c950f80c80380c0301e100001c080c001d140c079014411000c1c26402c010155081000b020900120010840301100c406540002c6c01150140e0b404106001c1d680040901d8051169581000c2045401a41c02a0104003041050701d10b0951001d21015194000035004883e0240c1000701d4034181d8007a6500c0700040c10850010503840418104a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 134614874 1250 134613624 134613629
    0x90d1202010f0b010f0c0206090d0b090d0e0d050304270203160f02070f050906030703050303040302060106170103050607110313032a030206031602030904020c0d022b111204 76
    0x107039502c441d10359100036140195004110b00f800c1405000c07900d101d0041c440010503030064007504000800c007072561504108001e925030005190020307400c0c4020499110103441e86c120000409052410f181032030400c040680395075000c4011840c003468000c6107047c8a0b0003840f104a42c2004200310841c0841034002584204039202007500d800d80d4a2102030094401030f1100f00c1191701c0aa400e005a60300014200281e4004490a52541d911000068174010107600014020300000c4103020800d50005084c40c140c03541a00d41071030009280300030b889001d0013407101a00706d45c48000030814050040c0d01410856155100381c9243c0502040c081001d902c1690040320311040380c1601c4440020080fa0054403640c905100c041c00a203150001415800050b01d41c404490b948950380c45464001c20448100305d901070400c0d501c4014070328a0b180c03594a17404800d000340c05410425801207051a1b4050f00001131003080c00c1e0701d031482c000c0032503460171001242e44940c42600c05012141c81c500700138000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 134616124 1250 134614874 134614877
    0x5090c0a0207060503010510030b1c03050d050714190915090602010b0312070201080a0204030c0b04030b06041b03090227060307210b04030e0a080f150615090d12 71
    0x594040680c030003854070090354004010000240300600036507940c0200b22813401c0161501040000314000001c0c1d0002079000854078458100d0010070030550070502508030060005010062a80c41070b406a402001a03076807100101420812403140d01c00c94284c3d05040b844030324100321503075103420b107130b240300c15024460300003147d10110f041099a41c24090f6542c1000d0980c054400100d800222188031702030340710300905018a0000143e49404c1d0307503064600071508804505100740d5120702e0609287d001d80000d543c1e40000318006a010700306409004013400110a9481c050010784004800418416408a0740300036070110f42c0c01584081c0345600b1001d1b8140c0c050b007a250900104042c80d080c555401960150b411030720712107005540001c1e1a05107600844ca49d459984c40780b4045560301003035400b04d50702c2003c0e020b0204021800090042d100e040060407604010044101c0c11a0302008403012035000d0b42c0d82c0e9007150610303c0c801c0504200000030741150048891070307590f0b4440d5850003283c1c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 134617374 1250 134616124 134616127
    0x30b1e070210151a0c15070c060501060e09060415090f020901020706080f160306080a0b090601050a05030c150918100e011401031d01020d05010f080606010203030414010605090c 78
    0xc01d520b0349108000101c80c8000c0114042c80ca071041510b0b009901c20620b03e04801d020480e500020000d01c0b48945008003120611414600000b0107040d0114040c1c0607244203262100202c0c6690143c0304d090154203004116400342d0b0783e080100300140601001c12600c0ca04441d20000305510b05005045208800302805620b419540c0c000a1400300103078088400c1003520024080b03031200101130103130403001070720129400c40c44181c03040d0060071860784020070174422150342109005901c0c00c5030b406180c0400c1a120180d176108204203031240c141c0102c40d8036422130704000113289003c1e003800300003c0c0ea200350142080705500004582ca190707000001a11840c080800910400c0e462810b80030b0306070a00c50784000e50621820b000c0800c11501018141941d40600d40001e04031482c004802c01c1021009644c1c40300d0028550000d880c080c403401a540810311008510020040354403481000c040c1e0086046942d00d071112110600d045100004a542e103510200b1240c82d40c81c2c0e050300c42c50004241c035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 134618624 1250 134617374 134617393
    0x40b030c030a061d0d0f0c060612061d1204050105250b0f0c1602040e07091104060e0f060f2b060e06011701050609060d0606080105190807030b1e0702 66
    0x1444614046003031a884d030303003240b0003480c421074000c00c05009400f480e2400c07003001140c0f440d2080c020815500410340840010481c4c5007001195000b980c269a0906140d103084500c20150326559881e113030381e01316141c200b40310510845d403280c8050105080500080000240d20307088842000040344425644010300ca020018000c92024100d0340100ba201091440c201c1041c03550f80841d4050b0500a02c26034948040c2004400300f0440300001d429829000c0081720075900c46099140d0151040d1408900001314405407803030444004000c441000e0201883c201e40c030340311248151710250070f030340150244042d01001404401d401c0200c0d6003a887c1b000846504002c090030341944020080ca0412910f218801e46e070703100c1c0550640c1140d1f000e40301907031138a0b665400515240240003185540310319007500082e00c160b2012269048800c00c0d07803901c80082001180c011054014018840141e01101d0200001640e02d410103510000740740092009807070051200c40c668409039240c2005a0190071071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 134619874 1250 134618624 134618651
    0x140307020a2013050406020702030d0905030d02060f010303080c0418090605011410030513020612010302010e0303070b06190902071104060902160b0a060e04260a02060402040b030c030a06 82
    0x512034101c1500c1804202052800001d103e5480c418041d69070f080d00c0b040400c2c104001b580503110042d500400356030b100b0a480d5001030584039144611482885803007141841c550000c520307507000e140d040000e841c560b070950700c003070fa40c105028082000044040000043c0091201c6058400c03d038100710110b00300c03015082010075503006804c8a100042d160b20107110139a60070001c0100c24102d8100881c039941c45a585c0e00f1520409030010390800d01c00220b0101c006904a20181603078400d8807600890902c400c14550340b0b00404d00000c26151669010404501d40290745a904800c41181d2600071900c80c074182013070380c01049044800c80c5400805000a03d01801900b0107084150421800d081c4442102c0012141c80c0d00050440c1038102c000c115462801e0b0002000341481201c07948950415107803d0046017036540400701890010122408008620700449044008641c010605030b1955004c100c000c0109500f00d60f450b04c00d000318451542c406010250310075026100004201c62940403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 134621124 1250 134619874 134619893
    0x70c0605010902030c1603051b03090301050906040b0103030c110a090209091b041a0d0c020d02010b030a020916030905120903070909080a050304050109051b180402010915140307020a 80
    0xa0b0310382c20300520070000551009001e940328132240d0b01d01a140300141e810240d40c64402e160b1265a94411040762150070203000006002c1e480c800e4000300701c160b441116198407500f06440c010400300c006001000801c0c890954030301d015011707840c800d61690003280010600171540e840000b4a58000c02d411220f80341500d0b6a662014807010840704040322501e01a03103a00c01c41c09035040d03103031400815608901013030003500d190a012410410128a0802d006940d80a2030790711800190b007030240000b45c42c00d001c0340300748540c0c2d40905112441d0300d880c80e48500d4441880301c01d00c100b41d80c4145200c08118104100c0d10010500384400b80d440030b030310043c50708103c51a04998a25414141d000002842180c12503440f00402d140c426100d840320b160441c094603490304081c10511031440515010191513085403010142240d03200c1c034103803d1461951078004111806400310320b910808010034540491003502c028118a000a01c42440007921405504182d03010401a0301000850041044904 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 134622374 1250 134621124 134621129
    0x40b06031b09161b030201020715061202040b01030e0d090501201005061309060221091b030a0209040c0e010b0f0a030c14030a05040c090b060708091503070c060501 72
    0x40407072001c011000450002400034203811241c040c1c40e81d600d60414400c01910040c2100c45103400340000481c103009010390020756050300d03185c80da2034004e280351f0b010380319807411245040c54030718007000c084d0200300041502096440c181510742030b40c1c255000c0103215110f409040b5445622a80b800d280004100300030040c80d411286150391104c9058080006110700b104010081c0032901342d071500d000c110801031000c0b4403079859082001d5101004170640182c008221070040803103865803040d019005040e8141c0d10140c25030411048280301946401c0c58403c155006012508000342d2341d404142406800ca5041d103602c14074400902001103a0001d44d4010400c4000785030034118225207100740c0c1e11441065506155441d81180b9006008541c84440c1c50105010280c0702e10b4520715403405030200b218115054640c00f0b801040440f29445886106400036001a0402250782c1d2900c0c200c0c1c1c8404000c50b480340c00c003820040080c41070710040d0f205080030790319031080c590180313400c8040d15810f8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 134623624 1250 134622374 134622403
    0x1202070c09090305040506131e06050313030318050109060c0503012601060f090902120601120602030606070507180507080c0a0c03090806100311030703020f0d050c09040b0603 77
    0x410194000c00c000c040600280e685103440022019998901030340d0500c0355070321054020b0004503007061601e180e85c1603602120768407051411000101c12242040c110349000d00c00210307c1c2030021444e0a04801c21030301d400d910074100041c0344115055400081021400221000d030b4407800001300300b20880c014202e80c0d0b6481c1c180107086504043d4403110b43d1010410b2a03101401002d02c0701c121250942100e0010403c030481120342549400b1b00001901c41d00702c00380d01446000040308918000024200c1c106c0d00e650440c96020100c40da50314000e0b6000fe031049500c0b030024007135400402d01c14000e00006003400c440c0404c00d0714050114100ba40c1c401030101090001d000c08010081c401e4800b140c00704e0301d00e031a150310810300c2842c060b1003244094102d000184182000c100c44407814200d050241d80c0142c000aa011841104141c5c1e540c285003c000d41202b1680421207081c10071890910241e8400e60079601c00740c7c6000085007000304200c90607194542d400c8240565030500f404005c01c00e1810 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 134624874 1250 134623624 134623627
    0x60a0305030d092303030c07030c0807061b110d110c040e0102030f09060c0f03090a0c0e1e0907120f0b0c0910030b1f0c0c081605030a050c060a03091e031202 69
    0x584444980306d000003040d2803803441e80002c940f000c1501c501001c00205600501040d01c038802400c01e0801002c0e20074a0410004029541800d800c0c0644129000d0528050042807141c0c04000c0440b140c0c074032045900080e2280c404140303442d81d604d0007040c18401c040e030001030f1a403400601c2e21114400190a035056a0002c80c10f00c914550b1200031111105800721071142e4a80390045180e281c0228400040d101c078421290106450014029407030041040261605600d038500c609910140019901d402c02070740485070412007101c1d90a040c0700e00341c0c09408007a5074080203440702c085900c0c1c101c441c054014400203100c4007929160440d0003070903a542c030b8200128034800300070400d038050841c07031000380348000b181d4440881d2050b43d540900c168808156801c481d41d803400da03070381c2d910100c0318140029202980880c103410001000340501d42c1010051800c2c500c00c5090040c16400f80c01d07400101503c8403654808a18651422a880710300801203007204281e504000b003c20b9184400748524a00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 134626124 1250 134624874 134624933
    0x40c17160306060912030c0201141903150f030b040303091a10090c0c020108090c03070b070b01090c0203030f2203021b0604050f1e1008220c03060203060a0305030d09 73
    0x7412805e0464180c2e150600054094107400140d504100b00e0701307100500c90380001d40c1003094511405444d40076a12391400d011b00b076458000340b8800b03819030044500c1019030007400c001041140601076000fa00905002074800403d07228600f0300361006450716010340d80310003805003c403a00c1d0348038401811400002c114400c0c4400340141151240030020341005030680200b5455501440101d85803500101107030f080070f0f45c0301000c9071740e03170490075040c0da10000810001480c0d42142c0200f5100001a41c003071403a642d500055000000006054134260b050183e4610400c01d1040040380c00c6580242c00514000c01074000180f5001481d24007140610802d0104102a880d5181001c8101000700c8103050301c44c4085103083c054001d00c50b0ba6a52101c4c81248604805410010480c010060700f42c10170560003242d075180b40344480380c4030010f00c501509141040480c100741d001d1904894028100c001c0b07584c0e40c0c3c42d00c6207150460202955026561006a000c21090303000d4507040c00040c4515002a51 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 134627374 1250 134626124 134626139
    0x501020601060e0108091002131406040f121103010612060f0b130b01050903060406140901090f080304061508030406021e030d05090a1e060c030b030705040c171603060609 75
    0x19071580f40207052109460102d546010184204c94624070210411520f4001301054401a40114814642402c0004044910a00744a1704a070241c1d1121810707690003d02c0e00ea02094160440741007607405400e0308424071410359080c044c0c4401040f9044806808400600f040e1080301c0b001c1141420b914a07242001201d522202070105003900d50b140001440a200401030300c01c2d109041c01030b607050250404020820103240d12041c08103d032903010541d00d82d908c030031890032211030391000341ca00e85c03200440701d000a8403c402035501620903540820000304607a2004075662054100d8091500007203410320000d0b0b0304212080d400040d0412401c807113403e0b0809640c491141203c1c465800303880343c00242d5064401c00069204036030003d00c48000954a40081841c0780d50084200d42644c10880c880180902c00d0040110401004014054452070801003100810344401c10400b44130210314819405809462402d1194031062004c0e60450907891005040b00e0701d942049062044440e4244001d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 134628624 1250 134627374 134627387
    0x1801090210080a0f0f051807060e061305090403170a060b04030b041e05031306080408090f03010f090614060102030a02121e0c030702031011090112020904150807050102060106 77
    0x41c401400c102815886404518001d490790300c0d04401c00320b043c44000071403051141e00480c822043d0a81c0f5910148880282c0c41c0c50b14014481c0b08001901c280310f92640303182240041c0142c0744582c14201e00240d8a80c04250f186c04120340a070081600025622115000340300c015a003c16503d408100e1241041a01d042a00850001070310700810b28001031300300720841c01100038801700030200035900002403a000d65250b1014050404459083e50000385241c01101c510b40601c3d03010f00e200d07042c031100105001d400240800e910741c0c15922140d03c1582d6100900c10183c003980585030100300420342c1c6007904140d07207001c1c1c522811507004014003503540d540400c11204820f0303c141910740e90b000d0f05403080b105100304040c7d00304088000481700d02041c0c0002c002d01d540e40c401e50135501202c540416520403180000d4030500c60b0310040110200030340c400c8084806d0803000c0e650060a00074405c0100b021141002006002e116079400140241c020400041d4020802403000300b00c150304001c0c000703200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 134629874 1250 134628624 134628649
    0x601021902060412080316081306150e07050c0c0d120f1116081603080a030f0f0f0605010206010e041a0c0702040507051c06080303010608060a0e01080618010902 71
    0x44080455a420440d038a1000f2a0000c159a00c0c4e900040180750500711110360099560340c070380040b8441260074250065a0481c882d400081d00c01120301c5441e21900c001c2d14034580080012035945a02052594410b80c1c40da018000a50301c540c1c960300c405075121f24022126069601c00c54004500000003440312042d1032150300c0e2032400728480c104002068911031600d00b26900da901404544800066066612070100c4900408940e2207600512461009842c1400042e01740f1404100f0f0170394084c002d400000116128100000700412941c46803803c903122031030a001c41351f4540d1410499586d0401510b40541481800300940c0d0410307588000003101c031801d0346402003825034000f4009a03207800580f021283c010300b09000303500c2c3c642d0f03008180b6030200820172403244040c941c1400c800c0b060f1042d4002c3c1ea1032400150f1079a42080070564000500400f103541c00308220b01d0100741820003100c00f80c001c080d10300c014050b074100204000301c0b00d4200c0c0500c0d40940e05d0f000103000566103050145c0791 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 134631124 1250 134629874 134629903
    0x11103041e0f06020309060f01060f021218130b1f0903060b040605120a03030533030a050307080304030e04051611010b06070c0f0e09071502070e010e0402090f060102 73
    0x1100c103664908007000c42d215800c0a885144040201300d0454000702d0100e00c91000c10594490310b0381c03210301c1a15002c807441107140050307001902888418020400070071005441e00f280d01b14103466400000c811301e00000c038050301c0c40c1d01d828600400d800d004010340312243d000d03011450011202d030f9004000034900c0c070000d030130542c4901400a07140c03034071341c029000380002600ca02135180ba80101c1d40e907540d102a2049000034940070005040e4101604024560401803255848040c01d00a810101d100c03004410b6605002c0c00000d1340010780e00700001e010300c5118407203007512442c00b402c3c003414811480941502030307420b101c100090700c111420050300200c2e003801d0035030034020b004a242d4010802d030a4000c1e041100014020103021034140d51800f10340c644100700c2c0710380e5165010303450b4030380b419213162406a01c98607041c010180500e4032241524181e20450780d410782d541c0b1450407010403e920840511102030248801c1d8100701c3d1400303070700c221554589070480c00c000d00004d40d507408418901c0c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 134632374 1250 134631124 134631173
    0xa050f0717030406050405100b0609010503311407050a05040903020c060c0c04050c0702010903020127090516111b0d02060406030c02061008121c06150201110304 71
    0x20841d020400014100100ca00c0e55103030719292a00300000c4c44151070540d50b82c420003140c948603840303038050b0018130703076000e4034003820011150015607103908081c00c892a400c0080310034007440c21a8031078031f0300031102c44002605281342d02d0401c5400510032840b40423058004601c1880f0586400c01007000711501950000340100582c14104d050103584002e81c0d41c4101b00081c000900b100000b001c0308400d400321410819500d90000300191449050402070220340c8a90f01080550b0103107403050312602d0050941055514450003111280e01150402c40e08a2342e030308280001c00380040100030300c003001410481209c0150402031a52030140203c5240d0280c110840b09603241c0f5444800d00d003c59000d00b50329191030711a04058040d20b6000001001403040303400084240c0d07820749940f0212034186001c1c044030307083c00645c4545a070000b40c118421940305a81d103801c1444c42d100b1036005120103200b040c5559030f1f8482c001e080d180c0c0c0c1080d00080b41c000f4003d02c0082071420a164012904221042 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 134633624 1250 134632374 134632387
    0x5010e0f041b090e0c03011404060905030f0f1b0303100b09040b0409120e0105070f060203040201051902010504020306100b0409050402012303100f08030d050415110c0d02030a050f 79
    0x42c404054141c0700c0c4411004080c0050210460340040740394210380c13810749440760b1005003498226180071900061102c030380b0010501154080d400b00603240d01841c180c0c1c1c9080181c038291038443d401000710f0340402000050310800d1800402c001007000c12140061032450900c8406581c484400d405a980c0b05000010b80925660302d03a4400700080e2b801034818840c080c840c0c1080c14100400c0000d00d004180d00307020440c03076980f0500803642c010303a0102000c100d0b464203888500094100820403814450100036000e40c4180c0210310303804002c0e841d0b00104280c50148141030404c0d001a10030664201038000078460f490005054500340c82400307100080c1c03540c035400101d070000c0041c5100c540001c1c01e6130460b02d8120300700700110b12034802401441500d95841945201c203110a2280d1541e0340c00c1031005208104550b00801d800a008110402800c84058103510480f002c44102c020480e2000844050b181800c4c40100108510340c0043c5003401ca41c1100134005115035a03080a2000000401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 134634874 1250 134633624 134633633
    0x50706050c030d05180d030608120a050a03090f0b090a0302151509042303030a0b0102070506030a090c030510020c150402030712140303070801050301290f04090f03180905010e0f04 79
    0xa000590800170304a40203454507840c0a0028134140c003e61040d4001d1446e105200100c0800325080c88a155031154034041c500b0304210010658010700b2101158001d0083c3c1c0410640c003600e42c000d0b0100e00c0a4a094032541c5000792400700304000682c0c401c8140010099160303c1c0c031000f0142d40e50180c5a4550680d62458004017082d0388510070aa11220458200080c03080000034510030841980100481d000040059a943c52944204c80e031102d41000090600c00c500e0f003186840600c0303060610241c40d20b82c0e0b10981418100023488003035a501090750b02d40c1c500100007000302c0e480301c0124141542469004a515010303c0d001d0b03090301c0c0b41d103002403000300b0400e03480046100350101e080d680c40307040560005244480a00c58a41300358200400c10785104c6891450b0400d0078102102505905181c0051210800030744081c00d60055440c10200080380c01c441d4840742051081c0e0340d9082c01c3c40071034001416510b041d0840c10b24903140000611100d1a100340b1a50403414501524015070b4403480e1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 134636124 1250 134634874 134634901
    0xb0105120a02040e030703200604060b0d020a08030306150903070b0f0f03010305071418010509100806090303270a02010e060d09030e01090602030f0702190b16050706050c030d05 78
    0x50003500f0515102507103c0550f40403014004243c803039503400307c9074001807201415150440146001680081d004103002400c81e038014000c010004d80b035981241d0340c0e500050300b00007a079407244016030800420003800345003010880c1c080c550503450060a102c01070b070106e035480d001d1f8010060700550002e0b146001002003000d0325100705030a02d40740e5680d80c50307190060300e5503d148241c610080000490300650f15045040c683c0c081c140f00354403040c50386000300f0418030240c007825903040d0901500020403030240911406101d292003400448c1d030b90415150050058105142d4915182e05040e0030f0050700401007032104880d81c0919109038040300c8031000504500c2211300c1080f120740741040034010590048460b441e43c1200740c071203c540683c0d0b65802c1c0c0e200d2042040142488004101500051030720200c074184146084154034803450300e0364094a0103a0001d00c3d43c520802a402c3c05101f040010808a0f02418080c030b01035040c100394002643d96401154940b1240e65100c00c0010300403410141c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 134637374 1250 134636124 134636143
    0x40b0c0a080f0403020301060b25021207090b09150a0603050c0904050411010f0201020a0e0909011d0a050c03070302100309050c09150109080a020a0e04060f0c0504060e0109030b010512 81
    0x316520b0751810724940606190b4018401280a5400d1910015409803100c0c00e541844243c6509802804043c503607204042503624800c90340a60324004907203564104000020103010440000582c02c0b65240811812a000070002c40713440500e60078400d40c03900c0f25a44101212281e040205107512180b0108401d409030000d0f094200d0310b4001080140140380401140801003a00d03001e402c8540c0741e00482c2070f4421707490039801199880380c03c3c00c42401d060320b80a03480901c0100000d61343c0c44611039108200744406816100c1d51120920b1814003000b403281810b43c00c4214010705025246501003611080580000c005043e0768441c80c01c00d200c824000316110340c10040c0323542e50a10301440c3e007100680036101d655001481c4010040344e072103000982042c0d0b03250001c10041c1c10618044c820101c0d1364004100300d41081d1101c1c2500380d0f04245004050402e2203d856898407182080e10007049031220506450400c110401c0800c00304000c0000c043c152130341503448041d10041e00740160303e48040301 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 134638624 1250 134637374 134637383
    0x906010302060f0a0309080a03050a1a090c0a03020705060702060613020a20010f0903091e0b09061b070e040311011e020a031e0e011803020607231902010f060803040b0c0a 75
    0xd104051594034ac0d010501c650152081003186500c135001100c00000e42c031200c69080135006020641041d2003401500c1e102136680340c094588801652280c2c18401d096a502026134020340500585190980c814280110145e404504100d1072400040410030b45a81103039101941c941041d03e002c2c000c2d00800b002c500d0380c5e10280141400c80c54010040700c00b501c200c810240e40b18500007043c0460700d42c11421945010b800604004190040105941c021310b140c020b072106910310702c0303030301c3d001400007000508120355400071610302824040c00d0a8803821700400c0c00d07450109450000781c00c10a2000c41d070f61a01e82e0040c0c41c0c5030b042c0d074190010810890149140703841030059100c1d065640d0841e5000704010b00080c0f01011480f140003149200b0280001c0250b008480000c403241d00ca141300081414171114070111810f07520100ca4116484800e060400c80c41c1503400c2051a0b409002d07542003070244000800070f061401d1030054881c041e83c010a201c140e00060481800201080148202e6401 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 134639874 1250 134638624 134638627
    0x1c240207031709190b070c1a06030c010503061e03030d060915051c03050f04030f030203090f1f0810171005100302060403260d060801050906010302060f0a030908 71
    0x5410094a41c9012800032100c0c0c001550000d220f00a02082100c100c10b0342030150b25500300300750380d2080c03c0c0398010300e0b100401054400b201701040469100c542c540c40703859400c0045e402d040003414200f50944a8060500c5010424131145840c0c2004c0c641a0111649400a90400000020f811485030f15010f900c558109000440c2c041b01c1c1d64011103080c0c3d64140040045980d0b0010f00c48030030b0900301000c0c2c0000c1c5484208010038011401050b41f00c1c2c1e45a600c2d480c2036100d035100445007421303440c1600140e0000c0790302103550403c0114100443c40803074051b000e58400310340080308444070500c000d0400c000040400d0000140940503400362446a48503e0950324500384140e40e0003001d2081e141003400c110100702c0e0000704820042c2a640c014084624045c29034840f8040c020202c080d2004113110720b104035500640400140c2082c1c589500c0204071146400035940c290740015001c00300c0b5412000041006a0744e02c0200c0c1e503a4090040d4264a0786440315094004207a078920107000c0840 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 134641124 1250 134639874 134639887
    0xf09040f1515080717031204030c0503031e0a05010f060e010905121c030b030606040903110d230315040e07080d03020304210c020105090409020d050304050307051c2402 74
    0x8088100c07405544000040300d44056031031050f2060045d0040c80c8032146e4000b001400e625600d080322040d400380c040d007860180190140d48030340ca10b500c121303200c6510ac4403c500001c4603242c4895440d0308210150000e000c0e07035040034802c5200390614403404051150f0b010459000780d0180d00110000d020003010302c4040140703441c8980e00c0781c41c0f01c045c860742c0354141c0c0c0301400030354028412034a010300094003c04082c0d46003414040104840c070419020301014090421184900304001900c02c00f1355030354421010700d54480345c10f03102a08201031071040310074000c00c0008618201c0c0d01400d820105c0c0e0100e04a2451140182840000e8122150700d006040d440c220b9142c064005500941c0b180c1101518034007519100c06c001d501c0750a000300020030240d80304000d903103c0c1000d040c00c0d450090000880204980c00980309030480d03101102c1035040400c0811a6107002e210542c0100020380e5480e118107201e070000f042c0c55680400040113509203010382c0008540030030151400b52050f4004665880 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 134642374 1250 134641124 134641151
    0x150807030216080c011b090e01120609080a0f020705010e13020906040f060203070c0608070806040f020f0408100606081b0d02071e170c0d0e03030702040204060503010303030b0f09040f15 82
    0x100390410700c001c80c81401251441442008440c04440540d11060501d900b0805552282b903181310b4151a0252581c201002061515004000d000d50039100c10700d01204181c0b01038101410f551006040c040880c180c0a0f442c2c4a005205450700d11000c001643c130b107400c00010300c031405140c22028144403c40004aa07064002000b4003034540600034800f003159496904a4008404a500c840001c1102002c100d090800d80c01102d00c01202d035034054102844200e10b2035042c0c00c987d00c41c1c161540041d0342044546041d03c0b40a02619483ca80300641d850649070f01200c00030b41104c1d2101e01d8100103070000052420754155445550700041594403084801c1d08110b1401e81c0250980c2c44c6088800d03140d2100b070080c41161130b8110a44060403404082110982c4c1441a02d0421601400104100001a44c03035200030302c041c181c180c0710640c595045d800c4c000c4c202c0d14240c0b4894010711000401d01210b0b507440003c0d5074400d501000c0c61005041501e44210168004a10904503a040c0486640001e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 134643624 1250 134642374 134642381
    0x7020d0e04020403170306011e05041805010b030606071b03081908220203070f0608090f0d0203071103030d05010e16020c061801020a0c1e150807030216080c01 70
    0x1aa5a444181460305081100324402c502c002402001044020136981c0c05890140d580b1190504004604048078041801c0c401c036140200e0300051400101807004030030b08140c02141c14000401001198102500c0c03034001d10000c1c01441c03141402103052000c101c80303803000204400029804460080c2c1c0e0b0b282c00c8071681c000ca842e2141c0d111100f90483d0100f0300c9000c000d81702c0e004602d41904043c20199045d44405890300090360140149103020032801d1034006980020100341d0382c2c10300140752604010f4140f59848422040701e40102d0b8080e0b03181030b800816944a01d42242c1b4604141032014002403462244050390180316040000005002c40906400b0344aa000b0440e440103002c54008100c7e02d542c02e85040f5680507100f44581e01003401d141c042c9191181c018012500e00401c0c039280c1c02c02c01c1441d40d2040d011a900e050300040c2d20f1450308804030060990072100d04141c402c1c54030207016180e0080c07034070b01050381c00f1400a440201c07010503400c001d03410010380d60342c0e1001c1401c40f6018 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 134644874 1250 134643624 134643643
    0x50604301206061e0806060705010504050c0307050a080705100306080a0f0308070203090630040c050a05010806030a0611040b04090212070c08270915011829120702 72
    0x141e45002d0300000d03460b004155140c40f01c0d1501d00100032420061005454000b0f02800b0b0390b405c06001d010b0000007074424412540214000c0c0002d048220140e030030545007900b29000a4054104481c00308500d01000964205454044950154001680710b007240104065030200001d88220311350f12081c03080700740140c41198040e58840700701341d5602005982da4410800440d400400c1008040002100f03198100100780c9650550446429280c0c000e02c008003068509a46c99078200c803040040b4034110928030020042804c8c414072074030744000000e458809000e40030700000c0d00d1710b86004545100604990241040c02007080e2215103070820714000f03400080201c42040003a0002c5a8042d000d50710081c0510b51014401c0c1c60f107e01d00081c0b8034468005850401200c8032044003c1c2c4580c0d421841c6031007110400030380190a0109800106030355410a03416130000540c10050000c001c6d0500750b9204d0388018852074042509d22142c0507054801d1442c100c40d102d0751013051107445680450098003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 134646124 1250 134644874 134644907
    0x41109030607050a0e04110403060606090f060801121506050a1806050f0d120c02040f0b040f0e03041719110102070f080307060b040f0e010519050405060430 69
    0x200d03a101c02d0199074500c1003100000114829014100d000d28042e000203c1e01040325101d5030901d69641d81d27400660f200381d00300c0d002180c032118042c88090309403030810005180300c2c0703072928065240500705a90000c80d030350040c2c030254692080306030130445500100001c11303020705005111a07036852100c8078011005412850035060910004140c6000034001032030510013000342c41c07a00d500390381e00e0180c80c88030204003050042c99410a80540e0b564864000302a810301c0c0701040c080400300800007115020480e1000181c5081ca0030460103034000241c5042d1006584070214140d40480764070f18000740c0d002d9010307407500600c0520040095440961100e86800e03000c8503e0903440c3d031901000030a51b070061900d40e80c01405102e010581035000032020700000b410010301003019001e400b0580c1c03400041058282e46a005110f81c8034949024500c8040242008001d24109503803030031b407545000341c4098081107610030702d01110040700d43d1841e000425050903c0c15521103120213419204419081e40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 134647374 1250 134646124 134646133
    0x18070e0904110d05150403030c17150907020717030c0c1c060b06041e030215070804030b0c0f04030b04030f090b0d110c0102040f030c09140f06010e04110903 69
    0x49003420600011805550300400c0025010700c500b0a0100340c450115083c0c9003840342c1d003101611290039800e1540501d0103035401041c102038159020309880c2088001001c2c511030401001601201d01c07102e03500c03004045681e6030781a100d6000c201d140c6140341d0010301d0307080c148020790091940b001008081a84c0d102d01518203595180003009040d05c400388451503448202694480029a04d5010b00181032008141c541000d84907000000303110310811083c01d100664031130620552400e001e50056851140d10304d13614220300365490204074003883c400101086030704c0f808545a14500c10a45104c108007040581c0c540e940c4e800c00d440c017010251810340210780d001040c064020300c42c220139001c2d80c080000e9540f4180402c0c0c03c4074000d048602c2c00201828080c41800e07011b03034081c00240024281c40d6820034020f4150b00713011010312034030340c441c3c0c803001d20341b000d00350440b0142e050704c07980f200d0103907810f9591740d5070307140140d5600c0c8052034690760103881c00c06e60100c01031800c0040c141504040d0100c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 134648624 1250 134647374 134647397
    0x3030e1213140108150a0e01091401080c06040608060307050d0f1406041e020307081b0f03010204080d0c0303150e150f09010b07050307080d020406230904050603010b1807 75
    0x924002c2001c0e407030b00007224000050040c1c4c04ea02e0303c40e210b450340980010030f0741d65034580d02c40000a0a07041000c459484850448140407103418a178090301c1a100070b4040703041e02c07800245061190f07124440c20b00c18000002041940d09001440041802800c01203035801c44e80390030003581400316422282c030b40301d0241704451500d0015510b440f80341c2c4802484410882c03000c0c40304080003405022a4144907007600400e52a400344401d80c280c0c1280d14940c00c80c805840300304a55040254034103402684140400c003d50480020345400040c00c9082ca51582c0e030050400301d026240c000b901d4044010441300008039031800c1e02007280728510450000421001c0e4104000c9000c42413091650b204c4012401400542d825800418540344508226032814030582d031001015044140d0001507560f020070100000e580111440203010500749004510304003886080085000d031008031401541d03a00b00051840d04c00754400d02000d00010303c0c0c58420140c0e690150038804040724004006044507555 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 134649874 1250 134648624 134648639
    0x60c0a12060b030f0402030a022d0607020a0b09130204060503060109061b0b07020f10051e0709120309050303070506070e0402090a090504080405210d1b060903030e1213 74
    0x120000e482c9030010701c0d4650307141d0b10500401164043d2090342d040c0103503512500165034440c0414001c207202e032078000c420160f540704c140d14414402c0f9441c0c0250410001100140d981c11101030035220408182500d03420b01001251910950a4145d08980c4c400607004c04c0c11130b00300000d54818042681c9880749242c03111411a2040320010701201c1c07488103052048002003504220341c0c1d000d002c0344110b8035840352401e0854a412a00400d5654440d5120284104030703501c0002d00040d03610b45240720000d030601030701c001c1020009200790303441d1440c042d011000f0107100b020b8134402864000e048944804803824901c0e2500c405951032004038161120181050a2074001e42d480b95000800045a03145800d00c1c003070107410001c10032140030000700f02c0480c941d50703207442840200340c038900e08d0052410040b040b607140c0007440c0380b020207120104140700d440001d4491a050802d900041c04298200d036407400f0703000b80400c01d0041d1494001c044c0000600d55582c0040d00040c1a88000c10045603503940c007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 134651124 1250 134649874 134649881
    0x20a032604031208041b0e01050906120a1103030706051602010f0b0a05040216020307030f030201180f0305070218011202010e0402030f0c130306020712180b0a20060c0a12 75
    0x2000c03010040d0981d40002c0c0039883c01548140510404514100440801031b1529480c2e00410118220000180304034184050450703070111040c2c90282c6694800c40d003099803501c0e0040010a0000844982280c0d07450603c16181d102c0c0d032146003480a41003140000090000d14640790380150b18104156030100d4040c01a4048124040d04240301a4100b10030300000c0d500100d26000d07140701255002c001a02c08000140056014000003071030042246002070950b50020305c05030360301400c41c10030700c0813503828080109115071500f0070b00d6a4400c5440400d20b1005d2030300c880c0141e03180141c0001140421f00d11a00f405c01c0c800d03600c0500442e5141e08000407800b0a640100c170503605400000c10380001000180700b220403290000f15603d42da680c50303000781e9200d40380071207505810101c0848910f41000140800c10901070540300f030b0500346000c40e4460b0142001d6201000b060032040d03140b00b6031305540c11034050740c110151245450802008600c65000d407942c200001c4082c0c28000b0790020610 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 134652374 1250 134651124 134651129
    0x609061e050906190b01090512070e100b031311190f050111030d05090f030a020d03060b2107050903190c0605030c041401050408060a1a0301090206030402040c0903020a032604 77
    0x122003480813070300460300c2c2c4020200400e00d541488140c80d408560b2390359041040048000001c0200106402d00c000c41c50929006001c105903280001c43c04c0c054035442d5810359a11101c1c0741d84400303042c1020300717255030184000c180312904107624000a0300301d00da82c07503c2030040c0c0d800c18403202241035440d001140c464501c00501c96181d082030000036034900321500140d07042880070302251411000141311a046501908944001d07901040d41e1045a80c0c150007210f0042400c2640541840c8207500b0152001c0801c0c45112580814440065031003405842940c20840f0041c0c222102e044041c000f942c1083c2c1d11140c292110441c4c4000015254810000c803442010481b00c071505042c6000d40017400b503540704552a051103400e00010032840c2c000c01190b8458884160042607008101007060b0151a00340040b0f40242d060050017005078540000322074010f941070340c00080c1d080c01c144040f108100c00780c0000790300652086002060000d4004025581200488003620041060701120500d200b40d2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 134653624 1250 134652374 134652391
    0x70b150d0b04110303121f06090602061b1e040504180507270509030a270608130204110a020624060304110a1e0503010917070609061e050906 62
    0x100000d00002d14011850141d07800103005c07a41407490050240c14a5807085034075140c00d94400c0400080401001c002000902050034400300c01402e00f2402520303280010034107196800e040c0103880820906200b15610f0051200030907400c006c075007100da01039500907c20148190b003003100036100c40200c0c0c003401d000640d00000400e1060300d0540f0048840b03121b0800d14a40c1480200240c0010305240182c6200c0c0c410354001c3c5a803044808000380c0401410034143c545141048840d2000184039070295082e82c0f0300d82030941d400d507281d40641c49501c044440094026080a03c60100304000c0f00c09885122026020398105550780c0c445582c001c60114900300503c104260084d4041c10940015034000780a03031983c014001c90580450075400c500d501c0034034018100600a03982100310071003200604003c038024000148140c561483c01c299401c1c208000e450f0000d8100300300045a40002500e59011005119400c0c007905500700407142c860050305c0007800d0000084203154040740d40791281c4200c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 134654874 1250 134653624 134653643
    0x60415061101021c0c1e050906180402070503030f0c031b1b070e072a020103020c07030f030309111002060a0507022118091b070204020906070b150d 65
    0x92940c00c6072495001100c046595600b0030401812512000d00c40e001c1040584010910b0007030108014031031040d2400005600d0794078041290b4590f4460102d07400f11310200c44460321400020380350107214910000c46a4000d10004403030341001408405944589030f100300181251780c40515209040c0300869544501d076001c080c1c43c0c2241c80d80540508800101c0000c00c011520791365082e1403918036181c1001100d040c5800405c41c40b141c1c88840380d03070048107070105020b484074405803210b212400104000e0625030007088804c44c6103001c00030030000b50740000031000114a1400e0103801803141200a0f9440c051130b80350f208550600c40081403101c48207500402d03069403501e981c0780041c58094406411030081d070b1810128004604081c0051010840c11980d640496120512900b0080000b072400360b640d407005c01c005001002803505800d41305500080c0c1d50401880005c0081c86030008140e40f01502003a410140b00c69a20141d11407480360a0710000c0808210800200b05924103005020601 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 134656124 1250 134654874 134654879
    0x111030406050f0705030318120403030c0b0915131b0302090a0e0f1e0601080109020a090915180302010506040528060b0703050a031b051213080a02070509060415 71
    0x4280020301d05803901c108070a00b000402d0741c91501b9940b00b620a0705070003411000007041040140310446184000070300c82c510389031540e600a8000000b00c45e0140140410303400007401c130442440a10030a03c80fa81003990380d4a88481b000010510381f92050361403203400006149100f1000c0d003c0000c0c0c03034000701080f4640d9255030704040a810240d02007180707401554010442c411003003181d2200d591810080102c48040711000320b00e0010140c0c003403001030b81000e100f5009030b103492010005445c611840030a410032503041060b0780404150f001800c4900c0c11480412012012074644e90b01c038405c2d40240035a446440400c000d81d0f00c10359280c0441e43d10088d00102410343c030720300c0f104500740d03911002c55019504d414011160f0894034040c0c000c96000915140382580c940320b0004090388030070505084c2e10359a007004002d0b00803040d400c6803810f82000821240380c074001e1442400c50b070040c1da603962001c418000035224101c2d40704960241c44044042506071070310b0700460310041016281c2488061 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 134657374 1250 134656124 134656127
    0x303110d0306032a051005040515040e01061103040f0311100e061c0b03060403030902150a020a0201110c091008070b0711010503060a0306050f040c08012a0e04020c1b0111030406 78
    0x2102404400441c0352251000502a11002c1260f06d01b0442e42c3c69007501d4514020601244541441d07820044400803c801c3c85100b50400d4940d06451043c9015044038101d000b05078954803494104400c0045880f50000820105800d000510001940c04d6840181d09200903189032944000f003580c013020034041009000d84981c807500b02c40c24600d20100304417507204046800c250382035800f039000a450f201a841903050504070559005049800c043c50101d4541000307480303012410009040201440c1850b01c107070f40c1006684261800201000a2800c0a510003610702145100342841401603810020700e600003042503d002d142c0041031072298085500c011961540000c00b03096020f0303100078000c40821040e1113143e226041c2000759500c3e504060401c550012403079442003140da81003200e0400003c80400c031004405120f01d0903884181c1e0462000d40c0c82d00700603070403d5009840400c20044184000400b1030081c8208840041050b9414004403840c031084c407191913181e4400c100410455 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 134658624 1250 134657374 134657423
    0x20c030a0b0a061d0711030a020705270f0a0b030f07030206030702010e060403050d060b07030c0f0311011e0b0312070816020619080601081003060203040206130303110d030603 77
    0x3030b40040303000694549038064000f88240d00c481c546640d0b40b5400c100081d040e0005131065114040d00c004500304412484025070381c1e00703603005190250320551042003070705400010b88603000d14070741e035800007601d002c801d0300989060403110191050705103002050301d07090100303841041240000240941604640a001407a4009000300c030840d0360741d990101f9200c1c024801030b801540709a40f0b456480300c044620394296403250b0826403c40f802006030000213074010350040f6109520894500a00000d420180c0d58640300c0401928194200500742121300c45105943c2c4d05441e03c02c0f41007140000301000e2581d01c00c0380d04d4100311424002c04c400004100b1260250101e52104d44e400c030710400180c1c0c041212500081c0071356840705240000b503413440350402d0b0660303803140c001e00e0840c0092811503485590f60400744030282419500102050654507444111040721030015030500003e0340d00e240044c01c03110201d034481f1b064000e484018034940c0c8280680e200b226007146040c44551224591030803036 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 134659874 1250 134658624 134658631
    0x3090709051503070806240f12070308040f0812160311010905120a0f030e030904090305130b03070906020613030806010c05010e0304090c02010209060d0b060d020c07060f020c030a0b 80
    0xb50388010303524440c980d800c1001030040c04015010340b10f941031a405100c03110019642d60011860201c0c0348900540b203002c0c0415000d0000c546031a03440555060302030174610160405031190340c0001d00803031200a812039000071599048105c0c5c1e40104521807060003800782090340750101400e403004d030003c20310803545607507103148400000a006c840c943c0c409140c082e41c285280007044001c02e01500941e0070883c58444806241424040c2811103030803180c0324840c103034070340388610380d281c00f0312085c94454400ea4036031440a80e07403860090b446207240001e40e0011034120001030b80842d8007186051000ca2114007403c010078641c0408042e40d0741c1940c000400901c0181006004e15140303020800c2405600080d60141000d1030303a8508040342c04058403002090142961b00410030b540d05501c49104880e0401071900c80010102c6c01072002139170500c15118100700c114004140c030340e01c0c84030200300d140c100c5040ba03c500c011117601c0001030341c03102d184000d129816008900c400002c680035140aa91 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 134661124 1250 134659874 134659891
    0x204140616060b0307080d020109020117070e011404051c02120a0b0408030c0d090b04020307050a050a211a09101406010c02010302090301020d0b0306010b04080712060605041e110309070905 83
    0x840b01d454a05447c03614801c101c0210043c0c1d101d81c030f43d0096582202410441080710219051030b458042d41c041d20025600c01c440e810040301c66200000f4010642c240c07406420000c2090304070200b4803034035066402051000303030b20861803641c8100da694000507100702e0050340806c1c019482e40e165200c509260704001d180c0d4201c2c1c10100a035000021403071240d9866103204071000780190409005052814581c1c0c1c0095010360340302c072000d010503030b02c00351032404403800f600c01c0d03240e8070b6402440c141b4a035400800040c4000503841840c43c0710409408464842c104c400120303141c1c0142c0100c50429540350707060440280c0c0b00076020a13401e5200300700800c1440d00604000d0314089030700700800e0032a400b5000c0308000d42d42c0d8001100b068139040c041e03c4d006010340020541001c1c01c04160a4842c6880e02c01c10740100d450454100030001d46403c52801000d006004104e0310420403040c154081c044000412000d2038009540800c503040000d40380904182002011254104440c900c000c0c0000351542a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 134662374 1250 134661124 134661133
    0x30905030d0f0f0b030706020a060504060b0907020a060b040b0a06050706060f1401120b011715060a08010e130308010b07031b030c020111010b0907050912100204140616060b03 77
    0x6609250003100b000b5540800005504146800d0640881c0c18243c0b1041c400c0d040340c0350400030580d0004c0d400c280c3d43d0b001800082c240c3c80b94a440401090981c81072a046104501040369194001c500603840b140210018000101110304001c200c60400021030b500544100c0c0510074144203901501d0800c2c8a608002101ca0715640780041a0809034003120040200c900d1810240d41e201c00c82c402c025494010074405244007800181c800718040c0590080c40c501940010001c001c0359034420400c6801070b205030303942d6901c1480102905001d00451340d01942a40114440800f180d01d8205070a41542d2500c5259003030030104846a131100d0000d8003049020b107084450122002c0105182601c283c580e44040c3e002440094005036440242c5803035079141903a88a8035071940c8881c568040b1075032403c5590b40702c43e00000750811080c41d00303001b1a4420444901c000c1206540100280c55809222100d619004c404010305480b0319107040c2100954085500c1c00241d00d5049050311100040554 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 134663624 1250 134662374 134662387
    0x120901050709180b120319020303010509010306020924030402040e0a0201080a050703200306152104060e0a06050114030708030433030507140403020906010e06090d0305070506070206130303090503 86
    0x240e0800346a402d41605074200040501d0001c400003681f850502160000c2c50866242c0000519144014440984641e0300000c0003561681d4420500916035405204440801c881c01c100b4012908115004ca00547c906840103210590011780c030034980c3c1e4140d5588206540c1d050710380010302400f61070b01307040c1500c80e0a8007084160300c03c1184091000074982a44914043e410010340341c0450040818444d410000c0740e001681041d4a1103401c0105010b8902c191540c2c64001c0081901070054603e074001e2f0500f6004000c2540c10041c1241c950303055100500c0d5a6404054881170f2510a523035844c0e1007000100600c0340030100004464100b4030032180e8024a2003840d9081d40440041000080e07924020031600941018140d400c2150b102001c500b0541181e0105006d01f001800e554107204a442805c0181e5803510201c0d000302c01d024218014441c2649000341036a08a124100c0d418081c2900041da0b6a00c0024900c1c401c480c003c2c41c00c40c1400550300d042c1c0040c180e800c0281c1d0140410080d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 134664874 1250 134663624 134663629
    0x31d03030f070b07080403091a0403140c01030e010b030304090b0a0906060f03200301060503180106080f0c0306040f0209040c091503050c0f030714030102160602120901050709180b 79
    0x180080e540d1141820b50703688060300d048121020018030480a0040800c2400046a404001002554129080e0111080421000c80150b005560004217040d240c60605031200380c021074032000414081e2400d000c0109007440d5503003694008031140d50554000d010400c024030182e044641c0111000e00b0051801da1105544d074141e0b4034079040742011550450300b024041303a26200d4041005071624000240c401240801080c5202c184613400401030f022000c0303428020b44001003c90314440c88020444183e80d04003c42d211201c020f03040202c6d000301d40d001c10242c2004619148190390001145000703000580c00c000065002500c2a5518101c3c3c0300081802841440ba05441a0000b083d6412461451400311b01e02041101b51b140900e40403d601c070415200042d0043c25515003070303030594a642c0c0e4000030a009000d010040c9400007028900001485002d5004001700301001d1920f141030354600c04241d099800c251000c80000700c0815080142e4803000080102c664008200031800c030340003000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 134666124 1250 134664874 134664877
    0xe1014030403050c060f0103020d03142209110306060d180c030516051f0e0d0503040b0d050105060301060f080c040905042f0f0d03051303080304020a0e0c07031d0303 73
    0x6040b00411070019120014282c1041896880030030503e50041e07560642c1c2c0402c5102031654001000c0c8480a000c40c0c04034400d035425a004401c07460405112030666625014095034140319104566203802086081e010854084030302c00d920140c803091501180c03e05003001401c069040598004015407154000740c2d0b40310944cbc0055000710010100759204a940c011501d0665000b00c0c89124600c00e230780c241c10149001000303509918200b40c140301740700740c000c03401ca2070b0360920090660100040c0407401d0b091141c0900003050100c00e0404c80350b078071075061141c0380c0f00038000d5002164100e90041002481240441d07844081e400b540c038240303540c6200d2030702a90801c1d10101c038044104160388000c071001014681140444c985149407075101580440c80449004182a0064110b220400c00f03042c0107408450007000701a010720829030380d0b400d01d021541c2065504074824440010001180302070030001a00546020801c640740c44400c0d0340039654202445001c031903002d03621a6078152680c0600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 134667374 1250 134666124 134666131
    0x1812010b061c1802010c0b040c15050c06060307120b100b0307050d0e06060a05120f060f010311010c03080a0b1201050c07060501080604050c060c03040504110403050d0f0e101403 78
    0x5100e01c20b50741c280d00c9200c02c3c0c0f00c004108144882c0312090f0000540c4c1e00c485d030401e9058119800c49020348a0342072404c00018070303820480c0d04101e8900c0c004201e603444001070680c50f50510544403152903000070551511001c2c4030b5610f4941840c0107a10220f900211215000244a110b200c0344540c0ea00d10429150021240480880c001058040d64280a03001d0b241035803040a02420180c07500388000ba21404840c01038030b005040030001c20f11a02030401c035540c00350001200f181c5e000c2c03801c0000f01c02d17074039000d010443c0c0c00c44102019030420b501540790310f030350b10f6896140c0420550b51080c80000925000100c00c2c0e0047c1071101e8071102440030702c503450088803000d19696895409040c501c1c25298107a0010215a200070204800304e400403ca6a50082049070081d5035000c000d0500c0d0720714086c40d001558000c2c40e0140c0c03c040e84c41d40304018000c0300d10450940d603550754240e0f01603403614a0094007101089203c6001110361810702c1e46100d10148a003400a4a0104040700078a0794104a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 134668624 1250 134667374 134667397
    0x80a021f0302300a0b09010b0a0c050f01090c0e01060801060e0d0f05011a060906030103020f031509100509160302010311071509230307060504060608060a1506051812010b06 76
    0x800e03c42d02c01e18400e010a0744d0000c8241c1041c0180024200070072031000d01489403503d60f81d0046004002580f1814a01c80c0440c2c121084030451010140308500811020f8002c50320901c491100145100850300b00328102c6440e0b031916901603180010694040c4000040c10b81c0c006503410341d040c000f60702d2100750040b49000c0c0c000050000d01c0d00c888140d41a090340803051260302c00303110700d0005540e24822681540c0e4144c440081e44001800401e281446a40307019112410210400c07041c1200000d940051110b0a4414450340c1c44045450340c80e0140c151000f40c008119074030500155020380c010303818035924841c05603d0b10440345c5a0117035035400c0507138429049803120745c032005210038841c40c1200014110820210114005000c0741d40e80b0640302c0007014152a80002030a004440d803200f4010310b101c038180c59940c0fa00e0f0850030000c240140584103804401100421298411025a81c141550780860902403400104000d00f82da80c44190303d00d190f40b11140503c0c039440d003801400c009050b4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 134669874 1250 134668624 134668687
    0x1807063e0705040623060403050d110c0f180c0c030d02070512030106050417030403080a03050a141308071103120a0f050715090c080d1701080a021f0302 67
    0x2101640390038040c09030300031841503080513800c0c010b505001014044016800c941c1866018845000c140079020b2944090142c0c02101c40b01400c0a800421582c5003150000c01e440b91490700b40c0801c0060100c2d494503d0700246103c00356401828840c0600790030000844a00c3e040c08804000304e03240d03a0100a9240000b034000c94250204003042006d404e04001c0c4041c1d243c115810b042008040340924421004054840f080603082a1005c2c000c03180607580001c2401c1d540c001504025011f40740641d91070a0141ca09003141c4003182503010300380d001741c050500ca08080131858032541e015030046030040d00c0100b40c20720744220380e40e030401080c903043c60011207861300c5442440d006004a04075040d6036041c41800c01844000030010b0f48240d1018645580c00a0001d1841c20700074540084d541184000344510703245404025007021070801d01030500c50541019030b07250742e003403a15480c3c1403100039009041402c01280042c2101c0091420040b2850f006081600100706410030607000706007280b00120 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 134671124 1250 134669874 134669987
    0x10302160b090c090c032a0f04090b090a060b1c06171c0806010c150f1103160c08030a2304031e1e0f03091401020909180706 55
    0x20082c0c4c02542c03207010002901c0c218549004680500f4050442020001c48012900b6411590710790648000e401da8a41242d21241c56a02c114010b280e110322091003200c04d200001c01c1c01b03490340640d10a5400301ba4040f800c024000c4c03c0792196400c148210030255840b02c60124460040200c500540c402810003401d20302c100754807550303614003100502c1d8108810b0710200500c61340c010100400c016070000424002c1800c00c0700ca440186070641e91052402e08020a002c4240300789400345004899015007101d030040c29800c2074800090354030006061110904c000b4509804a5204c0c41c80c020201d08015185001b401d1595110790040b5000c81c0484d1441e45200c42c1655010601c1c64203441d075040c5400d2001202600c014600080710022007000125071099036001e101e500400c00003948000c030940032420882409010350005d4030102e024010350f00000e0b4001c4044800010415000800703881e50741e04011048030036661303c07900c20130034861703149181400403424000c0011181051080020703030603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 134672374 1250 134671124 134671129
    0x9020d0b041a10021b01080606070b07020a020a150806040f06030c18051003150507050903011107021201020403020105030f040501091a070207080708031b10020c0604030206010e0c09010302160b090c 87
    0x401c411400404c5501070381642c401d2200c144034a0f070401c002401c14041036614a00018018428588000c01078180700c000d000c0510f4001809800c0300c3c0c401c94080e6030094880c99040440700800c12248001103a8001142442c102a40286c0b5940421100450010785a031140c60312000d05a202c1c200d6030382107005003d00402e0303500c15160040a102d08200c3c2141c41c50310303500300520500e00d61100030381e61800400c0043c2c0c0110211048204060028400d00f510008140496003103c0c006078028032464440e460f16500c18800c82d01604e038140c448a083d500d4680e180d2500c00c20041088034550740e981c030303418042101c2d0b0f02c0000034085042d885119500d00f502009086c04259071094043c0e91101c001401912400300544046500c0140307078120303001401c818549803840040055504610008041c80369074800f14806103d03074042e408a0b4141d981e50f141b0a081250f04440203007800c60140a40010340d80300e90002d28910101601c00049001141c403041c0301d0280c26a800301d0b030b80d40009003c03091070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 134673624 1250 134672374 134672389
    0x1407080606030601090303050c0109170715050105030304030f0807061415030604020f01050a140a05040f08160605030c1309060f0603020c060f0907090609020a120209010909020d0b041a 81
    0x100c025100c2504505015001a094070300ca408018140280824a0700c4004025480342100517084002025100d0484540b2076460740050415120015844c0045269903661b006080c103d0b980607006614051660301c0f4200d240b01d0003401241c080d8070800c10395020581c98000c45000d0145064943d9050034440c04014404142000c0d103402a041401040b0241e03540e0800000902001c0c00c0c11960340544240407a01540c481d510f001c040d40c2c0204590810542c00b00c0030307005a4034a0340c0501140c54a0f450915600c1d00e4400c03500905244681003440002d100700041c5810401c00350720141456910507011a100c10650031aa610a80d564003c00c04030440901d200010201410110b2629403d000c4458513103100500038080d00601d0700124620810400031540107103817210041182c15240d1408001a40c48018580001091300401400a00ca14030899001c90016101c1c0e40c0c3c00c03841c050b58803000e90442c90018010300d0342c1d40440c40b030035201e40c0100c4800030016030904600e081103400300800c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 134674874 1250 134673624 134673631
    0x90c0102011a01051e030f190c21150329010f0302041109030609100510050f0609010219030203070203071a072d05010608010c0801050306010b03091c0c050c121908040306140708 78
    0x159401e00d6041c46645030000a0b01c51424004c41c2b80075074070154202c11401402460401c00300303c1314024400800e0042c40c1400000c04010030401032080f00741080d40009078402030099211a5003103e6003000107140607803107841d1060035200e449040060340c00000741070810450740c000c2580c01404038030000d000340d03100e1140d00c074075150004d1050605120100e03825140701f144c19802039500040c4080117a000300701d50765580c3c824840d0103c0040705490025102d800c9000224028801e010010960800c51144915642c80402803182002e106441d0b4500c002c0d10038180c07003403031000c400c1040401c440c2e4160700c500e440d000d2800480c2103464100c541c0c0c212544441d8500c10411840300610641e60040303590790440d004c0410b550303142d48802c450349090900c00c440c200109040b00c202d44508c0d54000c45001810360190060f1040444c1c10424800a02074210740d20101c5e03004041c04014003450501e1196003140035491039800c068030781d652541200c8403080c038100d2501500d07040140c0c41e17510100c80c0d5070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 134676124 1250 134674874 134674921
    0x6090118060207080d050408040801050c03070e13090b010605040e06150910032408010b1915020a0501050708160c12080411100305090c0102011a01051e030f 69
    0x1900d6034448400c4080302004400070985a00040c4640a010b11041030f102003103120300e010003641c2401e1400059a600031700c1240c03001d500300340000f900307a50150141c82c400d02c19a1103280a56045008000c103500845801c60601035a903040031000c180c2c2c8044407406400f59480c0c56640d24103703000180380386001003081e44106503001204081c40418000e03164840000d84990560082040c0190054041140100c19603810018190141c45c0e0040d041000c80c1c400c0c8008000c07240e00340e0107104404040400300341000340801403c010840ba129403091420600f0300c19240d00c1c41e03580d5115400d541040d00c14000042400c03080c0400d5030841000034540718081e00f00b011600d4115681d000c0c001400398000d00902c040440082c003800290445059511303002000000a0540c0803c017030020601566500a14890440c240c1007a500501c20403d969100c201255a03010303000c001112640d00050600601009400c100c2c940c00400101a50080c3c8500d4201c86103860103803507401501281c040c4240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 134677374 1250 134676124 134676131
    0x1b0801110706050c0f0705010b0a080309090114130e0304031e0302060714070f030f0311070b01050909011e240e070e0102010e0a03020109020406151707090905010b0c060901 76
    0x400c4140c400c0c1101c0382558481008180c0741c2d10007141c141c0034051000c0d0049841d030001030711400c00c01c0c10341c0201c850007000c40b891a40d980e124013038182c0e240501e00c1c4a035045505c0e10014031021003030710410030f21200002c1104c1104a0755243d03800940e144c008044551350b101103010320800c1400d40b000340c141a5034039510440d96286860080d81c3d6580a4812402c1c070142c14101031911000303808030303035841d80c010031001c00e1402c0e245002000c0184401e044800689059403030031021000c3c0302111002c940000c0b0100f00e60342803d041080300c60b800b0f07212407560f650712290080030500230b00c2c0f150003509400030001080c1b80080041d8036549410502d1548083c1004002c0c130501c0050701449402c502c1529122500d002c1500050b03004003800100c00354184100181c0404140d415001542c84502c243c4090100035903406a101c200048007410303001040d40c03c071041c00f18100300070301564402c1030b9140000d0596550740903102255002c2c0c01603002000001a00c5014040400c0810f0f0000c40810080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 134678624 1250 134677374 134677391
    0xa110c0d030905030c150d15030c0308120f070f0302160b04080c070b090d0b060a031401200703020c0112230702060610021c1806110f01020c06061c0507031b0801 71
    0x14006d489031101810500369995600c01d07401260070041006140e11480000c051a200c0c14132480b560001000c048040300d004c40002c0c0b043c11042c883c14010010341c2c84000505d04040810380180d048604e03060001120100600003103115100c005003d280a4204035580d4120100818280b01c00ca800003c90301c4010031402080392a140c0f401401590000e4007290152101400101240c9040d4000f40051582e6000c0b44080c0070190b00512030011021201e043c0d21000d022560031b64040eaa9000c3e01681020010411950060b014072440d00086003001800c0c01a01d43c0030003404210454480100080000f00510a0b804101c11908000121609882d114041d80c0003540d90328814010b14588030b41f91031401400740204031181c414030b90031411900700713a00c03648003c0c8082c0c1c81e80d840909510a640c9a1010420184200e5085241241c00f810841d5102428001100411072006070005c0f8a0700740000407038010f00c0210051407140b03909614002c940d003440e000d0485207820100c2c959141040c43c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 134679874 1250 134678624 134678659
    0xc03170c030a0f0906090606050a0602191211030a030507082202060912060a380603060607150902010e04060602071e05190302150a050a110c0d030905030c 68
    0x907250301c0a904040420810003550256002e405103d00041409050404020400100e90000c4050f240d09a5400318903a039108012a9104035403640949080402d000450204203e038007031000038241410724001800409005620b990300c038201201c0000e5079107061010555201d260b0503002940c1011080e40441d02441010000d014800001d01c10322000038001141c3d180c00510a1600702d400041e5080d03407030103141e20300140004651261040840000c07100c0034002d1003003402e240c4031a806031400142d88135024080c150340094500c0e071b40000305001d2500050500b20030480005184040450600700d18070001d04151a980c41c4240b1a904280b42400580d0303002541c0e90813038002c0b5990460f100808035024001018682115406c8040b100d494219400c0c04100d450440740700340e85680200041404c0c00344aca008841401002071f90402c0074811540c03088241003120342032071041e21000c284000015841c44880031045021405050b000c0100307203402c2c010707414109020f507000008001841e01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 134681124 1250 134679874 134679877
    0x503040306140415090c2c01120503070f02060d0509010b0a0906181d15010602100204150c0c0806190b0a03020a050111010209090705090f01020c0913170a0c03170c 72
    0x24048030580e5524204000d1142d98a800c0c0000c2138900c0c44800e080c00c502c000c40304032582101c500c1480310480e07800029100034030300444427000d030840091410700040307941d100007200e1030020a0340d002c00207024505104807240b24490040345080b00003d001ca10f01e005100c0e070301c00705a1001142c9450003a0401071013881444810100090000024005205418500c0410101d0714024280c2c480c0310349640c01703845c0301c00000741078860329021500411881c00c070840c1644210b01820541500d0502141c0390039000c0c0d9140700c05548a01d0805107000e0310f80c000302c4d02d004000c9070b500704413420304004034044608a20404400c020144c0340401142d00799004a40f001d40e55109440c1049200314600d00c18507401e44c1a510700740001049105c45082450000f802d80e040207540522030401c2c2d90304d29040f0b41c0002802c4451500240c2822600d90f946000d850035101c140c101590f030010444c800034a00365812000b00302e0306103641c6030b400259140f0704008110783d01c2e082c0340015540a2600780310ac460b80d141e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 134682374 1250 134681124 134681153
    0x51308030c0f0d0e0303040c09020405030d0302090301240501090e100b030603030c12180f0d170c070b030711030423040b060d05060301110a141e030405030403061404 73
    0x8026030303070b4046408464156100e0310307000081441c5802c0750955140c8010000358007680c01001c4150800d915406490124841c81c8912685903100314041282039029030090090744070028000120039001142142c11103100705400328403080e00103400e01c001e40e0030010030005045400300000386490040b540c6401c103100b5009002c154480440000c03903136a0208115a0350401100030381c3c0c0c26800203081c180054100c3c008113000101c502c3c0c00300140d8207001325802541c4200810380380c1c80e041c080e02c0f01e40800340403201e040d52009003044484001e039402c020302c000504482d40101c0c0d6030314042d03030010555440302d40307040c0d6160030801c030400c43c07241d07c1002d036494409540c4e600107114407203500203002402c000174041d03017042020031081c0384406a50321607807156805400034010202124030128403441034480000c0421310003115203486601501c064811303180d00301004081030301d20b203820340956001190126004c0d80002010b004000450080c510047c03581081200135041560f60301414a2040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 134683624 1250 134682374 134682391
    0x60801020a050d180206040806160c080a030903031104141002060603120c03120a051501020f0d0c0203010b180406180213020a12020a0e010201153b0f0a05130803 71
    0x944d1207154121204400035031095004200551700c503642c00426031140b000b2203211031444480298991002c0c000d00941030400da000d0403440c6492403011081c1c008040d8201d0503420180e85004184c458020480100003400d03002080b24084038480c1c1c10040e510030000d0380c40c021904060700b84a0a0386001071408020709201080c0c1d5120f07030082643c0340c558061101d450034030211040a02c510114554005030007070107100200b9a010f4418401a41d9804035945142c4466011240055146201c0e0300d13080c42c0c6510040002c02d81d40c0c0c2000c0040c007801410240500452081c038180b100b0480c15101d044190045500100312100c095000502400301000b0002c0701190002042e20030a40302e18a10304d005011081c00715250008280002c01a0719414141c502641c41c0074118003500b10402038400840303821030804018061040d9540001c41c3c4040183c0c040504010ad8000d00303040c560a003148282d03240a030440b61803518841d00415a00090034040609807580c00c070101003000301c4201c0383e010040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 134684874 1250 134683624 134683631
    0x705010501120209162c18150d08040302030106030c06110f150a09020307080c01090605030115030b01050408100207121d0f030708030f0a08010602030301080c010c020105070f05010f060801020a050d 87
    0x11142c00b80c4404601002c6c1031400140d15009031851160076101c40e40041c2c00307880b0841050091002c0344c24164065480004407200101a1740c25443c0840040e03038043c0c45001401d003000d540f5400310f800e544054100b12001c50b9807a07014010746d98820232800300504200010031440418080444e100c0b0800c092002841500000103110340e00903411000e5070903400307001c0303524880d5100c000c5603c4018a40c2d415000649103840000c00c20b2081040d207050b203d142445151a02c0d03200c40c00c4c2e0042404214003810320000340700000f5002014028101c0e60680e160000d43d4841d070501c0c201d40c59040300400e46d000c1c030480c00001c0c00002d0185600203a900000c0d00ca0b00c511030a0311000a02d0b02a450344241c46911000800102e81e950281c09440a2840d949030f5442591b2200010382e1607000034090107400e0f40c0840103e0b0500d40c03188000141c2107006040003440c4c00d9050316626022110540162106da460380303101050710400b4415603008003515002103040120001d00140148120341d11010b110b40c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 134686124 1250 134684874 134684911
    0x30f1506040b1216030203120406081302040908040806043e0418110913150c0504050402040303030207050c040c0507080708040e07021e0c09041b0b0a050705010501120209 75
    0x860412000405034400f044442c0724000c0c03601c0809410326808128006e001d2040312200700c1f251081030b82d040e2195601c40c6a00d03543d0308441d42034040c1741c8510613a07103d6181c100d5100454581d0000300081c198400c0941040d180c18109101101c0c421003c4071001c90304800220b11b0034025171840558801011062060803410200280150885012a21f210304e0070700c1d0b41104002d054880f010403100c054400c2c000550741c0200c001180e41803014060b1402104040713103003041445a0060441c4041750801c903052a071140c0101d800ca8109400407030200783d000901c5d406212007003120b880720140c00c40d0302b484800d42004000300a40101c84008002050128804040018072000d0b01c020341407a2845007544d15024034000d62719130a611311500c0c185441e0344094254000420140c04020002d455000152284d95400c001201c0c1c8412101c3e281c00700b000c0208a44003070500900d9481d900d56100754a60003542842c508403103040c0d2090b02405078408403140142c9078a903d03d03510984161500e02a00e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 134687374 1250 134686124 134686129
    0x4030905040e0123060303030c0a05070f11010215220303020409050708040c08030403210201140103050d111c0c1505040503070303051303080103120e0411030105030f1506040b 77
    0x456401040c1c0c8641002542d4403244015884000c865079800740c52260703c001092600d01030042a1041600364000300005004101c145004003018441031500500d01311450715844003118011508a0b2100c0d00d0100c0303142c5660741000601c0028201166948130707418180c810b8103201020112511061035120700990a060080c0e040e580244480c4000340034038901000700038460307101110300710b42d2540c1c08100407900c03203400416101070302e80c40420328510036060248400d014402a02850031036481c1d040c81018190120070990085100d00010029052440f07000b03000b86250300c2411009600c010024040f42c2600c6010013410002414122491826410700b1500ca00a002e004204d031801c001c1400300708080000105151406640c04100356200e03a000c24005030340c0e10038094002540c01c001403011800144510040501c142420300e000b108200c042800d03102c000504150b8202c01100410103030506000701d5510304d040202421613201e40c40c08003040500098013150045945a214140c0ca8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 134688624 1250 134687374 134687387
    0x206160818030d0f060f030503090603060a051008040c080111040e070201020f03040f0b010603020906090f06090418020a0605070302030d0b06071505070921030804080f220e01031a0403 81
    0x304075010540303070303101d020801c46005881c05520302e83c0350038940b00001a204003000a07010580740e101c400365140c01d503050b00f00015504060846640251400d070005419542c1b1061506198002c3e10f92090340c0c5441c0c10074038401030007544113105503410305101d00c407024061400c80d4282d5200f282035600d1034580400c02c900a0044940c08115440c0000c2070005002c0c400c0034150080c2c0c464482240c042ea220201102640a1a4180e9402007424440750066140848040a1b400c0f13018213078505040d240d42c0010256412072059070319003240d1307105500941c14103202030300150159040c060324008250350300a6403449404291624180c0d10318242e007099513040100c5104603003090b0070100307043e000401e41c1e0003040290b865101060f02003000080384224100c02c900104060403506441c0401514107840504000700203d8290108010500d0000045c10140140513060800b91040b51410240300640c49900d40150084070550001000015520400307044004d41ca8201c041c10303600d442c0f50a4541 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 134689874 1250 134688624 134688661
    0x191107030c0501020c010e030d060b0a05030604092a140306130201080a200301081605130b1302030a0c020613050303060d020102030c0109050c0f0d050303061903060f06060f02061608 80
    0x25420280c1d86209030301e000025101d00641403508000c0c1c1d640c0c809600180b4400cce400702070081401840001c850b442c056004a02031402014020300c50b10130342d1650200402c02c1c80034400210544c03030091140104c001503040942100760000d00310b50501c01642103810741880c2000341001002d2000940401c0c43e034026503c0701e420041128441425900a10203d4000740500c100504c11417400f50364040c003030701c0014200d5001800180e454100408550060013a0780c02803070b0007146103140880016050f1008511400d88044e000031032401d80b00c0000d007402005003850400800b0080c0f1030021070b001004698008a0071540b284403c0e405100503421030040102c0f003010340d480d20301404d050190106032410141030484070441c80316422001c2001091000c1c03401340c0b4030340c02480000d6031402c000010b009452a9105103950042c2d803a500c0006640c9070031401440b00ba1145410003d82d1307004034188444d003142d400500800d141418069004041e035015400400c000034012175510300ba000c034021503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 134691124 1250 134689874 134689897
    0x3030f030c03070825050c030f071b0503030307210605030f010f0c0c03020a06020903010912050409150302060a031a030102070506101512050a0b040f05191107030c050102 75
    0x100c074600106007981c1c5400490750240403034504c600240c4180e0715110080d41c0c41509101c01d04110302011400c0f20075820075006040c0754441000801040c004850141c85105c0c498228001c002d280080c2400f070b010390540c005c6003c0d40c4107005000780070360000074821211000440180402101b040d200000d081c0701d0703012a03054002e4290070360550b24190812001d44500c031006103c129440e6000701c0700e68281c08005030041e00226604400a04903400614040030000c5c00400d40080035110000e000440303a4000c00882c03030005080100c0b2144d8000d2485106102c00c103810300c00e01d9238010403e00d01c20900796404040c3d884038403948070404640903c42da180050001c5403204d14518080740c0e105000d441400b14406450b4000400540f202ca1410f15240282c4d5500c0040c580a6041009408040c004542c066100c2804a8242e01c4501c18003002c0701c0d41510100b460306000c540b07402d0190b03007080e04038107060501c0ca075207a4003080c0408880c885540340c0341c500c68140260400d1402800384040040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 134692374 1250 134691124 134691127
    0x5030c1305040f1515050f030618010608070f0c0804180f0608100b040b012307020306040c090c0e06091c0b0103060501030210020606091306090c06020304090e010e0a020f03030f 78
    0x101d00f0a15507122503a484039421020203400d403528641ca51201e41051540d00103036080000d41c503220300c0c0e1000f46800c4200a850303007a07000c4495000354a0b0304002d0b0407800c0051080400c101c50142e000c0f250355004c02032800c040d01158500e407a4201e80b1b12841c020300e0b030f014003a240c20b4002084954449422174100c003104000d20340d01c7e01900b603200e111000e1058422401c001a0300818a494400d120003502c0c141c440e02d62110060860040241e1001103065264100307000d01000350300e050200340e1146104d84007841c1e026040c40c0c050380449040c4240c80702040342620038140c040c0c88074070446422000845655641c00b01c961a454070359050013000425049400000100704681034000ca81613901c202e501c1c1c030860120007000c90b600c000440e4040e500669140214200092900c0c01d0140c0500070301b80414200080d4807108800c1c02240e01510042c0c4c00010100400d4516209180141d1500f03c028807420b000c404205951303810740c0c0c0002c1e01c01c1c800d0b03440c07038900c50303a01b007084820b034100558086 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 134693624 1250 134692374 134692391
    0x3f090a090b03010e03090d0209040c03120e040e03070c0306020315040f0506091e060f04110c0d140c061f030f1b12020619022a1f05030c130504 63
    0xc03000e0104038a2241c001c1d803d141c6042c8800c0000300035140d0703101b4094010000940c00d9000c1110107000a8800e498030100302d04044045a140446100519919159004405032510500c411201d40860301c050a41083c0901e00000b09000040d40c200e80e0000f0025849031913a10800f22460f41c070b0100154000e00e81442c40c280e413a010740217240704000441d21100c1560f50000f0043c5444460050343c0981c403840b000040d900d20303140000c002c0c6a030000d0700004007d0720040d59012658005100b10840d68040300315003848a500c04070f00c0740001854241203062101598000742d0f02e14018100019941410070304842c408200c1045200454000034044801b0321070341020b00032242e0f0380e02200090751070b10002040e030f20110214030084aa000d400c49160907518103a22072042e00d90440482140101c070082000409a401c3d034034101540d01d10844851a210340410680f42c1d020fa80b01043c15501c456407070345054211040d2a0300c51101a103ca030b507025903001c840080f88281c0c00580d8840e203401c001b03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 134694874 1250 134693624 134693639
    0x5180d022b0b01050907090303030e01060e130b0711030405040b030307020307180506100507030302070609080a0914030105060a060513080d050903010b1e01031d01050112053f090a 79
    0x2108256014440c6450b40782d80350014804008400c442c05400714120b000d04000081c8030350710224038480a031000003505034858a04200b141d100751625031541c07401030300e4a4144849a00f0854101003103041c1a8480d029441c01075449000d00c1c410903211365511908505603440c21300807140150f90040660380b103680c5541b8510402d185110044031310503d0500010901d042030102940810040d448840c05c0215030741d0110301960184e8412204140c80d040303480700044c95100502440500d68445108403820184620a61036103038224600c203078100018007003907840700c1b5820703003e8601c0da19045a891107085490034003065103505c01c0700580700780000b108000354800c4c044c0c044e01d03b0850091000740701030400c00c0741d502e5640d541030151503464046403101c0d40c0a98458004200c51240003981041c40610349400c40302c00b40e00010340610321004200800c40280699071482d1180d42e0105040c440550a41d00d540300c0301503441c10100d042d05c620503204070002098070780042c03000b851040c3d1542c56555 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 134696124 1250 134694874 134694949
    0x2130203011e060203070b0621010f180c0e06010c120c021005181e030f03030402011b050c100302121305010c03060e16033905180d02 59
    0x14022590180b542442c402400d01c4565008403034243d4011030920b007880c0c5901284081c0a00020b90240e00741050f29036408403903401148030301140000203004a0005941c005803510701110340d81c5081d03076509000010f100480340600765002c0c0c0701810001d43c0d41600603a15000c00c44009043e9a1004201e18a850b5011810070440d510035600182a4015100c5c10394140c0201a40d1003c0c1700c9460016507458109451414000b060804a040d6114030007408282400b613084030500d142c0d0000010001036580002050a98081c8560410600d200c16100c03282c0340e03a281c00038284181d8185885508091103030701626030017213070981100054242002180c00728204d00e182101c0075424000d8203891203000f0f2043c0c400f03c5100048204403582d4000305800351080032052201030550f105c00b84114800035140d13400d400403400d07036001c0c40c5c025030015000043e14000c89034420058104038540345000307001c0c07028038841c0080d601030009186501c0000d0800756042080308082c0c8051500c640c09404034034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 134697374 1250 134696124 134696129
    0x100f2004050117090607230c0609060c0f0d0b0105040b0d0c0e0102030a0903170c070609170105040c09021309181e050717010e06010b0c06060406030b16020a0213020301 74
    0x3c9518050811100c0000070410040700d080401307411090000e0306081c0515110841c1d01c0c0e84402c0d806501c0d0794800c138051241c01c00e01011a41d41d00400400040010170810f440d0414400c00e860390400d40c0102e030500302840343c0c40345440c00a458464205d240d03401001030700c000d0f00f030120002d512180451140002801c01d44c44a1700000d004080602441d4004412668920440c6d40c0f400b11a07425500c3e81c103044c804520045100c1c203c100080f0070314100900c4000d0192400c1c0c1e840c0da010341d02d040c414540041c2c1082103000c1c10703403601081c08006542d5181560885410810241c1ca441504010000008140e84091101801d2800868004540030102501030b4850080e0f44c04820350200c45003881d0a200340014002d90002e04280203541c01488103200401c5400d00100300303000c80d081c00701d0078250203a01071403072500c011a04070b40240040c01213a034001019201040518a180c60300028000003600600601d541e0300c4400241a10920540d11090740241c0b07413035102103402400100075882403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 134698624 1250 134697374 134697377
    0xb16020103150b0307030b030f030301090903020601080f060106140c160501090f0e060607140109080904050a021306120e06100503010b06070f0219080d080a0b0111100f20040501 78
    0x20038440c10b52600e4450806032038100d00c2c1c00d401c5a60348002500185030b005075960340352007208000605400c0400085001c7e100102011030920740601e0b002e8a80041030300085001e1b0041c2100520035800001d100c0d044603408c0c0b501c0c454241c0002403d90300c42c0700304c007040c07070103405a0181c07103000c0e410300d00c40d0004a4800381d0760908840d549000602c0440b8650003485042414900882c0580c03802001070311100c0e01850410001032400c94800342100c80800c800c9901041c0461002c000d850704d885034a600041c098419031034074150960389003400300301e4000c030003e01901c0048252100b800d81d003d504c100c0c1d40b800407074103070f800c00c219075113a101150320596100351300b055030b40711703c0e0b0510400743d0709801c2d88002d50000b0144580d0812402d522103001206a030f0988090028001c00204030b940b05083c1141c40d01003c2c2e0070a0040101503a0f65041170300c0c10710600e022908803c050000d1049400850380000040300038100d002c0b81c0c054031a003902441429410039100c95146013040050013251001d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 134699874 1250 134698624 134698631
    0x4030e010810030f15021204060605090f011401082a04170102071e0f0b0a050403030509010501050f0603041703040302071806031a19021303061a0321040b16020103 72
    0x1400b0760720424180601000341459010345031000021400c04a403025032070036040260501d4031103802c4a1000b00110b4050b284151030749400c02c124180714081c26005041c0c5107035900c0c42c2d0706140030074064083ca00d403400e041140c00c400007940f1002c4181442107034840c2c080120380c0c0103050612441c45030800d0090300c00109a0090000d0102d605100b107071482548018840d0740b04800d90060304881001000c00c2e030b5250a0f64000c24002000d048101c1e1003001100030026140c00c150030010200d410050051392940c0c03400b0018013566a804081481c10841114036994076541ca1524801080c0c11004006e031005011003848201074012515000351880800700b585420110010f010585405210161407101d4044113100b0074860a203403507510016000b440e4601140d0010021b04a91014070b607184122a002001d100b00f100d18042c0900003403803900d0500008403032000107500d0303264802c2148000c10070740003601d814482890551340200460801e6a03100c264540300d118078000001801ca00185c078 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 134701124 1250 134699874 134699881
    0xa050d0e010909090302070605180603010603020406110f10020702010c0507030506060306160f0c0f02031002090a06021f0209120604060207030f030515190509010306150b310b0304030e0108 83
    0x243da104020070b280d059802848420310b021010354031640003001e1a62500040650050192036131700040d8001d0504e40ea0060340c0e146411001005c402d00d8440b242c8581d0001080a4203401c4009860001c004015900580d112070700c0c401650160560300f0020100e00030203e00009000004c82c19500c03c0c00f09406860f40781c0d481025003500d15402000090115900045078420b85100d1044c0681d02407062954000300740311500003030f1030040c042010000d5540c001034030f00b66604180d07074441c0c003c000c540000c1ca404041101140104410b140c0d200c1a8140d01140c000e07050ba840600109a030101030003620b80500b89403d210002c1c0d030000b4815004155000c22002c0c94038401d200d01486004651103106440c0c2d403250800580300b29610000d60710100c41800800c15a488450b028000c40c8500360000760448840c8002b4a80c05441e0311000b450310303051004e24110700c094280a04c41d000a845406840482c0d05071080d110182e640010a048002004220815030812a08450140241c8030300b5015074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 134702374 1250 134701124 134701139
    0x191d0109050c0705061b0408100506130c02061f030b0c0c15010501050901030903031d0304080c0402040e012106020d0213150f050306031903080103031205040807080a020a050d0e0109 80
    0x214504001300503030700c8200044c10500515014440c1d071801c41426514003541c0c0c0d441149804106454011781c01d5403002845140d15041ea002c000d200e020100c18005102a008080e489110080c088151a100140070b22200d40038a02510044c3d030384140040e0290800c0748100f010354014846401403445848a03010b6078200d0000168101d80e0160b454514101c0130b0380044020702841700040f0181a00da000000214221409500391209010000c43c3c0b00c9242800d628030303011103151002d01552040100b80303c41b965501001c2d0640312110030074003c01009850303560079851890800390215201007151314080c0503640041c414080c5100764400c905840742540c2c10b01070500c0700d00d21701190030740004a804a01034030107154007250050a9400c03000008080300c2c410300c1c141d2811030001e03a50300c0c010300415420003804174890505030001c202074a00703036990420300c0c030a19201402c004801304442155074030030055001c0d50303584602560500007900304042c1101c1c01240340d843c0450b5080b0720204854 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 134703624 1250 134702374 134702377
    0x72903130b01231903050d05070b180a020111070b1b0606010815011b020a030501050118020c0d05071112010213050102010207020f0418052a01030b030c191d0109050c 73
    0x40d95903107029518145100204056013a142410f555481482d4000101040080c407218401142a4079401c0d0b4404880c41c04e0a80a00001c0c6244c40c103034104400d00310408030002d03100c0c02e500c0c2e0a00b4803210704001490070314500041790f8848050100700041d000d070401e884181c03039242510a541140c1c82900d880005654469046507030b4641030700013002071800e139881400340341c0c214554010004242c4109402007503c5500b55041070790184e4440e07004004080c40c01288c0282000c9800342141481110f070482c5468400c41c50710681000404584c18052020480c01e541041d80001c1040c1c601007000380c00a8081d4000e82401ca066a000c404001219401030003280d000301d80c014903a0070a13180c1c800400c00245001c8801003840020304601000068003008000050b404280e02c84400344000d1483c004601c00306801c040c1014100b0f0050b07400c070740700042c941510020890b003900d00700c0401080085003c00c41c0d0f0144148800e00c5404221400c0603000d040e040e19400401030100d035035641c43d0344034076 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 134704874 1250 134703624 134703659
    0x91e03061d0c060315060301150f0c080d090305040b1c05010605090a0b030c070209040f0c050616170d09030905031608030a111009050c010e03010608072903130b01 72
    0x50b8100040c1984a842c000f00115400400101240e020900103008100103810907004034092508241d18500000c2d0021900240d1320640c0c81e1070708a41e5215a030324001802000346c0d4841d52600c950b41c020415020f8020344000d00b20007000140c4075421030803aa040c440c100415200f0307561800001282080c42403003100c66645001d4000c00e007050bd0700761460362300d9000401204c6007a805011500069444000030b40c021070148909a1040c1c14604181103086d0041e80160700c1680c041204a0120540b00460401142c002a080c0b80000400d12a442c03075114440f94003050343c1c07034660541c00300354100c00700406480058003120702e281042c0403004503040217406109010361092202503880d500c00d9500103080030414080e00e0a4202000f60740c002d560902d041201c441d0810041c80281d0759218110b50b102a0045000707226040c034000c2015220489030040e40e20300204540b1140c02c440811500442500f90090100e559107080280d4552a0040460840340e80200303500005a44a043d14900c2c2d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 134706124 1250 134704874 134704931
    0x6060a0f0803091306031205040f050a030f1b0b1c050c03010302010e060c01021c020d0b010206161b0503210a0e0d2a0302031e0313080a091e0306 64
    0xb07403025050402c01d4480d140c03130244402c035032101000320020386403c03000036440342d19440b200d8403039080100658460a240c2c00c6680101a104420404a443da42041c412207400940d0144101414400d001100035a508050b02d403030350000350342150440f010480e0880e02c4600d4420417107901c0d00070409000344401c1c44040c1c00100103031031038a02494901300a2003131600c10800107141105154403625030f814041e10b00101d095000c100c416110a1078087d86841c50006d20290000f450a441c41c01807107040b08164004010500a0f81c1001d0f120b4180036100c0700307400c0403c607500c414001661884d00009460f948012030014004240c0d1070354640100c55402c18250702404008204141c00c5170000c500441d2902164124450400a0081100300082407402580595541c40d50601002c03580c0303c07600300c131550320038081041008000342c0c00c2e11503084a51006005942c4c81d01c003130045410111075000220884c40286a107143c0b0840a5800c40449200d94400c0c000388200e50b43c44898a10f01e00301c0703001d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 134707374 1250 134706124 134706127
    0xc0f030307030f060e0109020c030d0c02030a0305010824060109030b0a02040f050901060914040b0d03090503010c05040323010902180f0a060e130311010606031409030403020102100507091706060a0f0803 89
    0x414200d40348c01516003284403a044905209119020500380c0b580e1000700c90140e040001c18241995060240310b000d8903984d0010800e890501141c070b001c40422005004026903c580440c5850384a080314030015604000026918245144140d000358014841c0615003076102c2000500c5040000d0001d049800310f403503a905562500000d89143c00718500625030080c1d413028821440d5481c030300700b41a040c0c06075445403c018200070038103003190141010002441410b0004200040b50890f0038406030442007110b000c0358484039551805494500c3c00254440a4800355000429104501c0761041003400511422074480040c079030b080f20f640703016820b102144800060f450394181d42002c00c03080d01c64944020f291015024107400c5801c550070190001e40c460320444071180c0c40c0404075070400d0010b80994645860342e40080c0d40c445a2a80302c41c2919140d400084440c1e0051204a0051442c25805102c01021000154070703010215401c0d84218a43c160106000c01448100030a40e100c403030045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 134708624 1250 134707374 134707379
    0x905040c170a0203060301150e091e0d0509040603020d0f03030c0c0206090d0203070506030c04050f0604120b040609050a06060512160512160e06010906050a05070303020f0c0f030307030f060e01 85
    0xa5130008140c6501907484d40c0d14003000007c12100c010003090440d18551050800c602018104080d540000041c144079080304104010301051340c807040003082c180550f98503007020214001e01140d03480603502c035060304198414401800300300d80046110399004c10030b00541c4401900c889030103920203500324506001c3c0c940c2e141003d9141c034502a000804584d425030f0b8034400103c040d0710485903448154000301d4200140e0420705038030071075100c00321780b84d0782490f051410110386882c3d8030303a000d09010164404a0213001c00350f442030303004580110035a0341c40d040e2802d01c680588402d00c80e10b4061910b03070360401d20302c0c180840d03094070080c840c5404040c164a0070041106070000c032380c2060b00500900788603000c940c421100307601c0240b000c00b0300c1e03d01c2440d08a001410301e020687c000424040708000c085a40c952040454459650500380141c4540e07c1215080b16409070b0f990f090070611625101c02200e03000007010350320880e4240c0d014801c031441d5142c90800e417401441100036560030720005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 134709874 1250 134708624 134708641
    0x27080d0203040f0605100503010b030a0503031609080313140405061e060d090606050f060304050d030917030f0a0b03010c0207050d060b150d0f18020d15020403030905040c17 76
    0x70354126020b007503442c43e81c402076103c0c14112001034074500c80303021000341d04000508080c09002d052034011000742071030b40c07156224182c07a88002084000215240820240002e00a41150340900810000c40e5180e56445242d1514105036001d5074208041c001031072a00c074070b810b004440c4280b601801c2c0036031840d41c0607690403a15440a42040c2e20400034060690950064461900041d0040303401140940c64801401500046582640d01900d030400c01c0102107000014000c001000520300040c2003a680c0c00d15022840b814103006031400f4000044c48003444103600b2150080865182c00c00611400320105800c2350001403081d00540c210800802c001e00e0403001500740c640c056180450b00c481c0300c07000070740d0b80ba4a443c5d01600b03d00c4045011039919400784901001c2403002c40b01000004411b645068005c00340f210000d11580f030026207002085903112500f500409040d00a5441e641c0b00c1c139020709049500e002e11409240b0703141c50b81604510507503140020b0440c0c0f0054083c42d4480716030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 134711124 1250 134709874 134709877
    0x60612030702220e07030b0901021201030f08190806030f030a0903020112020c01060e01080606040b0d021014040b0403060b100e091305060f0601120c050f0703030e1027080d02 77
    0x82c61212400c14010f07840d5014183c1c02150f000005100c042c210141c11841c00140e021000303003100c900342e0300c148a09024055440c180c14156900300f01900032540080c503040c4d50f00e215003044034000008550080c41c1da5500681201e010300e208900742ca485508a0065590302c0c001c08201c0307000034030007002c10030155020345640c1b0b00c40400b135007002d450200c40d07525144c04c0d50746507070005030035005e844010000c0030802e001f125001101100d00b40001028800050300c4a603821202a00c1004d0130384c0318942d00750040b600c0840c4440d188403202d490701c0d901d1000241680041c48155039450030607000102a181c50100d03a07284001d40c2e2034100170322804200740050548024165004955544101340c0850030412801e84190400350000d0701500e880b200061039099144510b0340c8607030401307451107400da4100082e202c0360321100a00584a1541d410214060700403802c00351414001c01a0006030b588450300096010500e20300c1c102c8804070261018851041142c0c0060f0450708188042000c0140390740 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 134712230 1106 134711124 134711149
    0xf061212020d0927180302070807090e100506030f0703060209041b09060e0625020a15020613110622050411030f0601090f06020304030302060612030702 67
    0x2c84190b60103c40400c1d41c0039212058182106420b2684906940c540c030101c030b1782013039225080203500e03003056010301c198501460402207034504141c000c5141c100d9244006042503c180e0112000401d40035010070340c940141c00300070740000b8081060300042c60243c940180d45256150411040380d07400014000a40b240c45104444540c02c41c0300003080303400381d00381808100c98082c0001d00a211b011503103c01900302c0c04094000140040c8030484041c800c0d03550303c20142c4c03201c120720301d001440002e010040e03000341c0c0020360850031a80100c6019114098a0300c10803c801e0000f40d4035013104000c0b010a114800500126002004030100109001d4504010b64901000c1485ca1b92000420b00c400791001a008242c10781d2207440c90305c0042424081001f04242c681e03030025101c3e481884181d0052060b040440d003249000f26840340c4528070302c80214a00040c81e030074482d40c5840034 = true := by decide +kernel

theorem cover : BRFrame.Cov 134532374 134712230 := by
  have h0 := BRFrame.cov_init 134532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 134532374 ≤ n) (h2 : n < 134712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
